/*
Copyright (C) 2007 Leo Freitas
This file is part of the czt project.
The czt project contains free software; you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation; either version 2 of the License, or
(at your option) any later version.
The czt project is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.
You should have received a copy of the GNU General Public License
along with czt; if not, write to the Free Software
Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 */
package net.sourceforge.czt.typecheck.circus;

import java.util.List;
import net.sourceforge.czt.circus.ast.ChannelType;
import net.sourceforge.czt.circus.ast.CircusCommunicationList;
import net.sourceforge.czt.circus.ast.CircusFieldList;
import net.sourceforge.czt.circus.ast.CommPattern;
import net.sourceforge.czt.circus.ast.CommUsage;
import net.sourceforge.czt.circus.ast.Communication;
import net.sourceforge.czt.circus.ast.CommunicationType;
import net.sourceforge.czt.circus.ast.DotField;
import net.sourceforge.czt.circus.ast.Field;
import net.sourceforge.czt.circus.ast.InputField;
import net.sourceforge.czt.circus.util.CircusUtils;
import net.sourceforge.czt.circus.visitor.CircusCommunicationListVisitor;
import net.sourceforge.czt.circus.visitor.CircusFieldListVisitor;
import net.sourceforge.czt.circus.visitor.CommunicationVisitor;
import net.sourceforge.czt.circus.visitor.DotFieldVisitor;
import net.sourceforge.czt.circus.visitor.InputFieldVisitor;
import net.sourceforge.czt.typecheck.circus.util.GlobalDefs;
import net.sourceforge.czt.typecheck.z.impl.UnknownType;
import net.sourceforge.czt.typecheck.z.util.UResult;
import net.sourceforge.czt.z.ast.Name;
import net.sourceforge.czt.z.ast.NameTypePair;
import net.sourceforge.czt.z.ast.Pred;
import net.sourceforge.czt.z.ast.ProdType;
import net.sourceforge.czt.z.ast.RefExpr;
import net.sourceforge.czt.z.ast.Signature;
import net.sourceforge.czt.z.ast.Type;
import net.sourceforge.czt.z.ast.Type2;
import net.sourceforge.czt.z.ast.ZExprList;

import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.z.util.ZUtils;

/**
 *
 * @author Leo Freitas
 */
public class CommunicationChecker extends Checker<List<NameTypePair>>
  implements CommunicationVisitor<List<NameTypePair>>,
             DotFieldVisitor<List<NameTypePair>>,
             InputFieldVisitor<List<NameTypePair>>,
             CircusFieldListVisitor<List<NameTypePair>>,
             CircusCommunicationListVisitor<List<NameTypePair>>
{

  /**
   * Pointer to the current field position within a communication list.
   * Synchronisation does not consider the value of this field.
   */
  private int fieldPosition_ = 0;
  /**
   * Number of fields in a communication. For synchronisation, this value MUST be zero.
   * Despite this fact, synchronisation does return a signature containing the 
   * synchronisation channel name and its type.
   */
  private int fieldCount_ = 0;
  /**
   * Flag determining whether the communication channel is of product type or not.
   * Before field evaluation the value is null. During field evaluation the value is t/f
   */
  private Boolean isProdType_ = null;
  /**
   * Communication pattern as detected by the parser.
   */
  private CommPattern commPattern_ = null;
  /**
   * Communication channel name.
   */
  private Name channelName_ = null;
  /**
   * Communication channel type after generic parameters have been resolved.
   */
  private ChannelType channelType_ = null;
  /**
   * This variable points to the resolved channelName/Type pair for 
   * the last communication analysed. It is inially null, but remains
   * with the last computed value. This way the calling visitor
   * knows what to extract from the resolved type of this comm.
   */
  private NameTypePair lastUsedChannel_ = null;

  /**
   * Synchronisation channel name
   */
  protected final ZName synchName_;
  
  /**
   * Synchronisation channel (spurious) type.
   */
  protected final Type2 synchType_;

  /** Creates a new instance of CommunicationChecker */
  public CommunicationChecker(TypeChecker typeChecker)
  {
    super(typeChecker);
    synchName_ = factory().createSynchName();        
    synchType_ = checkUnificationSpecialType(synchName_, CircusUtils.SYNCH_CHANNEL_TYPE);
  }  
  
  protected boolean isProdTypeComm()
  {
    // if previously evaluated, jusst used it. otherwise, recalculate it.
    boolean result = isProdType_ == null ? (channelType_ != null) : isProdType_;
    if (result)
    {
      // get the channel base type.
      Type2 baseType = channelType_.getType();
      assert baseType != null : "Invalid channel typechecking. base type is null.";
      result = (baseType instanceof ProdType);
    }
    return result;
  }

  @Override
  protected NameTypePair lastUsedChannel()
  {
    assert lastUsedChannel_ != null : "cannot query for last used channel information before analysing any";
    return lastUsedChannel_;
  }

  protected boolean channelFieldsWellFormed()
  {
    assert isProdType_ != null : "cannot check fields before knowing nature of channel type.";

    // this should never happen, unless the visitInputField is called
    // from a different point from visitCommunication.
    boolean fieldsFormatInv =
      // if not product type, we must be the first field
      ((!isProdType_ && fieldPosition_ == 0) ||
      // otherwise, our position must be within the product type size.
      (isProdType_ && fieldPosition_ <
      GlobalDefs.prodType(channelType_).getType().size()));
    return fieldsFormatInv;
  }

  protected Type2 getFieldTypeProjection()
  {
    assert isProdType_ != null : "cannot project on unknown channel type";
    assert fieldPosition_ < fieldCount_ : "no next field type to project on channel type";

    Type2 result;
    if (isProdType_)
    {
      // if the last field is being checked, get the remainder type; otherwise get just one
      ProdType type = GlobalDefs.prodType(channelType_);
      int count = (fieldPosition_ == fieldCount_ - 1) ? (type.getType().size() - fieldPosition_) : 1;
      result = getProdTypeProjection(type, fieldPosition_, count);
    }
    else
    {
      result = channelType_.getType();
    }
    return result;
  }

  /**
   * Removes from the given pairs all those that do not correspond to input variables.
   * That is, remove all those output fields fresshly added names. This is useful to
   * know which variables have been added to the action signature.
   */
  protected List<NameTypePair> filterInputs(List<NameTypePair> pairs)
  {
    List<NameTypePair> result = factory().list();
    for (NameTypePair pair : pairs)
    {
      if (!pair.getZName().getWord().startsWith(FRESH_INTERNAL_NAME_PREFIX))
      {
        result.add(pair);
      }
    }
    return result;
  }
  /**
   * Auxiliary methods to create fresh DotField names for their NameTypePair result
   */
  private static int freshDotId = 0;
  private static final String FRESH_INTERNAL_NAME_PREFIX =
    CircusUtils.DEFAULT_IMPLICIT_DOTEXPR_NAME_PREFIX;

  private String createFreshDotFieldName()
  {
    String result = FRESH_INTERNAL_NAME_PREFIX + channelName_.toString() + (freshDotId++);
    return result;
  }

  private enum CommFormatResolution
  {
    WellFormedSynch, WellFormedComm, CommNoFields, FieldSynch
  };

  private static final  CommFormatResolution[][] COMM_FORMAT_MATRIX =      
      {                     /* synch                                 comm */
        /* empty fields  */  { CommFormatResolution.WellFormedSynch, CommFormatResolution.CommNoFields   },  
        /* !empty fields */  { CommFormatResolution.FieldSynch     , CommFormatResolution.WellFormedComm } 
      };
  
  /**
   *
   * @law C.13.1, C.13.2, C.13.3
   */
  public List<NameTypePair> visitCommunication(Communication term)
  {      
  // Communication ::= N
  // Communication ::= N CParameter+
  // Communication ::= N[Expression+] CParameter+
    
    List<NameTypePair> result = factory().list();
    
    // get the channel name from the expression.
    channelName_ = term.getChannelExpr().getName();
    commPattern_ = term.getCommPattern();

    // communications can only appear within an action paragrph
    checkActionParaScope(term, channelName_);    
    
    // form the basis for all error messages: action where comm. appears + channel name.
    List<Object> params = factory().list();
    params.add(getCurrentProcessName());
    params.add(getCurrentActionName());
    params.add(channelName_);
    
    // typecheck the channel reference expression - resolve generic types
    RefExpr channelExpr = term.getChannelExpr();
    Type2 type = channelExpr.accept(exprChecker());
    
    // originally the comm invariant is true. if a specific error is catched
    // in the case analysis, nothing else is reported. otherwise, we check
    // this flag after it to see whether to raise an extra error or not.
    boolean commFormatInv = true;

    if (type instanceof ChannelType)
    {
      fieldPosition_ = 0;
      channelType_ = (ChannelType) type;
      CircusFieldList fields = term.getCircusFieldList();
      fieldCount_ = fields.size();

      // decide whether this is a well formed communication, or 
      // else if it isn't, raise an error.
      CommFormatResolution commFormat =
        COMM_FORMAT_MATRIX[(fields.isEmpty() ? 0 : 1)][(channelType_.equals(synchType_) ? 0 : 1)];

      isProdType_ = isProdTypeComm();
      assert isProdType_ != null;

      switch (commFormat)
      {
        case WellFormedSynch:
          // synchronisation isn't a product type, and field count is 0.
          // also, check that the parsed CommPattern flag is correct.
          commFormatInv = (!isProdType_ && fieldCount_ == 0 &&
            commPattern_.equals(CommPattern.Synch) &&
            term.getCommUsage().equals(CommUsage.Normal));
          if (commFormatInv)
          {
            result.add(factory().createNameTypePair(synchName_, synchType_));
          }
          break;

        case WellFormedComm:
          // communication is either with one field (i.e. c?x  for c: N or c: N x N)
          // or it MUST have all the fields explicitly, thus rulling out CSP_M
          // asymmetries: e.g., c: N x N x N , c?x?y  is (x, (y.1, y.2))
          //
          // NOTE: to consider such asymmetry, we would need:
          //       a) a weaker invariant: fieldCount_ <=  prodType(baseType).getType().size()
          //       b) treatment on InputField to get the tail type for the last field
          //      
          //       the trouble is that it will generate non-unifiable SigmaExpr.
          //       (e.g., { ("c", (x, (y.1, y.2))), ("c", (x, y, z)) } )
          commFormatInv = ((fieldCount_ == 1 ||
            (isProdType_ &&
            fieldCount_ == GlobalDefs.prodType(channelType_.getType()).getType().
            size())) &&
            !commPattern_.equals(CommPattern.Synch));

          // if there is a format error, raise it; otherwise carry on.
          if (commFormatInv)
          {
            // lets deal with generic instantiation at communication .
            ZExprList zGenActuals = channelExpr.getExprList() == null ? null : ZUtils.assertZExprList(channelExpr.getExprList());

            // TODO: CHECK: z.ExprChecker.visitRefExpr for way to deal with generics here
            if (zGenActuals != null && !zGenActuals.isEmpty())
            {
              assert false : "Not treating generic channels yet";
              term.setCommUsage(CommUsage.Generic);
//              if(!isGenericChannel(this.channelName_)) {
//                error(term, ErrorMessage.IS_NOT_GENERIC_CHANNEL, params);
//              }
//              else {
//                ZExprList exprs = zGenActuals;
//                List<DeclName> genParams = getGenParamsChannel(this.channelName_);
//                if(exprs.size() != genParams.size()) {
//                  error(term, ErrorMessage.DIFF_NUMBER_IN_GENERIC_CHANNEL_INSTATIATION, params);
//                }
//                else {
//                  int i = 0;
//                  for(Expr expr : exprs) {
//                    Type2 typeExpr = expr.accept(exprChecker());
//                    DeclName genName = genParams.get(i);
//                    if(typeExpr instanceof PowerType) {
//                      Type2 type = ((PowerType)typeExpr).getType();
//                      this.channelType_ = replaceChannelType(genName, type, this.channelType_);
//                    } else {
//                      error(term, ErrorMessage.EXPR_TYPE_IS_NOT_POWERSET, params);
//                      break;
//                    }
//                    i++;
//                  }
//                }
//              }
            }

            // finally, analyse each communication field.
            // 
            // NOTE: Manuela's original implementation mistakenly put fields into
            //       a local-local scope (i.e. c?x!x), so that output fields could
            //       refer to input variables. 
            //       On the other hand, we face an asymmetry w.r.t. FDR's CSP_M here.
            //       in FDR, "c?x!x" is invalid, whereas "c?x?z : { a, b | a<-T, b<-T, b==x }"
            //       is valid (and is equivalent to "c?x!x")!
            //       We decided to allow the reference to "x" right after it has 
            //       declared. That is, the pair is added to type environment 
            //       by the InputField, rather than the PrefixAction
            result.addAll(fields.accept(commChecker()));

            assert (result.size() == fieldCount_) :
              "Invalid field list typechecking: wrong field count.";

            // check whether any of the input variables were declared with the same name.
            // Here, this sufices because PrefixAction should have opened a new scope, hence
            // no name id unification is needed neither happens (as it does for InclDecl).
            // e.g., S == [x: \nat]; T == [S; x: \num] would unify the ids for two decl names x
            //       whereas in State == [x: \nat]; A = c?x -> x := x +1, we override the schema name
            //       since "x" in "x := x+1" comes from the input rather than the state name.
            checkForDuplicates(result, term);
          }
          break;

        case CommNoFields:
          // typed channels must have fields.
          assert fields.isEmpty();
          error(term, ErrorMessage.CHANNEL_NEEDS_CPARAMS, params);
          break;
        case FieldSynch:
          // synchronisation channels cannot have fields.
          assert !fields.isEmpty();
          error(term, ErrorMessage.SYNCH_CHANNEL_WITH_CPARAMS_ERROR, params);
          break;
      }
    }
    else
    {
      error(term, ErrorMessage.IS_NOT_CHANNEL_NAME, params);
    }

    // check invariant for good channels.
    if (!commFormatInv)
    {
      params.add(channelType_);
      params.add(fieldCount_);
      error(term, ErrorMessage.NUMBER_CPARAMS_INCOMPATIBLE_CHANNEL_TYPE, params);
    }

    // add this instantiated channel as a used channel in the calling scope.
    lastUsedChannel_ = factory().createNameTypePair(channelName_, channelType_);
    //circusTypeEnv().addUsedChannels(false, lastUsedChannel_);
   
    // add the used channel name and its instantiated type to the communication
    // signature. if there is an error, we add a null element.
    Signature signature = factory().createSignature(result);
    signature.getNameTypePair().add(0, lastUsedChannel_);
    
    // a signature to the Communication term. first element is the channel type.    
    addSignatureAnn(term, signature);

    CommunicationType commType = factory().getCircusFactory().
      createCommunicationType(signature);
    addTypeAnn(term, commType);

    // reset the attributes only valid for communication field analysis.
    // note that lastUsedChannel_ remains valid, so that the calling visitor
    // knows what to extract from the resolved type of this comm.
    commPattern_ = null;
    isProdType_ = null;
    channelName_ = null;
    channelType_ = null;
    fieldPosition_ = 0;
    fieldCount_ = 0;

    return result;
  }
  
  @Override
  public List<NameTypePair> visitCircusCommunicationList(CircusCommunicationList term)
  {
    List<NameTypePair> result = factory().list();
    for(Communication comm : term)
    {
      //Type2 commType getType2FromAnns(comm);
    }   
    assert false : "TODO";
    return result;
  }  

  /**
   * Typechecks each field within the field list, and increment the current field
   * position being analysed.
   *
   *@law C.14.1, C.14.2
   */
  public List<NameTypePair> visitCircusFieldList(CircusFieldList term)
  {
    List<NameTypePair> result = factory().list();
    for (Field field : term)
    {
      // analyse each communication field
      result.addAll(field.accept(commChecker()));
      fieldPosition_++;
    }
    return result;
  }

  /**
   * First checks the field is within a process scope, and that the whole
   * communication fields invariant holds. Then, get the right type projection 
   * from the channel type depending on the current field position. Next, declare
   * the new local (4) variables with their corresponding type in the current 
   * scope openned by a prefixing action. Note this might override the state 
   * variables in case the names are the same. Next, type check the predicate
   * restriction in the enriched environment. Finally, returns a list of name type 
   * pairs containing the (4) local variable names and corresponding projected type. 
   * These pairs are used others to have a complete communication signature.
   * 
   *@law C.15.1, C.15.2
   */
  public List<NameTypePair> visitInputField(InputField term)
  {
    Name varName = term.getVariableName();

    List<NameTypePair> result = factory().list();

    // communications can only appear within a process paragrph
    checkActionParaScope(term, channelName_);

    if (channelFieldsWellFormed())
    {
      // if the result type is a ProdType, it could be either because:
      //  a) fieldPos = 1, in c?x!z where the channel is typed as ((N x N) x N)
      //  b) fieldPos = 2, in c?x where the channel is typed (N x N) and so on.
      //
      // What is important to remember: the variable types do not necessarily 
      // unify with the channel type (i.e. the communication signature is not 
      // the same as the channel type signature).
      Type varType = getFieldTypeProjection();

      // add the input variable into scope. The calling "PrefixAction" must close it appropriately.      
      NameTypePair ntp = factory().createNameTypePair(varName, varType);

      // create local variables for varName and add them to the current scope
      result.addAll(addLocalVars(ntp));

      // type check the restriction predicate, if any
      Pred pred = term.getRestriction();
      if (pred != null)
      {
        UResult solved = pred.accept(predChecker());

        // if not solved in the first pass, do it again
        if (solved.equals(UResult.PARTIAL))
        {
          solved = pred.accept(predChecker());
          assert solved == UResult.SUCC : "could not solve predicate in input field";
        }
      }
    }
    else
    {
      // form the basis for all error messages: process where comm. appears + channel name.
      List<Object> params = factory().list();
      params.add(getCurrentProcessName());
      params.add(getCurrentActionName());
      params.add(channelName_);
      params.add("input variable " + varName);
      params.add(fieldPosition_);
      error(term, ErrorMessage.FAILED_FIELD_INVARIANT, params);
    }
    return result;
  }

  /**
   * First checks the field is within a process scope, and that the whole
   * communication fields invariant holds. Next, type check the output/dot 
   * field expression. Then, get the right type projection from the channel 
   * type depending on the current field position. After that, checks 
   * whether the projected channel type unifies with the given field expression.
   * Finally, returns a singleton name type pair in the list containing a 
   * fresh variable name and its projected type. This pair can be used by 
   * others to have a complete communication signature.
   *
   *@law C.15.3, C.15.4
   */
  @Override
  public List<NameTypePair> visitDotField(DotField term)
  {
    List<NameTypePair> result = factory().list();

    // communications can only appear within a process paragrph
    checkActionParaScope(term, channelName_);

    // form the basis for all error messages: process where comm. appears + channel name.
    List<Object> params = factory().list();
    params.add(getCurrentProcessName());
    params.add(getCurrentActionName());
    params.add(channelName_);

    if (channelFieldsWellFormed())
    {
      // typecheck the expression
      Type2 exprType = term.getExpr().accept(exprChecker());

      // extract its type from the channel type and position indexes.
      Type2 fieldType = getFieldTypeProjection();

      // if no type error on expression, unify types
      if (!(exprType instanceof UnknownType))
      {
        Type2 expectedU = GlobalDefs.unwrapType(fieldType);
        Type2 foundU = GlobalDefs.unwrapType(exprType);
        UResult unified = unify(foundU, expectedU);
        if (unified.equals(UResult.FAIL))
        {
          params.add(expectedU);
          params.add(foundU);
          error(term, ErrorMessage.CHANNEL_PARAM_NOT_UNIFY, params);
        }
        else
        {
          NameTypePair ntp = factory().createNameTypePair(
            factory().createZDeclName(createFreshDotFieldName()), expectedU);
          result.add(ntp);
        }
      }
    }
    else
    {
      params.add("output field");
      params.add(fieldPosition_);
      error(term, ErrorMessage.FAILED_FIELD_INVARIANT, params);
    }
    return result;
  }
  
  /* Método auxiliar que instancia o tipo de um canal genérico
   */
//  private Type replaceChannelType(DeclName genName, Type typeExpr, Type typeChan) {
//    Type result = null;
//    
//    if(typeChan instanceof ProdType) {
//      List<Type2> types = ((ProdType)typeChan).getType();
//      List<Type2> typesResult = new ArrayList<Type2>();
//      for(Type2 type : types) {
//        Type res = replaceChannelType(genName, typeExpr,  type);
//        // TODO: Check: Why not unwrapType?
//        typesResult.add((Type2)res);
//      }
//      result = factory().createProdType(typesResult);
//    }
//    else if(typeChan instanceof PowerType) {
//      Type2 type = ((PowerType)typeChan).getType();
//      Type res = replaceChannelType(genName, typeExpr, type);
//      result = factory().createPowerType((Type2)res);
//    }
//    else if(typeChan instanceof GenParamType) {
//      ZDeclName nameType = ((GenParamType)typeChan).getName();
//      if (compareDeclName(nameType, genName, true)) {
//        result = typeExpr;
//      } else {
//        result = typeChan;
//      }
//    }
//    else {
//      result = typeChan;
//    }
//    
//    return result;
//  }
}
