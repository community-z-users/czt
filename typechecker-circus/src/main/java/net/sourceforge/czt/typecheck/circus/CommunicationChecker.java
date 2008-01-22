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

import java.util.ArrayList;
import java.util.List;
import net.sourceforge.czt.circus.ast.ChannelType;
import net.sourceforge.czt.circus.ast.CircusFieldList;
import net.sourceforge.czt.circus.ast.Communication;
import net.sourceforge.czt.circus.ast.DotField;
import net.sourceforge.czt.circus.ast.Field;
import net.sourceforge.czt.circus.ast.InputField;
import net.sourceforge.czt.circus.visitor.CommunicationVisitor;
import net.sourceforge.czt.circus.visitor.DotFieldVisitor;
import net.sourceforge.czt.circus.visitor.InputFieldVisitor;
import net.sourceforge.czt.typecheck.circus.util.GlobalDefs;
import net.sourceforge.czt.typecheck.z.impl.UnknownType;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.GenParamType;
import net.sourceforge.czt.z.ast.Name;
import net.sourceforge.czt.z.ast.NameTypePair;
import net.sourceforge.czt.z.ast.PowerType;
import net.sourceforge.czt.z.ast.ProdType;
import net.sourceforge.czt.z.ast.RefExpr;
import net.sourceforge.czt.z.ast.Signature;
import net.sourceforge.czt.z.ast.Type;
import net.sourceforge.czt.z.ast.Type2;
import net.sourceforge.czt.z.ast.ZExprList;

import static net.sourceforge.czt.typecheck.circus.util.GlobalDefs.prodType;

/**
 *
 * @author Leo Freitas
 */
public class CommunicationChecker extends Checker<List<NameTypePair>>
  implements CommunicationVisitor<List<NameTypePair>>,            
             DotFieldVisitor<List<NameTypePair>>,
             InputFieldVisitor<List<NameTypePair>>             
{
  /**
   * Pointer to the current field position within a communication list.
   * Synchronisation does not consider the value of this field.
   */
  private int fieldPos_ = 0; 
  
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
   * Communication channel name.
   */
  private Name channelName_ = null;
  
  /**
   * Communication channel type after generic parameters have been resolved.
   */
  private ChannelType channelType_ = null;  
  
  /**
   * Synchronisation channel name
   */
  protected final Name synchName_ = null;
  
  /**
   * Synchronisation channel (spurious) type.
   */
  protected final Type2 synchType_ = null;

  /** Creates a new instance of CommunicationChecker */
  public CommunicationChecker(TypeChecker typeChecker)
  {
    super(typeChecker);    
    synchName_ = factory().createSynchName();
    synchType_ = getType(synchName_);
    assert synchName_ != null && synchType_ != null;
    assert !(synchType_ instanceof UnknownType) : "Channel synchronisation type " +
      "must be known in the sect type environment before creating a communication checker.";
  }
  
  protected boolean isProdTypeComm()
  {
    // if previously evaluated, jusst used it. otherwise, recalculate it.
    boolean result = isProdType_ == null ? (channelType != null) : isProdType_;
    if (result)
    {
      // get the channel base type.
      Type2 baseType = channelType_.getType();
      assert baseType != null : "Invalid channel typechecking. base type is null.";          
      result = (baseType instanceof ProdType);      
    }    
    return result;
  }
  
  
  private enum CommFormatResolution { WellFormedSynch, WellFormedComm, CommNoFields, FieldSynch };  
  private static final CommFormatResolution[][] COMM_FORMAT_MATRIX =      
      {                     /* synch       comm */
        /* empty fields  */  { WellFormedSynch, CommNoFields   },  
        /* !empty fields */  { FieldSynch     , WellFormedComm } 
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

    // communications can only appear within a process paragrph
    checkProcessParaScope("communication", channelName_);
    
    // form the basis for all error messages: process where comm. appears + channel name.
    List<Term> params = factory().list(getCurrentProcessName(), channelName_);
    
    // typecheck the channel reference expression - resolve generic types
    RefExpr channelExpr = term.getChannelExpr();
    Type2 type = channelExpr.accept(exprChecker());
          
    if (type instanceof ChannelType)
    {
      fieldPosition_ = 0;      
      channelType_ = (ChannelType)type;            
      CircusFieldList fields = term.getCircusFieldList();                  
      fieldCount_ = fields.size();
      
      // decide whether this is a well formed communication, or 
      // else if it isn't, raise an error.
      CommFormatResolution commFormat = 
          COMM_FORMAT_MATRIX[(fields.isEmpty() ? 0 : 1)]
                            [(channelType_.equals(synchType_) ? 0 : 1)];      
      
      // originally the comm invariant is true. if a specific error is catched
      // in the case analysis, nothing else is reported. otherwise, we check
      // this flag after it to see whether to raise an extra error or not.
      boolean commFormatInv = true;
      
      isProdType_ = isProdTypeComm();
      assert isProdType_ != null;
      
      switch (commFormat)
      {
        case WellFormedSynch:
          // synchronisation isn't a product type, and field count is 0
          commFormatInv = (!isProdType_ && fieldCount_ == 0);
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
          commFormatInv = (fieldCount_ == 1 || 
                           (isProdType_ && 
                            fieldCount_ == prodType(baseType).getType().size()));
          
          // if there is a format error, raise it; otherwise carry on.
          if (commFormatInv)           
          {
            // lets deal with generic instantiation at communication .
            ZExprList zGenActuals = channelExpr.getExprList() == null ? null : 
              ZUtils.assertZExprList(channelExpr.getExprList());            
            
            if(zGenActuals != null && !zGenActuals.isEmpty()) 
            {
              assert false : "Not treating generic channels yet";
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
            for(Field fields : fields) {
              
              // analyse the communication field
              result.addAll(field.accept(commChecker()));
              fieldPosition_++;              
            }    
            
            assert (result.size() == fieldCount_) :
              "Invalid field list typechecking: wrong field count.";
            
            // check whether any of the input variables were declared with the same name.            
            assert false : "this is wrong! same names with unifiable types are not allowed. add method for this checkForDuplicateNames";
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
    NameTypePair usedChannel = factory().createNameTypePair(channelName_, channelType_);
    circusTypeEnv().addUsedChannels(false, usedChannel);
    
    // add the used channel name and its instantiated type to the communication
    // signature. if there is an error, we add a null element.
    Signature signature = factory().createSignature(result);
    signature.getNameTypePair().add(0, usedChannel);
    
    //CommunicationType commType = factory().createCommunicationType(channelName_)
    //addTypeAnn(term, commType);
    
    // a signature to the Communication term. first element is the channel type.    
    addSignatureAnn(term, signature);
    
    // reset the prod type flag
    isProdType_ = null;
      
    return result;
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
        prodType(channelType_).getType().size()));
    return fieldsFormatInv;
  }  
  
  protected Type2 getFieldTypeProjection() 
  {    
    assert isProdType_ != null : "cannot project on unknown channel type";
    assert fieldPosition_ < fieldCount_ : "no next field type to project on channel type";
    
    Typ2 result;
    if (isProdType_) 
    {
      // if the last field is being checked, get the remainder type; otherwise get just one
      ProdType type = prodType(channelType_);
      int count = (fieldPosition_ == fieldCount - 1) ? (type.getType().size() - fieldPosition_) : 1;    
      result = getProdTypeProjection(type.getType(), fieldPosition_, count);
    } 
    else
    {
      result = channelType_;
    }
    return result;
  }
  
  protected Type2 getOutputFieldTypeProjection() 
  {    
    assert isProdType_ != null && isProdType_ : "cannot project a non-product channel type";
    assert fieldPosition_ < fieldCount_ : "no next field type to project out product channel type";
    
    // if the last field is being checked, get the remainder type; otherwise get just one
    ProdType type = prodType(channelType_);
    int count = (fieldPosition_ == fieldCount - 1) ? (type.getType().size() - fieldPosition_) : 1;    
    return getProdTypeProjection(type.getType(), fieldPosition_, count);
  }
  
  // CParameter ::= ?N
  // CParameter ::= ?N : Predicate
  //ok - verificado em 15/09/2005 às 14:38
  public List<NameTypePair> visitInputField(InputField term)
  {
    Name varName = term.getVariableName();
    
    List<NameTypePair> result = factory().list();
        
    // communications can only appear within a process paragrph
    checkProcessParaScope("input field communication", channelName_);
    
    // form the basis for all error messages: process where comm. appears + channel name.
    List<Term> params = factory().list(getCurrentProcessName(), channelName_, 
      "input variable " + varName);        
    
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
      result.addAll(mkLocalVars(ntp));            
      
      // type check the restriction predicate, if any
      Pred pred = term.getRestriction();      
      if (pred != null)
      {
        UResult solved = pred.accept(predChecker());
        
        // if not solved in the first pass, do it again
        if (solved.equals(UResult.PARTIAL)) {
          solved = pred.accept(predChecker());
          assert solved == SUCC : "could not solve predicate in input field";
        }      
      }
    }
    else
    {  
      // failed field position invariant
      params.add(fieldPosition_);      
      error(term, ErrorMessage.FAILED_FIELD_INVARIANT, params);      
    }
    return result;
  }
  
  private static int freshDotId = 0;
  private static final String FRESH_INTERNAL_NAME_PREFIX = "$$!";
  protected String createFreshDotFieldName()
  {    
    String result = FRESH_NAME_PREFIX + channelName_.toString() + (freshDotId++);    
    return result;
  }
  
  // CParameter ::= .Expression
  //ok - verificado em 15/09/2005 às 14:35
  public List<NameTypePair> visitDotField(DotField term)
  {    
    List<NameTypePair> result = factory().list();
   
    // communications can only appear within a process paragrph
    checkProcessParaScope("output field communication", channelName_);
    
    // form the basis for all error messages: process where comm. appears + channel name.
    List<Term> params = factory().list(getCurrentProcessName(), channelName_, "output field");
    
    if (channelFieldsWellFormed())
    {
      // typecheck the expression
      Type2 exprType = term.getExpression().accept(exprChecker());

      // extract its type from the channel type and position indexes.
      Type2 fieldType = getFieldTypeProjection() ;

      // if no type error on expression, unify types
      if (!(exprType instanceof UnknownType)) 
      {
        Type2 expectedU = unwrapType(fieldType);
        Type2 foundU = unwrapType(exprType);
        UResult unified = unify(foundU, expectedU);        
        if (unified.equals(UResult.FAIL))
        {
          Object [] params = {getCurrentProcessName(), channelName_, expectedU, foundU};
          error(term, ErrorMessage.CHANNEL_PARAM_NOT_UNIFY, params);
        }
        else 
        {
          NameTypePair ntp = factory().createNameTypePair(
            factory().createZDeclName(createFreshDotFieldName()), expectedU)
          result.add(ntp);
        }
      }
    }
    else 
    {
      params.add(fieldPosition_);      
      error(term, ErrorMessage.FAILED_FIELD_INVARIANT, params);      
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
    for(NameTypePair pair : pairs)
    {
      if (!pair.getZName().getWord().startsWith(FRESH_INTERNAL_NAME_PREFIX))
        result.add(pair);      
    }
    return result;
  }

  /*
   * Método auxiliar que instancia o tipo de um canal genérico
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
