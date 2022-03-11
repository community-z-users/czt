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
import net.sourceforge.czt.typecheck.z.impl.UnknownType;
import net.sourceforge.czt.typecheck.z.util.UResult;
import net.sourceforge.czt.typecheck.z.util.GlobalDefs;
import net.sourceforge.czt.z.ast.GenericType;
import net.sourceforge.czt.z.ast.LocAnn;
import net.sourceforge.czt.z.ast.Name;
import net.sourceforge.czt.z.ast.NameTypePair;
import net.sourceforge.czt.z.ast.PowerType;
import net.sourceforge.czt.z.ast.Pred;
import net.sourceforge.czt.z.ast.ProdType;
import net.sourceforge.czt.z.ast.RefExpr;
import net.sourceforge.czt.z.ast.Signature;
import net.sourceforge.czt.z.ast.Type;
import net.sourceforge.czt.z.ast.Type2;

import net.sourceforge.czt.z.ast.ZName;

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

  // sets the flags to -1 to make sure they are properly initialised everywhere
  // i.e., assert them to be != -1 before using them.
  
  /**
   * Pointer to the current field position within a communication list.
   * Synchronisation does not consider the value of this field.
   */
  private int fieldPosition_ = -1;
  
  /**
   * Number of fields in a communication. For synchronisation, this value MUST be zero.
   * Despite this fact, synchronisation does return a signature containing the 
   * synchronisation channel name and its type.
   */
  private int fieldCount_ = -1;
  
  /**
   * Counts the number of input fields in a communication. This is used to calculate
   * the number of expected variables to be declared within the environment.
   */
  private int inputFieldCount_ = -1;
  /**
   * Counts the number of output fields in a communication. This is used to calculate
   * the number of expected variables to be declared within the environment.
   */
  private int outputFieldCount_ = -1;
  
  /**
   * This records the expected number of fields based on the declared channel type.
   * That is, if the channel type is a product type, the value is the number of types
   * within the ProdType of the channel. Otherwise, it is either 0 (for synchronisation
   * channels) or 1 for all other channel types.
   */
  private int expectedCount_ = -1;
  
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
   * Communication ussage as detected by the parser.
   */
  private CommUsage commUsage_ = null;
  /**
   *  The actual communication term (with the list of fields) - used for 
   *  pretty error messages purposes only.
   */
  private Communication comm_ = null;
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
   * with the computed value of the last delcared channel used. 
   * This way the calling visitor knows what to extract from the 
   * resolved type of this comm.
   */
  private NameTypePair lastUsedChannelDecl_ = null;

  /**
   * Synchronisation channel name
   */
  private final ZName synchName_;
  
  /**
   * Synchronisation channel (spurious) type.
   */
  private Type2 synchType_;

  /** Creates a new instance of CommunicationChecker */
  public CommunicationChecker(TypeChecker typeChecker)
  {
    super(typeChecker);
    synchName_ = factory().createSynchName();        
    synchType_ = null;      
  }  
  
  protected void resetAttributes()
  {
    // note that lastUsedChannelDecl_, synchType_ and synchName_ remains valid, 
    // so that the calling visitor knows what to extract from the resolved type 
    // of this comm.
    comm_ = null;
    commPattern_ = null;
    isProdType_ = null;
    channelName_ = null;
    channelType_ = null;
    commUsage_ = null;
    // leave at -1 to make sure can only be used after processing 
    // starts (i.e. after they are set to 0).
    fieldPosition_ = -1;
    fieldCount_ = -1;
    inputFieldCount_ = -1;
    outputFieldCount_ = -1;
    expectedCount_ = -1;
  }
  
  protected boolean attribuesWereInitialised()
  {
    return comm_ != null && 
      commPattern_ != null &&
      isProdType_ != null &&
      channelName_ != null &&
      channelType_ != null &&
      commUsage_ != null &&    
      fieldPosition_ != -1 &&
      fieldCount_ != -1 &&
      inputFieldCount_ != -1 &&
      outputFieldCount_ != -1 &&
      expectedCount_ != -1;
  }
  
  /**
   * Returns the synchronisation type for channels. The first time this type is 
   * looked up, the circus_prelude section must be visible.
   * 
   * @return
   */
  protected Type2 synchType()
  {
    if (synchType_ == null)
    {
      synchType_ = checkUnificationSpecialType(synchName_, factory().createSynchType());    
      
      assert (synchType_ instanceof PowerType) : "invalid synch type - not power type";
      
      // unwrap it
      synchType_ = GlobalDefs.powerType(synchType_).getType();
      
      // adds type annotation to these circus expressions 
      CircusUtils.SYNCH_CHANNEL_EXPR.accept(exprChecker());
    }
    return synchType_;
  }
  
  protected boolean isSynchType(Type type)
  {    
    return type.equals(synchType());
  }
  
  protected Type2 getChannelBaseType()
  {
    assert channelType_ != null : "cannot get base type of a null channel type";
    return channelType_.getType();
  }
  
  protected boolean isProdTypeComm()
  {
    // if previously evaluated, jusst used it. otherwise, recalculate it.
    boolean result = isProdType_ == null ? (channelType_ != null) : isProdType_;
    if (result)
    {
      // get the channel base type.
      Type2 baseType = getChannelBaseType();
      assert baseType != null : "Invalid channel typechecking. base type is null.";
      result = (baseType instanceof ProdType);
    }
    return result;
  }

  @Override
  protected NameTypePair lastUsedChannelDecl()
  {
    assert lastUsedChannelDecl_ != null : "cannot query for last used channel information before analysing any";
    return lastUsedChannelDecl_;
  }
  
  /**
   * Extract the list of product types within a the underlying channel type
   * being visited by the current communication by this visitor. If the underlying
   * type within the channel type is a ProdType, it returns the list of product types.
   * @return the list of product types or null if not a product type channel  type
   */
  protected List<Type2> getProdTypeTypes()
  {
    assert isProdType_ != null : "cannot check fields before knowing nature of channel type.";
    List<Type2> result = null;
    if (isProdType_ && channelType_ != null)
    {      
      result = GlobalDefs.prodType(getChannelBaseType()).getType();
    }
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
      (isProdType_ && fieldPosition_ <= getProdTypeTypes().size()));
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
      List<Type2> prodTypes = getProdTypeTypes();
      int count = (fieldPosition_ == fieldCount_ - 1) ? (prodTypes.size() - fieldPosition_) : 1;
      result = getProdTypeProjection(prodTypes, fieldPosition_, count);
    }
    else
    {
      result = getChannelBaseType();
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

  private String createFreshDotFieldName(LocAnn loc)
  {    
    String result;
    if (loc != null)
    {
      result = CircusUtils.createFullQualifiedName(
        FRESH_INTERNAL_NAME_PREFIX + channelName_.toString(), loc);
    }
    else
    {
      result = CircusUtils.createFullQualifiedName(FRESH_INTERNAL_NAME_PREFIX, freshDotId);
      freshDotId++;
    }    
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
   * If a communication term is generically typed, then we need to clone it 
   * with the actual generic type for the communication list used and update
   * the term accordingly.
   * @param term
   * @return
   */
  protected boolean isGenericallyTyped(Communication term)
  {    
    Type type = getGlobalType(term.getChannelExpr().getName());
    return (type instanceof GenericType);
  }
  
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
    comm_        = term;
    channelName_ = term.getChannelExpr().getName();
    commPattern_ = term.getCommPattern();
    commUsage_   = term.getCommUsage();
    channelType_ = factory().createChannelType(factory().createUnknownType());

    // communications can only appear within an action paragrph
    checkActionParaScope(term, channelName_);    
    
    // form the basis for all error messages: action where comm. appears + channel name.
    List<Object> params = factory().list();
    params.add(getCurrentProcessName());
    params.add(getCurrentActionName());
    params.add(comm_);
    
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
      inputFieldCount_ = 0;
      outputFieldCount_ = 0;      
      channelType_ = (ChannelType) type;
      CircusFieldList fields = term.getCircusFieldList();
      fieldCount_ = fields.size();      
      
      // decide whether this is a well formed communication, or 
      // else if it isn't, raise an error.
      CommFormatResolution commFormat =
        COMM_FORMAT_MATRIX[(fields.isEmpty() ? 0 : 1)][(isSynchType(getChannelBaseType()) ? 0 : 1)];

      isProdType_ = isProdTypeComm();
      
      //      if product type -> get the product type size
      // else if synch type   -> 0 
      // else                 -> 1
      expectedCount_ = isProdType_ ? getProdTypeTypes().size() : 
          commFormat.equals(CommFormatResolution.WellFormedSynch) ? 0 : 1;
      
      assert attribuesWereInitialised() : "wrong initialisation of communication attributes at Communication";
      switch (commFormat)
      {
        case WellFormedSynch:
          // synchronisation isn't a product type, and field count is 0.
          // also, check that the parsed CommPattern flag is correct.
          commFormatInv = (!isProdType_ && fieldCount_ == 0 &&
            commPattern_.equals(CommPattern.Synch) &&
            commUsage_.equals(CommUsage.Normal));
          if (commFormatInv)
          {
            result.add(factory().createNameTypePair(synchName_, synchType()));
          }
          break;

        case WellFormedComm:
          // communication is either with one field (i.e. c?x  for c: N or c: N x N)
          // or it MUST have all the fields explicitly, thus rulling out CSP_M
          // asymmetries: e.g., c: N x N x N , c?x?y  is (x, (y.1, y.2))
          //
          // NOTE: to consider such asymmetry, we would need:
          //       a) a weaker invariant: fieldCount_ <=  prodType(baseType).getType().size()
          //          (i.e., the field type is not necessarily the same as the projected channel type
          //           ex: c \in \nat \cross \nat \cross \nat and c!0?x, x \in \nat \cross \nat
          //       b) treatment on InputField to get the tail type for the last field
          //      
          //       the trouble is that it will generate non-unifiable SigmaExpr.
          //       (e.g., { ("c", (x, (y.1, y.2))), ("c", (x, y, z)) } )
          commFormatInv = ((fieldCount_ == 1 ||
            (isProdType_ &&
            fieldCount_ <= expectedCount_)) &&
            !commPattern_.equals(CommPattern.Synch));

          // if there is a format error, raise it (done after the case statement); otherwise carry on.
          if (commFormatInv)
          {          
            // analyse each communication field.
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

            // 4 = NUMBER_OF_VARIABLES_ADDED, e.g. c?x --> x, x', x?, x!: typeOf(c)            
            // so, if channel fields are well formed, then the field count must match.
            
            // In the presence of a type error, this invariant will be breached and 
            // flagged as a warning - i.e., if the code is wrong at the field level
            // and misses the case, at least the communication invariant being breached
            // will be raised to the user as a warning.
            //
            //   !(channelFieldsWellFormed() => (result.size() == ((inputFieldCount_ * 4) + outputFieldCount_)))
            // = (!channelFieldsWellFormed() && (result.size() != ((inputFieldCount_ * 4) + outputFieldCount_)))
            if (channelFieldsWellFormed() && (result.size() != ((inputFieldCount_ * 4) + outputFieldCount_)))
            {
              params.add((inputFieldCount_ * 4) + outputFieldCount_);
              params.add(inputFieldCount_);
              params.add(outputFieldCount_);
              params.add(result.size());
              warningManager().warn(term, WarningMessage.INVALID_COMMUNICATION_PATTERN_WRT_CHANNEL_TYPE, params);              
            }           

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
          params.add(fieldCount_);
          params.add(fields.size());          
          params.add(" "); 
          error(term, ErrorMessage.COMM_CHANNEL_FIELDS_ERROR, params);
          break;
        case FieldSynch:
          // synchronisation channels cannot have fields.
          assert !fields.isEmpty();
          params.add(fieldCount_);
          params.add(fields.size());          
          params.add("--- synchronisation channels cannot have fields");
          error(term, ErrorMessage.COMM_CHANNEL_FIELDS_ERROR, params);
          break;
      }
    }
    else
    {
      error(term, ErrorMessage.IS_NOT_CHANNEL_NAME, params);
    }

    // check invariant for good channels.
    if (commFormatInv)
    { 
      comm_ = (Communication)factory().deepCloneTerm(term);
      
      // for generically typed communications, clone their type and themselves
      // to go to the used channels and communication lists
      if (isGenericallyTyped(term))
      {
        channelType_ = (ChannelType)factory().deepCloneTerm(channelType_);        
      }
    } 
    else
    {
      params.add(channelType_);
      params.add(expectedCount_);
      params.add(fieldCount_);      
      if (commPattern_.equals(CommPattern.Synch) && !commUsage_.equals(CommUsage.Normal))
      {
        params.add("\n\tCommunication via synchronisation channels does not allow generic actuals.");
      }
      else
      {
        params.add(" ");
      }
      error(term, ErrorMessage.COMM_FIELDS_DONT_UNIFY, params);
    }
    
    // add this instantiated channel as a used channel in the calling scope.
    NameTypePair instantiatedChannelDecl = factory().createNameTypePair(channelName_, channelType_);        
    lastUsedChannelDecl_ = instantiatedChannelDecl;
    
    // add the used channel name and its instantiated type to the communication
    // signature. if there is an error, we add a null element.
    Signature signature = factory().createSignature(result);
    signature.getNameTypePair().add(0, instantiatedChannelDecl);
    
    // a signature to the Communication term. first element is the channel type.    
    //addSignatureAnn(term, signature);

    // communication has been cloned, so add the type and put it into the environment.
    CommunicationType commType = factory().getCircusFactory().
      createCommunicationType(signature);    
    addTypeAnn(comm_, commType);    
    //circusTypeEnv().addUsedCommunication(comm_);   
    
    // reset the attributes only valid for communication field analysis.   
    resetAttributes();
    
    return result;
  }
  
  @Override
  public List<NameTypePair> visitCircusCommunicationList(CircusCommunicationList term)
  {
    // Communication lists typechecking requests can only come from ChannelSets
    checkChannelSetScope(term);    
    
    int i = 1;
    List<NameTypePair> result = factory().list();
    for(Communication comm : term)
    { 
      // if already typechecked, get its value - e.g., if refered within a different channel set.
      // get the type from the commExpr rather than comm because we don't have fields        
      RefExpr commExpr = comm.getChannelExpr();      
      Type2 type = getType2FromAnns(commExpr); 

      // if not the right pattern, don't worry about type checking inside
      if (comm.getCommPattern().equals(CommPattern.ChannelSet))
      {           
        // if type is unknown
        if (type instanceof UnknownType)      
        {
          // typecheck the channel reference expression - resolve generic types        
          type = commExpr.accept(exprChecker());
        }
      }
      else
      {
        List<Object> params = factory().list();    
        params.add((((ExprChecker)exprChecker()).inProcessPara_ ? "process" : 
          (((ExprChecker)exprChecker()).inActionPara_ ? "action" : 
          (((ExprChecker)exprChecker()).inChannelSetPara_ ? "channel set" : "???"))));
        params.add((((ExprChecker)exprChecker()).inActionPara_ ? 
          (getCurrentProcessName().toString() + "\n\tAction...:" +
           getCurrentActionName().toString()) :
          (((ExprChecker)exprChecker()).inProcessPara_ ? getCurrentProcessName() :
              (((ExprChecker)exprChecker()).inChannelSetPara_ ? getCurrentChannelSetName() : "error"))));
        params.add(comm + ": " + type + " -> " + comm.getCommPattern());
        params.add(i);
        error(comm, ErrorMessage.NON_CHANNELSET_IN_COMMLIST, params);                
      }
      
      // if type not a channel type, raise an error;       
      // otherwise, we are done for t his comm
      if (!(type instanceof ChannelType))
      {
        List<Object> params = factory().list();    
        params.add((((ExprChecker)exprChecker()).inProcessPara_ ? "process" : 
          (((ExprChecker)exprChecker()).inActionPara_ ? "action" : 
          (((ExprChecker)exprChecker()).inChannelSetPara_ ? "channel set" : "???"))));
        params.add((((ExprChecker)exprChecker()).inActionPara_ ? 
          (getCurrentProcessName().toString() + "\n\tAction...:" +
           getCurrentActionName().toString()) :
          (((ExprChecker)exprChecker()).inProcessPara_ ? getCurrentProcessName() :
              (((ExprChecker)exprChecker()).inChannelSetPara_ ? getCurrentChannelSetName() : "error"))));
        params.add(commExpr);
        params.add(i);
        params.add(type);
        error(term, ErrorMessage.IS_NOT_CHANNEL_NAME_IN_CHANNELSET, params);
      }
      
      NameTypePair ntp = factory().createNameTypePair(commExpr.getName(), type);
      result.add(ntp);
      i++;
    }       
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
      assert attribuesWereInitialised() : "wrong initialisation of communication attributes at InputField";
      inputFieldCount_++;
      
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
      result.addAll(addStateVars(ntp, fieldPosition_+1));

      // type check the restriction predicate, if any
      Pred pred = term.getRestriction();
      if (pred != null)
      {
        typeCheckPred(term, pred);        
      }
    }
    else
    {
      // form the basis for all error messages: process where comm. appears + channel name.
      List<Object> params = factory().list();
      params.add(getCurrentProcessName());
      params.add(getCurrentActionName());
      params.add(comm_);
      params.add(channelType_);
      params.add(fieldPosition_+1);
      params.add("input");
      error(term, ErrorMessage.COMM_FIELD_FAILED_INVARIANT, params);
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
    params.add(comm_);
    params.add(channelType_);

    if (channelFieldsWellFormed())
    {
      assert attribuesWereInitialised() : "wrong initialisation of DotField attributes";
      outputFieldCount_++;
      
      // typecheck the expression
      Type2 exprType = term.getExpr().accept(exprChecker());

      // extract its type from the channel type and position indexes.
      Type2 fieldType = getFieldTypeProjection();

      // if no type error on expression, unify types
      if (!(exprType instanceof UnknownType))
      {
        Type2 expectedU = GlobalDefs.unwrapType(fieldType);
        Type2 foundU = GlobalDefs.unwrapType(exprType);
        UResult unified;
        
        // for boolean typed channels, schemas are interpred as predicates
        if (CircusUtils.isBooleanType(expectedU) &&
            referenceToSchema(exprType) != null)
        {          
          unified = UResult.SUCC;
        }
        // otherwise, just treat the field as types
        else
        {
          unified = unify(foundU, expectedU);
        }
        // if unification fails, raise a type error.
        if (!unified.equals(UResult.SUCC))
        {          
          params.add(fieldPosition_+1);// it is zero based - show one based.
          params.add(expectedU);
          params.add(foundU);
          params.add(CircusUtils.isOutputField(term) ? "Output" : "Dot");
          error(term, ErrorMessage.COMM_DOTFIELD_DONT_UNIFY, params);
        }
        else
        {
          NameTypePair ntp = factory().createNameTypePair(
            factory().createZDeclName(createFreshDotFieldName(GlobalDefs.nearestLocAnn(term))), expectedU);
          result.add(ntp);
        }
      }
    }
    else
    {      
      params.add(fieldPosition_+1);      
      params.add(CircusUtils.isOutputField(term) ? "output" : "dot");
      error(term, ErrorMessage.COMM_FIELD_FAILED_INVARIANT, params);
    }
    return result;
  }
    
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
