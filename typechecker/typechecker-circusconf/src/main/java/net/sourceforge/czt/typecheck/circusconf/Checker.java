/*
Copyright (C) 2005, 2006, 2007, 2008 Leo Freitas
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
package net.sourceforge.czt.typecheck.circusconf;


/**
 * Derived superclass of all XXXChecker classes (i.e., one for each syntactic 
 * category). It provides general facilities for the derived checkers. This 
 * usually includes typeing environment lookup and update, factory methods,
 * syntax checks, and so on.
 *
 * @param R 
 * @author Leo Freitas
 */
public abstract class Checker<R>
  extends net.sourceforge.czt.typecheck.circus.Checker<R>
{
//
//  /**
//   * As mu actions could be parameterised, but only when at the beginning of
//   * a action paragraph, we keep a count over it to make sure inner parameterised
//   * mu actions are not allowed. This doesn't happen with ParamAction because the
//   * parser does not allow it; but the same is not the case for MuActions, which 
//   * when without parameters, can appear anywhere. The count is reset at visitActionPara
//   * and incremented at each term.accept(actionChecker), which is centralised in the
//   * #visit(CircusAction) method below.
//   */
//  private int actionCheckerVisitCount_;
//
  public Checker(TypeChecker typeChecker)
  {
    super(typeChecker);
  }


//  
//  protected SignatureList instantiate(SignatureList sigList)
//  {
//    SignatureList result;
//    if (sigList instanceof ZSignatureList)
//    {
//      ZSignatureList zSigList = (ZSignatureList)sigList;            
//      ZSignatureList instZSigList = factory().getCircusFactory().createZSignatureList();
//      for(Signature sig : zSigList)
//      {
//        Signature instZSig = instantiate(sig);
//        instZSigList.add(instZSig);
//      }
//      result = instZSigList;
//    }
//    else if (sigList instanceof ActionSignatureList)
//    {
//      ActionSignatureList actionSigList = (ActionSignatureList)sigList;            
//      ActionSignatureList instActionSigList = factory().getCircusFactory().createActionSignatureList();
//      for(ActionSignature sig : actionSigList)
//      {
//        ActionSignature instActionSig = instantiate(sig);
//        instActionSigList.add(instActionSig);
//      }
//      result = instActionSigList;
//    }
//    else if (sigList instanceof ProcessSignatureList)
//    {
//      ProcessSignatureList processSigList = (ProcessSignatureList)sigList;            
//      ProcessSignatureList instProcessSigList = factory().getCircusFactory().createProcessSignatureList();
//      for(ProcessSignature sig : processSigList)
//      {
//        ProcessSignature instProcessSig = instantiate(sig);
//        instProcessSigList.add(instProcessSig);
//      }
//      result = instProcessSigList;
//    }
//    else
//    {      
//      throw new UnsupportedAstClassException("Unknown Circus signature list to instantiate generic types - " + sigList.getClass().getSimpleName());
//    }
//    return result;
//  }
//  

//  protected void error(Term term, ErrorMessage errorMsg, Object... params)
//  {
//    ErrorAnn errorAnn = this.errorAnn(term, errorMsg, params);
//    error(term, errorAnn);
//  }
//
//  protected void error(Term term, ErrorMessage errorMsg, List<Object> params)
//  {
//    error(term, errorMsg, params.toArray());
//  }
//
//  @Override
//  protected void error(Term term,
//    net.sourceforge.czt.typecheck.z.ErrorMessage error,
//    Object[] params)
//  {
//    ErrorAnn errorAnn = this.errorAnn(term, error.toString(), params);
//    error(term, errorAnn);
//  }
//
//  protected ErrorAnn errorAnn(Term term, ErrorMessage error, Object... params)
//  {
//    ErrorAnn errorAnn = new ErrorAnn(error.toString(), params, sectInfo(),
//      sectName(), GlobalDefs.nearestLocAnn(term), markup());
//    return errorAnn;
//  }
//
//  @Override
//  protected ErrorAnn errorAnn(Term term, String error, Object[] params)
//  {
//    // this method is very important to make sure the right "ErrorAnn" is created!
//    ErrorAnn errorAnn = new ErrorAnn(error, params, sectInfo(),
//      sectName(), GlobalDefs.nearestLocAnn(term),
//      markup());
//    return errorAnn;
//  }
//
//  /**
//   * <p>
//   * These isometric resolution matrixes are used to figure out where is the
//   * problem for parameterised calls, if any. To do this, we check the signature
//   * of the calling action type against the CallAction expressions.
//   * </p>
//   * <p>
//   * The first CALL_TYPE matrix distinguishes normal calls from either non-parameterised 
//   * calls or wrong number of parameters, where an inconclusive solutions leads
//   * to the next CALL_PARAMS matrix. 
//   * </p>
//   * <p>
//   * Finally, the CALL_PARAMS matrix further distinguishes normal parameterised calls 
//   * from call with either wrong number of parameters, or non-unifiable calling types
//   * with respect to the action signature.
//   * </p>
//   * <p>
//   * This trick avoids too many if/else statements, clarifies the code, and
//   * allegedly is faster in general since ifs are all resolved at once (this case 
//   * at each matrix). The same solution applies for action and process calls.
//   * </p>
//   */
//  protected enum CallResolution
//  {
//
//    NormalCall,
//    NormalParamCall,
//    NotParameterisedCall,
//    WrongNumberParameters,
//    IncompatibleParamType,
//    Inconclusive
//  }
//
//  
//         [][] CALL_TYPE = 
//      {                             /* sig.isEmpty                           !sig.isEmpty  */
//        /* call.isEmpty          */  { CallResolution.NormalCall           , CallResolution.WrongNumberParameters },  
//        /* !call.isEmpty         */  { CallResolution.NotParameterisedCall , CallResolution.Inconclusive          } 
//      };//                                                        |        
//        //                                       |----------------|
//        //                                       v 
//  //protected static final CallResolution[][] CALL_PARAMS = 
//  //    {                             /* sig.size  = call.size                 sig.size != call.size */
//  //      /* paramUnify(sig, call) */  { CallResolution.NormalParamCall      , CallResolution.WrongNumberParameters },  
//  //      /* !paramUnify(sig, call)*/  { CallResolution.IncompatibleParamType, CallResolution.WrongNumberParameters } 
//  //   };
//  // PS: to maximise number of error detection, we do not use the CALL_PARAMS. It is here mostly for documenetaion.
//
//  @Override
//protected List<? extends Type2> checkActualParameters(ZExprList actuals)
//  {    
//  }
//
//  /**
//   * Checks the given call, either an action or process call, is well formed.
//   * That includes checking number of parameters, their types, the structure 
//   * of the underlying call, and so on. The resulting value is a list of error
//   * annotatiosn that MUST be raise by whoever call this method.   
//   * See checkCallActionConsistency for more detailed documentation.
//   * 
//   * @param call the call term
//   * @param resolvedFormals the resolved formals
//   * @param actuals the resolved actuals
//   * @return list of error annotations to be raised by the callee.
//   */
//  @Override
//protected List<ErrorAnn> checkCallParameters(Term call,
//    List<NameTypePair> resolvedFormals, ZExprList actuals, boolean checkProcessScope)
//  {

//  }
//
//  /**
//   * Checks the consistency of the call by checking that the call type from the
//   * current type environment correspond to the call name itself. It also checks
//   * the call actual parameters for type consistency with respect to the declared
//   * formals from the action type. This method is also used at post checking to
//   * guarantee mutually recursive actions are well typed. 
//   * <p>
//   * As during  postchecking it is not allowed to add error annotations, we 
//   * return an error annotation, if any.  This solution is not the neatest, 
//   * but the simplest. Tha is, instead of having two different methods, one for
//   * post checking and one for normal checking, doing the same work, we generalise 
//   * it and make the error ann result. Whoever call this method MUST raise the
//   * error, if any.
//   * </p>
//   * 
//   * to the 
//   * @param callType
//   * @param term
//   */
//  protected List<ErrorAnn> checkCallActionConsistency(Type2 callType, CallAction term)
//  {

//  }
//  
//  protected List<ErrorAnn> checkCallProcessConsistency(Type2 callType, CallProcess term, boolean checkProcessScope)
//  {

//  }
//

//  
//  /**
//   * This implements Manuela's "NoRep" function (see B.52, p.136).
//   * It is a stronger version of "z.Checker.checkForDuplicates", 
//   * which would accept declarations like "x: \nat; x: \num" since 
//   * both types would unify.
//   */
//  @Override
//protected void checkForDuplicateNames(ZNameList declNames, Term term)
//  {   
//  }
//  
}
