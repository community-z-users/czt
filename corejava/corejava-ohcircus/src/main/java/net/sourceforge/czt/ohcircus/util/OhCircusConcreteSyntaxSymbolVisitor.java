/*
 * CircusTimeConcreteSyntaxSymbolVisitor.java
 *
 * Created on 08 June 2006, 15:53
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */
package net.sourceforge.czt.ohcircus.util;


import net.sourceforge.czt.circus.util.CircusConcreteSyntaxSymbol;
import net.sourceforge.czt.ohcircus.ast.*;
import net.sourceforge.czt.ohcircus.visitor.*;

import net.sourceforge.czt.z.ast.RefExpr;
import net.sourceforge.czt.z.util.IsEmptyNameList;
import net.sourceforge.czt.z.util.StandardZ;

/**
 * This visitor classifies a given AST node as a concrete syntax
 * symbol {@link CircusConcreteSyntaxSymbol}.  This can be used by the JEdit and
 * Eclipse plugins to produce an outline view (or structure tree) of
 * the source.
 *
 * @author leo
 */
public class OhCircusConcreteSyntaxSymbolVisitor
  implements OhCircusVisitor<OhCircusConcreteSyntaxSymbol>
{

  private Utils utils_;

  public OhCircusConcreteSyntaxSymbolVisitor()
  {
    utils_ = new UtilsImpl();
  }

  public OhCircusConcreteSyntaxSymbolVisitor(Utils utils)
  {
    utils_ = utils;
  }


/* Support for OhCircus */ 
  
  
//TODO : To add other OhCircus symbols according to the grammar (visitor implementation)  
  
  
  

@Override
public OhCircusConcreteSyntaxSymbol visitVisibilityList(VisibilityList term) {
	return OhCircusConcreteSyntaxSymbol.OHCIRCUS_VISIBILITY;
}

@Override
public OhCircusConcreteSyntaxSymbol visitOhCircusMethodSignatureList(
		OhCircusMethodSignatureList term) {
	return OhCircusConcreteSyntaxSymbol.METHOD_SIGNATURE_LIST;
}

@Override
public OhCircusConcreteSyntaxSymbol visitOhCircusClassRefList(
		OhCircusClassRefList term) {
	return OhCircusConcreteSyntaxSymbol.OHCIRCUS_CLASS_REF_LIST;
}

@Override
public OhCircusConcreteSyntaxSymbol visitMuMethod(MuMethod term) {
	return OhCircusConcreteSyntaxSymbol.MU_METHOD;
}

@Override
public OhCircusConcreteSyntaxSymbol visitVarDeclOhCircusCommand(
		VarDeclOhCircusCommand term) {
	return OhCircusConcreteSyntaxSymbol.OHCIRCUS_VAR_CMD;
}

@Override
public OhCircusConcreteSyntaxSymbol visitCallMethod(CallMethod term) {
	return OhCircusConcreteSyntaxSymbol.CALL_METHOD;
}

@Override
public OhCircusConcreteSyntaxSymbol visitOhCircusGuardedCommand(
		OhCircusGuardedCommand term) {
	return OhCircusConcreteSyntaxSymbol.GUARDED_METHOD;
}

@Override
public OhCircusConcreteSyntaxSymbol visitOhCircusDot(OhCircusDot term) {
	return OhCircusConcreteSyntaxSymbol.OHCIRCUS_DOT;
	
}

@Override
public OhCircusConcreteSyntaxSymbol visitLetMuMethod(LetMuMethod term) {
	return OhCircusConcreteSyntaxSymbol.LETMU_METHOD;
}

@Override
public OhCircusConcreteSyntaxSymbol visitDoOhCircusGuardedCommand(
		DoOhCircusGuardedCommand term) {
	return OhCircusConcreteSyntaxSymbol.OHCIRCUS_DO_CMD;
}

@Override
public OhCircusConcreteSyntaxSymbol visitInitialState(InitialState term) {
	return OhCircusConcreteSyntaxSymbol.INITIAL_STATE;
}

@Override
public OhCircusConcreteSyntaxSymbol visitParamMethod(ParamMethod term) {
	return OhCircusConcreteSyntaxSymbol.PARAM_METHOD;
}

@Override
public OhCircusConcreteSyntaxSymbol visitGuardedMethod(GuardedMethod term) {
	return OhCircusConcreteSyntaxSymbol.GUARDED_METHOD;
}

@Override
public OhCircusConcreteSyntaxSymbol visitOhCircusClassType(
		OhCircusClassType term) {
	return OhCircusConcreteSyntaxSymbol.OHCIRCUS_CLASS_TYPE;
}

@Override
public OhCircusConcreteSyntaxSymbol visitOhCircusMethodList(
		OhCircusMethodList term) {
	return OhCircusConcreteSyntaxSymbol.METHOD_LIST;
}

@Override
public OhCircusConcreteSyntaxSymbol visitOhCircusClassSignature(
		OhCircusClassSignature term) {
	return OhCircusConcreteSyntaxSymbol.OHCIRCUS_CALSS_SIGNATURE;
}

@Override
public OhCircusConcreteSyntaxSymbol visitIfOhCircusGuardedCommand(
		IfOhCircusGuardedCommand term) {
	return OhCircusConcreteSyntaxSymbol.OHCIRCUS_COMMAND;
}

@Override
public OhCircusConcreteSyntaxSymbol visitOhCircusMethodSignature(
		OhCircusMethodSignature term) {
	return OhCircusConcreteSyntaxSymbol.METHOD_SIGNATURE;
}

@Override
public OhCircusConcreteSyntaxSymbol visitPredExpr(PredExpr term) {
	return OhCircusConcreteSyntaxSymbol.OHCIRCUS_PRED;
}

@Override
public OhCircusConcreteSyntaxSymbol visitOhCircusMethodType(
		OhCircusMethodType term) {
	return OhCircusConcreteSyntaxSymbol.METHOD_TYPE;
}

@Override
public OhCircusConcreteSyntaxSymbol visitOhCircusMethodPara(
		OhCircusMethodPara term) {
	return OhCircusConcreteSyntaxSymbol.METHOD_PARA;
}

@Override
public OhCircusConcreteSyntaxSymbol visitOhCircusClassPara(
		OhCircusClassPara term) {
	return OhCircusConcreteSyntaxSymbol.OHCIRCUS_CLASS_PARA;
}

@Override
public OhCircusConcreteSyntaxSymbol visitLetVarMethod(LetVarMethod term) {
	return OhCircusConcreteSyntaxSymbol.LETVAR_METHOD;
}

@Override
public OhCircusConcreteSyntaxSymbol visitState(State term) {
	return OhCircusConcreteSyntaxSymbol.OHCIRCUS_STATE;
}

@Override
public OhCircusConcreteSyntaxSymbol visitSchExprMethod(SchExprMethod term) {
	return OhCircusConcreteSyntaxSymbol.SCH_EXPR_METHOD;
}

@Override
public OhCircusConcreteSyntaxSymbol visitOhCircusClassSignatureList(
		OhCircusClassSignatureList term) {
	return OhCircusConcreteSyntaxSymbol.OHCIRCUS_CLASS_SIGNATURE_LIST;
}

@Override
public OhCircusConcreteSyntaxSymbol visitSeqMethod(SeqMethod term) {
	return OhCircusConcreteSyntaxSymbol.SEQ_METHOD;
}

@Override
public OhCircusConcreteSyntaxSymbol visitOhCircusClassRefType(
		OhCircusClassRefType term) {
	return OhCircusConcreteSyntaxSymbol.OHCIRCUS_CLASS_REF_TYPE;
}

@Override
public OhCircusConcreteSyntaxSymbol visitOhCircusClassRef(OhCircusClassRef term) {
	return OhCircusConcreteSyntaxSymbol.OHCIRCUS_CLASS_REF;
}

public interface Utils
extends IsEmptyNameList
{
}

public static class UtilsImpl
extends StandardZ
implements Utils
{
}
}
