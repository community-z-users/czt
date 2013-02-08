/*
  Copyright (C) 2007 Mark Utting
  This file is part of the czt project.

  The czt project contains free software; you can redistribute it and/or modify
  it under the terms of the GNU General @Override public License as published by
  the Free Software Foundation; either version 2 of the License, or
  (at your option) any later version.

  The czt project is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General @Override public License for more details.

  You should have received a copy of the GNU General @Override public License
  along with czt; if not, write to the Free Software
  Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
*/

package net.sourceforge.czt.z.util;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.base.visitor.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.visitor.*;

/**
 * This visitor classifies a given AST node as a concrete syntax
 * symbol {@link ConcreteSyntaxSymbol}.  This is used by the JEdit and
 * Eclipse Z plugins to produce an outline view (or structure tree) of
 * the Z source.
 * 
 * @author Petra Malik
 */
public class SyntaxSymbolVisitor
  implements ZVisitor<ConcreteSyntaxSymbol>,
             ListTermVisitor<ConcreteSyntaxSymbol>
{
  @Override
  public ConcreteSyntaxSymbol visitListTerm(ListTerm<?> term)
  {
    return ConcreteSyntaxSymbol.LIST;
  }

  @Override public ConcreteSyntaxSymbol visitAndExpr(AndExpr term)
  {
    return ConcreteSyntaxSymbol.AND_EXPR;
  }

  @Override public ConcreteSyntaxSymbol visitAndPred(AndPred andPred)
  {
    return ConcreteSyntaxSymbol.AND_PRED;
  }

  @Override public ConcreteSyntaxSymbol visitApplExpr(ApplExpr applExpr)
  {
    return ConcreteSyntaxSymbol.APPL_EXPR;
  }

  @Override public ConcreteSyntaxSymbol visitAxPara(AxPara axPara)
  {
    return ConcreteSyntaxSymbol.AX_PARA;
  }

  @Override public ConcreteSyntaxSymbol visitBindExpr(BindExpr term)
  {
    return ConcreteSyntaxSymbol.BIND_EXPR;
  }

  @Override public ConcreteSyntaxSymbol visitBindSelExpr(BindSelExpr term)
  {
    return ConcreteSyntaxSymbol.BIND_SEL_EXPR;
  }

  @Override public ConcreteSyntaxSymbol visitBranch(Branch term)
  {
    return ConcreteSyntaxSymbol.BRANCH;
  }

  @Override public ConcreteSyntaxSymbol visitZBranchList(ZBranchList zBranchList)
  {
    return ConcreteSyntaxSymbol.BRANCH_LIST;
  }

  @Override public ConcreteSyntaxSymbol visitCompExpr(CompExpr term)
  {
    return ConcreteSyntaxSymbol.COMP_EXPR;
  }

  @Override public ConcreteSyntaxSymbol visitCondExpr(CondExpr term)
  {
    return ConcreteSyntaxSymbol.COND_EXPR;
  }

  @Override public ConcreteSyntaxSymbol visitConjPara(ConjPara conjPara)
  {
    return ConcreteSyntaxSymbol.CONJ_PARA;
  }

  @Override public ConcreteSyntaxSymbol visitConstDecl(ConstDecl term)
  {
    return ConcreteSyntaxSymbol.CONST_DECL;
  }

  @Override public ConcreteSyntaxSymbol visitDecorExpr(DecorExpr term)
  {
    return ConcreteSyntaxSymbol.DECOR_EXPR;
  }

  @Override public ConcreteSyntaxSymbol visitDirective(Directive term)
  {
    return ConcreteSyntaxSymbol.DIRECTIVE;
  }

  @Override public ConcreteSyntaxSymbol visitExists1Expr(Exists1Expr term)
  {
    return ConcreteSyntaxSymbol.EXIONE_EXPR;
  }

  @Override public ConcreteSyntaxSymbol visitExists1Pred(Exists1Pred term)
  {
    return ConcreteSyntaxSymbol.EXIONE_PRED;
  }

  @Override public ConcreteSyntaxSymbol visitExistsExpr(ExistsExpr term)
  {
    return ConcreteSyntaxSymbol.EXI_EXPR;
  }

  @Override public ConcreteSyntaxSymbol visitExistsPred(ExistsPred term)
  {
    return ConcreteSyntaxSymbol.EXI_PRED;
  }

  @Override public ConcreteSyntaxSymbol visitExprPred(ExprPred term)
  {
    return ConcreteSyntaxSymbol.EXPR_PRED;
  }

  @Override public ConcreteSyntaxSymbol visitFalsePred(FalsePred term)
  {
    return ConcreteSyntaxSymbol.FALSE_PRED;
  }

  @Override public ConcreteSyntaxSymbol visitForallExpr(ForallExpr term)
  {
    return ConcreteSyntaxSymbol.ALL_EXPR;
  }

  @Override public ConcreteSyntaxSymbol visitForallPred(ForallPred term)
  {
    return ConcreteSyntaxSymbol.ALL_PRED;
  }

  @Override public ConcreteSyntaxSymbol visitFreePara(FreePara term)
  {
    return ConcreteSyntaxSymbol.FREE_PARA;
  }

  @Override public ConcreteSyntaxSymbol visitFreetype(Freetype term)
  {
    return ConcreteSyntaxSymbol.FREETYPE;
  }

  @Override public ConcreteSyntaxSymbol visitGenericType(GenericType term)
  {
    return null;
  }

  @Override public ConcreteSyntaxSymbol visitGenParamType(GenParamType term)
  {
    return null;
  }

  @Override public ConcreteSyntaxSymbol visitGivenPara(GivenPara term)
  {
    return ConcreteSyntaxSymbol.GIVEN_PARA;
  }

  @Override public ConcreteSyntaxSymbol visitGivenType(GivenType term)
  {
    return null;
  }

  @Override public ConcreteSyntaxSymbol visitHideExpr(HideExpr term)
  {
    return ConcreteSyntaxSymbol.HIDE_EXPR;
  }

  @Override public ConcreteSyntaxSymbol visitIffExpr(IffExpr term)
  {
    return ConcreteSyntaxSymbol.IFF_EXPR;
  }

  @Override public ConcreteSyntaxSymbol visitIffPred(IffPred term)
  {
    return ConcreteSyntaxSymbol.IFF_PRED;
  }

  @Override public ConcreteSyntaxSymbol visitImpliesExpr(ImpliesExpr term)
  {
    return ConcreteSyntaxSymbol.IMPL_EXPR;
  }

  @Override public ConcreteSyntaxSymbol visitImpliesPred(ImpliesPred term)
  {
    return ConcreteSyntaxSymbol.IMPL_PRED;
  }

  @Override public ConcreteSyntaxSymbol visitInclDecl(InclDecl term)
  {
    return ConcreteSyntaxSymbol.INCL_DECL;
  }

  @Override public ConcreteSyntaxSymbol visitInStroke(InStroke term)
  {
    return null;
  }

  @Override public ConcreteSyntaxSymbol visitLambdaExpr(LambdaExpr term)
  {
    return ConcreteSyntaxSymbol.LAMBDA_EXPR;
  }

  @Override public ConcreteSyntaxSymbol visitLatexMarkupPara(LatexMarkupPara term)
  {
    return ConcreteSyntaxSymbol.LATEX_MARKUP_PARA;
  }

  @Override public ConcreteSyntaxSymbol visitLetExpr(LetExpr term)
  {
    return ConcreteSyntaxSymbol.LET_EXPR;
  }

  @Override public ConcreteSyntaxSymbol visitLocAnn(LocAnn term)
  {
    return null;
  }

  @Override public ConcreteSyntaxSymbol visitMemPred(MemPred term)
  {
    return ConcreteSyntaxSymbol.REL_PRED;
  }

  @Override public ConcreteSyntaxSymbol visitMuExpr(MuExpr term)
  {
    return ConcreteSyntaxSymbol.MU_EXPR;
  }

  @Override public ConcreteSyntaxSymbol visitNameSectTypeTriple(NameSectTypeTriple term)
  {
    return ConcreteSyntaxSymbol.NAME_SECT_TYPE_TRIPLE;
  }

  @Override public ConcreteSyntaxSymbol visitNameTypePair(NameTypePair term)
  {
    return ConcreteSyntaxSymbol.NAME_TYPE_PAIR;
  }

  @Override public ConcreteSyntaxSymbol visitNarrPara(NarrPara term)
  {
    return ConcreteSyntaxSymbol.NARR_PARA;
  }

  @Override public ConcreteSyntaxSymbol visitNarrSect(NarrSect term)
  {
    return ConcreteSyntaxSymbol.NARR_SECT;
  }

  @Override public ConcreteSyntaxSymbol visitNegExpr(NegExpr term)
  {
    return ConcreteSyntaxSymbol.NEG_EXPR;
  }


  @Override public ConcreteSyntaxSymbol visitNegPred(NegPred term)
  {
    return ConcreteSyntaxSymbol.NEG_PRED;
  }

  @Override public ConcreteSyntaxSymbol visitNewOldPair(NewOldPair term)
  {
    return ConcreteSyntaxSymbol.NAME_NAME_PAIR;
  }

  @Override public ConcreteSyntaxSymbol visitNextStroke(NextStroke term)
  {
    return null;
  }

  @Override public ConcreteSyntaxSymbol visitNumExpr(NumExpr term)
  {
    return ConcreteSyntaxSymbol.NUM_EXPR;
  }

  @Override public ConcreteSyntaxSymbol visitNumStroke(NumStroke term)
  {
    return null;
  }

  @Override public ConcreteSyntaxSymbol visitOperand(Operand term)
  {
    return null;
  }

  @Override public ConcreteSyntaxSymbol visitOperator(Operator term)
  {
    return null;
  }

  @Override public ConcreteSyntaxSymbol visitOptempPara(OptempPara term)
  {
    return ConcreteSyntaxSymbol.OPTEMP_PARA;
  }

  @Override public ConcreteSyntaxSymbol visitOrExpr(OrExpr term)
  {
    return ConcreteSyntaxSymbol.OR_EXPR;
  }


  @Override public ConcreteSyntaxSymbol visitOrPred(OrPred term)
  {
    return ConcreteSyntaxSymbol.OR_PRED;
  }

  @Override public ConcreteSyntaxSymbol visitOutStroke(OutStroke term)
  {
    return null;
  }

  @Override public ConcreteSyntaxSymbol visitParenAnn(ParenAnn term)
  {
    return null;
  }

  @Override public ConcreteSyntaxSymbol visitParent(Parent term)
  {
    return ConcreteSyntaxSymbol.PARENT;
  }

  @Override public ConcreteSyntaxSymbol visitPipeExpr(PipeExpr term)
  {
    return ConcreteSyntaxSymbol.PIPE_EXPR;
  }

  @Override public ConcreteSyntaxSymbol visitPowerExpr(PowerExpr term)
  {
    return ConcreteSyntaxSymbol.POWER_EXPR;
  }

  @Override public ConcreteSyntaxSymbol visitPowerType(PowerType term)
  {
    return null;
  }

  @Override public ConcreteSyntaxSymbol visitPreExpr(PreExpr term)
  {
    return ConcreteSyntaxSymbol.PRE_EXPR;
  }

  @Override public ConcreteSyntaxSymbol visitProdExpr(ProdExpr term)
  {
    return ConcreteSyntaxSymbol.PROD_EXPR;
  }

  @Override public ConcreteSyntaxSymbol visitProdType(ProdType term)
  {
    return null;
  }

  @Override public ConcreteSyntaxSymbol visitProjExpr(ProjExpr term)
  {
    return ConcreteSyntaxSymbol.PROJ_EXPR;
  }

  @Override public ConcreteSyntaxSymbol visitRefExpr(RefExpr refExpr)
  {
    return ConcreteSyntaxSymbol.REF_EXPR;
  }

  @Override public ConcreteSyntaxSymbol visitRenameExpr(RenameExpr term)
  {
    return ConcreteSyntaxSymbol.RENAME_EXPR;
  }

  @Override public ConcreteSyntaxSymbol visitSchemaType(SchemaType term)
  {
    return null;
  }

  @Override public ConcreteSyntaxSymbol visitSchExpr(SchExpr term)
  {
    return ConcreteSyntaxSymbol.SCH_EXPR;
  }

  @Override public ConcreteSyntaxSymbol visitSectTypeEnvAnn(SectTypeEnvAnn term)
  {
    return null;
  }

  //@Override public ConcreteSyntaxSymbol visitSectWarningEnvAnn(SectWarningEnvAnn term)
  //{
  //  return null;
  //}

  @Override public ConcreteSyntaxSymbol visitSetCompExpr(SetCompExpr term)
  {
    return ConcreteSyntaxSymbol.SET_COMP_EXPR;
  }

  @Override public ConcreteSyntaxSymbol visitSetExpr(SetExpr term)
  {
    return ConcreteSyntaxSymbol.SET_EXPR;
  }

  @Override public ConcreteSyntaxSymbol visitSignatureAnn(SignatureAnn term)
  {
    return null;
  }

  @Override public ConcreteSyntaxSymbol visitSignature(Signature term)
  {
    return null;
  }

  @Override public ConcreteSyntaxSymbol visitSpec(Spec term)
  {
    return ConcreteSyntaxSymbol.SPEC;
  }

  @Override public ConcreteSyntaxSymbol visitThetaExpr(ThetaExpr term)
  {
    return ConcreteSyntaxSymbol.THETA_EXPR;
  }

  @Override public ConcreteSyntaxSymbol visitTruePred(TruePred term)
  {
    return ConcreteSyntaxSymbol.TRUE_PRED;
  }

  @Override public ConcreteSyntaxSymbol visitTupleExpr(TupleExpr term)
  {
    return ConcreteSyntaxSymbol.TUPLE_EXPR;
  }

  @Override public ConcreteSyntaxSymbol visitTupleSelExpr(TupleSelExpr term)
  {
    return ConcreteSyntaxSymbol.TUPLE_SEL_EXPR;
  }

  @Override public ConcreteSyntaxSymbol visitTypeAnn(TypeAnn term)
  {
    return null;
  }

  @Override public ConcreteSyntaxSymbol visitUnparsedPara(UnparsedPara term)
  {
    return ConcreteSyntaxSymbol.UNPARSED_PARA;
  }

  @Override public ConcreteSyntaxSymbol visitUnparsedZSect(UnparsedZSect term)
  {
    return ConcreteSyntaxSymbol.UNPARSED_Z_SECT;
  }

  @Override public ConcreteSyntaxSymbol visitVarDecl(VarDecl term)
  {
    return ConcreteSyntaxSymbol.VAR_DECL;
  }

  @Override public ConcreteSyntaxSymbol visitZDeclList(ZDeclList term)
  {
    return ConcreteSyntaxSymbol.DECL_LIST;
  }

  @Override public ConcreteSyntaxSymbol visitZExprList(ZExprList term)
  {
    return ConcreteSyntaxSymbol.EXPR_LIST;
  }

  @Override public ConcreteSyntaxSymbol visitZFreetypeList(ZFreetypeList term)
  {
    return ConcreteSyntaxSymbol.FREETYPE_LIST;
  }

  @Override public ConcreteSyntaxSymbol visitZNumeral(ZNumeral term)
  {
    return ConcreteSyntaxSymbol.NUMERAL;
  }

  @Override public ConcreteSyntaxSymbol visitZName(ZName term)
  {
    return ConcreteSyntaxSymbol.NAME;
  }

  @Override public ConcreteSyntaxSymbol visitZNameList(ZNameList term)
  {
    return ConcreteSyntaxSymbol.NAME_LIST;
  }

  @Override public ConcreteSyntaxSymbol visitZParaList(ZParaList term)
  {
    return ConcreteSyntaxSymbol.PARA_LIST;
  }

  @Override public ConcreteSyntaxSymbol visitZRenameList(ZRenameList term)
  {
    return ConcreteSyntaxSymbol.RENAME_LIST;
  }

  @Override public ConcreteSyntaxSymbol visitZSchText(ZSchText term)
  {
    return ConcreteSyntaxSymbol.SCH_TEXT;
  }

  @Override public ConcreteSyntaxSymbol visitZStrokeList(ZStrokeList term)
  {
    return ConcreteSyntaxSymbol.STROKE_LIST;
  }

  @Override public ConcreteSyntaxSymbol visitZSect(ZSect term)
  {
    return ConcreteSyntaxSymbol.SECT;
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
