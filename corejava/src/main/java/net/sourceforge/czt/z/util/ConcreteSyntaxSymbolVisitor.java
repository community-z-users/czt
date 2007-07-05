/*
  Copyright (C) 2006, 2007 Mark Utting
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

package net.sourceforge.czt.z.util;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.base.visitor.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.util.*;
import net.sourceforge.czt.z.visitor.*;

/**
 * This visitor classifies a given AST node as a concrete syntax
 * symbol {@link ConcreteSyntaxSymbol}.  This is used by the JEdit and
 * Eclipse Z plugins to produce an outline view (or structure tree) of
 * the Z source.
 * 
 * @author Petra Malik
 */
public class ConcreteSyntaxSymbolVisitor
  implements ZVisitor<ConcreteSyntaxSymbol>,
             ListTermVisitor<ConcreteSyntaxSymbol>
{
  private Utils utils_;

  public ConcreteSyntaxSymbolVisitor()
  {
    utils_ = new UtilsImpl();
  }

  public ConcreteSyntaxSymbolVisitor(Utils utils)
  {
    utils_ = utils;
  }

  public ConcreteSyntaxSymbol visitListTerm(ListTerm term)
  {
    return ConcreteSyntaxSymbol.LIST;
  }

  public ConcreteSyntaxSymbol visitAndExpr(AndExpr term)
  {
    return ConcreteSyntaxSymbol.AND_EXPR;
  }

  public ConcreteSyntaxSymbol visitAndPred(AndPred andPred)
  {
    And and = andPred.getAnd();
    if (And.NL.equals(and)) {
      return ConcreteSyntaxSymbol.NL_AND_PRED;
    }
    if (And.Semi.equals(and)) {
      return ConcreteSyntaxSymbol.SEMI_AND_PRED;
    }
    if (And.Chain.equals(and)) {
      return ConcreteSyntaxSymbol.CHAIN_AND_PRED;
    }
    return ConcreteSyntaxSymbol.AND_PRED;
  }

  public ConcreteSyntaxSymbol visitApplExpr(ApplExpr applExpr)
  {
    if (applExpr.getMixfix()) {
      return ConcreteSyntaxSymbol.FUN_APPL_EXPR;
    }
    return ConcreteSyntaxSymbol.APPL_EXPR;
  }

  public ConcreteSyntaxSymbol visitAxPara(AxPara axPara)
  {
    final Box box = axPara.getBox();
    if (box == null || Box.AxBox.equals(box)) {
      if (utils_.isEmpty(axPara.getNameList())) {
        return ConcreteSyntaxSymbol.AX_PARA;
      }
      return ConcreteSyntaxSymbol.GENAX_PARA;
    }
    else if (Box.SchBox.equals(box)) {
      if (utils_.isEmpty(axPara.getNameList())) {
        return ConcreteSyntaxSymbol.SCH_PARA;
      }
      return ConcreteSyntaxSymbol.GENSCH_PARA;
    }
    else if (Box.OmitBox.equals(box)) {
      final ConstDecl constDecl =
        (ConstDecl) axPara.getZSchText().getZDeclList().get(0);
      final ZName declName = constDecl.getZName();
      final OperatorName operatorName = declName.getOperatorName();
      if (operatorName != null) {
        return ConcreteSyntaxSymbol.OPDEF_PARA;
      }
      if (utils_.isEmpty(axPara.getName())) {
        return ConcreteSyntaxSymbol.DEF_PARA;
      }
      return ConcreteSyntaxSymbol.GENDEF_PARA;
    }
    return null;
  }

  public ConcreteSyntaxSymbol visitBindExpr(BindExpr term)
  {
    return ConcreteSyntaxSymbol.BIND_EXPR;
  }

  public ConcreteSyntaxSymbol visitBindSelExpr(BindSelExpr term)
  {
    return ConcreteSyntaxSymbol.BIND_SEL_EXPR;
  }

  public ConcreteSyntaxSymbol visitBranch(Branch term)
  {
    return ConcreteSyntaxSymbol.BRANCH;
  }

  public ConcreteSyntaxSymbol visitZBranchList(ZBranchList zBranchList)
  {
    return ConcreteSyntaxSymbol.BRANCH_LIST;
  }

  public ConcreteSyntaxSymbol visitCompExpr(CompExpr term)
  {
    return ConcreteSyntaxSymbol.COMP_EXPR;
  }

  public ConcreteSyntaxSymbol visitCondExpr(CondExpr term)
  {
    return ConcreteSyntaxSymbol.COND_EXPR;
  }

  public ConcreteSyntaxSymbol visitConjPara(ConjPara conjPara)
  {
    if (utils_.isEmpty(conjPara.getNameList())) {
      return ConcreteSyntaxSymbol.CONJ_PARA;
    }
    return ConcreteSyntaxSymbol.GENCONJ_PARA;
  }

  public ConcreteSyntaxSymbol visitConstDecl(ConstDecl term)
  {
    return ConcreteSyntaxSymbol.CONST_DECL;
  }

  public ConcreteSyntaxSymbol visitDecorExpr(DecorExpr term)
  {
    return ConcreteSyntaxSymbol.DECOR_EXPR;
  }

  public ConcreteSyntaxSymbol visitDirective(Directive term)
  {
    return ConcreteSyntaxSymbol.DIRECTIVE;
  }

  public ConcreteSyntaxSymbol visitExists1Expr(Exists1Expr term)
  {
    return ConcreteSyntaxSymbol.EXIONE_EXPR;
  }

  public ConcreteSyntaxSymbol visitExists1Pred(Exists1Pred term)
  {
    return ConcreteSyntaxSymbol.EXIONE_PRED;
  }

  public ConcreteSyntaxSymbol visitExistsExpr(ExistsExpr term)
  {
    return ConcreteSyntaxSymbol.EXI_EXPR;
  }

  public ConcreteSyntaxSymbol visitExistsPred(ExistsPred term)
  {
    return ConcreteSyntaxSymbol.EXI_PRED;
  }

  public ConcreteSyntaxSymbol visitExprPred(ExprPred term)
  {
    return ConcreteSyntaxSymbol.EXPR_PRED;
  }

  public ConcreteSyntaxSymbol visitFalsePred(FalsePred term)
  {
    return ConcreteSyntaxSymbol.FALSE_PRED;
  }

  public ConcreteSyntaxSymbol visitForallExpr(ForallExpr term)
  {
    return ConcreteSyntaxSymbol.ALL_EXPR;
  }

  public ConcreteSyntaxSymbol visitForallPred(ForallPred term)
  {
    return ConcreteSyntaxSymbol.ALL_PRED;
  }

  public ConcreteSyntaxSymbol visitFreePara(FreePara term)
  {
    return ConcreteSyntaxSymbol.FREE_PARA;
  }

  public ConcreteSyntaxSymbol visitFreetype(Freetype term)
  {
    return ConcreteSyntaxSymbol.FREETYPE;
  }

  public ConcreteSyntaxSymbol visitGenericType(GenericType term)
  {
    return null;
  }

  public ConcreteSyntaxSymbol visitGenParamType(GenParamType term)
  {
    return null;
  }

  public ConcreteSyntaxSymbol visitGivenPara(GivenPara term)
  {
    return ConcreteSyntaxSymbol.GIVEN_PARA;
  }

  public ConcreteSyntaxSymbol visitGivenType(GivenType term)
  {
    return null;
  }

  public ConcreteSyntaxSymbol visitHideExpr(HideExpr term)
  {
    return ConcreteSyntaxSymbol.HIDE_EXPR;
  }

  public ConcreteSyntaxSymbol visitIffExpr(IffExpr term)
  {
    return ConcreteSyntaxSymbol.IFF_EXPR;
  }

  public ConcreteSyntaxSymbol visitIffPred(IffPred term)
  {
    return ConcreteSyntaxSymbol.IFF_PRED;
  }

  public ConcreteSyntaxSymbol visitImpliesExpr(ImpliesExpr term)
  {
    return ConcreteSyntaxSymbol.IMPL_EXPR;
  }

  public ConcreteSyntaxSymbol visitImpliesPred(ImpliesPred term)
  {
    return ConcreteSyntaxSymbol.IMPL_PRED;
  }

  public ConcreteSyntaxSymbol visitInclDecl(InclDecl term)
  {
    return ConcreteSyntaxSymbol.INCL_DECL;
  }

  public ConcreteSyntaxSymbol visitInStroke(InStroke term)
  {
    return null;
  }

  public ConcreteSyntaxSymbol visitLambdaExpr(LambdaExpr term)
  {
    return ConcreteSyntaxSymbol.LAMBDA_EXPR;
  }

  public ConcreteSyntaxSymbol visitLatexMarkupPara(LatexMarkupPara term)
  {
    return ConcreteSyntaxSymbol.LATEX_MARKUP_PARA;
  }

  public ConcreteSyntaxSymbol visitLetExpr(LetExpr term)
  {
    return ConcreteSyntaxSymbol.LET_EXPR;
  }

  public ConcreteSyntaxSymbol visitLocAnn(LocAnn term)
  {
    return null;
  }

  public ConcreteSyntaxSymbol visitMemPred(MemPred term)
  {
    return ConcreteSyntaxSymbol.REL_PRED;
  }

  public ConcreteSyntaxSymbol visitMuExpr(MuExpr term)
  {
    return ConcreteSyntaxSymbol.MU_EXPR;
  }

  public ConcreteSyntaxSymbol visitNameSectTypeTriple(NameSectTypeTriple term)
  {
    return ConcreteSyntaxSymbol.NAME_SECT_TYPE_TRIPLE;
  }

  public ConcreteSyntaxSymbol visitNameTypePair(NameTypePair term)
  {
    return ConcreteSyntaxSymbol.NAME_TYPE_PAIR;
  }

  public ConcreteSyntaxSymbol visitNarrPara(NarrPara term)
  {
    return ConcreteSyntaxSymbol.NARR_PARA;
  }

  public ConcreteSyntaxSymbol visitNarrSect(NarrSect term)
  {
    return ConcreteSyntaxSymbol.NARR_SECT;
  }

  public ConcreteSyntaxSymbol visitNegExpr(NegExpr term)
  {
    return ConcreteSyntaxSymbol.NEG_EXPR;
  }

  public ConcreteSyntaxSymbol visitNegPred(NegPred term)
  {
    return ConcreteSyntaxSymbol.NEG_PRED;
  }

  public ConcreteSyntaxSymbol visitNewOldPair(NewOldPair term)
  {
    return ConcreteSyntaxSymbol.NAME_NAME_PAIR;
  }

  public ConcreteSyntaxSymbol visitNextStroke(NextStroke term)
  {
    return null;
  }

  public ConcreteSyntaxSymbol visitNumExpr(NumExpr term)
  {
    return ConcreteSyntaxSymbol.NUM_EXPR;
  }

  public ConcreteSyntaxSymbol visitNumStroke(NumStroke term)
  {
    return null;
  }

  public ConcreteSyntaxSymbol visitOperand(Operand term)
  {
    return null;
  }

  public ConcreteSyntaxSymbol visitOperator(Operator term)
  {
    return null;
  }

  public ConcreteSyntaxSymbol visitOptempPara(OptempPara term)
  {
    return ConcreteSyntaxSymbol.OPTEMP_PARA;
  }

  public ConcreteSyntaxSymbol visitOrExpr(OrExpr term)
  {
    return ConcreteSyntaxSymbol.OR_EXPR;
  }


  public ConcreteSyntaxSymbol visitOrPred(OrPred term)
  {
    return ConcreteSyntaxSymbol.OR_PRED;
  }

  public ConcreteSyntaxSymbol visitOutStroke(OutStroke term)
  {
    return null;
  }

  public ConcreteSyntaxSymbol visitParenAnn(ParenAnn term)
  {
    return null;
  }

  public ConcreteSyntaxSymbol visitParent(Parent term)
  {
    return ConcreteSyntaxSymbol.PARENT;
  }

  public ConcreteSyntaxSymbol visitPipeExpr(PipeExpr term)
  {
    return ConcreteSyntaxSymbol.PIPE_EXPR;
  }

  public ConcreteSyntaxSymbol visitPowerExpr(PowerExpr term)
  {
    return ConcreteSyntaxSymbol.POWER_EXPR;
  }

  public ConcreteSyntaxSymbol visitPowerType(PowerType term)
  {
    return null;
  }

  public ConcreteSyntaxSymbol visitPreExpr(PreExpr term)
  {
    return ConcreteSyntaxSymbol.PRE_EXPR;
  }

  public ConcreteSyntaxSymbol visitProdExpr(ProdExpr term)
  {
    return ConcreteSyntaxSymbol.PROD_EXPR;
  }

  public ConcreteSyntaxSymbol visitProdType(ProdType term)
  {
    return null;
  }

  public ConcreteSyntaxSymbol visitProjExpr(ProjExpr term)
  {
    return ConcreteSyntaxSymbol.PROJ_EXPR;
  }

  public ConcreteSyntaxSymbol visitRefExpr(RefExpr refExpr)
  {
    if (refExpr.getMixfix()) {
      return ConcreteSyntaxSymbol.GENOP_APPL_EXPR;
    }
    if (refExpr.getExplicit() && refExpr.getZExprList().size() > 0) {
      return ConcreteSyntaxSymbol.GENREF_EXPR;
    }
    return ConcreteSyntaxSymbol.REF_EXPR;
  }

  public ConcreteSyntaxSymbol visitRenameExpr(RenameExpr term)
  {
    return ConcreteSyntaxSymbol.RENAME_EXPR;
  }

  public ConcreteSyntaxSymbol visitSchemaType(SchemaType term)
  {
    return null;
  }

  public ConcreteSyntaxSymbol visitSchExpr(SchExpr term)
  {
    return ConcreteSyntaxSymbol.SCH_EXPR;
  }

  public ConcreteSyntaxSymbol visitSectTypeEnvAnn(SectTypeEnvAnn term)
  {
    return null;
  }

  public ConcreteSyntaxSymbol visitSetCompExpr(SetCompExpr term)
  {
    return ConcreteSyntaxSymbol.SET_COMP_EXPR;
  }

  public ConcreteSyntaxSymbol visitSetExpr(SetExpr term)
  {
    return ConcreteSyntaxSymbol.SET_EXPR;
  }

  public ConcreteSyntaxSymbol visitSignatureAnn(SignatureAnn term)
  {
    return null;
  }

  public ConcreteSyntaxSymbol visitSignature(Signature term)
  {
    return null;
  }

  public ConcreteSyntaxSymbol visitSpec(Spec term)
  {
    return ConcreteSyntaxSymbol.SPEC;
  }

  public ConcreteSyntaxSymbol visitThetaExpr(ThetaExpr term)
  {
    return ConcreteSyntaxSymbol.THETA_EXPR;
  }

  public ConcreteSyntaxSymbol visitTruePred(TruePred term)
  {
    return ConcreteSyntaxSymbol.TRUE_PRED;
  }

  public ConcreteSyntaxSymbol visitTupleExpr(TupleExpr term)
  {
    return ConcreteSyntaxSymbol.TUPLE_EXPR;
  }

  public ConcreteSyntaxSymbol visitTupleSelExpr(TupleSelExpr term)
  {
    return ConcreteSyntaxSymbol.TUPLE_SEL_EXPR;
  }

  public ConcreteSyntaxSymbol visitTypeAnn(TypeAnn term)
  {
    return null;
  }

  public ConcreteSyntaxSymbol visitUnparsedPara(UnparsedPara term)
  {
    return ConcreteSyntaxSymbol.UNPARSED_PARA;
  }

  public ConcreteSyntaxSymbol visitUnparsedZSect(UnparsedZSect term)
  {
    return ConcreteSyntaxSymbol.UNPARSED_Z_SECT;
  }

  public ConcreteSyntaxSymbol visitVarDecl(VarDecl term)
  {
    return ConcreteSyntaxSymbol.VAR_DECL;
  }

  public ConcreteSyntaxSymbol visitZDeclList(ZDeclList term)
  {
    return ConcreteSyntaxSymbol.DECL_LIST;
  }

  public ConcreteSyntaxSymbol visitZExprList(ZExprList term)
  {
    return ConcreteSyntaxSymbol.EXPR_LIST;
  }

  public ConcreteSyntaxSymbol visitZFreetypeList(ZFreetypeList term)
  {
    return ConcreteSyntaxSymbol.FREETYPE_LIST;
  }

  public ConcreteSyntaxSymbol visitZNumeral(ZNumeral term)
  {
    return ConcreteSyntaxSymbol.NUMERAL;
  }

  public ConcreteSyntaxSymbol visitZName(ZName term)
  {
    return ConcreteSyntaxSymbol.NAME;
  }

  public ConcreteSyntaxSymbol visitZNameList(ZNameList term)
  {
    return ConcreteSyntaxSymbol.NAME_LIST;
  }

  public ConcreteSyntaxSymbol visitZParaList(ZParaList term)
  {
    return ConcreteSyntaxSymbol.PARA_LIST;
  }

  public ConcreteSyntaxSymbol visitZRenameList(ZRenameList term)
  {
    return ConcreteSyntaxSymbol.RENAME_LIST;
  }

  public ConcreteSyntaxSymbol visitZSchText(ZSchText term)
  {
    return ConcreteSyntaxSymbol.SCH_TEXT;
  }

  public ConcreteSyntaxSymbol visitZStrokeList(ZStrokeList term)
  {
    return ConcreteSyntaxSymbol.STROKE_LIST;
  }

  public ConcreteSyntaxSymbol visitZSect(ZSect term)
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
