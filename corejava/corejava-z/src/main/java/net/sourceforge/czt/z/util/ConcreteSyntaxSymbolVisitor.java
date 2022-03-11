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

import net.sourceforge.czt.z.ast.*;

/**
 * This visitor classifies a given AST node as a concrete syntax
 * symbol {@link ConcreteSyntaxSymbol}.  This is used by the JEdit and
 * Eclipse Z plugins to produce an outline view (or structure tree) of
 * the Z source.
 * 
 * @author Petra Malik
 */
public class ConcreteSyntaxSymbolVisitor
  extends SyntaxSymbolVisitor
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

  public ConcreteSyntaxSymbol visitConjPara(ConjPara conjPara)
  {
    if (utils_.isEmpty(conjPara.getNameList())) {
      return ConcreteSyntaxSymbol.CONJ_PARA;
    }
    return ConcreteSyntaxSymbol.GENCONJ_PARA;
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
