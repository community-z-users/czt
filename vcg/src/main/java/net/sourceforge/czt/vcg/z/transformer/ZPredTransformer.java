/*
  Copyright (C) 2008 Leo Freitas
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
package net.sourceforge.czt.vcg.z.transformer;

import java.util.Iterator;
import java.util.List;
import net.sourceforge.czt.util.Visitor;
import net.sourceforge.czt.z.ast.AxPara;
import net.sourceforge.czt.z.ast.ConstDecl;
import net.sourceforge.czt.z.ast.Decl;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.Name;
import net.sourceforge.czt.z.ast.Pred;
import net.sourceforge.czt.z.ast.ZDeclList;
import net.sourceforge.czt.z.ast.ZSchText;
import net.sourceforge.czt.z.util.Factory;

/**
 * Z-Centric predicate transformers and auxiliary methods.
 *
 * @author Leo Freitas
 * @date Dec 23, 2010
 */
public class ZPredTransformer extends AbstractPredTransformer
{
  public ZPredTransformer(Factory factory, Visitor<Pred> termV)
  {
    super(factory, termV);
  }

  /**
   * Extract schema text predicates. When null (see Z Std syntactic
   * transformations for when that is the case), just returns true.
   *
   * @param schText
   * @return
   */
  protected Pred getZSchTextPred(ZSchText schText)
  {
    assert schText != null : "Invalid ZSchText (null)!";
    Pred result = schText.getPred();
    // In case of a sch text without Pred, just return true
    if (result == null)
    {
      result = truePred();
    }
    return result;
  }

  /** Transforms a predicate into a (Sch)Expr (with empty Decl): P --> [ |P]
   * @param pred
   * @return 
   */
  public Expr predAsSchExpr(Pred pred)
  {
    assert pred != null : "Invalid SchExpr request!";
    return factory_.createSchExpr(factory_.createZSchText(factory_.createZDeclList(), pred));
  }

  /**
   * For a zSchText (D | P) creates an \begin{schema}{schName}[genFormals] D \where P \end{schema}
   * @param formals
   * @param genFormals
   * @param schName
   * @param zSchText
   * @return
   */
  public AxPara createSchExpr(List<? extends Name> formals , Name schName, ZSchText zSchText)
  {
    return factory_.createSchema(schName, formals, zSchText);
  }

  /**
   * Checks whether the list of declarations are ConstDecl only.
   * This is important while checking for LetExpr, and BindExpr
   * (syntactic/parsing) consistency.
   * @param decls
   * @return
   */
  public boolean isOnlyConstDecl(ZDeclList decls)
  {
    boolean result = true;
    Iterator<Decl> it = decls.iterator();
    while (result && it.hasNext())
    {
      result = (it.next() instanceof ConstDecl);
    }
    it = null;
    return result;
  }
}
