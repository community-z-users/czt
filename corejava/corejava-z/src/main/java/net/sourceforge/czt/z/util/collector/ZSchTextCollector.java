/*
 * Copyright (C) 2011 Leo Freitas
 * This file is part of the CZT project.
 * 
 * The CZT project contains free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 * 
 * The CZT project is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License
 * along with CZT; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 */

package net.sourceforge.czt.z.util.collector;

import java.util.Map;
import java.util.TreeMap;
import net.sourceforge.czt.z.ast.ConstDecl;
import net.sourceforge.czt.z.ast.Decl;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.InclDecl;
import net.sourceforge.czt.z.ast.Name;
import net.sourceforge.czt.z.ast.VarDecl;
import net.sourceforge.czt.z.ast.ZDeclList;
import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.z.ast.ZSchText;
import net.sourceforge.czt.z.util.ZUtils;
import net.sourceforge.czt.z.visitor.ConstDeclVisitor;
import net.sourceforge.czt.z.visitor.InclDeclVisitor;
import net.sourceforge.czt.z.visitor.VarDeclVisitor;
import net.sourceforge.czt.z.visitor.ZDeclListVisitor;
import net.sourceforge.czt.z.visitor.ZSchTextVisitor;

/**
 *
 * @param <R>
 * @author Leo Freitas
 * @date Jul 26, 2011
 */
public class ZSchTextCollector<R> extends BaseCollector<R>
        implements ZSchTextVisitor<R>, ZDeclListVisitor<R>,
          VarDeclVisitor<R>, ConstDeclVisitor<R>, InclDeclVisitor<R>
{

  protected final Map<ZName, Expr> fDeclVars;
  protected ExprCollector fExprCollector;
  protected PredCollector fPredCollector;

  ZSchTextCollector()
  {
    this(new ExprCollector(), new PredCollector());
  }

  ZSchTextCollector(ExprCollector ec, PredCollector pc)
  {
    fDeclVars = new TreeMap<ZName, Expr>(ZUtils.ZNAME_COMPARATOR);
    fExprCollector = ec;
    fPredCollector = pc;
  }

  @Override
  public R visitZDeclList(ZDeclList term)
  {
    for(Decl d : term)
    {
      d.accept(this);
    }
    return null;
  }

  @Override
  public R visitVarDecl(VarDecl term)
  {
    Expr expr = term.getExpr();
    for(Name name : term.getZNameList())
    {
      fDeclVars.put(ZUtils.assertZName(name), expr);
    }
    return null;
  }

  @Override
  public R visitConstDecl(ConstDecl term)
  {
    fDeclVars.put(term.getZName(), term.getExpr());
    //TODO: should we go deep into term.getExpr().accept(fExprCollector)? Not yet
    return null;
  }

  @Override
  public R visitInclDecl(InclDecl term)
  {
    term.getExpr().accept(fExprCollector);
    return null;
  }

  @Override
  public R visitZSchText(ZSchText term)
  {
    term.getDeclList().accept(this);
    term.getPred().accept(fPredCollector);
    return null;
  }

}
