/*
  Copyright (C) 2007 Petra Malik
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

package net.sourceforge.czt.rules.oracles;

import java.util.HashSet;
import java.util.Set;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.rules.Joker;
import net.sourceforge.czt.z.ast.ConstDecl;
import net.sourceforge.czt.z.ast.Decl;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.InclDecl;
import net.sourceforge.czt.z.ast.Name;
import net.sourceforge.czt.z.ast.NameTypePair;
import net.sourceforge.czt.z.ast.PowerType;
import net.sourceforge.czt.z.ast.SchemaType;
import net.sourceforge.czt.z.ast.SchExpr;
import net.sourceforge.czt.z.ast.Signature;
import net.sourceforge.czt.z.ast.TypeAnn;
import net.sourceforge.czt.z.ast.VarDecl;
import net.sourceforge.czt.z.ast.ZDeclList;
import net.sourceforge.czt.z.visitor.ConstDeclVisitor;
import net.sourceforge.czt.z.visitor.InclDeclVisitor;
import net.sourceforge.czt.z.visitor.VarDeclVisitor;
import net.sourceforge.czt.z.visitor.ZDeclListVisitor;
import net.sourceforge.czt.zpatt.ast.HeadDeclList;
import net.sourceforge.czt.zpatt.ast.JokerDeclList;
import net.sourceforge.czt.zpatt.visitor.HeadDeclListVisitor;
import net.sourceforge.czt.zpatt.visitor.JokerDeclListVisitor;

/**
 * A visitor for collecting all ZNames in some schema text.
 *
 * It takes into account the fact that ids inside a InclDecl are
 * different to the ids outside.  Eg. [ [x@1 : N | x@1<10] | x@2 > 0 ]
 * collects x@1 and x@2 (they are connected via the type annotation on
 * the InclDecl).
 */
public class CollectStateVariablesVisitor
  implements ConstDeclVisitor<Object>,
             HeadDeclListVisitor<Object>,
             InclDeclVisitor<Object>,
             VarDeclVisitor<Object>,
             JokerDeclListVisitor<Object>,
             ZDeclListVisitor<Object>
{
  private Set<Name> variables_ = new HashSet<Name>();

  public Set<Name> getVariables()
  {
    return variables_;
  }

  public Object visitHeadDeclList(HeadDeclList headDeclList)
  {
    for (Decl decl : headDeclList.getZDeclList()) {
      decl.accept(this);
    }
    headDeclList.getJokerDeclList().accept(this);
    return null;
  }

  public Term visitInclDecl(InclDecl inclDecl)
  {
    Expr expr = inclDecl.getExpr();
    if (expr instanceof SchExpr) {
      SchExpr schExpr = (SchExpr) expr;
      schExpr.getZSchText().getDeclList().accept(this);
      final TypeAnn typeAnn = (TypeAnn) schExpr.getAnn(TypeAnn.class);
      final PowerType powerType = (PowerType) typeAnn.getType();
      final SchemaType schType = (SchemaType) powerType.getType();
      final Signature sig = schType.getSignature();
      for (NameTypePair pair : sig.getNameTypePair()) {
        variables_.add(pair.getName());
      }
      return null;
    }
    String message = "Include declaration " + inclDecl + " not supported.";
    throw new IllegalStateException(message);
  }

  public Object visitVarDecl(VarDecl varDecl)
  {
    for (Name declName : varDecl.getName()) {
      variables_.add(declName);
    }
    return null;
  }

  public Object visitConstDecl(ConstDecl constDecl)
  {
    variables_.add(constDecl.getName());
    return null;
  }

  public Object visitJokerDeclList(JokerDeclList jokerDeclList)
  {
    if (jokerDeclList instanceof Joker) {
      Joker joker = (Joker) jokerDeclList;
      Term boundTo = joker.boundTo();
      if (boundTo != null) {
        return boundTo.accept(this);
      }
    }
    throw new RuntimeException("Found unbound Joker");
  }

  public Object visitZDeclList(ZDeclList zDeclList)
  {
    for (Decl decl : zDeclList) {
      decl.accept(this);
    }
    return null;
  }
}
