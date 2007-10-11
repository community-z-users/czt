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

package net.sourceforge.czt.rules;

import java.util.HashSet;
import java.util.Set;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.visitor.*;
import net.sourceforge.czt.zpatt.ast.*;
import net.sourceforge.czt.zpatt.visitor.*;

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
