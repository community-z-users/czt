/*
Copyright (C) 2004 Petra Malik
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

package net.sourceforge.czt.print.ast;

import java.util.ArrayList;
import java.util.List;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.util.TypesafeList;
import net.sourceforge.czt.util.Visitor;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.impl.ExprImpl;
import net.sourceforge.czt.z.util.OperatorName;

/**
 *
 */
public class OperatorApplication
  extends ExprImpl
{
  private OperatorName opName_;
  private List args_ = new TypesafeList(Expr.class);

  public OperatorApplication(OperatorName opName, List args)
  {
    opName_ = opName;
    args_.addAll(args);
  }

  public OperatorName getOperatorName()
  {
    return opName_;
  }

  public List getArgs()
  {
    return args_;
  }

  public Object accept(Visitor visitor)
  {
    if (visitor instanceof OperatorApplicationVisitor) {
      OperatorApplicationVisitor v = (OperatorApplicationVisitor) visitor;
      return v.visitOperatorApplication(this);
    }
    return super.accept(visitor);
  }

  public Object[] getChildren()
  {
    return args_.toArray();
  }

  public Term create(Object[] children)
  {
    List argList = new ArrayList();
    for (int i = 0; i < children.length; i++) {
      argList.add(children[0]);
    }
    return new OperatorApplication(opName_, argList);
  }
}
