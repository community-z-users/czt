/*
  ZLive - A Z animator -- Part of the CZT Project.
  Copyright 2004 Mark Utting

  This program is free software; you can redistribute it and/or
  modify it under the terms of the GNU General Public License
  as published by the Free Software Foundation; either version 2
  of the License, or (at your option) any later version.

  This program is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with this program; if not, write to the Free Software
  Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA  02111-1307, USA.
*/
package net.sourceforge.czt.animation.eval.flatpred;

import java.util.List;
import net.sourceforge.czt.util.*;
import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.base.visitor.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.visitor.*;
import net.sourceforge.czt.animation.eval.*;
import net.sourceforge.czt.animation.eval.flatpred.*;

/** FlatPlus implements the a+b=c predicate. */
public class FlatPlus extends FlatPred
			      // implements MemPred
{
  protected Expr args[] = new Expr[3];

  public FlatPlus(Expr a, Expr b, Expr c)
  {
    args[0] = a;
    args[1] = b;
    args[2] = c;
  }

  public Mode chooseMode(Envir /*@non_null@*/ env)
  { return null; }

  public void setMode(Mode /*@non_null@*/ mode)
  { evalMode_ = mode; }

  public void startEvaluation()
  {}

  public boolean nextEvaluation()
  { return false; }


  ///////////////////////// Pred methods ///////////////////////

  /** @czt.todo Implement this properly. */
  public Object accept(Visitor visitor)
  { //TODO: call memPredVisitor
    return super.accept(visitor);
  }

  /** @czt.todo Implement this properly. */
  public /*@non_null@*/ Object[] getChildren()
  { return new Object[0]; }

  /** @czt.todo Implement this properly. */
  public Term /*@non_null@*/ create(Object[] args)
  { throw new RuntimeException("create not implemented"); }
}
