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

import java.util.ArrayList;

import net.sourceforge.czt.animation.eval.Envir;
import net.sourceforge.czt.animation.eval.flatvisitor.FlatFalseVisitor;
import net.sourceforge.czt.util.Visitor;
import net.sourceforge.czt.z.ast.ZName;

/** FlatFalse implements the false predicate, which causes
 *  all evaluations to fail.
 */
public class FlatFalse extends FlatPred
{
  public FlatFalse()
  {
    args_ = new ArrayList<ZName>();
  }

  /** Chooses the mode in which the predicate can be evaluated.*/
  public Mode chooseMode(/*@non_null@*/ Envir env)
  {
    return new Mode(this, env,args_,0.0);
  }

  /** Does the actual evaluation */
  public boolean nextEvaluation()
  {
    return false;
  }

  public String toString() {
    return "false";
  }


  ///////////////////////// Pred methods ///////////////////////

  /** getChildren returns { args[0], constant } */
  public /*@non_null@*/ Object[] getChildren()
  {
    return new Object[0];
  }

  public /*@non_null@*/ FlatFalse create(/*@non_null@*/ Object[] newargs)
  {
    return new FlatFalse();
  }

  public <R> R accept(Visitor<R> visitor)
  {
    if (visitor instanceof FlatFalseVisitor)
      return ((FlatFalseVisitor<R>) visitor).visitFlatFalse(this);
    else
      return super.accept(visitor);
  }
}
