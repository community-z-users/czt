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
package net.sourceforge.czt.animation.eval;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.animation.eval.*;

/** An Environment is conceptually a mapping from variable names to values.
    However, it can also contain additional information about each
    name, such as type information.  This data structure is designed
    to allow environments to be extended in a non-destructive way.
    This is why add() returns a new environment.
    
    TODO: think more about the semantics of the equals.  Should the
    order matter?  Should duplicate names matter?
*/
public class Envir
{
  protected Envir nextEnv;
  // An empty environment always has name==null && term==null;
  protected RefName name;
  protected Expr expr;

  /** Create an empty Envir */
  public Envir()
  {
  }

  /** Lookup a name in the Environment. 
     @return null if the name does not exist.
  */
  public /*@pure@*/ Expr lookup(RefName /*@non_null@*/ want)
  {
    Envir env = this;
    while (env != null)
      {
	if (want.equals(env.name))
	  return env.expr;
	env = env.nextEnv;
      }
    return null;
  }

  /** Update the value of a name in the Environment. 
      WARNING: this destructively changes the Environment
      and may change other environments that share parts of this environment.
     @param name This name must already exist in the environment.
     @param newvalue The new value for name.
  */
  public void setValue(/*@non_null@*/ RefName name, 
		       /*@non_null@*/ Expr newvalue)
  {
    Envir env = this;
    while (env != null)
      {
	if (name.equals(env.name)) {
	  env.expr = newvalue;
	  return;
	}
	env = env.nextEnv;
      }
    assert(false);
  }

  /** Add a name to the environment.
      @return The new extended environment
  */
  public Envir add(/*@non_null@*/ RefName name, /*@non_null@*/ Expr value)
  {
    Envir result = new Envir();
    result.nextEnv = this;
    result.name = name;
    result.expr = value;
    return result;
  }

  /** Two environments are equal if they contain the same names
      and values, in exactly the same order.
  */
  public boolean equals(Object obj)
  {
    if ( ! (obj instanceof Envir))
      return false;
    Envir e2 = (Envir)obj;

    //System.out.println("equals: name="+name+", e2.name="+e2.name);
    if (name==null) {
      if (e2.name != null)
        return false;
    } else {
      if (!name.equals(e2.name))
        return false;
    }

    //System.out.println("equals: expr="+expr+", e2.expr="+e2.expr);
    if (expr==null) {
      if (e2.expr != null)
        return false;
    } else {
      if (!expr.equals(e2.expr))
        return false;
    }

    //System.out.println("equals: nextEnv="+nextEnv+", e2.nextEnv="+e2.nextEnv);
    if (nextEnv==null) {
      if (e2.nextEnv != null)
        return false;
    } else {
      if (!nextEnv.equals(e2.nextEnv))
        return false;
    }

    return true;
  }
}
