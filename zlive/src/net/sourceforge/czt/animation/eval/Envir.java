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
  protected Term term;

  /** Create an empty Envir */
  public Envir()
  {
  }

  /** Lookup a name in the Environment. 
     @return null if the name does not exist.
  */
  public /*@pure@*/ Term lookup(RefName /*@non_null@*/ want)
  {
    Envir env = this;
    while (env != null)
      {
	if (want.equals(env.name))
	  return env.term;
	env = env.nextEnv;
      }
    return null;
  }

  /** Add a name to the environment.
      @return The new extended environment
  */
  public Envir add(RefName /*@non_null@*/ name, Term /*@non_null@*/ value)
  {
    Envir result = new Envir();
    result.nextEnv = this;
    result.name = name;
    result.term = value;
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

    //System.out.println("equals: term="+term+", e2.term="+e2.term);
    if (term==null) {
      if (e2.term != null)
        return false;
    } else {
      if (!term.equals(e2.term))
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
