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
 */
public class Envir
{
  protected Envir nextEnv;
  protected RefExpr name;
  protected Term term;

  /** Create an empty Envir */
  public Envir()
  {
  }

  /** Lookup a name in the Environment. 
     @return null if the name does not exist.
  */
  public /*@pure@*/ Term lookup(RefExpr /*@non_null@*/ want)
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
  public Envir add(RefExpr /*@non_null@*/ name, Term /*@non_null@*/ value)
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
    if (name==null ? e2.name!=null : !name.equals(e2.name))
      return false;
    if (term==null ? e2.term!=null : !term.equals(e2.term))
      return false;
    if (nextEnv==null ? e2.nextEnv!=null : !nextEnv.equals(e2.nextEnv))
      return false;
    return true;
  }
}
