/*
  Copyright (C) 2005 Mark Utting
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

import java.util.*;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.session.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.visitor.*;
import net.sourceforge.czt.zpatt.ast.*;

/**
 * Utility methods for proving and rewriting.
 *
 * @author Petra Malik
 */
public final class ProverUtils
{
  public static List<Rule> collectRules(Term term)
  {
    List<Rule> result = new ArrayList<Rule>();  
    if (term instanceof Spec) {
      for (Iterator i = ((Spec) term).getSect().iterator(); i.hasNext(); ) {
        Sect sect = (Sect) i.next();
        if (sect instanceof ZSect) {
          for (Iterator j = ((ZSect) sect).getPara().iterator();
               j.hasNext(); ) {
            Para para = (Para) j.next();
            if (para instanceof Rule) {
              result.add((Rule) para);
            }
          }
        }
      }
    }
    return result;
  }

  public static List<ConjPara> collectConjectures(Term term)
  {
    List<ConjPara> result = new ArrayList<ConjPara>();  
    if (term instanceof Spec) {
      for (Iterator i = ((Spec) term).getSect().iterator(); i.hasNext(); ) {
        Sect sect = (Sect) i.next();
        if (sect instanceof ZSect) {
          for (Iterator j = ((ZSect) sect).getPara().iterator();
               j.hasNext(); ) {
            Para para = (Para) j.next();
            if (para instanceof ConjPara) {
              result.add((ConjPara) para);
            }
          }
        }
      }
    }
    return result;
  }
}
