/**
Copyright 2003 Mark Utting
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

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.base.visitor.*;
import net.sourceforge.czt.base.util.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.visitor.*;

/**
 * <p>This class provides an example of a substitution visitor.
 * It substitutes each AndPred with an OrPred having the same
 * children, and removes all NarrPara.</p>
 *
 * @author Petra Malik
 */
public class SubstVisitor
  extends AstTermVisitor
  implements AndPredVisitor, NarrParaVisitor
{
  ZFactory mFactory = new net.sourceforge.czt.z.impl.ZFactoryImpl();

  /**
   * Substitute AndPred with OrPred.
   *
   * @param andPred the conjunction predicate to be substituted.
   * @return a newly created disjunction predicate
   *         having the same children as the given conjunction.
   */
  public Object visitAndPred(AndPred andPred)
  {
    Pred leftPred = (Pred) andPred.getLeftPred().accept(this);
    Pred rightPred = (Pred) andPred.getRightPred().accept(this);
    OrPred orPred = mFactory.createOrPred(leftPred, rightPred);
    orPred.getAnns().addAll(andPred.getAnns());
    return orPred;
  }

  /**
   * Substitute NarrPara with <code>null</code>.
   *
   * @param narrPara the narrative paragraph to be substituted.
   * @return <code>null</code>.
   */
  public Object visitNarrPara(NarrPara narrPara)
  {
    return null;
  }
}
