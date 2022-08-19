/**
Copyright (C) 2006 Mark Utting
This file is part of the CZT project.

The CZT project contains free software; you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation; either version 2 of the License, or
(at your option) any later version.

The CZT project is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with CZT; if not, write to the Free Software
Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
*/

package net.sourceforge.czt.animation.eval.result;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import net.sourceforge.czt.animation.eval.TextUI;
import net.sourceforge.czt.animation.eval.ZTestCase;
import net.sourceforge.czt.session.Markup;
import net.sourceforge.czt.z.ast.Expr;

/**
 * Tests for PowerSet.
 *
 * @author Petra Malik
 */
public class RelSetTest extends ZTestCase
{
  public void testSimpleEmpty()
  {
    RelSet relSet =
      new RelSet(getSet1(), getEmptySet(), false, false, false, false);
    assertFalse(relSet.isEmpty());
    assertTrue(relSet.contains(getEmptySet()));
  }

  public void testSimpleRel()
  {
    RelSet relSet =
      new RelSet(getSet1(), getSet2(), false, true, true, false);
    assertFalse(relSet.contains(getEmptySet()));
    List<EvalSet> list = new ArrayList<EvalSet>();
    list.add(getSet1());
    list.add(getSet2());
    ProdSet prodSet = new ProdSet(list);
    Iterator<Expr> iter = prodSet.iterator();
    DiscreteSet set = new DiscreteSet();
    while (iter.hasNext()) {
      set.add(iter.next());
    }
    assertTrue(relSet.contains(set));
    assertEquals("\\{ 1 \\} \\rel \\{ 2 , 3 \\}", latex(relSet));
  }

  public void testSimpleFun1()
  {
    RelSet relSet =
      new RelSet(getSet1(), getSet1(), true, true, true, true);
    assertFalse(relSet.contains(getEmptySet()));
    assertTrue(relSet.contains(set(tuple(i1, i1))));
    assertEquals("\\{ 1 \\} \\bij \\{ 1 \\}", latex(relSet));
  }

  public void testSimpleFun2()
  {
    RelSet relSet =
      new RelSet(getSet1(), getSet2(), true, true, true, true);
    assertFalse(relSet.contains(getEmptySet()));
    assertFalse(relSet.contains(set(tuple(i1, i2))));
    assertFalse(relSet.contains(set(tuple(i1, i3))));
  }

  private DiscreteSet getEmptySet()
  {
    return new DiscreteSet();
  }

  private DiscreteSet getSet1()
  {
    return set(i1);
  }

  private DiscreteSet getSet2()
  {
    return set(i2, i3);
  }

  private DiscreteSet set(Expr e)
  {
    DiscreteSet result = new DiscreteSet();
    result.add(e);
    return result;
  }

  private DiscreteSet set(Expr e1, Expr e2)
  {
    DiscreteSet result = new DiscreteSet();
    result.add(e1);
    result.add(e2);
    return result;
  }

  private Expr tuple(Expr e1, Expr e2)
  {
    List<EvalSet> list = new ArrayList<EvalSet>();
    list.add(set(e1));
    list.add(set(e2));
    ProdSet prod = new ProdSet(list);
    return prod.iterator().next();
  }
  
  private String latex(RelSet rel)
  {
    return new TextUI(zlive_, null).printTerm(rel, Markup.LATEX);
  }
}
