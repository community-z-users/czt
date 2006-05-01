/*
  Copyright (C) 2006 Mark Utting
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

package net.sourceforge.czt.z.util;

import java.util.Stack;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.base.visitor.*;
import net.sourceforge.czt.util.Visitor;
import net.sourceforge.czt.z.ast.*;

/**
 * @author Petra Malik
 */
public class TermSelector
{
  private Term root_;
  private Stack<Term> stack_ = new Stack<Term>();

  /**
   * @param root The non-null root of the AST from which the search and
   *             selection algorithm start.
   */
  public TermSelector(Term root)
  {
    if (root == null) throw new IllegalArgumentException();
    root_ = root;
  }

  public Term getSelectedTerm()
  {
    if (stack_.empty()) return null;
    return stack_.peek();
  }

  public boolean next(int position)
  {
    if (stack_.empty()) {
      return root_.accept(new FindTermVisitor(position, stack_));
    }
    LocAnn locAnn = (LocAnn) stack_.pop().getAnn(LocAnn.class);
    if (locAnn.getStart() > position ||
        position > locAnn.getStart() + locAnn.getLength())
      return root_.accept(new FindTermVisitor(position, stack_));
    while (! stack_.empty()) {
      final Term term = stack_.pop();
      locAnn = (LocAnn) term.getAnn(LocAnn.class);
      if (isLocation(locAnn)) {
        stack_.push(term);
        return true;
      }
    }
    return false;
  }

  /**
   * Checks whether the given location annotation contains useful
   * location information.
   */
  private static boolean isLocation(LocAnn locAnn)
  {
    return locAnn != null &&
      locAnn.getStart() != null &&
      locAnn.getLength() != null;
  }

  /**
   * None of the methods in this class should ever return <code>null</code>.
   */
  static class FindTermVisitor
    implements TermVisitor<Boolean>
  {
    private int position_;
    private Stack<Term> stack_;

    public FindTermVisitor(int position, Stack<Term> stack)
    {
      position_ = position;
      stack_ = stack;
    }

    public Boolean visitTerm(Term term)
    {
      LocAnn locAnn = (LocAnn) term.getAnn(LocAnn.class);
      if (locAnn != null && locAnn.getStart() != null) {
	if (position_ < locAnn.getStart()) {
	  return false;
	}
	if (locAnn.getLength() != null &&
	    position_ > locAnn.getStart() + locAnn.getLength()) {
	  return false;
	}
      }
      stack_.push(term);
      Object[] children = term.getChildren();
      for (int i = children.length - 1; i >= 0; i--) {
        Object o = children[i];
	if (o instanceof Term && ((Term) o).accept(this)) return true;
      }
      if (isLocation(locAnn)) return true;
      stack_.pop();
      return false;
    }
  }
}
