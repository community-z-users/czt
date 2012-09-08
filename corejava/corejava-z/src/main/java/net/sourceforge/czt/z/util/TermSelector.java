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

import java.math.BigInteger;
import java.util.Iterator;
import java.util.Stack;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.base.visitor.*;
import net.sourceforge.czt.z.ast.*;

/**
 * This class provides methods to select terms in an AST based on the
 * location annotations of the terms and a given position, which is
 * usually the position of a pointing device like a caret.
 *
 * @author Petra Malik
 */
public class TermSelector
{
  private Term root_;
  private Stack<Term> stack_ = new Stack<Term>();

  /**
   * Creates a new TermSelector with the given root term.
   *
   * @param root The non-null root of the AST from which the search and
   *             selection algorithms start.
   */
  public TermSelector(Term root)
  {
    if (root == null) throw new IllegalArgumentException();
    root_ = root;
  }

  /**
   * Returns the currently selected term, or <code>null</code> if none
   * is currently selected.
   *
   * @return the currently selected term.  If it is not <code>null</code>,
   *         the returned term has non-<code>null</code> start and length
   *         notation annotations.
   */
  public Term getSelectedTerm()
  {
    if (stack_.empty()) return null;
    return stack_.peek();
  }

  /**
   * <p>Computes the new term to be selected based on the given position.
   * This works as follows:</p>
   *
   * <p>If no term is currently selected or the given position is
   * outside the currently selected term, this method tries to find a
   * term in the tree with non-<code>null</code> start and length
   * location annotations so that <code>start <= position <= start +
   * length</code>.  It makes also sure that this newly selected term
   * doesn't have a descendant with non-<code>null</code> start and
   * length location annotation for which <code>start <= position <=
   * start + length</code> holds.</p>
   *
   * <p>If the given position is inside the currently selected term,
   * the closest ancestor with non-<code>null</code> start and length
   * location annotation is selected.  If there doesn't exist such an
   * ancestor, the next selected term is set to <code>null</code>.
   *
   * @return whether a new term has been selected or not.
   */
  public boolean next(int position)
  {
    if (stack_.empty()) {
      return root_.accept(new FindTermVisitor(position, stack_));
    }
    LocAnn locAnn = stack_.pop().getAnn(LocAnn.class);
    BigInteger pos = BigInteger.valueOf(position);
    if (locAnn.getStart().compareTo(pos) > 0 ||
        pos.compareTo(locAnn.getEnd()) > 0) {
      stack_.clear();
      return root_.accept(new FindTermVisitor(position, stack_));
    }
    while (! stack_.empty()) {
      final Term term = stack_.pop();
      locAnn = term.getAnn(LocAnn.class);
      if (isLocation(locAnn)) {
        stack_.push(term);
        return true;
      }
    }
    return false;
  }

  /**
   * Not sure whether this is a good method to have here.
   * I want to use it to have access to the parents of a term.
   */
  public Iterator<Term> iterator()
  {
    return stack_.iterator();
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

  /** This visitor searches down an AST to find the smallest
   *  subtree that contains the given cursor position.
   *  
   * None of the methods in this class should ever return <code>null</code>.
   */
  static class FindTermVisitor
    implements TermVisitor<Boolean>
  {
    private BigInteger position_;
    private Stack<Term> stack_;

    public FindTermVisitor(int position, Stack<Term> stack)
    {
      position_ = BigInteger.valueOf(position);
      stack_ = stack;
    }

    public Boolean visitTerm(Term term)
    {
      LocAnn locAnn = (LocAnn) term.getAnn(LocAnn.class);
      if (locAnn != null && locAnn.getStart() != null) {
        if (position_.compareTo(locAnn.getStart()) < 0) {
          return false;
        }
        BigInteger endPos = locAnn.getEnd();
        if (endPos != null && position_.compareTo(endPos) > 0) {
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
