/*
 * WffHighlight.java
 * Copyright (C) 2006 Petra Malik
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA  02111-1307, USA.
 */
package zsidekick;

import java.awt.*;
import java.util.Stack;

import org.gjt.sp.jedit.*;
import org.gjt.sp.jedit.textarea.*;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.visitor.TermVisitor;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.util.ConcreteSyntaxDescriptionVisitor;

public class WffHighlight
  extends TextAreaExtension
{
  private JEditTextArea textArea_;
  private Spec spec_;
  private Stack<Term> stack_ = new Stack<Term>();
  private int matchStart_ = -1;
  private int matchEnd_ = -1;

  public WffHighlight(JEditTextArea textArea)
  {
    textArea_ = textArea;
  }

  public String getToolTipText(int x, int y)
  {
    final int offset = textArea_.xyToOffset(x, y);
    if (matchStart_ <= offset && offset <= matchEnd_) {
      Term term = stack_.peek();
      String msg = term.accept(new ConcreteSyntaxDescriptionVisitor());
      final TypeAnn typeAnn = (TypeAnn) term.getAnn(TypeAnn.class);
      if (typeAnn != null) msg += " of type " + typeAnn.getType().toString();
      final SectTypeEnvAnn sectTypeEnvAnn =
        (SectTypeEnvAnn) term.getAnn(TypeEnvAnn.class);
      if (sectTypeEnvAnn != null) msg += " with " + sectTypeEnvAnn.toString();
      return msg;
    }
    return null;
  }

  public void paintValidLine(Graphics2D gfx, int screenLine,
			     int physicalLine, int start, int end, int y)
  {
    if(matchStart_ < end && matchEnd_ >= start) { // spec_ != null) {
      final int matchStartLine = textArea_.getScreenLineOfOffset(matchStart_);
      final int matchEndLine = textArea_.getScreenLineOfOffset(matchEnd_);
      final int height = textArea_.getPainter().getFontMetrics().getHeight();
      final int x1 = getStartOffset(screenLine, matchStart_);
      final int x2 = getEndOffset(screenLine, matchEnd_);

      gfx.setColor(textArea_.getPainter().getStructureHighlightColor());
      gfx.drawLine(x1, y, x1, y + height - 1);
      gfx.drawLine(x2, y, x2, y + height - 1);

      if(matchStartLine == screenLine || screenLine == 0) {
	gfx.drawLine(x1, y, x2, y);
      }
      else {
	int prevX1 = getStartOffset(screenLine - 1, matchStart_);
	int prevX2 = getEndOffset(screenLine - 1, matchEnd_);
	gfx.drawLine(Math.min(x1, prevX1), y, Math.max(x1, prevX1), y);
	gfx.drawLine(Math.min(x2, prevX2), y, Math.max(x2, prevX2), y);
      }

      if(matchEndLine == screenLine) {
	gfx.drawLine(x1, y + height - 1, x2, y + height - 1);
      }
    }
  }

  public void setSpec(Spec spec)
  {
    spec_ = spec;
    stack_.clear();
    textArea_.repaint();
  }

  /**
   * Checks whether this contains useful location information.
   */
  private static boolean isLocation(LocAnn locAnn)
  {
    return locAnn != null &&
      locAnn.getStart() != null &&
      locAnn.getLength() != null;
  }

  public void next()
  {
    if (spec_ != null) {
      final int caretPos = textArea_.getCaretPosition();
      if (stack_.empty() || caretPos < matchStart_ || caretPos > matchEnd_) {
        stack_.clear();
        spec_.accept(new FindWffVisitor(caretPos, stack_));
      }
      else {
        stack_.pop();
      }
      while (! stack_.empty()) {
        final Term term = stack_.pop();
        final LocAnn locAnn = (LocAnn) term.getAnn(LocAnn.class);
        if (isLocation(locAnn)) {
          stack_.push(term);
          matchStart_ = locAnn.getStart();
          matchEnd_ = matchStart_ + locAnn.getLength();
          textArea_.repaint();
          return;
        }
      }
      matchStart_ = matchEnd_ = -1;
      textArea_.repaint();
    }
  }

  public Term getSelectedWff()
  {
    if (stack_.empty()) return null;
    return stack_.peek();
  }

  private int getStartOffset(int screenLine, int start)
  {
    final int startLine = textArea_.getScreenLineOfOffset(start);
    if (startLine == screenLine) {
      return textArea_.offsetToXY(start).x;
    }
    return
      textArea_.offsetToXY(textArea_.getScreenLineStartOffset(screenLine)).x;
  }

  private int getEndOffset(int screenLine, int end)
  {
    final int endLine = textArea_.getScreenLineOfOffset(end);
    if (endLine == screenLine) {
      return textArea_.offsetToXY(end).x;
    }
    return
      textArea_.offsetToXY(textArea_.getScreenLineEndOffset(screenLine) - 1).x;
  }

  static class FindWffVisitor
    implements TermVisitor
  {
    private int position_;
    private Stack<Term> stack_;

    public FindWffVisitor(int position, Stack<Term> stack)
    {
      position_ = position;
      stack_ = stack;
    }

    public Object visitTerm(Term term)
    {
      LocAnn locAnn = (LocAnn) term.getAnn(LocAnn.class);
      if (locAnn != null && locAnn.getStart() != null) {
	if (position_ < locAnn.getStart()) {
	  return null;
	}
	if (locAnn.getLength() != null &&
	    position_ > locAnn.getStart() + locAnn.getLength()) {
	  return null;
	}
      }
      stack_.push(term);
      Object[] children = term.getChildren();
      for (int i = children.length - 1; i >= 0; i--) {
        Object o = children[i];
	if (o instanceof Term && ((Term) o).accept(this) != null) return term;
      }
      if (isLocation(locAnn)) return term;
      stack_.pop();
      return null;
    }
  }
}
