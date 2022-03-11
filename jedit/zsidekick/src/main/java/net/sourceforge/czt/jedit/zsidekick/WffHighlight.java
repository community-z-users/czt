/*
 * WffHighlight.java
 * Copyright (C) 2006, 2007 Petra Malik
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
package net.sourceforge.czt.jedit.zsidekick;

import java.awt.*;
import java.util.Iterator;

import org.gjt.sp.jedit.*;
import org.gjt.sp.jedit.textarea.*;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.util.ZConcreteSyntaxDescriptionVisitor;
import net.sourceforge.czt.z.util.ZGetNameVisitor;
import net.sourceforge.czt.z.util.TermSelector;

public class WffHighlight
  extends TextAreaExtension
{
  private JEditTextArea textArea_;
  private TermSelector termSelector_;

  public void setTextArea(JEditTextArea textArea)
  {
    textArea_ = textArea;
  }

  @Override
  public String getToolTipText(int x, int y)
  {
    if (termSelector_ != null) {
      final Term term = termSelector_.getSelectedTerm();
      if (term != null) {
        final int offset = textArea_.xyToOffset(x, y);
        final LocAnn locAnn = term.getAnn(LocAnn.class);
        if (locAnn.getStart().intValue() <= offset &&
            offset <= locAnn.getEnd().intValue()) {
          ZGetNameVisitor visitor = new ZGetNameVisitor();
          if (jEdit.getBooleanProperty(ZSideKickPlugin.PROPERTY_PREFIX + ZSideKickPlugin.PROP_PRINT_NAME_IDS)) {
            visitor.setPrintIds(true);
          }
          ZConcreteSyntaxDescriptionVisitor csdv =
            new ZConcreteSyntaxDescriptionVisitor();
          csdv.setNameVisitor(visitor);
          String text = "<html>" + term.accept(csdv);
          TypeAnn typeAnn = term.getAnn(TypeAnn.class);
          if (typeAnn != null) {
            text += "<br/>Type: " +
              typeAnn.getType().accept(visitor);
          }
          text += "</html>";
          return text;
        }
      }
    }
    return null;
  }

  @Override
  public void paintValidLine(Graphics2D gfx, int screenLine,
			     int physicalLine, int start, int end, int y)
  {
    if (termSelector_ != null && termSelector_.getSelectedTerm() != null) {
      final Term term = termSelector_.getSelectedTerm();
      final LocAnn locAnn = term.getAnn(LocAnn.class);
      final int matchStart = locAnn.getStart().intValue();
      final int matchEnd = locAnn.getEnd().intValue();
      if (matchStart < end && matchEnd >= start) {
        final int matchStartLine = textArea_.getScreenLineOfOffset(matchStart);
        final int matchEndLine = textArea_.getScreenLineOfOffset(matchEnd);
        final int height = textArea_.getPainter().getFontMetrics().getHeight();
        final int x1 = getStartOffset(screenLine, matchStart);
        final int x2 = getEndOffset(screenLine, matchEnd);

        gfx.setColor(textArea_.getPainter().getStructureHighlightColor());
        gfx.drawLine(x1, y, x1, y + height - 1);
        gfx.drawLine(x2, y, x2, y + height - 1);

        if(matchStartLine == screenLine || screenLine == 0) {
          gfx.drawLine(x1, y, x2, y);
        }
        else {
          int prevX1 = getStartOffset(screenLine - 1, matchStart);
          int prevX2 = getEndOffset(screenLine - 1, matchEnd);
          gfx.drawLine(Math.min(x1, prevX1), y, Math.max(x1, prevX1), y);
          gfx.drawLine(Math.min(x2, prevX2), y, Math.max(x2, prevX2), y);
        }

        if(matchEndLine == screenLine) {
          gfx.drawLine(x1, y + height - 1, x2, y + height - 1);
        }
      }
    }
  }

  public void setSpec(Spec spec)
  {
    termSelector_ = new TermSelector(spec);
    // At the very first parse, setSpec might occur prior to setTextArea, hence a nullpointer exception!
    if (textArea_ != null)
      textArea_.repaint();
  }

  /**
   * Checks whether this contains useful location information.
   */
  protected static boolean isLocation(LocAnn locAnn)
  {
    return locAnn != null &&
      locAnn.getStart() != null &&
      locAnn.getLength() != null;
  }

  public void next()
  {
    if (termSelector_ != null) {
      termSelector_.next(textArea_.getCaretPosition());
      textArea_.repaint();
    }
  }

  public Term getSelectedWff()
  {
    Term result = null;
    if (termSelector_ != null) {
      result = termSelector_.getSelectedTerm();
    }
    return result;
  }

  public ZSect findZSectForCurrentWff()
  {
    for(Iterator<Term> iter = termSelector_.iterator(); iter.hasNext(); ) {
      Term term = iter.next();
      if (term instanceof ZSect) return (ZSect) term;
    }
    return null;
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
}
