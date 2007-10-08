/*
  Copyright (C) 2007 Petra Malik
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

package net.sourceforge.czt.print.util;

import java.util.List;
import java.util.ListIterator;

import net.sourceforge.czt.parser.util.NewlineCategory;
import net.sourceforge.czt.parser.util.Token;
import net.sourceforge.czt.parser.util.TokenImpl;
import net.sourceforge.czt.parser.z.ZToken;
import net.sourceforge.czt.z.util.ZString;

/**
 *
 * @author Petra Malik
 */
public class PrettyPrinter
{
  private int lineWidth_ = 80;
  private int offset_ = 2;

  public void setOffset(int offset)
  {
    offset_ = offset;
  }

  public void setLineWidth(int width)
  {
    lineWidth_ = width;
  }

  public int handleTokenSequence(TokenSequence tseq,
                                 int startPos)
  {
    return handleTokenSequence(tseq, lineWidth_-startPos, 0);
  }

  public int handleTokenSequence(TokenSequence tseq,
                                 int space,
                                 int indent)
  {
    final List<Object> list = tseq.getSequence();
    int spaceLeft = space;
    int processed = 0;
    Object previous = null;
    for (ListIterator iter = list.listIterator(); iter.hasNext();) {
      final Object o = iter.next();
      final int length = getLength(o);
      if (previous != null) { // handle space
        boolean nlAllowed = allowsNlAfter(previous) || allowsNlBefore(o);
        if (nlAllowed && (spaceLeft < 0 ||
                          (spaceLeft < length && processed > 1))) {
          iter.previous();
          iter.add(ZToken.NL);
          spaceLeft = indent(iter, indent);
          Object next = iter.next();
          assert next == o;
        }
        else {
          spaceLeft -= 1;
        }
      }
      if (o instanceof TokenSequence) {
        spaceLeft =
          handleTokenSequence((TokenSequence) o, spaceLeft, indent+1);
      }
      else {
        if (ZToken.NL.equals(o)) {
          spaceLeft = indent(iter, indent);
        }
        else {
          spaceLeft -= length;
        }
      }
      processed += length;
      previous = o;
    }
    return spaceLeft;
  }

  private int indent(ListIterator iter, int indent)
  {
    iter.add(new TokenImpl(ZToken.INDENT, indent(indent)));
    return lineWidth_-2*indent;
  }

  private String indent(int indent)
  {
    StringBuilder result = new StringBuilder();
    for (int i = 0; i < indent; i++) {
      result.append(ZString.SPACE);
    }
    return result.toString();
  }

  public boolean allowsNlBefore(Object o)
  {
    if (o instanceof Token) {
      NewlineCategory nlCat = ((Token) o).getNewlineCategory();
      return
        (nlCat == NewlineCategory.BOTH || nlCat == NewlineCategory.BEFORE);
    }
    final TokenSequence seq = (TokenSequence) o;
    final List<Object> list = seq.getSequence();
    if (list.isEmpty()) return false;
    return allowsNlBefore(list.get(0));
  }

  public boolean allowsNlAfter(Object o)
  {
    if (o instanceof Token) {
      NewlineCategory nlCat = ((Token) o).getNewlineCategory();
      return
        (nlCat == NewlineCategory.BOTH || nlCat == NewlineCategory.AFTER);
    }
    final TokenSequence seq = (TokenSequence) o;
    final List<Object> list = seq.getSequence();
    if (list.isEmpty()) return false;
    return allowsNlAfter(list.get(0));
  }

  //@ requires (o instanceof Token) || (o instanceof TokenSequence);
  private int getLength(Object o)
  {
    if (o instanceof Token) {
      return ((Token) o).spelling().length();
    }
    TokenSequence tseq = (TokenSequence) o;
    return tseq.getLength() + tseq.getNrOfTokens() - 1;
  }
}
