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
import net.sourceforge.czt.parser.z.ZKeyword;
import net.sourceforge.czt.parser.z.ZToken;
import net.sourceforge.czt.z.util.ZString;

/**
 *
 * @author Petra Malik
 */
public class PrettyPrinter
{
  private int lineWidth_ = PrintPropertiesKeys.PROP_TXT_WIDTH_DEFAULT;
  private int offset_ = PrintPropertiesKeys.PROP_TXT_TAB_SIZE_DEFAULT;

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
                                 int indentAmount)
  {
    final List<Token> list = tseq.getSequence();
    int spaceLeft = space;
    int processed = 0;
    Token previous = null;
    for (ListIterator<Token> iter = list.listIterator(); iter.hasNext();) {
      final Token current = iter.next();
      final int length = getLength(current);
      if (previous != null) { // handle space
        spaceLeft = handleSpaces(iter, previous, current, spaceLeft, length, processed, indentAmount);
      }
      if (current instanceof TokenSequence) {
        spaceLeft = handleTokenSequence((TokenSequence) current, spaceLeft, indentAmount+1);
      }
      else {
        if (ZToken.NL.equals(current)) {
          spaceLeft = indent(iter, indentAmount);
        }
        else {
          spaceLeft -= length;
        }
      }
      processed += length;
      previous = current;
    }
    return spaceLeft;
  }

  protected boolean isSpecialCase(Token previous, Token current)
  {
    if (current instanceof TokenSequence)
    {
      final TokenSequence seq = (TokenSequence) current;
      final List<Token> list = seq.getSequence();
      if (list.isEmpty()) return false;
      return isSpecialCase(previous, list.get(0));
    }
    else if (previous instanceof TokenSequence)
    {
      final TokenSequence seq = (TokenSequence) previous;
      final List<Token> list = seq.getSequence();
      if (list.isEmpty()) return false;
      return isSpecialCase(list.get(list.size()-1), current);
    }
    else
    {
      return isSpecialTokenCase(previous, current);
    }
  }

  protected boolean isSpecialTokenCase(Token previous, Token current)
  {
    if (previous instanceof TokenSequence || current instanceof TokenSequence)
      throw new PrintException("Cannot test special pretty printin case over token sequences");
    // there is this one special case because THEOREM is not a proper environment
    // and yet within Unicode2Latex it does not allow for NL/IDENT between them,
    // although ZED allowed NL after it
    //
    // adding "specialSeq" at Unicode2Latex could work, but it's not quite extensible.
    // (e.g., parser-zeves put something in between ZED and THEOREM, namely DISABLEDTHMTAG
    // or EMPTY, which gets a conflict with the empty production of specialSeq!
    return previous.equals(ZToken.ZED) && current.equals(ZKeyword.THEOREM)
            ||
           previous.getName().equals(ZToken.DECORWORD.getName()) && current.equals(ZToken.RSQUARE)
            ||
           previous.equals(ZToken.LSQUARE) && current.getName().equals(ZToken.DECORWORD.getName());
  }

  protected int handleSpaces(ListIterator<Token> iter, Token previous,
          Token current, int spaceLeft, int length, int processed, int indentAmount)
  {
    assert previous != null && current != null;
    boolean nlAllowedOnPrevious = allowsNlAfter(previous);
    boolean nlAllowedOnCurrent  = allowsNlBefore(current);
    boolean nlAllowed = nlAllowedOnPrevious || nlAllowedOnCurrent;
    if (nlAllowed && (spaceLeft < 0 ||
                      (spaceLeft < length && processed > 1))) {
      assert iter.hasPrevious();

      if (!isSpecialCase(previous, current))
      {
        iter.previous();

        // allowedOnPrevious => hasPrevious again
        assert !nlAllowedOnPrevious || iter.hasPrevious();
        // add a newline just before current or after previous
        iter.add(ZToken.NL);
        spaceLeft = indent(iter, indentAmount);
        Token next = iter.next();
        assert next == current;
      }
    }
    else {
      spaceLeft -= 1;
    }
    return spaceLeft;
  }

  private int indent(ListIterator<Token> iter, int indentAmount)
  {
    iter.add(new TokenImpl(ZToken.INDENT, indent(indentAmount)));
    return lineWidth_-2*indentAmount;
  }

  private String indent(int indentAmount)
  {
    StringBuilder result = new StringBuilder();
    for (int i = 0; i < indentAmount; i++) {
      result.append(ZString.SPACE);
    }
    return result.toString();
  }

  public boolean allowsNlBefore(Token o)
  {
    if (o instanceof TokenSequence)
    {
      final TokenSequence seq = (TokenSequence) o;
      final List<Token> list = seq.getSequence();
      if (list.isEmpty()) return false;
      return allowsNlBefore(list.get(0));
    }
    else
    {
      NewlineCategory nlCat = o.getNewlineCategory();
      return (nlCat == NewlineCategory.BOTH || nlCat == NewlineCategory.BEFORE);
    }
  }

  public boolean allowsNlAfter(Token o)
  {
    if (o instanceof TokenSequence)
    {
      final TokenSequence seq = (TokenSequence) o;
      final List<Token> list = seq.getSequence();
      if (list.isEmpty()) return false;
      return allowsNlAfter(list.get(list.size() - 1));
    }
    else
    {
      NewlineCategory nlCat = o.getNewlineCategory();
      return (nlCat == NewlineCategory.BOTH || nlCat == NewlineCategory.AFTER);
    }
  }

  //@ requires (o instanceof Token) || (o instanceof TokenSequence);
  private int getLength(Token o)
  {
    if (o instanceof TokenSequence)
    {
      TokenSequence tseq = (TokenSequence) o;
      return tseq.getLength() + tseq.getNrOfTokens() - 1;
    }
    else
    {
      return o.spelling().length();
    }
  }
}
