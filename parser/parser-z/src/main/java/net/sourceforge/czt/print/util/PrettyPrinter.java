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
import net.sourceforge.czt.base.ast.Term;

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
  private final Term term_;
  private int lineWidth_ = PrintPropertiesKeys.PROP_TXT_WIDTH_DEFAULT;
  private int offset_ = PrintPropertiesKeys.PROP_TXT_TAB_SIZE_DEFAULT;

  public PrettyPrinter(Term term, int initW)
  {
    term_ = term;
    lineWidth_ = initW;
  }
  
  public Term getTerm()
  {
	  return term_;
  }

  public void setOffset(int offset)
  {
    offset_ = offset;
  }
  
  public int getOffSet()
  {
	  return offset_;
  }
  

  public void setLineWidth(int width)
  {
    lineWidth_ = width;
  }

  public int handleTokenSequence(TokenSequence tseq,
                                 int startPos) throws PrintException
  {
    return handleTokenSequence(tseq, lineWidth_-startPos, 0);
  }

  public int handleTokenSequence(TokenSequence tseq,
                                 int space,
                                 int indentAmount) throws PrintException
  {
    final List<Token> list = tseq.getSequence();
    int spaceLeft = space;
    int processed = 0;
    Token previous = null;
    ListIterator<Token> iter = list.listIterator(); 
    while (iter.hasNext()) {
      final Token current = iter.next();
      final int length = getLength(current);
      if (previous != null) { // handle space
        spaceLeft = handleSpaces(iter, previous, current, spaceLeft, length, processed > 1, indentAmount);
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
    iter = null;
    return spaceLeft;
  }

  /**
   * Check tokens to see whether space handling is to be treated as special case or not.
   * This depends on various factors like if the LHS or RHS are token sequences or actual
   * tokens themselves.
   * @param previous
   * @param current
   * @return
   */
  protected boolean isSpecialCase(Token previous, Token current) throws PrintException
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

  /**
   * Check tokens to see whether space handling is to be treated as a special case or not.
   * It only handles non-token-sequence cases.
   * @param previous
   * @param current
   * @return
   * @throws PrintException is either previous or current is a token sequence.
   */
  protected boolean isSpecialTokenCase(Token previous, Token current) throws PrintException
  {
    if (previous instanceof TokenSequence)
      throw new PrintException(((TokenSequence)previous).getDialect(), 
    		  "Cannot test special pretty print in case over token sequences - previous");
    if (current instanceof TokenSequence)
        throw new PrintException(((TokenSequence)current).getDialect(), 
      		  "Cannot test special pretty print in case over token sequences - current");
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

  protected boolean considerAddingNL(Token previous, Token current,
          int spaceLeft, int length, boolean startedProcessing) throws PrintException
  {
    boolean result = (spaceLeft < 0 ||
           (spaceLeft < length && startedProcessing));
    if (!result)
    {
      // if couldn't tell, try checking if either side were token sequences
      if (current instanceof TokenSequence)
      {
        final TokenSequence seq = (TokenSequence) current;
        final List<Token> list = seq.getSequence();
        if (list.isEmpty())
          result = false;
        else
          result = considerAddingNL(previous, list.get(0), spaceLeft, length, startedProcessing);
      }
      else if (previous instanceof TokenSequence)
      {
        final TokenSequence seq = (TokenSequence) previous;
        final List<Token> list = seq.getSequence();
        if (list.isEmpty())
          result = false;
        else
          result = considerAddingNL(list.get(list.size()-1), current, spaceLeft, length, startedProcessing);
      }
      else
      {
        return considerAddingNLForToken(previous, current, spaceLeft, length, startedProcessing);
      }
    }
    return result;
  }

  protected boolean considerAddingNLForToken(Token previous, Token current,
          int spaceLeft, int length, boolean startedProcessing) throws PrintException
  {
    if (previous instanceof TokenSequence)
        throw new PrintException(((TokenSequence)previous).getDialect(), 
      		  "Cannot consider adding NL case over token sequences - previous");
      if (current instanceof TokenSequence)
          throw new PrintException(((TokenSequence)current).getDialect(), 
        		  "Cannot consider adding NL case over token sequences - current");
    return false;
  }

  protected int handleSpaces(ListIterator<Token> iter, Token previous,
          Token current, int spaceLeft, int length, boolean startedProcessing, int indentAmount) 
        		  throws PrintException
  {
    assert previous != null && current != null;
    boolean nlAllowedOnPrevious = allowsNlAfter(previous);
    boolean nlAllowedOnCurrent  = allowsNlBefore(current);
    boolean nlAllowed = nlAllowedOnPrevious || nlAllowedOnCurrent;
    if (nlAllowed && considerAddingNL(previous, current,
            spaceLeft, length, startedProcessing)) {
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
