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

import java.io.PrintWriter;
import java.io.Writer;

import net.sourceforge.czt.parser.util.Token;
import net.sourceforge.czt.parser.z.TokenName;

/**
 * Print Z specifications in Unicode.
 * This class adds the functionality to print Z tokens in unicode
 * to the PrintWriter class.
 *
 * @author Petra Malik
 */
public class PrettyPrinter
  extends PrintWriter
{
  private TokenSequence.Printer tokenPrinter_;
  private int lineWidth_ = 80;
  private int offset_ = 2;

  /**
   * Create a new PrintWriter, without automatic line flushing.
   *
   * @param out a character-output stream.
   */
  public PrettyPrinter(Writer out, TokenSequence.Printer tokenPrinter)
  {
    super(out);
    tokenPrinter_ = tokenPrinter;
  }

  /**
   * Create a new PrintWriter.
   *
   * @param out a character-output stream.
   * @param autoFlush a boolean; if true, the println() methods
   *                  will flush the output buffer
   */
  public PrettyPrinter(Writer out, boolean autoFlush)
  {
    super(out, autoFlush);
  }

  public void setOffset(int offset)
  {
    offset_ = offset;
  }

  public void setLineWidth(int width)
  {
    lineWidth_ = width;
  }

  public int printToken(Token token)
  {
    String s = tokenPrinter_.toString(token);
    print(s);
    return s.length();
  }

  public int printTokenSequence(TokenSequence tseq,
                                int startPos)
  {
    int pos = startPos;
    boolean first = true;
    for (Object o : tseq.getSequence()) {
      if (! first) { // handle space
        if (lineWidth_ < pos + getLength(o)) {
          pos = startPos + offset_;
          indent(pos);
        }
        else {
          print(" ");
          pos += 1;
        }
      }
      if (o instanceof Token) {
        Token token = (Token) o;
        pos += printToken(token);
      }
      else {
        pos = printTokenSequence((TokenSequence) o, pos);
      }
      first = false;
    }
    return pos;
  }

  //@ requires (o instanceof Token) || (o instanceof TokenSequence);
  private int getLength(Object o)
  {
    if (o instanceof Token) return tokenPrinter_.toString((Token) o).length();
    TokenSequence tseq = (TokenSequence) o;
    return tseq.getLength(tokenPrinter_) + tseq.getNrOfTokens() - 1;
  }

  public void indent(int spaces)
  {
    println();
    for (int i = 0; i < spaces; i++) {
      print(" ");
    }
  }
}
