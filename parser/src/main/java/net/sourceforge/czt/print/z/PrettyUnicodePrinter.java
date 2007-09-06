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

package net.sourceforge.czt.print.z;

import java.io.PrintWriter;
import java.io.Writer;

import net.sourceforge.czt.parser.util.Token;
import net.sourceforge.czt.parser.z.TokenName;
import net.sourceforge.czt.print.util.TokenSequence;
import net.sourceforge.czt.z.util.ZString;

/**
 * Print Z specifications in Unicode.
 * This class adds the functionality to print Z tokens in unicode
 * to the PrintWriter class.
 *
 * @author Petra Malik
 */
public class PrettyUnicodePrinter
  extends PrintWriter
  implements TokenSequence.Printer
{
  // called margin in Oppen's algorithm
  private int lineWidth_ = 80;
  private int offset_ = 2;

  /**
   * Create a new PrintWriter, without automatic line flushing.
   *
   * @param out a character-output stream.
   */
  public PrettyUnicodePrinter(Writer out)
  {
    super(out);
  }

  /**
   * Create a new PrintWriter.
   *
   * @param out a character-output stream.
   * @param autoFlush a boolean; if true, the println() methods
   *                  will flush the output buffer
   */
  public PrettyUnicodePrinter(Writer out, boolean autoFlush)
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
    String s = toString(token);
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

  //@ assumes (o instanceof Token) || (o instanceof TokenSequence);
  private int getLength(Object o)
  {
    if (o instanceof Token) return toString((Token) o).length();
    TokenSequence tseq = (TokenSequence) o;
    return tseq.getLength(this) + tseq.getNrOfTokens() - 1;
  }

  public void indent(int spaces)
  {
    println();
    for (int i = 0; i < spaces; i++) {
      print(" ");
    }
  }

  public String toString(Token token)
  {
    if (TokenName.NUMSTROKE.getName().equals(token.getName())) {
      return ZString.SE + token.getSpelling() + ZString.NW;
    }
    return token.spelling();
  }
}
