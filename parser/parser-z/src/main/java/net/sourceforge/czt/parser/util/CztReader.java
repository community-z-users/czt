/*
  Copyright (C) 2003, 2004, 2006 Petra Malik
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

package net.sourceforge.czt.parser.util;

import java.io.IOException;
import java.io.Reader;
import java.util.NoSuchElementException;
import java.util.SortedMap;
import java.util.TreeMap;

/**
 * A reader for a list of tokens.  In addition to the usual Reader
 * functionality there are getLine and getColumn methods that use
 * the line and column number provided by the token.
 *
 * @author Petra Malik
 */
public class CztReader
  extends Reader
{
  /**
   * The scanner used to provide the tokens.
   */
  private final Lexer lexer_;

  /**
   * Left over charcters from the previous read call.
   * This character should be used first when the next read method is called.
   * It is set to <code>null</code> if no more characters are available.
   */
  private String buffer_ = "";

  /**
   * Number of characters provided by the scanner.
   * If <code>buffer_</code> is the empty string, this number is
   * equal to the number of characters sent so far.
   */
  private int charNum_ = 0;

  /**
   * Maps character numbers to LocInfo.
   */
  private final TreeMap<Integer,LocInfo> map_ = new TreeMap<Integer,LocInfo>();

  /**
   * Create a new character-stream reader
   * whose critical sections will synchronize on the reader itself.
   */
  public CztReader(Lexer lexer)
  {
    super();
    if (lexer == null) throw new NullPointerException();
    lexer_ = lexer;
  }

  /**
   * Create a new character-stream reader
   * whose critical sections will synchronize on the given object.
   */
  public CztReader(Lexer lexer, Object lock)
  {
    super(lock);
    if (lexer == null) throw new NullPointerException();
    lexer_ = lexer;
  }

  public void close()
  {
  }

  public int read(char[] cbuf, int off, int len)
    throws IOException
  {
    if (buffer_ == null) return -1;
    while (buffer_.length() < len) {
      LocToken s = lexer_.next();
      if (s == null) {
        if (buffer_.length() == 0) return -1;
        for (int i = 0; i < buffer_.length(); i++) {
          cbuf[off + i] = buffer_.charAt(i);
        }
        int result = buffer_.length();
        buffer_ = null;
        return result;
      }
      if (s.spelling() != null) {
        buffer_ += s.spelling();
        map_.put(charNum_, s.getLocation());
        charNum_ += s.spelling().length();
      }
    }
    for (int i = 0; i < len; i++) {
      cbuf[off + i] = buffer_.charAt(i);
    }
    buffer_ = buffer_.substring(len);
    return len;
  }

  public int getLine(int charNum)
  {
    return get(charNum).getLine();
  }

  public int getColumn(int charNum)
  {
    return get(charNum).getColumn();
  }

  public LocInfo getLocation(int charNum)
  {
    return get(charNum);
  }

  protected LocInfo get(int value)
  {
    LocInfo result = map_.get(value);
    if (result == null) {
      SortedMap<Integer,LocInfo> smap = map_.headMap(value);
      try {
        Integer lastKey = smap.lastKey();
        result = smap.get(lastKey);
      }
      catch (NoSuchElementException e) {
        return new LocInfoImpl(lexer_.getDialect(), null, -1, -1);
      }
    }
    return result;
  }
}
