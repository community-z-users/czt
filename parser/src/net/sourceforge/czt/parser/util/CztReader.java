/**
Copyright (C) 2003, 2004 Petra Malik
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

import java.io.*;
import java.util.NoSuchElementException;
import java.util.SortedMap;
import java.util.TreeMap;

import net.sourceforge.czt.java_cup.runtime.*;

/**
 * A reader for a list of Symbol.  In addition to the usual Reader
 * functionality there are getLine and getColumn methods that use
 * the line and column number provided by Symbol.
 */
public class CztReader
  extends Reader
{
  /**
   * The scanner used to provide the tokens.
   */
  private Scanner scanner_;

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
   * Maps character numbers to line numbers.
   */
  private TreeMap lineMap_ = new TreeMap();

  /**
   * Maps character numbers to column numbers.
   */
  private TreeMap columnMap_ = new TreeMap();

  /**
   * Create a new character-stream reader
   * whose critical sections will synchronize on the reader itself.
   */
  public CztReader(Scanner scanner)
  {
    super();
    scanner_ = scanner;
  }

  /**
   * Create a new character-stream reader
   * whose critical sections will synchronize on the given object.
   */
  public CztReader(Scanner scanner, Object lock)
  {
    super(lock);
    scanner_ = scanner;
  }

  public void close()
  {
  }

  public int read(char[] cbuf, int off, int len)
  {
    if (buffer_ == null) return -1;
    while (buffer_.length() < len) {
      Symbol s = null;
      try {
        s = scanner_.next_token();
      }
      catch (Exception e) {
        throw new RuntimeException(e);
      }
      if (s != null) {
        if (s.sym == LatexSym.EOF) {
          if (buffer_.length() == 0) return -1;
          for (int i = 0; i < buffer_.length(); i++) {
            cbuf[off + i] = buffer_.charAt(i);
          }
          int result = buffer_.length();
          buffer_ = null;
          return result;
        }
        else if (s.value != null) {
          buffer_ += s.value;
          lineMap_.put(new Integer(charNum_), new Integer(s.left));
          columnMap_.put(new Integer(charNum_), new Integer(s.right));
          charNum_ += ((String) s.value).length();
        }
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
    Integer iCharNum = new Integer(charNum);
    Integer result = (Integer) lineMap_.get(iCharNum);
    if (result == null) {
      SortedMap map = lineMap_.headMap(new Integer(charNum));
      try {
        Integer lastKey = (Integer) map.lastKey();
        result = (Integer) map.get(lastKey);
      }
      catch (NoSuchElementException e) {
        return 0;
      }
    }
    return result.intValue();
  }

  public int getColumn(int charNum)
  {
    Integer iCharNum = new Integer(charNum);
    Integer result = (Integer) columnMap_.get(iCharNum);
    if (result == null) {
      SortedMap map = columnMap_.headMap(new Integer(charNum));
      try {
        Integer lastKey = (Integer) map.lastKey();
        result = (Integer) map.get(lastKey);
      }
      catch (NoSuchElementException e) {
        return 0;
      }
    }
    return result.intValue();
  }
}
