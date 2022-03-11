/*
  Copyright (C) 2008 Ian Toyn
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

package net.sourceforge.czt.specreader;

/**
 * Records the common fields of any block from a file.
 * 
 * @author ian
 */
public abstract class Block
{
  /** Characters in block */
  private StringBuilder text_;

  /** Starting line number, counting from 1 */
  private int lineNo_;

  /** Starting column number, counting from 1 */
  private int columnNo_;

  /** Starting character number, counting from 0 */
  private int charNo_;

  /** Number of characters in block */
  private int length_;

  /**
   * Constructs a block.
   * 
   * @param text characters in this block
   * @param isBufferingWanted whether to remember <code>text</code>
   * @param lineNo starting line number
   * @param columnNo starting column number
   * @param charNo starting character number
   */
  public Block(StringBuilder text, boolean isBufferingWanted, int lineNo, int columnNo, int charNo)
  {
    text_ = isBufferingWanted? text : null;
    lineNo_ = lineNo;
    columnNo_ = columnNo;
    charNo_ = charNo;
    length_ = text.length();
    //System.err.format("Block charNo %d length %d%n", charNo, length);
  }

  /**
   * Projects the charNo field.
   * 
   * @return starting character number
   */
  public int getCharNo()
  {
    return charNo_;
  }

  /**
   * Projects the length field.
   * 
   * @return number of characters in block
   */
  public int getLength()
  {
    return length_;
  }

  /**
   * Returns a %%Zloc directive saying where the text of this block came from
   * 
   * @return %%loc directive
   */
  public String getLocDir()
  {
    return "%%Zloc "+lineNo_+"#"+columnNo_+"@"+charNo_+ZFileReader.NL;
  }

  /**
   * Returns the text of this block.
   */
  @Override
  public String toString()
  {
    return text_.toString();
  }
}
