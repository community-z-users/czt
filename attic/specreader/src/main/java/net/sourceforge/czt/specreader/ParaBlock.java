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
 * Records the details of a paragraph.
 * 
 * @author ian
 */
public abstract class ParaBlock extends Block
{
  /**
   * Constructs a paragraph block.
   * 
   * @param text characters in this paragraph
   * @param isBufferingWanted whether to remember <code>text</code>
   * @param lineNo starting line number
   * @param columnNo starting column number
   * @param charNo starting character number
   */
  public ParaBlock(StringBuilder text, boolean isBufferingWanted, int lineNo, int columnNo, int charNo)
  {
    super(text, isBufferingWanted, lineNo, columnNo, charNo);
  }
}
