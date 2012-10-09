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

import java.util.List;

/**
 * Records the details of a section header.
 * 
 * @author ian
 */
public final class HeaderBlock extends Block
{
  /** Name of this section */
  private String name_;

  /** Names of parents of this section */
  private List<String> parents_;

  /**
   * Constructs a header block.
   * 
   * @param text characters in this section header
   * @param isBufferingWanted whether to remember <code>text</code>
   * @param lineNo starting line number
   * @param columnNo starting column number
   * @param charNo starting character number
   * @param name section name in this section header
   * @param parents names of parents of this section header
   */
  public HeaderBlock(StringBuilder text, boolean isBufferingWanted, int lineNo, int columnNo, int charNo, String name, List<String> parents)
  {
    super(text, isBufferingWanted, lineNo, columnNo, charNo);
    name_ = name;
    parents_ = parents;
  }

  /**
   * Projects name field.
   * 
   * @return section name in this section header
   */
  public String getName()
  {
    return name_;
  }

  /**
   * Projects parents field.
   * 
   * @return names of parents in this section header
   */
  public List<String> getParents()
  {
    return parents_;
  }
}
