/**
Copyright (C) 2005 Tim Miller, Mark Utting, Petra Malik
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

import java.util.*;

import net.sourceforge.czt.util.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.zpatt.ast.*;

/**
 * An joker table manages all the joker definitions of a section.
 * It provides search facilities for all the jokers defined in this
 * section or inherited from parent sections.
 */
public class JokerTable
{
  /**
   * The name of the section.
   */
  private String section_;

  /**
   * Records all jokers defined in this section.
   */
  private Map/*<String, int>*/ jokers_ = new HashMap();

  /**
   * Constructs a joker table for a new section, checking for duplicates.
   *
   * @param parents Joker tables of all direct parents of the new section.
   */
  public JokerTable(String section, Collection/*<JokerTable>*/ parents)
    throws JokerException
  {
    section_ = section;
    if (parents != null) {
      for (Iterator iter = parents.iterator(); iter.hasNext();) {
        JokerTable table = (JokerTable) iter.next();
        addJokerTable(table);
      }
    }
  }

  public String getSection()
  {
    return section_;
  }

  public JokerTokenType getTokenType(String name)
  {
    return (JokerTokenType) jokers_.get(name);
  }

  public void add(Jokers jokers)
    throws JokerException
  {
    LocAnn locAnn = (LocAnn) jokers.getAnn(LocAnn.class);
    String kind = jokers.getKind();
    List<String> names = jokers.getName();
    for (String name : names) {
      final int line = locAnn.getLine();
      final int col = locAnn.getCol();
      final String loc = locAnn.getLoc();
      addTokenType(name, kind, line, col, loc);
    }
  }

  /**
   * Adds a new association from a decl name to joker token.
   *
   * throws JokerException if an association of the same name already
   * exists.
   */
  private void addTokenType(String name, String type, String loc)
    throws JokerException
  {
    addTokenType(name, type, -1, -1, loc);
  }

  /**
   * Adds a new association from a decl name to joker token.
   *
   * throws JokerException if an association of the same name already
   * exists.
   */
  private void addTokenType(String name, String kind,
                            int line, int col, String loc)
    throws JokerException
  {
    final JokerTokenType existingType =
      (JokerTokenType) jokers_.get(name);
    if (existingType != null) {
      String message = "Joker name " + name + " already defined ";
      if (line >= 0)  message += " at line " + line;
      if (col >= 0) message += " column " + col;
      message += " in " + loc;
      throw new JokerException(message);
    }
    JokerTokenType type = JokerTokenType.fromString(kind);
    jokers_.put(name, type);
  }

  /**
   *
   * @czt.todo reimplement this method exploiting the fact that table
   *           <code>jokers_</code> is ordered.
   */
  private void addJokerTable(JokerTable parentTable)
    throws JokerException
  {
    final Set<Map.Entry<String, JokerTokenType>> parentJokers =
      parentTable.jokers_.entrySet();
    for (Map.Entry<String, JokerTokenType> entry : parentJokers) {
      addTokenType(entry.getKey(), entry.getValue().toString(),
                   parentTable.getSection());
    }
  }

  /**
   * @czt.todo How should this class look like?
   */
  public static class JokerException
    extends Exception
  {
    public JokerException(String message)
    {
      super(message);
    }
  }
}
