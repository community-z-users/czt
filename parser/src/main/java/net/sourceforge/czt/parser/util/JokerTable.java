/*
  Copyright (C) 2005 Tim Miller, Mark Utting
  Copyright (C) 2005, 2006 Petra Malik
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
  private Map<String, Jokers> jokers_ = new HashMap<String, Jokers>();

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

  public JokerType getTokenType(String name)
  {
    Jokers jokers = jokers_.get(name);
    if (jokers != null) return jokers.getKind();
    return null;
  }

  public void add(Jokers jokers)
    throws JokerException
  {
    List<String> names = jokers.getName();
    for (String name : names) {
      addTokenType(name, jokers);
    }
  }

  /**
   * Adds a new association from a decl name to joker token.
   *
   * throws JokerException if an association of the same name already
   * exists.
   */
  private void addTokenType(String name, Jokers jokers)
    throws JokerException
  {
    final Jokers existingJokers = jokers_.get(name);
    if (existingJokers != null) {
      String message = "Duplicate joker name " + name;
      LocAnn locAnn = (LocAnn) jokers.getAnn(LocAnn.class);
      if (locAnn != null) {
        if (locAnn.getLine() != null) {
          message += " at line " + locAnn.getLine();
        }
        if (locAnn.getCol() != null) {
          message += " column " + locAnn.getCol();
        }
        if (locAnn.getLoc() != null) {
          message += " in " + locAnn.getLoc();
        }
      }
      throw new JokerException(message);
    }
    jokers_.put(name, jokers);
  }

  /**
   *
   * @czt.todo reimplement this method exploiting the fact that table
   *           <code>jokers_</code> is ordered.
   */
  private void addJokerTable(JokerTable parentTable)
    throws JokerException
  {
    final Set<Map.Entry<String, Jokers>> parentJokers =
      parentTable.jokers_.entrySet();
    for (Map.Entry<String, Jokers> entry : parentJokers) {
      addTokenType(entry.getKey(), entry.getValue());
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
