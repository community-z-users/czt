/**
Copyright (C) 2004 Petra Malik
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

import net.sourceforge.czt.z.ast.*;

/**
 * A definition table stores all the definitions of a section.
 */
public class DefinitionTable
{
  /**
   * The name of the section.
   */
  private String section_;

  /**
   * Records all operators defined in this section.
   *
   * @czt.todo should the domain be String, Name or DeclName?
   */
  private /*@non_null@*/ SortedMap/*<String,Term>*/ definitions_ =
    new TreeMap();

  /**
   * Constructs a definition table for a new section.
   *
   * @param parents Definition tables of all direct parents of the new section.
   */
  public DefinitionTable(String section,
                         Collection/*<DefinitionTable>*/ parents)
    throws DefinitionException
  {
    section_ = section;
    if (parents != null) {
      for (Iterator iter = parents.iterator(); iter.hasNext();) {
        DefinitionTable table = (DefinitionTable) iter.next();
        addParentDefinitionTable(table);
      }
    }
  }

  /**
   *
   * @czt.todo Really throw the exception.
   */
  private void addParentDefinitionTable(DefinitionTable parentTable)
    throws DefinitionException
  {
    definitions_.putAll(parentTable.definitions_);
  }

  public String getSection()
  {
    return section_;
  }

  /**
   * Looks up a definition to see if it is defined
   * in this section or in any of the ancestor sections.
   *
   * @param defname The definition name.
   * @return       Returns <code>null</code> if <code>defname</code>
   *               is not defined.
   */
  public Definition lookup(String /*@non_null@*/ defname)
  {
    return (Definition) definitions_.get(defname);
  }

  public String toString()
  {
    return "DefinitionTable for " + section_ + "\n" + definitions_;
  }

  /**
   * Adds a new definition.
   *
   * @throws DefinitionException if definition is incompatible
   *                           with existing definitions.
   */
  public void add(String defName, Definition def)
    throws DefinitionException
  {
    definitions_.put(defName, def);
  }

  /**
   * @czt.todo How should this class look like?
   */
  public class DefinitionException
    extends Exception
  {
    public DefinitionException(String message)
    {
      super(message);
    }
  }

  public static class Definition
  {
    private List genericParams_;
    private Expr definition_;

    public Definition(List generic, Expr definition)
    {
      genericParams_ = generic;
      definition_ = definition;
    }

    public List getDeclNames()
    {
      return genericParams_;
    }

    public Expr getExpr()
    {
      return definition_;
    }

    public String toString()
    {
      return genericParams_.toString() + " " + definition_.toString();
    }
  }
}
