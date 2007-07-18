/*
  Copyright (C) 2004, 2007 Petra Malik
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

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.impl.TermImpl;
import net.sourceforge.czt.util.Visitor;
import net.sourceforge.czt.z.ast.*;

/**
 * A definition table stores all the global definitions of a section.
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
   * @czt.todo should the domain be String or Name?
   */
  private /*@non_null@*/ SortedMap<String,Definition> definitions_ =
    new TreeMap<String,Definition>();

  /**
   * Constructs a definition table for a new section.
   *
   * @param parents Definition tables of all direct parents of the new section.
   */
  public DefinitionTable(String section,
                         Collection<DefinitionTable> parents)
    throws DefinitionException
  {
    section_ = section;
    if (parents != null) {
      for (DefinitionTable table : parents) {
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
  public static class DefinitionException
    extends Exception
  {
    public DefinitionException(String message)
    {
      super(message);
    }
  }

  /** This interface allows visitors to visit definitions. */
  public interface DefinitionVisitor<T>
  {
    T visitDefinition(Definition def);
  }
  
  /** This defines a definition, but without the name.
   *  That is, for the generic definition g[T,U] = T \fun U,
   *  this Definition records the type parameters T,U and
   *  the right hand side expression.
   */
  public static class Definition
  {
    private final ZNameList genericParams_;
    private final Expr definition_;
    private final DefinitionType defType_;

    public Definition(ZNameList generic, Expr definition, DefinitionType definitionType)
    {
      assert generic != null && definition != null && definitionType != null;
      genericParams_ = generic;
      definition_ = definition;
      defType_ = definitionType;
    }

    /** Returns the list of generic type parameters of this definition.
     *  It never returns null, so if the definition has no generic
     *  parameters, it returns an empty list.
     * @return List of the names of any type parameters.
     */
    public ZNameList getDeclNames()
    {
      return genericParams_;
    }

    /** For an equality definition (name==expr), this returns the
     *  right-hand side of the definition, expr.
     *  For a variable declaration (name:expr), this returns the type
     *  expression, expr.  Note that this is often more specific than
     *  the carrier set of name (as returned by the typechecker).
     */
    public Expr getExpr()
    {
      return definition_;
    }
    
    /** Tells you whether this name was declared via a constant
     * definition, or a variable declaration.
     * @return
     */
    public DefinitionType getDefinitionType() 
    {
      return defType_;
    }

    public String toString()
    {
      return genericParams_.toString() + " " + definition_.toString() + " [" + defType_.toString() + "]";
    }
  }
}
