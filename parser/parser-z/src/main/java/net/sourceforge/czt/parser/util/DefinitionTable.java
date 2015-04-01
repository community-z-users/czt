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

import java.util.Collections;
import java.util.Map.Entry;
import java.util.logging.Logger;
import net.sourceforge.czt.base.util.PerformanceSettings;
import net.sourceforge.czt.session.Dialect;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.z.ast.*;

/**
 * A definition table stores all the global definitions of a section.
 */
public class DefinitionTable extends InfoTable
{
  private static final Logger logger_ = Logger.getLogger(SectionManager.class.getName());

  /**
   * Records all operators defined in this section.
   *
   * @czt.todo should the domain be String or Name?
   */
  private final /*@non_null@*/ SortedMap<String,Definition> definitions_ =
    new TreeMap<String,Definition>();
  

  /**
   * Constructs a definition table for a new section. Changed the originally
   * public method to be protected. One should not directly update the DefinitionTable,
   * but use the lookup algorithm from the DefinitionTableVisitor instead.
   *
   * @param sectionName
   * @param parents Definition tables of all direct parents of the new section.
   * @throws net.sourceforge.czt.parser.util.DefinitionTable.DefinitionException
   */
  protected DefinitionTable(Dialect d, String sectionName,
                         Collection<DefinitionTable> parents)
    throws DefinitionException
  {
    super(d, sectionName);

    // do not use InfoTable.addParents in this specialised case
    // in a constructor, we shall not override addParents either :-(
    if (parents != null)
    {
      // collect all exceptions in one chain of throwable causes
      // rather than stopping the collection upon finding the
      // first duplication problem. This way, we leave room for
      // whoever is calling this method to deal with a complete
      // definition table appropriately.
      List<DefinitionException> exceptions = new ArrayList<DefinitionException>(parents.size());
      for (DefinitionTable table : parents)
      {
        try
        {
          addParentDefinitionTable(table);
        }
        catch(DefinitionException e)
        {
          // collect the exception and carry on
          exceptions.add(e);
        }
      }
      // throw exception if one only, or throw their list otherwise
      if (exceptions.size() == 1)
      {
        throw exceptions.get(0);
      }
      else if (exceptions.size() > 1)
      {
        final String message = "Multiple definition exceptions when creating definition" +
          "table. They happened while processing parents for section " + sectionName +
          ". This occurs either because the section is not typechecked, or because type-compatible " +
          "names (i.e., those with different declared types but same carrier set) are repeated.";
        logger_.warning(message + " with exceptions " + exceptions.toString());
        throw new DefinitionException(d, message, exceptions);
      }
    }
  }

  @Override
  protected <T extends InfoTable> void addParentTable(T table) throws InfoTableException
  {
    addParentDefinitionTable((DefinitionTable)table);
  }
  
  private void addParentDefinitionTable(DefinitionTable parentTable)
    throws DefinitionException
  {
    assert parentTable != null;

    // collect all exceptions from this one parent.
    List<DefinitionException> exceptions = new ArrayList<DefinitionException>(PerformanceSettings.INITIAL_ARRAY_CAPACITY);

    // process them one-by-one, so add can check for duplicates.
    for (Entry<String, Definition> def : parentTable.definitions_.entrySet()) 
    {
      try
      {
        add(def.getKey(), def.getValue());
      }
      catch (DefinitionException e)
      {
        exceptions.add(e);
      }
    }

    if (exceptions.size() == 1)
    {
      throw exceptions.get(0);
    }
    else if (exceptions.size() > 1)
    {
      throw new DefinitionException(getDialect(), "DEFTBL-ADDPARENT", exceptions);
    }
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
    return definitions_.get(defname);
  }

  @Override
  public String toString()
  {
    return "DefinitionTable for " + getSectionName() + "\n" + definitions_;
  }

  /**
   * Adds a new definition. Changed the originally public method to be
   * protected. One should not directly update the DefinitionTable, but
   * use the lookup algorithm from the DefinitionTableVisitor instead.
   *
   * @param defName
   * @param def
   * @throws DefinitionException if definition is incompatible
   *                           with existing definitions.
   */
  protected void add(String defName, Definition def)
    throws DefinitionException
  {
    assert defName != null && !defName.isEmpty() && def != null :
      "Invalid definition name and value to add to definition table: name = " + defName + "; value = " + def;

    Definition old = definitions_.put(defName, def);
    if (old != null && ! old.getSectionName().equals(def.getSectionName()))
    {
      final String message = "Duplicated def \"" + defName + "\" in " + getSectionName()
    		  + " from " + old.getSectionName();
      // MarkU: 2/4/2015 downgraded this to a warning, because it stops ZLive working
      //throw new DefinitionException(getDialect(), message);
      System.err.println("WARNING: " + message);  
      logger_.warning(message);
    }
  }

  /**
   * @czt.todo How should this class look like?
   */
  public static class DefinitionException
    extends InfoTable.InfoTableException
  {
    /**
	 * 
	 */
	private static final long serialVersionUID = 3082756228588908110L;
	private final List<DefinitionException> exceptions_;

    public DefinitionException(Dialect d, String message)
    {
      super(d, message);
      exceptions_ = null;
    }

    public DefinitionException(Dialect d, String message, Throwable cause)
    {
      super(d, message, cause);
      exceptions_ = null;
    }

    public DefinitionException(Dialect d, String message, List<DefinitionException> exceptions)
    {
      super(d, message);
      exceptions_ = Collections.unmodifiableList(exceptions);
    }

    public DefinitionException(Dialect d, String message, Throwable cause, List<DefinitionException> exceptions)
    {
      super(d, message, cause);
      exceptions_ = Collections.unmodifiableList(exceptions);
    }

    public List<DefinitionException> getExceptions()
    {
      return exceptions_;
    }

    @Override
    public String toString()
    {
      String result = super.toString();
      if (exceptions_ != null)
      {
        result += " with inner definition exceptions list as ";
        result += exceptions_.toString();
      }
      return result;
    }
  }

  /** This interface allows visitors to visit definitions.
   * @param <T>
   */
  public interface DefinitionVisitor<T>
  {
    T visitDefinition(Definition def);
  }

  /** This defines a definition, but without the name.
   *  That is, for the generic definition g[T,U] = T \fun U,
   *  this Definition records the type parameters T,U and
   *  the right hand side expression.
   */
  public static class Definition extends InfoTable.Info
  {
    private final ZNameList genericParams_;
    private final Expr definition_;
    private final DefinitionType defType_;

    public Definition(String sectName, ZNameList generic, Expr definition, DefinitionType definitionType)
    {
      super(sectName);
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
     * @return
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

    @Override
    public String toString()
    {
      return genericParams_.toString() + " " + definition_.toString() + " [" + defType_.toString() + "]";
    }
  }
}
