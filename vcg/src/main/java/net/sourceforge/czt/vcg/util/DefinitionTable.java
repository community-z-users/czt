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

package net.sourceforge.czt.vcg.util;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map.Entry;
import java.util.Set;
import java.util.SortedMap;
import java.util.TreeMap;
import net.sourceforge.czt.parser.util.InfoTable;
import net.sourceforge.czt.parser.util.InfoTable.InfoTableException;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.Name;
import net.sourceforge.czt.z.ast.Stroke;
import net.sourceforge.czt.z.ast.Type2;
import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.z.ast.ZNameList;
import net.sourceforge.czt.z.util.PrintVisitor;
import net.sourceforge.czt.z.util.ZUtils;


/**
 * A definition table stores all the global definitions of a section.
 */
public class DefinitionTable extends InfoTable
{
  protected static final boolean DEFTBL_PRINTVISITOR_UNICODE = false;
  protected static final PrintVisitor printVisitor_ = new PrintVisitor(DEFTBL_PRINTVISITOR_UNICODE);

  /**
   * Records all operators defined in this section.
   *
   * @czt.todo should the domain be String or Name? ZUtils has a Name comparator,
   *           so it would be fine I (Leo) rather prefer this solution. Yet, there
   *           are the needs of ZPatt and jokers, which I am not familiar. Opinions?
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
  protected DefinitionTable(String sectionName,
                         Collection<DefinitionTable> parents)
    throws DefinitionException
  {
    super(sectionName);
    
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
        throw new DefinitionException(message, exceptions);
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
    List<DefinitionException> exceptions = new ArrayList<DefinitionException>();

    // process them one-by-one, so add can check for duplicates.
    for (Entry<String, Definition> defEntry : parentTable.definitions_.entrySet())
    {
      try
      {
        // TODO: this is not checking tyhat defEntry.getKey().equals(defEntry.getValue().getDeclName().accept(printVisitor_))
        //       this would go away if we use Name as key. In any case, parents must use the add(Name,Def) method, which
        //       does do this check. And the add(String, Def) method is now private.
        add(defEntry.getKey(), defEntry.getValue());
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
      throw new DefinitionException("DEFTBL-ADDPARENT", exceptions);
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

  public Definition lookup(Name defname)
  {
    if (defname instanceof ZName)
    {
      ZName zn = (ZName)defname;
      String declName = zn.accept(printVisitor_);
      return lookup(declName);
    }
    return null;
  }
  
  public Set<Definition> bindings(Name defName) throws DefinitionException
  {
    Definition def = lookup(defName);
    // if this is a schema declaration, look for its bindings
    if (def != null &&
            (def.getDefinitionKind().equals(DefinitionKind.SCHEMADECL) ||
             def.getDefinitionKind().equals(DefinitionKind.SCHEMAINCLUSION)))
    {
      HashSet<Definition> result = new HashSet<Definition>();
      // lookup all def, in case of included from othe sections getSectDefinitions(def.getSectionName())
      for(Definition defLookup : definitions_.values())
      {
        DefinitionKind defKind = defLookup.getDefinitionKind();

        // if defLookup is a binding with the right name, add it
        if (defKind.isSchemaBinding())
        {
          if (ZUtils.namesEqual(defName, defKind.getSchName()))
            result.add(defLookup);
        }
        // if it is an inclusion, get the included name bindings as well if not the calee 
        else if (defKind.isSchemaInclusion())
        {
          Name defLookupName = defLookup.getDefName();
          boolean isDeltaXi = ZUtils.isDeltaXi(defLookupName);
          // get inner name if special
          if (isDeltaXi)
          {
            defLookupName = ZUtils.getSpecialSchemaBaseName(ZUtils.assertZName(defLookupName));
          }
          if (
              // if defLookupName is NEITHER: Delta/Xi nor self-referencing then  
              (!isDeltaXi && !ZUtils.namesEqual(defName, defLookupName))
              ||
              // if defLookup is: Delta/Xi yet not self-referencing then
              (isDeltaXi && !ZUtils.assertZName(defLookupName).getWord().equals(
                                                                ZUtils.assertZName(defName).getWord())))
          {
            result.addAll(bindings(defLookupName));

            if (isDeltaXi)
            {
              List<Stroke> strokes = ZUtils.FACTORY.list();
              strokes.add(ZUtils.FACTORY.createNextStroke());
              defLookupName = ZUtils.buildName(defLookupName, strokes);
              result.addAll(bindings(defLookupName));
            }
          }
        }
      }
      return result;
    }
    else
    {
      throw new DefinitionException("Unknown schema name in DefTbl " + defName);
    }
  }

  public Collection<Definition> getSectDefinitions(String sectName)
  {
    ArrayList<Definition> result = new ArrayList<Definition>(definitions_.values());
    Iterator<Definition> it = result.iterator();
    while (it.hasNext())
    {
      Definition def = it.next();
      if (!def.getSectionName().equals(sectName))
        it.remove();
    }
    return result;
  }

  @Override
  public String toString()
  {
    return "DefinitionTable for " + sectionName_ + "\n" + definitions_;
  }

  protected void add(Name declName, Definition def)
    throws DefinitionException
  {
    final String defName = declName.accept(printVisitor_);
    if (!ZUtils.namesEqual(declName, def.getDefName()))
    {
      throw new DefinitionException("Inconsistent names: " + declName
              + " must equal defined name " + def.getDefName());
    }
    add(defName, def);
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
  private void add(String defName, Definition def)
    throws DefinitionException
  {
    assert defName != null && !defName.isEmpty() && def != null :
      "Invalid definition name and value to add to definition table: name = " + defName + "; value = " + def;

    Definition old = definitions_.put(defName, def);
    if (old != null && ! old.getSectionName().equals(def.getSectionName()))
    {
      // TODO: why is it okay to have it in different section? Well, the parent section update needs to take care of duplicates then?
      final String message = "Duplicated def \"" + defName + "\" in " + def.getSectionName();
      throw new DefinitionException(message);
    }
  }

  /**
   * @czt.todo How should this class look like?
   */
  public static class DefinitionException
    extends InfoTable.InfoTableException
  {
    private final List<DefinitionException> exceptions_;

    public DefinitionException(String message)
    {
      super(message);
      exceptions_ = null;
    }

    public DefinitionException(String message, Throwable cause)
    {
      super(message, cause);
      exceptions_ = null;
    }

    public DefinitionException(String message, List<DefinitionException> exceptions)
    {
      super(message);
      exceptions_ = Collections.unmodifiableList(exceptions);
    }

    public DefinitionException(String message, Throwable cause, List<DefinitionException> exceptions)
    {
      super(message, cause);
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

  /** This defines a definition, including its name.
   *  That is, for the generic definition g[T,U] = T \fun U,
   *  this Definition records the type parameters T,U,
   *  the right hand side expression, the name, and the kind
   *  of definition it is given the context where it appeared.
   *  If types are available, a carrier set is also attached; it's null otherwise.
   */
  public static class Definition extends InfoTable.Info
  {
    private final Name defName_;
    private final ZNameList genericParams_;
    private final Expr definition_;
    private final DefinitionKind defKind_;
    private final Type2 carrierSet_;

    /**
     * Each definition has its section name, generic list, declared expression,
     * carrier set (if type information is available), and the kind of definition.
     * @param sectName
     * @param defName 
     * @param generic
     * @param definition
     * @param unifiedType
     * @param carrierSet
     * @param definitionKind
     * @param definitionType
     */
    protected Definition(String sectName, Name defName, ZNameList generic,
            Expr definition, Type2 carrierSet, DefinitionKind definitionKind)
    {
      super(sectName);
      assert generic != null && defName != null && definition != null && definitionKind != null;
      genericParams_ = generic;
      defName_ = defName;
      definition_ = definition;
      defKind_ = definitionKind;
      carrierSet_ = carrierSet; // type maybe null
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
    public DefinitionKind getDefinitionKind()
    {
      return defKind_;
    }

    /**
     * Carrier set, if available; null otherwise.
     * @return
     */
    public Type2 getCarrierSet()
    {
      return carrierSet_;
    }

    public Name getDefName()
    {
      return defName_;
    }

    public ZName getDefZName()
    {
      return ZUtils.assertZName(defName_);
    }

    // Add \n\t here since it is likely to appear from within a DefTable.
    @Override
    public String toString()
    {
      return "\n\t " + definition_.toString()
             + "\n\t DEFNAME = " + defName_.accept(printVisitor_)
             + "\n\t " + (genericParams_.isEmpty() ? "" :
                    "GENERICS= " + genericParams_.toString() 
                    + "\n\t ") 
             +      "KIND    = " + getSectionName() + "." + defKind_.toString()
             + (carrierSet_ == null ? "" :
               "\n\t CARSET  = " + carrierSet_.toString());
    }

    @Override
    public boolean equals(Object o)
    {
      boolean result = (o == this);
      if (!result && o instanceof Definition)
      {
        Definition d = (Definition)o;
        result = this.getSectionName().equals(d.getSectionName()) &&
                 this.defName_.equals(d.defName_) &&
                 this.defKind_.equals(d.defKind_) &&
                 this.genericParams_.equals(d.genericParams_);
      }
      return result;
    }

    @Override
    public int hashCode()
    {
      int hash = 7;
      hash = 29 * hash + this.getSectionName().hashCode();
      hash = 29 * hash + this.defName_.hashCode();
      hash = 29 * hash + this.defKind_.hashCode();
      hash = 29 * hash + this.genericParams_.hashCode();
      return hash;
    }
  }
}
