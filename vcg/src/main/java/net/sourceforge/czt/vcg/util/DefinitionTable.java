/*
  Copyright (C) 2011 Leo Freitas
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

import java.util.AbstractSet;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Iterator;
import java.util.List;
import java.util.SortedMap;
import java.util.Set;
import java.util.TreeMap;
import net.sourceforge.czt.parser.util.InfoTable;
import net.sourceforge.czt.parser.util.InfoTable.InfoTableException;
import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.z.util.PrintVisitor;
import net.sourceforge.czt.z.util.ZUtils;


/**
 * A definition table stores all the global definitions of a section.
 *
 * @author Leo Freitas
 */
public class DefinitionTable extends InfoTable
{
  protected static final boolean DEFTBL_PRINTVISITOR_UNICODE = false;
  protected static final PrintVisitor printVisitor_ = new PrintVisitor(DEFTBL_PRINTVISITOR_UNICODE);

  /**
   * Records all operators defined in this section.
   */
  // SortedMap<knownSections_.indexOf(sectName), SortedMap<DeclName, Def>>
  // invariant knownSections_.size() == definitions_.keySet().size();
  private final /*@non_null@*/ SortedMap<Integer, SortedMap<ZName, Definition>> definitions_;

  /**
   * known sections in order
   */
  private final List<String> knownSections_;

  /**
   * Constructs a definition table for a new section. Changed the originally
   * public method to be protected. One should not directly update the DefinitionTable,
   * but use the lookup algorithm from the DefinitionTableVisitor instead.
   *
   * @param sectionName
   * @param parents Definition tables of all direct parents of the new section.
   * @throws DefinitionException
   */
  protected DefinitionTable(String sectionName,
                         Collection<DefinitionTable> parents)
    throws DefinitionException
  {
    super(sectionName);
    knownSections_ = new ArrayList<String>();
    definitions_ = new TreeMap<Integer, SortedMap<ZName, Definition>>();
    
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
    for (SortedMap.Entry<Integer, SortedMap<ZName, Definition>> defEntry : parentTable.definitions_.entrySet())
    {
      Integer sectIndex = defEntry.getKey();
      assert parentTable.knownSections_.size() > sectIndex;
      String sectName = parentTable.knownSections_.get(sectIndex);
      assert sectName != null;
      for(Definition def : defEntry.getValue().values())
      {
        try
        {
          addGlobalDecl(sectName, def);
        }
        catch (DefinitionException e)
        {
          exceptions.add(e);
        }
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

  private void checkSectionConsistency(String sectName, Definition def)
     throws DefinitionException
  {
    if (!def.getSectionName().equals(sectName))
    {
      final String message = "Inconsistent sections within defined name: " +
              printName(def.getDefName()) + ". Given " + sectName +
              ", declared section is " + def.getSectionName() +
              " in DefTbl for " + getSectionName();
      throw new DefinitionException(message);
    }
    checkSectionConsistency(sectName, def.getLocalDecls().values());
  }

  private void checkSectionConsistency(String sectName, Collection<Definition> defs)
          throws DefinitionException
  {
    if (defs != null)
    {
      for(Definition d : defs)
      {
       checkSectionConsistency(sectName, d);
      }
    }
  }

  private void checkGlobalDef(String sectName, Definition def)
    throws DefinitionException
  {
    // only glogal allowed here
    if (!def.getDefinitionKind().isGlobal())
    {
      final String message = "Definition kind is not top-level declaration in "
              + sectName + "\n\t" + def ;
      throw new DefinitionException(message);
    }
  }

  protected void addGlobalDecl(String sectName, Definition def)
    throws DefinitionException
  {
    assert def != null && def.getSectionName() != null;
    assert sectName != null && !sectName.isEmpty();

    checkGlobalDef(sectName, def);

    // check sect names are consistent, even if different from getSectionName() of this table.
    checkSectionConsistency(sectName, def);

    // get / create defs for calling section
    SortedMap<ZName, Definition> defOfSect;
    int key = knownSections_.indexOf(sectName);
    if (key == -1)
    {
      knownSections_.add(sectName);
      key = knownSections_.indexOf(sectName);
      assert key >= 0 && !definitions_.containsKey(key);
      defOfSect = new TreeMap<ZName, Definition>(ZUtils.ZNAME_COMPARATOR);
      SortedMap<ZName, Definition> old = definitions_.put(key, defOfSect);
      if (old != null)
        throw new DefinitionException("Inconsistent (new) definition indexes for " + sectName);
    }
    else
    {
      if (!definitions_.containsKey(key))
        throw new DefinitionException("Inconsistent (old) definition indexes for " + sectName);
      defOfSect = definitions_.get(key);
    }
    assert defOfSect != null && key >= 0;
    assert knownSections_.size() >= definitions_.keySet().size();

    // add definition or raise duplicates
    Definition old = defOfSect.put(def.getDefName(), def);
    if (old != null)
    {
      final String message = "Duplicated def \"" +
              printName(def.getDefName()) + "\" from section " +
              def.getSectionName() + " in section " + getSectionName();
      throw new DefinitionException(message);
    }
  }

  protected SortedMap<ZName, Definition> getDefinitions(String sectName)
  {
    assert knownSections_.size() >= definitions_.keySet().size();
    return definitions_.get(knownSections_.indexOf(sectName));
  }

  public Set<Definition> lookupDefinitions(final String sectName)
  {
    assert sectName != null;
    final SortedMap<ZName, Definition> result = getDefinitions(sectName);
    final Set<Definition> res = new AbstractSet<Definition>()
    {
      @Override
      public Iterator<Definition> iterator()
      {
        return new Iterator<Definition>()
          {
            Iterator<Definition> iterator = result != null ? 
              result.values().iterator() : Collections.<Definition>emptySet().iterator();

            @Override
            public boolean hasNext()
            {
              return iterator.hasNext();
            }

            @Override
            public Definition next()
            {
              Definition answer = iterator.next();
              //checkSectionConsistency(sectName, answer);
              return answer;
            }
            @Override
            public void remove()
            {
              throw new UnsupportedOperationException();
            }
          };
      }

      @Override
      public int size()
      {
        return result != null ? result.values().size() : 0;
      }
    };
    //checkSectionConsistency(sectName, result);
    //assert result.iterator().next().getSectionName().equals(sectName) for all elements;
    return Collections.unmodifiableSet(res);
  }

  /**
   * Looks up a unique name within the given sect.
   * @param sectName
   * @param name
   * @return
   */
  protected Definition lookupDeclName(String sectName, ZName name)
  {
    assert sectName != null && name != null;
    Definition result = null;
    SortedMap<ZName, Definition> map = getDefinitions(sectName);
    if (map != null)
    {
      result = map.get(name);
    }
    return result;
  }

  /**
   * Looks up a unique name within the current sect and its declared parents.
   * The name must be a global name according to {@link DefinitionKind#isGlobal() }.
   * @param name
   * @return
   */
  public Definition lookupDeclName(ZName name) 
  {
    Definition result = null;
    for (int i = knownSections_.size()-1; i >= 0; i--)
    {
      result = lookupDeclName(knownSections_.get(i), name);
      if (result != null)
      {
        if (!result.getDefinitionKind().isGlobal() &&
        !result.getDefinitionKind().isReference())
        {
          // throw? checkGlobalDef?
        }
        break;
      }
    }
    return result;
  }

  private Definition lookupLocalNames(Collection<Definition> defs, ZName name)
  {
    assert defs != null && name != null;
    Definition result = null;
    for (Definition def : defs)
    {
      SortedMap<ZName, Definition> locals = def.getLocalDecls();
      if (!locals.isEmpty())
      {
        result = locals.get(name);
        // if not found, look deeper
        if (result == null && !locals.values().isEmpty())
        {
          result = lookupLocalNames(locals.values(), name);
        }
        // if found, stop
        else
        {
          break;
        }
      }
    }
    return result;
  }

  public Definition lookupName(ZName name)
  {
    // look top-level
    Definition result = lookupDeclName(name);

    // if name is not top-level name, try locals
    if (result == null)
    {
      assert knownSections_.size() >= definitions_.keySet().size();
      for (int i = knownSections_.size()-1; i >= 0; i--)
      {
        SortedMap<ZName, Definition> defOfSect = definitions_.get(i);
        if (defOfSect != null)
        {
          result = defOfSect.get(name);
          // if not a top-level name, try local names
          if (result == null)
          {
            result = lookupLocalNames(defOfSect.values(), name);
          }
        }
      }
    }
    return result;
  }

  public Set<Definition> bindings(ZName defName) throws DefinitionException
  {
    Definition def = lookupDeclName(defName);
    // if this is a schema declaration, look for its bindings
    if (def != null && def.getDefinitionKind().isReference())
    {
//      HashSet<Definition> result = new HashSet<Definition>();
//      // lookup all def, in case of included from othe sections getSectDefinitions(def.getSectionName())
//      for(Definition defLookup : definitions_.values())
//      {
//        DefinitionKind defKind = defLookup.getDefinitionKind();
//
//        // if defLookup is a binding with the right name, add it
//        if (defKind.isSchemaBinding())
//        {
//          if (ZUtils.namesEqual(defName, defKind.getSchName()))
//            result.add(defLookup);
//        }
//        // if it is an inclusion, get the included name bindings as well if not the calee
//        else if (defKind.isSchemaInclusion())
//        {
//          Name defLookupName = defLookup.getDefName();
//          boolean isDeltaXi = ZUtils.isDeltaXi(defLookupName);
//          // get inner name if special
//          if (isDeltaXi)
//          {
//            defLookupName = ZUtils.getSpecialSchemaBaseName(ZUtils.assertZName(defLookupName));
//          }
//          if (
//              // if defLookupName is NEITHER: Delta/Xi nor self-referencing then
//              (!isDeltaXi && !ZUtils.namesEqual(defName, defLookupName))
//              ||
//              // if defLookup is: Delta/Xi yet not self-referencing then
//              (isDeltaXi && !ZUtils.assertZName(defLookupName).getWord().equals(
//                                                                ZUtils.assertZName(defName).getWord())))
//          {
//            result.addAll(bindings(defLookupName));
//
//            if (isDeltaXi)
//            {
//              List<Stroke> strokes = ZUtils.FACTORY.list();
//              strokes.add(ZUtils.FACTORY.createNextStroke());
//              defLookupName = ZUtils.buildName(defLookupName, strokes);
//              result.addAll(bindings(defLookupName));
//            }
//          }
//        }
//      }
      return null;//result;
    }
    else
    {
      throw new DefinitionException("Unknown schema name in DefTbl " + defName);
    }
  }

  public String toString(boolean printParents, boolean simple)
  {
    if (printParents)
      return toString();
    else
    {
      SortedMap<ZName, Definition> defs = getDefinitions(sectionName_);
      assert defs != null;
      StringBuilder buffer = new StringBuilder(defs.size() * 30);
      buffer.append("Definition table for ");
      buffer.append(sectionName_);
      buffer.append(" (with parrents hidden)");
      Iterator<SortedMap.Entry<ZName, Definition>> itE = defs.entrySet().iterator();
      buffer.append("\n\t");
      while (itE.hasNext())
      {
        SortedMap.Entry<ZName, Definition> entry2 = itE.next();
        buffer.append(printName(entry2.getKey()));
        buffer.append("\t\t= ");
        buffer.append(entry2.getValue().toString(simple));
        if (itE.hasNext())
               buffer.append("\n\t");
      }
      buffer.append('\n');
      return buffer.toString();
    }
  }

  @Override
  public String toString()
  {
    StringBuilder buffer = new StringBuilder(definitions_.size() * 30);
    buffer.append("Definition table for ");
    buffer.append(sectionName_);
    if (!definitions_.isEmpty())
    {
      buffer.append("\n\t");
      Iterator<SortedMap.Entry<Integer, SortedMap<ZName, Definition>>> it = definitions_.entrySet().iterator();
      while (it.hasNext())
      {
         SortedMap.Entry<Integer, SortedMap<ZName, Definition>> entry = it.next();
         Integer key = entry.getKey();
         assert knownSections_.size() > key;
         buffer.append(knownSections_.get(key));
         buffer.append("\t= {");
         if (!entry.getValue().isEmpty())
         {
           Iterator<SortedMap.Entry<ZName, Definition>> itE = entry.getValue().entrySet().iterator();
           buffer.append("\n\t\t");
           while (itE.hasNext())
           {
             SortedMap.Entry<ZName, Definition> entry2 = itE.next();
             buffer.append(printName(entry2.getKey()));
             buffer.append("\t= ");
             buffer.append(entry2.getValue().toString());
             if (itE.hasNext())
               buffer.append("\n\t\t");
           }
         }
         buffer.append("}\n\t");
      }
    }
    buffer.append('\n');
    return buffer.toString();
  }

  public static String printName(ZName name)
  {
    return name.accept(printVisitor_);
  }

  /** This interface allows visitors to visit definitions.
   * @param <T>
   */
  public interface DefinitionVisitor<T>
  {
    T visitDefinition(Definition def);
  }
}
