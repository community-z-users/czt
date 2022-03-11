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
import java.util.ListIterator;
import java.util.Set;
import java.util.SortedMap;
import java.util.SortedSet;
import java.util.Stack;
import java.util.TreeMap;
import java.util.TreeSet;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.parser.util.InfoTable;
import net.sourceforge.czt.session.Dialect;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.Name;
import net.sourceforge.czt.z.ast.NameTypePair;
import net.sourceforge.czt.z.ast.NewOldPair;
import net.sourceforge.czt.z.ast.PipeExpr;
import net.sourceforge.czt.z.ast.PreExpr;
import net.sourceforge.czt.z.ast.SchExpr;
import net.sourceforge.czt.z.ast.Type2;
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
  /**
   * default flag for printing unicode or not = (false)
   */
  protected static final boolean DEFTBL_PRINTVISITOR_UNICODE = false;
  /**
   * console printing visitor
   */
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
   * stack of special bindings used to calculate whether to substitute or remove local bindings (e.g., rename/hiding)
   */
  private final Stack<List<NewOldPair>> specialBindingsStack_;

  /**
   * Constructs a definition table for a new section. Changed the originally
   * public method to be protected. One should not directly update the DefinitionTable,
   * but use the lookup algorithm from the DefinitionTableVisitor instead.
   *
   * @param sectionName
   * @param parents Definition tables of all direct parents of the new section.
   * @throws DefinitionException
   */
  protected DefinitionTable(Dialect d, String sectionName,
                         Collection<DefinitionTable> parents)
    throws DefinitionException
  {
    super(d, sectionName);
    knownSections_ = new ArrayList<String>();
    definitions_ = new TreeMap<Integer, SortedMap<ZName, Definition>>();
    specialBindingsStack_ = new Stack<List<NewOldPair>>();

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
        throw new DefinitionException(d, message, exceptions);
      }
    }
  }

  /**
   * Makes a structural (shallow) copy of this table
   * @param copy
   */
  protected DefinitionTable(DefinitionTable copy)
  {
    super(copy.getDialect(), copy.getSectionName());
    knownSections_ = new ArrayList<String>(copy.knownSections_);
    definitions_ = new TreeMap<Integer, SortedMap<ZName, Definition>>();
    specialBindingsStack_ = new Stack<List<NewOldPair>>();
    //specialBindingsStack_.addAll(copy.specialBindingsStack_);
    for(SortedMap.Entry<Integer, SortedMap<ZName, Definition>> entry : copy.definitions_.entrySet())
    {
      definitions_.put(entry.getKey(), new TreeMap<ZName, Definition>(entry.getValue()));
    }
    assert copy.specialBindingsStack_.isEmpty() : "auxiliary stack for hide/renaming bindings should be empty";
    assert knownSections_.equals(copy.knownSections_) && definitions_.equals(copy.definitions_);
  }

  /**
   * Adds a parent table to this one. Usually called during initial construction --- the
   * definition table does accumulate its parents definitions.
   * @param <T>
   * @param table
   * @throws net.sourceforge.czt.parser.util.InfoTable.InfoTableException
   */
  @Override
  protected <T extends InfoTable> void addParentTable(T table) throws InfoTableException
  {
    addParentDefinitionTable((DefinitionTable)table);
  }

  /**
   * adds all given parent table (e.g., it also checks the table is indeed of a parent,
   * throwing an exception if not) definitions as global definitions of the current child table.
   * It accumulates any exception
   * thrown in the process as a list for the one that might indeed be thrown.
   *
   * @param parentTable
   * @throws DefinitionException
   */
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
      // avoid processing the same parent twice in case it is multiply inherited
      if (!knownSections_.contains(sectName))
      {
        for(Definition def : defEntry.getValue().values())
        {
          try
          {
            addGlobalDecl(sectName, def);
            //addGlobalDecl(def.getSectionName(), def);
          }
          catch (DefinitionException e)
          {
            exceptions.add(e);
          }
        }
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
   * checks if the given definition, and all its local children have the
   * same section information as the section provided. this method is usually
   * called with sectName as the current section, but also as the table parents.
   * This check is recursive (see {@link #checkSectionConsistency(java.lang.String, java.util.Collection) }).
   * @param sectName
   * @param def
   * @throws DefinitionException
   */
  private void checkSectionConsistency(String sectName, Definition def)
     throws DefinitionException
  {
    if (!def.getSectionName().equals(sectName) && !knownSections_.contains(sectName))
    {
      final String message = "Inconsistent sections within defined name: " +
              printTerm(def.getDefName()) + ". Given " + sectName +
              ", declared section is " + def.getSectionName() +
              " in DefTbl for " + getSectionName();
      throw new DefinitionException(getDialect(), def.getDefName(), message);
    }
    // local names might be declared in another sections. So use the first name
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

  /**
   * check whether or not <code>def</code> has {@link DefinitionKind#isGlobal() }
   * throwing an exception if it doesn't.
   * @param sectName
   * @param def
   * @throws DefinitionException
   */
  public static void checkGlobalDef(String sectName, Definition def)
    throws DefinitionException
  {
    // only glogal allowed here
    if (!def.getDefinitionKind().isGlobal())
    {
      final String message = "Definition kind is not top-level declaration in "
              + sectName + "\n\t" + def ;
      throw new DefinitionException(def.getDialect(), def.getDefName(), message);
    }
  }

  /**
   * check whether or not <code>def</code> has {@link DefinitionKind#isGlobal() }
   * throwing an exception if it doesn't.
   * @param sectName
   * @param def
   * @throws DefinitionException
   */
  public static void checkLocalDef(String sectName, Definition def)
    throws DefinitionException
  {
    // only local allowed here --- although there is come mixed, like schemaReference (local+global)
    if (def.getDefinitionKind().isGlobal() && !def.getDefinitionKind().isLocal()) // TODO: this is not quite right
    {
      final String message = "Definition kind is not local declaration in "
              + sectName + "\n\t" + def ;
      throw new DefinitionException(def.getDialect(), def.getDefName(), message);
    }
  }


  /**
   * Adds the given definition for the current section. It checks that the
   * definition's section (and the section of all its local definitions, see {@link #checkSectionConsistency(java.lang.String, java.util.Collection) }
   * are indeed for the current section, and that it is a global definition, see {@link #checkGlobalDef(java.lang.String, net.sourceforge.czt.vcg.util.Definition) }.
   * It then finds the right indexes within the internal table structures to add this definition,
   * creating one if this is the first definition. Finally, it checks whether the definition is a
   * duplicate or not. In all these cases, it might thrown an exception.
   * @param def
   * @throws DefinitionException
   */
  protected void addGlobalDecl(Definition def) throws DefinitionException
  {
    addGlobalDecl(getSectionName(), def);
  }

  /**
   * Adds the given definition as a global definition within the given section name,
   * which is to be either the current section or one of its parents. This is only called
   * by {@link #addGlobalDecl(java.lang.String, net.sourceforge.czt.vcg.util.Definition) }.
   * @param sectName
   * @param def
   * @throws DefinitionException
   */
  private void addGlobalDecl(String sectName, Definition def)
    throws DefinitionException
  {
    assert def != null && def.getSectionName() != null;
    assert sectName != null && !sectName.isEmpty();

    checkGlobalDef(sectName, def);

    ZName defName = def.getDefName();

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
        throw new DefinitionException(getDialect(), defName, "Inconsistent (new) definition indexes for " + sectName);
    }
    else
    {
      if (!definitions_.containsKey(key))
        throw new DefinitionException(getDialect(), defName, "Inconsistent (old) definition indexes for " + sectName);
      defOfSect = definitions_.get(key);
    }
    assert defOfSect != null && key >= 0;
    assert knownSections_.size() >= definitions_.keySet().size();

    // check sect names are consistent, even if different from getSectionName() of this table.
    // do it after updating known sections, though.
    checkSectionConsistency(sectName, def);

    // add definition or raise duplicates
    Definition old = defOfSect.put(defName, def);
    if (old != null)
    {
      final String message = "Duplicated def \"" +
              printTerm(def.getDefName()) + "\" from section " +
              def.getSectionName() + " in section " + getSectionName();
      throw new DefinitionException(getDialect(), defName, message);
    }
  }

  /**
   * Get all the mapped definitions for a given section name.
   * This returns a map backed by the underlying table. That is,
   * changes to the resulting map, will imply changes in the table!
   * @param sectName
   * @return
   */
  protected SortedMap<ZName, Definition> getDefinitions(String sectName)
  {
    assert knownSections_.size() >= definitions_.keySet().size();
    return definitions_.get(knownSections_.indexOf(sectName));
  }

//  protected SortedSet<ZName> schemaDeclNamesFromType(SchemaType type)
//  {
//    SortedSet<ZName> result = new TreeSet<ZName>(ZUtils.ZNAME_COMPARATOR);
//    for(NameTypePair ntp : type.getSignature())
//    {
//      result.add(ntp.getZName());
//    }
//  }
//

  public DefinitionException checkOverallConsistency()
  {
    return checkOverallConsistency(false);
  }

  public DefinitionException checkOverallConsistency(boolean modifyDeclaredTypesOfColludedNames)
  {
    SortedSet<ZName> namesToFind = new TreeSet<ZName>(ZUtils.ZNAME_COMPARATOR);
    SortedSet<ZName> namesFound = new TreeSet<ZName>(ZUtils.ZNAME_COMPARATOR);
    List<DefinitionException> result = new ArrayList<DefinitionException>();
    // go through all sections
    for (int i = knownSections_.size()-1; i >= 0; i--)
    {
      String sectName = knownSections_.get(i);
      SortedMap<ZName, Definition> global = getDefinitions(sectName);
      // go through all definitions of given section
      for(SortedMap.Entry<ZName, Definition> globalEntry : global.entrySet())
      {
        ZName globalName = globalEntry.getKey();
        Definition globalDef = globalEntry.getValue();

        namesFound.add(globalName);

        // check it is global and names match
        try
        {
          checkGlobalDef(sectName, globalDef);
        }
        catch(DefinitionException e)
        {
          result.add(e);
        }
        if (!ZUtils.namesEqual(globalName, globalDef.getDefName()))
        {
          result.add(new DefinitionException(getDialect(), "inconsistent global name in " +
                  sectName + " = (MAP: " + DefinitionTable.printTerm(globalName) + ", DEF: " + DefinitionTable.printTerm(globalDef.getDefName()) + ")"));
        }

        // SCHEMADECL kind *MUST* be SchExpr, and SCHEMAEXPR kind *MUSTN'T* !
        DefinitionKind globalDefKind = globalDef.getDefinitionKind();
        if (globalDefKind.isSchemaReference())
        {
          if (globalDefKind.isSchemaDecl() &&
              !(globalDef.getExpr() instanceof SchExpr))
          {
            result.add(new DefinitionException(getDialect(), "inconsistent schema expr in " +
                    sectName + " = (DEF: " + DefinitionTable.printTerm(globalName) + ", EXPECT: SchExpr, FOUND: "
                    + globalDef.getExpr().getClass().getSimpleName() + ")"));
          }
          // in complex inclusions, this could be a schema reference as SchExpr, like Tokeneer TISControlledRealWorld'
//          else if (globalDefKind.isSchemaExpr() &&
//                   globalDef.getExpr() instanceof SchExpr)
//          {
//            result.add(new DefinitionException(getDialect(), "inconsistent schema calculus in " +
//                    sectName + " = (DEF: " + globalName + ", EXPECT: not SchExpr, FOUND: SchExpr" + ")"));
//          }

          // global definitions can only have schema name if they are for SCHEXPR
          if (globalDefKind.hasSchemaName())
          {
            if (!globalDefKind.isSchemaExpr())
              result.add(new DefinitionException(getDialect(), "inconsistent global definition kind = " + globalDefKind));
            else if (!namesFound.contains(globalDefKind.getSchName()))
              // check the reference exists later on, if not processed yet (e.g., forward reference?)
              namesToFind.add(globalDefKind.getSchName());
          }

          // if we have type, check the names in the type are indeed those we find bindings definition for (!!!)
          // TODO: MAYBE ASSUME THERE MUST BE TYPE INFO? THEN SIMPLIFY IT CONSIDERABLY BELOW?
          Type2 globalType = globalDef.getCarrierType();
          if (globalType != null)
          {
            if (!UnificationEnv.isSchemaPowerType(globalType))
            {
              result.add(new DefinitionException(getDialect(), "type of " + DefinitionTable.printTerm(globalName) +
                      " defined as " + globalDefKind + " is not a schema = " + globalType));
            }
            // this part is rather (computationally) expensive, yet quite good double check: typecheck x def table!
            else
            {
              // first get the type names
              boolean allNamesRemoved = true; // don't use a set for the bindings names because there may be more bindings than in the type in case of name collusion.
              SortedSet<ZName> namesInType = new TreeSet<ZName>(ZUtils.ZNAME_COMPARATOR);
              SortedMap<ZName, SortedSet<Definition>> possiblyColludedNames = new TreeMap<ZName, SortedSet<Definition>>(ZUtils.ZNAME_COMPARATOR);
              List<NameTypePair> ntpl = UnificationEnv.schemaType(UnificationEnv.powerType(globalType).getType()).getSignature().getNameTypePair();
              int varCountDifference = ntpl.size();
              for(NameTypePair ntp : ntpl)
              {
                namesInType.add(ntp.getZName());
                possiblyColludedNames.put(ntp.getZName(), new TreeSet<Definition>());
              }
              assert namesInType.size() == possiblyColludedNames.size() : "inconsistent type info: " + namesInType.toString() + " yet " + possiblyColludedNames.toString();

              // next get the bindings
              try
              {
                SortedSet<Definition> bindingsOf = bindings(globalName);
                varCountDifference = bindingsOf.size() - varCountDifference;
                for(Definition bindDef : bindingsOf)
                {
                  ZName localNameOfGlobalBindingName = bindDef.getDefName();
                  DefinitionKind globalBindingKind = bindDef.getDefinitionKind();

                  // check it is binding and names match
                  try
                  {
                    checkLocalDef(sectName, bindDef);
                  }
                  catch(DefinitionException e)
                  {
                    result.add(e);
                  }
                  if (!ZUtils.namesEqual(localNameOfGlobalBindingName, bindDef.getDefName()))
                  {
                    result.add(new DefinitionException(getDialect(), "inconsistent binding name of " +
                            DefinitionTable.printTerm(globalName) + " in " + sectName +
                            " = (MAP: " + DefinitionTable.printTerm(localNameOfGlobalBindingName) +
                            ", DEF: " + DefinitionTable.printTerm(bindDef.getDefName()) + ")"));
                  }

                  if (globalBindingKind.isSchemaBinding())
                  {
                    if (!namesFound.contains(globalBindingKind.getSchName()))
                    {
                        // check the reference exists later on, if not processed yet (e.g., forward reference?)
                        namesToFind.add(globalBindingKind.getSchName());
                    }
                  }
                  else
                  // if not a binding, error
                  {
                    result.add(new DefinitionException(getDialect(), "inconsistent def kind for binding of global name "
                            + DefinitionTable.printTerm(globalName) + " = " + globalBindingKind));
                  }

                  // remove found binding from the names collected from type: if not found could be because of hiding/renaming
                  boolean bindingFound = namesInType.remove(localNameOfGlobalBindingName);
                  if (!bindingFound)
                  {
                    // consider hide/renaming both local and global
                    if (!globalDef.getSpecialBindings().isEmpty() || bindDef.getSpecialBindings().isEmpty())
                    {
                      List<NewOldPair> sb = new ArrayList<NewOldPair>(globalDef.getSpecialBindings());
                      sb.addAll(bindDef.getSpecialBindings());
                      for (NewOldPair pair : sb)
                      {
                        if (pair.getNewName() == null)
                        {
                          // hiding case, just accept it's being found
                          bindingFound = ZUtils.namesEqual(localNameOfGlobalBindingName, pair.getOldName());
                        }
                        // renaming case
                        else
                        {
                          // old code changed after find bugs report: this seems like a copy-paste error :=(
                        	//bindingFound = ZUtils.namesEqual(localNameOfGlobalBindingName, pair.getOldName());
                            // should already be the localNameOfGlobalBindingName ?
                          bindingFound = ZUtils.namesEqual(localNameOfGlobalBindingName, pair.getNewName());
                        }
                        if (bindingFound) 
                        {
                          break;
                        }
                      }
                    }
                  }
                  else
                  {
                    // when found, add it to the bindDef
                    if (!possiblyColludedNames.containsKey(localNameOfGlobalBindingName))
                    {
                      result.add(new DefinitionException(getDialect(), "inconsistent name collusion information. could not find " + DefinitionTable.printTerm(localNameOfGlobalBindingName)));
                    }
                    else
                    {
                      possiblyColludedNames.get(localNameOfGlobalBindingName).add(bindDef);
                    }
                  }

                  // add the collusion for later
                  if (!bindingFound)
                  {
                    // TODO: what if add is false?
                    SortedSet<Definition> colludedDefs = possiblyColludedNames.get(localNameOfGlobalBindingName);
                    if (colludedDefs == null)
                    {
                      result.add(new DefinitionException(getDialect(), "could not find bindings for possibly colluded name "  
                              + DefinitionTable.printTerm(localNameOfGlobalBindingName) +
                              " of global name " + DefinitionTable.printTerm(globalName)));
                    }
                    else if (!colludedDefs.add(bindDef))
                    {
                      SectionManager.traceInfo("multiple collusion for bindings of globalName " +
                              DefinitionTable.printTerm(globalName) + " = " +
                              DefinitionTable.printTerm(localNameOfGlobalBindingName));
                    }
                  }
                  allNamesRemoved = bindingFound && allNamesRemoved;

                  // check the local name exists later on
                  if (!namesFound.contains(localNameOfGlobalBindingName))
                    namesToFind.add(localNameOfGlobalBindingName);
                }
              }
              catch (DefinitionException ex)
              {
                result.add(ex);
              }

              if (allNamesRemoved && namesInType.isEmpty())
              {
                // we are okay; no collusion
              }
              // !allNamesRemoved || !namesInType.isEmpty()
              else if (allNamesRemoved)
              {
                // did not found bindings from namesInType: serious! bindings code is missing something
                assert !namesInType.isEmpty();
                result.add(new DefinitionException(getDialect(), "bindings of " + 
                        DefinitionTable.printTerm(globalName) + " were not found = " +
                        DefinitionTable.printCollection(namesInType)));
              }
              // if not all elements in the type were found, or the variable count difference exists
              else if (namesInType.isEmpty() || varCountDifference > 0)
              {
                // found more bindings than names in type: log the fact that there are name collusions.
                assert !allNamesRemoved && !possiblyColludedNames.isEmpty();

                //if there is name collusion there might be different causes: hiding/renaming; multi-layer, etc...
                //assert possiblyColludedNames.size() >= varCountDifference;

                // remove any duplicated (or empty) mappings.
                Iterator<SortedMap.Entry<ZName, SortedSet<Definition>>> it = possiblyColludedNames.entrySet().iterator();
                while (it.hasNext())
                {
                  SortedMap.Entry<ZName, SortedSet<Definition>> next = it.next();
                  // == 1 is the usual; == 0 is for hidding; > 1 is for collusion
                  if (next.getValue().size() <= 1)
                    it.remove();
                  else
                  {
                    // check if duplicated types aren't just the same
                    boolean typeEquiv = true;
                    Iterator<Definition> dit = next.getValue().iterator();
                    assert dit.hasNext(); // can call next
                    Expr defTypeExpr = dit.next().getExpr();
                    assert dit.hasNext(); // more than once
                    while (dit.hasNext() && typeEquiv)
                    {
                      Expr defTypeExprOther = dit.next().getExpr();
                      typeEquiv = defTypeExpr.equals(defTypeExprOther);
                      if (typeEquiv) dit.remove();
                    }
                    // try again
                    if (next.getValue().size() <= 1) it.remove();
                    dit = null;
                  }
                }
                it = null;
                if (!possiblyColludedNames.isEmpty())
                {
                  if (!modifyDeclaredTypesOfColludedNames)
                    result.add(new DefinitionException(getDialect(), "name collusion for bindings of globalName " +
                            DefinitionTable.printTerm(globalName) + " = " + DefinitionTable.printMap(possiblyColludedNames)));
                  else
                  {
                    // modify colluded name types.... by intersecting or unioning? or what? TODO
                    result.add(new DefinitionException(getDialect(), "UNSUPPORTED OPERATION - MODIFICATION OF COLLUDED NAMES TYPES for bindings of globalName " +
                            DefinitionTable.printTerm(globalName) + " = " + DefinitionTable.printMap(possiblyColludedNames)));
                  }
                }
              }
            }
          }
          else
          {
            boolean addMissingInfoError = true;
            
            // check if it's for \Delta or \Xi: if so, add the error only if the base name doesn't have bindings being checked
            if (ZUtils.isDeltaXi(globalName))
            {
              ZName baseName = ZUtils.getSpecialSchemaBaseName(ZUtils.FACTORY, globalName);
              addMissingInfoError = !global.containsKey(baseName);
            }
            if (addMissingInfoError)
              result.add(new DefinitionException(getDialect(), "could not retrieve type information for " +
                         DefinitionTable.printTerm(globalName) + ". Cannot check bindings consistency"));
          }
        }

        // check all local names for each global name
        SortedMap<ZName, Definition> local = globalDef.getLocalDecls();
        for (SortedMap.Entry<ZName, Definition> localEntry : local.entrySet())
        {
          ZName localName = localEntry.getKey();
          Definition localDef = localEntry.getValue();

          namesFound.add(localName);
          namesToFind.remove(localName);

          // check if the special bindings are still to find (e.g., case of renaming)
          // NOTE: for implicitly declared schemas (E.g., State' in Delta State), there will be no type information
          for (NewOldPair pair : localDef.getSpecialBindings())
          {
            // if not hiding, then it's renaming
            if (pair.getNewName() != null)
            {
              namesToFind.remove(ZUtils.assertZName(pair.getNewName()));
            }
          }

          // check it is local and names match
          try
          {
            checkLocalDef(sectName, localDef);
          }
          catch(DefinitionException e)
          {
            result.add(e);
          }
          if (!ZUtils.namesEqual(localName, localDef.getDefName()))
          {
            result.add(new DefinitionException(getDialect(), "inconsistent local name of " +
                    globalName + " in " + sectName + " = (MAP: " + localName + ", DEF: " + localDef.getDefName() + ")"));
          }

          // TODO: anything else on local names?
        }

        // check if the special bindings are still to find (e.g., case of renaming)
        for (NewOldPair pair : globalDef.getSpecialBindings())
        {
          // if not hiding, then it's renaming
          if (pair.getNewName() != null)
          {
            namesToFind.remove(ZUtils.assertZName(pair.getNewName()));
          }
        }
      }
      SectionManager.traceLog("DEFTBL-CONSISTENCY-CHECK-FOR-" + sectName + " = " + result.size() + " errors");
    }
    namesToFind.removeAll(namesFound);
    if (!namesToFind.isEmpty())
    {
      result.add(new DefinitionException(getDialect(), "found references to names without definitions = " + namesToFind.toString()));
    }
    return result.isEmpty() ? null : new DefinitionException(getDialect(), "DefTable consistency failed (see details)", result);
  }

  /**
   * Gets all definitions of a a given section name as a unmodifiable set.
   * It is homomorphic to the values of {@link #getDefinitions(java.lang.String) }.
   * @param sectName
   * @return
   */
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
   * Looks up a (unique) name within the given sect only.
   * @param sectName section to look into.
   * @param name definition name
   * @return the Definition for the name, or null if not found.
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
   * Looks up a (unique) name within the current sect and its declared parents.
   * The name should be a global name according to {@link DefinitionKind#isGlobal() }.
   * @param name definition name
   * @return the name if found, or null otherwise
   */
  public Definition lookupDeclName(ZName name) 
  {
    Definition result = null;
    for (int i = knownSections_.size()-1; i >= 0 && result == null; i--)
    {
      String sectName = knownSections_.get(i);
      result = lookupDeclName(sectName, name);
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

  /**
   * Looks a (unique) possibly local name within this section and all its declared parents.
   * It is first checks whether {@code name} is global or not (e.g., {@link #lookupDeclName(net.sourceforge.czt.z.ast.ZName) }).
   * If not (e.g., got null as result), then it tries, within all definitions from all sections
   * to look for either global names of parents or local names anywhere.
   * @param name definition name
   * @return the definition (local or global) if found, null otherwise
   */
  public Definition lookupName(ZName name)
  {
    // look top-level
    Definition result = lookupDeclName(name);

    // if name is not top-level name, try locals
    if (result == null)
    {
      assert knownSections_.size() >= definitions_.keySet().size();
      for (int i = knownSections_.size()-1; i >= 0 && result == null; i--)
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

  private SortedSet<Definition> bindings0(ZName defName) throws DefinitionException
  {
    Definition def = lookupDeclName(defName);
    SortedSet<Definition> result = new TreeSet<Definition>();

    // if this is a schema declaration, look for its bindings
                        // TODO: should this be isSchemaReference()? MAYBE
    if (def != null && def.getDefinitionKind().isSchemaReference())
    {
      List<NewOldPair> currentSpecialBindings = def.getSpecialBindings();
      if (!currentSpecialBindings.isEmpty())
        specialBindingsStack_.push(currentSpecialBindings);
      checkGlobalDef(def.getSectionName(), def);
      for(Definition localDef : def.getLocalDecls().values())
      {
        if (localDef.getDefinitionKind().isSchemaBinding())
        {
          assert localDef.getLocalDecls().isEmpty();
          checkLocalDef(localDef.getSectionName(), localDef);
          Definition localDefToAdd = localDef;

          // if there are special bindings to consider check them
          boolean foundPair = false;
          ListIterator<List<NewOldPair>> it = specialBindingsStack_.listIterator(specialBindingsStack_.size());
          while (it.hasPrevious() && !foundPair)
          {
            List<NewOldPair> top = it.previous();
            // take care of renaming/hiding
            for(NewOldPair pair : top)
            {
              Name oldName = pair.getOldName();
              Name newName = pair.getNewName();
              if (ZUtils.namesEqual(localDefToAdd.getDefName(), oldName))
              {
                // hiding
                if (newName == null)
                  localDefToAdd = null;
                // renaming
                else
                  localDefToAdd = new Definition(localDef, ZUtils.assertZName(newName));
                foundPair = true;
                break;
              }
            }
          }
          it = null;
          // if not hiding, add the renamed one
          if (localDefToAdd != null)
          {
            assert localDefToAdd == localDef /*|| specialBindingsStack_.isEmpty()*/ ^ foundPair;
            boolean isNew = result.add(localDefToAdd);
            if (!isNew)
            {
              System.out.println("HAS COLLUSION FOR " + localDefToAdd.getDefName());
            }
          }

        }
                      // TODO: should this be isSchemaReference()?
        else if (localDef.getDefinitionKind().isSchemaReference())
        {
          SortedSet<Definition> localResult = bindings0(localDef.getDefName());
          for(Definition d : localResult)
          {
            boolean isNew = result.add(d);
            if (!isNew)
            {
              // possible name collusion?
            }
          }
        }
      }

      if (!currentSpecialBindings.isEmpty())
      {
        List<NewOldPair> old = specialBindingsStack_.pop();
        assert old == currentSpecialBindings;
      }

      // for complex schema expressions, we need to apply further modification to bindings.
      if (def.getDefinitionKind().isSchemaExpr())
      {
        if (def.getExpr() instanceof PreExpr)
        {
          result = BindingUtils.beforeBindingsOf(result);
        }
        else if (def.getExpr() instanceof PipeExpr)
          throw new DefinitionException(getDialect(), "Cannot calculate bindings for schema piping expression yet - " + DefinitionTable.printTerm(defName));
      }

      return result;
    }
    else
    {
      throw new DefinitionException(getDialect(), defName, "Unknown schema name in DefTbl " + defName);
    }
  }

  /**
   * Looks up all local bindings of the definition for the given name.
   * If this name is not a schema reference (as in {@link DefinitionKind#isSchemaReference() }),
   * then an exception is thrown, since other definition kinds do not have bindings. ?
   * TODO: MAYBE RELAX THIS A BIT AND HAVE BINDINGS FROM AXIOMS, SAY DEFINED WITH LAMBDA or MU etc?
   * @param defName definition name
   * @return set of bindings associated with this name definition, if any.
   * @throws DefinitionException
   */
  public SortedSet<Definition> bindings(ZName defName) throws DefinitionException
  {
    assert specialBindingsStack_.isEmpty();
    SortedSet<Definition> result = bindings0(defName);
    assert specialBindingsStack_.isEmpty();
    return result;
  }
  // ALTERNATIVE RECURSIVE ALGORITHM WHEN THERE WERE NO LOCAL DEFINITIONS.
        // assert all elements have isSchemaBinding() kind

//      assert knownSections_.size() >= definitions_.keySet().size();
//      for (int i = knownSections_.size()-1; i >= 0; i--)
//      {
//        SortedMap<ZName, Definition> defOfSect = definitions_.get(i);
//        if (defOfSect != null)
//        {
//          result = defOfSect.get(name);
//          // if not a top-level name, try local names
//          if (result == null)
//          {
//            result = lookupLocalNames(defOfSect.values(), name);
//          }
//        }
//      }
//
//
//      HashSet<Definition> result = new HashSet<Definition>();
//      // lookup all def, in case of included from othe sections getSectDefinitions(def.getSectionName())
//      for(SortedMap.Entry<ZName, Definition> defLookup : definitions_.values())
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
//          ZName defLookupName = defLookup.getDefName();
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

  /**
   * Specialised to string method that might print parents or not, and
   * also can provide simpler output containing less definition information
   * (see {@link Definition#toString(boolean) }).
   * @param printParents
   * @param simple
   * @return
   */
  public String toString(boolean printParents, boolean simple)
  {
    if (printParents)
      return toString();
    else
    {
      SortedMap<ZName, Definition> defs = getDefinitions(getSectionName());
      assert defs != null;
      StringBuilder buffer = new StringBuilder(defs.size() * 30);
      buffer.append("Definition table for ");
      buffer.append(getSectionName());
      buffer.append(" (with parrents hidden)");
      Iterator<SortedMap.Entry<ZName, Definition>> itE = defs.entrySet().iterator();
      buffer.append("\n\t");
      while (itE.hasNext())
      {
        SortedMap.Entry<ZName, Definition> entry2 = itE.next();
        buffer.append(printTerm(entry2.getKey()));
        buffer.append(" = ");
        buffer.append(entry2.getValue().toString(simple));
        if (itE.hasNext())
          buffer.append("\n\t");
      }
      itE = null;
      buffer.append('\n');
      return buffer.toString();
    }
  }

  /**
   * Prints the table definitions, and of its parents, in a form useful for debugging.
   * @return
   */
  @Override
  public String toString()
  {
    StringBuilder buffer = new StringBuilder(definitions_.size() * 30);
    buffer.append("Definition table for ");
    buffer.append(getSectionName());
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
             buffer.append(printTerm(entry2.getKey()));
             buffer.append("\t= ");
             buffer.append(entry2.getValue().toString());
             if (itE.hasNext())
               buffer.append("\n\t\t");
           }
           itE = null;
         }
         buffer.append("}\n\t");
      }
      it = null;
    }
    buffer.append('\n');
    return buffer.toString();
  }

  /**
   * Uses a console print visitor to print the given term
   * @param term
   * @return
   */
  public static String printTerm(Term term)
  {
    return term.accept(printVisitor_);
  }

  public static String printMap(SortedMap<ZName, SortedSet<Definition>> map)
  {
    StringBuilder result = new StringBuilder(map.size()*50);
    for(SortedMap.Entry<ZName, SortedSet<Definition>> entry : map.entrySet())
    {
      result.append("\n\t");
      result.append(printTerm(entry.getKey()));
      result.append(" |--> ");
      result.append((entry.getValue()));
    }
    return result.toString().trim();
  }

  public static String printCollection(Collection<? extends Term> collection)
  {
    StringBuilder result = new StringBuilder(collection.size()*30);
    for(Term t : collection)
    {
      result.append(printTerm(t));
      result.append("  ");
    }
    return result.toString().trim();
  }

  /** This interface allows visitors to visit definitions.
   * @param <T>
   */
  public interface DefinitionVisitor<T>
  {
    /**
     *
     * @param def
     * @return
     */
    T visitDefinition(Definition def);
  }
}
