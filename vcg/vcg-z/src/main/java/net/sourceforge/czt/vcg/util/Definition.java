/*
 * Copyright (C) 2011 Leo Freitas
 * This file is part of the CZT project.
 *
 * The CZT project contains free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * The CZT project is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with CZT; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 */
package net.sourceforge.czt.vcg.util;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Iterator;
import java.util.List;
import java.util.SortedMap;
import java.util.TreeMap;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.util.PerformanceSettings;
import net.sourceforge.czt.parser.util.InfoTable;
import net.sourceforge.czt.session.Dialect;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.util.CztLogger;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.Name;
import net.sourceforge.czt.z.ast.NewOldPair;
import net.sourceforge.czt.z.ast.Type2;
import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.z.ast.ZNameList;
import net.sourceforge.czt.z.util.ZString;
import net.sourceforge.czt.z.util.ZUtils;

/**
 * This defines a definition, including its name.
 * That is, for the generic definition g[T,U] = T \fun U,
 * this Definition records the type parameters T,U,
 * the right hand side expression, the name, and the kind
 * of definition it is given the context where it appeared.
 * If types are available, a carrier set is also attached; it's null otherwise.
 *
 * @authot Leo Freitas
 */
public class Definition extends InfoTable.Info implements Comparable<Definition>
{

  private final ZName defName_;
  private DefinitionKind defKind_;
  private final ZNameList genericParams_;
  private final Expr definition_;
  private final Type2 carrierType_;
  /**
   * Local bindings to hide/rename, where new=null for hide. It is a list because of
   * possible chained rename/hide, in which case latter ones override former.
   * ex.  Op[x/y] hide (x)
   */
  private final List<NewOldPair> specialBindings_; // local bindings for Hide/Rename; new for Hide is null.
  private final SortedMap<ZName, Definition> locals_;

  /**
   * A definition that has local names, e.g., schema bindings, might have name 
   * collusion (e.g., S == [x:\seq \nat]; T == [x: \nat\fun\nat]; State == [S; T]).
   * 
   * That means, the bindings of State will have collusion on "x". That is in spite
   * of unifiable types (e.g., maximally correct types), and is allowed. We tag State
   * as such to inform the user of that.
   */
  private boolean hasLocalNamesCollusion_;
  // invariant: hasLocalNamesCollusion_ => definitionKind.isSchemaBinding()
  //    only schema bindings can have name collusion flag on

  /**
   * On local bindings of State, say "x" above, there will be a synthetic type for
   * it, namely the intersection of all declared types involved (e.g., x : \seq \nat \cap \nat\fun\nat).
   * If that's the case, we tag it with a boolean flag here. That's to differentiate to the rather
   * unusual user-declared type, if it ever happens. Notice that there is a clear link between
   * the local bindings of State which might collude and will have synthetic types tag and this flag.
   */
  private final boolean hasSyntheticTypeDueToCollusion_;
  // invariant: hasSyntheticTypeDueToCollusion_ => DefinitionTable.checkLocalDef(this) && \exists def @ def.locals_.containsKey(this.defName_) && def.definitionKind.isSchemaBinding()
  //    if this definition has synthetic types from name collusion, then it must be a local definition of some schema binding

  /**
   * Usual constructor given parameters for global definitions.
   * @param sectName
   * @param defName
   * @param generic
   * @param definition
   * @param carrierType
   * @param definitionKind
   */
  protected Definition(String sectName, ZName defName, 
          ZNameList generic, Expr definition, Type2 carrierType,
          DefinitionKind definitionKind)
  {
    this(sectName, defName, generic, definition, carrierType, definitionKind, false);
  }

  /**
   * Usual constructor given parameter for local definitions
   * @param sectName
   * @param defName
   * @param generic
   * @param definition
   * @param carrierType
   * @param definitionKind
   * @param hasSynthTypes
   */
  private Definition(String sectName, ZName defName,
          ZNameList generic, Expr definition, Type2 carrierType,
          DefinitionKind definitionKind, boolean hasSynthTypes)
  {
    super(sectName);
    assert generic != null && defName != null && definition != null && definitionKind != null;
    genericParams_ = generic;
    defName_ = defName;
    definition_ = definition;
    defKind_ = definitionKind;
    carrierType_ = carrierType; // type maybe null
    specialBindings_ = new ArrayList<NewOldPair>(PerformanceSettings.INITIAL_ARRAY_CAPACITY);
    hasSyntheticTypeDueToCollusion_ = hasSynthTypes;
    hasLocalNamesCollusion_ = false;
    locals_ = new TreeMap<ZName, Definition>(ZUtils.ZNAME_COMPARATOR);
  }

  /**
   * Deep copies the given definition with the generics in context. This is used
   * for local references like included schemas or implicit ones (E.g., Delta S = S and S')
   * @param contextGenerics
   * @param deepCopy
   * @throws DefinitionException
   */
  protected Definition(ZNameList contextGenerics, Definition deepCopy) throws DefinitionException
  {
    //super(deepCopy == null ? null : deepCopy.getSectionName());
	super("");
    if (deepCopy == null) {
    	throw new NullPointerException("Cannot deep copy null definition");
    }
    setSectionName(deepCopy.getSectionName());
    DefinitionTable.checkLocalDef(deepCopy.getSectionName(), deepCopy);

    assert contextGenerics != null;
    genericParams_ = cloneTerm(deepCopy.genericParams_);
    defName_ = cloneTerm(deepCopy.defName_);
    defKind_ = deepCopy.defKind_; //new DefinitionKind(local.defKind_);
    carrierType_ = deepCopy.carrierType_ == null ? null : cloneTerm(deepCopy.carrierType_);
    hasSyntheticTypeDueToCollusion_ = deepCopy.hasSyntheticTypeDueToCollusion_;
    hasLocalNamesCollusion_ = deepCopy.hasLocalNamesCollusion_;
    Expr copiedExpr = cloneTerm(deepCopy.definition_);
    assert genericParams_.equals(deepCopy.genericParams_) &&
           defName_.equals(deepCopy.defName_) &&
           defKind_.equals(deepCopy.defKind_) &&
           copiedExpr.equals(deepCopy.definition_) &&
           ((carrierType_ == null && deepCopy.carrierType_ == null) ||
            (carrierType_ != null && carrierType_.equals(deepCopy.carrierType_)));
    definition_ = tryResolvingGenerics(contextGenerics, carrierType_, copiedExpr);

    // try to avoid cloning local definitions --- have a list of hidden / renamed terms instead
//    locals_ = new TreeMap<ZName, Definition>(ZUtils.ZNAME_COMPARATOR);
//    for(SortedMap.Entry<ZName, Definition> localEntry : local.locals_.entrySet())
//    {
//      ZName localName = cloneTerm(localEntry.getKey());
//      Definition localDef = new Definition(contextGenerics, localEntry.getValue());
//      assert localName.equals(localEntry.getKey()) &&
//             localDef.equals(localEntry.getValue());
//      locals_.put(localName, localDef);
//    }
    locals_ = new TreeMap<ZName, Definition>(deepCopy.locals_);
    assert locals_.size() == deepCopy.locals_.size();

    // copy the local bindings: TODO? Clone or not?
    specialBindings_ = new ArrayList<NewOldPair>(deepCopy.specialBindings_);
  }

  /**
   * Copies all from the given definition, yet changes definition name's accordingly.
   * @param copy
   * @param newLocalName
   * @throws DefinitionException
   */
  protected Definition(Definition copy, ZName newLocalName) throws DefinitionException
  {
    super(copy.getSectionName());
    DefinitionTable.checkLocalDef(copy.getSectionName(), copy);
    defName_ = newLocalName;
    genericParams_ = copy.genericParams_;
    definition_ = copy.definition_;
    defKind_ = copy.defKind_;
    carrierType_ = copy.carrierType_;
    hasLocalNamesCollusion_ = copy.hasLocalNamesCollusion_;
    hasSyntheticTypeDueToCollusion_ = copy.hasSyntheticTypeDueToCollusion_;
    locals_ = new TreeMap<ZName, Definition>(copy.locals_);
    specialBindings_ = new ArrayList<NewOldPair>(copy.specialBindings_);
  }


  /**
   * Test whether a list contains a reference to an object.
   * @param list the list to search.
   * @param o the reference to search for.
   * @return true if and only if the reference is in the list.
   */
  private static boolean containsObject(List<?> list, Object o)
  {
    boolean result = false;
    Iterator<?> iter = list.iterator();
    while (iter.hasNext())
    {
      Object next = iter.next();
      if (next == o)
      {
        result = true;
        break;
      }
    }
    iter = null;
    return result;
  }

  protected static <T extends Term> T cloneTerm(T term)
  {
    assert term != null;
    List<Term> listTerm = new ArrayList<Term>();
    listTerm.add(term);
    return cloneTerm(term, listTerm);
  }

  private static <T extends Term> T cloneTerm(T term, List<Term> listTerm)
  {
    Object[] children = term.getChildren();
    for (int i = 0; i < children.length; i++) {
      Object child = children[i];
      if (child instanceof Term &&
          ! containsObject(listTerm, child)) {
        children[i] = cloneTerm((Term) child, listTerm);
      }
    }
    @SuppressWarnings("unchecked")
    T result = (T)term.create(children);
    assert result.equals(term);
    cloneAnns(term, result);
    return result;
  }

  //copy the LocAnn and UndeclaredAnn from term1 to term2
  private static void cloneAnns(Term term1, Term term2)
  {
    if (term1.hasAnn())
    {
      for(Object obj : term1.getAnns())
      {
        if (obj instanceof Term)
        {
          Term ann = (Term)obj;
          Term cann = cloneTerm(ann);
          term2.getAnns().add(cann);
        }
        else
        {
          term2.getAnns().add(obj);
        }
      }
    }
  }
  
  protected Dialect getDialect()
  {
	  return Dialect.Z;
  }

  private Expr tryResolvingGenerics(ZNameList genFormals, Type2 carrierType, Expr expr)
  {
    Expr resolvedExpr = expr;
    if (carrierType != null)
    {
      // returns defExpr if it can't handle instantiation
      resolvedExpr = expr;
    }
    return resolvedExpr;
  }


  public SortedMap<ZName, Definition> getLocalDecls()
  {
    return Collections.unmodifiableSortedMap(locals_);
  }

  protected Definition addLocalDecl(ZName defName,
          ZNameList generic, Expr definition, Type2 carrierSet,
          DefinitionKind definitionKind) throws DefinitionException
  {
    boolean foundCollusion = false;
    // if new local def is a schema binding
    if (definitionKind.isSchemaBinding())
    {
      // and there is a previous (repeated def) schema binding for it
      // ex: S == [ f: \nat ; f : \num ]
      Definition previous = locals_.get(defName);
      if (previous != null)
      {
        if (previous.getDefinitionKind().isSchemaBinding())
        {
          // create a combination of their types as the actual definition
          definition = ZUtils.FACTORY.createFunOpAppl(
            ZUtils.FACTORY.createZName(
              ZString.ARG_TOK + ZString.CAP + ZString.ARG_TOK),
            ZUtils.FACTORY.createTupleExpr(previous.getExpr(), definition));
          final String message = "Duplicated local def \"" + DefinitionTable.printTerm(defName) +
            "\" of \"" + DefinitionTable.printTerm(defName_) + "\" in section " + getSectionName() +
            ". This only happens on explicit duplication (e.g., within same paragraph); "
            + " adding intersection of declarations as " + DefinitionTable.printTerm(definition);
          //throw new DefinitionException(getDialect(), getDialect(), oldLocalDef.getDefName(), message);
          CztLogger.getLogger(getClass()).warning(message);

          foundCollusion = true;
          // tag this schema reference with a name collusion.
          hasLocalNamesCollusion_ = true;
        }
        else
        {
          final String message = "Duplicated local def \"" + DefinitionTable.printTerm(defName) +
            "\" of \"" + DefinitionTable.printTerm(defName_) + "\" in section " + getSectionName() +
            ". Previous declaration is not a schema binding but a " + previous.getDefinitionKind().toString() +
            ", whereas current definition is a " + definitionKind + ". This is likely to be type incorrect.";
          throw new DefinitionException(getDialect(), previous.getDefName(), message);
        }
      }
      // NOTE: this case doesn't usually happen by the user;
      //       duplication through name collusion is more common
      //       (e.g., S == [ x: \num ]; T == [ x: \nat ]; R == S \land T
      //       but in this case, there is no need for intersecting here?
      //       Actually there will be no collusion, given the locals are
      //       not transitively investigated. Maybe should ? TODO see...
    }
    Definition localDef = new Definition(getSectionName(), defName,
            generic, definition, carrierSet, definitionKind, foundCollusion);
    addLocalDecl(localDef);
    return localDef;
  }

  /**
   * Called when schema inclusions are given as a local reference.
   * @param def
   * @throws DefinitionException
   */
  protected void addLocalDecl(Definition def) throws DefinitionException
  {
    ZName defName = def.getDefName();
    Definition oldLocalDef = locals_.put(defName, def);
    if (oldLocalDef != null)
    {
      // if there is a duplicated local that are not both schema bindings, raise an error
      if (!(def.getDefinitionKind().isSchemaBinding() &&
          oldLocalDef.getDefinitionKind().isSchemaBinding()))
      {
          final String message = "Duplicated local def \"" + DefinitionTable.printTerm(defName) +
            "\" of \"" + DefinitionTable.printTerm(defName_) + "\" in section " + getSectionName() +
            ". Previous declaration is not a schema binding but a " + oldLocalDef.getDefinitionKind().toString() +
            ", whereas current definition is a " + def.getDefinitionKind().toString() +
            ". This is likely to be type incorrect.";
          throw new DefinitionException(getDialect(), oldLocalDef.getDefName(), message);
      }
    }
  }

  protected void updateDefKind(DefinitionKind defKind) throws DefinitionException
  {
    if (defKind_.isSchemaReference() && defKind.isSchemaReference())
    {
      defKind_ = defKind;
    }
    else
      throw new DefinitionException(getDialect(), "Cannot update schema reference " + 
              DefinitionTable.printTerm(getDefName()) +
              " from " + defKind_ + " to " + defKind);
  }

  protected void updateSpecialBindings(List<NewOldPair> bindings) throws DefinitionException
  {
    if (bindings == null || bindings.isEmpty())
    {
      throw new DefinitionException(getDialect(), "Empty local bindings to modify for " + DefinitionTable.printTerm(getDefName()));
    }
    specialBindings_.addAll(bindings);
  }


  /**
   * Checks a given name is consistent with the definition found.
   * @param exceptions
   * @param oldName
   * @param def
   */
  private void checkLocalModification(List<DefinitionException> exceptions, ZName oldName, Definition def)
  {
    if (def == null || !ZUtils.namesEqual(oldName, def.getDefName()))
    {
      exceptions.add(new DefinitionException(getDialect(), "Could not modify local definition named \"" +
              DefinitionTable.printTerm(oldName) + "\" of " +
              DefinitionTable.printTerm(getDefName()) +
              (def != null ? ": names differ - "
                + DefinitionTable.printTerm(getDefName()) : "")));
    }
  }

  /**
   * Modifies the local bindings within this definition, recursively, for all its inner locals,
   * collecting exceptions along the way, if they occur. This is to be used by the DefinitionTable only.
   * @param localBindings
   * @param exceptions
   * @param newName
   * @param oldName
   * @return
   */
  private int modifyExtraBindings(SortedMap<ZName, Definition> localBindings,
          List<DefinitionException> exceptions, Name newName, ZName oldName) throws DefinitionException
  {
    int found = localBindings.containsKey(oldName) ? 1 : 0;
    // if we found the bindings to modify belong to given locals, do it
    if (found == 1)
    {
      // check the modified name exists and is consistent (e.g., equal to defined name)
      Definition localDefToRename = localBindings.remove(oldName);
      checkLocalModification(exceptions, oldName, localDefToRename);


      // something todo only if names differ (e.g., in case of hiding newName is null, so nothing to do)
      if (newName != null && !ZUtils.namesEqual(newName, oldName))
      {
        // copy the local with a new name and update this.locals_
        localDefToRename = new Definition(localDefToRename, ZUtils.assertZName(newName));
        Definition oldDef = localBindings.put(ZUtils.assertZName(newName), localDefToRename);
        if (oldDef != null)
        {
          exceptions.add(new DefinitionException(getDialect(), "Name capture during renaming: new name \"" +
                DefinitionTable.printTerm(newName) + "\" of " +
                DefinitionTable.printTerm(getDefName()) + " is already defined."));
        }
      }
    }
    // otherwise look deeper into each local definition, until found. TODO: or should it go everywhere changing all?
    else
    {
//      Iterator<Definition> it = localBindings.values().iterator();
//      while (!found && it.hasNext())
//      {
//        Definition def = it.next();
//        found = modifyExtraBindings(def.locals_, exceptions, newName, oldName);
//      }
      for(Definition def : localBindings.values())
      {
        found += modifyExtraBindings(def.locals_, exceptions, newName, oldName);
      }
    }
    return found;
  }

  protected void modifyExtraBindings(List<NewOldPair> bindings) throws DefinitionException
  {
    assert bindings != null;
    List<DefinitionException> exceptions = new ArrayList<DefinitionException>();
    if (bindings.isEmpty())
    {
      exceptions.add(new DefinitionException(getDialect(), "Empty local bindings to modify " + DefinitionTable.printTerm(getDefName())));
    }
    ZName defName = getDefName();
    for(NewOldPair pair : bindings)
    {
      assert pair.getOldName() != null : "inconsistent local bindings modification: old name is null";
      ZName oldName = pair.getZRefName(); // getZRefName may throw exception if getOldName = null

      // if definition already contains the oldName, then process it
      int found = modifyExtraBindings(locals_, exceptions, pair.getNewName(), oldName);
      // if we couldn't find, raise an error
      if (found <= 0)
      {
        exceptions.add(new DefinitionException(getDialect(), "Could not find local binding for \"" +
                DefinitionTable.printTerm(oldName) + "\" of " +
                DefinitionTable.printTerm(defName)));
      }
      // if we found more than once, raise a warning. TODO: use WarningManager, please
      else if (found > 1)
      {
        SectionManager.traceWarning("Local binding for \"" +
                DefinitionTable.printTerm(oldName) + "\" of " +
                DefinitionTable.printTerm(defName) + " found " +
                found + " times");
      }
    }
    if (!exceptions.isEmpty())
    {
      throw new DefinitionException(getDialect(), "Inconsistent local bindings modification", exceptions);
    }
  }

  /** Returns the list of generic type parameters of this definition.
   *  It never returns null, so if the definition has no generic
   *  parameters, it returns an empty list.
   * @return List of the names of any type parameters.
   */
  public ZNameList getGenericParams()
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
   * Hide   = null/old
   * Rename = new /old
   * @return
   */
  public List<NewOldPair> getSpecialBindings()
  {
    return Collections.unmodifiableList(specialBindings_);
  }

  /**
   * Carrier set, if available; null otherwise.
   * @return
   */
  public Type2 getCarrierType()
  {
    return carrierType_;
  }

  public ZName getDefName()
  {
    return defName_;
  }

  private static int localsDepth_ = 0;

  private static String asMany(char ch, int count)
  {
    StringBuilder builder = new StringBuilder(count);
    while (count > 0)
    {
      builder.append(ch);
      count--;
    }
    return builder.toString();
  }

  protected String printSpecialBindings(boolean simple)
  {
    StringBuilder buffer = new StringBuilder(specialBindings_.size()+1 * 20);
    buffer.append(asMany('\t', localsDepth_+1));
    buffer.append("Extra bindings = { ");
    if (!specialBindings_.isEmpty())
    {
      Iterator<NewOldPair> itB = specialBindings_.iterator();
      buffer.append(" ");
      while (itB.hasNext())
      {
        NewOldPair pair = itB.next();
        buffer.append('\n');
        buffer.append(asMany('\t', localsDepth_+2));
        String oldName = DefinitionTable.printTerm(pair.getOldName());
        Name newName = pair.getNewName();
        if (newName == null)
        {
          buffer.append("HIDE ");
          buffer.append(oldName);
        }
        else
        {
          buffer.append(DefinitionTable.printTerm(newName));
          buffer.append('/');
          buffer.append(oldName);
        }
      }
      itB = null;
    }
    buffer.append(" }");
    return buffer.toString();
  }

  protected String printLocals(boolean simple)
  {
    StringBuilder buffer = new StringBuilder(locals_.size()+1 * 20);
    //buffer.append('\n');
    buffer.append(asMany('\t', localsDepth_+1));
    buffer.append("Locals = {");
    if (!locals_.isEmpty())
    {
      Iterator<SortedMap.Entry<ZName, Definition>> itE = locals_.entrySet().iterator();
      buffer.append(" ");
      while (itE.hasNext())
      {
        SortedMap.Entry<ZName, Definition> entry2 = itE.next();
        buffer.append('\n');
        buffer.append(asMany('\t', localsDepth_+2));
        //buffer.append(DefinitionTable.printTerm(entry2.getKey()));
        //buffer.append("=");
        buffer.append(entry2.getValue().toString(simple));
      }
      itE = null;
      //buffer.append('\n');
      //buffer.append(asMany('\t', localsDepth_+1));
    }
    buffer.append(" }");
    return buffer.toString();
  }

  // Add \n\t here since it is likely to appear from within a DefTable.
  @Override
  public String toString()
  {
    return "\n\t DEFNAME = " + DefinitionTable.printTerm(defName_) +
           "\n\t DEFEXPR = " + DefinitionTable.printTerm(definition_) +
           "\n\t " + (genericParams_.isEmpty() ? "" :
                 "GENERICS= " + DefinitionTable.printTerm(genericParams_) +
           "\n\t ") + "KIND    = " + defKind_.toString() +
                      (carrierType_ == null ? "" :
           "\n\t CARSET  = " + DefinitionTable.printTerm(carrierType_).replaceAll("\n;","; ").replaceAll("\n]", "] ")) +
                      (locals_.isEmpty() ? "" :
           "\n\t LOCALS  = \n\t\t   " + printLocals(false).replaceAll("\n\t", "\n\t\t").replaceAll("}", "}\n\t")) +
                      (specialBindings_.isEmpty() ? "" :
           "\n\t SPECIAL-BINDINGS = \n\t\t   " + printSpecialBindings(false).replaceAll("\n\t", "\n\t\t").replaceAll("}", "}\n\t"));
  }
  
  private static synchronized final void incrementLocalsDepth()
  {
	  localsDepth_++;
  }

  private static synchronized final void decrementLocalsDepth()
  {
	  localsDepth_--;
  }

  public String toString(boolean simple)
  {
    if (simple)
    {
      incrementLocalsDepth();
      String result = (genericParams_.isEmpty() ? "" : " [" + DefinitionTable.printTerm(genericParams_) + "]") + defKind_.toString() +
             //"(" + DefinitionTable.printTerm(defName_) + ", " +
                    //+ ")"
                   (!locals_.isEmpty() ? printLocals(simple) : "") +
                   (!specialBindings_.isEmpty() ? printSpecialBindings(simple) : "");
      decrementLocalsDepth();
      return result;
    }
    else
      return toString();
  }

  /**
   * TODO: equals does use the equals for all fields, including defName_, yet ZNameComparator
   * where some Definition within Set<Definition> leave only consider word/strokes and no id! Normalise?
   * @param o
   * @return
   */
  @Override
  public boolean equals(Object o)
  {
    boolean result = o == this;
    if (!result && o instanceof Definition)
    {
      Definition d = (Definition) o;
      result = this.getSectionName().equals(d.getSectionName()) &&
              this.defName_.equals(d.defName_) && // this does consider getId()!
              this.defKind_.equals(d.defKind_) &&
              this.genericParams_.equals(d.genericParams_) &&
              this.locals_.equals(d.locals_) &&
              this.specialBindings_.equals(d.specialBindings_);
    }
    return result;
  }

  @Override
  public int hashCode()
  {
    int hash = 31;
    hash = 29 * hash + this.getSectionName().hashCode();
    hash = 29 * hash + this.defName_.hashCode();
    hash = 29 * hash + this.defKind_.hashCode();
    hash = 29 * hash + this.genericParams_.hashCode();
    hash = 29 * hash + this.locals_.hashCode();
    hash = 29 * hash + this.specialBindings_.hashCode();
    return hash;
  }

  @Override
  public int compareTo(Definition o)
  {
    // first compare by DefKind order
    int result = this.defKind_.value() - o.defKind_.value();
    if (result == 0)
    {
      // next by name order
      result = ZUtils.compareTo(this.getDefName(), o.getDefName());

      // if the same binding, check if they come from the same schema name (e.g., handle name collusion)
      if (result == 0 && this.defKind_.hasSchemaName())
      {
        result = ZUtils.compareTo(this.defKind_.getSchName(), o.defKind_.getSchName());
      }
    }
    return result;
  }

  public enum BindingType { HIDING, RENAMING, EXISTS, FORALL }

  protected class SpecialBinding
  {
  }

  protected class HideBinding extends SpecialBinding
  {

  }

  protected class RenameBinding extends SpecialBinding
  {

  }

  protected class ExistsBinding extends HideBinding
  {
    
  }

  protected class ForallBinding extends HideBinding
  {

  }

}
