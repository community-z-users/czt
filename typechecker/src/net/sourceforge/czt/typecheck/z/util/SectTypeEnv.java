/*
  Copyright (C) 2004 Tim Miller
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
package net.sourceforge.czt.typecheck.z.util;

import java.io.*;
import java.util.List;
import java.util.ArrayList;
import java.util.Set;
import java.util.HashSet;
import java.util.Map;
import java.util.HashMap;
import java.util.Iterator;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.util.ZString;
import net.sourceforge.czt.z.impl.ZFactoryImpl;
import net.sourceforge.czt.typecheck.z.*;
import net.sourceforge.czt.typecheck.z.impl.*;

/**
 * A <code>SectTypeEnv</code> maintains a mapping between a global
 * declaration, its section name, and its type.
 */
public class SectTypeEnv
{
  /** The name of the prelude section. */
  public static final String PRELUDE = "prelude";

  /** The names of the toolkit sections. */
  public static final String [] TOOLKITS = {PRELUDE,
                                            "set_toolkit",
                                            "relation_toolkit",
                                            "function_toolkit",
                                            "sequence_toolkit",
                                            "number_toolkit",
                                            "standard_toolkit"};
  /** A Factory. */
  protected static Factory factory_;

  /** The list of all NameSectTypeTriples add so far. */
  protected List<NameSectTypeTriple> typeInfo_;

  /** The list of variables declared so far. */
  protected List<DeclName> declarations_;

  /** The list of sections declared so far. */
  protected List<String> sectionDeclarations_;

  /** The current section. */
  protected String section_ = null;

  /** True if the typechecker is traversing for a 2nd time. */
  protected boolean secondTime_ = false;

  /** The currently visible sections. */
  protected Set<String> visibleSections_;

  /** The list of all typechecked parents. */
  protected Set<String> checkedSections_;

  /** The function of all sections to their immediate parents. */
  protected Map<String, Set<String>> parents_;

  public SectTypeEnv()
  {
    this(new ZFactoryImpl());
  }

  public SectTypeEnv(ZFactory zFactory)
  {
    factory_ = new Factory(zFactory);
    typeInfo_ = new ArrayList<NameSectTypeTriple>();
    declarations_ = new ArrayList<DeclName>();
    sectionDeclarations_ = new ArrayList<String>();
    visibleSections_ = new HashSet<String>();
    checkedSections_ = new HashSet<String>();
    parents_ = new HashMap<String, Set<String>>();
  }

  public void overwriteTriples(List<NameSectTypeTriple> triples)
  {
    typeInfo_ = new ArrayList<NameSectTypeTriple>();
    add(triples);
  }

  /**
   * Set the current section.
   * @param section the section
   */
  public void setSection(String section)
  {
    if (!visibleSections_.contains(section)) visibleSections_.add(section);
    if (!checkedSections_.contains(section)) checkedSections_.add(section);
    section_ = section;
  }

  public void setSecondTime(boolean secondTime)
  {
    secondTime_ = secondTime;
  }

  public boolean getSecondTime()
  {
    return secondTime_;
  }

  public Factory getFactory()
  {
    return factory_;
  }

  /**
   * @return true if and only if this section has been checked.
   */
  public boolean isChecked(String section)
  {
    boolean result = checkedSections_.contains(section);

    if (secondTime_) {
      result = sectionDeclarations_.contains(section);
      sectionDeclarations_.add(section);
    }
    return result;
  }

  /**
   * @return the current section
   */
  public String getSection()
  {
    return section_;
  }

  /**
   * @return the visible sections
   */
  public Set<String> getVisibleSections()
  {
    return visibleSections_;
  }

  /**
   * End the current section.
   */
  public void endSection()
  {
    visibleSections_.clear();
    section_ = null;
  }

  /**
   * Add a parent to the current section.
   * @param parent the parent to be added
   */
  public void addParent(String parent)
  {
    //add the parent as a visible section
    visibleSections_.add(parent);

    //get the current section's list of parents
    Set<String> parents = parents_.get(section_);

    //add the parents to the list of the current section's parents
    if (parents == null) {
      parents = new HashSet<String>();
    }
    parents.add(parent);
    parents_.put(section_, parents);

    //add the transitive parents
    visibleSections_.addAll(getTransitiveParents(parent));
  }

  /**
   * Add a <code>NameSectTypeTriple</code> to this environment.
   * @return true if and only if this name is not a duplicate
   */
  public boolean add(NameSectTypeTriple triple)
  {
    boolean result = true;

    //if not already declared, add this declaration to the environment
    NameSectTypeTriple existing = getTriple(triple.getName());
    if (existing == null) {
      typeInfo_.add(triple);
      result = true;
    }
    else {
      existing.setType(triple.getType());
    }

    if (secondTime_) {
      result = !declarations_.contains(triple.getName());
      declarations_.add(triple.getName());
    }

    return result;
  }

  public void add(List<NameSectTypeTriple> triples)
  {
    for (NameSectTypeTriple triple : triples) {
      add(triple);
    }
  }

  /**
   * Add a <code>NameTypePair</code> to this environment.
   * @return true if and only if this name is not a duplicate
   */
  public boolean add(NameTypePair nameTypePair)
 {
    return add(nameTypePair.getName(), nameTypePair.getType());
  }

  public boolean add(DeclName declName, Type type)
  {
    boolean result = true;
    for (NameSectTypeTriple triple : typeInfo_) {
      if (triple.getName().equals(declName)) {
        triple.setType(type);
        result = false;
      }
    }

    if (result) {
      NameSectTypeTriple insert =
        factory_.createNameSectTypeTriple(declName, section_, type);
      typeInfo_.add(insert);
    }

    if (secondTime_) {
      result = !declarations_.contains(declName);
      declarations_.add(declName);
    }

    return result;
  }

  public boolean update(RefName refName, Type type)
  {
    NameSectTypeTriple triple = getTriple(refName);
    if (triple != null) {
      triple.setType(type);
    }
    else {
      DeclName declName = factory_.createDeclName(refName.getWord(),
                                                  refName.getStroke(),
                                                  null);
      NameSectTypeTriple insert =
        factory_.createNameSectTypeTriple(declName, section_, type);
      typeInfo_.add(insert);
    }

    return true;
  }

  public List<NameSectTypeTriple> getTriple()
  {
    List<NameSectTypeTriple> triples = new ArrayList<NameSectTypeTriple>();
    for (NameSectTypeTriple triple : typeInfo_) {
      if (visibleSections_.contains(section_) ||
          triple.getSect().equals(PRELUDE)) {
        triples.add(triple);
      }
    }
    return triples;
  }

  public SectTypeEnvAnn getSectTypeEnvAnn()
  {
    List<NameSectTypeTriple> triples = getTriple();
    return factory_.createSectTypeEnvAnn(triples);
  }

  /**
   * Return the type of the variable.
   */
  public Type getType(RefName name)
  {
    DeclName declName = factory_.createDeclName(name);
    Type result = factory_.createUnknownType();

    //get the info for this name
    NameSectTypeTriple triple = getTriple(name);
    if (triple != null && visibleSections_.contains(triple.getSect())) {
      result = triple.getType();
      name.setDecl(triple.getName());
    }

    //if the type is unknown and the name starts with delta or xi, try
    //looking up the base name
    if (result instanceof UnknownType &&
        (name.getWord().startsWith(ZString.DELTA) ||
         name.getWord().startsWith(ZString.XI))) {
      final int size = (ZString.DELTA).length();
      String baseWord = name.getWord().substring(size);
      RefName baseName =
        factory_.createRefName(baseWord, name.getStroke(), null);
      Type baseType = getType(baseName);

      //if this is a schema, determine and add the delta/xi type
      if (isSchema(baseType)) {
        PowerType powerType = (PowerType) unwrapType(baseType);
        SchemaType schemaType = (SchemaType) powerType.getType();
        Signature signature = schemaType.getSignature();

        List<NameTypePair> pairs = signature.getNameTypePair();
        List<NameTypePair> newPairs = new ArrayList<NameTypePair>(pairs);
        for (NameTypePair pair : pairs) {
          DeclName primedName = factory_.createDeclName(pair.getName());
          primedName.getStroke().add(factory_.createNextStroke());
          NameTypePair newPair =
            factory_.createNameTypePair(primedName, pair.getType());
          newPairs.add(newPair);
        }
        //create the new type
        Signature newSignature = factory_.createSignature(newPairs);
        SchemaType newSchemaType = factory_.createSchemaType(newSignature);
        PowerType newPowerType = factory_.createPowerType(newSchemaType);

        if (baseType instanceof GenericType) {
          GenericType gType = (GenericType) baseType;
          result =
            factory_.createGenericType(gType.getName(), newPowerType, null);
        }
        else {
          result = newPowerType;
        }

        //add this to the environment so it need not be determined again
        add(declName, result);
      }
    }

    return result;
  }

  //not a generic type, return the type
  protected static Type2 unwrapType(Type type)
  {
    Type2 result = null;
    if (type instanceof GenericType) {
      GenericType genericType = (GenericType) type;
      result = genericType.getType();
    }
    else {
      result = (Type2) type;
    }
    return result;
  }

  protected boolean isSchema(Type type)
  {
    boolean result = false;
    Type2 type2 = unwrapType(type);
    if (type2 instanceof PowerType) {
      PowerType powerType = (PowerType) type2;
      if (powerType.getType() instanceof SchemaType) {
        result = true;
      }
    }
    return result;
  }

  /**
   * For debugging purposes.
   */
  public void dump()
  {
    System.err.println("typeinfo:");
    for (NameSectTypeTriple next : typeInfo_) {
      System.err.print("\t(" + next.getName());
      System.err.print(", (" + next.getSect());
      System.err.println(", (" + next.getType() + ")))");
    }
  }

  //get a triple whose name matches a specified name and it
  //defined in a currently visible scope.
  private NameSectTypeTriple getTriple(Name name)
  {
    NameSectTypeTriple result = null;
    for (NameSectTypeTriple next : typeInfo_) {
      //we don't use equals() in DeclName so that we can use this
      //lookup for RefName objects as well
      if (next.getName().getWord().equals(name.getWord()) &&
          next.getName().getStroke().equals(name.getStroke()) &&
          (visibleSections_.contains(section_) ||
           next.getSect().equals(PRELUDE))) {
        result = next;
        break;
      }
    }
    return result;
  }

  //get the transitive parents of a section
  private Set<String> getTransitiveParents(String section)
  {
    Set<String> result = new HashSet<String>();

    //get the set of direct parents
    Set<String> parents = parents_.get(section);

    if (parents != null) {
      result.addAll(parents);
      //for each direct parent, get the transitive parents
      for (String parent : parents) {
	if (!parent.equals(section)) {
	  Set<String> transitiveParents = getTransitiveParents(parent);
	  result.addAll(transitiveParents);
	}
      }
    }
    return result;
  }
}
