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
package net.sourceforge.czt.typecheck.util.typingenv;

import java.io.*;
import java.util.List;
import java.util.ArrayList;
import java.util.Set;
import java.util.HashSet;
import java.util.Map;
import java.util.HashMap;
import java.util.Iterator;

import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.util.ZString;
import net.sourceforge.czt.z.impl.ZFactoryImpl;
import net.sourceforge.czt.typecheck.z.*;
import net.sourceforge.czt.typecheck.util.*;
import net.sourceforge.czt.typecheck.z.impl.*;

/**
 * A <code>SectTypeEnv</code> maintains a mapping between a global
 * declaration, its section name, and its type.
 */
public class SectTypeEnv
{
  /** The name of the prelude section. */
  public static final String PRELUDE = "prelude";

  /** A Factory. */
  protected static Factory factory_;

  /** The list of all NameSectTypeTriples add so far. */
  protected List<NameSectTypeTriple> typeInfo_;

  /** The current section. */
  protected String section_ = null;

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
    visibleSections_ = new HashSet<String>();
    checkedSections_ = new HashSet<String>();
    parents_ = new HashMap<String, Set<String>>();
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

  public Factory getFactory()
  {
    return factory_;
  }

  /**
   * @return true if and only if this section has been checked.
   */
  public boolean isChecked(String section)
  {
    return checkedSections_.contains(section);
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
   * @return true if and only if this name is already declared
   */
  public boolean add(NameSectTypeTriple triple)
  {
    boolean result = false;

    //if not already declared, add this declaration to the environment
    NameSectTypeTriple existing = getTriple(triple.getName());
    if (existing == null) {
      typeInfo_.add(triple);
      result = true;
    }
    else {
      existing.setType(triple.getType());
    }

    return result;
  }

  /**
   * Add a <code>NameTypePair</code> to this environment.
   * @return true if and only if this name is already declared
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

    return result;
  }

  public List<NameSectTypeTriple> getNameSectTypeTriple()
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
    List<NameSectTypeTriple> triples = getNameSectTypeTriple();
    return factory_.createSectTypeEnvAnn(triples);
  }

  /**
   * Return the type of the variable.
   */
  public Type getType(RefName name)
  {
    DeclName declName = factory_.createDeclName(name);
    Type result = factory_.createUnknownType(declName);

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

      if (isSchema(baseType)) {
        // CloningVisitor cloner = new CloningVisitor();
        Type clonedType = (Type) factory_.cloneTerm(baseType);
        //Type clonedType = (Type) baseType.accept(cloner);
        PowerType powerType = (PowerType) unwrapType(clonedType);
        SchemaType schemaType = (SchemaType) powerType.getType();

        List<NameTypePair> newPairs = new ArrayList<NameTypePair>();
        List<NameTypePair> pairs =
          (List<NameTypePair>) schemaType.getSignature().getNameTypePair();
        for (NameTypePair pair : pairs) {
          //DeclName primedName = (DeclName) pair.getName().accept(cloner);
          DeclName primedName = (DeclName) factory_.cloneTerm(pair.getName());
          primedName.getStroke().add(factory_.createNextStroke());
          NameTypePair newPair =
            factory_.createNameTypePair(primedName, pair.getType());
          newPairs.add(newPair);
        }

        pairs.addAll(newPairs);

        if (baseType instanceof GenericType) {
          GenericType gType = (GenericType) baseType;
          result =
            factory_.createGenericType(gType.getName(), powerType, null);
        }
        else {
          result = powerType;
        }

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
    for (Iterator iter = typeInfo_.iterator(); iter.hasNext(); ) {
      NameSectTypeTriple next = (NameSectTypeTriple) iter.next();

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

    for (Iterator iter = typeInfo_.iterator(); iter.hasNext(); ) {
      NameSectTypeTriple next = (NameSectTypeTriple) iter.next();
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
      for (Iterator iter = parents.iterator(); iter.hasNext(); ) {
        String parent = (String) iter.next();
        Set<String> transitiveParents = getTransitiveParents(parent);
        result.addAll(transitiveParents);
      }
    }
    return result;
  }
}
