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
import java.util.Set;
import java.util.Map;
import java.util.Iterator;

import static net.sourceforge.czt.typecheck.z.util.GlobalDefs.*;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.util.ZString;
import net.sourceforge.czt.z.impl.ZFactoryImpl;
import net.sourceforge.czt.typecheck.z.*;
import net.sourceforge.czt.typecheck.z.impl.*;

/**** TODO: Remove this ****/
import net.sourceforge.czt.oz.ast.*;

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
  protected List<ZDeclName> declarations_;

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
    typeInfo_ = factory_.list();
    declarations_ = factory_.list();
    sectionDeclarations_ = factory_.list();
    visibleSections_ = set();
    checkedSections_ = set();
    parents_ = map();
  }

  public void overwriteTriples(List<NameSectTypeTriple> triples)
  {
    typeInfo_ = factory_.list();
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
      parents = set();
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
    NameSectTypeTriple existing = getTriple(triple.getZDeclName());
    if (existing == null) {
      typeInfo_.add(triple);
      result = true;
    }
    else {
      existing.setType(triple.getType());
    }

    if (secondTime_) {
      result = !declarations_.contains(triple.getZDeclName());
      declarations_.add(triple.getZDeclName());
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
    return add(nameTypePair.getZDeclName(), nameTypePair.getType());
  }

  public boolean add(ZDeclName zDeclName, Type type)
  {
    boolean result = true;
    for (NameSectTypeTriple triple : typeInfo_) {
      if (namesEqual(triple.getZDeclName(), zDeclName)) {
        triple.setType(type);
        result = false;
      }
    }

    if (result) {
      NameSectTypeTriple insert =
        factory_.createNameSectTypeTriple(zDeclName, section_, type);
      typeInfo_.add(insert);
    }

    if (secondTime_) {
      result = !declarations_.contains(zDeclName);
      declarations_.add(zDeclName);
    }

    return result;
  }

  public boolean update(ZRefName zRefName, Type type)
  {
    NameSectTypeTriple triple = getTriple(zRefName);
    if (triple != null) {
      triple.setType(type);
    }
    else {
      ZDeclName zDeclName = factory_.createZDeclName(zRefName);
      NameSectTypeTriple insert =
        factory_.createNameSectTypeTriple(zDeclName, section_, type);
      typeInfo_.add(insert);
    }
    return true;
  }

  public List<NameSectTypeTriple> getTriple()
  {
    List<NameSectTypeTriple> triples = factory_.list();
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
  public Type getType(ZRefName zRefName)
  {
    ZDeclName zDeclName = factory_.createZDeclName(zRefName);
    Type result = factory_.createUnknownType();

    //get the info for this name
    NameSectTypeTriple triple = getTriple(zRefName);
    if (triple != null && visibleSections_.contains(triple.getSect())) {
      result = triple.getType();
      zRefName.setDecl(triple.getZDeclName());
    }

    //if the type is unknown and the name starts with delta or xi, try
    //looking up the base name
    if (result instanceof UnknownType &&
        (zRefName.getWord().startsWith(ZString.DELTA) ||
         zRefName.getWord().startsWith(ZString.XI))) {
      final int size = (ZString.DELTA).length();
      String baseWord = zRefName.getWord().substring(size);
      ZRefName baseName =
        factory_.createZRefName(baseWord, zRefName.getStroke(), null);
      Type baseType = getType(baseName);

      //if this is a schema, determine and add the delta/xi type
      if (isSchema(baseType)) {
        PowerType powerType = (PowerType) unwrapType(baseType);
        SchemaType schemaType = (SchemaType) powerType.getType();
        Signature signature = schemaType.getSignature();

        List<NameTypePair> pairs = signature.getNameTypePair();
        List<NameTypePair> newPairs = factory_.list(pairs);
        for (NameTypePair pair : pairs) {
          ZDeclName primedName = factory_.createZDeclName(pair.getZDeclName());
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
        add(zDeclName, result);
      }
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
      System.err.print("\t(" + next.getZDeclName());
      System.err.print(", (" + next.getSect());
      System.err.println(", (" + toString2(next.getType()) + ")))");
    }
  }

  private NameSectTypeTriple getTriple(ZRefName zRefName)
  {
    ZDeclName zDeclName = factory_.createZDeclName(zRefName);
    return getTriple(zDeclName);
  }

  //get a triple whose name matches a specified name and it
  //defined in a currently visible scope.
  private NameSectTypeTriple getTriple(ZDeclName zDeclName)
  {
    NameSectTypeTriple result = null;
    for (NameSectTypeTriple triple : typeInfo_) {
      //we don't use equals() in DeclName so that we can use this
      //lookup for RefName objects as well
      if (namesEqual(triple.getZDeclName(), zDeclName) &&
          (visibleSections_.contains(section_) ||
           triple.getSect().equals(PRELUDE))) {
        result = triple;
        break;
      }
    }
    return result;
  }

  //get the transitive parents of a section
  private Set<String> getTransitiveParents(String section)
  {
    Set<String> result = set();

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

  protected List<Type> seen = new java.util.ArrayList<Type>();
  public String toString2(Type type)
  {
    seen = new java.util.ArrayList<Type>();
    return toString(type);
  }

  public String toString(Type type)
  {
    String result = new String();
    if (unwrapType(type) instanceof PowerType &&
        powerType(unwrapType(type)).getType() instanceof ClassRefType) {
      net.sourceforge.czt.oz.ast.ClassRefType ctype =
        (ClassRefType) powerType(unwrapType(type)).getType();
      if (!containsObject(seen, ctype)) {
        seen.add(ctype);
        result = "P " + classRefTypeToString(ctype);
      }
    }
    else if (type instanceof net.sourceforge.czt.oz.ast.ClassRefType) {
      ClassRefType ctype = (ClassRefType) type;
      if (!containsObject(seen, ctype)) {
        seen.add(ctype);
        result = classRefTypeToString(ctype);
      }
    }
    else {
      result = type.toString();
    }
    return result;
  }

  public String classRefTypeToString(ClassRefType ctype)
  {
    String result = new String();
    ZRefName className = ctype.getThisClass().getZRefName();
    result += "(CLASS " + className + "\n";

    ClassSig csig = ctype.getClassSig();
    result += "\tREF(" + csig.getClasses() + ")\n";
    result += "\tATTR(" + className + ")\n";
    for (Object o : csig.getAttribute()) {
      NameTypePair pair = (NameTypePair) o;
      result += "\t\t" + pair.getZDeclName() + " : " + pair.getType() + "\n";
    }
    result += "\tSTATE(" + className + ")\n";
    for (Object o : csig.getState().getNameTypePair()) {
      NameTypePair pair = (NameTypePair) o;
      result += "\t\t" + pair.getZDeclName() + " : " + toString(pair.getType()) + "\n";
    }
    result += "\tOPS(" + className + ")\n";
    for (Object o : csig.getOperation()) {
      NameSignaturePair p = (net.sourceforge.czt.oz.ast.NameSignaturePair) o;
      result += "\t\t" + p.getZDeclName() + " : " + p.getSignature() + "\n";
    }
    result += ")";
    return result;
  }
}
