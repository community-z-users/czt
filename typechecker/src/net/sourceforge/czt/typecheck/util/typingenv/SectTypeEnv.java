package net.sourceforge.czt.typecheck.util.typingenv;

import java.io.*;
import java.util.List;
import java.util.ArrayList;
import java.util.Set;
import java.util.HashSet;
import java.util.Map;
import java.util.HashMap;
import java.util.Iterator;

import net.sourceforge.czt.typecheck.util.*;
import net.sourceforge.czt.typecheck.z.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.util.ZString;

/**
 * A <code>SectTypeEnv</code> maintains a mapping between a global
 * declaration, its section name, and its type.
 */
public class SectTypeEnv
{
  /** The name of the prelude section. */
  public static final String PRELUDE = "prelude";

  /** A ZFactory. */
  protected static ZFactory factory_ = null;

  /** The list of all NameSectTypeTriples add so far. */
  protected List typeInfo_ = null;

  /** The current section. */
  protected String section_ = null;

  /** The currently visible sections. */
  protected Set visibleSections_ = new HashSet();

  /** The function of all sections to their immediate parents. */
  protected Map parents_ = new HashMap();

  public SectTypeEnv()
  {
    factory_ = new net.sourceforge.czt.z.impl.ZFactoryImpl();
    typeInfo_ = new ArrayList();
    parents_ = new HashMap();
  }

  /**
   * Set the current section.
   * @param section the section
   */
  public void setSection(String section)
  {
    visibleSections_.add(section);
    section_ = section;
  }

  /**
   * @return the current section
   */
  public String getSection()
  {
    return section_;
  }

  /**
   * Set the visible sections.
   * @param visibleSections the new visible sections
   */
  public void setVisibleSections(Set visibleSections)
  {
    visibleSections_ = visibleSections;
  }

  /**
   * @return the visible sections
   */
  public Set getVisibleSections()
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
    Set parents = (Set) parents_.get(section_);

    //add the parents to the list of the current section's parents
    if (parents == null) {
      parents = new HashSet();
    }
    parents.add(parent);
    parents_.put(section_, parents);

    //add the transitive parents
    visibleSections_.addAll(getTransitiveParents(parent));
  }

  public void add(List nameTypePairs)
  {
    for (Iterator iter = nameTypePairs.iterator(); iter.hasNext(); ) {
      NameTypePair nameTypePair = (NameTypePair) iter.next();
      add(nameTypePair);
    }
  }

  public void add(NameTypePair nameTypePair)
  {
    add(nameTypePair.getName(), nameTypePair.getType());
  }

  public void add(DeclName declName, Type type)
  {
    //first check to see if this has already been declared
    //if so, update the value of the type
    NameSectTypeTriple triple = getTriple(declName);
    if (triple != null &&
        visibleSections_.contains(triple.getSect())) {
      triple.setType(type);
    }
    //otherwise insert the triple into the list of all triples and the
    //annotation for the current section
    else {
      NameSectTypeTriple insert =
        factory_.createNameSectTypeTriple(declName, section_, type);
      typeInfo_.add(insert);
    }
  }

  public List getNameSectTypeTriple()
  {
    return typeInfo_;
  }

  public SectTypeEnvAnn getSectTypeEnvAnn()
  {
    return factory_.createSectTypeEnvAnn(typeInfo_);
  }

  /**
   * Return the type of the variable.
   */
  public Type getType(Name name)
  {
    DeclName declName =
      factory_.createDeclName(name.getWord(), name.getStroke(), null);

    Type result = UnknownTypeImpl.create(declName, true);

    //get the info for this name
    NameSectTypeTriple triple = getTriple(name);
    if (triple != null && visibleSections_.contains(triple.getSect())) {
      result = triple.getType();
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
        CloningVisitor cloner = new CloningVisitor();
        Type clonedType = (Type) baseType.accept(cloner);
        PowerType powerType = (PowerType) unwrapType(clonedType);
        SchemaType schemaType = (SchemaType) powerType.getType();

        List newPairs = new ArrayList();
        List pairs = schemaType.getSignature().getNameTypePair();
        for (Iterator iter = pairs.iterator(); iter.hasNext(); ) {
          NameTypePair pair = (NameTypePair) iter.next();
          DeclName primedName = (DeclName) pair.getName().accept(cloner);
          primedName.getStroke().add(factory_.createNextStroke());
          NameTypePair newPair =
            factory_.createNameTypePair(primedName, pair.getType());
          newPairs.add(newPair);
        }

        pairs.addAll(newPairs);
        result = powerType;
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
   * Update the types of variables that used other variables before
   * they are declared.
   */
  public void expandUnknownTypes()
  {
    TypeUpdatingVisitor typeUpdatingVisitor =
      new TypeUpdatingVisitor(this);

    //update references to all unknown types that contain 'declName'
    for (Iterator iter = typeInfo_.iterator(); iter.hasNext(); ) {
      NameSectTypeTriple next = (NameSectTypeTriple) iter.next();
      if (visibleSections_.contains(next.getSect())) {
        Type newType = (Type) next.getType().accept(typeUpdatingVisitor);
        next.setType(newType);
      }
    }
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

    /*
    expandUnknownTypes();

    System.err.println("\ntypeinfo2:");
    for (Iterator iter = typeInfo_.iterator(); iter.hasNext(); ) {
      NameSectTypeTriple next = (NameSectTypeTriple) iter.next();

      System.err.print("\t(" + next.getName());
      System.err.print(", (" + next.getSect());
      System.err.println(", (" + next.getType() + ")))");
    }
    */
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
  private Set getTransitiveParents(String section)
  {
    Set result = new HashSet();

    //get the set of direct parents
    Set parents = (Set) parents_.get(section);

    if (parents != null) {
      result.addAll(parents);

      //for each direct parent, get the transitive parents
      for (Iterator iter = parents.iterator(); iter.hasNext(); ) {
        String parent = (String) iter.next();
        Set transitiveParents = getTransitiveParents(parent);
        result.addAll(transitiveParents);
      }
    }
    return result;
  }
}
