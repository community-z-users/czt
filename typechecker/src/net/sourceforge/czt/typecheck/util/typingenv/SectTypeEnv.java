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
import net.sourceforge.czt.typecheck.util.typeerror.*;
import net.sourceforge.czt.typecheck.z.*;
import net.sourceforge.czt.util.CztException;
import net.sourceforge.czt.z.util.ZString;

import net.sourceforge.czt.z.ast.*;

public class SectTypeEnv
{
  /** The name of the prelude section */
  public static final String PRELUDE = "prelude";

  /** a ZFactory */
  protected static ZFactory factory_ = null;

  /** the list of all NameSectTypeTriples checked so far */
  protected List typeInfo_ = null;

  /** the current section */
  protected String section_ = null;

  /** The currently visible sections */
  protected Set visibleSections_ = new HashSet();

  /** The function of all sections to their immediate parents */
  protected Map parents_ = new HashMap();

  public SectTypeEnv ()
  {
    factory_ = new net.sourceforge.czt.z.impl.ZFactoryImpl();
    typeInfo_ = new ArrayList();
    parents_ = new HashMap();
  }

  public NameSectTypeTriple addNameSectTypePair(NameSectTypeTriple ntPair)
    throws TypeException
  {
    NameSectTypeTriple result = null;
    /*
    DeclName dn = ntPair.getName();
    String name = dn.getWord();
    System.out.println("sect = " + ntPair.getSect());
    System.out.println("name = " + name);
    NameSectTypeTriple pair1 = search(name);
    //System.out.println("pair1 = " + pair1 + " " + (pair1 != null));
    if (pair1 == null) {
      add(ntPair);
      result = ntPair;
    }
    else {
      String sn = ntPair.getSect();
      String sect1 = pair1.getSect();
      if (! sn.equals(sect1)) {
        result = pair1;
        throw new TypeException(ErrorKind.SECT_REDECLARATION, pair1);
      }
      else {
        Type ntType = ntPair.getType();
        Type type1 = pair1.getType();
        if (! TypeChecker.unify(ntType, type1)) {
          result = pair1;
          throw new TypeException(ErrorKind.REDECLARATION, ntPair);
        }
        else {
          result = ntPair;
        }
      }
    }
    */
    return result;
  }

  private void add(NameSectTypeTriple ntPair)
  {
    //    typeEnv_.add(ntPair);
  }

  public NameSectTypeTriple search(String name)
  {
    NameSectTypeTriple result = null;
    /*
    NameSectTypeTriple temp = null;
    for (int i = typeEnv_.size() - 1; i >= 0; i--) {
      temp = (NameSectTypeTriple) typeEnv_.get(i);
      String name1 = temp.getName().getWord();
      if (name.equals(name1)) {
        result = temp;
        break;
      }
    }
    */
    return result;
  }

  /**
   * Set the current section.
   * @param section the section
   */
  public void setSection(String section)
  {
    endSection();
    visibleSections_.add(PRELUDE);
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
    throws TypeException
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
    throws TypeException
  {
    //first check to see if this has already been declared
    NameSectTypeTriple triple = getTriple(declName);
    if (triple != null &&
	visibleSections_.contains(triple.getSect())) {
      String message = "Redeclared name: " + toString(declName);
      throw new TypeException(ErrorKind.REDECLARATION, declName, message);
    }

    //insert the triple into the list of all triples and the
    //annotation for the current section
    NameSectTypeTriple insert =
      factory_.createNameSectTypeTriple(declName, section_, type);
    typeInfo_.add(insert);
  }

  public void checkAndAdd(SectTypeEnvAnn ann){}

  public SectTypeEnvAnn getSectTypeEnvAnn()
  {
    return factory_.createSectTypeEnvAnn(typeInfo_);
  }

  /**
   * Return the type of the variable 
   */
  public Type getType(Name name)
  {
    Type result = UnknownTypeImpl.create();

    //get the info for this name
    NameSectTypeTriple triple = getTriple(name);
    if (triple != null && visibleSections_.contains(triple.getSect())) {
      result = triple.getType();
    }

    return result;
  }

  /**
   * Returns the type that an element of a specified type would have
   * TODO: not sure what to do with SchemaTypes yet
   */
  public static Type getElementType(Type type)
    throws TypeException
  {
    Type result = null;

    //these are error cases
    if (type instanceof GivenType ||
	type instanceof GenType ||
	type instanceof ProdType) {
      //TODO: not the best error message, but will do for now
      throw new TypeException(ErrorKind.POWERTYPE_NEEDED, type);
    }
    //if it's a PowerType, get the inner type
    else if (type instanceof PowerType) {
      PowerType powerType = (PowerType) type;
      result = powerType.getType();
    }
    else if (type instanceof UnknownType) {
      result = UnknownTypeImpl.create();
    }
    else {
      System.err.println("unknown type: " + toString(type));
    }

    return result;
  }

  /**
   * For testing purposes
   */
  public void dump()
  {
    System.err.println("typeinfo:");
    for (Iterator iter = typeInfo_.iterator(); iter.hasNext(); ) {
      NameSectTypeTriple next = (NameSectTypeTriple) iter.next();

      System.err.print("\t(" + next.getName().getWord());
      System.err.print(", (" + next.getSect());
      System.err.println(", (" + toString(next.getType()) + ")))");
    }
  }

  //get a triple whose name matches a specified name and it
  //defined in a currently visible scope
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
  private Set getTransitiveParents(String section) {
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

  public static String toString(Type type) 
  {
    String result = new String();
    if (type instanceof PowerType) {
      PowerType powerType = (PowerType) type;
      result += "power (";
      result += toString(powerType.getType());
      result += ")";
    }
    else if (type instanceof GenType) {
      GenType genType = (GenType) type;
      result += "GEN ";
      result += genType.getName().getWord();
    }
    else if (type instanceof GivenType) {
      GivenType givenType = (GivenType) type;
      result += "GIVEN ";
      result += givenType.getName().getWord();
    }
    else if (type instanceof ProdType) {
      ProdType prodType = (ProdType) type;
      List list = prodType.getType();
      result += "(";
      for (int i = 0; i < list.size() - 1; i++) {
	Type next = (Type) list.get(i);
	result += toString(next) + " cross ";
      }
      result += toString((Type) list.get(list.size() - 1));
      result += ")";
    }
    else if (type instanceof SchemaType) {
      SchemaType schemaType = (SchemaType) type;
      result += "schema (";
      List list = schemaType.getSignature().getNameTypePair();
      if (list.size() > 0) {
	for (int i = 0; i < list.size() - 1; i++) {
	  NameTypePair pair = (NameTypePair) list.get(i);
	  result += toString(pair.getName()) + " : " + 
	    toString(pair.getType());
	  result += "; ";
	}
	NameTypePair pair = (NameTypePair) list.get(list.size() - 1);
	result += toString(pair.getName()) + " : " +
	  toString(pair.getType());
      }
    }
    else if (type instanceof UnknownType) {
      result += "unknown";
    }
    else {
      result += "type:" + type.getClass().getName();
    }

    return result;
  }

  //convert a name into a string
  public static String toString(Name name)
  {
    String result = name.getWord();

    for (Iterator iter = name.getStroke().iterator(); iter.hasNext(); ) {
      Stroke stroke = (Stroke) iter.next();

      if (stroke instanceof InStroke) {
	result += ZString.INSTROKE;
      }
      else if (stroke instanceof OutStroke) {
	result += ZString.OUTSTROKE;
      }
      else if (stroke instanceof NextStroke) {
	result += ZString.PRIME;
      }
      else if (stroke instanceof NumStroke) {
	NumStroke numStroke = (NumStroke) stroke;
	result += ZString.SE + numStroke.getNumber() + ZString.NW;
      }
    }

    return result;
  }
}
