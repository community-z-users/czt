/*
  Copyright (C) 2004, 2005 Tim Miller
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

import java.util.Iterator;
import java.util.List;
import java.util.Set;
import java.util.Map;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.z.ast.*;

import net.sourceforge.czt.typecheck.z.impl.*;
import static net.sourceforge.czt.z.util.ZUtils.*;

public class GlobalDefs
{
  public static final UResult SUCC = UResult.SUCC;
  public static final UResult PARTIAL = UResult.PARTIAL;
  public static final UResult FAIL = UResult.FAIL;
  
  public static final Factory ZFACTORRY = new Factory();
  
  /**
   * Create an empty Set.
   * @return the empty set
   */
  public static <E> Set<E> set()
  {
    return new java.util.HashSet<E>();
  }
  
  /**
   * Create an empty List.
   * @return the empty list
   */
  public static <E> List<E> list()
  {
    return new java.util.ArrayList<E>();
  }

  /**
   * Create an empty Map.
   * @return the empty map
   */
  public static <E,F> Map<E,F> map()
  {
    return new java.util.HashMap<E,F>();
  }
  
  /**
   * If this is a generic type, get the type without the
   * parameters. If not a generic type, return the type.
   * @param type the <code>Type</code> to unwrap
   * @return if <code>type</code> is a generic type, return the inner
   * <code>Type2</code> object. Otherwise, return <code>type</code>
   */
  public static Type2 unwrapType(Type type)
  {
    Type2 result = null;
    if (type instanceof GenericType)
    {
      GenericType gType = (GenericType) type;
      Type2 optType = null;
      if (gType.getType().size() > 1) optType = gType.getType().get(1);
      result = optType == null ? gType.getType().get(0) : optType;
    }
    else
    {
      result = (Type2) type;
    }
    
    return result;
  }
  
  /**
   * Find a pair with a specified ZName in a list of NameTypePair.
   * @param zName the name to search for in the list.
   * @param pairs the list of NameTypePair to search.
   * @return the first pair with the corresponding name.
   */
  public static NameTypePair findNameTypePair(ZName zName,
    List<NameTypePair> pairs)
  {
    NameTypePair result = null;
    for (NameTypePair pair : pairs)
    {
      if (namesEqual(pair.getZName(), zName))
      {
        result = pair;
        break;
      }
    }
    return result;
  }
  
  /**
   * Find a pair with a specified ZName in a Signature.
   * @param zName the name to search for in the list.
   * @param signature the signature to search.
   * @return the first pair with the corresponding name.
   */
  public static NameTypePair findNameTypePair(ZName zName,
    Signature signature)
  {
    List<NameTypePair> pairs = signature.getNameTypePair();
    NameTypePair result = findNameTypePair(zName, pairs);
    return result;
  }
  
  /**
   * Test is an object is an instance of a class.
   * @param o the object to be tested.
   * @param aClass the <code>Class</code> the object against which the
   * object is tested.
   * @return true if and only if <code>o</code> is an instance of
   * <code>aClass</code>
   */
  public static boolean instanceOf(Object o, Class<?> aClass)
  {
    return aClass.isInstance(o);
  }
  
  /**
   * Resolve a type if it is a variable type.
   * @param type the <code>Type2</code> to be resolved.
   * @return if <code>type</code> is a variable type, return the type
   * to which it is unified (possibly itself). Otherwise, return
   * <code>type</code>
   */
  public static Type2 resolve(Type2 type)
  {
    Type2 result = type;
    if (type instanceof VariableType)
    {
      VariableType vType = (VariableType) type;
      if (vType.getValue() != vType)
      {
        result = vType.getValue();
      }
    }
    return result;
  }
  
  /**
   * Resolve a signature if it is a variable signature.
   * @param signature the <code>Signature</code> to be resolved.
   * @return if <code>signature</code> is a variable signature, return
   * the signature to which it is unified (possibly
   * itself). Otherwise, return <code>signature</code>
   */
  public static Signature resolve(Signature signature)
  {
    Signature result = signature;
    if (signature instanceof VariableSignature)
    {
      VariableSignature vSig = (VariableSignature) signature;
      if (vSig.getValue() != vSig)
      {
        result = vSig.getValue();
      }
    }
    return result;
  }
  
  /**
   * Adds an annotation to a <code>Term</code>.
   * @param term the <code>Term</code> to which to add the annotation.
   * @param ann the annotation to add.
   */
  public static void addAnn(Term term, Object ann)
  {
    if (ann != null)
    {
      term.getAnns().add(ann);
    }
  }
  
  /**
   * Removes an annotation from a <code>Term</code>.
   * @param term the <code>Term</code> from which to remove the annotation.
   * @param ann the annotation to remove.
   */
  public static void removeAnn(Term term, Object ann)
  {
    if (ann != null && term.annsSize() > 0)
    {
      List<Object> anns = term.getAnns();
      for (Iterator<Object> iter = anns.iterator(); iter.hasNext(); )
      {
        Object next = iter.next();
        if (next == ann)
        {
          iter.remove();
        }
      }
    }
  }
  
  /**
   * Removes all annotations of a particular class from a
   * <code>Term</code>.
   * @param term the <code>Term</code> from which to remove the
   * annotations.
   * @param aClass the class of annotations to remove.
   */
  public static void removeAnn(Term term, Class<?> aClass)
  {
    if (term.annsSize() > 0)
    {
      List<Object> anns = term.getAnns();
      for (Iterator<Object> iter = anns.iterator(); iter.hasNext(); )
      {
        Object ann = iter.next();
        if (aClass.isInstance(ann))
        {
          iter.remove();
        }
      }
    }
  }
  
  /**
   * Copies annoatations from one <code>Term</code> to another.
   * @param src the <code>Term</code> from which to read the annotations.
   * @param dest the <code>Term</code> to which to add the annotations.
   */
  public static void copyAnns(Term src, Term dest)
  {
    dest.getAnns().addAll(src.getAnns());
  }

  /**
   * Copies location annoatations from one <code>Term</code> to another.
   * @param src the <code>Term</code> from which to read the annotations.
   * @param dest the <code>Term</code> to which to add the annotations.
   */
  public static void copyLocAnn(Term src, Term dest)
  {
    List<Object> anns = src.getAnns();
    for (Object ann : anns) {
      if (ann instanceof LocAnn) {
	dest.getAnns().add(ann);
      }
    }
  }


  /**
   * Gets a type annotation from a term, returning an UnknownType is
   * no type is present.
   * @param term the <code>Term</code> from which to read the annotation.
   * @ @return the <code>Type</code> of the term.
   */
  public static Type getTypeFromAnns(Term term)
  {    
    Type result = ZFACTORRY.createUnknownType();
    TypeAnn typeAnn = (TypeAnn) term.getAnn(TypeAnn.class);
    
    if (typeAnn != null)
    {
      result = typeAnn.getType();
      // z.Checker.getTypeAnn could create an empty TypeAnn!
      assert result != null;
    }
    return result;
  }
  
  /**
   * Test whether a list contains a reference to an object.
   * @param list the list to search.
   * @param o the reference to search for.
   * @return true if and only if the reference is in the list.
   */
  public static <T> boolean containsObject(List<T> list, Object o)
  {
    boolean result = false;
    
    for (Iterator<T> iter = list.iterator(); iter.hasNext(); )
    {
      T next = iter.next();
      if (next == o)
      {
        result = true;
        break;
      }
    }
    return result;
  }
  
  /**
   * Remove all occurrences of a reference from a list.
   * @param list the list to search.
   * @param o the reference to be removed.
   */
  public static void removeObject(List<?> list, Object o)
  {
    for (Iterator<?> iter = list.iterator(); iter.hasNext(); )
    {
      Object next = iter.next();
      if (next == o)
      {
        iter.remove();
      }
    }
  } 
  
  //non-safe typecast
  public static SchemaType schemaType(Object o)
  {
    return (SchemaType) o;
  }
  
  //non-safe typecast
  public static PowerType powerType(Object o)
  {
    return (PowerType) o;
  }
  
  //non-safe typecast
  public static GivenType givenType(Object o)
  {
    return (GivenType) o;
  }
  
  //non-safe typecast
  public static GenericType genericType(Object o)
  {
    return (GenericType) o;
  }
  
  //non-safe typecast
  public static GenParamType genParamType(Object o)
  {
    return (GenParamType) o;
  }
  
  //non-safe typecast
  public static ProdType prodType(Object o)
  {
    return (ProdType) o;
  }
  
  //non-safe typecast
  public static UnknownType unknownType(Object o)
  {
    return (UnknownType) o;
  }
  
  //non-safe typecast
  public static VariableType variableType(Object o)
  {
    return (VariableType) o;
  }
  
  //non-safe typecast
  public static VariableSignature variableSignature(Object o)
  {
    return (VariableSignature) o;
  }
  
  /**
   * Gets the position of a Term from its annotations.
   */
  public static String position(Term term)
  {    
    String result = "Unknown location: ";
    
    LocAnn locAnn = nearestLocAnn(term);
    if (locAnn != null)
    {
      result = "\"" + locAnn.getLoc() + "\", ";
      result += "line " + locAnn.getLine() + ": ";
    }
    else
    {
      result = "No location information";
    }
    
    return result;
  }
  
  /**
   * Finds the closest LocAnn.
   */
  public static LocAnn nearestLocAnn(Term term)
  {
    LocAnn result = (LocAnn) term.getAnn(LocAnn.class);
    
    if (result == null)
    {
      for (int i = 0; i < term.getChildren().length; i++)
      {
        Object next = term.getChildren()[i];
        if (next instanceof Term)
        {
          LocAnn nextLocAnn = nearestLocAnn((Term) next);
          return nextLocAnn;
        }
      }
    }
    return result;
  }

  public static void printLocAnns(Term term, String info)
  {
    List<Object> anns = term.getAnns();
    for (Object ann : anns) {
      if (ann instanceof LocAnn) {
	System.err.println(info + " : " + ann.toString());
      }
    }
  }
}
