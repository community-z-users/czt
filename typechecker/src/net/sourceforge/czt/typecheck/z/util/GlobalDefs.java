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

public class GlobalDefs
{
  public static final UResult SUCC = UResult.SUCC;
  public static final UResult PARTIAL = UResult.PARTIAL;
  public static final UResult FAIL = UResult.FAIL;

  /**
   * Create an empty list.
   * @return the empty list
   */
  public static <E> List<E> list()
  {
    return new java.util.ArrayList<E>();
  }

  /**
   * Create a list containing a specified element.
   * @param e the specified element
   * @return a list containg only <code>e</code>
   */
  public static <E> List<E> list(E e)
  {
    List<E> result = list();
    result.add(e);
    return result;
  }

  /**
   * Create a list containing two specified elements.
   * @param e1 the first specified element
   * @param e2 the second specified element
   * @return a list containg only the specified elements.
   */
  public static <E> List<E> list(E e1, E e2)
  {
    List<E> result = list(e1);
    result.add(e2);
    return result;
  }

  /**
   * Create a list from another list.
   * @param list the list from which to copy the members.
   * @return a new list containing the elements in <code>list</code>
   */
  public static <E> List<E> list(List<E> list)
  {
    List<E> result = new java.util.ArrayList<E>(list);
    return result;
  }

  /**
   * Create an empty Set.
   * @return the empty set
   */
  public static <E> Set<E> set()
  {
    return new java.util.HashSet<E>();
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
    if (type instanceof GenericType) {
      GenericType gType = (GenericType) type;
      Type2 optType = gType.getOptionalType();
      result = optType == null ? gType.getType() : optType;
    }
    else {
      result = (Type2) type;
    }

    return result;
  }

  /**
   * Find a pair with a specified ZDeclName in a list of NameTypePair.
   * @param zDeclName the name to search for in the list.
   * @param pairs the list of NameTypePair to search.
   * @return the first pair with the corresponding name.
   */
  public static NameTypePair findNameTypePair(ZDeclName zDeclName,
					      List<NameTypePair> pairs)
  {
    NameTypePair result = null;
    for (NameTypePair pair : pairs) {
      if (namesEqual(pair.getZDeclName(), zDeclName)) {
        result = pair;
        break;
      }
    }
    return result;
  }

  /**
   * Find a pair with a specified ZDeclName in a Signature.
   * @param zDeclName the name to search for in the list.
   * @param signature the signature to search.
   * @return the first pair with the corresponding name.
   */
  public static NameTypePair findNameTypePair(ZDeclName zDeclName,
					      Signature signature)
  {
    List<NameTypePair> pairs = signature.getNameTypePair();
    NameTypePair result = findNameTypePair(zDeclName, pairs);
    return result;
  }

  /**
   * Test is an object is an instance of a class
   * @param o the object to be tested.
   * @param aClass the <code>Class</code> the object against which the
   * object is tested.
   * @return true if and only if <code>o</code> is an instance of
   * <code>aClass</code>
   */
  public static boolean instanceOf(Object o, Class aClass)
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
    if (type instanceof VariableType) {
      VariableType vType = (VariableType) type;
      if (vType.getValue() != vType) {
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
    if (signature instanceof VariableSignature) {
      VariableSignature vSig = (VariableSignature) signature;
      if (vSig.getValue() != vSig) {
        result = vSig.getValue();
      }
    }
    return result;
  }

  /**
   * Adds an annotation to a <code>TermA</code>
   * @param termA the <code>TermA</code> to which to add the annotation.
   * @param ann the annotation to add.
   */
  public static void addAnn(TermA termA, Object ann)
  {
    if (ann != null) {
      termA.getAnns().add(ann);
    }
  }

  /**
   * Removes an annotation from a <code>TermA</code>
   * @param termA the <code>TermA</code> from which to remove the annotation.
   * @param ann the annotation to remove.
   */
  public static void removeAnn(TermA termA, Object ann)
  {
    if (ann != null) {
      List anns = termA.getAnns();
      for (Iterator iter = anns.iterator(); iter.hasNext(); ) {
        Object next = iter.next();
        if (next == ann) {
          iter.remove();
        }
      }
    }
  }

  /**
   * Removes all annotations of a particular class from a
   * <code>TermA</code>
   * @param termA the <code>TermA</code> from which to remove the
   * annotations.
   * @param aClass the class of annotations to remove.
   */
  public static void removeAnn(TermA termA, Class aClass)
  {
    List anns = termA.getAnns();
    for (Iterator iter = anns.iterator(); iter.hasNext(); ) {
      Object ann = iter.next();
      if (aClass.isInstance(ann)) {
        iter.remove();
      }
    }
  }

  /**
   * Test whether a list contains a reference to an object.
   * @param list the list to search.
   * @param o the reference to search for.
   * @return true if and only if the reference is in the list.
   */
  public static boolean containsObject(List list, Object o)
  {
    boolean result = false;

    for (Iterator iter = list.iterator(); iter.hasNext(); ) {
      Object next = iter.next();
      if (next == o) {
        result = true;
        break;
      }
    }
    return result;
  }

  /**
   * Test whether a list contains a ZDeclName.
   * @param list the list to search.
   * @param zDeclName the ZDeclName to search for.
   * @return true if and only if the name is in the list.
   */
  public static boolean containsZDeclName(List<ZDeclName> list,
                                         ZDeclName zDeclName)
  {
    boolean result = false;
    for (ZDeclName next : list) {
      if (namesEqual(next, zDeclName)) {
        result = true;
        break;
      }
    }
    return result;
  }

  /**
   * Test whether a list contains a ZRefame.
   * @param list the list to search.
   * @param zRefName the ZRefName to search for.
   * @return true if and only if the name is in the list.
   */
  public static boolean containsRefName(List<ZRefName> list,
                                        ZRefName zRefName)
  {
    boolean result = false;
    for (ZRefName next : list) {
      if (namesEqual(next, zRefName)) {
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
  public static void removeObject(List list, Object o)
  {
    for (Iterator iter = list.iterator(); iter.hasNext(); ) {
      Object next = iter.next();
      if (next == o) {
        iter.remove();
      }
    }
  }

  /**
   * Test whether the base name and strokes of two ZDeclNames are equal.
   */
  public static boolean namesEqual(ZDeclName zDeclName1, ZDeclName zDeclName2)
  {
    boolean result = zDeclName1.getWord().equals(zDeclName2.getWord()) &&
      zDeclName1.getStroke().equals(zDeclName2.getStroke());
    return result;
  }

  /**
   * Test whether the base name and strokes of two DeclNames are equal.
   */
  public static boolean namesEqual(ZDeclName zDeclName, ZRefName zRefName)
  {
    boolean result =zDeclName.getWord().equals(zRefName.getWord()) &&
      zDeclName.getStroke().equals(zRefName.getStroke());
    return result;
  }

  /**
   * Test whether the base name and strokes of two RefNames are equal.
   */
  public static boolean namesEqual(ZRefName zRefName1, ZRefName zRefName2)
  {
    boolean result = zRefName1.getWord().equals(zRefName2.getWord()) &&
      zRefName1.getStroke().equals(zRefName2.getStroke());
    return result;
  }

  public static ZDeclName assertZDeclName(DeclName declName)
  {
    if (declName instanceof ZDeclName) {
      return (ZDeclName) declName;
    }
    else {
      throw new net.sourceforge.czt.base.util.UnsupportedAstClassException();
    }
  }

  public static ZRefName assertZRefName(RefName refName)
  {
    if (refName instanceof ZRefName) {
      return (ZRefName) refName;
    }
    else {
      throw new net.sourceforge.czt.base.util.UnsupportedAstClassException();
    }
  }

  public static ZNumeral assertZNumeral(Numeral numeral)
  {
    if (numeral instanceof ZNumeral) {
      return (ZNumeral) numeral;
    }
    else {
      throw new net.sourceforge.czt.base.util.UnsupportedAstClassException();
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
}
