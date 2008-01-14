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
   * Find a pair with a specified ZName in a list of NameTypePair.
   * @param zName the name to search for in the list.
   * @param pairs the list of NameTypePair to search.
   * @return the first pair with the corresponding name.
   */
  public static NameTypePair findNameTypePair(ZName zName,
                                              List<NameTypePair> pairs)
  {
    NameTypePair result = null;
    for (NameTypePair pair : pairs) {
      if (namesEqual(pair.getZName(), zName)) {
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
   * Adds an annotation to a <code>Term</code>.
   * @param term the <code>Term</code> to which to add the annotation.
   * @param ann the annotation to add.
   */
  public static void addAnn(Term term, Object ann)
  {
    if (ann != null) {
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
    if (ann != null) {
      List anns = term.getAnns();
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
   * <code>Term</code>.
   * @param term the <code>Term</code> from which to remove the
   * annotations.
   * @param aClass the class of annotations to remove.
   */
  public static void removeAnn(Term term, Class aClass)
  {
    List anns = term.getAnns();
    for (Iterator iter = anns.iterator(); iter.hasNext(); ) {
      Object ann = iter.next();
      if (aClass.isInstance(ann)) {
        iter.remove();
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
   * Gets a type annotation from a term, returning an UnknownType is
   * no type is present.
   * @param term the <code>Term</code> from which to read the annotation.
   @ @return the <code>Type</code> of the term.
   */
  public static Type getTypeFromAnns(Term term)
  {
    Factory factory = new Factory();
    Type result = factory.createUnknownType();
    TypeAnn typeAnn = (TypeAnn) term.getAnn(TypeAnn.class);

    if (typeAnn != null) {
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
   * Test whether a list contains a ZName.
   * @param list the list to search.
   * @param zName the ZName to search for.
   * @return true if and only if the name is in the list.
   */
  public static boolean containsZName(List<ZName> list,
                                      ZName zName)
  {
    boolean result = false;
    for (ZName next : list) {
      if (namesEqual(next, zName)) {
        result = true;
        break;
      }
    }
    return result;
  }

  /**
   * Test whether a list contains a ZName with the same ID.
   * @param list the list to search.
   * @param zName the ZName to search for.
   * @return true if and only if the name is in the list.
   */
  public static boolean containsID(List<ZName> list,
                                   ZName zName)
  {
    boolean result = false;
    for (ZName next : list) {
      if (next.getId().equals(zName.getId())) {
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
   * Test whether the base name and strokes of two ZNames are equal.
   */
  public static boolean namesEqual(ZName zName1, ZName zName2)
  {
    boolean result = zName1.getWord().equals(zName2.getWord()) &&
      zName1.getStrokeList().equals(zName2.getStrokeList());
    return result;
  }

  /**
   * Test whether the base name and strokes of two Names are equal.
   */
  public static boolean namesEqual(Name name1, Name name2)
  {
    boolean result = false;
    if (name1 instanceof ZName && name2 instanceof ZName) {
      result = namesEqual((ZName) name1, (ZName) name2);
    }
    return result;
  }

  public static boolean idsEqual(String id1, String id2)
  {
    boolean result = id1 != null && id2 != null && id1.equals(id2);
    return result;
  }

  public static Signature sort(Signature signature)
  {
    sort(signature.getNameTypePair());
    return signature;
  }

  public static List<NameTypePair> sort(List<NameTypePair> pairs)
  {
    for (int j = 1; j < pairs.size(); j++) {
      NameTypePair pair = pairs.get(j);
      int i = j - 1;
      while (i >= 0 && compareTo(pairs.get(i).getZName(),
                                 pair.getZName()) > 0) {
        pairs.set(i + 1, pairs.get(i));
        i--;
      }
      pairs.set(i + 1, pair);
    }
    return pairs;
  }

  public static void insert(List<NameTypePair> pairsA,
                            List<NameTypePair> pairsB)
  {
    for (NameTypePair pair : pairsB) {
      insert(pairsA, pair);
    }
  }

  //precondition: pairs is sorted
  public static void insert(List<NameTypePair> pairs, NameTypePair pair)
  {
    int i = 0;
    while (i < pairs.size() &&
           compareTo(pairs.get(i).getZName(), pair.getZName()) < 0) {
      i++;
    }
    pairs.add(i, pair);
  }

  public static int compareTo(ZName zName1, ZName zName2)
  {
    String word1 = zName1.getWord();
    String word2 = zName2.getWord();
    int compareWord = word1.compareTo(word2);
    if (compareWord != 0) {
      return compareWord;
    }
    else {
      ZStrokeList strokes1 = zName1.getZStrokeList();
      ZStrokeList strokes2 = zName2.getZStrokeList();
      int lengthDiff = strokes1.size() - strokes2.size();
      if (lengthDiff != 0) {
        return lengthDiff;
      }
      else {
        //sort as ? < ! < ' < num
        for (int i = 0; i < strokes1.size(); i++) {
          int stroke1Val = getValue(strokes1.get(i));
          int stroke2Val = getValue(strokes2.get(i));
          int compareStroke = stroke1Val - stroke2Val;
          if (compareStroke != 0) {
            return compareStroke;
          }
        }
        return 0;
      }
    }
  }

  public static int getValue(Stroke stroke)
  {
    int result = -1;
    if (stroke instanceof InStroke) {
      result = 0;
    }
    else if (stroke instanceof OutStroke) {
      result = 1;
    }
    else if (stroke instanceof NextStroke) {
      result = 2;
    }
    else if (stroke instanceof NumStroke) {
      result = 3;
    }
    else {
      assert false : "Stroke instanceof " + stroke.getClass().getName();
    }
    return result;
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
