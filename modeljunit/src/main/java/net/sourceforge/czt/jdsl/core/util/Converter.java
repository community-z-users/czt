/*
  Copyright (c) 1999, 2000 Brown University, Providence, RI
  
                            All Rights Reserved
  
  Permission to use, copy, modify, and distribute this software and its
  documentation for any purpose other than its incorporation into a
  commercial product is hereby granted without fee, provided that the
  above copyright notice appear in all copies and that both that
  copyright notice and this permission notice appear in supporting
  documentation, and that the name of Brown University not be used in
  advertising or publicity pertaining to distribution of the software
  without specific, written prior permission.
  
  BROWN UNIVERSITY DISCLAIMS ALL WARRANTIES WITH REGARD TO THIS
  SOFTWARE, INCLUDING ALL IMPLIED WARRANTIES OF MERCHANTABILITY AND
  FITNESS FOR ANY PARTICULAR PURPOSE.  IN NO EVENT SHALL BROWN
  UNIVERSITY BE LIABLE FOR ANY SPECIAL, INDIRECT OR CONSEQUENTIAL
  DAMAGES OR ANY DAMAGES WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR
  PROFITS, WHETHER IN AN ACTION OF CONTRACT, NEGLIGENCE OR OTHER
  TORTIOUS ACTION, ARISING OUT OF OR IN CONNECTION WITH THE USE OR
  PERFORMANCE OF THIS SOFTWARE.
*/
// Jan 2006: marku@cs.waikato.ac.nz, added the full package name of
//   PriorityQueue, to fix ambiguity with Java 1.5 PriorityQueue.

package net.sourceforge.czt.jdsl.core.util;

import net.sourceforge.czt.jdsl.core.ref.*;
import net.sourceforge.czt.jdsl.core.api.*;
import net.sourceforge.czt.jdsl.graph.api.*;
import java.util.*;



/**
 * Provides for conversion of JDSL data structures to java.util
 * Collections and Java base types and for conversion of java.util
 * Collections to JDSL data structures.<p>
 *
 * The conversion format is <code>method(from,to)</code>, where
 * <code>from</code> is the instance you wish to convert and
 * <code>to</code> is a new instance that you wish to contain the
 * contents of the converted instance.  If the <code>to</code>
 * instance is non-empty, the old contents will be retained with the
 * new contents added in, and the new elements added to the end (for
 * linear data structures).<p>
 *
 * In methods that convert iterators to dictionaries or priority
 * queues, we try to resolve the iterator's contents as Locators or
 * KeyEntries (as appropriate).  Failing this, we insert elements of
 * the iterator with themselves as their keys.<p>
 *
 * JDSL data structures are all multi-maps, but the corresponding
 * java.util data structures need not be.  In the event a conversion
 * is requested to a single-map java.util Collection, and the JDSL
 * data structure has multiple copies of one key or element in
 * violation of the java.util structure's requirements, an
 * InvalidContainerException will be thrown.<p>
 *
 * If a conversion fails due to elements that are unacceptable to the
 * to java.util instance for reasons other than these, its exception
 * (ClassCastException, IllegalArgumentExeption) will be allowed to
 * pass through.<p>
 *
 * In all descriptions of time complexity, N is the number of elements
 * in the <code>from</code> data structure.<p>
 */ 
public class Converter {

  /**
   * Places the contents of a sequence into a list, preserving order.
   * Running-time is O(N) for ref implementations of Sequence,
   * including ArraySequence and NodeSequence, and for all current
   * util implementations of List, including ArrayList (amortized
   * O(N)), LinkedList, and Vector (amortized O(N)).  Dependent upon
   * after() in Sequence and add(Object) in List for unknown
   * implementations.
   *
   * The method used here is different from the method used in other
   * converters, because elements() does not necessarily preserve
   * order.
   * 
   * @param from The sequence to convert
   * @param to The list to convert to
   */
  public static void sequenceToList(InspectableSequence from, List to) {
    if (from.isEmpty())
      return;
    Position cur = from.first();
    try {
      while (true) {
	to.add(cur.element());
	cur = from.after(cur);
      }
    }
    catch(BoundaryViolationException bve) {}//end condition    
  }

  /**
   * Places the contents of a list into a sequence, preserving order.
   * Running-time is O(N) for ref implementations of Sequence,
   * including ArraySequence (amortized O(N)) and NodeSequence, and
   * for all current util implementations of List, including
   * ArrayList, LinkedList, and Vector.  Dependent upon insertLast()
   * in Sequence and toArray() in List for unknown implementations.
   * 
   * @param from The list to convert
   * @param to The sequence to convert to
   */
  public static void listToSequence(List from, Sequence to) {
    iteratorToSequence(from.iterator(),to);
  }

  /**
   * Places the contents of an array into a sequence, preserving
   * order.  Running-time is O(N) for ref implementations of Sequence,
   * including ArraySequence (amortized O(N)) and NodeSequence.
   *
   * Dependent upon insertLast() in Sequence and toArray() in List for
   * unknown implementations.
   * 
   * @param from The array to convert
   * @param to The sequence to convert to
   */
  public static void arrayToSequence(Object from[], Sequence to) {
    for (int i = 0; i < from.length; i++)
      to.insertLast(from[i]);
  }

  /**
   * Places the contents of a tree into a set.  Running-time is O(N)
   * for known implementations of Tree and Set, except for TreeSet,
   * which is O(NlogN).  Dependent upon elements() in Tree and add()
   * in Set.
   *
   * @param from The tree to convert
   * @param to The set to convert to
   * @throws InvalidContainerException if the tree has two of the same 
   * element, a violation of Set's properties
   */
  public static void treeToSet(InspectableTree from, Set to)
    throws InvalidContainerException {
    iteratorToSet(from.elements(), to);
  }

 /**
  * Places the contents of a sequence into a set.  Running-time is
  * O(N) for known implementations of Sequence and Set.  Dependent
  * upon elements() in Sequence and add() in Set.
  *
  * @param from The sequence to convert
  * @param to The set to convert to
  * @throws InvalidContainerException if the sequence has two of the same 
  * element, a violation of Set's properties
  */
  public static void sequenceToSet(InspectableSequence from, Set to)
    throws InvalidContainerException {
    iteratorToSet(from.elements(), to);
  }

  /**
   * Places the contents of a set into a sequence.  Running-time is
   * O(N) for ref implementations of Sequence, including ArraySequence
   * (amortized O(N)) and NodeSequence, and for all current util
   * implementations of Set.  Dependent upon insertLast() in Sequence
   * and iterator() in List for unknown implementations.
   * 
   * @param from The set to convert
   * @param to The sequence to convert to
   */
  public static void setToSequence(Set from, Sequence to) {
    iteratorToSequence(from.iterator(),to);
  }

  /**
   * Places the contents of a map into a dictionary.  Running-time is
   * O(N) expected for known implementations of Dictionary and Map,
   * except O(NlogN) for TreeMap.  Dependent upon insert() in
   * Dictionary, and entrySet() in Map.
   * 
   * @param from The map to convert
   * @param to The dictionary to convert to
   * @throws InvalidKeyException if the map has a key that the dictionary 
   * can't deal with properly
   */
  public static void mapToDictionary(Map from, net.sourceforge.czt.jdsl.core.api.Dictionary to)
    throws InvalidKeyException {
    Set fromset = from.entrySet();
    iteratorToDictionary(fromset.iterator(),to);
  }

  /**
   * Places the contents of a sorted map into an ordered dictionary.
   * Running-time is O(NlogN) for known implementations of Dictionary
   * and SortedMap.  Dependent upon insert() in Dictionary, and
   * entrySet() in Map.
   *
   * @param from The sorted map to convert
   * @param to The ordered dictionary to convert to
   * @throws InvalidKeyException if the map has a key that the dictionary 
   * can't deal with properly
   */
  public static void sortedmapToOrderedDictionary(SortedMap from,
						  OrderedDictionary to)
    throws InvalidKeyException {
    Set fromset = from.entrySet();
    iteratorToDictionary(fromset.iterator(),to);
  }

  /**
   * Places the contents of a dictionary into a map.  Running-time is
   * O(N) expected for known implementations of Dictionary and Map,
   * except O(NlogN) for TreeMap.  Dependent upon iterator used in
   * implementation of Dictionary, and runtime of add() in Map.
   *
   * @param from The dictionary to convert
   * @param to The map to convert to
   * @throws InvalidContainerException if the tree has two of the same 
   * element, a violation of Map's properties
   */
  public static void dictionaryToMap(InspectableDictionary from, Map to)
    throws InvalidContainerException {
    iteratorToMap(from.locators(),to);
  }

  /**
   * Places the contents of a dictionary into a sorted map.
   * Running-time is O(NlogN) for known implementations of Dictionary
   * and Map.  Dependent upon iterator used in implementation of
   * Dictionary, and runtime of add() in Map.
   *
   * @param from The dictionary to convert
   * @param to The map to convert to
   * @throws InvalidContainerException if the tree has two of the same 
   * element, a violation of Map's properties
   */
  public static void dictionaryToSortedMap(InspectableDictionary from,
					   SortedMap to)
    throws InvalidContainerException {
    dictionaryToMap(from,to);
  }

  /**
   * Places the contents of a java.util iterator into a sequence.
   * Running-time is O(N) for ref implementations of Sequence,
   * including ArraySequence (amortized O(N)) and NodeSequence.
   * Dependent upon insertLast() in Sequence for unknown
   * implementations.  Also dependent on having an O(N) iterator.
   * 
   * @param from The iterator to convert
   * @param to The sequence to convert to
   */
  public static void iteratorToSequence(Iterator from, Sequence to) {
    while (from.hasNext())
      to.insertLast(from.next());
  }
  
  /**
   * Places the contents of a java.util iterator into a dictionary.
   * Runs in O(N) expected time for HashtableDictionary, O(NlogN) for
   * RedBlackTree.  Is dependent upon insert() for other
   * implementations, and is dependent on having an O(N) iterator.
   *
   * In converting iterators to dictionaries, we try to resolve the
   * iterator's contents as Entries -- failing this, we insert
   * elements of the iterator with themselves as their keys.
   *
   * @param from The iterator to convert
   * @param to The dictionary to convert to
   * @throws InvalidKeyException if the iterator has a non-locator or entry
   * that the dictionary can't treat as a key, or if the iterator has a 
   * locator or entry which the dictionary can't deal with
   */
  public static void iteratorToDictionary(Iterator from,
					  net.sourceforge.czt.jdsl.core.api.Dictionary to)
    throws InvalidKeyException {
    while (from.hasNext()) {
      Object o = from.next();
      if (o instanceof Map.Entry)	
	to.insert(((Map.Entry)o).getKey(),((Map.Entry)o).getValue());
      else to.insert(o,o);
    }
  }

  /**
   * Places the contents of a java.util iterator into a PQ.  Runs in
   * O(NlogN) time for all known implementations of PriorityQueue.  Is
   * dependent upon insert() for other implementations, and is
   * dependent on having an O(N) iterator.
   *
   * In converting iterators to PQs, we try to resolve the iterator's
   * contents as Entries -- failing this, we insert elements of the
   * iterator with themselves as their keys.
   *
   * @param from The iterator to convert
   * @param to The PQ to convert to
   * @throws InvalidKeyException if the iterator has a non-locator or entry
   * that the PQ can't treat as a key, or if the iterator has a 
   * locator or entry which the PQ can't deal with
   */
  public static void iteratorToPriorityQueue(Iterator from, 
					     net.sourceforge.czt.jdsl.core.api.PriorityQueue to)
    throws InvalidKeyException { 
    while (from.hasNext()) {
      Object o = from.next();
      if (o instanceof Map.Entry)	
	to.insert(((Map.Entry)o).getKey(),((Map.Entry)o).getValue());
      else to.insert(o,o);
    }
  }

  /**
   * Places the contents of a JDSL iterator into a List, preserving
   * order.  Runs in O(N) time for all known implementations of List.
   * Is dependent upon add() for other implementations, and is
   * dependent on having an O(N) iterator.
   *
   * @param from The iterator to convert
   * @param to The list to convert to
   */
  public static void iteratorToList(ObjectIterator from, List to) {
    while (from.hasNext()) {
      to.add(from.nextObject());
    }
  }

  /**
   * Places the contents of a JDSL iterator into a Set.  Runs in O(N)
   * expected time for HashSet, O(NlogN) for TreeSet.  Is dependent
   * upon add() for other implementations, and is dependent on having
   * an O(N) iterator.
   *
   * @param from The iterator to convert
   * @param to The set to convert to
   * @throws InvalidContainerException if the tree has two of the same 
   * element, a violation of Set's properties
   */
  public static void iteratorToSet(ObjectIterator from, Set to)
    throws InvalidContainerException {
    while (from.hasNext()) {
      if (!to.add(from.nextObject()))
	throw new InvalidContainerException("Sets cannot contain 2 of one type of element");
    }
  }

  /**
   * Places the contents of a JDSL iterator into a Map.  Runs in O(N)
   * expected time for HashMap, O(NlogN) for TreeMap.  Is dependent
   * upon put() for other implementations, and is dependent on having
   * an O(N) iterator.
   *
   * In converting iterators to maps, we try to resolve the iterator's
   * contents as Locators or KeyEntries -- failing this, we insert
   * elements of the iterator with themselves as their keys.
   *
   * @param from The iterator to convert
   * @param to The map to convert to
   * @throws InvalidKeyException if the iterator has a non-locator or
   * entry that the map can't treat as a key, or if the iterator has a
   * locator or entry which the map can't deal with
   */
  public static void iteratorToMap(ObjectIterator from, Map to)
    throws IllegalArgumentException,InvalidContainerException {
    while (from.hasNext()) {
      Object o = from.nextObject();
      if (o instanceof Locator) {
	if (to.containsKey(((Locator)o).key()))
	  throw new InvalidContainerException("Sets cannot contain 2 of one type of element");
	to.put(((Locator)o).key(),((Locator)o).element());
      }
      else to.put(o,o); 
    }
  }


}
