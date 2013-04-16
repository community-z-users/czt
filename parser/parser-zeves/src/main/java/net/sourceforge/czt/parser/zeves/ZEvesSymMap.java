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

package net.sourceforge.czt.parser.zeves;

import java.lang.reflect.Field;
import java.lang.reflect.Modifier;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;
import net.sourceforge.czt.util.CztException;

/**
 *
 * @author Leo Freitas
 * @date Jun 30, 2011
 */
public class ZEvesSymMap {

  private ZEvesSymMap()
  {
  }

  private static Map<String,Integer> MAP = createMap(Sym.class);
  // it includes "apply", "prove", etc... but not "by" or "to" or "expression", say.
  public static Set<String> HEAD_PROOF_WORDS_ONLY = getZEvesHeadProofWordsOnly();

  public static Set<String> ALL_ZEVES_KEYWORDS = getAllZEvesKeywords();
  public static Set<String> ALL_ZEVES_USAGE_WORDS = getAllZEvesUsageWords();

  public static Map<String,Integer> createMap(Class<?> symClass)
  {
    try {
      Map<String,Integer> result = new HashMap<String,Integer>();
      Field[] fields = symClass.getFields();
      for (int i = 0; i < fields.length; i++) {
        Field field = fields[i];
        if (Modifier.isStatic(field.getModifiers())) {
          result.put(field.getName(), (Integer) field.get(null));
        }
      }
      return Collections.unmodifiableMap(result);
    }
    catch (IllegalAccessException e) {
      throw new CztException("Cannot initialise ZEves parser symbol map", e);
    }
  }



  public static Map<String,Integer> getMap()
  {
    return MAP;
  }

  /** Flips a given map, provided that is possible - see assertion */
  public static <K, V> Map<V, K> flipMap(Map<K, V> m)
  {
    Map<V, K> result = new HashMap<V, K>();
    Iterator<Map.Entry<K, V>> it = m.entrySet().iterator();
    while (it.hasNext())
    {
      Map.Entry<K, V> entry = it.next();
      result.put(entry.getValue(), entry.getKey());
    }
    assert
      ((m.keySet().containsAll(result.values()) && m.keySet().size() == result.values().size()) &&
      (result.keySet().containsAll(m.values()) && result.keySet().size() == m.values().size())) : "map flipped ok";
    return result;
  }

  /**
   * Collects all symbol names of interest. That is,
   * remove from the symbol table all Z symbols, as well as
   * all non head proof words.
   *
   * Because of the order they appear in the Parser.xml, some symbol numbers
   * are actually different in Z and ZEves!
   *
   * One way to simplify this would be to impose an order for the symbols in
   * Parser.xml. However, this compromises precedences for CUP (I think) - so
   * we use this solution here.
   *
   */
  private static Set<String> getZEvesHeadProofWordsOnly()
  {
    // get both symbol tables for ZEves and Z
    Set<String> result = new TreeSet<String>(getMap().keySet());
    Map<String,Integer> zSymbols = new TreeMap<String,Integer>(net.sourceforge.czt.parser.z.SymMap.getMap());

    // remove all Z elements
    result.removeAll(zSymbols.keySet());

    // collect other proof words that are not head
    ArrayList<ZEvesProofKeyword> zevesProofKeywords = 
            new ArrayList<ZEvesProofKeyword>(Arrays.asList(ZEvesProofKeyword.values()));
    zevesProofKeywords.removeAll(Arrays.asList(ZEvesProofKeyword.headProofWordsOnly()));

    for (ZEvesProofKeyword w : zevesProofKeywords)
    {
      // remove all non-head zeves proof keywords
      result.remove(w.getName());
    }

    // return the symbol names.
    return Collections.unmodifiableSet(result);
  }

  private static Set<String> getAllZEvesKeywords()
  {
    Set<String> result = new TreeSet<String>();

    for(ZEvesProofKeyword w : ZEvesProofKeyword.values())
    {
      result.add(w.getName());
    }
    
    // return the symbol names.
    return Collections.unmodifiableSet(result);
  }

  private static Set<String> getAllZEvesUsageWords()
  {
    Set<String> result = new TreeSet<String>();

    result.add(ZEvesProofKeyword.THMRULE.getName());
    result.add(ZEvesProofKeyword.THMFRULE.getName());
    result.add(ZEvesProofKeyword.THMGRULE.getName());
    result.add(ZEvesProofKeyword.THMAXIOM.getName());

    return Collections.unmodifiableSet(result);
  }
}
