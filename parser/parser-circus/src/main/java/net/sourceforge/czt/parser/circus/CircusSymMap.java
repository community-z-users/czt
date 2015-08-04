/*
  Copyright (C) 2008 Leo Freitas
  This file is part of the czt project.

  The czt project contains free software; you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation); either version 2 of the License, or
  (at your option) any later version.

  The czt project is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY); without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with czt); if not, write to the Free Software
  Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
*/

package net.sourceforge.czt.parser.circus;

import java.lang.reflect.Field;
import java.lang.reflect.Modifier;
import java.util.Collections;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;
import net.sourceforge.czt.util.CztException;

public class CircusSymMap
{
  private CircusSymMap()
  {
  }
  
  private static Map<String,Integer> MAP = createMap(Sym.class);
  public final static Set<String> CIRCUS_SYMBOL_NAMES_ONLY = getCircusSymbolNamesOnly();
  
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
      throw new CztException("Cannot initialise Circus parser symbol map", e);
    }
  }

  

  public static Map<String,Integer> getMap()
  {
    return MAP;
  }
  
  /** Flips a given map, provided that is possible - see assertion */ 
//  private static <K, V> Map<V, K> flipMap(Map<K, V> m)
//  {
//    Map<V, K> result = new HashMap<V, K>();
//    Iterator<Map.Entry<K, V>> it = m.entrySet().iterator();
//    while (it.hasNext())
//    {
//      Map.Entry<K, V> entry = it.next();      
//      result.put(entry.getValue(), entry.getKey());
//    }    
//    assert 
//      ((m.keySet().containsAll(result.values()) && m.keySet().size() == result.values().size()) &&
//      (result.keySet().containsAll(m.values()) && result.keySet().size() == m.values().size())) : "map flipped ok";
//    it = null;
//    return result;
//  }
  
  /** 
   * Collects all symbol names that are specific to Circus. That is,
   * remove from the Circus symbol table all Z symbols. 
   *
   * Because of the order they appear in the Parser.xml, some symbol numbers 
   * are actually different in Z and Circus! Ex: 73 in Z is TEXT, and in 
   * Circus CIRCREFINES; whereas in Circus TEXT is 130.
   *
   * One way to simplify this would be to impose an order for the symbols in 
   * Parser.xml. However, this compromises precedences for CUP (I think) - so 
   * we use this solution here.
   *
   * NOTE: When doing the Circus Pattern parser, perhaps we need to consider
   *       removing the Circus Pattern symbols as well.
   *   
   */
  private static Set<String> getCircusSymbolNamesOnly()
  {
    // get both symbol tables for Circus and Z
    Set<String> result = new TreeSet<String>(getMap().keySet());    
    Map<String,Integer> zSymbols = new TreeMap<String,Integer>(net.sourceforge.czt.parser.z.SymMap.getMap());    
    
    // disconsider ANDALSO and ZCOMP from Z
    zSymbols.values().remove(Sym.ANDALSO);
    zSymbols.values().remove(Sym.ZCOMP);
        
    // remove all Z elements, but those reused for REPSEQ (ZCOMP) and CIRCGUARD (ANDASLO) :-(
    result.removeAll(zSymbols.keySet());
    
    // remove any other extension element here - if needed 
    // result.removeAll(net.sourceforge.czt.parser.z.SymMap.getMap().keySet());
    
    // return the symbol names.
    return Collections.unmodifiableSet(result);
  }
}
