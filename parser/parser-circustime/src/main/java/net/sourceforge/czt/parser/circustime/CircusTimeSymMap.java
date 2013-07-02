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

package net.sourceforge.czt.parser.circustime;

import java.lang.reflect.Field;
import java.lang.reflect.Modifier;
import java.util.Collections;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;

import net.sourceforge.czt.parser.circustime.Sym;
import net.sourceforge.czt.util.CztException;

public class CircusTimeSymMap
{
  private CircusTimeSymMap()
  {
  }
  
  private static Map<String,Integer> MAP = createMap(Sym.class);
  public static Set<String> CIRCUSTIME_SYMBOL_NAMES_ONLY = getCircusTimeSymbolNamesOnly();
  
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
      throw new CztException("Cannot initialise CircusTime parser symbol map", e);
    }
  }

  

  public static Map<String,Integer> getMap()
  {
    return MAP;
  }
  
  private static Set<String> getCircusTimeSymbolNamesOnly()
  {
    // get both symbol tables for Circus Time, Circus and Z
    Set<String> result = new TreeSet<String>(getMap().keySet());    
    Map<String,Integer> zSymbols = new TreeMap<String,Integer>(net.sourceforge.czt.parser.z.SymMap.getMap());    
    Map<String,Integer> circusSymbols = new TreeMap<String,Integer>(net.sourceforge.czt.parser.circus.SymMap.getMap());    
    
    // ignore shared Z symbols (i.e. Circus get priority) ANDALSO and ZCOMP from Z
    zSymbols.values().remove(Sym.ANDALSO);
    zSymbols.values().remove(Sym.ZCOMP);
        
    // remove all Z elements, but those reused for REPSEQ (ZCOMP) and CIRCGUARD (ANDASLO) :-(
    result.removeAll(zSymbols.keySet());
    
    result.removeAll(circusSymbols.keySet());
    
    // return the symbol names.
    return Collections.unmodifiableSet(result);

  // get all symbol tables for Circustime, Circus and Z
//    Set<String> result = new TreeSet<String>(getMap().keySet());    
//    Map<String,Integer> circustimeSymbols = new TreeMap<String,Integer>(net.sourceforge.czt.parser.circustime.SymMap.getMap());
//    // remove Circustime elements
//    circustimeSymbols.values().remove(Sym.CIRCSTARTBY);
//    circustimeSymbols.values().remove(Sym.CIRCENDBY);
//    circustimeSymbols.values().remove(Sym.CIRCTIMEDINTERRUPT);
//    circustimeSymbols.values().remove(Sym.CIRCTIMEOUT);
//    circustimeSymbols.values().remove(Sym.CIRCWAIT);
//    circustimeSymbols.values().remove(Sym.LCIRCTIME);
//    circustimeSymbols.values().remove(Sym.RCIRCTIME);    
//    result.removeAll(circustimeSymbols.keySet());    
//
//    // return the symbol names.
//    return Collections.unmodifiableSet(result);
  }
}

