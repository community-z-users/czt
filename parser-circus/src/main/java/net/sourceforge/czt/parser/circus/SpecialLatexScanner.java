/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package net.sourceforge.czt.parser.circus;

import java.util.EnumSet;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Properties;
import java.util.Set;
import java.util.TreeMap;
import net.sourceforge.czt.parser.util.DebugUtils;
import net.sourceforge.czt.session.FileSource;
import net.sourceforge.czt.session.Markup;
import net.sourceforge.czt.session.SectionInfo;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.session.Source;

/**
 *
 * @author leo
 */
public class SpecialLatexScanner {
 
  private static Set< String > collectCircusSymbolNames()
  {
    Set< String > result = new HashSet();
    EnumSet CIRCUS_TOKENS = EnumSet.allOf(CircusToken.class);
    EnumSet CIRCUS_KEYWORDS = EnumSet.allOf(CircusKeyword.class);
    CIRCUS_KEYWORDS.remove(CircusKeyword.PREFIXTHEN);
    CIRCUS_KEYWORDS.remove(CircusKeyword.PREFIXCOLON);            
    
    Iterator< CircusToken > it = CIRCUS_TOKENS.iterator();
    while (it.hasNext())
    {
      boolean ok = result.add(it.next().getName());
      assert ok : "invalid CircusToken at smart scanning";
    }
    Iterator< CircusKeyword > it2 = CIRCUS_KEYWORDS.iterator();
    while (it2.hasNext())
    {
      boolean ok = result.add(it2.next().getName());
      assert ok : "invalid CircusKeyword at smart scanning";
    }
    
    assert result.size() == CIRCUS_TOKENS.size() + CIRCUS_KEYWORDS.size();
    
    return result;
  }
  
  private static <K, V> Map<V, K> flipMap(Map<K, V> m)
  {
    Map<V, K> result = new HashMap<V, K>();
    Iterator<Map.Entry<K, V>> it = m.entrySet().iterator();
    while (it.hasNext())
    {
      Map.Entry<K, V> entry = it.next();      
      result.put(entry.getValue(), entry.getKey());
    }    
    //assert 
    //  ((m.keySet().containsAll(result.values()) && m.keySet().size() == result.values().size()) &&
    //  (result.keySet().containsAll(m.values()) && result.keySet().size() == m.values().size())) : "map flipped ok";
    return result;
  }
  
  public static void main(String[] args) 
  {
    try {
      Map<String, Object> map= DebugUtils.getFieldMap2(Sym.class);
      
      System.out.println(map);
      map.keySet().retainAll(collectCircusSymbolNames());      
      System.out.println("\n\n");
      System.out.println(map);
      System.out.println("\n\n");
      Map<Object, String> flip = flipMap(map);
      System.out.println(flip);
      System.out.println("\n\n");
      System.out.println("keys equal? " +
          (map.keySet().containsAll(flip.values()) && 
          map.keySet().size() == flip.values().size()));
      System.out.println("vals equal? " +
          (flip.keySet().containsAll(map.values()) && 
          flip.keySet().size() == map.values().size()));
      
      
            
            
      //Object o = DebugUtils.getFieldMap(Sym.class).get(new Integer(Sym.DECORWORD));      
      //System.out.println("SmartScanner.get_sym() = " + o.getClass() + " " + o);
      
      SectionInfo sectInfo_ = new SectionManager("circus");
      Source source = new FileSource(args[0]);
      source.setMarkup(Markup.LATEX);      
      LatexScanner scanner = new LatexScanner(source, sectInfo_, new Properties());      
      DebugUtils.scan(scanner, Sym.class);
    }
    catch (Exception e) {
      e.printStackTrace();
    }
  }
}
