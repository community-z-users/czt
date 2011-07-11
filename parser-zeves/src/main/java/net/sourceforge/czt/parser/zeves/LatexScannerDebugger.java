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

import java.io.IOException;
import java.util.EnumSet;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Properties;
import java.util.Set;
import java.util.logging.Level;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.util.UnmarshalException;
import net.sourceforge.czt.parser.util.DebugUtils;
import net.sourceforge.czt.parser.util.ParseException;
import net.sourceforge.czt.print.zeves.Unicode2Latex;
import net.sourceforge.czt.session.FileSource;
import net.sourceforge.czt.session.Markup;
import net.sourceforge.czt.session.SectionInfo;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.session.Source;
import net.sourceforge.czt.util.CztLogger;
import net.sourceforge.czt.util.SimpleFormatter;
import net.sourceforge.czt.z.util.ZUtils;
import net.sourceforge.czt.zeves.util.PrintVisitor;

/**
 *
 * @author Leo Freitas
 * @date Jun 22, 2011
 */
public class LatexScannerDebugger {
 private static Set< String > collectZEvesProofSymbolNames()
  {
    Set< String > result = new HashSet<String>();
    EnumSet<ZEvesProofToken> ZEVESPROOF_TOKENS = EnumSet.allOf(ZEvesProofToken.class);
    EnumSet<ZEvesProofKeyword> ZEVESPROOF_KEYWORDS = EnumSet.allOf(ZEvesProofKeyword.class);
    
    Iterator< ZEvesProofToken > it = ZEVESPROOF_TOKENS.iterator();
    while (it.hasNext())
    {
      boolean ok = result.add(it.next().getName());
      assert ok : "invalid ZEvesProofToken at smart scanning";
    }
    Iterator< ZEvesProofKeyword > it2 = ZEVESPROOF_KEYWORDS.iterator();
    while (it2.hasNext())
    {
      boolean ok = result.add(it2.next().getName());
      assert ok : "invalid ZEvesProofKeyword at smart scanning";
    }

    assert result.size() == ZEVESPROOF_TOKENS.size() + ZEVESPROOF_KEYWORDS.size();

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

  public static void debugScanner(Source source) throws IOException, Exception
  {
     SectionInfo sectInfo_ = new SectionManager("zeves");
     LatexScanner scanner = new LatexScanner(source, sectInfo_, new Properties());
     DebugUtils.scan(scanner, Sym.class);
  }


  private static void debugParser(Source source) throws ParseException, IOException, UnmarshalException
  {
      SectionInfo sectInfo_ = new SectionManager("zeves");
      Term term = ParseUtils.parse(source, sectInfo_);
      PrintVisitor printer = new PrintVisitor(false);
      printer.setPrintIds(false);
      printer.setOffset(1, 1);
      ZUtils.setToStringVisitor(term, printer);
      //((TermImpl)term).getFactory().setToStringVisitor(printer);
      System.out.println(term.toString());
  }

  public static void main(String[] args)
  {
    try {
     

      //Object o = DebugUtils.getFieldMap(Sym.class).get(new Integer(Sym.DECORWORD));
      //System.out.println("SmartScanner.get_sym() = " + o.getClass() + " " + o);

//      System.out.println("ZEvesProof Symbol Table \n\t" + new TreeMap(DebugUtils.getFieldMap(Sym.class)));
//      System.out.println("Z      Symbol Table \n\t" + new TreeMap(DebugUtils.getFieldMap(net.sourceforge.czt.parser.z.Sym.class)));
//      System.out.println("\n\n");
//      Map<String, Object>  circusMap = DebugUtils.getFieldMap2(Sym.class);
//      Map<String, Object>  zMap = DebugUtils.getFieldMap2(net.sourceforge.czt.parser.z.Sym.class);
//      circusMap.keySet().removeAll(zMap.keySet());
//      System.out.println("ZEvesProof only Symbol Table \n\t" + new TreeMap(flipMap(circusMap)));

      Source source = new FileSource(args[0]); // args[0] = -in
      source.setMarkup(Markup.LATEX);
      SimpleFormatter formatter = new SimpleFormatter(false, true, false, false);
      CztLogger.setConsoleHandler(CztLogger.getLogger(LatexMarkupParser.class), Level.ALL, Level.OFF, formatter);
      if (args.length == 1 || args[1].equals("-s"))
      {
        CztLogger.setConsoleHandler(CztLogger.getLogger(KeywordScanner.class), Level.ALL, Level.OFF, formatter);
        CztLogger.setConsoleHandler(CztLogger.getLogger(SmartScanner.class), Level.ALL, Level.OFF, formatter);
        CztLogger.setConsoleHandler(CztLogger.getLogger(Unicode2Latex.class), Level.ALL, Level.OFF, formatter);
        debugScanner(source);
      }
      if (args.length == 1 || args[1].equals("-p"))
      {
        CztLogger.setConsoleHandler(CztLogger.getLogger(Parser.class), Level.ALL, Level.OFF, formatter);
        debugParser(source);
      }
    }
    catch (Exception e) {
      e.printStackTrace();
    }
  }
}

