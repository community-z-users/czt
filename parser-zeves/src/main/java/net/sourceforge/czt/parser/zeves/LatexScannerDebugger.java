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

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileOutputStream;
import java.io.FileWriter;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.io.StringWriter;
import java.util.EnumSet;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;
import java.util.logging.Level;
import net.sourceforge.czt.base.util.UnmarshalException;
import net.sourceforge.czt.parser.util.CztError;
import net.sourceforge.czt.parser.util.DebugUtils;
import net.sourceforge.czt.parser.util.ParseException;
import net.sourceforge.czt.print.util.LatexString;
import net.sourceforge.czt.print.util.UnicodeString;
import net.sourceforge.czt.print.zeves.PrintUtils;
import net.sourceforge.czt.print.zeves.Unicode2Latex;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.FileSource;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.Markup;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.session.Source;
import net.sourceforge.czt.session.SourceLocator;
import net.sourceforge.czt.util.CztLogger;
import net.sourceforge.czt.util.SimpleFormatter;
import net.sourceforge.czt.z.ast.Spec;
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
     SectionManager sectInfo_ = new SectionManager("zeves");
     sectInfo_.setProperty("czt.debug.LatexToUnicode", "false");
     sectInfo_.setProperty("czt.debug.ContextFreeScanner", "false");
     sectInfo_.setProperty("czt.debug.UnicodeScanner", "false");
    net.sourceforge.czt.java_cup.runtime.Scanner scanner;
     if (source.getMarkup().equals(Markup.UNICODE))
       scanner = new UnicodeScanner(source, sectInfo_.getProperties());
     else // assume LaTex
       scanner = new LatexScanner(source, sectInfo_, sectInfo_.getProperties());
     DebugUtils.scan(scanner, Sym.class);
  }

  private static void debugPrinter(Source source, SectionManager sectInfo, Spec term) throws IOException, CommandException
  {
    sectInfo.setProperty("czt.debug.ZmlScanner", "false");
    String sourceKeyName = SourceLocator.getSourceName(source.getName());
    if (term != null)
    {
      System.out.println("\n=================================================================");
      System.out.println("Direct " + source.getMarkup() + " printing of " + source.getName());
      PrintVisitor printer = new PrintVisitor(false);
      printer.setPrintIds(false);
      printer.setOffset(1, 1);

      System.out.println("\n============================ TOSTRING ============================");
      ZUtils.setToStringVisitor(term, printer);
      System.out.println(term.toString());

      System.out.println("\n============================ PRTUTILS-LATEX ============================");
      StringWriter sw = new StringWriter();
      PrintUtils.print(term, sw, sectInfo, sourceKeyName, Markup.LATEX);
      sw.flush();
      System.out.println(sw.toString());
      System.out.println();

      System.out.println("\n============================ PRTUTILS-UNICODE ============================");
      File file = new File(source.getName() + "PTRUTLS.zed8");
      if (file.exists())
        file.delete();
      BufferedWriter fw = new BufferedWriter(new OutputStreamWriter(new FileOutputStream(file),"UTF8"));
      //Doesn't do Unicode properly:
      //  FileWriter fw = new FileWriter(file);
      PrintUtils.print(term, fw, sectInfo, sourceKeyName, Markup.UNICODE);
      fw.close();
      System.out.println("Created file " + source.getName() + "PTRUTLS.zed8");
      System.out.println();
    }

    System.out.println("\n==================================================================");
    System.out.println("SM Printing of " + source.getName());

    System.out.println("\n============================ LATEX    ============================");
    LatexString ls = sectInfo.get(new Key<LatexString>(sourceKeyName, LatexString.class));
    System.out.println(ls.toString());

    System.out.println("\n============================ UNICODE  ============================");
    UnicodeString us = sectInfo.get(new Key<UnicodeString>(sourceKeyName, UnicodeString.class));
    System.out.println(us.toString());
    File file = new File(source.getName() + ".zed8");
    if (file.exists())
      file.delete();
    BufferedWriter fw = new BufferedWriter(new OutputStreamWriter(new FileOutputStream(file),"UTF8"));
    fw.write(us.toString());
    fw.close();
    System.out.println("Created file " + source.getName() + ".zed8");

    System.out.println("\n============================ XML      ============================");
    //XmlString xs = sectInfo.get(new Key<XmlString>(sourceKeyName, XmlString.class));
    //System.out.println(xs.toString());
    
    System.out.println("==================================================================");
  }


  private static void debugParser(Source source, boolean print) throws CommandException, ParseException, IOException, UnmarshalException
  {
      SectionManager sectInfo_ = new SectionManager("zeves");

      File file = new File(source.getName());
      String sourceName = SourceLocator.getSourceName(file.getName());
      SourceLocator.addCZTPathFor(file, sectInfo_);
      sectInfo_.put(new Key<Source>(sourceName, Source.class), source);
      Spec term;
      try
      {
        term = sectInfo_.get(new Key<Spec>(sourceName, Spec.class));
      }
      catch(CommandException ex)
      {
        term = null;
        System.out.println("Parsing errors!");
      }

//      Term term = ParseUtils.parse(source, sectInfo_);

      // check for parse exceptions
      ParseException parseException = sectInfo_.get(new Key<ParseException>(source.getName(), ParseException.class));
      if (parseException != null && !parseException.getErrors().isEmpty()) {
        System.out.println("Found parser errors (" + parseException.getErrors().size() + ")");
        for(CztError e : parseException.getErrors())
        {
          System.out.println(e.toString());
        }
      }

      if (print)
        debugPrinter(source, sectInfo_, term);
  }

  @SuppressWarnings("CallToThreadDumpStack")
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

      if (args.length == 0)
        throw new IllegalArgumentException("No file name given");

      String fileName = args[0];
      boolean scan = args.length == 1;
      boolean parse = scan;
      boolean print = scan;
      for(String arg : args)
      {
        if (arg.equals("-s"))
          scan = true;
        else if (arg.equals("-p"))
          parse = true;
        else if (arg.equals("-t"))
          print = true;
      }

      Source source = new FileSource(fileName); // args[0] = -in
      System.out.println("Working with " + Markup.getMarkup(fileName) + " for " + fileName);
      source.setMarkup(Markup.getMarkup(fileName));
      SimpleFormatter formatter = new SimpleFormatter(false, true, false, false);
      CztLogger.setConsoleHandler(CztLogger.getLogger(LatexMarkupParser.class), Level.ALL, Level.ALL, formatter);
      if (scan)
      {
        CztLogger.setConsoleHandler(CztLogger.getLogger(KeywordScanner.class), Level.ALL, Level.OFF, formatter);
        CztLogger.setConsoleHandler(CztLogger.getLogger(ContextFreeScanner.class), Level.ALL, Level.OFF, formatter);
        CztLogger.setConsoleHandler(CztLogger.getLogger(SmartScanner.class), Level.ALL, Level.ALL, formatter);
        CztLogger.setConsoleHandler(CztLogger.getLogger(Unicode2Latex.class), Level.ALL, Level.ALL, formatter);
        CztLogger.setConsoleHandler(CztLogger.getLogger(Latex2Unicode.class), Level.ALL, Level.ALL, formatter);
        debugScanner(source);
      }
      if (parse)
      {
        CztLogger.setConsoleHandler(CztLogger.getLogger(Parser.class), Level.ALL, Level.OFF, formatter);
        debugParser(source, print);
      }
    }
    catch (Exception e) {
      System.out.flush();
      e.printStackTrace();
    }
  }

  private LatexScannerDebugger()
  {
  }
}

