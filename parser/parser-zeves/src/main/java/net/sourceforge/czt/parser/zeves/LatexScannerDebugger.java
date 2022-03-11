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
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.io.UnsupportedEncodingException;
import java.io.Writer;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.EnumSet;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.logging.Level;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.util.UnmarshalException;
import net.sourceforge.czt.parser.util.CztError;
import net.sourceforge.czt.parser.util.DebugUtils;
import net.sourceforge.czt.parser.util.ParseException;
import net.sourceforge.czt.print.util.CztPrintString;
import net.sourceforge.czt.print.util.LatexString;
import net.sourceforge.czt.print.util.PrintPropertiesKeys;
import net.sourceforge.czt.print.util.UnicodeString;
import net.sourceforge.czt.print.util.XmlString;
import net.sourceforge.czt.print.zeves.Unicode2Latex;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.FileSource;
import net.sourceforge.czt.session.Dialect;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.Markup;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.session.Source;
import net.sourceforge.czt.session.SourceLocator;
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
 public static Set< String > collectZEvesProofSymbolNames()
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

  public static <K, V> Map<V, K> flipMap(Map<K, V> m)
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

  public static void debugScanner(Writer writer, Source source) throws IOException, Exception
  {
    SectionManager sectInfo_ = new SectionManager(Dialect.ZEVES);
    //sectInfo_.setProperty("czt.debug.LatexToUnicode", "true");
    //sectInfo_.setProperty("czt.debug.ContextFreeScanner", "true");
    //sectInfo_.setProperty("czt.debug.UnicodeScanner", "false");
    //sectInfo_.setProperty("czt.debug.*", "true");
    //sectInfo_.setTracing(true, Level.ALL);
    
    // if available, resolve the czt.path from the source
    // it allows us to find parent sections if needed
    if (source instanceof FileSource) {
      String sourceDir = new File(source.getName()).getParent();
      if (sourceDir != null) {
        sectInfo_.setProperty(SourceLocator.PROP_CZT_PATH, sourceDir);
      }
    }

    java_cup.runtime.Scanner scanner;
     if (source.getMarkup().equals(Markup.UNICODE))
       scanner = new UnicodeScanner(source, sectInfo_.getProperties());
     else // assume LaTex
       scanner = new LatexScanner(source, sectInfo_, sectInfo_.getProperties());
    DebugUtils.scan(scanner, Sym.class, writer);
  }

  private static Writer createWriter(Source source, Markup markup, boolean isDebugging) throws UnsupportedEncodingException, FileNotFoundException
  {
    final String fileName = source.getName() + Markup.getDefaultFileExtention(markup);
    File file = new File(fileName);
    if (file.exists()) file.delete();
    BufferedWriter result = new BufferedWriter(new OutputStreamWriter(new FileOutputStream(file),"UTF-8"));
    if (isDebugging) System.out.println("  created file " + fileName);
    return result;
  }

  protected static void debugPrinter(Source source, SectionManager sectInfo, Term term, boolean isDebugging) throws IOException, CommandException
  {
    sectInfo.setProperty("czt.debug.ZmlScanner", "false");
    //sectInfo.setProperty(PrintPropertiesKeys.PROP_TXT_WIDTH, Integer.toString(2));
    String sourceKeyName = SourceLocator.getSourceName(source.getName());
    while (sourceKeyName.lastIndexOf(".") != -1)
        sourceKeyName = sourceKeyName.substring(0, sourceKeyName.lastIndexOf("."));
    if (term != null)
    {
      if (isDebugging)
      {
        System.out.println("\n=================================================================");
        System.out.println("Direct " + source.getMarkup() + " printing of " + source.getName());
      }
      PrintVisitor printer = new PrintVisitor(false);
      printer.setPrintIds(false);
      printer.setOffset(1, 1);

      if (isDebugging)
      {
        System.out.println("\n============================ TOSTRING ============================");
      }
      ZUtils.setToStringVisitor(term, printer);
      final String s = term.toString();

      if (isDebugging)
      {
        System.out.println("SM " + source.getMarkup() + " printing of " + source.getName() + " = " + s);
      }

      List<Markup> markups = new ArrayList<Markup>(Arrays.asList(Markup.values()));
      markups.remove(Markup.getMarkup(source.getName()));
      CztPrintString ps;
      for(Markup m : markups)
      {
        ps = null;
        switch (m)
        {
          case LATEX:
            if (isDebugging) System.out.println("\n============================ LATEX    ============================");
            ps = sectInfo.get(new Key<LatexString>(sourceKeyName, LatexString.class));
            break;
          case UNICODE:
            if (isDebugging) System.out.println("\n============================ UNICODE  ============================");
            ps = sectInfo.get(new Key<UnicodeString>(sourceKeyName, UnicodeString.class));
            break;
          case  ZML:
            if (isDebugging) System.out.println("\n============================ XML      ============================");
            ps = sectInfo.get(new Key<XmlString>(sourceKeyName, XmlString.class));
            break;
          default:
            throw new Error();
        }
        assert ps != null;
        Writer w = createWriter(source, m, isDebugging);
        w.write(ps.toString());
        w.close();
      }
      if (isDebugging) System.out.println("==================================================================");
    }
    else
    {
      throw new RuntimeException("Cannot print null term!");
    }
  }


  protected static void debugParser(Source source, boolean print,
          Integer width, boolean formatGoal, boolean isDebugging) throws CommandException, ParseException, IOException, UnmarshalException
  {
      SectionManager sectInfo_ = new SectionManager(Dialect.ZEVES);
      //sectInfo_.setTracing(true, Level.ALL);
      sectInfo_.setProperty(PrintPropertiesKeys.PROP_TXT_WIDTH, width.toString());
      sectInfo_.setProperty(PrintPropertiesKeys.PROP_PRINTING_STRUCTURED_GOAL,
              String.valueOf(formatGoal));
      File file = new File(source.getName());
      // for the case of .tex.zed8 remove all possible .s
      String sourceName = SourceLocator.getSourceName(file.getName());
      while (sourceName.lastIndexOf(".") != -1)
        sourceName = sourceName.substring(0, sourceName.lastIndexOf("."));
      SourceLocator.addCZTPathFor(file, sectInfo_);
      sectInfo_.put(new Key<Source>(sourceName, Source.class), source);
      Term term;
      try
      {
        // don't use Spec, because for XML, a singleton spec returns ZSect rather than Spec (!)
        term = sectInfo_.get(new Key<Term>(sourceName, Term.class));
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
        debugPrinter(source, sectInfo_, term, isDebugging);
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

      if (args.length == 0)
        throw new IllegalArgumentException("No file name given");

      String fileName = args[0];

      File f = new File(fileName);
      if (!f.exists())
        throw new IllegalArgumentException("File does not exist - " + fileName);
      boolean scan = args.length == 1;
      boolean parse = scan;
      boolean print = scan;
      boolean formatG = false;
      int width = 0;
      for(String arg : args)
      {
        if (arg.equals("-s"))
          scan = true;
        else if (arg.equals("-p"))
          parse = true;
        else if (arg.equals("-t"))
          print = true;
        else if (arg.startsWith("-w"))
          width = Integer.valueOf(arg.substring(2));
        else if (arg.equals("-f"))
          formatG = true;
      }

      Source source = new FileSource(fileName); // args[0] = -in
      System.out.println("Working with " + Markup.getMarkup(fileName) + " for " + fileName);
      source.setMarkup(Markup.getMarkup(fileName));
      SimpleFormatter formatter = new SimpleFormatter(false, true, false, false);
      //CztLogger.setConsoleHandler(CztLogger.getLogger(LatexMarkupParser.class), Level.ALL, Level.ALL, formatter);
      if (scan)
      {
        //CztLogger.setConsoleHandler(CztLogger.getLogger(KeywordScanner.class), Level.ALL, Level.OFF, formatter);
        //CztLogger.setConsoleHandler(CztLogger.getLogger(ContextFreeScanner.class), Level.ALL, Level.OFF, formatter);
        //CztLogger.setConsoleHandler(CztLogger.getLogger(SmartScanner.class), Level.ALL, Level.ALL, formatter);
        CztLogger.setConsoleHandler(CztLogger.getLogger(Unicode2Latex.class), Level.ALL, Level.ALL, formatter);
        CztLogger.setConsoleHandler(CztLogger.getLogger(Latex2Unicode.class), Level.ALL, Level.ALL, formatter);
        debugScanner(new OutputStreamWriter(System.out, "UTF-8"), source);
      }
      if (parse)
      {
        //CztLogger.setConsoleHandler(CztLogger.getLogger(Parser.class), Level.ALL, Level.OFF, formatter);
        //CztLogger.setConsoleHandler(CztLogger.getLogger(net.sourceforge.czt.zeves.jaxb.AstToJaxb.class), Level.ALL, Level.ALL, formatter);
        debugParser(source, print, width, formatG, false);
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

