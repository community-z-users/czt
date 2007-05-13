/*
  Copyright (C) 2004, 2006 Petra Malik
  Copyright (C) 2004 Tim Miller
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
package net.sourceforge.czt.typecheck.z;

import java.io.*;
import java.util.Arrays;
import java.util.List;
import java.util.SortedMap;
import java.util.TreeMap;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.util.MarshalException;
import net.sourceforge.czt.base.util.XmlWriter;
import net.sourceforge.czt.session.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.ast.ZFactory;
import net.sourceforge.czt.z.impl.ZFactoryImpl;
import net.sourceforge.czt.parser.z.*;
import net.sourceforge.czt.typecheck.z.impl.Factory;

/**
 * Utilities for typechecking Z specifications.
 * This class provides a main method for command line use,
 * as well as several 'typecheck' methods that are designed
 * to be called by other Java classes.
 *
 * @author Petra Malik, Tim Miller
 */
public class TypeCheckUtils
{
  /**
   * Do not generate instances of this class.
   * You should use the static methods directly.
   */
  protected TypeCheckUtils()
  {
  }
  
  /**
   * Typecheck and type annotate a term, with no default section 
   * and not allowing names to be used before they are declared.
   * @param term the <code>Term</code> to typecheck (typically a Spec).
   * @param sectInfo the <code>SectionManager</code> object to use.
   * @return the list of ErrorAnns in the AST added by the typechecker.
   */
  public static List<? extends ErrorAnn> typecheck(Term term,
                                                   SectionManager sectInfo)
  {
    return typecheck(term, sectInfo, false);
  }


  /**
   * Typecheck and type annotate a term, with no default section.
   * @param term the <code>Term</code> to typecheck (typically a Spec).
   * @param sectInfo the <code>SectionManager</code> object to use.
   * @param useBeforeDecl allow use of variables before declaration
   * @return the list of ErrorAnns in the AST added by the typechecker.
   */
  public static List<? extends ErrorAnn> typecheck(Term term,
                                                   SectionManager sectInfo,
                                                   boolean useBeforeDecl)
  {
    return typecheck(term, sectInfo, useBeforeDecl, null);
  }

  /**
   * Typecheck and type annotate a Term, in the context of a given section.
   * @param term the <code>Term</code> to typecheck.
   * @param sectInfo the <code>SectionManager</code> object to use.
   * @param useBeforeDecl allow use of variables before declaration
   * @param sectName the section within which this term should be checked.
   * @return the list of ErrorAnns in the AST added by the typechecker.
   */
  public static List<? extends ErrorAnn> typecheck(Term term,
                                                   SectionManager sectInfo,
                                                   boolean useBeforeDecl,
                                                   String sectName)
  {
    TypeCheckUtils utils = new TypeCheckUtils();
    return utils.lTypecheck(term, sectInfo, useBeforeDecl, false, sectName);
  }

  /**
   * Typecheck and type annotate a Term, in the context of a given section.
   * @param term the <code>Term</code> to typecheck.
   * @param sectInfo the <code>SectionManager</code> object to use.
   * @param useBeforeDecl allow use of variables before declaration
   * @param useNameIds use name ids as part of the name
   * @return the list of ErrorAnns in the AST added by the typechecker.
   */
  public static List<? extends ErrorAnn> typecheck(Term term,
                                                   SectionManager sectInfo,
                                                   boolean useBeforeDecl,
                                                   boolean useNameIds)
  {
    TypeCheckUtils utils = new TypeCheckUtils();
    return utils.lTypecheck(term, sectInfo, useBeforeDecl, useNameIds, null);
  }


  /**
   * Typecheck and type annotate a Term, in the context of a given section.
   * @param term the <code>Term</code> to typecheck.
   * @param sectInfo the <code>SectionManager</code> object to use.
   * @param useBeforeDecl allow use of variables before declaration
   * @param useNameIds use name ids as part of the name
   * @param sectName the section within which this term should be checked.
   * @return the list of ErrorAnns in the AST added by the typechecker.
   */
  public static List<? extends ErrorAnn> typecheck(Term term,
                                                   SectionManager sectInfo,
                                                   boolean useBeforeDecl,
                                                   boolean useNameIds,
                                                   String sectName)
  {
    TypeCheckUtils utils = new TypeCheckUtils();
    return utils.lTypecheck(term, sectInfo, useBeforeDecl, useNameIds, sectName);
  }

  /** An internal method of the typechecker. */
  protected List<? extends ErrorAnn> lTypecheck(Term term,
                                                SectionManager sectInfo,
                                                boolean useBeforeDecl,
                                                boolean useNameIds,
                                                String sectName)
  {
    ZFactory zFactory = new ZFactoryImpl();
    TypeChecker typeChecker =
      new TypeChecker(new Factory(zFactory), sectInfo, useBeforeDecl);
    typeChecker.setPreamble(sectName, sectInfo);
    typeChecker.setUseNameIds(useNameIds);
    term.accept(typeChecker);
    return typeChecker.errors();
  }

  /** A convenience method for parsing an arbitrary input specification.
   *  Note that source.setMarkup(...) allows you to specify which markup format
   *  the specification is using: LATEX or UNICODE etc.
   *  @param  source The string or file to be parsed.
   *  @param  sectInfo The section manager or SectionManager to use during parsing.
   *  @return A non-typechecked term.
   */
  protected Term parse(Source source, SectionManager sectInfo)
    throws IOException, net.sourceforge.czt.parser.util.ParseException,
      net.sourceforge.czt.base.util.UnmarshalException
  {
    return ParseUtils.parse(source, sectInfo);
  }

  /** A convenience method for parsing a file.
   *  It uses the file name extension to guess which Z markup to parse.
   *  @param  file The path to the file to be parsed.
   *  @param  sectInfo The section manager or SectionManager to use during parsing.
   *  @return a non-typechecked term.
   */
  protected Term parse(String file, SectionManager sectInfo)
    throws IOException, net.sourceforge.czt.parser.util.ParseException,
           net.sourceforge.czt.base.util.UnmarshalException
  {
    return parse(new FileSource(file), sectInfo);
  }

  protected String name()
  {
    return "zedtypecheck";
  }

  /** Print a usage message to System.err, describing the
   *  command line arguments accepted by main.
   */
  protected void printUsage()
  {
    System.err.println("usage: " + name() + " [-sdt] filename ...");
    System.err.println("flags: -s     syntax check only");
    System.err.println("       -d     allow use before declaration");
    System.err.println("       -n     force declarations before use");
    System.err.println("       -i     use name ids");
    System.err.println("       -p     print the AST");
    System.err.println("       -t     print global type declarations");
    System.err.println("       -b     print benchmarking times");
  }

  protected boolean useBeforeDeclDefault()
  {
    return false;
  }

  protected boolean printBenchmarkTimesDefault()
  {
    return true;
  }

  /** The list of known toolkits.
   *  This is used internally to avoid printing the types of toolkit names.
   */
  protected List<String> toolkits()
  {
    List<String> toolkits = new java.util.ArrayList<String>();
    toolkits.add("prelude");
    toolkits.add("set_toolkit");
    toolkits.add("relation_toolkit");
    toolkits.add("function_toolkit");
    toolkits.add("sequence_toolkit");
    toolkits.add("number_toolkit");
    toolkits.add("standard_toolkit");
    return toolkits;
  }

  protected void printTypes(SectTypeEnvAnn sectTypeEnvAnn)
  {
    List<NameSectTypeTriple> triples = sectTypeEnvAnn.getNameSectTypeTriple();
    String prevSect = "";
    for (NameSectTypeTriple triple : triples) {
      if (!toolkits().contains(triple.getSect())) {
        if (!prevSect.equals(triple.getSect())) {
          System.out.println("section " + triple.getSect());
        }
        System.out.println("\t" + triple.getZName() +
                           " : " + triple.getType());
        prevSect = triple.getSect();
      }
    }
  }

  /** @return a fresh new section manager. */
  protected SectionManager getSectionManager()
  {
    SectionManager sectionManager = new SectionManager();
    sectionManager.putCommand(SectTypeEnvAnn.class, TypeCheckUtils.getCommand());
    return sectionManager;
  }
  
  /** @return an XML writer for Z. */
  protected XmlWriter getXmlWriter()
  {
    return new net.sourceforge.czt.z.jaxb.JaxbXmlWriter();
  }

  protected void run(String [] args)
    throws IOException, net.sourceforge.czt.base.util.UnmarshalException
  {
    if (args.length == 0) {
      printUsage();
      System.exit(0);
    }

    List<String> files = new java.util.ArrayList<String>();
    boolean syntaxOnly = false;
    boolean useBeforeDecl = useBeforeDeclDefault();
    boolean printTypes = false;
    boolean printZml = false;
    boolean printBenchmark = printBenchmarkTimesDefault();
    boolean useNameIds = false;

    for (int i = 0; i < args.length; i++) {
      if (args[i].startsWith("-")) {
        for (int j = 1; j < args[i].length(); j++) {
          switch (args[i].charAt(j)) {
          case 's':
            syntaxOnly = true;
            break;
          case 'd':
            useBeforeDecl = true;
            break;
          case 'n':
            useBeforeDecl = false;
            break;
          case 't':
            printTypes = true;
            break;
          case 'p':
            printZml = true;
            break;
          case 'b':
            printBenchmark = true;
            break;
          case 'i':
            useNameIds = true;
            break;
          default:
            printUsage();
          }
        }
      }
      else {
        files.add(args[i]);
      }
    }
    SectionManager manager = getSectionManager();
    int result = 0;
    SortedMap<String, List<Long>> timesPerFile = new TreeMap<String, List<Long>>();    
    long zeroTime = System.currentTimeMillis();     
    long currentTime = zeroTime;
    long lastTime = zeroTime;
    for (String file : files) {            
      //parse the file
      Term term = null;
      Markup markup = ParseUtils.getMarkup(file);
      try {
        if (markup == null) {
          Source src = new FileSource(file);
          term = this.parse(src, manager);
        }
        else {
          term = this.parse(file, manager);
        }
      }
      catch (net.sourceforge.czt.parser.util.ParseException exception) {
        exception.printErrorList();
      }
      /* ex:
       * 0        40           
       * |--Parse--|--TypeCheck--|--PrintType--|--PrintZml--|      
       * lt = 0
       * ct = 40
       * pt = 40 (40 - 0)
       */            
      lastTime = currentTime;
      currentTime = System.currentTimeMillis();
      long parseTime = currentTime - lastTime;
      long typeCheckTime = 0;
      long printTypeTime = 0;
      long printZmlTime  = 0; 
     
      //if the parse succeeded, typecheck the term
      if (term != null && !syntaxOnly) {
        List<? extends ErrorAnn> errors =
          this.lTypecheck(term, manager, useBeforeDecl, useNameIds, null);

        //print any errors
        for (Object next : errors) {
          System.out.println(next);
          System.out.println();
          result = -1;
        }
        
        /* ex:
         * 0        40            100
         * |--Parse--|--TypeCheck--|--PrintType--|--PrintZml--|         
         * lt = 40
         * ct = 100
         * tt = 60  (100-40)
         */
        lastTime = currentTime;
        currentTime = System.currentTimeMillis();
        typeCheckTime = currentTime - lastTime;        

        if (printTypes) {
          SectTypeEnvAnn sectTypeEnvAnn =
            (SectTypeEnvAnn) term.getAnn(SectTypeEnvAnn.class);
          if (sectTypeEnvAnn != null) {
            printTypes(sectTypeEnvAnn);
          }
          else {
            System.err.println("No type information available");
          }
          /* ex:
           * 0        40            100           120
           * |--Parse--|--TypeCheck--|--PrintType--|--PrintZml--|         
           * lt = 100
           * ct = 120
           * ptt= 20 (120-100)  
           */
          lastTime = currentTime;
          currentTime = System.currentTimeMillis();
          printTypeTime = currentTime - lastTime;
        }        
      }            

      if (term != null && printZml) {
        try {
          XmlWriter writer = getXmlWriter();
          writer.write(term, System.err);
        }
        catch (MarshalException e) {
          e.printStackTrace();
        }
        /* ex:
         * 0        40            100           120          150
         * |--Parse--|--TypeCheck--|--PrintType--|--PrintZml--|         
         * lt = 120
         * ct = 150
         * pzt= 30 (150-120)  
         */
        lastTime = currentTime;
        currentTime = System.currentTimeMillis();
        printZmlTime = currentTime - lastTime;
      }      
      timesPerFile.put(file, Arrays.asList(parseTime, 
          typeCheckTime, printTypeTime, printZmlTime, 
          parseTime+typeCheckTime+printTypeTime+printZmlTime));
      // Reset the currentTime offset
      currentTime = System.currentTimeMillis();
      lastTime = currentTime;
    }
    long totalTime = System.currentTimeMillis() - zeroTime;
    
    System.out.println(totalTime + "ms for " + files.size() + " files.");
    if (printBenchmark) {      
      for(String file : timesPerFile.keySet()) {
        List<Long> times = timesPerFile.get(file);
        System.out.println("\t" + times.get(4) + "ms for " + file + ":");
        System.out.println("\t\tparser.........." + times.get(0) + "ms");
        if (!syntaxOnly) {
          System.out.println("\t\ttypechecker....." + times.get(1) + "ms");
        }
        if (printTypes) {
          System.out.println("\t\tprint types....." + times.get(2) + "ms");
        }
        if (printZml) {
          System.out.println("\t\tprint zml......." + times.get(3) + "ms");          
        }
      }             
    }        
    System.exit(result);
  }

  public static void main(String[] args)
    throws IOException, net.sourceforge.czt.base.util.UnmarshalException
  {    
    TypeCheckUtils utils = new TypeCheckUtils();    
    utils.run(args);
  }

  /**
   * Get a Command object for use in SectionManager
   *
   * @return A command for typechecking sections.
   */
  public static Command getCommand()
  {
    return new TypeCheckCommand();
  }
}
