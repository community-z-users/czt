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
import net.sourceforge.czt.parser.util.ErrorType;
import net.sourceforge.czt.print.z.PrintUtils;
import net.sourceforge.czt.session.*;
import net.sourceforge.czt.util.CztException;
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
  
  public static List<? extends ErrorAnn> typecheck(Term term,
                                                   SectionManager sectInfo,
                                                   boolean useBeforeDecl,
                                                   boolean useNameIds,
                                                   boolean raiseWarnings,
                                                   String sectName)
  {
    TypeCheckUtils utils = new TypeCheckUtils();
    return utils.lTypecheck(term, sectInfo, useBeforeDecl, useNameIds, raiseWarnings, sectName);
  }

  protected List<? extends ErrorAnn> lTypecheck(Term term,
                                                SectionManager sectInfo,
                                                boolean useBeforeDecl,
                                                boolean useNameIds,
                                                String sectName)
  {
    return lTypecheck(term, sectInfo, useBeforeDecl, useNameIds, raiseWarningsDefault(), sectName);
  }

  /** An internal method of the typechecker. */
  protected List<? extends ErrorAnn> lTypecheck(Term term,
                                                SectionManager sectInfo,
                                                boolean useBeforeDecl,
                                                boolean useNameIds,
                                                boolean raiseWarnings,
                                                String sectName)
  {
    ZFactory zFactory = new ZFactoryImpl();    
    //((net.sourceforge.czt.z.util.PrintVisitor)((ZFactoryImpl)zFactory).getToStringVisitor()).setPrintIds(true);
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
    System.err.println("       -w     raise warnings as errors");
    System.err.println("      -cp <l> specify the value for czt.path as");
    System.err.println("              a semicolon-separated list of dirs");
    System.err.println("              (e.g., -cp=./tests;/user/myfiles).");
    System.err.println("              The list is mandatory and must not be empty.");
  }

  protected boolean useBeforeDeclDefault()
  {
    return false;
  }

  protected boolean printBenchmarkTimesDefault()
  {
    return false;
  }
  
  protected boolean syntaxOnlyDefault()
  {
    return false;
  }
  
  protected boolean printTypesDefault()
  {
    return false;
  }
    
  protected boolean printZMLDefault()
  {
    return false;
  }
  
  protected boolean useNameIdsDefault()
  {
    return false;
  }
  
  protected boolean raiseWarningsDefault()
  { 
    return false;
  }
  
  protected String cztPathDefault()
  {
    return null;
  }

  /** The list of known toolkits.
   *  This is used internally to avoid printing the types of toolkit names.
   * @return list of toolkit names
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

  /**
   * Calls PrintUtils.print(term, writer, sectInfo, sectName, markup).
   * Different extensions may use different versions of PrintUtils.
   * @param term
   * @param writer
   * @param sectInfo
   * @param sectName
   * @param markup
   */
  protected void printTerm(Term term, StringWriter writer, SectionManager sectInfo, String sectName, Markup markup)
  {
    PrintUtils.print(term, writer, sectInfo, sectName, markup);
  }
  
  /**
   * Tries calling printTerm(term, writer, sectInfo, sectName, markup) on a local String writer
   * to see whether it is possible to pretty print the term given. If that fails (throws an
   * exception), the PrintVisitor is used by just calling term.toString().
   * @param term
   * @param sectInfo
   * @param sectName
   * @param markup
   * @return
   */   
  protected String printTerm(Term term, SectionManager sectInfo, String sectName, Markup markup)
  {
    String result;    
    try 
    {
      StringWriter writer = new StringWriter();
      printTerm(term, writer, sectInfo, sectName, markup);
      writer.flush();
      result = writer.toString();
    } catch(/*CztException*/ Throwable e)      
    {
      result = term.toString();
    }
    return result;
  }
  
  protected int printErrors(List<? extends ErrorAnn> errors, boolean raiseWarnings)
  {
    int result = 0;
    //print any errors
    for (ErrorAnn next : errors) {
      // raiseWarnings => next.getErrorType(ErrorType.ERROR) only
      if (raiseWarnings || next.getErrorType().equals(ErrorType.ERROR))
      {
        System.out.println(next);
        System.out.println();
        result++;
      }
    }
    return result;
  }
  
  protected void printTypes(SectTypeEnvAnn sectTypeEnvAnn, SectionManager sectInfo, Markup markup)
  {
    List<NameSectTypeTriple> triples = sectTypeEnvAnn.getNameSectTypeTriple();
    String prevSect = "";    
    for (NameSectTypeTriple triple : triples) {
      String currSect = triple.getSect();
      if (!toolkits().contains(currSect)) {
        if (!prevSect.equals(currSect)) {
          System.out.println("section " + currSect);
        }
        System.out.println("\t" + printTerm(triple.getZName(), sectInfo, currSect, markup) +
                          " : " + printTerm(triple.getType(), sectInfo, currSect, markup));
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
    int result = 0;
    
    if (args.length == 0) {
      printUsage();
      System.exit(result);
    }

    List<String> files = new java.util.ArrayList<String>();
    boolean syntaxOnly = syntaxOnlyDefault();
    boolean useBeforeDecl = useBeforeDeclDefault();
    boolean printTypes = printTypesDefault();
    boolean printZml = printZMLDefault();
    boolean printBenchmark = printBenchmarkTimesDefault();
    boolean useNameIds = useNameIdsDefault();
    boolean raiseWarnings = raiseWarningsDefault();
    String cztpath = cztPathDefault();

    for (int i = 0; i < args.length; i++) 
    {
      if ("-s".equals(args[i])) 
      {
        syntaxOnly = true;
      }
      else if ("-d".equals(args[i]))
      {
        useBeforeDecl = true;
      }
      else if ("-n".equals(args[i]))
      {
        useBeforeDecl = false;
      }
      else if ("-t".equals(args[i]))
      {
        printTypes = true;  
      }
      else if ("-p".equals(args[i]))
      {
        printZml = true;  
      }
      else if ("-b".equals(args[i]))
      {
        printBenchmark = true;    
      }
      else if ("-i".equals(args[i]))
      {
        useNameIds = true;    
      }
      else if ("-w".equals(args[i]))
      {
        raiseWarnings = true;    
      }
      else if (args[i].equals("-cp"))
      {          
        if (i == args.length)
        {
          printUsage();
          System.err.println("\nYou need to provide an argument for `-cp'");
          System.exit(result);
        }
        i++;
        cztpath = args[i].trim();        
      }
      else if (args[i].startsWith("-")) 
      {
        // keep compatible as before for: -sdt
        if (args[i].length() > "- ".length())
        {        
          if (args[i].startsWith("-")) 
          {
            for (int j = 1; j < args[i].length(); j++) 
            {
              switch (args[i].charAt(j)) 
              {
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
              case 'w':
                raiseWarnings = true;
                break;
              default:
                printUsage();
                return;
              }
            }
          }
        }
        else 
        {
          printUsage();
          return;
        }
      }
      else
      {
        files.add(args[i]);    
      }        
    }       
    SectionManager manager = getSectionManager();
    SortedMap<String, List<Long>> timesPerFile = new TreeMap<String, List<Long>>();    
    if (cztpath != null && !cztpath.isEmpty())
    {
      manager.setProperty("czt.path", cztpath);
    }
    long zeroTime = System.currentTimeMillis();     
    long currentTime = zeroTime;
    long lastTime = zeroTime;
    for (String file : files) {            
      //parse the file
      Term term = null;
      Markup markup = ParseUtils.getMarkup(file);
      long parsingErrors = 0;
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
        parsingErrors = exception.getErrorList().size();
        exception.printErrorList();
      }
      catch(net.sourceforge.czt.base.util.UnsupportedAstClassException e)
      {
        System.err.println("An attempt to wrongly cast an AST class has happened.\n" +
          "This is usually a bug, and should not happen. Please report it to czt-devel@lists.sourceforge.net");    
        e.printStackTrace();
      }
      catch(net.sourceforge.czt.util.CztException f)
      {
        System.err.println("A general CztException has happened.\n" +
          "This is usually a bug, and should not happen. Please report it to czt-devel@lists.sourceforge.net");    
        f.printStackTrace();
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
      long numberOfErrors = 0;
      //if the parse succeeded, typecheck the term
      if (term != null && !syntaxOnly) {
        List<? extends ErrorAnn> errors =
          this.lTypecheck(term, manager, useBeforeDecl, useNameIds, raiseWarnings, null);
        
        // result is the number of errors to consider
        numberOfErrors = printErrors(errors, raiseWarnings);        
        result += numberOfErrors + parsingErrors;
        
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
          if (sectTypeEnvAnn != null) 
          {
            printTypes(sectTypeEnvAnn, manager, markup);
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
      timesPerFile.put(file, Arrays.asList(parsingErrors, numberOfErrors,
          parseTime, typeCheckTime, printTypeTime, printZmlTime, 
          parseTime+typeCheckTime+printTypeTime+printZmlTime));
      // Reset the currentTime offset
      currentTime = System.currentTimeMillis();
      lastTime = currentTime;
    }
    long totalTime = System.currentTimeMillis() - zeroTime;
    
    if (printBenchmark) {      
      System.out.println(totalTime + "ms for " + files.size() + " files.");
      for(String file : timesPerFile.keySet()) {
        List<Long> times = timesPerFile.get(file);
        System.out.println("\t" + times.get(6) + "ms for " + file + ":");
        System.out.println("\t\tparsing errors.." + times.get(0));
        if (!syntaxOnly) {
          System.out.println("\t\ttype errors....." + times.get(1));
        }
        System.out.println("\t\tparser.........." + times.get(2) + "ms");
        if (!syntaxOnly) {
          System.out.println("\t\ttypechecker....." + times.get(3) + "ms");
        }
        if (printTypes) {
          System.out.println("\t\tprint types....." + times.get(4) + "ms");
        }
        if (printZml) {
          System.out.println("\t\tprint zml......." + times.get(5) + "ms");          
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
