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
import java.io.File;
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
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.ast.ZFactory;
import net.sourceforge.czt.z.impl.ZFactoryImpl;
import net.sourceforge.czt.parser.z.*;
import net.sourceforge.czt.typecheck.z.impl.Factory;
import net.sourceforge.czt.typecheck.z.util.TypeErrorException;
import net.sourceforge.czt.z.util.WarningManager;
import sun.nio.cs.ext.TIS_620;

/**
 * Utilities for typechecking Z specifications.
 * This class provides a main method for command line use,
 * as well as several 'typecheck' methods that are designed
 * to be called by other Java classes.
 *
 * @author Petra Malik, Tim Miller
 */
public class TypeCheckUtils implements TypecheckPropertiesKeys
{
  /**
   * Do not generate instances of this class.
   * You should use the static methods directly.
   */
  protected TypeCheckUtils()
  {
  }
  
  /**
   * Typecheck and type annotate a term, with no default section and
   * not allowing names to be used before they are declared or
   * recursive types.
   * @param term the <code>Term</code> to typecheck (typically a Spec).
   * @param sectInfo the <code>SectionManager</code> object to use.
   * @return the list of ErrorAnns in the AST added by the typechecker.
   */
  public static List<? extends ErrorAnn> typecheck(Term term,
                                                   SectionManager sectInfo)
  {
    return typecheck(term,
		     sectInfo, 
		     PROP_TYPECHECK_USE_BEFORE_DECL_DEFAULT,
		     PROP_TYPECHECK_RECURSIVE_TYPES_DEFAULT);
  }


  /**
   * Typecheck and type annotate a term, with no default section.
   * @param term the <code>Term</code> to typecheck (typically a Spec).
   * @param sectInfo the <code>SectionManager</code> object to use.
   * @param useBeforeDecl allow variable use before declaration.
   * @param recursiveTypes allow use of recursive types.
   * @return the list of ErrorAnns in the AST added by the typechecker.
   */
  public static List<? extends ErrorAnn> typecheck(Term term,
                                                   SectionManager sectInfo,
                                                   boolean useBeforeDecl,
                                                   boolean recursiveTypes)
  {
    return typecheck(term, sectInfo, useBeforeDecl, recursiveTypes, null);
  }

  /**
   * Typecheck and type annotate a Term, in the context of a given section.
   * @param term the <code>Term</code> to typecheck.
   * @param sectInfo the <code>SectionManager</code> object to use.
   * @param useBeforeDecl allow variable use before declaration.
   * @param recursiveTypes allow use of recursive types.
   * @param sectName the section within which this term should be checked.
   * @return the list of ErrorAnns in the AST added by the typechecker.
   */
  public static List<? extends ErrorAnn> typecheck(Term term,
                                                   SectionManager sectInfo,
                                                   boolean useBeforeDecl,
                                                   boolean recursiveTypes,
                                                   String sectName)
  {
    TypeCheckUtils utils = new TypeCheckUtils();
    return utils.lTypecheck(term, sectInfo, useBeforeDecl, recursiveTypes, PROP_TYPECHECK_USE_NAMEIDS_DEFAULT, sectName);
  }

  /**
   * Typecheck and type annotate a Term, in the context of a given section.
   * @param term the <code>Term</code> to typecheck.
   * @param sectInfo the <code>SectionManager</code> object to use.
   * @param useBeforeDecl allow variable use before declaration.
   * @param recursiveTypes allow use of recursive types.
   * @param useNameIds use name ids as part of the name
   * @return the list of ErrorAnns in the AST added by the typechecker.
   */
  public static List<? extends ErrorAnn> typecheck(Term term,
                                                   SectionManager sectInfo,
                                                   boolean useBeforeDecl,
                                                   boolean recursiveTypes,
                                                   boolean useNameIds)
  {
    TypeCheckUtils utils = new TypeCheckUtils();
    return utils.lTypecheck(term, sectInfo, useBeforeDecl, 
			    recursiveTypes, useNameIds, null);
  }


  /**
   * Typecheck and type annotate a Term, in the context of a given section.
   * @param term the <code>Term</code> to typecheck.
   * @param sectInfo the <code>SectionManager</code> object to use.
   * @param useBeforeDecl allow variable use before declaration.
   * @param recursiveTypes allow use of recursive types.
   * @param useNameIds use name ids as part of the name
   * @param sectName the section within which this term should be checked.
   * @return the list of ErrorAnns in the AST added by the typechecker.
   */
  public static List<? extends ErrorAnn> typecheck(Term term,
                                                   SectionManager sectInfo,
                                                   boolean useBeforeDecl,
                                                   boolean recursiveTypes,
                                                   boolean useNameIds,
                                                   String sectName)
  {
    TypeCheckUtils utils = new TypeCheckUtils();
    return utils.lTypecheck(term, sectInfo, useBeforeDecl,
			    recursiveTypes, useNameIds, sectName);
  }
  
  public static List<? extends ErrorAnn> typecheck(Term term,
                                                   SectionManager sectInfo,
                                                   boolean useBeforeDecl,
                                                   boolean recursiveTypes,
                                                   boolean useNameIds,
                                                   WarningManager.WarningOutput warningOutput,
                                                   String sectName)
  {
    TypeCheckUtils utils = new TypeCheckUtils();
    return utils.lTypecheck(term, sectInfo, useBeforeDecl, recursiveTypes,
			    useNameIds, warningOutput, sectName);
  }

  protected List<? extends ErrorAnn> lTypecheck(Term term,
                                                SectionManager sectInfo,
						boolean useBeforeDecl,
                                                boolean recursiveTypes,
                                                boolean useNameIds,
                                                String sectName)
  {
    return lTypecheck(term, sectInfo, useBeforeDecl, recursiveTypes, 
		      useNameIds, WarningManager.WarningOutput.SHOW, sectName);
  }

  /** An internal method of the typechecker.
   * @param term
   * @param sectInfo
   * @param useBeforeDecl
   * @param recursiveTypes
   * @param useNameIds
   * @param warningOutput
   * @param sectName
   * @return
   */
  protected List<? extends ErrorAnn> lTypecheck(Term term,
                                                SectionManager sectInfo,
                                                   boolean useBeforeDecl,
                                                boolean recursiveTypes,
                                                boolean useNameIds,
                                                WarningManager.WarningOutput warningOutput,
                                                String sectName)
  {
    ZFactory zFactory = new ZFactoryImpl();    
    //((net.sourceforge.czt.z.util.PrintVisitor)((ZFactoryImpl)zFactory).getToStringVisitor()).setPrintIds(true);
    TypeChecker typeChecker = new TypeChecker(new Factory(zFactory), 
					      sectInfo, useBeforeDecl, 
					      recursiveTypes);
    typeChecker.setPreamble(sectName, sectInfo);
    typeChecker.setUseNameIds(useNameIds);

    return guardedTypeCheck(typeChecker, term);
  }

  @SuppressWarnings("CallToThreadDumpStack")
  protected List<? extends ErrorAnn> guardedTypeCheck(TypeChecker typeChecker, Term term)
  {
    // add type checking robustness on exceptions occurring at the top-level
    // that means, we have it for both command based and non-command based requests.
    try {
      term.accept(typeChecker);
    }
    catch(net.sourceforge.czt.base.util.UnsupportedAstClassException e)
    {
      Object[] params = {
        "An attempt to wrongly cast an AST class has happened",
        e.getMessage(),
        e.getClass().getName(),
        e.getCause() != null ? e.getCause().getClass() + " = " + e.getCause().getMessage() : "none"
      };
      // use any checker to report the error
      ErrorAnn error = typeChecker.exprChecker_.errorAnn(term, ErrorMessage.UNEXPECTED_EXCEPTION_ERROR, params);
      typeChecker.errors_.add(error);
      e.printStackTrace();
    }
    catch(net.sourceforge.czt.util.CztException f)
    {
      Object[] params = {
        "A unexpected CztException has happened",
        f.getMessage(),
        f.getClass().getName(),
        f.getCause() != null ? f.getCause().getClass() + " = " + f.getCause().getMessage() : "none"
      };
      // use any checker to report the error
      ErrorAnn error = typeChecker.exprChecker_.errorAnn(term, ErrorMessage.UNEXPECTED_EXCEPTION_ERROR, params);
      typeChecker.errors_.add(error);      
      if (f.getCause() != null && f.getCause() instanceof CommandException &&
          f.getCause().getCause() != null && f.getCause().getCause() instanceof TypeErrorException)
      {
        TypeErrorException tee = (TypeErrorException)f.getCause().getCause();
        typeChecker.errors_.addAll(0, tee.getErrors());
      }
      else
      {
        f.printStackTrace();
      }
    }
    catch(Throwable t)
    {
      Object[] params = {
        "A general Throwable exception has happened",
        t.getMessage(),
        t.getClass().getName(),
        t.getCause() != null ? t.getCause().getClass() + " = " + t.getCause().getMessage() : "none"
      };
      // use any checker to report the error
      ErrorAnn error = typeChecker.exprChecker_.errorAnn(term, ErrorMessage.UNEXPECTED_EXCEPTION_ERROR, params);
      typeChecker.errors_.add(error);
      t.printStackTrace();
    }
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
    System.err.println("       -r     allow recursive types");
    System.err.println("       -i     use name ids");
    System.err.println("       -p     print the AST");
    System.err.println("       -t     print global type declarations");
    System.err.println("       -b     print benchmarking times");
    System.err.println("       -h     hide warnings (cannot hide when raising!)");
    System.err.println("       -o     show warnings");
    System.err.println("       -w     raise warnings as errors");
    System.err.println("      -cp <l> specify the value for czt.path as");
    System.err.println("              a semicolon-separated list of dirs");
    System.err.println("              (e.g., -cp ./tests;/user/myfiles).");
    System.err.println("              The list is mandatory and must not be empty.");
    System.err.println("       -g{bi} gathering of latex mark-up so that directives");
    System.err.println("              are moved to the beginnings of their sections");
    System.err.println("           b  buffer whole spec in memory (faster)");
    System.err.println("           i  retain informal narrative (no eliding)");
    System.err.println("\n");
    System.err.println("Default flags are: \"-" +
        ((syntaxOnlyDefault() ? "s " : "") +
        (useBeforeDeclDefault() ? "d " : "n ") +
        (recursiveTypesDefault() ? "r " : "") +
        (useNameIdsDefault() ? "i " : "") +
        (printZMLDefault() ? "p " : "") + 
        (printTypesDefault() ? "t " : "") +
        (printBenchmarkTimesDefault() ? "b" : "") +
        (warningOutputDefault().equals(WarningManager.WarningOutput.RAISE) ? "w" :
          warningOutputDefault().equals(WarningManager.WarningOutput.HIDE) ? "h" : "") +
        (useSpecReaderDefault() ? "gb " : "")).trim() +
        "\"");
  }

  protected boolean useBeforeDeclDefault()
  {
    return PROP_TYPECHECK_USE_BEFORE_DECL_DEFAULT;
  }

  protected boolean recursiveTypesDefault()
  {
    return PROP_TYPECHECK_RECURSIVE_TYPES_DEFAULT;
  }

  protected boolean printBenchmarkTimesDefault()
  {
    return false;
  }
  
  protected boolean syntaxOnlyDefault()
  {
    return false;
  }

  protected WarningManager.WarningOutput warningOutputDefault()
  {
    return PROP_TYPECHECK_WARNINGS_OUTPUT_DEFAULT;
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
    return PROP_TYPECHECK_USE_NAMEIDS_DEFAULT;
  }

  protected String cztPathDefault()
  {
    return null;
  }
  
  protected  boolean useSpecReaderDefault()
  {
    return PROP_TYPECHECK_USE_SPECREADER_DEFAULT;
  }

  protected boolean isSpecReaderBufferingWantedDefault() 
  {
    return false && useSpecReaderDefault();
  }
  
  protected boolean isSpecReaderNarrativeWantedDefault()
  {
    return false && useSpecReaderDefault();
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
  
  protected List<Integer> printErrors(List<? extends ErrorAnn> errors, WarningManager.WarningOutput warningOutput)
  {
    int errorCount = 0;
    int warningCount = 0;
    boolean print = true;
    //print any errors
    for (ErrorAnn next : errors) {
      switch (next.getErrorType())
      {
        case ERROR:
          errorCount++;
          print = true;
          break;
        case WARNING:
          switch (warningOutput)
          {
            case RAISE:
              errorCount++;
              print = true;
              break;
            case HIDE:
              print = false; // hide but count
              warningCount++;
              break;
            case SHOW:
              warningCount++;
              print = true;
              break;
          }
          break;
      }
      if (print)
      {
        System.out.println(next);
        System.out.println();        
      }      
    }
    return Arrays.asList(errorCount, warningCount);
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
    sectionManager.setProperties(System.getProperties());
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

    if (args == null || args.length == 0) {
      printUsage();
      System.exit(result);
    }

    List<String> files = new java.util.ArrayList<String>();

    // If we initialise flags here with default values, and different
    // flags from the default ones are given, the flag control variables
    // won't get changed. Instead use "null" for the case where they
    // are indeed to be set to the default.
    boolean defaultFlags = true;
    Boolean syntaxOnly = null;
    Boolean useBeforeDecl = null;
    Boolean recursiveTypes = null;
    Boolean printTypes = null;
    Boolean printZml = null;
    Boolean printBenchmark = null;
    Boolean useNameIds = null;
    WarningManager.WarningOutput warningOutput = null;
    Boolean useSpecReader = null;
    Boolean isBufferingWanted = null;
    Boolean isNarrativeWanted = null;
    String cztpath = null;

    SectionManager manager = getSectionManager();    
      
    for (int i = 0; i < args.length; i++) 
    {
      if ("-s".equals(args[i])) 
      {
        syntaxOnly = true;
        defaultFlags = false;
      }
      else if ("-r".equals(args[i]))
      {
        recursiveTypes = true;
        defaultFlags = false;
        manager.setProperty(PROP_TYPECHECK_RECURSIVE_TYPES, String.valueOf(recursiveTypes));
      }
      else if ("-d".equals(args[i]))
      {
        useBeforeDecl = true;
        defaultFlags = false;
        manager.setProperty(PROP_TYPECHECK_USE_BEFORE_DECL, String.valueOf(useBeforeDecl));
      }
      else if ("-n".equals(args[i]))
      {
        recursiveTypes = false;
        defaultFlags = false;
        manager.setProperty(PROP_TYPECHECK_RECURSIVE_TYPES, String.valueOf(recursiveTypes));
      }
      else if ("-t".equals(args[i]))
      {
        printTypes = true;
        defaultFlags = false;
      }
      else if ("-p".equals(args[i]))
      {
        printZml = true;
        defaultFlags = false;
      }
      else if ("-b".equals(args[i]))
      {
        printBenchmark = true;
        defaultFlags = false;
      }
      else if ("-i".equals(args[i]))
      {
        useNameIds = true;
        defaultFlags = false;
        manager.setProperty(PROP_TYPECHECK_USE_NAMEIDS, String.valueOf(useNameIds));
      }
      else if ("-w".equals(args[i]))
      {
        warningOutput = WarningManager.WarningOutput.RAISE;
        defaultFlags = false;
        manager.setProperty(PROP_TYPECHECK_WARNINGS_OUTPUT, String.valueOf(warningOutput));
      }
      else if ("-h".equals(args[i]))
      {
        // raise has precedence over hide
        if (warningOutput == null || !warningOutput.equals(WarningManager.WarningOutput.RAISE))
        {
          defaultFlags = false;
          warningOutput = warningOutput.HIDE;
          manager.setProperty(PROP_TYPECHECK_WARNINGS_OUTPUT, String.valueOf(warningOutput));
        }
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
        defaultFlags = false;
        cztpath = args[i].trim();
      }
      else if (args[i].startsWith("-g")) 
      {
          useSpecReader = true;
          defaultFlags = false;
          isBufferingWanted = args[i].indexOf('b', 2) > -1? true : false;
          isNarrativeWanted = args[i].indexOf('i', 2) > -1? true : false;          
          manager.setProperty(PROP_TYPECHECK_USE_SPECREADER, String.valueOf(useSpecReader));    
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
                defaultFlags = false;
                break;
              case 'n':
                recursiveTypes = false;
                defaultFlags = false;
                manager.setProperty(PROP_TYPECHECK_RECURSIVE_TYPES, String.valueOf(recursiveTypes));
                break;
              case 'r':
                recursiveTypes = true;
                defaultFlags = false;
                manager.setProperty(PROP_TYPECHECK_RECURSIVE_TYPES, String.valueOf(recursiveTypes));
                break;
              case 'd':
                useBeforeDecl = true;
                defaultFlags = false;
                manager.setProperty(PROP_TYPECHECK_USE_BEFORE_DECL, String.valueOf(useBeforeDecl));
              case 't':
                printTypes = true;
                defaultFlags = false;
                break;
              case 'p':
                printZml = true;
                defaultFlags = false;
                break;
              case 'b':
                printBenchmark = true;
                defaultFlags = false;
                break;
              case 'i':
                useNameIds = true;
                defaultFlags = false;
                manager.setProperty(PROP_TYPECHECK_USE_NAMEIDS, String.valueOf(useNameIds));
                break;
              case 'o':
                warningOutput = WarningManager.WarningOutput.SHOW;
                defaultFlags = false;
                manager.setProperty(PROP_TYPECHECK_WARNINGS_OUTPUT, String.valueOf(warningOutput));
                break;
              case 'w':
                warningOutput = WarningManager.WarningOutput.RAISE;
                defaultFlags = false;
                manager.setProperty(PROP_TYPECHECK_WARNINGS_OUTPUT, String.valueOf(warningOutput));
                break;
              case 'h':
                //args[i].indexOf('w') != -1
                //warningOutput.equals(WarningManager.WarningOutput.RAISE)
                if (warningOutput == null || (!warningOutput.equals(WarningManager.WarningOutput.RAISE) && args[i].indexOf('w') == -1))
                {
                  defaultFlags = false;
                  warningOutput = warningOutput.HIDE;
                  manager.setProperty(PROP_TYPECHECK_WARNINGS_OUTPUT, String.valueOf(warningOutput));
                }
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
    // TODO: use bitSet for this... rather ugly now :-(

    // if no flag is changed default flag is true,
    // then we set all to the default values.
    if (defaultFlags)
    {
      syntaxOnly        = syntaxOnlyDefault();
      useBeforeDecl     = useBeforeDeclDefault();
      recursiveTypes    = recursiveTypesDefault();
      printTypes        = printTypesDefault();
      printZml          = printZMLDefault();
      printBenchmark    = printBenchmarkTimesDefault();
      useNameIds        = useNameIdsDefault();
      warningOutput     = warningOutputDefault();
      useSpecReader     = useSpecReaderDefault();
      isBufferingWanted = isSpecReaderBufferingWantedDefault();
      isNarrativeWanted = isSpecReaderNarrativeWantedDefault();
      cztpath           = cztPathDefault();
    }
    // otherwise, we set all unset flags (e.g., null values) to false
    else
    {
      syntaxOnly        = syntaxOnly != null ? syntaxOnly : false;
      useBeforeDecl     = useBeforeDecl != null ? useBeforeDecl : false;
      recursiveTypes    = recursiveTypes != null ? recursiveTypes : false;
      printTypes        = printTypes != null ? printTypes : false;
      printZml          = printZml != null ? printZml : false;
      printBenchmark    = printBenchmark != null ? printBenchmark : false;
      useNameIds        = useNameIds != null ? useNameIds : false;
      warningOutput     = warningOutput != null ? warningOutput : WarningManager.WarningOutput.SHOW;
      useSpecReader     = useSpecReader != null ? useSpecReader : false;
      isBufferingWanted = isBufferingWanted != null ? isBufferingWanted : false;
      isNarrativeWanted = isNarrativeWanted != null ? isNarrativeWanted : false;
      //cztpath           = cztpath != null ? cztpath : null;
    }  
    assert syntaxOnly != null && useBeforeDecl != null &&
      recursiveTypes != null && printTypes != null &&
      printZml != null && printBenchmark != null && useNameIds != null &&
      warningOutput != null && useSpecReader != null &&
      isBufferingWanted != null && isNarrativeWanted != null : "Invalid flags!";
    
    // add a potentially old czt path (? TODO: decide to add this or not ?)
    String localcztpath = "";
    if (cztpath != null && !cztpath.trim().isEmpty())
    {
      String oldcztpath = manager.getProperty("czt.path");
      if (oldcztpath != null && !oldcztpath.trim().isEmpty())
      {
        cztpath = oldcztpath + File.pathSeparator + cztpath;
      }      
      localcztpath = cztpath;
    }                
    
    SortedMap<String, List<Long>> benchmarkPerFile = new TreeMap<String, List<Long>>();
    long zeroTime = System.currentTimeMillis();     
    long currentTime = zeroTime;
    long lastTime = zeroTime;    
    for (String file : files) {            
      //parse the file
      Term term = null;
      Markup markup = ParseUtils.getMarkup(file);
      
      // add the file parent to the path as well.      
      File archive = new File(file);
      if (archive != null && archive.getParent() != null) 
      {
        String fileParent = archive.getParent();
        if (fileParent != null && !fileParent.isEmpty())
        {
          localcztpath = fileParent;
        }
        if (cztpath != null && !cztpath.isEmpty())
        {
          localcztpath = fileParent + File.pathSeparator + cztpath;
        }             
      }            
      if (localcztpath != null && !localcztpath.trim().isEmpty())
      {
        manager.setProperty("czt.path", localcztpath);
      }
      
      Source source = null;
      boolean openOk = false;
      if (useSpecReader)
      {
        for (String suff : net.sourceforge.czt.specreader.SpecReader.SUFFICES) {
          if (file.endsWith(suff)) {
            source = new SpecSource(file, isBufferingWanted, isNarrativeWanted);
            openOk = true;
            break;
          }
        }
      }
      if (!openOk)
      {
        //NOTE: from the Main CZT UI, the file.getParent() is being added
        //      to czt.path. This seems to be spurious as it works without it.
        source = new FileSource(file);
      }
      long parsingErrors = 0;
      try {
        term = this.parse(source, manager);
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
      long numberOfWarnings = 0;
      //if the parse succeeded, typecheck the term
      if (term != null && !syntaxOnly)
      {
        List<? extends ErrorAnn> errors =
          this.lTypecheck(term, manager, useBeforeDecl, 
			  recursiveTypes, useNameIds, warningOutput, null);

        // result is the number of errors to consider
        List<Integer> eCount = printErrors(errors, warningOutput);
        numberOfErrors = eCount.get(0);
        numberOfWarnings = eCount.get(1);
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

        if (printTypes != null && printTypes)
        {
          SectTypeEnvAnn sectTypeEnvAnn =
            term.getAnn(SectTypeEnvAnn.class);
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
      if (term != null && printZml)
      {
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
      benchmarkPerFile.put(file, Arrays.asList(parsingErrors, numberOfErrors,
          numberOfWarnings, parseTime, typeCheckTime, printTypeTime, printZmlTime, 
          parseTime+typeCheckTime+printTypeTime+printZmlTime));
      // Reset the currentTime offset
      currentTime = System.currentTimeMillis();
      lastTime = currentTime;
    }
    long totalTime = System.currentTimeMillis() - zeroTime;
    
    if (cztpath != null)
    {
      // set the global czt path after all files have been processed.
      manager.setProperty("czt.path", cztpath);
    }
    
    if (printBenchmark) {      
      System.out.println(totalTime + "ms for " + files.size() + " files.");
      for(String file : benchmarkPerFile.keySet()) {
        // 0=parsingErrors,
        // 1=numberOfErrors,
        // 2=numberOfWarnings,
        // 3=parseTime
        // 4=typeCheckTime
        // 5=printTypeTime
        // 6=printZmlTime
        // 7=totalTime
        List<Long> benchmarks = benchmarkPerFile.get(file);
        assert benchmarks != null && benchmarks.size() == 8;
        System.out.println("\t" + benchmarks.get(7) + "ms for " + file + ":");
        System.out.println("\t\tparsing errors.." + benchmarks.get(0));
        if (!syntaxOnly) {
          System.out.println("\t\ttype errors....." + benchmarks.get(1));
          //if (warningOutput.equals(WarningManager.WarningOutput.SHOW))
          {
            System.out.println("\t\twarnings........" + benchmarks.get(2));
          }
        }
        System.out.println("\t\tparser.........." + benchmarks.get(3) + "ms");
        if (!syntaxOnly) {
          System.out.println("\t\ttypechecker....." + benchmarks.get(4) + "ms");
        }
        if (printTypes) {
          System.out.println("\t\tprint types....." + benchmarks.get(5) + "ms");
        }
        if (printZml) {
          System.out.println("\t\tprint zml......." + benchmarks.get(6) + "ms");
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
