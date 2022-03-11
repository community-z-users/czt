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

import java.io.File;
import java.io.IOException;
import java.io.StringWriter;
import java.util.Arrays;
import java.util.List;
import java.util.Set;
import java.util.SortedMap;
import java.util.TreeMap;

import net.sourceforge.czt.base.ast.ListTerm;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.impl.BaseFactory;
import net.sourceforge.czt.base.util.MarshalException;
import net.sourceforge.czt.base.util.TermInstanceCountManager;
import net.sourceforge.czt.base.util.XmlWriter;
import net.sourceforge.czt.parser.util.LatexMarkupFunction;
import net.sourceforge.czt.parser.z.ParseUtils;
import net.sourceforge.czt.print.util.PrintException;
import net.sourceforge.czt.print.z.PrintUtils;
import net.sourceforge.czt.session.Command;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.Dialect;
import net.sourceforge.czt.session.FileSource;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.Markup;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.session.Source;
import net.sourceforge.czt.typecheck.z.impl.Factory;
import net.sourceforge.czt.typecheck.z.impl.SectSummaryAnn;
import net.sourceforge.czt.typecheck.z.util.TypeErrorException;
import net.sourceforge.czt.util.Pair;
import net.sourceforge.czt.z.ast.NameSectTypeTriple;
import net.sourceforge.czt.z.ast.Sect;
import net.sourceforge.czt.z.ast.SectTypeEnvAnn;
import net.sourceforge.czt.z.ast.Spec;
import net.sourceforge.czt.z.ast.ZSect;
import net.sourceforge.czt.z.impl.NameTypePairImpl;
import net.sourceforge.czt.z.impl.ZFactoryImpl;
import net.sourceforge.czt.z.impl.ZNameImpl;
import net.sourceforge.czt.z.impl.ZStrokeListImpl;
import net.sourceforge.czt.z.util.WarningManager;

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
    return typecheck(term, sectInfo, useBeforeDecl, recursiveTypes, PROP_TYPECHECK_USE_NAMEIDS_DEFAULT, sectName);
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
    return typecheck(term, sectInfo, useBeforeDecl, recursiveTypes, useNameIds, null);
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
    //((net.sourceforge.czt.z.util.PrintVisitor)((ZFactoryImpl)zFactory).getToStringVisitor()).setPrintIds(true);
    TypeChecker typeChecker = new TypeChecker(new Factory(new ZFactoryImpl()),
					      sectInfo, useBeforeDecl, 
					      recursiveTypes);
    typeChecker.setPreamble(sectName, sectInfo);
    typeChecker.setUseNameIds(useNameIds);

    // see Checker.checkZSect for initial transaction setup

    return guardedTypeCheck(typeChecker, term);
  }

  /**
   *
   * @param typeChecker
   * @param term
   * @return
   */
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
          warningOutputDefault().equals(WarningManager.WarningOutput.HIDE) ? "h" : "")).trim() +
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

  protected boolean printDepsOfDefault()
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
  
  /** The list of known toolkits.
   *  This is used internally to avoid printing the types of toolkit names.
   * @return list of toolkit names
   */
  protected List<String> toolkits()
  {
    List<String> toolkits = new java.util.ArrayList<String>();
    toolkits.add(net.sourceforge.czt.util.Section.PRELUDE.getName());
    toolkits.add(net.sourceforge.czt.util.Section.SET_TOOLKIT.getName());
    toolkits.add(net.sourceforge.czt.util.Section.RELATION_TOOLKIT.getName());
    toolkits.add(net.sourceforge.czt.util.Section.FUNCTION_TOOLKIT.getName());
    toolkits.add(net.sourceforge.czt.util.Section.SEQUENCE_TOOLKIT.getName());
    toolkits.add(net.sourceforge.czt.util.Section.NUMBER_TOOLKIT.getName());
    toolkits.add(net.sourceforge.czt.util.Section.STANDARD_TOOLKIT.getName());
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
  protected void printTerm(Term term, StringWriter writer, SectionManager sectInfo, 
		  String sectName, Markup markup) throws PrintException
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
    ListTerm<NameSectTypeTriple> triples = sectTypeEnvAnn.getNameSectTypeTriple();
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

  protected SectSummaryAnn createSectSummaryAnn(String sectName)
  {
    return new SectSummaryAnn(sectName);
  }

  protected void printSummary(SectSummaryAnn summary)
  {
    System.out.println();
    System.out.println("Summary information for section " + summary.getSectName());
    for(Pair<String, Integer> pair : summary.getSectSummary())
    {
      System.out.print("\t");
      System.out.print(pair.getFirst());
      System.out.print(" = ");
      System.out.println(pair.getSecond());
    }
  }

  /** @return a fresh new section manager. */
  protected SectionManager getSectionManager()
  {
    SectionManager sectionManager = new SectionManager(Dialect.Z);
    // do not reuse the method: getCommand is static
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
      //System.exit(result);
    }
    else
    {
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
    String cztpath = null;
    Boolean printDepsOf = null;

    BaseFactory.resetInstanceCounter();
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
          warningOutput = WarningManager.WarningOutput.HIDE;
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
      else if (args[i].startsWith("-deps"))
      {
        printDepsOf = true;
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
                break;
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
                  warningOutput = WarningManager.WarningOutput.HIDE;
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
      cztpath           = cztPathDefault();
      printDepsOf       = printDepsOfDefault();
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
      //cztpath           = cztpath != null ? cztpath : null;
      printDepsOf       = printDepsOf != null ? printDepsOf : false;
    }  
    assert syntaxOnly != null && useBeforeDecl != null &&
      recursiveTypes != null && printTypes != null &&
      printZml != null && printBenchmark != null && useNameIds != null &&
      warningOutput != null &&
      printDepsOf != null : "Invalid flags!";
    
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
      
      //NOTE: from the Main CZT UI, the file.getParent() is being added
      //      to czt.path. This seems to be spurious as it works without it.
      Source source = new FileSource(file);
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
      if (term != null)
      {
        SectSummaryAnn summary = term.getAnn(SectSummaryAnn.class);
        if (summary == null && term instanceof Spec)
        {
          for(Sect s : ((Spec)term).getSect())
          {
            if (s.hasAnn(SectSummaryAnn.class))
            {
              printSummary(s.getAnn(SectSummaryAnn.class));
            }
            else if (s instanceof ZSect)
            {
              ZSect zs = (ZSect)s;
              summary = createSectSummaryAnn(zs.getName());
              summary.generateSummary(manager, zs);
              s.getAnns().add(summary);
              printSummary(summary);
            }
          }
        }
        else if (summary != null)
        {
          printSummary(summary);
        }
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
      for(java.util.Map.Entry<String, List<Long>> entry : benchmarkPerFile.entrySet()) {
        // 0=parsingErrors,
        // 1=numberOfErrors,
        // 2=numberOfWarnings,
        // 3=parseTime
        // 4=typeCheckTime
        // 5=printTypeTime
        // 6=printZmlTime
        // 7=totalTime
    	  String file = entry.getKey();
        List<Long> benchmarks = entry.getValue();
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
        System.out.println("\n\t\tAST instances..." + BaseFactory.howManyInstancesCreated());
        System.out.println  ("\t\tZStrokeL count.." + TermInstanceCountManager.instancesCount(ZStrokeListImpl.class, false));
        // or System.out.println  ("\t\tZStrokeL count.." + BaseUtils.instaceCount(ZStrokeListImpl.class));
        System.out.println  ("\t\tNTPair count...." + TermInstanceCountManager.instancesCount(NameTypePairImpl.class, false));

        System.out.println("\n\t\tZName count....." + TermInstanceCountManager.instancesCount(ZNameImpl.class, false));
//        System.out.println  ("\t\tZName live......" + (ZNameImpl.instancesFinalised()));
        System.out.println  ("\t\tZName live......" + TermInstanceCountManager.instancesCount(ZNameImpl.class, true));
        
        System.out.println("\n\tForce GC");
        System.gc();

        System.out.println("\n\t\tAST instances..." + BaseFactory.howManyInstancesCreated());
        System.out.println  ("\t\tZStrokeL count.." + TermInstanceCountManager.instancesCount(ZStrokeListImpl.class, false));
        // or System.out.println  ("\t\tZStrokeL count.." + BaseUtils.instaceCount(ZStrokeListImpl.class));
        System.out.println  ("\t\tNTPair count...." + TermInstanceCountManager.instancesCount(NameTypePairImpl.class, false));

        System.out.println("\n\t\tZName count....." + TermInstanceCountManager.instancesCount(ZNameImpl.class, false));
//        System.out.println  ("\t\tZName live......" + (ZNameImpl.instancesFinalised()));
        System.out.println  ("\t\tZName live......" + TermInstanceCountManager.instancesCount(ZNameImpl.class, true));

        System.out.println("  \t\tName pool size.." + ZNameImpl.nameIdPool().size());
        System.out.println("\n\t\tName-Id map....." + ZNameImpl.nameIdPool());

      }            
    }
        
    if (printDepsOf)
    {
      System.out.println("\n\n=========================================================================");
      for (Key<?> sk : manager.keysOf(Source.class))
      {
        if (!manager.isPermanentKey(sk))
        {
          printSet("All keys that depend on " + sk.toString(), manager.getDependants(sk));
          printSet("All keys that " + sk.toString() + " depends on", manager.getDependencies(sk));
        }
      }

      for(Key<?> zsk : manager.keysOf(ZSect.class))
      {
        if (!manager.isPermanentKey(zsk))
        {
          printSet("All keys that depend on " + zsk.toString(), manager.getDependants(zsk));
          printSet("All keys that " + zsk.toString() + " depends on", manager.getDependencies(zsk));
        }
      }

      for(Key<?> lmfk : manager.keysOf(LatexMarkupFunction.class))
      {
        if (!manager.isPermanentKey(lmfk))
        {
          printSet("All keys that depend on " + lmfk.toString(), manager.getDependants(lmfk));
          printSet("All keys that " + lmfk.toString() + " depends on", manager.getDependencies(lmfk));
        }
      }

      System.out.println("\n=========================================================================");
      

//      Set<Key<Source>> sourceKeys = manager.keysOf(Source.class);
//      Iterator<Key<Source>> it = sourceKeys.iterator();
//      while (it.hasNext())
//      {
//        Key<Source> sk = it.next();
//        if (manager.isPermanentKey(sk))
//          it.remove();
//      }
//
//      Set<Key<ZSect>> zsectKeys = manager.keysOf(ZSect.class);
//      Iterator<Key<ZSect>> it2 = zsectKeys.iterator();
//      while (it2.hasNext())
//      {
//        Key<ZSect> sk = it2.next();
//        if (manager.isPermanentKey(sk))
//          it2.remove();
//      }

    }
    System.exit(result);
    }
  }

  private static void printSet(String extra, Set<Key<?>> keys)
  {
    System.out.print(extra);
    System.out.print("\n\t\t");
    for (Key<?> k : keys)
    {
      System.out.print(k.toString());
      System.out.print("\n\t\t");
    }
    System.out.println();
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
