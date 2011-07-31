/*
  Copyright (C) 2006, 2007 Leo Freitas
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
package net.sourceforge.czt.typecheck.zeves;

import java.io.IOException;
import java.io.PrintWriter;
import java.io.StringWriter;
import java.util.ArrayList;
import java.util.List;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.zeves.ast.ZEvesFactory;
import net.sourceforge.czt.zeves.impl.ZEvesFactoryImpl;
import net.sourceforge.czt.zeves.jaxb.JaxbXmlWriter;
import net.sourceforge.czt.parser.zeves.ParseUtils;
import net.sourceforge.czt.parser.util.LatexMarkupFunction;
import net.sourceforge.czt.session.Command;
import net.sourceforge.czt.session.FileSource;
import net.sourceforge.czt.session.Markup;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.session.Source;
import net.sourceforge.czt.util.SimpleFormatter;
import net.sourceforge.czt.z.ast.SectTypeEnvAnn;
import net.sourceforge.czt.z.ast.Spec;
import net.sourceforge.czt.z.ast.ZFactory;
import net.sourceforge.czt.z.ast.ZSect;
import net.sourceforge.czt.z.impl.ZFactoryImpl;

/**
 *
 * @author Leo Freitas
 */
public class TypeCheckUtils 
    extends net.sourceforge.czt.typecheck.z.TypeCheckUtils {
  
  private static final TypeCheckUtils instance_ = new TypeCheckUtils();
  
  /**
   * Do not generate instances of this class.
   * You should use the static methods directly.
   */
  protected TypeCheckUtils()
  {
    super();
  }
  
  /**
   * Typecheck and type annotate a term, with no default section and
   * not allowing names to be used before they are declared or
   * recursive types.
   * @param term the <code>Term</code> to typecheck (typically a Spec).
   * @param sectInfo the <code>SectionManager</code> object to use.
   * @return the list of ErrorAnns in the AST added by the typechecker.
   */
  public static List<? extends net.sourceforge.czt.typecheck.z.ErrorAnn> typecheck(Term term,
                                                   SectionManager sectInfo)
  {
    return typecheck(term, sectInfo, PROP_TYPECHECK_RECURSIVE_TYPES_DEFAULT);
  }
  
  /**
   * Typecheck and type annotate a term, with no default section.
   * @param term the <code>Term</code> to typecheck (typically a Spec).
   * @param sectInfo the <code>SectionManager</code> object to use.
   * @param recursiveTypes allow use of recursive types
   * @return the list of ErrorAnns in the AST added by the typechecker.
   */
  public static List<? extends net.sourceforge.czt.typecheck.z.ErrorAnn> typecheck(Term term,
                                                   SectionManager sectInfo,
                                                   boolean recursiveTypes)
  {
    return typecheck(term, sectInfo, recursiveTypes, PROP_TYPECHECK_SORT_DECL_NAMES_DEFAULT, null);
  }
  
  /**
   * Typecheck and type annotate a term, with no default section.
   * @param term the <code>Term</code> to typecheck (typically a Spec).
   * @param sectInfo the <code>SectionManager</code> object to use.
   * @param recursiveTypes allow use of recursive types
   * @param sortDeclNames 
   * @return the list of ErrorAnns in the AST added by the typechecker.
   */
  public static List<? extends net.sourceforge.czt.typecheck.z.ErrorAnn> typecheck(Term term,
                                                   SectionManager sectInfo,
                                                   boolean recursiveTypes,
                                                   boolean sortDeclNames)
  {
    return typecheck(term, sectInfo, recursiveTypes, sortDeclNames, null);
  }
  
  /**
   * Typecheck and type annotate a Term, in the context of a given section.
   * @param term the <code>Term</code> to typecheck.
   * @param sectInfo the <code>SectionManager</code> object to use.
   * @param recursiveTypes allow use of recursive types
   * @param sortDeclNames 
   * @param sectName the section within which this term should be checked.
   * @return the list of ErrorAnns in the AST added by the typechecker.
   */
  public static List<? extends net.sourceforge.czt.typecheck.z.ErrorAnn> typecheck(Term term,
                                                   SectionManager sectInfo,
                                                   boolean recursiveTypes,
                                                   boolean sortDeclNames,
                                                   String sectName)
  {    
    return instance_.lTypecheck(term, sectInfo, recursiveTypes, sortDeclNames,
        PROP_TYPECHECK_USE_NAMEIDS_DEFAULT, PROP_TYPECHECK_WARNINGS_OUTPUT_DEFAULT, sectName);
  }
  
  /**
   * Typecheck and type annotate a Term, in the context of a given section.
   * @param term the <code>Term</code> to typecheck.
   * @param sectInfo the <code>SectionManager</code> object to use.
   * @param recursiveTypes allow use of recursive types
   * @param sortDeclNames 
   * @param useNameIds use name ids as part of the name
   * @return the list of ErrorAnns in the AST added by the typechecker.
   */
  public static List<? extends net.sourceforge.czt.typecheck.z.ErrorAnn> typecheck(Term term,
                                                   SectionManager sectInfo,
                                                   boolean recursiveTypes,
                                                   boolean sortDeclNames,
                                                   boolean useNameIds)
  {    
    return instance_.lTypecheck(term, sectInfo, recursiveTypes, sortDeclNames, useNameIds, 
        PROP_TYPECHECK_WARNINGS_OUTPUT_DEFAULT, null);
  }
  
  /**
   * Typecheck and type annotate a Term, in the context of a given section.
   * @param term the <code>Term</code> to typecheck.
   * @param sectInfo the <code>SectionManager</code> object to use.
   * @param recursiveTypes allow use of recursive types
   * @param sortDeclNames 
   * @param useNameIds use name ids as part of the name
   * @param sectName the section within which this term should be checked.
   * @return the list of ErrorAnns in the AST added by the typechecker.
   */
  public static List<? extends net.sourceforge.czt.typecheck.z.ErrorAnn> typecheck(Term term,
                                                   SectionManager sectInfo,
                                                   boolean recursiveTypes,
                                                   boolean sortDeclNames,
                                                   boolean useNameIds,
                                                   String sectName)
  {    
    return instance_.lTypecheck(term, sectInfo, recursiveTypes, sortDeclNames, useNameIds, 
        PROP_TYPECHECK_WARNINGS_OUTPUT_DEFAULT, sectName);
  }

  public static List<? extends net.sourceforge.czt.typecheck.z.ErrorAnn> typecheck(Term term,
                                                   SectionManager sectInfo,
                                                   boolean recursiveTypes,
                                                   boolean useNameIds,
                                                   WarningManager.WarningOutput warningOutput,
                                                   String sectName)
  {
    return instance_.lTypecheck(term, sectInfo, recursiveTypes, useNameIds,
      PROP_TYPECHECK_SORT_DECL_NAMES_DEFAULT, warningOutput, sectName);
  }
  
  public static List<? extends net.sourceforge.czt.typecheck.z.ErrorAnn> typecheck(Term term,
                                                   SectionManager sectInfo,
                                                   boolean recursiveTypes,
                                                   boolean sortDeclNames,
                                                   boolean useNameIds,
                                                   WarningManager.WarningOutput warningOutput,
                                                   String sectName)
  {    
    return instance_.lTypecheck(term, sectInfo, recursiveTypes, sortDeclNames, useNameIds, warningOutput, sectName);
  }

  protected List<? extends net.sourceforge.czt.typecheck.z.ErrorAnn> lTypecheck(Term term,
                                                SectionManager sectInfo,
                                                boolean recursiveTypes,
                                                boolean useNameIds,
                                                String sectName)
  {
    return lTypecheck(term, sectInfo, recursiveTypes, PROP_TYPECHECK_SORT_DECL_NAMES_DEFAULT,
        useNameIds, warningOutputDefault(), sectName);
  }
  
  /** An internal method of the typechecker. */
  protected List<? extends net.sourceforge.czt.typecheck.z.ErrorAnn> lTypecheck(Term term,
                                                SectionManager sectInfo,
                                                boolean recursiveTypes,
                                                boolean useNameIds,
                                                WarningManager.WarningOutput warningOutput,
                                                String sectName)
  {
    return lTypecheck(term, sectInfo, recursiveTypes, PROP_TYPECHECK_SORT_DECL_NAMES_DEFAULT,
        useNameIds, warningOutput, sectName);
  }
  
  private String stackTraceAsString(Throwable e)
  {    
    StringWriter swriter = new StringWriter();
    PrintWriter pwriter = new PrintWriter(swriter);      
    e.fillInStackTrace();      
    e.printStackTrace(pwriter);      
    pwriter.flush();
    pwriter.close();
    return swriter.toString();
  }
  
  /** An internal method of the typechecker. */
  protected List<? extends net.sourceforge.czt.typecheck.z.ErrorAnn> lTypecheck(Term term,
                                                SectionManager sectInfo,
                                                boolean recursiveTypes,
                                                boolean sortDeclNames,
                                                boolean useNameIds,
                                                WarningManager.WarningOutput warningOutput,
                                                String sectName)
  {
    
    ZFactory zFactory = new ZFactoryImpl();
    ZEvesFactory zevesFactory = new ZEvesFactoryImpl();
    //((net.sourceforge.czt.z.util.PrintVisitor)((ZFactoryImpl)zFactory).getToStringVisitor()).setPrintIds(true);
    TypeChecker typeChecker = new TypeChecker(
      new net.sourceforge.czt.typecheck.zeves.impl.Factory(zFactory, zevesFactory ),
      sectInfo, recursiveTypes, sortDeclNames);
    typeChecker.setPreamble(sectName, sectInfo);
    typeChecker.setUseNameIds(useNameIds);
    typeChecker.getWarningManager().setWarningOutput(warningOutput);
    
    // For Circus add the type checking robustness at the top-level
    // that means, we have it for both command based and non-command based requests.
    try {
      term.accept(typeChecker);
    }
    catch(net.sourceforge.czt.base.util.UnsupportedAstClassException e)
    {      
      Object[] params = { 
        "An attempt to wrongly cast an AST class has happened.",
        e.getClass().getSimpleName(),
        stackTraceAsString(e) };
      // use any checker to report the error
      net.sourceforge.czt.typecheck.z.ErrorAnn error = 
        typeChecker.proofCommandChecker_.errorAnn(term, net.sourceforge.czt.typecheck.zeves.ErrorMessage.UNEXPECTED_EXCEPTION_ERROR, params);
      ((List<net.sourceforge.czt.typecheck.z.ErrorAnn>)typeChecker.errors()).add(error);
      System.err.println("UNEXPECTED_EXCEPTION_ERROR!");
      e.printStackTrace();
    }
    catch(net.sourceforge.czt.util.CztException f)
    {
      Object[] params = { 
        "A general CztException has happened.",
        f.getClass().getSimpleName(),
        stackTraceAsString(f) };
      // use any checker to report the error
      ErrorAnn error = typeChecker.proofCommandChecker_.errorAnn(term, net.sourceforge.czt.typecheck.zeves.ErrorMessage.UNEXPECTED_EXCEPTION_ERROR, params);
      ((List<net.sourceforge.czt.typecheck.z.ErrorAnn>)typeChecker.errors()).add(error);
      System.err.println("UNEXPECTED_EXCEPTION_ERROR!");
      f.printStackTrace();
    }
    catch(Throwable t)
    {
      Object[] params = { 
        "A general Throwable exception has happened.",
        t.getClass().getSimpleName(),
        stackTraceAsString(t) };
      // use any checker to report the error
      ErrorAnn error = typeChecker.proofCommandChecker_.errorAnn(term, net.sourceforge.czt.typecheck.zeves.ErrorMessage.UNEXPECTED_EXCEPTION_ERROR, params);
      ((List<net.sourceforge.czt.typecheck.z.ErrorAnn>)typeChecker.errors()).add(error);
      System.err.println("UNEXPECTED_EXCEPTION_ERROR!");
      t.printStackTrace();
    }
    List<net.sourceforge.czt.typecheck.z.ErrorAnn> errors = new ArrayList<net.sourceforge.czt.typecheck.z.ErrorAnn>();
    errors.addAll(typeChecker.errors());
    for(ErrorAnn err : typeChecker.getWarningManager().warnErrors())
    {
      errors.add(err);
    }
    return errors;
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
    return "zevestypecheck";
  }

  protected boolean printBenchmarkTimesDefault()
  {
    return true;
  }
  
  protected boolean printTypesDefault()
  {
    return true;
  }
  
  protected void printTerm(Term term, StringWriter writer, SectionManager sectInfo, String sectName, Markup markup)  
  {
    //PrintUtils.print(term, writer, sectInfo, sectName, markup);
    super.printTerm(term, writer, sectInfo, sectName, markup);
  }
  
  public static void main(String[] args)
    throws IOException, net.sourceforge.czt.base.util.UnmarshalException
  {    
    instance_.run(args);
    //instance_.typeCheckCommandTest(args[0]);
  }
  
  private void typeCheckCommandTest(String file)
  {
    System.out.println("Testing TypeCheckCommand for CIRCUS:");

    SimpleFormatter sfc = new SimpleFormatter(false, true, false, false);
    //boolean showTimeStamp, boolean showRecordedMessage,
    //            boolean showSourceMethod, boolean showDirectory, boolean showStackTrace)
     
    java.util.logging.ConsoleHandler ch = new java.util.logging.ConsoleHandler();
    ch.setLevel(java.util.logging.Level.ALL);        
    ch.setFormatter(sfc);       
    java.util.logging.FileHandler fh = null;
    try{
      fh = new java.util.logging.FileHandler("TypeCheckUtils.TypeCheckCommandTest.log");
      fh.setLevel(java.util.logging.Level.ALL);
      fh.setFormatter(sfc);          
    } catch (IOException e) {

    }
    SectionManager manager = new SectionManager("zeves");
    
    java.util.logging.Logger logger = java.util.logging.Logger.getLogger(manager.getClass().getName());    
    logger.addHandler(ch);
    logger.addHandler(fh);
    logger.setLevel(java.util.logging.Level.ALL);
    
    try{
      Spec spec = (Spec)instance_.parse(file, manager);
      for (net.sourceforge.czt.z.ast.Sect s : spec.getSect())
      {
        if (s instanceof ZSect)
        {
          ZSect zs = (ZSect)s;          
          SectTypeEnvAnn result = manager.get(new net.sourceforge.czt.session.Key<SectTypeEnvAnn>(zs.getName(), SectTypeEnvAnn.class));
          break;
        }
      }
    }
    catch(Throwable e)
    {
      throw new RuntimeException(e);
    }
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

  protected SectionManager getSectionManager()
  {
    SectionManager sectionManager = new SectionManager("zeves");
    sectionManager.putCommand(Spec.class, ParseUtils.getCommand());
    sectionManager.putCommand(ZSect.class, ParseUtils.getCommand());
    sectionManager.putCommand(LatexMarkupFunction.class,
                              ParseUtils.getCommand());
    sectionManager.putCommand(SectTypeEnvAnn.class, TypeCheckUtils.getCommand());
    return sectionManager;
  }

  /** @return a Jaxb writer for Circus. */
  protected JaxbXmlWriter getJaxbXmlWriter()
  {
    return new net.sourceforge.czt.zeves.jaxb.JaxbXmlWriter();
  } 
}