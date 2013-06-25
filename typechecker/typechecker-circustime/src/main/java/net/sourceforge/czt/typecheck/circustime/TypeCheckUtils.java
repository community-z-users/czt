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
package net.sourceforge.czt.typecheck.circustime;

import java.io.IOException;
import java.io.StringWriter;
import java.util.ArrayList;
import java.util.List;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.util.PerformanceSettings;
import net.sourceforge.czt.circus.ast.CircusFactory;
import net.sourceforge.czt.circus.impl.CircusFactoryImpl;
import net.sourceforge.czt.circustime.ast.CircusTimeFactory;
import net.sourceforge.czt.circustime.impl.CircusTimeFactoryImpl;
import net.sourceforge.czt.parser.circus.WarningManager;
import net.sourceforge.czt.parser.circustime.ParseUtils;
import net.sourceforge.czt.session.Command;
import net.sourceforge.czt.session.Dialect;
import net.sourceforge.czt.session.FileSource;
import net.sourceforge.czt.session.Markup;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.session.Source;
import net.sourceforge.czt.typecheck.circustime.TypeCheckUtils;
import net.sourceforge.czt.typecheck.circustime.impl.Factory;
import net.sourceforge.czt.z.ast.SectTypeEnvAnn;
import net.sourceforge.czt.z.ast.Spec;
import net.sourceforge.czt.z.ast.ZFactory;
import net.sourceforge.czt.z.ast.ZSect;
import net.sourceforge.czt.z.impl.ZFactoryImpl;
import net.sourceforge.czt.print.circustime.PrintUtils;
import net.sourceforge.czt.print.util.PrintException;


public class TypeCheckUtils 
    extends net.sourceforge.czt.typecheck.circus.TypeCheckUtils {
  
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
  
  
  
  @Override
  protected List<net.sourceforge.czt.typecheck.z.ErrorAnn> lTypecheck(Term term,
                                                SectionManager sectInfo,
                                                boolean recursiveTypes,
                                                boolean sortDeclNames,
                                                boolean useNameIds,
                                                WarningManager.WarningOutput warningOutput,
                                                String sectName)
  {
	ZFactory zFactory = new ZFactoryImpl();
	CircusFactory circusFactory = new CircusFactoryImpl();
    CircusTimeFactory circustimeFactory = new CircusTimeFactoryImpl();    
    Factory factory = new Factory(zFactory, circusFactory, circustimeFactory);
    TypeChecker typeChecker = new TypeChecker(factory,sectInfo, recursiveTypes, sortDeclNames);
    typeChecker.setPreamble(sectName, sectInfo);
    typeChecker.setUseNameIds(useNameIds);
    typeChecker.getWarningManager().setWarningOutput(warningOutput);    
    List<net.sourceforge.czt.typecheck.z.ErrorAnn> errors = new ArrayList<net.sourceforge.czt.typecheck.z.ErrorAnn>(PerformanceSettings.INITIAL_ARRAY_CAPACITY);
    errors.addAll(guardedTypeCheck(typeChecker, term));
    for(net.sourceforge.czt.typecheck.z.ErrorAnn err : typeChecker.getWarningManager().warnErrors())
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
    return "circustimetypecheck";
  }

  protected boolean printBenchmarkTimesDefault()
  {
    return true;
  }
  
  protected boolean printTypesDefault()
  {
    return true;
  }
  
  protected void printTerm(Term term, StringWriter writer, SectionManager sectInfo, String sectName, Markup markup)  throws PrintException
  {
	  // TODO: finish circus time pretty printer!
    //PrintUtils.print(term, writer, sectInfo, sectName, markup);
	  boolean warning;
	  super.printTerm(term, writer, sectInfo, sectName, markup);
  }
  
  
  public static void main(String[] args)
    throws IOException, net.sourceforge.czt.base.util.UnmarshalException
  {    
    instance_.run(args);
  }
  
  @SuppressWarnings("unused")
  protected void typeCheckCommandTest(String file)
  {
    System.out.println("Testing TypeCheckCommand for CIRCUSTIME:");
    
    net.sourceforge.czt.parser.circustime.SpecialLatexParser.SimpleFormatterForCircusTime sfc = 
      new net.sourceforge.czt.parser.circustime.SpecialLatexParser.SimpleFormatterForCircusTime(true, true,
        false, false, true);
    
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
    SectionManager manager = new SectionManager(Dialect.CIRCUSTIME);    
    
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

  protected List<String> toolkits()
  {
    List<String> toolkits = super.toolkits();
    toolkits.add("circustime_prelude");
    toolkits.add("circustime_toolkit");
    return toolkits;
  }
  
    
  protected SectionManager getSectionManager()
  {
    SectionManager sectionManager = new SectionManager(Dialect.CIRCUSTIME);
    sectionManager.putCommand(SectTypeEnvAnn.class, TypeCheckUtils.getCommand());
    sectionManager.setProperties(System.getProperties());
    return sectionManager;
  }
  
  
}
