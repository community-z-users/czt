/*
  Copyright (C) 2006, 2007 Leo Freitas, Manuela Xavier
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
package net.sourceforge.czt.typecheck.circus;

import java.io.IOException;
import java.util.List;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.circus.ast.CircusFactory;
import net.sourceforge.czt.circus.impl.CircusFactoryImpl;
import net.sourceforge.czt.circus.jaxb.JaxbXmlWriter;
import net.sourceforge.czt.circus.util.Factory;
import net.sourceforge.czt.parser.circus.ParseUtils;
import net.sourceforge.czt.parser.util.LatexMarkupFunction;
import net.sourceforge.czt.session.Command;
import net.sourceforge.czt.session.FileSource;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.session.Source;
import net.sourceforge.czt.typecheck.z.ErrorAnn;
import net.sourceforge.czt.z.ast.SectTypeEnvAnn;
import net.sourceforge.czt.z.ast.Spec;
import net.sourceforge.czt.z.ast.ZFactory;
import net.sourceforge.czt.z.ast.ZSect;
import net.sourceforge.czt.z.impl.ZFactoryImpl;

/**
 *
 * @author Leo Freitas, Manuela Xavier
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
    return typecheck(term, sectInfo, useBeforeDecl, false, null);
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
                                                   boolean useBeforeDecl,
                                                   boolean sortDeclNames)
  {
    return typecheck(term, sectInfo, useBeforeDecl, sortDeclNames, null);
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
                                                   boolean sortDeclNames,
                                                   String sectName)
  {    
    return instance_.lTypecheck(term, sectInfo, useBeforeDecl, sortDeclNames, false, sectName);
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
                                                   boolean sortDeclNames,
                                                   boolean useNameIds)
  {    
    return instance_.lTypecheck(term, sectInfo, useBeforeDecl, sortDeclNames, useNameIds, null);
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
                                                   boolean sortDeclNames,
                                                   boolean useNameIds,
                                                   String sectName)
  {    
    return instance_.lTypecheck(term, sectInfo, useBeforeDecl, sortDeclNames, useNameIds, sectName);
  }
  
  /** An internal method of the typechecker. */
  protected List<? extends ErrorAnn> lTypecheck(Term term,
                                                SectionManager sectInfo,
                                                boolean useBeforeDecl,
                                                boolean sortDeclNames,
                                                boolean useNameIds,
                                                String sectName)
  {
    ZFactory zFactory = new ZFactoryImpl();
    CircusFactory circusFactory = new CircusFactoryImpl();    
    //((net.sourceforge.czt.z.util.PrintVisitor)((ZFactoryImpl)zFactory).getToStringVisitor()).setPrintIds(true);
    TypeChecker typeChecker = new TypeChecker(
      new net.sourceforge.czt.typecheck.circus.impl.Factory(zFactory, circusFactory ), 
      sectInfo, useBeforeDecl, sortDeclNames);
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
    return "circustypecheck";
  }

  protected boolean printBenchmarkTimesDefault()
  {
    return true;
  }
  
  public static void main(String[] args)
    throws IOException, net.sourceforge.czt.base.util.UnmarshalException
  {    
    instance_.run(args);
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
    toolkits.add("circus_prelude");
    toolkits.add("circus_toolkit");
    return toolkits;
  }

  protected SectionManager getSectionManager()
  {
    SectionManager sectionManager = new SectionManager();
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
    return new net.sourceforge.czt.circus.jaxb.JaxbXmlWriter();
  }  
}
