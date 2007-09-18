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
import net.sourceforge.czt.parser.circus.ParseUtils;
import net.sourceforge.czt.parser.util.LatexMarkupFunction;
import net.sourceforge.czt.session.Command;
import net.sourceforge.czt.session.FileSource;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.session.Source;
import net.sourceforge.czt.typecheck.circus.impl.Factory;
import net.sourceforge.czt.typecheck.z.TypeCheckCommand;
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
  
  private static final TypeCheckUtils utils_ = new TypeCheckUtils();
  
  protected TypeCheckUtils() {
  }
  
  /**
   * Typecheck and type annotate a file.
   * @param term the <code>Term</code> to typecheck.
   * @param sectInfo the <code>SectionManager</code> object to use.
   * returns the list of ErrorAnns in the AST added by the typechecker.
   */
  public static List<? extends ErrorAnn> typecheck(Term term,
      SectionManager sectInfo) {
    return typecheck(term, sectInfo, utils_.useBeforeDeclDefault());
  }
  
  /**
   * Typecheck and type annotate a file.
   * @param term the <code>Term</code> to typecheck.
   * @param sectInfo the <code>SectionManager</code> object to use.
   * @param useBeforeDecl allow use of variables before declaration
   * returns the list of ErrorAnns in the AST added by the typechecker.
   */
  public static List<? extends ErrorAnn> typecheck(Term term,
      SectionManager sectInfo,
      boolean useBeforeDecl) {
    return utils_.lTypecheck(term, sectInfo, useBeforeDecl, null);
  }  

  public static void main(String[] args)
    throws IOException, net.sourceforge.czt.base.util.UnmarshalException
  {    
    utils_.run(args);
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

  /** An internal method of the typechecker. */
  /** An internal method of the typechecker. */
  protected List<? extends ErrorAnn> lTypecheck(Term term,
                                                SectionManager sectInfo,
                                                boolean useBeforeDecl,
                                                String sectName)
  {
    ZFactory zFactory = new ZFactoryImpl();
    CircusFactory circusFactory = new CircusFactoryImpl();
    TypeChecker typeChecker = new TypeChecker(new Factory(zFactory, circusFactory),
                                              sectInfo,
                                              useBeforeDecl);
    typeChecker.setPreamble(sectName, sectInfo);
    typeChecker.visitTerm(term);
    return typeChecker.errors();
  }
  
  protected Term parse(Source src, SectionManager sectInfo)
    throws IOException, net.sourceforge.czt.parser.util.ParseException,
           net.sourceforge.czt.base.util.UnmarshalException
  {
    try {
      return ParseUtils.parse(src, sectInfo);
    }
    catch (net.sourceforge.czt.base.util.UnmarshalException ex) {
      throw new RuntimeException(ex);
    }
  }

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

  protected List<String> toolkits()
  {
    List<String> toolkits = super.toolkits();
    toolkits.add("circus_toolkit");
    return toolkits;
  }

  protected boolean useBeforeDeclDefault()
  {
    return true;
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
  
  protected static Command getCommand() {
    return new net.sourceforge.czt.typecheck.circus.TypeCheckCommand();
  }
}
