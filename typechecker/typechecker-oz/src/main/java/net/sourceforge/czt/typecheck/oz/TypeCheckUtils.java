/*
  Copyright (C) 2004, 2005 Petra Malik
  Copyright (C) 2004, 2005 Tim Miller
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
package net.sourceforge.czt.typecheck.oz;

import java.io.*;
import java.util.List;

import net.sourceforge.czt.base.jaxb.BaseJaxbXmlWriter;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.session.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.impl.ZFactoryImpl;
import net.sourceforge.czt.oz.ast.OzFactory;
import net.sourceforge.czt.oz.impl.OzFactoryImpl;
import net.sourceforge.czt.parser.oz.*;
import net.sourceforge.czt.typecheck.oz.impl.Factory;
import net.sourceforge.czt.typecheck.z.ErrorAnn;
import net.sourceforge.czt.z.util.WarningManager;

/**
 * Utilities for typechecking Object-Z specifications.
 *
 * @author Petra Malik, Tim Miller
 */
public class TypeCheckUtils
  extends net.sourceforge.czt.typecheck.z.TypeCheckUtils
{
  /**
   * Do not generate instances of this class.
   */
  protected TypeCheckUtils()
  {
  }

  /**
   * Typecheck and type annotate a file.
   * @param term the <code>Term</code> to typecheck.
   * @param sectInfo the <code>SectionManager</code> object to use.
   * returns the list of ErrorAnns in the AST added by the typechecker.
   */
  public static List<? extends ErrorAnn> typecheck(Term term,
                                                   SectionManager sectInfo)
  {
    return typecheck(term, sectInfo, true, false);
  }

  /**
   * Typecheck and type annotate a file.
   * @param term the <code>Term</code> to typecheck.
   * @param sectInfo the <code>SectionManager</code> object to use.
   * @param recursiveTypes allow use of recursive types.
   * returns the list of ErrorAnns in the AST added by the typechecker.
   */
  public static List<? extends ErrorAnn> typecheck(Term term,
                                                   SectionManager sectInfo,
                                                   boolean recursiveTypes)
  {
    return typecheck(term, sectInfo, recursiveTypes, false);
  }

  public static List<? extends ErrorAnn> typecheck(Term term,
                                                   SectionManager sectInfo,
                                                   boolean recursiveTypes,
                                                   boolean useStrongTyping)
  {
    net.sourceforge.czt.typecheck.oz.TypeCheckUtils utils = new TypeCheckUtils();
    return utils.lTypecheck(term, sectInfo, PROP_TYPECHECK_USE_BEFORE_DECL_DEFAULT, 
                            recursiveTypes, false, useStrongTyping, null, null);
  }

  public static List<? extends ErrorAnn> typecheck(Term term,
                                                   SectionManager sectInfo,
						   boolean useBeforeDecl,
                                                   boolean recursiveTypes,
                                                   boolean sortDeclNames,
						   boolean useStrongTyping,
						   WarningManager.WarningOutput warningOutput,
						   String sectName)
  {
    net.sourceforge.czt.typecheck.oz.TypeCheckUtils utils = new TypeCheckUtils();
    return utils.lTypecheck(term, sectInfo, useBeforeDecl, recursiveTypes, sortDeclNames,
    		                useStrongTyping, warningOutput, sectName);
  }
  
  /** An internal method of the typechecker. */
  protected List<? extends ErrorAnn> lTypecheck(Term term,
                                                SectionManager sectInfo,
						boolean useBeforeDecl,
                                                boolean recursiveTypes,
                                                boolean sortDeclNames,
						WarningManager.WarningOutput warningOutput,
                                                String sectName)
  {
    net.sourceforge.czt.typecheck.oz.TypeCheckUtils utils = new TypeCheckUtils();
    return utils.lTypecheck(term, sectInfo, useBeforeDecl, recursiveTypes, sortDeclNames,
    		                false, warningOutput, sectName);
  }

  /** An internal method of the typechecker. */
  protected List<? extends ErrorAnn> lTypecheck(Term term,
                                                SectionManager sectInfo,
						boolean useBeforeDecl,
                                                boolean recursiveTypes,
                                                boolean sortDeclNames,
						boolean useStrongTyping,
						WarningManager.WarningOutput warningOutput,
                                                String sectName)
  {
    ZFactory zFactory = new ZFactoryImpl();
    OzFactory ozFactory = new OzFactoryImpl();
    TypeChecker typeChecker = new TypeChecker(new Factory(zFactory, ozFactory),
                                              sectInfo,
					      useBeforeDecl,
                                              recursiveTypes,
					      sortDeclNames,
                                              useStrongTyping);
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
    return "oztypecheck";
  }

  protected List<String> toolkits()
  {
    List<String> toolkits = super.toolkits();
    toolkits.add("oz_toolkit");
    return toolkits;
  }

  protected boolean recursiveTypesDefault()
  {
    return true;
  }

  protected SectionManager getSectionManager()
  {
    SectionManager sectionManager = new SectionManager(Dialect.OZ);
    sectionManager.putCommand(SectTypeEnvAnn.class, TypeCheckUtils.getCommand());
    sectionManager.setProperties(System.getProperties());
    return sectionManager;
  }

  /** @return a Jaxb writer for Object-Z. */
  protected BaseJaxbXmlWriter getJaxbXmlWriter()
  {
    return new net.sourceforge.czt.oz.jaxb.JaxbXmlWriter();
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
