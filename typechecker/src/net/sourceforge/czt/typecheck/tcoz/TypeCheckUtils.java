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
package net.sourceforge.czt.typecheck.tcoz;

import java.io.*;
import java.util.List;

import net.sourceforge.czt.util.*;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.session.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.impl.ZFactoryImpl;
import net.sourceforge.czt.oz.ast.OzFactory;
import net.sourceforge.czt.oz.impl.OzFactoryImpl;
import net.sourceforge.czt.tcoz.ast.TcozFactory;
import net.sourceforge.czt.tcoz.impl.TcozFactoryImpl;
import net.sourceforge.czt.parser.tcoz.*;
import net.sourceforge.czt.parser.util.*;
import net.sourceforge.czt.typecheck.z.ErrorAnn;

/**
 * Utilities for typechecking TCOZ specifications.
 *
 * @author Petra Malik, Tim Miller
 */
public class TypeCheckUtils
  extends net.sourceforge.czt.typecheck.oz.TypeCheckUtils
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
   * @param sectInfo the <code>SectionInfo</code> object to use.
   * @param markup the <code>Markup</code> of the specification.
   * returns the list of ErrorAnns in the AST added by the typechecker.
   */
  public static List<? extends ErrorAnn> typecheck(Term term,
					 SectionInfo sectInfo,
					 Markup markup)
  {
    TypeCheckUtils utils = new TypeCheckUtils();
    return utils.lTypecheck(term, sectInfo, markup, false);
  }

  /**
   * Typecheck and type annotate a file.
   * @param term the <code>Term</code> to typecheck.
   * @param sectInfo the <code>SectionInfo</code> object to use.
   * @param markup the <code>Markup</code> of the specification.
   * @param useBeforeDecl allow use of variables before declaration
   * returns the list of ErrorAnns in the AST added by the typechecker.
   */
  public static List<? extends ErrorAnn> typecheck(Term term,
					 SectionInfo sectInfo,
					 Markup markup,
					 boolean useBeforeDecl)
  {
    TypeCheckUtils utils = new TypeCheckUtils();
    return utils.lTypecheck(term, sectInfo, markup, useBeforeDecl);
  }

  public static List<? extends ErrorAnn> typecheck(Term term,
					 SectionInfo sectInfo,
					 Markup markup,
					 boolean useBeforeDecl,
					 boolean useStrongTyping)
  {
    TypeCheckUtils utils = new TypeCheckUtils();
    return utils.lTypecheck(term,
                            sectInfo,
                            markup,
                            useBeforeDecl,
                            useStrongTyping);
  }

  protected List<? extends ErrorAnn> lTypecheck(Term term,
				      SectionInfo sectInfo,
				      Markup markup,
				      boolean useBeforeDecl)
  {
    return lTypecheck(term, sectInfo, markup, useBeforeDecl, false);
  }

  protected List<? extends ErrorAnn> lTypecheck(Term term,
				      SectionInfo sectInfo,
				      Markup markup,
				      boolean useBeforeDecl,
				      boolean useStrongTyping)
  {
    ZFactory zFactory = new ZFactoryImpl();
    OzFactory ozFactory = new OzFactoryImpl();
    TcozFactory tcozFactory = new TcozFactoryImpl();
    TypeChecker typeChecker = new TypeChecker(zFactory,
                                              ozFactory,
					      tcozFactory,
                                              sectInfo,
                                              markup,
                                              useBeforeDecl,
                                              useStrongTyping);
    typeChecker.visitTerm(term);
    return typeChecker.errors();
  }

  protected List<? extends ErrorAnn> lTypecheck(Term term,
				      SectionInfo sectInfo,
				      Markup markup)
  {
    return lTypecheck(term, sectInfo, markup, false);
  }

  protected Term parse(Source src, SectionInfo sectInfo)
    throws IOException, net.sourceforge.czt.parser.util.ParseException
  {
    return ParseUtils.parse(src, sectInfo);
  }

  protected Term parse(String file, SectionInfo sectInfo)
    throws IOException, net.sourceforge.czt.parser.util.ParseException
  {
    return ParseUtils.parse(file, sectInfo);
  }

  protected String name()
  {
    return "tcoztypecheck";
  }

  protected SectionManager getSectionManager()
  {
    SectionManager sectionManager = new SectionManager();
    sectionManager.putCommand(Spec.class, ParseUtils.getCommand());
    sectionManager.putCommand(ZSect.class, ParseUtils.getCommand());
    sectionManager.putCommand(LatexMarkupFunction.class,
			      ParseUtils.getCommand());
    return sectionManager;
  }

  public static void main(String[] args)
    throws IOException
  {
    TypeCheckUtils utils = new TypeCheckUtils();
    utils.run(args);
  }
}
