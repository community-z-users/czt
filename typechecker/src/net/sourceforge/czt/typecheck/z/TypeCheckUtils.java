/*
  Copyright (C) 2004 Petra Malik
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
import java.util.List;
import java.util.Iterator;

import net.sourceforge.czt.z.jaxb.*;
import net.sourceforge.czt.util.*;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.session.*;
import net.sourceforge.czt.z.ast.ZFactory;
import net.sourceforge.czt.z.impl.ZFactoryImpl;
import net.sourceforge.czt.parser.z.*;
import net.sourceforge.czt.parser.util.*;
import net.sourceforge.czt.typecheck.util.typingenv.*;

/**
 * Utilities for typechecking Z specifications.
 *
 * @author Petra Malik, Tim Miller
 */
public final class TypeCheckUtils
{
  /**
   * Do not generate instances of this class.
   */
  private TypeCheckUtils()
  {
  }

  /**
   * Typecheck and type annotate a file.
   * @param term the term to typecheck.
   * @return the list of ErrorAnns in the AST added by the typechecker.
   */
  public static List typecheck(Term term,
                               SectionInfo sectInfo,
                               ErrorFactory errorFactory,
                               SectTypeEnv sectTypeEnv)
  {
    ZFactory zFactory = new ZFactoryImpl();
    TypeChecker typeChecker =
      new TypeChecker(zFactory, sectTypeEnv, errorFactory, sectInfo);
    typeChecker.visitTerm(term);
    return typeChecker.errors();
  }

  public static List typecheck(Term term,
                               SectionInfo sectInfo,
                               SectTypeEnv sectTypeEnv)
  {
    return typecheck(term, sectInfo,
                     new DefaultErrorFactory(sectInfo), sectTypeEnv);
  }

  public static List typecheck(Term term,
                               SectionInfo sectInfo,
                               ErrorFactory errorFactory)
  {
    return typecheck(term, sectInfo, errorFactory, new SectTypeEnv());
  }

  public static List typecheck(Term term,
                               SectionInfo sectInfo)
  {
    return typecheck(term, sectInfo,
                     new DefaultErrorFactory(sectInfo), new SectTypeEnv());
  }

  public static void main(String[] args)
    throws ParseException, FileNotFoundException
  {
    if (args.length == 0) {
      System.err.println("usage: typechecker filename");
      return;
    }

    for (int i = 0; i < args.length; i++) {
      //parse the file
      String fileName = args[i];
      SectionManager manager = new SectionManager();
      Term term = null;
      if (fileName.endsWith(".error")) {
        term = ParseUtils.parseLatexFile(fileName, manager);
      }
      else {
        term = ParseUtils.parse(fileName, manager);
      }

      //if the parse succeeded, typecheck the term
      if (term != null) {
        SectTypeEnv sectTypeEnv = new SectTypeEnv();
        List errors = TypeCheckUtils.typecheck(term, manager, sectTypeEnv);

        //print any errors
        for (Iterator iter = errors.iterator(); iter.hasNext(); ) {
          Object next = iter.next();
          System.err.println(next.toString());
        }
      }
    }
  }
}
