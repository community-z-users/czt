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
                               ErrorFactory errorFactory)
  {
    ZFactory zFactory = new ZFactoryImpl();
    TypeChecker typeChecker =
      new TypeChecker(zFactory, errorFactory, sectInfo);
    typeChecker.visitTerm(term);
    return typeChecker.errors();
  }

  public static List typecheck(Term term,
                               SectionInfo sectInfo)
  {
    return typecheck(term, sectInfo, new DefaultErrorFactory(sectInfo));
  }

  public static void main(String[] args)
    throws FileNotFoundException
  {
    if (args.length == 0) {
      System.err.println("usage: typechecker [-s] filename ...");
      System.exit(0);
    }

    List<String> files = new java.util.ArrayList<String>();
    boolean typecheck = true;

    for (int i = 0; i < args.length; i++) {
      if ("-s".equals(args[i])) {
        typecheck = false;
      }
      else {
        files.add(args[i]);
      }
    }

    int result = 0;
    SectionManager manager = new SectionManager();
    for (String file : files) {
      //parse the file
      Term term = null;
      try {
        if (file.endsWith(".error")) {
          term = ParseUtils.parseLatexFile(file, manager);
        }
        else {
          term = ParseUtils.parse(file, manager);
        }
      }
      catch (net.sourceforge.czt.parser.util.ParseException exception) {
        exception.printErrorList();
      }

      //if the parse succeeded, typecheck the term
      if (term != null && typecheck) {
        List errors = TypeCheckUtils.typecheck(term, manager);

        //print any errors
        for (Object next : errors) {
          System.err.println(next);
          result = -1;
        }
      }
    }

    System.exit(result);
  }
}
