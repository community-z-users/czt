
package net.sourceforge.czt.typecheck.z;

import java.io.*;
import java.util.List;
import java.util.Iterator;

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
      Term term = ParseUtils.parse(fileName, manager);

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
