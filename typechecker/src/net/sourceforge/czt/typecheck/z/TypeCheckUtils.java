
package net.sourceforge.czt.typecheck.z;

import java.io.*;
import java.util.List;

import net.sourceforge.czt.util.*;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.session.SectionInfo;
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
}
