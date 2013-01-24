/**
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

import junit.framework.Test;
import junit.framework.TestCase;
import junit.framework.TestSuite;

import static net.sourceforge.czt.z.util.ZUtils.*;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.impl.ZFactoryImpl;
import net.sourceforge.czt.z.util.Factory;
import net.sourceforge.czt.parser.z.ParseUtils;
import net.sourceforge.czt.session.*;

import net.sourceforge.czt.typecheck.z.impl.VariableType;
import net.sourceforge.czt.typecheck.testutil.TypeParser;

/**
 * A JUnit test class for testing implicit type inference
 *
 * @author Tim Miller
 */
public class TypeInferenceTest
  extends TestCase
{
  //the SectionManager to pass to the typechecker
  protected SectionManager manager_;

  //the latest parsed spec
  protected Spec spec_;

  //a Factory
  protected Factory factory_;

  public static Test suite()
  {
    TestSuite suite = new TestSuite();
    suite.addTestSuite(TypeInferenceTest.class);
    return suite;
  }

  protected void setUp()
  {
    factory_ = new Factory(new ZFactoryImpl());
    manager_ = new SectionManager(Dialect.Z);
    spec_ = null;
  }

  protected void tearDown()
  {
    //do nothing?
  }

  public void testGivenPara()
    throws Exception
  {
    String para = header() + "\\begin{zed} [A,B] \\end{zed}";
    Spec spec = getSpec(para);
    TypeCheckUtils.typecheck(spec, manager_);

    Type typeA = getType("A");
    Type typeB = getType("B");

    Type expTypeA = parseType("P (GIVEN A)");
    Type expTypeB = parseType("P (GIVEN B)");

    assertTypeEquals("testGivenPara - A", typeA, expTypeA);
    assertTypeEquals("testGivenPara - B", typeB, expTypeB);
  }

  public void testFreePara()
    throws Exception
  {
    //a free type paragraph with mutually recursive types
    String para =
      header() +
      "\\begin{zed}" +
      "A ::= a | aa \\ldata B \\rdata &" +
      "B ::= b | bb \\ldata A \\rdata" +
      "\\end{zed}";
    Spec spec = getSpec(para);
    TypeCheckUtils.typecheck(spec, manager_);

    Type succ [][] =
      {
        {getType("A"), parseType("P (GIVEN A)")},
        {getType("a"), parseType("GIVEN A")},
        {getType("aa"), parseType("P (GIVEN B x GIVEN A)")},
        {getType("B"), parseType("P (GIVEN B)")},
        {getType("b"), parseType("GIVEN B")},
        {getType("bb"), parseType("P (GIVEN A x GIVEN B)")},
      };

    typeTest(succ, "testFreePara");
  }

  public void testAxParaBasicNoGenParamTypes()
    throws Exception
  {
    String para = header() +
      "\\begin{zed} [A] \\end{zed}" +
      "\\begin{axdef}" +
      "a : A\\\\" +
      "b : \\power (A \\cross A)\\\\" +
      "c : \\power [ca : \\power A]\\\\" +
      "\\end{axdef}";
    Spec spec = getSpec(para);
    TypeCheckUtils.typecheck(spec, manager_);

    Type succ [][] =
      {
        {getType("a"), parseType("GIVEN A")},
        {getType("b"), parseType("P (GIVEN A x GIVEN A)")},
        {getType("c"), parseType("P ([ca : P (GIVEN A)])")},
      };

    typeTest(succ, "testAxParaBasicNoGenParamTypes");
  }

  public void testAxParaBasicGenParamTypes()
    throws Exception
  {
    String para = header() +
      "\\begin{gendef}[X,Y]" +
      "a : X\\\\" +
      "b : \\power (X \\cross Y)\\\\" +
      "c : \\power [ca : \\power X]\\\\" +
      "\\end{gendef}";
    Spec spec = getSpec(para);
    TypeCheckUtils.typecheck(spec, manager_);

    Type succ [][] =
      {
        {getType("a"), parseType("\\[X,Y\\] GENTYPE X")},
        {getType("b"), parseType("\\[X,Y\\] P (GENTYPE X x GENTYPE Y)")},
        {getType("c"),
         parseType("\\[X,Y\\] P ([ca : P (GENTYPE X)])")},
      };

    typeTest(succ, "testAxParaBasicGenParamTypes");
  }

  public void testAxParaImplicitNoGenParamTypes()
    throws Exception
  {
    String para = header() +
      "\\begin{zed} [A,B] \\end{zed}\n" +
      "\\begin{zed} g[X] == X \\end{zed}\n" +
      "\\begin{axdef}" +
      "a == g\\\\" +
      "b == \\power g\\\\" +
      "\\where\n" +
      "a \\in \\power A\\\\" +
      "b = \\power B" +
      "\\end{axdef}";
    Spec spec = getSpec(para);
    TypeCheckUtils.typecheck(spec, manager_);

    Type succ [][] =
      {
        {getType("a"), parseType("P GIVEN A")},
        {getType("b"), parseType("P P GIVEN B")},
      };

    typeTest(succ, "testAxParaImplicitNoGenParamTypes");
  }

  public void testAxParaImplicitGenParamTypes()
    throws Exception
  {
    String para = header() +
      "\\begin{zed} g[X] == X \\end{zed}\n" +
      "\\begin{gendef}[Y,Z]" +
      "a : \\power g\\\\" +
      "b == \\power g\\\\" +
      "\\where\n" +
      "a \\in \\power Y\\\\" +
      "b = \\power Z" +
      "\\end{gendef}";
    Spec spec = getSpec(para);
    TypeCheckUtils.typecheck(spec, manager_);

    Type succ [][] =
      {
        {getType("a"), parseType("\\[Y, Z\\] P GENTYPE Y")},
        {getType("b"), parseType("\\[Y, Z\\] P P GENTYPE Z")},
      };

    typeTest(succ, "testAxParaImplicitGenParamTypes");
  }

  protected void typeTest(Type [][] succ, String operation)
  {
    for (int i = 0; i < succ.length; i++) {
      Type actual = succ[i][0];
      Type expected = succ[i][1];

      String message = operation + " - index = " + i;
      assertTypeEquals(message, expected, actual);
    }
  }

  //lookup a type from the SectTypeEnv
  protected Type getType(String word)
  {
    ZName zName = factory_.createZName(word);
    ZSect zSect = (ZSect) spec_.getSect().get(0);
    SectTypeEnvAnn ann = (SectTypeEnvAnn) zSect.getAnn(SectTypeEnvAnn.class);

    for (NameSectTypeTriple triple : ann.getNameSectTypeTriple()) {
      if (namesEqual(zName, triple.getZName())) {
        return triple.getType();
      }
    }
    return null;
  }

  protected Type parseType(String type)
  {
    return TypeParser.getType(type);
  }

  protected void assertTypeEquals(String message, Term termA, Term termB)
  {
    assertTrue(message + "(" + termA + ", " + termB + ")",
	       assertTypeEqualsProxy(termA, termB));
  }

  protected boolean assertTypeEqualsProxy(Term unresolvedTermA, 
					  Term unresolvedTermB)
  {
    Term termA = resolve(unresolvedTermA);
    Term termB = resolve(unresolvedTermB);

    if (termA instanceof ZName) {
      if (termB instanceof ZName) {
	if (namesEqual((ZName) termA, (ZName) termB)) {
	  return true;
	}
      }

      return false;
    }
    else if (termA.getClass().equals(termB.getClass())) {
      Object [] aChildren = termA.getChildren();
      Object [] bChildren = termB.getChildren();
      if (aChildren.length == bChildren.length) {
	for (int i = 0; i < aChildren.length; i++) {
	  if (aChildren[i] instanceof Term &&
	      bChildren[i] instanceof Term) {
	    if (!assertTypeEqualsProxy((Term) aChildren[i], (Term) bChildren[i])) {
	      return false;
	    }
	  }
	}
      }
      return true;
    }

    return false;
  }

  protected Term resolve(Term term)
  {
    Term result = term;
    if (term instanceof VariableType) {
      result = ((VariableType) term).getValue();
    }
    return result;
  }

  //the header for each section
  protected String header()
  {
    String header = "\\begin{zsection} \\SECTION test \\end{zsection}";
    return header;
  }

  protected Spec getSpec(String str)
    throws Exception
  {
    Source source = new StringSource(str);
    source.setMarkup(Markup.LATEX);
    Spec spec = (Spec) ParseUtils.parse(source, manager_);
    spec_ = spec;
    return spec;
  }
}
