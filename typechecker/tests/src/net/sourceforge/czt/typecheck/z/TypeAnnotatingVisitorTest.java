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

import java.io.IOException;
import java.util.Iterator;
import java.util.List;
import java.util.ArrayList;

import junit.framework.Test;
import junit.framework.TestCase;
import junit.framework.TestSuite;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.impl.ZFactoryImpl;
import net.sourceforge.czt.parser.z.ParseUtils;

import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.typecheck.util.typingenv.SectTypeEnv;

import net.sourceforge.czt.typecheck.testutil.TypeParser;

/**
 * A JUnit test class for testing the Z type annotating visitor
 *
 * @author Tim Miller
 */
public class TypeAnnotatingVisitorTest
  extends TestCase
{
  //the SectTypeEnv to pass to the TypeAnnotatingVisitor
  SectTypeEnv sectTypeEnv_;

  //the SectionManager to pass to the TypeAnnotatingVisitor
  protected SectionManager manager_;

  //the TypeAnnotatingVisitor that we are testing
  protected TypeAnnotatingVisitor visitor_;

  //a ZFactory
  protected ZFactory factory_ = new ZFactoryImpl();

  public static Test suite()
  {
    TestSuite suite = new TestSuite();
    suite.addTestSuite(TypeAnnotatingVisitorTest.class);
    return suite;
  }

  protected void setUp()
  {
    manager_ = new SectionManager();
    sectTypeEnv_ = new SectTypeEnv();
    visitor_ = new TypeAnnotatingVisitor(sectTypeEnv_, manager_);
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
    spec.accept(visitor_);

    Type typeA = getType("A");
    Type typeB = getType("B");

    Type expTypeA = parseType("P (GIVEN A)");
    Type expTypeB = parseType("P (GIVEN B)");

    assertEquals("testGivenPara - A", typeA, expTypeA);
    assertEquals("testGivenPara - B", typeB, expTypeB);
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
    spec.accept(visitor_);

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
    spec.accept(visitor_);

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
    spec.accept(visitor_);

    Type succ [][] =
      {
        {getType("a"), parseType("\\[X,Y\\] GENTYPE X")},
        {getType("b"), parseType("\\[X,Y\\] P (GENTYPE X x GENTYPE Y)")},
        {getType("c"),
         parseType("\\[X,Y\\] P ([ca : \\[X,Y\\] P (GENTYPE X)])")},
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
    spec.accept(visitor_);

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
    spec.accept(visitor_);

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
      assertEquals(message, expected, actual);
    }
  }

  //lookup a type from the SectTypeEnv
  protected Type getType(String word)
  {
    DeclName declName = factory_.createDeclName(word, list(), null);
    return sectTypeEnv_.getType(declName);
  }

  protected Type parseType(String type)
  {
    return TypeParser.getType(type);
  }

  //the header for each section
  protected String header()
  {
    String header = "\\begin{zsection} \\SECTION tests \\end{zsection}";
    return header;
  }

  protected Spec getSpec(String str)
    throws Exception
  {
    return (Spec) ParseUtils.parseLatexString(str, manager_);
  }

  protected static List list()
  {
    return new ArrayList();
  }
}
