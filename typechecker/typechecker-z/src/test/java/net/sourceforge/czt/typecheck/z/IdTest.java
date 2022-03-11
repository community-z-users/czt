/*
  Copyright (C) 2006 Petra Malik
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

import java.util.*;

import junit.framework.Test;
import junit.framework.TestCase;
import junit.framework.TestSuite;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.visitor.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.util.ZString;
import net.sourceforge.czt.z.visitor.*;
import net.sourceforge.czt.session.*;
import net.sourceforge.czt.util.Section;

/**
 * A JUnit test class for testing the typechecker. This reads any
 * files not ending with a "_" from the directory tests/z.
 *
 * If the file ends with ".error", then the test reads everything up
 * to the first "-" and that is the name of the error constant.
 *
 * If the file does not end in ".error" or "_", then no error is
 * expected.
 *
 * @author Tim Miller
 */
public class IdTest
  extends TestCase
{
  //the section manager
  protected SectionManager manager_;

  //allow use before declaration
  protected boolean recursiveTypes_ = false;

  public static Test suite()
  {
    TestSuite suite = new TestSuite();
    suite.addTestSuite(IdTest.class);
    return suite;
  }

  @Override
  protected void setUp()
  {
    manager_ = new SectionManager(Dialect.Z);
  }

  @Override
  protected void tearDown()
  {
    //do nothing?
  }

  protected Term parseAndTypecheck(String spec)
    throws Exception
  {
    Source source = new StringSource(spec);
    source.setMarkup(Markup.LATEX);
    manager_.put(new Key<Source>(source.getName(), Source.class), source);
    Term term = manager_.get(new Key<Spec>(source.getName(), Spec.class));
    manager_.get(new Key<SectTypeEnvAnn>(Section.ANONYMOUS.getName(), SectTypeEnvAnn.class));
    return term;
  }

  public void test1()
    throws Exception
  {
    String spec =
      "\\begin{zed}" +
      "  S == [ x : \\nat | x < 4 ] \\\\" +
      "  T == S \\land [x:\\nat | x = 1]" +
      "\\end{zed}";
    Term term = parseAndTypecheck(spec);
    NameCollector visitor = new NameCollector("x");
    term.accept(visitor);
    List<String> list = visitor.getResult();
    assertEquals(6, list.size());
    String firstSig = list.get(0);
    String firstDeclName = list.get(1);
    String firstRefName = list.get(2);
    assertTrue(firstSig.equals(firstDeclName));
    assertTrue(firstSig.equals(firstRefName));
    String secondSig = list.get(3);
    String secondDeclName = list.get(4);
    String secondRefName = list.get(5);
    assertTrue(secondSig.equals(secondDeclName));
    assertTrue(secondSig.equals(secondRefName));
    assertFalse(firstSig.equals(secondSig));
    visitor = new NameCollector("S");
    term.accept(visitor);
    list = visitor.getResult();
    assertEquals(3, list.size());
    assertTrue(list.get(0).equals(list.get(1)));
    assertTrue(list.get(1).equals(list.get(2)));
  }

  public void test2()
    throws Exception
  {
    String spec =
      "\\begin{zed}" +
      "  S == [ x : \\nat | x < 4 ] \\\\" +
      "  T == [S | x = 1]" +
      "\\end{zed}";
    Term term = parseAndTypecheck(spec);
    NameCollector visitor = new NameCollector("x");
    term.accept(visitor);
    List<String> list = visitor.getResult();
    assertEquals(5, list.size());
    String firstSig = list.get(0);
    String firstDeclName = list.get(1);
    String firstRefName = list.get(2);
    assertTrue(firstSig.equals(firstDeclName));
    assertTrue(firstSig.equals(firstRefName));
    String secondSig = list.get(3);
    String secondRefName = list.get(4);
    assertTrue(secondSig.equals(secondRefName));
    assertFalse(firstSig.equals(secondSig));
  }

  public void test3()
    throws Exception
  {
    String spec =
      "\\begin{zed}" +
      "   F[\\arithmos] == (\\arithmos, 3)" +
      "\\end{zed}";
    Term term = parseAndTypecheck(spec);
    NameCollector visitor = new NameCollector(ZString.ARITHMOS);
    term.accept(visitor);
    List<String> list = visitor.getResult();
    assertEquals(5, list.size());
    String first = list.get(0);
    assertTrue(first.equals(list.get(1)));
    assertFalse(first.equals(list.get(2)));
    assertTrue(first.equals(list.get(3)));
    assertTrue(first.equals(list.get(4)));
  }

  public void test4()
    throws Exception
  {
    String spec =
      "\\begin{zed}" +
      "    S == \\{ x:\\arithmos | x > 0 \\land x < 3 \\}" +
      "\\end{zed}";
    Term term = parseAndTypecheck(spec);
    NameCollector visitor = new NameCollector("x");
    term.accept(visitor);
    List<String> list = visitor.getResult();
    assertEquals(3, list.size());
    String first = list.get(0);
    assertTrue(first.equals(list.get(1)));
    assertTrue(first.equals(list.get(2)));
  }

  public void test5()
    throws Exception
  {
    String spec =
      "\\begin{zed}" +
      "    S == [x:\\nat | x > 0] \\land [x:\\arithmos | x < 3]" +
      "\\end{zed}";
    Term term = parseAndTypecheck(spec);
    NameCollector visitor = new NameCollector("x");
    term.accept(visitor);
    List<String> list = visitor.getResult();
    assertEquals(5, list.size());
    String first = list.get(0);
    assertTrue(first.equals(list.get(1)));
    assertTrue(first.equals(list.get(2)));
    assertTrue(first.equals(list.get(3)));
    assertTrue(first.equals(list.get(4)));
  }
    
  public void test6() throws Exception
  {
    net.sourceforge.czt.typecheck.z.impl.Factory factory = new net.sourceforge.czt.typecheck.z.impl.Factory();    
    
    net.sourceforge.czt.z.util.ZUtils.assertZPrintVisitor(
      net.sourceforge.czt.z.util.ZUtils.assertZFactoryImpl(
        factory.getZFactory()).getToStringVisitor()).setPrintIds(true);
    
    //factory.createInStroke();
    java.util.List<net.sourceforge.czt.z.ast.ZName> list = factory.list(
      factory.createZDeclName("x"), 
      factory.createZDeclName("y"), 
      factory.createZDeclName("a"),
      factory.createZDeclName("x", factory.createZStrokeList(factory.list(factory.createNumStroke(0)))),
      factory.createZDeclName("x", factory.createZStrokeList(factory.list(factory.createInStroke()))),
      factory.createZDeclName("b"), 
      factory.createZDeclName("c"));
    
    java.util.List<net.sourceforge.czt.z.ast.ZName> list2 = factory.list(
      factory.createZName("d"), 
      factory.createZName("z"), 
      factory.createZName("x"),
      factory.createZName("x", factory.createZStrokeList(factory.list(factory.createNumStroke(9)))),
      factory.createZName("x", factory.createZStrokeList(factory.list(factory.createNumStroke(0)))),
      factory.createZName("x", factory.createZStrokeList(factory.list(factory.createOutStroke()))),
      factory.createZName("b", factory.createZStrokeList(factory.list(factory.createNumStroke(2)))),
      factory.createZName("c"));
    
    //    System.out.println("\n\nList of names BEFORE sorting : " + list);
    list = net.sourceforge.czt.z.util.ZUtils.sortNames(list);
    //    System.out.println("\nList of names AFTER sorting  : " + list);
    //    System.out.println("\nNow lets insert              : " + list2);    
    net.sourceforge.czt.z.util.ZUtils.insertNames(list, list2);
    //    System.out.println("\nList of names AFTER inserting: " + list);    
  }

  public static class NameCollector
    implements TermVisitor<Object>,
               ZNameVisitor<Object>
  {
    private List<String> list_ = new ArrayList<String>();
    private String name_;

    public NameCollector(String name)
    {
      name_ = name;
    }

    public List<String> getResult()
    {
      return list_;
    }

    @Override
    public Object visitTerm(Term term)
    {
      if (term instanceof AxPara) {
    	SignatureAnn sig = term.getAnn(SignatureAnn.class);
    	if (sig != null)
    		VisitorUtils.visitTerm(this, sig);
      }
      VisitorUtils.visitTerm(this, term);
      return null;
    }

    @Override
    public Object visitZName(ZName zName)
    {
      if (zName.getWord().equals(name_)) list_.add(zName.getId());
      return null;
    }
  }
}
