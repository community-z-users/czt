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

import java.io.*;
import java.util.*;

import junit.framework.Test;
import junit.framework.TestCase;
import junit.framework.TestSuite;

import net.sourceforge.czt.util.CztLogger;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.visitor.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.impl.ZFactoryImpl;
import net.sourceforge.czt.z.visitor.*;
import net.sourceforge.czt.parser.z.ParseUtils;

import net.sourceforge.czt.session.*;
import net.sourceforge.czt.typecheck.z.util.SectTypeEnv;

import net.sourceforge.czt.typecheck.testutil.TypeParser;

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
  protected boolean useBeforeDecl_ = false;

  public static Test suite()
  {
    TestSuite suite = new TestSuite();
    suite.addTestSuite(IdTest.class);
    return suite;
  }

  protected void setUp()
  {
    manager_ = new SectionManager();
  }

  protected void tearDown()
  {
    //do nothing?
  }

  protected Term parseAndTypecheck(String spec)
    throws Exception
  {
    Source source = new StringSource(spec);
    source.setMarkup(Markup.LATEX);
    manager_.put(new Key(source.getName(), Source.class), source);
    Term term = (Term) manager_.get(new Key(source.getName(), Spec.class));
    manager_.get(new Key("Specification", SectTypeEnvAnn.class));
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
    System.out.println(visitor.getResult());
  }

  public void test2()
    throws Exception
  {
    String spec =
      "\\begin{zed}" +
      "  S == [ x : \\nat | x < 4 ] \\\\" +
      "  T == [S | S]" +
      "\\end{zed}";
    Term term = parseAndTypecheck(spec);
    NameCollector visitor = new NameCollector("x");
    term.accept(visitor);
    System.out.println(visitor.getResult());
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

    public Object visitTerm(Term term)
    {
      if (term instanceof AxPara) {
        list_.add("new AxPara");
        VisitorUtils.visitTerm(this, term.getAnn(SignatureAnn.class));
        list_.add("end Signature");
      }
      VisitorUtils.visitTerm(this, term);
      return null;
    }

    public Object visitZName(ZName zName)
    {
      if (zName.getWord().equals(name_)) list_.add(zName.getId());
      return null;
    }
  }
}
