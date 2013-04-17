/*
  Copyright (C) 2004, 2006 Petra Malik
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

package net.sourceforge.czt.parser.util;

import java.net.URL;

import junit.framework.*;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.parser.Examples;
import net.sourceforge.czt.parser.util.ParseException;
import net.sourceforge.czt.session.Dialect;
import net.sourceforge.czt.session.SectionManager;

/**
 * A (JUnit) test class for testing the parser.
 * This class contains tests where the parser is supposed to fail,
 * i.e. to throw an exception.
 *
 * @author Petra Malik
 */
public abstract class AbstractParserFailTest
  extends TestCase
{
  private SectionManager manager_;

  protected SectionManager getManager()
  {
	  if (manager_ == null)
	  {
		  manager_ = new SectionManager(getDialect());
	  }
	  return manager_;
  }
  
  protected void setUp()
  {
    getManager().reset();
    getManager().putCommands(getDialect());
  }

  public abstract Term parse(URL url, SectionManager manager)
    throws Exception;
  
  protected abstract Dialect getDialect();

  private URL getTestExample(String name)
  {
    return Examples.getTestExample(name);
  }

  private void check(URL url)
    throws Exception
  {
    try {
      Term term = parse(url, getManager());
      // A return value of null is also acceptable
      if (term == null) return;
      fail("Should throw parse exception!");
    }
    catch (ParseException e) {
      // ok
    }
  }

  public void testInvalidOperatorWord()
    throws Exception
  {
    check(getTestExample("invalidOperatorWord.tex"));
  }

  public void testInvalidOperatorWord2()
    throws Exception
  {
    check(getTestExample("invalidOperatorWord2.tex"));
  }

  public void testInvalidOperatorWord3()
    throws Exception
  {
    check(getTestExample("invalidOperatorWord3.tex"));
  }

  public void testInvalidOperatorWord4()
    throws Exception
  {
    check(getTestExample("invalidOperatorWord4.tex"));
  }

  public void testInvalidOperator1()
    throws Exception
  {
    check(getTestExample("invalidOperator1.tex"));
  }

  public void testInvalidOperator2()
    throws Exception
  {
    check(getTestExample("invalidOperator2.tex"));
  }

  public void testInvalidOperator3()
    throws Exception
  {
    check(getTestExample("invalidOperator3.tex"));
  }

  public void testInvalidOperator4()
    throws Exception
  {
    check(getTestExample("invalidOperator4.tex"));
  }
}
