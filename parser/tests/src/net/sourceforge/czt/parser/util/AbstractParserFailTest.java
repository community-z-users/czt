/*
  Copyright (C) 2004 Petra Malik
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

import java.io.*;
import java.net.URL;
import java_cup.runtime.*;

import junit.framework.*;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.parser.Examples;
import net.sourceforge.czt.parser.util.ParseException;
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
  protected SectionManager manager_;

  protected void setUp()
  {
    manager_ = new SectionManager();
  }
  
  protected void tearDown()
  {
    manager_ = null;
  }

  public abstract Term parse(URL url, SectionManager manager)
    throws ParseException, IOException;

  private URL getTestExample(String name)
  {
    return Examples.getTestExample(name);
  }

  private void check(URL url)
  {
    try {
      Term term = parse(url, manager_);
      // A return value of null is also acceptable
      if (term == null) return;
      fail("Should throw parse exception!");
    }
    catch (ParseException e) {
      // ok
    }
    catch (IOException e) {
      fail("Should not throw IOException!");
    }
  }

  public void testInvalidOperatorWord()
  {
    check(getTestExample("invalidOperatorWord.tex"));
  }

  public void testInvalidOperatorWord2()
  {
    check(getTestExample("invalidOperatorWord2.tex"));
  }

  public void testInvalidOperatorWord3()
  {
    check(getTestExample("invalidOperatorWord3.tex"));
  }

  public void testInvalidOperatorWord4()
  {
    check(getTestExample("invalidOperatorWord4.tex"));
  }

  public void testInvalidOperator1()
  {
    check(getTestExample("invalidOperator1.tex"));
  }

  public void testInvalidOperator2()
  {
    check(getTestExample("invalidOperator2.tex"));
  }

  public void testInvalidOperator3()
  {
    check(getTestExample("invalidOperator3.tex"));
  }

  public void testInvalidOperator4()
  {
    check(getTestExample("invalidOperator4.tex"));
  }
}
