/**
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
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.util.ParseException;

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
  protected SectionManager manager_ = new SectionManager();

  public abstract Term parse(URL url, SectionManager manager)
    throws ParseException, IOException;

  private URL getTestExample(String name)
  {
    return Examples.getTestExample(name);
  }

  public void testInvalidOperatorWord()
  {
    try {
      parse(getTestExample("invalidOperatorWord.tex"), manager_);
      fail("Should throw parse exception!");
    }
    catch (ParseException e) {
      // ok
    }
    catch (IOException e) {
      fail("Should not throw IOException!");
    }
  }

  public void testInvalidOperatorWord2()
  {
    try {
      parse(getTestExample("invalidOperatorWord2.tex"), manager_);
      fail("Should throw parse exception!");
    }
    catch (ParseException e) {
      // ok
    }
    catch (IOException e) {
      fail("Should not throw IOException!");
    }
  }

  public void testInvalidOperatorWord3()
  {
    try {
      parse(getTestExample("invalidOperatorWord3.tex"), manager_);
      fail("Should throw parse exception!");
    }
    catch (ParseException e) {
      // ok
    }
    catch (IOException e) {
      fail("Should not throw IOException!");
    }
  }

  public void testInvalidOperatorWord4()
  {
    try {
      parse(getTestExample("invalidOperatorWord4.tex"), manager_);
      fail("Should throw parse exception!");
    }
    catch (ParseException e) {
      // ok
    }
    catch (IOException e) {
      fail("Should not throw IOException!");
    }
  }

  public void testInvalidOperator1()
  {
    try {
      parse(getTestExample("invalidOperator1.tex"), manager_);
      fail("Should throw parse exception!");
    }
    catch (ParseException e) {
      // ok
    }
    catch (IOException e) {
      fail("Should not throw IOException!");
    }
  }

  public void testInvalidOperator2()
  {
    try {
      parse(getTestExample("invalidOperator2.tex"), manager_);
      fail("Should throw parse exception!");
    }
    catch (ParseException e) {
      // ok
    }
    catch (IOException e) {
      fail("Should not throw IOException!");
    }
  }
}
