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

package net.sourceforge.czt.parser.oz;

import java.io.FileNotFoundException;

import junit.framework.Test;
import junit.framework.TestSuite;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.parser.util.AbstractParserTest;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.util.ParseException;

/**
 * A (JUnit) test class for testing the Z parser.
 *
 * @author Petra Malik
 */
public class ParserTest
  extends AbstractParserTest
{
  public static Test suite()
  {
    return new TestSuite(ParserTest.class);
  }

  /**
   * Example test5.tex cannot be parses with the Object Z parser
   * since the keyword "Init" is used as a schema name.
   */
  public void test5Test()
  {
    try {
      parse(getTestExample("test5.tex"), manager_);
      fail("Should throw ParseException");
    }
    catch(ParseException ok) {
      // we want to end up here
    }
    catch(FileNotFoundException e) {
      fail("Should not throw FileNotFoundException");
    }
  }

  public Term parse(String filename, SectionManager manager)
    throws ParseException, FileNotFoundException
  {
    return ParseUtils.parse(filename, manager_);
  }
}
