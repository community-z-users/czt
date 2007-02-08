/*
  Copyright (C) 2004, 2006 Leo Freitas
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

package net.sourceforge.czt.parser.circus;

import java.io.*;

import java.util.logging.Level;

import junit.framework.*;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.session.FileSource;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.util.CztLogger;

/**
 * A (JUnit) test class for testing the Z parser.
 *
 * @author Leo Freitas
 */
public class ParserTest extends AbstractParserTest
{
  public static Test suite()
  {
    CztLogger.getLogger(SectionManager.class).setLevel(Level.OFF);
    TestSuite suite = new TestSuite();
    ParserTest parserTests = new ParserTest();
    parserTests.collectTests(suite, TESTS_SOURCEDIR);        
    return suite;
  }
  
  protected void collectTest(TestSuite suite, File file)
  {    
    String fileName = file.getName();
    if (fileName.indexOf("-error") == -1 && fileName.endsWith(".tex"))
    {
      suite.addTest(new TestNormal(file.getAbsolutePath()));
    }
  }
  
  class TestNormal extends TestCase
  {
    private String file_;
    
    TestNormal(String file)
    {
      file_ = file;
    }
    
    public void runTest()
    {
      try
      {
        Term term = parse(new FileSource(file_));
        if (term == null)
        {
          fail("Parser returned null (i.e., parsing error)");
        }
      }
      catch (net.sourceforge.czt.parser.util.ParseException f)
      {
        f.printStackTrace();
        fail(lineSeparator_ + "Unexpected parser exception" +
            lineSeparator_ + "\tFile: " + file_ +
            lineSeparator_ + "\tException: " + f.toString());
        f.printErrorList();
      }
      catch (RuntimeException e)
      {
        e.printStackTrace();
        fail(lineSeparator_ + "Unexpected runtime exception" +
            lineSeparator_ + "\tFile: " + file_ +
            lineSeparator_ + "\tException: " + e.toString());
      }
      catch (Throwable e)
      {
        e.printStackTrace();
        fail(lineSeparator_ + "Unexpected exception" +
            lineSeparator_ + "\tFile: " + file_ +
            lineSeparator_ + "\tException: " + e.toString());
      }
    }
  }
}
