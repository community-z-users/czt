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

package net.sourceforge.czt.parser.circusconf;

import java.io.*;

import java.util.logging.Level;

import junit.framework.*;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.session.FileSource;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.util.CztLogger;
import net.sourceforge.czt.circusconf.jaxb.JaxbXmlWriter;

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
    if (VERBOSE) { System.out.println("Number of successful tests to run: " + suite.countTestCases()); }
    return suite;
  }
  
  @Override
  protected void collectTest(TestSuite suite, File file)
  {    
    String fileName = file.getName();
    if (fileName.indexOf("-errors") == -1 && fileName.endsWith(".tex"))
    {
      suite.addTest(createTestCase(file.getAbsolutePath()));
    }
  }
  
  protected TestNormal createTestCase(String name) {
      return new TestNormal(name);
  }
  
  private JaxbXmlWriter writer_ = new JaxbXmlWriter();
  
  protected class TestNormal extends TestCase
  {
    private String file_;
    private Term term_;    
    
    protected TestNormal(String file)
    {
      file_ = file;
      term_ = null;
    }
    
    protected String getFile() {
        return file_;
    }
    
    protected Term getTerm() {
        return term_;
    }
    
    protected void innerTest() {
        try
      {
        term_ = parse(new FileSource(file_));
        if (term_ == null)
        {
          fail("Parser returned null (i.e., parsing error)");
        }
        else
        { 
          if (VERBOSE) { System.out.println("Parsing successful, start XML printing..."); }
          String xmlFile;
          if (file_.lastIndexOf(".") != -1)
            xmlFile = file_.substring(0, file_.lastIndexOf(".")) + ".xml";
          else
            xmlFile = file_ + ".xml";
          File f = new File(xmlFile);
          f.delete();
          FileWriter fw = new FileWriter(f);          
          writer_.write(term_, fw);          
          fw.close();          
        }
      }
      catch (net.sourceforge.czt.parser.util.ParseException f)
      {
        printCauses(f);
        fail(lineSeparator_ + "Unexpected parser exception" +
            lineSeparator_ + "\tFile: " + file_ +
            lineSeparator_ + "\tException: " + f.toString());
        f.printErrorList();        
      }
      catch (RuntimeException e)
      {
        printCauses(e);
        fail(lineSeparator_ + "Unexpected runtime exception" +
            lineSeparator_ + "\tFile: " + file_ +
            lineSeparator_ + "\tException: " + e.toString());                
      }
      catch (Throwable e)
      {        
        printCauses(e);
        fail(lineSeparator_ + "Unexpected exception" +
            lineSeparator_ + "\tFile: " + file_ +
            lineSeparator_ + "\tException: " + e.toString());        
      }
    }
    
    @Override
    public void runTest()
    {      
      innerTest();
    }
  }
}
