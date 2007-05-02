/*
 * AbstractParserTest.java
 *
 * Created on 02 February 2007, 11:51
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package net.sourceforge.czt.parser.circus;

import java.io.File;
import java.io.FileOutputStream;
import java.io.OutputStreamWriter;
import java.io.Writer;
import java.net.URL;
import java.util.logging.Level;
import junit.framework.Assert;
import junit.framework.TestCase;
import junit.framework.TestSuite;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.visitor.TermVisitor;
import net.sourceforge.czt.base.visitor.VisitorUtils;
import net.sourceforge.czt.circus.jaxb.JaxbXmlReader;
import net.sourceforge.czt.circus.jaxb.JaxbXmlWriter;
import net.sourceforge.czt.circus.util.PrintVisitor;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.session.Source;
import net.sourceforge.czt.session.UrlSource;
import net.sourceforge.czt.util.CztException;
import net.sourceforge.czt.util.Visitor;
import net.sourceforge.czt.z.ast.LocAnn;
import net.sourceforge.czt.z.ast.Spec;
import net.sourceforge.czt.z.util.DeleteMarkupParaVisitor;
import net.sourceforge.czt.z.util.DeleteNarrVisitor;
import net.sourceforge.czt.zml.Resources;

/**
 *
 * @author leo
 */
public abstract class AbstractParserTest extends TestCase
{
  protected static boolean DEBUG_TESTING = true;
  protected static Level DEBUG_LEVEL = Level.FINE;
  protected static String TESTS_SOURCEDIR = (DEBUG_TESTING ? "tests/circus/debug" : "tests/circus");  

  protected static final ParseErrorLogging pel_ = new ParseErrorLogging(Parser.class, DEBUG_LEVEL);
  protected static final ParseErrorLogging pelsm_ = new ParseErrorLogging(SectionManager.class, DEBUG_LEVEL);
  
  protected final SectionManager manager_ = new SectionManager();
  protected final String lineSeparator_ = System.getProperty("line.separator", "\r\n");
   
  public URL getCircusExample(String name)
  {
    URL result = Resources.getCircusExample(name);
    if (result == null)
    {
      throw new CztException("Cannot find example " + name);
    }
    return result;
  }
  
  public URL getCircusTestExample(String name)
  {
    URL result = getClass().getResource("/tests/circus/" + name);
    if (result == null)
    {
      throw new CztException("Cannot find example " + name);
    }
    return result;
  }
  
  protected SectionManager getSectionManager() {
      return manager_;
  }
  
  protected Term parse(Source source) throws Exception
  {
    Term term = ParseUtils.parse(source, manager_);
    if (DEBUG_TESTING) {
        System.out.flush();
        //PrintVisitor pv = new PrintVisitor();
        System.out.println("DEBUG: AFTER PARSING, PrintVisitor for " + source);        
        //System.out.println(pv.printProcessPara(term));
        //System.out.println();
        System.out.println(term);
        System.out.flush();
    }
    return term;
  }
  
  class DeleteLocVisitor implements TermVisitor
  {
    public Object visitTerm(Term term)
    {
      VisitorUtils.visitTerm(this, term);
      LocAnn locAnn = (LocAnn) term.getAnn(LocAnn.class);
      if (locAnn != null) locAnn.setLoc(null);
      return null;
    }
  }
  
  public void compareCircus(URL url, URL zmlURL)
  throws Exception
  {
    JaxbXmlReader reader = new JaxbXmlReader();
    Visitor visitor = new DeleteNarrVisitor();
    Spec zmlSpec = (Spec) reader.read(zmlURL.openStream()).accept(visitor);
    Spec parsedSpec = (Spec) parse(new UrlSource(url)).accept(visitor);
    visitor = new DeleteMarkupParaVisitor();
    parsedSpec = (Spec) parsedSpec.accept(visitor);
    zmlSpec = (Spec) zmlSpec.accept(visitor);
    if (! zmlSpec.equals(parsedSpec))
    {
      String message = "For " + url.toString();
      JaxbXmlWriter xmlWriter = new JaxbXmlWriter();
      File expected = File.createTempFile("cztCircusParser", "test.zml");
      Writer out =
          new OutputStreamWriter(new FileOutputStream(expected), "UTF-8");
      xmlWriter.write(zmlSpec, out);
      out.close();
      message += lineSeparator_ + "expected: " + expected.getAbsolutePath();
      File got = File.createTempFile("cztCircusParser", "test.zml");
      out = new OutputStreamWriter(new FileOutputStream(got), "UTF-8");
      xmlWriter.write(parsedSpec, out);
      out.close();
      message += lineSeparator_ + "but was:" + got.getAbsolutePath();
      fail(message);
    }
  }
  
  // Tim's directory search structe testing strategy :)
  
  protected abstract void collectTest(TestSuite suite, File file);
  
  //test all the files from a directory
  protected void collectTests(TestSuite suite, String directoryName)
  {
    String cztHome = System.getProperty("czt.home");
    //System.out.println("CZT-HOME = " + cztHome);
    if (cztHome == null || cztHome.length() == 0)
    {
      cztHome = manager_.getProperty("czt.path");
      //System.out.println("CZT-PATH = " + cztHome);
      if (cztHome == null) { cztHome = ""; }
    }
    String fullDirectoryName = cztHome + directoryName;
    System.out.println("Full directory name = " + fullDirectoryName);
    File directory = new File(fullDirectoryName);
    File[] files = null;
    if (! directory.isDirectory())
    {
      URL url = getClass().getResource("/");
      if (url != null) {
        System.out.println("Looking for tests under: " + url.getFile() + fullDirectoryName);
        directory = new File(url.getFile() + fullDirectoryName);        
        if (! directory.isDirectory()) {
          System.out.println("No tests to perform on " + directory.getAbsolutePath());            
        } else {
            files = directory.listFiles();
        }       
      } else {
        fail("Could not retrieve a valid testing set under " + directory.getAbsolutePath());
      }
    } else {
        files = directory.listFiles();
    }
    if (files != null) {
        for (File file : files)
        {
          collectTest(suite, file);
        }    
    }
  }
  
  protected void printCauses(Throwable e) {
      e.printStackTrace();
      if (e.getCause() != null) printCauses(e.getCause());
  }
}

