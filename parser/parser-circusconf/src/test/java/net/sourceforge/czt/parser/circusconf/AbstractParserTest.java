/*
 * AbstractParserTest.java
 *
 * Created on 02 February 2007, 11:51
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package net.sourceforge.czt.parser.circusconf;

import java.io.File;
import java.io.FileOutputStream;
import java.io.InputStream;
import java.io.OutputStreamWriter;
import java.io.UnsupportedEncodingException;
import java.io.Writer;
import java.net.URL;
import java.net.URLDecoder;
import java.util.ArrayList;
import java.util.List;
import java.util.logging.Level;

import junit.framework.TestCase;
import junit.framework.TestSuite;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.visitor.TermVisitor;
import net.sourceforge.czt.base.visitor.VisitorUtils;
import net.sourceforge.czt.circus.util.PrintVisitor;
import net.sourceforge.czt.circusconf.jaxb.JaxbXmlReader;
import net.sourceforge.czt.circusconf.jaxb.JaxbXmlWriter;
import net.sourceforge.czt.parser.circus.ParseErrorLogging;
import net.sourceforge.czt.session.Dialect;
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
  // true => looks into tests/circusconf/debug/*.tex;
  // false=> looks into tests/circusconf/*.tex
  protected static boolean DEBUG_TESTING = false; // true;
  
  // true => executes the printing tests, which will reparse and print files.
  protected final static boolean VERBOSE = false;
  protected static Level DEBUG_LEVEL = DEBUG_TESTING ? Level.FINEST : VERBOSE ? Level.WARNING : Level.SEVERE;
  protected static List<String> TESTS_SOURCEDIR = new ArrayList<String>();
  protected static final ParseErrorLogging pel_;
  protected static final ParseErrorLogging pelsm_;
  
  static {          
      File shouldDebug = new File("src/test/resources/tests/circusconf/debug-please");      
      try{
        if (VERBOSE)
        {
            System.out.println("shouldDebug? \n path = " + shouldDebug.getPath()
          + "\n abs path = " + shouldDebug.getAbsolutePath()
          + "\n can path = " + shouldDebug.getCanonicalPath()
          + " \n exists? = " + shouldDebug.exists());
        }
      }  catch(java.io.IOException e) {  }
      DEBUG_TESTING = shouldDebug.exists();
      if (DEBUG_TESTING) {
        System.out.println("Debug mode is on");
        pel_ = new ParseErrorLogging(Parser.class, DEBUG_LEVEL);
        pelsm_ = new ParseErrorLogging(SectionManager.class, DEBUG_LEVEL);
        TESTS_SOURCEDIR.add("tests/circusconf/debug");
        DEBUG_LEVEL = Level.FINEST;
      } else {
        if (VERBOSE) { System.out.println("Debug mode is off"); }
        TESTS_SOURCEDIR.add("tests/circusconf");
        // If not debugging testing, then do not do logging.
        pel_ = null;
        pelsm_ = null;
        DEBUG_LEVEL = Level.WARNING;
      }
  }
  
  protected final SectionManager manager_ = new SectionManager(Dialect.CIRCUSCONF);
  protected final String lineSeparator_ = System.getProperty("line.separator", "\r\n");
   
  public URL getCircusConfExample(String name)
  {
    URL result = Resources.getCircusConfExample(name);
    if (result == null)
    {
      throw new CztException("Cannot find example " + name);
    }
    return result;
  }
  
  public URL getCircusConfTestExample(String name)
  {
    URL result = getClass().getResource("/tests/circusconf/" + name);
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
    if (VERBOSE) { System.out.println("Parsing " + source); }
    Term term = ParseUtils.parse(source, manager_);    
    if (DEBUG_TESTING && DEBUG_LEVEL.intValue() <= Level.INFO.intValue()) {
        System.out.flush();
        PrintVisitor pv = new PrintVisitor();
        System.out.println("DEBUG: AFTER PARSING, PrintVisitor for " + source);        
        System.out.println(pv.printProcessPara(term));
        System.out.println();
        System.out.println(term);
        System.out.flush();
    }
    return term;
  }
  
  class DeleteLocVisitor implements TermVisitor<Term>
  {
    @Override
	public Term visitTerm(Term term)
    {
      VisitorUtils.visitTerm(this, term);
      LocAnn locAnn = term.getAnn(LocAnn.class);
      if (locAnn != null) locAnn.setLoc(null);
      return null;
    }
  }
  
  public void compareCircusConf(URL url, URL zmlURL)
  throws Exception
  {
    JaxbXmlReader reader = new JaxbXmlReader();
    Visitor<Term> visitor = new DeleteNarrVisitor();
    InputStream zmlStream = zmlURL.openStream();
    Term zmlTerm;
    try {
      zmlTerm = reader.read(zmlStream);
    } finally {
      zmlStream.close();
    }
    Spec zmlSpec = (Spec) zmlTerm.accept(visitor);
    Spec parsedSpec = (Spec) parse(new UrlSource(url)).accept(visitor);
    visitor = new DeleteMarkupParaVisitor();
    parsedSpec = (Spec) parsedSpec.accept(visitor);
    zmlSpec = (Spec) zmlSpec.accept(visitor);
    if (! zmlSpec.equals(parsedSpec))
    {
      String message = "For " + url.toString();
      JaxbXmlWriter xmlWriter = new JaxbXmlWriter();
      File expected = File.createTempFile("cztCircusConfParser", "test.zml");
      Writer out =
          new OutputStreamWriter(new FileOutputStream(expected), "UTF-8");
      xmlWriter.write(zmlSpec, out);
      out.close();
      message += lineSeparator_ + "expected: " + expected.getAbsolutePath();
      File got = File.createTempFile("cztCircusConfParser", "test.zml");
      out = new OutputStreamWriter(new FileOutputStream(got), "UTF-8");
      xmlWriter.write(parsedSpec, out);
      out.close();
      message += lineSeparator_ + "but was:" + got.getAbsolutePath();
      fail(message);
    }
  }
  
  // Tim's directory search structe testing strategy :)
  
  protected abstract void collectTest(TestSuite suite, File file);
  
  protected void collectTests(TestSuite suite, List<String> directoryNames) 
  {
    for(String dirName : directoryNames) {
      collectTests(suite, dirName);
    }
  }
  
  //test all the files from a directory
  private void collectTests(TestSuite suite, String directoryName)
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
    if (VERBOSE) { System.out.println("Full directory name = " + fullDirectoryName); }
    File directory = new File(fullDirectoryName);
    File[] files = null;
    if (! directory.isDirectory())
    {
      URL url = getClass().getResource("/");
      if (url != null) {
        try {
          String urlPath = URLDecoder.decode(url.getFile(), "UTF-8");
          if (VERBOSE) { System.out.println("Looking for tests under: " + urlPath + fullDirectoryName); }
          directory = new File(urlPath + fullDirectoryName);
        } catch (UnsupportedEncodingException e) {
          throw new RuntimeException(e);
        }
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

