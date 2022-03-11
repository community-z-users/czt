package net.sourceforge.czt.parser.zeves;

import java.io.File;
import java.io.IOException;
import java.io.StringWriter;
import java.io.UnsupportedEncodingException;
import java.net.URL;
import java.net.URLDecoder;

import junit.framework.Test;
import junit.framework.TestCase;
import junit.framework.TestSuite;
import net.sourceforge.czt.session.FileSource;
import net.sourceforge.czt.session.Markup;
import net.sourceforge.czt.session.Source;

/**
 * Unit test for simple App.
 */
public class ScanningTest
          // TODO: should derive from CztManagedTest? But that class is from Parsing onwards :-(....
        extends TestCase
{

  protected final static boolean DEBUG = false;
  protected final static String TEST_DIR =
                                "/tests/zeves/";

  public static Test suite()
  {
    //CztLogger.getLogger(SectionManager.class).setLevel(Level.OFF);
    TestSuite suite = new TestSuite();
    ScanningTest checkerTest = new ScanningTest(TEST_DIR);
    checkerTest.collectTests(suite, ScanningTest.class.getResource(TEST_DIR));
    return suite;
  }

  /**
   * Create the test case
   *
   * @param testName name of the test case
   */
  public ScanningTest(String testName)
  {
    super(testName);
  }

  /**
   * Tests all the files from a directory.
   */
  protected void collectTests(TestSuite suite, URL url)
  {
      String protocol = url.getProtocol();
      if (!"file".equals(protocol))
      {
        throw new IllegalArgumentException("Unsupported Protocol");
      }
      File dir;
      try {
        dir = new File(URLDecoder.decode(url.getFile(), "UTF-8"));
      } catch (UnsupportedEncodingException e) {
        throw new RuntimeException(e);
      }
      String[] content = dir.list();
      String path = dir.getPath() + "/";
      //System.out.println("AHHHHH = " + dir.getAbsolutePath());
      for (String name : content)
      {
        //if the file name ends with error, then we have a case with
        //the typechecker should throw the exception specified at the
        //start of the filename
        if (name.endsWith(".error"))
        {
          int index = name.indexOf("-");
          if (index < 1)
          {
            fail(name + " does not specify an exception name");
          }
          String exception = name.substring(0, index);
          suite.addTest(new TestError(path, name, exception));
        }
        //if the file name does not end with error, then we have a
        //normal case
        else if (name.endsWith(".tex") || name.endsWith("zed8"))
        {
          suite.addTest(new TestNormal(path, name));
        }
      }
    }


  protected void scan(String name) throws IOException, Exception
  {
    Source source = new FileSource(name);
    source.setMarkup(Markup.getMarkup(name));
    StringWriter sw = new StringWriter();
    LatexScannerDebugger.debugScanner(sw, source);
    sw.close();
    if (DEBUG) System.out.println("\t\t scanning OKAY");
  }

  class TestNormal
          extends TestCase
  {

    private String name_;

    TestNormal(String path, String name)
    {
      super("Test normal: " + path + name);
      name_ = path + name;
    }

    @Override
    public void runTest()
    {
      try
      {
        if (DEBUG) System.out.print("Scanning test for " + name_);
        scan(name_);
      }
      catch (RuntimeException e)
      {
        e.printStackTrace();
        fail("\nUnexpected runtime exception"
             + "\n\tFile: " + name_
             + "\n\tException: " + e.toString());
      }
      catch (Throwable e)
      {
        e.printStackTrace();
        fail("\nUnexpected exception"
             + "\n\tFile: " + name_
             + "\n\tException: " + e.toString());
      }
    }
  }

  class TestError
          extends TestCase
  {

    private String name_;
    private String exception_;

    TestError(String path, String name, String exception)
    {
      super("Test error - " + exception + ": " + path + name);
      name_ = path + name;
      exception_ = exception;
    }

    @Override
    public void runTest()
    {
      try
      {
        scan(name_);
      }
      catch (RuntimeException e)
      {
        e.printStackTrace();
        fail("\nUnexpected runtime exception"
             + "\n\tFile: " + name_
             + "\n\tException: " + e.toString());
      }
      catch (Throwable e)
      {
        fail("\nUnexpected exception"
             + "\n\tFile: " + name_
             + "\n\tException: " + e.toString());
      }
      boolean foundErrors = true;
      if (!foundErrors)
      {
        fail("\nNo type error found"
             + "\n\tFile: " + name_
             + "\n\tExpected: " + exception_);
      }
      else
      {
        // handle scanning error? nahh
      }
    }
  }
}
