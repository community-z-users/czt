/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package net.sourceforge.czt.parser.util;

import java.io.File;
import java.io.IOException;
import java.net.URL;
import junit.framework.Test;
import junit.framework.TestCase;
import junit.framework.TestSuite;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.FileSource;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.Markup;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.session.Source;
import net.sourceforge.czt.session.SourceLocator;
import net.sourceforge.czt.util.CztException;
import net.sourceforge.czt.z.ast.Spec;

/**
 * <p>
 * Throughout CZT, various testing infrastructures are similar. For example,
 * various type checkers use directory structures for testing resources that
 * need management. On those, there are certain common functionality, which
 * was spread/repeated in various places. This class aims at collecting them
 * for cohesion / reuse. This includes debugging and logging facilities, as
 * well as proper section management protocols.
 * </p>
 * <p>
 * This class is meant for tools above the parser that depend on resource-based
 * testing. It contains both positive (e.g., normal) and negative (e.g., erroneous)
 * test cases.
 * </p>
 *
 * @author Leo
 */
public abstract class CztManagedTest extends TestCase
{

  /* MODEL EXAMPLE
   *
  public static Test suite()
  {
    CztManagedTest test = new CztManagedTest("z", DEBUG_TESTING);
    return test.suite("", null);
  }
   *
   */

  public static final Markup DEFAULT_MARKUP = Markup.LATEX;

  private final SectionManager manager_;
  
  /**
   * Default Markup for file tests 
   */
  private Markup markup_;

  private boolean debug_;

  private String testsPath_;

  /**
   * Creates a new test case with a fresh section manager and given extension
   * @param extension usually "z" or "circus"
   * @param debug true or false
   */
  protected CztManagedTest(String extension, boolean debug)
  {
    this(new SectionManager(extension), debug);
  }
  
  /**
   * Creates a test case with given (shared) section manager and debug flag. 
   * @param manager given
   * @param debug 
   */
  protected CztManagedTest(SectionManager manager, boolean debug)
  {
    if (manager == null)
      throw new IllegalArgumentException("Null section manager for test case");
    manager_ = manager;
    manager_.setTracing(debug);
    markup_ = DEFAULT_MARKUP;
    debug_ = debug;
    testsPath_ = "./";
  }

  /**
   * Section manager tracing protocol: logs finest messages
   * @param msg
   */
  protected void traceLog(String msg)
  {
    manager_.getLogger().finest(msg);
  }

  /**
   * Section manager tracing protocol: logs info messages
   * @param msg
   */
  protected void traceInfo(String msg)
  {
    manager_.getLogger().info(msg);
  }

  protected SectionManager getManager()
  {
    return manager_;
  }

  protected boolean isDebugging()
  {
    return debug_;
  }

  protected void setMarkup(Markup x)
  {
    markup_ = x;
  }

  protected Markup getMarkup()
  {
    return markup_;
  }

  /**
   * Create a test suite by looking at all file resources within the given
   * relative test directory. It looks into this class (dynamic) resources
   * available (e.g., within a jar file, say). The resulting test suite can
   * be exposes in a state suite() method as usual in jUnit.
   * @param relativeTestDirectory
   * @param negativeTestExceptionClass
   * @return
   */
  public Test suite(String relativeTestDirectory,
          Class<? extends Throwable> negativeTestExceptionClass)
  {
    TestSuite suite = new TestSuite();
    try
    {
      collectTests(suite, getClass().getResource(relativeTestDirectory), negativeTestExceptionClass);
    }
    catch (IOException e)
    {
      throw new CztException("CZT-TEST-IOERROR = " + relativeTestDirectory, e);
    }
    return suite;
  }

  protected void testing(Spec term)
  {
    // do nothing.
  }

  protected void encounteredException(Throwable e, String failureMsg, boolean handled)
  {
    // do nothing
  }

  protected String getTestsPath()
  {
    return testsPath_;
  }

  protected void createSource(URL url)
  {
    final String sourceData = url.getFile();
    final String sourceName = SourceLocator.getSourceName(sourceData);
    //if (isDebugging())
    //{
      System.out.println("createSource = " + sourceName + ", " + sourceData);
    //}
    Source source = new FileSource(sourceData);
    source.setMarkup(Markup.getMarkup(sourceData)); // extract the right markup
    getManager().put(new Key<Source>(sourceName, Source.class), source);
  }

  /**
   * Parses the given URL as a Spec term. It also adds the <code>UrlSource</code>
   * to the section manager as this is important for calculating certain structures.
   * @param url
   * @return
   * @throws CommandException
   */
  protected Spec parse(URL url) throws CommandException
  {
    traceLog("CZT-TEST-PARSE " + url);
    createSource(url);
    try
    {
      return manager_.get(new Key<Spec>(getSourceName(url), Spec.class));
    }
    catch (CommandException e)
    {
      traceInfo("CZT-TEST-ERROR = " +
              (e.getCause() != null ? e.getCause().getMessage() : e.getMessage()));
      throw e;
    }
  }

  protected String getSourceName(URL url)
  {
    return SourceLocator.getSourceName(url.getFile());
  }

  protected void setCZTPath()
  {
    String localcztpath = manager_.getProperty("czt.path");
    if (localcztpath == null || localcztpath.isEmpty())
    {
      localcztpath = testsPath_;
    }
    else if (localcztpath.indexOf(testsPath_) == -1)
    {
      localcztpath += File.pathSeparator + testsPath_;
    }
    manager_.setProperty("czt.path", localcztpath);
    if (debug_)
    {
      System.out.println("test.path= " + testsPath_);
      System.out.println("czt.path = " + localcztpath);
    }
  }

  /**
   * <p>
   * Tests all the files from a directory given as a URL. It creates positive test
   * cases for all files of known markup (e.g., .tex, .zml, etc. [see Markup.getMarkup()].
   * It creates negative test cases for all files ending with ".error". 
   * </p>
   * <p>
   * Negative test cases are guided by the file name and given exception class.
   * The naming convention is: "./dir/ErrorText-filename.error". That is, if given
   * URL has ".error" ending and the given Throwable <code>expCls</code> is raised
   * during testing, the test case will look for ErrorText in the raised message.
   * If found, then that is a successful negative test. For instance, the Z type
   * checker uses Java resource names as error strings, say DUPLICATE_IN_BIND_EXPR.
   * So, a file URL "./dir/DuplicateInBindExpr-myerror-1.error" will be successful
   * if the type checker finds a "DUPLICATE_IN_BIND_EXPR" as part of the file name
   * with extension ".error", yet prior to the first "-" separator. ErrorText should
   * be as simple as possible. The only processing we do is to remove underscores,
   * and ignore case / locale sensitivity.
   * </p>
   *
   * @param suite
   * @param url
   * @param expCls
   * @throws IOException
   */
  protected void collectTests(TestSuite suite, URL url,
          Class<? extends Throwable> expCls) throws IOException
  {
    traceLog("CZT-TEST-COLLECT = " + url);
    String protocol = url.getProtocol();
    if (!"file".equals(protocol))
    {
      throw new IllegalArgumentException("Unsupported Protocol");
    }
    final File dir = new File(url.getFile());
    if (debug_)
    {
      manager_.getLogger().info("Looking for test files under " + dir);
    }
    if (!dir.isDirectory())
    {
      throw new IOException("Given resource is not a relative directory - " + dir);
    }
    testsPath_ = dir.toString();
    setCZTPath();
    String[] content = dir.list();
    for (String name : content)
    {
      //if the file name ends with error, then we have a case with
      //the typechecker should throw the exception specified at the
      //start of the filename
      if (includeTest(name, false))
      {
        int index = name.indexOf("-");
        if (index < 1)
        {
          fail(name + " does not specify an exception name");
        }
        String exception = name.substring(0, index);
        suite.addTest(createNegativeTest(new URL(url, name), exception, expCls));
      }
      //if the file name does not end with error, then we have a
      //normal case
      else if (includeTest(name, true))
      {
        suite.addTest(createPositiveTest(new URL(url, name)));
      }
    }
  }

  /**
   *
   * @param sourceName name of test file
   * @param positive or negative test flag
   * @return true if name is to be included for testing
   */
  protected boolean includeTest(String sourceName, boolean positive)
  {
    if (positive)
      return hasKnownSuffixes(sourceName);
    else
      return sourceName.endsWith(".error");
  }

  protected boolean hasKnownSuffixes(String sourceName)
  {
    for(String suffix : Markup.KNOWN_FILENAME_SUFFIXES)
    {
      if (sourceName.endsWith(suffix))
      {
        return true;
      }
    }
    return false;
  }

  protected TestCase createPositiveTest(URL url)
  {
    return new TestNormal(url);
  }

  protected abstract TestCase createNegativeTest(URL url, String exception, Class<?> expCls);

  /**
   * Abstract managed test case class
   */
  protected abstract class AbstractManagedTest extends TestCase
  {

    protected final URL url_;

    protected AbstractManagedTest(URL url)
    {
      url_ = url;
    }

    protected URL getURL()
    {
      return url_;
    }

    protected String getSourceName()
    {
      return CztManagedTest.this.getSourceName(url_);
    }

    /**
     * Logs what kind of this is this on the given URL, parses the URL and
     * call user-defined test code. If an exception is raised, stack trace
     * might be printed when debugging, and further user-exception test code is called.
     */
    @Override
    public void runTest()
    {
      Spec term = null;
      try
      {
        // log
        final String msg = "CZT-" + getClass().getSimpleName() + " = " + url_;
        traceLog(msg);
        // parse
	      term = parse(url_);
        if (term == null)
        {
          fail("CZT-TEST = parser returned null");
        }
        // give the user a chance
        doTest(term);
      }
      catch (Throwable e)
      {
        // TODO: ,make this a template
        StringBuilder msg = new StringBuilder();
        msg.append("\nUnexpected exception").append(
                   "\n\tFile     : ").append(url_).append(
                   "\n\tException: ").append(e.toString()).append(
                   "\n\tCause    : ").append(String.valueOf(e.getCause()));
        // should we report failure?
        if (!handledException(e, msg))
        {
          // do so, verbosily or not
          if (debug_)
          {
            e.printStackTrace();
          }
          fail(msg.toString());
        }
        else
        {
          msg.append("\n EXPTION HANDLED DURING TESTING \n--------------------------------");
          manager_.getLogger().finer(msg.toString());
          System.err.println(msg.toString());
        }
      }
    }

    /**
     * After parsing, further process this test accordingly.
     * @param term
     * @throws Exception
     */
    protected abstract void doTest(Spec term) throws Exception;

    /**
     * When an exception happens this method might handle it, in which case
     * it will be ignored, or not, in which case the test will fail. It contains
     * a conveniently formatted string with the full failure message from <code>e</code>
     * @param e thrown exception
     * @param failureMsg
     * @return handled or not
     */
    protected abstract boolean handledException(Throwable e, StringBuilder failureMsg);

    protected void printStackTraceWithCauses(Throwable e)
    {
      e.printStackTrace();
      if (e.getCause() != null)
      {
        printStackTraceWithCauses(e.getCause());
      }
    }
  }

  /**
   * Positive test case
   */
  protected class TestNormal extends AbstractManagedTest
  {
    public TestNormal(URL url)
    {
      super(url);
    }

    /**
     * The default positive test case does nothing beyond parsing.
     * @param term
     * @throws Exception
     */
    @Override
    protected void doTest(Spec term) throws Exception
    {
      CztManagedTest.this.testing(term);
    }

    /**
     * Exceptions on positive tests are errors.
     * @param e
     * @param failureMsg
     * @return false
     */
    @Override
    protected boolean handledException(Throwable e, StringBuilder failureMsg)
    {
      if (e instanceof ParseException)
      {
        if (debug_)
        {
          printStackTraceWithCauses(e);
        }
        ParseException pe = (ParseException)e;
        failureMsg.append("\n\t Reason   : ");
        failureMsg.append(pe.getErrorList().size());
        failureMsg.append(" parsing error(s)");
        pe.printErrorList();
      }
      CztManagedTest.this.encounteredException(e, failureMsg.toString(), false);
      return false;
    }
  }

  /**
   * Negative test cases for <code>T</code> exception class.
   * @param <T> kind of test exception to consider
   */
  protected abstract class TestError<T> extends AbstractManagedTest
  {

    private final String exception_;
    private final Class<T> excetptionClass_;
    
    private boolean errorsFound_;

    protected TestError(URL url, Class<T> eClass, String exception)
    {
      super(url);
      errorsFound_ = false;
      exception_ = exception;
      excetptionClass_ = eClass;
    }

    protected boolean errorsFound()
    {
      return errorsFound_;
    }

    private String removeUnderscore(String string)
    {
      String result = new String();
      for (int i = 0; i < string.length(); i++)
      {
        char c = string.charAt(i);
        if (c != '_')
        {
          result += c;
        }
      }
      return result;
    }

    /**
     * For negative error cases we further process the term for errors.
     * It affects the errorsFound() flag.
     *  
     * @param term
     * @throws Exception
     */
    @Override
    protected final void doTest(Spec term) throws Exception
    {
      errorsFound_ = process(term);
    }

    /**
     * Further process term during test to say if errors were found or not
     * @param term to process
     * @return true if errors were found, false otherwise
     * @throws Exception during processing, if any.
     */
    protected abstract boolean process(Spec term) throws Exception;

    /**
     * Actual errors message produced by processing Spec term during testing.
     * It will be compared with expected exception text given at construction time.
     * 
     * @return
     */
    //TODO: add list of errors as well?
    protected abstract String getErrorMessage();

    /**
     * For negative errors, if exception is from the parser, raise then
     * (e.g., parsing errors are NOT considered for negative testing).
     * Otherwise, if exception is the one this error handles, then check
     * whether errors were indeed found. If so, check it matches the expected
     * exception text. Otherwise, either if the text is not right or the 
     * exception was unknown, raise the error.
     * @param e error
     * @param failureMsg updated accordingly 
     * @return true if matches the negative test case.
     */
    @Override
    protected final boolean handledException(Throwable e, StringBuilder failureMsg)
    {
      boolean result = false;
      // for parsing errors, add error information but do not handle it      
      if (e instanceof ParseException)
      {
        failureMsg.append("\n\t with parsing errors:");
        ParseException pe = (ParseException)e;
        for(CztError error : pe.getErrors())
        {
          failureMsg.append("\n\t\t");
          failureMsg.append(error.toString());
        }
      }
      // else if (e instanceof exceptionClass_)
      else if (excetptionClass_.isInstance(e))
      {
        // if we can handle this exception, then an error must have happened,
        // in which case we handled the error. Result is false when no errors
        // are found, yet they are supposed to be!
        result = errorsFound();
        if (result)
        {
          // errors found => check if the right error
          final String actualError = removeUnderscore(getErrorMessage());

          // is this right error? 
          result = (exception_.compareToIgnoreCase(actualError) == 0);

          // if not, raise it
          if (!result)
          {
            failureMsg.append("\n\t Incorrect error for ").append(
                    excetptionClass_.getClass().getSimpleName());
            failureMsg.append("\n\t\t Expected: ").append(exception_);
            failureMsg.append("\n\t\t Found   : ").append(actualError);
          }
        }
        // if no errors were found, raise the problem!
        else
        {
          // no errors found => raise exception
          // add extra info on what was expected.
          failureMsg.append("\n\t Expected :");
          failureMsg.append(exception_);
        }
      }
      return result;
    }
  }
}
