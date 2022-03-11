
/*
ParserFailTest.java
 *
Created on 02 February 2007, 12:45
 *
To change this template, choose Tools | Template Manager
and open the template in the editor.
 */
package net.sourceforge.czt.parser.circus;

//~--- non-JDK imports --------------------------------------------------------

import junit.framework.Test;
import junit.framework.TestCase;
import junit.framework.TestSuite;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.session.FileSource;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.util.CztLogger;

//~--- JDK imports ------------------------------------------------------------

import java.io.File;

import java.util.logging.Level;

//~--- classes ----------------------------------------------------------------

/**
 *
 * @author leo
 */
public class ParserFailTest extends AbstractParserTest {
    protected void collectTest(TestSuite suite, File file) {

        // if the file name ends with error, then we have a case with
        // the typechecker should throw the exception specified at the
        // start of the filename
        if (file.getName().endsWith("-errors.tex")) {

            // int index = fileName.indexOf("-");
            // if (index < 1) {
            // fail(fileName + " does not specify an exception name");
            // }
            // String exception = fileName.substring(0, index);
            suite.addTest(
                new TestError(file.getAbsolutePath() /* , exception) */));
        }
    }

    public static Test suite() {
        CztLogger.getLogger(SectionManager.class).setLevel(Level.OFF);

        TestSuite      suite       = new TestSuite();
        ParserFailTest parserTests = new ParserFailTest();

        parserTests.collectTests(suite, TESTS_SOURCEDIR);
        if (VERBOSE) {
          System.out.println("Number of (hoppefully) erroneous tests to run: "
                           + suite.countTestCases());
        }

        return suite;
    }

    //~--- inner classes ------------------------------------------------------

    class TestError extends TestCase {
        private String file_;

        //~--- constructors ---------------------------------------------------

        TestError(String file) {
            file_ = file;

            // exception_ = exception;
        }

        //~--- methods --------------------------------------------------------

        public void runTest() {
            try {
                @SuppressWarnings("unused")
				Term term = parse(new FileSource(file_));
            } catch (net.sourceforge.czt.parser.util.ParseException f) {
                if (f.getErrorList().isEmpty()) {
                    f.printStackTrace();
                    fail(lineSeparator_
                         + "No parsing error found, despite syntactic problems"
                         + lineSeparator_ + "\tFile: " + file_
                         + lineSeparator_ + "tErrors: " + f.getMessage()
                         + lineSeparator_);
                } else {
                    if (VERBOSE)
                    {
                      System.out.print(lineSeparator_
                                     + "Expected errors found for"
                                     + lineSeparator_ + "\tFile: " + file_
                                     + lineSeparator_ + "\tErrors: "
                                     + f.getMessage() + lineSeparator_);
                    }
                    return;
                }
            } catch (RuntimeException e) {
                printCauses(e);
                fail(lineSeparator_ + "Unexpected runtime exception"
                     + lineSeparator_ + "\tFile: " + file_ + lineSeparator_
                     + "\tException: " + e.toString());
            } catch (Throwable e) {
                printCauses(e);
                fail(lineSeparator_ + "Unexpected exception" + lineSeparator_
                     + "\tFile: " + file_ + lineSeparator_ + "\tException: "
                     + e.toString());
            }

            fail(lineSeparator_
                 + "Parsing errors were not raised, despite syntactic problems"
                 + lineSeparator_ + "\tFile: " + file_);
        }
    }
}