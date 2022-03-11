package net.sourceforge.czt.typecheck.z;

import java.io.File;
import java.net.MalformedURLException;
import java.net.URISyntaxException;
import java.net.URL;
import java.util.List;

import org.junit.Before;
import org.junit.Test;

import net.sourceforge.czt.parser.util.AbstractCyclicParentTest;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.Dialect;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.session.Source;
import net.sourceforge.czt.session.SourceLocator;
import net.sourceforge.czt.session.UrlSource;
import net.sourceforge.czt.typecheck.z.util.TypeErrorException;
import net.sourceforge.czt.z.ast.Sect;
import net.sourceforge.czt.z.ast.SectTypeEnvAnn;
import net.sourceforge.czt.z.ast.Spec;
import net.sourceforge.czt.z.ast.ZSect;

import static org.junit.Assert.*;

/**
 * The test case parses and typechecks cyclic specifications. It asserts that cyclic parent
 * errors are found during typechecking, and that only such errors are found.
 * 
 * @author Andrius Velykis
 */
public class CyclicParentTypeCheckerTest extends AbstractCyclicParentTest
{
  private SectionManager sectMan;

  public CyclicParentTypeCheckerTest(UrlSource source)
  {
    super(source);
  }

  @Before
  public void initialize() throws MalformedURLException, URISyntaxException
  {
    sectMan = createSectionManager();

    URL sourceUrl = new URL(getSource().toString());
    File sourceFile = new File(sourceUrl.toURI());
    String dir = sourceFile.getParent();

    sectMan.setProperty(SourceLocator.PROP_CZT_PATH, dir);
  }

  protected SectionManager createSectionManager()
  {
    return new SectionManager(Dialect.Z);
  }

  protected SectionManager getSectionManager()
  {
    return sectMan;
  }

  @Test
  public void testTypeCheck() throws CommandException
  {
    String name = "cyclicTypeCheckTest";

    sectMan.put(new Key<Source>(name, Source.class), getSource());
    Spec spec = sectMan.get(new Key<Spec>(name, Spec.class));

    assertTrue("No sections found in the spec: " + getSource(), !spec.getSect().isEmpty());

    boolean foundSect = false;
    for (Sect sect : spec.getSect()) {
      if (sect instanceof ZSect) {
        foundSect = true;

        ZSect zSect = (ZSect) sect;
        try {
          // typecheck sections
          sectMan.get(new Key<SectTypeEnvAnn>(zSect.getName(), SectTypeEnvAnn.class));
        }
        catch (CommandException ce) {
          // check errors - only parent errors should be there
          // and not only, but there should be some
          Throwable cause = ce.getCause();
          if (cause instanceof TypeErrorException) {
            TypeErrorException typeEx = (TypeErrorException) cause;
            List<ErrorAnn> errs = typeEx.getErrors();
            boolean foundErr = false;
            for (ErrorAnn err : errs) {
              
              boolean cyclicErr = ErrorMessage.CYCLIC_PARENT.toString().equals(err.getErrorMessage());
              boolean selfErr = ErrorMessage.SELF_PARENT.toString().equals(err.getErrorMessage());
              
              if (!cyclicErr && !selfErr) {
                AssertionError out = new AssertionError(
                    "A non-cyclic-parent error found while typechecking: " + err.getMessage()
                        + "\n" + "Section : " + zSect.getName() + ", spec: " + getSource());
                out.initCause(ce);
                throw out;
              }
              
              foundErr = true;
            }
            
            if (!foundErr) {
              AssertionError out = new AssertionError(
                  "No cyclic parent errors reported during typechecking cyclic sections.\n"
                      + "Section : " + zSect.getName() + ", spec: " + getSource());
              out.initCause(ce);
              throw out;
            }
            
            continue;
          }
          
          throw ce;
        }
        
        fail("Typechecking did not find a cycle in sect " + zSect.getName() + ", spec: " + getSource());
      }
    }

    assertTrue("No Z Sections found in spec: " + getSource(), foundSect);
  }

}
