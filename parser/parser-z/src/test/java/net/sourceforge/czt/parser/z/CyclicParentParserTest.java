package net.sourceforge.czt.parser.z;

import java.io.File;
import java.net.MalformedURLException;
import java.net.URISyntaxException;
import java.net.URL;

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
import net.sourceforge.czt.z.ast.Spec;

public class CyclicParentParserTest extends AbstractCyclicParentTest
{
  private SectionManager sectMan;
  
  public CyclicParentParserTest(UrlSource source)
  {
    super(source);
  }
  
  @Before
  public void initialize() throws MalformedURLException, URISyntaxException {
      sectMan = createSectionManager();
      
      URL sourceUrl = new URL(getSource().toString());
      File sourceFile = new File(sourceUrl.toURI());
      String dir = sourceFile.getParent();
      
      sectMan.setProperty(SourceLocator.PROP_CZT_PATH, dir);
  }

  protected SectionManager createSectionManager() {
    return new SectionManager(Dialect.Z);
  }
  
  protected SectionManager getSectionManager() {
    return sectMan;
  }
  
  @Test
  public void testParse() throws CommandException {
    
    String name = "cyclicParseTest";
    
    sectMan.put(new Key<Source>(name, Source.class), getSource());
    sectMan.get(new Key<Spec>(name, Spec.class));
  }
  
}
