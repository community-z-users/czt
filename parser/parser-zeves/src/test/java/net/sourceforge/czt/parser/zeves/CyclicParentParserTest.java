package net.sourceforge.czt.parser.zeves;

import net.sourceforge.czt.session.Dialect;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.session.UrlSource;

public class CyclicParentParserTest extends net.sourceforge.czt.parser.z.CyclicParentParserTest
{

  public CyclicParentParserTest(UrlSource source)
  {
    super(source);
  }

  @Override
  protected SectionManager createSectionManager()
  {
    return new SectionManager(Dialect.ZEVES);
  }
}
