package net.sourceforge.czt.typecheck.zeves;

import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.session.UrlSource;

public class CyclicParentTypeCheckerTest extends net.sourceforge.czt.typecheck.z.CyclicParentTypeCheckerTest
{

  public CyclicParentTypeCheckerTest(UrlSource source)
  {
    super(source);
  }

  @Override
  protected SectionManager createSectionManager()
  {
    return new SectionManager("zeves");
  }
}
