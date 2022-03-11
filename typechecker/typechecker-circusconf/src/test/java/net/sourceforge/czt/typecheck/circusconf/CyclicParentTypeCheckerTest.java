package net.sourceforge.czt.typecheck.circusconf;

import net.sourceforge.czt.session.Dialect;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.session.UrlSource;

public class CyclicParentTypeCheckerTest extends net.sourceforge.czt.typecheck.circus.CyclicParentTypeCheckerTest
{

  public CyclicParentTypeCheckerTest(UrlSource source)
  {
    super(source);
  }

  @Override
  protected SectionManager createSectionManager()
  {
    return new SectionManager(Dialect.CIRCUSCONF);
  }
}
