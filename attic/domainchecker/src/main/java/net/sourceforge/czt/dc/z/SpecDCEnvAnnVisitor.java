package net.sourceforge.czt.dc.z;

import net.sourceforge.czt.util.Visitor;

/**
 *
 * @author leo
 */
public interface SpecDCEnvAnnVisitor<R> extends Visitor<R>
{
  /**
   * Visits a ZSectDCEnvAnn.
   * @param  term the ZSectDCEnvAnn to be visited.
   * @return some kind of <code>Object</code>.
   */
  R visitZSpecDCEnvAnn(SpecDCEnvAnn term);
}
