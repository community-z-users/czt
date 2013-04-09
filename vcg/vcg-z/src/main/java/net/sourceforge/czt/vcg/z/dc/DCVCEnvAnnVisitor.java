/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package net.sourceforge.czt.vcg.z.dc;

import net.sourceforge.czt.util.Visitor;

/**
 *
 * @author leo
 */
public interface DCVCEnvAnnVisitor<R> extends Visitor<R>
{
  /**
   * Visits a DCVCEnvAnn.
   * @param  term the DCVCEnvAnn to be visited.
   * @return some kind of <code>Object</code>.
   */
  R visitDCVCEnvAnn(DCVCEnvAnn term);
}
