/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package net.sourceforge.czt.vcg.z.feasibility;

import net.sourceforge.czt.util.Visitor;

/**
 *
 * @author leo
 */
public interface FeasibilityVCEnvAnnVisitor<R> extends Visitor<R>
{
  /**
   * Visits a DCVCEnvAnn.
   * @param  term the DCVCEnvAnn to be visited.
   * @return some kind of <code>Object</code>.
   */
  R visitFeasibilityVCEnvAnn(FeasibilityVCEnvAnn term);
}
