/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package net.sourceforge.czt.dc.z;

import net.sourceforge.czt.util.Visitor;

/**
 *
 * @author leo
 */
public interface ZSectDCEnvAnnVisitor<R> extends Visitor<R>
{
  /**
   * Visits a ZSectDCEnvAnn.
   * @param  term the ZSectDCEnvAnn to be visited.
   * @return some kind of <code>Object</code>.
   */
  R visitZSectDCEnvAnn(ZSectDCEnvAnn term);
}
