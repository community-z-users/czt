package net.sourceforge.czt.vcg.z.feasibility.util;

import net.sourceforge.czt.z.ast.Ann;

/**
 * Z state annotation. It contains information regarding the role a schema plays in refinement.
 *
 * @author Leo Freitas
 */
public interface ZStateAnn extends Ann {
	  /**
	   * Returns the Info element.
	   *
	   * @return the Info element.
	   */
	  ZStateInfo getInfo();


	  /**
	   * Sets the Info element.
	   *
	   * @param info   the Info element.
	   * @see #getInfo
	   */
	  void setInfo(ZStateInfo info);
}
