package net.sourceforge.czt.vcg.z.feasibility.util;

/**
 * Refactored from core java z
 * @author Leo Freitas
 *
 */
public enum ZStateInfo {
	  NONE("Normal schema"),
	  STATE("State schema"),
	  STINIT("State initialisation schema"),
	  STFIN("State finalisation schema"),
	  ABSTRACT("Abstract specification schema"),
	  CONCRETE("Concrete specification schema"),
	  RETRIEVE("Refinement retrieve schema"),
	  ININIT("Inputs initialisation schema"),
	  OUTFIN("Output finalisation schema"),
	  INRETRIEVE("Input retrieve schema"),
	  OUTRETRIEVE("Output retrieve schema");
	  
	  private final String description_;
	  ZStateInfo(String desc)
	  {
		  description_ = desc;
	  }
	  
	  public String getDescription()
	  {
		  return description_;
	  }
}

