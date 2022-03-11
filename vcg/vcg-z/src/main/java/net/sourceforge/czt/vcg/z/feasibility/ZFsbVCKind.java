package net.sourceforge.czt.vcg.z.feasibility;


public enum ZFsbVCKind {

  /**
   * Operation precondition check
   */
  PRE,
  /**
   * State schema feasibility check
   */
  STATE,
  /**
   * Axiom global consistency check
   */
  AXIOM,
  /**
   * Horizontal definition for axioms
   */
  HORIZ_DEF,
  /**
   * None-empty given types check
   */
  GIVEN_PARA,
  /**
   * Free type injections check
   */
  FREE_PARA,
  /**
   * State initialisation feasibility check
   */
  INIT,
  /**
   * State finalisation feasibility check
   */
  FIN,
  /**
   * Unknown feasibility check
   */
  DEFAULT;
  
  public String getTypeId() {
    return "vc_fsb_" + name().toLowerCase();
  }
  
}
