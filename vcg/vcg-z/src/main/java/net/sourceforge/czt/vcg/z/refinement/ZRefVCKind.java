/*
 * Copyright (C) 2011 Leo Freitas
 * This file is part of the CZT project.
 * 
 * The CZT project contains free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 * 
 * The CZT project is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License
 * along with CZT; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 */

package net.sourceforge.czt.vcg.z.refinement;

import net.sourceforge.czt.vcg.z.refinement.util.ZRefinementKind;

/**
 *
 * @author Leo Freitas
 * @date Sep 7, 2011
 */
public enum ZRefVCKind
{
  /**
   * Initialisation
   */
  INIT,
  /**
   * Initialisation Input
   */
  INIT_IN,
  /**
   * Applicability
   */
  APPLIC,
  /**
   * Correctness
   */
  CORRECT,
  /**
   * Finalisation
   */
  FIN,
  /**
   * Finalisation Output
   */
  FIN_OUT;
  
  public String getTypeId(ZRefinementKind rk) {
    return "vc_ref_" + getRefKindStr(rk) + name().toLowerCase();
  }
  
  private String getRefKindStr(ZRefinementKind rk) {
    if (rk != null) {
      switch(rk) {
        case FORWARD: return "fs_";
        case BACKWARD: return "bs_";
        default: return rk.name().toLowerCase() + "_";
      }
    }
    
    return "";
  }
}
