/*
  GAfFE - A (G)raphical (A)nimator (F)ront(E)nd for Z - Part of the CZT Project.
  Copyright 2003 Nicholas Daley
  
  This program is free software; you can redistribute it and/or
  modify it under the terms of the GNU General Public License
  as published by the Free Software Foundation; either version 2
  of the License, or (at your option) any later version.
  
  This program is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with this program; if not, write to the Free Software
  Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA  02111-1307, USA.
*/
package czt.animation.gui;

import com.ibm.bsf.BSFManager;

import czt.animation.gui.history.History;
import czt.animation.gui.scripting.BSFServiceProvider;

/**
 * The core program for normal animation of a specification.
 */
abstract class AnimatorCore extends AnimatorCoreBase {
  /**
   * Creates an AnimatorCore.
   */
  public AnimatorCore() {
    BSFManager bsfm=new BSFManager();
    //XXX (register any new scripting languages)
    //XXX register and declare beans in bsfm
    rootContext.addService(BSFManager.class,new BSFServiceProvider(bsfm));
    
    //XXX load interface file somewhere...

    //XXX activate initialisation schema.
  };
  
  
};
