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
package czt.animation.gui.beans;

import java.awt.Image;

import java.beans.SimpleBeanInfo;

/**
 * <code>BeanInfo</code> for ScriptDelegate.  
 * Exists for the sole purpose of giving the ScriptDelegateBeanInfo bean an icon.
 */
public class ScriptDelegateBeanInfo extends SimpleBeanInfo {
  /**
   * Obtains the image for ScriptDelegate's icon. 
   * @return The image obtained from the file "ScriptDelegateIcon.gif".
   */
  public Image getIcon(int iconKind) {
    switch(iconKind) {
     case ICON_COLOR_32x32: case ICON_MONO_32x32:
       return loadImage("ScriptDelegateIcon.gif");
     case ICON_COLOR_16x16: case ICON_MONO_16x16:
       return loadImage("ScriptDelegateIcon.gif")
	 .getScaledInstance(16,16,Image.SCALE_FAST);
     default:
       throw new Error("iconKind should be one of ICON_COLOR_32x32, ICON_MONO_32x32, "
		       +"ICON_COLOR_16x16, ICON_MONO_16x16");
    }     
  };
};
