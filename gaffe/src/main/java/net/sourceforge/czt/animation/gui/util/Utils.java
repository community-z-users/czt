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

package net.sourceforge.czt.animation.gui.util;

import java.io.File;

import javax.swing.filechooser.FileFilter;

/**
 * Useful bits and pieces that lack any other home.
 */
public final class Utils
{
  /**
   * File filter for displaying only .gaffe files, and directories.
   */
  public static final FileFilter gaffeFileFilter = new FileFilter()
  {
    public boolean accept(File f)
    {
      return f.getName().endsWith(".gaffe") || f.isDirectory();
    }

    public String getDescription()
    {
      return "Gaffe Interface Files (*.gaffe)";
    }
  };

  /**
   * This class isn't meant to be instantiated.
   */
  private Utils()
  {
  }
}
