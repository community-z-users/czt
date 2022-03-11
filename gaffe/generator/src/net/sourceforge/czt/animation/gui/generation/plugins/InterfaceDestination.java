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

package net.sourceforge.czt.animation.gui.generation.plugins;

import java.io.OutputStream;
import java.net.URL;

import net.sourceforge.czt.animation.gui.generation.Plugin;

/**
 * Plugin interface for selecting where to write the generated GUI to.
 * @author Nicholas Daley
 */
public interface InterfaceDestination extends Plugin
{
  /**
   * This plugin's option name.
   */
  public static final String optionName = "destination";

  /** 
   * This plugin's name.
   */
  public static final String name = "Interface Destination";

  /**
   * Gives the output stream to write the generated interface to.
   * @param inputURL The URL (or null) that {@link SpecSource#getURL()} returned.
   */
  public OutputStream obtainOutputStream(URL inputURL)
      throws IllegalStateException;
};
