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

package net.sourceforge.czt.animation.gui.generation;

/**
 * Top level interface for all plugins.  All plugin interface interfaces must extend Plugin, and 
 * implementation classes extend their implementation interface.<br/>
 * All interface classes <em>must</em> provide <tt>public static final String</tt> members called 
 * <tt>name</tt> and <tt>optionName</tt>.  <tt>name</tt> is an English name describing the plugin.  
 * <tt>optionName</tt> is a short, simple name for use on the command line (e.g. when selecting a plugin).
 * All interface classes must also provide a constructor taking no arguments (suitable for use by 
 * <tt>Class.newInstance</tt>).
 * @author Nicholas Daley
 */
public interface Plugin
{
  /**
   * Getter method for the list of options accepted by this plugin.
   */
  public Option[] getOptions();

  /**
   * Getter method for help.  A simple piece of text to appear in help displays describing the plugin.
   */
  public String getHelp();
};
