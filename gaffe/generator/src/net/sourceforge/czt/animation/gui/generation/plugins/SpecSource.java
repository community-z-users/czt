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

import java.net.URL;

import net.sourceforge.czt.animation.gui.generation.Plugin;

import net.sourceforge.czt.base.ast.Term;

/**
 * A plugin interface for obtaining the Z specification in AST form.
 * @author Nicholas Daley
 */
public interface SpecSource extends Plugin {
  /**
   * This plugin's option name.
   */
  public static final String optionName="source";
  /**
   * This plugin's name.
   */
  public static final String name="Specification Source";

  /**
   * Method for acquiring the parsed specification.
   * @return Term containing the specification, section, or paragraph containing the schemas to build the 
   * interface from.
   * @throws IllegalStateException if it has not been given enough information (e.g. from the command line) 
   * to determine this.
   */
  public Term obtainSpec() throws IllegalStateException;
  /**
   * Gives a URL at which the specification can be found.
   * Should be run after <tt>obtainSpec</tt>.
   * @return The URL or null if the source can not be described as a URL.
   */
  public URL getURL();  
};
