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

import java.util.Map;

import net.sourceforge.czt.animation.gui.generation.Plugin;
import net.sourceforge.czt.z.ast.ConstDecl;
import net.sourceforge.czt.z.ast.DeclName;
import net.sourceforge.czt.z.ast.VarDecl;

/**
 * Plugin interface for finding all of the relevant variables in a schema.
 * <em>To do:</em> Add method for finding primed versions of the state variables.
 * @author Nicholas Daley
 */
public interface VariableExtractor extends Plugin
{
  /** 
   * This plugin's option name.
   */
  public static final String optionName = "variable";

  /** 
   * This plugin's name.
   */
  public static final String name = "Variable Extractor";

  /**
   * Returns all relevant input variables (ending in a '?').
   * @param schema The schema to search for variables.
   * @return A map from declaration names (<tt>DeclName</tt>) to variable declarations (<tt>VarDecl</tt>).
   */
  public Map<DeclName, VarDecl> getInputVariables(ConstDecl/*<SchExpr>*/schema);

  /**
   * Returns all relevant output variables (ending in a '!').
   * @param schema The schema to search for variables.
   * @return A map from declaration names (<tt>DeclName</tt>) to variable declarations (<tt>VarDecl</tt>).
   */
  public Map<DeclName, VarDecl> getOutputVariables(
      ConstDecl/*<SchExpr>*/schema);

  /**
   * Returns all relevant initial-state variables (with no decorations).
   * @param schema The schema to search for variables.
   * @return A map from declaration names (<tt>DeclName</tt>) 
   *         to variable declarations (<tt>VarDecl</tt>).
   */
  public Map<DeclName, VarDecl> getStateVariables(ConstDecl/*<SchExpr>*/schema);

  /**
   * Returns all relevant final-state variables (ending in a "'").
   * @param schema The schema to search for variables.
   * @return A map from declaration names (<tt>DeclName</tt>) 
   *         to variable declarations (<tt>VarDecl</tt>).
   */
  public Map<DeclName, VarDecl> getPrimedVariables(
      ConstDecl/*<SchExpr>*/schema);

  /**
   * Returns all variables that end with a numeric decoration.
   * @param schema The schema to search for variables.
   * @return A map from declaration names (<tt>DeclName</tt>) 
   *         to variable declarations (<tt>VarDecl</tt>).
   */
  public Map<DeclName, VarDecl> getNumberedVariables(
      ConstDecl/*<SchExpr>*/schema);
};
