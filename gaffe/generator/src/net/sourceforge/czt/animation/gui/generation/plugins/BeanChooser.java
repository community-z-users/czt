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

import java.awt.Component;

import net.sourceforge.czt.animation.gui.generation.Plugin;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.z.ast.ConstDecl;
import net.sourceforge.czt.z.ast.VarDecl;

/**
 * A plugin interface.
 * For creating the part of the GUI for displaying or inputting one variable from a Z schema.
 * @author Nicholas Daley
 */
public interface BeanChooser extends Plugin
{
  /** 
   * This plugin's option name.
   */
  public static final String optionName = "bean";

  /** 
   * This plugin's name.
   */
  public static final String name = "Bean Chooser";

  /**
   * Method for creating the GUI for a schema variable.
   * <code>chooseBean</code> creates the component, and sets its name; but does not set its location, or add
   * it to the form.
   * @param specification Term containing the Spec, Sect, or Para the schema was found in.
   * @param schema The schema that contains the variable.
   * @param variableName The name of the variable the bean is for.
   * @param variableDeclaration The VarDecl in which the variable was declared.
   * @param editable True if the component is to be used for inputting data, false if it is to be used for 
   *                 output.
   * @return A <code>Component</code> suitable for editing or viewing the variable.
   */
  public Component chooseBean(Term specification,
      ConstDecl/*<SchExpr>*/schema, String variableName,
      VarDecl variableDeclaration, boolean editable);
};
