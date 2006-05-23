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
import java.util.List;

import net.sourceforge.czt.animation.gui.generation.Plugin;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.z.ast.ConstDecl;

/**
 * Plugin interface for creating the Z Specification's whole GUI.
 * @author Nicholas Daley
 */
public interface BeanInterfaceGenerator extends Plugin
{
  /**
   * This plugin's option name.
   */
  public static final String optionName = "interface";

  /**
   * This plugin's name.
   */
  public static final String name = "Interface Generator";

  /**
   * Method for creating the interface.
   * @param specification Term containing the Spec, Sect, or Para the schema was found in.
   * @param specURL URL (or null) that {@link SpecSource#getURL()} returned.
   * @param schemas List of all of the schemas in the specification.
   * @param stateSchema The specification's state schema.
   * @param initSchema The initialisation schema.
   * @param operationSchemas List of all of the operation schemas.
   * @param variableExtractor The {@link VariableExtractor variable extractor plugin} to use to find all of
   * the relevant variables in a schema.
   * @param beanChooser The {@link BeanChooser bean chooser plugin} to use to generate the part of the GUI
   * for a schema variable.
   * @param os The output stream to write the generated interface to.
   */
  public void generateInterface(Term specification, URL specURL,
      List<ConstDecl/*<SchExpr>*/> schemas,
      ConstDecl/*<SchExpr>*/stateSchema, ConstDecl/*<SchExpr>*/initSchema,
      List<ConstDecl/*<SchExpr>*/> operationSchemas,
      VariableExtractor variableExtractor, BeanChooser beanChooser,
      OutputStream os);
};
