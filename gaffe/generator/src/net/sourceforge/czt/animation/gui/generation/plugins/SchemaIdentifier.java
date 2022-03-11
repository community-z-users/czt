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

import java.util.List;

import net.sourceforge.czt.animation.gui.generation.Plugin;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.z.ast.ConstDecl;

/**
 * Plugin interface for identifying the purpose of schemas.
 * A list of schemas is fed into this plugin.  After which it can be queried for the state schema, init 
 * schema, and operation schemas.
 * @author Nicholas Daley
 */
public interface SchemaIdentifier extends Plugin
{
  /** 
   * This plugin's option name.
   */
  public static final String optionName = "identifier";

  /** 
   * This plugin's name.
   */
  public static final String name = "Schema Identifier";

  /**
   * Method for feeding in the list of schemas.
   * @param specification Term containing the Spec, Sect, or Para the schemas were found in.
   * @param schemas The list of schemas.
   * @throws IllegalStateException if it has not been given enough information (e.g. from the command line) 
   * to determine this.
   */
  public void identifySchemas(Term specification,
      List<ConstDecl/*<SchExpr>*/> schemas) throws IllegalStateException;

  /**
   * State schema query method.
   * Must be run after <tt>identifySchemas</tt>.
   * @return The specification's state schema.
   */
  public ConstDecl/*<SchExpr>*/getStateSchema();

  /**
   * Initialisation schema query method.
   * Must be run after <tt>identifySchemas</tt>.
   * @return The specification's initialisation schema.
   */
  public ConstDecl/*<SchExpr>*/getInitSchema();

  /**
   * Operation schema query method.
   * Must be run after <tt>identifySchemas</tt>.
   * @return A list of the specification's operation schemas.
   */
  public List<ConstDecl/*<SchExpr>*/> getOperationSchemas();
};
