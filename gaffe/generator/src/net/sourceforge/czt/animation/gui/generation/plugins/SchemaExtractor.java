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
 * Plugin interface for finding all of the schemas in a specification.
 * @author Nicholas Daley
 */
public interface SchemaExtractor extends Plugin
{
  /** 
   * This plugin's option name.
   */
  public static final String optionName = "extractor";

  /** 
   * This plugin's name.
   */
  public static final String name = "Schema Extractor";

  /**
   * Gives the list of schemas in the specification.
   * @param spec Term containing the Spec, Sect, or Para
   *             the schema was found in.
   * @return The list of schemas.
   */
  public List<ConstDecl/*<SchExpr>*/> getSchemas(Term spec);
};
