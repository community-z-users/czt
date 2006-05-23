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

package net.sourceforge.czt.animation.gui.generation.plugins.impl;

import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

import net.sourceforge.czt.animation.gui.generation.Option;
import net.sourceforge.czt.animation.gui.generation.plugins.VariableExtractor;
import net.sourceforge.czt.z.ast.ConstDecl;
import net.sourceforge.czt.z.ast.DeclName;
import net.sourceforge.czt.z.ast.InStroke;
import net.sourceforge.czt.z.ast.NextStroke;
import net.sourceforge.czt.z.ast.NumStroke;
import net.sourceforge.czt.z.ast.OutStroke;
import net.sourceforge.czt.z.ast.SchExpr;
import net.sourceforge.czt.z.ast.Stroke;
import net.sourceforge.czt.z.ast.VarDecl;
import net.sourceforge.czt.z.ast.ZDeclName;

/**
 * Plugin implementation for finding all of the relevant variables in a schema.
 * <em>To do:</em> Add method for finding primed versions of the state variables.
 * @author Nicholas Daley
 */
public final class DefaultVariableExtractor implements VariableExtractor
{
  /**
   * {@inheritDoc}
   * DefaultVariableExtractor has no command line options.
   */
  public Option[] getOptions()
  {
    return new Option[]{};
  };

  /**
   * {@inheritDoc}
   */
  public String getHelp()
  {
    return "Finds the variable declarations in a schema.";
  };

  /**
   * Helper methods for finding variables decorated with a certain stroke.
   * @param schema The schema to search for variables.
   * @param clazz The class of Stroke with which the variables should end.
   *              If it is null, then undecorated variables are returned. 
   * @return A map from declaration names (<tt>DeclName</tt>) 
   *         to variable declarations (<tt>VarDecl</tt>).
   */
  private Map<DeclName, VarDecl> getXVariables(ConstDecl/*<SchExpr>*/schema,
      Class clazz)
  {
    Map<DeclName, VarDecl> results = new HashMap<DeclName, VarDecl>();
    List declarations = ((SchExpr) schema.getExpr()).getZSchText()
        .getZDeclList();
    for (Iterator it = declarations.iterator(); it.hasNext();) {
      VarDecl declaration;
      try {
        declaration = (VarDecl) it.next();
      } catch (ClassCastException ex) {
        continue;
      }
      for (Iterator itn = declaration.getDeclName().iterator(); itn.hasNext();) {
        ZDeclName name = (ZDeclName) itn.next();
        List decors = (List) name.getStrokeList();
        if (decors.size() == 0) {
          if (clazz == null)
            results.put(name, declaration);
        }
        else {
          Stroke lastStroke = (Stroke) decors.get(decors.size() - 1);
          if (clazz != null && clazz.isInstance(lastStroke))
            results.put(name, declaration);
        }
      }
    }
    return results;
  };

  /**
   * {@inheritDoc}
   * Uses {@link #getXVariables getXVariables}.
   */
  public Map<DeclName, VarDecl> getInputVariables(ConstDecl/*<SchExpr>*/schema)
  {
    return getXVariables(schema, InStroke.class);
  };

  /**
   * {@inheritDoc}
   * Uses {@link #getXVariables getXVariables}.
   */
  public Map<DeclName, VarDecl> getOutputVariables(
      ConstDecl/*<SchExpr>*/schema)
  {
    return getXVariables(schema, OutStroke.class);
  };

  /**
   * {@inheritDoc}
   * Uses {@link #getXVariables getXVariables}.
   */
  public Map<DeclName, VarDecl> getStateVariables(ConstDecl/*<SchExpr>*/schema)
  {
    return getXVariables(schema, null);
  };

  /**
   * {@inheritDoc}
   * Uses {@link #getXVariables getXVariables}.
   */
  public Map<DeclName, VarDecl> getPrimedVariables(
      ConstDecl/*<SchExpr>*/schema)
  {
    return getXVariables(schema, NextStroke.class);
  };

  /**
   * {@inheritDoc}
   * Uses {@link #getXVariables getXVariables}.
   */
  public Map<DeclName, VarDecl> getNumberedVariables(
      ConstDecl/*<SchExpr>*/schema)
  {
    return getXVariables(schema, NumStroke.class);
  };
};
