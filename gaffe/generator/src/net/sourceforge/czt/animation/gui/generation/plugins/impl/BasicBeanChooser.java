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

import java.awt.Component;

import javax.swing.JScrollPane;
import javax.swing.JTable;
import javax.swing.JTextField;
import javax.swing.table.TableModel;

import net.sourceforge.czt.animation.gui.beans.table.RelationModel;
import net.sourceforge.czt.animation.gui.beans.table.SetModel;
import net.sourceforge.czt.animation.gui.beans.table.TupleModel;
import net.sourceforge.czt.animation.gui.beans.table.TupleSetModel;
import net.sourceforge.czt.animation.gui.generation.Option;
import net.sourceforge.czt.animation.gui.generation.plugins.BeanChooser;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.z.ast.ConstDecl;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.PowerExpr;
import net.sourceforge.czt.z.ast.ProdExpr;
import net.sourceforge.czt.z.ast.VarDecl;

/**
 * A plugin implementation.
 * For creating the part of the GUI for displaying or inputting one variable from a Z schema.
 * @author Nicholas Daley
 */
public final class BasicBeanChooser implements BeanChooser
{
  /**
   * {@inheritDoc}
   * BasicDOMBeanChooser has no command line options.
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
    return "Generates the interface for one variable.";
  };

  /**
   * {@inheritDoc}
   */
  public Component chooseBean(Term specification,
      ConstDecl/*<SchExpr>*/schema, String variableName,
      VarDecl variableDeclaration, boolean editable)
  {
    //XXX can I rely on all relations having been turned into sets of tuples, etc.?
    Expr typeExpr = variableDeclaration.getExpr();
    if (typeExpr instanceof ProdExpr)
      return chooseTableBean(new TupleModel(), variableName, editable);
    else if (typeExpr instanceof PowerExpr) {
      PowerExpr powerExpr = (PowerExpr) typeExpr;
      if (powerExpr.getExpr() instanceof ProdExpr)
        if (((ProdExpr) powerExpr.getExpr()).getZExprList().size() == 2)
          return chooseTableBean(new RelationModel(), variableName, editable);
        else
          return chooseTableBean(new TupleSetModel(), variableName, editable);
      else
        return chooseTableBean(new SetModel(), variableName, editable);
    }
    else {
      JTextField textField = new JTextField();
      textField.setName(variableName);
      textField.setEditable(editable);
      return textField;
    }
  };

  protected Component chooseTableBean(TableModel model, String tableName,
      boolean editable)
  {
    if (editable)
      System.err
          .println("Warning: At present tables created by BasicBeanChooser cannot be used for input.");

    JTable tab = new JTable(model);
    JScrollPane sp = new JScrollPane(tab);
    tab.setName(tableName);
    return sp;
  };
};
