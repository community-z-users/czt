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

import java.awt.Container;

import javax.swing.JScrollPane;
import javax.swing.JTable;
import javax.swing.JTextField;

import javax.swing.table.TableModel;

import net.sourceforge.czt.animation.gui.Form;

import net.sourceforge.czt.animation.gui.beans.table.RelationModel;
import net.sourceforge.czt.animation.gui.beans.table.SetModel;
import net.sourceforge.czt.animation.gui.beans.table.TupleModel;
import net.sourceforge.czt.animation.gui.beans.table.TupleSetModel;

import net.sourceforge.czt.animation.gui.generation.Option;

import net.sourceforge.czt.animation.gui.generation.plugins.BeanChooser;

import net.sourceforge.czt.base.ast.Term;

import net.sourceforge.czt.z.ast.ConstDecl;
import net.sourceforge.czt.z.ast.DeclName;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.PowerExpr;
import net.sourceforge.czt.z.ast.ProdExpr;
import net.sourceforge.czt.z.ast.VarDecl;

/**
 * A plugin implementation.
 * For creating the part of the GUI for displaying or inputting one variable from a Z schema.
 * @author Nicholas Daley
 */
public final class BasicBeanChooser implements BeanChooser {
  /**
   * {@inheritDoc}
   * BasicDOMBeanChooser has no command line options.
   */
  public Option[] getOptions() {return new Option[]{};};
  /**
   * {@inheritDoc}
   */
  public String getHelp() {return "Generates the interface for one variable.";};  

  /**
   * {@inheritDoc}
   */
  public void chooseBean(Term specification, ConstDecl/*<SchExpr>*/ schema, 
			 DeclName variableName, VarDecl variableDeclaration,
			 Form form, Container parent) {
    //XXX can I rely on all relations having been turned into sets of tuples, etc.?
    String varNameString=Name2String.toString(variableName);
    Expr typeExpr=variableDeclaration.getExpr();
    if(typeExpr instanceof ProdExpr)
      chooseTableBean(new TupleModel(), form, parent, varNameString);
    else if(typeExpr instanceof PowerExpr) {
      PowerExpr powerExpr=(PowerExpr)typeExpr;
      if(powerExpr.getExpr() instanceof ProdExpr)
	if(((ProdExpr)powerExpr.getExpr()).getExpr().size()==2)
	  chooseTableBean(new RelationModel(), form, parent, varNameString);
	else
	  chooseTableBean(new TupleSetModel(), form, parent, varNameString);
      else chooseTableBean(new SetModel(), form, parent, varNameString);
    } else {
      JTextField textField=new JTextField();
      textField.setName(varNameString);
      form.addBean(textField,parent);
    }
  };

  protected void chooseTableBean(TableModel model, Form form, Container parent, String tableName) {
    JTable tab=new JTable(model);
    JScrollPane sp=new JScrollPane(tab);
    form.addBean(sp,parent);
    form.addBean(tab,sp);
    tab.setName(tableName);
  };  
};
