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

import net.sourceforge.czt.animation.gui.generation.Option;

import net.sourceforge.czt.animation.gui.generation.plugins.DOMBeanChooser;

import net.sourceforge.czt.base.ast.Term;

import net.sourceforge.czt.z.ast.ConstDecl;
import net.sourceforge.czt.z.ast.DeclName;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.PowerExpr;
import net.sourceforge.czt.z.ast.ProdExpr;
import net.sourceforge.czt.z.ast.VarDecl;

import org.w3c.dom.Document;
import org.w3c.dom.Element;

/**
 * A plugin implementation.
 * For creating the part of the GUI for displaying or inputting one variable from a Z schema.
 * @author Nicholas Daley
 */
public final class BasicDOMBeanChooser implements DOMBeanChooser {
  Document doc;
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
  public Element chooseBean(Term specification, ConstDecl/*<SchExpr>*/ schema, 
			    DeclName variableName, VarDecl variableDeclaration) {
    //XXX can I rely on all relations having been turned into sets of tuples, etc.?
    Expr typeExpr=variableDeclaration.getExpr();
    if(typeExpr instanceof ProdExpr)
      return chooseTupleBean(variableName, variableDeclaration);
    else if(typeExpr instanceof PowerExpr) {
      PowerExpr powerExpr=(PowerExpr)typeExpr;
      if(powerExpr.getExpr() instanceof ProdExpr)
	if(((ProdExpr)powerExpr.getExpr()).getExpr().size()==2)
	  return chooseRelationBean(variableName,variableDeclaration);
	else 
	  return choosePowTupleBean(variableName,variableDeclaration);
      else return chooseSetBean(variableName, variableDeclaration);
    } else return chooseSimpleBean(variableName, variableDeclaration);
  };

  public Element chooseTupleBean(DeclName variableName, VarDecl variableDeclaration) {
    return null;
    //XXX
  };
  public Element chooseRelationBean(DeclName variableName, VarDecl variableDeclaration) {
    return null;
    //XXX
  };
  public Element choosePowTupleBean(DeclName variableName, VarDecl variableDeclaration) {
    return null;
    //XXX
  };
  public Element chooseSetBean(DeclName variableName, VarDecl variableDeclaration) {
    //XXX need to get this into a JScrollPane.
    return createObjectElement(doc, "javax.swing.JTable",
	      createPropertyElement(doc, "model", 
		 createObjectElement(doc,"net.sourceforge.czt.animation.gui.beans.table.SetModel", 
				     (Element[])null)));
  };
  public Element chooseSimpleBean(DeclName variableName, VarDecl variableDeclaration) {
    //XXX maybe add bits for e.g. verifying text entered is a number?
    return createObjectElement(doc, "javax.swing.JTextField", 
			       createPropertyElement(doc, "name", 
						     createStringElement(doc,Name2String.toString(variableName))
						     )
			       );
  };  

  private Element createObjectElement(Document doc, String clasz, Element child) {
    return createObjectElement(doc, clasz,new Element[]{child});
  };
  private Element createObjectElement(Document doc, String clasz, Element[] children) {
    Element el=doc.createElement("object");
    el.setAttribute("class",clasz);
    for(int i=0;children!=null && i<children.length;i++)
      el.appendChild(children[i]);
    return el;
  };
  private Element createPropertyElement(Document doc, String property, Element child) {
    return createPropertyElement(doc, property,new Element[]{child});
  };
  private Element createPropertyElement(Document doc, String property, Element[] children) {
    Element el=doc.createElement("void");
    el.setAttribute("property",property);
    for(int i=0;children!=null && i<children.length;i++)
      el.appendChild(children[i]);
    return el;
  };
  private Element createStringElement(Document doc, String s) {
    Element el=doc.createElement("string");
    el.appendChild(doc.createTextNode(s));
    return el;
  };
};
