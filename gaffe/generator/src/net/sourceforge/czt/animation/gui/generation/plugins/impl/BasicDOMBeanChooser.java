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

import java.awt.Dimension;

import java.util.Iterator;
import java.util.List;
import java.util.ListIterator;

import net.sourceforge.czt.animation.gui.generation.Option;

import net.sourceforge.czt.animation.gui.generation.plugins.DOMBeanChooser;

import net.sourceforge.czt.base.ast.Term;

import net.sourceforge.czt.z.ast.ConstDecl;
import net.sourceforge.czt.z.ast.DeclName;
import net.sourceforge.czt.z.ast.GenType;
import net.sourceforge.czt.z.ast.GivenType;
import net.sourceforge.czt.z.ast.PowerType;
import net.sourceforge.czt.z.ast.ProdType;
import net.sourceforge.czt.z.ast.SchemaType;
import net.sourceforge.czt.z.ast.Type;
import net.sourceforge.czt.z.ast.TypeAnn;
import net.sourceforge.czt.z.ast.VarDecl;

import org.w3c.dom.Element;

/**
 * A plugin implementation.
 * For creating the part of the GUI for displaying or inputting one variable from a Z schema.
 * @author Nicholas Daley
 */
public final class BasicDOMBeanChooser implements DOMBeanChooser {
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
    
//      if(variableDeclaration.getExpr() instanceof RefExpr) {
//        RefExpr refExpr=variableDeclaration.getExpr();
//        RefName refName=refExpr.getRefName();
//        if(refExpr().getExpr().size()==0)
//  	if(refName.getStroke().size()==0) {
//  	  if(refName.getWord().equals("\u2124")) {
//  	    //Type is integer Z
//  	  } else if(refName.getWord().equals("\u2115")) {
//  	    //Type is natural N
//  	  } 
//  	} else if(refName.getStroke().size()==1
//  		  && refName.getStroke().get(0) instanceof NumStroke
//  		  && ((NumStroke)refName.getStroke().get(0)).getNumber()==1
//  		  &&refExpr().getRefName().getWord().equals("\u2115")) {
//  	    //Type is natural N1
//  	} 
      
//      }
    List declAnns=variableDeclaration.getAnns();
    for(Iterator it=declAnns.iterator();it.hasNext();) try {
      TypeAnn ann=(TypeAnn)it.next();
      Type type=ann.getType();
      if(type instanceof GenType) {
	break;
      } else if (type instanceof GivenType) {
	//given type/free type/number type.
	break; //textfield is fine for these
      } else if (type instanceof PowerType) {
	//set/relation/function type.
	//XXX create table using appropriate model
      } else if (type instanceof ProdType) {
	//tuple type.
	//XXX create table using appropriate model
      } else if (type instanceof SchemaType) {
	//schema type.
      } else break;
    } catch(ClassCastException ex) {
      continue;
    }
    //Deal with unknown/unhandled types:
    //XXX
    return null;
  };
};
