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
package net.sourceforge.czt.animation.gui.beans;

import java.awt.Component;
import java.awt.Label;
import java.awt.TextComponent;

import java.beans.PropertyChangeListener;
import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeSupport;
import java.beans.PropertyVetoException;

import java.beans.beancontext.BeanContext;
import java.beans.beancontext.BeanContextChildSupport;
import java.beans.beancontext.BeanContextServiceAvailableEvent;
import java.beans.beancontext.BeanContextServiceRevokedEvent;
import java.beans.beancontext.BeanContextServices;

import java.util.TooManyListenersException;

import javax.swing.JLabel;
import javax.swing.JTable;
import javax.swing.text.JTextComponent;

import net.sourceforge.czt.animation.ZLocator;

import net.sourceforge.czt.animation.gui.Form;

import net.sourceforge.czt.animation.gui.beans.table.*;

import net.sourceforge.czt.animation.gui.history.History;

import net.sourceforge.czt.animation.gui.temp.*;

public class FormFiller extends BeanContextChildSupport {
  private History history=null;
  private Form form=null;
  
  private static void fillBean(Component obj, ZValue value) {
    System.err.println("FormFilling "+obj.getClass());
    if(obj instanceof TextComponent) ((TextComponent)obj).setText(value.toString());
    if(obj instanceof JTextComponent) ((JTextComponent)obj).setText(value.toString());
    if(obj instanceof Label) ((Label)obj).setText(value.toString());
    if(obj instanceof JLabel) ((JLabel)obj).setText(value.toString());
    if(obj instanceof JTable) {
      JTable table=(JTable)obj;
      System.err.println("  with model "+table.getModel().getClass());
      if(table.getModel() instanceof RelationModel)
	if(value instanceof ZSet)
	  ((RelationModel)table.getModel()).setRelation((ZSet)value);
	else
	  ((RelationModel)table.getModel()).setRelation(null);
      else if(table.getModel() instanceof BindingModel)
	if(value instanceof ZBinding)
	  ((BindingModel)table.getModel()).setBinding((ZBinding)value);
	else
	  ((BindingModel)table.getModel()).setBinding(null);
    }
    //XXX Fill in here for more types of components.
  };
  private static void clearBean(Component obj) {
    if(obj instanceof TextComponent) ((TextComponent)obj).setText("");
    if(obj instanceof JTextComponent) ((JTextComponent)obj).setText("");
    if(obj instanceof Label) ((Label)obj).setText("");
    if(obj instanceof JLabel) ((JLabel)obj).setText("");
    if(obj instanceof JTable) {
      JTable table=(JTable)obj;
      if(table.getModel() instanceof RelationModel)
	((RelationModel)table.getModel()).setRelation(null);
      else if(table.getModel() instanceof BindingModel)
	((BindingModel)table.getModel()).setBinding(null);
    }
    //XXX Fill in here for more types of components.
  };

  private void fillBeans() {
    if(form==null||history==null) return;
	
    Component[] beans=form.getComponents();
    for(int i=0;i<beans.length;i++) {
      String name=beans[i].getName();
      if(name!=null) try {
	ZBinding b=history.getCurrentSolution();
	if(b!=null)
	  fillBean(beans[i], ZLocator.fromString(name).apply(b));
	else
	  clearBean(beans[i]);
      } catch (ClassCastException ex) {
	fillBean(beans[i],null);
      };
    }
  };
  
  private final PropertyChangeListener pcListener=new PropertyChangeListener() {
      public void propertyChange(PropertyChangeEvent evt) {
	fillBeans();
      };
    };

  private void registerHistory() {
    if(((BeanContextServices)getBeanContext()).hasService(History.class)) try {
      history=(History)((BeanContextServices)getBeanContext())
	.getService(this,this,History.class,null,this);
      history.addPropertyChangeListener("currentSolution",pcListener);
    } catch (TooManyListenersException ex) {
    } 
    fillBeans();
  };
  private void registerForm() {
    if(((BeanContextServices)getBeanContext()).hasService(Form.class)) try {
      form=(Form)((BeanContextServices)getBeanContext())
	.getService(this,this,Form.class,null,this);
    } catch (TooManyListenersException ex) {
    }
    fillBeans();
  };
  
  public void serviceAvailable(BeanContextServiceAvailableEvent bcsae) {
    if(bcsae.getServiceClass().equals(History.class))   registerHistory();
    else if(bcsae.getServiceClass().equals(Form.class)) registerForm();
  };

  private void unregisterHistory() {
    if(history!=null)
      history.removePropertyChangeListener("currentSolution",pcListener);
    history=null;
  };
  private void unregisterForm() {
    form=null;
  };
  
  public void serviceRevoked(BeanContextServiceRevokedEvent bcsre) {
    if(bcsre.getServiceClass().equals(History.class))   unregisterHistory();
    else if(bcsre.getServiceClass().equals(Form.class)) unregisterForm();
  };
  public FormFiller() {
    addPropertyChangeListener("beanContext",new PropertyChangeListener() {
	public void propertyChange(PropertyChangeEvent evt) {
	  if(evt.getOldValue()!=null && evt.getOldValue() instanceof BeanContextServices) {
	    ((BeanContextServices)evt.getOldValue())
	      .removeBeanContextServicesListener(FormFiller.this);
	    unregisterHistory();
	    unregisterForm();
	  }
	  if(evt.getNewValue()!=null && evt.getNewValue() instanceof BeanContextServices) {
	    ((BeanContextServices)evt.getNewValue())
	      .addBeanContextServicesListener(FormFiller.this);
	    registerHistory();
	    registerForm();
	  } 
	};
      });
    
  };
  
};
