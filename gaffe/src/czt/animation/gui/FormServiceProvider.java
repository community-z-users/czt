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
package czt.animation.gui;

import java.beans.beancontext.BeanContextServiceProvider;
import java.beans.beancontext.BeanContextServices;

import java.util.Iterator;

public final class FormServiceProvider implements BeanContextServiceProvider {
  /**
   * The Form to provide.
   */
  private final Form form;
  /**
   * Create a FormServiceProvider.
   * @param form the Form to use.
   */
  public FormServiceProvider(Form form) {this.form=form;};

  public Object getService(BeanContextServices bcs, Object requestor, 
			   Class serviceClass, Object serviceSelector) {
    return form;
  };
  /**
   * Does Nothing. Required because inherited from BeanContextServiceProvider.
   */
  public void releaseService(BeanContextServices bcs, Object requestor, Object service) {
  };
  /**
   * Does Nothing. Required because inherited from BeanContextServiceProvider.
   */
  public Iterator getCurrentServiceSelectors(BeanContextServices bcs, Class serviceClass) {
    return null;
  };
};
  
