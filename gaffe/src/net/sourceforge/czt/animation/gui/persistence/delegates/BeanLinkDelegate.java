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
package net.sourceforge.czt.animation.gui.persistence.delegates;

import net.sourceforge.czt.animation.gui.design.FormDesign;
import java.beans.BeanInfo;
import java.beans.DefaultPersistenceDelegate;
import java.beans.Encoder;
import java.beans.Expression;
import java.beans.IntrospectionException;
import java.beans.Introspector;

public class BeanLinkDelegate extends DefaultPersistenceDelegate {
  private BeanLinkDelegate() {};
  private static final BeanLinkDelegate singleton=new BeanLinkDelegate();

  //Have to keep a strong reference to get around bug #4646747
  //Mentioned here:
  //http://java.sun.com/products/jfc/tsc/articles/persistence4/index.html
  private static final BeanInfo beanInfo;  
  static {
    try {
      beanInfo=Introspector.getBeanInfo(FormDesign.BeanLink.class);
    } catch (IntrospectionException ex) {
      throw new Error("Shouldn't get IntrospectionException examining BeanLink from "
		      +"BeanLinkDelegate."+ex);
    }
  };
  
  public static void registerDelegate() {
      beanInfo.getBeanDescriptor().setValue("persistenceDelegate", singleton);
  };
  protected boolean mutatesTo(Object oldInstance, Object newInstance) {
    return newInstance!=null;
  };
  protected Expression instantiate(Object oldInstance, Encoder out) {
    FormDesign.BeanLink oldLink=(FormDesign.BeanLink)oldInstance;
    System.err.println("@@B");
    return new Expression(oldLink,FormDesign.BeanLink.class,"new",
			  new Object[] {oldLink.source,
					oldLink.listener,
					oldLink.listenerType});
  };
};
