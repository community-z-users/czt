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

import java.beans.BeanInfo;
import java.beans.DefaultPersistenceDelegate;
import java.beans.Encoder;
import java.beans.Expression;
import java.beans.IntrospectionException;
import java.beans.Introspector;

import net.sourceforge.czt.animation.gui.util.IntrospectionHelper;
import net.sourceforge.czt.animation.gui.beans.ResourceIcon;

public class ResourceIconDelegate extends DefaultPersistenceDelegate {
  private ResourceIconDelegate() {};
  private static final ResourceIconDelegate singleton=new ResourceIconDelegate();

  public static void registerDelegate() {
    try {
      final BeanInfo beanInfo=Introspector.getBeanInfo(ResourceIcon.class);
      IntrospectionHelper.rememberBeanInfo(beanInfo);
      beanInfo.getBeanDescriptor().setValue("persistenceDelegate", singleton);
    } catch (IntrospectionException ex) {
      throw new Error("Shouldn't get IntrospectionException examining ResourceIcon from "
		      +"ResourceIconDelegate."+ex);
    }
  };

  protected boolean mutatesTo(Object oldInstance, Object newInstance) {
    return newInstance!=null;
  };
  protected Expression instantiate(Object oldInstance, Encoder out) {
    ResourceIcon oldIcon=(ResourceIcon)oldInstance;
    return new Expression(oldIcon,ResourceIcon.class,"new",
			  new Object[] {oldIcon.getURL()});
  };

};
