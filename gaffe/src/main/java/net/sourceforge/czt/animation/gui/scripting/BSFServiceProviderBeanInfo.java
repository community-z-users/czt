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

package net.sourceforge.czt.animation.gui.scripting;

import java.beans.BeanInfo;
import java.beans.IntrospectionException;
import java.beans.Introspector;
import java.beans.SimpleBeanInfo;
import java.beans.beancontext.BeanContextServiceProviderBeanInfo;

import org.apache.bsf.BSFManager;

/**
 * <code>BeanInfo</code> for <code>BSFServiceProvider</code>.
 */
class BSFServiceProviderBeanInfo extends SimpleBeanInfo
    implements
      BeanContextServiceProviderBeanInfo
{
  /**
   * Returns <code>BeanInfo</code>s for the services provided by
   * <code>BSFServiceProvider</code>.
   */
  public BeanInfo[] getServicesBeanInfo()
  {
    try {
      return new BeanInfo[]{Introspector.getBeanInfo(BSFManager.class)};
    } catch (IntrospectionException e) {
      throw new Error("Could not get BeanInfo for BSFManager!:" + e);
    }
  };
};
