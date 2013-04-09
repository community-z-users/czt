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

package net.sourceforge.czt.animation.gui.design;

import java.util.EventObject;

/**
 * Event triggered when a bean is selected in the {@link FormDesign}.
 */
public class BeanSelectedEvent extends EventObject
{
  /**
	 * 
	 */
	private static final long serialVersionUID = -4823982742775610504L;
private Object bean;

  //XXX should it have the beanwrapper/component for the bean as well as/instead
  //    of the bean.
  public BeanSelectedEvent(FormDesign beansForm, Object selectedBean)
  {
    super(beansForm);
    bean = selectedBean;
  };

  public FormDesign getSelectedBeansForm()
  {
    return (FormDesign) getSource();
  };

  public Object getSelectedBean()
  {
    return bean;
  };
};
