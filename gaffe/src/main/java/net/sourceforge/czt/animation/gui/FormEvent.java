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

package net.sourceforge.czt.animation.gui;

import java.util.EventObject;

/**
 * Event object used by {@link net.sourceforge.czt.animation.gui.Form Form} to
 * notify listeners when a bean has been added or removed.
 */
public class FormEvent extends EventObject
{
  /**
	 * 
	 */
	private static final long serialVersionUID = 6064692693347880232L;

/**
   * Value for <code>id_</code> indicating whether this event shows that a bean
   *  was added.
   */
  public static final int ADDED = 0;

  /**
   * Value for <code>id_</code> indicating whether this event shows that a bean
   * was removed.
   */
  public static final int REMOVED = 1;

  /**
   * Member indicating what type of FormEvent this is.  May be either
   * <code>ADDED</code> or <code>REMOVED</code>.
   */
  protected final int id_;

  /**
   * The bean that was added/removed.
   */
  protected final Object bean_;

  /**
   * Create a <code>FormEvent</code> notifying that <code>bean</code> has been
   *  added/removed to/from <code>source</code>.
   */
  public FormEvent(Object source, Object bean, int id)
  {
    super(source);
    bean_ = bean;
    id_ = id;
  };

  /**
   * Returns the bean.
   */
  public Object getBean()
  {
    return bean_;
  };

  /**
   * Returns id_.
   */
  public int getId()
  {
    return id_;
  };
};
