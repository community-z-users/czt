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
 * Event object used by {@link DesignerCore} to
 * notify listeners when a form has been created or deleted.
 */
public class FormDesignEvent extends EventObject
{
  /**
	 * 
	 */
	private static final long serialVersionUID = 557169969963727029L;

/**
   * Value for <code>id_</code> indicating whether this event shows that a form
   * was created.
   */
  public static final int CREATED = 0;

  /**
   * Value for <code>id_</code> indicating whether this event shows that a form
   * was deleted.
   */
  public static final int DELETED = 1;

  /**
   * Member indicating what type of FormDesignEvent this is.  May be either
   * <code>ADDED</code> or <code>REMOVED</code>.
   */
  protected final int id_;

  /**
   * The form that was created/deleted.
   */
  protected final FormDesign formDesign_;

  /**
   * Create a <code>FormDesignEvent</code> notifying that <code>form</code> has
   * been created/removed.
   */
  public FormDesignEvent(Object source, FormDesign formDesign, int id)
  {
    super(source);
    formDesign_ = formDesign;
    id_ = id;
  };

  /**
   * Returns the <code>FormDesign</code>.
   */
  public FormDesign getFormDesign()
  {
    return formDesign_;
  };

  /**
   * Returns id_.
   */
  public int getId()
  {
    return id_;
  };
};
