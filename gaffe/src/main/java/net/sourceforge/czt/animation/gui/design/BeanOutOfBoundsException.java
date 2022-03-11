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

import java.awt.Point;
import java.awt.Rectangle;

/**
 * Triggered when a component bean is placed outside the form, or a
 * non-component bean is placed inside it.
 */
public class BeanOutOfBoundsException extends Exception
{
  /**
	 * 
	 */
	private static final long serialVersionUID = 670944014238126764L;

private Class<?> type_;

  private Point attemptedLocation_;

  private Rectangle formBounds_;

  public BeanOutOfBoundsException(Class<?> type, Point attemptedLocation,
      Rectangle formBounds)
  {
    super("BeanOutOfBoundsException: Attempted to place " + type.getName()
        + (formBounds.contains(attemptedLocation) ? " in" : " out")
        + "side the Form, which is not allowed.  Attempted location = "
        + attemptedLocation + "; Form bounds = " + formBounds + ".");
    type_ = type;
    attemptedLocation_ = attemptedLocation;
    formBounds_ = formBounds;
  };

  public Class<?> getType()
  {
    return type_;
  };

  public Point getAttemptedLocation()
  {
    return attemptedLocation_;
  };

  public Rectangle getFormBounds()
  {
    return formBounds_;
  };
};
