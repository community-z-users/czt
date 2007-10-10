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

/**
 * Represents a registration of a listener with a bean.
 */
public class BeanLink
{
  public final Object source, listener;

  public final Class<?> listenerType;

  public BeanLink(Object source, Object listener, Class<?> listenerType)
  {
    this.source = source;
    this.listener = listener;
    this.listenerType = listenerType;
  };

  public boolean equals(Object obj)
  {
    if (!(obj instanceof BeanLink))
      return false;
    BeanLink bl = (BeanLink) obj;
    return bl.source == source && bl.listener == listener
        && bl.listenerType.equals(listenerType);
  };

  public int hashCode()
  {
    return source.hashCode() + listener.hashCode() + listenerType.hashCode();
  };
};
