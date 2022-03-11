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

package net.sourceforge.czt.animation.gui.history;

import java.beans.beancontext.BeanContextServiceProvider;
import java.beans.beancontext.BeanContextServices;
import java.util.Iterator;

/**
 * <code>BeanContextServiceProvider</code> for the {@link History}.
 * Allows beans to access the animation history object via their BeanContext.
 */
public final class HistoryServiceProvider implements BeanContextServiceProvider
{
  /**
   * The History to provide.
   */
  private final History history_;

  /**
   * Create a HistoryServiceProvider.
   * @param history the History to use.
   */
  public HistoryServiceProvider(History history)
  {
    history_ = history;
  };

  /**
   * Returns the History. Inherits from BeanContextServiceProvider.
   */
  public Object getService(BeanContextServices bcs, Object requestor,
      @SuppressWarnings("rawtypes") Class serviceClass, Object serviceSelector)
  {
    return history_;
  };

  /**
   * Does Nothing. Required because inherited from BeanContextServiceProvider.
   */
  public void releaseService(BeanContextServices bcs, Object requestor,
      Object service)
  {
  };

  /**
   * Does Nothing. Required because inherited from BeanContextServiceProvider.
   */
  @SuppressWarnings("rawtypes")
public Iterator getCurrentServiceSelectors(BeanContextServices bcs,
      Class serviceClass)
  {
    return null;
  };
};
