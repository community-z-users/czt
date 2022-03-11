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

import java.beans.beancontext.BeanContextServiceProvider;
import java.beans.beancontext.BeanContextServices;
import java.util.Iterator;

import org.apache.bsf.BSFManager;

/**
 * Provides access to scripting with the BSF manager via bean contexts.
 */
public final class BSFServiceProvider implements BeanContextServiceProvider
{
  /**
   * The BSFManager to provide.
   */
  private final BSFManager bsfManager;

  /**
   * Create a BSFServiceProvider.
   * @param bsfm The BSFManager to use.
   */
  public BSFServiceProvider(BSFManager bsfm)
  {
    bsfManager = bsfm;
  };

  /**
   * Returns the BSFManager.  Inherits from BeanContextServiceProvider.
   */
  public Object getService(BeanContextServices bcs, Object requestor,
      @SuppressWarnings("rawtypes") Class serviceClass, Object serviceSelector)
  {
    return bsfManager;
  };

  /**
   * Does Nothing.  Required because inherited from BeanContextServiceProvider.
   */
  public void releaseService(BeanContextServices bcs, Object requestor,
      Object service)
  {
    //do nothing
  };

  /**
   * Does Nothing.  Required because inherited from BeanContextServiceProvider.
   */
  @SuppressWarnings("rawtypes") 
  public Iterator getCurrentServiceSelectors(BeanContextServices bcs,
      Class serviceClass)
  {
    //do nothing
    return null;
  };
};
