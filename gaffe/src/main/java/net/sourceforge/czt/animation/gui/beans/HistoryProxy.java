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

package net.sourceforge.czt.animation.gui.beans;

import java.awt.AWTEvent;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import java.beans.beancontext.BeanContextChildSupport;
import java.beans.beancontext.BeanContextServiceAvailableEvent;
import java.beans.beancontext.BeanContextServiceRevokedEvent;
import java.beans.beancontext.BeanContextServices;
import java.util.TooManyListenersException;

import javax.swing.event.EventListenerList;

import net.sourceforge.czt.animation.gui.history.History;
import net.sourceforge.czt.animation.gui.temp.SolutionSet;
import net.sourceforge.czt.animation.gui.temp.ZBinding;

/**
 * Bean that forwards events from the History object to any interested beans.
 */
public class HistoryProxy extends BeanContextChildSupport
{
  /**
	 * 
	 */
	private static final long serialVersionUID = 6027426440660049729L;

private History history_ = null;

  private final PropertyChangeListener pcListener = new PropertyChangeListener()
  {
    public void propertyChange(PropertyChangeEvent evt)
    {
      pcSupport.firePropertyChange(new PropertyChangeEvent(HistoryProxy.this,
          evt.getPropertyName(), evt.getOldValue(), evt.getNewValue()));
      if (evt.getPropertyName().equals("currentSolution")) {
        ActionListener[] listeners = (ActionListener[]) ell
            .getListeners(ActionListener.class);
        ActionEvent ev = new ActionEvent(this, AWTEvent.RESERVED_ID_MAX + 1,
            "History.currentSolution changed");
        for (int i = 0; i < listeners.length; i++)
          listeners[i].actionPerformed(ev);
      };
    };
  };

  private final EventListenerList ell = new EventListenerList();

  public HistoryProxy()
  {
    addPropertyChangeListener("beanContext", new PropertyChangeListener()
    {
      public void propertyChange(PropertyChangeEvent ev)
      {
        if (ev.getOldValue() != null
            && ev.getOldValue() instanceof BeanContextServices)
          ((BeanContextServices) ev.getOldValue())
              .removeBeanContextServicesListener(HistoryProxy.this);
        if (ev.getNewValue() != null
            && ev.getNewValue() instanceof BeanContextServices)
          ((BeanContextServices) ev.getNewValue())
              .addBeanContextServicesListener(HistoryProxy.this);
      };
    });
  };

  public SolutionSet getCurrentSolutionSet()
  {
    return history_.getCurrentSolutionSet();
  };

  public ZBinding getCurrentSolution()
  {
    return history_.getCurrentSolution();
  };

  public boolean hasCurrentSolution()
  {
    return history_ != null && history_.hasCurrentSolution();
  };

  public void serviceAvailable(BeanContextServiceAvailableEvent bcsae)
  {
    if (bcsae.getServiceClass().equals(History.class)) {
      try {
        history_ = (History) ((BeanContextServices) getBeanContext())
            .getService(this, this, History.class, null, this);
        history_.addPropertyChangeListener("currentSolution", pcListener);
        history_.addPropertyChangeListener("currentSolutionSet", pcListener);
      } catch (TooManyListenersException ex) {
      }
    }
  };

  public void serviceRevoked(BeanContextServiceRevokedEvent bcsre)
  {
    if (bcsre.getServiceClass().equals(History.class)) {
      history_.removePropertyChangeListener("currentSolution", pcListener);
      history_.removePropertyChangeListener("currentSolutionSet", pcListener);
      history_ = null;
    };
  };

  public void addActionListener(ActionListener l)
  {
    ell.add(ActionListener.class, l);
  };

  public void removeActionListener(ActionListener l)
  {
    ell.remove(ActionListener.class, l);
  };

  public ActionListener[] getActionListeners()
  {
    return (ActionListener[]) ell.getListeners(ActionListener.class);
  };
};
