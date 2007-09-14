/**
Copyright (C) 2007 Mark Utting
This file is part of the CZT project.

The CZT project contains free software; you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation; either version 2 of the License, or
(at your option) any later version.

The CZT project is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with CZT; if not, write to the Free Software
Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
*/

package net.sourceforge.czt.modeljunit;

import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import net.sourceforge.czt.modeljunit.coverage.ActionCoverage;
import net.sourceforge.czt.modeljunit.coverage.StateCoverage;
import net.sourceforge.czt.modeljunit.coverage.TransitionCoverage;
import net.sourceforge.czt.modeljunit.coverage.TransitionPairCoverage;

/** This singleton object defines all the pre-defined model listeners
 *  (and coverage metrics).
 *  Each new Model object uses this object to create listeners that
 *  are requested via name.  So you can make new pre-defined listeners
 *  available to all Models simply by adding them this object.
 *  You can also override the class of one of the existing
 *  pre-defined listeners -- that new class will be used when the
 *  next instance of that kind of listener is created.
 *
 * @author marku
 */
public class ListenerFactory
{
  private Map<String, Class<? extends ModelListener>> known_;
  private static ListenerFactory factory_;

  protected ListenerFactory()
  {
    known_ = new HashMap<String, Class<? extends ModelListener>>();
    known_.put("graph", GraphListener.class);
    known_.put("verbose", VerboseListener.class);
    known_.put("action coverage", ActionCoverage.class);
    known_.put("state coverage", StateCoverage.class);
    known_.put("transition coverage", TransitionCoverage.class);
    known_.put("transition pair coverage", TransitionPairCoverage.class);
  }

  /** Returns the singleton instance of this factory class. */
  public static ListenerFactory getFactory()
  {
    if (factory_ == null) {
      factory_ = new ListenerFactory();
    }
    return factory_;
  }

  /** Gets a pre-defined listener, or null if one is not known.
   * The names used as parameters to this method are not the Java
   * class names, but the informal lowercase name of the resulting
   * Listener object.  For example, requesting "transition coverage"
   * will return an instance of class TransitionCoverage (by default).
   *
   * @param name  The non-null name of a listener.
   * @return      A fresh instance of the requested kind of listener.
   */
  public ModelListener getListener(String name)
  {
    Class<? extends ModelListener> clazz = known_.get(name);
    if (clazz == null) {
      return null;
    }
    else {
      try {
        return clazz.newInstance();
      }
      catch (Exception ex) {
        throw new RuntimeException("Exception while creating new "
            +clazz.getName()+" listener.", ex);
      }
    }
  }

  /** Returns the class that will be used to create the given kind of
   *  listeners, or null if unknown.  For example, this can be useful
   *  for a tool that wants to create metrics for a HistoryCoverage wrapper.
   *
   * @param name The non-null name of a listener.
   * @return     The appropriate subclass of ModelListener, or null.
   */
  public Class<? extends ModelListener> getListenerClass(String name)
  {
    return known_.get(name);
  }

  /** Defines a new kind of pre-defined listener.
   *
   * @param name  The name used to refer to this class of listener.
   *   This should usually be the same as the name of the listener instances.
   * @param clazz Which listener should be created by each getListener call.
   * @return      The previous listener class (or null if none).
   */
  public Class<? extends ModelListener> putListener(String name,
      Class<? extends ModelListener> clazz)
  {
    Class<? extends ModelListener> result = known_.get(name);
    known_.put(name, clazz);
    return result;
  }

  /** Remove the listener class associated with name.
   *  @param name  The name of a predefined kind of listener.
   *  @return      The removed class, or null.
   */
  public Class<? extends ModelListener> removeListener(String name)
  {
    return known_.remove(name);
  }

  /** Returns all the known names of predefined listeners. */
  public Set<String> getNames()
  {
    return known_.keySet();
  }
}
