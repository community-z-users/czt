/*
 * Copyright (C) 2011 Leo Freitas
 * This file is part of the CZT project.
 * 
 * The CZT project contains free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 * 
 * The CZT project is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License
 * along with CZT; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 */
package net.sourceforge.czt.vcg.util;

import java.util.Collections;
import java.util.Iterator;
import java.util.SortedSet;
import java.util.TreeSet;

/**
 *
 * @author Leo Freitas
 * @date Aug 31, 2011
 */
public final class BindingUtils
{

  private BindingUtils()
  {
  }

  public static final BindingFilter AFTER_FILTER  = new AfterBindings();
  public static final BindingFilter BEFORE_FILTER = new BeforeBindings();
  public static final BindingFilter INPUT_FILTER  = new InputBindings();
  public static final BindingFilter OUTPUT_FILTER = new OutputBindings();
  public static final BindingFilter STATE_FILTER  = new StateBindings();
  public static final BindingFilter DASHED_FILTER = new DashedBindings();
  public static final BindingFilter INIT_FILTER   = new InitBindings();
  public static final BindingFilter FIN_FILTER   = new FinBindings();

  /**
   * Filter the given set of bindings according to the binding filter criteria given.
   * These are usually for before or after bindings, but could vary according to the user.
   * @param bindings
   * @param filter
   * @return
   */
  public static SortedSet<Definition> filterBindings(SortedSet<Definition> bindings, BindingFilter filter)
  {
    SortedSet<Definition> result = new TreeSet<Definition>(bindings);
    if (!result.isEmpty())
    {
      Iterator<Definition> it = result.iterator();
      while (it.hasNext())
      {
        Definition def = it.next();
        // if this name is not to be considered, then remove it
        if (!filter.considerName(def.getDefName()))
        {
          it.remove();
        }
      }
      assert bindings.containsAll(result);
    }
    return result;
  }

  public static SortedSet<Definition> beforeBindingsOf(SortedSet<Definition> bindings)
  {
    return filterBindings(bindings, BEFORE_FILTER);
  }

  public static SortedSet<Definition> afterBindingsOf(SortedSet<Definition> bindings)
  {
    return filterBindings(bindings, AFTER_FILTER);
  }

  public static SortedSet<Definition> inputBindingsOf(SortedSet<Definition> bindings)
  {
    return filterBindings(bindings, INPUT_FILTER);
  }

  public static SortedSet<Definition> outputBindingsOf(SortedSet<Definition> bindings)
  {
    return filterBindings(bindings, OUTPUT_FILTER);
  }

  public static SortedSet<Definition> stateBindingsOf(SortedSet<Definition> bindings)
  {
    return filterBindings(bindings, STATE_FILTER);
  }

  public static SortedSet<Definition> initBindingsOf(SortedSet<Definition> bindings)
  {
    return filterBindings(bindings, INIT_FILTER);
  }

  public static SortedSet<Definition> dashedBindingsOf(SortedSet<Definition> bindings)
  {
    return filterBindings(bindings, DASHED_FILTER);
  }

  public static boolean bindingsInvariant(SortedSet<Definition> mixed, SortedSet<Definition> before, SortedSet<Definition> after)
  {
    return Collections.disjoint(before, after)
          && mixed.containsAll(after)
          && mixed.containsAll(before)
          && (before.size() + after.size() == mixed.size());
  }
}
