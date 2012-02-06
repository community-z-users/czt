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

package net.sourceforge.czt.parser.util;

import java.util.Collections;
import java.util.HashSet;
import java.util.Set;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.z.ast.Parent;
import net.sourceforge.czt.z.ast.ZSect;

/**
 *
 * @author Leo Freitas
 * @date Jan 27, 2012
 */
public class DependenciesBuilder {

  private final Set<Key<?>> dependencies_ = new HashSet<Key<?>>();

  public <T> DependenciesBuilder self(ZSect sect, Class<T> type)
  {
    dependencies_.add(new Key<T>(sect.getName(), type));
    return this;
  }

  public <T> DependenciesBuilder parents(ZSect sect, Class<T> type)
  {
    for(Parent p : sect.getParent())
    {
      dependencies_.add(new Key<T>(p.getWord(), type));
    }
    return this;
  }

  public DependenciesBuilder add(Key<?> key)
  {
    dependencies_.add(key);
    return this;
  }
  
  public DependenciesBuilder add(Set<? extends Key<?>> keys)
  {
    dependencies_.addAll(keys);
    return this;
  }

  public Set<Key<?>> build()
  {
    return Collections.unmodifiableSet(dependencies_);
  }
}
