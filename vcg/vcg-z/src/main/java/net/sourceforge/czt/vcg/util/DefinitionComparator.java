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

import java.io.Serializable;
import java.util.Comparator;
import net.sourceforge.czt.z.util.ZUtils;

/**
 *
 * @author Leo Freitas
 * @date Nov 24, 2011
 */
public class DefinitionComparator implements Comparator<Definition>, Serializable
{

  /**
	 * 
	 */
	private static final long serialVersionUID = -3386230387378783217L;
private final boolean ignoreStrokes_;
  
  public DefinitionComparator()
  {
    this(false);
  }

  public DefinitionComparator(boolean ignoreStrokes)
  {
    this.ignoreStrokes_ = ignoreStrokes;
  }

  @Override
  public int compare(Definition o1, Definition o2)
  {
    // first compare by DefKind order
    int result = o1.getDefinitionKind().value() - o2.getDefinitionKind().value();
    if (result == 0)
    {
      // next by name order
      result = ignoreStrokes_ ? ZUtils.compareToIgnoreStrokes(o1.getDefName(), o2.getDefName()) :
                                ZUtils.compareTo(o1.getDefName(), o2.getDefName());

      // if the same binding, check if they come from the same schema name (e.g., handle name collusion)
      if (result == 0 && o1.getDefinitionKind().hasSchemaName())
      {
        result = ignoreStrokes_ ? ZUtils.compareToIgnoreStrokes(o1.getDefinitionKind().getSchName(), o2.getDefinitionKind().getSchName()) :
                                  ZUtils.compareTo(o1.getDefinitionKind().getSchName(), o2.getDefinitionKind().getSchName());
      }
    }
    return result;
  }
}
