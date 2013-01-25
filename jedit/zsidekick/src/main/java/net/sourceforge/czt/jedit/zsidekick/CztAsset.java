/*
 * CztAsset.java
 * Copyright (C) 2006 Petra Malik
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA  02111-1307, USA.
 */
package net.sourceforge.czt.jedit.zsidekick;

import javax.swing.Icon;
import javax.swing.text.Position;

import sidekick.*;

public class CztAsset
  extends Asset
{
  private String description_;

  public CztAsset(String name, String description,
                  Position start, Position end)
  {
    super(name == null ? "unknown" : name);
    description_ = description;
    setStart(start);
    setEnd(end);
  }

  public Icon getIcon()
  {
    return null;
  }

  public String getLongString()
  {
    return description_;
  }

  public String getShortString()
  {
    return getName();
  }
}
