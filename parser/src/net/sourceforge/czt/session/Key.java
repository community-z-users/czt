/*
  Copyright (C) 2004 Petra Malik
  Copyright (C) 2004 Mark Utting
  This file is part of the czt project.

  The czt project contains free software; you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation; either version 2 of the License, or
  (at your option) any later version.

  The czt project is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with czt; if not, write to the Free Software
  Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
*/

package net.sourceforge.czt.session;

/** A Key is a pair (String,Class). */
public class Key
{
  private String name_;
  private Class type_;

  public Key(String name, Class type)
  {
    name_ = name;
    type_ = type;
  }

  public String getName()
  {
    return name_;
  }

  public Class getType()
  {
    return type_;
  }

  public int hashCode()
  {
    return name_.hashCode() + type_.hashCode();
  }

  public boolean equals(Object other)
  {
    if (other == null || ! (other instanceof Key))
      return false;
    Key key2 = (Key) other;
    return name_.equals(key2.name_) && type_.equals(key2.type_);
  }

  public String toString()
  {
    return "("+name_+","+type_+")";
  }
}
