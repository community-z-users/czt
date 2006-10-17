/*
 * CztSegment.java
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

package net.sourceforge.czt.eclipse.outline;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import org.eclipse.jface.text.Position;

/**
 * @author Chengdong Xu
 */
public class CztSegment
{
  private Object source_ = null;

  private Segment segment_ = null;

  private Position range_ = null;

  private Position namePosition_ = null;

  private CztSegment parent_ = null;

  private List<CztSegment> children_ = new ArrayList<CztSegment>();

  public CztSegment(Object source, Segment segment)
  {
    source_ = source;
    this.segment_ = segment;
  }

  public CztSegment(Object source, Segment segment, Position range)
  {
    source_ = source;
    this.segment_ = segment;
    this.range_ = this.namePosition_ = range;
  }

  public CztSegment(Object source, Segment segment, Position range,
      Position namePosition)
  {
    this(source, segment, range);
    if (namePosition != null)
      this.namePosition_ = namePosition;
  }

  public Object getSource()
  {
    return source_;
  }

  public void setSource(Object source)
  {
    source_ = source;
  }

  public String getName()
  {
    if (this.segment_ == null)
      return null;
    return this.segment_.getName();
  }

  public Segment getSegment()
  {
    return this.segment_;
  }

  public void setSegment(Segment segment)
  {
    this.segment_ = segment;
  }

  public Position getRange()
  {
    return this.range_;
  }

  public void setRange(Position range)
  {
    this.range_ = range;
  }

  public Position getNamePosition()
  {
    return this.namePosition_;
  }

  public void setNamePosition(Position namePosition)
  {
    this.namePosition_ = namePosition;
  }

  public CztSegment getParent()
  {
    return parent_;
  }

  public void setParent(CztSegment parent)
  {
    if (parent_ == null) {
      parent_ = parent;
      if (parent != null)
        parent.addChild(this);
    }
    else {

    }

  }

  public CztSegment getChild(int index)
  {
    return children_.get(index);
  }

  public List<CztSegment> getChildren()
  {
    return children_;
  }

  public void addChild(CztSegment child)
  {
    if (child == null)
      return;
    if (!children_.contains(child)) {
      children_.add(child);
      child.setParent(this);
    }
  }

  public void addChild(int index, CztSegment child)
  {
    if (child == null)
      return;
    if (!children_.contains(child)) {
      children_.add(index, child);
      child.setParent(this);
    }
  }

  public CztSegment removeChild(int index)
  {
    CztSegment child = children_.remove(index);
    if (child == null)
      return null;
    if (child.getParent() != null)
      if (child.getParent().equals(this))
        child.setParent(null);

    return child;
  }

  public boolean removeChild(CztSegment child)
  {
    boolean success = children_.remove(child);
    if (child == null)
      return success;
    if (child.getParent() == null)
      return success;
    if (child.getParent().equals(this))
      child.setParent(null);

    return success;
  }

  public void addAllChildren(Collection<? extends CztSegment> children)
  {
    for (CztSegment child : children) {
      addChild(child);
    }
  }

  public void addAllChildren(int index,
      Collection<? extends CztSegment> children)
  {
    for (CztSegment child : children) {
      addChild(index++, child);
    }
  }

  public boolean removeAllChildren(Collection<? extends CztSegment> children)
  {
    for (CztSegment child : children) {
      if (!removeChild(child))
        return false;
    }
    return true;
  }

  public String toString()
  {
    if (this.segment_ == null)
      return null;
    return this.segment_.getName();
  }
}
