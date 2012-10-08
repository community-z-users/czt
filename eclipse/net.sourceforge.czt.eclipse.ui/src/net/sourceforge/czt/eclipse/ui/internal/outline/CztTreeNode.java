
package net.sourceforge.czt.eclipse.ui.internal.outline;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import net.sourceforge.czt.base.ast.Term;

import org.eclipse.jface.text.Position;

/**
 * @author Chengdong Xu
 */
public class CztTreeNode
{
  private Object source_ = null;

  private Term term_ = null;

  private Position range_ = null;

  private Position namePosition_ = null;

  private CztTreeNode parent_ = null;

  private List<CztTreeNode> children_ = new ArrayList<CztTreeNode>();

  public CztTreeNode(Object source, Term term)
  {
    this(source, term, null, null);
  }

  public CztTreeNode(Object source, Term term, Position range)
  {
    this(source, term, range, range);
  }

  public CztTreeNode(Object source, Term term, Position range,
      Position namePosition)
  {
    source_ = source;
    term_ = term;
    range_ = range;
    
    if (namePosition == null)
      namePosition_ = range_;
    else
      namePosition_ = namePosition;
  }

  public Object getSource()
  {
    return source_;
  }

  public void setSource(Object source)
  {
    source_ = source;
  }

  public Term getTerm()
  {
    return term_;
  }

  public void setTerm(Term term)
  {
    term_ = term;
  }

  public Position getRange()
  {
    return range_;
  }

  public void setRange(Position range)
  {
    range_ = range;
  }

  public Position getNamePosition()
  {
    return namePosition_;
  }

  public void setNamePosition(Position namePosition)
  {
    namePosition_ = namePosition;
  }

  public CztTreeNode getParent()
  {
    return parent_;
  }

  public void setParent(CztTreeNode parent)
  {
    parent_ = parent;
    if (parent != null)
      parent.addChild(this);
  }

  public CztTreeNode getChild(int index)
  {
    return children_.get(index);
  }

  public List<CztTreeNode> getChildren()
  {
    return children_;
  }

  public void addChild(CztTreeNode child)
  {
    if (child == null)
      return;
    if (!children_.contains(child)) {
      children_.add(child);
      child.setParent(this);
    }
  }

  public void addChild(int index, CztTreeNode child)
  {
    if (child == null)
      return;
    if (!children_.contains(child)) {
      children_.add(index, child);
      child.setParent(this);
    }
  }

  public CztTreeNode removeChild(int index)
  {
    CztTreeNode child = children_.remove(index);
    if (child == null)
      return null;
    if (child.getParent() != null)
      if (child.getParent().equals(this))
        child.setParent(null);

    return child;
  }

  public boolean removeChild(CztTreeNode child)
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

  public void addAllChildren(Collection<? extends CztTreeNode> children)
  {
    for (CztTreeNode child : children) {
      addChild(child);
    }
  }

  public void addAllChildren(int index,
      Collection<? extends CztTreeNode> children)
  {
    for (CztTreeNode child : children) {
      addChild(index++, child);
    }
  }

  public boolean removeAllChildren(Collection<? extends CztTreeNode> children)
  {
    for (CztTreeNode child : children) {
      if (!removeChild(child))
        return false;
    }
    return true;
  }

  public String toString()
  {
    return String.valueOf(term_);
  }
}
