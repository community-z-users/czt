/**
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

package net.sourceforge.czt.base.util;

import java.util.Enumeration;
import java.util.List;
import java.util.Vector;
import java.util.Arrays;
import javax.swing.tree.TreeNode;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.ast.TermA;

/**
 * A node of an AST that can be used as a tree node in a JTree.
 *
 * @author Petra Malik
 */
public class TermTreeNode
  implements TreeNode
{
  private int pos_;
  private Object node_;
  private TermTreeNode parent_;

  public TermTreeNode(int pos, Object node, TermTreeNode parent)
  {
    pos_ = pos;
    node_ = node;
    parent_ = parent;
  }

  public TreeNode getChildAt(int index)
  {
    if (node_ instanceof Term) {
      Term term = (Term) node_;
      Object[] anns = null;
      Object[] children = term.getChildren();      
      if (term instanceof TermA)  {
          TermA ta = (TermA)term;
          if (ta.getAnns() != null) {
            anns = ta.getAnns().toArray();
          }
      }
      if (index < children.length) {
        return new TermTreeNode(index, children[index], this);
      }
      else if (index < children.length+anns.length) {
        return new TermTreeNode(index, anns[index-children.length], this);
      }
    }
    return null;
  }

  public int getChildCount()
  {
    if (node_ instanceof Term) {
      Term term = (Term) node_;
      int result = term.getChildren().length;
      if (term instanceof TermA) {
        TermA ta = (TermA)term;
        if (ta.getAnns() != null) {
            result += ta.getAnns().size();
        }
      }
      return result;
    }
    return 0;
  }

  public TreeNode getParent()
  {
    return parent_;
  }

  public int getIndex(TreeNode node)
  {
    return ((TermTreeNode) node).pos_;
  }

  public boolean getAllowsChildren()
  {
    return ! isLeaf();
  }

  public boolean isLeaf()
  {
    return getChildCount() == 0;
  }

  public Enumeration children()
  {
    Vector childNodes = new Vector();
    for (int i = 0; i < getChildCount(); i++) {
      childNodes.add(getChildAt(i));
    }
    return childNodes.elements();
  }

  public String toString()
  {
    if (node_ instanceof List) {
      return "List[" + ((List)node_).size()+ "]";
    }
    else if (node_ != null) {
      return node_.toString();
    }
    return "null";
  }
}
