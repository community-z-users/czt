/**
Copyright 2003 Mark Utting
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
package net.sourceforge.czt.parser.oz;

import java.util.Vector;

import javax.swing.event.TreeModelListener;
import javax.swing.tree.TreeModel;
import javax.swing.tree.TreePath;

public class AstTreeModel
  implements TreeModel
{
  /**
   * The list of tree model listeners.
   */
  private Vector<TreeModelListener> treeModelListeners_ = new Vector<TreeModelListener>();

  /**
   * The root of the AST.
   */
  private TermModel root_;

  public AstTreeModel(TermModel root)
  {
    root_ = root;
  }

  public Object getChild(Object parent, int index)
  {
    if (parent instanceof TermModel) {
      TermModel termModel = (TermModel) parent;
      return termModel.getChild(index);
    }
    return null;
  }

  public int getChildCount(Object parent)
  {
    if (parent instanceof TermModel) {
      TermModel termModel = (TermModel) parent;
      return termModel.size();
    }
    return 0;
  }

  public int getIndexOfChild(Object parent, Object child)
  {
    if (parent instanceof TermModel) {
      TermModel termModel = (TermModel) parent;
      return termModel.getIndexOf(child);
    }
    return -1;
  }

  public Object getRoot()
  {
    return root_;
  }

  public boolean isLeaf(Object node)
  {
    return getChildCount(node) == 0;
  }

  public void addTreeModelListener(TreeModelListener l)
  {
    treeModelListeners_.addElement(l);
  }

  public void removeTreeModelListener(TreeModelListener l)
  {
    treeModelListeners_.removeElement(l);
  }

  /**
   * Not used by this model.
   */
  public void valueForPathChanged(TreePath path, Object newValue)
  {
    System.out.println("*** valueForPathChanged : "
                       + path + " --> " + newValue);
  }
}
