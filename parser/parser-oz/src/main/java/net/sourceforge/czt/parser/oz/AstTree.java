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

import javax.swing.Icon;
import javax.swing.JTree;
import javax.swing.tree.DefaultTreeCellRenderer;
import javax.swing.tree.TreeSelectionModel;

/**
 * An AST Tree.
 */
public class AstTree extends JTree
{
  /**
	 * 
	 */
	private static final long serialVersionUID = 564950389196626734L;
AstTreeModel model_;

  public AstTree(TermModel termModel)
  {
    super(new AstTreeModel(termModel));
    getSelectionModel().setSelectionMode(
                 TreeSelectionModel.SINGLE_TREE_SELECTION);
    DefaultTreeCellRenderer renderer = new DefaultTreeCellRenderer();
    Icon icon = null;
    renderer.setLeafIcon(icon);
    renderer.setClosedIcon(icon);
    renderer.setOpenIcon(icon);
    setCellRenderer(renderer);
  }
}
