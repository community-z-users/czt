/*
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

package net.sourceforge.czt.base.dom;

import net.sourceforge.czt.util.Visitor;
import org.w3c.dom.Document;

/**
 * <p>The base interface for all DOM visitors.</p>
 *
 * <p>A DOM visitor visits an AST for Z and builds a DOM representation
 * of the visited tree.  The {@link DomXmlWriter} can be used to
 * serialize the resulting DOM which gives an XML representation of the
 * AST.</P>
 *
 * @author Petra Malik
 */
public interface DomVisitor extends Visitor
{
  /**
   * Returns the document used for building the DOM.
   */
  public Document getDocument();

  /**
   * Sets the document used for building the DOM.
   */
  public void setDocument(Document doc);
}
