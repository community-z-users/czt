/*
  Copyright 2003, 2005 Petra Malik
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

package net.sourceforge.czt.gnast.schema;

import javax.xml.transform.TransformerException;

import com.sun.org.apache.xpath.internal.XPathAPI;
import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.Node;
import org.w3c.dom.traversal.NodeIterator;

import net.sourceforge.czt.gnast.GnastException;

/**
 * This class provides access to the Xalan XPath API.
 * All evaluations of XPath expressions are with respect
 * to the document given in the constructor.
 * Currently, a fixed set of namespace prefixes (<code>xs</code> and
 * <code>jaxb</code>) is provided.  In case a new prefix
 * is needed, the namespace node of this class must be modified.
 *
 * @author Petra Malik
 */
@SuppressWarnings("restriction")
public class XPath
{
  // ############################################################
  // ##################### MEMBER VARIABLES #####################
  // ############################################################

  /**
   * The node from which prefixes in the XPath will be resolved to namespaces.
   * Currently supports prefixes <code>jaxb</code> and <code>xs</code>.
   */
  protected Element namespaceNode_;

  /**
   * The document used to process the XPath expressions.
   */
  private Document document_;

  // ############################################################
  // ####################### CONSTRUCTORS #######################
  // ############################################################

  /**
   * Creates a new XPath accessor for the given document.
   */
  public XPath(Document doc)
  {
    document_ = doc;

    namespaceNode_ = doc.createElement("namespace");
    namespaceNode_.setAttribute("xmlns:xs",
                                "http://www.w3.org/2001/XMLSchema");
    namespaceNode_.setAttribute("xmlns:jaxb",
                                "http://java.sun.com/xml/ns/jaxb");
    namespaceNode_.setAttribute("xmlns:gnast",
                                "http://czt.sourceforge.net/gnast");
  }

  /**
   * Use the given XPath expression to select a single node.
   * A {@link GnastException} is thrown in case a transformer
   * error occurs.
   *
   * @param node the context node to start searching from.
   * @param xPathExpr the XPath expression.
   */
  public Node selectSingleNode(Node node, String xPathExpr)
  {
    try {
      return XPathAPI.selectSingleNode(node, xPathExpr, namespaceNode_);
    }
    catch (TransformerException e) {
      throw new GnastException(e);
    }
  }
  public Node selectSingleNode(String xPathExpr)
  {
    return selectSingleNode(document_, xPathExpr);
  }

  /**
   * Use the given XPath expression to select a node list.
   * A {@link GnastException} is thrown in case a transformer
   * error occurs.
   */
  public NodeIterator selectNodeIterator(Node node, String xPathExpr)
  {
    try {
      return XPathAPI.selectNodeIterator(node, xPathExpr, namespaceNode_);
    }
    catch (TransformerException e) {
      throw new GnastException(e);
    }
  }
  public NodeIterator selectNodeIterator(String xPathExpr)
  {
    return selectNodeIterator(document_, xPathExpr);
  }

  /**
   * Returns the attribute value of the attribute whos name is
   * <code>string</code> for the given node or <code>null</code> if
   * the attribute is not present.
   */
  public String getNodeValue(Node node, String string)
  {
    try {
      return selectSingleNode(node, string).getNodeValue();
    }
    catch (NullPointerException e) {
      return null;
    }
  }

  public String getNodeValue(String string)
  {
    return getNodeValue(document_, string);
  }
}
