/*
Copyright (C) 2003, 2004 Mark Utting
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

import java.io.*;
import java.util.logging.Logger;

import javax.xml.parsers.*;
import javax.xml.transform.*;
import javax.xml.transform.dom.DOMSource;
import javax.xml.transform.stream.*;

import org.apache.xml.serialize.*;
import org.w3c.dom.*;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.util.XmlWriter;

/**
 * An XML marshaller using DOM.
 *
 * @author Petra Malik
 */
public class DomXmlWriter implements XmlWriter
{
  /**
   * The visitor used for translating the AST into a DOM tree.
   */
  private DomVisitor visitor_;

  /**
   * Creates a new DomXmlWriter.
   *
   * @param visitor the visitor to be used for translating the
   *        AST into a DOM tree.
   */
  public DomXmlWriter(DomVisitor visitor)
  {
    visitor_ = visitor;
  }

  /**
   * The class name of this class; used for logging purposes.
   *
   * @return the name of this class.
   */
  private String getClassName()
  {
    return "DomXmlWriter";
  }

  /**
   * Returns the logger.
   *
   * @return the logger.
   */
  private Logger getLogger()
  {
    return Logger.getLogger("net.sourceforge.czt.base.dom"
                            + getClassName());
  }

  /**
   * Returns the DOM document.
   *
   * @param term the root of the AST to be transformed into DOM.
   * @return the DOM document containing the transformed AST.
   */
  private Document getDocument(Term term)
  {
    Document document = null;
    DocumentBuilderFactory factory =
      DocumentBuilderFactory.newInstance();
    factory.setNamespaceAware(true);
    try {
      DocumentBuilder builder = factory.newDocumentBuilder();
      document = builder.newDocument();
      visitor_.setDocument(document);
      Element root = (Element) term.accept(visitor_);
      root.setAttributeNS("http://www.w3.org/2000/xmlns/",
                          "xmlns",
                          "http://czt.sourceforge.net/zml");
      document.appendChild(root);
      document.normalize();
    }
    catch (Exception e) {
      e.printStackTrace();
    }
    return document;
  }

  public void write(Term term, Writer writer)
  {
    final String methodName = "write";
    Object[] args = {term, writer};
    getLogger().entering(getClassName(), methodName, args);

    try {
      Document document = getDocument(term);

      OutputFormat format = new OutputFormat(document);
      format.setIndent(2);
      format.setPreserveSpace(true);
      //      Serializer serializer = SerializerFactory.getSerializer
      //        (OutputPropertiesFactory.getDefaultMethodProperties("xml"));
      XMLSerializer serializer =
        new XMLSerializer (writer, format);
      serializer.asDOMSerializer();
      serializer.serialize(document);
      //      serializer.setOutputStream(System.out);
      //      serializer.asDOMSerializer().serialize(document);
    }
    catch (Exception e) {
      e.printStackTrace();
    }
    getLogger().exiting(getClassName(), methodName);
  }

  public void write(Term term, OutputStream stream)
  {
    final String methodName = "write";
    Object[] args = {term, stream};
    getLogger().entering(getClassName(), methodName, args);
    try {
      Document document = getDocument(term);
      TransformerFactory tFactory =
        TransformerFactory.newInstance();
      Transformer transformer =
        tFactory.newTransformer();
      DOMSource source = new DOMSource(document);
      StreamResult result = new StreamResult(stream);
      transformer.setOutputProperty("indent", "yes");
      transformer.transform(source, result);
      /*
      OutputFormat format = new OutputFormat(document);
      format.setIndent(2);
      format.setPreserveSpace(true);
      XMLSerializer serializer =
        new XMLSerializer (stream, format);
      serializer.asDOMSerializer();
      serializer.serialize(document);
      */
    }
    catch (Exception e) {
      e.printStackTrace();
    }

    getLogger().exiting(getClassName(), methodName);
  }
}
