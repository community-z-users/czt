/*
  Copyright (C) 2003, 2004, 2006, 2007 Mark Utting
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

package net.sourceforge.czt.base.jaxb;

import java.io.File;
import java.io.InputStream;
import java.net.URL;
import javax.xml.bind.JAXBContext;
import javax.xml.bind.JAXBException;
import javax.xml.bind.Unmarshaller;
import javax.xml.validation.Schema;
import javax.xml.validation.SchemaFactory;
import org.xml.sax.InputSource;
import org.xml.sax.SAXException;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.base.util.UnmarshalException;
import net.sourceforge.czt.base.util.XmlReader;
import net.sourceforge.czt.util.ReflectiveVisitor;

/**
 * The unmarshaller responsible for deserializing XML data.
 *
 * @author Petra Malik
 */
public abstract class BaseJaxbXmlReader
  implements XmlReader
{
  /**
   * The visitor for transforming a JAXB tree into an AST.
   */
  private ReflectiveVisitor visitor_;

  /**
   * Returns a new JaxbXmlReader.
   * @param visitor
   */
  public BaseJaxbXmlReader(ReflectiveVisitor visitor)
  {
    visitor_ = visitor;
  }
  
  protected abstract JAXBContext getContext();

  private Unmarshaller createUnmarshaller()
    throws JAXBException, SAXException
  {
    Unmarshaller unmarshaller = getContext().createUnmarshaller();
    SchemaFactory schemaFactory = SchemaFactory.newInstance(
      javax.xml.XMLConstants.W3C_XML_SCHEMA_NS_URI);
    Schema schema = getSchema() == null ? null :
      schemaFactory.newSchema(getSchema());
    unmarshaller.setSchema(schema);
    return unmarshaller;
  }

  protected URL getSchema()
  {
    return null;
  }

  /**
   * Unmarshalles XML data from the specified file and
   * returns the root Term.
   * @param stream  the stream to be unmarshalled.
   * @return the root element of the unmarshalled file.
   */
  @Override
  public Term read(InputStream stream)
    throws UnmarshalException
  {
    Term term = null;
    try {
      term = (Term) visitor_.dispatch(createUnmarshaller().unmarshal(stream));
    }
    catch (Exception e) {
      throw new UnmarshalException(e);
    }
    return term;
  }

  /**
   * Unmarshalles XML data from the specified source and
   * returns the root Term.
   * @param input  the source to be unmarshalled.
   * @return the root element of the unmarshalled file.
   */
  @Override
  public Term read(InputSource input)
    throws UnmarshalException
  {
    Term term = null;
    try {
      term = (Term) visitor_.dispatch(createUnmarshaller().unmarshal(input));
    }
    catch (Exception e) {
      throw new UnmarshalException(e);
    }
    return term;
  }

  /**
   * Unmarshalles XML data from the specified file and
   * returns the root Term.
   *
   * @param file  the file to be unmarshalled.
   * @return the root element of the unmarshalled file.
   */
  @Override
  public Term read(File file)
    throws UnmarshalException
  {
    Term term = null;
    try {
      term = (Term) visitor_.dispatch(createUnmarshaller().unmarshal(file));
    }
    catch (Exception e) {
      throw new UnmarshalException(e);
    }
    return term;
  }
}
