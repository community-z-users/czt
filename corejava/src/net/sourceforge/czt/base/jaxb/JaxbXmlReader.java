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

package net.sourceforge.czt.base.jaxb;

import javax.xml.bind.JAXBContext;
import javax.xml.bind.Unmarshaller;

import net.sourceforge.czt.util.ReflectiveVisitor;
import net.sourceforge.czt.base.ast.*;

/**
 * The unmarshaller responsible for deserializing XML data.
 *
 * @author Petra Malik
 */
public class JaxbXmlReader
  implements net.sourceforge.czt.base.util.XmlReader
{
  /**
   * The visitor for transforming a JAXB tree into an AST.
   */
  private ReflectiveVisitor visitor_;

  /**
   * The JAXB context path used for unmarshalling data.
   */
  private String jaxbContextPath_;

  /**
   * Returns a new JaxbXmlReader.
   */
  public JaxbXmlReader(ReflectiveVisitor visitor, String jaxbContextPath)
  {
    visitor_ = visitor;
    jaxbContextPath_ = jaxbContextPath;
  }

  private Unmarshaller createUnmarshaller()
  {
    Unmarshaller unmarshaller = null;
    try {
      JAXBContext jaxcontext =
        JAXBContext.newInstance(jaxbContextPath_);
      unmarshaller = jaxcontext.createUnmarshaller();
    }
    catch (Exception e) {
      e.printStackTrace();
    }
    return unmarshaller;
  }

  /**
   * Unmarshalles XML data from the specified file and
   * returns the root Term.
   * @param stream  the stream to be unmarshalled.
   * @return the root element of the unmarshalled file.
   */
  public Term read(java.io.InputStream stream)
  {
    Term term = null;
    try {
      term = (Term) visitor_.dispatch(createUnmarshaller().unmarshal(stream));
    }
    catch (UnsupportedOperationException e) {
      throw e;
    }
    catch (Exception e) {
      e.printStackTrace();
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
  public Term read(java.io.File file)
  {
    Term term = null;
    try {
      term = (Term) visitor_.dispatch(createUnmarshaller().unmarshal(file));
    }
    catch (UnsupportedOperationException e) {
      throw e;
    }
    catch (Exception e) {
      // TODO: what to do now?
      e.printStackTrace();
    }
    return term;
  }
}
