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

package net.sourceforge.czt.core.jaxb;

import java.io.FileInputStream;
import java.io.IOException;
import java.util.*;

import javax.xml.bind.JAXBContext;
import javax.xml.bind.JAXBException;

import java.util.logging.Logger;

import net.sourceforge.czt.core.ast.*;

/**
 * The unmarshaller responsible for deserializing XML data.
 *
 * @author Petra Malik
 */
public class JaxbXmlReader
implements net.sourceforge.czt.core.util.XmlReader
{
  private javax.xml.bind.Unmarshaller createUnmarshaller() {
    javax.xml.bind.Unmarshaller unmarshaller = null;
    try {
      JAXBContext jaxcontext =
	JAXBContext.newInstance("net.sourceforge.czt.core.jaxb.gen");
      unmarshaller = jaxcontext.createUnmarshaller();
    } catch(Exception e) {
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
      JaxbToAst j2a = new JaxbToAst();
      term = (Term) j2a.dispatch(createUnmarshaller().unmarshal(stream));
    } catch(Exception e) {
      e.printStackTrace();
    }
    return term;
  }

  /**
   * Unmarshalles XML data from the specified file and
   * returns the root Term.
   * @param file  the file to be unmarshalled.
   * @return the root element of the unmarshalled file.
   */
  public Term read(java.io.File file)
  {
    Term term = null;
    try {
      JaxbToAst j2a = new JaxbToAst();
      term = (Term) j2a.dispatch(createUnmarshaller().unmarshal(file));
    } catch(Exception e) {
      e.printStackTrace();
    }
    return term;
  }
}
