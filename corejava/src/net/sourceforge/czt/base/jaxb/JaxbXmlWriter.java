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

import java.io.OutputStream;
import java.io.Writer;
import java.util.*;

import javax.xml.bind.JAXBContext;
import javax.xml.bind.JAXBException;
import javax.xml.bind.Marshaller;

import net.sourceforge.czt.util.Visitor;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.util.AbstractXmlWriter;

/**
 * The Jaxb marshaller responsible for serializing XML data.
 *
 * @author Petra Malik
 */
public class JaxbXmlWriter
  extends AbstractXmlWriter
{
  private Visitor visitor_;
  private String jaxbContextPath_;

  public JaxbXmlWriter(Visitor visitor, String jaxbContextPath)
  {
    visitor_ = visitor;
    jaxbContextPath_ = jaxbContextPath;
  }

  private Marshaller createMarshaller()
  {
    Marshaller result = null;
    try {
      JAXBContext jc = JAXBContext.newInstance(jaxbContextPath_);
      result = jc.createMarshaller();
      result.setProperty(Marshaller.JAXB_FORMATTED_OUTPUT, Boolean.TRUE);
      result.setProperty(Marshaller.JAXB_ENCODING, getEncoding());
    }
    catch (Exception e) {
      // TODO
      e.printStackTrace();
    }
    return result;
  }

  private Object toJaxb(Term term)
  {
    Object erg = term.accept(visitor_);
    return erg;
  }

  public void write(Term term, Writer writer)
  {
    final String methodName = "write";
    Object[] args = {term, writer};

    Marshaller m = createMarshaller();
    try {
      m.marshal(toJaxb(term), writer);
    }
    catch (JAXBException e) {
      // TODO
      System.err.println("JaxbXmlWriter: Caught Exception:");
      e.printStackTrace();
    }
  }
}
