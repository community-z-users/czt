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

package net.sourceforge.czt.zed.jaxb;

import java.io.IOException;
import java.io.OutputStream;
import java.io.Writer;
import java.util.*;
import java.util.logging.Logger;

import javax.xml.bind.JAXBContext;
import javax.xml.bind.JAXBException;
import javax.xml.bind.Marshaller;

import net.sourceforge.czt.util.Visitor;
import net.sourceforge.czt.zed.ast.Term;
import net.sourceforge.czt.zed.util.XmlWriter;

/**
 * The Jaxb marshaller responsible for serializing XML data.
 *
 * @author Petra Malik
 */
public class JaxbXmlWriter implements XmlWriter
{
  private static final String sClassName = "JaxbXmlWriter";
  private static final Logger sLogger =
    Logger.getLogger("net.sourceforge.czt.zed.jaxb." + sClassName);

  private Visitor mVisitor;
  private String mJaxbContextPath;

  public JaxbXmlWriter(Visitor visitor, String jaxbContextPath)
  {
    mVisitor = visitor;
    mJaxbContextPath = jaxbContextPath;
  }

  private Marshaller createMarshaller()
  {
    Marshaller erg = null;
    try {
      JAXBContext jc = JAXBContext.newInstance(mJaxbContextPath);
      erg = jc.createMarshaller();
      erg.setProperty(Marshaller.JAXB_FORMATTED_OUTPUT, Boolean.TRUE);
    } catch(Exception e) {
      e.printStackTrace();
    }
    return erg;
  }

  private Object toJaxb(Term term)
  {
    final String methodName = "toJaxb";
    sLogger.entering(sClassName, methodName, term);
    Object erg = term.accept(mVisitor);
    sLogger.exiting(sClassName, methodName, erg);
    return erg;
  }

  public void write(Term term, Writer writer)
  {
    final String methodName = "write";
    Object[] args = {term, writer};
    sLogger.entering(sClassName, methodName, args);
      
    Marshaller m = createMarshaller();
    try {
      m.marshal(toJaxb(term), writer);
    } catch(Exception e) {
      e.printStackTrace();
    }
    sLogger.exiting(sClassName, methodName);
  }

  public void write(Term term, OutputStream stream)
  {
    final String methodName = "write";
    Object[] args = {term, stream};
    sLogger.entering(sClassName, methodName, args);
    Marshaller m = createMarshaller();
    try {
      m.marshal(toJaxb(term), stream);
    } catch(Exception e) {
      e.printStackTrace();
    }
    sLogger.exiting(sClassName, methodName);
  }
}
