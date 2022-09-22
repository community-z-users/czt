/*
  Copyright (C) 2003, 2004, 2005 Mark Utting
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

import java.io.Writer;
import java.util.Arrays;
import java.util.LinkedHashSet;
import java.util.Set;

import javax.xml.bind.JAXBContext;
import javax.xml.bind.JAXBException;
import javax.xml.bind.Marshaller;

import net.sourceforge.czt.util.Visitor;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.util.AbstractXmlWriter;
import net.sourceforge.czt.z.util.Version;

/**
 * The Jaxb marshaller responsible for serializing XML data.
 *
 * @author Petra Malik
 */
public abstract class BaseJaxbXmlWriter
  extends AbstractXmlWriter
  implements Version
{
  private Visitor<?> visitor_;

  public BaseJaxbXmlWriter(Visitor<?> visitor)
  {
    visitor_ = visitor;
  }
  
  protected abstract JAXBContext getContext();

  private Marshaller createMarshaller() throws JAXBException
  {
    Marshaller result = getContext().createMarshaller();
    result.setProperty(Marshaller.JAXB_FORMATTED_OUTPUT, Boolean.TRUE);
    result.setProperty(Marshaller.JAXB_ENCODING, getEncoding());
    String location = "http://czt.sourceforge.net/zml " + Z_SCHEMA_LOCATION;
    result.setProperty(Marshaller.JAXB_SCHEMA_LOCATION, location);
    return result;
  }

  private Object toJaxb(Term term)
  {
    Object erg = term.accept(visitor_);
    return erg;
  }

  @Override
  public void write(Term term, Writer writer)
  {
    try {
      Marshaller m = createMarshaller();
      Object obj = toJaxb(term);
      m.marshal(obj, writer);
    }
    catch (JAXBException e) {
      // TODO
      System.err.println("JaxbXmlWriter: Caught Exception:");
      e.printStackTrace();
    }
  }
  
  /**
   * Constructs a JAXB context path out of given classes. Uses package names of
   * these classes to produce a colon-separated String.
   * 
   * @param contextClasses
   * @return
   */
  public static String toJaxbContextPath(Class<?>... contextClasses)
  {
    // exclude duplicates but preserve order
    Set<Class<?>> noDuplicates = new LinkedHashSet<Class<?>>(Arrays.asList(contextClasses));
    
    StringBuilder out = new StringBuilder();
    String separator = "";
    for (Class<?> clazz : noDuplicates) {
      out.append(separator);
      out.append(clazz.getPackage().getName());
      separator = ":";
    }
    
    return out.toString();
  }
}
