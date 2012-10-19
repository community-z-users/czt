/*
  Copyright (C) 2005 Mark Utting
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

package net.sourceforge.czt.zeves.jaxb;

import javax.xml.bind.JAXBContext;
import javax.xml.bind.JAXBException;

/**
 * The Jaxb marshaller responsible for serializing XML data.
 *
 * @author Petra Malik
 */
public class JaxbXmlWriter
  extends net.sourceforge.czt.base.jaxb.JaxbXmlWriter
{
  
  // static field for the JAXB context, because it is heavy to initialise,
  // does not change after initialisation, and is thread-safe
  static final JAXBContext JAXB_CONTEXT;
  static {
    try {
      JAXB_CONTEXT = JAXBContext.newInstance(toJaxbContextPath(
              net.sourceforge.czt.z.jaxb.gen.ObjectFactory.class,
              net.sourceforge.czt.zeves.jaxb.gen.ObjectFactory.class), 
          net.sourceforge.czt.zeves.jaxb.gen.ObjectFactory.class.getClassLoader());
    } catch (JAXBException e) {
      throw new RuntimeException(e);
    }
  }
  
  public JaxbXmlWriter()
  {
    super(new AstToJaxb());
  }

  @Override
  protected JAXBContext getContext() {
    return JAXB_CONTEXT;
  }
}
