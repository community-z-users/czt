/*
  Copyright (C) 2005, 2007 Mark Utting
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

package net.sourceforge.czt.circusconf.jaxb;

import javax.xml.bind.JAXBContext;

import net.sourceforge.czt.z.ast.ZFactory;
import net.sourceforge.czt.zpatt.ast.ZpattFactory;
import net.sourceforge.czt.circus.ast.CircusFactory;
import net.sourceforge.czt.circuspatt.ast.CircusPatternFactory;
import net.sourceforge.czt.circusconf.ast.CircusConfFactory;

/**
 * The unmarshaller responsible for deserializing XML data.
 *
 * @author Petra Malik
 */
public class JaxbXmlReader
  extends net.sourceforge.czt.base.jaxb.BaseJaxbXmlReader
{
  public JaxbXmlReader(ZFactory zFactory,
                       ZpattFactory zpattFactory,
                       CircusFactory circusFactory,
                       CircusPatternFactory circusPattFactory,
                       CircusConfFactory circusconfFactory)
  {
    super(new JaxbToAst(zFactory, zpattFactory, circusFactory, circusPattFactory, circusconfFactory));
  }

  public JaxbXmlReader()
  {
    super(new JaxbToAst());
  }
  
  @Override
  protected JAXBContext getContext() {
    return JaxbXmlWriter.JAXB_CONTEXT;
  }
}
