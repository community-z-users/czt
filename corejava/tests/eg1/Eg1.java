/**
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

package eg1;

import junit.framework.*;
import net.sourceforge.czt.core.ast.*;
import net.sourceforge.czt.core.util.XmlReader;
import net.sourceforge.czt.core.jaxb.JaxbXmlReader;

/**
 * @author Petra Malik
 */
public class Eg1 extends TestCase {
  private Spec mSpec;

  public static Test suite() {
    return new TestSuite(Eg1.class);
  }
  protected void setUp() {
    try {
      XmlReader reader
	= new JaxbXmlReader();
      mSpec =
	(Spec) reader.read(new java.io.File("../../zml/examples/eg1.xml"));
    } catch(Exception e) {
      e.printStackTrace();
    }
  }
  public void testNumberOfSect() {
    Assert.assertTrue(mSpec.getSect().size()==1);
  }
  public void testZSectName() {
    ZSect sect = (ZSect) mSpec.getSect().get(0);
    Assert.assertTrue(sect.getName().equals("Specification"));
  }
}
