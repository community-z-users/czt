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

import java.util.*;
import java.util.logging.*;
import junit.framework.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.jaxb.JaxbValidator;
import net.sourceforge.czt.z.jaxb.JaxbXmlReader;
import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.base.util.AstValidator;
import net.sourceforge.czt.base.util.XmlReader;

/**
 * Test cases using the eg1 example.
 *
 * @author Petra Malik
 */
public class Eg1 extends TestCase {
  private static final String sFilename = "../../zml/examples/eg1.xml";
  private Spec mSpec;
  private ZSect mZSect;

  public static Test suite() {
    try {
      Handler handler = new FileHandler("eg1.log");
      handler.setLevel(Level.ALL);
      handler.setEncoding("utf8");
      Logger.getLogger("").addHandler(handler);
      Logger.getLogger("").setLevel(Level.FINEST);
    } catch(SecurityException e) {
      e.printStackTrace();
    } catch(java.io.IOException e) {
      e.printStackTrace();
    }

    return new TestSuite(Eg1.class);
  }
  protected void setUp() {
    try {
      XmlReader reader
	= new JaxbXmlReader();
      mSpec = (Spec) reader.read(new java.io.File(sFilename));
      if (mSpec.getSect().size() > 0)
	mZSect = (ZSect) mSpec.getSect().get(0);
    } catch(Exception e) {
      e.printStackTrace();
    }
  }
  public void testValid() {
    AstValidator v = new JaxbValidator();
    Assert.assertTrue(v.validate(mSpec));
  }
  public void testNumberOfSect() {
    Assert.assertTrue(mSpec.getSect().size()==1);
  }
  public void testZSectName() {
    Assert.assertTrue(mZSect.getName().equals("Specification"));
  }
  public void testZSectParent() {
    List parentList = mZSect.getParent();
    Assert.assertTrue(parentList.size() == 2);
    Parent parent1 = (Parent) parentList.get(0);
    Parent parent2 = (Parent) parentList.get(1);
    Assert.assertEquals(parent1.getWord(), "Sect1");
    Assert.assertEquals(parent2.getChildren()[0], "Sect2");
    Assert.assertFalse(parent1.equals(parent2));
    Assert.assertFalse(parent2.equals(parent1));
    parent1.setWord("Sect3");
    Object[] args = { "Sect3" };
    Term parent3 = parent2.create(args);
    Assert.assertTrue(parent1.equals(parent3));
    Assert.assertTrue(parent3.equals(parent1));
    Assert.assertTrue(parent1.hashCode() == parent3.hashCode());
    List anns1 = parent1.getAnns();
    List anns2 = parent2.getAnns();
    Assert.assertTrue(anns1.size() == 1);
    Assert.assertTrue(anns2.size() == 0);
  }
  public void testZSectPara() {
    List paraList = mZSect.getPara();
    Assert.assertTrue(paraList.size() == 5);
    Assert.assertFalse(paraList.get(0).equals(paraList.get(1)));
  }
}
