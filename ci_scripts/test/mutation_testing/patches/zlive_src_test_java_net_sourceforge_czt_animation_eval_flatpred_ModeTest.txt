/*
  ZLive - A Z animator -- Part of the CZT Project.
  Copyright 2006 Mark Utting

  This program is free software; you can redistribute it and/or
  modify it under the terms of the GNU General Public License
  as published by the Free Software Foundation; either version 2
  of the License, or (at your option) any later version.

  This program is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with this program; if not, write to the Free Software
  Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA  02111-1307, USA.
*/

package net.sourceforge.czt.animation.eval.flatpred;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import junit.framework.Assert;
import net.sourceforge.czt.animation.eval.Envir;
import net.sourceforge.czt.animation.eval.ZTestCase;
import net.sourceforge.czt.z.ast.ZName;

public class ModeTest extends ZTestCase
{
  Envir x10;
  List<ZName> xy;
  Mode modey;
  
  public void setUp()
  {
    x10 = new Envir().plus(x,i10);
    xy = new ArrayList<ZName>();
    xy.add(x);
    xy.add(y);
    modey = new Mode(null, x10, xy, 5.0);
  }

  /*
   * Test method for 'net.sourceforge.czt.animation.eval.flatpred.Mode.isInput(ZName)'
   */
  public void testIsInput()
  {
    Assert.assertTrue(modey.isInput(x));
    Assert.assertFalse(modey.isInput(y));
    Assert.assertFalse(modey.isInput(z));
  }

  /*
   * Test method for 'net.sourceforge.czt.animation.eval.flatpred.Mode.isOutput(ZName)'
   */
  public void testIsOutput()
  {
    Assert.assertFalse(modey.isOutput(x));
    Assert.assertTrue(modey.isOutput(y));
    Assert.assertFalse(modey.isOutput(z));
  }

  /*
   * Test method for 'net.sourceforge.czt.animation.eval.flatpred.Mode.getSolutions()'
   */
  public void testGetSolutions()
  {
    Assert.assertEquals(5.0, modey.getSolutions());
  }

  /*
   * Test method for 'net.sourceforge.czt.animation.eval.flatpred.Mode.setSolutions(double)'
   */
  public void testSetSolutions()
  {
    Mode tmp = new Mode(null, x10, xy, 5.0);
    tmp.setSolutions(1.0);
    Assert.assertEquals(1.0, tmp.getSolutions());
  }

  /*
   * Test method for 'net.sourceforge.czt.animation.eval.flatpred.Mode.getEnvir0()'
   */
  public void testGetEnvir0()
  {
    Assert.assertEquals(x10, modey.getEnvir0());
  }

  /*
   * Test method for 'net.sourceforge.czt.animation.eval.flatpred.Mode.getEnvir()'
   */
  public void testGetEnvir()
  {
    Assert.assertEquals(x10.plus(y,null), modey.getEnvir());
  }

  /*
   * Test method for 'net.sourceforge.czt.animation.eval.flatpred.Mode.numOutputs()'
   */
  public void testNumOutputs()
  {
    Assert.assertEquals(1, modey.numOutputs());
  }
  
  /*
   * Test method for 'net.sourceforge.czt.animation.eval.flatpred.Mode.getOutputs()'
   */
  public void testGetOutputs()
  {
    Set<ZName> result = new HashSet<ZName>();
    result.add(y);
    Assert.assertEquals(result, modey.getOutputs());
  }
}
