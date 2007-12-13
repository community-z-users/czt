/**
 Copyright (C) 2007 Mark Utting
 This file is part of the CZT project.

 The CZT project contains free software; you can redistribute it and/or modify
 it under the terms of the GNU General Public License as published by
 the Free Software Foundation; either version 2 of the License, or
 (at your option) any later version.

 The CZT project is distributed in the hope that it will be useful,
 but WITHOUT ANY WARRANTY; without even the implied warranty of
 MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 GNU General Public License for more details.

 You should have received a copy of the GNU General Public License
 along with CZT; if not, write to the Free Software
 Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 */

package net.sourceforge.czt.modeljunit;

import net.sourceforge.czt.modeljunit.examples.FSM;
import junit.framework.TestCase;

/**
 *  Unit tests for the lookahead tester.
 * @author marku
 *
 */
public class LookaheadTesterTest extends TestCase
{
  protected LookaheadTester tester = new LookaheadTester(new FSM());
  
  public void testGenerate()
  {
    //fail("Not yet implemented");
  }

  public void testGetDepth()
  {
    assertEquals(3, tester.getDepth());
  }

  public void testSetDepth()
  {
    tester.setDepth(0);
    assertEquals(0, tester.getDepth());
    tester.setDepth(1);
    assertEquals(1, tester.getDepth());
  }

  public void testGenerateInt()
  {
    //fail("Not yet implemented");
  }

}
