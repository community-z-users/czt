/**
 Copyright (C) 2006 Mark Utting
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

import java.io.FileNotFoundException;

import junit.framework.Assert;
import junit.framework.Test;
import junit.framework.TestCase;
import junit.framework.TestSuite;

/**
 * Unit test for ModelJUnit
 */
public class QuiDoncTest extends TestCase
{
  /**
   * Create the test case
   *
   * @param testName name of the test case
   */
  public QuiDoncTest(String testName)
  {
    super(testName);
  }

  /**
   * @return the suite of tests being tested
   */
  public static Test suite()
  {
    return new TestSuite(QuiDoncTest.class);
  }

  public static void testEnabled()
  throws FileNotFoundException
  {
    ModelTestCase model = new ModelTestCase(new QuiDonc());
    model.buildGraph();
    //    model.printGraphDot("QuiDonc.dot");
    // NOTE: with the State+timeouts getState, it has 11 vertices, 37 edges.
    Assert.assertEquals(5, model.getGraph().numVertices());
    int numEdges = model.getGraph().numEdges();
    System.out.println("QuiDonc has "+numEdges+" edges.");
    // should be 18 transitions, but we cannot find some of the non-det
    // wait transitions that are enabled only on the third wait call.
    Assert.assertEquals(17, model.getGraph().numEdges());
    // fsmDoAction(fsmGetAction("dial"));
  }
}
