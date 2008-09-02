/**
 Copyright (C) 2007 Mark Utting
 This file is part of the CZT project.

 The CZT project contains free software; you can redistribute it and/or
 modify it under the terms of the GNU General Public License as published
 by the Free Software Foundation; either version 2 of the License, or
 (at your option) any later version.

 The CZT project is distributed in the hope that it will be useful,
 but WITHOUT ANY WARRANTY; without even the implied warranty of
 MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 GNU General Public License for more details.

 You should have received a copy of the GNU General Public License
 along with CZT; if not, write to the Free Software
 Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 */

package net.sourceforge.czt.modeljunit.examples;

import java.io.IOException;
import java.util.Set;

import net.sourceforge.czt.modeljunit.GreedyTester;
import net.sourceforge.czt.modeljunit.Tester;
import net.sourceforge.czt.modeljunit.VerboseListener;
import net.sourceforge.czt.modeljunit.coverage.TransitionCoverage;
import junit.framework.TestCase;

/** A simple example of a JUnit test that uses model-based
 *  test generation, from the model SimpleSetWithAdaptor.
 *
 * @author marku
 */
public class StringSetTest extends TestCase
{
  public StringSetTest(String arg0)
  {
    super(arg0);
  }

  public void testSet() throws IOException
  {
    Set<String> sut = new StringSet();
    Tester tester = new GreedyTester(new SimpleSetWithAdaptor(sut));
    tester.addCoverageMetric(new TransitionCoverage());
    tester.addListener("verbose");
    tester.generate(60);
    tester.printCoverage(); // print the model coverage information
  }
}
