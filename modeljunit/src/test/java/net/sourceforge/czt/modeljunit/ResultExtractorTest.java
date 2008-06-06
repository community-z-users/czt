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

import java.io.BufferedReader;
import java.io.FileReader;
import java.io.IOException;
import java.util.Random;

import junit.framework.TestCase;

public class ResultExtractorTest extends TestCase
{
  public void testTwoRuns() throws IOException
  {
    ResultExtractor results = new ResultExtractor(2);
    results.setRand(new Random(123456789));
    results.setTestLength(10);
    results.run();
    FileReader file = new FileReader("ResultExtractorOutput.csv");
    BufferedReader buf = new BufferedReader(file);

    // check pass 1
    String line = buf.readLine();
    assertNotNull(line);
    assertEquals("Seed,-1442945365,Random,0,1,2,2,3,3,3,3,3,4,4", line);
    line = buf.readLine();
    assertNotNull(line);
    assertEquals(",,Greedy,0,1,2,3,4,5,6,7,8,8,8", line);

    // check pass 2
    line = buf.readLine();
    assertNotNull(line);
    assertEquals("Seed,-1016548095,Random,0,1,2,2,3,3,3,3,3,3,4", line);
    line = buf.readLine();
    assertNotNull(line);
    // this illustrates the greediness nicely.
    assertEquals(",,Greedy,0,1,2,3,4,5,6,7,8,9,10", line);
  }
}
