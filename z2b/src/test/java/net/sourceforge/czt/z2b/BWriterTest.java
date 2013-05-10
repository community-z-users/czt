/**
Copyright (C) 2005 Mark Utting
This file is part of the CZT project.

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

package net.sourceforge.czt.z2b;

import java.io.*;

import junit.framework.*;


/**
 * A (JUnit) test class for testing the BWriter class of Z2B
 *
 * @author Mark Utting
 */
public class BWriterTest
  extends TestCase
{
 // private ZFactory factory_ = new net.sourceforge.czt.z.impl.ZFactoryImpl();
  private BWriter writer;
  private StringWriter output;
  private String tokens[];
  private int tokensDone;

  public void setUp()
  {
    output = new StringWriter();
    writer = new BWriter(output, "Test");
    tokens = null;
    tokensDone = 0;
  }

  /** Returns the BWriter output and removes the first line.
   *  Can be called at most once.
   */
  private String cleanOutput()
  {
    assert output != null;
    writer.close();
    String str = output.toString();
    output = null;
    return str.substring(str.indexOf('\n') + 1);
  }

  /** Returns the output tokens one at a time. */
  private String nextToken()
  {
    if (tokens == null)
      {
	tokens = cleanOutput().split("[ \t\r\n]+");
	tokensDone = 0;
      }
    if (tokensDone >= tokens.length)
	return null;
    else
	return tokens[tokensDone++];
  }


  public void testSimpleSection()
  {
    writer.startSection("FOO");
    writer.endSection("FOO");
    // now check the output
    assertEquals("FOO", nextToken());
    assertEquals("END", nextToken());
  }

  public void testMultiSection()
  {
    writer.startSection("FOO");
    writer.write("abc");
    writer.continueSection("FOO","BAR");
    writer.write("def");
    writer.endSection("FOO");

    // now check the output
    assertEquals("FOO", nextToken());
    assertEquals("abc", nextToken());
    assertEquals("BAR", nextToken());
    assertEquals("def", nextToken());
    assertEquals("END", nextToken());
    assertNull(nextToken());
  }

  public void testNestedSection()
  {
    writer.startSection("FOO");
    writer.startSection("BAR");
    writer.write("abc");
    writer.endSection("BAR");
    writer.endSection("FOO");
    // now check the output
    assertEquals("FOO", nextToken());
    assertEquals("BAR", nextToken());
    assertEquals("abc", nextToken());
    assertEquals("END", nextToken());
    assertEquals("END", nextToken());
    assertNull(nextToken());
  }
}

  
    
    
