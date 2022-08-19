/*
  Copyright (C) 2004, 2006 Petra Malik
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

package net.sourceforge.czt.z.util;

import junit.framework.*;

/**
 * A (JUnit) test class for testing the OperatorName class.
 *
 * @author Petra Malik
 */
public class OperatorNameTest
  extends TestCase
{
  public void testPlusOp()
    throws OperatorName.OperatorNameException
  {
    String plusName = ZString.ARG_TOK + ZString.PLUS + ZString.ARG_TOK;
    OperatorName op = new OperatorName(plusName, null);
    String[] words = op.getWords();
    Assert.assertTrue(words.length == 3);
    Assert.assertEquals(words[0], ZString.ARG);
    Assert.assertEquals(words[1], ZString.PLUS);
    Assert.assertEquals(words[2], ZString.ARG);
  }
}
