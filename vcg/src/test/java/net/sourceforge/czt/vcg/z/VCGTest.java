/*
 * Copyright (C) 2011 Leo Freitas
 * This file is part of the czt project.
 * 
 * The czt project contains free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 * 
 * The czt project is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License
 * along with czt; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 */

package net.sourceforge.czt.vcg.z;

import net.sourceforge.czt.parser.util.CztManagedTest;
import net.sourceforge.czt.session.SectionManager;

/**
 *
 * @author Leo Freitas
 * @date Dec 26, 2010
 */
public abstract class VCGTest extends CztManagedTest
  implements VCGPropertyKeys {


  /**
   * Creates a new test case with a fresh section manager and given extension
   * @param extension usually "z" or "circus"
   * @param debug true or false
   */
  protected VCGTest(String extension, boolean debug)
  {
    super(extension, debug);
  }
  
  /**
   * Creates a test case with given (shared) section manager and debug flag. 
   * @param manager given
   * @param debug 
   */
  protected VCGTest(SectionManager manager, boolean debug)
  {
    super(manager, debug);
  }

  //  @Override
//  protected TestCase createNegativeTest(URL url, String exception, Class<?> expCls) {
//    throw new UnsupportedOperationException("Not supported yet.");
//  }

}
