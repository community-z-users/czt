/*
  Copyright (C) 2007 Petra Malik
  This file is part of the czt project.

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

package net.sourceforge.czt.ui;

import static junit.framework.Assert.*;
import junit.framework.*;

public class MainTest extends TestCase
{
  /**
   * @org.junit.Test
   */
  public void testVersionNumberPresent()
  {
    String version = Main.getVersion();
    assertTrue(version.startsWith("0") || version.startsWith("1"));
  }
}
