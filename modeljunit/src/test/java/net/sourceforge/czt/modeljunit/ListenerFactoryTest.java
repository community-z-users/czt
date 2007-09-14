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

import net.sourceforge.czt.modeljunit.coverage.TransitionCoverage;
import junit.framework.TestCase;

public class ListenerFactoryTest extends TestCase
{
  protected ListenerFactory factory_;
  
  protected void setUp() throws Exception
  {
    super.setUp();
    factory_ = ListenerFactory.getFactory();
    assertNotNull(factory_);
  }

  public void testGetListener()
  {
    ModelListener graph = factory_.getListener("graph");
    assertNotNull(graph);
    assertTrue(graph instanceof GraphListener);
    
    assertNull(factory_.getListener(""));
  }

  public void testGetListenerClass()
  {
    assertEquals(GraphListener.class, factory_.getListenerClass("graph"));
  }

  public void testPutListener()
  {
    String name = "dummy 81 42 66 01 @!$#^%*&)("; // an unused string
    ModelListener dummy = factory_.getListener(name);
    assertNull(dummy);
    assertNull(factory_.removeListener(name));
    assertNull(factory_.putListener(name, TransitionCoverage.class));
    assertEquals(TransitionCoverage.class, factory_.getListenerClass(name));
    dummy = factory_.getListener(name);
    assertNotNull(dummy);
    assertTrue(dummy instanceof TransitionCoverage);
    assertEquals(TransitionCoverage.class, factory_.removeListener(name));
  }

  public void testGetNames()
  {
    assertEquals(6, factory_.getNames().size());
  }

}
