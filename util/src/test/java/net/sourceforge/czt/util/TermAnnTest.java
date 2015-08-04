/*
 * Copyright (C) 2011 Leo Freitas
 * This file is part of the CZT project.
 * 
 * The CZT project contains free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 * 
 * The CZT project is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License
 * along with CZT; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 */
package net.sourceforge.czt.util;

import junit.framework.Test;
import junit.framework.TestCase;
import junit.framework.TestSuite;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.impl.TermImpl;

/**
 *
 * @author nljsf
 */
public class TermAnnTest extends TestCase
{

  public TermAnnTest()
  {
  }

  public static Test suite()
  {
    return new TestSuite(TermAnnTest.class);
  }

  @org.junit.Test
  public void testHasAnn()
  {
    Term t = new TermAnnImpl();
    t.getAnns().add(Integer.valueOf(0));
    t.getAnns().add(Boolean.TRUE);
    assertEquals(true, t.hasAnn(Integer.class));
    assertEquals(true, t.hasAnn(Boolean.class));
    assertEquals(false, t.hasAnn(String.class));
  }

  @org.junit.Test
  public void testRemoveAnn()
  {
    Term t = new TermAnnImpl();
    t.getAnns().add(Integer.valueOf(0));
    t.getAnns().add(Boolean.TRUE);
    assertEquals(true, t.removeAnn(Integer.valueOf(0)));
    assertEquals(true, t.removeAnn(Boolean.TRUE));
    assertEquals(false, t.removeAnn("bla bla"));
  }

  @org.junit.Test
  public void testRemoveAnn2()
  {
    Term t = new TermAnnImpl();
    t.getAnns().add(Integer.valueOf(0));
    t.getAnns().add(Integer.valueOf(1));
    t.getAnns().add(Boolean.TRUE);
    assertEquals(true, t.removeAnn(Integer.valueOf(0)));
    t.removeAnn(Integer.class);
    assertEquals(false, t.hasAnn(Integer.class));
    assertEquals(true, t.removeAnn(Boolean.TRUE));
    assertEquals(false, t.removeAnn("bla bla"));
  }

  static class TermAnnImpl extends TermImpl
  {
    TermAnnImpl() {}

    @Override
    public Object[] getChildren()
    {
      throw new UnsupportedOperationException("Not supported yet.");
    }

    @Override
    public Term create(Object[] args)
    {
      throw new UnsupportedOperationException("Not supported yet.");
    }
  }
}
