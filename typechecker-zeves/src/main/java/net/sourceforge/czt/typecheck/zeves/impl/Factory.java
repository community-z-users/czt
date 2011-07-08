/*
Copyright (C) 2007 Leo Freitas
This file is part of the CZT project.
The CZT project contains free software;
you can redistribute it and/or modify
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

package net.sourceforge.czt.typecheck.zeves.impl;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.z.ast.ZFactory;
import net.sourceforge.czt.z.impl.ZFactoryImpl;
import net.sourceforge.czt.zeves.ast.ZEvesFactory;
import net.sourceforge.czt.zeves.impl.ZEvesFactoryImpl;

/**
 *
 * @author Leo Freitas
 */
public class Factory 
  extends net.sourceforge.czt.typecheck.z.impl.Factory
{

  /** The ZEvesFactory that is used to create wrapped types. */
  protected ZEvesFactory zevesFactory_;
    
  public Factory()
  {
    this(new ZFactoryImpl(), new ZEvesFactoryImpl());
  }

  public Factory(ZFactory zFactory)
  {
    this(zFactory, new ZEvesFactoryImpl());
  }

  public Factory(ZFactory zFactory, ZEvesFactory zevesFactory)
  {
    // use the zeves.util.Factory to create Z objects ;-)
    super(zFactory, new net.sourceforge.czt.zeves.util.Factory(zevesFactory));
    zevesFactory_ = zevesFactory;
  }
  
  /**
   * For now, overrides the deep clonning of terms and just use
   * shallow, term.create(term.getChildren()) cloning. 
   * @param term
   * @return
   */
  public <T extends Term> T deepCloneTerm(T term)
  {    
    return (T)Factory.cloneTerm(term);
  }
  
  public <T extends Term> T shallowCloneTerm(T term)
  {
    return (T)term.create(term.getChildren());
  }
  
  private static int freshId_ = 0;
  public String createFreshName(String prefix)
  {
    String result = prefix + (freshId_++);
    return result;
  }

  public ZEvesFactory getZEvesFactory()
  {
    return zevesFactory_;
  }
}
