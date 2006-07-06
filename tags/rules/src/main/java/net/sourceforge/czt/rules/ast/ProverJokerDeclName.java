/*
  Copyright (C) 2005 Petra Malik
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

package net.sourceforge.czt.rules.ast;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.rules.Joker;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.impl.ZFactoryImpl;
import net.sourceforge.czt.zpatt.ast.*;
import net.sourceforge.czt.zpatt.impl.JokerDeclNameImpl;

/**
 * An implementation of the JokerDeclName and Joker interface.
 *
 * @author Petra Malik
 */
public class ProverJokerDeclName
  extends JokerDeclNameImpl
  implements Joker
{
  private JokerDeclNameBinding binding_;

  private ProverJokerRefName jokerRefName_;

  protected void setJokerRefName(ProverJokerRefName jokerRefName)
  {
    jokerRefName_ = jokerRefName;
  }

  protected ProverJokerRefName getJokerRefName()
  {
    return jokerRefName_;
  }

  protected ProverJokerDeclName(String name)
  {
    super.setName(name);
    binding_ = new ProverJokerDeclNameBinding(this);
  }

  public Term boundTo()
  {
    return getBinding().getDeclName();
  }

  protected Binding bind2(Term term)
  {
    if (! (term instanceof DeclName)) {
      String message = "Cannot bind " + term + " to a JokerDeclName";
      throw new IllegalArgumentException(message);
    }
    DeclName vDeclName = (DeclName) term;
    getBinding().setDeclName(vDeclName);
    return getBinding();
  }

  public Binding bind(Term term)
  {
    if (! (term instanceof DeclName)) {
      String message = "Cannot bind " + term + " to a JokerDeclName";
      throw new IllegalArgumentException(message);
    }
    DeclName vDeclName = (DeclName) term;
    getBinding().setDeclName(vDeclName);
    if (vDeclName instanceof JokerDeclName) {
      ProverJokerRefName assoc = getJokerRefName();
      assoc.bind2(((ProverJokerDeclName) vDeclName).getJokerRefName());
    }
    else if (vDeclName instanceof ZDeclName) {
      ZDeclName zDeclName = (ZDeclName) vDeclName;
      ZFactory factory = new ZFactoryImpl();
      ZRefName zRefName = factory.createZRefName(zDeclName.getWord(),
                                                 zDeclName.getStrokeList(),
                                                 zDeclName);
      getJokerRefName().bind2(zRefName);
    }
    else {
      String message = "Cannot bind " + term + " to a JokerDeclName";
      throw new IllegalArgumentException(message);
    }
    return getBinding();
  }

  public JokerDeclNameBinding getBinding()
  {
    return binding_;
  }

  public void setName(String name)
  {
    throw new UnsupportedOperationException();
  }

  public ProverJokerDeclName create(Object[] args)
  {
    throw new UnsupportedOperationException();
  }
}
