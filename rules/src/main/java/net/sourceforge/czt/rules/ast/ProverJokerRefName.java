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
import net.sourceforge.czt.zpatt.impl.JokerRefNameImpl;

/**
 * An implementation of the JokerRefName and Joker interface.
 *
 * @author Petra Malik
 */
public class ProverJokerRefName
  extends JokerRefNameImpl
  implements Joker
{
  private JokerRefNameBinding binding_;

  private ProverJokerDeclName jokerDeclName_;

  protected void setJokerDeclName(ProverJokerDeclName jokerDeclName)
  {
    jokerDeclName_ = jokerDeclName;
  }

  protected ProverJokerDeclName getJokerDeclName()
  {
    return jokerDeclName_;
  }

  protected ProverJokerRefName(String name)
  {
    super.setName(name);
    binding_ = new ProverJokerRefNameBinding(this);
  }

  public Term boundTo()
  {
    return getBinding().getRefName();
  }

  protected Binding bind2(Term term)
  {
    if (! (term instanceof RefName)) {
      String message = "Cannot bind " + term + " to a JokerRefName";
      throw new IllegalArgumentException(message);
    }
    RefName vRefName = (RefName) term;
    getBinding().setRefName(vRefName);
    return getBinding();
  }

  public Binding bind(Term term)
  {
    if (! (term instanceof RefName)) {
      String message = "Cannot bind " + term + " to a JokerRefName";
      throw new IllegalArgumentException(message);
    }
    RefName vRefName = (RefName) term;
    getBinding().setRefName(vRefName);
    if (vRefName instanceof JokerRefName) {
      ProverJokerDeclName assoc = getJokerDeclName();
      assoc.bind2(((ProverJokerRefName) vRefName).getJokerDeclName());
    }
    else if (vRefName instanceof ZRefName) {
      ZRefName zRefName = (ZRefName) vRefName;
      getJokerDeclName().bind2(zRefName.getDecl());
    }
    else {
      String message = "Cannot bind " + term + " to a JokerRefName";
      throw new IllegalArgumentException(message);
    }
    return getBinding();
  }

  public JokerRefNameBinding getBinding()
  {
    return binding_;
  }

  public void setName(String name)
  {
    throw new UnsupportedOperationException();
  }

  public ProverJokerRefName create(Object[] args)
  {
    throw new UnsupportedOperationException();
  }
}
