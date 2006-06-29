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
import net.sourceforge.czt.zpatt.impl.JokerPredImpl;

/**
 * An implementation of the JokerPred and Joker interface.
 *
 * @author Petra Malik
 */
public class ProverJokerPred
  extends JokerPredImpl
  implements Joker
{
  private JokerPredBinding binding_;

  protected ProverJokerPred(String name)
  {
    super.setName(name);
    binding_ = new ProverJokerPredBinding(this);
  }

  public Term boundTo()
  {
    return getBinding().getPred();
  }

  public Binding bind(Term term)
  {
    if (! (term instanceof Pred)) {
      String message = "Cannot bind " + term + " to a JokerPred";
      throw new IllegalArgumentException(message);
    }
    Pred vPred = (Pred) term;
    getBinding().setPred(vPred);
    return getBinding();
  }

  public JokerPredBinding getBinding()
  {
    return binding_;
  }

  public void setName(String name)
  {
    throw new UnsupportedOperationException();
  }

  public ProverJokerPred create(Object[] args)
  {
    throw new UnsupportedOperationException();
  }
}
