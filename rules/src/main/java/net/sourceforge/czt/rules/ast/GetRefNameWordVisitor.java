/*
  Copyright (C) 2005 Mark Utting
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

import net.sourceforge.czt.z.ast.RefName;
import net.sourceforge.czt.z.ast.ZRefName;
import net.sourceforge.czt.z.visitor.RefNameVisitor;
import net.sourceforge.czt.z.visitor.ZRefNameVisitor;
import net.sourceforge.czt.zpatt.ast.JokerRefName;
import net.sourceforge.czt.zpatt.visitor.JokerRefNameVisitor;

public class GetRefNameWordVisitor
  implements ZRefNameVisitor<String>,
	     JokerRefNameVisitor<String>
{
  public String visitRefName(RefName refName)
  {
    return null;
  }

  public String visitZRefName(ZRefName zRefName)
  {
    return zRefName.getWord();
  }

  public String visitJokerRefName(JokerRefName joker)
  {
    if (joker instanceof ProverJokerRefName) {
      return ((ProverJokerRefName) joker).boundTo().accept(this);
    }
    return null;
  }
}
