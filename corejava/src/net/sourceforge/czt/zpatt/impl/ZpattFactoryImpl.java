
/******************************************************************************
DO NOT EDIT THIS FILE!  THIS FILE WAS GENERATED BY GNAST
FROM THE TEMPLATE FILE CoreFactoryImpl.vm.
ANY MODIFICATIONS TO THIS FILE WILL BE LOST UPON REGENERATION.

-------------------------------------------------------------------------------

Copyright 2003, 2004 Mark Utting
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
******************************************************************************/

package net.sourceforge.czt.zpatt.impl;

import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.zpatt.ast.*;

/**
 * <p>An implementation of the object factory for constructing
 * concrete Z terms.  Each factory method returns an instance
 * of the corresponding class provided in this package.</p>
 *
 * @author Gnast version 0.1
 */
public class ZpattFactoryImpl
  extends net.sourceforge.czt.z.impl.ZFactoryImpl
  implements net.sourceforge.czt.zpatt.ast.ZpattFactory
{
  public JokerExpr createJokerExpr()
  {
    JokerExpr zedObject = new JokerExprImpl();
    return zedObject;
  }

  public JokerExpr createJokerExpr(String name)
  {
    JokerExpr zedObject = createJokerExpr();
    zedObject.setName(name);
    return zedObject;
  }

  public Substitute createSubstitute()
  {
    Substitute zedObject = new SubstituteImpl();
    return zedObject;
  }

  public Substitute createSubstitute(java.util.List expr, java.util.List pred)
  {
    Substitute zedObject = createSubstitute();
    if (expr != null) {
      zedObject.getExpr().addAll(expr);
    }
    if (pred != null) {
      zedObject.getPred().addAll(pred);
    }
    return zedObject;
  }

  public JokerPred createJokerPred()
  {
    JokerPred zedObject = new JokerPredImpl();
    return zedObject;
  }

  public JokerPred createJokerPred(String name)
  {
    JokerPred zedObject = createJokerPred();
    zedObject.setName(name);
    return zedObject;
  }

  public SubstList createSubstList()
  {
    SubstList zedObject = new SubstListImpl();
    return zedObject;
  }

  public SubstList createSubstList(java.util.List substitute)
  {
    SubstList zedObject = createSubstList();
    if (substitute != null) {
      zedObject.getSubstitute().addAll(substitute);
    }
    return zedObject;
  }

}
