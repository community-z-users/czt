
/******************************************************************************
DO NOT EDIT THIS FILE!  THIS FILE WAS GENERATED BY GNAST
FROM THE TEMPLATE FILE AstInterface.vm.
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

package net.sourceforge.czt.oz.ast;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.z.ast.*;

/**
 *
 * @author Gnast version 0.1
 */
public interface ClassPara extends Para
{

  /**
   * Returns the Name element.
   *
   * @return the Name element.
   */
  net.sourceforge.czt.z.ast.DeclName getName();

  /**
   * Sets the Name element.
   *
   * @param name   the Name element.
   * @see #getName
   */
  void setName(net.sourceforge.czt.z.ast.DeclName name);

  /**
   * Returns the FormalParameters element.
   *
   * @return the FormalParameters element.
   */
  FormalParameters getFormalParameters();

  /**
   * Sets the FormalParameters element.
   *
   * @param formalParameters   the FormalParameters element.
   * @see #getFormalParameters
   */
  void setFormalParameters(FormalParameters formalParameters);

  /**
   * Returns the VisibilityList element.
   *
   * @return the VisibilityList element.
   */
  RefNameList getVisibilityList();

  /**
   * Sets the VisibilityList element.
   *
   * @param visibilityList   the VisibilityList element.
   * @see #getVisibilityList
   */
  void setVisibilityList(RefNameList visibilityList);

  /**
   * <p>Returns the InheritedClass elements.</p>
   * <p>To add or remove elements, use the methods provided by
   * the List interface (that's why there is no need for a setter
   * method).</p>
   *
   * @return a list of InheritedClass elements.
   */
  net.sourceforge.czt.base.ast.ListTerm getInheritedClass();

  /**
   * Returns the LocalDef element.
   *
   * @return the LocalDef element.
   */
  LocalDef getLocalDef();

  /**
   * Sets the LocalDef element.
   *
   * @param localDef   the LocalDef element.
   * @see #getLocalDef
   */
  void setLocalDef(LocalDef localDef);

  /**
   * Returns the State element.
   *
   * @return the State element.
   */
  State getState();

  /**
   * Sets the State element.
   *
   * @param state   the State element.
   * @see #getState
   */
  void setState(State state);

  /**
   * Returns the InitialState element.
   *
   * @return the InitialState element.
   */
  InitialState getInitialState();

  /**
   * Sets the InitialState element.
   *
   * @param initialState   the InitialState element.
   * @see #getInitialState
   */
  void setInitialState(InitialState initialState);

  /**
   * <p>Returns the Operation elements.</p>
   * <p>To add or remove elements, use the methods provided by
   * the List interface (that's why there is no need for a setter
   * method).</p>
   *
   * @return a list of Operation elements.
   */
  net.sourceforge.czt.base.ast.ListTerm getOperation();
}
