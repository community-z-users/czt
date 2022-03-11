/*
  Copyright (C) 2003, 2004, 2005 Tim Miller
  Copyright (C) 2007 Petra Malik
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

package net.sourceforge.czt.parser.oz;

import java.util.Stack;
import net.sourceforge.czt.session.Source;

public class ParserState
  extends net.sourceforge.czt.parser.z.ParserState
{
  /**
   * The tope of the stack is true if an operation expr is
   * currently being parsed. This is needed because Z exprs and
   * Object-Z operations are both specified using non-terminal 'term'
   */
  private Stack<Boolean> isOpExpr_ =  new Stack<Boolean>();

  public ParserState(Source loc) {
      super(loc);
  }
  
  /**
   * Reset the isOpExpr_ stack.
   */
  public void resetIsOpExpr()
  {
    isOpExpr_.clear();
  } 
 
  /**
   * Return the top of the isOpExpr_ stack.
   */
  public boolean isOpExpr()
  {
    if (isOpExpr_.size() == 0) {
      return false;
    }
    return isOpExpr_.peek();
  } 

  /**
   * Push an item onto the isOpExpr_ stack.
   */
  public void pushIsOpExpr(boolean b)
  {
    isOpExpr_.push(b);
  }

  /**
   * Pop the stop of the isOpExpr_ stack.
   */
  public void popIsOpExpr()
  {
    isOpExpr_.pop();
  }
}
