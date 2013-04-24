/*
  Copyright (C) 2005, 2006 Petra Malik
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

package net.sourceforge.czt.parser.util;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.session.*;
import net.sourceforge.czt.util.CztException;
import net.sourceforge.czt.util.Visitor;

public class AbstractVisitor<R>
  implements Visitor<R>
{
  private SectionInfo sectInfo_;

  public AbstractVisitor(SectionInfo sectInfo)
  {
	if (sectInfo == null) throw new NullPointerException();
    sectInfo_ = sectInfo;
  }
  
  public SectionInfo getSectionInfo()
  {
	  return sectInfo_;
  }

  public R run(Term term)
    throws CommandException
  {
    try {
      return term.accept(this);
    }
    catch (RuntimeException exception) {
      Throwable cause = exception.getCause();
      if (cause instanceof CommandException) {
        throw (CommandException) cause;
      }
      throw exception;
    }
  }

  /**
   * <p>Asks the section manager to provide the requested info.</p>
   *
   * <p>If the section manager throws a CommandException, this
   * exception is wrapped into a RuntimeException and thrown.
   * It can be retrieved by calling getCause().</p>
   * @param <T>
   * @param name
   * @param type
   * @return
   */
  protected <T> T get(String name, Class<T> type)
  {
    Key<T> key = new Key<T>(name, type);
    try {
      return sectInfo_.get(key);
    }
    catch (CommandException exception) {
      throw new CztException(exception);
    }
  }
}
