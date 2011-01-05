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
package net.sourceforge.czt.vcg.util;

import java.util.Collections;
import java.util.List;
import net.sourceforge.czt.parser.util.InfoTable;

public class DefinitionException extends InfoTable.InfoTableException
{

  private final List<DefinitionException> exceptions_;

  public DefinitionException(String message)
  {
    super(message);
    exceptions_ = Collections.emptyList();
  }

  public DefinitionException(String message, Throwable cause)
  {
    super(message, cause);
    exceptions_ = Collections.emptyList();
  }

  public DefinitionException(String message, List<DefinitionException> exceptions)
  {
    super(message);
    exceptions_ = Collections.unmodifiableList(exceptions);
  }

  public DefinitionException(String message, Throwable cause, List<DefinitionException> exceptions)
  {
    super(message, cause);
    exceptions_ = Collections.unmodifiableList(exceptions);
  }

  public List<DefinitionException> getExceptions()
  {
    return exceptions_;
  }

  @Override
  public String toString()
  {
    String result = super.toString();
    if (exceptions_ != null && !exceptions_.isEmpty())
    {
      result += " with inner definition exceptions list as ";
      result += exceptions_.toString();
    }
    return result;
  }
}
