/*
  Copyright (C) 2006 Petra Malik
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

public class TokenImpl
  implements Token
{
  private Token token_;
  private Object spelling_;

  public TokenImpl(Token token, Object spelling)
  {
    token_ = token;
    spelling_ = spelling;
  }

  @Override
  public String getName()
  {
    return token_.toString();
  }

  @Override
  public Object getSpelling()
  {
    return spelling_ != null ? spelling_ : token_.spelling();
  }

  @Override
  public String spelling()
  {
    Object o = getSpelling();
    return o != null ? o.toString() : null;
  }

  @Override
  public NewlineCategory getNewlineCategory()
  {
    return token_.getNewlineCategory();
  }

  @Override
  public String toString()
  {
    return "Token[" + getName() + ", " + spelling() + "]";
  }
}
