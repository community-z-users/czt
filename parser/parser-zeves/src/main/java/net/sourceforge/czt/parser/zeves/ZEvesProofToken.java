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

package net.sourceforge.czt.parser.zeves;

import net.sourceforge.czt.zeves.util.ZEvesString;
import net.sourceforge.czt.parser.util.NewlineCategory;
import net.sourceforge.czt.parser.util.Token;

/**
 *
 * @author Leo Freitas
 * @date Jun 22, 2011
 */
public enum ZEvesProofToken implements Token
{
  ZPROOF(ZEvesString.ZPROOF, NewlineCategory.NEITHER),
  ZPROOFSECTION(ZEvesString.ZPROOFSECTION, NewlineCategory.NEITHER),
  ZPROOFDOLLAR(ZEvesString.ZPROOFDOLLAR, NewlineCategory.NEITHER),
  ZPROOFCOMMANDSEP(ZEvesString.ZPROOFCOMMANDSEP, NewlineCategory.BOTH),
  // token because of DEFEQUAL (as ==) already being a keyword?
  QNTINSTANTIATION(ZEvesString.QNTINSTANTIATION, NewlineCategory.BOTH),

  LLABEL(ZEvesString.LLABEL, NewlineCategory.NEITHER),
  RLABEL(ZEvesString.RLABEL, NewlineCategory.AFTER),
  LZNOTE(ZEvesString.LZNOTE, NewlineCategory.NEITHER),
  RZNOTE(ZEvesString.RZNOTE, NewlineCategory.NEITHER),

  DISABLEDTHMTAG(ZEvesString.DISABLEDTHMTAG, NewlineCategory.NEITHER),
  DISABLEDDEFTAG(ZEvesString.DISABLEDDEFTAG, NewlineCategory.NEITHER)
          ;

  private String spelling_ = null;
  private NewlineCategory newlineCategory_;

  ZEvesProofToken(NewlineCategory newlineCategory)
  {
    newlineCategory_ = newlineCategory;
  }

  ZEvesProofToken(String spelling, NewlineCategory newlineCategory)
  {
    spelling_ = spelling;
    newlineCategory_ = newlineCategory;
  }

  @Override
  public String getName()
  {
    return toString();
  }

  @Override
  public Object getSpelling()
  {
    return spelling_;
  }

  @Override
  public String spelling()
  {
    return spelling_;
  }

  @Override
  public NewlineCategory getNewlineCategory()
  {
    return newlineCategory_;
  }
}

