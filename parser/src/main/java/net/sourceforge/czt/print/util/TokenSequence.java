/*
  Copyright (C) 2007 Petra Malik
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

package net.sourceforge.czt.print.util;

import java.util.ArrayList;
import java.util.List;

import net.sourceforge.czt.parser.util.Token;
import net.sourceforge.czt.parser.z.TokenName;

public class TokenSequence
{
  private String name_;

  /*@ invariant (\forall Object o; list_.contains(o);
    @                 (o instanceof Token) ||
    @                 (o instanceof TokenSequence));
    @*/
  private List<Object> list_ = new ArrayList<Object>();

  private int nrOfTokens_ = 0;
  //@ invariant nrOfTokens_ >= 0;

  private int length_ = 0;
  //@ invariant length_ >= 0;

  public TokenSequence(String name)
  {
    name_ = name;
  }

  public String getName()
  {
    return name_;
  }

  public void add(Token t)
  {
    list_.add(t);
    nrOfTokens_++;
    length_ += t.spelling().length();
    if (TokenName.NUMSTROKE.getName().equals(t.getName())) {
      length_ += 2;
    }
  }

  public void add(TokenSequence seq)
  {
    list_.add(seq);
    nrOfTokens_ += seq.getNrOfTokens();
    length_ += seq.getLength();
  }

  public Object[] getSequence()
  {
    return list_.toArray();
  }

  /**
   * The sum of all the token length.
   */
  public int getLength()
  {
    return length_;
  }

  public int getNrOfTokens()
  {
    return nrOfTokens_;
  }

  public String toString()
  {
    return list_.toString();
  }
}
