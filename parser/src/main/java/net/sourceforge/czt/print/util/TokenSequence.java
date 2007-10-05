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
import java.util.Iterator;
import java.util.List;
import java.util.NoSuchElementException;
import java.util.Stack;

import net.sourceforge.czt.parser.util.Token;
import net.sourceforge.czt.parser.z.ZToken;

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
    if (ZToken.NUMSTROKE.getName().equals(t.getName())) {
      length_ += 2;
    }
  }

  public void add(TokenSequence seq)
  {
    list_.add(seq);
    nrOfTokens_ += seq.getNrOfTokens();
    length_ += seq.getLength();
  }

  public List<Object> getSequence()
  {
    return list_;
  }

  public Iterator<Token> iterator()
  {
    return new TokenSeqIterator(getSequence());
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

  public static class TokenSeqIterator
    implements Iterator<Token>
  {
    Stack<Iterator> stack_ = new Stack<Iterator>();
    Token next_;

    protected TokenSeqIterator(List<Object> list)
    {
      stack_.push(list.iterator());
      next_ = null;
    }

    public boolean hasNext()
    {
      if (next_ != null) return true;
      while (! stack_.isEmpty() && ! stack_.peek(). hasNext()) {
        stack_.pop();
      }
      if (stack_.isEmpty()) return false;
      Object next = stack_.peek().next();
      if (next instanceof Token) {
        next_ = (Token) next;
        return true;
      }
      TokenSequence seq = (TokenSequence) next;
      stack_.push(seq.getSequence().iterator());
      return hasNext();
    }

    public Token next()
    {
      if (! hasNext()) throw new NoSuchElementException();
      Token result = next_;
      next_ = null;
      return result;
    }

    public void remove()
    {
      throw new UnsupportedOperationException();
    }
  }
}
