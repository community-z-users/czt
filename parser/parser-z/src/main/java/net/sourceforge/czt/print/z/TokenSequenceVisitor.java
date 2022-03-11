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

package net.sourceforge.czt.print.z;

import java.util.Stack;
import java.util.Properties;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.visitor.TermVisitor;
import net.sourceforge.czt.parser.util.Token;
import net.sourceforge.czt.print.util.TokenSequence;
import net.sourceforge.czt.session.Dialect;
import net.sourceforge.czt.session.SectionInfo;


/**
 * A new TokenSequenceVisitor needs to be created for each print
 * since a Stack is build up while recursing into children.
 */
public class TokenSequenceVisitor
  implements TermVisitor<Object>,
             ZPrinter
{
  private ZPrintVisitor visitor_;
  private final Stack<TokenSequence> stack_ = new Stack<TokenSequence>();
  private final ZPrinter tokenSeqPrinter_;

  protected TokenSequenceVisitor(SectionInfo si, ZPrinter tokenSeqPrinter)
  {
	if (tokenSeqPrinter == null || si == null) throw new NullPointerException();
    tokenSeqPrinter_ = tokenSeqPrinter;
    setZPrintVisitor(new ZPrintVisitor(si, this));
  }

  public TokenSequenceVisitor(SectionInfo si, ZPrinter tokenSeqPrinter, Properties props)
  {
    if (tokenSeqPrinter == null || si == null) throw new NullPointerException();
    tokenSeqPrinter_ = tokenSeqPrinter;
    setZPrintVisitor(new ZPrintVisitor(si, this, props));
  }

  protected final void setZPrintVisitor(ZPrintVisitor visitor)
  {
    visitor_ = visitor;
    visitor_.setVisitor(this);
  }

  //@ requires (* visitTerm has been called first *)
  public TokenSequence getResult()
  {
    return stack_.pop();
  }

  @Override
  public Object visitTerm(Term term)
  {
    String s = term.getClass().toString();
    begin(s);
    term.accept(visitor_);
    end(s);
    return null;
  }

  private void begin(String s)
  {
    stack_.push(new TokenSequence(s, tokenSeqPrinter_));
  }

  @Override
  public void printToken(Token token)
  {
    stack_.peek().add(token);
  }

  public void end(String s)
  {
    TokenSequence tseq = stack_.pop();
    if (!tseq.getName().equals(s)) throw new IllegalStateException();
    if (stack_.empty()) {
      stack_.push(tseq);
    }
    else {
      stack_.peek().add(tseq);
    }
  }

	@Override
	public Dialect getDialect() {
		return tokenSeqPrinter_.getDialect();
	}
}
