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

package net.sourceforge.czt.print.z;

import net.sourceforge.czt.parser.util.Token;
import net.sourceforge.czt.parser.z.ZToken;
import net.sourceforge.czt.session.Dialect;

/**
 * Newline printer adaptor to consider NewlineCategory whilst printing Unicode
 *
 * TODO: check within AbstractPRinterCommand about PrettyPrinter's role when PROP_WIDTH_TEXT is present (!)
 *
 * Not the best place. Use PrettyPrinter instead (!)
 * 
 * @author Leo Freitas
 * @date Aug 11, 2011
 */
public class NewlinePrinter 
        implements ZPrinter
{

  private final ZPrinter printer_;

  public NewlinePrinter(ZPrinter printer)
  {
    printer_ = printer;
  }
  
  @Override
  public Dialect getDialect()
  {
	  return printer_.getDialect();
  }

  @Override
  public void printToken(Token token)
  {
    // TokenSequence or NL or SPACE, don't process
    if (token.getNewlineCategory() == null ||
            ZToken.NL.equals(token) ||
            ZToken.INDENT.equals(token))
    {
      printer_.printToken(token);
    }
    else
    {
      boolean before = false;
      boolean after = false;
      switch (token.getNewlineCategory())
      {
        case BEFORE:
          before = true;
          break;
        case AFTER:
          after = true;
          break;
        case BOTH:
          before = true;
          after  = true;
          break;
        case NEITHER:
        default:
          break;
      }
      if (before)
        printer_.printToken(ZToken.NL);
      printer_.printToken(token);
      if (after)
        printer_.printToken(ZToken.NL);
    }
  }
}
