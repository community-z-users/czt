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

package net.sourceforge.czt.print.zeves;

import java.io.Writer;
import net.sourceforge.czt.parser.util.Token;
import net.sourceforge.czt.parser.zeves.ZEvesProofToken;
import net.sourceforge.czt.session.Dialect;

/**
 *
 * @author Leo Freitas
 * @date Aug 10, 2011
 */
public class UnicodePrinter
  extends net.sourceforge.czt.print.z.UnicodePrinter
{
  /**
   * Create a new PrintWriter, without automatic line flushing.
   *
   * @param out a character-output stream.
   */
  public UnicodePrinter(Writer out)
  {
    super(out);
  }

  /**
   * Create a new PrintWriter.
   *
   * @param out a character-output stream.
   * @param autoFlush a boolean; if true, the println() methods
   *                  will flush the output buffer
   */
  public UnicodePrinter(Writer out, boolean autoFlush)
  {
    super(out, autoFlush);
  }

  @Override
  public boolean addExtraNLFor(Token token)
  {
    return (super.addExtraNLFor(token) || 
            ZEvesProofToken.ZPROOFCOMMANDSEP.getName().equals(token.getName()) ||
            ZEvesProofToken.ZPROOF.getName().equals(token.getName()));
  }
  
	@Override
	public Dialect getDialect() {
		return Dialect.ZEVES;
	}

}

