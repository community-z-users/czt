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

import net.sourceforge.czt.parser.util.CztScanner;

/**
 *
 * @author Leo Freitas
 * @date Aug 10, 2011
 */
public class NewlineScanner extends net.sourceforge.czt.print.z.NewlineScanner
{

  public NewlineScanner(CztScanner scanner)
  {
    super(scanner);
  }

  // DONT CALL SUPER: Sym.ZED in one parser might be different from another one
  @Override
  protected boolean isBoxSymbol(int sym)
  {
    return Sym.ZED == sym || Sym.AX == sym
        || Sym.GENAX == sym || Sym.GENSCH == sym
        || Sym.ZPROOF == sym 
        || Sym.ZPROOFSECTION == sym;
  }

  @Override
  protected boolean isWhereSymbol(int sym)
  {
    return Sym.WHERE == sym;
  }

  @Override
  protected boolean isSchSymbol(int sym)
  {
    return Sym.SCH == sym;
  }

  @Override
  protected int getNLSym()
  {
    return Sym.NL;
  }

  @Override
  protected Class<?> getSymbolClass()
  {
    return Sym.class;
  }
}
