
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

package net.sourceforge.czt.parser.util;

import java.util.Map;
import java.util.Properties;
import net.sourceforge.czt.java_cup.runtime.Symbol;

/**
 *
 * @author Leo Freitas
 * @date Aug 4, 2011
 */
public abstract class CztScannerImpl
        extends TokeniserDebugger implements CztScanner {

  protected CztScannerImpl()
  {
    super();
  }

  protected CztScannerImpl(Properties properties)
  {
    super();
  }

  private long symbolCnt_ = 1;
  private final static String LOG_SYMBOL = "{0} token no ({1}): ({1}, {2}, {3}).";

  protected abstract Class<?> getSymbolClass();

  private Map<Object, String> symbolMap_ = null;

  protected Map<Object, String> getSymbolMap()
  {
    if (symbolMap_ == null)
    {
      symbolMap_ = DebugUtils.getFieldMap(getSymbolClass());
    }
    return symbolMap_;
  }

  @Override
  public void logSymbol(Symbol symbol)
  {
    if (logDebugInfo())
    {
      final String symbolValue = String.valueOf(symbol.value);
      logFormatted(LOG_SYMBOL, 
              symbolCnt_,
              getClass().getSimpleName(),
              getSymbolMap().get(symbol.sym),
              // only get the 1st 20 characters of spelling and substitute any NL to SPACE
              symbolValue.substring(0, symbolValue.length() > 20 ? 20 : symbolValue.length()).replaceAll("\\s", " "),
              symbol.value != null ? symbol.value.getClass().getName() : "null");
      symbolCnt_++;
    }
  }
}
