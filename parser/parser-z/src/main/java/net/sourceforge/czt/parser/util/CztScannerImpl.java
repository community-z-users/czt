
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
import java_cup.runtime.Symbol;

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
    super(properties);
  }

  private long symbolCnt_ = 1;

  //          SCANNER token NO : (SYM-NAME, SYM-VAL (SYM-VAL-LEN) SYM-JAVA-CLASS).
  private final static String LOG_SYMBOL = "{0} token no ({1}): ({2}, {3} ({4}) \t\t, {5}, {6}).";

  protected abstract Class<?> getSymbolClass();

  private Map<Object, String> symbolMap_ = null;
  private Map<String, Object> symbolMap2_ = null;

  protected Map<Object, String> getSymbolMap()
  {
    if (symbolMap_ == null)
    {
      symbolMap_ = DebugUtils.getFieldMap(getSymbolClass());
    }
    return symbolMap_;
  }

  protected Map<String, Object> getSymbolMap2()
  {
    if (symbolMap2_ == null)
    {
      symbolMap2_ = DebugUtils.getFieldMap2(getSymbolClass());
    }
    return symbolMap2_;
  }

  @Override
  public void logSymbol(Symbol symbol)
  {
    if (logDebugInfo())
    {
      String symbolV = String.valueOf(symbol.value);
      final String symbolValue;
      // for simple unicode symbols get its Hex value
      if (symbolV.length() == 1)
      {
        int codePoint = symbolV.codePointAt(0);
        if (!Character.isWhitespace(codePoint) &&
            !Character.isLetterOrDigit(codePoint) &&
            !(codePoint >= 0x20 && codePoint <= 0x7E))
          symbolValue = "U+" + Integer.toHexString(codePoint);
        else
          symbolValue = symbolV;
      }
      // for higher (more than Uniode8?) get first symbol as well
      else if (symbolV.length() == 2 && symbolV.codePointCount(0, 1) == 1)
      {
        symbolValue = "U+" + Integer.toHexString(symbolV.codePointAt(0)) + "; U+" + Integer.toHexString(symbolV.codePointAt(1));  // U+20 = space?
      }
      else
        // only get the 1st 20 characters of spelling and substitute any NL to SPACE
        symbolValue = symbolV.substring(0, symbolV.length() > 20 ? 20 : symbolV.length()).replaceAll("\\s", " ");
      logFormatted(LOG_SYMBOL, 
              getClass().getSimpleName(),
              symbolCnt_,
              getSymbolMap().get(symbol.sym),
              symbolValue,
              symbolV.length(),
              symbol.value != null ? symbol.value.getClass().getName() : "null",
              getDialect());
      symbolCnt_++;
    }
  }
}
