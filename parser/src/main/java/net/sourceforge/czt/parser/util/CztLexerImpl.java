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

import java.util.Properties;
import net.sourceforge.czt.util.Section;

/**
 *
 * @author Leo Freitas
 * @date Aug 4, 2011
 */
public abstract class CztLexerImpl extends TokeniserDebugger implements Lexer {

  protected CztLexerImpl()
  {
    super();
  }

  protected CztLexerImpl(Properties properties)
  {
    super(properties);
  }

  private long tokenCnt_ = 1;
  private final static String LOG_TOKEN = "{0} token no ({1}):\t ({2}, {3}, \t NL={4}, \t {5}).";

  protected boolean isKnownToolkit(LocInfo locInfo)
  {
    boolean result = locInfo != null && locInfo.getSource() != null;
    if (result)
    {
      final String source = locInfo.getSource();
      for(Section s : Section.values())
      {
        result = source.indexOf(s.getName()) != -1;
        if (result) break;
      }
    }
    return result;
  }

  public void logToken(LocToken token)
  {
    if (token != null && logDebugInfo() && !isKnownToolkit(token.getLocation()))
    {
      final String spelling = String.valueOf(token.getSpelling());
      logFormatted(LOG_TOKEN,
              getClass().getSimpleName(),
              tokenCnt_,
              token.getName(),
              // only get the 1st 15 characters of spelling and substitute any NL to SPACE
              spelling.substring(0, spelling.length() > 15 ? 15 : spelling.length()).replaceAll("\\s", " "),
              token.getNewlineCategory(),
              token.getLocation());
      tokenCnt_++;
    }
  }
}
