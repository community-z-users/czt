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

import java.text.MessageFormat;

/**
 *
 * @author Leo Freitas
 * @date Aug 10, 2011
 */
public enum ZEvesPrintMessage {

  MSG_PRINT_LATEX_EXCEPTION("An exception occurred while trying to print " +
        "LaTeX markup for term within section {0}"),
  MSG_PRINT_OLDLATEX_EXCEPTION("An exception occurred while trying to print " +
        "old (Spivey's) LaTeX markup within section {0}"),
  MSG_PRINTTERMLIST_EXCEPTION("{0} is processed by printTermList directly")

        ;

  private final String message_;
  private final String explanation_;

  ZEvesPrintMessage(String message)
  {
    message_ = message;
    explanation_ = null;
  }

  ZEvesPrintMessage(String message, String explanation)
  {
    message_ = message;
    explanation_ = explanation;
  }

  String getMessage()
  {
    return message_;
  }

  String getExplanation()
  {
    return explanation_;
  }

  String format(Object... args)
  {
    return MessageFormat.format(message_, args);
  }
}
