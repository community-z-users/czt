/*
  Copyright (C) 2005 Petra Malik
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

package net.sourceforge.czt.parser.zpatt;

/**
 * An enumeration of possible Zpatt parse/scan messages, warnings, and
 * errors that may occur during a parse.
 */
public enum ZpattParseMessage
{
  MSG_UNKNOWN_JOKER_TYPE ("Unknow joker type {0}"),
  MSG_CANNOT_MERGE_JOKERTABLES ("Cannot merge the parent joker tables ({0})"),
  MSG_CANNOT_ADD_JOKER ("Cannot add joker ({0})");

  private final String message_;
  private final String explanation_;

  ZpattParseMessage(String message)
  {
    message_ = message;
    explanation_ = null;
  }

  ZpattParseMessage(String message, String explanation)
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
}
