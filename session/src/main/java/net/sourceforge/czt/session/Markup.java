/*
  Copyright (C) 2005, 2007 Petra Malik
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

package net.sourceforge.czt.session;

import java.util.Arrays;
import java.util.List;

/**
 * An enumeration of supported mark-ups.
 */
public enum Markup
{
  LATEX,
  UNICODE,
  ZML;
  
  public final static String [] KNOWN_FILENAME_SUFFIXES = {
    ".tex", ".zed", ".zed8", ".zed16", ".oz", ".oz8", ".oz16",
    ".circus", ".circus8", ".circus16", ".zedpatt", ".zedpatt8", ".zedpatt16",
    ".zev", ".zev8", ".zev16", ".zml"};
  
  //TODO: These could come from a configuration file perhaps?
  public static List<String> getKnownLatexSuffixes()
  {
    return Arrays.asList(".tex", ".zed", ".oz", ".circus", ".zedpatt", ".zev");
  }
  
  public static List<String> getKnownUnicodeSuffixes()
  {
    return Arrays.asList(".zed8", ".zed16", ".oz8", ".oz16", ".circus8", ".circus16", ".zedpatt8", ".zedpatt16", ".zev8", "zev16");
  }
  
  public static List<String> getKnownXMLSuffixes()
  {
    return Arrays.asList(".zml", ".xml");
  }
  
  public static Markup getMarkup(String filename)
  {
    if (filename == null) throw new IllegalArgumentException("Null file name");
    Markup result = null;    
    for(String suffix : getKnownLatexSuffixes())
    {
      if (filename.toLowerCase().endsWith(suffix)) return Markup.LATEX;
    }
    for(String suffix : getKnownUnicodeSuffixes())
    {
      if (filename.toLowerCase().endsWith(suffix)) return Markup.UNICODE;
    }
    for(String suffix : getKnownXMLSuffixes())
    {
      if (filename.toLowerCase().endsWith(suffix)) return Markup.ZML;
    }        
    return result;
  }

  public static String getDefaultFileExtention(Markup markup)
  {
    switch (markup)
    {
      case LATEX  : return ".tex";
      case UNICODE: return ".zed16";
      case ZML    : return ".zml";
      default     : throw new Error();
    }
  }
}
