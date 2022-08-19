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

import java.nio.charset.Charset;
import java.nio.charset.StandardCharsets;
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
  
  final static String [] KNOWN_FILENAME_SUFFIXES = {
    ".tex", ".zed", ".zed8", ".zed16", ".oz", ".oz8", ".oz16",
    ".circus", ".circus8", ".circus16", ".zedpatt", ".zedpatt8", ".zedpatt16",
    ".zev", ".zev8", ".zev16", ".zml"};
  
  //TODO: These could come from a configuration file perhaps?
  public static List<String> getKnownLatexSuffixes()
  {
    // .error is used in the type checker tests for negative test cases
    return Arrays.asList(".tex", ".zed", ".oz", ".circus", ".zedpatt", ".zev", "error");
  }
  
  public static List<String> getKnownUnicodeSuffixes()
  {
    return Arrays.asList(".zed8", ".zed16", ".oz8", ".oz16", ".circus8", ".circus16", ".zedpatt8", ".zedpatt16", ".zev8", "zev16", "error8", "error16");
  }
  
  public static List<String> getKnownXMLSuffixes()
  {
    // eml = for XML errors tests?
    return Arrays.asList(".zml", ".xml", "eml");
  }
  
  public static List<String> getAllSufixes()
  {
	  //List<String> result = getKnownLatexSuffixes();
	  //result.addAll(getKnownUnicodeSuffixes());
	  //result.addAll(getKnownXMLSuffixes());
	  //result.removeAll(getAllErrorSufixes());
	  return Arrays.asList(KNOWN_FILENAME_SUFFIXES);
  }
  
  public static List<String> getAllErrorSufixes()
  {
	  return Arrays.asList(".error", ".error8", ".error16");
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
  
  public static Charset getDefaultEncoding(Markup markup)
  {
	  if (Markup.LATEX.equals(markup))
		  return StandardCharsets.US_ASCII;
	  else
		  return StandardCharsets.UTF_8;
  }

  public static String getDefaultFileExtention(Markup markup)
  {
    switch (markup)
    {
      case LATEX  : return ".tex";
      case UNICODE: return ".zed8";
      case ZML    : return ".zml";
      default     : throw new Error();
    }
  }
}
