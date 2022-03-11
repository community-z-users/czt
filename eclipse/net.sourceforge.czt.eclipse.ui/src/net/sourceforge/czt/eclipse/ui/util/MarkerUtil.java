package net.sourceforge.czt.eclipse.ui.util;

public class MarkerUtil
{
  
  private static final int DEFAULT_MAX_LENGTH = 21000;
  private static final String MARKER_SHORTEN_TEXT = " <..>"; 

  /**
   * Adapts a String value for markers to be less than allowed max length. Implements a quick check
   * which may trim too much, but should be quicker.
   * 
   * @param value
   * @return the value itself if it is of correct length, a trimmed value otherwise.
   */
  public static String adaptMarkerValue(String value) {
    
    if (value == null) {
      return value;
    }
    
    // from org.eclipse.core.internal.resources.MarkerInfo
    // we cannot write attributes whose UTF encoding exceeds 65535 bytes.
    // quick check based on maximum 3 bytes per character
    if (value.length() < DEFAULT_MAX_LENGTH) {
      return value;
    }
    
    // shorten the value automatically
    String shortVal = value.substring(0, DEFAULT_MAX_LENGTH - MARKER_SHORTEN_TEXT.length());
    
    return shortVal + MARKER_SHORTEN_TEXT;
  }
  
}
