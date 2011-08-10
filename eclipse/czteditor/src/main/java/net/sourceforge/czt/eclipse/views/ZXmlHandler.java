/**
 * 
 */

package net.sourceforge.czt.eclipse.views;

import java.util.ArrayList;
import java.util.List;

import com.microstar.xml.*;

/**
 * @author Chengdong Xu
 *
 */
public class ZXmlHandler extends HandlerBase
{

  private List<List<Object>> fCharTable = new ArrayList<List<Object>>();

  private List<Object> fCurrentRow;
  
  private String fName;
  private String fUnicode;
  private String fLatex;
  private String fDescription;

  /**
   * 
   */
  public ZXmlHandler()
  {
    super();
  }

  public List<List<Object>> getCharList()
  {
    return fCharTable;
  }

  /**
   * @see org.xml.sax.helpers.DefaultHandler#startDocument()
   */
  public void startDocument()
  {
  }
  
  public void attribute(String name, String value, boolean isSpecified)
  {
    if ("HEADING".equalsIgnoreCase(name)) {
      fCurrentRow = new ArrayList<Object>();
      fCurrentRow.add(value);
    }
    else if ("NAME".equalsIgnoreCase(name)) {
      fName = value;
    }
    else if ("UNICODE".equalsIgnoreCase(name)) {
      fUnicode = value;
    }
    else if ("LATEX".equalsIgnoreCase(name)) {
      fLatex = value;
    }
    else if ("DESCRIPTION".equalsIgnoreCase(name)) {
      fDescription = value;
    }
  }
  public void endElement(String element)
  {
    if ("TABLE".equalsIgnoreCase(element)) {
    }
    else if ("ROW".equalsIgnoreCase(element)) {
      fCharTable.add(fCurrentRow);
    }
    else if ("ITEM".equalsIgnoreCase(element)) {
      if (fUnicode == null)
        fUnicode = fName;
      /*
      System.out.println("ZCHAR    = " + fName + 
    		  		   "\n UNICODE = " + 
    		  		   		(fUnicode.length() == 1 ? 
    		  				   "U+" + Integer.toHexString(fUnicode.codePointAt(0)) : 
    		  					fUnicode)+ 
    		  		   "\n LATEX   = " + fLatex +
    		  		   "\n DESCRIP = " + fDescription);	
      */
      fCurrentRow.add(new ZChar(fName, fUnicode, fLatex, fDescription));
      fName = fUnicode = fLatex = fDescription = null;
    }
  }

  public void endDocument()
  {
  }
}
