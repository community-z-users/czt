/**
 * 
 */

package net.sourceforge.czt.eclipse.views;

import java.util.ArrayList;
import java.util.List;

import org.xml.sax.Attributes;
import org.xml.sax.helpers.DefaultHandler;

/**
 * @author Chengdong Xu
 *
 */
public class ZXmlHandler extends DefaultHandler
{

  List<List<Object>> fCharTable = new ArrayList<List<Object>>();

  List<Object> fCurrentRow;

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
    System.out.println("startDocument");
  }

  /**
   * @see org.xml.sax.helpers.DefaultHandler#startElement(java.lang.String, java.lang.String, java.lang.String, org.xml.sax.Attributes)
   */
  public void startElement(String uri, String localName, String rawName,
      Attributes attributes)
  {
    if ("TABLE".equalsIgnoreCase(rawName))
      fCharTable = new ArrayList<List<Object>>();
    else if ("ROW".equalsIgnoreCase(rawName)) {
      fCurrentRow = new ArrayList<Object>();
      fCurrentRow.add(attributes.getValue("heading"));
    }
    else if ("ITEM".equalsIgnoreCase(rawName)) {
      String name = attributes.getValue("name");
      String unicode = attributes.getValue("unicode");
      String latex = attributes.getValue("latex");
      String description = attributes.getValue("description");
      if (unicode == null)
        unicode = name;
      fCurrentRow.add(new ZChar(name, unicode, latex, description));
    }
  }

  /**
   * @see org.xml.sax.helpers.DefaultHandler#endElement(java.lang.String, java.lang.String, java.lang.String)
   */
  public void endElement(String uri, String localName, String rawName)
  {
    if ("TABLE".equalsIgnoreCase(rawName)) {

    }
    else if ("ROW".equalsIgnoreCase(rawName)) {
      fCharTable.add(fCurrentRow);
    }
    else if ("ITEM".equalsIgnoreCase(rawName)) {

    }
  }

  /**
   * @see org.xml.sax.helpers.DefaultHandler#endDocument()
   */
  public void endDocument()
  {
    System.out.println("endDocument");
  }
}
