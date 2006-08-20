/**
 * 
 */

package net.sourceforge.czt.eclipse.views;

import org.xml.sax.Attributes;
import org.xml.sax.ext.DefaultHandler2;

/**
 * @author Chengdong
 *
 */
public class CztXmlHandler extends DefaultHandler2
{

  public void startDocument() {
    
  }
  
  public void startElement(String namespaceURI, String localName, String qName,
      Attributes attributes)
  {
    System.out.println("Start Element: namespaceURI-" + namespaceURI
        + " --> localName-" + localName + " --> qName-" + qName + " --> attributes-" + attributes);
  }
  
  public void characters(char[] ch, int start, int length) {
    System.out.println("Characters: " + ch + " --- Start at-" + start + " --- length of-" + length);
  }
  
  public void endElement(String namespaceURI, String localName, String qName) {
    System.out.println("Start Element: namespaceURI-" + namespaceURI
        + " --> localName-" + localName + " --> qName-" + qName);
  }
  
  public void endDocument() {
    
  }

}
