package net.sourceforge.czt.jedit.zcharmap;

import java.util.ArrayList;
import java.util.List;

import org.xml.sax.Attributes;
import org.xml.sax.SAXException;
import org.xml.sax.ext.DefaultHandler2;

/**
 * 
 * @author Andrius Velykis
 */
public class CztXmlHandler extends DefaultHandler2
{
  private List<List<Object>> table_ = new ArrayList<List<Object>>();
  private List<Object> row_;

  public List<List<Object>> getList()
  {
    return table_;
  }
  
  @Override
  public void startElement(String uri, String localName, String qName, Attributes attributes)
      throws SAXException
  {
    if ("row".equals(qName)) {
      row_ = createRow(attributes);
      table_.add(row_);
    }
    else if ("item".equals(qName)) {
      row_.add(createZChar(attributes));
    }
  }

  private List<Object> createRow(Attributes attributes)
  {
    List<Object> row = new ArrayList<Object>();

    String rowHeading = attributes.getValue("heading");
    row.add(rowHeading);

    return row;
  }

  private ZChar createZChar(Attributes attributes)
  {

    String name = attributes.getValue("name");
    String description = attributes.getValue("description");
    String unicode = attributes.getValue("unicode");
    String latex = attributes.getValue("latex");

    if (unicode == null) {
      unicode = name;
    }

    return new ZChar(name, unicode, latex, description);
  }

}
