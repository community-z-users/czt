package net.sourceforge.czt.eclipse.ui.internal.editors;

import java.util.ArrayList;
import java.util.List;

import org.xml.sax.Attributes;
import org.xml.sax.SAXException;
import org.xml.sax.ext.DefaultHandler2;

/**
 * @author Chengdong Xu
 * @author Andrius Velykis
 */
public class ZXmlHandler extends DefaultHandler2
{

  private List<List<Object>> fCharTable = new ArrayList<List<Object>>();

  private List<Object> fCurrentRow;

  public List<List<Object>> getCharList()
  {
    return fCharTable;
  }

  @Override
  public void startElement(String uri, String localName, String qName, Attributes attributes)
      throws SAXException
  {
    if ("row".equals(qName)) {
      fCurrentRow = createRow(attributes);
      fCharTable.add(fCurrentRow);
    }
    else if ("item".equals(qName)) {
      fCurrentRow.add(createZChar(attributes));
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
