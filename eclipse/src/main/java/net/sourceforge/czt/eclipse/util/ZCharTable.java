/*
 * Created on 2005-10-13
 *
 * TODO To change the template for this generated file go to
 * Window - Preferences - Java - Code Style - Code Templates
 */

package net.sourceforge.czt.eclipse.util;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;

import net.sourceforge.czt.eclipse.CZTPlugin;
import net.sourceforge.czt.eclipse.views.ZXmlHandler;

import org.apache.xerces.parsers.SAXParser;
import org.eclipse.core.runtime.Platform;
import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;
import org.xml.sax.SAXException;

/**
 * @author Chengdong Xu
 */
public class ZCharTable
{
  private final String ZTABLEFILE = "lib/ZTable.xml";

  /**
   * An array of objects where the first column contains strings
   * (the heading for the corresponding row) and all other columns
   * contain ZChar objects.
   */
  private Object[][] mTableArray = createZCharTable();
//  private Object[][] mTableArray = getTable();

  public ZCharTable()
  {
  }

  /**
   * Returns the Z Char file
   */
  public File getZCharFile()
  {
    try {
      return new File(Platform.resolve(
          CZTPlugin.getDefault().getBundle().getEntry("/")).getFile(),
          this.ZTABLEFILE);
    } catch (IOException ie) {

    }

    return null;
    /*
     String filepath = getClass().getResource("/ZTable2.xml").getFile();
     return new File(filepath);
     */
  }

  /**
   * Returns the Object array comprising Z char table.
   *
   * @return the Object array comprising Z char table.
   */
  public Object[][] getZCharTable()
  {
    return this.mTableArray;
  }

  public Object[][] createZCharTable()
  {
    Object[][] table;
    // to store all z chars
    List tableList = new ArrayList();
    try {
      DocumentBuilderFactory factory = DocumentBuilderFactory.newInstance();
      DocumentBuilder builder = factory.newDocumentBuilder();
      File file = getZCharFile();
      if (file == null)
        return new Object[0][0];
      Document doc = builder.parse(file);
      
      // gets the root of the structure of the XML file
      Element root = doc.getDocumentElement();
      // gets the list of all items
      NodeList rows = root.getChildNodes();
      for (int i = 0; i < rows.getLength(); i++) {
        Node rowNode = rows.item(i);
        // continue if the child is not an element, but a whitespace
        if (!(rowNode instanceof Element))
          continue;
        // to store all z chars in a row of the XML file
        List rowList = new ArrayList();
        Element row = (Element) rowNode;
        String heading = row.getAttribute("heading");
        rowList.add(heading);
        NodeList items = row.getChildNodes();
        for (int j = 0; j < items.getLength(); j++) {
          Node itemNode = items.item(j);
          // continue if the child is not an element, but a whitespace
          if (!(itemNode instanceof Element))
            continue;
          Element item = (Element) itemNode;
          String name = item.getAttribute("name");
          String description = item.getAttribute("description");
          String unicode = item.getAttribute("unicode");
          String latex = item.getAttribute("latex");
          ZChar zch;
          if (unicode == null)
            zch = new ZChar(name, latex, description);
          else
            zch = new ZChar(name, unicode, latex, description);
          rowList.add(zch);
        }

        Object[] rowArray = new Object[rowList.size()];
        rowList.toArray(rowArray);
        tableList.add(rowArray);
      }
    } catch (IOException ie) {
      ie.printStackTrace();
    } catch (ParserConfigurationException pce) {
      pce.printStackTrace();
    } catch (SAXException se) {
      se.printStackTrace();
    }

    table = new Object[tableList.size()][];
    tableList.toArray(table);

    return table;
  }

  /**
   * Returns the maximum length of all the rows.
   *
   * @return the number of columns in this table.
   */
  public int getColumnCount()
  {
    int erg = 0;
    for (int i = 0; i < mTableArray.length; i++) {
      if (mTableArray[i].length > erg) {
        erg = mTableArray[i].length;
      }
    }
    return erg;
  }

  /**
   * Returns the number of rows.
   *
   * @return the number of rows in this table.
   */
  public int getRowCount()
  {
    return mTableArray.length;
  }

  /**
   * Gets the object at the specified position.
   * If no object can be found the empty string
   * is returned.
   *
   * @return the object at the specified position
   *         or the empty string (should never be
   *         <code>null</code>). 
   */
  public Object getValueAt(int row, int col)
  {
    try {
      return mTableArray[row][col];
    } catch (IndexOutOfBoundsException e) {
      return "";
    }
  }

  /**
   * Returns <code>String.class</code> if <code>col</code>
   * is zero, <code>ZChar.class</code> otherwise.
   * Note that this method does not take the actual classes
   * contained in table into account.
   *
   * @return <code>String.class</code> if <code>col</code>
   *         is zero, <code>ZChar.class</code> otherwise.
   */
  public Class getColumnClass(int col)
  {
    if (col == 0) {
      return String.class;
    }
    return ZChar.class;
  }

  /**
   * Returns <code>null</code> regardless of the column number.
   *
   * @return <code>null</code>
   */
  public String getColumnName(int col)
  {
    return null;
  }
  
  public Object[][] getTable() {
    try {
      ZXmlHandler handler = new ZXmlHandler();
      SAXParser parser = new SAXParser();
      parser.setContentHandler(handler);
      parser.setErrorHandler(handler);
      parser.parse(getZCharFile().getAbsolutePath());
      
      List<List<Object>> lists = handler.getCharList();
      int maxsize = 0;
      for (List<Object> list : lists) {
        int size = list.size();
        if (size > maxsize) maxsize = size;
      }
      Object[][] result = new Object[lists.size()][maxsize];
      int i = 0;
      for (List<Object> list : lists) {
        int j = 0;
        for (Object elem : list) {
          result[i][j] = elem;
          j++;
        }
        i++;
      }
      return result;
      
    } catch (Exception e) {
      e.printStackTrace();
    }
    return new Object[0][];
  }
}
