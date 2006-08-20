/*
 * Created on 2005-10-13
 *
 * TODO To change the template for this generated file go to
 * Window - Preferences - Java - Code Style - Code Templates
 */

package net.sourceforge.czt.eclipse.views;

import java.io.IOException;
import java.io.InputStream;
import java.util.List;

import javax.xml.parsers.ParserConfigurationException;
import javax.xml.parsers.SAXParser;
import javax.xml.parsers.SAXParserFactory;

import net.sourceforge.czt.eclipse.CZTPlugin;

import org.eclipse.core.runtime.FileLocator;
import org.eclipse.core.runtime.IPath;
import org.xml.sax.SAXException;

import com.microstar.xml.XmlParser;

/**
 * @author Chengdong Xu
 */
public class ZCharTable
{
  // Path of the character file
  private final IPath fPath;
  
  /**
   * An array of objects where the first column contains strings
   * (the heading for the corresponding row) and all other columns
   * contain ZChar objects.
   */
  private final Object[][] mTableArray;

  public ZCharTable(IPath path)
  {
    fPath = path;
    mTableArray = getTable(path);
//    mTableArray = getTableFromFile(path);
  }

  /**
   * Returns the Z Char file
   */
  public IPath getZCharFile()
  {
    return this.fPath;
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
  
  public Object[][] getTable(IPath path) {
    try {
      InputStream stream = FileLocator.openStream(CZTPlugin.getDefault().getBundle(), path, false);
      if (stream == null)
        return new Object[0][0];
      XmlParser parser = new XmlParser();
      ZXmlHandler handler = new ZXmlHandler();
      parser.setHandler(handler);
      parser.parse(null, null, stream, null);
      
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
/*  
  public Object[][] getTableFromFile(IPath path) {
    try {
    SAXParserFactory factory = SAXParserFactory.newInstance();
    SAXParser parser = factory.newSAXParser();
    parser.parse(FileLocator.openStream(CZTPlugin.getDefault().getBundle(), path, false), new CztXmlHandler());
    } catch(SAXException se) {
      System.out.println("SAXException-->");
      se.printStackTrace();
    } catch(ParserConfigurationException pce) {
      System.out.println("ParserConfigurationException-->");
      pce.printStackTrace();
    } catch(IOException ioe) {
      System.out.println("Cann't read the file.");
      ioe.printStackTrace();
    }
      
    
    return new Object[0][];
  }
*/
}
