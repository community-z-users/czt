package net.sourceforge.czt.eclipse.ui.internal.editors;

import java.io.InputStream;
import java.util.List;

import javax.xml.parsers.SAXParser;
import javax.xml.parsers.SAXParserFactory;

import net.sourceforge.czt.eclipse.ui.CztUIPlugin;

import org.eclipse.core.runtime.FileLocator;
import org.eclipse.core.runtime.IPath;

import static java.lang.Math.max;

/**
 * @author Chengdong Xu
 * @author Andrius Velykis
 */
public class ZCharTable
{
  
  /**
   * An array of objects where the first column contains strings
   * (the heading for the corresponding row) and all other columns
   * contain ZChar objects.
   */
  private final Object[][] mTableArray;

  public ZCharTable(IPath path)
  {
    mTableArray = loadTable(path);
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

  private Object[][] loadTable(IPath path)
  {
    ZXmlHandler handler = new ZXmlHandler();

    try {
      InputStream stream = FileLocator.openStream(CztUIPlugin.getDefault().getBundle(), path, false);

      SAXParserFactory factory = SAXParserFactory.newInstance();
      SAXParser saxParser = factory.newSAXParser();

      saxParser.parse(stream, handler);
    }
    catch (Exception e) {
      CztUIPlugin.log(e);
    }

    List<List<Object>> lists = handler.getCharList();
    int maxSize = 0;
    for (List<Object> list : lists) {
      maxSize = max(maxSize, list.size());
    }
    
    Object[][] result = new Object[lists.size()][maxSize];
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
  }
}
