package net.sourceforge.czt.eclipse.core.document;

import net.sourceforge.czt.eclipse.core.parser.StringFileSource;
import net.sourceforge.czt.session.FileSource;
import net.sourceforge.czt.session.Source;

public class DocumentUtil
{

  /**
   * Tries to resolve the file path of the given source object.
   * 
   * @param source
   * @return the path, or <code>null</code> if could not resolve it
   */
  public static String getPath(Source source) {
    if (source instanceof FileSource) {
      FileSource fileSource = (FileSource) source;
      // TODO something more deterministic than toString() to get the path?
      return fileSource.toString();
    }
    
    if (source instanceof StringFileSource) {
      return ((StringFileSource) source).getPath();
    }
    
    return null;
  }

}
