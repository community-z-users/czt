package net.sourceforge.czt.eclipse.core.parser;

import net.sourceforge.czt.session.StringSource;

/**
 * An extension of a {@link StringSource}, which allows explicitly indicating the file path that the
 * source represents.
 * 
 * @author Andrius Velykis
 */
public class StringFileSource extends StringSource
{
  
  private final String filePath;

  public StringFileSource(String value, String filePath)
  {
    super(value, filePath);
    this.filePath = filePath;
  }
  
  public String getPath() {
    return filePath;
  }

}
