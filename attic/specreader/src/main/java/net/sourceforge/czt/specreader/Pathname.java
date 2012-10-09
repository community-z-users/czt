package net.sourceforge.czt.specreader;

/**
 * Records the details of a pathname.
 * 
 * @author ian
 */
public final class Pathname
{
  /** Text of the pathname */
  private String name_;

  /**
   * Constructs a pathname.
   * 
   * @param name text of this pathname
   */
  public Pathname(String name)
  {
    name_ = name;
  }

  /**
   * Projects the part without the file type suffix.
   * 
   * @return basename of pathname
   */
  public String basename()
  {
    final int suffixPos = name_.lastIndexOf('.');
    if (suffixPos == -1) {
      return name_;
    } else {
      return name_.substring(0, suffixPos);
    }
  }

  /**
   * Projects the file type suffix.
   * 
   * @return suffix of pathname
   */ 
  public String suffix()
  {
    final int suffixPos = name_.lastIndexOf('.');
    if (suffixPos == -1) {
      return "";
    } else {
      return name_.substring(suffixPos, name_.length());
    }
  }

  /**
   * Returns the text of this pathname.
   */
  public String toString()
  {
    return name_;
  }
}
