package net.sourceforge.czt.specreader;

import java.io.BufferedReader;

/**
 * Records the details to be returned by openZFile().
 * 
 * @author ian
 */
public final class ZFile
{
  /** Text of the pathname of the file chosen to be opened */
  private Pathname pathname_;

  /** Reader onto the opened file */
  private BufferedReader bufferedReader_;

  /**
   * Constructs a ZFile.
   * 
   * @param pathname text of this file's pathname
   * @param bufferedReader Reader onto this file.
   */
  public ZFile(Pathname pathname, BufferedReader bufferedReader)
  {
    pathname_ = pathname;
    bufferedReader_ = bufferedReader;
  }

  /**
   * Projects the pathname.
   * 
   * @return pathname
   */
  public Pathname getPathname()
  {
    return pathname_;
  }

  /**
   * Projects the Reader.
   * 
   * @return reader
   */
  public BufferedReader getBufferedReader()
  {
    return bufferedReader_;
  }
}
