/*
  Copyright (C) 2008 Ian Toyn
  This file is part of the czt project.

  The czt project contains free software; you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation; either version 2 of the License, or
  (at your option) any later version.

  The czt project is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with czt; if not, write to the Free Software
  Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 */

package net.sourceforge.czt.specreader;

import java.io.BufferedReader;
import java.io.IOException;

/**
 * Records the common fields of any section.
 * 
 * @author ian
 */
public abstract class Section
{
  /** Path to file from which section was read */
  private Pathname pathname_;

  /** Whether buffering of whole section's text is wanted */
  private boolean isBufferingWanted_;

  /** File for re-reading if in unbuffered mode */
  private BufferedReader inFile_;

  /** Current read position in inFile */
  private int offset_;

  /**
   * Constructs a section.
   * 
   * @param pathname path to file from which section was read
   * @param isBufferingWanted whether to buffer whole section's text in memory
   */
  public Section(Pathname pathname, boolean isBufferingWanted)
  {
    pathname_ = pathname;
    isBufferingWanted_ = isBufferingWanted;
    inFile_ = null;
  }

  /**
   * Projects the pathname field.
   * 
   * @return path to file from which section was read
   */
  protected Pathname getPathname()
  {
    return pathname_;
  }

  /**
   * Constructs a %%Zfile directive saying which file the section came from.
   * 
   * @return constructed %%Zfile directive
   */
  private String getFileDir()
  {
    return "%%Zfile " + pathname_.toString() + ZFileReader.NL;
  }

  /**
   * Arranges for file to be re-opened in case text wasn't buffered,
   * creates a StringBuilder, and writes a %%Zfile directive to it.
   * 
   * @return resulting StringBuilder
   */
  protected StringBuilder initializeWriter()
  {
    inFile_ = null;
    return new StringBuilder(getFileDir());
  }

  /**
   * Closes any file that was open for re-reading unbuffered text.
   */
  protected void finalizeWriter()
  {
    if (inFile_ != null) {
      try {
        inFile_.close();
      }
      catch (IOException e) {
        throw new RuntimeException("Unexpected IOException in finalizeWriter");
      }
    }
  }

  /**
   * Appends the text of the given block to the given StringBuilder.
   * If the text wasn't buffered, it is re-read from the file.
   * 
   * @param stringBuilder
   * @param block
   */
  protected void blockAppend(StringBuilder stringBuilder, Block block)
  {
    stringBuilder.append(block.getLocDir());
    if (isBufferingWanted_) {
      stringBuilder.append(block.toString());           // Append already buffered text
    } else {
      try {
        int charNo = block.getCharNo();
        int length = block.getLength();
        if (inFile_ == null || offset_ > charNo) {      // File not open or earlier in file
          if (inFile_ != null) {
            inFile_.close();
          }
          ZFile zFile = ZFileReader.openZFile(pathname_.basename(), pathname_.suffix(), this);
          inFile_ = zFile.getBufferedReader();
          offset_ = 0;
        }
        //System.err.format("blockAppend skip %d-%d%n", charNo, offset);
        inFile_.skip(charNo-offset_);                   // Move to right place in file
        offset_ = charNo;
        char[] text = new char[length];
        if (inFile_.read(text, 0, length) < 0) {        // Read in right amount of text
          throw new RuntimeException("Unexpected EOF in blockAppend");
        }
        offset_ += length;
        stringBuilder.append(text);                     // Apend re-read text
      }
      catch (IOException e) {
        throw new RuntimeException("Unexpected IOException in blockAppend");
      }
      catch (SectionNotFoundException e) {
        throw new RuntimeException("Unexpected SectionNotFoundException in blockAppend");
      }
    }
    if (!stringBuilder.substring(stringBuilder.length() - ZFileReader.NL.length()).equals(ZFileReader.NL)) {
      stringBuilder.append(ZFileReader.NL);
    }
  }
}
