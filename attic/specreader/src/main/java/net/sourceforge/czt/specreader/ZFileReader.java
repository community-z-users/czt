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
import java.io.EOFException;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.net.URL;
import java.util.LinkedList;
import java.util.List;

/**
 * Each object of this class reads one of the files of a Z specification.
 * The text of the file is parsed as a list of blocks,
 * which is then partitioned into a list of sections.
 * 
 * @author ian
 */
public final class ZFileReader
{
  /** System-specific newline separator (e.g. "\n" for Unix, "\r\n" for Windows.  */
  public static final String NL = System.getProperty("line.separator");

  /** Name of section being read */
  private String basename_;

  /** Path to file being read (optional resourcePrefix, <code>basename_</code> and a suffix) */
  private Pathname pathname_;

  /** Whether buffering of whole spec's text is wanted */
  private boolean isBufferingWanted_;

  /** Whether informal narrative is retained or elided. */
  private boolean isNarrativeWanted_;

  /** File being read from */
  private BufferedReader bufferedReader_;

  /** Complete blocks read so far.
   * This is kept in reverse order, to ease blocksToSections().
   */
  private List<Block> blocks_;

  /** Text consumed since end of last block */
  private StringBuilder text_;

  /** Whether <code>text</code> contains a formal Z paragraph */
  private boolean isFormal_;

  /** Line number where <code>text</code> started */
  private int firstLineNo_;

  /** Column number where <code>text</code> started */
  private int firstColumnNo_;

  /** Character number where <code>text</code> started */
  private int firstCharNo_;

  /** Current line */
  private String line_;

  /** Number of current line, counting from 1 */
  private int lineNo_;

  /** Number of first character in line, counting from 0 */
  private int charNo_;

  /** Read-ahead position in current line, indexing from 0 */
  private int peekedPosition_;

  /** Position in current line of last character consumed into <code>text</code> */
  private int consumedPosition_;

  /**
   * Constructs a new Z file reader, opening the file so that it is ready to be read.
   * 
   * @param basename name of file to be read, without suffix
   * @param suffix file type associated with <code>basename</code>, or ""
   * @param isBufferingWanted whether to buffer whole spec's text in memory
   * @param isNarrativeWanted whether informal narrative is retained or elided
   * @throws SectionNotFoundException
   */
  public ZFileReader(String basename, String suffix, boolean isBufferingWanted, boolean isNarrativeWanted)
    throws SectionNotFoundException
  {
    basename_ = basename;
    isBufferingWanted_ = isBufferingWanted;
    isNarrativeWanted_ = isNarrativeWanted;
    final ZFile zFile = openZFile(basename, suffix, this);
    bufferedReader_ = zFile.getBufferedReader();
    pathname_ = zFile.getPathname();
    blocks_ = new LinkedList<Block>();
    text_ = new StringBuilder("");
    isFormal_ = false;
    firstLineNo_ = 1;
    firstColumnNo_ = 1;
    firstCharNo_ = 0;
    line_ = "";
    lineNo_ = 0;
    charNo_ = -1;          // Compensates for apparent initial empty line
    peekedPosition_ = 0;
    consumedPosition_ = 0;
  }

  /**
   * Opens the file to be read.
   * Looks for the file first in the resources library of standard toolkit sections,
   * and then in the user's current directory.
   * TODO: maybe allow a search-path of multiple user's directories.
   * 
   * @param basename name of file to be read
   * @param suffix file type associated with <code>basename</code>, or ""
   * @param anyInMyJar
   * @return a Reader onto the opened file
   * @throws SectionNotFoundException
   */
  protected static ZFile openZFile(String basename, String suffix, Object anyInMyJar)
    throws SectionNotFoundException
  {
    Pathname pathname = null;
    InputStream inputStream;
    if (basename.startsWith(SpecReader.RESOURCE_PREFIX)) {  // Look only for a resource
      String urlName = basename + (suffix.isEmpty()? SpecReader.SUFFICES[0] : suffix);
      inputStream = openUrl(urlName, anyInMyJar);
      if (inputStream != null) {
        pathname = new Pathname(urlName);
      }
    } else {                                                // Look first for a resource
      String urlName = SpecReader.RESOURCE_PREFIX + basename
        + (suffix.isEmpty()? SpecReader.SUFFICES[0] : suffix);
      inputStream = openUrl(urlName, anyInMyJar);
      if (inputStream != null) {
        pathname = new Pathname(urlName);
      } else if (suffix.isEmpty()) {                        // Look for any suffixed file
        boolean openOk = false;
        for (String suff : SpecReader.SUFFICES) {
          final String filename = basename + suff;
          try {
            inputStream = new FileInputStream(filename);
          }
          catch (FileNotFoundException e) {
            continue;
          }
          openOk = true;
          pathname = new Pathname(filename);
          break;
        }
        if (! openOk) {
          throw new SectionNotFoundException("Cannot find section " + basename);
        }
      } else {                                              // Look for specific suffixed file
        final String filename = basename + suffix;
        try {
          inputStream = new FileInputStream(filename);
        }
        catch (FileNotFoundException e) {
          throw new SectionNotFoundException("Cannot open file " + filename);
        }
        pathname = new Pathname(filename);
      }
    }
    BufferedReader bufferedReader = new BufferedReader(new InputStreamReader(inputStream));
    return new ZFile(pathname, bufferedReader);
  }

    /**
     * Attempts to open the given URL.
     * 
     * @param urlName name of resource to be read
     * @param anyInMyJar
     * @return an InputStream onto the opened file, else null
     */
  private static InputStream openUrl(String urlName, Object anyInMyJar)
    {
      URL url = anyInMyJar.getClass().getResource(urlName);
      if (url == null) {
        return null;
      } else {
        try {
          return url.openStream();
        }
        catch (IOException e) {
          throw new RuntimeException("IOException on opening " + urlName);
        }
      }
    }
    
  /**
   * Reads from this file and returns a list of sections.
   * 
   * @return list of sections read from this file
   * @throws IllegalAnonSectionException if anon section followed by named section
   * @throws IOException
   */
  public List<Section> readSections()
    throws IllegalAnonSectionException, IOException
  {
    return blocksToSections(readBlocks());
  }

  /**
   * Partitions the given list of blocks into sections.
   * Gives the default header to an anonymous section
   * (<code>section Specification parents standard_toolkit</code>).
   * The given list is in reverse order, so another reversal is done.
   * 
   * @param blocks blocks to be partitioned, in reverse order
   * @return list of sections
   * @throws IllegalAnonSectionException if anon section followed by named section
   */
  private List<Section> blocksToSections(List<Block> blocks)
    throws IllegalAnonSectionException
  {
    final List<Section> sections = new LinkedList<Section>();
    LinkedList<ParaBlock> paraBlocks = new LinkedList<ParaBlock>();
    LinkedList<MarkupBlock> markupBlocks = new LinkedList<MarkupBlock>();
    for (Block block : blocks) {
      if (block instanceof ParaBlock) {
        paraBlocks.add(0, (ParaBlock)block);
      } else if (block instanceof MarkupBlock) {
        markupBlocks.add(0, (MarkupBlock)block);
      } else if (block instanceof HeaderBlock) {
        HeaderBlock header = (HeaderBlock)block;
        Section section = new ZSection(
            pathname_, isBufferingWanted_, header, markupBlocks, paraBlocks);
        sections.add(section);
        paraBlocks = new LinkedList<ParaBlock>();
        markupBlocks = new LinkedList<MarkupBlock>();
      } else {
        throw new RuntimeException("Unknown block instance in blocksToSections()");
      }
    }
    final Section section = anonSection(markupBlocks, paraBlocks, sections);
    if (section != null) {
      sections.add(section);
    }
    return sections;
  }

  /**
   * If the given blocks form an anonymous section
   * and there are no named sections in this file,
   * builds and returns that section, else returns null.
   * There is an anonymous section if any mark-up directives or
   * formal paragraphs appear before any explicit section header.
   * The anonymous section is given an explicit section header
   * (<code>section filename parents standard_toolkit</code>).
   * 
   * @param markupBlocks any mark-up directives preceding any explicit section header
   * @param paraBlocks any paragraphs preceding any explicit section header
   * @param sections any other sections from later in the file
   * @return the anonymous section, or null if there isn't one
   * @throws IllegalAnonSectionException
   */
  private Section anonSection(
      List<MarkupBlock> markupBlocks, List<ParaBlock> paraBlocks, List<Section> sections)
    throws IllegalAnonSectionException
  {
    boolean isFormal = ! markupBlocks.isEmpty();
    for (ParaBlock block : paraBlocks) {
      if (block instanceof FormalParaBlock) {
        isFormal = true;
      }
    }
    if (isFormal) {
      if (sections.isEmpty()) {
        final List<String> parents = new LinkedList<String>();
        parents.add("standard_toolkit");
        final HeaderBlock header = new HeaderBlock(
            new StringBuilder(), isBufferingWanted_, 0, 0, 0, basename_, parents);
        return new ZSection(pathname_, isBufferingWanted_, header, markupBlocks, paraBlocks);
      } else {
        throw new IllegalAnonSectionException(
            "Formal text should not precede named section in " + pathname_);
      }
    } else if (isNarrativeWanted_ && ! paraBlocks.isEmpty()) {
      return new NarrSection(
          pathname_, isBufferingWanted_, (InformalParaBlock)paraBlocks.get(0));
    } else {
      return (null);
    }
  }

  /**
   * Reads words from this file, parses, and returns a list of blocks.
   * 
   * @return list of blocks corresponding to contents of file
   * @throws IOException
   */
  private List<Block> readBlocks()
    throws IOException
  {
    try {
      while (true) {                 // Read word-sized units, looking for section headers
        String word = peekWord();
        if (! word.equals("\\begin{zsection}")) {
          if (isBeginFormal(word)) {
            consumeParaBlock();      // informal text excluding \begin{...}
            isFormal_ = true;
          }
          consumeText();
          if (isEndFormal(word)) {
            peekChar();              // If at EOL, take the newline too
            consumeParaBlock();      // formal text including \end{...}
          }
        } else {
          consumeParaBlock();
          String name = "unknown";
          final List<String> parents = new LinkedList<String>();
          if (peekWordBeyondSpace().equals("\\SECTION")) {
            name = peekWordBeyondSpace().replaceAll("\\\\_", "_");
            if (peekWordBeyondSpace().equals("\\parents")) {
              word = peekWordBeyondSpace();
              while (true) {
                if (word.equals("\\end{zsection}")) {
                  break;
                }
                parents.add(word.replaceAll("\\\\_", "_"));
                word = peekWordBeyondSpace();
                if (! word.equals(",")) {
                  break;
                }
                word = peekWordBeyondSpace();
              }
            }
          }
          consumeText();
          consumeHeaderBlock(name, parents);
        }
      }
    } catch (EOFException e) {
      consumeParaBlock();
      bufferedReader_.close();
      return blocks_;
    }
  }

  /**
   * Reads ahead to the next non-space LaTeX word and returns that word.
   * 
   * @return string of next non-space LaTeX word
   * @throws EOFException
   * @throws IOException
   */
  private String peekWordBeyondSpace()
    throws EOFException, IOException
  {
    String word;
    while (true) {
      word = peekWord();
      if (word.equals("~")
          || word.equals("\\,")
          || word.equals("\\ ")
          || word.equals("\\:")
          || word.equals("\\;")
          || word.equals("\\\\")
          || word.equals("\\t")
          || word.equals("\\also")
          || word.equals("\\znewpage")) {
        continue;
      } else {
        //System.err.format("peekWordBeyondSpace=%s%n", word);
        return word;
      }
    }
  }

  /**
   * Reads ahead to the next LaTeX word and returns that word.
   * 
   * @return string of next LaTeX word
   * @throws EOFException
   * @throws IOException
   */
  private String peekWord()
    throws EOFException, IOException
  {
    char ch;
    while ((ch = peekChar()) == ' ' || ch == '\t') {
      peekedPosition_++;
    }
    final int startp = peekedPosition_;
    if (Character.isLetter(ch)) {
      peekAlphabeticWord();
    } else if (Character.isDigit(ch)) {
      while (Character.isDigit(peekCharOrEol())) {
        peekedPosition_++;
      }
    } else if (ch != '\\') {
      peekedPosition_++;
    } else {
      return peekCommandWord();
    }
    //System.err.format("peekWord returns %s\n", line.substring(startp, cp));
    return line_.substring(startp, peekedPosition_);
  }

  /**
   * Reads ahead over an alphabetic word.
   * 
   * @throws IOException
   */
  private void peekAlphabeticWord()
    throws IOException
  {
    for (;;) {
      char ch = peekCharOrEol();
      if (ch == '\\') {
        peekedPosition_++;
        ch = peekCharOrEol();
        if (ch != '_') {
          peekedPosition_--;
          break;
        }
      } else if (! Character.isLetterOrDigit(ch)) {
        break;
      }
      peekedPosition_++;
    }
  }

  /**
   * Reads ahead over a LaTeX command word and returns that word.
   * In the case of "\begin", also includes the {environment} name.
   * 
   * @return string of LaTeX command word
   * @throws IOException
   */
  private String peekCommandWord()
    throws IOException
  {
    int startp = peekedPosition_;
    peekedPosition_++;
    if (! Character.isLetter(peekChar())) {
      peekedPosition_++;
    } else {
      while (Character.isLetter(peekCharOrEol())) {
        peekedPosition_++;
      }
      String word = line_.substring(startp, peekedPosition_);
      if (! word.equals("\\begin") && ! word.equals("\\end")) {
        //System.err.format("peekWord returns %s\n", word);
        return word;
      } else {
        char ch;
        while ((ch = peekChar()) == ' ' || ch == '\t') {
          peekedPosition_++;
        }
        startp = peekedPosition_;
        if (ch == '{') {
          peekedPosition_++;
          while (Character.isLetter(peekCharOrEol())) {
            peekedPosition_++;
          }
          if (peekChar() == '}') {
            peekedPosition_++;
          }
        }
        //System.err.format("peekWord returns %s\n", word + line.substring(startp, cp));
        return word + line_.substring(startp, peekedPosition_);
      }
    }
    return line_.substring(startp, peekedPosition_);
  }

  /**
   * Reads ahead to the next character and returns that character.
   * Elides LaTeX %comments.
   * At end of line, inserts <code>'\n'</code>.
   * Suitable for use while reading a word.
   * 
   * @return next character
   * @throws EOFException
   * @throws IOException
   * @see #peekChar()
   */
  private char peekCharOrEol()
    throws EOFException, IOException
  {
    if (peekedPosition_ >= line_.length()
        || line_.charAt(peekedPosition_) == '%'
          && (peekedPosition_ > 0 || line_.charAt(peekedPosition_ - 1) != '\\')) {
      return '\n';
    }
    return line_.charAt(peekedPosition_);
  }

  /**
   * Reads ahead to the next character and returns that character.
   * Elides LaTeX %comments.
   * At end of line, reads on to the next line.
   * Suitable for use while skipping soft space before the next word.
   * 
   * @return next character
   * @throws EOFException
   * @throws IOException
   * @see #peekCharOrEol()
   */
  private char peekChar()
    throws EOFException, IOException
  {
    while (peekedPosition_ >= line_.length()
        || line_.charAt(peekedPosition_) == '%'
          && (peekedPosition_ == 0 || line_.charAt(peekedPosition_ - 1) != '\\')) {
      peekedPosition_ = line_.length();
      nextLine();
    }
    return line_.charAt(peekedPosition_);
  }

  /**
   * Buffers the next line from the file, handling mark-up directives.
   * Puts each mark-up directive into a separate <code>MarkupBlock</code>.
   * 
   * @throws EOFException
   * @throws IOException
   */
  private void nextLine()
    throws EOFException, IOException
  {
    //System.err.format("nextLine\n");
    consumeText();
    while (true) {
      //System.out.format("nextline charNo %d + %d%n", charNo, line.length());
      charNo_ += line_.length() + 1;
      if ((line_ = bufferedReader_.readLine()) == null) {
        throw new EOFException("ZFileReader finishing");
      }
      //System.err.format("nextLine %s", line);
      lineNo_++;
      peekedPosition_ = 0;
      consumedPosition_ = 0;
      if (isMarkupDirective()) {
        consumeParaBlock();
        peekedPosition_ = line_.length();
        consumeText();
        consumeMarkupBlock();
      } else if (line_.length() == 0) {
        text_.append(NL);
      } else {
        return;
      }
    }
  }

  /**
   * Decides whether the current line is a mark-up directive.
   * 
   * @return whether <code>line</code> contains a mark-up directive
   */
  private boolean isMarkupDirective()
  {
    return line_.startsWith("%%Z")
    && (line_.startsWith("%%Zchar")
        || line_.startsWith("%%Zprechar")
        || line_.startsWith("%%Zinchar")
        || line_.startsWith("%%Zpostchar")
        || line_.startsWith("%%Zword")
        || line_.startsWith("%%Zpreword")
        || line_.startsWith("%%Zinword")
        || line_.startsWith("%%Zpostword"));
  }

  /**
   * Decides whether a LaTeX word starts a formal Z paragraph.
   * 
   * @param word string of a LaTeX word
   * @return whether <code>word</code> starts a formal Z paragraph
   */
  private static boolean isBeginFormal(String word)
  {
    return word.startsWith("\\begin{")
    && (word.equals("\\begin{zed}")
        || word.equals("\\begin{axdef}")
        || word.equals("\\begin{gendef}")
        || word.equals("\\begin{schema}")
        || word.equals("\\begin{theorem}"));
  }

  /**
   * Decides whether a LaTeX word ends the current formal Z paragraph.
   * 
   * @param word string of a LaTeX word
   * @return whether <code>word</code> matches the \begin{env} already in <code>text</code>
   */
  private boolean isEndFormal(String word)
  {
    if (! isFormal_ || ! word.startsWith("\\end{")) {
      return false;
    }
    String rest = word.substring(5);                            // 5 = "\end{".length()
    return rest.equals(text_.substring(7, 7 + rest.length()));  // 7 = "\begin{".length()
  }

  /**
   * Copies the read-ahead words into the consumed text buffer.
   * Appends a newline character at the end of a line.
   */
  private void consumeText()
  {
    //System.err.format("consumeText '%s'\n", line.substring(lastcp, cp));
    if (consumedPosition_ != peekedPosition_) {
      text_.append(line_.substring(consumedPosition_, peekedPosition_));
      consumedPosition_ = peekedPosition_;
      if (peekedPosition_ == line_.length()) {
        text_.append(NL);
      }
    }
  }

  /**
   * Moves the consumed text into a new mark-up block.
   */
  private void consumeMarkupBlock()
  {
    blocks_.add(0, new MarkupBlock(text_, isBufferingWanted_, lineNo_, firstCharNo_));
    //System.err.format("MarkupBlock: %s", text);
    startNewText();
    /* Next block starts at beginning of next line. */
    firstLineNo_ = lineNo_ + 1;
    firstColumnNo_ = 1;
    firstCharNo_ = charNo_ + line_.length() + 1;
  }

  /**
   * Moves the consumed text into a new header block.
   * 
   * @param name name of section
   * @param parents names of section's parents
   */
  private void consumeHeaderBlock(String name, List<String> parents)
  {
    blocks_.add(0, new HeaderBlock(
        text_, isBufferingWanted_, firstLineNo_, firstColumnNo_, firstCharNo_, name, parents));
    //System.err.format("HeaderBlock: %s", text);
    startNewText();
    /* Next block starts where Header block left off. */
    firstLineNo_ = lineNo_;
    firstColumnNo_ = consumedPosition_ + 1;
    firstCharNo_ = charNo_ + consumedPosition_;
  }

  /**
   * Moves any consumed text into a new paragraph block.
   * Unwanted informal narrative is elided.
   */
  private void consumeParaBlock()
  {
    if (text_.length() != 0) {
      if (isFormal_) {
        blocks_.add(0, new FormalParaBlock(
            text_, isBufferingWanted_, firstLineNo_, firstColumnNo_, firstCharNo_));
      } else if (isNarrativeWanted_) {
        blocks_.add(0, new InformalParaBlock(
            text_, isBufferingWanted_, firstLineNo_, firstColumnNo_, firstCharNo_));
      }
      //System.err.format("ParaBlock (isFormal=%s): %s", isFormal? "true" : "false", text);
      startNewText();
      /* Next block starts where Para block left off. */
      firstLineNo_ = lineNo_;
      firstColumnNo_ = consumedPosition_ + 1;
      firstCharNo_ = charNo_ + consumedPosition_;
    }
  }

  /**
   * Prepares for reading of the next block.
   * Empties the consumed text buffer,
   * and notes that no formal Z paragraphs have been seen yet.
   */
  private void startNewText()
  {
    text_ = new StringBuilder("");
    isFormal_ = false;
  }
}
