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

import java.util.Collection;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.io.Reader;
import java.io.IOException;

/**
 * Provides a Reader for reading the result of
 * gathering the sections of a Z specification into definition-before-use order
 * and moving mark-up directives to the beginnings of their sections.
 * Options are provided to retain (default elide) informal text,
 * and to buffer the whole spec in memory (default re-read sections from files).
 * 
 * @author ian
 */
public final class SpecReader extends Reader
{
  /** File types to be considered */
  public static final String[] SUFFICES = {".tex", ".zed"};
  
  /** Where toolkit sections are under resources */
  protected static final String RESOURCE_PREFIX = "/lib/";
  
  /** Whether buffering of whole spec's text is wanted */
  private boolean isBufferingWanted_;

  /** Whether informal narrative is retained or elided */
  private boolean isNarrativeWanted_;

  /** Sorted collection of gathered sections */
  private Collection<Section> sections_;

  /** Iterator over sections, if still more to be read, else null */
  private Iterator sectionIterator_;

  /** Text of section currently being read */
  private String sectionText_;

  /** Number of characters in the section being read */
  private int length_;

  /** Index of current character in section being read */
  private int currentPosition_;

  /**
   * Gathers the sections of a Z specification into definition-before-use order
   * and moves mark-up directives to the beginnings of their sections.
   * Prepares the Reader to read the text of those sections,
   * including opening the file and determining where the sections are.
   * 
   * @param fileName name of file to start from
   * @param isBufferingWanted whether to buffer whole spec's text in memory
   * @param isNarrativeWanted whether informal narrative is retained or elided
   * @throws CyclicSectionsException
   * @throws DupSectionNameException
   * @throws IllegalAnonSectionException
   * @throws IOException
   * @throws SectionNotFoundException
   */
  public SpecReader(String fileName, boolean isBufferingWanted, boolean isNarrativeWanted)
    throws CyclicSectionsException, DupSectionNameException, IllegalAnonSectionException,
    IOException, SectionNotFoundException
  {
    isBufferingWanted_ = isBufferingWanted;
    isNarrativeWanted_ = isNarrativeWanted;
    sections_ = gatherSections(new Pathname(fileName));
    sectionIterator_ = sections_.iterator();
    if (sectionIterator_.hasNext()) {
      nextSection();
    } else {
      sectionIterator_ = null;
    }
  }
 
  /**
   * Arranges for any subsequent read() to throw IOException.
   */
  @Override
  public void close()
  {
    sectionIterator_ = null;
  }

  /**
   * Reads characters into a portion of the given array.
   * 
   * @param cbuf destination buffer
   * @param off offset at which to start storing characters
   * @param len maximum number of characters to read
   * @return number of characters read, except -1 if already at end of file
   * @throws IOException if Reader has already been closed
   */
  @Override
  public int read(char[] cbuf, int off, int len)
    throws IOException
  {
    if (sectionIterator_ == null) {
      throw new IOException("read on closed SpecReader");
    }
    for (int count = 0; count < len; count++) {
      if (currentPosition_ == length_) {
        if (sectionIterator_.hasNext()) {
          nextSection();
        } else if (count > 0) {
          return count;
        } else {
          return -1;
        }
      }
      cbuf[off++] = sectionText_.charAt(currentPosition_++);
    }
    return len;
  }

  /**
   * Prepares the Reader to read the text of the next section.
   */
  private void nextSection()
  {
    Section section = (Section)(sectionIterator_.next());
    sectionText_ = section.toString();
    length_ = sectionText_.length();
    currentPosition_ = 0;
  }

  /**
   * Gathers the sections of a Z specification into definition-before-use order,
   * and moves mark-up directives to the beginnings of their sections.
   * 
   * @param filename name of file to start from
   * @throws CyclicSectionsException
   * @throws DupSectionNameException
   * @throws IllegalAnonSectionException
   * @throws IOException
   * @throws SectionNotFoundException
   */
  private List<Section> gatherSections(Pathname filename)
    throws CyclicSectionsException, DupSectionNameException, IllegalAnonSectionException,
    IOException, SectionNotFoundException
  {
    final Collection<Section> sections = readFiles(filename.basename(), filename.suffix());
    //System.err.format("Total #sections read: %d%n", sections.size());
    return orderSects(sections);
  }

  /**
   * Returns all the sections of a whole Z specification.
   * Reads files determined by the given specification name
   * and the names of ancestral sections (including prelude).
   * 
   * @param specName string naming the whole specification
   * @param suffix file type associated with <code>specName</code>, or ""
   * @return all sections that are part of the Z specification
   * @throws DupSectionNameException
   * @throws IllegalAnonSectionException
   * @throws IOException
   * @throws SectionNotFoundException
   */
  private Collection<Section> readFiles(String specName, String suffix)
    throws DupSectionNameException, IllegalAnonSectionException, IOException,
    SectionNotFoundException
  {
    final List<String> toBeRead = new LinkedList<String>();
    toBeRead.add(specName);
    if (! specName.equals("prelude")) {
      toBeRead.add("prelude");
    }
    final Map<String,Section> cache = new HashMap<String,Section>();
    while (! toBeRead.isEmpty()) {
      final String basename = toBeRead.remove(0);
      if (cache.get(basename) == null) {
        final String suff = basename.equals(specName)? suffix : "";
        final List<Section> sections = readFile(basename, suff);
        for (Section section : sections) {
          if (section instanceof ZSection) {
            HeaderBlock header = ((ZSection)section).getHeader();
            toBeRead.addAll(header.getParents());
            final String name = header.getName();
            final Section existingSection = cache.get(name);
            if (existingSection == null) {
              cache.put(name, section);
            } else {
              throw new DupSectionNameException("Multiple sections with same name " + name
                  + " in " + section.getPathname() + " and " + existingSection.getPathname());
            }
          } else if (section instanceof NarrSection) {
            cache.put(basename + "__Narrative", section);
          } else {
            throw new RuntimeException("Unknown section instance in readFiles()");
          }
        }
      }
    }
    return cache.values();
  }

  /**
   * Reads the file with the given name and returns the sections therein.
   * 
   * @param basename name of file to be read (without suffix)
   * @param suffix file type associated with <code>basename</code>, or ""
   * @return list of sections defined in that one file
   * @throws IllegalAnonSectionException
   * @throws IOException
   * @throws SectionNotFoundException
   */
  private List<Section> readFile(String basename, String suffix)
    throws IllegalAnonSectionException, IOException, SectionNotFoundException
  {
    //System.err.format("Reading %s%s%n", basename, SUFFICES[0]);
    final ZFileReader zFileReader = new ZFileReader(
        basename, suffix, isBufferingWanted_, isNarrativeWanted_);
    final List<Section> sections = zFileReader.readSections();
    //System.err.format("#sections read: %d%n", sections.size());
    return sections;
  }

  /**
   * Sorts the given sections into definition-before-use order.
   * 
   * @param sections collection of sections
   * @return sorted list of sections
   * @throws CyclicSectionsException
   */
  private List<Section> orderSects(Collection<Section> sections)
    throws CyclicSectionsException
  {
    final List<Section> result = new LinkedList<Section>();
    Section chosenSection = null;
    takeNarrSections(sections, result);
    takePrelude(sections, result);
    for (;;) {                               // Repeatedly choose one section
      chosenSection = null;
      for (Section section : sections) {     // from those yet to be sorted
        boolean pre = true;                  // whose parents have all already been sorted
        for (String parent : ((ZSection)section).getHeader().getParents()) {
          boolean found = false;
          for (Section s : result) {
            if (s instanceof ZSection && ((ZSection)s).getHeader().getName().equals(parent)) {
              found = true;
              break;
            }
          }
          if (! found) {
            pre = false;
            break;
          }
        }
        if (pre) {
          chosenSection = section;
          break;
        }
      }
      if (chosenSection == null) {
        break;                             // Either all chosen or cycle in parents relation
      }
      // Move the chosen section to the end of the result list.
      sections.remove(chosenSection);
      result.add(chosenSection);
    }
    if (! sections.isEmpty()) {
      StringBuilder stringBuilder = new StringBuilder("Sections are parents of each other:");
      for (Section s : sections) {
        stringBuilder.append(" ");
        stringBuilder.append(((ZSection)s).getHeader().getName());
      }
      throw new CyclicSectionsException(stringBuilder.toString());
    }
    return result;
  }

  /**
   * Moves section prelude from the sections collection to the result list.
   * 
   * @param sections collection of sections including prelude
   * @param result where to move section prelude to
   */
  private static void takePrelude(Collection<Section> sections, List<Section> result)
  {
    Section chosenSection = null;
    for (Section section : sections) {
      if (section instanceof ZSection
          && ((ZSection)section).getHeader().getName().equals("prelude")) {
        chosenSection = section;
        break;
      }
    }
    if (chosenSection != null) {
      // Move the prelude section to the result list.
      sections.remove(chosenSection);
      result.add(chosenSection);
    } else {
      throw new RuntimeException("Failure to find section prelude is an installation bug");
    }
  }

  /**
   * Moves all narrative sections from the sections collection to the result list.
   * 
   * @param sections collection of sections
   * @param result where to move narrative sections to
   */
  private static void takeNarrSections(Collection<Section> sections, List<Section> result)
  {
    for (;;) {
      Section chosenSection = null;
      for (Section section : sections) {
        if (section instanceof NarrSection) {
          chosenSection = section;
          break;
        }
      }
      if (chosenSection == null) {
        return;
      }
      // Move the chosen narrative section to the result list.
      sections.remove(chosenSection);
      result.add(chosenSection);
    }
  }
}
