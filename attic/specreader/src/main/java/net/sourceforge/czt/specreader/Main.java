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

import java.io.IOException;

/**
 * Reads a whole Z specification from a SpecReader and writes it to System.out.
 * 
 * @author ian
 */
public final class Main
{
  /**
   * Reads a whole Z specification from a SpecReader and writes it to System.out.
   * <DL><DT><B>Description:</B>
   * <DD>Parses command-line arguments to determine what is to be done,
   * does it,
   * and writes the result to System.out.
   * <DT><B>Options:</B>
   * <DD><CODE>-b</CODE> buffers the whole spec's text in memory, else files are read more than once
   * <DD><CODE>-i</CODE> retains informal text, else that is elided
   * <DT><B>Exit status:</B>
   * <DD><CODE>0</CODE> if all succeeded
   * <DD><CODE>1</CODE> if any mistakes detected
   * <DD><CODE>2</CODE> if assertion failed
   * </DL>
   * 
   * @param args should be [-[bi]] filename.tex
   */
  public static void main(String[] args)
  {
    boolean isNarrativeWanted = false;
    boolean isBufferingWanted = false;
    String fileName = null;

    for (String arg : args) {
      if (arg.charAt(0) == '-') {
        for (int j = 1; j < arg.length(); j++) {
          switch (arg.charAt(j)) {
            case 'b':
              isBufferingWanted = true;
              break;
            case 'i':
              isNarrativeWanted = true;
              break;
            default: {
              printUsage();
              System.exit(1);
            }
          }
        }
      } else if (fileName == null) {
        boolean suffixOk = false;
        for (String suffix : SpecReader.SUFFICES) {
          if (arg.endsWith(suffix)) {
            suffixOk = true;
          }
        }
        if (suffixOk) {
          fileName = arg;
        } else {
          printUsage();
          System.exit(1);
        }
      } else {
        printUsage();
        System.exit(1);
      }
    }

    try {
      final SpecReader specReader = new SpecReader(
          fileName, isBufferingWanted, isNarrativeWanted);
      final int len = 4096;
      char[] cbuf = new char[len];
      int count;
      while ((count = specReader.read(cbuf, 0, len)) > 0) {
        System.out.print(new String(cbuf, 0, count));
      }
    }
    catch (CyclicSectionsException e) {
      System.err.print(e.toString());
      System.exit(1);
    }
    catch (DupSectionNameException e) {
      System.err.print(e.toString());
      System.exit(1);
    }
    catch (IllegalAnonSectionException e) {
      System.err.print(e.toString());
      System.exit(1);
    }
    catch (IOException e) {
      System.err.print(e.toString());
      System.exit(1);
    }
    catch (RuntimeException e) {
      System.err.print(e.toString());
      System.exit(2);
    }
    catch (SectionNotFoundException e) {
      System.err.print(e.toString());
      System.exit(1);
    }
    System.exit(0);
  }

  /**
   * Writes a message to System.err explaining command-line arguments.
   */
  private static void printUsage()
  {
    System.err.println("usage: java specreader [-b] [-i] filename.tex");
    System.err.println("where -b buffers whole spec's text in memory");
    System.err.println("  and -i includes informal narrative in output");
  }
}
