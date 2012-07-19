/*
  Copyright (C) 2008 Ian Toyn
  This file is part of the czt project.

  This program is free software; you can redistribute it and/or
  modify it under the terms of the GNU General Public License
  as published by the Free Software Foundation; either version 2
  of the License, or (at your option) any later version.

  This program is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with this program; if not, write to the Free Software
  Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA  02111-1307, USA.
*/

package net.sourceforge.czt.specreader;

import static junit.framework.Assert.*;

import java.io.Reader;
import java.io.IOException;

public class SpecReaderTester
{
  public static void specReaderTester(String basename, Object testCase)
  {
    final int len = 65536;    // Enough to get entire input file from one call to read()
    final char[] cbuf_expected = new char[len];
    final char[] cbuf_actual = new char[len];
    int count_expected;
    int count_actual;
    try {
      ZFile zFile = ZFileReader.openZFile(basename + "_expected", SpecReader.SUFFICES[0], testCase);
      Reader reader = zFile.getBufferedReader();
      count_expected = reader.read(cbuf_expected, 0, len);
      if (count_expected < 1) {
        fail("read expected failed as if EOF");
      }
      final String string_expected = new String(cbuf_expected, 0, count_expected);
      try {
        // Set 'isBufferingWanted' to true, because the non-buffered implementation
        // has problems with Windows (CR+LF line endings).
        // See bug #3545808 for details.
        // 
        // The buffering prevents re-reading source file, which was causing problems due
        // to bad calculations of character positions involving different line endings.
        // (see net.sourceforge.czt.specreader.Section:116-136)
        SpecReader specReader = new SpecReader(basename + SpecReader.SUFFICES[0], true, false);
        count_actual = specReader.read(cbuf_actual, 0, len);
        if (count_actual < 1) {
          fail("read actual failed as if EOF");
        } else {
          assertEquals(string_expected, new String(cbuf_actual, 0, count_actual));
          assertEquals(count_expected, count_actual);
        }
      }
      catch (CyclicSectionsException e) {
        assertEquals(string_expected, e.toString());
      }
      catch (DupSectionNameException e) {
        assertEquals(string_expected, e.toString());
      }
      catch (IllegalAnonSectionException e) {
        assertEquals(string_expected, e.toString());
      }
      catch (IOException e) {
        fail("Unexpected IOException on reading actual result");
      }
      catch (SectionNotFoundException e) {
        assertEquals(string_expected, e.toString());
      }
    }
    catch (IOException e) {
      fail("Unexpected IOException on reading expected result");
    }
    catch (SectionNotFoundException e) {
      fail("Cannot open " + basename + "_expected" + SpecReader.SUFFICES[0]);
    }
  }
}
