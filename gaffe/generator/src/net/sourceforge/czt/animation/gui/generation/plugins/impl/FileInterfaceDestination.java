/*
 GAfFE - A (G)raphical (A)nimator (F)ront(E)nd for Z - Part of the CZT Project.
 Copyright 2003 Nicholas Daley
 
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

package net.sourceforge.czt.animation.gui.generation.plugins.impl;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.OutputStream;
import java.net.URL;

import net.sourceforge.czt.animation.gui.generation.BadOptionException;
import net.sourceforge.czt.animation.gui.generation.Option;
import net.sourceforge.czt.animation.gui.generation.OptionHandler;
import net.sourceforge.czt.animation.gui.generation.plugins.InterfaceDestination;

/**
 * Plugin implementation for selecting where to write the generated GUI to.
 * @author Nicholas Daley
 */
public final class FileInterfaceDestination implements InterfaceDestination
{
  /**
   * {@inheritDoc}
   * Arguments for writing the interface to a filem or to System.out.
   * <ul>
   *   <li>-destination &lt;filename&gt;</li>
   *   <li>-destination-stdout</li>
   * </ul>
   */
  public Option[] getOptions()
  {
    return new Option[]{
        new Option("destination", Option.MUST, "filename",
            "File to write the interface to.", destHandler),
        new Option("destination-stdout", Option.MUSTNOT, null,
            "The interface will be written to System.out.", destStdOutHandler)};
  };

  /**
   * {@inheritDoc}
   */
  public String getHelp()
  {
    return "Selects a location to write the interface to.";
  };

  /**
   * Option handler for <tt>-destination</tt>.
   * Finds the file to write to, and checks that it can be written to.
   */
  private OptionHandler destHandler = new OptionHandler()
  {
    public void handleOption(Option opt, String argument)
        throws BadOptionException
    {
      file = new File(argument);
      if (!file.canWrite() && file.exists())
        throw new BadOptionException(
            "The argument to -dest must be a file location that can be "
                + "written to.");
    };
  };

  /**
   * Option handler for <tt>-destination-stdout</tt>.
   * Sets the output stream to use to System.out.
   */
  private OptionHandler destStdOutHandler = new OptionHandler()
  {
    public void handleOption(Option opt, String argument)
    {
      os = System.out;
    };
  };

  /**
   * The file to write to, or null.
   */
  private File file = null;

  /**
   * The output stream to use, or null.
   */
  private OutputStream os = null;

  /**
   * {@inheritDoc}
   * Opens the file specified by <tt>-destination</tt>,
   * or returns System.out (if <tt>-destination-stdout</tt> was specified),
   * or tries to create a file based on the filename part of the URL supplied by the SpecSource plugin,
   * or fails (throwing <tt>IllegalStateException</tt>).
   */
  public OutputStream obtainOutputStream(URL inputURL)
      throws IllegalStateException
  {
    if (os != null)
      return os;
    if (file == null && inputURL != null
        && inputURL.getProtocol().equals("file")) {
      File inputFile = new File(inputURL.getPath());
      if (inputFile.getName().endsWith(".zml")
          || inputFile.getName().endsWith(".xml"))
        file = new File(inputFile.getName().substring(0,
            inputFile.getName().lastIndexOf("."))
            + ".gaffe");
    }
    if (file != null)
      try {
        return new FileOutputStream(file);
      } catch (FileNotFoundException ex) {
        throw new IllegalStateException(
            "The FileInterfaceDestination couldn't write to the file given to "
                + "it (" + file + ").");
      }
    else
      throw new IllegalStateException(
          "The FileInterfaceDestination needs an argument giving a location to "
              + "write to.");
  };
};
