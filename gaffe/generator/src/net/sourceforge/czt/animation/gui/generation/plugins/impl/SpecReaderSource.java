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

import java.io.BufferedReader;
import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.net.Authenticator;
import java.net.MalformedURLException;
import java.net.PasswordAuthentication;
import java.net.URL;
import java.net.URLConnection;

import net.sourceforge.czt.animation.gui.generation.BadOptionException;
import net.sourceforge.czt.animation.gui.generation.Option;
import net.sourceforge.czt.animation.gui.generation.OptionHandler;
import net.sourceforge.czt.animation.gui.generation.plugins.SpecSource;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.session.Source;
import net.sourceforge.czt.session.Dialect;
import net.sourceforge.czt.session.UrlSource;
import net.sourceforge.czt.z.ast.Spec;

/**
 * A plugin implementation for obtaining Z the specifications from a file, URL, or System.in.
 * @author Nicholas Daley
 */
public final class SpecReaderSource implements SpecSource
{

  private SectionManager sectman_ = new SectionManager(Dialect.Z);

  public SectionManager getSectionManager()
  {
    return sectman_;
  }

  public void setSectionManager(/*@non_null@*/SectionManager sectMan)
  {
    sectman_ = sectMan;
  }

  /**
   * {@inheritDoc}
   * Options for specifying where the specification is loaded from:
   * <ul>
   *   <li>-spec &lt;filename or URL&gt;</li>
   *   <li>-spec-file &lt;filename&gt;</li>
   *   <li>-spec-url &lt;URL&gt;</li>
   *   <li>-spec-stdin</li>
   * </ul>
   */
  public Option[] getOptions()
  {
    return new Option[]{
        new Option("spec", Option.MUST, "filename or URL",
            "File name or URL of the specification to use.", specHandler),
        new Option("spec-file", Option.MUST, "filename",
            "File name of the specification to use.", specFileHandler),
        new Option("spec-url", Option.MUST, "URL",
            "URL of the specification to use.", specURLHandler),
        new Option("spec-stdin", Option.MUSTNOT, null,
            "The specification to use will come from System.in.",
            specStdInHandler), new Option(doneHandler)};
  };

  /**
   * {@inheritDoc}
   */
  public String getHelp()
  {
    return "Obtains a Z specification from a file, URL, or standard input.";
  };

  /**
   * Option handler for <tt>-spec</tt>.
   * Tries to turn it into a URL, then as a file, if both fail it throws an Error.
   */
  private OptionHandler specHandler = new OptionHandler()
  {
    public void handleOption(Option opt, String argument)
        throws BadOptionException
    {
      try {
        url = new URL(argument);
      } catch (MalformedURLException ex) {
        file = new File(argument);
        if (!file.canRead())
          throw new BadOptionException(
              "The argument to -spec must be an existing readable file or a "
                  + "valid URL.");
      }
    };
  };

  /**
   * Option handler for <tt>-spec-file</tt>.
   * Tries to turn it into a file, if this fails it throws an Error.
   */
  private OptionHandler specFileHandler = new OptionHandler()
  {
    public void handleOption(Option opt, String argument)
        throws BadOptionException
    {
      file = new File(argument);
      if (!file.canRead())
        throw new BadOptionException(
            "The argument to -spec-file must be an existing readable file.");
    };
  };

  /**
   * Option handler for <tt>-spec-url</tt>.
   * Tries to turn it into a URL, if this fails it throws an Error.
   */
  private OptionHandler specURLHandler = new OptionHandler()
  {
    public void handleOption(Option opt, String argument)
        throws BadOptionException
    {
      try {
        url = new URL(argument);
      } catch (MalformedURLException ex) {
        throw new BadOptionException(
            "The argument to -spec-url must be a valid URL.");
      }
    };
  };

  /**
   * Option handler for <tt>-spec-stdin</tt>.
   * Sets the input stream to use to System.in.
   */
  private OptionHandler specStdInHandler = new OptionHandler()
  {
    public void handleOption(Option opt, String argument)
    {
      is = System.in;
    };
  };

  /**
   * Handler for the end of option processing.
   */
  private final OptionHandler doneHandler = new OptionHandler()
  {
    public void handleOption(Option opt, String argument)
        throws BadOptionException
    {
      if (is == null && file == null && url == null)
        throw new BadOptionException(
            "The SpecReaderSource needs an argument giving a location to "
                + "read from.");
    };
  };

  /**
   * The file to read from or null.
   */
  private File file = null;

  /**
   * The URL to read from or null.
   */
  private URL url = null;

  /**
   * The input stream to read from or null.
   */
  private InputStream is = null;

  /**
   * {@inheritDoc}
   * Opens the file/URL/input stream, turns its contents 
   * into a Z specification, then returns this specification.
   * For URL sources, it may prompt for username and password.
   * @czt.todo The username/password reader should probably be
   * moved into net.sourceforge.czt.session.UrlSource?
   */
  public Term obtainSpec() throws IllegalStateException, CommandException
  {
    URLConnection.setDefaultAllowUserInteraction(true);
    Authenticator.setDefault(new Authenticator()
    {
      protected PasswordAuthentication getPasswordAuthentication()
      {
        System.out.print("AUTHENTICATION");
        if (getRequestingHost() != null) {
          System.out.print(": " + getRequestingHost() + ":"
              + getRequestingPort());
        }
        System.out.println();
        System.out.println();
        System.out.println(getRequestingPrompt());

        BufferedReader authReader = new BufferedReader(new InputStreamReader(
            System.in), 1);

        String username;
        char[] password = new char[10];
        PasswordAuthentication pa;
        try {
          System.out.print("user name:");
          username = authReader.readLine();

          System.out.print("password (not starred out):");

          int cur;
          int i;
          cur = authReader.read();
          for (i = 0; cur >= 0 && cur != '\n' && cur != '\r'; i++) {
            if (i == password.length) {
              char[] newPassword = new char[2 * password.length];
              for (int j = 0; j < password.length; j++) {
                newPassword[j] = password[j];
                password[j] = 0;
              }
              password = newPassword;
            };
            password[i] = (char) cur;
            cur = authReader.read();
          }
          cur = 0;
          char[] newPassword = new char[i];
          for (int j = 0; j < i; j++) {
            newPassword[j] = password[j];
            password[j] = 0;
          }
          password = newPassword;
          pa = new PasswordAuthentication(username, password);
        } catch (IOException ex) {
          pa = null;
        }
        for (int j = 0; j < password.length; j++)
          password[j] = 0;
        return pa;
      };
    });
    URL finalurl = getURL();
    if (finalurl != null) {
      String name = finalurl.toString();
      sectman_.put(new Key(name, Source.class), new UrlSource(finalurl));
      return (Spec) sectman_.get(new Key<Spec>(name, Spec.class));
    }
    //catch(IOException ex) {
    //  throw new IllegalStateException("The SpecReaderSource could not read from the URL that was given.");
    else if (is != null) {
      //return reader.read(is);
      throw new IllegalStateException("The SpecReaderSource does not "
          + "implement standard input yet.");
    }
    else
      throw new Error("Should never reach this point in SpecReaderSource.");
  };

  /**
   * {@inheritDoc}
   * If it was loaded from a file, translates this into a URL.
   * If it was loaded from a URL, returns this.
   * Otherwise returns null.
   */
  public URL getURL()
  {
    if (file != null)
      try {
        return file.toURL();
      } catch (MalformedURLException ex) {
        return null;
      }
    else if (url != null)
      return url;
    else
      return null;
  };
};
