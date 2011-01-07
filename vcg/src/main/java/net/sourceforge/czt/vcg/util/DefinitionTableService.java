/*
 * Copyright (C) 2011 Leo Freitas
 * This file is part of the CZT project.
 *
 * The CZT project contains free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * The CZT project is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with CZT; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 */

package net.sourceforge.czt.vcg.util;

import java.io.File;
import java.net.URISyntaxException;
import java.net.URL;
import java.util.Set;
import java.util.SortedSet;
import net.sourceforge.czt.session.Command;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.SectionInfo;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.util.CztException;
import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.z.ast.ZSect;
import net.sourceforge.czt.z.util.ZUtils;


/**
 * A visitor that computes a {@link DefinitionTable} from a given
 * Z Section.
 *
 * @author Leo Freitas
 */
public class DefinitionTableService
  implements Command
{
  SectionInfo sectInfo_;

  public DefinitionTableService()
  {
    sectInfo_ = null;
  }

  /**
   * Creates a new definition table service.
   * The section information should be able to provide information of
   * type <code>net.sourceforge.czt.parser.util.DefinitionTable.class</code>.
   * @param sectInfo
   */
  public DefinitionTableService(SectionInfo sectInfo)
  {
    sectInfo_ = sectInfo;
  }

  public static Class<?> getCommandInfoType()
  {
    return DefinitionTable.class;
  }

  public DefinitionTable run(ZSect sect)
    throws CommandException
  {
    return run(sect, sectInfo_);
  }

  public DefinitionTable run(ZSect sect, SectionInfo sectInfo)
    throws CommandException
  {
    DefinitionTableVisitor visitor = new DefinitionTableVisitor(sectInfo);
    return visitor.run(sect);
  }

  protected void updateManager(SectionManager manager,
          Key<ZSect> sectKey, Key<DefinitionTable> defTblKey,
          DefinitionTable table, Set<Key<?>> dependencies)
  {
    if (table != null)
    {
      dependencies.add(sectKey);
      manager.put(defTblKey, table, dependencies);
    }
  }

  /**
   * Computes the definition table for the given ZSect and all its parents.
   * In order to provide as much information as possible, it fails gracefully
   * by accumulating all raised exceptions to the end (top-most parent). It
   * also updates the manager with what was possible to calculate, despite the
   * errors. In the end, they are raised. It is up to the caller to fix the
   * section manager with a better table, if needed.
   * @param name
   * @param manager
   * @return
   * @throws CommandException
   */
  @Override
  public boolean compute(String name,
                         SectionManager manager)
    throws CommandException
  {
    DefinitionTableVisitor visitor = new DefinitionTableVisitor(manager);
    Key<ZSect> sectKey = new Key<ZSect>(name, ZSect.class);
    ZSect zsect = manager.get(sectKey);
    Key<DefinitionTable> defTblKey = new Key<DefinitionTable>(name, DefinitionTable.class);
    DefinitionTable table;
    // don't calculate if cached
    if (manager.isCached(defTblKey))
    {
      table = manager.get(defTblKey);
      return table != null;
    }
    else
    {
      // calculate table
      try
      {
        table = visitor.run(zsect);
        updateManager(manager, sectKey, defTblKey, table, visitor.getDependencies());
        return table != null;
      }
      catch(CommandException f)
      {
        // in case of raised definition exception, still update the manager
        // with calculated results, if they are available, before raising
        // the error. It is up to the caller to fix the manager.
        if (f instanceof DefinitionException)
        {
          updateManager(manager, sectKey, defTblKey, visitor.getDefinitionTable(), visitor.getDependencies());
        }
        // then throw it
        throw f;
      }
      catch(CztException e)
      {
        // catch visiting related exceptions. cmd exceptions must be handled by caller
        throw new CommandException("Could not calculate definition table for " + name +
          "\n\t with message " + e.getMessage() +
          (e.getCause() != null ? ("\n\t and cause " + e.getCause().getMessage()) : "") + ".", e);
      }
    }
  }

  static String removePath(String filename)
  {
    int barIdx = filename.lastIndexOf(java.io.File.separatorChar);
    if (barIdx == -1)
    {
      barIdx = filename.lastIndexOf("/");
    }
    if (barIdx == -1)
    {
      barIdx = filename.lastIndexOf("\\");
    }
    return barIdx == -1 ? filename : filename.substring(barIdx + 1);
  }

  static String getFileNameNoExt(String filename)
  {
    int dotIdx = filename.lastIndexOf(".");
    return dotIdx == -1 ? filename : filename.substring(0, dotIdx);
  }

  static String getSourceName(String filename)
  {
    // transforms c:\temp\myfile.tex into myfile
    String resource = removePath(getFileNameNoExt(filename));
    return resource;
  }

  public static Command getCommand()
  {
    return new DefinitionTableService();
  }

  public static Command getCommand(SectionInfo sectInfo)
  {
    return new DefinitionTableService(sectInfo);
  }

  public static void main(String args[]) throws URISyntaxException
  {
    SectionManager manager = new SectionManager();
    manager.putCommand(getCommandInfoType(), getCommand(manager));
    manager.setTracing(true);
    DefinitionTable table = null;
    java.io.File file = new java.io.File(args[0]);
    String sourceName = getSourceName(file.getName());
    manager.put(new Key<net.sourceforge.czt.session.Source>(sourceName, net.sourceforge.czt.session.Source.class),
            new net.sourceforge.czt.session.FileSource(file));
    Key<DefinitionTable> defTblKey = new Key<DefinitionTable>(sourceName, DefinitionTable.class);
    try
    {
      table = manager.get(defTblKey);
    }
    catch (CommandException ex)
    {
      handleCmdException(ex);
      // try a second time to see if the one with errors was cached
      try
      {
        table = manager.get(defTblKey);
      }
      catch (CommandException fx)
      {
        handleCmdException(fx);
      }
    }

    if (table != null)
    { 
      final String result = table.toString(false, true);
      System.out.println("\n");
      System.out.println(result);
      System.out.println();
      
      if (args.length > 1)
      {

        ZName arg = ZUtils.FACTORY.createZName(args[1]);
        assert table.lookupName(arg) != null;
        try
        {
          SortedSet<Definition> bindings = table.bindings(arg);
          final String result2 = bindings.toString().replaceAll(", ", ",\n");
          System.out.println("\n");
          System.out.println(result2);
          System.out.println();
        }
        catch (DefinitionException ex)
        {
          System.err.println("Could not retrive bindings for " + args[1]);
        }
      }
    }
/*
    URL url = table.getClass().getResource("/lib/");//dc_toolkit.tex");
    file = new File(url.toURI());
    System.out.println("url.file   = " + url.getFile());
    System.out.println("url.path   = " + url.getPath());
    System.out.println("url.extf   = " + url.toExternalForm());
    System.out.println("url.toStr  = " + url.toString());
    System.out.println("URI.toStr  = " + url.toURI());
    System.out.println("file.name  = " + file.getName());
    System.out.println("file.parent= " + file.getParent());
    System.out.println("file.path  = " + file.getPath());
    System.out.println("file.abspth= " + file.getAbsolutePath());
    System.out.println("file.tostr = " + file.toString());
 * 
 */

  }

  private static void handleCmdException(CommandException ex)
  {
    System.err.println("\n\n");
    System.err.println("--------------- ERRORS --------------------");
    if (ex instanceof DefinitionException)
    {
      printDefException((DefinitionException)ex);
    }
    else
    {
      printException(ex);
      ex.printStackTrace();
    }
    System.err.println("-------------------------------------------");
    System.err.println("\n\n");
  }

  private static void printException(CommandException e)
  {
    System.err.println(e.getMessage());
    if (e.getCause() != null)
      System.err.println(e.getCause().getMessage());
  }

  private static void printDefException(DefinitionException dex)
  {
    printException(dex);
    for(DefinitionException e : dex.getExceptions())
    {
      printException(e);
    }
  }
}
