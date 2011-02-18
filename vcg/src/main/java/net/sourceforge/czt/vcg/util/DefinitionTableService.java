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
import java.util.Set;
import java.util.SortedSet;
import net.sourceforge.czt.session.Command;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.SectionInfo;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.session.SourceLocator;
import net.sourceforge.czt.util.CztException;
import net.sourceforge.czt.z.ast.SectTypeEnvAnn;
import net.sourceforge.czt.z.ast.Spec;
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
    long startTime = System.nanoTime();
    DefinitionTableVisitor.DEFAULT_DEBUG_DEFTBL_VISITOR = true;
    SectionManager manager = new SectionManager();
    manager.putCommand(getCommandInfoType(), getCommand(manager));
    manager.setTracing(false);
    DefinitionTable table = null;
    File file = new File(args[0]);
    String sourceName = SourceLocator.getSourceName(file.getName());
    SourceLocator.addCZTPathFor(file, manager);
    manager.put(new Key<net.sourceforge.czt.session.Source>(sourceName, net.sourceforge.czt.session.Source.class),
            new net.sourceforge.czt.session.FileSource(file));
    Key<Spec> specKey = new Key<Spec>(sourceName, Spec.class);
    Key<SectTypeEnvAnn> typeKey = new Key<SectTypeEnvAnn>(sourceName, SectTypeEnvAnn.class);
    Key<DefinitionTable> defTblKey = new Key<DefinitionTable>(sourceName, DefinitionTable.class);
    long setupTime = System.nanoTime();
    boolean exceptionThrown = false;
    try
    {
      manager.get(specKey);
    }
    catch(CommandException ex)
    {
      System.out.println("Parsing errors!");
    }
    long parseTime = System.nanoTime();
    try
    {
      manager.get(typeKey);
    }
    catch(CommandException ex)
    {
      System.out.println("Typechecking errors!");
    }
    long typeTime = System.nanoTime();
    try
    {
      table = manager.get(defTblKey);
    }
    catch (CommandException ex)
    {
      handleCmdException(ex);
      //exceptionThrown = true;
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
    long defTblTime = System.nanoTime();
    long dtCons = 0, dtOther = 0, dtBinding = 0;
    if (table != null)
    {
      DefinitionException consistency = table.checkOverallConsistency();
      dtCons = System.nanoTime();

      if (!exceptionThrown)
      {

//        final String result = table.toString(false, true);
//        System.out.println("\n------------------------------- DEFTABLE -------------------------------");
//        System.out.println(result);
//        System.out.println();

        Set<Definition> defs = table.lookupDefinitions(sourceName);
        System.out.println("\n------------------------------- SCHREFS --------------------------------");
        for(Definition d : defs)
        {
          if (d.getDefinitionKind().isSchemaReference())
          {
            System.out.println(d.toString());
          }
        }
        dtOther = System.nanoTime();
        if (args.length > 1)
        {
          ZName arg = ZUtils.FACTORY.createZName(args[1]);
          System.out.println("\n------------------------------- BINDINGS -------------------------------");
          Definition def = table.lookupName(arg);
          if (def == null)
          {
            System.out.println("Could not find bindings for " + arg);
          }
          else
          {
            try
            {
              SortedSet<Definition> bindings = table.bindings(arg);
              dtBinding = System.nanoTime() - dtOther;
              final String result2 = bindings.toString().replaceAll(", ", ",\n");
              System.out.println("Bindings for " + args[1] + " = " + bindings.size());
              System.out.println(result2);
            }
            catch (DefinitionException ex)
            {
              System.err.println("Could not retrive bindings for " + args[1]);
            }
            System.out.println("\n-------------- of Def -------------");
            System.out.println(def.toString());
          }
          System.out.println("\n------------------------------------------------------------------------");
          System.out.println();
        }
      }
      else
      {
        dtOther = System.nanoTime();
        dtBinding = System.nanoTime();
      }
      System.out.println("CONSISTENCY-CHECK = " + (consistency == null ? " okay! " : " has " + (consistency.totalNumberOfErrors()-1) + " errors"));
      System.out.println(consistency == null ? "" : consistency.getMessage(true));
    }
    long finishTime = System.nanoTime();
    long nano2msec = 1000000;
    System.out.println("\n------------------------------------------------------------------------");
    System.out.println("START-TIME = " + startTime / nano2msec);
    System.out.println("SETUP-TIME = " + (setupTime / nano2msec) + "\t " + ((setupTime-startTime)/nano2msec));
    System.out.println("PARSE-TIME = " + (parseTime / nano2msec) + "\t " + ((parseTime-setupTime)/nano2msec));
    System.out.println("TYPEC-TIME = " + (typeTime / nano2msec) + "\t " + ((typeTime-parseTime)/nano2msec));
    System.out.println("DEFTB-TIME = " + (defTblTime / nano2msec) + "\t " + ((defTblTime-typeTime)/nano2msec));
    System.out.println("DTCON-TIME = " + (dtCons / nano2msec) + "\t " + ((dtCons-defTblTime)/nano2msec));
    System.out.println("DTOTH-TIME = " + (dtOther / nano2msec) + "\t " + ((dtOther-dtCons)/nano2msec));
    System.out.println("DTBIN-TIME = " + (dtBinding / nano2msec) + "\t " + ((dtBinding-dtOther)/nano2msec));
    System.out.println("TOTAL-TIME = " + (finishTime / nano2msec) + "\t " + ((finishTime-startTime)/nano2msec));
    System.out.println();

//    DefinitionException c =
//      new DefinitionException("a",
//        Arrays.asList(new DefinitionException("a.b",
//            Arrays.asList(new DefinitionException("a.b.1"),
//                          new DefinitionException("a.b.2",
//                            Arrays.asList(new DefinitionException("a.b.2.1"))))),
//                      new DefinitionException("a.c",
//                        Arrays.asList(new DefinitionException("a.c.1"))),
//                      new DefinitionException("a.d")));
//    System.out.println("c = " + c.getMessage());
//    System.out.println("c = " + c.totalNumberOfErrors());
//    System.out.println("c = transitive list with " + c.getTransitiveExceptions().size());
//    Iterator<DefinitionException> it = c.getTransitiveExceptions().iterator();
//    while (it.hasNext())
//      System.out.println("c = " + it.next().getMessage(false));
      
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
    System.err.println("-------------------------------------------");
    System.err.println("TOTAL = " + dex.totalNumberOfErrors());
  }
}
