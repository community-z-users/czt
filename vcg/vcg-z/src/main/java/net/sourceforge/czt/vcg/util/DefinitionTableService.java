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
import net.sourceforge.czt.session.Dialect;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.SectionInfo;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.session.SourceLocator;
import net.sourceforge.czt.typecheck.z.TypecheckPropertiesKeys;
import net.sourceforge.czt.util.CztException;
import net.sourceforge.czt.vcg.z.VCGPropertyKeys;
import net.sourceforge.czt.z.ast.SectTypeEnvAnn;
import net.sourceforge.czt.z.ast.Spec;
import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.z.ast.ZSect;
import net.sourceforge.czt.z.util.WarningManager.WarningOutput;
import net.sourceforge.czt.z.util.ZUtils;


/**
 * A visitor that computes a {@link DefinitionTable} from a given
 * Z Section.
 *
 * @author Leo Freitas
 */
public class DefinitionTableService
  implements Command, VCGPropertyKeys
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
          Key<ZSect> sectKey, Key<DefinitionTable> defTblKey, DefinitionTable table)
  {
    if (table != null)
    {
      // table calculated successfully - end transaction to capture the dependencies implicitly
      manager.endTransaction(defTblKey, table);
    } else {
      // could not calculate - cancel the transaction
      manager.cancelTransaction(defTblKey);
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
    Key<ZSect> sectKey = new Key<ZSect>(name, ZSect.class);
    ZSect zsect = manager.get(sectKey);
    Key<DefinitionTable> defTblKey = new Key<DefinitionTable>(name, DefinitionTable.class);
    DefinitionTable table;
    
    // the definition table cannot be cached - parsing does not calculate the definition table
    
    DefinitionTableVisitor visitor = new DefinitionTableVisitor(manager);
    // calculate table
    try
    {
      table = visitor.run(zsect);
      updateManager(manager, sectKey, defTblKey, table);
      return table != null;
    }
    catch(CommandException f)
    {
      // in case of raised definition exception, still update the manager
      // with calculated results, if they are available, before raising
      // the error. It is up to the caller to fix the manager.
      if (f instanceof DefinitionException)
      {
        updateManager(manager, sectKey, defTblKey, visitor.getDefinitionTable());
      }
      // then throw it
      throw f;
    }
    catch(CztException e)
    {
      // catch visiting related exceptions. cmd exceptions must be handled by caller
      throw new CommandException(manager.getDialect(), "Could not calculate definition table for " + name +
        "\n\t with message " + e.getMessage() +
        (e.getCause() != null ? ("\n\t and cause " + e.getCause().getMessage()) : "") + ".", e);
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

    String fileName = null;
    Dialect extension = SectionManager.DEFAULT_EXTENSION;
    boolean debug = false;
    boolean printSchRefs = false;
    boolean hideWarnings = false;
    boolean checkDefTblConsistency = false;
    int fileArgIndex = 0;
    for (int i = 0; i < args.length && fileName == null; i++, fileArgIndex++)
    {
      if ("-y".equals(args[i]))
      {
        checkDefTblConsistency = true;
      }
      else if ("-h".equals(args[i]))
      {
        hideWarnings = true;
      }
      else if ("-p".equals(args[i]))
      {
        printSchRefs = true;
      }
      else if ("--debug".equals(args[i]))
      {
        debug = true;
      }
      else if (args[i].startsWith("-e"))
      {
        final String ext = args[i].substring(2).toUpperCase();
        try
        {
          extension = Dialect.valueOf(ext);
        }
        catch (IllegalArgumentException e)
        {
          System.err.println("Unknown CZT extension " + ext);
          System.exit(-1);
        }
      }
      else if (args[i].startsWith("-"))
      {
        System.err.println("Ignoring unknown argument " + args[i]);
      }
      else
      {
        fileName = args[i];
        System.out.println("Processing " + fileName);
      }
    }
    assert fileName != null;
    System.out.println();

    SectionManager manager = new SectionManager(extension);
    manager.setProperty(PROP_VCG_RAISE_TYPE_WARNINGS, String.valueOf(false));
    manager.setProperty(PROP_VCG_CHECK_DEFTBL_CONSISTENCY, String.valueOf(checkDefTblConsistency));
    manager.setProperty(TypecheckPropertiesKeys.PROP_TYPECHECK_WARNINGS_OUTPUT, String.valueOf(hideWarnings ? WarningOutput.HIDE : WarningOutput.SHOW));
    manager.setTracing(debug);
    manager.putCommand(getCommandInfoType(), getCommand(manager));
    DefinitionTable table = null;
    File file = new File(fileName);
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
      handleCmdException(ex, -2);
    }
    long parseTime = System.nanoTime();
    try
    {
      manager.get(typeKey);
    }
    catch(CommandException ex)
    {
      System.out.println("Typechecking errors!");
      handleCmdException(ex, -3);
    }
    long typeTime = System.nanoTime();
    try
    {
      table = manager.get(defTblKey);
    }
    catch (CommandException ex)
    {
      handleCmdException(ex, 0);//>=0 is to try again

      //exceptionThrown = true;
      // try a second time to see if the one with errors was cached
      try
      {
        table = manager.get(defTblKey);
      }
      catch (CommandException fx)
      {
        handleCmdException(fx, 0);
        exceptionThrown = true;
      }
    }
    long defTblTime = System.nanoTime();
    long dtCons = 0, dtOther = 0, dtBinding = 0;
    StringBuilder output = new StringBuilder();
    output.append("\n\n");
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
        if (printSchRefs)
        {
          output.append("\n------------------------------- SCHREFS --------------------------------");
          for(Definition d : defs)
          {
            if (d.getDefinitionKind().isSchemaReference())
            {
              output.append(d.toString()).append("\n");
            }
          }
        }
        dtOther = System.nanoTime();
        dtBinding = dtOther;
        if (args.length > fileArgIndex)
        {
          ZName arg = ZUtils.FACTORY.createZName(args[fileArgIndex]);
          output.append("\n------------------------------- BINDINGS -------------------------------").append("\n");
          Definition def = table.lookupName(arg);
          if (def == null)
          {
            output.append("Could not find bindings for ").append(arg).append("\n");
          }
          else
          {
            try
            {
              SortedSet<Definition> bindings = table.bindings(arg);
              dtBinding = System.nanoTime() - dtOther;
              final String result2 = bindings.toString().replaceAll(", ", ",\n");
              output.append("Bindings for ").append(args[fileArgIndex]).append(" = ").append(bindings.size()).append("\n");
              output.append(result2).append("\n");
            }
            catch (DefinitionException ex)
            {
              System.err.println("Could not retrive bindings for " + args[fileArgIndex]);
              handleCmdException(ex, 0);
            }
            output.append("\n-------------- of Def -------------").append("\n");
            output.append(def.toString()).append("\n");
          }
          output.append("\n------------------------------------------------------------------------").append("\n");
          output.append("\n");
        }
      }
      else
      {
        dtOther = System.nanoTime();
        dtBinding = dtOther;
      }
      output.append("CONSISTENCY-CHECK = ").append(consistency == null ? " okay! " : " has " + (consistency.totalNumberOfErrors() - 1) + " errors");
      output.append(consistency == null ? "" : consistency.getMessage(true)).append("\n");
    }
    long finishTime = System.nanoTime();
    long nano2msec = 1000000;
    output.append("\n------------------------------------------------------------------------").append("\n");
    output.append("START-TIME = ").append(startTime / nano2msec).append("\n");
    output.append("SETUP-TIME = ").append(setupTime / nano2msec).append("\t ").append((setupTime - startTime) / nano2msec).append("\n");
    output.append("PARSE-TIME = ").append(parseTime / nano2msec).append("\t ").append((parseTime - setupTime) / nano2msec).append("\n");
    output.append("TYPEC-TIME = ").append(typeTime / nano2msec).append("\t ").append((typeTime - parseTime) / nano2msec).append("\n");
    output.append("DEFTB-TIME = ").append(defTblTime / nano2msec).append("\t ").append((defTblTime - typeTime) / nano2msec).append("\n");
    output.append("DTCON-TIME = ").append(dtCons / nano2msec).append("\t ").append((dtCons - defTblTime) / nano2msec).append("\n");
    output.append("DTOTH-TIME = ").append(dtOther / nano2msec).append("\t ").append((dtOther - dtCons) / nano2msec).append("\n");
    output.append("DTBIN-TIME = ").append(dtBinding / nano2msec).append("\t ").append((dtBinding - dtOther) / nano2msec).append("\n");
    output.append("TOTAL-TIME = ").append(finishTime / nano2msec).append("\t ").append((finishTime - startTime) / nano2msec).append("\n");
    output.append("\n");

    System.out.println(output.toString());

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

  private static void handleCmdException(CommandException ex, int status) // negative exits
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
    if (status < 0) throw new CztException("Negative status while handling command exception, should exit JVM");//System.exit(status);
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
