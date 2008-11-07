/*
  Copyright (C) 2004, 2006 Petra Malik
  Copyright (C) 2008 Leo Freitas
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
package net.sourceforge.czt.z.dc;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.SortedMap;
import java.util.TreeMap;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.parser.z.ParseUtils;
import net.sourceforge.czt.session.Command;
import net.sourceforge.czt.session.FileSource;
import net.sourceforge.czt.session.Markup;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.session.Source;
import net.sourceforge.czt.typecheck.z.ErrorAnn;
import net.sourceforge.czt.typecheck.z.TypeCheckCommand;
import net.sourceforge.czt.typecheck.z.TypeCheckUtils;
import net.sourceforge.czt.z.ast.Spec;
import net.sourceforge.czt.z.ast.ZSect;

/**
 * Utilities for domain checking Z specifications.
 * This class provides a main method for command line use,
 * as well as several 'typecheck' methods that are designed
 * to be called by other Java classes.
 *
 * @author leo
 */
public class DomainCheckUtils implements DomainCheckPropertyKeys 
{  
  private final DomainChecker domainChecker_;
  
  /**
   * Do not generate instances of this class.
   * You should use the static methods directly.
   */
  protected DomainCheckUtils()
  {
    domainChecker_ = new DomainChecker();
  }

  protected String name()
  {
    return "zeddomaincheck";
  }

  /** Print a usage message to System.err, describing the
   *  command line arguments accepted by main.
   */
  protected void printUsage()
  {
    System.err.println("usage: " + name() + " [-apt] filename ...");
    System.err.println("flags: -a     use infix applies to definition.");
    System.err.println("       -p     process parent sections.");
    System.err.println("       -t     add trivial DC predicates.");
    System.err.println("       -i <l> list of parents to ignore.");
    System.err.println("              a semicolon-separated list of section names");
    System.err.println("              (e.g., -cp ./tests;/user/myfiles).");
    System.err.println("              The list is mandatory and must not be empty.");    
    System.err.println("      -cp <l> specify the value for czt.path as");
    System.err.println("              a semicolon-separated list of dirs");
    System.err.println("              (e.g., -cp ./tests;/user/myfiles).");
    System.err.println("              The list is mandatory and must not be empty.");    
    System.err.println("\n");
        System.err.println("Default flags are: \"" +
        ((useInfixAppliesToDefault() ? "-a " : "") +
        (processParentsDefault() ? "-p " : "") +
        (addTrivialDCDefault() ? "-t " : "")).trim() +
        "\"");
  }

  protected boolean useInfixAppliesToDefault()
  {
    return true;
  }

  protected boolean processParentsDefault()
  {
    return false;
  }
  
  protected boolean addTrivialDCDefault()
  {
    return false;
  }  
 
  protected String cztPathDefault()
  {
    return null;
  } 
  
  protected List<ZSectDCEnvAnn> lDomainCheck(Term term, SectionManager manager, List<String> parentsToIgnore,
    boolean useInfixAppliesto, boolean processParents, boolean addTrivialDC)
    throws DomainCheckException
  {
    // prepare the domain checker properties
    domainChecker_.setInfixAppliesTo(useInfixAppliesto);    
    domainChecker_.setProcessingParents(processParents);
    domainChecker_.setAddingTrivialDC(addTrivialDC);
    domainChecker_.setSectInfo(manager);
    
    // MUST be after setSectInfo, as it resets the default parent sections to ignore
    for(String parent : parentsToIgnore)
    {
      domainChecker_.addParentSectionToIgnore(parent);
    }    
    
    // domain check the given term accordingly
    List<ZSectDCEnvAnn> result = new ArrayList<ZSectDCEnvAnn>();
    if (term instanceof Spec)
    {
      result.addAll(domainChecker_.createDCZSect((Spec)term));
    }
    else if (term instanceof ZSect)
    {
      result.add(domainChecker_.createDCZSect((ZSect)term));
    }
    else
    {
      // for general terms, wrap it around a Z Sect
      result.add(domainChecker_.createDCZSect(term));
    }
    return result;
  }

  /** @return a fresh new section manager. */
  protected SectionManager getSectionManager()
  {
    SectionManager sectionManager = new SectionManager();
    sectionManager.putCommand(ZSectDCEnvAnn.class, DomainCheckUtils.getCommand());
    return sectionManager;
  }  
  
  protected void run(String [] args)
    throws IOException, net.sourceforge.czt.base.util.UnmarshalException, DomainCheckException
  {
    int result = 0;
    
    if (args.length == 0) {
      printUsage();
      System.exit(result);
    }

    List<String> files = new java.util.ArrayList<String>();
    boolean useInfixAppliesTo = useInfixAppliesToDefault();
    boolean processParents = processParentsDefault();
    boolean addTrivialDC = addTrivialDCDefault();    
    String cztpath = cztPathDefault();
    String parentsToIgnore = null;

    for (int i = 0; i < args.length; i++) 
    {
      if ("-a".equals(args[i])) 
      {
        useInfixAppliesTo = true;
      }
      else if ("-p".equals(args[i]))
      {
        processParents = true;
      }
      else if (args[i].equals("-i"))
      {
        if (i == args.length)
        {
          printUsage();
          System.err.println("\nYou need to provide an argument for `-i'");
          System.exit(result);
        }
        i++;
        parentsToIgnore = args[i].trim(); 
      }
      else if (args[i].equals("-cp"))
      {          
        if (i == args.length)
        {
          printUsage();
          System.err.println("\nYou need to provide an argument for `-cp'");
          System.exit(result);
        }
        i++;
        cztpath = args[i].trim();        
      }      
      else if (args[i].startsWith("-")) 
      {
        printUsage();
        System.exit(result);
      }
      else
      {
        files.add(args[i]);    
      }        
    }       
    SectionManager manager = getSectionManager();    
    manager.setProperty(PROP_DOMAINCHECK_USE_INFIX_APPLIESTO, String.valueOf(useInfixAppliesTo));
    manager.setProperty(PROP_DOMAINCHECK_PROCESS_PARENTS, String.valueOf(processParents));
    manager.setProperty(PROP_DOMAINCHECK_ADD_TRIVIAL_DC, String.valueOf(addTrivialDC));       
    if (cztpath != null && !cztpath.isEmpty())
    {
      manager.setProperty("czt.path", cztpath);
    }
    
    SortedMap<String, List<Long>> timesPerFile = new TreeMap<String, List<Long>>();        
    long zeroTime = System.currentTimeMillis();     
    long currentTime = zeroTime;
    long lastTime = zeroTime;    
    for (String file : files) {            
      //parse the file
      Term term = null;
      Markup markup = ParseUtils.getMarkup(file);
      
      Source source = null;
//      boolean openOk = false;      
//      if (useSpecReader)
//      {
//        for (String suff : net.sourceforge.czt.specreader.SpecReader.SUFFICES) {
//          if (file.endsWith(suff)) {
//            source = new SpecSource(file, isBufferingWanted, isNarrativeWanted);
//            openOk = true;
//            break;
//          }
//        }
//      }
//      if (!openOk)
//      {
        //NOTE: from the Main CZT UI, the file.getParent() is being added
        //      to czt.path. This seems to be spurious as it works without it.
        source = new FileSource(file);
//      }
      long parsingErrors = 0;
      try {
        lDomainCheck(term, manager, files, useInfixAppliesTo, processParents, addTrivialDC)
        term = this.domain
        term = this.domainCheck(source, manager);
      }
      catch (DomainCheckException e) {
        System.err.println("A domain check exception has happened: " + e.getMessage());
        e.printStackTrace();
      }
      catch (net.sourceforge.czt.parser.util.ParseException exception) {
        parsingErrors = exception.getErrorList().size();
        exception.printErrorList();
      }
      catch(net.sourceforge.czt.base.util.UnsupportedAstClassException e)
      {
        System.err.println("An attempt to wrongly cast an AST class has happened.\n" +
          "This is usually a bug, and should not happen. Please report it to czt-devel@lists.sourceforge.net");    
        e.printStackTrace();
      }
      catch(net.sourceforge.czt.util.CztException f)
      {
        System.err.println("A general CztException has happened.\n" +
          "This is usually a bug, and should not happen. Please report it to czt-devel@lists.sourceforge.net");    
        f.printStackTrace();
      }
      /* ex:
       * 0        40           
       * |--Parse--|--TypeCheck--|--PrintType--|--PrintZml--|      
       * lt = 0
       * ct = 40
       * pt = 40 (40 - 0)
       */            
      lastTime = currentTime;
      currentTime = System.currentTimeMillis();      
      long parseTime = currentTime - lastTime;
      long typeCheckTime = 0;
      long printTypeTime = 0;
      long printZmlTime  = 0; 
      long numberOfErrors = 0;
      //if the parse succeeded, typecheck the term
      if (term != null) {
        List<? extends ErrorAnn> errors =
          typeCheck(term, manager, false /*useBeforeDecl*/, false /*useNameIds*/, false /*raiseWarnings*/, null);
        
        // result is the number of errors to consider
        numberOfErrors = printErrors(errors, false /*raiseWarnings*/);
        result += numberOfErrors + parsingErrors;
        
        /* ex:
         * 0        40            100
         * |--Parse--|--TypeCheck--|--PrintType--|--PrintZml--|         
         * lt = 40
         * ct = 100
         * tt = 60  (100-40)
         */
        lastTime = currentTime;
        currentTime = System.currentTimeMillis();
        typeCheckTime = currentTime - lastTime;        
      }            
            
      timesPerFile.put(file, Arrays.asList(parsingErrors, numberOfErrors,
          parseTime, typeCheckTime, printTypeTime, printZmlTime, 
          parseTime+typeCheckTime+printTypeTime+printZmlTime));
      // Reset the currentTime offset
      currentTime = System.currentTimeMillis();
      lastTime = currentTime;
    }
    long totalTime = System.currentTimeMillis() - zeroTime;
    
    if (printBenchmark) {      
      System.out.println(totalTime + "ms for " + files.size() + " files.");
      for(String file : timesPerFile.keySet()) {
        List<Long> times = timesPerFile.get(file);
        System.out.println("\t" + times.get(6) + "ms for " + file + ":");
        System.out.println("\t\tparsing errors.." + times.get(0));
        if (!syntaxOnly) {
          System.out.println("\t\ttype errors....." + times.get(1));
        }
        System.out.println("\t\tparser.........." + times.get(2) + "ms");
        if (!syntaxOnly) {
          System.out.println("\t\ttypechecker....." + times.get(3) + "ms");
        }
        if (printTypes) {
          System.out.println("\t\tprint types....." + times.get(4) + "ms");
        }
        if (printZml) {
          System.out.println("\t\tprint zml......." + times.get(5) + "ms");          
        }
      }             
    }        
    System.exit(result);
  }

  public static void main(String[] args)
    throws IOException, net.sourceforge.czt.base.util.UnmarshalException
  {    
    TypeCheckUtils utils = new TypeCheckUtils();    
    utils.run(args);
  }

  /**
   * Get a Command object for use in SectionManager
   *
   * @return A command for typechecking sections.
   */
  public static Command getCommand()
  {
    return new TypeCheckCommand();
  }
}
