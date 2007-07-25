/**
Copyright 2007, Leo Freitas
This file is part of the CZT project.

The CZT project contains free software; you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation; either version 2 of the License, or
(at your option) any later version.

The CZT project is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with CZT; if not, write to the Free Software
Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
*/
package net.sourceforge.czt.z.dc;

import java.io.File;
import java.io.IOException;
import java.io.Writer;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Date;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.SortedMap;
import java.util.SortedSet;
import java.util.TreeMap;
import java.util.TreeSet;
import java.util.logging.Logger;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.util.UnsupportedAstClassException;
import net.sourceforge.czt.parser.util.DefinitionTable;
import net.sourceforge.czt.parser.util.DefinitionTableService;
import net.sourceforge.czt.parser.util.OpTable;
import net.sourceforge.czt.parser.util.OpTableService;
import net.sourceforge.czt.print.util.PrintException;
import net.sourceforge.czt.print.z.AstToPrintTreeVisitor;
import net.sourceforge.czt.print.z.PrintUtils;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.FileSource;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.Markup;
import net.sourceforge.czt.session.SectionInfo;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.session.Source;
import net.sourceforge.czt.util.CztException;
import net.sourceforge.czt.z.ast.AxPara;
import net.sourceforge.czt.z.ast.ConjPara;
import net.sourceforge.czt.z.ast.LocAnn;
import net.sourceforge.czt.z.ast.NarrPara;
import net.sourceforge.czt.z.ast.Para;
import net.sourceforge.czt.z.ast.Parent;
import net.sourceforge.czt.z.ast.Pred;
import net.sourceforge.czt.z.ast.Sect;
import net.sourceforge.czt.z.ast.Spec;
import net.sourceforge.czt.z.ast.TruePred;
import net.sourceforge.czt.z.ast.ZNameList;
import net.sourceforge.czt.z.ast.ZSect;
import net.sourceforge.czt.z.visitor.ParaVisitor;
import net.sourceforge.czt.z.visitor.ParentVisitor;
import net.sourceforge.czt.z.visitor.SectVisitor;
import net.sourceforge.czt.z.visitor.ZSectVisitor;

/**
 *
 * @author leo
 */
public class DomainChecker extends AbstractDC<List<Pair<Para, Pred>>> implements
  SectVisitor<List<Pair<Para, Pred>>>,
  ZSectVisitor<List<Pair<Para, Pred>>>,
  ParentVisitor<List<Pair<Para, Pred>>>,
  ParaVisitor<List<Pair<Para, Pred>>>
{  
  
  private static final Logger logger_ = Logger.getLogger(DomainChecker.class.getName());
  public static boolean DEFAULT_PROCESS_PARENTS = false;
  
  private SectionInfo sectInfo_;
  private Spec dcToolkit_;
  private DefinitionTable defTable_;
  private OpTable opTable_;
  private final SortedSet<String> parentsToIgnore_;
  private final DomainCheck domainCheck_;  
  private final OpTableService opTableService_;
  private final DefinitionTableService defTableService_;
    
  protected static final String DC_TOOLKIT_NAME = "dc_toolkit";

  protected static final String[] EXTENDED_TOOLKIT_NAMES =
    {
      "whitespace",
      "fuzz"
    };
  
  protected static final String[] STANDARD_TOOLKIT_NAMES =
    { 
      "prelude", 
      "number_toolkit", 
      "set_toolkit",
      "relation_toolkit", 
      "function_toolkit", 
      "sequence_toolkit",
      "standard_toolkit"
    };
  
  public DomainChecker()
  {
    setSectInfo(null);
    domainCheck_ = new DomainCheck();    
    opTableService_ = new OpTableService(null);
    defTableService_ = new DefinitionTableService();
    parentsToIgnore_ = new TreeSet<String>();
    reset();
  }
  
  protected void reset()
  {    
    opTable_ = null;
    defTable_ = null;
    clearParentsToIgnore();
    parentsToIgnore_.addAll(defaultParentsToIgnore());
  }
  
  /**
   * By default ignore all STANDARD_TOOLKIT_NAMES and EXTENDED_TOOLKIT_NAMES Z sections.
   */  
  protected SortedSet<String> defaultParentsToIgnore() 
  {
    SortedSet<String> result = new TreeSet<String>(Arrays.asList(STANDARD_TOOLKIT_NAMES));
    result.addAll(Arrays.asList(EXTENDED_TOOLKIT_NAMES));
    result.add(DC_TOOLKIT_NAME);
    return result;
  }
  
  public void setSectInfo(SectionInfo si)
  {
    dcToolkit_ = null;
    sectInfo_ = si;
  }
  
  /**
   * Clears both sets of parents to process and to ignore
   */
  public void clearParentsToIgnore()
  {
    parentsToIgnore_.clear();
  }
  
  /**
   * Returns a unmodifiable set of section names not being domain checked. 
   */
  public SortedSet<String> getParentsToIgnore() 
  {
    return Collections.unmodifiableSortedSet(parentsToIgnore_);
  }
  
  public void addParentSectionToIgnore(Parent parent)
  {
    assert parent != null;
    addParentSectionToIgnore(parent.getWord());
  }
  
  public void addParentSectionToIgnore(String parent)
  {
    assert parent != null && !parent.isEmpty() : "Invalid (null or empty) section name.";
    parentsToIgnore_.add(parent);  
  }
  
  /**
   * Collects the list of predicates associated with the top-level paragraphs for 
   * each section within the given Spec term. The list of parents to process determines
   * which parents should be included while processing the Spec.
   */
  public SortedMap<String, List<Pair<Para, Pred>>> dc(Spec term, boolean processParents) 
  {
    assert term != null : "Invalid (null) specification!";
    // sectInfo_ = sectInfo; // null section info is not helpful, but neither an impediment!
    
    SortedMap<String, List<Pair<Para, Pred>>> result = new TreeMap<String, List<Pair<Para, Pred>>>();    
    for(Sect sect : term.getSect())
    {
      if (sect instanceof ZSect)
      {
        ZSect zsect = (ZSect)sect;
        processZSect(result, zsect, processParents);        
      }
    }    
    // clear fields to default values, this includes parent sections to ignore
    // outside the standard ones!!!
    reset();
    return result;
  }
  
  public SortedMap<String, List<Pair<Para, Pred>>> dc(ZSect term, boolean processParents) 
  {
    assert term != null : "Invalid (null) specification!";
    //sectInfo_ = sectInfo; // null section info is not helpful, but neither an impediment!

    SortedMap<String, List<Pair<Para, Pred>>> result = new TreeMap<String, List<Pair<Para, Pred>>>();    
    processZSect(result, term, processParents);    
    reset();
    assert (result.size() == 1) : "Could not collect ZSect DC?"; 
    return result;
  }
  
  protected void processZSect(SortedMap<String, List<Pair<Para, Pred>>> result, ZSect term, boolean processParents)
  {
    String sectName = term.getName();
    if (!processParents) 
    {
      for(Parent parent : term.getParent())
      {
        addParentSectionToIgnore(parent);
      }
    }
    List<Pair<Para, Pred>> sectDC = term.accept(this);
    List<Pair<Para, Pred>> old = result.put(sectName, sectDC);
    assert old == null : "Duplicated section term within specification for section " + sectName;
  }
  
  private ZSect createDCZSect(String sectName) 
  {
    ZSect result = factory_.createZSect(sectName + "_dc", 
      factory_.list(factory_.createParent(sectName),
        factory_.createParent(DC_TOOLKIT_NAME)),
      factory_.createZParaList());
    return result;
  }
  
  protected void processDCZSect(ZSect result, List<Pair<Para, Pred>> dcList, boolean addTrivialDC)
  {
    assert result != null && dcList != null;
    ConjPara conjPara;
    NarrPara narrPara;
    String narrText;
    ZNameList genFormals;
    
    // header. avoid \n\t in case of UNICODE printing?
    narrText = "Z section " + result.getName() + " has " + dcList.size() + " DCs (including trivial ones).";
    narrPara = factory_.createNarrPara(factory_.list(narrText));
    result.getZParaList().add(narrPara);        
    Date date = new Date();    
    narrText = "Created at " + date.toString() + ".";    
    narrPara = factory_.createNarrPara(factory_.list(narrText));
    result.getZParaList().add(narrPara);        
      
    for(Pair<Para, Pred> pair : dcList)
    {
      //!addTrivialDC ==> !(pair.SECOND instanceof TruePred)      
      if (addTrivialDC || !(pair.SECOND instanceof TruePred))
      {
        // since we cannot retrieve the theorem's name from a latex, neither
        // generate it from a ConjPara, just add some NarrText around instead.
        narrText = "";
        LocAnn loc = (LocAnn)pair.FIRST.getAnn(LocAnn.class);
        if (loc != null)
        {
          narrText = "DC for " + loc.toString() + "\n";
        } 
        else 
        { 
          narrText = "DC for " + pair.FIRST.toString() + "\n";      
        }  
        narrPara = factory_.createNarrPara(factory_.list(narrText)); 

        // retrieve genFormals in case of AxPara, or an empty list otherwise
        genFormals = factory_.createZNameList();
        if (pair.FIRST instanceof AxPara)
        {
          genFormals.addAll(((AxPara)pair.FIRST).getZNameList());
        }      
        conjPara = factory_.createConjPara(genFormals, pair.SECOND);
     
        // add both narrative and dc conjecture paragraphs!
        result.getZParaList().add(narrPara);
        result.getZParaList().add(conjPara);
      }
    }
  }
  
  public ZSect createDCSection(ZSect term, boolean processParents, boolean addTrivialDC)
  {
    assert term != null; 
    ZSect result = createDCZSect(term.getName());
    SortedMap<String, List<Pair<Para, Pred>>> dcMap = dc(term, processParents);
    assert dcMap != null && !dcMap.isEmpty() : "Could not calculate DC map for " + term; 
    
    assert dcMap.containsKey(term.getName()) : "Could not find DC mapping for " + term;
    // add to result.getZParaList() the appropriate DC conjParas
    processDCZSect(result, dcMap.get(term.getName()), addTrivialDC);
    return result;
  }
  
  public List<ZSect> createDCSection(Spec term, boolean processParents, boolean addTrivialDC)
  {
    SortedMap<String, List<Pair<Para, Pred>>> dcMap = dc(term, processParents);
    assert dcMap != null && !dcMap.isEmpty() : "Could not calculate DC map for " + term; 
    
    List<ZSect> result = new ArrayList<ZSect>(dcMap.size());
    for(Map.Entry<String, List<Pair<Para, Pred>>> entry : dcMap.entrySet()) 
    {
      ZSect zsect = createDCZSect(entry.getKey());
      processDCZSect(zsect, entry.getValue(), addTrivialDC);
      result.add(zsect);
    }
    assert result.size() == dcMap.size() : "More DC's for mapped section than resulting List<ZSecT>!";

    return result;
  }
  
  public Spec createDCSpec(Spec term, boolean processParents, boolean addTrivialDC)
  {
    List<ZSect> sects = createDCSection(term, processParents, addTrivialDC);
    Spec result = factory_.createSpec(sects, term.getVersion());
    return result;
  }
  
  
  private void loadDCToolkit() throws DomainCheckException
  {
    assert sectInfo_ != null : "Cannot load " + DC_TOOLKIT_NAME + " without a section info set!";
    if (dcToolkit_ == null)
    {
      // parse the dcToolkit within the section manager so that that operator 
      // table for (_appliesTo_) is available within it.      
      try 
      {
        String dcURL = DomainChecker.class.getResource("/lib/" + DC_TOOLKIT_NAME + ".tex").toString();
        dcToolkit_ = (Spec)sectInfo_.get(new Key(dcURL, Spec.class));      
      } catch(CommandException e)
      {
        throw new DomainCheckException("A command exception happened (see causes) while trying to parse " + DC_TOOLKIT_NAME, e);
      }
    }
    assert dcToolkit_ != null : "Could not load " + DC_TOOLKIT_NAME;
  }
  
  private void loadOpTable(ZSect term) throws DomainCheckException
  {
    assert sectInfo_ != null && term != null && sectInfo_ instanceof SectionManager; 
    try 
    {
      opTable_ = (OpTable)opTableService_.run(term, sectInfo_);
      ((SectionManager)sectInfo_).put(new Key(term.getName(), OpTable.class), opTable_);
    }
    catch(CommandException i)
    {
      opTable_ = null;
      throw new DomainCheckException("Could not create an operator table (see causes) for given ZSect " + term.getName(), i);
    }
  }
  
  private void loadFileSource(String sectName, Markup markup) throws DomainCheckException
  {
    assert sectInfo_ != null;
    String fileName = "./" + sectName + (markup.equals(Markup.LATEX) ? ".tex" : (markup.equals(Markup.ZML) ? ".xml" : ".utf-8"));
    File file = new File(fileName);
    if (!file.exists()) 
    { 
      try {
        boolean created = file.createNewFile();
        assert created : "Could not create file for DC section " + sectName; 
      } catch(IOException e)
      {
        throw new DomainCheckException("Could not create new ZSect DC file " + sectName + 
          " in " + markup.toString() + " markup format (see causes).", e);
      }
    }
    ((SectionManager)sectInfo_).put(new Key(sectName, Source.class), new FileSource(file));        
        
  }
  
  public void printDCZSect(ZSect term, Writer writer, Markup markup) // term must be ZSect or spec
    throws DomainCheckException
  {
    // don't accept null or non-section manager impl, since PrintLatex requires a SectionManager!
    if (sectInfo_ == null || !(sectInfo_ instanceof SectionManager)) 
    {
      throw new DomainCheckException("Cannot print DCs because no section manager is set!");
    } 
    else
    {
      String name = term.getName();      
      //loadFileSource(name);
      //loadOpTable(term);
      //assert opTable_ != null;
      //loadDCToolkit();
      //assert dcToolkit_ != null;
      try 
      {                
        PrintUtils.print(term, writer, (SectionManager)sectInfo_, markup);
      } 
      catch(AstToPrintTreeVisitor.CannotPrintAstException f)
      {
        throw new DomainCheckException("A AST printing exception happened (see causes) while trying to print " + name, f);
      }
      catch(PrintException g)
      {
        throw new DomainCheckException("A AST printing exception happened (see causes) while trying to print " + name, g);
      }
      catch(CztException h)
      {
        throw new DomainCheckException("A CZT exception happened (see causes) while trying to print " + name, h);
      }            
    }    
  }
  
  /* TERM DC COLLECTION METHODS */
  
  /**
   * Collect all DC predicates from the terms within the given list.
   * This could be a ZParaList, a ListTerm<Parent>, or ListTerm<Sect>,
   * which comes from ZSect.getZParaList(), ZSect.getParent(), and
   * Spec.getSect().
   */
  protected <T extends Term> List<Pair<Para, Pred>> collect(List<T> list) 
  {
    List<Pair<Para, Pred>> result = new ArrayList<Pair<Para, Pred>>();
    for(T term : list) 
    {
      result.addAll(term.accept(this));
    }
    return result;
  }

  // UnparsedZSect, NarrSect
  public List<Pair<Para, Pred>> visitSect(Sect term)
  {
    // just ignore other types of Sect
    return factory_.list();
  }

  public List<Pair<Para, Pred>> visitParent(Parent term)
  {
    String sectName = term.getWord();
    List<Pair<Para, Pred>> result = factory_.list();
    if (!parentsToIgnore_.contains(sectName))
    { 
      if (sectInfo_ != null) 
      {
        try
        {
          ZSect parentSect = (ZSect)sectInfo_.get(new Key(sectName, ZSect.class));    
          result.addAll(parentSect.accept(this));
        } catch (CommandException ex)
        {
          // warns in case of failure, but do not stop.
          logger_.warning("Could not retrieve definitions for parent section " + sectName + 
            ". Continuing without domain checking this parent (and its parents).");
          logger_.fine("CommandException thrown while trying to retrieve definitions for parent section " + sectName + 
            " with the following message: " + ex.getMessage() + ". Continuing without domain checking this parent (and its parents).");
        }
      }
      else
      {
        throw new CztException("Domain Check Exception thrown (see causes) while visiting ZSect " + sectName, 
          new DomainCheckException("Could not process requested parent section " + sectName + 
          " because no section manager is set!"));
      }
    }
    return result;
  }

  public List<Pair<Para, Pred>> visitZSect(ZSect term)
  {
    String sectName = term.getName();
    if (parentsToIgnore_.contains(sectName)) 
    {
      throw new CztException("Domain Check Exception thrown (see causes) while visiting ZSect " + sectName, 
        new DomainCheckException("Should not process section marked to be ignored (" + sectName + ")!"));
    }
    List<Pair<Para, Pred>> result = factory_.list();    
    if (sectInfo_ != null)
    {
      try {
        // retrieve definition table for Z section being analysed
        defTable_ = (DefinitionTable)defTableService_.run(term, sectInfo_);
      } catch(CommandException e) {
        defTable_ = null;
        logger_.warning("Could not retrieve DefinitionTable for section " + sectName + 
          ". That means the appliesTo operator will always be used for ApplExpr.");
        logger_.warning("CommandException thrown while trying to retrieve definition table for " + sectName +
          " with the following message: " + e.getMessage() + ".");
      }
    }
    else 
    {
      throw new CztException("Domain Check Exception thrown (see causes) while visiting ZSect " + sectName, 
        new DomainCheckException("Could not retrieve DefinitionTable for section " + sectName + 
        " because no section manager is set!"));
    }
    // process section parents
    result.addAll(collect(term.getParent()));
    
    // collect all DC predicates from the declared paragraphs
    result.addAll(collect(term.getZParaList()));
    
    // clear definition table
    defTable_ = null;
    
    return result;
  }
  
  public List<Pair<Para, Pred>> visitPara(Para term) 
  {    
    return factory_.list(new Pair<Para, Pred>(term, domainCheck_.runDC(term, defTable_)));
  }

  public List<Pair<Para, Pred>> visitTerm(Term term)
  {
    throw new CztException("Domain Check Exception thrown (see causes) while visiting Term " + term.toString(), 
        new DomainCheckException("Invalid term " + term.getClass().getName() + " to calculate domain check for!"));
  }
}
