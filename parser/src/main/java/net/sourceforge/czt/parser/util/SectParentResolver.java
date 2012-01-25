package net.sourceforge.czt.parser.util;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.SectionInfo;
import net.sourceforge.czt.z.ast.Parent;
import net.sourceforge.czt.z.ast.ZSect;

public class SectParentResolver
{

  public static class CyclicSectionsException extends Exception
  {

    private final List<String> cyclicSects;

    public CyclicSectionsException(String message, List<String> cyclicSects)
    {
      super(message);
      this.cyclicSects = new ArrayList<String>(cyclicSects);
    }

    public List<String> getCyclicSects()
    {
      return Collections.unmodifiableList(cyclicSects);
    }
  }
  
  public static interface ParentCollector {
    public void collect(String sectName, String parent);
  }

  /**
   * Checks for cyclic parents of the given section, and throws an exception if a cyclic
   * relationship is found. The section manager must have the sections already parsed.
   * 
   * @param sectName
   * @param manager
   * @throws CommandException
   * @throws CyclicSectionsException
   */
  public static void checkCyclicParents(String sectName, SectionInfo manager)
      throws CommandException, CyclicSectionsException
  {
    collectParents(sectName, manager, null);
  }
  
  private static class OrderedParentCollector implements ParentCollector {
    
    private final List<String> parents = new ArrayList<String>();

    public List<String> getParents()
    {
      return Collections.unmodifiableList(parents);
    }

    @Override
    public void collect(String sectName, String parent)
    {
      // FIXME implement
    }
  }
  
  private static class DependenciesCollector implements ParentCollector {
    
    private final Map<String, Set<String>> dependencies = new HashMap<String, Set<String>>();

    public Map<String, Set<String>> getDependencyMap()
    {
      return dependencies;
    }

    @Override
    public void collect(String sectName, String parent)
    {
      
      Set<String> deps = dependencies.get(parent);
      if (deps == null) {
        deps = new HashSet<String>();
        dependencies.put(parent, deps);
      }
      
      deps.add(sectName);
    }
  }
  
  /**
   * Calculates a parent dependency map. The map contains sections mapping to sets of other
   * sections, that depend on it (have the first section as their parent). 
   * 
   * @param sectName
   * @param manager
   * @return
   * @throws CommandException
   * @throws CyclicSectionsException
   */
  public static Map<String, Set<String>> getParentDependencies(String sectName, SectionInfo manager)
      throws CommandException, CyclicSectionsException
  {
    DependenciesCollector deps = new DependenciesCollector();
    collectParents(sectName, manager, deps);
    return deps.getDependencyMap();
  }
  
  /**
   * Collects the parent section names of the given sectName. The collector is called
   * first on the deepest parents, and goes up afterwards. Note that the collector
   * may visit the same section several times if it is referenced in different
   * "parent branches".
   *  
   * The section manager must have the sections already parsed.
   * 
   * @param sectName
   * @param manager
   * @param collector
   * @throws CommandException
   * @throws CyclicSectionsException if a cyclic parent relationship is found 
   */
  public static void collectParents(String sectName, SectionInfo manager, ParentCollector collector)
      throws CommandException, CyclicSectionsException
  {
    collectParents(sectName, manager, new ArrayList<String>(1), collector);
  }
  
  private static void collectParents(String sectName, SectionInfo manager, List<String> visited,
      ParentCollector collector) throws CommandException, CyclicSectionsException
  {
    
    boolean cyclic = visited.contains(sectName);
    visited.add(sectName);
    
    if (cyclic) {
      
      StringBuilder msg = new StringBuilder("Sections are parents of each other:");
      for (String s : visited) {
        msg.append(" ").append(s);
      }
      
      throw new CyclicSectionsException(msg.toString(), visited);
    }
    
    Key<ZSect> sectKey = new Key<ZSect>(sectName, ZSect.class);
    if (!manager.isCached(sectKey)) {
      // The section in question has not been parsed yet - do not continue.
      // Note that we choose not to parse, we assume parsing is done separately
      throw new CommandException("Cannot resolve section " + sectName);
    }
    
    ZSect zs = manager.get(sectKey);
    for (Parent parent : zs.getParent()) {
      
      // copy the visited list (with additional space for the next one)
      // we need to copy the list, because the parents may branch
      List<String> visitedCopy = new ArrayList<String>(visited.size() + 1);
      visitedCopy.addAll(visited);
      
      String parentSectName = parent.getWord();
      // continue recursively
      collectParents(parentSectName, manager, visitedCopy, collector);
      
      if (collector != null) {
        collector.collect(sectName, parentSectName);
      }
    }
  }
  

}
