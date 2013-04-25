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

/**
 * A utility class to resolve section parents, taking cyclic relationships into account.
 * The class provides static methods to check for cycles or collect parent relationships.
 * 
 * @author Andrius Velykis
 */
public class SectParentResolver
{

  /**
   * Exception to signal that cyclic parent sections have been found. The exception carries
   * the cycles that triggered it as String lists.
   * 
   * @author Andrius Velykis
   */
  public static class CyclicSectionsException extends Exception
  {

    /**
	 * 
	 */
	private static final long serialVersionUID = -1095064817735467171L;
	private final List<List<String>> cycles;

    public CyclicSectionsException(List<List<String>> cycles)
    {
      super(cyclicMsg(cycles));
      if (cycles.isEmpty()) {
        throw new IllegalArgumentException("Exception initialised without cycles.");
      }
      
      this.cycles = new ArrayList<List<String>>(cycles.size());
      for (List<String> cycle : cycles) {
        // defensive copy
        this.cycles.add(Collections.unmodifiableList(new ArrayList<String>(cycle)));
      }
    }

    /**
     * Retrieves the first (or only) cycle found - will always return a cycle.
     * @return
     */
    public List<String> getCyclicSects()
    {
      return cycles.get(0);
    }
    
    /**
     * Retrieves all cycles stored.
     * @return
     */
    public List<List<String>> getAllCycles() {
      return Collections.unmodifiableList(cycles);
    }

    private static String cyclicMsg(List<List<String>> cycles) {
      
      StringBuilder msg = new StringBuilder("Sections are parents of each other: ");
      String lineSep = "";
      for (List<String> cycle : cycles) {
        
        msg.append(lineSep);
        lineSep = ";\n";
        
        String sep = "";
        for (String s : cycle) {
          msg.append(sep).append(s);
          sep = " > ";
        }
      }
      
      return msg.toString();
    }
  }
  
  public interface ParentCollector {
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
  
  private static class AllParentsCollector implements ParentCollector {
    
    private final Set<String> parents = new HashSet<String>();

    public Set<String> getParents()
    {
      return Collections.unmodifiableSet(parents);
    }

    @Override
    public void collect(String sectName, String parent)
    {
      parents.add(parent);
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
   * Collects all parents for the given section. Ignores any cyclic dependencies.
   * 
   * @param sectName
   * @param manager
   * @return
   * @throws CommandException
   */
  public static Set<String> getParents(String sectName, SectionInfo manager)
      throws CommandException
  {
    AllParentsCollector parents = new AllParentsCollector();
    collectParentsUnchecked(sectName, manager, parents);
    return parents.getParents();
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
   * @throws CyclicSectionsException if a cyclic parent relationships are found 
   */
  public static void collectParents(String sectName, SectionInfo manager, ParentCollector collector)
      throws CommandException, CyclicSectionsException
  {
    List<List<String>> cycles = new ArrayList<List<String>>();
    collectParents(sectName, manager, new ArrayList<String>(1), collector, cycles, true);
    
    if (!cycles.isEmpty()) {
      // collecting all cycles - report found ones
      throw new CyclicSectionsException(cycles);
    }
  }
  
  /**
   * The same as {@link #collectParents(String, SectionInfo, ParentCollector)}, but does not throw
   * exception if cycles found. If a cycle is visited, the repeated section is ignored.
   * 
   * @param sectName
   * @param manager
   * @param collector
   * @throws CommandException
   */
  public static void collectParentsUnchecked(String sectName, SectionInfo manager, ParentCollector collector)
      throws CommandException
  {
    try {
      collectParents(sectName, manager, new ArrayList<String>(1), collector, new ArrayList<List<String>>(), true);
    } catch (CyclicSectionsException ex) {
      // ignore - should not be thrown for all cycles
    }
  }
  
  private static boolean collectParents(String sectName, SectionInfo manager, List<String> visited,
      ParentCollector collector, List<List<String>> cycles, boolean allCycles)
      throws CommandException, CyclicSectionsException
  {
    
    boolean cyclic = visited.contains(sectName);
    visited.add(sectName);
    
    if (cyclic) {
      if (!cycles.contains(visited)) {
        // avoid duplicates
        cycles.add(visited);
      }
      
      if (allCycles) {
        // found a cycle, but collecting all cycles - do not go further
        return false;
      } else {
        // break on first cycle
        throw new CyclicSectionsException(cycles);
      }
    }
    
    Key<ZSect> sectKey = new Key<ZSect>(sectName, ZSect.class);
    if (!manager.isCached(sectKey)) {
      // The section in question has not been parsed yet - do not continue.
      // Note that we choose not to parse, we assume parsing is done separately
      throw new CommandException(manager.getDialect(), "Cannot resolve section " + sectName);
    }
    
    ZSect zs = manager.get(sectKey);
    for (Parent parent : zs.getParent()) {
      
      // copy the visited list (with additional space for the next one)
      // we need to copy the list, because the parents may branch
      List<String> visitedCopy = new ArrayList<String>(visited.size() + 1);
      visitedCopy.addAll(visited);
      
      String parentSectName = parent.getWord();
      // continue recursively
      boolean success = collectParents(
          parentSectName, manager, visitedCopy, collector, cycles, allCycles);
      
      // check if success - it can fail if a cycle is found
      if (success && collector != null) {
        collector.collect(sectName, parentSectName);
      }
    }
    
    return true;
  }
  

}
