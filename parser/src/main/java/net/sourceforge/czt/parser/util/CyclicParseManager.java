package net.sourceforge.czt.parser.util;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;
import java.util.Stack;

import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.SectionInfo;
import net.sourceforge.czt.util.CztException;
import net.sourceforge.czt.z.ast.Parent;

/**
 * <p>
 * A manager to resolve cyclic parent paths during the parsing process. It is stateful
 * and should be used during the parsing process. When the sections have already been
 * parsed, resolving cyclic parents should be done using methods in 
 * {@link SectParentResolver} class.
 * </p>
 * <p>
 * This class is used together with a {@link SectionInfo} section manager, to which
 * the manager attaches itself. This allows keeping the state during the parsing
 * of sections, as long as the same section manager is used. Use static method 
 * {@link #getManager(SectionInfo)} to retrieve the instance of the cyclic parents 
 * manager for the given section manager. 
 * </p>
 * <p>
 * The manager tracks "active" sections during parent section calls of the parsing 
 * process. Then, if an already "active" section is reached again, the manager
 * filters it out, essentially "cutting" the cycle at that point.
 * </p>
 * <p>
 * For example, if the cycle is of sections "A &rarr; B &rarr; C &rarr; A", before
 * section A calls to parent section B for its info tables (and thus parsing), section
 * A is marked "active". Because B is not active yet, parser is allowed to go parsing
 * section B. Now before B calls parent C, it is marked "active", and so on. Eventually,
 * we arrive when parsing section C, we are about to call for parsing of section 
 * A&mdash;which will get us into the loop. However, the "active" sections stack at this
 * point is "A, B, C", so A is already "active". Thus the algorithm excludes A from the
 * valid parent list, and C appears to the parser as having no parents at all. At this
 * point, we have "cut" the cycle. Without any parents to process, C marks itself "inactive".
 * C finishes parsing (maybe with errors, because it was relying on something in A) and 
 * the call returns to B. Now it makes itself "inactive", and so on. Finally, A resolves
 * its parents, is marked "inactive" and finishes parsing itself.
 * </p>
 * <p>
 * The algorithm relies on all parent calls during the parsing process using this manager.
 * All parent calls must be encapsulated by the pair of 
 * {@link #getValidParentNames(String, List)} and {@link #visitedParents(String)}, to
 * ensure correct "activation/deactivation" of sections. Note that 
 * {@link #getValidParents(String, List)} can be used for convenience instead of
 * {@link #getValidParentNames(String, List)}. 
 * </p>
 * 
 * @author Andrius Velykis
 */
public class CyclicParseManager {
  
  private static final Key<CyclicManagerSingleton> CYCLIC_MANAGER_KEY = 
      new Key<CyclicManagerSingleton>("cyclic-parse-manager", CyclicManagerSingleton.class);
  
  /**
   * Retrieves the instance of {@link CyclicParseManager} for the given sectInfo. 
   * If one does not exist, it gets created and assigned to the sectInfo.
   * 
   * @param sectInfo Section manager
   * @return
   */
  public static CyclicParseManager getManager(SectionInfo sectInfo)
  {
    CyclicManagerSingleton sectSingleton;
    if (sectInfo.isCached(CYCLIC_MANAGER_KEY)) {
      try {
        sectSingleton = sectInfo.get(CYCLIC_MANAGER_KEY);
      }
      catch (CommandException e) {
        // should not happen
        throw new CztException(e);
      }
    } else {
      sectSingleton = new CyclicManagerSingleton();
      sectInfo.put(CYCLIC_MANAGER_KEY, sectSingleton, Collections.<Key<?>>emptySet());
    }
    
    CyclicParseManager manager = sectSingleton.manager.get();
    if (manager == null) {
      // new thread
      manager = new CyclicParseManager();
      sectSingleton.manager.set(manager);
    }

    return manager;
  }
  
  private final Stack<String> activeSects = new Stack<String>();
  
  private final List<List<String>> foundCycles = new ArrayList<List<String>>();
  
  /**
   * Filters the parents - only parents that are not active in the call stack are 
   * returned. This allows to "cut" the section cycle.
   * 
   * This also makes the given section active - so it is filtered
   * from the parent list, and any recursive parent queries as well.
   * 
   * After visiting the parents, {@link #visitedParents(String)} must
   * be called for the given section, to mark the section as no longer
   * active. Basically, the calls to {@link #getValidParentNames(String, List)}
   * and {@link #visitedParents(String)} must wrap the calls to parents.
   * 
   * @param section 
   *          The section to activate - parents must belong to the section
   * @param parents 
   *          Parents of the section, which will be filtered
   * @return 
   *          Filtered list of the given parents, which have not been visited yet
   * @see #visitedParents(String)
   */
  public List<String> getValidParentNames(String section, List<String> parents)
  {
    assert section != null;
    assert !activeSects.contains(section) : "Section " + section
        + " is already active - invalid parent call. Active sections: "
        + String.valueOf(activeSects);

    activeSects.add(section);

    List<String> validParents = new ArrayList<String>();

    for (String parent : parents) {
      if (activeSects.contains(parent)) {
        // found a cycle - mark the stack to return for reporting
        List<String> cycle = new LinkedList<String>(activeSects);
        // include the end parent
        cycle.add(parent);
        if (!foundCycles.contains(cycle)) {
          // maybe found a duplicate cycle?
          foundCycles.add(cycle);
        }
      }
      else {
        // only add parents that are not in the "active" parents stack
        validParents.add(parent);
      }
    }

    // produces a filtered list of parents, which have not been visited yet
    return validParents;
  }
  
  /**
   * A convenience method to filter non-cyclic parents. Calls 
   * {@link #getValidParentNames(String, List)} with the names of given parents.
   * 
   * @param section
   *          The section to activate - parents must belong to the section
   * @param parents
   *          Parents of the section, which will be filtered
   * @return
   *          Filtered list of the given parents, which have not been visited yet
   * @see #getValidParentNames(String, List)
   */
  public List<Parent> getValidParents(String section, List<Parent> parents)
  {
    List<String> parentNames = new ArrayList<String>();
    for (Parent parent : parents) {
      parentNames.add(parent.getWord());
    }

    List<String> validParentNames = getValidParentNames(section, parentNames);
    List<Parent> validParents = new ArrayList<Parent>();
    for (Parent parent : parents) {
      if (validParentNames.contains(parent.getWord())) {
        validParents.add(parent);
      }
    }

    return validParents;
  }
  
  /**
   * Marks the given section as inactive. The section must have been activated via
   * {@link #getValidParentNames(String, List)} before.
   * 
   * @param section 
   *          The section to deactivate
   * @return
   *          All cycles found for the section during the parent visit, or empty list
   *          if no cycles found. The cycles start with the given section, then go to
   *          its parent, and end with a second instance of the cycle section.
   * @see #getValidParents(String, List)
   */
  public List<List<String>> visitedParents(String section)
  {
    assert section != null;
    assert !activeSects.isEmpty() : "Section " + section + " has not been made active.";
    assert section.equals(activeSects.peek()) : "Section " + section
        + " cannot be made inactive, because section " + activeSects.peek()
        + " is currently activated.";

    activeSects.pop();
    
    List<List<String>> cyclesForSect = getFoundCyclesForSection(section);

    if (activeSects.isEmpty()) {
      // clear the found cycles
      foundCycles.clear();
    }

    return cyclesForSect;
  }

  private List<List<String>> getFoundCyclesForSection(String section)
  {

    List<List<String>> sectionCycles = new ArrayList<List<String>>();
    
    for (List<String> cycle : foundCycles) {

      List<String> sectCycle = getCycleForSection(section, cycle);
      if (!sectCycle.isEmpty()) {
        // found a cycle
        sectionCycles.add(sectCycle);
      }
    }

    return sectionCycles;
  }

  /**
   * <p>
   * Calculates a cycle for the given section, based upon a given other cycle.
   * It can unfold cyclic relationship, e.g. cycle "A &rarr; B &rarr; A" for
   * section B would be returned as "B &rarr; A &rarr; B".
   * </p>
   * <p>
   * Default visibility for testing purposes.
   * </p>
   * 
   * @param section
   * @param cycle
   * @return
   */
  static List<String> getCycleForSection(String section, List<String> cycle)
  {
    int sectIndex = cycle.indexOf(section);
    if (sectIndex < 0) {
      // the section does not feature in the cycle
      return Collections.emptyList();
    }

    // get the end of the cycle, and check where the cycle starts
    String lastSect = cycle.get(cycle.size() - 1);
    int cycleStart = cycle.indexOf(lastSect);

    if (sectIndex > cycleStart) {
      /*
       * The section is inside a cycle - append to the end. 
       * e.g. if the cycle is A -> B -> C -> B, and we want
       * cycle for section C, first we will append the remainder
       * between the cycle start (first B) and the section in 
       * question - C. It will produce a cycle of
       * A -> B -> C -> B -> C. Now we can get everything from 
       * C to the end, and will get the necessary cycle: 
       * C -> B -> C. 
       */

      List<String> startToSect = cycle.subList(cycleStart + 1, sectIndex + 1);
      List<String> updatedCycle = new ArrayList<String>(cycle);
      updatedCycle.addAll(startToSect);
      cycle = updatedCycle;
    }
    
    // get the cycle from the section to the end
    return new ArrayList<String>(cycle.subList(sectIndex, cycle.size()));
  }
  
  /**
   * Renders the parent cycle into a nice String. Returns as a pair of parent
   * and the cycle rendered based on the parent as root.
   * 
   * @param cycle
   * @return Pair of <parentName, cycleString>
   */
  public static Pair<String, String> renderParseParentCycle(List<String> cycle)
  {
    
    assert cycle.size() > 1 : "Invalid cycle: " + cycle;
    
    // Because the cycle starts with the section, we want to rebase it to start
    // with the parent of the section.
    
    // copy the list for modification
    cycle = new ArrayList<String>(cycle);
    String sect = cycle.get(0);
    // remove the first section - the cycle is now based on the parent
    cycle.remove(0);
    String cycleParent = cycle.get(0);
    
    // check if it was a full cycle (e.g. "A -> B -> C -> A"), 
    // or just a cycle later in the stack, e.g. "A -> B -> C -> D -> C".
    if (sect.equals(cycle.get(cycle.size() - 1))) {
      // full cycle - the section is at the end of the cycle
      // add the cycle parent to the end to "rotate" the cycle
      // it becomes "B -> C -> A -> B"
      cycle.add(cycleParent);
    } else {
      // the cycle is later in the stack, so do not do anything else,
      // e.g. we now have "B -> C -> D -> C"
    }
    
    // print the cycle
    StringBuilder parentLoop = new StringBuilder();
    String delim = "";
    for (String pName : cycle) {
      parentLoop.append(delim).append(pName);
      delim = " > ";
    }
    
    return new Pair<String, String>(cycleParent, parentLoop.toString());
  }
  
  /**
   * A workaround for to address multi-thread problems of using singleton {@link CyclicParseManager}.
   * <p>
   * The issues arise when the section manager is cloned to be used in a different thread (e.g. for
   * parsing/printing some term). The CyclicParseManager is used in a singleton manner within the
   * section manager, and the shallow cloning keeps the same cyclic manager for the cloned section
   * manager. So if the parsing is done in multiple threads, the same cyclic manager is utilised and
   * runs into problems.
   * </p>
   * <p>
   * By using thread-local values we can address the multi-threading to some extent. The parsing is
   * usually done by a single thread. However, the whole "singleton in section manager" approach
   * should be reviewed.
   * </p>
   * TODO review singleton approach for CyclicParseManager
   * 
   * @author Andrius Velykis
   */
  private static class CyclicManagerSingleton {
    private ThreadLocal<CyclicParseManager> manager = new ThreadLocal<CyclicParseManager>();
  }
  
}