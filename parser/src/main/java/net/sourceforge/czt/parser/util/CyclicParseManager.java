package net.sourceforge.czt.parser.util;

import java.util.ArrayList;
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
  
  private static final Key<CyclicParseManager> CYCLIC_MANAGER_KEY = 
      new Key<CyclicParseManager>("cyclic-parse-manager", CyclicParseManager.class);
  
  /**
   * Retrieves the instance of {@link CyclicParseManager} for the given sectInfo. 
   * If one does not exist, it gets created and assigned to the sectInfo.
   * 
   * @param sectInfo Section manager
   * @return
   */
  public static CyclicParseManager getManager(SectionInfo sectInfo) {
    
    if (sectInfo.isCached(CYCLIC_MANAGER_KEY)) {
      try {
        return sectInfo.get(CYCLIC_MANAGER_KEY);
      }
      catch (CommandException e) {
        // should not happen
        throw new CztException(e);
      }
    }
    
    CyclicParseManager manager = new CyclicParseManager();
    sectInfo.put(CYCLIC_MANAGER_KEY, manager, null);
    
    return manager;
  }
  
  private final Stack<String> activeSects = new Stack<String>();
  
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
  public List<String> getValidParentNames(String section, List<String> parents) {
    
    assert section != null;
    
    activeSects.add(section);
    
    List<String> validParents = new ArrayList<String>();
    
    for (String parent : parents) {
      if (!activeSects.contains(parent)) {
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
   * @see #getValidParentNames(String, List)
   */
  public List<Parent> getValidParents(String section, List<Parent> parents) {
    
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
   * @see #getValidParents(String, List)
   */
  public void visitedParents(String section) {
    
    assert section != null;
    assert !activeSects.isEmpty() : "Section " + section + " has not been made active.";
    assert section.equals(activeSects.peek()) : "Section " + section
        + " cannot be made inactive, because section " + activeSects.peek()
        + " is currently activated.";
    
    activeSects.pop();
    
  }
}