package net.sourceforge.czt.zeves.response;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import net.sourceforge.czt.base.util.PerformanceSettings;

import net.sourceforge.czt.zeves.response.form.ZEvesBlurb;

/**
 * A utility class that parses Z/EVES response trace (given as ZEvesBlurb object),
 * and partitions the results according to trace type. The parsed result can be
 * retrieved via {@link #getTraceContents()}, which gives a map from String text,
 * representing the trace type, to the associated content elements 
 * (e.g. Z/EVES constructs). The map preserves the parsing order, thus can be
 * printed back to get the original message (with corrected spacing). 
 * 
 * The class also provides access methods for elements of specific trace types,
 * so it could be queried, e.g., for REWRITE rules only.
 * 
 * @author Andrius Velykis
 */
public class ZEvesProofTrace
{
  
  public enum TraceType {
    /*
     * Beginning proof of<x/>...
     */
    BEGIN_PROOF("Beginning proof of"),
    /*
     * Applying<x/>gives ...
     * Applying<x/>to<x/>gives ...
     */
    APPLY("Applying"),
    /*
     * Applying<x/>to<x/>gives ...
     */
    APPLY_TARGET(APPLY, "to"),
    /*
     * Starting case1...
     * Starting case2...
     */
    CASE("Starting case"),
    /*
     * Completing all cases produces ...
     */
    CASE_COMPLETE("Completing all cases", "Completing case"),
    /*
     * The conjunctive normal form ...
     */
    CONJUNCTIVE("The conjunctive normal form"),
    /*
     * The disjunctive normal form ...
     */
    DISJUNCTIVE("The disjunctive normal form"),
    /*
     * Substitutingproduces ...
     * Substituting<x/>produces ...
     */
    EQUALITY_SUB("Substituting"),
    /*
     * Assuming<x/>with the instantiations:<x/><x/>generates ...
     */
    USE("Assuming"),
    /*
     * Instantiating<x/>gives ...
     * Assuming<x/>with the instantiations:<x/><x/>generates ...
     * Which simplifieswith invocation of<x/>when rewriting with<x/><x/>forward chaining using<x/><x/>with the assumptions<x/><x/>with the instantiation<x/>to ...
     * Which simplifieswith invocation of<x/>when rewriting with<x/><x/>forward chaining using<x/><x/>with the assumptions<x/><x/>with the instantiations<x/><x/>to ...
     */
    INSTANTIATE("Instantiating", "with the instantiations:", 
        "with the instantiations", "with the instantiation"),
    /*
     * Invoking<x/>gives ...
     * Which simplifieswith invocation of<x/>when rewriting with<x/><x/>forward chaining using<x/><x/>with the assumptions<x/><x/>to ...
     */
    INVOKE("Invoking", "with invocation of"),
    /*
     * Prenexing produces ...
     */
    PRENEX("Prenexing"),
    /*
     * Rearranging gives ...
     */
    REARRANGE("Rearranging"),
    /*
     * Splitting on<x/>generates ...
     */
    SPLIT("Splitting on"),
    /*
     * All below come from the rewrite chain traces:
     * 
     * Trivially simplifies to ...
     * Trivially rewrites using<x/>to ...
     * 
     * Which simplifiesforward chaining using<x/><x/>with the assumptions<x/><x/>to ...
     * Which simplifieswhen rewriting with<x/>forward chaining using<x/><x/>to ...
     * Which simplifieswhen rewriting with<x/>forward chaining using<x/><x/>with the assumptions<x/><x/>to ...
     * Which simplifieswith invocation of<x/>when rewriting with<x/><x/>forward chaining using<x/><x/>with the assumptions<x/><x/>to ...
     * Which simplifieswith invocation of<x/>when rewriting with<x/><x/>forward chaining using<x/><x/>with the assumptions<x/><x/>with the instantiation<x/>to ...
     * Which simplifieswith invocation of<x/>when rewriting with<x/><x/>forward chaining using<x/><x/>with the assumptions<x/><x/>with the instantiations<x/><x/>to ...
     */
    SIMPLIFY("Which simplifies", "Trivially simplifies"),
    REWRITE("when rewriting with", "Trivially rewrites using"),
    FRULE("forward chaining using"),
    GRULE("with the assumptions");
    
    private final List<String> texts;
    private final TraceType before;
    
    private TraceType(String... texts) {
      this(null, texts);
    }
    
    private TraceType(TraceType before, String... texts) {
      this.texts = Collections.unmodifiableList(Arrays.asList(texts));
      this.before = before;
    }
  }
  
  private static final String UNPRINTABLE_FORMULA = "an unprintable formula";
  
  private final Map<String, List<Object>> traceContents = new LinkedHashMap<String, List<Object>>();

  public ZEvesProofTrace(ZEvesBlurb info) {
    
    if (info != null) {
      parseContent(info);
    }
  }

  private void parseContent(ZEvesBlurb info)
  {
    
    String lastMatch = null;
    
    for (Iterator<?> it = info.getContent().iterator(); it.hasNext(); ) {
      
      Object elem = it.next();
      
      if (elem instanceof String) {

        lastMatch = parseText((String) elem, lastMatch, info);
        
        if (lastMatch == null && it.hasNext()) {
          // The text did not match, and is not the last 
          // element - thus it is unknown match
          throw new IllegalStateException("Unknown trace type or invalid Z/EVES response: "
              + info.toString());
        }
        
      } else if (lastMatch != null) {
        // not a String - so just add to the last type elements
        addTraceElement(lastMatch, elem);
      } else {
        // adding elements even though no type has been matched!
        throw new IllegalStateException("Unknown trace type or invalid Z/EVES response: " + info.toString());
      }
    }
  }
  
  private String parseText(String text, String lastMatch, ZEvesBlurb info) {
    
    /*
     * New trace content - we assume that the trace elements will be 
     * separated by Strings, which will define what the elements represent.
     */
    text = text.trim();
    
    do {
      
      text = checkSpecialStrings(text, lastMatch);
      
      lastMatch = matchText(text, lastMatch);
      
      if (lastMatch == null) {
        // nothing matched, thus use everything in the results, 
        // and nothing is left to parse
        markTrace(text, info);
        return null;
      }
      
      // the type might have matched just the beginning of the actual string
      // so get the remainder, and rerun the match
      // this is possible, e.g. with Substituting, and others
      
      markTrace(lastMatch, info);
      text = text.substring(lastMatch.length()).trim();
      
    } while (!text.isEmpty());
    
    // return the last matched
    return lastMatch;
  }
  
  private String checkSpecialStrings(String text, String lastMatch) {
    
    text = checkCaseNumber(text, lastMatch);
    
    text = checkUnprintableFormula(text, lastMatch);
    
    // nothing to adapt - continue with the whole text
    return text;
  }

  private String checkUnprintableFormula(String text, String lastMatch)
  {
    if (lastMatch != null && text.startsWith(UNPRINTABLE_FORMULA)) {
      // an unprintable formula can be embedded within another text,
      // e.g. Splitting onan unprintable formulagenerates ...
      addTraceElement(lastMatch, UNPRINTABLE_FORMULA);
      return text.substring(UNPRINTABLE_FORMULA.length());
    }
    
    return text;
  }

  private String checkCaseNumber(String text, String lastMatch)
  {
    if (TraceType.CASE.texts.contains(lastMatch) || TraceType.CASE_COMPLETE.texts.contains(lastMatch)) {
      // for CASE, the next can be a case number - try checking for it
      // the case number can be written as dot-separated sequence of digits,
      // e.g. 1.2.1
      StringBuilder nums = new StringBuilder();
      for (int index = 0; index < text.length(); index++) {
        char c = text.charAt(index);
        // check for digits and dots only
        if (Character.isDigit(c) || c == '.') {
          nums.append(c);
        } else {
          break;
        }
      }
      
      if (nums.length() > 0) {
        // found digits - remove trailing dots, because it can be "..." of the end of proof.
        String numsStr = nums.toString();
        if (numsStr.endsWith("...")) {
          numsStr = numsStr.substring(0, numsStr.length() - 3);
        }
        
        addTraceElement(lastMatch, numsStr);
        return text.substring(numsStr.length());
      }
    }
    
    return text;
  }
  
  private String matchText(String text, String lastMatched) {
    
    for (TraceType t : TraceType.values()) {
      for (String typeText : t.texts){
        if (text.startsWith(typeText)) {
          
          if (t.before == null || t.before.texts.contains(lastMatched)) {
            // either no before type is required, or it matches
            return typeText;
          }
        }
      }
    }
    
    return null;
  }
  
  private void markTrace(String text, ZEvesBlurb info) {
    
    if (traceContents.containsKey(text)) {
      throw new IllegalStateException("A trace type text '" + text
          + "' found multiple times in a Z/EVES response: " + info.toString());
    }
    
    // add an empty list for the text (either matched or the end)
    traceContents.put(text, new ArrayList<Object>(PerformanceSettings.INITIAL_ARRAY_CAPACITY));
  }
  
  private void addTraceElement(String traceText, Object elem) {
    List<Object> typeElems = traceContents.get(traceText);
    typeElems.add(elem);
  }
  
  /**
   * Retrieves Z/EVES trace elements for a particular trace type,
   * e.g. instantiations for INSTANTIATE, used lemmas for REWRITE, etc.
   * 
   * @param type
   * @return
   */
  public List<Object> getTraceElements(TraceType type) {
    
    List<Object> elems = new ArrayList<Object>(type.texts.size());
    for (String typeText : type.texts) {
      List<Object> textElems = traceContents.get(typeText);
      if (textElems != null) {
        elems.addAll(textElems);
      }
    }
    
    return elems;
  }
  
  /**
   * Retrieves trace contents - the parsed trace. The map preserves the order of original
   * text, and each pair represents a parse type (e.g. rewrite) and its associated
   * Z/EVES elements. 
   * 
   * @return
   */
  public Map<String, List<Object>> getTraceContents() {
    return Collections.unmodifiableMap(traceContents);
  }
  
  public boolean isEmpty() {
    return traceContents.isEmpty();
  }
  
}
