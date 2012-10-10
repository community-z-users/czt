package net.sourceforge.czt.parser.util;

import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import junit.framework.TestCase;

public class CyclicParserManagerTest extends TestCase
{

  public void testGetCycleForSection()
  {
    
    validateSectionCycle("A", 
        Arrays.asList("A", "B", "C", "A"), 
        Arrays.asList("A", "B", "C", "A"));
    
    validateSectionCycle("B", 
        Arrays.asList("A", "B", "C", "A"), 
        Arrays.asList("B", "C", "A", "B"));
    
    validateSectionCycle("A", 
        Arrays.asList("A", "B", "C", "B"), 
        Arrays.asList("A", "B", "C", "B"));
    
    validateSectionCycle("B", 
        Arrays.asList("A", "B", "C", "B"), 
        Arrays.asList("B", "C", "B"));
    
    validateSectionCycle("C", 
        Arrays.asList("A", "B", "C", "B"), 
        Arrays.asList("C", "B", "C"));
    
    validateSectionCycle("D", 
        Arrays.asList("A", "B", "C", "B"), 
        Collections.<String>emptyList());
    
    validateSectionCycle("A", 
        Collections.<String>emptyList(), 
        Collections.<String>emptyList());
    
    validateSectionCycle("A", 
        Arrays.asList("A"), 
        Arrays.asList("A"));
    
    validateSectionCycle("A", 
        Arrays.asList("A", "A"), 
        Arrays.asList("A", "A"));
    
    // this is actually an invalid cycle - the same section should
    // not be repeated, unless it is the last one (cycle)
    validateSectionCycle("B", 
        Arrays.asList("A", "B", "B", "C", "B"), 
        Arrays.asList("B", "B", "C", "B"));
  }
  
  private void validateSectionCycle(String section, List<String> cycle, List<String> expected)
  {
    List<String> sectCycle = CyclicParseManager.getCycleForSection(section, cycle);
    assertEquals("Section cycle invalid:\nsection: " + section + "\ncycle: " + cycle + "\n", 
        expected, sectCycle);
  }

}
