package net.sourceforge.czt.z.util;

import static org.junit.Assert.*;

import java.util.Set;

import net.sourceforge.czt.util.Section;

import org.junit.Test;

//TODO: ADD LOADS MORE HERE PLEASE !!!
public class ZUtilsTest {

	@Test
	public void testParentsTransformationInv() {
		Set<String> set1 = Section.standardSections();
		String s1 = ZUtils.parentsAsString(set1);
		
		Set<String> set2 = ZUtils.parentsCSVAsSetOfString(s1);
		String s2 = ZUtils.parentsAsString(set2);
		
		Set<String> set3 = ZUtils.parentsCSVAsSetOfString(s1);
		Set<String> set4 = ZUtils.parentsCSVAsSetOfString(s2);
		
		assertEquals(set1, set2);
		assertEquals(set1, set3);
		assertEquals(set1, set4);
		assertEquals(set2, set3);
		assertEquals(set2, set4);
		assertEquals(set3, set4);
	}
}
