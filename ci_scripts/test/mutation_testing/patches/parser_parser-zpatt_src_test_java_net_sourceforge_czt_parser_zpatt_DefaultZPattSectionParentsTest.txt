package net.sourceforge.czt.parser.zpatt;

import static org.junit.Assert.*;

import java.util.Collections;

import net.sourceforge.czt.util.Section;
import net.sourceforge.czt.z.util.ZUtils;

import org.junit.Before;
import org.junit.Test;

/**
 * Tests whether default parents are correct for various toolkits and user sections.
 * This is not a calculation of transitive parents, but rather transitive defaults.
 * Mostly this include preludes and possibly toolkits (for anonymous sections).
 * 
 * @author Leo Freitas
 *
 */
public class DefaultZPattSectionParentsTest {

	DefaultZPattSectionParentsCommand cmd_;
	@Before
	public void setUp() throws Exception {
		cmd_ = new DefaultZPattSectionParentsCommand();
	}

	@Test
	public void testPrelude() {
		assertEquals(cmd_.defaultParents(Section.PRELUDE.getName()), Collections.EMPTY_SET);
	}

	@Test
	public void testSetToolkit() {
		assertEquals(cmd_.defaultParents(Section.SET_TOOLKIT.getName()), 
				ZUtils.parentsArgListAsSetOfString(Section.PRELUDE.getName()));
	}

	@Test
	public void testNumberToolkit() {
		assertEquals(cmd_.defaultParents(Section.NUMBER_TOOLKIT.getName()), 
				ZUtils.parentsArgListAsSetOfString(Section.PRELUDE.getName()));
	}

	@Test
	public void testRelationToolkit() {
		assertEquals(cmd_.defaultParents(Section.RELATION_TOOLKIT.getName()), 
				ZUtils.parentsArgListAsSetOfString(Section.PRELUDE.getName()
								//,Section.SET_TOOLKIT.getName()
								));
	}

	@Test
	public void testFunctionToolkit() {
		assertEquals(cmd_.defaultParents(Section.FUNCTION_TOOLKIT.getName()), 
				ZUtils.parentsArgListAsSetOfString(Section.PRELUDE.getName()
						//, Section.RELATION_TOOLKIT.getName()
						));
	}

	@Test
	public void testSequenceToolkit() {
		assertEquals(cmd_.defaultParents(Section.SEQUENCE_TOOLKIT.getName()), 
				ZUtils.parentsArgListAsSetOfString(Section.PRELUDE.getName()
						//,
									//Section.FUNCTION_TOOLKIT.getName(),
									//Section.NUMBER_TOOLKIT.getName()
									));
	}

	@Test
	public void testFuzzToolkit() {
		// don't include ZEVES prelude
		assertEquals(cmd_.defaultParents(Section.FUZZ_TOOLKIT.getName()), 
				ZUtils.parentsArgListAsSetOfString(Section.PRELUDE.getName()//, 
									//Section.STANDARD_TOOLKIT.getName()
						));
	}

	@Test
	public void testWhitespaceToolkit() {
		// don't include ZEVES prelude
		assertEquals(cmd_.defaultParents(Section.WHITESPACE.getName()), 
				ZUtils.parentsArgListAsSetOfString(Section.PRELUDE.getName()));
	}

	@Test
	public void testZPatternToolkit() {
		// don't include ZEVES prelude
		assertEquals(cmd_.defaultParents(Section.ZPATT_TOOLKIT.getName()), 
				ZUtils.parentsArgListAsSetOfString(Section.PRELUDE.getName()//, 
									//Section.STANDARD_TOOLKIT.getName()
						));
	}

	@Test
	public void testOracleToolkit() {
		// don't include ZEVES prelude
		assertEquals(cmd_.defaultParents(Section.ORACLE_TOOLKIT.getName()), 
				ZUtils.parentsArgListAsSetOfString(Section.PRELUDE.getName()//, 
									//Section.STANDARD_TOOLKIT.getName()
						));
	}

	@Test
	public void testStandardToolkit() {
		// don't include ZEVES prelude
		assertEquals(cmd_.defaultParents(Section.STANDARD_TOOLKIT.getName()), 
				ZUtils.parentsArgListAsSetOfString(Section.PRELUDE.getName()//, 
									//Section.SEQUENCE_TOOLKIT.getName()
						));
	}
	
		@Test
	public void testAnonymous() {
		assertEquals(cmd_.defaultParents(Section.ANONYMOUS.getName()), 
				ZUtils.parentsArgListAsSetOfString( 
									Section.STANDARD_TOOLKIT.getName(),
									Section.ORACLE_TOOLKIT.getName()));
	}
	
	@Test
	public void testMySect() {
		assertEquals(cmd_.defaultParents("my_sect"), 
				ZUtils.parentsArgListAsSetOfString(Section.PRELUDE.getName()//, 
									//Section.STANDARD_TOOLKIT.getName()
									));
	}

}
