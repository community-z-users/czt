package net.sourceforge.czt.parser.circus;

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
public class DefaultCircusSectionParentsTest {

	DefaultCircusSectionParentsCommand cmd_;
	@Before
	public void setUp() throws Exception {
		cmd_ = new DefaultCircusSectionParentsCommand();
	}

	@Test
	public void testPrelude() {
		assertEquals(cmd_.defaultParents(Section.PRELUDE.getName()), Collections.EMPTY_SET);
	}

	@Test
	public void testSetToolkit() {
		assertEquals(cmd_.defaultParents(Section.SET_TOOLKIT.getName()), 
				ZUtils.parentsAsSet(Section.PRELUDE.getName()));
	}

	@Test
	public void testNumberToolkit() {
		assertEquals(cmd_.defaultParents(Section.NUMBER_TOOLKIT.getName()), 
				ZUtils.parentsAsSet(Section.PRELUDE.getName()));
	}

	@Test
	public void testRelationToolkit() {
		assertEquals(cmd_.defaultParents(Section.RELATION_TOOLKIT.getName()), 
				ZUtils.parentsAsSet(Section.PRELUDE.getName()
								//,Section.SET_TOOLKIT.getName()
								));
	}

	@Test
	public void testFunctionToolkit() {
		assertEquals(cmd_.defaultParents(Section.FUNCTION_TOOLKIT.getName()), 
				ZUtils.parentsAsSet(Section.PRELUDE.getName()
						//, Section.RELATION_TOOLKIT.getName()
						));
	}

	@Test
	public void testSequenceToolkit() {
		assertEquals(cmd_.defaultParents(Section.SEQUENCE_TOOLKIT.getName()), 
				ZUtils.parentsAsSet(Section.PRELUDE.getName()
						//,
									//Section.FUNCTION_TOOLKIT.getName(),
									//Section.NUMBER_TOOLKIT.getName()
									));
	}

	@Test
	public void testFuzzToolkit() {
		// don't include ZEVES prelude
		assertEquals(cmd_.defaultParents(Section.FUZZ_TOOLKIT.getName()), 
				ZUtils.parentsAsSet(Section.PRELUDE.getName()//, 
									//Section.STANDARD_TOOLKIT.getName()
						));
	}

	@Test
	public void testWhitespaceToolkit() {
		// don't include ZEVES prelude
		assertEquals(cmd_.defaultParents(Section.WHITESPACE.getName()), 
				ZUtils.parentsAsSet(Section.PRELUDE.getName()));
	}

	@Test
	public void testZStateToolkit() {
		// don't include ZEVES prelude
		assertEquals(cmd_.defaultParents(Section.ZSTATE_TOOLKIT.getName()), 
				ZUtils.parentsAsSet(Section.PRELUDE.getName()//, 
									//Section.STANDARD_TOOLKIT.getName()
						));
	}

	@Test
	public void testStandardToolkit() {
		// don't include ZEVES prelude
		assertEquals(cmd_.defaultParents(Section.STANDARD_TOOLKIT.getName()), 
				ZUtils.parentsAsSet(Section.PRELUDE.getName()//, 
									//Section.SEQUENCE_TOOLKIT.getName()
						));
	}
	
	@Test
	public void testCircusPrelude() {
		assertEquals(cmd_.defaultParents(Section.CIRCUS_PRELUDE.getName()), 
				ZUtils.parentsAsSet(Section.PRELUDE.getName()));
	}

	@Test
	public void testCircusToolkit() {
		// don't include ZEVES prelude
		assertEquals(cmd_.defaultParents(Section.CIRCUS_TOOLKIT.getName()), 
				ZUtils.parentsAsSet(Section.PRELUDE.getName(), 
									Section.CIRCUS_PRELUDE.getName()//, 
									//Section.STANDARD_TOOLKIT.getName()
									));
	}
	
	@Test
	public void testCircusBagToolkitSpivey() {
		// don't include ZEVES prelude
		assertEquals(cmd_.defaultParents("bag_toolkit_spivey"), 
				ZUtils.parentsAsSet(Section.PRELUDE.getName(), 
									Section.CIRCUS_PRELUDE.getName()//, 
									//Section.STANDARD_TOOLKIT.getName()
									));
	}

	@Test
	public void testAnonymous() {
		// don't include ZEVES prelude
		assertEquals(cmd_.defaultParents(Section.ANONYMOUS.getName()), 
				ZUtils.parentsAsSet(Section.PRELUDE.getName(), 
									Section.CIRCUS_PRELUDE.getName(), 
									Section.STANDARD_TOOLKIT.getName(), 
									Section.CIRCUS_TOOLKIT.getName()));
	}
	
	@Test
	public void testMySect() {
		// don't include ZEVES prelude
		assertEquals(cmd_.defaultParents("my_sect"), 
				ZUtils.parentsAsSet(Section.PRELUDE.getName(), 
									Section.CIRCUS_PRELUDE.getName()//, 
									//Section.STANDARD_TOOLKIT.getName()
									));
	}

}
