package net.sourceforge.czt.parser.z;

import static org.junit.Assert.*;

import java.util.Collections;

import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.DefaultSectionParents;
import net.sourceforge.czt.session.Dialect;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.SectionManager;
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
public class DefaultZSectionParentsTest {

	DefaultZSectionParentsCommand cmd1_;
	DefaultSectionParents cmd2_;
	SectionManager sm_;
	@Before
	public void setUp() throws Exception {
		cmd1_ = new DefaultZSectionParentsCommand();
		
		sm_ = new SectionManager(Dialect.Z);
	}

	@Test
	public void testPrelude() {
		assertEquals(cmd1_.defaultParents(Section.PRELUDE.getName()), Collections.EMPTY_SET);
	}

	@Test
	public void testSetToolkit() {
		assertEquals(cmd1_.defaultParents(Section.SET_TOOLKIT.getName()), 
				ZUtils.parentsArgListAsSetOfString(Section.PRELUDE.getName()));
	}

	@Test
	public void testNumberToolkit() {
		assertEquals(cmd1_.defaultParents(Section.NUMBER_TOOLKIT.getName()), 
				ZUtils.parentsArgListAsSetOfString(Section.PRELUDE.getName()));
	}

	@Test
	public void testRelationToolkit() {
		assertEquals(cmd1_.defaultParents(Section.RELATION_TOOLKIT.getName()), 
				ZUtils.parentsArgListAsSetOfString(Section.PRELUDE.getName()
								//,Section.SET_TOOLKIT.getName()
								));
	}

	@Test
	public void testFunctionToolkit() {
		assertEquals(cmd1_.defaultParents(Section.FUNCTION_TOOLKIT.getName()), 
				ZUtils.parentsArgListAsSetOfString(Section.PRELUDE.getName()
						//, Section.RELATION_TOOLKIT.getName()
						));
	}

	@Test
	public void testSequenceToolkit() {
		assertEquals(cmd1_.defaultParents(Section.SEQUENCE_TOOLKIT.getName()), 
				ZUtils.parentsArgListAsSetOfString(Section.PRELUDE.getName()
						//,
									//Section.FUNCTION_TOOLKIT.getName(),
									//Section.NUMBER_TOOLKIT.getName()
									));
	}

	@Test
	public void testFuzzToolkit() {
		// don't include ZEVES prelude
		assertEquals(cmd1_.defaultParents(Section.FUZZ_TOOLKIT.getName()), 
				ZUtils.parentsArgListAsSetOfString(Section.PRELUDE.getName()//, 
									//Section.STANDARD_TOOLKIT.getName()
						));
	}

	@Test
	public void testWhitespaceToolkit() {
		// don't include ZEVES prelude
		assertEquals(cmd1_.defaultParents(Section.WHITESPACE.getName()), 
				ZUtils.parentsArgListAsSetOfString(Section.PRELUDE.getName()));
	}

	@Test
	public void testStandardToolkit() {
		// don't include ZEVES prelude
		assertEquals(cmd1_.defaultParents(Section.STANDARD_TOOLKIT.getName()), 
				ZUtils.parentsArgListAsSetOfString(Section.PRELUDE.getName()//, 
									//Section.SEQUENCE_TOOLKIT.getName()
						));
	}
	
		@Test
	public void testAnonymous() {
		// don't include ZEVES prelude
		assertEquals(cmd1_.defaultParents(Section.ANONYMOUS.getName()), 
				ZUtils.parentsArgListAsSetOfString(
									Section.STANDARD_TOOLKIT.getName()));
	}
	
	@Test
	public void testMySect() {
		// this test is for a section without parents.
		// if any parent is available, then that's what is added.
		assertEquals(cmd1_.defaultParents("my_sect"), 
				ZUtils.parentsArgListAsSetOfString(Section.PRELUDE.getName()//, 
									//Section.STANDARD_TOOLKIT.getName()
									));
		
		try
		{
			Key<DefaultSectionParents> k = new Key<DefaultSectionParents>("my_sect", DefaultSectionParents.class);
			cmd2_ = sm_.get(k);
			
			assertEquals(cmd2_.defaultParents("my_sect"), 
					ZUtils.parentsArgListAsSetOfString(Section.PRELUDE.getName()//, 
										//Section.STANDARD_TOOLKIT.getName()
										));
		}
		catch (CommandException e)
		{
			fail("Shouldn't have thrown CommandException " + e.toString());
		}
	}
	
	@Test
	public void testWrongDialect() {
		try
		{
			Key<DefaultSectionParents> k = new Key<DefaultSectionParents>("my_sect", DefaultSectionParents.class);
			SectionManager wd = new SectionManager(Dialect.CIRCUS);
			cmd2_ = wd.get(k);
			
			assertEquals(cmd2_.defaultParents("my_sect"), 
					ZUtils.parentsArgListAsSetOfString(Section.PRELUDE.getName()//, 
										//Section.STANDARD_TOOLKIT.getName()
										));
		}
		catch (CommandException e)
		{
			// all is okay because exception was about wrong dialect.
			return;
		}
		fail("Shouldn't have thrown CommandException about wrong dialect used");
	}
}
