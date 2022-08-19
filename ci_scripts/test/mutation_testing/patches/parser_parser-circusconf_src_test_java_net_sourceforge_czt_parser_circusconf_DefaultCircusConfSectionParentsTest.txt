package net.sourceforge.czt.parser.circusconf;

import static org.junit.Assert.*;

import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.DefaultSectionParents;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.session.Dialect;
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
public class DefaultCircusConfSectionParentsTest {

	DefaultCircusConfSectionParentsCommand cmd_;
	@Before
	public void setUp() throws Exception {
		cmd_ = new DefaultCircusConfSectionParentsCommand();
	}

	@Test
	public void testCircusConfToolkit() {
		assertEquals(cmd_.defaultParents(Section.CIRCUSCONF_TOOLKIT.getName()), 
				ZUtils.parentsArgListAsSetOfString(Section.PRELUDE.getName(), 
									Section.CIRCUS_PRELUDE.getName(),
									Section.CIRCUSCONF_PRELUDE.getName()//, 
									//Section.STANDARD_TOOLKIT.getName()
									));
	}

	@Test
	public void testAnonymous() {
		assertEquals(cmd_.defaultParents(Section.ANONYMOUS.getName()), 
				ZUtils.parentsArgListAsSetOfString(
									Section.STANDARD_TOOLKIT.getName(), 
									Section.CIRCUS_TOOLKIT.getName(),
									Section.CIRCUSCONF_TOOLKIT.getName()));
	}
	
	@Test
	public void testMySect() {
		assertEquals(cmd_.defaultParents("my_sect"), 
				ZUtils.parentsArgListAsSetOfString(Section.PRELUDE.getName(), 
									Section.CIRCUS_PRELUDE.getName(),
									Section.CIRCUSCONF_PRELUDE.getName()//, 
									//Section.STANDARD_TOOLKIT.getName()
									));
		
		try
		{
			Key<DefaultSectionParents> k = new Key<DefaultSectionParents>("my_sect", DefaultSectionParents.class);
			SectionManager sm_ = new SectionManager(Dialect.CIRCUSCONF);
			DefaultSectionParents cmd2_ = sm_.get(k);
			
			assertEquals(cmd2_.defaultParents("my_sect"), 
					ZUtils.parentsArgListAsSetOfString(Section.PRELUDE.getName(), 
										Section.CIRCUS_PRELUDE.getName(),
										Section.CIRCUSCONF_PRELUDE.getName()
										));
		}
		catch (CommandException e)
		{
			fail("Shouldn't have thrown CommandException " + e.toString());
		}
	}
	
}
