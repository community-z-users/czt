package net.sourceforge.czt.parser.z;

import static org.junit.Assert.*;

import java.util.List;

import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.Dialect;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.util.Section;
import net.sourceforge.czt.z.ast.Parent;
import net.sourceforge.czt.z.ast.Sect;
import net.sourceforge.czt.z.ast.Spec;
import net.sourceforge.czt.z.ast.ZSect;
import net.sourceforge.czt.z.util.Version;

import org.junit.After;
import org.junit.AfterClass;
import org.junit.BeforeClass;
import org.junit.Test;

import static net.sourceforge.czt.z.util.ZUtils.FACTORY;

/**
 * This class test a particular aspect of ZSect parse process. For on-the-fly specifications, a Spec
 * can be located in the section manager, however its sections not. In that case, a parse request
 * (in ParseUtils.doCompute()) finds a Spec under the requested name, and resolves its ZSects into
 * the section manager.
 * 
 * @author Andrius Velykis
 */
public class SectFromSpecParserTest
{

  private static SectionManager manager;
  
  @BeforeClass
  public static void setUpManager() throws Exception
  {
    manager = new SectionManager(Dialect.Z);
  }

  @AfterClass
  public static void tearDownManager() throws Exception
  {
    manager = null;
  }

  @After
  public void tearDown() throws Exception
  {
    // after each run, reset the manager
    manager.reset();
  }

  @Test
  public void testSingleNamedSect() throws CommandException
  {
    String name = "singleNamedSect";
   
    // test adding a spec with a single section, named after the requested key
    ZSect sect = createSect(name);
    Spec spec = createSpec(FACTORY.list(sect));
    
    Key<Spec> specKey = new Key<Spec>(name, Spec.class);
    manager.put(specKey, spec);
    
    // get the section with the spec name - must resolve
    ZSect result = manager.get(new Key<ZSect>(name, ZSect.class));
    
    // check its the same we put in
    assertSame(sect, result);
  }
  
  @Test
  public void testTwoNamedSectsFirst() throws CommandException
  {
    String name = "firstNamedSect";
    String name2 = "secondNamedSect";
   
    // create 2 specs, the first one is named correctly
    ZSect sect = createSect(name);
    ZSect sect2 = createSect(name2);
    Spec spec = createSpec(FACTORY.list(sect, sect2));
    
    Key<Spec> specKey = new Key<Spec>(name, Spec.class);
    manager.put(specKey, spec);
    
    // get the section with the spec name - must resolve
    ZSect result = manager.get(new Key<ZSect>(name, ZSect.class));
    
    // check its the same we put in
    assertSame(sect, result);
    
    // also check that we can get the second one
    Key<ZSect> key2 = new Key<ZSect>(name2, ZSect.class);
    assertTrue(manager.isCached(key2));
    ZSect result2 = manager.get(key2);
    assertSame(sect2, result2);
  }
  
  @Test
  public void testTwoNamedSectsSecond() throws CommandException
  {
    String name = "firstNamedSect";
    String name2 = "secondNamedSect";
   
    // create 2 specs, the second one is named correctly
    // basically testing that the order is not important
    ZSect sect = createSect(name);
    ZSect sect2 = createSect(name2);
    Spec spec = createSpec(FACTORY.list(sect2, sect));
    
    Key<Spec> specKey = new Key<Spec>(name, Spec.class);
    manager.put(specKey, spec);
    
    // get the section with the spec name - must resolve
    ZSect result = manager.get(new Key<ZSect>(name, ZSect.class));
    
    // check its the same we put in
    assertSame(sect, result);
    
    // also check that we can get the second one
    Key<ZSect> key2 = new Key<ZSect>(name2, ZSect.class);
    assertTrue(manager.isCached(key2));
    ZSect result2 = manager.get(key2);
    assertSame(sect2, result2);
  }
  
  @Test
  public void testAnonymousSect() throws CommandException
  {
    String name = "testAnonymous";
   
    // create 2 specs, the first one is named correctly
    ZSect sect = createSect(Section.ANONYMOUS.getName());
    Spec spec = createSpec(FACTORY.list(sect));
    
    // use custom key for spec
    Key<Spec> specKey = new Key<Spec>(name, Spec.class);
    manager.put(specKey, spec);
    
    // get the section with the spec name - must resolve
    // because it's anonymous, must get a correct one
    ZSect result = manager.get(new Key<ZSect>(name, ZSect.class));
    
    // check its the same we put in
    assertSame(sect, result);
    
    // also check that we can get it by its ANONYMOUS name
    Key<ZSect> key2 = new Key<ZSect>(Section.ANONYMOUS.getName(), ZSect.class);
    assertTrue(manager.isCached(key2));
    ZSect result2 = manager.get(key2);
    assertSame(sect, result2);
  }
  
  @Test
  public void testRedeclaredSects() throws CommandException
  {
    String name = "redeclaredSect";
   
    // create 2 specs with the same name
    ZSect sect = createSect(name);
    ZSect sect2 = createSect(name);
    Spec spec = createSpec(FACTORY.list(sect, sect2));
    
    Key<Spec> specKey = new Key<Spec>(name, Spec.class);
    manager.put(specKey, spec);
    
    // get the section with the spec name - must resolve
    ZSect result = manager.get(new Key<ZSect>(name, ZSect.class));
    
    // check its the second one - the first one will be ignored
    assertSame(sect2, result);
  }
  
  @Test (expected=CommandException.class)
  public void testEmptySpec() throws CommandException
  {
    String name = "emptySpec";
   
    // test with an empty spec - the ZSect will not be resolved
    Spec spec = createSpec(FACTORY.<Sect>list());
    
    Key<Spec> specKey = new Key<Spec>(name, Spec.class);
    manager.put(specKey, spec);
    
    // get the section with the spec name
    // must fail, no section resolved
    manager.get(new Key<ZSect>(name, ZSect.class));
  }
  
  @Test
  public void testNotFoundSect() throws CommandException
  {
    String name = "expectedSpec";
    String badName = "notfoundSpec";
   
    // Create a section with a name that's different from Spec key
    ZSect sect = createSect(badName);
    Spec spec = createSpec(FACTORY.list(sect));
    
    Key<Spec> specKey = new Key<Spec>(name, Spec.class);
    manager.put(specKey, spec);
    
    // get the section with the spec name
    // must fail, no section resolved
    try {
      manager.get(new Key<ZSect>(name, ZSect.class));
      fail("CommandException not thrown");
    }
    catch (CommandException e) {
      // exception thrown correctly
    }
    
    // also check that we can get the section by its bad name
    Key<ZSect> key2 = new Key<ZSect>(badName, ZSect.class);
    assertTrue(manager.isCached(key2));
    ZSect result2 = manager.get(key2);
    assertSame(sect, result2);
  }
  
  private ZSect createSect(String name) {
    // create empty ZSect
    return FACTORY.createZSect(name, FACTORY.<Parent>list(), FACTORY.createZParaList());
  }
  
  private Spec createSpec(List<? extends Sect> sects) {
    return FACTORY.createSpec(sects, Version.ZML_VERSION);
  }

}
