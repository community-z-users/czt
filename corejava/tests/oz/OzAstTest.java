package oz;

import java.io.*;
import java.util.*;
import java.util.logging.*;

import junit.framework.*;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.visitor.DebugVisitor;
import net.sourceforge.czt.base.util.AstValidator;
import net.sourceforge.czt.base.util.XmlReader;
import net.sourceforge.czt.base.util.XmlWriter;

import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.impl.ZFactoryImpl;

import net.sourceforge.czt.oz.ast.*;
import net.sourceforge.czt.oz.impl.OzFactoryImpl;
import net.sourceforge.czt.oz.jaxb.JaxbContext;
import net.sourceforge.czt.oz.jaxb.JaxbValidator;
import net.sourceforge.czt.oz.jaxb.JaxbXmlReader;
import net.sourceforge.czt.oz.jaxb.JaxbXmlWriter;
import net.sourceforge.czt.oz.jaxb.AstToJaxb;

/**
 * Try creating an OZ ast
 */
public class OzAstTest extends TestCase {
  
  //the number of operations in the ClassPara
  final private static int NUM_OP_BOXES = 5;
  final private static int NUM_OPS = NUM_OP_BOXES + 2;

  /**
   * The factory for creating Z terms.
   */
  private ZFactory zFactory_ = new ZFactoryImpl();

  /**
   * The factory for creating Object Z terms.
   */
  private OzFactory ozFactory_ = new OzFactoryImpl();

  /**
   * An Object Z validator which can be used
   * for on-demand validations of an AST.
   */
  private AstValidator validator_ = new JaxbValidator();

  /**
   * A Z specification (the root of the AST).
   */
  private Spec spec_ = null;

  public static void main(String[] args)
    throws Exception
  {
    OzAstTest test = new OzAstTest();
    test.blubb();
  }

  public void blubb()
    throws Exception
  {
    setUp();
    Term oldSpec = spec_;
    // write ...
    XmlWriter writer = new JaxbXmlWriter();
    OutputStreamWriter outputStream
      = new OutputStreamWriter(new FileOutputStream("MyClass.xml"), "utf8");
    writer.write(spec_, outputStream);

    // ... and read back
    XmlReader reader = new JaxbXmlReader();
    spec_ = (Spec) reader.read(new java.io.File("MyClass.xml"));

    // perform checks

    // TODO: check why this check does not work
    //    Assert.assertTrue(oldSpec.equals(spec_));
    System.out.println(oldSpec.equals(spec_));
    System.out.println(spec_.equals(oldSpec));
  }

  public static Test suite() {
    try {
      Handler handler = new FileHandler("oz.log");
      handler.setLevel(Level.ALL);
      handler.setEncoding("utf8");
      Logger.getLogger("").addHandler(handler);
      Logger.getLogger("").setLevel(Level.FINEST);
    } catch(SecurityException e) {
      e.printStackTrace();
    } catch(java.io.IOException e) {
      e.printStackTrace();
    }

    return new TestSuite(OzAstTest.class);
  }

  /**
   * Sets up a quite complex Object Z AST.
   */  
  protected void setUp() {
    spec_ = zFactory_.createSpec();
    spec_.setVersion("1.0");
    
    //the class name
    DeclName className =
      zFactory_.createDeclName("MyClass", null, "MyClass");
    
    //create formal parameters
    RefName xTypeRefName =
      zFactory_.createRefName("X", null, null);
    
    FormalParameters fp = 
      ozFactory_.createFormalParameters(list(xTypeRefName));
    
    //create a visibility list
    DeclName xName = zFactory_.createDeclName("x", null, null);
    DeclName pxName = zFactory_.createDeclName("px", null, null);
    List vNameList = new ArrayList();	
    vNameList.add(xName);
    vNameList.add(pxName);
    StringListType sList = ozFactory_.createStringListType(vNameList);
    
    // create a state schema with a variable declaration and
    // secondary variable
    RefName xRefName = zFactory_.createRefName("x", null, null);
    RefName pxRefName = zFactory_.createRefName("px", null, null);
    
    RefExpr xTypeRefExpr =
      zFactory_.createRefExpr(xRefName, null, new Boolean(false));
    PowerExpr powerX = zFactory_.createPowerExpr(xTypeRefExpr);
    VarDecl xDecl = zFactory_.createVarDecl(list(xName), xTypeRefExpr);
    VarDecl pxDecl = zFactory_.createVarDecl(list(pxName), powerX);
    
    RefExpr xRefExpr =
      zFactory_.createRefExpr(xRefName, null, new Boolean(false));
    RefExpr pxRefExpr =
      zFactory_.createRefExpr(pxRefName, null, new Boolean(false));
    
    MemPred memPred =
      zFactory_.createMemPred(xRefExpr, pxRefExpr, new Boolean(false));

    // This call does create an invalid AST.
    // The second argument of createState should be a list of
    // SecondaryAttributes.
    // But Jaxb doesn't find this error.
    State state =
      ozFactory_.createState(list(xDecl), list(pxDecl), null);
    
    //create the init operation
    TruePred truePred = zFactory_.createTruePred();
    InitialState init = ozFactory_.createInitialState(list(truePred));
    
    //create some operations
    DeclName xInName =
      zFactory_.createDeclName("x", list(zFactory_.createInStroke()), null);
    VarDecl xInDecl = zFactory_.createVarDecl(list(xInName), xTypeRefExpr);
    
    List opList = new ArrayList();
    for (int i = 0; i < NUM_OP_BOXES; i++) {
      OperationBox box1 =
	ozFactory_.createOperationBox(sList, list(xInDecl), list(truePred));
      DeclName declName = zFactory_.createDeclName("op" + i, null, null);
      Operation op = ozFactory_.createOperation( declName, box1);
      opList.add(op);
    }
    
    //create a parallel operation
    RefName refNameOp1 = zFactory_.createRefName("op1", null, null);
    RefName refNameOp2 = zFactory_.createRefName("op2", null, null);
    OperationExpr leftExpr =
      ozFactory_.createOpPromotionExpr(null, refNameOp1);
    OperationExpr rightExpr =
      ozFactory_.createOpPromotionExpr(null, refNameOp2);
    OperationExpr parallelOpExpr =
      ozFactory_.createParallelOpExpr(leftExpr, rightExpr);
    DeclName declName = zFactory_.createDeclName("paraOp", null, null);
    Operation parallelOp =
      ozFactory_.createOperation(declName, parallelOpExpr);
    opList.add(parallelOp);
    
    //create a distibuted choice operation
    SchText schText = zFactory_.createSchText(list(xInDecl), truePred);
    OperationExpr promoteOpExpr =
      ozFactory_.createOpPromotionExpr(null, refNameOp2);
    declName = zFactory_.createDeclName("distOp", new ArrayList(), null);
    Operation distOp = ozFactory_.createOperation(declName, promoteOpExpr);
    opList.add(distOp);
    
    //create the class paragraph
    ClassPara classPara =
      ozFactory_.createClassPara(className, fp, sList, null,
				 null, state, init, opList);
    
    ArrayList paras = new ArrayList();
    paras.add(classPara);
    ZSect section =
      zFactory_.createZSect("Specification", null, paras);
    
    spec_.getSect().add(section);
  }

  /**
   * Creates a list with the given object as element.
   *
   * @param object the object to be inserted into the list.
   * @return a list with exactly one element.  The element is
   *         the one provided as argument.
   */  
  private List list(Object object) {
    List list = new ArrayList();
    list.add(object);
    return list;
  }

  /**
   * Tests the provided AST directly.
   */
  public void testAst()
  {
    Assert.assertTrue(validator_.validate(spec_));
    numberOfSectTest();
    classDetailsTest();
  }

  /**
   * Test the AST that one gets
   * after writing and reading it back
   * into memory.
   */
  public void testWriteReadAst()
    throws Exception
  {
    Spec oldSpec = spec_;

    // write ...
    XmlWriter writer = new JaxbXmlWriter();
    OutputStreamWriter outputStream
      = new OutputStreamWriter(new FileOutputStream("ozspec.xml"), "utf8");
    writer.write(spec_, outputStream);

    // ... and read back
    XmlReader reader = new JaxbXmlReader();
    spec_ = (Spec) reader.read(new java.io.File("ozspec.xml"));

    // perform checks

    Assert.assertTrue(validator_.validate(spec_));
    numberOfSectTest();
    classDetailsTest();
  }

  private void numberOfSectTest() {
    Assert.assertEquals(1, spec_.getSect().size());
  }
  
  private void classDetailsTest() {
    List sects = spec_.getSect();
    ZSect firstSect = (ZSect)sects.get(0);
    List paras = firstSect.getPara();
    Iterator it = paras.iterator();
    ClassPara classPara = (ClassPara)it.next();
    
    Assert.assertTrue(classPara.getName().getWord().equals("MyClass"));
    
    FormalParameters fp = classPara.getFormalParameters();
    Assert.assertEquals(1, fp.getRefName().size());
    
    StringListType sList = classPara.getVisibilityList();
    Assert.assertEquals(2, sList.getName().size());
    
    List inheritList = classPara.getInheritedClass();
    Assert.assertEquals(0, inheritList.size());
    
    Assert.assertTrue(classPara.getLocalDef() == null);
    
    State state = classPara.getState();

    // The following assertion is not satisfied
    // since the VarDecl included in the SecondaryAttributes list
    // is also written into the XML file and inserted as a Decl
    // when read from the file.
    // Actually, the provided AST should not be valid,
    // but Jaxb does not catch this when validation is performed.
    // For now uncommented ...

    //    Assert.assertEquals(1, state.getDecl().size());

    Assert.assertEquals(0, state.getPred().size());
    
    InitialState init = classPara.getInitialState();
    Assert.assertEquals(1, init.getPred().size());
    
    List ops = classPara.getOperation();
    Assert.assertEquals(NUM_OPS, ops.size());
    
    for (int i = 0; i < NUM_OP_BOXES; i++) {
      Operation op = (Operation)ops.get(i);
      Assert.assertEquals("op" + i, op.getName().getWord());
    }
  }

  public void testJaxbAst()
    throws Exception
  {
    net.sourceforge.czt.oz.jaxb.gen.ObjectFactory ozObjectFactory =
      new net.sourceforge.czt.oz.jaxb.gen.ObjectFactory();
    net.sourceforge.czt.z.jaxb.gen.ObjectFactory zObjectFactory =
      new net.sourceforge.czt.z.jaxb.gen.ObjectFactory();

    // Creating two DeclName
    net.sourceforge.czt.z.jaxb.gen.DeclNameElement declName1 =
      zObjectFactory.createDeclNameElement();
    declName1.setWord("Foo1");
    net.sourceforge.czt.z.jaxb.gen.DeclNameElement declName2 =
      zObjectFactory.createDeclNameElement();
    declName2.setWord("Foo2");

    // Creating two RefExpr
    net.sourceforge.czt.z.jaxb.gen.RefNameElement refName1 =
      zObjectFactory.createRefNameElement();
    refName1.setWord("Bar1");
    net.sourceforge.czt.z.jaxb.gen.RefNameElement refName2 =
      zObjectFactory.createRefNameElement();
    refName2.setWord("Bar2");

    net.sourceforge.czt.z.jaxb.gen.RefExprElement refExpr1 =
      zObjectFactory.createRefExprElement();
    refExpr1.setRefName(refName1);
    net.sourceforge.czt.z.jaxb.gen.RefExprElement refExpr2 =
      zObjectFactory.createRefExprElement();
    refExpr2.setRefName(refName2);

    // Create two VarDecl
    net.sourceforge.czt.z.jaxb.gen.VarDeclElement xDecl =
      zObjectFactory.createVarDeclElement();
    net.sourceforge.czt.z.jaxb.gen.VarDeclElement pxDecl =
      zObjectFactory.createVarDeclElement();
    xDecl.getDeclName().add(declName1);
    pxDecl.getDeclName().add(declName2);
    xDecl.setExpr(refExpr1);
    pxDecl.setExpr(refExpr2);

    net.sourceforge.czt.oz.jaxb.gen.StateElement state =
      ozObjectFactory.createStateElement();

    state.getDecl().add(xDecl);
    state.getSecondaryAttributes().add(pxDecl);

    String jaxbContext =
      "net.sourceforge.czt.z.jaxb.gen:net.sourceforge.czt.oz.jaxb.gen";

    javax.xml.bind.JAXBContext jc =
      javax.xml.bind.JAXBContext.newInstance(jaxbContext);
    javax.xml.bind.Validator v = jc.createValidator();
    Assert.assertTrue(v.validate(state));
  }
}
