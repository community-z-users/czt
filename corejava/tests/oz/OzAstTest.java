package oz;

import java.io.*;
import java.util.*;
import java.util.logging.*;

import junit.framework.*;

import net.sourceforge.czt.base.util.AstValidator;
import net.sourceforge.czt.base.util.XmlReader;
import net.sourceforge.czt.base.util.XmlWriter;

import net.sourceforge.czt.z.ast.*;

import net.sourceforge.czt.oz.ast.*;
import net.sourceforge.czt.oz.impl.OzFactoryImpl;
import net.sourceforge.czt.oz.jaxb.JaxbValidator;
import net.sourceforge.czt.oz.jaxb.JaxbXmlReader;
import net.sourceforge.czt.oz.jaxb.JaxbXmlWriter;

/**
 * Try creating an Object Z AST.
 */
public class OzAstTest extends TestCase
{
  //the number of operations in the ClassPara
  private static final int NUM_OP_BOXES = 5;
  private static final int NUM_OPS = NUM_OP_BOXES + 2;

  /**
   * The factory for creating (Object) Z terms.
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

  /**
   * Sets up a quite complex Object Z AST.
   */
  protected void setUp()
  {
    spec_ = ozFactory_.createSpec();
    spec_.setVersion("1.0");

    //the class name
    DeclName className =
      ozFactory_.createDeclName("MyClass", null, "MyClass");

    //create formal parameters
    DeclName xTypeDeclName =
      ozFactory_.createDeclName("X", null, null);

    FormalParameters fp =
      ozFactory_.createFormalParameters(list(xTypeDeclName));

    //create a visibility list
    RefName refName1 = ozFactory_.createRefName("x", null, null);
    RefName refName2 = ozFactory_.createRefName("px", null, null);
    List list = new ArrayList();
    list.add(refName1);
    list.add(refName2);
    RefNameList refNameList = ozFactory_.createRefNameList(list);

    DeclName xName = ozFactory_.createDeclName("x", null, null);
    DeclName pxName = ozFactory_.createDeclName("px", null, null);

    // create a state schema with a variable declaration and
    // secondary variable
    RefName xRefName = ozFactory_.createRefName("x", null, null);
    RefName pxRefName = ozFactory_.createRefName("px", null, null);

    RefExpr xTypeRefExpr =
      ozFactory_.createRefExpr(xRefName, null, new Boolean(false));
    PowerExpr powerX = ozFactory_.createPowerExpr(xTypeRefExpr);
    VarDecl xDecl = ozFactory_.createVarDecl(list(xName), xTypeRefExpr);
    VarDecl pxDecl = ozFactory_.createVarDecl(list(pxName), powerX);

    RefExpr xRefExpr =
      ozFactory_.createRefExpr(xRefName, null, new Boolean(false));
    RefExpr pxRefExpr =
      ozFactory_.createRefExpr(pxRefName, null, new Boolean(false));

    MemPred memPred =
      ozFactory_.createMemPred(xRefExpr, pxRefExpr, new Boolean(false));

    List declList = new ArrayList();
    declList.add(xDecl);
    declList.add(pxDecl);
    State state =
      ozFactory_.createState(declList, null, null);

    //create the init operation
    TruePred truePred = ozFactory_.createTruePred();
    InitialState init = ozFactory_.createInitialState(list(truePred));

    //create some operations
    DeclName xInName =
      ozFactory_.createDeclName("x", list(ozFactory_.createInStroke()), null);
    VarDecl xInDecl = ozFactory_.createVarDecl(list(xInName), xTypeRefExpr);

    List opList = new ArrayList();
    for (int i = 0; i < NUM_OP_BOXES; i++) {
      OperationBox box1 =
        ozFactory_.createOperationBox(refNameList,
                                      list(xInDecl),
                                      list(truePred));
      DeclName declName = ozFactory_.createDeclName("op" + i, null, null);
      Operation op = ozFactory_.createOperation(declName, box1);
      opList.add(op);
    }

    //create a parallel operation
    RefName refNameOp1 = ozFactory_.createRefName("op1", null, null);
    RefName refNameOp2 = ozFactory_.createRefName("op2", null, null);
    OperationExpr leftExpr =
      ozFactory_.createOpPromotionExpr(null, refNameOp1);
    OperationExpr rightExpr =
      ozFactory_.createOpPromotionExpr(null, refNameOp2);
    OperationExpr parallelOpExpr =
      ozFactory_.createParallelOpExpr(leftExpr, rightExpr);
    DeclName declName = ozFactory_.createDeclName("paraOp", null, null);
    Operation parallelOp =
      ozFactory_.createOperation(declName, parallelOpExpr);
    opList.add(parallelOp);

    //create a distibuted choice operation
    SchText schText = ozFactory_.createSchText(list(xInDecl), truePred);
    OperationExpr promoteOpExpr =
      ozFactory_.createOpPromotionExpr(null, refNameOp2);
    declName = ozFactory_.createDeclName("distOp", new ArrayList(), null);
    Operation distOp = ozFactory_.createOperation(declName, promoteOpExpr);
    opList.add(distOp);

    //create the class paragraph
    ClassPara classPara =
      ozFactory_.createClassPara(className, fp, refNameList, null,
                                 null, state, init, opList);

    ArrayList paras = new ArrayList();
    paras.add(classPara);
    ZSect section =
      ozFactory_.createZSect("Specification", null, paras);

    spec_.getSect().add(section);
  }

  /**
   * Creates a list with the given object as element.
   *
   * @param object the object to be inserted into the list.
   * @return a list with exactly one element.  The element is
   *         the one provided as argument.
   */
  private List list(Object object)
  {
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
    File tmpFile = File.createTempFile("cztOzAstTest", ".zml");
    tmpFile.deleteOnExit();
    Spec oldSpec = spec_;

    // write ...
    XmlWriter writer = new JaxbXmlWriter();
    OutputStreamWriter outputStream
      = new OutputStreamWriter(new FileOutputStream(tmpFile), "utf8");
    writer.write(spec_, outputStream);

    // ... and read back
    XmlReader reader = new JaxbXmlReader();
    spec_ = (Spec) reader.read(tmpFile);

    // perform checks
    Assert.assertEquals(oldSpec, spec_);
    Assert.assertTrue(validator_.validate(spec_));
    numberOfSectTest();
    classDetailsTest();
  }

  private void numberOfSectTest()
  {
    Assert.assertEquals(1, spec_.getSect().size());
  }

  private void classDetailsTest()
  {
    List sects = spec_.getSect();
    ZSect firstSect = (ZSect) sects.get(0);
    List paras = firstSect.getPara();
    Iterator it = paras.iterator();
    ClassPara classPara = (ClassPara) it.next();
    Assert.assertTrue(classPara.getName().getWord().equals("MyClass"));
    FormalParameters fp = classPara.getFormalParameters();
    Assert.assertEquals(1, fp.getName().size());
    RefNameList refNameList = classPara.getVisibilityList();
    Assert.assertEquals(2, refNameList.getName().size());
    List inheritList = classPara.getInheritedClass();
    Assert.assertEquals(0, inheritList.size());
    Assert.assertTrue(classPara.getLocalDef() == null);
    State state = classPara.getState();
    Assert.assertEquals(2, state.getDecl().size());
    Assert.assertEquals(0, state.getPred().size());
    InitialState init = classPara.getInitialState();
    Assert.assertEquals(1, init.getPred().size());
    List ops = classPara.getOperation();
    Assert.assertEquals(NUM_OPS, ops.size());
    for (int i = 0; i < NUM_OP_BOXES; i++) {
      Operation op = (Operation) ops.get(i);
      Assert.assertEquals("op" + i, op.getName().getWord());
    }
  }
}
