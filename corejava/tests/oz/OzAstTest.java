package oz;

import java.util.*;
import java.io.*;
import junit.framework.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.oz.ast.*;

import net.sourceforge.czt.oz.jaxb.JaxbContext;
import net.sourceforge.czt.oz.jaxb.JaxbXmlReader;
import net.sourceforge.czt.oz.jaxb.AstToJaxb;
import net.sourceforge.czt.base.jaxb.JaxbXmlWriter;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.util.XmlReader;
import net.sourceforge.czt.base.util.XmlWriter;

/**
 * Try creating an OZ ast
 */
public class OzAstTest extends TestCase {

    //the number of operations in the ClassPara
    final protected static int NUM_OP_BOXES = 5;
    final protected static int NUM_OPS = NUM_OP_BOXES + 2;

    protected OzFactory mOzFactory;
    protected ZFactory mZFactory;
    protected Spec mSpec;

    protected void setUp() {
	mSpec = null;
    }

    protected List list(Object o) {
	List aList = new ArrayList();
	aList.add(o);

	return aList;
    }

    protected void createAst() {

	mOzFactory = new net.sourceforge.czt.oz.impl.OzFactoryImpl();
	mZFactory = new net.sourceforge.czt.z.impl.ZFactoryImpl();	

	mSpec = mZFactory.createSpec();

	//the class name
	DeclName className = mZFactory.createDeclName("MyClass",
						      new ArrayList(),
						      "MyClass");

	//create formal parameters
	RefName xTypeRefName = mZFactory.createRefName("X",
						       new ArrayList(),
						       null);

	FormalParameters fp = 
	    mOzFactory.createFormalParameters(list(xTypeRefName));

	//create a visibility list
	DeclName xName = mZFactory.createDeclName("x", new ArrayList(), null);
	DeclName pxName = mZFactory.createDeclName("px", new ArrayList(), null);
	List vNameList = new ArrayList();	
	vNameList.add(xName);
	vNameList.add(pxName);
	StringListType sList = mOzFactory.createStringListType(vNameList);

	/*
	 * create a state schema with a variable declaration and
	 * secondary variable
	 */
	RefName xRefName = mZFactory.createRefName("x", new ArrayList(), null);
	RefName pxRefName = mZFactory.createRefName("px", new ArrayList(), null);

	RefExpr xTypeRefExpr = mZFactory.createRefExpr(xRefName,
						       new ArrayList(),
						       new Boolean(false));
	PowerExpr powerX = mZFactory.createPowerExpr(xTypeRefExpr);
	VarDecl xDecl = mZFactory.createVarDecl(list(xName), xTypeRefExpr);
	VarDecl pxDecl = mZFactory.createVarDecl(list(pxName), powerX);

	RefExpr xRefExpr = mZFactory.createRefExpr(xRefName,
						   new ArrayList(),
						   new Boolean(false));
	RefExpr pxRefExpr = mZFactory.createRefExpr(pxRefName,
						    new ArrayList(),
						    new Boolean(false));

	MemPred memPred = mZFactory.createMemPred(xRefExpr, 
						  pxRefExpr,
						  new Boolean(false));

	State state = mOzFactory.createState(list(xDecl),
					     list(pxDecl),
					     new ArrayList());

	//create the init operation
	TruePred truePred = mZFactory.createTruePred();
	InitialState init = mOzFactory.createInitialState(list(truePred));

	//create some operations
	DeclName xInName = mZFactory.createDeclName("x",
						    list(mZFactory.createInStroke()),
						    null);
	VarDecl xInDecl = mZFactory.createVarDecl(list(xInName), xTypeRefExpr);

	List opList = new ArrayList();
	for (int i = 0; i < NUM_OP_BOXES; i++) {
	    OperationBox box1 = mOzFactory.createOperationBox(sList,
							      list(xInDecl),
							      list(truePred));

	    Operation op = mOzFactory.createOperation(
	        mZFactory.createDeclName("op" + i, new ArrayList(), null),
		                         box1);

	    opList.add(op);
	}

	//create a parallel operation
	RefName refNameOp1 = mZFactory.createRefName("op1",
						     new ArrayList(),
						     null);
	RefName refNameOp2 = mZFactory.createRefName("op2",
						     new ArrayList(),
						     null);
	OperationExpr leftExpr =
	    mOzFactory.createOpPromotionExpr(null, refNameOp1);
	OperationExpr rightExpr =
	    mOzFactory.createOpPromotionExpr(null, refNameOp2);
	OperationExpr parallelOpExpr =
	    mOzFactory.createParallelOpExpr(leftExpr, rightExpr);
	Operation parallelOp =
	    mOzFactory.createOperation(
	        mZFactory.createDeclName("paraOp", new ArrayList(), null),
		                         parallelOpExpr);
	opList.add(parallelOp);

	//create a distibuted choice operation
	SchText schText = mZFactory.createSchText(list(xInDecl), truePred);
	OperationExpr promoteOpExpr =
	    mOzFactory.createOpPromotionExpr(null, refNameOp2);
	Operation distOp = 
	     mOzFactory.createOperation(
		 mZFactory.createDeclName("distOp", new ArrayList(), null),
		                          promoteOpExpr);
	opList.add(distOp);

	//create the class paragraph
	ClassPara classPara = mOzFactory.createClassPara(className,
							 fp,
							 sList,
							 new ArrayList(),
							 null,
							 state,
							 init,
							 opList);

 	ArrayList paras = new ArrayList();
 	paras.add(classPara);
 	ZSect section =
 	  mZFactory.createZSect("Specification", null, paras);
 
 	mSpec.getSect().add(section);

    }

    public void openXml() {

	//createAst();
	try {
	    XmlReader reader = new JaxbXmlReader();
	    mSpec = (Spec) reader.read(new java.io.File("MyClass.xml"));
	} catch(Exception e) {
	    e.printStackTrace();
	}
    }

    public void testAstNumberOfSect() {
	createAst();
	numberOfSectTest();
    }

    public void testXmlReadNumberOfSect() {
	openXml();
	numberOfSectTest();
    }

    public void testAstClassDetails() {
	createAst();
	classDetailsTest();
    }

    public void testXmlReadClassDetails() {
	openXml();
	classDetailsTest();
    }

    public void testAstXmlWriter() {
	createAst();
	xmlWriterTest();
    }

    public void testXmlReadXmlWriter() {
	openXml();
	xmlWriterTest();
    }

    protected void numberOfSectTest() {
	Assert.assertEquals(1, mSpec.getSect().size());
    }

    protected void xmlWriterTest() {
	XmlWriter writer = 
	    new JaxbXmlWriter(new AstToJaxb(), JaxbContext.PATH);

	try {
	    OutputStreamWriter outputStream
		= new OutputStreamWriter(new FileOutputStream("MyClass.xml"), "utf8");
	    writer.write(mSpec, outputStream);
	} catch (Throwable e) {
	    //    e.printStackTrace();
	    System.exit(-1);
	}
    }

    protected void classDetailsTest() {
	List sects = mSpec.getSect();
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
	Assert.assertEquals(1, state.getDecl().size());
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
}
