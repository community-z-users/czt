package net.sourceforge.czt.zml2html.testing;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FilenameFilter;
import java.io.IOException;

import java.util.List;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.Hashtable;
import java.util.Enumeration;

import net.sourceforge.czt.zml2html.xml.*;

/**
 * Testsets contain 0..MAX_TESTCASES testcases, and 0..MAX_CHILD_TESTSETS sub-testsets.
 *
 * Testsets are organized as a tree of Testsets. The root of the tree is the root testset.
 *
 * A testset has a name that is divided into a global and a local part. The local name
 * is the suffix of the global name. The global name is derived by concattenating
 * the names of a Testsets ancestors, down to the root.
 *
 * @todo: (1) Internally represent Testsets and Testcases as "something-other-than-array"
 *
 * @author Gerret Apelt
 */
public class Testset
{
    /* Maximum number of <code>Testcase</code>s that may be associated with the <code>Testset</code>. */
    public static final int MAX_TESTCASES = 100;

    /* Maximum number of <code>Testset</code>s that may be associated withthe <code>Testset</code>. */
    public static final int MAX_TESTSETS = 50;

    /* Maximum nesting depth of <code>Testset</code>s */
    public static final int MAX_TREE_DEPTH = 10;

    Testcase[] testcases = new Testcase[MAX_TESTCASES];
    Testset[] testsets = new Testset[MAX_TESTSETS];
    int testcaseCount = 0;
    int testsetCount = 0;

    Testset parent;
    boolean root = false;

    String name;            // name of this testset, e.g. "axdef"
    
    File dir; // the directory overseen by this Testset; may be empty

    public Testset(boolean root, Testset parent, File dir)
    {
	this.root = root;
	this.dir = dir;
	this.parent = parent;

	this.name = dir.getName();
    }

    public String getName()
    {
	return this.name;
    }

    public String getQualifiedName()
    {
	Iterator i = getAncestorsIterator();
	String lname = "";
	while (i.hasNext()) {
	    Testset ancestor = (Testset)i.next();
	    if (ancestor.getName() != "testcases")
		lname += ancestor.getName();
	    if (i.hasNext())
		lname += "_";
	}
	return lname;
    }
    
    /*
     * Adds a child Testset to the current Testset.
     */
    public void addTestset(Testset testset)
    {
	if (testsetCount == MAX_TESTSETS)
	    throw new RuntimeException("Trying to add a Testset to a Testset that has reached its maximum capacity.");
	testsets[testsetCount++] = testset;
    }

    /*
     * Add a Testcase to this TestSet.
     */
    public void addTestcase(Testcase testcase)
    {
	if (testsetCount == MAX_TESTCASES)
	    throw new RuntimeException("Trying to add a Testcase to a Testset that has reached its maximum capacity.");
	testcases[testcaseCount++] = testcase;
    }

    /*
     * given a local name for a Testcase, creates a corresponding Testcase 
     * (the filename for ZML testcase is inferred).
     */
    Testcase generateTestcase(String name)
	throws IOException, XMLException, TransformerException
    {
	Testcase t = new Testcase(this, name);
	//	addTestcase(t);
	return t;
    }

    /**
     * Computes the global name of the Testset within the test hierarchy.
     */
    public String getGlobalName()
    {
	Testset[] nameHierarchy = getAncestors();
	String globalName = "";
	
	for (int i = 0; i < nameHierarchy.length && nameHierarchy[i] != null; i++) {
	    globalName += nameHierarchy[i].getName();
	    if (i < nameHierarchy.length && nameHierarchy[i+1] != null)
		globalName += "_";
	}

	return globalName;	
    }

    /**
     * Retrieves an array containing the ancestor Testsets of this Testset,
     * beginning at index 0 with the root testset.
     */
    public Testset[] getAncestors() {
	Testset[] ancestors;

	if (root)
	    ancestors = new Testset[MAX_TREE_DEPTH];
	else
	    ancestors = parent.getAncestors();

	int myIndex = findFreeSlot(ancestors);
	ancestors[myIndex] = this;

	return ancestors;
    }

    public Iterator getAncestorsIterator()
    {
	List l = new ArrayList();
	Testset[] ancestors = getAncestors();
	for (int i = 0; i < ancestors.length && ancestors[i] != null; i++) {
	    l.add(ancestors[i]);
	}
	return l.iterator();
    }

    /*
     * Returns the index of the first free slot found in the given array,
     * or -1 if all slots are filled
     */ 
    public static int findFreeSlot(Object[] array)
    {
	for (int i = 0; i < array.length; i++) {
	    if (array[i] == null)
		return i;
	}
	return -1;
    }
   
    /*
     * Returns the named Testset. 
     */
    public Testset getTestset(String relativeName) 
    {
	int firstUnderscorePos = relativeName.indexOf('_');

	if (firstUnderscorePos == -1)
	    if (relativeName.equals(getName()))
		return this;
	    else
		throw new RuntimeException(relativeName + "is invalid");

	String localPortion = relativeName.substring(0, firstUnderscorePos);
	String beyondLocalPortion = relativeName.substring(firstUnderscorePos+1);       

	if (localPortion.equals(getName()) && beyondLocalPortion.indexOf('_') == -1) {	    
	    return getLocalTestset(beyondLocalPortion);
	}
	else {
	    //	    System.out.println("getting "+beyondLocalPortion+" from "+localPortion);
	    String childTestset = beyondLocalPortion.substring(0, beyondLocalPortion.indexOf('_'));
	    Testset containingTestset = getLocalTestset(childTestset);
	    return containingTestset.getTestset(beyondLocalPortion);
	}
    }

    /**
     * Returns the named Testcase.
     */
    public Testcase getTestcase(String relativeName)
    {
	int lastUnderscorePos = relativeName.lastIndexOf('_');

	if (lastUnderscorePos == -1) {
	    return getLocalTestcase(relativeName);
	} else {
	    String testsetName = relativeName.substring(0, lastUnderscorePos);
	    String testcaseName = relativeName.substring(lastUnderscorePos+1);
	    Testset testset = getTestset(testsetName);
	    return testset.getLocalTestcase(testcaseName);
	}
    }

    /*
     * Returns true if a Testcase by the given localName
     * exists at the current level
     */
    public boolean hasLocalTestcase(String localName)
    {	
	Testcase testcase;
	if ((testcase = getLocalTestcase(localName)) != null)
	    return true;
	return false;
    }

    /*
     * Returns the testcase named 'localName' at the current level
     * 
     */
    public Testcase getLocalTestcase(String localName)
    {
	for (int i = 0; i < testcases.length && testcases[i] != null; i++) {
	    if (testcases[i].getName().equals(localName))
		return testcases[i];
	}
	return null;
    }

    public boolean hasLocalTestset(String relativeName)
    {
	Testset testset;
	if ((testset = getTestset(relativeName)) != null)
	    return true;
	return false;
    }

    public Testset getLocalTestset(String relativeName)
    {
	for (int i = 0; i < testsets.length && testsets[i] != null; i++) {
	    if (testsets[i].name.equals(relativeName))
		return testsets[i];
	}
	return null;

    }

    public Iterator getTestcases()
    {
	ArrayList l = new ArrayList();
	for (int i = 0; i < testcaseCount; i++) {
	    Testcase testcase = testcases[i];
	    l.add(testcase);
	}
	return l.iterator();
    }

    public Iterator getTestsets()
    {
	ArrayList l = new ArrayList();
	for (int i = 0; i < testsetCount; i++) {
	    Testset testset = testsets[i];
	    l.add(testset);
	}
	return l.iterator();
    }

    /*
     * returns the testset hierarchy from the root to the level of the current testset
     */
    public String toString()
    {
	return "[Testset:"+getGlobalName()+"]";
    }

    /*
     * Filename Filter that accepts directories
     * and .ZML files
     */
    class ZmlRecurseFilter implements FilenameFilter
    {
	public boolean accept(File dir, String name) {
	    File childdir = new File(dir, name);
	    return ((childdir.isDirectory() && !name.equals("CVS")) || 
		(name.endsWith(".zml") &&
		 !name.startsWith(".") &&
		 !name.startsWith(".#")));
	}	
    }

    /*
     * Scans through all files and directories at the current level,
     * creating and registering objects for filenames and directories
     * where appropriate.
     * The scan reacts as follows to the three filetypes it differentiates:
     * 
     *  <li>directories: A new testset is created for the directory
     *  and the new testSet's populateDirectory method is called
     *  <li>filenames that represent testcases and contain further
     *  sublevels in the filename: A new testset is created for the
     *  first new level represented by the filename and the new
     *  testset's populateLevel method is called.
     *  <li>filenames that represent a testcase at the current level:
     *  A new testcase is created for the file and added to the current
     *  testset
     */
    public void populate(boolean recursive)
    {	
	File[] children = dir.listFiles(new ZmlRecurseFilter());
	for (int i=0; i<children.length; i++) {
	    File file = children[i];
	    if (file.isDirectory())	{
		Testset testset = new Testset(false, this, file);
		//		System.out.println("adding testset: "+testset.getGlobalName());
		if (recursive)
		    testset.populate(true);

		addTestset(testset);
	    }
	    else {
		Exception exception = null;
		try {
		    String testcaseName = file.getName().substring(0, file.getName().indexOf("."));
		    Testcase testcase = generateTestcase(testcaseName);		
		    //		    System.out.print("creating new testcase '"+testcase.getName()+"' at level "+ this.toString()+" ... ");
		    addTestcase(testcase);
		} catch (IOException ioe) {
		    exception = ioe;
		    System.out.println ("FAILED: I/O");
		} catch (XMLException xmle) {
		    exception = xmle;
		    xmle.printStackTrace();
		    throw new RuntimeException(xmle.getMessage());
		} catch (TransformerException te) {
		    exception = te;
		    System.out.println ("FAILED: transforming ZML specification");
		} finally {
		}
		
	    }
	}
    }

    /**
     * Some basic testing of the Testtree classes.
     */
    public static void main(String[] args)
    {
	String path = "testcases";
	if (args.length > 0)
	    path = args[0];

	File dir = new File(path);
	if (!dir.exists())
	    throw new RuntimeException(path+" does not exist!");

	Testset rootTestset = new Testset(true, null, dir);
	rootTestset.populate(true);

	Iterator it = rootTestset.getTestcases();
	//	System.out.println(ht.size()+" testcases at root.");
	while (it.hasNext()) {
	    Testcase t = (Testcase)it.next();
	    System.out.println(t.getName());
	    ZMLDocument testcaseDoc = t.getTestcaseDoc();
	    boolean valid = false;
	    ActionReport report;
	    try {
		valid = testcaseDoc.isValid();
	    } catch (ValidationException ve) {
		ve.printStackTrace();
	    } finally {
		report = testcaseDoc.getValidationActionReport();		
	    }
	    if (!valid) {
		System.out.println("Specification is not valid!!!");
		java.util.List messages = report.getMessages();
		java.util.Iterator i = messages.iterator();
		while (i.hasNext()) {
		    ActionMessage message = (ActionMessage)i.next();		    
		    System.out.println(message.toString());
		}
	    }

	    //	    CommentHashtable comments = testcaseDoc.comments;
	    //	    System.out.println(((Comment)comments.get(new Integer(1))).toString());
	    //	    t.addComment("Gerret", "another comment", "comment");
	    System.out.println(t.getStatus());

	}
	Testcase t1 = rootTestset.getTestcase("AndExpr");
	Testcase t2 = rootTestset.getTestcase("NoCommentsAndExpr");	          

	try {
	    ZMLDocument zml = t1.getTestcaseDoc();
	    zml.write(new File("/home/ga11/development/zml/zml2html/AndExpr.write"));
	} catch(XMLException xmle) {
	    xmle.printStackTrace();
	}
    }
}









