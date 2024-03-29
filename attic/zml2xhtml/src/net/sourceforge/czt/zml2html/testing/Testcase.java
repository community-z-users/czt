package net.sourceforge.czt.zml2html.testing;

import java.io.File;
import java.io.FileInputStream;
import java.io.InputStreamReader;
import java.io.BufferedReader;
import java.io.IOException;

import net.sourceforge.czt.zml2html.xml.*;

/**
 * A Testcase is a member of a Testset. A Testcase is based on a small specification
 * document that exists as a .zml files. Inside the Testcase class, the specification
 * it is based on is represented as a ZMLDocument instance.
 *
 * <p/>Each Testcase has a "status". The status may be one of
 *
 * <li>not evaluated</li>
 * <li>approved</li>
 * <li>failed</li>
 * <li>input changed</li>
 *
 * <p/>A Testcase is considered <i>not evaluated</i> if it has never been approved.
 * It is considered <i>approved</i> after it has been approved. When a <code>Testcase</code>
 * is approved, a copy is saved of its ZML input file. This copy is called the "approved input".
 * A copy is also saved of the output generated by applying the current version of the stylesheets.
 * This second copy is called the <code>Testcase</code>'s "approved output".
 * The two approved copies are represendted by the member <code>approvedTestcaseDoc</code>, which is an instance
 * of <code>ApprovedZMLDocument</code>.
 *
 * <p/>A <code>Testcase</code> is considered <i>failed</i> if its transformation output does not match
 * its approved output.
 *
 * <p/>A <code>Testcase</code> is considered <i>input changed</i> if its input ZML specification is not
 * the same as its approved output.
 *
 * @author Gerret Apelt
 */
public class Testcase
{
    public static final int STATUS_NOT_EVALUATED = 0;
    public static final int STATUS_APPROVED = 1;
    public static final int STATUS_DISAPPROVED = 2;
    public static final int STATUS_FAILED = 3;
    public static final int STATUS_INPUT_CHANGED = 4;


    private String name;
    private Testset parent;    

    private int status = -1;

    private ZMLDocument testcaseDoc;
    private ApprovedZMLDocument approvedTestcaseDoc;

    public Testcase(Testset parent, String name)
	throws IOException, XMLException
    {
	this.parent = parent;
	this.name = name;

	load();
    }

    /**
     * Sets the internal state of this <code>Testcase</code> by reading
     * the specification files it is associated with.
     *
     * <p/>The specification files are the "input" (typically a small zml specification)
     * and potentially the "approved input" and the "approved output".
     */
    public void load()
	throws IOException, XMLException
    {
	File testcaseInputFile = new File(getParent().dir, name+".zml");
	testcaseDoc = new ZMLDocument(testcaseInputFile);
	
	if (hasApprovedInputDocument()){
	    approvedTestcaseDoc =
		new ApprovedZMLDocument(new File(getParent().dir, name+".zml.approved"));
	}

	this.status = determineStatus();
    }

    public String getName()
    {
	return this.name;
    }

    public String getQualifiedName()
    {
	return getParent().getQualifiedName()+"_"+getName();
    }

    public Testset getParent()
    {
	return this.parent;
    }

    public String getGlobalName() {
	return parent.getGlobalName() + "_" + getName();
    }

    /**
     * Returns <code>true</code> if an approved input document exists in the filesystem,
     * else returns <code>false</code>.
     */
    public boolean hasApprovedInputDocument()
    {	
	return (new File(getParent().dir, getName()+".zml.approved")).exists();
    }

    /**
     * Marks the <code>Testcase</code> as approved by making a note in its ZML input,
     * and saves copies of its ZML input ("approved input") and of its current
     * output ("approved output").
     *
     * @todo Create approved input and approved output, specify inline format for
     * remembering when testcase was approved (and comments), override (delete) old
     * approved copies.
     */
    public void approve()
    {
	// ... do something to indicate approval, etc ...
	
	status = STATUS_APPROVED;
    }

    public void write()
	throws IOException, XMLException
    {
	testcaseDoc.write(new File(getParent().dir, getName()+".zml.write"));

	if (approvedTestcaseDoc != null) {
	    approvedTestcaseDoc.write(new File(getParent().dir, getName()+".zml.approved.write"));

	    XHTMLDocument htmlDoc = approvedTestcaseDoc.getApprovedOutput();
	    htmlDoc.write(new File(getParent().dir, getName()+".zml.approved.html"));
	}
    }

    public int addComment(String author, String text, String typeDesc)
    {
	Comment comment = new Comment(author, text, typeDesc);
	return testcaseDoc.addComment(comment);
    }

    /**
     * Returns one of STATUS_NOT_EVALUATED, STATUS_APPROVED, STATUS_FAILED,
     * or STATUS_INPUT_CHANGED.
     *
     * <p/>
     * IF document marked disapproved, THEN STATUS_DISAPPROVED
     * else
     * IF document not marked approved, THEN STATUS_NOT_EVALUATED
     * ELSE IF approved_document_exists (
     *   IF inputs_differ
     *     STATUS_INPUT_CHANGED
     *   ELSE IF output_differ
     *     STATUS_FAILED
     *   ELSE
     *     STATUS_PASSED
     * )
     *
     */
    private int determineStatus()
    {
	if (isDisapproved())
	    return STATUS_DISAPPROVED;
	else if (isApproved()) {
	    if (inputsDiffer()) {
		return STATUS_INPUT_CHANGED;
	    } else if (outputsDiffer()) {
		return STATUS_FAILED;
	    } else {
		return STATUS_APPROVED;
	    }	    
	}
	else {
	    return STATUS_NOT_EVALUATED;
	}
    }

    public boolean inputsDiffer()
    {
	return false;
    }

    public boolean outputsDiffer()
    {
	return false;
    }
    
    public boolean isDisapproved()
    {
	return testcaseDoc.comments.isDisapproved();
    }

    public boolean isApproved()
    {
	return testcaseDoc.comments.isApproved();
    }

    public int getStatus()
    {
	if (status == -1)
	    throw new RuntimeException("Internal Error: status has not been determined.");
	return status;
    }

    public ZMLDocument getTestcaseDoc()
    {
	return this.testcaseDoc;
    }
}






