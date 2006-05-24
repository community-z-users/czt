/**
 * Created on 2005-10-13
 *
 * TODO To change the template for this generated file go to
 * Window - Preferences - Java - Code Style - Code Templates
 */
package net.sourceforge.czt.eclipse.util;

import org.eclipse.swt.graphics.RGB;

/**
 * Color keys used for syntax highlighting Java
 * code and Javadoc compliant comments.
 * A <code>IColorManager</code> is responsible for mapping
 * concrete colors to these keys.
 * <p>
 * This interface declares static final fields only; it is not intended to be
 * implemented.
 * </p>
 *
 * @see org.eclipse.jdt.ui.text.IColorManager
 * @see org.eclipse.jdt.ui.text.IColorManagerExtension
 
 * @author Chengdong Xu
 */
public interface IZColorConstants {
	public static final RGB DEFAULT= new RGB(0, 0, 0);
	public static final RGB SINGLE_LINE_COMMENT= new RGB(128, 128, 0);	
	public static final RGB MULTI_LINE_COMMENT= new RGB(128, 0, 0);
	public static final RGB KEYWORD= new RGB(64, 64, 128);
	public static final RGB TYPE= new RGB(0, 0, 128);
	public static final RGB STRING= new RGB(0, 128, 0);
	public static final RGB TAG = new RGB(0, 0, 128);
	public static final RGB PARAGRAPH = new RGB(128, 64, 0);
	public static final RGB PREDICATE = new RGB(128, 64, 0);
	public static final RGB SET = new RGB(128, 64, 0);
	public static final RGB RELATION = new RGB(128, 64, 0);
	public static final RGB FUNCTION = new RGB(128, 64, 0);
	public static final RGB SEQUENCE = new RGB(128, 64, 0);
	public static final RGB ARITHMETIC = new RGB(128, 64, 0);
	public static final RGB SCHEMA = new RGB(128, 64, 0);
	public static final RGB CONSTANT = new RGB(0, 0, 128);
	public static final RGB BACKGROUND = new RGB(64, 64, 64);
	
	/**
	 * Note: This constant is for internal use only. Clients should not use this constant.
	 * The prefix all color constants start with
	 * (value <code>"java_"</code>).
	 */
	String PREFIX= "java_"; //$NON-NLS-1$

	/** The color key for multi-line comments in Java code
	 * (value <code>"java_multi_line_comment"</code>).
	 */
	String JAVA_MULTI_LINE_COMMENT= "java_multi_line_comment"; //$NON-NLS-1$

	/** The color key for single-line comments in Java code
	 * (value <code>"java_single_line_comment"</code>).
	 */
	String JAVA_SINGLE_LINE_COMMENT= "java_single_line_comment"; //$NON-NLS-1$

	/** The color key for Java keywords in Java code
	 * (value <code>"java_keyword"</code>).
	 */
	String JAVA_KEYWORD= "java_keyword"; //$NON-NLS-1$

	/** The color key for string and character literals in Java code
	 * (value <code>"java_string"</code>).
	 */
	String JAVA_STRING= "java_string"; //$NON-NLS-1$

	/** The color key for method names in Java code
	 * (value <code>"java_method_name"</code>).
	 *
	 * @since 3.0
	 * @deprecated replaced as of 3.1 by an equivalent semantic highlighting, see {@link org.eclipse.jdt.internal.ui.javaeditor.SemanticHighlightings#METHOD}
	 */
	String JAVA_METHOD_NAME= "java_method_name"; //$NON-NLS-1$

	/** The color key for keyword 'return' in Java code
	 * (value <code>"java_keyword_return"</code>).
	 *
	 * @since 3.0
	 */
	String JAVA_KEYWORD_RETURN= "java_keyword_return"; //$NON-NLS-1$

	/** The color key for operators and brackets in Java code
	 * (value <code>"java_operator"</code>).
	 *
	 * @since 3.0
	 */
	String JAVA_OPERATOR= "java_operator"; //$NON-NLS-1$

	/**
	 * The color key for everything in Java code for which no other color is specified
	 * (value <code>"java_default"</code>).
	 */
	String JAVA_DEFAULT= "java_default"; //$NON-NLS-1$

	/**
	 * The color key for the Java built-in types such as <code>int</code> and <code>char</code> in Java code
	 * (value <code>"java_type"</code>).
	 *
	 * @deprecated no longer used, replaced by <code>JAVA_KEYWORD</code>
	 */
	String JAVA_TYPE= "java_type"; //$NON-NLS-1$

	/**
	 * The color key for annotations
	 * (value <code>"java_annotation"</code>).
	 *
	 * @since 3.1
	 */
	String JAVA_ANNOTATION= "java_annotation"; //$NON-NLS-1$

	/**
	 * The color key for task tags in java comments
	 * (value <code>"java_comment_task_tag"</code>).
	 *
	 * @since 2.1
	 */
	String TASK_TAG= "java_comment_task_tag"; //$NON-NLS-1$

	/**
	 * The color key for JavaDoc keywords (<code>@foo</code>) in JavaDoc comments
	 * (value <code>"java_doc_keyword"</code>).
	 */
	String JAVADOC_KEYWORD= "java_doc_keyword"; //$NON-NLS-1$

	/**
	 * The color key for HTML tags (<code>&lt;foo&gt;</code>) in JavaDoc comments
	 * (value <code>"java_doc_tag"</code>).
	 */
	String JAVADOC_TAG= "java_doc_tag"; //$NON-NLS-1$

	/**
	 * The color key for JavaDoc links (<code>{foo}</code>) in JavaDoc comments
	 * (value <code>"java_doc_link"</code>).
	 */
	String JAVADOC_LINK= "java_doc_link"; //$NON-NLS-1$

	/**
	 * The color key for everything in JavaDoc comments for which no other color is specified
	 * (value <code>"java_doc_default"</code>).
	 */
	String JAVADOC_DEFAULT= "java_doc_default"; //$NON-NLS-1$

	//---------- Properties File Editor ----------

	/**
	 * The color key for keys in a properties file
	 * (value <code>"pf_coloring_key"</code>).
	 *
	 * @since 3.1
	 */
	String PROPERTIES_FILE_COLORING_KEY= "pf_coloring_key"; //$NON-NLS-1$

	/**
	 * The color key for comments in a properties file
	 * (value <code>"pf_coloring_comment"</code>).
	 *
	 * @since 3.1
	 */

	String PROPERTIES_FILE_COLORING_COMMENT= "pf_coloring_comment"; //$NON-NLS-1$

	/**
	 * The color key for values in a properties file
	 * (value <code>"pf_coloring_value"</code>).
	 *
	 * @since 3.1
	 */
	String PROPERTIES_FILE_COLORING_VALUE= "pf_coloring_value"; //$NON-NLS-1$

	/**
	 * The color key for assignment in a properties file.
	 * (value <code>"pf_coloring_assignment"</code>).
	 *
	 * @since 3.1
	 */
	String PROPERTIES_FILE_COLORING_ASSIGNMENT= "pf_coloring_assignment"; //$NON-NLS-1$

	/**
	 * The color key for arguments in values in a properties file.
	 * (value <code>"pf_coloring_argument"</code>).
	 *
	 * @since 3.1
	 */
	String PROPERTIES_FILE_COLORING_ARGUMENT= "pf_coloring_argument"; //$NON-NLS-1$
}
