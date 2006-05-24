/**
 * 
 */
package net.sourceforge.czt.eclipse.editors;

/**
 * /**
 * Definition of Z partitioning and its partitions.
 *
 * @since 3.1
 * 
 * @author Chengdong Xu
 */
public interface IZPartitions {

	/**
	 * The identifier of the Java partitioning.
	 */
	String Z_PARTITIONING= "___java_partitioning";  //$NON-NLS-1$

	/**
	 * The identifier of the single-line (JLS2: EndOfLineComment) end comment partition content type.
	 */
	String JAVA_SINGLE_LINE_COMMENT= "__java_singleline_comment"; //$NON-NLS-1$

	/**
	 * The identifier multi-line (JLS2: TraditionalComment) comment partition content type.
	 */
	String JAVA_MULTI_LINE_COMMENT= "__java_multiline_comment"; //$NON-NLS-1$

	/**
	 * The identifier of the Javadoc (JLS2: DocumentationComment) partition content type.
	 */
	String JAVA_DOC= "__java_javadoc"; //$NON-NLS-1$

	/**
	 * The identifier of the Java string partition content type.
	 */
	String JAVA_STRING= "__java_string"; //$NON-NLS-1$

	/**
	 * The identifier of the Java character partition content type.
	 */
	String JAVA_CHARACTER= "__java_character";  //$NON-NLS-1$
}
