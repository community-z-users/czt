/*
 * @(#)SystemProperties.java    0.1 01sep2001
 *
 * Copyright 2001 by Leonardo Freitas, UFPE
 * All rights reserved.
 * Av. Luis Freire s/n Recife, Pernambuco, Brazil.
 * CCEN CIn, Laboratory of Formal Methods
 * ljsf@cin.ufpe.br
 * http://www.cin.ufpe.br/~ljsf/java-csp
 *
 * @history
 *  When          Who      What
 *  01sep2001     ljsf     Create public version
 */
/*
 * SystemProperties.java
 *
 * Created on 17 May 2005, 12:50
 */
 
package net.sourceforge.czt.util;

/**
 * 
 *
 * @pattern 
 * @author Leo Freitas <leo@cs.york.ac.uk>
 * @version 0.1 01sep2001 
 * @since JDK1.2.2
 */
 
public interface CztSystemProperties {
   
	public final String LINE_BREAK = System.getProperty("line.separator");
	public final String LINE_BREAK_TAB = LINE_BREAK ;
	public final String FILE_SEPARATOR = System.getProperty("file.separator");
	public final String PATH_SEPARATOR = System.getProperty("path.separator");

	public final String USER_NAME = System.getProperty("user.name");
	public final String USER_HOME_DIR = System.getProperty("user.home");
	public final String USER_CURR_DIR = System.getProperty("user.dir");
}
