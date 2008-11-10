package net.sourceforge.czt.modeljunit.timing;

import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

/**
 * Annotation for Timeouts. The parameter provided is the name of 
 * the action to call when the timeout expires.
 * @author Scott
 * 
 * eg. a timeout is declared as:
 * @Timeout("myAction") public int myTimer;
 * 
 * The action myAction will be triggered when the timeout is expired
 * 
 * Timeouts follow the following conventions:
 * value == 0 or -1						--> Not Set
 * value > 0 && value < current time	--> Set
 * value > current time					--> Expired
 *
 */


@Retention(RetentionPolicy.RUNTIME)
@Target(ElementType.FIELD)
public @interface Timeout {
	String value();
}
