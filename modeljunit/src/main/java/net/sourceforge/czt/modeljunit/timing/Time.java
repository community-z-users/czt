package net.sourceforge.czt.modeljunit.timing;

import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;
import java.lang.annotation.ElementType;

/**
 * Time annotation for use in TimedModels. Each TimedModel should have
 * one integer field for the current time.
 * @author Scott
 *
 */

@Retention(RetentionPolicy.RUNTIME)
@Target(ElementType.FIELD)
public @interface Time {

}
