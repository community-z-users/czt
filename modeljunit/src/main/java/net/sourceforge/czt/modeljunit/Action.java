package net.sourceforge.czt.modeljunit;

import java.lang.annotation.*;

/**
 * Indicates that the annotated method is a transition of an FSM.
 * This annotation should be used only on parameterless methods.
 */
@Retention(RetentionPolicy.RUNTIME)
@Target({ElementType.FIELD,ElementType.METHOD,ElementType.LOCAL_VARIABLE,ElementType.PARAMETER})
public @interface Action
{
}
