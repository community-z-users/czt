package net.sourceforge.czt.zml2html.xml;

import java.util.List;

/**
 * Simple concrete implementation of ActionReport.
 *
 * GenericActionReport makes the abstract
 * implementation of interface ActionReport concrete
 * without adding any additional features.
 *
 * That is, actions can report ActionMessage objects,
 * but more detailed error or status information cannot be
 * passed.
 *
 */
public class GenericActionReport extends AbstractActionReport
{
    public GenericActionReport(String description)
    {
	super(description);
    }

    public GenericActionReport(String description, List actionMessageStore)
    {
	super(description, actionMessageStore);
    }
}
