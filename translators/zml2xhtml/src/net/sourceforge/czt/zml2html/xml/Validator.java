package net.sourceforge.czt.zml2html.xml;

/**
 * Validator instances determine whether a <code>SmartDocument</code>
 * is considered semantically correct.
 */
public interface Validator
{
    /*
     * Determines whether the given SmartDocument conforms to the rules
     * of this Validator.
     *
     * This method uses cached results if possible.
     *
     * @param inputDocument The document to be validated
     *
     * @return <code>true</code> if the document was validated,
     *   else false.
     *
     * @throws ValidationException if the validation
     *   could not be performed.
     */
    public boolean isValid(SmartDocument inputDocument)
	throws ValidationException;

    /**
     * Determines whether the given SmartDocument conforms to the rules of
     * this Validator. Cached results will be used depending on the value
     * of the forceValidation parameter.
     * 
     * @param inputDocument the document to be validated
     * @param forceValidation if <code>true</code>, the inputDocument
     *   will always be validated. if <code>false</code>, cached results
     *   may be used.
     * 
     * @return <code>true</code> if the inputDocument conforms to this Validator's
     *   rules, else <code>false</code>
     *
     * @throws ValidationException If errors were encountered during validation
     *
     */
    public boolean isValid(SmartDocument inputDocument, boolean forceValidation)
	throws ValidationException;

    /*
     * Returns an ActionReport describing the last validation
     * performed by the current instance.
     *
     * This method is typically called after val
     * has thrown an XMLException, and the error cause needs to be
     * analyzed.
     */
    public ActionReport getActionReport();
    
}
