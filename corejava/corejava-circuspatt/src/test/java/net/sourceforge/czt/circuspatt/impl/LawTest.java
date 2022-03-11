/*
 * LawTest.java
 *
 * Created on 12 June 2007, 15:31
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package net.sourceforge.czt.circuspatt.impl;

import java.util.List;
import junit.framework.Assert;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.ast.TermTest;
import net.sourceforge.czt.circus.ast.TransformerPred;
import net.sourceforge.czt.circuspatt.util.CircusLaw;
import net.sourceforge.czt.circuspatt.util.CircusLawVisitor;
import net.sourceforge.czt.circuspatt.util.CircusPattUtils;
import net.sourceforge.czt.circuspatt.util.Factory;
import net.sourceforge.czt.z.ast.Pred;

/**
 *
 * @author leo
 */
public abstract class LawTest extends TermTest {
    protected Factory factory_ = new Factory();
    
    public LawTest(String name) {
        super(name);
    }
        
    /**
     * An example visitor that visits Term objects.
     */
    static class ExampleCircusLawVisitor implements CircusLawVisitor<String>
    {
        public String visitCircusLaw(CircusLaw term) {
            String name = term.getName();
            Assert.assertTrue(term.isActionLaw() || term.isProcessLaw());
            return "Visted circus law " + name + ": HELLO WORLD!";
        }
    }
    
    public void testCircusLawVisitor(){
        Term term = createTerm();
        ExampleCircusLawVisitor visitor = new ExampleCircusLawVisitor();
        Assert.assertEquals("Visted circus law " + getLawName() + ": HELLO WORLD!", term.accept(visitor));
    }
    
    protected abstract String getLawName();    
    protected abstract List<? extends Pred> createProvisos();    
    protected abstract TransformerPred createTransformerPred();
    
    protected final Term createTerm() {               
        return CircusPattUtils.createCircusLaw(getLawName(),
            createTransformerPred(), createProvisos());
    }
}