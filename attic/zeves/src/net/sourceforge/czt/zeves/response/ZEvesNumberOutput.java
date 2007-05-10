/*
 * ZEvesNumberOutput.java
 *
 * Created on 21 September 2005, 14:36
 */

package net.sourceforge.czt.zeves.response;

/**
 *
 * @author leo
 */
public class ZEvesNumberOutput extends AbstractZEvesOutput<Integer> {
    
    private final Integer fNumber;
    
    /** Creates a new instance of ZEvesNumberOutput */
    public ZEvesNumberOutput(int number) {
        fNumber = number;
    }
    
    public Integer getOutput() {
        return fNumber;
    }    
}
