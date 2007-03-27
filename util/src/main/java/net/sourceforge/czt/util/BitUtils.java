/*
 * @(#)BitUtil.java    0.1 15jan2002
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
 *  15jan2002     ljsf     Create public version
 */
/*
 * BitUtils.java
 *
 * Created on 23 May 2005, 11:43
 */

package net.sourceforge.czt.util;

/**
 *
 *
 * /**
 *
 *
 * @pattern
 * @author Leo Freitas <leo@cs.york.ac.uk>
 * @version 0.1 15jan2002
 * @since JDK1.2.2
 */
public class BitUtils {
    
    public static final int MIN_BIT = 0;
    public static final int MAX_BIT = 31;    
    
    private BitUtils() {
    }
    
    public static void forceBit(int bit) throws IllegalArgumentException {
        if (!checkBit(bit))
            throw new IllegalArgumentException("Invalid bit! must be between [0..31]");
    }
    
    public static boolean checkBit(int bit) {
        return (bit >= MIN_BIT && bit <= MAX_BIT);
    }
    
    public static boolean isBitOn(int mask, int bit) {
        forceBit(bit);
        return ((mask & (1 << bit)) != 0);
    }
    
    public static int turnBitOn(int mask, int bit) {
        forceBit(bit);
        return (mask | (1 << bit));
    }
    
    public static int turnBitOff(int mask, int bit) {
        forceBit(bit);
        return (mask & ~(1 << bit));
    }
    
    public static int bitCount(int value, boolean on)  {
        int i, j;
        for ( i = MIN_BIT, j = 0; i <= MAX_BIT ; i++ ) {
            if ( ( on && isBitOn( value, i ) ) ||
                    ( !on && !isBitOn( value, i ) ) )
                j++;
        }
        return ( j );
    }
    
    public static int firstBit( int value, boolean on )  {
        int i;
        for ( i = MIN_BIT; i < MAX_BIT ; i++ ) {
            if ( ( on && isBitOn( value, i ) ) ||
                    ( !on && !isBitOn( value, i ) ) )
                break;
        }
        return ( i );
    }
        
    /**
     * Makes a bit mask containing the first bitCnt elements on.
     *
     * @methodtype command
     * @methodproperty primitive
     */
    public static int makeMask(int bitCnt) {
        forceBit(bitCnt);
        int result = 0;
        for (int i = 0; i <= bitCnt; i++) {
            result = turnBitOn(result, i);
        }
        return result;
    }
    
    public static int makeMask(int[] maskPos) {
        int result = 0;
        for (int i = 0; i < maskPos.length; i++) {
            forceBit(maskPos[i]);
            result = turnBitOn(result, maskPos[i]);
        }
        return result;
    }
    
    public static boolean[] getBits(int mask, int bitCnt) {
        forceBit(bitCnt);
        boolean[] result = new boolean[bitCnt+1];
        for(int i = MIN_BIT; i <= bitCnt; i++) {
            result[i] = isBitOn(mask, i);
        }
        return result;
    }
    
    public static boolean[] flipBits(boolean[] bits) {        
        boolean[] result = new boolean[bits.length];
        for(int i = 0; i < result.length; i++) {
            result[i] = !bits[i];
        }
        return result;
    }
}