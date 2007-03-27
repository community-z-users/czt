/*
 * StrUtils.java
 *
 * Created on 05 May 2005, 14:51
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package net.sourceforge.czt.util;

import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.util.Arrays;
import java.util.Collection;
import java.util.Iterator;
import java.util.Map;
import java.util.StringTokenizer;

/**
 *
 * @author leo
 */
public class StrUtils implements CztSystemProperties {
    
    public static int DEFAULT_ASSTRING_TABCNT = 1;
    public static boolean DEFAULT_ASSTRING_LINE_BREAK = false;
    
    /** Creates a new instance of StrUtils */
    public StrUtils() {
    }
    
    public static String stripPackage(Class cls) {
        return stripPackage(cls.getName());
    }
    
    public static String stripPackage(Object obj) {
        return stripPackage(String.valueOf(obj));
    }
    
    public static String stripAddr(String str) {
        if (str.indexOf("@") != -1) {
            str = str.substring(0, str.indexOf("@"));
        }
        return str;
    }
    
    public static String stripPackage(String fromClsStr) {
        /*if (fromClsStr.lastIndexOf(".") != -1 && fromClsStr.indexOf("@") != -1) {
            fromClsStr = fromClsStr.substring(fromClsStr.lastIndexOf(".")+1, fromClsStr.indexOf("@"));
        }*/
        if (fromClsStr.lastIndexOf(".") != -1) {
            fromClsStr = fromClsStr.substring(fromClsStr.lastIndexOf(".")+1);
        }
        return fromClsStr;
    }
    
    public static String stringOfChar(char c, int count) {
        StringBuilder sb = new StringBuilder("");
        while (count > 0) {
            sb.append(c);
            count--;
        }
        return sb.toString();
    }
    
    public static String className(Object o)  {
        String r = "null";
        if (o != null)
            return className(o.getClass());
        return r;
    }
    
    public static String className(Class c)  {
        String r = "null";
        if (c != null)  {
            r = c.getName();
            // If it isn't an array
            if (!c.isArray())
                return stripPackage(r);
            // If it is an array
            Class ct = c.getComponentType();
            Class deepest = ct;
            while (ct != null && ct.isArray()) {
                ct = ct.getComponentType();
                if (ct != null)
                    deepest = ct;
            }
            // If it is a primitive array
            if (deepest.isPrimitive())
                return r;
            // Otherwise: it is a non primitive array.
            String s = r.substring(0, r.lastIndexOf('[')+2);
            r = stripPackage(r);
            r = s + r;
        }
        return r;
    }
    
    public static <K, V> String toString(Map<K, V> object, boolean linebreak, int tabCnt) {
        if (object == null)
            return "null";
        Iterator<Map.Entry<K, V>> it = object.entrySet().iterator();
        StringBuilder sb = new StringBuilder();
        sb.append("{ ");
        boolean hasElements = it.hasNext();
        String sep = (linebreak ? LINE_BREAK + stringOfChar('\t', tabCnt) : ", ");
        while (it.hasNext()) {
            Map.Entry entry = it.next();
            sb.append(toString(entry.getKey()));
            sb.append("=");
            sb.append(toString(entry.getValue()));
            sb.append(sep);
        }
        if (hasElements)
            sb.delete(sb.length()-sep.length(), sb.length());
        sb.append("} ");
        return sb.toString();
    }   
    
    public static <T> String toString(Collection<T> object, boolean linebreak, int tabCnt) {
        if (object == null)
            return "null";
        Iterator<?> it = object.iterator();
        StringBuilder sb = new StringBuilder();
        sb.append("{ ");
        boolean hasElements = it.hasNext();
        String sep = (linebreak ? LINE_BREAK + stringOfChar('\t', tabCnt) : ", ");
        while (it.hasNext()) {
            sb.append(toString(it.next()));
            sb.append(sep);
        }
        if (hasElements)
            sb.delete(sb.length()-sep.length(), sb.length());
        sb.append("} ");
        return sb.toString();
    }
    
    public static String toString(Throwable t) {
        StringBuilder builder = new StringBuilder();
        if (t != null) {            
            builder.append(StrUtils.className(t));
            builder.append(": ");
            builder.append(t.getMessage());                
            builder.append("\n");
            Throwable cause = t.getCause();
            while (cause != null) {
                builder.append("Caused by ");
                builder.append(StrUtils.className(cause));
                builder.append(": ");
                builder.append(cause.getMessage());                
                builder.append("\n");
                cause = cause.getCause();
            }                            
        } else {
            builder.append("null exception?");
        }                
        return builder.toString();
    }    
    
    public static String toString(Object object) {
        return (object != null ? 
            (object.getClass().isArray() ? 
                Arrays.toString((Object[])object) : 
                (object instanceof Method ? toString((Method)object) : 
                    (object instanceof Class ? toString((Class<?>)object) : object.toString()))) : "null");
    }    
    
    public static int DEFAULT_BREAKINDEX = 80;
    
    public static String formatLineForDebug(String line)  {
        return formatLineForDebug(DEFAULT_BREAKINDEX, line);
    }
    
    public static String formatLineForDebug(int breakIndex, String line)  {
        return formatLineForDebug(breakIndex, line, LINE_BREAK);
    }
    
    public static boolean checkStr(String source)  {
        return (source != null && source.length() > 0);
    }
    
    public static void forceStr(String source)
    throws IllegalArgumentException {
        if (!checkStr(source))
            throw new IllegalArgumentException( "Invalid string, it is either null or empty" );
    }
    
    public static String formatLineForDebug(int breakIndex, String line, String suffix)  {
        if (!checkStr(line) || line.length() < breakIndex)
            return line;
        StringBuilder sb = new StringBuilder(line);
        int round = 1;
        int length = line.length();
        while (length > breakIndex) {
            sb.insert(round * breakIndex, suffix);
            length -= breakIndex;
            round++;
        }
        return sb.toString();
    }
    
    public static String formatLineForDebug(String line, String breakTokens)  {
        return formatLineForDebug(line, breakTokens, LINE_BREAK);
    }
    
    public static String formatLineForDebug(String line, String breakTokens, String suffix) {
        if (!checkStr(line))
            return line;
        StringBuilder sb = new StringBuilder();        
        StringTokenizer st = new StringTokenizer(line, breakTokens);        
        while (st.hasMoreTokens()) {
            sb.append(st.nextToken());
            sb.append(suffix);
        }
        return sb.toString();
    }
    
    public static String padStr(String str) {
        return padStr(str, "\t", "\n");
    }
    
    /**
     * At each occurrence of "at" string in "str", pad it with the "pad" str.
     */
    public static String padStr(String str, String pad, String at) {
        StringBuilder builder = new StringBuilder();
        String[] lines = str.split(at);
        int i = 0;
        while (i < lines.length) {
            builder.append(pad);
            builder.append(lines[i]);            
            i++;
            if (i != lines.length) {
                builder.append(at);            
            }
        }
        return builder.toString();
    }
    
    public static String toString(Class<?> c) {
        return StrUtils.className(c);
    }
    
    private static final int LANGUAGE_MODIFIERS =
        Modifier.PUBLIC		| Modifier.PROTECTED	| Modifier.PRIVATE |
        Modifier.ABSTRACT	| Modifier.STATIC	| Modifier.FINAL   |
        Modifier.SYNCHRONIZED	| Modifier.NATIVE;
    
    public static String toString(Method m) {
        StringBuilder builder = new StringBuilder();
        
        int mod = m.getModifiers() & LANGUAGE_MODIFIERS;
        if (mod != 0) {
            builder.append(Modifier.toString(mod) + " ");
        }
        builder.append(toString(m.getReturnType()));
        builder.append(" ");
        builder.append(toString(m.getDeclaringClass()));
        builder.append(".");
        builder.append(m.getName());
        builder.append("(");
        builder.append(toString(m.getParameterTypes()));
        builder.append(")");
        return builder.toString();
    }
    
    
    
    public static <T> String toString(T[] t) {
        return toString(Arrays.asList(t));
    }
    
    public static <T> String toString(Collection<T> a) {
        StringBuilder builder = new StringBuilder("[");
        if (!a.isEmpty()) {
            Iterator<T> it = a.iterator();
            while (it.hasNext()) {
                builder.append(toString(it.next()));
                if (it.hasNext())
                    builder.append(", \n");
            }
        }
        builder.append("]");
        return builder.toString();
    } 
}
