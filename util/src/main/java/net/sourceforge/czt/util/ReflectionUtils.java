/* 
 * ReflectionUtils.java
 *
 * Created on 26 March 2007, 18:48
 */
package net.sourceforge.czt.util;

import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Set;

/**
 *
 * @author leo
 */
public class ReflectionUtils {
    
    /** Creates a new instance of ReflectionUtils */
    private ReflectionUtils() {
    }    
    
       
    
    public static List<Class<?>> transitiveSuperClasses(Object o) {
        return transitiveSuperClasses(o.getClass().getSuperclass());
    }
    
    public static List<Class<?>> reflexiveTransitiveSuperClasses(Object o) {
        return transitiveSuperClasses(o.getClass());
    }
    
    public static List<Class<?>> transitiveSuperClasses(Class<?> cls) {
        List<Class<?>> result = new ArrayList<Class<?>>();
        while (cls != null) {
            if (!result.contains(cls)) {
                result.add(cls);
            }
            cls = cls.getSuperclass();
        }
        return result;
    }
    
    protected static List<Class<?>> transitiveInterfaces(Class<?>... cls) {
        List<Class<?>> result = new ArrayList<Class<?>>();
        List<Class<?>> partialResult;
        for(Class<?> intf : cls) {
            partialResult = transitiveInterfaces(intf.getInterfaces());
            for(Class<?> superIntf : partialResult) {
                if (!result.contains(superIntf)) {
                    result.add(superIntf);
                }
            }
            if (!result.contains(intf)) {
                result.add(intf);
            }
        }
        return result;
    }
    
    public static List<Class<?>> reflexiveTransitiveInterfaces(Object o) {
        return transitiveInterfaces(o.getClass());
    }
    
    public static List<Class<?>> transitiveInterfaces(Object o) {
        return transitiveInterfaces(o.getClass().getSuperclass());
    }
    
    public static List<Class<?>> transitiveInterfaces(Class<?> cls) {
        List<Class<?>> result = new ArrayList<Class<?>>();
        List<Class<?>> partialResult;
        while (cls != null) {
            partialResult = transitiveInterfaces(cls.getInterfaces());
            for(Class<?> intf : partialResult) {
                if (!result.contains(intf)) {
                    result.add(intf);
                }
            }
            cls = cls.getSuperclass();
        }
        return result;
    }
    
    // to minimise search within method just for its name map MethodName->Method ?
    public static Set<Method> getAllMethodsFrom(Object o, String startingWith) {
        List<Method> result = new ArrayList<Method>();
        
        // collect all super classes up to Object considering o itself
        List<Class<?>> superCls = reflexiveTransitiveSuperClasses(o);
        
        Set<Method> allPublicMethods = new HashSet<Method>();
        for(Class<?> cls : superCls) {
            for(Method m : o.getClass().getMethods()) {
                if (m.getName().startsWith(startingWith)) {
                    allPublicMethods.add(m);
                }
            }
        }
        return allPublicMethods;
    }
    
    public static Set<Class<?>> getAllInterfacesFrom(Object o, String endingWith) {
        // collect all super classes up to Object considering o itself
        List<Class<?>> superIntf = reflexiveTransitiveInterfaces(o);
        
        Set<Class<?>> allInterfaces = new HashSet<Class<?>>();
        for(Class<?> cls : superIntf) {
            if (cls.getName().endsWith(endingWith)) {
                allInterfaces.add(cls);
            }
        }
        return allInterfaces;
    }        
    
/*    
    public static void main(String[] args) {
        Object o = new Object();
        List<String> l = new ArrayList<String>();

        System.out.println("o.getClass().getInterfaces() = \n\t" +
            Arrays.toString(o.getClass().getInterfaces()));
        System.out.println("o.getClass().getClasses() = \n\t" +
            Arrays.toString(o.getClass().getClasses()));
        System.out.println("o.getClass().getDeclaredClasses() = \n\t" +
            Arrays.toString(o.getClass().getDeclaredClasses()));
        System.out.println("o.getClass().getDeclaringClass() = \n\t" +
            o.getClass().getDeclaringClass());
        System.out.println("o.getClass().getEnclosingClass() = \n\t" +
            o.getClass().getEnclosingClass());
        System.out.println("o.getClass().getSuperclass() = \n\t" +
            o.getClass().getSuperclass());
        System.out.println("o.getClass().getTypeParameters() = \n\t" +
            Arrays.toString(o.getClass().getTypeParameters()));
 
        System.out.println("l.getClass().getInterfaces() = \n\t" +
            Arrays.toString(l.getClass().getInterfaces()));
        System.out.println("l.getClass().getClasses() = \n\t" +
            Arrays.toString(l.getClass().getClasses()));
        System.out.println("l.getClass().getDeclaredClasses() = \n\t" +
            Arrays.toString(l.getClass().getDeclaredClasses()));
        System.out.println("l.getClass().getDeclaredClasses() = \n\t" +
            Arrays.toString(l.getClass().getDeclaredClasses()));
        System.out.println("l.getClass().getDeclaringClass() = \n\t" +
            l.getClass().getDeclaringClass());
        System.out.println("l.getClass().getEnclosingClass() = \n\t" +
            l.getClass().getEnclosingClass());
        System.out.println("l.getClass().getSuperclass() = \n\t" +
            l.getClass().getSuperclass());
        System.out.println("l.getClass().getTypeParameters() = \n\t" +
            Arrays.toString(l.getClass().getTypeParameters()));
 
        System.out.println("l.getClass().getInterfaces()[0].getSuperClass() = \n\t" +
            l.getClass().getInterfaces()[0].getSuperclass());
        System.out.println("l.getClass().getInterfaces()[0].getInterfaces() = \n\t" +
            Arrays.toString(l.getClass().getInterfaces()[0].getInterfaces()));
 
        System.out.println("List.class.getInterfaces() = \n\t" +
            Arrays.toString(List.class.getInterfaces()));
        System.out.println("List.class.getInterfaces()[0].getInterfaces() = \n\t" +
            Arrays.toString(List.class.getInterfaces()[0].getInterfaces()));
        System.out.println("List.class.getInterfaces()[0].getInterfaces()[0].getInterfaces() = \n\t" +
            Arrays.toString(List.class.getInterfaces()[0].getInterfaces()[0].getInterfaces()));
        System.out.println("List.class.getClasses() = \n\t" +
            Arrays.toString(List.class.getClasses()));
        System.out.println("List.class.getDeclaredClasses() = \n\t" +
            Arrays.toString(List.class.getDeclaredClasses()));
        System.out.println("List.class.getDeclaredClasses() = \n\t" +
            Arrays.toString(List.class.getDeclaredClasses()));
        System.out.println("List.class.getDeclaringClass() = \n\t" +
            List.class.getDeclaringClass());
        System.out.println("List.class.getEnclosingClass() = \n\t" +
            List.class.getEnclosingClass());
        System.out.println("List.class.getSuperclass() = \n\t" +
            List.class.getSuperclass());
        System.out.println("List.class.getTypeParameters() = \n\t" +
            Arrays.toString(List.class.getTypeParameters()));
 
        System.out.println("\n\ntransitiveSuperClasses(o) = \n\t" +
            toString(transitiveSuperClasses(o)));
        System.out.println("transitiveInterfaces(o) = \n\t" +
            toString(transitiveInterfaces(o)));
 
        System.out.println("transitiveSuperClasses(l) = \n\t" +
            toString(transitiveSuperClasses(l)));
        System.out.println("reflexiveTransitiveSuperClasses(l) = \n\t" +
            toString(reflexiveTransitiveSuperClasses(l)));
        System.out.println("transitiveInterfaces(l) = \n\t" +
            toString(transitiveInterfaces(l)));
        System.out.println("reflexiveTransitiveInterfaces(l) = \n\t" +
            toString(reflexiveTransitiveInterfaces(l)));
 
        System.out.println("l.getClass().getMethods() = \n\t" +
            toString(l.getClass().getMethods()));
        System.out.println("l.getClass().getDeclaredMethods() = \n\t" +
            toString(l.getClass().getDeclaredMethods()));
 
        System.out.println("Enabled2.class.getMethods() = \n\t" +
            toString(Enabled2.class.getMethods()));
        System.out.println("\n\nEnabled2.class.getDeclaredMethods() = \n\t" +
            toString(Enabled2.class.getDeclaredMethods()));
        FreeVariablesCollector fvc = new FreeVariablesCollector();
        Enabled2 enabled = new Enabled2(CircusCompiler.getCircusCompiler());
        //VisitorUtils.checkVisitorRules(enabled);
        boolean ok = checkVisitorRules(enabled);
        System.out.println(ok);
        ok = checkVisitorRules(fvc);
        System.out.println(ok);
 
    }
 */          
}
