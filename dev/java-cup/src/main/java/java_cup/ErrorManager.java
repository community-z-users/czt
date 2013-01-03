
package java_cup;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import java_cup.runtime.ComplexSymbolFactory.ComplexSymbol;
import java_cup.runtime.ComplexSymbolFactory.Location;
import java_cup.runtime.Symbol;

public class ErrorManager{
    private static ErrorManager errorManager;
    private final List<CupLogMessage> errors = new ArrayList<CupLogMessage>();
    private final List<CupLogMessage> warnings = new ArrayList<CupLogMessage>();
    private final List<CupLogMessage> fatals = new ArrayList<CupLogMessage>();
    public int getFatalCount() { return fatals.size(); }
    public int getErrorCount() { return errors.size(); }
    public int getWarningCount() { return warnings.size(); }
    
    public List<CupLogMessage> getErrors() {
        return Collections.unmodifiableList(errors);
    }
    public List<CupLogMessage> getWarnings() {
        return Collections.unmodifiableList(warnings);
    }
    public List<CupLogMessage> getFatals() {
        return Collections.unmodifiableList(fatals);
    }
    
    public void clear() {
        fatals.clear();
        errors.clear();
        warnings.clear();
    }

    static {
        errorManager = new ErrorManager();
    }
    public static ErrorManager getManager() { return errorManager; }
    private ErrorManager(){
    }

    //TODO: migrate to java.util.logging
    /**
     * Error message format: 
     * ERRORLEVEL at (LINE/COLUMN)@SYMBOL: MESSAGE
     * ERRORLEVEL : MESSAGE
     **/
    public void emit_fatal(String message){
        CupLogMessage msg = new CupLogMessage(message);
        fatals.add(msg);
        System.err.println("Fatal : " + msg);
    }
    public void emit_fatal(String message, Symbol sym){
        //System.err.println("Fatal at ("+sym.left+"/"+sym.right+")@"+convSymbol(sym)+" : "+message);
        CupLogMessage msg = CupLogMessage.fromSym(message, sym);
        fatals.add(msg);
        System.err.println("Fatal: " + msg);
    }
    public void emit_warning(String message){
        CupLogMessage msg = new CupLogMessage(message);
        warnings.add(msg);
        System.err.println("Warning : " + msg);
    }
    public void emit_warning(String message, Symbol sym){
//        System.err.println("Warning at ("+sym.left+"/"+sym.right+")@"+convSymbol(sym)+" : "+message);
        CupLogMessage msg = CupLogMessage.fromSym(message, sym);
        warnings.add(msg);
        System.err.println("Warning: " + msg);
    }
    public void emit_error(String message){
        CupLogMessage msg = new CupLogMessage(message);
        errors.add(msg);
        System.err.println("Error : " + msg);
    }
    public void emit_error(String message, Symbol sym){
//        System.err.println("Error at ("+sym.left+"/"+sym.right+")@"+convSymbol(sym)+" : "+message);
        CupLogMessage msg = CupLogMessage.fromSym(message, sym);
        errors.add(msg);
        System.err.println("Error: " + msg);
    }
    
    public static class CupLogMessage {
        
        private final String message;
        
        private Location leftLoc = null;
        private Location rightLoc = null;
        
        private int offset = -1;
        private int length = 0;
        
        public CupLogMessage(String message, int offset, int length) {
            this.message = message;
            this.offset = offset;
            this.length = length;
        }
        
        public CupLogMessage(String message) {
            this.message = message;
        }
        
        private CupLogMessage(String message, Location left, Location right) {
            this.message = message;
            this.leftLoc = left;
            this.rightLoc = right;
        }
        
        public static CupLogMessage fromSym(String message, Symbol sym) {
            String msg = message + " @ " + sym;
            
            if (sym instanceof ComplexSymbol) {
                // if complex symbol is available, get the location from it
                ComplexSymbol csym = (ComplexSymbol) sym;
                return new CupLogMessage(msg, csym.getLeft(), csym.getRight());
            } else {
                return new CupLogMessage(msg, sym.left, sym.right - sym.left);
            }
        }

        public String getMessage() {
            return message;
        }

        public int getOffset() {
            return offset;
        }

        public int getLength() {
            return length;
        }

        public Location getLeftLoc() {
            return leftLoc;
        }

        public Location getRightLoc() {
            return rightLoc;
        }

        @Override
        public String toString() {
            return message;
        }
    }
    
//    private static String convSymbol(Symbol symbol){
//        String result = (symbol.value == null)? "" : " (\""+symbol.value.toString()+"\")";
//        Field [] fields = sym.class.getFields();
//        for (int i = 0; i < fields.length ; i++){
//            if (!Modifier.isPublic(fields[i].getModifiers())) continue;
//            try {
//                if (fields[i].getInt(null) == symbol.sym) return fields[i].getName()+result;
//            }catch (Exception ex) {
//            }
//        }
//        return symbol.toString()+result;
//    }
    
}
