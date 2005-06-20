
package java_cup;
import java_cup.runtime.Symbol;
import java.lang.reflect.Field;
import java.lang.reflect.Modifier;
public class ErrorManager{
    private static ErrorManager errorManager;
    private int errors = 0;
    private int warnings = 0;
    public void emit_warning(String message){
        System.err.println("Warning " + message);
        warnings++;	
    }
    public void emit_warning(String message, Symbol sym){
        emit_warning(message+ " at Symbol: "+convSymbol(sym)+" in line "+sym.left+" / column "+sym.right);
    }
    public static String convSymbol(Symbol symbol){
        String result = (symbol.value == null)? "" : " (\""+symbol.value.toString()+"\")";
        Field [] fields = sym.class.getFields();
        for (int i = 0; i < fields.length ; i++){
            if (!Modifier.isPublic(fields[i].getModifiers())) continue;
            try {
                if (fields[i].getInt(null) == symbol.sym) return fields[i].getName()+result;
            }catch (Exception ex) {
            }
        }
        return symbol.toString()+result;
    }
    public int getErrorCount() { return errors; }
    public int getWarningCount() { return warnings; }
    public void emit_error(String message){
        System.err.println("Error " + message);
        errors++;
    }
    public void emit_error(String message, Symbol sym){
        emit_error(message+ " at Symbol: "+convSymbol(sym)+" in line "+sym.left+" / column "+sym.right);
    }
    private ErrorManager(){
    }
    static {
	errorManager = new ErrorManager();
    }
    public static ErrorManager getManager() { return errorManager; }
    
}
