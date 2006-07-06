import jdsl.core.api.*;
import jdsl.core.ref.*;
import java.io.*;

/** 
 * Utility class that reads names from a file.  The names are returned in a
 * Sequence.  The class consists of one static method that does all the work.
 * The file, names.list, contains the  200 most popular last names in the USA.
 *
 * @author Lucy Perry (lep)
 * @version JDSL 2
*/ 
class NameGenerator {
    public static Sequence getNames() {
        Sequence ret = new ArraySequence();
        try {
            StreamTokenizer in = new StreamTokenizer(new FileReader("names.list"));
            String str;
            int i=0;
            int type;
            do {
                type = in.nextToken();
                if (type==StreamTokenizer.TT_WORD) {
                    ret.insertLast(in.sval);
                    i++;
                }
            } while (type!=StreamTokenizer.TT_EOF);
        } catch (IOException e) {}
        return ret;
    }
}
