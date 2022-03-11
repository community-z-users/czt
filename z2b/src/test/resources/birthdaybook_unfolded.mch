/* Translated automatically from file:/research/czt/trunk/z2b/birthdaybook_unfolded.tex */
MACHINE
    Specification
SETS
    REPORT = {ok,already_known,not_known}
DEFINITIONS
    NAME == 1 .. 5;
    DATE == 10 .. 15
VARIABLES
    known,
    birthday
INVARIANT
    known : POW(NAME) & 
    birthday : NAME +-> DATE & 
    known = dom(birthday)
INITIALISATION
    ANY known__prime,birthday__prime
    WHERE known__prime : POW(NAME) & 
        birthday__prime : NAME +-> DATE & 
        known__prime = dom(birthday__prime) & 
        known__prime = {}
    THEN known := known__prime || 
        birthday := birthday__prime
    END
OPERATIONS
    
    date__out <-- FindBirthday(name__in) =
    PRE name__in : NAME & 
        known = dom(birthday) & 
        name__in : known
    THEN ANY known__prime,date__out__prime,birthday__prime
        WHERE known__prime : POW(NAME) & 
            birthday__prime : NAME +-> DATE & 
            date__out__prime : DATE & 
            known__prime = dom(birthday__prime) & 
            known__prime = known & 
            birthday__prime = birthday & 
            date__out__prime = birthday(name__in)
        THEN known := known__prime || 
            date__out := date__out__prime || 
            birthday := birthday__prime
        END
    END;
    
    result__out <-- Success =
    PRE 1=1
    THEN ANY known__prime,result__out__prime,birthday__prime
        WHERE result__out__prime : REPORT & 
            result__out__prime = ok
        THEN known := known__prime || 
            result__out := result__out__prime || 
            birthday := birthday__prime
        END
    END;
    
    result__out <-- NotKnown(name__in) =
    PRE name__in : NAME & 
        known = dom(birthday) & 
        name__in /: known
    THEN ANY known__prime,result__out__prime,birthday__prime
        WHERE known__prime : POW(NAME) & 
            birthday__prime : NAME +-> DATE & 
            result__out__prime : REPORT & 
            known__prime = dom(birthday__prime) & 
            known__prime = known & 
            birthday__prime = birthday & 
            result__out__prime = not_known
        THEN known := known__prime || 
            result__out := result__out__prime || 
            birthday := birthday__prime
        END
    END;
    
    card__out <-- RemindOne(today__in) =
    PRE today__in : DATE & 
        known = dom(birthday)
    THEN ANY known__prime,card__out__prime,birthday__prime
        WHERE known__prime : POW(NAME) & 
            birthday__prime : NAME +-> DATE & 
            card__out__prime : NAME & 
            known__prime = dom(birthday__prime) & 
            known__prime = known & 
            birthday__prime = birthday & 
            card__out__prime : known & 
            birthday(card__out__prime) = today__in
        THEN known := known__prime || 
            card__out := card__out__prime || 
            birthday := birthday__prime
        END
    END;
    
    AddBirthday(name__in,date__in) =
    PRE name__in : NAME & 
        date__in : DATE & 
        known = dom(birthday) & 
        name__in /: known
    THEN ANY known__prime,birthday__prime
        WHERE known__prime : POW(NAME) & 
            birthday__prime : NAME +-> DATE & 
            known__prime = dom(birthday__prime) & 
            birthday__prime = birthday \/ {name__in |-> date__in}
        THEN known := known__prime || 
            birthday := birthday__prime
        END
    END;
    
    result__out <-- AlreadyKnown(name__in) =
    PRE name__in : NAME & 
        known = dom(birthday) & 
        name__in : known
    THEN ANY known__prime,result__out__prime,birthday__prime
        WHERE known__prime : POW(NAME) & 
            birthday__prime : NAME +-> DATE & 
            result__out__prime : REPORT & 
            known__prime = dom(birthday__prime) & 
            known__prime = known & 
            birthday__prime = birthday & 
            result__out__prime = already_known
        THEN known := known__prime || 
            result__out := result__out__prime || 
            birthday := birthday__prime
        END
    END
END