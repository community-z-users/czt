package net.sourceforge.czt.typecheck.util.typeerror;

public final class ErrorKind
{
  /**
   * Do not create instances of this class.
   */
  private ErrorKind()
  {
  }

  public static final int
    UNKNOWN_ERROR = -1,
    REDECLARATION = 0,
    SECT_REDECLARATION = 1,
    NO_PARENT = 2,
    EXTRA_STROKE = 3,
    POWERTYPE_NEEDED = 4,
    SETEXPR_MEMBTYPE_NOT_AGREE = 5,
    TUPLEEXPR_LESSTHAN_2 = 6,
    PRODTYPE_REQUIRED = 7,
    INVALID_TUPLESELEXPR_SELECT = 8,
    UNDECLAREDNAME = 9,
    NAMETYPEPAIR_NOT_FOUND = 10,
    GENTYPE_FOUND = 11,
    SCHEMATYPE_NEEDED = 12,
    DECLNAME_NOT_FOUND_IN_SCHEMA = 13,
    TWO_COMPONENT_NEEDED = 14,
    APPLEXPR_TYPES_DO_NOT_AGREE = 15,
    SCHEXPR_EXPECTED = 16,
    TUPLESELEXPR_OUT_OF_RANGE = 17,
    INCOMPATIBLE_SIGNATURES = 18,
    PRODTYPE_SIZE_2_REQUIRED = 19,
    UNIFICATION_FAILED = 20,
    BINDEXPR_EXPECTED = 21;

  public static String getCase(int k)
  {
    String result = null;
    switch (k) {
      case UNKNOWN_ERROR :
        result = "Unknown error";
        break;
      case REDECLARATION :
        result = "Redeclaration";
        break;
      case SECT_REDECLARATION :
        result = "Declared in a previous section";
        break;
      case NO_PARENT :
        result = "Cannot find parent section";
        break;
      case EXTRA_STROKE :
        result = "Extra stroke found";
        break;
      case POWERTYPE_NEEDED :
        result = "Power type needed!";
        break;
      case SETEXPR_MEMBTYPE_NOT_AGREE :
        result = "SetExpr components' types do not agree!";
        break;
      case TUPLEEXPR_LESSTHAN_2 :
        result = "TupleExpr has less than 2 components!";
        break;
      case PRODTYPE_REQUIRED :
        result = "Cartesian product type (ProdType) needed!";
        break;
      case INVALID_TUPLESELEXPR_SELECT :
        result = "Invalid TupleSelExpr Select!";
        break;
      case UNDECLAREDNAME :
        result = "Undeclared name!";
        break;
      case NAMETYPEPAIR_NOT_FOUND :
        result = "NameTypePair not found in type environment!";
        break;
      case GENTYPE_FOUND :
        result = "Generic type found!";
        break;
      case SCHEMATYPE_NEEDED :
        result = "SchemaType required!";
        break;
      case DECLNAME_NOT_FOUND_IN_SCHEMA :
        result = "DeclName is not found in the SchemaType!";
        break;
      case TWO_COMPONENT_NEEDED :
        result = "2 component type needed!";
        break;
      case APPLEXPR_TYPES_DO_NOT_AGREE :
        result = "ApplExpr types do not agree!";
        break;
      case SCHEXPR_EXPECTED :
        result = "Schema expression expected!";
        break;
      case TUPLESELEXPR_OUT_OF_RANGE :
        result = "Tuple selection out of range!";
	break;
      case INCOMPATIBLE_SIGNATURES :
        result = "Incompatible signatures!";
	break;
      case PRODTYPE_SIZE_2_REQUIRED :
        result = "Cross product of size 2 required!";
        break;
      case UNIFICATION_FAILED:
        result = "Unification failed!";
        break;
      case BINDEXPR_EXPECTED:
        result = "Binding expression expected!";
        break;
      default :
        result = "Illegal error!";
        break;
    }
    return result;
  }
}
