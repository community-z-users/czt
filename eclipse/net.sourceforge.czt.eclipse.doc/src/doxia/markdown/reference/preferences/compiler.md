# Compiler Preferences

The **CZT > Compiler** preference page allows configuring the various properties of the section manager for parsing and typechecking of Z specifications.

![Compiler Preference Page](../../images/pref_compiler.png)

## Dialect

Use the **Dialect** field to select the Z dialect to use within CZT Eclipse. This dialect will be used for all open files.

_Note: reload all open editors after changing the dialect to trigger parsing with the new dialect._

## Other properties

The following properties can be set in this page:

PROP_IGNORE_UNKNOWN_LATEX_COMMANDS
:   _Default: Off_
:   When set to true, the parser tools will ignore unknown LaTeX commands (that is, give a warning
    and use the name of the command) instead of reporting an error. Reporting an error is Standard
    conforming but ignoring those unknown commands is sometimes convenient.

PROP_TYPECHECK_USE_BEFORE_DECL
:   _Default: Off_
:   When this property is true, the typechecker will check that names are declared before they are
    used.

PROP_TYPECHECK_USE_STRONG_TYPING
:   _Default: Off_
:   Note: This property will affect Object-Z only. When this property is true, the typechecker
    will check the specification using strong typing.
