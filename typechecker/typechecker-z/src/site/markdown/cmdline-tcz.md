Title: CZT Z Type Check Command Line
Tags: CZT Z Typecheck CmdLine

CZT Z Type checker Command Line:
===============================

| Long 					| Small  | Arg	|Type			| Description								  |
|:--------------------- |:------ |:----:|:------------- |:--------------------------------------------|
|`--syntax-check`		| `-S`   |	0	| Boolean		| Syntax-check (parsing)					  |
|`--use-before-decl`	| `-UBD` |	0	| Boolean		| Allow use of names before their declaration |
|`--use-rec-types`		| `-URT` |	0	| Boolean		| Allow the use of recursive types (??)		  |
|`--print-ast`			| `-PA`  |	0 	| Boolean		| Print the AST if type check succeeds 		  |
|`--print-type-env`		| `-PT`  |	0 	| Boolean		| Print (global) type environment if succeeds |
|`--print-benchmarks`	| `-PB`	 |	0	| Boolean		| Print benchmarks for various stages		  |
|`--warning-output`		| `-WO`  |	1	| WarningOutput	| Choose treatment of warnings 				  |
|`--czt-path`			| `-CP`  |	1	| List<URL:>	| Specification lookup path list			  |

DEFAULT VALUES:
--------------

```
--warning-output show
```

NOTES:
-----

* Arguments are mandatory when present. 

* Boolean parameters are false when not explicitly mentioned.
  
* List arguments are separated by semi-colon (:) and cannot be empty.

* Default czt-path is the current directory or anything given in a `./czt.properties` file

* Warning output determine how warnings are handled. Values are: `hide`, `show`, and `raise`.
  They are ignored when hidden, logged when shown, and an exception is thrown when raise.
  The default value is to `show` then.
  
* Some flags have been phased out. They were: `-n` on force use before declaration that is default, 
	and `-i` for printing name ids.

EXAMPLES:
--------

```
--print-ast --print-type-env --print-benchmarks --warning-output raise --use-before-decl my-file.tex
```

Type checks `my-file.tex` using LaTeX parser for Z and looking for parent section in the current directory.
If successful, an ASCII representation of the AST is printed together with the global typing environment
and the tool execution benchmarks per stage. Variable names can also be used before declaration, and 
warnings are not tolerated.
