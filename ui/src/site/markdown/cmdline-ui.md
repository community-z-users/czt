Title: CZT UI Command Line
Tags: CZT UI CmdLine

CZT User Interface Command Line
===============================


| Long 			  |	Small   | Arg  |	Type	 |	Description					    |
|:----------------|:--------|:----:|:----------- |:---------------------------------|
|`--dialect` 	  |	-D 	    | 1    | Dialect	 |	Specify dialect to be used	    |
|`--output-file`  |	-O		| 1    | URL		 |	Specify output file				|
|`--syntax-check` |	-S		| 0    | Boolean	 |	Syntax-check (parsing)			|
|`--czt-path`	  | -CP		| 1    | List<URL:>  |	Specification lookup path list	|

DEFAULT VALUES:
--------------

```
--dialect z
```

NOTES:
-----


* Arguments are mandatory when present. 

* Boolean parameters are false when not explicitly mentioned.
  
* List arguments are separated by semi-colon (:) and cannot be empty.

* Default czt-path is the current directory or anything given in a `./czt.properties` file

* Dialects available are: 

|Dialect 	| Description 							|
|:----------|:--------------------------------------|
|z      	| Standard Z 							|
|oz      	| Object Z								|
|circus  	| Circus 								|
|circustime	| Circus Time							|
|zeves   	| ZEves extension to Z					|
|zpatt   	| Z with transformation rules			|
|ozpatt  	| Object Z with transformation rules	|
|circuspatt	| Circus with transformation rules		|

  
* Markup of files is determined by their file extension. A LaTeX file ends in .tex, and an
  Unicode file ends in .utf8 or .utf16. This will determine what tool to use for processing
  the input file or returning the results. File ending bindings are:
  
| Extention | Markup 			|
|:----------|:------------------|
|tex, zed	| LaTeX				|
|xml, zml	| ZML				|
|zev     	| ZEves				|
|*8      	| Unicode (UTF-8)	|
|*16      	| Unicode (UTF-16)	|

* Some flags have been phased out. They were `-p` (for `zpatt` dialect), 
	`-dc` (for domain checking VCs), and `-id` for if an output in LaTeX or 
	Unicode mark-up is specified, the type checker prints the ids for names 
	as part of the name. The output will not type check any more.

EXAMPLES:
--------

```
--dialect z --output-file ./my-output.tex --czt-path ./tests:/user/local/pkg/myfiles my-input.utf8
```

Type checks `my-input.utf8` using Unicode parser for Z and looking for parent section in the given path list.
If successful, the result is transformed to LaTeX markup and output as `my-output.tex` file.
