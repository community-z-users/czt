# GnAST Maven plugin

The GnAST Maven plugin is used to generate Java interfaces and classes from an XML Schema
definition.

The plugin provides a Maven interface to CZT [GnAST AST generator][gnast] and supports all its
configuration options.

Furthermore, it adds source code generation for [CZT Rules][rules] prover (see goals).

[gnast]: ../gnast/
[rules]: ../../rules/


## Goals overview

The GnAST plugin has 2 goals:

-   **[gnast:generate][]** attempts to generate AST source files from the provided XML Schema
    files.

-   **[gnast:rulecodegen][]** attempts to generate CZT Rules prover classes from XML Schema file.

[gnast:generate]: generate-mojo.html
[gnast:rulecodegen]: rulecodegen-mojo.html


## Usage

Refer to corresponding goal descriptions for the list of all configuration options for GnAST plugin
goals.

```xml
<project>
  ...
  <build>
    <plugins>
      <plugin>
        <groupId>net.sourceforge.czt.dev</groupId>
        <artifactId>gnast-maven-plugin</artifactId>
        <version>2.0.0</version>
        <!-- Configure the plugin: mandatory and optional parameters -->
        ...
      </plugin>
      ...
    </plugins>
  </build>
  ...
</project>
```

The plugin is an interface to GnAST AST generator, so refer to [GnAST documentation][gnast]
for details on developing suitable XML Schema definitions and using the AST generator.
