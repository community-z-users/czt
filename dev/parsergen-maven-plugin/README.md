# CZT parser generator Maven plugin

The CZT ParserGen Maven plugin is used to generate source files for CZT parsers and parser
generators.

CZT parsers share a lot of similarities among different Z extensions and the differences may
appear in the middle of the parser for specific extensions. For that reason, the corresponding
classes and sources are defined as single parser definition files for every dialect.

The ParserGen plugin slices such XML definitions based on dialects listed in configuration,
producing dialect-specific parser source files. The approach is used to generate Java source
files as well as CUP or JFlex specifications for each dialect.


## Goals overview

The ParserGen plugin only has one goal:

-   **[parsergen:generate][]** attempts to generate source files for different CZT parser
    generators by splitting the corresponding XML definition files.

[parsergen:generate]: generate-mojo.html


## Usage

Refer to [goal description][parsergen:generate] for the list of all configuration options for
ParserGen plugin.

```xml
<project>
  ...
  <build>
    <plugins>
      <plugin>
        <groupId>net.sourceforge.czt.dev</groupId>
        <artifactId>parsergen-maven-plugin</artifactId>
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

The XML definitions for ParserGen plugin feature `<add:dialect></add:dialect>` code blocks
to indicate that this part must be included when corresponding dialect source file is being
generated. An excerpt from a sample definition file is given below:

```xml
<?xml version="1.0" encoding="UTF-8"?>
<utils xmlns:add="http://czt.sourceforge.net/templates/additional">
/* */
package <package/>;

import net.sourceforge.czt.util.Section;
...

<add:z>
import net.sourceforge.czt.z.jaxb.JaxbXmlReader;
</add:z>
<add:circus>
import net.sourceforge.czt.circus.jaxb.JaxbXmlReader;
</add:circus>
...
</utils>
```
