# CUP Maven plugin

The Java CUP Maven plugin is used to generate Java-based parsers from CUP parser specifications.

The plugin provides a Maven interface to [Java CUP parser generator][cup] and supports all its
configuration options. Uses [CUP 0.11a generator (with CZT updates)][cup-lib].

## Goals overview

The CUP plugin only has one goal:

-   **[cup:generate][]** attempts to generate parser source files from the provided CUP
    specification files.


## Usage

Refer to [goal description][cup:generate] for the list of all configuration options for CUP plugin.

```xml
<project>
  ...
  <build>
    <plugins>
      <plugin>
        <groupId>net.sourceforge.czt.dev</groupId>
        <artifactId>cup-maven-plugin</artifactId>
        <version>2.0.0</version>
        ...
      </plugin>
      ...
    </plugins>
  </build>
  ...
</project>
```

The plugin is an interface to Java CUP parser generator, so refer to [CUP manual][cup-manual] for
details on writing CUP specifications and using the parser generator.

The CUP plugin uses a modified version of the last CUP release. The official CUP library is no
longer in active development, however several minor updates have been added by the Community Z
Tools project. The current version used is [0.11-a-czt01][cup-lib].

### CUP runtime dependency

The CUP-generated parsers require CUP runtime dependency for compilation and runtime. To avoid
having full CUP parser generator as a dependency, the runtime is provided as a
[separate lightweight library][cup-runtime].

Include the matching CUP runtime dependency where parser is generated:

```xml
<project>
  ...
  <dependencies>
    <dependency>
      <groupId>net.sourceforge.czt.dev</groupId>
      <artifactId>java-cup-runtime</artifactId>
      <version>0.11-a-czt01</version>
    </dependency>
  </dependencies>
  ...
</project>
```


[cup]: http://www2.cs.tum.edu/projects/cup/
[cup-manual]: ../java-cup/manual.html
[cup-lib]: ../java-cup/
[cup-runtime]: ../java-cup-runtime/
[cup:generate]: generate-mojo.html
