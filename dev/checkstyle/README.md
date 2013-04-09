# CZT Checkstyle settings

The CZT Checkstyle project contains just the CZT settings for [Checkstyle][checkstyle] tool.
The configuration is adapted from the [style guidelines from Geosoft][geosoft-style].

[checkstyle]: http://checkstyle.sourceforge.net
[geosoft-style]: http://geosoft.no/development/javastyle.html


## Usage

The CZT Checkstyle configuration is [available for download](checkstyle.xml).
Use it with all [tools that support Checkstyle][checkstyle-tools],
e.g. [Eclipse-CS][eclipse-cs] for Eclipse IDE.

[checkstyle-tools]: http://checkstyle.sourceforge.net#Related_Tools
[eclipse-cs]: http://eclipse-cs.sourceforge.net


### Use in Maven build

This Checkstyle project enables these settings to be used as part of the Maven build, just add
the project as a dependency to `maven-checkstyle-plugin` and then reference the CZT Checkstyle
config in your POM file:

```xml
<project>
  ...
  <build>
    <plugins>
      <plugin>
        <groupId>org.apache.maven.plugins</groupId>
        <artifactId>maven-checkstyle-plugin</artifactId>
        <version>2.9.1</version>
        <dependencies>
          <dependency>
            <groupId>net.sourceforge.czt.dev</groupId>
            <artifactId>checkstyle</artifactId>
            <version>2.0.0</version>
          </dependency>
        </dependencies>
      </plugin>
    </plugins>
    ...
  </build>
  ...
  <reporting>
    <plugins>
      <plugin>
        <groupId>org.apache.maven.plugins</groupId>
        <artifactId>maven-checkstyle-plugin</artifactId>
        <version>2.9.1</version>
        <configuration>
          <configLocation>/net/sourceforge/czt/checkstyle.xml</configLocation>
        </configuration>
      </plugin>
    </plugins>
  </reporting>
  ...
</project>       
```
