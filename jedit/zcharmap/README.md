# CZT ZCharMap plugin for jEdit

The ZCharMap plugin displays a dockable window listing important Z characters and Z constructs.
The plugin currently supports two markup formats for Z: the LaTeX markup and the Unicode markup.

![CZT ZCharMap palette for jEdit](images/czt-jedit-zcharmap.png)

## Usage

You can simply click on a Z character or construct to insert it into your current buffer.
The top line ("Paragraphs") inserts complete Z paragraphs, with uppercase placeholders for the
parts that you should fill in, while most of the other constructs insert just one Z symbol
or operator. For example, clicking on "`Sch[]`", with LaTeX markup selected, will insert a
_generic schema_ construct, like this:

```
\begin{schema}{NAME}[ TYPE ]
  DECLS
\where
  PREDS
\end{schema}
```

You should replace `NAME` by the name of your schema, `TYPE` by the generic type parameter(s),
`DECLS` by a sequence of declarations and `PREDS` by a sequence of predicates.

### Hints

-   To write the name of a primed variable, like `x'`, use the `'` character from the "Schemas"
    line of the ZCharMap plugin. (In LaTeX, this just inserts the normal ASCII prime character,
    but in Unicode it inserts a special prime symbol. To prime a schema or expression, you must
    put a space in between the schema name and the prime. This space must be a normal space
    character in Unicode markup, but a special spacing command like tilde (`~`) in LaTeX markup.
-   In LaTeX markup, you must write underscores as `\_`, newlines as `\\` and spaces as `~`.
    In Unicode markup these can just be written as normal ASCII characters.
