# CZT Views

In addition to the CZT Editor, the CZT editor plug-in provides a set of views.

-   **Z Character Map**

    ![Z Character Map View](../images/view_zcharmap.png)

    This view provides users a palette of Unicode characters, including Z-specific characters,
    useful for writing Z specifications, particularly Using Unicode markup.

    Users can insert a Z character or construct into the active editor by clicking on a character
    in the panel.

    The actual text inserted follow the logic below:

    1.  If the active editor is not a CZT Editor, the description of the selected Z character is
        inserted in the editor.
    2.  If the specification is in LaTeX markup (the name of the specification file has the
        extension _*.tex_), then the actual text inserted in the active editor is the LaTeX
        representation of the selected Z character.
    3.  If the specification is in Unicode markup (the name of the specification file has the
        extension of either _*.utf8_ or _*.utf16_), then the Unicode representation of the selected
        Z character is inserted into the active editor.

-   **Z Conversion**

    ![Z Conversion View](../images/view_zconversion.png)

    This view is used to receive the contents converted from the specification in the editor. It
    also supports syntax colouring using the same rule as the editor.

-   **Outline**

    ![Outline View](../images/view_outline.png)

    The view provides the overview of the Z specification in the active CZT editor. If enabled,
    the selection in the editor can synchronize with the selection in the **Outline** view.
