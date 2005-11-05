    public String toString()
    {
        StringBuilder builder = new StringBuilder();
        if (!getMixfix()) {
            // ran(x)
            builder.append(String.valueOf(getLeftExpr()));
            builder.append("~");
            builder.append(String.valueOf(getRightExpr()));
        } else {
            // ("_ + _") (x, y)
            builder.append("(");
            builder.append(String.valueOf(getLeftExpr()));
            builder.append(")~");
            builder.append(String.valueOf(getRightExpr()));
        }
        return builder.toString();
    }
