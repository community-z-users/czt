    public String toString()
    {
        StringBuilder builder = new StringBuilder();
        if (!getMixfix()) {
            // n \in S
            builder.append(String.valueOf(getLeftExpr()));
            builder.append(" in ");
            builder.append(String.valueOf(getRightExpr()));
        } else {
            if (getRightExpr() instanceof SetExpr) {
                // x = y
                SetExpr se = (SetExpr)getRightExpr();
                builder.append(" = ");
                builder.append(String.valueOf(getLeftExpr()));
                if ((se.getExprList() instanceof ZExprList) &&
                     se.getZExprList().size() == 1) {
                    builder.append(String.valueOf(se.getZExprList().get(0)));
                } else {
                    builder.append(String.valueOf(se.getClass().getName()));
                }
            } else {
                // op appl: ex: x < y, where L = (x,y), R = "_ < _"
                builder.append("(");
                builder.append(String.valueOf(getRightExpr()));
                builder.append(")");
                builder.append("~");
                builder.append(String.valueOf(getRightExpr()));
            }
        }
        return builder.toString();
    } 
