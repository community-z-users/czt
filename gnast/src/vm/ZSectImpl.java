    public String toString()
    {
        StringBuilder builder = new StringBuilder(getName());
        builder.append(String.valueOf(getParent()));
        builder.append(String.valueOf(getPara()));
        return builder.toString();
    } 
