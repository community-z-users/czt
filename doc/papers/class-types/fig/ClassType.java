class ClassType inherits Type2
{
  DeclName className;
  DeclType declType;
  List<ClassRef> classes;
  CoreInfo coreInfo;
}

class CoreInfo
{
  VisibilityList visibility;
  Signature state;
  List<NameTypePair> attribute;
  List<NameSignaturePair> operation;
}

class ClassRef
{
  RefName refName;
  List<Type2> instantiations;
}

enum DeclType { POLY, CLASSREF, CLASSUNION }
