package frontend;

import java.util.Map;
import java.util.HashMap;

public class Type {
  private static Map<String, Type> type_map = new HashMap<String,Type>();
  private String name;

  public Type( String a_name ) {
    name = a_name;
    registerTypeName( name );
  }
  
  public static Type from_name( String a_name ){
    return type_map.get( a_name );
  }
  
  public void registerTypeName( String name ){
    type_map.put( name, this );
  }

  public String name(){
    return name;
  }

  public boolean satisfies( Type t ){
    if( t == this || t == ANYTYPE )
      return true;
    else 
      return false;
  }
  
  public static final Type ArrayType = new Type("Array");
  public static final Type IntType = new Type("int");
  public static final Type BoolType = new Type("bool");
  public static final Type ANYTYPE = new Type("_any");
}