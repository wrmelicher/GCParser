package frontend;
import java.util.Scanner;
import java.math.BigInteger;
public class ArrayData extends TypeData {
  private TypeData elem_type;
  private int size;
  
  public ArrayData( TypeData elem, int s ){
    super( Type.ArrayType );
    elem_type = elem;
    size = s;
  }

  public int getSize(){
    return size;
  }

  public TypeData getElementData(){
    return elem_type;
  }

  public int bit_count(){
    return size * elem_type.bit_count();
  }
  public boolean is_constant() {
    return false;
  }
  public String constant_name() {
    return "";
  }
  public TypeData conditional( TypeData other ){
    // what to do...
    assert false : "operation not allowed";
    assert (other instanceof ArrayData) : "conditional return types do not match";
    ArrayData intother = (ArrayData) other;
    return null;
  }
  
  public BigInteger user_input( String debug_name, int party, Scanner in ) {
    BigInteger ret = BigInteger.ZERO;
    for( int i = 0; i < size; i++){
      BigInteger at = elem_type.user_input( debug_name+"["+i+"]", party, in );
      ret = ret.add( at.shiftLeft( i * getElementData().bit_count() ) );
    }
   
    return ret;
  }
}