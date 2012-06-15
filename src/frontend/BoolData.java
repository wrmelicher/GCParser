package frontend;

import java.math.BigInteger;
import java.util.Scanner;

public class BoolData extends TypeData {
  private int possible_values;
  public static final int FALSE = 0;
  public static final int TRUE = 1;
  public static final int MAYBE = 2;
  public BoolData(){
    this( BoolData.MAYBE );
  }
  public BoolData( int possible ){
    super( Type.BoolType );
    possible_values = possible;
  }
  public int bit_count(){
    return 1;
  }
  public int poss_value(){
    return possible_values;
  }
  public static BoolData and( BoolData a, BoolData b ){
    if( a.possible_values == BoolData.FALSE || b.possible_values == BoolData.FALSE ){
      return new BoolData( BoolData.FALSE );
    } else {
      return new BoolData( BoolData.MAYBE );
    }
  }
  public static BoolData or( BoolData a, BoolData b ){
    if( a.possible_values == BoolData.TRUE || b.possible_values == BoolData.TRUE ){
      return new BoolData( BoolData.TRUE );
    } else {
      return new BoolData( BoolData.MAYBE );
    } 
  }
  public static BoolData equals( BoolData a, BoolData b ){
    if( a.is_constant() && b.is_constant() ){
      return new BoolData( a.poss_value() == b.poss_value() ? BoolData.TRUE : BoolData.FALSE );
    } else {
      return new BoolData( BoolData.MAYBE );
    }
  }
  public boolean is_constant(){
    return possible_values != BoolData.MAYBE;
  }
  public String constant_name(){
    return possible_values == BoolData.FALSE ? "0:1" : "1:1";
  }
  public TypeData conditional( TypeData other ){
    return new BoolData( BoolData.MAYBE );     
  }
  public BigInteger user_input( String debug_name, int party, Scanner in ) {
    System.out.print( getType().name() + " " + debug_name + " from party " + party + " value (true or false): " );
    boolean b = in.nextBoolean();
    System.out.println();
    return b ? BigInteger.ONE :  BigInteger.ZERO;
  }
}