package frontend;

import java.math.BigInteger;
import java.util.Scanner;

class IntTypeData extends TypeData {
  private BigInteger magnitude;
  private boolean signed;
  private boolean is_const;

  private static final BigInteger TWO = BigInteger.ONE.add( BigInteger.ONE );

  public IntTypeData( int val ){
    this( new BigInteger( val+"" ) );
  }
  public IntTypeData( BigInteger val ){
    super( Type.IntType );
    is_const = true;
    signed = val.compareTo( BigInteger.ZERO ) < 0 ? true : false;
    magnitude = val;
  }
  public IntTypeData( BigInteger mag, boolean sign ) {
    super( Type.IntType );
    magnitude = mag;
    signed = sign;
    is_const = false;
  }
  public IntTypeData( int mag, boolean sign ){
    this( new BigInteger( mag+"" ), sign );
  }
  public int bit_count(){
    return signed ? magnitude.bitLength()+1 :  magnitude.bitLength();
  }
  public boolean signed(){
    return signed;
  }
  public static IntTypeData add( IntTypeData a, IntTypeData b ){
    if( a.is_constant() && b.is_constant() ){
      return new IntTypeData( a.magnitude.add(b.magnitude) );
    } else {
      return new IntTypeData( a.magnitude.add( b.magnitude ), a.signed || b.signed );
    }
  }
  public static IntTypeData negate( IntTypeData a ) {
    if( a.is_constant() ){
      return new IntTypeData( a.magnitude.negate() );
    }
    return new IntTypeData( a.magnitude, true );
  }
  public static IntTypeData subtraction( IntTypeData a, IntTypeData b ){
    if( a.is_constant() && b.is_constant() ){
      return new IntTypeData( a.magnitude.subtract( b.magnitude ) );
    }
    return new IntTypeData( a.magnitude.add( b.magnitude ), true );
  }
  public static BoolData equals( IntTypeData a, IntTypeData b ){
    if( a.is_constant() && b.is_constant() ){
      return new BoolData( a.magnitude.compareTo( b.magnitude ) == 0 ? BoolData.TRUE : BoolData.FALSE );
    } else {
      return new BoolData( BoolData.MAYBE );
    }
  }
  public static BoolData lessthan( IntTypeData a, IntTypeData b ) {
    if( a.is_constant() && b.is_constant() ){
      return new BoolData( a.magnitude.compareTo( b.magnitude ) < 0 ? BoolData.TRUE : BoolData.FALSE );
    } else {
      return new BoolData( BoolData.MAYBE );
    }
  }
  public String extend_operation(){
    if( signed() ){
      return "sextend";
    } else {
      return "zextend";
    }
  }
 
  public boolean is_constant() {
    return is_const;
  }
  public String constant_name(){
    if( magnitude.compareTo( BigInteger.ZERO ) == 0 )
      return magnitude+":"+1;
    return magnitude+":"+bit_count();
  }
  public int value(){
    return magnitude.intValue();
  }
  public TypeData conditional( TypeData other ){
    assert (other instanceof IntTypeData) : "conditional return types do not match";
    IntTypeData intother = (IntTypeData) other;
    return new IntTypeData( magnitude.max( intother.magnitude ), signed || intother.signed );     
  }
  public BigInteger user_input( String debug_name, int party, Scanner in ) {
    System.out.print( getType().name() + " " + debug_name + " of party " + party + " value (between "+ ( signed() ? magnitude.negate() : BigInteger.ZERO ) + " and " + magnitude + "): ");
    System.out.println();
    return in.nextBigInteger();
   }
}