package frontend;

import java.util.*;

public class IfExpression extends Statement {
  
  private boolean if_form_branch;
  private Expression cond;
  private Expression if_form;
  private Expression else_form;
  private IfExpression prev;

  private Variable cond_var;

  // holds the read values of the key variable from before the if, and before the else, and after the else statements
  private Map<Variable, AssignmentData> dests;
  
  public IfExpression( int line, Expression acond, Expression anif ){
    this( line, acond, anif, null );    
  }
  public IfExpression( int line, Expression acond, Expression anif, Expression anelse ){
    super( line );
    cond = acond;
    if_form = anif;
    else_form = anelse;
  }

  public void register_assignment( Variable dest ){
    AssignmentData destlist = dests.get( dest );
    if( destlist == null ){
      destlist = new AssignmentData();
      dests.put( dest, destlist );
    }
    destlist.setData( dest, true );
  }

  private void assignment( Variable dest, String if_name, TypeData if_type, String else_name, TypeData else_type ) throws CompileException {
    String cond_name = cond_var.cur_name();
    Variable temp = new Variable( if_type.conditional( else_type ) );
    
    ProgramTree.output.println( temp.new_name() + " chose " + cond_name + " " + if_name + " " + else_name );
    
    dest.compile_assignment( temp, this );
  }
  
  public void compile() throws CompileException {

    dests = new HashMap< Variable, AssignmentData >();
    
    cond.compile();
    cond_var = cond.returnVar();
    if( cond_var.getType() != Type.BoolType ){
      throw error("Expecting a boolean expression");
    }
    BoolData cond_data = ( BoolData ) cond_var.getData();
    if( cond_data.is_constant() ){
      if( cond_data.poss_value() == BoolData.TRUE ){
	if_form.compile();
      } else if( else_form != null ) {
	else_form.compile();
      }
      return;
    } else {

      prev = Expression.cond_scope;
      Expression.cond_scope = this;

      if_form_branch = true;
      if_form.compile();
      for( Variable v : dests.keySet() ){
	AssignmentData data = dests.get( v );
	data.setData( v, false );
	v.reset_from_snap( data.before_if );
      }
      
      if_form_branch = false;
      if( else_form != null ){
	else_form.compile();
      }

      for( Variable v : dests.keySet() ){
	AssignmentData data = dests.get( v );
	data.setData( v, false );
      }
      
      Expression.cond_scope = prev;      
      for( Variable v : dests.keySet() ){
	Variable.Snapshot first_arg = dests.get( v ).first_mux_arg();
	Variable.Snapshot second_arg = dests.get( v ).second_mux_arg();
	int max = Math.max( first_arg.length_at(), second_arg.length_at() );
	assignment( v, first_arg.padTo( max ), first_arg.data,
		    second_arg.padTo( max ), second_arg.data );
      }
    }
  }

  private class AssignmentData {
    private boolean assigned_in_if = false;
    private boolean assigned_in_else = false;
    
    private Variable.Snapshot before_if;
    private Variable.Snapshot after_if;
    private Variable.Snapshot before_else;
    private Variable.Snapshot after_else;
    
    public AssignmentData(){}
    public void setData( Variable v, boolean before ){
      Variable.Snapshot sn = v.snapshot();
      if( if_form_branch ){
	if( before ){
	  assigned_in_if = true;
	  before_if = sn;
	} else {
	  after_if = sn;
	}
      } else {
	if( before ){
	  assigned_in_else = true;
	  before_else = sn;
	} else {
	  after_else = sn;
	}
      }
    }
    public Variable.Snapshot first_mux_arg(){
      if( assigned_in_if )
	return after_if;
      else
	return before_else;
    }
    public Variable.Snapshot second_mux_arg(){
      if( assigned_in_else )
	return after_else;
      else
	return before_if;
    }
  }
}


