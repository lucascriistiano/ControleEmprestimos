package dao;

import java.util.List;

import dominio.Cliente;
import excecao.DataException;

public interface DaoCliente {
	
	//@ public model instance List listaClientes;
	
	/*@ 
	 @ public normal_behavior
	 @ 		requires cliente != null;
	 @		requires !listaClientes.contains(cliente);
	 @ 		assignable listaClientes;
 	 @ 		ensures listaClientes.size() == \old(listaClientes.size()) + 1;
 	 @ 		ensures listaClientes.get(listaClientes.size()-1) == cliente;
	 @	also
	 @	public exceptional_behavior
	 @ 		requires cliente != null;
	 @		requires listaClientes.contains(cliente);
	 @		assignable \nothing;
	 @		signals_only DataException;
	 @*/
	public void add(Cliente cliente) throws DataException;
	
	/*@
	 @	public normal_behavior 
	 @		requires cliente != null;
	 @		requires listaClientes.isEmpty() == false;
	 @		requires listaClientes.contains(cliente);
	 @ 		assignable listaClientes;	 
	 @		ensures !listaClientes.contains(cliente);
	 @	also
	 @	public exceptional_behavior
	 @		assignable \nothing;
     @		signals_only DataException;
 	 @		signals (DataException e)
 	 @			listaClientes.isEmpty() || listaClientes.contains(cliente) == false;
	 @*/
	public void remove(Cliente cliente) throws DataException;
	
	/*@
	 @	public normal_behavior 
	 @		requires cliente != null;
	 @		requires listaClientes.isEmpty() == false;
	 @		requires listaClientes.contains(cliente);
	 @ 		assignable listaClientes;	 
	 @	also
	 @	public exceptional_behavior
	 @		assignable \nothing;
	 @		signals_only DataException;
	 @		signals (DataException e)
	 @			listaClientes.isEmpty() || listaClientes.contains(cliente) == false;
	 @*/	
	public void update(Cliente cliente) throws DataException;
	
	/*@
	 @	public normal_behavior 
	 @		requires codigo > 0L;
	 @		requires listaClientes.isEmpty() == false;
	 @		requires this.exists(codigo);
	 @		ensures \result != null;
	 @	also
	 @	public exceptional_behavior
	 @		requires codigo <= 0L || listaClientes.isEmpty();
	 @		signals_only DataException;
	 @*/	
	public /*@ pure @*/ Cliente get(long codigo) throws DataException;
	
	/*@
	 @ 	requires codigo > 0L;
	 */
	public /*@ pure @*/ boolean exists(long codigo);
	
	/*@ 
	 @	public normal_behavior 
	 @ 		requires listaClientes != null;
	 @		ensures \result != null;
	 @	also
	 @	public exceptional_behavior
	 @		requires listaClientes == null;
	 @		signals_only DataException;
	 @*/
	public /*@ pure @*/ List<Cliente> list() throws DataException;
	

}