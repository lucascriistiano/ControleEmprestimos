package dao;

import java.util.List;

import dominio.Cliente;
import excecao.DataException;

public interface DaoCliente {
	
	//@ public model instance List listaClientes;
	
	/*@ 
	 @ requires cliente != null;
	 @ assignable listaClientes;
 	 @ ensures listaClientes.size() == \old(listaClientes.size()) + 1;
 	 @ ensures listaClientes.get(listaClientes.size()-1) == cliente;
	 @*/
	public void add(Cliente cliente) throws DataException;
	
	/*@
	 @	public normal_behavior 
	 @		requires cliente != null;
	 @		requires listaClientes.isEmpty() == false;
	 @		requires listaClientes.contains(cliente);
	 @	also
	 @	public exceptional_behavior
     @		signals_only DataException;
 	 @		signals (DataException e)
 	 @			listaClientes.contains(cliente) == false;
	 @*/
	public void remove(Cliente cliente) throws DataException;
	
	/*@ ensures this.listaClientes.size() == \old(listaClientes.size() + 1); @*/
	public void update(Cliente cliente) throws DataException;
	public Cliente get(Long codigo) throws DataException;
	
	
	
	public List<Cliente> list() throws DataException;
}