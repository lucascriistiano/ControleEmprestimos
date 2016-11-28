package dao;

import java.util.List;

import dominio.Cliente;
import excecao.DataException;

public interface DaoCliente {
	
	//@ public model instance List<Cliente> listaClientes;
	
	/*@ 
	 @ requires cliente != null;
	 @ assignable listaClientes;
	 @ ensures listaClientes.size() == \old(listaClientes.size() + 1);
	 @*/
	public void add(Cliente cliente) throws DataException;
	
	public void remove(Cliente cliente) throws DataException;
	
	/*@ ensures this.listaClientes.size() == \old(listaClientes.size() + 1); @*/
	public void update(Cliente cliente) throws DataException;
	public Cliente get(Long codigo) throws DataException;
	
	
	
	public List<Cliente> list() throws DataException;
}