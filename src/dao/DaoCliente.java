package dao;

import java.util.List;

import dominio.Cliente;
import excecao.DataException;

public interface DaoCliente {
	
	//@ private model instance Collection<Cliente> clientes;
	
	/*@ 
	 @ requires cliente != null;
	 @ assignable clientes;
	 @ ensures clientes.size() == \old(clientes.size() + 1);
	 @*/
	public void add(Cliente cliente) throws DataException;
	
	public void remove(Cliente cliente) throws DataException;
	
	/*@ ensures this.clientes.size() == \old(clientes.size() + 1); @*/
	public void update(Cliente cliente) throws DataException;
	public Cliente get(Long codigo) throws DataException;
	
	
	
	public List<Cliente> list() throws DataException;
}