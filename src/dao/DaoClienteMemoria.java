package dao;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import dominio.Cliente;
import excecao.DataException;

public class DaoClienteMemoria implements DaoCliente {

	static /*@ nullable @*/ DaoCliente daoCliente = null;
	private List<Cliente> clientes; //@ in listaClientes;
	//@ private represents listaClientes <- clientes;
	
	public static DaoCliente getInstance() {
		if(daoCliente == null)
			daoCliente = new DaoClienteMemoria();
				
		return daoCliente;
	}
	
	private DaoClienteMemoria() {
		clientes = new ArrayList<Cliente>();
	}
	
	@Override
	public void add(Cliente cliente) throws DataException {
		clientes.add(cliente);
	}

	@Override
	public void remove(Cliente cliente) throws DataException {
		Iterator<Cliente> it = clientes.iterator();
		while(it.hasNext()) {
			Cliente c = it.next();
			
			//Remove o objeto armazenado se o codigo for igual
			if(c.getCodigo().equals(cliente.getCodigo())) {
				it.remove();
				return;
			}
		}
		throw new DataException("Cliente não encontrado");
	}

	@Override
	public void update(Cliente cliente) throws DataException {
		Iterator<Cliente> it = clientes.iterator();
		while(it.hasNext()) {
			Cliente c = it.next();
			
			//Atualiza objeto armazenado se o codigo for igual
			if(c.getCodigo().equals(cliente.getCodigo())) {
				c = cliente;
				return;
			}
		}
	}

	@Override
	public Cliente get(long codigo) throws DataException {
		
		if(codigo <= 0L){
			throw new DataException("Codigo menor que zero");
		} else if (clientes.isEmpty()){
			throw new DataException("Lista clientes vazia");
		}
		
		Iterator<Cliente> it = clientes.iterator();
		while(it.hasNext()) {
			Cliente c = it.next();
			
			if(c.getCodigo().equals(codigo)) {
				return c;
			}
		}
		
		return null;
	}

	@Override
	public List<Cliente> list() throws DataException{
		return new ArrayList<Cliente>(clientes);
	}

}
