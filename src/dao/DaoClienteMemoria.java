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
	public Cliente get(Long codigo) throws DataException {
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
		List<Cliente> resultList = new ArrayList<Cliente>();
		
		Iterator<Cliente> it = clientes.iterator();
		while(it.hasNext()) {
			resultList.add(it.next());
		}
		
		return resultList;
	}

}
