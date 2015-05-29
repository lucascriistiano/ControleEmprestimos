package dao;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Set;

import dominio.Cliente;

public class DaoClienteMemoria implements DaoCliente {

	static DaoCliente daoCliente = null;
	private Set<Cliente> clientes;
	
	public static DaoCliente getInstance() {
		if(daoCliente == null)
			daoCliente = new DaoClienteMemoria();
		
		return daoCliente;
	}
	
	private DaoClienteMemoria() {
		clientes = new HashSet<Cliente>();
	}
	
	@Override
	public void add(Cliente cliente) {
		clientes.add(cliente);
	}

	@Override
	public void remove(Cliente cliente) {
		clientes.remove(cliente);
	}

	@Override
	public void update(Cliente cliente) {
		clientes. add(cliente);
		
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
	public Cliente get(Long codigo) {
		Iterator<Cliente> it = clientes.iterator();
		while(it.hasNext()) {
			Cliente c = it.next();
			
			//Atualiza objeto armazenado se o codigo for igual
			if(c.getCodigo().equals(codigo)) {
				return c;
			}
		}
		
		return null;
	}

	@Override
	public List<Cliente> list() {
		List<Cliente> resultList = new ArrayList<Cliente>();
		
		Iterator<Cliente> it = clientes.iterator();
		while(it.hasNext()) {
			resultList.add(it.next());
		}
		
		return resultList;
	}

}
