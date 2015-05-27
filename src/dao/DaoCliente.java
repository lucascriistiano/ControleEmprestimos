package dao;

import java.util.List;

import dominio.Cliente;

public interface DaoCliente {
	public void add(Cliente cliente);
	public void remove(Cliente cliente);
	public void update(Cliente cliente);
	public Cliente get(Long codigo);
	public List<Cliente> list();
}