package dao;

import java.util.List;

import dominio.Usuario;

public interface DaoUsuario {
	public void add(Usuario usuario);
	public void remove(Usuario usuario);
	public void update(Usuario usuario);
	
	public Usuario get(String login);
	public List<Usuario> list();
}