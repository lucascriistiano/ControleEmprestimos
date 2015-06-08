package dao;

import java.util.List;

import dominio.Usuario;
import excecao.DataException;

public interface DaoUsuario {
	public void add(Usuario usuario) throws DataException;
	public void remove(Usuario usuario) throws DataException;
	public void update(Usuario usuario) throws DataException;
	
	public Usuario get(String login) throws DataException;
	public List<Usuario> list() throws DataException;
}