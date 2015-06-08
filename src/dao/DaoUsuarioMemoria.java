package dao;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Set;

import dominio.Usuario;
import excecao.DataException;

public class DaoUsuarioMemoria implements DaoUsuario {

	static DaoUsuario daoUsuario = null;
	private Set<Usuario> usuarios;
	
	public static DaoUsuario getInstance() {
		if(daoUsuario == null)
			daoUsuario = new DaoUsuarioMemoria();
		
		return daoUsuario;
	}
	
	private DaoUsuarioMemoria() {
		usuarios = new HashSet<Usuario>();
	}
	
	@Override
	public void add(Usuario usuario) throws DataException {
		usuarios.add(usuario);
	}

	@Override
	public void remove(Usuario usuario) throws DataException {
		Iterator<Usuario> it = usuarios.iterator();
		while(it.hasNext()) {
			Usuario u = it.next();
			
			//Remove o objeto armazenado se o login for igual
			if(u.getLogin().equals(usuario.getLogin())) {
				it.remove();
				return;
			}
		}
	}

	@Override
	public void update(Usuario usuario) throws DataException {
		Iterator<Usuario> it = usuarios.iterator();
		while(it.hasNext()) {
			Usuario u = it.next();
			
			//Atualiza objeto armazenado se o login for igual
			if(u.getLogin().equals(usuario.getLogin())) {
				u = usuario;
				return;
			}
		}
	}

	@Override
	public Usuario get(String login) throws DataException {
		Iterator<Usuario> it = usuarios.iterator();
		while(it.hasNext()) {
			Usuario u = it.next();
			
			if(u.getLogin().equals(login)) {
				return u;
			}
		}
		
		return null;
	}

	@Override
	public List<Usuario> list() throws DataException {
		List<Usuario> resultList = new ArrayList<Usuario>();
		
		Iterator<Usuario> it = usuarios.iterator();
		while(it.hasNext()) {
			resultList.add(it.next());
		}
		
		return resultList;
	}

}
