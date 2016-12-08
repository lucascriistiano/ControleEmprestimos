package dao;

import java.util.Iterator;

import dominio.Usuario;
import excecao.DataException;

public class DaoUsuario extends DaoImpl<Usuario> {
	
	static /*@ nullable @*/ DaoUsuario daoUsuario = null;
	
	private DaoUsuario() {
		super ("Usuario");
	}
	
	public static DaoUsuario getInstance() {
		if(daoUsuario == null)
			daoUsuario = new DaoUsuario();
		
		return daoUsuario;
	}

	public Usuario get(String login) throws DataException {
		if("".equals(login)) {
			throw new DataException("Login Vazio");
		}
		
		Iterator<Usuario> it = list.iterator();
		while(it.hasNext()) {
			Usuario c = it.next();
			if(c.getLogin().equals(login)) {
				return c;
			}
		}
		
		throw new DataException("Cliente não cadastrado");
	}
	
}
