package dao;

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
	
	public /*@ pure @*/ boolean existsLogin(String login) {
		return list.stream().filter(x -> x.getLogin().equals(login)).count() > 0;
	}

	public /*@ pure @*/ Usuario get(String login) throws DataException {
		if("".equals(login)) {
			throw new DataException("Login Vazio");
		}
			
		Usuario usuario = list.stream().filter(x -> x.getLogin().equals(login)).findFirst().orElse(null);
		
		if(usuario == null){
			throw new DataException("Cliente não cadastrado");
		}		
		
		return usuario;
		
	}
	
}
