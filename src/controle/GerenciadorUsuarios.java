package controle;

import dao.DaoUsuario;
import dominio.Usuario;

public class GerenciadorUsuarios {
	private DaoUsuario daoUsuario; 
	
	public GerenciadorUsuarios() {
		this.daoUsuario = new DaoUsuario();
	}
	
	public void cadastrarUsuarios(Usuario usuario) {
		this.daoUsuario.add(usuario);
	}
	
	public void validarUsuario(Usuario usuario) {
		
	}
}
