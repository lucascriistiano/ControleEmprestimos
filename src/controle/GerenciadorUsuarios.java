package controle;

import java.util.List;

import dao.DaoUsuario;
import dao.DaoUsuarioMemoria;
import dominio.Usuario;

public class GerenciadorUsuarios {
	private DaoUsuario daoUsuario; 
	
	public GerenciadorUsuarios() {
		this.daoUsuario = DaoUsuarioMemoria.getInstance();
	}
	
	public void cadastrarUsuarios(Usuario usuario) {
		this.daoUsuario.add(usuario);
	}
	
	public List<Usuario> listarUsuarios() {
		return daoUsuario.list();
	}
	
	public void validarUsuario(Usuario usuario) {
		
	}
}
