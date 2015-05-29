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
	
	public void cadastrarUsuario(Usuario usuario) {
		if(validarUsuario(usuario)) {
			this.daoUsuario.add(usuario);
		}
	}
	
	public void removerUsuario(Usuario usuario) {
		this.daoUsuario.remove(usuario);
	}
	
	public List<Usuario> listarUsuarios() {
		return daoUsuario.list();
	}
	
	public boolean validarUsuario(Usuario usuario) {
		
		if(usuario.getLogin().equals("")) {
			//TODO Lancar excessao
			System.out.println("Usuario invalido: Nome de usuario vazio");
			return false;
		}
		if(usuario.getNome().equals("")) {
			//TODO Lancar excessao
			System.out.println("Usuario Invalido: Nome vazio");
			return false;
		}
		if(usuario.getNome().equals("")) {
			//TODO Lancar excessao
			System.out.println("Usuario Invalido: Senha vazia");
			return false;
		}
		if(daoUsuario.get(usuario.getLogin()) != null) {
			//TODO Lancar excessao
			System.out.println("Usuario Invalido: Nome de usuario já existe");
			return false;
		}
		
		return true;
	}
}
