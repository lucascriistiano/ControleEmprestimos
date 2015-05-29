package visao;

import java.util.List;

import controle.GerenciadorUsuarios;
import dominio.Usuario;

public class UIGerenciamentoUsuariosConsole implements UIGerenciamentoUsuarios {

	GerenciadorUsuarios gerenciadorUsuarios = new GerenciadorUsuarios();
	
	@Override
	public void cadastrarUsuario() {
		// TODO Auto-generated method stub
	}

	@Override
	public void removerUsuario() {
		// TODO Auto-generated method stub

	}

	@Override
	public void listarUsuarios() {
		// TODO Auto-generated method stub
		List<Usuario> usuarios = gerenciadorUsuarios.listarUsuarios();
		
		for(Usuario usuario : usuarios) {
			System.out.println("Nome: " + usuario.getNome());
			System.out.println("Login: " + usuario.getLogin());
			System.out.println("Senha: " + usuario.getSenha());
			System.out.println();
		}
	}

}
