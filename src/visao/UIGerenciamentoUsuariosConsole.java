package visao;

import java.util.List;
import java.util.Scanner;

import controle.GerenciadorUsuarios;
import dominio.Usuario;

public class UIGerenciamentoUsuariosConsole implements UIGerenciamentoUsuarios {

	private Scanner in = new Scanner(System.in);
	private GerenciadorUsuarios gerenciadorUsuarios = new GerenciadorUsuarios();
	
	@Override
	public void cadastrarUsuario() {
		Usuario usuario = new Usuario();
		
		System.out.println("---------- Cadastrar Usuario ----------");
		System.out.print("Nome: ");
		usuario.setNome(in.nextLine());
		System.out.print("Login: ");
		usuario.setLogin(in.nextLine());
		System.out.print("Senha: ");
		usuario.setSenha(in.nextLine());
		
		gerenciadorUsuarios.cadastrarUsuario(usuario);
	}

	@Override
	public void removerUsuario() {
		Usuario usuario = new Usuario();
		
		System.out.println("---------- Remover Usuario ----------");
		System.out.print("Login: ");
		usuario.setLogin(in.nextLine());
		
		gerenciadorUsuarios.removerUsuario(usuario);
	}

	@Override
	public void listarUsuarios() {
		List<Usuario> usuarios = gerenciadorUsuarios.listarUsuarios();
		
		System.out.println("---------- Lista de Usuarios ----------");
		
		for(Usuario usuario : usuarios) {
			System.out.print("Nome: " + usuario.getNome());
			System.out.print(" - Login: " + usuario.getLogin());
			System.out.print(" - Senha: " + usuario.getSenha());
			System.out.println();
		}
	}

}
