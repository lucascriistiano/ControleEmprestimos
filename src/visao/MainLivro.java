package visao;

import java.util.Calendar;
import java.util.Scanner;






//************ TEMPORARIO ************
import dao.DaoCliente;
import dao.DaoClienteMemoria;
import dao.DaoRecurso;
import dao.DaoRecursoMemoria;
import dao.DaoUsuario;
import dao.DaoUsuarioMemoria;
//*************************************

import dominio.Aluno;
import dominio.Livro;
import dominio.Professor;
import dominio.Recurso;
import dominio.Usuario;
import excecao.DataException;

public class MainLivro {
	private static Scanner in = new Scanner(System.in);
	
	private static UIGerenciamentoClientes uiClientes = new UIGerenciamentoClientesConsoleLivro();
	private static UIGerenciamentoUsuarios uiUsuarios = new UIGerenciamentoUsuariosConsole();
	private static UIGerenciamentoRecursos uiRecursos = new UIGerenciamentoRecursosConsoleLivro();
	private static UIGerenciamentoEmprestimos uiEmprestimos = new UIGerenciamentoEmprestimosConsoleLivro();
	
	public static void main(String [] args) {
		//************ TEMPORARIO ************
		populateDAOs();
		//************************************
		
		//Implementacao do menu de opcoes
		int option;
		
		do {
			System.out.println("---------- Gerenciamento de Emprestimos de Livros ----------");
			System.out.println("1 - Gerenciar Usuarios");
			System.out.println("2 - Gerenciar Clientes");
			System.out.println("3 - Gerenciar Recursos");
			System.out.println("4 - Gerenciar Emprestimos");
			System.out.println("0 - Sair");
			
			System.out.print("Opcao desejada: ");
			option = in.nextInt();
			
			clearConsole();
			
			switch (option) {
			case 1:
				showMenuUIUsuarios();
				break;
			case 2:
				showMenuUIClientes();
				break;
			case 3:
				showMenuUIRecursos();
				break;
			case 4:
				showMenuUIEmprestimos();
				break;
			default:
				break;
			}
		} while(option > 0);
	}
 
	private static void populateDAOs() {
		DaoUsuario daoUsuario = DaoUsuarioMemoria.getInstance();
		Usuario usuario1 = new Usuario("João da Silva", "joao", "123456");
		Usuario usuario2 = new Usuario("Regina Costa", "regina", "456789");
		
		try {
			daoUsuario.add(usuario1);
			daoUsuario.add(usuario2);
		} catch (DataException e) {
			System.out.println("Não foi possível adicionar o usuario. Erro: " + e.getMessage());
			e.printStackTrace();
		}
		
		DaoRecurso daoRecurso = DaoRecursoMemoria.getInstance();
		Recurso livro1 = new Livro(Long.valueOf(1), "Livro muito bom", "Cormem", "Editora desconheciada1", 3, 50, "Algoritmos: Teoria e Pr�tica");
		Recurso livro2 = new Livro(Long.valueOf(2), "Livro bom", "Machado de Assis", "Editora desconheciada2", 1, 10, "Capitu");
		Recurso livro3 = new Livro(Long.valueOf(3), "Livro legal", "Jos� de Alencar", "Editora desconheciada3", 1, 5, "Iracema");
		
		try {
			daoRecurso.add(livro1);
			daoRecurso.add(livro2);
			daoRecurso.add(livro3);
		} catch (DataException e) {
			System.out.println("Não foi possível adicionar o recurso. Erro: " + e.getMessage());
			e.printStackTrace();
		}
		
		DaoCliente daoCliente = DaoClienteMemoria.getInstance();
		
		Aluno aluno1 = new Aluno(Long.valueOf(1), "Sidemar", "777.777.777-77", "777.777.777", Long.valueOf(7777), "T.I");
		Calendar calendar = Calendar.getInstance();
		calendar.set(Calendar.DAY_OF_MONTH, 27);
		calendar.set(Calendar.MONTH, 5);
		calendar.set(Calendar.YEAR, 1990);
		Professor professor1 = new Professor(Long.valueOf(2), "Lucas", "999.999.999-99", "999.999.999", "doutor", calendar.getTime());
		
		try {
			daoCliente.add(aluno1);
			daoCliente.add(professor1);
		} catch (DataException e) {
			System.out.println("Não foi possível adicionar o cliente. Erro: " + e.getMessage());
			e.printStackTrace();
		}	
	}

	private static void showMenuUIClientes() {
		int option;
		
		do {
			System.out.println("---------- Gerenciamento de Clientes ----------");
			System.out.println("1 - Cadastrar Novo Cliente");
			System.out.println("2 - Remover Cliente");
			System.out.println("3 - Listar Clientes");
			
			System.out.println("0 - Voltar");
			
			System.out.print("Opcao desejada: ");
			option = in.nextInt();
			
			clearConsole();
			
			switch (option) {
			case 1:
				uiClientes.cadastrarCliente();
				break;
			case 2:
				uiClientes.removerCliente();
				break;
			case 3:
				uiClientes.listarClientes();
				break;
			default:
				return;
			}
		} while(option > 0);
	}
	
	private static void showMenuUIEmprestimos() {
		int option;
		
		do {
			System.out.println("---------- Gerenciamento de Emprestimos ----------");
			System.out.println("1 - Realizar Novo Emprestimo");
			System.out.println("2 - Realizar Devolucao");
			System.out.println("3 - Listar Emprestimos");
			System.out.println("4 - Verificar Prazos");
			
			System.out.println("0 - Voltar");
			
			System.out.print("Opcao desejada: ");
			option = in.nextInt();
			
			clearConsole();
			
			switch (option) {
			case 1:
				uiEmprestimos.realizarEmprestimo();
				break;
			case 2:
				uiEmprestimos.realizarDevolucao();
				break;
			case 3:
				uiEmprestimos.listarEmprestimos();
				break;
			case 4:
				uiEmprestimos.verificarPrazos();
				break;
			default:
				return;
			}
		} while(option > 0);
	}
	
	private static void showMenuUIRecursos() {
		int option;
		
		do {
			System.out.println("---------- Gerenciamento de Recursos ----------");
			System.out.println("1 - Cadastrar Novo Recurso");
			System.out.println("2 - Remover Recurso");
			System.out.println("3 - Listar Recursos");
			
			System.out.println("0 - Voltar");
			
			System.out.print("Opcao desejada: ");
			option = in.nextInt();
			
			clearConsole();
			
			switch (option) {
			case 1:
				uiRecursos.cadastrarRecurso();
				break;
			case 2:
				uiRecursos.removerRecurso();
				break;
			case 3:
				uiRecursos.listarRecursos();
				break;
			default:
				return;
			}
		} while(option > 0);
	}
	
	private static void showMenuUIUsuarios() {
		int option;
		
		do {
			System.out.println("---------- Gerenciamento de Usuarios ----------");
			System.out.println("1 - Cadastrar Novo Usuario");
			System.out.println("2 - Remover Usuario");
			System.out.println("3 - Listar Usuarios");
			
			System.out.println("0 - Voltar");
			
			System.out.print("Opcao desejada: ");
			option = in.nextInt();
			
			clearConsole();
			
			switch (option) {
			case 1:
				uiUsuarios.cadastrarUsuario();
				break;
			case 2:
				uiUsuarios.removerUsuario();
				break;
			case 3:
				uiUsuarios.listarUsuarios();
				break;
			default:
				return;
			}
		} while(option > 0);
	}
	
	public final static void clearConsole()
	{
	    try
	    {
	        final String os = System.getProperty("os.name");
	        
	        if (os.contains("Windows"))
	        	Runtime.getRuntime().exec("cmd /c cls");
	        else
	            Runtime.getRuntime().exec("clear");
	    }
	    catch (final Exception e)
	    {
	    	System.out.println("Erro ao limpar console. Erro: " + e.getMessage());
	    	e.printStackTrace();
	    }
	}
}