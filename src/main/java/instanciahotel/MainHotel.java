package instanciahotel;

import java.util.Calendar;
import java.util.Scanner;

import dao.Dao;
import dao.DaoCliente;
import dao.DaoRecurso;
import dao.DaoUsuario;
import dominio.Cliente;
//*************************************
import dominio.Recurso;
import dominio.Usuario;
import excecao.DataException;
import visao.UIGerenciamentoClientes;
import visao.UIGerenciamentoEmprestimos;
import visao.UIGerenciamentoRecursos;
import visao.UIGerenciamentoUsuarios;
import visao.UIGerenciamentoUsuariosConsole;

public class MainHotel {
	private static Scanner in = new Scanner(System.in);
	
	private static UIGerenciamentoClientes uiClientes = new UIGerenciamentoClientesHotel();
	private static UIGerenciamentoUsuarios uiUsuarios = new UIGerenciamentoUsuariosConsole();
	private static UIGerenciamentoRecursos uiRecursos = new UIGerenciamentoRecursosHotel();
	private static UIGerenciamentoEmprestimos uiEmprestimos = new UIGerenciamentoEmprestimosHotel();
	
	public static void main(String [] args) {
		//************ TEMPORARIO ************
		populateDAOs();
		//************************************
		
		//Implementacao do menu de opcoes
		int option;
		
		do {
			System.out.println("---------- Gerenciamento de Emprestimos de Quartos ----------");
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
		DaoUsuario daoUsuario = DaoUsuario.getInstance();
		Usuario usuario1 = new Usuario("Joao da Silva", "joao", "123456");
		Usuario usuario2 = new Usuario("Regina Costa", "regina", "456789");
		
		try {
			daoUsuario.add(usuario1);
			daoUsuario.add(usuario2);
		} catch (DataException e) {
			System.out.println("Não foi possível adicionar o usuario. Erro: " + e.getMessage());
			e.printStackTrace();
		}
		
		DaoRecurso daoRecurso = DaoRecurso.getInstance();
		Recurso quarto1 = new Quarto("1 andar", 1, 700, 1, 2, 1000);
		Recurso quarto2 = new Quarto("2 andar", 2, 500, 2, 3, 2000);
		Recurso quarto3 = new Quarto("3 andar", 2, 600, 3, 4, 5000);
				
		try {
			daoRecurso.add(quarto1);
			daoRecurso.add(quarto2);
			daoRecurso.add(quarto3);
		} catch (DataException e) {
			System.out.println("Nao foi possivel adicionar o recurso. Erro: " + e.getMessage());
			e.printStackTrace();
		}
		
		Dao<Cliente> daoCliente = DaoCliente.getInstance();
		
		Calendar calendar = Calendar.getInstance();
		calendar.set(Calendar.DAY_OF_MONTH, 27);
		calendar.set(Calendar.MONTH, 5);
		calendar.set(Calendar.YEAR, 1990);
		ClienteHotel cliente1 = new ClienteHotel("Pedro Inacio", "123.456.789-10", "endereco1", "1233456784",calendar.getTime());
		
		calendar.set(Calendar.DAY_OF_MONTH, 31);
		calendar.set(Calendar.MONTH, 4);
		calendar.set(Calendar.YEAR, 1965);
		ClienteHotel cliente2 = new ClienteHotel("Juvenal da Costa", "456.890.123-22", "endereco2", "7125782334",calendar.getTime());
		
		try {
			daoCliente.add(cliente1);
			daoCliente.add(cliente2);
		} catch (DataException e) {
			System.out.println("Nao foi possivel adicionar o cliente. Erro: " + e.getMessage());
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
			System.out.println("5 - Sugerir Emprestimos");
			
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
			case 5:
				uiEmprestimos.sugerirEmprestimos();
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