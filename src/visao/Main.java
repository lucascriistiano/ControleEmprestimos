package visao;

import java.text.SimpleDateFormat;
import java.util.ArrayList;
import java.util.Calendar;
import java.util.Scanner;

import controle.GerenciadorEmprestimos;
import dao.DaoCliente;
import dao.DaoClienteMemoria;
import dao.DaoEmprestimo;
import dao.DaoEmprestimoMemoria;
import dao.DaoRecurso;
import dao.DaoRecursoMemoria;
import dao.DaoUsuario;
import dao.DaoUsuarioMemoria;
import dominio.Carro;
import dominio.ClienteLocador;
import dominio.Emprestimo;
import dominio.Recurso;
import dominio.Usuario;

public class Main {
	private static Scanner in = new Scanner(System.in);
	private static UIGerenciamentoClientes uiClientes = new UIGerenciamentoClientesConsole();
	private static UIGerenciamentoUsuarios uiUsuarios = new UIGerenciamentoUsuariosConsole();
	private static UIGerenciamentoRecursos uiRecursos = new UIGerenciamentoRecursosConsole();
	private static UIGerenciamentoEmprestimos uiEmprestimos = new UIGerenciamentoEmprestimosConsole();
	
	public static void main(String [] args) {
		//************ TEMPORÁRIO ************
		DaoUsuario daoUsuario = DaoUsuarioMemoria.getInstance();
		Usuario usuario1 = new Usuario("João da Silva", "joao", "123456");
		Usuario usuario2 = new Usuario("Regina Costa", "regina", "456789");
		
		daoUsuario.add(usuario1);
		daoUsuario.add(usuario2);
		
		DaoRecurso daoRecurso = DaoRecursoMemoria.getInstance();
		Carro carro1 = new Carro(Long.valueOf(1),"Chevrolet Meriva 2002. Veículo super agradável","ABC-1234","Meriva","Chevrolet","Prata",40.5);
		Carro carro2 = new Carro(Long.valueOf(2),"VW Gol 2010. Veículo muito confortável","DEF-4567","Gol","Volkswagem","Branco",50);
		Carro carro3 = new Carro(Long.valueOf(3),"Ford Ka 2007. Veículo muito pequeno","HIJ-8901","Ka","Ford","Rosa",30);
		
		daoRecurso.add(carro1);
		daoRecurso.add(carro2);
		//************************************
		
		//---------- Implementação do menu de opções ----------
		int option;
		
		do {
			System.out.println("---------- Gerenciamento de Empréstimos de Veículos ----------");
			System.out.println("1 - Gerenciar Usuarios");
			System.out.println("2 - Gerenciar Clientes");
			System.out.println("3 - Gerenciar Recursos");
			System.out.println("4 - Gerenciar Emprestimos");
			System.out.println("0 - Sair");
			
			System.out.print("Opcao desejada: ");
			option = in.nextInt();
			
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
			
			clearConsole();
		} while(option > 0);

		//************ TEMPORÁRIO ************
//		DaoCliente daoCliente = DaoClienteMemoria.getInstance();
//		ClienteLocador cliente1 = new ClienteLocador(Long.valueOf(1), "Pedro Inácio", "123.456.789-10", "123.456", "1233456784");
//		ClienteLocador cliente2 = new ClienteLocador(Long.valueOf(1), "Juvenal da Costa", "456.890.123-22", "342.312", "7125782334");
//		
//		daoCliente.add(cliente1);
//		daoCliente.add(cliente2);
//		
//		ArrayList<Recurso> recursos1 = new ArrayList<Recurso>();
//		recursos1.add(carro1);
//		recursos1.add(carro2);
//		
//		ArrayList<Recurso> recursos2 = new ArrayList<Recurso>();
//		recursos2.add(carro3);
//		
//		//SIMULACAO DE EMPRESTIMOS
//		GerenciadorEmprestimos gerenciadorEmprestimos = new GerenciadorEmprestimos();
//		
//		//----- EMPRESTIMO 01 (SEM DATA DEFINIDA) -----
//		gerenciadorEmprestimos.realizarEmprestimo(usuario1, cliente1, recursos1);
//		
//		//----- EMPRESTIMO 02 (COM DATA DEFINIDA) -----
//		Calendar calendar = Calendar.getInstance();
//		calendar.add(Calendar.DAY_OF_MONTH, 30);
//		
//		gerenciadorEmprestimos.realizarEmprestimo(usuario2, cliente2, recursos2, calendar.getTime());
//
//		//Listagem de emprestimos
//		DaoEmprestimo daoEmprestimo = DaoEmprestimoMemoria.getInstance();
//		for(Emprestimo emprestimo : daoEmprestimo.list()) {
//			System.out.println("Codigo: " + emprestimo.getCodigo());
//			System.out.println("Data Emprestimo: " + new SimpleDateFormat("dd/MM/yyyy").format(emprestimo.getDataEmprestimo()));
//			System.out.println("Data Devolução: " + new SimpleDateFormat("dd/MM/yyyy").format(emprestimo.getDataDevolucao()));
//			System.out.println("Usuario: " + emprestimo.getUsuario().getNome());
//			System.out.println("Cliente: " + emprestimo.getCliente().getNome());
//			
//			System.out.println("Recursos: ");
//			for(Recurso recurso : emprestimo.getRecursos()) {
//				System.out.println(" - " + recurso.getDescricao());
//			}
//			System.out.println();
//		}
		//************************************
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
			
			System.out.println("0 - Voltar");
			
			System.out.print("Opcao desejada: ");
			option = in.nextInt();
			
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
	            Runtime.getRuntime().exec("cls");
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