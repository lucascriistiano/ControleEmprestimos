package visao;

import java.text.SimpleDateFormat;
import java.util.ArrayList;
import java.util.Calendar;

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
	public static void main(String [] args) {
		DaoUsuario daoUsuario = DaoUsuarioMemoria.getInstance();
		Usuario usuario1 = new Usuario("João da Silva", "joao", "123456");
		Usuario usuario2 = new Usuario("Regina Costa", "regina", "456789");
		
		daoUsuario.add(usuario1);
		daoUsuario.add(usuario2);
		
		for(Usuario usuario : daoUsuario.list()) {
			System.out.println("Nome: " + usuario.getNome());
			System.out.println("Login: " + usuario.getLogin());
			System.out.println("Senha: " + usuario.getSenha());
			System.out.println();
		}
		
		DaoRecurso daoRecurso = DaoRecursoMemoria.getInstance();
		Carro carro1 = new Carro(Long.valueOf(1),"Chevrolet Meriva 2002. Veículo super agradável","ABC-1234","Meriva","Chevrolet","Prata",40.5);
		Carro carro2 = new Carro(Long.valueOf(2),"VW Gol 2010. Veículo muito confortável","DEF-4567","Gol","Volkswagem","Branco",50);
		Carro carro3 = new Carro(Long.valueOf(3),"Ford Ka 2007. Veículo muito pequeno","HIJ-8901","Ka","Ford","Rosa",30);
		
		daoRecurso.add(carro1);
		daoRecurso.add(carro2);
		
		for(Recurso recurso : daoRecurso.list()) {
			System.out.println("Codigo: " + recurso.getCodigo());
			System.out.println("Descricao: " + recurso.getDescricao());
			System.out.println();
		}
		
		DaoCliente daoCliente = DaoClienteMemoria.getInstance();
		ClienteLocador cliente1 = new ClienteLocador(Long.valueOf(1), "Pedro Inácio", "123.456.789-10", "123.456", "1233456784");
		ClienteLocador cliente2 = new ClienteLocador(Long.valueOf(1), "Juvenal da Costa", "456.890.123-22", "342.312", "7125782334");
		
		daoCliente.add(cliente1);
		daoCliente.add(cliente2);
		
		ArrayList<Recurso> recursos1 = new ArrayList<Recurso>();
		recursos1.add(carro1);
		recursos1.add(carro2);
		
		ArrayList<Recurso> recursos2 = new ArrayList<Recurso>();
		recursos2.add(carro3);
		
		//SIMULACAO DE EMPRESTIMOS
		GerenciadorEmprestimos gerenciadorEmprestimos = new GerenciadorEmprestimos();
		
		//----- EMPRESTIMO 01 (SEM DATA DEFINIDA) -----
		gerenciadorEmprestimos.realizarEmprestimo(usuario1, cliente1, recursos1);
		
		//----- EMPRESTIMO 02 (COM DATA DEFINIDA) -----
		Calendar calendar = Calendar.getInstance();
		calendar.add(Calendar.DAY_OF_MONTH, 30);
		
		gerenciadorEmprestimos.realizarEmprestimo(usuario2, cliente2, recursos2, calendar.getTime());

		//Listagem de emprestimos
		DaoEmprestimo daoEmprestimo = DaoEmprestimoMemoria.getInstance();
		for(Emprestimo emprestimo : daoEmprestimo.list()) {
			System.out.println("Codigo: " + emprestimo.getCodigo());
			System.out.println("Data Emprestimo: " + new SimpleDateFormat("dd/MM/yyyy").format(emprestimo.getDataEmprestimo()));
			System.out.println("Data Devolução: " + new SimpleDateFormat("dd/MM/yyyy").format(emprestimo.getDataDevolucao()));
			System.out.println("Usuario: " + emprestimo.getUsuario().getNome());
			System.out.println("Cliente: " + emprestimo.getCliente().getNome());
			
			System.out.println("Recursos: ");
			for(Recurso recurso : emprestimo.getRecursos()) {
				System.out.println(" - " + recurso.getDescricao());
			}
			System.out.println();
		}
	}
}