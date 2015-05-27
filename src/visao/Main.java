package visao;

import java.text.SimpleDateFormat;
import java.util.ArrayList;
import java.util.Calendar;

import dao.DaoCliente;
import dao.DaoClienteMemory;
import dao.DaoEmprestimo;
import dao.DaoEmprestimoMemory;
import dao.DaoRecurso;
import dao.DaoRecursoMemory;
import dao.DaoUsuario;
import dao.DaoUsuarioMemory;

import dominio.Carro;
import dominio.ClienteLocador;
import dominio.Emprestimo;
import dominio.Recurso;
import dominio.Usuario;

public class Main {
	public static void main(String [] args) {
		DaoUsuario daoUsuario = DaoUsuarioMemory.getInstance();
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
		
		DaoRecurso daoRecurso = DaoRecursoMemory.getInstance();
		Carro carro1 = new Carro(Long.valueOf(1),"Chevrolet Meriva 2002. Veículo super agradável","ABC-1234","Meriva","Chevrolet","Prata",40.5);
		Carro carro2 = new Carro(Long.valueOf(2),"Gol VW 2010. Veículo muito confortável","DEF-4567","Gol","Volkswagem","Branco",50);
		
		daoRecurso.add(carro1);
		daoRecurso.add(carro2);
		
		for(Recurso recurso : daoRecurso.list()) {
			System.out.println("Codigo: " + recurso.getCodigo());
			System.out.println("Descricao: " + recurso.getDescricao());
			System.out.println();
		}
		
		DaoCliente daoCliente = DaoClienteMemory.getInstance();
		ClienteLocador cliente1 = new ClienteLocador(Long.valueOf(1), "Pedro Inácio", "123.456.789-10", "123.456", "1233456784");
		ClienteLocador cliente2 = new ClienteLocador(Long.valueOf(1), "Juvenal da Costa", "456.890.123-22", "342.312", "7125782334");
		
		daoCliente.add(cliente1);
		daoCliente.add(cliente2);
		
		Calendar cal = Calendar.getInstance();
		ArrayList<Recurso> recursos = new ArrayList<Recurso>();
		recursos.add(carro1);
		recursos.add(carro2);
		
		DaoEmprestimo daoEmprestimo = DaoEmprestimoMemory.getInstance();
		daoEmprestimo.add(new Emprestimo(Long.valueOf(1), cal.getTime(),usuario1,cliente1, recursos));
		
		for(Emprestimo emprestimo : daoEmprestimo.list()) {
			System.out.println("Codigo: " + emprestimo.getCodigo());
			System.out.println("Data: " + new SimpleDateFormat("dd/MM/yyyy").format(emprestimo.getData()));
			System.out.println("Usuario: " + emprestimo.getUsuario().getNome());
			System.out.println("Cliente: " + emprestimo.getCliente().getNome());
			for(Recurso recurso : emprestimo.getRecursos()) {
				System.out.println("Recurso: " + recurso.getDescricao());
			}
			System.out.println();
		}
	}
}