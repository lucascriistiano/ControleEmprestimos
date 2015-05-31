package visao;

import java.text.ParseException;
import java.text.SimpleDateFormat;
import java.util.ArrayList;
import java.util.Date;
import java.util.List;
import java.util.Scanner;

import controle.GerenciadorClientes;
import controle.GerenciadorEmprestimos;
import controle.GerenciadorRecursos;
import controle.GerenciadorUsuarios;
import dominio.Carro;
import dominio.Cliente;
import dominio.Emprestimo;
import dominio.Recurso;
import dominio.Usuario;

public class UIGerenciamentoEmprestimosConsole implements UIGerenciamentoEmprestimos {

	private Scanner in = new Scanner(System.in);
	
	private GerenciadorUsuarios gerenciadorUsuarios = new GerenciadorUsuarios();
	private GerenciadorClientes gerenciadorClientes = new GerenciadorClientes();
	private GerenciadorRecursos gerenciadorRecursos = new GerenciadorRecursos();
	private GerenciadorEmprestimos gerenciadorEmprestimos = new GerenciadorEmprestimos();
	
	@Override
	public void realizarEmprestimo() {
		System.out.println("---------- Realizar Emprestimo ----------");
		System.out.print("Login do usuario: ");
		String login = in.nextLine();
		Usuario usuario = gerenciadorUsuarios.getUsuario(login);
		
		System.out.print("Codigo do cliente: ");
		Long codigoCliente = in.nextLong();
		in.nextLine();
		Cliente cliente = gerenciadorClientes.getCliente(codigoCliente);
		
		String continuar = "N";
		List<Recurso> recursos = new ArrayList<Recurso>(); 
		
		do {
			System.out.print("Codigo do veiculo: ");
			Long codigoRecurso = in.nextLong();
			in.nextLine();
			
			Carro recurso = (Carro) gerenciadorRecursos.getRecurso(codigoRecurso);
			if(!recursos.contains(recurso)) {
				recursos.add(recurso);
				
				System.out.print("Veiculo Adicionado => ");
				System.out.print("Descricao: " + recurso.getDescricao());
				System.out.print(" - Placa: " + recurso.getPlaca());
				System.out.print(" - Modelo: " + recurso.getModelo());
				System.out.print(" - Fabricante: " + recurso.getFabricante());
				System.out.print(" - Cor: " + recurso.getCor());
				System.out.print(" - Preco (de aluguel): " + recurso.getPreco());
				System.out.println();
			}
			
			System.out.print("Deseja inserir outro item (S/N)? ");
			continuar = in.nextLine();
		} while(continuar.equals("S"));
		
		System.out.print("Data de Devolucao Prevista (dd/mm/aaaa): ");
		String strDataDevolucao = in.nextLine();
		SimpleDateFormat dateFormat = new SimpleDateFormat("dd/MM/yyyy");
		Date dataDevolucao;
		
		try {
			dataDevolucao = dateFormat.parse(strDataDevolucao);
			gerenciadorEmprestimos.realizarEmprestimo(usuario, cliente, recursos, dataDevolucao);
		} catch (ParseException e) {
			// TODO Auto-generated catch block
			System.out.println("Impossivel concretizar o emprestimo");
			e.printStackTrace();
		}
	}

	@Override
	public void realizarDevolucao() {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void listarEmprestimos() {
		List<Emprestimo> emprestimos = gerenciadorEmprestimos.listarEmprestimos();
		
		System.out.println("---------- Lista de Emprestimos ----------");
		
		if(emprestimos.size() > 0) {
			for(Emprestimo emprestimo : emprestimos) {
				System.out.print("Codigo: " + emprestimo.getCodigo());
				System.out.print(" - Usuario: " + emprestimo.getUsuario().getLogin());
				System.out.print(" - Cliente: " + emprestimo.getCliente().getNome());
				System.out.print(" - Data emprestimo: " + emprestimo.getDataEmprestimo());
				System.out.println(" - Data devolucao: " + emprestimo.getDataDevolucao());
				System.out.println("Recursos: ");
				
				for(Recurso recurso : emprestimo.getRecursos()) {
					Carro carro = (Carro) recurso;
					
					System.out.print("\tCodigo: " + carro.getCodigo());
					System.out.print(" - Descricao: " + carro.getDescricao());
					System.out.print(" - Placa: " + carro.getPlaca());
					System.out.print(" - Modelo: " + carro.getModelo());
					System.out.print(" - Fabricante: " + carro.getFabricante());
					System.out.print(" - Cor: " + carro.getCor());
					System.out.print(" - Preco de aluguel: " + carro.getPreco());
					System.out.println();
				}
				System.out.println();
			}
		}
		else {
			System.out.println("Nao existem alugueis em aberto.");
		}
	}

}
