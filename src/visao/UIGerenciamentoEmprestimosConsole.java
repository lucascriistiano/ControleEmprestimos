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
import dominio.ComprovanteDevolucao;
import dominio.ComprovanteDevolucaoBuilderCarro;
import dominio.ComprovanteEmprestimo;
import dominio.ComprovanteEmprestimoBuilderCarro;
import dominio.Emprestimo;
import dominio.Recurso;
import dominio.RegraLocadoraCarros;
import dominio.Usuario;
import excecao.ClienteInvalidoException;
import excecao.DataException;
import excecao.EmprestimoInvalidoException;
import excecao.RecursoInvalidoException;

public class UIGerenciamentoEmprestimosConsole implements UIGerenciamentoEmprestimos {

	private Scanner in = new Scanner(System.in);
	
	private GerenciadorUsuarios gerenciadorUsuarios = new GerenciadorUsuarios();
	private GerenciadorClientes gerenciadorClientes = new GerenciadorClientes();
	private GerenciadorRecursos gerenciadorRecursos = new GerenciadorRecursos();
	private GerenciadorEmprestimos gerenciadorEmprestimos = new GerenciadorEmprestimos(new RegraLocadoraCarros(), new ComprovanteEmprestimoBuilderCarro(), new ComprovanteDevolucaoBuilderCarro());
	
	@Override
	public void realizarEmprestimo() {
		
		try {
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
			
			Date dataDevolucao = dateFormat.parse(strDataDevolucao);
			ComprovanteEmprestimo comprovanteEmprestimo = gerenciadorEmprestimos.realizarEmprestimo(usuario, cliente, recursos, dataDevolucao);
			System.out.println("Emprestimo realizado!");
			System.out.println();
			comprovanteEmprestimo.imprimir();
			
		} catch (DataException e) {
			System.out.println("Erro ao armazenar dados do emprestimo. Erro: " + e.getMessage());
		} catch (ParseException e) {
			System.out.println("Erro ao cadastrar data de devolucao. Verifique o formato inserido.");
		} catch (ClienteInvalidoException e) {
			System.out.println("Cliente invalido selecionado. Erro: " + e.getMessage());
		} catch (EmprestimoInvalidoException e) {
			System.out.println("Emprestimo invalido. Erro: " + e.getMessage());
		} catch (RecursoInvalidoException e) {
			System.out.println("Recurso invalido selecionado. Erro: " + e.getMessage());
		}
	}

	@Override
	public void realizarDevolucao() {
		
		try {
			System.out.println("---------- Realizar Devolucao ----------");
			
			System.out.print("Codigo do emprestimo: ");
			Long codigo = in.nextLong();
			in.nextLine();
			
			Emprestimo emprestimo = gerenciadorEmprestimos.getEmprestimo(codigo);
		
		
			for(Recurso recurso : emprestimo.getRecursos()) {
				int quilometragemInicial = ((Carro) recurso).getQuilometragemInicial();
				int quilometragemAtual;
				
				do {
					System.out.print("Quilometragem atual do veiculo de placa " + ((Carro) recurso).getPlaca() + ": ");
					quilometragemAtual = in.nextInt();
					
					if(quilometragemAtual < quilometragemInicial)
						System.out.print("A quilometragem atual do veiculo nao pode ser menor do que no momento do emprestimo.");
				} while(quilometragemAtual < quilometragemInicial);
				
				((Carro) recurso).setQuilometragemFinal(quilometragemAtual);
			}
			
			System.out.print("Taxa extra: R$ ");
			double taxaExtra = in.nextDouble();
			
			ComprovanteDevolucao comprovanteDevolucao = gerenciadorEmprestimos.realizarDevolucao(emprestimo,taxaExtra);
			System.out.println("Emprestimo finalizado!");
			System.out.println();
			comprovanteDevolucao.imprimir();
		} catch (DataException e) {
			System.out.println("Erro ao armazenar dados da devolucao. Erro: " + e.getMessage());
		}
	}

	@Override
	public void listarEmprestimos() {
		try {
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
		} catch (DataException e) {
			System.out.println("Erro ao recuperar registros dos emprestimos. Erro: " + e.getMessage());
		}
	}

}
