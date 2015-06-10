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
import dominio.Cliente;
import dominio.ComprovanteDevolucao;
import dominio.ComprovanteDevolucaoBuilderLivro;
import dominio.ComprovanteEmprestimo;
import dominio.ComprovanteEmprestimoBuilderLivro;
import dominio.Emprestimo;
import dominio.FabricaNotificacaoLivro;
import dominio.Livro;
import dominio.Recurso;
import dominio.RegraBiblioteca;
import dominio.Usuario;
import excecao.ClienteInvalidoException;
import excecao.DataException;
import excecao.EmprestimoInvalidoException;
import excecao.RecursoInvalidoException;

public class UIGerenciamentoEmprestimosConsoleLivro implements UIGerenciamentoEmprestimos {

	private Scanner in = new Scanner(System.in);
	
	private GerenciadorUsuarios gerenciadorUsuarios = new GerenciadorUsuarios();
	private GerenciadorClientes gerenciadorClientes = new GerenciadorClientes();
	private GerenciadorRecursos gerenciadorRecursos = new GerenciadorRecursos();
	private GerenciadorEmprestimos gerenciadorEmprestimos = new GerenciadorEmprestimos(new RegraBiblioteca(), new ComprovanteEmprestimoBuilderLivro(), new ComprovanteDevolucaoBuilderLivro(), new FabricaNotificacaoLivro());
	
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
				System.out.print("Codigo do livro: ");
				Long codigoRecurso = in.nextLong();
				in.nextLine();
				
				Livro recurso = (Livro) gerenciadorRecursos.getRecurso(codigoRecurso);
				
				if(!recursos.contains(recurso)) {
					recursos.add(recurso);
					
					System.out.print("Livro Adicionado => ");
					System.out.print("Descricao: " + recurso.getDescricao());
					System.out.print(" - Autor: " + recurso.getAutor());
					System.out.print(" - Editora: " + recurso.getEditora());
					System.out.print(" - Edição: " + recurso.getEdicao());
					System.out.print(" - Quantidade: " + recurso.getQuantidade());
					System.out.print(" - Título: " + recurso.getTitulo());
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
		
			/*
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
			}*/
			
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
						Livro livro = (Livro) recurso;
						
						System.out.print("Codigo: " + livro.getCodigo());
						System.out.print(" - Descricao: " + livro.getDescricao());
						System.out.print(" - Autor: " + livro.getAutor());
						System.out.print(" - Editora: " + livro.getEditora());
						System.out.print(" - Edição: " + livro.getEdicao());
						System.out.print(" - Quantidade: " + livro.getQuantidade());
						System.out.print(" - Título: " + livro.getTitulo());
						System.out.println();
					}
					System.out.println();
				}
			}
			else {
				System.out.println("Nao existem empréstimos em aberto.");
			}
		} catch (DataException e) {
			System.out.println("Erro ao recuperar registros dos emprestimos. Erro: " + e.getMessage());
		}
	}

	@Override
	public void verificarPrazos() {
		try {
			System.out.println("---------- Verificar Prazos de Emprestimos ----------");
			System.out.println("Verificando prazos. Aguarde... ");
		
			if(this.gerenciadorEmprestimos.verificarPrazos()) { //Existiram empréstimos notificados
				System.out.println("Os usuarios com empréstimos pendentes foram devidamente notificados.");
			}
			else {
				System.out.println("Nao houveram usuarios notificados.");
			}
			
		} catch (DataException e) {
			System.out.println("Erro ao acessar registros dos emprestimos. Erro: " + e.getMessage());
		};
	}

}
