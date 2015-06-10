package visao;

import java.util.List;
import java.util.Scanner;

import controle.GerenciadorRecursos;
import dominio.Carro;
import dominio.Livro;
import dominio.Recurso;
import excecao.DataException;

public class UIGerenciamentoRecursosConsoleLivro implements UIGerenciamentoRecursos {

	private GerenciadorRecursos gerenciadorRecursos = new GerenciadorRecursos();
	private Scanner in = new Scanner(System.in);
	
	@Override
	public void cadastrarRecurso() {
		try {
			System.out.println("---------- Cadastrar Livro ----------");
			
			System.out.print("Codigo: ");			
			Long codigo = in.nextLong();
			in.nextLine();
			System.out.print("Descri��o: ");
			String descricao = in.nextLine();
			System.out.print("Autor: ");
			String autor = in.nextLine();
			System.out.print("Editora: ");
			String editora = in.nextLine();
			System.out.print("Edi��o: ");
			Integer edicao = in.nextInt();
			System.out.print("Quantidade: ");
			Integer quantidade = in.nextInt();
			System.out.print("T�tulo: ");
			String titulo = in.nextLine();
			
			Recurso recurso = new Livro(codigo, descricao, autor, editora, edicao, quantidade, titulo);
			
			gerenciadorRecursos.cadastrarRecurso(recurso);
		} catch (DataException e) {
			System.out.println("Erro ao armazenar dados do recurso. Erro: " + e.getMessage());
		}
	}

	@Override
	public void removerRecurso() {
		try {
			System.out.println("---------- Remover Livro ----------");
		
			System.out.print("Codigo: ");
			Long codigo = in.nextLong();
			in.nextLine();
			
			Recurso recurso = new Livro(codigo,"");
		
			gerenciadorRecursos.removerRecurso(recurso);
		} catch (DataException e) {
			System.out.println("Erro ao remover registro do recurso. Erro: " + e.getMessage());
		}
	}

	@Override
	public void listarRecursos() {
		try {
			List<Recurso> recursos = gerenciadorRecursos.listarRecursos();
		
			System.out.println("---------- Lista de Livros ----------");
			
			for(Recurso recurso : recursos) {
				Livro livro = (Livro) recurso;
				
				System.out.print("Codigo: " + livro.getCodigo());
				System.out.print(" - Descricao: " + livro.getDescricao());
				System.out.print(" - Autor: " + livro.getAutor());
				System.out.print(" - Editora: " + livro.getEditora());
				System.out.print(" - Edi��o: " + livro.getEdicao());
				System.out.print(" - Quantidade: " + livro.getQuantidade());
				System.out.print(" - T�tulo: " + livro.getTitulo());
				System.out.println();
			}
		} catch (DataException e) {
			System.out.println("Erro ao recuperar registros dos recursos. Erro: " + e.getMessage());
		}
	}

}
