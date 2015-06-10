package instanciabiblioteca;

import java.text.SimpleDateFormat;
import java.util.Date;
import java.util.List;

import dominio.ComprovanteDevolucao;
import dominio.Recurso;

public class ComprovanteDevolucaoBiblioteca extends ComprovanteDevolucao {
    
	public ComprovanteDevolucaoBiblioteca(String empresa, String locador, Long codigo, Date dataEmprestimo, Date dataDevolucao, List<Recurso> recursos) {
		super(empresa, locador, codigo, dataEmprestimo, dataDevolucao, recursos, 0);
	}

	@Override
	public void imprimir() {
		System.out.println("------- " + this.getEmpresa() + " -------");
		
		System.out.println("----- Comprovante de Devolucao -----");
		System.out.println("Codigo do aluguel: " + this.getCodigo());
		System.out.println("Nome do locador: " + this.getLocador());
		System.out.println("Data de emprestimo: " + new SimpleDateFormat("dd/MM/yyyy").format(this.getDataEmprestimo()));
		System.out.println("Data da devolucao: " + new SimpleDateFormat("dd/MM/yyyy").format(this.getDataDevolucao()));
		
		System.out.println("Lista de Livros Alugados: ");
		for (Recurso recurso : getRecursos()) {
			Livro livro = (Livro) recurso;
			
			System.out.print("Codigo: " + livro.getCodigo());
			System.out.print(" - Descricao: " + livro.getDescricao());
			System.out.print(" - Autor: " + livro.getAutor());
			System.out.print(" - Editora: " + livro.getEditora());
			System.out.print(" - Edicao: " + livro.getEdicao());
			System.out.print(" - Quantidade: " + livro.getQuantidade());
			System.out.print(" - Titulo: " + livro.getTitulo());
			System.out.println();
		}
	}
}