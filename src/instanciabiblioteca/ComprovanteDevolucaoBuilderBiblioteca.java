package instanciabiblioteca;

import java.util.Date;
import java.util.List;

import dominio.ComprovanteDevolucao;
import dominio.ComprovanteDevolucaoBuilder;
import dominio.Recurso;

public class ComprovanteDevolucaoBuilderBiblioteca implements ComprovanteDevolucaoBuilder {

	private String locador;
	private Long codigo;
	private Date dataEmprestimo;
	private Date dataDevolucao;
    private List<Recurso> recursos;

	@Override
	public void buildLocador(String nomeLocador) {
		this.locador = nomeLocador;
	}
	
	@Override
	public void buildCodigo(Long codigo) {
		this.codigo = codigo;
	}

	@Override
	public void buildDataEmprestimo(Date dataEmprestimo) {
		this.dataEmprestimo = dataEmprestimo;
	}
	
	@Override
	public void buildDataDevolucao(Date dataDevolucao) {
		this.dataDevolucao = dataDevolucao;
	}
	
	@Override
	public void buildRecursos(List<Recurso> recursos) {
		this.recursos = recursos;		
	}
	
	@Override
	public void buildValor(double valor) {
		// Como os emprestimos de livro não tem custo, metodo nao e sobrescrito
	}

	@Override
	public ComprovanteDevolucao getComprovante() {
		return new ComprovanteDevolucaoBiblioteca("ZN biblioteca", locador, codigo, dataEmprestimo, dataDevolucao, recursos);
	}
}
