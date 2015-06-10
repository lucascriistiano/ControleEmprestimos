package dominio;

import java.util.Date;
import java.util.List;

public class ComprovanteDevolucaoBuilderLivro implements ComprovanteDevolucaoBuilder {

	private String locador;
	private Long codigo;
	private Date dataEmprestimo;
	private Date dataDevolucao;
    private List<Recurso> recursos;
    private double valor;

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
		this.valor = valor;
	}

	@Override
	public ComprovanteDevolucao getComprovante() {
		return new ComprovanteDevolucaoCarro("ZN biblioteca", locador, codigo, dataEmprestimo, dataDevolucao, recursos, valor);
	}
}
