package dominio;

import java.util.Date;
import java.util.List;

public class ComprovanteEmprestimoBuilderLivro implements ComprovanteEmprestimoBuilder {

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
	public ComprovanteEmprestimo getComprovante() {
		return new ComprovanteEmprestimoCarro("ZN Biblioteca", locador, codigo, dataEmprestimo, dataDevolucao, recursos);
	}
}
