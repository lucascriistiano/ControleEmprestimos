package instancialocadoraveiculos;

import java.util.Date;
import java.util.List;

import dominio.ComprovanteDevolucao;
import dominio.ComprovanteDevolucaoBuilder;
import dominio.Recurso;

public class ComprovanteDevolucaoBuilderLocadoraVeiculos implements ComprovanteDevolucaoBuilder {

	private /*@ nullable spec_public @*/ String locador;
	private /*@ nullable spec_public @*/ Long codigo;
	private /*@ nullable spec_public @*/ Date dataEmprestimo;
	private /*@ nullable spec_public @*/ Date dataDevolucao;
    private /*@ nullable spec_public @*/ List<Recurso> recursos;
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
		return new ComprovanteDevolucaoLocadoraVeiculos("LoCar Locadora", locador, codigo, dataEmprestimo, dataDevolucao, recursos, valor);
	}
}
