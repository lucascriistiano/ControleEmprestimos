package dominio;

import java.util.Date;
import java.util.List;

public abstract class ComprovanteDevolucao extends Comprovante {
    
	private double valor;
	
	public ComprovanteDevolucao(String empresa, String locador, Long codigo, Date dataEmprestimo, Date dataDevolucao, List<Recurso> recursos, double valor) {
		super(empresa, locador, codigo, dataEmprestimo, dataDevolucao,recursos);
		this.valor = valor;
	}
	
	public double getValor() {
		return valor;
	}
}