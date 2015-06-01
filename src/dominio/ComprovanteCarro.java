package dominio;

import java.util.Calendar;
import java.util.List;

public class ComprovanteCarro implements Comprovante{

	private String empresa ;
    private String locador ;
    private double valor ;
    private Calendar devolucao ;
    private long numero ;
    private List<Recurso> recursos;
    
	public ComprovanteCarro(String empresa, String locador, double valor,
    		Calendar devolucao, long numero, List<Recurso> recursos) {
		this.empresa = empresa;
		this.locador = locador;
		this.valor = valor;
		this.devolucao = devolucao;
		this.numero = numero;
		this.recursos = recursos;
	}
    
	@Override
	public String getEmpresa() {
		return this.empresa;
	}

	@Override
	public String getLocador() {
		return this.locador;
	}

	@Override
	public double getValor() {
		return this.valor;
	}

	@Override
	public Calendar getDevolucao() {
		return this.devolucao;
	}

	@Override
	public long getNumero() {
		return this.numero;
	}

	@Override
	public void imprimir() {
		System.out.println("Nome da empresa de carro: " + this.empresa);
		System.out.println("Nome da locador: " + this.locador);
		System.out.println("Valor do aluguel: " + this.valor);
		System.out.println("Data da devolução: " + this.devolucao);
		System.out.println("Número: " + this.numero);
		for (Recurso recurso : recursos) {
			System.out.println(recurso.getDescricao());
		}
	}

	@Override
	public List<Recurso> getRecursos() {
		return this.recursos;
	}

}