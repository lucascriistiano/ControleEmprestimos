package dominio;

import java.util.Calendar;

public class ComprovanteCarro implements Comprovante{

	private String empresa ;
    private String locador ;
    private double valor ;
    private Calendar devolucao ;
    private long numero ;
    
	public ComprovanteCarro(String empresa, String locador, double valor,
    		Calendar devolucao, long numero) {
		this.empresa = empresa;
		this.locador = locador;
		this.valor = valor;
		this.devolucao = devolucao;
		this.numero = numero;
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
	}

}