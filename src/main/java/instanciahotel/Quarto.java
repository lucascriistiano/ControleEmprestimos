package instanciahotel;

import dominio.Recurso;
import excecao.RecursoInvalidoException;

public class Quarto extends Recurso {
	
	private double area;
	private int numero;
	private int quantidadePessoas;
	private double preco; 				// Referente ao valor do aluguel
	
	public Quarto(String descricao, int categoria) {
		super(descricao, categoria);
	}
	
	public Quarto(String descricao, int categoria, double area, int numero, int quantidadePessoas, double preco) {
		super(descricao, categoria);
		this.area = area;
		this.numero = numero;
		this.quantidadePessoas = quantidadePessoas;
		this.preco = preco;
	}

	public double getArea() {
		return area;
	}

	public void setArea(double area) {
		this.area = area;
	}

	public int getNumero() {
		return numero;
	}

	public void setNumero(int numero) {
		this.numero = numero;
	}

	public int getQuantidadePessoas() {
		return quantidadePessoas;
	}

	public void setQuantidadePessoas(int quantidadePessoas) {
		this.quantidadePessoas = quantidadePessoas;
	}

	public double getPreco() {
		return preco;
	}

	public void setPreco(double preco) {
		this.preco = preco;
	}
	
	@Override
	public boolean valido() {
		boolean isValido = super.valido();
		if(area < 0){
			isValido = false;
		} else if (quantidadePessoas < 0){
			isValido = false;
		}
		return isValido;
	}

	@Override
	public RecursoInvalidoException toRecursoInvalidoException() {
		RecursoInvalidoException exception = super.toRecursoInvalidoException();
		if(!this.isDisponivel())
			exception = new RecursoInvalidoException("Recurso invalido para emprestimo. O quarto de codigo " + getCodigo() + " ja esta alocado.", (Throwable) exception);
		return exception;
	}

	
}
