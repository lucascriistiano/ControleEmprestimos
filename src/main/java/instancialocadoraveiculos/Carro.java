package instancialocadoraveiculos;

import dominio.Recurso;
import excecao.RecursoInvalidoException;

public class Carro extends Recurso {
	
	private /*@ nullable @*/ String placa;
	private /*@ nullable @*/ String modelo;
	private /*@ nullable @*/ String fabricante;
	private /*@ nullable @*/ String cor;
	private int quilometragemInicial; 	// Quilometragem rodada pelo veiculo antes do momento do emprestimo
	private int quilometragemFinal; 	// Quilometragem rodada pelo veiculo antes do momento do emprestimo
	private double preco; 				// Referente ao valor do aluguel
	
	public Carro(String descricao, int categoria) {
		super(descricao, categoria);
		this.placa = "PlacaPadrao";
		this.modelo = "ModeloPadrao";
		this.fabricante = "FabricantePadrao";
		this.cor = "CorPadrao";
		this.quilometragemInicial = 0;
		this.preco = 0;
	}
	
	public Carro(String descricao, int categoria, String placa, String modelo, String fabricante, String cor, int quilometragemInicial, double preco) {
		super(descricao, categoria);	
		this.placa = placa;
		this.modelo = modelo;
		this.fabricante = fabricante;
		this.cor = cor;
		this.quilometragemInicial = quilometragemInicial;
		this.preco = preco;
	}
	
	public /*@ pure @*/ String getPlaca() {
		return placa;
	}

	public void setPlaca(String placa) {
		this.placa = placa;
	}

	public /*@ pure @*/ String getModelo() {
		return modelo;
	}

	public void setModelo(String modelo) {
		this.modelo = modelo;
	}

	public /*@ pure @*/ String getFabricante() {
		return fabricante;
	}

	public void setFabricante(String fabricante) {
		this.fabricante = fabricante;
	}

	public /*@ pure @*/ String getCor() {
		return cor;
	}

	public void setCor(String cor) {
		this.cor = cor;
	}

	public /*@ pure @*/ int getQuilometragemInicial() {
		return quilometragemInicial;
	}

	public void setQuilometragemInicial(int quilometragemInicial) {
		this.quilometragemInicial = quilometragemInicial;
	}

	public /*@ pure @*/ int getQuilometragemFinal() {
		return quilometragemFinal;
	}

	public void setQuilometragemFinal(int quilometragemFinal) {
		this.quilometragemFinal = quilometragemFinal;
	}

	public /*@ pure @*/ double getPreco() {
		return preco;
	}

	public void setPreco(double preco) {
		this.preco = preco;
	}
		
	@Override
	public boolean valido() {
		boolean isValido = super.valido();
		if("".equals(placa)){
			isValido = false;
		} else if ("".equals(modelo)){
			isValido = false;
		} else if ("".equals(fabricante)){
			isValido = false;
		} else if ("".equals(cor)){
			isValido = false;
		}
		return isValido;
	}

	@Override
	public RecursoInvalidoException toRecursoInvalidoException() {
		RecursoInvalidoException exception = super.toRecursoInvalidoException();
		if(!this.isDisponivel())
			exception = new RecursoInvalidoException("Recurso invalido para emprestimo. O carro de codigo " + getCodigo() + " ja esta alocado.", exception);
		return exception;
	}
	
}