package dominio;

public class Carro extends Recurso {
	
	private String placa;
	private String modelo;
	private String fabricante;
	private String cor;
	private double preco; 		// Referente ao valor do aluguel
	
	public Carro(Long codigo, String descricao, String placa, String modelo, String fabricante, String cor, double preco) {
		super(codigo, descricao);
		
		this.placa = placa;
		this.modelo = modelo;
		this.fabricante = fabricante;
		this.cor = cor;
		this.preco = preco;
	}
	
	public String getPlaca() {
		return placa;
	}

	public void setPlaca(String placa) {
		this.placa = placa;
	}

	public String getModelo() {
		return modelo;
	}

	public void setModelo(String modelo) {
		this.modelo = modelo;
	}

	public String getFabricante() {
		return fabricante;
	}

	public void setFabricante(String fabricante) {
		this.fabricante = fabricante;
	}

	public String getCor() {
		return cor;
	}

	public void setCor(String cor) {
		this.cor = cor;
	}

	public double getPreco() {
		return preco;
	}

	public void setPreco(double preco) {
		this.preco = preco;
	}
	
	public void alocarRecurso(Recurso recurso) {
		// TODO Auto-generated method stub
		
	}
	
}
