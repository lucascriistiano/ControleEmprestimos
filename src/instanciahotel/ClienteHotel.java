package instanciahotel;

import java.util.Calendar;
import java.util.Date;
import java.util.GregorianCalendar;

import dominio.Cliente;
import excecao.ClienteInvalidoException;

public class ClienteHotel extends Cliente{
	
	private static final int IDADE_MINIMA = 18; //Idade mínima de 21 anos para alugar
	
	private String cpf;
	private String rg;
	private String endereco;
	private Date dataNascimento;

	public ClienteHotel(Long codigo, String nome) {
		super(codigo, nome);
	}
	
	public ClienteHotel(Long codigo, String nome, String cpf, String rg, String endereco, Date dataNascimento) {
		super(codigo, nome);
		
		this.cpf = cpf;
		this.rg = rg;
		this.endereco = endereco;
		this.dataNascimento = dataNascimento;
	}
	
	public String getCpf() {
		return cpf;
	}

	public void setCpf(String cpf) {
		this.cpf = cpf;
	}

	public String getRg() {
		return rg;
	}

	public void setRg(String rg) {
		this.rg = rg;
	}

	public String getEndereco() {
		return endereco;
	}

	public void setEndereco(String endereco) {
		this.endereco = endereco;
	}
	
	public Date getDataNascimento() {
		return dataNascimento;
	}
	
	public void setDataNascimento(Date dataNascimento) {
		this.dataNascimento = dataNascimento;
	}
	
	public int getIdade() {
		Calendar dataNascimento = new GregorianCalendar();
		dataNascimento.setTime(this.dataNascimento);

		// Cria um objeto calendar com a data atual
		Calendar dataAtual = Calendar.getInstance();

		// Obtém a idade baseado no ano
		int idade = dataAtual.get(Calendar.YEAR) - dataNascimento.get(Calendar.YEAR);

		dataNascimento.add(Calendar.YEAR, idade);

		if (dataAtual.before(dataNascimento)) {
			idade--;
		}
		
		return idade;
	}

	public boolean validar() throws ClienteInvalidoException {
		if(this.getNome().trim().isEmpty()) {
			throw new ClienteInvalidoException("Nome do cliente vazio");
		}
		if(this.getCpf().trim().isEmpty()) {
			throw new ClienteInvalidoException("CPF vazio");
		}
		if(this.getEndereco().trim().isEmpty()) {
			throw new ClienteInvalidoException("Endere�o vazio");
		}
		if(this.getDataNascimento() == null) {
			throw new ClienteInvalidoException("Data de nascimento vazia");
		}
		if(this.getIdade() < IDADE_MINIMA) {
			throw new ClienteInvalidoException("Cliente não tem a idade minima necessaria (" + IDADE_MINIMA + " anos)");
		}
		
		return true;
	}
	
}
