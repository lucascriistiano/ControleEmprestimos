package dominio;

import java.util.Calendar;
import java.util.Date;
import java.util.GregorianCalendar;

import excecao.ClienteInvalidoException;

public class ClienteLocador extends Cliente{
	
	private static final int IDADE_MINIMA = 21; //Idade mínima de 21 anos para alugar
	
	private String cpf;
	private String rg;
	private String carteiraMotorista;
	private Date dataNascimento;

	public ClienteLocador(Long codigo, String nome) {
		super(codigo, nome);
	}
	
	public ClienteLocador(Long codigo, String nome, String cpf, String rg, String carteiraMotorista, Date dataNascimento) {
		super(codigo, nome);
		
		this.cpf = cpf;
		this.rg = rg;
		this.carteiraMotorista = carteiraMotorista;
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

	public String getCarteiraMotorista() {
		return carteiraMotorista;
	}

	public void setCarteiraMotorista(String carteiraMotorista) {
		this.carteiraMotorista = carteiraMotorista;
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
		if(this.getCarteiraMotorista().trim().isEmpty()) {
			throw new ClienteInvalidoException("Numero de carteira de motorista nao fornecido");
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
