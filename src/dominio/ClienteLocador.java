package dominio;

public class ClienteLocador extends Cliente{
	
	private String cpf;
	private String rg;
	private String carteiraMotorista;

	public ClienteLocador(Long codigo, String nome, String cpf, String rg, String carteiraMotorista) {
		super(codigo, nome);
		
		this.cpf = cpf;
		this.rg = rg;
		this.carteiraMotorista = carteiraMotorista;
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
	
	public boolean validar() {
		if((this.getNome().trim().isEmpty()) 
				|| (this.getCpf().trim().isEmpty())
				|| (this.getCarteiraMotorista().trim().isEmpty()))
			return false;
		else
			return true;
	}
	
}
