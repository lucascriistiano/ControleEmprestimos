package dominio;

import java.util.Date;

public class Professor extends Cliente{

	private String cpf;
	private String rg;
	private String titulacao;
	private Date dataAdmissao;
	
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

	public String getTitulacao() {
		return titulacao;
	}

	public void setTitulacao(String titulacao) {
		this.titulacao = titulacao;
	}

	public Date getDataAdmissao() {
		return dataAdmissao;
	}

	public void setDataAdmissao(Date dataAdmissao) {
		this.dataAdmissao = dataAdmissao;
	}

	public Professor(Long codigo, String nome) {
		super(codigo, nome);
	}

	@Override
	public boolean validar() {
		// TODO Auto-generated method stub
		return false;
	}

}