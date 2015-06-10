package dominio;

public class Aluno extends Cliente{
	private String cpf;
	private String rg;
	private Long matricula;
	private String curso;

	public Aluno(Long codigo, String nome) {
		super(codigo, nome);
	}
	
	public Aluno(Long codigo, String nome, String cpf, String rg, Long matricula, String curso) {
		super(codigo, nome);
		this.cpf = cpf;
		this.rg = rg;
		this.matricula = matricula;
		this.curso = curso;
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

	public Long getMatricula() {
		return matricula;
	}

	public void setMatricula(Long matricula) {
		this.matricula = matricula;
	}

	public String getCurso() {
		return curso;
	}

	public void setCurso(String curso) {
		this.curso = curso;
	}

	@Override
	public boolean validar() {
		// TODO Auto-generated method stub
		return false;
	}

}
