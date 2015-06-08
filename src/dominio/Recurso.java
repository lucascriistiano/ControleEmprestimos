package dominio;

import excecao.RecursoInvalidoException;

public abstract class Recurso {
	
	private Long codigo;
	private String descricao;
	
	protected Recurso(Long codigo, String descricao) {
		this.codigo = codigo;
		this.descricao = descricao;
	}
	
	public Long getCodigo() {
		return codigo;
	}

	public void setCodigo(Long codigo) {
		this.codigo = codigo;
	}

	public String getDescricao() {
		return descricao;
	}

	public void setDescricao(String descricao) {
		this.descricao = descricao;
	}

	public abstract void alocarRecurso(Recurso recurso);
	public abstract boolean validar() throws RecursoInvalidoException;
}
