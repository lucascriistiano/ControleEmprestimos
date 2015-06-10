package instanciabiblioteca;

import dominio.Recurso;
import excecao.RecursoInvalidoException;

public class Livro extends Recurso{
	
	private String autor;
	private String editora;
	private Integer edicao;
	private Integer quantidade;
	private String titulo;
	
	public Livro(Long codigo, String descricao) {
		super(codigo, descricao);
	}
	
	public Livro(Long codigo, String descricao, 
			String autor, String editora, int edicao, 
			int quantidade, String titulo) {
		super(codigo, descricao);
		this.autor = autor;
		this.editora = editora;
		this.edicao = edicao;
		this.quantidade = quantidade;
		this.titulo = titulo;
	}
	
	public String getAutor() {
		return autor;
	}
	public void setAutor(String autor) {
		this.autor = autor;
	}
	public String getEditora() {
		return editora;
	}
	public void setEditora(String editora) {
		this.editora = editora;
	}
	public int getEdicao() {
		return edicao;
	}
	public void setEdicao(Integer edicao) {
		this.edicao = edicao;
	}
	public Integer getQuantidade() {
		return quantidade;
	}
	public void setQuantidade(int quantidade) {
		this.quantidade = quantidade;
	}
	public String getTitulo() {
		return titulo;
	}
	public void setTitulo(String titulo) {
		this.titulo = titulo;
	}
	@Override
	public void alocar() {
		this.quantidade--;
		
		if(this.quantidade == 0)
			setDisponivel(false);
	}
	
	@Override
	public void desalocar() {
		this.quantidade++;
		
		if(!isDisponivel())
			setDisponivel(true);
	}
	
	@Override
	public boolean validar() throws RecursoInvalidoException {
		if(!this.isDisponivel())
			throw new RecursoInvalidoException("Recurso invalido para emprestimo. O livro de codigo " + getCodigo() + " ja esta alocado.");
			
		return true;
	}
	
}
