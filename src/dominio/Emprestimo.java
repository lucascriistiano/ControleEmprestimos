package dominio;

import java.util.ArrayList;
import java.util.Date;
import java.util.List;

public class Emprestimo {
	private Long codigo; 			//ID do emprestimo
	private Date dataEmprestimo;	//Data de realizacao do emprestimo
	private Date dataDevolucao;		//Data de realizacao do emprestimo
	private Usuario usuario;		//Usuario que efetivou o emprestimo 
	private Cliente cliente;		//Cliente que realizou o emprestimo
	private List<Recurso> recursos;//Lista de recursos emprestados
	
	private static Long CODIGO_ATUAL = (long) 1;
	
	public Emprestimo() {
		this.codigo = CODIGO_ATUAL;
		CODIGO_ATUAL++;
		
		this.recursos = new ArrayList<Recurso>();
	}
	
	public Emprestimo(Date dataEmprestimo, Usuario usuario, Cliente cliente, List<Recurso> recursos) {
		this.codigo = CODIGO_ATUAL;
		CODIGO_ATUAL++;
		
		this.dataEmprestimo = dataEmprestimo;
		this.usuario = usuario;
		this.cliente = cliente;
		
		this.recursos = new ArrayList<Recurso>(recursos);
	}
	
	public Long getCodigo() {
		return codigo;
	}
	
	public Date getDataEmprestimo() {
		return dataEmprestimo;
	}

	public void setDataEmprestimo(Date dataEmprestimo) {
		this.dataEmprestimo = dataEmprestimo;
	}
	
	public Date getDataDevolucao() {
		return dataDevolucao;
	}

	public void setDataDevolucao(Date dataDevolucao) {
		this.dataDevolucao = dataDevolucao;
	}

	public Usuario getUsuario() {
		return usuario;
	}

	public void setUsuario(Usuario usuario) {
		this.usuario = usuario;
	}

	public Cliente getCliente() {
		return cliente;
	}

	public void setCliente(Cliente cliente) {
		this.cliente = cliente;
	}

	public void adicionarRecurso(Recurso recurso){
		this.recursos.add(recurso);
	}
	
	public void removerRecurso(Recurso recurso) {
		this.recursos.remove(recurso);
	}
	
	public List<Recurso> getRecursos() {
		return recursos;
	}
}
