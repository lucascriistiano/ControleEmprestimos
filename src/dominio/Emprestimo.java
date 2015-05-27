package dominio;

import java.util.ArrayList;
import java.util.Date;
import java.util.List;

public class Emprestimo {
	private Long codigo; 			//ID do emprestimo
	private Date data;				//Data de realizacao do emprestimo
	private Usuario usuario;		//Usuario que efetivou o emprestimo 
	private Cliente cliente;		//Cliente que realizou o emprestimo
	private List<Recurso> recursos;//Lista de recursos emprestados
	
	public Emprestimo() {
		this.recursos = new ArrayList<Recurso>();
	}
	
	public Emprestimo(Long codigo, Date data, Usuario usuario, Cliente cliente, List<Recurso> recursos) {
		this.codigo = codigo;
		this.data = data;
		this.usuario = usuario;
		this.cliente = cliente;
		
		this.recursos = new ArrayList<Recurso>(recursos);
	}
	
	public Long getCodigo() {
		return codigo;
	}

	public void setCodigo(Long codigo) {
		this.codigo = codigo;
	}
	
	public Date getData() {
		return data;
	}

	public void setData(Date data) {
		this.data = data;
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
