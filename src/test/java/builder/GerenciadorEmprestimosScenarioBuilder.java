package builder;

import java.util.Date;
import java.util.List;

import controle.GerenciadorEmprestimos;
import dominio.Cliente;
import dominio.ComprovanteEmprestimo;
import dominio.Emprestimo;
import dominio.Recurso;
import dominio.Usuario;
import excecao.ClienteInvalidoException;
import excecao.DataException;
import excecao.EmprestimoInvalidoException;
import excecao.RecursoInvalidoException;
import excecao.UsuarioInvalidoException;

public class GerenciadorEmprestimosScenarioBuilder {

	private GerenciadorEmprestimos gerenciador;
	
	private Cliente cliente;
	private Usuario usuario;
	private List<Recurso> recursos;
	private Date dataDevolucao;

	private ComprovanteEmprestimo comprovanteEmprestimo;
	private Emprestimo emprestimo;

	public GerenciadorEmprestimosScenarioBuilder(GerenciadorEmprestimos gerenciadorEmprestimos) {
		super();
		this.gerenciador = gerenciadorEmprestimos;
	}
		
	public GerenciadorEmprestimosScenarioBuilder comCliente(Cliente cliente){
		this.cliente = cliente;
		return this;
	}
	
	public GerenciadorEmprestimosScenarioBuilder comUsuario(Usuario usuario){
		this.usuario = usuario;
		return this;
	}
	
	public GerenciadorEmprestimosScenarioBuilder comRecursos(List<Recurso> recursos){
		this.recursos = recursos;
		return this;
	}
	
	public GerenciadorEmprestimosScenarioBuilder comDevolucao(Date dataDevolucao){
		this.dataDevolucao = dataDevolucao;
		return this;
	}

	public GerenciadorEmprestimosScenarioBuilder realizarEmprestimo() throws DataException, EmprestimoInvalidoException, ClienteInvalidoException, RecursoInvalidoException, UsuarioInvalidoException{
		comprovanteEmprestimo = gerenciador.realizarEmprestimo(usuario, cliente, recursos, dataDevolucao);
		return this;
	}

	public ComprovanteEmprestimo getComprovanteEmprestimoInstance(){
		return comprovanteEmprestimo;
	}
	
	public Emprestimo getEmprestimoInstance(){
		return emprestimo;
	}
	
}
