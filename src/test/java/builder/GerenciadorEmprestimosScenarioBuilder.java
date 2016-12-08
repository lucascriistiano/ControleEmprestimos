package builder;

import static org.junit.Assert.assertTrue;

import java.util.Date;
import java.util.List;
import java.util.Random;

import controle.GerenciadorEmprestimos;
import controle.GerenciadorUsuarios;
import dominio.Emprestimo;
import dominio.Usuario;
import excecao.DataException;
import excecao.UsuarioInvalidoException;

public class GerenciadorEmprestimosScenarioBuilder {

	private Emprestimo emprestimo;
	private GerenciadorEmprestimos gerenciador;

	public GerenciadorEmprestimosScenarioBuilder(GerenciadorEmprestimos gerenciadorEmprestimos) {
		super();
		this.gerenciador = gerenciador;
	}

	public GerenciadorEmprestimosScenarioBuilder comDevolucao(Date date){
		//
	}
	
	public GerenciadorUsuariosScenarioBuilder realizarEmprestimo(){
		assertTrue("Id do usuario deve ser maior que 0", usuario.getCodigo() > 0);
		return this;
	}
	
	public Usuario getUsuarioInstance(){
		return usuario;
	}
	
	
}
