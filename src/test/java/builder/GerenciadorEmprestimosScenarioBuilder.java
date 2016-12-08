package builder;

import java.util.Date;

import controle.GerenciadorEmprestimos;
import dominio.Emprestimo;
import dominio.Usuario;

public class GerenciadorEmprestimosScenarioBuilder {

	private Emprestimo emprestimo;
	private GerenciadorEmprestimos gerenciador;

	public GerenciadorEmprestimosScenarioBuilder(GerenciadorEmprestimos gerenciadorEmprestimos) {
		super();
		this.gerenciador = gerenciadorEmprestimos;
	}

	public GerenciadorEmprestimosScenarioBuilder comDevolucao(Date date){
		return null;
	}
	
	public GerenciadorEmprestimosScenarioBuilder realizarEmprestimo(){
		/*assertTrue("Id do usuario deve ser maior que 0", usuario.getCodigo() > 0);
		return this;*/
		return this;
	}
		
	
}
