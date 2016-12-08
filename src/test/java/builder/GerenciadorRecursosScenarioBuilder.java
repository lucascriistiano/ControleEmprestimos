package builder;

import static org.junit.Assert.assertTrue;

import java.util.List;
import java.util.Random;

import controle.GerenciadorRecursos;
import dominio.Recurso;
import excecao.DataException;
import excecao.RecursoInvalidoException;
import instanciahotel.Quarto;

public class GerenciadorRecursosScenarioBuilder {
	
	private Recurso recurso;
	private GerenciadorRecursos gerenciador;

	public GerenciadorRecursosScenarioBuilder(GerenciadorRecursos gerenciador) {
		this.gerenciador = gerenciador;
	}
	
	public GerenciadorRecursosScenarioBuilder criarRecursoValido() {
		long codigo;
		try{
			List<Recurso> lista = gerenciador.listarRecursos();
			if(lista == null || lista.isEmpty()){
				codigo = 1L;
			} else {
				codigo = lista.get(lista.size() -1).getCodigo() + 1L;
			}
		} catch (DataException e){
			codigo = 1L;
		}
		
		Random rand = new Random();
		recurso = new Quarto(codigo, "descricao" + rand.nextInt(), rand.nextInt());
		assertTrue("Recurso não deve ser nulo", recurso != null);
		assertTrue("Recurso deve ser válido", recurso.valido());	
		return this;
	}
	
	public GerenciadorRecursosScenarioBuilder criarRecursoInvalido(){
		recurso = new Quarto(1L, "", 0);
		assertTrue("Recurso não deve ser nulo", recurso != null);
		assertTrue("Recurso deve ser inválido", !recurso.valido());	
		return this;
	}
	
	public GerenciadorRecursosScenarioBuilder cadastrarRecurso() throws DataException, RecursoInvalidoException{
		gerenciador.cadastrarRecurso(recurso);
		return this;
	}
	
	public GerenciadorRecursosScenarioBuilder atualizarRecurso() throws DataException, RecursoInvalidoException{
		gerenciador.updateRecurso(recurso);
		return this;
	}	
	
	public GerenciadorRecursosScenarioBuilder removerRecurso() throws DataException{
		gerenciador.removerRecurso(recurso);
		return this;
	}
	
	public GerenciadorRecursosScenarioBuilder setCodigoInvalido(){
		if(recurso != null){
			recurso.setCodigo(0L);
		}
		return this;
	}
	
	public GerenciadorRecursosScenarioBuilder setDescricaoRecurso(String nome){
		if(recurso != null){
			recurso.setDescricao(nome);
		}
		return this;
	}
	
	public GerenciadorRecursosScenarioBuilder setCodigo(Long codigo){
		if(recurso != null){
			recurso.setCodigo(codigo);
		}
		return this;
	}
	
	public GerenciadorRecursosScenarioBuilder tornarRecursoInvalido(){
		if(recurso != null){
			recurso.setDescricao("");
		}
		return this;
	}
	
	public GerenciadorRecursosScenarioBuilder tornarCodigoInvalido(){
		if(recurso != null){
			recurso.setCodigo(0L);
		}
		return this;
	}	
	
	public GerenciadorRecursosScenarioBuilder getRecurso() throws DataException{
		recurso = gerenciador.getRecurso(recurso.getCodigo());
		return this;
	}
	
	public GerenciadorRecursosScenarioBuilder getRecurso(Long codigo) throws DataException{
		recurso = gerenciador.getRecurso(codigo);
		return this;
	}
	
	public GerenciadorRecursosScenarioBuilder assertExists(){
		assertTrue("Recurso deve estar cadastrado", gerenciador.exists(recurso.getCodigo()));
		return this;
	}
	
	public GerenciadorRecursosScenarioBuilder assertNotExists(){
		assertTrue("Recurso não deve estar cadastrado", !gerenciador.exists(recurso.getCodigo()));
		return this;
	}
	
	public GerenciadorRecursosScenarioBuilder assertCodigoValido(){
		assertTrue("Id do recurso deve ser maior que 0", recurso.getCodigo() > 0);
		return this;
	}
	
	public Recurso getRecursoInstance(){
		return recurso;
	}

}
