package builder;

import static org.junit.Assert.assertTrue;

import java.util.Random;

import controle.GerenciadorRecursos;
import dominio.Recurso;
import excecao.DataException;
import excecao.RecursoInvalidoException;
import instanciahotel.Quarto;
import instancialocadoraveiculos.Carro;

public class GerenciadorRecursosScenarioBuilder {
	
	private Recurso recurso;
	private GerenciadorRecursos gerenciador;
	private Class<Recurso> classeRecurso;

	public GerenciadorRecursosScenarioBuilder(GerenciadorRecursos gerenciador, Class<Recurso> classeRecurso) {
		this.gerenciador = gerenciador;
		this.classeRecurso = classeRecurso;
	}
	
	public GerenciadorRecursosScenarioBuilder criarRecursoValido() {		
		Random rand = new Random();
		
		if(classeRecurso.equals(Quarto.class)) {
			recurso = new Quarto(classeRecurso.getSimpleName() + rand.nextInt(), rand.nextInt());
		} else {
			recurso =  new Carro(classeRecurso.getSimpleName() + rand.nextInt(), rand.nextInt());
		}
	
		assertTrue("Recurso não deve ser nulo", recurso != null);
		assertTrue("Recurso deve ser válido", recurso.valido());	
		return this;
	}
	
	public GerenciadorRecursosScenarioBuilder criarRecursoInvalido(){
		if(classeRecurso.equals(Quarto.class)) {
			recurso = new Quarto("", 1);
		} else {
			recurso =  new Carro("", 1);
		}
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
	
	public GerenciadorRecursosScenarioBuilder tornarRecursoIndisponivel(){
		if(recurso != null){
			recurso.setDisponivel(false);
		}
		return this;
	}
	
	public GerenciadorRecursosScenarioBuilder tornarRecursoDisponivel(){
		if(recurso != null){
			recurso.setDisponivel(true);
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
			recurso.setCodigo(-1L);
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
		assertTrue("Id do cliente não deve ser menor que 0", !(recurso.getCodigo() < 0));
		return this;
	}
	
	public Recurso getRecursoInstance(){
		return recurso;
	}

}
