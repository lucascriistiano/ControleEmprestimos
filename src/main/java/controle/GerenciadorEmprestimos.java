package controle;

import java.util.ArrayList;
import java.util.Date;
import java.util.List;

import dao.DaoEmprestimo;
import dao.DaoHistorico;
import dao.DaoRecurso;
import dominio.Cliente;
import dominio.ComprovanteDevolucao;
import dominio.ComprovanteEmprestimo;
import dominio.Emprestimo;
import dominio.FabricaNotificacao;
import dominio.GeradorComprovante;
import dominio.Recurso;
import dominio.RegraEmprestimo;
import dominio.Usuario;
import excecao.ClienteInvalidoException;
import excecao.DataException;
import excecao.EmprestimoInvalidoException;
import excecao.RecursoInvalidoException;
import excecao.UsuarioInvalidoException;
import util.GerenciadorDatas;

public class GerenciadorEmprestimos {
	
	//@ public invariant daoEmprestimo != null;
	private final /*@ spec_public @*/ DaoEmprestimo daoEmprestimo;
	
	//@ public invariant daoHistorico != null;
	private final /*@ spec_public @*/ DaoHistorico daoHistorico;
	
	//@ public invariant daoRecurso != null;
	private final /*@ spec_public @*/ DaoRecurso daoRecurso;
	
	private final /*@ spec_public @*/ RegraEmprestimo regraEmprestimo;
	
	private final /*@ spec_public @*/ GeradorComprovante geradorComprovante;
	
	private final /*@ spec_public @*/ VerificadorPrazos verificadorPrazos;
	
	private final /*@ spec_public @*/ GerenciadorDatas gerenciadorDatas;
		
	public GerenciadorEmprestimos(RegraEmprestimo regraEmprestimo, GeradorComprovante geradorComprovante, 
			 FabricaNotificacao fabricaNotificacao, GerenciadorDatas gerenciadorDatas) {
		this.daoEmprestimo = DaoEmprestimo.getInstance();
		this.daoHistorico = DaoHistorico.getInstance(); 
		this.daoRecurso = DaoRecurso.getInstance();
		this.regraEmprestimo = regraEmprestimo;
		this.geradorComprovante = geradorComprovante;
		this.verificadorPrazos = new VerificadorPrazos(regraEmprestimo, fabricaNotificacao, gerenciadorDatas);
		this.gerenciadorDatas = gerenciadorDatas;
	}
		
	/*@
	@ public normal_behavior
	@	requires usuario != null;
	@ 	requires cliente != null;
	@	requires usuario.valido();
	@	requires cliente.valido();
	@	requires (\forall int i; 
	@				0 <= i && i < recursos.size();
	@				 recursos.get(i) != null);	
	@	ensures \result != null;
	@	ensures (\forall int i; 
	@				0 <= i && i < recursos.size();
	@				((List<Recursos>) \result.getEmprestimo().getRecursos()) .contains( ((Recurso) recursos.get(i)) )   );	
	@	also
	@	public exceptional_behavior
	@		requires !usuario.valido();
	@		signals_only UsuarioInvalidoException;	
	@	also
	@	public exceptional_behavior
	@		requires !cliente.valido();
	@		signals_only ClienteInvalidoException;
	@*/
	public /*@ pure @*/ ComprovanteEmprestimo realizarEmprestimo(Usuario usuario, Cliente cliente, List<Recurso> recursos, /*@ nullable @*/ Date dataDevolucao) throws ClienteInvalidoException, EmprestimoInvalidoException, DataException, RecursoInvalidoException, UsuarioInvalidoException {
		//Validacao do status do cliente para emprestimos
		
		if(!usuario.valido()){
			throw new UsuarioInvalidoException(usuario.toUsuarioInvalidoException());
		}
		
		if(!cliente.valido()){
			throw new ClienteInvalidoException(cliente.toClienteInvalidoException());
		}
		
		//Validacao do recurso para emprestimo
		for(Recurso recurso : recursos) {
			recurso.validar();
		}
		
		//Realiza o emprestimo
		Emprestimo emprestimo = new Emprestimo();
		emprestimo.setUsuario(usuario);
		emprestimo.setCliente(cliente);
		
		Date dataAtual = gerenciadorDatas.getDataAtual();
		emprestimo.setDataEmprestimo(dataAtual);
		
		if(dataDevolucao != null){
			regraEmprestimo.validarDataDevolucao(dataAtual, dataDevolucao);
			emprestimo.setDataDevolucao(dataDevolucao);
		} else {
			emprestimo.setDataDevolucao(regraEmprestimo.calcularDataDevolucao(emprestimo));
		}
		
		for(Recurso recurso : recursos) {
			emprestimo.adicionarRecurso(recurso);
			recurso.alocar();
		}
		
		daoEmprestimo.add(emprestimo);
	
		ComprovanteEmprestimo comprovanteEmprestimo = geradorComprovante.gerarComprovanteEmprestimo(emprestimo);
		return comprovanteEmprestimo;
	}
	
	public ComprovanteEmprestimo realizarEmprestimo(Usuario usuario, Cliente cliente, List<Recurso> recursos) throws DataException, EmprestimoInvalidoException, ClienteInvalidoException, RecursoInvalidoException, UsuarioInvalidoException {
		return realizarEmprestimo(usuario, cliente, recursos, null);
	}
	
	/*@
	 @ requires emprestimo != null;
	 @ assignable \nothing;
	 @ ensures this.daoHistorico.exists((long) \result.getEmprestimo().getCodigo());
 	 @ ensures !this.daoEmprestimo.exists((long) \result.getEmprestimo().getCodigo());
 	 @ ensures \result.getValor() == regraEmprestimo.calcularValorFinal(emprestimo, taxaExtra);
	 @*/
	public /*@ pure @*/ ComprovanteDevolucao realizarDevolucao(Emprestimo emprestimo, double taxaExtra) throws DataException {
		double valorFinal = regraEmprestimo.calcularValorFinal(emprestimo, taxaExtra);
		
		//TODO Implementar a realizacao do pagamento

		for(Recurso recurso : emprestimo.getRecursos()) {
			recurso.desalocar();
		}
		
		daoHistorico.add(emprestimo); // Antes de remover da memoria adiciona no historico
		daoEmprestimo.remove(emprestimo);

		ComprovanteDevolucao comprovanteDevolucao = geradorComprovante.gerarComprovanteDevolucao(emprestimo, valorFinal);
		return comprovanteDevolucao;
	}
			
	/*@
	@ requires codigoCliente > 0L;
	@ assignable \nothing;
	@ ensures \result != null;
	@*/
	public List<Recurso> buscarSugestoes(long codigoCliente) throws DataException {				
		List<Recurso> recursosSugeridos;
		
		Integer idCategoria = daoHistorico.findCategoriaAltaByCliente(codigoCliente);
		
		if(idCategoria != null){
			recursosSugeridos = daoRecurso.getPorCategoria(idCategoria);
		} else {
			recursosSugeridos = new ArrayList<>();
		}
		
		return recursosSugeridos;
	}
	
	/*@
	 @ requires codigo > 0L;
	 @ assignable \nothing;
	 @ ensures daoEmprestimo.exists(codigo) ==> \result != null;
	 @*/
	public /*@ pure @*/ Emprestimo getEmprestimo(long codigo) throws DataException {
		return (Emprestimo) this.daoEmprestimo.get(codigo);
	}
	
	public /*@ pure @*/ boolean verificarPrazos() throws DataException {
		List<Emprestimo> emprestimos = daoEmprestimo.list();
		return this.verificadorPrazos.verificarEmprestimos(emprestimos);
	}
	
	public boolean verificarStatusCliente(Cliente cliente) {
		//TODO Implementar verificacao de status do cliente
		return false;
	}
	
	public /*@ pure @*/ List<Emprestimo> listarEmprestimos() throws DataException {
		return this.daoEmprestimo.list();
	}
	
}
