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
import dominio.HistoricoEmprestimo;
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
		
	//@ public initially daoEmprestimo != null;
	//@ public initially daoHistorico != null;
	//@ public initially daoRecurso != null;
	//@ public initially regraEmprestimo != null;
	//@ public initially geradorComprovante != null;
	//@ public initially verificadorPrazos != null;
	//@ public initially gerenciadorDatas != null;
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
	@				 recursos.get(i) != null && ((Recurso) recursos.get(i)).valido() && ((Recurso) recursos.get(i)).isDisponivel() );	
	@	ensures \result != null;
	@	ensures (\forall int i; 
	@				0 <= i && i < recursos.size();
	@				((List<Recursos>) \result.getEmprestimo().getRecursos()) .contains( ((Recurso) recursos.get(i)) )  
	@								&&	!( (Recurso) \result.getEmprestimo().getRecursos().get(i)).isDisponivel()	 );	
	@	ensures daoEmprestimo.exists((long) \result.getEmprestimo().getCodigo());
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
			if(!recurso.valido()){
				throw recurso.toRecursoInvalidoException();
			}
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
			recurso.setDisponivel(false);
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
	 @ ensures emprestimo.isQuitado();
	 @ ensures this.daoHistorico.existsEmprestimo((long) \result.getEmprestimo().getCodigo());
 	 @ ensures !this.daoEmprestimo.exists((long) \result.getEmprestimo().getCodigo());
 	 @ ensures \result.getValor() == regraEmprestimo.calcularValorFinal(emprestimo, taxaExtra);
	 @*/
	public /*@ pure @*/ ComprovanteDevolucao realizarDevolucao(Emprestimo emprestimo, double taxaExtra) throws DataException {
		double valorFinal = regraEmprestimo.calcularValorFinal(emprestimo, taxaExtra);
		
		for(Recurso recurso : emprestimo.getRecursos()) {
			recurso.setDisponivel(true);
		}
		
		emprestimo.setQuitado(true);
		daoHistorico.add(new HistoricoEmprestimo(emprestimo)); // Antes de remover da memoria adiciona no historico
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
		
	public /*@ pure @*/ List<Emprestimo> listarEmprestimos() throws DataException {
		return this.daoEmprestimo.list();
	}
	
}
