package controle;

import java.util.Calendar;
import java.util.Date;
import java.util.List;

import dao.DaoEmprestimo;
import dao.DaoEmprestimoMemoria;
import dominio.Cliente;
import dominio.ComprovanteDevolucao;
import dominio.ComprovanteDevolucaoBuilder;
import dominio.ComprovanteEmprestimo;
import dominio.ComprovanteEmprestimoBuilder;
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

public class GerenciadorEmprestimos {
	private DaoEmprestimo daoEmprestimo;
	
	private RegraEmprestimo regraEmprestimo;
	private GeradorComprovante geradorComprovante;
	private VerificadorPrazos verificadorPrazos;
	
	public GerenciadorEmprestimos(RegraEmprestimo regraEmprestimo, ComprovanteEmprestimoBuilder comprovanteEmprestimoBuilder, ComprovanteDevolucaoBuilder comprovanteDevolucaoBuilder, FabricaNotificacao fabricaNotificacao) {
		this.daoEmprestimo = DaoEmprestimoMemoria.getInstance();
		this.regraEmprestimo = regraEmprestimo;
		this.geradorComprovante = new GeradorComprovante(comprovanteEmprestimoBuilder, comprovanteDevolucaoBuilder);
		this.verificadorPrazos = new VerificadorPrazos(regraEmprestimo, fabricaNotificacao);
	}
	
	public ComprovanteEmprestimo realizarEmprestimo(Usuario usuario, Cliente cliente, List<Recurso> recursos) throws DataException, ClienteInvalidoException, RecursoInvalidoException {
		//Validacao do status do cliente para emprestimos
		cliente.validar();
		
		//Validacao do recurso para emprestimo
		for(Recurso recurso : recursos) {
			recurso.validar();
		}
		
		//Realiza o emprestimo
		Emprestimo emprestimo = new Emprestimo();
		emprestimo.setUsuario(usuario);
		emprestimo.setCliente(cliente);
		emprestimo.setDataEmprestimo(Calendar.getInstance().getTime());
		emprestimo.setDataDevolucao(regraEmprestimo.calcularDataDevolucao(emprestimo));
		
		for(Recurso recurso : recursos) {
			emprestimo.adicionarRecurso(recurso);
			//TODO Alocar recurso
		}
		
		daoEmprestimo.add(emprestimo);
		
		ComprovanteEmprestimo comprovanteEmprestimo = geradorComprovante.gerarComprovanteEmprestimo(emprestimo);
		return comprovanteEmprestimo;
	}
	
	public ComprovanteEmprestimo realizarEmprestimo(Usuario usuario, Cliente cliente, List<Recurso> recursos, Date dataDevolucao) throws ClienteInvalidoException, EmprestimoInvalidoException, DataException, RecursoInvalidoException {
		//Validacao do status do cliente para emprestimos
		cliente.validar();
		
		//Validacao do recurso para emprestimo
		for(Recurso recurso : recursos) {
			recurso.validar();
		}
		
		//Realiza o emprestimo
		Emprestimo emprestimo = new Emprestimo();
		emprestimo.setUsuario(usuario);
		emprestimo.setCliente(cliente);
		
		Date dataAtual = Calendar.getInstance().getTime();
		emprestimo.setDataEmprestimo(dataAtual);
		
		regraEmprestimo.validarDataDevolucao(dataAtual, dataDevolucao);
		
		emprestimo.setDataDevolucao(dataDevolucao);
		
		for(Recurso recurso : recursos) {
			emprestimo.adicionarRecurso(recurso);
			//TODO Alocar recurso
		}
		
		daoEmprestimo.add(emprestimo);
	
		ComprovanteEmprestimo comprovanteEmprestimo = geradorComprovante.gerarComprovanteEmprestimo(emprestimo);
		return comprovanteEmprestimo;
	}
	
	public ComprovanteDevolucao realizarDevolucao(Emprestimo emprestimo, double taxaExtra) throws DataException {
		double valorFinal = regraEmprestimo.calcularValorFinal(emprestimo, taxaExtra);
		
		//TODO Implementar a realizacao do pagamento

		daoEmprestimo.remove(emprestimo);

		ComprovanteDevolucao comprovanteDevolucao = geradorComprovante.gerarComprovanteDevolucao(emprestimo, valorFinal);
		return comprovanteDevolucao;
	}
	
	public Emprestimo getEmprestimo(Long codigo) throws DataException {
		return this.daoEmprestimo.get(codigo);
	}
	
	public List<Emprestimo> listarEmprestimos() throws DataException {
		return this.daoEmprestimo.list();
	}
	
	public boolean verificarPrazos() throws DataException {
		List<Emprestimo> emprestimos = daoEmprestimo.list();
		return this.verificadorPrazos.verificarEmprestimos(emprestimos);
	}
	
	public boolean verificarStatusCliente(Cliente cliente) {
		//TODO implementar verificação
		return false;
	}
	
}
