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
import dominio.GeradorComprovante;
import dominio.Recurso;
import dominio.RegraEmprestimo;
import dominio.Usuario;

public class GerenciadorEmprestimos {
	private DaoEmprestimo daoEmprestimo;
	
	private RegraEmprestimo regraEmprestimo;
	private GeradorComprovante geradorComprovante;
	
	public GerenciadorEmprestimos(RegraEmprestimo regraEmprestimo, ComprovanteEmprestimoBuilder comprovanteEmprestimoBuilder, ComprovanteDevolucaoBuilder comprovanteDevolucaoBuilder) {
		this.daoEmprestimo = DaoEmprestimoMemoria.getInstance();
		this.regraEmprestimo = regraEmprestimo;
		this.geradorComprovante = new GeradorComprovante(comprovanteEmprestimoBuilder, comprovanteDevolucaoBuilder);
	}
	
	public ComprovanteEmprestimo realizarEmprestimo(Usuario usuario, Cliente cliente, List<Recurso> recursos) {
		//Validacao do status do cliente para emprestimos
		if(!cliente.validar()) {
			//TODO Lancar excessao
			System.out.println("Cliente invalido para emprestimo");
			return null;
		}
		
		//Validacao do recurso para emprestimo
		for(Recurso recurso : recursos) {
			if(!recurso.validar()) {
				//TODO Lancar excessao
				System.out.println("Recurso invalido para emprestimo");
				return null;
			}
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
	
	public ComprovanteEmprestimo realizarEmprestimo(Usuario usuario, Cliente cliente, List<Recurso> recursos, Date dataDevolucao) {
		//Validacao do status do cliente para emprestimos
		if(!cliente.validar()) {
			//TODO Lancar excessao
			System.out.println("Cliente invalido para emprestimo");
			return null;
		}
		
		//Validacao do recurso para emprestimo
		for(Recurso recurso : recursos) {
			if(!recurso.validar()) {
				//TODO Lancar excessao
				System.out.println("Recurso invalido para emprestimo");
				return null;
			}
		}
		
		//Realiza o emprestimo
		Emprestimo emprestimo = new Emprestimo();
		emprestimo.setUsuario(usuario);
		emprestimo.setCliente(cliente);
		
		Date dataAtual = Calendar.getInstance().getTime();
		emprestimo.setDataEmprestimo(dataAtual);
		
		if(regraEmprestimo.validarDataDevolucao(dataAtual, dataDevolucao)) {
			emprestimo.setDataDevolucao(dataDevolucao);
			
			for(Recurso recurso : recursos) {
				emprestimo.adicionarRecurso(recurso);
				//TODO Alocar recurso
			}
			
			daoEmprestimo.add(emprestimo);
		
			ComprovanteEmprestimo comprovanteEmprestimo = geradorComprovante.gerarComprovanteEmprestimo(emprestimo);
			return comprovanteEmprestimo;
		}
		else {
			//Lancar excessao
			System.out.println("Data de devolucao invalida");
			return null;
		}	
	}
	
	public ComprovanteDevolucao realizarDevolucao(Emprestimo emprestimo, double taxaExtra) {
		double valorFinal = regraEmprestimo.calcularValorFinal(emprestimo, taxaExtra);
		
		//TODO Implementar a realizacao do pagamento

		daoEmprestimo.remove(emprestimo);

		ComprovanteDevolucao comprovanteDevolucao = geradorComprovante.gerarComprovanteDevolucao(emprestimo, valorFinal);
		return comprovanteDevolucao;
	}
	
	public Emprestimo getEmprestimo(Long codigo) {
		return this.daoEmprestimo.get(codigo);
	}
	
	public List<Emprestimo> listarEmprestimos() {
		return this.daoEmprestimo.list();
	}
	
}
