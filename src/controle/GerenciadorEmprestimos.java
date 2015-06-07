package controle;

import java.util.Calendar;
import java.util.Date;
import java.util.List;

import dao.DaoEmprestimo;
import dao.DaoEmprestimoMemoria;
import dominio.Cliente;
import dominio.ComprovanteBuilder;
import dominio.ComprovanteCarro;
import dominio.ComprovanteCarroBuilder;
import dominio.Emprestimo;
import dominio.GeradorDeComprovante;
import dominio.Recurso;
import dominio.Comprovante;
import dominio.RegraLocadoraCarros;
import dominio.RegraEmprestimo;
import dominio.Usuario;

public class GerenciadorEmprestimos {
	private DaoEmprestimo daoEmprestimo;
	private RegraEmprestimo regraEmprestimo = new RegraLocadoraCarros();
	
	public GerenciadorEmprestimos() {
		this.daoEmprestimo = DaoEmprestimoMemoria.getInstance();
	}
	
	public Comprovante realizarEmprestimo(Usuario usuario, Cliente cliente, List<Recurso> recursos) {
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
		
		//TODO Emitir comprovante
		ComprovanteBuilder comprovantebuilder = new ComprovanteCarroBuilder();
		GeradorDeComprovante geradorDeComprovante = new GeradorDeComprovante(comprovantebuilder);
		
		Comprovante comprovante = geradorDeComprovante.geraComprovante(emprestimo);
		
		return comprovante;
	}
	
	public Comprovante realizarEmprestimo(Usuario usuario, Cliente cliente, List<Recurso> recursos, Date dataDevolucao) {
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
		
			//TODO Emitir comprovante
			return null;
		}
		else {
			//Lancar excessao
			System.out.println("Data de devolucao invalida");
			return null;
		}	
	}
	
	public void realizarDevolucao(Emprestimo emprestimo, double taxaExtra) {
		double valorFinal = regraEmprestimo.calcularValorFinal(emprestimo, taxaExtra);
		
		//TODO Implementar a realizacao do pagamento

		daoEmprestimo.remove(emprestimo);

		//TODO Implementar a emissao do comprovante
		System.out.println(String.format("Valor final: R$ %.2f", valorFinal));
	}
	
	public Emprestimo getEmprestimo(Long codigo) {
		return this.daoEmprestimo.get(codigo);
	}
	
	public List<Emprestimo> listarEmprestimos() {
		return this.daoEmprestimo.list();
	}
	
}
