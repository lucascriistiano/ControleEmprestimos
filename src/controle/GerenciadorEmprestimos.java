package controle;

import java.util.Calendar;
import java.util.Date;
import java.util.List;

import dao.DaoEmprestimo;
import dao.DaoEmprestimoMemoria;
import dominio.Cliente;
import dominio.ComprovanteCarro;
import dominio.Emprestimo;
import dominio.Recurso;
import dominio.Comprovante;
import dominio.RegraCarro;
import dominio.RegraEmprestimo;
import dominio.Usuario;

public class GerenciadorEmprestimos {
	private DaoEmprestimo daoEmprestimo;
	private RegraEmprestimo regraEmprestimo = new RegraCarro();
	
	public GerenciadorEmprestimos() {
		this.daoEmprestimo = DaoEmprestimoMemoria.getInstance();
	}
	
	public Comprovante realizarEmprestimo(Usuario usuario, Cliente cliente, List<Recurso> recursos) {
		//Validacao do status do cliente para emprestimos
		if(!regraEmprestimo.validarCliente(cliente)) {
			//TODO Lancar excessao
			System.out.println("Cliente invalido para emprestimo");
			return null;
		}
		
		//Validacao do recurso para emprestimo
		for(Recurso recurso : recursos) {
			if(!regraEmprestimo.validarRecurso(recurso)) {
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
		emprestimo.setDataDevolucao(regraEmprestimo.calcularDataDeDevolucao(emprestimo));
		
		for(Recurso recurso : recursos) {
			emprestimo.adicionarRecurso(recurso);
			//TODO Alocar recurso
		}
		
		daoEmprestimo.add(emprestimo);
		
		//TODO Emitir comprovante
		
		return null;
	}
	
	public Comprovante realizarEmprestimo(Usuario usuario, Cliente cliente, List<Recurso> recursos, Date dataDevolucao) {
		//Validacao do status do cliente para emprestimos
		if(!regraEmprestimo.validarCliente(cliente)) {
			//TODO Lancar excessao
			System.out.println("Cliente invalido para emprestimo");
			return null;
		}
		
		//Validacao do recurso para emprestimo
		for(Recurso recurso : recursos) {
			if(!regraEmprestimo.validarRecurso(recurso)) {
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
		emprestimo.setDataDevolucao(dataDevolucao);
		
		for(Recurso recurso : recursos) {
			emprestimo.adicionarRecurso(recurso);
			//TODO Alocar recurso
		}
		
		daoEmprestimo.add(emprestimo);
		
		//TODO Emitir comprovante
		
		return null;
	}
	
	public void realizarDevolucao(Emprestimo emprestimo) {
		//TODO Implementar
	}
	
	public Emprestimo getEmprestimo(Long codigo) {
		return this.daoEmprestimo.get(codigo);
	}
	
	public List<Emprestimo> listarEmprestimos() {
		return this.daoEmprestimo.list();
	}
	
}
