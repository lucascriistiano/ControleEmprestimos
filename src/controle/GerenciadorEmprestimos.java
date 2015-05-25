package controle;

import java.util.ArrayList;

import dao.DaoEmprestimo;
import dominio.ComprovanteCarro;
import dominio.Emprestimo;
import dominio.Recurso;
import dominio.Comprovante;

public class GerenciadorEmprestimos {
	private DaoEmprestimo daoEmprestimo;
	
	public GerenciadorEmprestimos() {
		this.daoEmprestimo = new DaoEmprestimo();
	}
	
	public Comprovante realizarEmprestimo(ArrayList<Recurso> Recursos) {
		
		return null;
	}
	
}
