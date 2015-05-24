package controle;

import java.util.List;

import dominio.ComprovanteCarro;
import dominio.Recurso;
import dominio.Comprovante;

public class GerenciadorEmprestimos {
	public Comprovante realizarEmprestimo(List Recursos) {
		return new ComprovanteCarro();
	}
}
