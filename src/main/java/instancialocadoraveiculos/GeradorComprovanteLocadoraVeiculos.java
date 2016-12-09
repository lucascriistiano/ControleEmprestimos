package instancialocadoraveiculos;

import dominio.ComprovanteDevolucao;
import dominio.ComprovanteEmprestimo;
import dominio.Emprestimo;
import dominio.GeradorComprovante;

public class GeradorComprovanteLocadoraVeiculos implements GeradorComprovante {

	/*@ also
	  @ ensures \result != null; 
	  @*/
	@Override
	public /*@ pure @*/ ComprovanteEmprestimo gerarComprovanteEmprestimo(Emprestimo emprestimo) {
		return new ComprovanteEmprestimoLocadoraVeiculos(emprestimo);
	}

	/*@ also
	  @ ensures \result != null; 
	  @*/
	@Override
	public /*@ pure @*/ ComprovanteDevolucao gerarComprovanteDevolucao(Emprestimo emprestimo, double valor) {
		return new ComprovanteDevolucaoLocadoraVeiculos(emprestimo, valor);
	}

}
