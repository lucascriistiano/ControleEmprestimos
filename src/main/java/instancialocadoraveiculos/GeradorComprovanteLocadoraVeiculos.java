package instancialocadoraveiculos;

import dominio.ComprovanteDevolucao;
import dominio.ComprovanteEmprestimo;
import dominio.Emprestimo;
import dominio.GeradorComprovante;

public class GeradorComprovanteLocadoraVeiculos implements GeradorComprovante {

	@Override
	public ComprovanteEmprestimo gerarComprovanteEmprestimo(Emprestimo emprestimo) {
		return new ComprovanteEmprestimoLocadoraVeiculos(emprestimo);
	}

	@Override
	public ComprovanteDevolucao gerarComprovanteDevolucao(Emprestimo emprestimo, double valor) {
		return new ComprovanteDevolucaoLocadoraVeiculos(emprestimo, valor);
	}

}
