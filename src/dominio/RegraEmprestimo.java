package dominio;

import java.util.Date;

public interface RegraEmprestimo {
	boolean validarCliente(Cliente cliente);
	boolean validarRecurso(Recurso recurso);
	boolean prazoExpirado(Emprestimo emprestimo);
	Date calcularDataDeDevolucao(Emprestimo emprestimo);
}
