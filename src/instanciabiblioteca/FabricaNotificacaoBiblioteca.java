package instanciabiblioteca;

import java.text.SimpleDateFormat;

import dominio.Emprestimo;
import dominio.FabricaNotificacao;
import dominio.Notificacao;
import dominio.NotificacaoEmail;
import dominio.Recurso;

public class FabricaNotificacaoBiblioteca implements FabricaNotificacao {

	@Override
	public Notificacao getNotificacaoPrazoExpirado(Emprestimo emprestimo) {
		String mensagem = "---------- Biblioteca ZN----------\n";
		mensagem += "-Notificacao de Emprestimo Expirado-\n";
		mensagem += "O prazo do seu emprestimo foi expirado. Compareca a biblioteca para devolucao ou entre em contato para redefinir o prazo.\n";
		mensagem += "Data do Emprestimo: " + new SimpleDateFormat("dd/MM/yyyy").format(emprestimo.getDataEmprestimo()) + "\n";
		mensagem += "Data para Devolucao: " + new SimpleDateFormat("dd/MM/yyyy").format(emprestimo.getDataDevolucao()) + "\n";
		mensagem += "Livro(s):\n";
		
		for(Recurso recurso : emprestimo.getRecursos()) {
			Livro livro = (Livro) recurso;
			
			mensagem += "\tCodigo: " + livro.getCodigo();
			mensagem += " - Descricao: " + livro.getDescricao();
			mensagem += " - Autor: " + livro.getAutor();
			mensagem += " - Editora: " + livro.getEditora();
			mensagem += " - Edicao: " + livro.getEdicao();
			mensagem += " - Quantidade: " + livro.getQuantidade();
			mensagem += " - Titulo: " + livro.getTitulo() + "\n";
		}
		
		return new NotificacaoEmail(mensagem);
	}

	@Override
	public Notificacao getNotificacaoPrazoProximo(Emprestimo emprestimo) {
		String mensagem = "---------- Biblioteca ZN ----------\n";
		mensagem += "-Notificacao de Emprestimo Proximo de Expirar-\n";
		mensagem += "O prazo do seu emprestimo esta expirando. Caso deseje renovar o prazo do emprestimo, entre em contato ou compareca a biblioteca.\n";
		mensagem += "Data do Emprestimo: " + new SimpleDateFormat("dd/MM/yyyy").format(emprestimo.getDataEmprestimo()) + "\n";
		mensagem += "Data para Devolucao: " + new SimpleDateFormat("dd/MM/yyyy").format(emprestimo.getDataDevolucao()) + "\n";
		mensagem += "Livro(s):\n";
		
		for(Recurso recurso : emprestimo.getRecursos()) {
			Livro livro = (Livro) recurso;
			
			mensagem += "\tCodigo: " + livro.getCodigo();
			mensagem += " - Descricao: " + livro.getDescricao();
			mensagem += " - Autor: " + livro.getAutor();
			mensagem += " - Editora: " + livro.getEditora();
			mensagem += " - Edicao: " + livro.getEdicao();
			mensagem += " - Quantidade: " + livro.getQuantidade();
			mensagem += " - Titulo: " + livro.getTitulo() + "\n";
		}
		
		return new NotificacaoEmail(mensagem);
	}

}
