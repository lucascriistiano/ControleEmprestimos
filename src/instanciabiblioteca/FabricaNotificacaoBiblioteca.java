package instanciabiblioteca;

import dominio.Emprestimo;
import dominio.FabricaNotificacao;
import dominio.Notificacao;
import dominio.NotificacaoCelular;

public class FabricaNotificacaoBiblioteca implements FabricaNotificacao {

	@Override
	public Notificacao getNotificacaoPrazoExpirado(Emprestimo emprestimo) {
		// TODO Auto-generated method stub
		String mensagem = "---------- Biblioteca ZN----------\n";
		mensagem += "-Notificacao de Emprestimo Expirado-\n";
		mensagem += "O prazo do seu emprestimo foi expirado. Compareca a biblioteca para devolucao ou entre em contato para redefinir o prazo.\n";
		mensagem += "Data do Emprestimos: ...\n";
		mensagem += "Data para Devolucao: ...\n";
		mensagem += "Livro: ...\n";
		
		return new NotificacaoCelular(mensagem);
	}

	@Override
	public Notificacao getNotificacaoPrazoProximo(Emprestimo emprestimo) {
		// TODO Auto-generated method stub
		String mensagem = "---------- Biblioteca ----------\n";
		mensagem += "-Notificacao de Emprestimo Proximo de Expirar-\n";
		mensagem += "O prazo do seu emprestimo esta expirando. Caso deseje renovar o prazo do emprestimo, entre em contato ou compareca a biblioteca.\n";
		mensagem += "Data da Locacao: ...\n";
		mensagem += "Data para Devolucao: ...\n";
		mensagem += "Livro: ...\n";
		
		return new NotificacaoCelular(mensagem);
	}

}
