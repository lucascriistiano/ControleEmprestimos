package dominio;

public class FabricaNotificacaoQuarto implements FabricaNotificacao {

	@Override
	public Notificacao getNotificacaoPrazoExpirado(Emprestimo emprestimo) {
		// TODO Auto-generated method stub
		String mensagem = "---------- Hotel H ----------\n";
		mensagem += "-Notificação de Empréstimo Expirado-\n";
		mensagem += "O prazo do seu emprestimo foi expirado. Compareça ao hotel para devolução ou entre em contato para redefinir o prazo.\n";
		mensagem += "Data da Locação: ...\n";
		mensagem += "Data para Devolução: ...\n";
		mensagem += "Quarto: ...\n";
		
		return new NotificacaoCelular(mensagem);
	}

	@Override
	public Notificacao getNotificacaoPrazoProximo(Emprestimo emprestimo) {
		// TODO Auto-generated method stub
		String mensagem = "---------- Hotel H ----------\n";
		mensagem += "-Notificação de Empréstimo Próximo de Expirar-\n";
		mensagem += "O prazo do seu emprestimo está expirando. Caso deseje renovar o prazo do empréstimo, entre em contato ou compareça ao hotel.\n";
		mensagem += "Data da Locação: ...\n";
		mensagem += "Data para Devolução: ...\n";
		mensagem += "Quarto: ...\n";
		
		return new NotificacaoCelular(mensagem);
	}

}
