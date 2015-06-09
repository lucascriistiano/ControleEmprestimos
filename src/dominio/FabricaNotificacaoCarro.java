package dominio;

public class FabricaNotificacaoCarro implements FabricaNotificacao {

	@Override
	public Notificacao getNotificacaoPrazoExpirado(Emprestimo emprestimo) {
		// TODO Auto-generated method stub
		String mensagem = "---------- Locadora LoCar ----------\n";
		mensagem += "-Notificação de Empréstimo Expirado-\n";
		mensagem += "O prazo do seu emprestimo foi expirado. Compareça á loja para devolução ou entre em contato para redefinir o prazo.\n";
		mensagem += "Data da Locação: ...\n";
		mensagem += "Data para Devolução: ...\n";
		mensagem += "Veículo: ...\n";
		
		return new NotificacaoCelular(mensagem);
	}

	@Override
	public Notificacao getNotificacaoPrazoProximo(Emprestimo emprestimo) {
		// TODO Auto-generated method stub
		String mensagem = "---------- Locadora LoCar ----------\n";
		mensagem += "-Notificação de Empréstimo Próximo de Expirar-\n";
		mensagem += "O prazo do seu emprestimo está expirando. Caso deseje renovar o prazo do empréstimo, entre em contato ou compareça à loja mais próxima.\n";
		mensagem += "Data da Locação: ...\n";
		mensagem += "Data para Devolução: ...\n";
		mensagem += "Veículo: ...\n";
		
		return new NotificacaoCelular(mensagem);
	}

}
