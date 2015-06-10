package instancialocadoraveiculos;

import dominio.Emprestimo;
import dominio.FabricaNotificacao;
import dominio.Notificacao;
import dominio.NotificacaoCelular;

public class FabricaNotificacaoLocadoraVeiculos implements FabricaNotificacao {

	@Override
	public Notificacao getNotificacaoPrazoExpirado(Emprestimo emprestimo) {
		// TODO Auto-generated method stub
		String mensagem = "---------- Locadora LoCar ----------\n";
		mensagem += "-Notificacao de Emprestimo Expirado-\n";
		mensagem += "O prazo do seu emprestimo foi expirado. Compareca a loja para devolucao ou entre em contato para redefinir o prazo.\n";
		mensagem += "Data da Locacao: ...\n";
		mensagem += "Data para Devolucao: ...\n";
		mensagem += "Veiculo: ...\n";
		
		return new NotificacaoCelular(mensagem);
	}

	@Override
	public Notificacao getNotificacaoPrazoProximo(Emprestimo emprestimo) {
		// TODO Auto-generated method stub
		String mensagem = "---------- Locadora LoCar ----------\n";
		mensagem += "-Notificacao de Emprestimo Proximo de Expirar-\n";
		mensagem += "O prazo do seu emprestimo esta expirando. Caso deseje renovar o prazo do emprestimo, entre em contato ou compareca a loja mais proxima.\n";
		mensagem += "Data da Locacao: ...\n";
		mensagem += "Data para Devolucao: ...\n";
		mensagem += "Veiculo: ...\n";
		
		return new NotificacaoCelular(mensagem);
	}

}
