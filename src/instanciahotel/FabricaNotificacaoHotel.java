package instanciahotel;

import dominio.Emprestimo;
import dominio.FabricaNotificacao;
import dominio.Notificacao;
import dominio.NotificacaoCelular;

public class FabricaNotificacaoHotel implements FabricaNotificacao {

	@Override
	public Notificacao getNotificacaoPrazoExpirado(Emprestimo emprestimo) {
		// TODO Auto-generated method stub
		String mensagem = "---------- Hotel H ----------\n";
		mensagem += "-Notificacao de Emprestimo Expirado-\n";
		mensagem += "O prazo do seu emprestimo foi expirado. Compareca a recepcao para verificar a possibilidade de renovacao do prazo.\n";
		mensagem += "Data da Locacao: ...\n";
		mensagem += "Data para Devolucao: ...\n";
		mensagem += "Quarto: ...\n";
		
		return new NotificacaoCelular(mensagem);
	}

	@Override
	public Notificacao getNotificacaoPrazoProximo(Emprestimo emprestimo) {
		// TODO Auto-generated method stub
		String mensagem = "---------- Hotel H ----------\n";
		mensagem += "-Notificacao de Emprestimo Proximo de Expirar-\n";
		mensagem += "O prazo do seu emprestimo esta expirando. Caso deseje renovar o prazo do emprestimo, compareca a recepcao do hotel para verificar a possibilidade de extensao do prazo.\n";
		mensagem += "Data da Locacao: ...\n";
		mensagem += "Data para Devolucao: ...\n";
		mensagem += "Quarto: ...\n";
		
		return new NotificacaoCelular(mensagem);
	}

}
