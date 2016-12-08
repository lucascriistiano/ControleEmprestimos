package controle;

import dominio.Emprestimo;
import dominio.FabricaNotificacao;
import dominio.Notificacao;

public class NotificadorPrazos {
	
	//@ public invariant fabricaNotificacao != null;
	private /*@ spec_public @*/ FabricaNotificacao fabricaNotificacao;
	
	//@ public initially fabricaNotificacao != null;
	public NotificadorPrazos(FabricaNotificacao fabricaNotificacao) {
		this.fabricaNotificacao = fabricaNotificacao;
	}
	
	/*@
	 @ requires !emprestimo.isQuitado();
	 @*/
	public void notificarPrazoExpirado(Emprestimo emprestimo) {
		Notificacao notificacao = fabricaNotificacao.getNotificacaoPrazoExpirado(emprestimo);
		notificacao.enviar();
	}

	/*@
	 @ requires !emprestimo.isQuitado();
	 @*/
	public void notificarPrazoProximo(Emprestimo emprestimo) {
		Notificacao notificacao = fabricaNotificacao.getNotificacaoPrazoProximo(emprestimo);
		notificacao.enviar();
	}
}
