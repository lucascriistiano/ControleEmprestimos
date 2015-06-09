package controle;

import java.util.List;

import dominio.Emprestimo;
import dominio.FabricaNotificacao;
import dominio.RegraEmprestimo;

public class VerificadorPrazos {
	
	private RegraEmprestimo regraEmprestimo;
	private NotificadorPrazos notificadorPrazos;
	

	public VerificadorPrazos(RegraEmprestimo regraEmprestimo, FabricaNotificacao fabricaNotificacao) {
		this.regraEmprestimo = regraEmprestimo;
		this.notificadorPrazos = new NotificadorPrazos(fabricaNotificacao);
	}
	
	public boolean verificarEmprestimo(Emprestimo emprestimo) {
		if(regraEmprestimo.prazoExpirado(emprestimo)) {
			notificadorPrazos.notificarPrazoExpirado(emprestimo);
			return false;
		}
		else if(regraEmprestimo.prazoProximo(emprestimo)) {
			notificadorPrazos.notificarPrazoProximo(emprestimo);
			return false;
		}
		
		return true;
	}
	
	public boolean verificarEmprestimos(List<Emprestimo> emprestimos) {
		boolean notificado = false;
		for(Emprestimo emprestimo : emprestimos) {
			if(regraEmprestimo.prazoExpirado(emprestimo)) {
				notificadorPrazos.notificarPrazoExpirado(emprestimo);
				notificado = true;
			}
			else if(regraEmprestimo.prazoProximo(emprestimo)) {
				notificadorPrazos.notificarPrazoProximo(emprestimo);
				notificado = true;
			}
		}
		return notificado;
	}
}
