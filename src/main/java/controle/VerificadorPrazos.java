package controle;

import java.util.Date;
import java.util.List;

import dominio.Emprestimo;
import dominio.FabricaNotificacao;
import dominio.RegraEmprestimo;
import util.GerenciadorDatas;

public class VerificadorPrazos {
	
	private /*@ spec_public @*/ RegraEmprestimo regraEmprestimo;
	private /*@ spec_public @*/ NotificadorPrazos notificadorPrazos;
	private /*@ spec_public @*/ GerenciadorDatas gerenciadorDatas;
	
	public VerificadorPrazos(RegraEmprestimo regraEmprestimo, FabricaNotificacao fabricaNotificacao, GerenciadorDatas gerenciadorDatas) {
		this.regraEmprestimo = regraEmprestimo;
		this.notificadorPrazos = new NotificadorPrazos(fabricaNotificacao);
		this.gerenciadorDatas = gerenciadorDatas;
	}
	
	/*@
	 @ requires gerenciadorDatas != null;
	 @ requires emprestimo.getDataDevolucao() != null;
	 @ requires gerenciadorDatas.getDataAtual() != null;
	 @ ensures gerenciadorDatas.getDataAtual().after(emprestimo.getDataDevolucao()) ==> \result == true;
	 @ ensures !gerenciadorDatas.getDataAtual().after(emprestimo.getDataDevolucao()) ==> \result == false;
	 @*/
	public /*@ pure @*/ boolean prazoExpirado(Emprestimo emprestimo) {
		Date dataAtual = gerenciadorDatas.getDataAtual();
	
		long tempoExpirado = (dataAtual.getTime() - emprestimo.getDataDevolucao().getTime());
		if(tempoExpirado > 0)			
			return true;
		else
			return false;
	}

	public /*@ pure @*/ boolean prazoProximo(Emprestimo emprestimo) {
		Date dataAtual = gerenciadorDatas.getDataAtual();
		long tempoExpirado = dataAtual.getTime() - emprestimo.getDataDevolucao().getTime();
		long diasExpirado = tempoExpirado / (1000 * 60 * 60 * 24);
		
		if(diasExpirado < 0 && Math.abs(diasExpirado) <= this.regraEmprestimo.getDiasNotificacaoPrevia())			
			return true;
		else
			return false;
	}
	
	/*@
	 @ requires emprestimo.getDataDevolucao() != null;
	 @ ensures prazoExpirado(emprestimo) ==> \result == true;
	 @ ensures prazoProximo(emprestimo) ==> \result == true;
	 @ ensures !prazoExpirado(emprestimo) && !prazoProximo(emprestimo) ==> \result == false;
	 @*/
	public /*@ pure @*/ boolean notificarPrazoDevolucao(Emprestimo emprestimo) {
		if(prazoExpirado(emprestimo)) {
			notificadorPrazos.notificarPrazoExpirado(emprestimo);
			return true;
		} else if(prazoProximo(emprestimo)) {
			notificadorPrazos.notificarPrazoProximo(emprestimo);
			return true;
		}
	
		return false;
	}
	
	public /*@ pure @*/ long contarPendentesNotificacao(List<Emprestimo> emprestimos){
		return emprestimos.stream().filter(x -> prazoExpirado(x) || prazoProximo(x)).count();
	}

	/*@
	 @ requires emprestimos != null;
	 @ ensures contarPendentesNotificacao(emprestimos) > 0 ==> \result == true;	
	 @ ensures contarPendentesNotificacao(emprestimos) <= 0 ==> \result == false;	
	 @*/
	public /*@ pure @*/ boolean verificarEmprestimos(List<Emprestimo> emprestimos) {
		boolean notificado = false;
		for(Emprestimo emprestimo : emprestimos) {
			if(prazoExpirado(emprestimo)) {
				notificadorPrazos.notificarPrazoExpirado(emprestimo);
				notificado = true;
			} else if(prazoProximo(emprestimo)) {
				notificadorPrazos.notificarPrazoProximo(emprestimo);
				notificado = true;
			}
		}
		return notificado;
	}
}
