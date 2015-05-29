package dominio;

public interface Notificacao {
	boolean notificarPrazoExpirado(Emprestimo emprestimo);
	boolean notificarPrazoProximo(Emprestimo emprestimo);
}