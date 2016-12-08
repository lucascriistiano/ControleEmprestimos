package dominio;

public abstract class Notificacao {

	private /*@  spec_public @*/ String mensagem;
	
	public Notificacao(String mensagem) {
		this.mensagem = mensagem;
	}
	
	public /*@ pure @*/ String getMensagem() {
		return mensagem;
	}
	
	public abstract void enviar();

}