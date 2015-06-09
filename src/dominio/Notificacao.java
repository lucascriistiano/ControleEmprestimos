package dominio;

public abstract class Notificacao {
	private String mensagem;
	
	public Notificacao(String mensagem) {
		this.setMensagem(mensagem);
	}
	
	public String getMensagem() {
		return mensagem;
	}

	public void setMensagem(String mensagem) {
		this.mensagem = mensagem;
	}
	
	public abstract void enviar();

}