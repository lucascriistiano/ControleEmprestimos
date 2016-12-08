package excecao;

public class UsuarioInvalidoException extends Exception {
	
	private static final long serialVersionUID = 1L;

	
	
	public UsuarioInvalidoException(Throwable cause) {
		super(cause);
		// TODO Auto-generated constructor stub
	}
	
	
	
	public UsuarioInvalidoException(String message, Throwable cause) {
		super(message, cause);
		// TODO Auto-generated constructor stub
	}



	public UsuarioInvalidoException(String message) {
		super(message);
	}
	
}
