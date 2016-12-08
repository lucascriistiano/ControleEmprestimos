package excecao;

public class RecursoInvalidoException extends Exception {

	private static final long serialVersionUID = 1L;

	public RecursoInvalidoException(String message) {
		super(message);
	}

	
	
	public RecursoInvalidoException(Throwable cause) {
		super(cause);
		// TODO Auto-generated constructor stub
	}



	public RecursoInvalidoException(String message, Throwable cause) {
		super(message, cause);
		// TODO Auto-generated constructor stub
	}

	
}
