package dominio;

import java.util.Calendar;
import java.util.Date;

public class RegraCarro implements RegraEmprestimo{

	@Override
	public boolean validarCliente(Cliente cliente) {
		// TODO Auto-generated method stub
		return true;
	}

	@Override
	public boolean validarRecurso(Recurso recurso) {
		// TODO Auto-generated method stub
		return true;
	}

	@Override
	public boolean prazoExpirado(Emprestimo emprestimo) {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public Date calcularDataDeDevolucao(Emprestimo emprestimo) {
		// TODO Auto-generated method stub
		Calendar calendar = Calendar.getInstance();
		calendar.add(Calendar.DAY_OF_MONTH, 7);
		return calendar.getTime();
	}


}
