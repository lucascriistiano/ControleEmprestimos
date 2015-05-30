package dominio;

import java.util.Calendar;
import java.util.Date;

public class RegraCarro implements RegraEmprestimo{

	@Override
	public boolean validarCliente(Cliente cliente) {
		ClienteLocador c = (ClienteLocador) cliente;
		if(c.getCarteiraMotorista().trim().isEmpty()) // não tem carteira de motorista
			return false;
		else
			return true;
	}

	@Override
	public boolean validarRecurso(Recurso recurso) {
		// TODO Auto-generated method stub
		return true;
	}

	@Override
	public boolean prazoExpirado(Emprestimo emprestimo) {
		Date dataAtual = new Date();
		if((dataAtual.getTime() - emprestimo.getDataDevolucao().getTime()) >= 0)			
			return false;
		else
			return true;
	}

	@Override
	public Date calcularDataDeDevolucao(Emprestimo emprestimo) {
		// TODO Auto-generated method stub
		Calendar calendar = Calendar.getInstance();
		calendar.add(Calendar.DAY_OF_MONTH, 7);
		return calendar.getTime();
	}


}
