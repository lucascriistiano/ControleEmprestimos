package instanciabiblioteca;

import java.util.Calendar;
import java.util.Date;

import dominio.Cliente;
import dominio.Emprestimo;
import dominio.RegraEmprestimo;
import excecao.EmprestimoInvalidoException;

public class RegraBiblioteca implements RegraEmprestimo{

	private static final int DIAS_PARA_NOTIFICACAO = 5;

	@Override
	public int getDiasNotificacaoPrevia() {
		return DIAS_PARA_NOTIFICACAO;
	}
	
	@Override
	public double calcularValorFinal(Emprestimo emprestimo, double taxaExtra) {
		return 0;
	}

	@Override
	public Date calcularDataDevolucao(Emprestimo emprestimo) {
		//Retorna a data minima para emprestimo (1 dia)
		Calendar calendar = Calendar.getInstance();
		Cliente locador = emprestimo.getCliente();
		
		if(locador instanceof Aluno) {
			//Prazo de 15 dias para o emprestimo se for aluno
			calendar.add(Calendar.DAY_OF_MONTH, 15);
		}
		else if(locador instanceof Professor) {
			//Prazo de 45 dias para o emprestimo se for professor 
			calendar.add(Calendar.DAY_OF_MONTH, 45);
		}
		
		return calendar.getTime();
	}

	@Override
	public boolean validarDataDevolucao(Date dataEmprestimo, Date dataDevolucao) throws EmprestimoInvalidoException {
		//Como a data é gerada automaticamente, retorna sempre true
		return true;
	}
}
