package dao;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.stream.Collectors;

import dominio.Emprestimo;
import dominio.Recurso;
import excecao.DataException;

public class DaoHistorico extends DaoImpl<Emprestimo> {
	
	private static /*@ nullable @*/ DaoHistorico daoHistorico = null;
	
	private DaoHistorico() {
		super("Emprestimo");
	}
	
	public static DaoHistorico getInstance() {
		if(daoHistorico == null)
			daoHistorico = new DaoHistorico();
				
		return daoHistorico;
	}

	public List<Emprestimo> getHistoricoCliente(Long codigo) throws DataException {
		List<Emprestimo> resultList = new ArrayList<Emprestimo>();
		
		Iterator<Emprestimo> it = list.iterator();
		while(it.hasNext()) {
			Emprestimo emprestimo = it.next();
			if(emprestimo.getCliente().getCodigo().equals(codigo)) {
				resultList.add(emprestimo);
			}
		}
		
		return resultList;
	}
	
	public Integer findCategoriaAltaByCliente(long codigoCliente) throws DataException{
		
		List<Emprestimo> historicoEmprestimos = this.getHistoricoCliente(codigoCliente);
		
		Map<Integer, List<Recurso>> recursosByCategoria = historicoEmprestimos.stream()
		.map(e -> e.getRecursos())
		.flatMap(r -> r.stream())
		.collect(Collectors.groupingBy(Recurso::getCategoria));
		
		Optional<Integer> categoria = recursosByCategoria.entrySet()
					.stream()
					.map(e -> e.getValue().size())
					.max(Integer::max);
		
		return categoria.orElse(null);
		
	}
	

}
