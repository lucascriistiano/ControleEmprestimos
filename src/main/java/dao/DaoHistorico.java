package dao;

import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.stream.Collectors;

import dominio.HistoricoEmprestimo;
import dominio.Recurso;
import excecao.DataException;

public class DaoHistorico extends DaoImpl<HistoricoEmprestimo> {
	
	private static /*@ nullable @*/ DaoHistorico daoHistorico = null;
	
	private DaoHistorico() {
		super("Emprestimo");
	}
	
	
	/*@
 	 @	requires obj.getEmprestimo().isQuitado();
 	 @ 	requires obj != null;
 	 @	requires ((long) obj.getCodigo()) == 0L;
	 @	requires !list.contains(obj);
	 @ 	ensures list.size() == \old(list.size()) + 1;
	 @ 	ensures list.get(list.size()-1) == obj;
	 @	ensures ((long) obj.getCodigo()) > 0L;		
	 @*/
	@Override
	public /*@ pure @*/ void add(HistoricoEmprestimo obj) throws DataException {
		super.add(obj);
	}

	public static DaoHistorico getInstance() {
		if(daoHistorico == null)
			daoHistorico = new DaoHistorico();
				
		return daoHistorico;
	}
	
	public /*@ pure @*/ boolean existsEmprestimo(long codigo) throws DataException {
		return list.stream().filter(x -> x.getEmprestimo().getCodigo().equals(codigo)).count() > 0;
	}

	public /*@ pure @*/ List<HistoricoEmprestimo> getHistoricoCliente(long codigo) throws DataException {
		return list.stream().filter(x -> x.getEmprestimo().getCliente().getCodigo().equals(codigo)).collect(Collectors.toList());
	}
	
	public /*@ pure @*/ Integer findCategoriaAltaByCliente(long codigoCliente) throws DataException{
		
		List<HistoricoEmprestimo> historicoEmprestimos = this.getHistoricoCliente(codigoCliente);
		
		Map<Integer, List<Recurso>> recursosByCategoria = historicoEmprestimos.stream()
		.map(e -> e.getEmprestimo().getRecursos())
		.flatMap(r -> r.stream())
		.collect(Collectors.groupingBy(Recurso::getCategoria));
		
		Optional<Integer> categoria = recursosByCategoria.entrySet()
					.stream()
					.map(e -> e.getValue().size())
					.max(Integer::max);
		
		return categoria.orElse(null);
		
	}
	

}
