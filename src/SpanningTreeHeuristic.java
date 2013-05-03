import ilog.concert.IloException;
import ilog.concert.IloLinearNumExpr;
import ilog.cplex.IloCplex;
import ilog.cplex.IloCplex.UnknownObjectException;

import java.io.IOException;
import java.util.HashSet;
import java.util.PriorityQueue;


public class SpanningTreeHeuristic extends Model {

	public SpanningTreeHeuristic(String ipath, double alpha, double beta,
			double gamma, double cbw, double limit) throws IloException,
			IOException {
		super(ipath, alpha, beta, gamma, cbw, limit);
	}
	
	public void spanningTree() throws IloException {
		model.solve();
		relaxations++;
		if(model.getStatus() != IloCplex.Status.Optimal)
		{
			fail();
			return;
		}
		log.info("Relaxation status = " + model.getStatus() + " value = " + model.getObjValue());
		makeCopy();
		
		HashSet<Integer> connected = new HashSet<Integer>();
		connected.add(0);
		
		PriorityQueue<Edge> edges = new PriorityQueue<Edge>();
		
		
		for(int i = 1; i < routerCount; i++)
			addEdge(0, i, edges);
		
		while(connected.size() < routerCount)
		{
			Edge e = edges.remove();
			log.info("Taking edge (" + e.a + "," + e.b + ") with load = " + e.weight);
			int v;
			if(connected.contains(e.a))
				if(connected.contains(e.b))
					continue;
				else
					v = e.b;
			else
				v = e.a;
			connected.add(v);
			for(int i = 0; i < routerCount; i++)
				if(!connected.contains(i))
					addEdge(v, i, edges);
			IloLinearNumExpr exp = model.linearNumExpr();
			exp.addTerm(1, x[e.a][e.b]);
			model.addEq(exp, 1);
			xToDo.remove(Pair.of(e.a, e.b));
		}
	}

	protected void addEdge(int i, int j, PriorityQueue<Edge> edges) throws UnknownObjectException, IloException
	{
		//System.err.println("Adding edge (" + i + "," + j + ")");
		
		if(j < i)
		{
			int tmp = i;
			i = j;
			j = tmp;
		}

		if(topo[i][j] > 0)
		{
			edges.add(new Edge(i, j, xcopy[i][j]));
		}
	}
	

	
	public void step() throws IloException {
		model.solve();
		relaxations++;
		makeCopy();
		freezeInteger();
		
		if(finished())
			return;
		
		Pair<Integer, Integer> be = null;
		double bev = -1;
		for(Pair<Integer, Integer> e: xToDo)
		{
			double v = xcopy[e.a][e.b];
			if(v > bev)
			{
				bev = v;
				be = e;
			}
		}
		int bc = -1;
		double bcv = -1;
		for(int i: yToDo)
		{
			double v = ycopy[i];
			if(v > bcv)
			{
				bcv = v;
				bc = i;
			}
		}
		if((bev > bcv))
			freezeEdge(be);
		else
			freezeCache(bc);
	}
	
	protected void freezeEdge(Pair<Integer, Integer> be) throws IloException {
		log.info("Taking edge (" + be.a + "," + be.b + ") with load = " + xcopy[be.a][be.b]);
		IloLinearNumExpr exp = model.linearNumExpr();
		exp.addTerm(1, x[be.a][be.b]);
		model.addEq(exp, 1);
		xToDo.remove(be);		
	}

	protected void freezeCache(Integer bc) throws IloException {
		log.info("Taking cache " + bc +" with load = " + ycopy[bc]);
		IloLinearNumExpr exp = model.linearNumExpr();
		exp.addTerm(1, y[bc]);
		model.addEq(exp, 1);
		yToDo.remove(bc);									
	}
}
