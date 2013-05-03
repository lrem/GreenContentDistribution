import ilog.concert.IloException;
import java.io.IOException;
import java.util.Comparator;
import java.util.PriorityQueue;


public class FastSTH extends SpanningTreeHeuristic {

	private double speed;
	
	public FastSTH(String ipath, double alpha, double beta, double gamma,
			double cbw, double limit, double speed) throws IloException, IOException {
		super(ipath, alpha, beta, gamma, cbw, limit);
		this.speed = speed;
	}

	public void step() throws IloException {
		model.solve();
		relaxations++;
		makeCopy();
		freezeInteger();
		
		if(finished())
			return;
		
		final int toFreeze = Math.max(1, (int)((xToDo.size() + yToDo.size()) * speed));
		
		PriorityQueue<Pair<Integer, Integer>> edges = new PriorityQueue<Pair<Integer,Integer>>(xToDo.size() + 1, new Comparator<Pair<Integer,Integer>>() {
			public int compare(Pair<Integer,Integer> o1, Pair<Integer,Integer> o2) {
				if (xcopy[o1.a][o1.b] < xcopy[o2.a][o2.b])
					return 1;
				else if (xcopy[o1.a][o1.b] > xcopy[o2.a][o2.b])
					return -1;
				else
					return 0;
			};
		} );
		edges.addAll(xToDo);
		PriorityQueue<Integer> caches = new PriorityQueue<Integer>(yToDo.size() + 1, new Comparator<Integer>() {
			@Override
			public int compare(Integer o1, Integer o2) {
				if (ycopy[o1] < ycopy[o2])
					return 1;
				else if (ycopy[o1] > ycopy[o2])
					return -1;
				else
					return 0;
			}
		});
		caches.addAll(yToDo);
		
		for(int i = 0; i < toFreeze; i++)
			if(edges.size() == 0)
				freezeCache(caches.remove());
			else if (caches.size() == 0 || xload(edges.peek()) < yload(caches.peek()))
				freezeEdge(edges.remove());
			else
				freezeCache(caches.remove());
	}

	private double yload(Integer c) {
		return ycopy[c];
	}

	private double xload(Pair<Integer, Integer> e) {
		return xcopy[e.a][e.b];
	}
}
