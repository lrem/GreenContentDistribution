import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.HashSet;
import java.util.StringTokenizer;
import java.util.logging.Logger;

import ilog.concert.IloException;
import ilog.concert.IloLinearNumExpr;
import ilog.concert.IloNumVar;
import ilog.concert.IloObjectiveSense;
import ilog.cplex.IloCplex;
import ilog.cplex.IloCplex.UnknownObjectException;

/**
 * The LP model of an instance
 */

/**
 * @author lrem
 *
 */
public class Model {

	protected static Logger log = Logger.getLogger("Model");
	int routerCount;
	int cdnCount;
	double [][] r2r;
	double [][] r2cdn;
	double [][] topo;
	IloNumVar [][] x;
	IloNumVar [] y;
	IloNumVar [] z;
	IloNumVar [][][] f;
	IloNumVar [][][] sv;
	IloNumVar [][] cr;
	IloNumVar [][] cc;
	HashSet<Pair<Integer, Integer>> xToDo;
	HashSet<Integer> yToDo;
	double alpha, beta, gamma, cbw;
	ArrayList<ArrayList<Integer>> locations;
	ArrayList<ArrayList<Double>> capacities;
	public int relaxations = 0;

	IloCplex model;
	protected double [][] xcopy;
	protected double [] ycopy;

	public Model (String ipath, double alpha, double beta, double gamma, double cbw, double limit) 
			throws IloException, IOException
			{
		this.alpha = alpha;
		this.beta = beta;
		this.gamma = gamma;
		this.cbw = cbw;
		routerCount = parseInt(ipath + "rcount");
		cdnCount = parseInt(ipath + "ccount");
		r2r = parseMatrix(ipath + "r2r.int", routerCount, routerCount);
		r2cdn = parseMatrix(ipath + "r2cdn.int", routerCount, cdnCount);
		topo = parseMatrix(ipath + "topo.txt", routerCount, routerCount);
		locations = parseAL(ipath + "cdnl.int", new Integer(3));
		assert(locations.size() == cdnCount);
		capacities = parseAL(ipath + "cdnc.int", new Double(3));
		assert(capacities.size() == cdnCount);

		model = new IloCplex();
		model.setParam(IloCplex.DoubleParam.TiLim, limit);

		IloLinearNumExpr obj = model.linearNumExpr();
		x = new IloNumVar[routerCount][routerCount];
		y = new IloNumVar[routerCount];
		z = new IloNumVar[routerCount];
		for(int i = 0; i < routerCount; i++)
		{
			for(int j = 0; j < routerCount; j++)
			{
				x[i][j] = model.numVar(0, 1);
				obj.addTerm(1, x[i][j]);
			}
			y[i] = model.numVar(0, 1);
			obj.addTerm(beta, y[i]);
			z[i] = model.numVar(0, 1);
			obj.addTerm(gamma, z[i]);
		}
		model.addObjective(IloObjectiveSense.Minimize, obj);

		f = new IloNumVar[routerCount][routerCount][routerCount];
		for(int i = 0; i < routerCount; i++)
			for(int j = 0; j < routerCount; j++)
				for(int k = 0; k < routerCount; k++)
					f[i][j][k] = model.numVar(0, Double.MAX_VALUE);
		cr = new IloNumVar[routerCount][routerCount];
		for(int i = 0; i < routerCount; i++)
			for(int j = 0; j < routerCount; j++)
				cr[i][j] = model.numVar(0, Double.MAX_VALUE);
		cc = new IloNumVar[routerCount][cdnCount];
		for(int i = 0; i < routerCount; i++)
			for(int j = 0; j < cdnCount; j++)
				cc[i][j] = model.numVar(0, Double.MAX_VALUE);
		sv = new IloNumVar[cdnCount][routerCount][routerCount];
		for(int i = 0; i < cdnCount; i++)
			for(int j = 0; j < routerCount; j++)
				for(int k = 0; k < routerCount; k++)
					sv[i][j][k] = model.numVar(0, Double.MAX_VALUE);

		// Flow constraints
		for(int src = 0; src < routerCount; src++)
			for(int middle = 0; middle < routerCount; middle++)
			{
				IloLinearNumExpr lhs = model.linearNumExpr();
				for(int left = 0; left < routerCount; left++)
					lhs.addTerm(1, f[src][left][middle]);
				for(int right = 0; right < routerCount; right++)
					lhs.addTerm(-1, f[src][middle][right]);
				double total = 0;
				if(middle == src)
				{
					/*total = -sum(strict_demand(src, dst) 
                            for dst in xrange(router_count)) \
                        -sum(flexible_demand(src, cdn)
                            for cdn in xrange(cdn_count))*/
					for(int dst = 0; dst < routerCount; dst++)
					{
						total -= r2r[src][dst];
						lhs.addTerm(-1, cr[src][dst]);
					}
					for(int cdn = 0; cdn < cdnCount; cdn++)
					{
						total -= r2cdn[src][cdn];
						lhs.addTerm(-1, cc[src][cdn]);
					}
				}
				else
				{
					/*total = strict_demand(src, middle) + \
	                        sum(serv_vars[cdn, src, middle]
	                                for cdn in xrange(cdn_count) 
	                                if  middle in locations[cdn])*/
					total += r2r[src][middle];
					lhs.addTerm(1, cr[src][middle]);
					for(int cdn = 0; cdn < cdnCount; cdn++)
						if(locations.get(cdn).contains(middle))
							lhs.addTerm(-1, sv[cdn][src][middle]);
				}
				// lpSum(incoming) - lpSum(outgoing) == total
				model.addEq(lhs, total);
			}

		// Link capacities
		for(int i = 0; i < routerCount; i++)
			for(int j = 0; j < i; j++)
			{
				IloLinearNumExpr total = model.linearNumExpr();
				for(int src = 0; src < routerCount; src++)
				{
					total.addTerm(1, f[src][i][j]);
					total.addTerm(1, f[src][j][i]);
				}
				IloLinearNumExpr cap = model.linearNumExpr();
				assert(topo[i][j] == topo[j][i]);
				cap.addTerm(x[j][i], topo[i][j]);
				model.addLe(total, cap);
			}

		// Server capacities
		for(int cdn = 0; cdn < cdnCount; cdn++)
			for(int i = 0; i < locations.get(cdn).size(); i++)
			{
				int loc = locations.get(cdn).get(i);
				IloLinearNumExpr total = model.linearNumExpr();
				for(int src = 0; src < routerCount; src++)
					total.addTerm(1, sv[cdn][src][loc]);
				model.addLe(total, capacities.get(cdn).get(i));
			}

		// Cache alpha-limits
		for(int src = 0; src < routerCount; src++)
		{
			for(int dst = 0; dst < routerCount; dst++)
			{
				IloLinearNumExpr lhs = model.linearNumExpr();
				lhs.addTerm(1, cr[src][dst]);
				model.addLe(lhs, alpha * r2r[src][dst]);
			}
			for(int cdn = 0; cdn < cdnCount; cdn++)
			{
				IloLinearNumExpr lhs = model.linearNumExpr();
				lhs.addTerm(1, cc[src][cdn]);
				model.addLe(lhs, alpha * r2cdn[src][cdn]);
			}
		}

		// Cache capacities
		for(int src = 0; src < routerCount; src++)
		{
			IloLinearNumExpr total = model.linearNumExpr();
			for(int dst = 0; dst < routerCount; dst++)
				total.addTerm(1, cr[src][dst]);
			for(int cdn = 0; cdn < cdnCount; cdn++)
				total.addTerm(1, cc[src][cdn]);
			IloLinearNumExpr cap = model.linearNumExpr();
			cap.addTerm(z[src], cbw);
			model.addLe(total, cap);
			IloLinearNumExpr load = model.linearNumExpr();
			load.addTerm(1, z[src]);
			IloLinearNumExpr up = model.linearNumExpr();
			up.addTerm(1, y[src]);
			model.addLe(load, up);
		}
		
		xToDo = new HashSet<Pair<Integer,Integer>>();
		yToDo = new HashSet<Integer>();
		for(int i = 0; i < routerCount; i++)
		{		
			for(int j = 0; j < i; j++)
				if(topo[j][i] > 0)
					xToDo.add(Pair.of(j, i));
			yToDo.add(i);
		}
			}


	protected void freezeInteger() throws UnknownObjectException, IloException {
		ArrayList<Pair<Integer, Integer>> xrem = new ArrayList<Pair<Integer,Integer>>();
		for(Pair<Integer, Integer> e: xToDo)
		{
			double v = xcopy[e.a][e.b];
			if(v == 1)
			{
				log.info("Taking edge (" + e.a + "," + e.b + ") with load = " + xcopy[e.a][e.b]);
				IloLinearNumExpr exp = model.linearNumExpr();
				exp.addTerm(1, x[e.a][e.b]);
				model.addEq(exp, 1);
				xrem.add(e);
			}
			if(v == 0)
			{
				log.info("Killing edge (" + e.a + "," + e.b + ") with load = " + xcopy[e.a][e.b]);
				IloLinearNumExpr exp = model.linearNumExpr();
				exp.addTerm(1, x[e.a][e.b]);
				model.addEq(exp, 0);
				xrem.add(e);
			}
		}
		for(Pair<Integer, Integer> e: xrem)
			xToDo.remove(e);
		ArrayList<Integer> yrem = new ArrayList<Integer>();
		for(int i: yToDo)
		{
			double v = ycopy[i];
			if(v == 1)
			{
				log.info("Taking cache " + i +" with load = " + ycopy[i]);
				IloLinearNumExpr exp = model.linearNumExpr();
				exp.addTerm(1, y[i]);
				model.addEq(exp, 1);
				yrem.add(i);				
			}
			if(v == 0)
			{
				log.info("Killing cache " + i +" with load = " + ycopy[i]);
				IloLinearNumExpr exp = model.linearNumExpr();
				exp.addTerm(1, y[i]);
				model.addEq(exp, 0);
				yrem.add(i);				
			}
		}
		for(int i: yrem)
			yToDo.remove(i);
	}
	
	protected void fail() {
		xToDo.clear();
		yToDo.clear();
	}
	
	public boolean finished() {
		return (xToDo.size() == 0) && (yToDo.size() == 0);
	}
	
	public void output(String path) throws IOException, UnknownObjectException, IloException {
		model.solve(); // Just to make sure we have all values in place
		if(model.getStatus() != IloCplex.Status.Optimal)
		{
			outputFailed(path);
			return;
		}
		BufferedWriter xo = new BufferedWriter(new FileWriter(path + "x.out"));
		for(int i = 0; i < routerCount; i++)
		{
			for(int j = 0; j < routerCount; j++)
				xo.write(model.getValue(x[i][j]) + " ");
			xo.write("\n");
		}
		xo.close();
		BufferedWriter yo = new BufferedWriter(new FileWriter(path + "y.out"));
		for(int i = 0; i < routerCount; i++)
			yo.write(model.getValue(y[i]) + " ");
		yo.write("\n");
		yo.close();
		BufferedWriter zo = new BufferedWriter(new FileWriter(path + "z.out"));
		for(int i = 0; i < routerCount; i++)
			zo.write(model.getValue(z[i]) + " ");
		zo.write("\n");
		zo.close();
		BufferedWriter fo = new BufferedWriter(new FileWriter(path + "f.out"));
		for(int i = 0; i < routerCount; i++)
		{
			for(int j = 0; j < routerCount; j++)
				for(int k = 0; k < routerCount; k++)
					fo.write(model.getValue(f[i][j][k]) + " ");
			fo.write("\n");
		}
		fo.close();
		// We don't use any more details of the solution right now
		BufferedWriter ro = new BufferedWriter(new FileWriter(path + "relaxations.out"));
		ro.write(relaxations + "\n");
		ro.close();
		BufferedWriter oo = new BufferedWriter(new FileWriter(path + "obj.out"));
		oo.write(model.getObjValue() + "\n");
		oo.close();
		log.info("Final objective value = " + model.getObjValue());
	}
	
	private void outputFailed(String path) throws IOException {
		BufferedWriter xo = new BufferedWriter(new FileWriter(path + "x.out"));
		for(int i = 0; i < routerCount; i++)
		{
			for(int j = 0; j < routerCount; j++)
				xo.write(-1 + " ");
			xo.write("\n");
		}
		xo.close();
		BufferedWriter yo = new BufferedWriter(new FileWriter(path + "y.out"));
		for(int i = 0; i < routerCount; i++)
			yo.write(-1 + " ");
		yo.write("\n");
		yo.close();
		BufferedWriter zo = new BufferedWriter(new FileWriter(path + "z.out"));
		for(int i = 0; i < routerCount; i++)
			zo.write(-1 + " ");
		zo.write("\n");
		zo.close();
		BufferedWriter fo = new BufferedWriter(new FileWriter(path + "f.out"));
		for(int i = 0; i < routerCount; i++)
		{
			for(int j = 0; j < routerCount; j++)
				for(int k = 0; k < routerCount; k++)
					fo.write(-1 + " ");
			fo.write("\n");
		}
		fo.close();
		// We don't use any more details of the solution right now
		BufferedWriter ro = new BufferedWriter(new FileWriter(path + "relaxations.out"));
		ro.write(relaxations + "\n");
		ro.close();
		BufferedWriter oo = new BufferedWriter(new FileWriter(path + "obj.out"));
		oo.write(-1 + "\n");
		oo.close();
		log.info("Final objective value = FAIL");		
	}


	private double [][] parseMatrix(String path, int rows, int columns) throws IOException {
		BufferedReader reader = new BufferedReader(new FileReader(path));
		String line;
		double [][] matrix = new double[rows][columns];
		for(int i = 0; i < rows; i++){
			line = reader.readLine();
			assert(line != null);
			StringTokenizer tok = new StringTokenizer(line);
			assert(tok.countTokens() == columns);
			for(int j = 0; j < columns; j++)
				matrix[i][j] = Double.valueOf(tok.nextToken());
		}
		return matrix;
	}

	@SuppressWarnings("unchecked")
	private <T extends Number> ArrayList<ArrayList<T>> parseAL(String path, T ignored) throws NumberFormatException, IOException {
		BufferedReader reader = new BufferedReader(new FileReader(path));
		String line;
		ArrayList<ArrayList<T>> ret = new ArrayList<ArrayList<T>> ();
		while((line = reader.readLine()) != null) {
			StringTokenizer tok = new StringTokenizer(line);
			if(tok.countTokens() == 0) // empty lines can happen only at the end of file, can't they?
				break;
			ArrayList<T> row = new ArrayList<T>();
			while(tok.hasMoreTokens())
				if(ignored instanceof Integer)
					row.add((T) Integer.valueOf(tok.nextToken()));
				else
					row.add((T) Double.valueOf(tok.nextToken()));
			ret.add(row);
		}
		return ret;
	}

	private int parseInt(String path) throws IOException {
		BufferedReader reader = new BufferedReader(new FileReader(path));
		String line = reader.readLine();
		return Integer.valueOf(line);
	}


	protected void makeCopy() throws UnknownObjectException, IloException {
		xcopy = new double[routerCount][routerCount];
		for(int i = 0; i < routerCount; i++)
			for(int j = 0; j < routerCount; j++)
				xcopy[i][j] = model.getValue(x[i][j]);
		ycopy = new double[routerCount];
		for(int i = 0; i < routerCount; i++)
			ycopy[i] = model.getValue(y[i]);
	}
}

@SuppressWarnings("rawtypes")
class Edge implements Comparator, Comparable {
    public int a, b;
    double weight;
    
    public Edge() {
    }
    
    public Edge(int a, int b, double weight) {
      this.a = a;
      this.b = b;
      this.weight = weight;
    }
    
    public int compare(Object o1, Object o2) {
      // Need all the ugliness due to add/remove
      double w1 = ((Edge) o1).weight;
      double w2 = ((Edge) o2).weight;
      int a1 = ((Edge) o1).a;
      int a2 = ((Edge) o2).a;
      int b1   = ((Edge) o1).b;
      int b2   = ((Edge) o2).b;

      if (w1<w2)
        return(1);
      else if (w1==w2 && a1==a2 && b1==b2)
        return(0);
      else if (w1==w2)
        return(1);
      else if (w1>w2)
        return(-1); 
      else
        return(0);
    }
    
    public int compareTo(Object o2) {
    	return compare(this, o2);
    }
    
    public boolean equals(Object obj) {
      return compare(this, obj) == 0;
    }
  }

class Pair<L,R> {
    final L a;
    final R b;

    public Pair(L left, R right) {
      this.a = left;
      this.b = right;
    }

    static <L,R> Pair<L,R> of(L left, R right){
        return new Pair<L,R>(left, right);
    }
}