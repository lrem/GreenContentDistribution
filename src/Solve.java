import ilog.concert.IloException;

import java.io.IOException;

/**
 * The entry point for solving a single problem instance.
 */

/**
 * @author lrem
 *
 */
public class Solve {

	/**
	 * @param args
	 * @throws IOException 
	 * @throws IloException 
	 */
	public static void main(String[] args) throws IloException, IOException {
		String ipath = args[0];
		double alpha = Double.valueOf(args[1]);
		double beta = Double.valueOf(args[2]);
		double gamma = Double.valueOf(args[3]);
		double cbw = Double.valueOf(args[4]);
		double limit = Double.valueOf(args[5]);
		
		Model model = new Model (ipath, alpha, beta, gamma, cbw, limit);
		System.out.println("Model constructed");
	}

}
