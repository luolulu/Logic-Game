import java.io.File;
import java.io.FileNotFoundException;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

public class TheoremProver {
	private static List<Clause> clauses;
	private static List<Integer> parent1, parent2;

	public static void main(String[] args) throws FileNotFoundException {
		String FILE_PATH = args[0];
		int count = 0;	
		File testCase = new File(FILE_PATH);
		clauses = ClauseParser.parse(testCase);
		int GOAL_CLAUSE_START_INDEX = ClauseParser.getGoalStart();
		parent1 = new ArrayList<Integer>();
		parent2 = new ArrayList<Integer>();
		//System.out.println(GOAL_CLAUSE_START_INDEX);
		System.out.println("Number of clauses: " + clauses.size());
		for (int i = 0; i < clauses.size(); i++) {
			printClause(clauses.get(i));
			parent1.add(-1);
			parent2.add(-1);
		}
		System.out.println("------------------------------");
		System.out.println();
		
		//System.out.println("Resolution:");
		
		int i = 0;
		int j = GOAL_CLAUSE_START_INDEX;
		while (true) {
			if (j >= clauses.size()) {
				System.out.println("Cannot be proved.");
				return;
			}
			
			if (i >= j) {
				i = 0;
				j++;
				continue;
			}
			
			Clause ci = clauses.get(i);
			Clause cj = clauses.get(j);
			
			//System.out.println("The " + i + "th clause: ");
			//printClause(ci);
			//System.out.println("The " + j + "th clause: ");
			//printClause(cj);
			
			Clause resoResult = resolution(ci, cj);
			//System.out.println("Resolution result");
			//printClause(resoResult);
			
			if (resoResult.getPosLits().size() == 0 && resoResult.getNegLits().size() == 0) {
				//System.out.println("Proved from clauses: " + i + ", " + j);
				parent1.add(i);
				parent2.add(j);
				break;
			}
			
			if ((!hasRepeat(resoResult)) && (resoResult.getPosSize() + resoResult.getNegSize() < Math.max(ci.getPosSize()+ ci.getNegSize(), cj.getPosSize()  + cj.getNegSize()))) {
				count++;
				clauses.add(resoResult);
				parent1.add(i);
				parent2.add(j);
				//printRes();
			}
			i++;
		}
		printRes();
		int index = parent1.size() - 1;
		System.out.println((index + 1) + ". False {" + (parent1.get(index) + 1) + ", " + (parent2.get(index) + 1) + "}");
		System.out.println("The total resolve steps: " + count);
		}

	public static void printRes() {
		int tempIndex = 0;
		for (Clause c : clauses) {
			System.out.print((tempIndex + 1) + ". " + c);
			if (parent1.get(tempIndex) == -1) {
				System.out.println(" {} ");
			} else {
				System.out.println(" {" + (parent1.get(tempIndex) + 1) + ", " + (parent2.get(tempIndex) + 1) + "}");
			}
			tempIndex++;
		}
	}

	public static void printClause(Clause c) {
		System.out.print("Pos: ");
		for (Literal lit : c.getPosLits()) {
			System.out.print("(" + lit.funcName);
			System.out.print(": ");
			for (String arg : lit.arguments) System.out.print(arg + " ");
			System.out.print(") ");
		}
		System.out.println();
		
		System.out.print("Neg: ");
		for (Literal lit : c.getNegLits()) {
			System.out.print("(" + lit.funcName);
			System.out.print(": ");
			for (String arg : lit.arguments) System.out.print(arg + " ");
			System.out.print(") ");
		}
		System.out.println("\n");
	}
	
	private static Clause resolution(Clause c1, Clause c2) {
		List<Literal> posLits = new ArrayList<>();
		List<Literal> negLits = new ArrayList<>();
		
		Set<Integer> mergedPosIndices1 = new HashSet<>();
		Set<Integer> mergedNegIndices1 = new HashSet<>();
		Set<Integer> mergedPosIndices2 = new HashSet<>();
		Set<Integer> mergedNegIndices2 = new HashSet<>();
		
		for (int i = 0; i < c1.getPosSize(); i++) {
			if (mergedPosIndices1.contains(i)) continue;
			
			Literal l1 = c1.getPosLits().get(i);
			
			for (int j = 0; j < c2.getNegSize(); j++) {
				if (mergedNegIndices2.contains(j)) continue;
				
				Literal l2 = c2.getNegLits().get(j);
				
				if (!l1.funcName.equals(l2.funcName)) continue;
				if (Literal.isSame(l1.arguments, l2.arguments)) {
					// System.out.println("此处应该有掌声。");
					
					mergedPosIndices1.add(i);
					mergedNegIndices2.add(j);
					break;
				} else {
					// System.out.println("Unify");
					
					for (int litIdx = 0; litIdx < l1.arguments.size(); litIdx++) {
						String arg1 = l1.arguments.get(litIdx);
						String arg2 = l2.arguments.get(litIdx);
						
						if (!arg1.equals(arg2)) {
							if (!Character.isLowerCase(arg1.charAt(0)) && !Character.isLowerCase(arg2.charAt(0))) continue;
							if (Character.isLowerCase(arg1.charAt(0)) && !Character.isLowerCase(arg2.charAt(0))) return(resolution(Clause.unify(c1, arg1, arg2), c2));
							if (Character.isLowerCase(arg2.charAt(0)) && !Character.isLowerCase(arg1.charAt(0))) return(resolution(Clause.unify(c2, arg2, arg1), c1));
							return resolution(Clause.unify(c1, arg1, arg2), c2);
						}
					}
				}
			}
		}
		
		for (int i = 0; i < c1.getNegSize(); i++) {
			if (mergedNegIndices1.contains(i)) continue;
			
			Literal l1 = c1.getNegLits().get(i);
			
			for (int j = 0; j < c2.getPosSize(); j++) {
				if (mergedPosIndices2.contains(j)) continue;
				
				Literal l2 = c2.getPosLits().get(j);
				
				if (!l1.funcName.equals(l2.funcName)) continue;
				if (Literal.isSame(l1.arguments, l2.arguments)) {
					// System.out.println("此处应该有掌声。");
					
					mergedNegIndices1.add(i);
					mergedPosIndices2.add(j);
					break;
				} else {
					// System.out.println("Unify");
					
					for (int litIdx = 0; litIdx < l1.arguments.size(); litIdx++) {
						String arg1 = l1.arguments.get(litIdx);
						String arg2 = l2.arguments.get(litIdx);
						
						if (!arg1.equals(arg2)) {
							if (!Character.isLowerCase(arg1.charAt(0)) && !Character.isLowerCase(arg2.charAt(0))) continue;
							if (Character.isLowerCase(arg1.charAt(0)) && !Character.isLowerCase(arg2.charAt(0))) return(resolution(Clause.unify(c1, arg1, arg2), c2));
							if (Character.isLowerCase(arg2.charAt(0)) && !Character.isLowerCase(arg1.charAt(0))) return(resolution(Clause.unify(c2, arg2, arg1), c1));
							return resolution(Clause.unify(c1, arg1, arg2), c2);
						}
					}
				}
			}
		}
		
		for (int i = 0; i < c1.getPosSize(); i++) {
			if (mergedPosIndices1.contains(i)) continue;
			posLits.add(c1.getPosLits().get(i));
		}
		
		for (int i = 0; i < c1.getNegSize(); i++) {
			if (mergedNegIndices1.contains(i)) continue;
			negLits.add(c1.getNegLits().get(i));
		}
		
		for (int i = 0; i < c2.getPosSize(); i++) {
			if (mergedPosIndices2.contains(i)) continue;
			posLits.add(c2.getPosLits().get(i));
		}
		
		for (int i = 0; i < c2.getNegSize(); i++) {
			if (mergedNegIndices2.contains(i)) continue;
			negLits.add(c2.getNegLits().get(i));
		}
		
		return new Clause(posLits, negLits);
	}
	
	private static boolean hasRepeat(Clause c) {
		for (Clause c1 : clauses)
			if (!Clause.isSame(c, c1)) return false;
		
		return true;
	}
	
	//private static final String FILE_PATH = "/Users/tianshuchu/Documents/Study/ArtificialIntelligence/Program/prog2/TheoremProver/src/theorems4";
	//private static final int GOAL_CLAUSE_START_INDEX = 6;
}
