import java.util.ArrayList;
import java.util.List;
import java.lang.StringBuilder;

public class Clause {

	private List<Literal> posLits;
	private List<Literal> negLits;

	public Clause() {
		this.posLits = new ArrayList<>();
		this.negLits = new ArrayList<>();
	}
	
	public Clause(List<Literal> pos, List<Literal> neg) {
		this.posLits = pos;
		this.negLits = neg;
	}
	
	public int getPosSize() {
		return posLits.size();
	}
	
	public int getNegSize() {
		return negLits.size();
	}
	
	public List<Literal> getPosLits() {
		return this.posLits;
	}
	
	public List<Literal> getNegLits() {
		return this.negLits;
	}
	
	public static boolean isSame(Clause c1, Clause c2) {
		if (c1.getPosSize() != c2.getPosSize() || c1.getNegSize() != c2.getNegSize()) return false;
		
		for (int i = 0; i < c1.getPosSize(); i++)
			if (!c1.getPosLits().get(i).funcName.equals(c2.getPosLits().get(i).funcName)
			 || !Literal.isSame(c1.getPosLits().get(i).arguments, c2.getPosLits().get(i).arguments)
			 || !c1.getNegLits().get(i).funcName.equals(c2.getNegLits().get(i).funcName)
			 || !Literal.isSame(c1.getNegLits().get(i).arguments, c2.getNegLits().get(i).arguments))
				return false;
			
		return true;
	}
	
	public static Clause unify(Clause c, String oldArg, String newArg) {
		System.out.println("oldArg: " + oldArg);
		System.out.println("newArg: " + newArg);
		
		List<Literal> pos = new ArrayList<>();
		List<Literal> neg = new ArrayList<>();
		
		for (Literal posLit : c.posLits) {
			Literal newPosLit = new Literal();
			newPosLit.funcName = posLit.funcName;
			for (String arg : posLit.arguments) {
				if (arg.equals(oldArg)) newPosLit.arguments.add(newArg);
				else newPosLit.arguments.add(arg);
			}
			pos.add(newPosLit);
		}
		
		for (Literal negLit : c.negLits) {
			Literal newNegLit = new Literal();
			newNegLit.funcName = negLit.funcName;
			for (String arg : negLit.arguments) {
				if (arg.equals(oldArg)) newNegLit.arguments.add(newArg);
				else newNegLit.arguments.add(arg);
			}
			neg.add(newNegLit);
		}
		
		Clause unified = new Clause(pos, neg);
		
		TheoremProver.printClause(unified);
		
		return unified;
	}

	public String toString() {
		StringBuilder sb = new StringBuilder();
		sb.append("((");
		for (Literal arg : posLits) {
			sb.append(arg.toString());
			sb.append(" ");
		}
		sb.append(")  (");
		for (Literal arg : negLits) {
			sb.append(arg.toString());
			sb.append(" ");
		}
		sb.append("))");
		return sb.toString();
	}
}
