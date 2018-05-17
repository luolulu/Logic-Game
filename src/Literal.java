import java.util.ArrayList;
import java.util.List;
import java.lang.StringBuilder;

public class Literal {
	public String funcName;
	public List<String> arguments;

	public Literal() {
		this.funcName = new String();
		this.arguments = new ArrayList<>();
	}
	
	public Literal(String[] arr) {
		this.funcName = arr[0];
		this.arguments = new ArrayList<>();
		for (int i = 1; i < arr.length; i++) this.arguments.add(arr[i]);
	}
	
	public static boolean isSame(List<String> args1, List<String> args2) {
		if (args1.size() != args2.size()) return false;

		for (int i = 0; i < args1.size(); i++)
			if (!args1.get(i).equals(args2.get(i))) return false;
		
		return true;
	}
	
	public String toString() {
		StringBuilder sb = new StringBuilder();
		sb.append("(" + funcName + ":");
		for (String arg : arguments) {
			sb.append(" ");
			sb.append(arg);
		}
		sb.append(")");
		return sb.toString();
	}
}