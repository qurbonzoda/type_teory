import exceptions.ParserException;
import lambdaTree.Abstraction;
import lambdaTree.Applicative;
import lambdaTree.LambdaExpression;
import lambdaTree.LambdaVariable;
import parsers.LambdaParser;
import termTree.Function;
import termTree.TermExpression;
import termTree.TermVariable;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.PrintWriter;
import java.rmi.RemoteException;
import java.util.*;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.stream.Collectors;

public class Homework2 {

    private static class Equals {

        public final TermExpression left;
        public final TermExpression right;

        private Equals(TermExpression left, TermExpression right) {
            this.left = left;
            this.right = right;
        }

        @Override
        public boolean equals(Object o) {
            if (this == o) return true;
            if (o == null || getClass() != o.getClass()) return false;

            Equals equals = (Equals) o;

            if (left != null ? !left.equals(equals.left) : equals.left != null) return false;
            return !(right != null ? !right.equals(equals.right) : equals.right != null);

        }

        @Override
        public int hashCode() {
            int result = left != null ? left.hashCode() : 0;
            result = 31 * result + (right != null ? right.hashCode() : 0);
            return result;
        }
    }


    private static final String VAR_NAME = "t";
    private static final String FUNC_NAME = "f";

    private static TermVariable getVariable(int n) {
        return new TermVariable(VAR_NAME + n);
    }

    private static TermExpression getArrow(TermVariable v1, TermVariable v2) {
        List<TermExpression> args = new ArrayList<>();
        args.add(v1);
        args.add(v2);
        return new Function(args, FUNC_NAME);
    }

    private static TermExpression getArrow(int n1, int n2) {
        return getArrow(getVariable(n1), getVariable(n2));
    }


    private static int makeEquations(LambdaExpression expression,
                                     List<Equals> system,
                                     AtomicInteger nextNumber,
                                     Map<LambdaVariable, Integer> counter,
                                     Map<LambdaVariable, Integer> context) {

        if (expression instanceof LambdaVariable) {
            if (counter.containsKey(expression)) {
                return counter.get(expression);
            }
            if (context.containsKey(expression)) {
                return context.get(expression);
            }
            int resNumber = nextNumber.getAndIncrement();
            context.put((LambdaVariable) expression, resNumber);
            return resNumber;
        } else if (expression instanceof Abstraction) {
            Abstraction it = (Abstraction) expression;
            LambdaVariable variable = (LambdaVariable) it.getVariable();
            LambdaExpression statement = it.getStatement();
            int oldNumber = counter.getOrDefault(variable, -1);
            int newNumber = nextNumber.getAndIncrement();
            counter.put(variable, newNumber);
            int stNumber = makeEquations(statement, system, nextNumber, counter, context);
            int resNumber = nextNumber.getAndIncrement();
            system.add(new Equals(getVariable(resNumber), getArrow(newNumber, stNumber)));
            counter.remove(variable);
            if (oldNumber != -1) {
                counter.put(variable, oldNumber);
            }
            return resNumber;
        } else if (expression instanceof Applicative) {
            Applicative it = (Applicative) expression;
            LambdaExpression left = it.getLeft();
            LambdaExpression right = it.getRight();
            int leftNumber = makeEquations(left, system, nextNumber, counter, context);
            int rightNumber = makeEquations(right, system, nextNumber, counter, context);
            int resNumber = nextNumber.getAndIncrement();
            system.add(new Equals(getVariable(leftNumber), getArrow(rightNumber, resNumber)));
            return resNumber;
        }
        throw new IllegalArgumentException("Unknown type");
    }

    private static List<Equals> getWithout(List<Equals> initial, Equals withoutWhat) {
        return initial.stream().filter(eq -> !eq.equals(withoutWhat)).collect(Collectors.toList());
    }

    private static Set<TermVariable> getFreeVariables(TermExpression expression) {
        HashSet<TermVariable> set = new HashSet<>();
        if (expression instanceof TermVariable) {
            set.add((TermVariable) expression);
        } else {
            Function function = (Function) expression;
            for (TermExpression var : function.getArgs()) {
                set.addAll(getFreeVariables(var));
            }
        }
        return set;
    }

    private static TermExpression substitute(TermExpression expression, TermVariable termVariable, TermExpression replacement) {
        if (expression instanceof TermVariable) {
            if (expression.equals(termVariable)) {
                return replacement;
            }
            return expression;
        } else {
            Function function = (Function) expression;
            List<TermExpression> newArgs = new ArrayList<>();
            for (TermExpression arg : function.getArgs()) {
                newArgs.add(substitute(arg, termVariable, replacement));
            }
            return new Function(newArgs, function.getName());
        }
    }

    private static List<Equals> substitute(List<Equals> system, TermVariable termVariable, TermExpression replacement) {
        List<Equals> result = new ArrayList<>();
        for (Equals eq : system) {
            TermExpression sLeft = substitute(eq.left, termVariable, replacement);
            TermExpression sRight = substitute(eq.right, termVariable, replacement);
            result.add(new Equals(sLeft, sRight));
        }
        return result;
    }

    private static class SystemException extends RemoteException {
        public SystemException(String s) {
            super(s);
        }
    }

    private static List<Equals> solveSystem(List<Equals> system) throws SystemException {
        repeat:
        while (true) {
            if (system.isEmpty()) break;

            for (Equals eq : system) {
                //1 rule
                if (eq.left.equals(eq.right)) {
                    system = getWithout(system, eq);
                    continue repeat;
                }

                TermExpression leftPart = eq.left;
                TermExpression rightPart = eq.right;

                if (leftPart instanceof Function && rightPart instanceof Function) {
                    Function leftF = (Function) leftPart;
                    Function rightF = (Function) rightPart;

                    //3 rule - conflict
                    if (!leftF.getName().equals(rightF.getName()) || leftF.getArgs().size() != rightF.getArgs().size()) {
                        throw new SystemException("Система неразрешима: " + leftF + " != " + rightF);
                    }

                    //2 rule - decompose
                    List<Equals> nextSystem = getWithout(system, eq);
                    List<TermExpression> lefts = leftF.getArgs();
                    List<TermExpression> rights = rightF.getArgs();

                    for (int i = 0; i < lefts.size(); i++) {
                        nextSystem.add(new Equals(lefts.get(i), rights.get(i)));
                    }

                    system = nextSystem;
                    continue repeat;
                }

                //4 rule (swap)
                if (leftPart instanceof Function && rightPart instanceof TermVariable) {
                    List<Equals> nextSystem = getWithout(system, eq);
                    nextSystem.add(new Equals(rightPart, leftPart));
                    system = nextSystem;
                    continue repeat;
                }

                //6 rule (check)
                if (leftPart instanceof TermVariable) {
                    if (getFreeVariables(rightPart).contains(leftPart)) {
                        throw new SystemException("Система неразрешима: переменная " + leftPart + " входит свободно в " + rightPart);
                    }

                    //5 rule (eliminate)
                    List<Equals> nextSystem = getWithout(system, eq);

                    boolean isInG = false;
                    for (Equals neq : nextSystem) {
                        if (getFreeVariables(neq.left).contains(leftPart)) {
                            isInG = true;
                            break;
                        }
                        if (getFreeVariables(neq.right).contains(leftPart)) {
                            isInG = true;
                            break;
                        }
                    }

                    if (isInG) {
                        nextSystem = substitute(nextSystem, (TermVariable) leftPart, rightPart);
                        nextSystem.add(new Equals(leftPart, rightPart));
                        system = nextSystem;
                        continue repeat;
                    }
                }

            }
            break;
        }
        return system;
    }


    private static String parseTermToType(TermExpression expression) {
        if (expression instanceof TermVariable) {
            return expression.toString();
        }
        Function function = (Function) expression;
        List<TermExpression> args = function.getArgs();
        if (args.size() != 2) {
            throw new IllegalArgumentException("Incorrect arguments size in term");
        }
        StringBuilder result = new StringBuilder();
        if (args.get(0) instanceof TermVariable) {
            result.append(((TermVariable) args.get(0)).getName());
        } else {
            result.append("(").append(parseTermToType(args.get(0))).append(")");
        }
        result.append("->");
        result.append(parseTermToType(args.get(1)));
        return result.toString();
    }

    public static void main(String[] args) {
        try (
                Scanner in = new Scanner(new File("input.txt"));
                PrintWriter out = new PrintWriter(new File("output.txt"))
        ) {
            String input = getInput(in);
            LambdaParser parser = new LambdaParser();
            LambdaExpression expression = parser.parse(input);

            List<Equals> system = new ArrayList<>();
            Map<LambdaVariable, Integer> context = new HashMap<>();
            int equationAnswer = makeEquations(expression, system, new AtomicInteger(1), new HashMap<>(), context);

            try {
                List<Equals> solution = solveSystem(system);

                Map<TermExpression, TermExpression> leftToRight = new HashMap<>();
                for (Equals eq : solution) {
                    leftToRight.put(eq.left, eq.right);
                }

                TermExpression answer = leftToRight.get(getVariable(equationAnswer));
                String resultingType;
                if (answer == null) {
                    resultingType = getVariable(equationAnswer).toString();
                } else {
                    resultingType = parseTermToType(answer);
                }

                out.println(resultingType);

                for (Map.Entry<LambdaVariable, Integer> entry : context.entrySet()) {
                    int index = entry.getValue();
                    TermExpression termExpression = leftToRight.get(getVariable(index));
                    String freeVarType = parseTermToType(termExpression);
                    out.println(entry.getKey() + ":" + freeVarType);
                }

            } catch (SystemException e) {
                out.println("Лямбда-выражение не имеет типа.");
            }

        } catch (FileNotFoundException | ParserException e) {
            e.printStackTrace();
        }
    }

    private static String getInput(Scanner in) {
        StringBuilder input = new StringBuilder();
        while (in.hasNextLine()) {
            input.append(in.nextLine());
        }
        return input.toString().trim();
    }
}
