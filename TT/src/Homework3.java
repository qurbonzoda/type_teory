import exceptions.ParserException;
import hmType.ArrowType;
import hmType.ForallType;
import hmType.HMType;
import hmType.VariableType;
import lambdaTree.*;
import parsers.LambdaParser;
import sun.jvm.hotspot.utilities.AssertionFailure;
import termTree.AlgebraicFunction;
import termTree.TermExpression;
import termTree.TermVariable;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.PrintWriter;
import java.util.*;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.function.Function;

public class Homework3 {

    private final static AtomicInteger nextNumber = new AtomicInteger(1);

    private static class WResult {
        final Map<VariableType, HMType> S;
        final HMType tau;


        private WResult(Map<VariableType, HMType> s, HMType tau) {
            this.S = s;
            this.tau = tau;
        }
    }

    private static final String VAR_NAME = "t";

    private static VariableType getVariable(int n) {
        return new VariableType(VAR_NAME + n);
    }

    private static Set<LambdaVariable> getFreeVariables(LambdaExpression expression) {
        HashSet<LambdaVariable> bound = new HashSet<>();
        return getFreeVariables(expression, bound);
    }

    private static Set<LambdaVariable> getFreeVariables(LambdaExpression e, Set<LambdaVariable> bound) {
        if (e instanceof LambdaVariable) {
            HashSet<LambdaVariable> res = new HashSet<>();
            if (!bound.contains(e)) {
                res.add((LambdaVariable) e);
            }
            return res;
        }
        if (e instanceof Applicative) {
            LambdaExpression e1 = ((Applicative) e).getLeft();
            LambdaExpression e2 = ((Applicative) e).getRight();
            Set<LambdaVariable> result = new HashSet<>(getFreeVariables(e1, bound));
            result.addAll(getFreeVariables(e2, bound));
            return result;
        }
        if (e instanceof Abstraction) {
            LambdaExpression variable = ((Abstraction) e).getVariable();
            LambdaExpression statement = ((Abstraction) e).getStatement();

            Set<LambdaVariable> newBound = new HashSet<>(bound);
            newBound.add((LambdaVariable) variable);
            return getFreeVariables(statement, newBound);
        }
        if (e instanceof LetExpression) {
            LambdaExpression variable = ((LetExpression) e).variable;
            LambdaExpression variableExpr = ((LetExpression) e).variableExpr;
            LambdaExpression inExpr = ((LetExpression) e).inExpr;

            Set<LambdaVariable> result = new HashSet<>(getFreeVariables(variableExpr, bound));
            Set<LambdaVariable> newBound = new HashSet<>(bound);
            newBound.add((LambdaVariable) variable);
            result.addAll(getFreeVariables(inExpr, newBound));
            return result;
        }

        throw new IllegalArgumentException("Unknown type");
    }


    private static Set<VariableType> getTypeFreeVariables(HMType tau) {
        return getTypeFreeVariables(tau, new HashSet<>());
    }


    private static Set<VariableType> getTypeFreeVariables(HMType tau, Set<VariableType> bound) {
        if (tau instanceof VariableType) {
            HashSet<VariableType> res = new HashSet<>();
            if (!bound.contains(tau)) {
                res.add((VariableType) tau);
            }
            return res;
        }
        if (tau instanceof ArrowType) {
            Set<VariableType> res = getTypeFreeVariables(((ArrowType) tau).left, bound);
            res.addAll(getTypeFreeVariables(((ArrowType) tau).right, bound));
            return res;
        }
        if (tau instanceof ForallType) {
            VariableType variable = ((ForallType) tau).variable;
            HMType statement = ((ForallType) tau).statement;
            Set<VariableType> newBound = new HashSet<>(bound);
            newBound.add(variable);
            return getTypeFreeVariables(statement, newBound);
        }

        throw new IllegalArgumentException("Unknown type");
    }

    private static HMType substitutePrecedingForalls(HMType tau) {
        if (tau instanceof ForallType) {
            VariableType variable = ((ForallType) tau).variable;
            HMType statement = ((ForallType) tau).statement;

            HMType resultType = substitute(variable, getVariable(nextNumber.getAndIncrement()), statement);
            return substitutePrecedingForalls(resultType);
        }
        return tau;
    }

    private static Map<LambdaVariable, HMType> mapTypes(Map<LambdaVariable, HMType> context,
                                                        Map<VariableType, HMType> S) {
        Map<LambdaVariable, HMType> newContext = new HashMap<>();
        for (Map.Entry<LambdaVariable, HMType> entry : context.entrySet()) {
            newContext.put(entry.getKey(), mapType(entry.getValue(), S));
        }
        return newContext;
    }

    private static HMType mapType(HMType type, Map<VariableType, HMType> S) {
        HMType res = type;
        for (Map.Entry<VariableType, HMType> entry : S.entrySet()) {
            res = substitute(entry.getKey(), entry.getValue(), res);
        }
        return res;
    }

    private static HMType substitute(VariableType var, HMType subst, HMType tau) {
        return substitute(var, subst, tau, new HashSet<>());
    }

    private static HMType substitute(VariableType var, HMType subst, HMType tau, Set<VariableType> bound) {
        if (tau instanceof VariableType) {
            if (tau.equals(var) && !bound.contains(tau)) {
                return subst;
            }
            return tau;
        }
        if (tau instanceof ArrowType) {
            HMType left = substitute(var, subst, ((ArrowType) tau).left, bound);
            HMType right = substitute(var, subst, ((ArrowType) tau).right, bound);
            return new ArrowType(left, right);
        }
        if (tau instanceof ForallType) {
            VariableType variable = ((ForallType) tau).variable;
            HMType statement = ((ForallType) tau).statement;
            Set<VariableType> newBound = new HashSet<>(bound);
            newBound.add(variable);
            HMType newStatement = substitute(var, subst, statement, newBound);
            return new ForallType(variable, newStatement);
        }

        throw new IllegalArgumentException("Unknown type");
    }

    private static Map<VariableType, HMType> substitutionComposition(Map<VariableType, HMType> S1,
                                                                     Map<VariableType, HMType> S2) {
        Map<VariableType, HMType> composition = new HashMap<>();
        for (Map.Entry<VariableType, HMType> entry : S2.entrySet()) {
            composition.put(entry.getKey(), mapType(entry.getValue(), S1));
        }
        for (Map.Entry<VariableType, HMType> entry : S1.entrySet()) {
            if (composition.containsKey(entry.getKey())) {
                throw new AssertionFailure("S1 unexpectedly contains S2 key types");
            }
            composition.putIfAbsent(entry.getKey(), entry.getValue());
        }
        return composition;
    }

    private static Set<VariableType> contextFreeVars(Map<LambdaVariable, HMType> context) {
        Set<VariableType> contextFreeVariables = new HashSet<>();
        for (Map.Entry<LambdaVariable, HMType> entry : context.entrySet()) {
            contextFreeVariables.addAll(getTypeFreeVariables(entry.getValue()));
        }
        return contextFreeVariables;
    }

    private static HMType zamykanie(Map<LambdaVariable, HMType> context, HMType tau) {
        Set<VariableType> tauFreeVariables = getTypeFreeVariables(tau);
        tauFreeVariables.removeAll(contextFreeVars(context));
        HMType res = tau;
        for (VariableType freeVariable : tauFreeVariables) {
            res = new ForallType(freeVariable, res);
        }
        return res;
    }

    private static TermExpression hmToAlg(HMType tau) {
        if (tau instanceof VariableType) {
            return new TermVariable(((VariableType) tau).name);
        }
        if (tau instanceof ArrowType) {
            TermExpression leftTerm = hmToAlg(((ArrowType) tau).left);
            TermExpression rightTerm = hmToAlg(((ArrowType) tau).right);
            return new AlgebraicFunction(Arrays.asList(leftTerm, rightTerm), "arrow");
        }
        if (tau instanceof ForallType) {
            TermExpression variableTerm = hmToAlg(((ForallType) tau).variable);
            TermExpression statementTerm = hmToAlg(((ForallType) tau).statement);
            return new AlgebraicFunction(Arrays.asList(variableTerm, statementTerm), "forall");
        }

        throw new IllegalArgumentException("Unknown type");
    }

    private static HMType algToHM(TermExpression term) {
        if (term instanceof TermVariable) {
            return new VariableType(((TermVariable)term).getName());
        }
        if (term instanceof AlgebraicFunction) {
            String name = ((AlgebraicFunction) term).getName();
            List<TermExpression> args = ((AlgebraicFunction) term).getArgs();
            if (name.equals("arrow")) {
                return new ArrowType(algToHM(args.get(0)), algToHM(args.get(1)));
            }
            if (name.equals("forall")) {
                return new ForallType((VariableType) algToHM(args.get(0)), algToHM(args.get(1)));
            }
            throw new IllegalArgumentException("Unknown type");
        }

        throw new IllegalArgumentException("Unknown type");
    }

    private static Map<VariableType, HMType> unificate(HMType t1, HMType t2) throws Exception {
        TermExpression term1 = hmToAlg(t1);
        TermExpression term2 = hmToAlg(t2);
        List<Homework2.Equals> system = new ArrayList<>(Arrays.asList(new Homework2.Equals(term1, term2)));
        List<Homework2.Equals> solution = Homework2.solveSystem(system);
        Map<VariableType, HMType> res = new HashMap<>();
        for (Homework2.Equals equals : solution) {
            res.put((VariableType) algToHM(equals.left), algToHM(equals.right));
        }
        return res;
    }

    private static WResult WAlgorithm(Map<LambdaVariable, HMType> context,
                                      LambdaExpression e) throws Exception {
        if (e instanceof LambdaVariable) {
            HMType eType = context.get(e);
            return new WResult(new HashMap<>(), substitutePrecedingForalls(eType));
        }
        if (e instanceof Applicative) {
            LambdaExpression e1 = ((Applicative) e).getLeft();
            LambdaExpression e2 = ((Applicative) e).getRight();
            WResult res1 = WAlgorithm(context, e1);
            WResult res2 = WAlgorithm(mapTypes(context, res1.S), e2);

            VariableType beta = getVariable(nextNumber.getAndIncrement());
            Map<VariableType, HMType> V = unificate(mapType(res1.tau, res2.S), new ArrowType(res2.tau, beta));

            Map<VariableType, HMType> S = substitutionComposition(V, substitutionComposition(res1.S, res2.S));

            HMType newBeta = mapType(beta, S);
            Set<VariableType> newBetaFreeVars = getTypeFreeVariables(newBeta);
            Map<VariableType, HMType> newS = new HashMap<>();
            Set contextFreeVariables = contextFreeVars(context);
            for (Map.Entry<VariableType, HMType> entry : S.entrySet()) {
                if (newBetaFreeVars.contains(entry.getKey()) || contextFreeVariables.contains(entry.getKey())) {
                    newS.put(entry.getKey(), entry.getValue());
                }
            }

            return new WResult(newS, newBeta);
//            return new WResult(S, newBeta);
        }
        if (e instanceof Abstraction) {
            LambdaVariable variable = (LambdaVariable) ((Abstraction) e).getVariable();
            LambdaExpression statement = ((Abstraction) e).getStatement();

            VariableType beta = getVariable(nextNumber.getAndIncrement());

            Map<LambdaVariable, HMType> newContext = new HashMap<>(context);
            newContext.put(variable, beta);
            WResult res1 = WAlgorithm(newContext, statement);

            HMType tau = new ArrowType(mapType(beta, res1.S), res1.tau);
            return new WResult(res1.S, tau);
        }
        if (e instanceof LetExpression) {
            LambdaVariable variable = (LambdaVariable) ((LetExpression) e).variable;
            LambdaExpression variableExpr = ((LetExpression) e).variableExpr;
            LambdaExpression inExpr = ((LetExpression) e).inExpr;
            WResult res1 = WAlgorithm(context, variableExpr);

            Map<LambdaVariable, HMType> newContext = mapTypes(context, res1.S);
            newContext.put(variable, mapType(zamykanie(context, res1.tau), res1.S));
            WResult res2 = WAlgorithm(newContext, inExpr);

            Map<VariableType, HMType> S = substitutionComposition(res2.S, res1.S);
            return new WResult(S, res2.tau);
        }

        throw new IllegalArgumentException("Unknown type");
    }

    public static void main(String[] args) {
        try (
                Scanner in = new Scanner(new File("input.txt"));
                PrintWriter out = new PrintWriter(new File("output.txt"))
        ) {
            String input = getInput(in);
            LambdaParser parser = new LambdaParser();
            LambdaExpression expression = parser.parse(input);

//            out.println(expression.toString());

            Set<LambdaVariable> freeVars = getFreeVariables(expression);
            HashMap<LambdaVariable, HMType> context = new HashMap<>();

            for (LambdaVariable variable : freeVars) {
                context.put(variable, getVariable(nextNumber.getAndIncrement()));
            }

//            for (Map.Entry entry : context.entrySet()) {
//                out.println(entry.getKey() + ":" + entry.getValue());
//            }

            try {
                WResult res = WAlgorithm(context, expression);
                out.println(res.tau);
                for (Map.Entry entry : res.S.entrySet()) {
                    out.println(entry.getKey() + ":" + entry.getValue());
                }
            } catch (Exception e) {
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
