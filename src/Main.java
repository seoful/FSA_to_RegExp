import java.io.*;
import java.util.*;
import java.util.regex.Pattern;

public class Main {
    public static void main(String[] args) {
        try {
            PrintWriter writer = new PrintWriter(new FileWriter("output.txt"));
            try {
                FSA fsa = new FSA();
                Scanner scanner = new Scanner(new FileInputStream("input.txt"));

                String line = scanner.nextLine();
                if (!Pattern.compile("states=\\[(\\w+,)*\\w+]").matcher(line).matches()) {
                    throw new InputFormatException();
                }
                String[] states = line.substring(8, line.length() - 1).split(",");
                for (String state : states) {
                    fsa.addState(state);
                }

                line = scanner.nextLine();
                if (!Pattern.compile("alpha=\\[(\\w+,)*\\w+]").matcher(line).matches()) {
                    throw new InputFormatException();
                }
                String[] alphabet = line.substring(7, line.length() - 1).split(",");
                for (String symbol : alphabet) {
                    fsa.addSymbolToAlphabet(symbol);
                }


                line = scanner.nextLine();
                if (!Pattern.compile("initial=\\[\\w*]").matcher(line).matches()) {
                    throw new InputFormatException();
                }
                fsa.setInitialState(line.substring(9, line.length() - 1));


                line = scanner.nextLine();
                if (!Pattern.compile("accepting=\\[(((\\w+,)*\\w+)|((\\w+)?))]").matcher(line).matches()) {
                    throw new InputFormatException();
                }

                String[] acceptingStates = line.substring(11, line.length() - 1).split(",");
                for (String state : acceptingStates) {
                    if (!state.equals(""))
                        fsa.addAcceptingState(state);
                }


                line = scanner.nextLine();
                if (!Pattern.compile("trans=\\[((\\w+>\\w+>\\w+)*,)*(\\w+>\\w+>\\w+)?]").matcher(line).matches())
                    throw new InputFormatException();

                String[] transitions = line.substring(7, line.length() - 1).split(",");
                for (String transition : transitions) {
                    if (!transition.equals("")) {
                        String[] fields = transition.split(">");
                        fsa.addTransition(fields[0], fields[2], fields[1]);
                    }
                }

                writer.print(fsa.toRegExp() + "\n");

            } catch (FileNotFoundException e) {
                e.printStackTrace();
            } catch (InputFormatException e) {
                writer.print("Error:\nE0: Input file is malformed");
            } catch (FSA.NoSuchStateException e) {
                writer.print("Error:\nE1: A state '" + e.state + "' is not in the set of states");
            } catch (FSA.NoSuchSymbolException e) {
                writer.print("Error:\nE3: A transition '" + e.symbol + "' is not represented in the alphabet");
            } catch (FSA.FSAIsNonDeterministic fsaIsNonDeterministic) {
                writer.print("Error:\nE5: FSA is nondeterministic");
            } catch (FSA.NoInitialStateException e) {
                writer.print("Error:\nE4: Initial state is not defined");
            } catch (FSA.FSAIsDisjointException e) {
                writer.print("Error:\nE2: Some states are disjoint");
            }
            writer.close();
        } catch (IOException e) {
            e.printStackTrace();
        }

    }
}

class InputFormatException extends Exception {
    public InputFormatException() {
    }
}

class FSA {
    private final GraphADT<String, String> graph = new AdjacencyMatrixGraph<>();
    private final Set<String> states = new HashSet<>();
    private final Set<String> alphabet = new HashSet<>();
    private String initialState;
    private final ArrayList<String> acceptingStates = new ArrayList<>();
    static String eps = "eps";
    static String emptySet = "{}";

    public FSA() {
    }

    public void addState(String state) {
        states.add(state);
        graph.addVertex(state);
    }

    static class NoSuchStateException extends Exception {
        String state;

        public NoSuchStateException(String state) {
            this.state = state;
        }
    }

    static class NoSuchSymbolException extends Exception {
        String symbol;

        public NoSuchSymbolException(String symbol) {
            this.symbol = symbol;
        }
    }

    public void setInitialState(String state) throws NoSuchStateException {
        if (states.contains(state))
            initialState = state;
        else
            throw new NoSuchStateException(state);
    }

    public void addAcceptingState(String state) throws NoSuchStateException {
        if (states.contains(state))
            acceptingStates.add(state);
        else
            throw new NoSuchStateException(state);
    }

    public void addSymbolToAlphabet(String symbol) {
        alphabet.add(symbol);
    }

    public void addTransition(String from, String to, String symbol) throws NoSuchStateException, NoSuchSymbolException {
        if (!states.contains(from))
            throw new NoSuchStateException(from);
        if (!states.contains(to))
            throw new NoSuchStateException(to);
        if (!checkSymbol(symbol))
            throw new NoSuchSymbolException(symbol);
        graph.addEdge(graph.findVertex(from), graph.findVertex(to), symbol);
    }

    private boolean checkSymbol(String symbol) {
        if (symbol.equals(eps))
            return true;
        return alphabet.contains(symbol);
    }

    static class NoInitialStateException extends Exception {
        public NoInitialStateException() {
        }
    }

    static class FSAIsDisjointException extends Exception {
        public FSAIsDisjointException() {
        }
    }

    static class FSAIsNonDeterministic extends Exception {
        public FSAIsNonDeterministic() {
        }
    }

    private boolean isJoint() {
        return graph.isJoint(graph.findVertex(initialState));
    }

    private boolean isDeterministic() {
        for (Vertex<String> state : graph.getVertices()) {
            List<Edge<String, String>> edges = graph.edgesFrom(state);
            List<String> transitions = new ArrayList<>();
            for (Edge<String, String> edge : edges) {
                transitions.addAll(edge.getValues());
            }
            for (int i = 0; i < transitions.size() - 1; i++) {
                for (int j = i + 1; j < transitions.size(); j++) {
                    if (transitions.get(i).equals(transitions.get(j)))
                        return false;
                    if (transitions.get(i).equals(eps))
                        return false;
                }
            }
        }
        return true;
    }

    public String toRegExp() throws NoInitialStateException, FSAIsDisjointException, FSAIsNonDeterministic {
        if (initialState == null)
            throw new NoInitialStateException();
        if (!isJoint()) {
            throw new FSAIsDisjointException();
        }
        if (!isDeterministic())
            throw new FSAIsNonDeterministic();
        if (acceptingStates.isEmpty())
            return emptySet;
        LinkedList<String> statesList = new LinkedList<>(states);
        int fromIndex = findString(statesList, initialState);
        String frommm = statesList.remove(fromIndex);
        statesList.add(0,frommm);
        StringBuilder builder = new StringBuilder();
        for (String finalState : acceptingStates) {
            int finalIndex = findString(statesList, finalState);
            builder.append(calculateF(statesList, 0, finalIndex, states.size() - 1)).append("|");
        }
        return builder.substring(0, builder.length() - 1);
    }

    private int findString(List<String> list, String str) {
        for (int i = 0; i < list.size(); i++) {
            if (list.get(i).equals(str))
                return i;
        }
        return -1;
    }


    private String calculateF(List<String> statesList, int i, int j, int k) {
        if (k == -1) {
            Edge<String, String> transitions = graph.findEdge(graph.findVertex(statesList.get(i)), graph.findVertex(statesList.get(j)));
            String str;
            StringBuilder builder = new StringBuilder();
            if (i == j) {
                if (transitions == null)
                    return eps;
                for (String symbol : transitions.getValues()) {
                    builder.append(symbol).append("|");
                }
                str = builder.substring(0, builder.length() - 1);
                return str + "|" + eps;
            } else {
                if (transitions == null)
                    return emptySet;
                for (String symbol : transitions.getValues()) {
                    builder.append(symbol).append("|");
                }
                return builder.substring(0, builder.length() - 1);
            }
        }
        return "(" + calculateF(statesList, i, k, k - 1) + ")(" + calculateF(statesList, k, k, k - 1) + ")*(" +
                calculateF(statesList, k, j, k - 1) + ")|(" + calculateF(statesList, i, j, k - 1) + ")";
    }


}


class Vertex<V> {
    private final V value;
    private int index;

    public Vertex(V value, int index) {
        this.value = value;
        this.index = index;
    }

    public int getIndex() {
        return index;
    }

    public void setIndex(int index) {
        this.index = index;
    }

    public V getValue() {
        return value;
    }

    @Override
    public String toString() {
        return "Vertex{" +
                "value=" + value +
                '}';
    }
}

class Edge<E extends Comparable<E>, V> {
    private final List<E> values;
    private Vertex<V> from, to;

    public Edge(E value, Vertex<V> from, Vertex<V> to) {
        this.values = new ArrayList<>();
        values.add(value);
        this.from = from;
        this.to = to;
    }

    public List<E> getValues() {
        return values;
    }

    public void addValue(E value) {
        values.add(value);
    }

    public Vertex<V> getFrom() {
        return from;
    }

    public Vertex<V> getTo() {
        return to;
    }

    public Edge<E, V> reverse() {
        Vertex<V> temp = from;
        from = to;
        to = temp;
        return this;
    }

    @Override
    public String toString() {
        return from.getValue() + "->" + to.getValue();
    }
}

interface GraphADT<V, E extends Comparable<E>> {
    /**
     * add a vertex with value value to the graph
     * and return reference to the created vertex object
     */
    Vertex<V> addVertex(V value);

    /**
     * remove a vertex, provided a reference to a
     * vertex object
     */
    void removeVertex(Vertex<V> v);

    List<Vertex<V>> getVertices();

    /**
     * add a directed edge between
     * from and to vertices with weight weight, return reference to the
     * created edge object
     */
    Edge<E, V> addEdge(Vertex<V> from, Vertex<V> to, E weight);

    /**
     * remove an edge, given a reference to an edge
     * object
     */
    void removeEdge(Edge<E, V> e);

    /**
     * return a collection or edge objects that are going
     * from vertex v
     */
    List<Edge<E, V>> edgesFrom(Vertex<V> v);

    /**
     * return a collection or edge objects that are going
     * into vertex v
     */
    List<Edge<E, V>> edgesTo(Vertex<V> v);

    /**
     * find any vertex with the specified value
     */
    Vertex<V> findVertex(V value);

    /**
     * find any edge with specified values in the source and target vertices
     */
    Edge<E, V> findEdge(V fromValue, V toValue);

    /**
     * find any edge with specified values in the source and target vertices
     */
    Edge<E, V> findEdge(Vertex<V> from, Vertex<V> to);

    /**
     * determine whether there exists a directed edge
     * from v to u
     */
    boolean hasEdge(Vertex<V> from, Vertex<V> to);

    /**
     * reverse all edges in a graph
     */
    void transpose();

    /**
     * Finds any cycle in the graph
     *
     * @return list of vertices of the cycle. If graph is acyclic - returns null
     */
    List<Vertex<V>> isAcylcic();


    boolean isJoint(Vertex<V> from);
}

class AdjacencyMatrixGraph<V, E extends Comparable<E>> implements GraphADT<V, E> {
    private final List<Vertex<V>> vertices;
    private final List<List<Edge<E, V>>> matrix;
//    private final HashMap<Vertex<V>, Integer> vertexMap;

    public AdjacencyMatrixGraph() {
        matrix = new ArrayList<>();
//        vertexMap = new HashMap<>();
        vertices = new LinkedList<>();
    }

    @Override
    public Vertex<V> addVertex(V value) {
        Vertex<V> vertex = new Vertex<>(value, verticesNumber());
        vertices.add(vertex);
        for (List<Edge<E, V>> edgeList : matrix) {
            edgeList.add(null);
        }
        List<Edge<E, V>> lastRow = new ArrayList<>(verticesNumber());
        for (int i = 0; i < verticesNumber(); i++) {
            lastRow.add(null);
        }
        matrix.add(lastRow);
        return vertex;
    }

    @Override
    public void removeVertex(Vertex<V> v) {
        vertices.remove(v.getIndex());
        for (int i = v.getIndex(); i < verticesNumber(); i++) {
            vertices.get(i).setIndex(i);
        }
        matrix.remove(v.getIndex());
        for (int i = 0; i < verticesNumber(); i++) {
            matrix.get(i).remove(v.getIndex());
        }
    }

    @Override
    public List<Vertex<V>> getVertices() {
        return vertices;
    }

    @Override
    public Edge<E, V> addEdge(Vertex<V> from, Vertex<V> to, E weight) {
        Edge<E, V> edgeInArray = matrix.get(from.getIndex()).get(to.getIndex());
        if (edgeInArray == null) {
            Edge<E, V> edge = new Edge<>(weight, from, to);
            matrix.get(from.getIndex()).set(to.getIndex(), edge);
            return edge;
        } else {
            edgeInArray.addValue(weight);
            return edgeInArray;
        }
    }

    @Override
    public void removeEdge(Edge<E, V> e) {
        matrix.get(e.getFrom().getIndex()).set(e.getTo().getIndex(), null);
    }

    @Override
    public List<Edge<E, V>> edgesFrom(Vertex<V> v) {
        ArrayList<Edge<E, V>> edges = new ArrayList<Edge<E, V>>();
        for (int i = 0; i < verticesNumber(); i++) {
            Edge<E, V> edge = matrix.get(v.getIndex()).get(i);
            if (edge != null)
                edges.add(edge);
        }
        return edges;
    }

    @Override
    public List<Edge<E, V>> edgesTo(Vertex<V> v) {
        List<Edge<E, V>> edgesList = new ArrayList<>();
        for (int i = 0; i < verticesNumber(); i++) {
            Edge<E, V> edge = matrix.get(i).get(v.getIndex());
            if (edge != null)
                edgesList.add(edge);
        }
        return edgesList;
    }

    @Override
    public Vertex<V> findVertex(V value) {
        for (Vertex<V> v : vertices) {
            if (v.getValue().equals(value))
                return v;
        }
        return null;
    }

    @Override
    public Edge<E, V> findEdge(V fromValue, V toValue) {
        for (int i = 0; i < verticesNumber(); i++) {
            for (int j = 0; j < verticesNumber(); j++) {
                Edge<E, V> edge = matrix.get(i).get(j);
                if (edge != null) {
                    V iValue = edge.getFrom().getValue();
                    V jValue = edge.getTo().getValue();
                    if (fromValue.equals(iValue) && toValue.equals(jValue))
                        return edge;
                }
            }
        }
        return null;
    }

    @Override
    public Edge<E, V> findEdge(Vertex<V> from, Vertex<V> to) {
        int fromIndex = 0, toIndex = 0;
        for (int i = 0; i < verticesNumber(); i++) {
            if (vertices.get(i) == from)
                fromIndex = i;
            if (vertices.get(i) == to)
                toIndex = i;
        }
        return matrix.get(fromIndex).get(toIndex);
    }

    @Override
    public boolean hasEdge(Vertex<V> from, Vertex<V> to) {
        return matrix.get(from.getIndex()).get(to.getIndex()) != null;
    }

    @Override
    public void transpose() {
        for (int i = 1; i < verticesNumber(); i++) {
            for (int j = 0; j < i; j++) {
                Edge<E, V> edge1 = matrix.get(i).get(j);
                Edge<E, V> edge2 = matrix.get(j).get(i);
                matrix.get(i).set(j, edge2 == null ? null : edge2.reverse());
                matrix.get(j).set(i, edge1 == null ? null : edge1.reverse());
            }
        }
    }

    private enum Color {WHITE, GREY, BLACK}

    @Override
    public List<Vertex<V>> isAcylcic() {
        Color[] colors = new Color[verticesNumber()];
        Arrays.fill(colors, Color.WHITE);
        for (int i = 0; i < verticesNumber(); i++) {
            List<Vertex<V>> cycle;
            if (colors[i] == Color.WHITE) {
                cycle = traverseAndFindCycle(vertices.get(i), colors);
                if (cycle != null) {
                    ArrayList<Vertex<V>> reversedCycle = new ArrayList<Vertex<V>>();
                    for (int m = 1; m < cycle.size(); m++)
                        reversedCycle.add(cycle.get(cycle.size() - m));
                    return reversedCycle;
                }
            }
        }
        return null;
    }

    @Override
    public boolean isJoint(Vertex<V> from) {
        boolean[] visited = new boolean[verticesNumber()];
        Arrays.fill(visited, false);
        visited[from.getIndex()] = true;
        Queue<Vertex<V>> queue = new LinkedList<>();
        queue.add(from);
        while (!queue.isEmpty()) {
            Vertex<V> vertex = queue.poll();
            for (Edge<E, V> edge : edgesFrom(vertex)) {
                Vertex<V> to = edge.getTo();
                if (!visited[to.getIndex()]) {
                    visited[to.getIndex()] = true;
                    queue.add(to);
                }
            }
        }
        for (boolean v : visited) {
            if (!v)
                return false;
        }
        return true;
    }

    private List<Vertex<V>> traverseAndFindCycle(Vertex<V> vertex, Color[] colors) {
        colors[vertex.getIndex()] = Color.GREY;
        List<Edge<E, V>> edges = edgesFrom(vertex);
        for (Edge<E, V> edge : edges) {
            if (colors[edge.getTo().getIndex()] == Color.GREY) {
                ArrayList<Vertex<V>> list = new ArrayList<Vertex<V>>();
                list.add(edge.getTo());
                list.add(vertex);
                return list;
            }
        }
        for (Edge<E, V> edge : edges) {
            List<Vertex<V>> cycle = traverseAndFindCycle(edge.getTo(), colors);
            if (cycle != null) {
                if (cycle.get(0) != cycle.get(cycle.size() - 1))
                    cycle.add(vertex);

                return cycle;
            }
        }
        colors[vertex.getIndex()] = Color.BLACK;
        return null;
    }

    private int verticesNumber() {
        return vertices.size();
    }

    @Override
    public String toString() {
        StringBuilder builder = new StringBuilder();
        for (List<Edge<E, V>> a : matrix) {
            for (Edge<E, V> b : a) {
                if (b == null)
                    builder.append(" null ");
                else
                    builder.append(" ").append(b).append(" ");
            }
            builder.append("\n");
        }
        return builder.toString();
    }
}