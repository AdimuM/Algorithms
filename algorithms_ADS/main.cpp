#include <bits/stdc++.h>
using namespace std;
# define INF 0x3f3f3f3f

///*Implementation of Kruskal's algorithm for MST*/
class DSU {
    int* parent;
    int* rank;

public:
    DSU(int n)
    {
        parent = new int[n];
        rank = new int[n];

        for (int i = 0; i < n; i++) {
            parent[i] = -1;
            rank[i] = 1;
        }
    }

    // Find function
    int find(int i)
    {
        if (parent[i] == -1)
            return i;

        return parent[i] = find(parent[i]);
    }

    // Union function
    void unite(int x, int y)
    {
        int s1 = find(x);
        int s2 = find(y);

        if (s1 != s2) {
            if (rank[s1] < rank[s2]) {
                parent[s1] = s2;
            }
            else if (rank[s1] > rank[s2]) {
                parent[s2] = s1;
            }
            else {
                parent[s2] = s1;
                rank[s1] += 1;
            }
        }
    }
};

class Graph_1 {
    vector<vector<int> > edgelist;
    int V;

public:
    Graph_1(int V) { this->V = V; }

    // Function to add edge in a graph
    void addEdge(int x, int y, int w)
    {
        edgelist.push_back({ w, x, y });
    }

    void kruskals_mst()
    {
        // Sort all edges
        sort(edgelist.begin(), edgelist.end());

        // Initialize the DSU
        DSU s(V);
        int ans = 0;
        cout << "Following are the edges in the "
                "constructed MST"
             << endl;
        for (auto edge : edgelist) {
            int w = edge[0];
            int x = edge[1];
            int y = edge[2];

            // Take this edge in MST if it does not forms a cycle
            if (s.find(x) != s.find(y)) {
                s.unite(x, y);
                ans += w;
                cout << x << " -- " << y << " == " << w
                     << endl;
            }
        }
        cout << "Minimum Cost Spanning Tree: " << ans<<"\n\n";
    }
};


///* Prim's algorithm for MST*/
// Number of vertices in the graph
#define V0 4

// A utility function to find the vertex with
// minimum key value, from the set of vertices
// not yet included in MST
int minKey(int key[], bool mstSet[])
{
    // Initialize min value
    int min = INT_MAX, min_index;

    for (int v = 0; v < V0; v++)
        if (mstSet[v] == false && key[v] < min)
            min = key[v], min_index = v;

    return min_index;
}

// A utility function to print the
// constructed MST stored in parent[]
int printMST(int parent[], int graph[V0][V0])
{
    printf("Edge \tWeight\n");
    for (int i = 1; i < V0; i++)
        printf("%d - %d \t%d \n", parent[i], i,
               graph[i][parent[i]]);
}

// Function to construct and print MST for
// a graph represented using adjacency
// matrix representation
void primMST(int graph1[V0][V0])
{
    // Array to store constructed MST
    int parent[V0];
    // Key values used to pick minimum weight edge in cut
    int key[V0];
    // To represent set of vertices included in MST
    bool mstSet[V0];

    // Initialize all keys as INFINITE
    for (int i = 0; i < V0; i++)
        key[i] = INT_MAX, mstSet[i] = false;

    // Always include first 1st vertex in MST.
    // Make key 0 so that this vertex is picked as first
    // vertex.
    key[0] = 0;

    // First node is always root of MST
    parent[0] = -1;

    // The MST will have V vertices
    for (int count = 0; count < V0 - 1; count++) {

        // Pick the minimum key vertex from the
        // set of vertices not yet included in MST
        int u = minKey(key, mstSet);

        // Add the picked vertex to the MST Set
        mstSet[u] = true;

        // Update key value and parent index of
        // the adjacent vertices of the picked vertex.
        // Consider only those vertices which are not
        // yet included in MST
        for (int v = 0; v < V0; v++)

            // graph[u][v] is non zero only for adjacent
            // vertices of m mstSet[v] is false for vertices
            // not yet included in MST Update the key only
            // if graph[u][v] is smaller than key[v]
            if (graph1[u][v] && mstSet[v] == false
                && graph1[u][v] < key[v])
                parent[v] = u, key[v] = graph1[u][v];
    }

    // print the constructed MST
    printMST(parent, graph1);
    cout<<"\n";
}





///*Dijkstra's algorithm for shortest path*/
// Data structure to store a graph edge
struct Edge {
    int source, dest, weight;
};

// Data structure to store a heap node
struct Node {
    int vertex, weight;
};

// A class to represent a graph object
class Graph
{
public:
    // a vector of vectors of `Edge` to represent an adjacency list
    vector<vector<Edge>> adjList;

    // Graph Constructor
    Graph(vector<Edge> const &edges, int n)
    {
        // resize the vector to hold `n` elements of type vector<Edge>
        adjList.resize(n);

        // add edges to the directed graph
        for (Edge const &edge: edges)
        {
            // insert at the end
            adjList[edge.source].push_back(edge);
        }
    }
};

void printPath(vector<int> const &prev, int i, int source)
{
    if (i < 0) {
        return;
    }
    printPath(prev, prev[i], source);
    if (i != source) {
        cout << ", ";
    }
    cout << i;
}

// Comparison object to be used to order the heap
struct comp
{
    bool operator()(const Node &lhs, const Node &rhs) const {
        return lhs.weight > rhs.weight;
    }
};

// Run Dijkstra’s algorithm on the given graph
void findShortestPaths(Graph const &graph, int source, int n)
{
    // create a min-heap and push source node having distance 0
    priority_queue<Node, vector<Node>, comp> min_heap;
    min_heap.push({source, 0});

    // set initial distance from the source to `v` as infinity
    vector<int> dist(n, INT_MAX);

    // distance from the source to itself is zero
    dist[source] = 0;

    // boolean array to track vertices for which minimum
    // cost is already found
    vector<bool> done(n, false);
    done[source] = true;

    // stores predecessor of a vertex (to a print path)
    vector<int> prev(n, -1);

    // run till min-heap is empty
    while (!min_heap.empty())
    {
        // Remove and return the best vertex
        Node node = min_heap.top();
        min_heap.pop();

        // get the vertex number
        int u = node.vertex;

        // do for each neighbor `v` of `u`
        for (auto i: graph.adjList[u])
        {
            int v = i.dest;
            int weight = i.weight;

            // Relaxation step
            if (!done[v] && (dist[u] + weight) < dist[v])
            {
                dist[v] = dist[u] + weight;
                prev[v] = u;
                min_heap.push({v, dist[v]});
            }
        }

        // mark vertex `u` as done so it will not get picked up again
        done[u] = true;
    }

    for (int i = 0; i < n; i++)
    {
        if (i != source && dist[i] != INT_MAX)
        {
            cout << "Path (" << source << " -> " << i << "): Minimum cost = "
                 << dist[i] << ", Route = [";
            printPath(prev, i, source);
            cout << "]" << endl;
        }
    }
}





///*Bellman Ford */

struct Edge1 {
    int source1, dest1, weight1;
};

// Recursive function to print the path of a given vertex from source vertex
void printPath1(vector<int> const &parent1, int vertex1, int source1)
{
    if (vertex1 < 0) {
        return;
    }

    printPath1(parent1, parent1[vertex1], source1);
    if (vertex1 != source1) {
        cout << ", ";
    }
    cout << vertex1;
}

// Function to run the Bellman–Ford algorithm from a given source
void bellmanFord(vector<Edge1> const &edges1, int source1, int n1)
{
    // distance[] and parent[] stores the shortest path (the least cost/path)
    // information. Initially, all vertices except the source vertex
    // weight INFINITY and no parent

    vector<int> distance (n1, INT_MAX);
    distance[source1] = 0;

    vector<int> parent (n1, -1);

    int u, v, w, k = n1;

    // relaxation step (run V-1 times)
    while (--k)
    {
        for (Edge1 edge: edges1)
        {
            // edge from `u` to `v` having weight `w`
            u = edge.source1;
            v = edge.dest1;
            w = edge.weight1;

            // if the distance to destination `v` can be
            // shortened by taking edge (u, v)
            if (distance[u] != INT_MAX && distance[u] + w < distance[v])
            {
                // update distance to the new lower value
                distance[v] = distance[u] + w;

                // set v's parent as `u`
                parent[v] = u;
            }
        }
    }

    // run relaxation step once more for n'th time to check for negative-weight cycles
    for (Edge1 edge: edges1)
    {
        // edge from `u` to `v` having weight `w`
        u = edge.source1;
        v = edge.dest1;
        w = edge.weight1;

        // if the distance to destination `u` can be shortened by taking edge (u, v)
        if (distance[u] != INT_MAX && distance[u] + w < distance[v])
        {
            cout << "Negative-weight cycle is found!!";
            return;
        }
    }

    for (int i = 0; i < n1; i++)
    {
        if (i != source1 && distance[i] < INT_MAX)
        {
            cout << "The distance of vertex " << i << " from the source is "
                 << setw(2) << distance[i] << ". Its path is [";
            printPath(parent, i, source1); cout << "]" << endl;
        }
    }
}




int main()
{
///*Kruskal's algorithm for MST*/
    Graph_1 graph1(4);
    graph1.addEdge(0, 1, 10);
    graph1.addEdge(1, 3, 15);
    graph1.addEdge(2, 3, 4);
    graph1.addEdge(2, 0, 6);
    graph1.addEdge(0, 3, 5);
    graph1.kruskals_mst();

///*Prim's algorithm*/
    int graph_1[V0][V0] = { { 0, 2, 0, 6 },
                        { 2, 0, 3, 8 },
                        { 0, 3, 0, 0 },
                        { 6, 8, 0, 0 }};

    primMST(graph_1);

///*Dijkstra's algorithm*/
    // initialize edges as per the above diagram
    // (u, v, w) represent edge from vertex `u` to vertex `v` having weight `w`
    vector<Edge> edges1 =
            {
                    {0, 1, 10}, {0, 4, 3}, {1, 2, 2}, {1, 4, 4}, {2, 3, 9},
                    {3, 2, 7}, {4, 1, 1}, {4, 2, 8}, {4, 3, 2}
            };

    // total number of nodes in the graph (labelled from 0 to 4)
    int n = 5;

    // construct graph
    Graph graph(edges1, n);

    // run the Dijkstra’s algorithm from every node
    for (int source1 = 0; source1 < n; source1++) {
        findShortestPaths(graph, source1, n);
    }

    cout<<"\n"<<"\n";


///*Bellman Ford's algorithm*/
// vector of graph edges as per the above diagram
    vector<Edge1> edges =
            {
                    // (x, y, w) —> edge from `x` to `y` having weight `w`
                    {0, 1, -1}, {0, 2, 4}, {1, 2, 3}, {1, 3, 2},
                    {1, 4, 2}, {3, 2, 5}, {3, 1, 1}, {4, 3, -3}
            };

    // set the maximum number of nodes in the graph
    int n1 = 5;

    // run the Bellman–Ford algorithm from every node
    for (int source = 0; source < n1; source++) {
        bellmanFord(edges, source, n1);
    }
    return 0;
}
