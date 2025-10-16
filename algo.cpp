#include <iostream>
#include <vector>
#include <limits>
#include <cmath>
#include <algorithm>
#include <queue>
#include <map>
#include <list>
#include <functional>
#include <chrono>
#include <random>
#include <iomanip>

// Use a large value for infinity
const double INF = std::numeric_limits<double>::infinity();

// --- Graph Representation ---
struct Edge {
    int to;
    double weight;
};

// We use a simplified graph structure for clarity
using AdjacencyList = std::vector<std::vector<Edge>>;

// --- Data Structures from the Paper ---

// Represents a path for comparison, breaking ties consistently
// Corresponds to Section 2, "Total order of Paths"
struct Path {
    double distance;
    int length; // number of vertices
    std::vector<int> vertices;

    bool operator<(const Path& other) const {
        if (distance != other.distance) {
            return distance < other.distance;
        }
        if (length != other.length) {
            return length < other.length;
        }
        // Lexicographical comparison of reversed vertex sequence
        for (int i = 0; i < std::min(vertices.size(), other.vertices.size()); ++i) {
            if (vertices[i] != other.vertices[i]) {
                return vertices[i] < other.vertices[i];
            }
        }
        return vertices.size() < other.vertices.size();
    }
};


// Represents a vertex in the priority queue data structure
struct PQNode {
    int vertex;
    double distance;

    bool operator>(const PQNode& other) const {
        return distance > other.distance;
    }
};

// --- Forward Declarations for Main Algorithm Components ---
struct BMSSPResult {
    double new_bound;
    std::vector<int> completed_vertices;
};

BMSSPResult bounded_multi_source_shortest_path(int l, double B, const std::vector<int>& S, 
                                               AdjacencyList& graph, std::vector<double>& d, std::vector<int>& pred,
                                               int k, int t, bool verbose);


// --- Algorithm 1: Finding Pivots ---
struct FindPivotsResult {
    std::vector<int> pivots;
    std::vector<int> W; // Vertices completed in the process
};

FindPivotsResult find_pivots(double B, const std::vector<int>& S, AdjacencyList& graph, 
                             std::vector<double>& d, std::vector<int>& pred, int k, bool verbose) {
    if (verbose) std::cout << "  FINDPIVOTS started with |S| = " << S.size() << std::endl;
    std::vector<bool> in_W(graph.size(), false);
    std::vector<int> W;
    std::vector<int> W_i = S;

    for(int v : S) {
        if (!in_W[v]) {
            W.push_back(v);
            in_W[v] = true;
        }
    }
    
    // Relax for k steps
    for (int i = 0; i < k; ++i) {
        std::vector<int> W_next;
        for (int u : W_i) {
            for (const auto& edge : graph[u]) {
                int v = edge.to;
                if (d[u] + edge.weight < d[v]) {
                    if (d[u] + edge.weight < B) {
                        d[v] = d[u] + edge.weight;
                        pred[v] = u;
                        if (!in_W[v]) {
                            W.push_back(v);
                            in_W[v] = true;
                            W_next.push_back(v);
                        }
                    }
                }
            }
        }
        W_i = W_next;
        if (S.size() > 0 && W.size() > k * S.size()) {
            if (verbose) std::cout << "    FINDPIVOTS: |W| > k|S|, returning all of S as pivots." << std::endl;
            return { S, W };
        }
    }

    // Identify pivots from trees in the shortest path forest
    std::map<int, std::vector<int>> children;
    std::map<int, int> parent_count;
    std::vector<int> roots;
    
    std::vector<bool> in_S(graph.size(), false);
    for(int v : S) in_S[v] = true;

    for (int u : W) {
        if (pred[u] != -1 && u < in_W.size() && pred[u] < in_W.size() && in_W[pred[u]]) {
             children[pred[u]].push_back(u);
             parent_count[u]++;
        }
    }

    for (int u : W) {
        if(parent_count.find(u) == parent_count.end()){
            if(in_S[u]) roots.push_back(u);
        }
    }

    std::vector<int> pivots;
    std::function<int(int)> count_descendants = 
        [&](int u) -> int {
        int count = 1;
        if (children.count(u)) {
            for (int v : children[u]) {
                count += count_descendants(v);
            }
        }
        return count;
    };
    
    for (int r : roots) {
        if (count_descendants(r) >= k) {
            pivots.push_back(r);
        }
    }
    if (verbose) std::cout << "  FINDPIVOTS finished. Found " << pivots.size() << " pivots." << std::endl;

    return { pivots, W };
}

// --- Algorithm 2: Base Case of BMSSP ---
// A simple Dijkstra-like procedure from a single source 'x'
BMSSPResult base_case_bmssp(double B, int x, AdjacencyList& graph, std::vector<double>& d, std::vector<int>& pred, int k) {
    std::priority_queue<PQNode, std::vector<PQNode>, std::greater<PQNode>> pq;
    std::vector<int> U0;
    
    pq.push({x, d[x]});
    
    std::vector<bool> visited(graph.size(), false);
    
    while (!pq.empty() && U0.size() < k + 1) {
        PQNode current = pq.top();
        pq.pop();
        
        int u = current.vertex;
        if(visited[u]) continue;
        visited[u] = true;

        U0.push_back(u);

        for (const auto& edge : graph[u]) {
            int v = edge.to;
            if (d[u] + edge.weight < d[v] && d[u] + edge.weight < B) {
                d[v] = d[u] + edge.weight;
                pred[v] = u;
                pq.push({v, d[v]});
            }
        }
    }
    
    if (U0.size() <= k) {
        return {B, U0};
    } else {
        double max_dist = 0.0;
        bool found = false;
        for (int v : U0) {
            if (d[v] != INF) {
                if (!found || d[v] > max_dist) {
                    max_dist = d[v];
                    found = true;
                }
            }
        }
        std::vector<int> final_U;
        for (int v : U0) {
            if (d[v] < max_dist) {
                final_U.push_back(v);
            }
        }
        return {max_dist, final_U};
    }
}

// --- Lemma 3.3: Custom Data Structure ---
// A simplified implementation for demonstration. A production version would need
// the complex block-based linked list structure for performance.
class CustomPriorityQueue {
private:
    std::list<std::pair<int, double>> data;
    size_t M;
    double B_upper;

public:
    CustomPriorityQueue(size_t m, double b) : M(m), B_upper(b) {}

    void insert(int key, double value) {
        // Simple sorted insert for this example
        auto it = std::lower_bound(data.begin(), data.end(), std::make_pair(key, value),
            [](const std::pair<int, double>& a, const std::pair<int, double>& b){ return a.second < b.second; });
        data.insert(it, {key, value});
    }

    void batch_prepend(const std::vector<std::pair<int, double>>& items) {
       for(const auto& item : items) {
           data.push_front({item.first, item.second});
       }
       // In a real implementation, this would be more efficient, creating new blocks.
       data.sort([](const std::pair<int, double>& a, const std::pair<int, double>& b){ return a.second < b.second; });
    }

    std::pair<double, std::vector<int>> pull() {
        if (data.empty()) {
            return {B_upper, {}};
        }

        std::vector<int> result_keys;
        size_t count = 0;
        while(count < M && !data.empty()){
            result_keys.push_back(data.front().first);
            data.pop_front();
            count++;
        }
        
        double next_bound = B_upper;
        if (!data.empty()) {
            next_bound = data.front().second;
        }
        
        return {next_bound, result_keys};
    }

    bool is_empty() const {
        return data.empty();
    }
};


// --- Algorithm 3: Bounded Multi-Source Shortest Path (BMSSP) ---
BMSSPResult bounded_multi_source_shortest_path(int l, double B, const std::vector<int>& S, 
                                               AdjacencyList& graph, std::vector<double>& d, std::vector<int>& pred,
                                               int k, int t, bool verbose) {
    if (verbose) std::cout << "BMSSP level " << l << " started. |S| = " << S.size() << ", B = " << B << std::endl;
    if (l == 0) {
        if (S.empty()) return {B, {}};
        return base_case_bmssp(B, S[0], graph, d, pred, k);
    }
    
    FindPivotsResult pivots_res = find_pivots(B, S, graph, d, pred, k, verbose);
    std::vector<int> P = pivots_res.pivots;
    std::vector<int> W = pivots_res.W;
    
    size_t M = (l > 1) ? static_cast<size_t>(pow(2, (l - 1) * t)) : 1;
    if (M==0) M = 1;

    CustomPriorityQueue D(M, B);

    double B0_prime = B;
    if (!P.empty()) {
        B0_prime = d[P[0]];
        for (int p : P) {
            D.insert(p, d[p]);
            if(d[p] < B0_prime) B0_prime = d[p];
        }
    }
    
    std::vector<int> U;
    
    while (U.size() < k * pow(2, l*t) && !D.is_empty()) {
        auto pull_res = D.pull();
        double Bi = pull_res.first;
        std::vector<int> Si = pull_res.second;

        if (Si.empty()) break;
        
        BMSSPResult sub_res = bounded_multi_source_shortest_path(l - 1, Bi, Si, graph, d, pred, k, t, verbose);
        double Bi_prime = sub_res.new_bound;
        std::vector<int> Ui = sub_res.completed_vertices;

        for(int v : Ui) U.push_back(v);

        std::vector<std::pair<int, double>> K;

        // Relax edges from Ui
        for (int u : Ui) {
            for (const auto& edge : graph[u]) {
                int v = edge.to;
                double new_dist = d[u] + edge.weight;
                if (new_dist < d[v]) {
                    d[v] = new_dist;
                    pred[v] = u;
                    if (new_dist >= Bi && new_dist < B) {
                        D.insert(v, new_dist);
                    } else if (new_dist >= Bi_prime && new_dist < Bi) {
                        K.push_back({v, new_dist});
                    }
                }
            }
        }
        
        // Add back elements from Si that weren't processed
        for(int x : Si){
            if(d[x] >= Bi_prime && d[x] < Bi){
                K.push_back({x, d[x]});
            }
        }

        if(!K.empty()){
            D.batch_prepend(K);
        }
        
        B0_prime = Bi_prime; // Update the boundary
    }

    double final_B_prime = (U.size() >= k * pow(2, l*t)) ? B0_prime : B;
    
    // Add completed vertices from W
    for(int v : W){
        if(d[v] < final_B_prime){
            bool already_in_U = false;
            for(int u_v : U) if(u_v == v) already_in_U = true;
            if(!already_in_U) U.push_back(v);
        }
    }
    
    if (verbose) std::cout << "BMSSP level " << l << " finished. |U| = " << U.size() << ", B' = " << final_B_prime << std::endl;
    return {final_B_prime, U};
}

// --- Main SSSP Solver ---
std::vector<double> solve_sssp(AdjacencyList& graph, int start_node, bool verbose=false) {
    int n = graph.size();
    if (n == 0) return {};
    
    // Set parameters k and t as per the paper
    double logn = (n > 1) ? log2(n) : 1;
    int k = static_cast<int>(floor(pow(logn, 1.0/3.0)));
    int t = static_cast<int>(floor(pow(logn, 2.0/3.0)));
    
    // Handle very small graphs where log(n) might be small
    if (k < 1) k = 1;
    if (t < 1) t = 1;

    if (verbose) std::cout << "Parameters: n=" << n << ", k=" << k << ", t=" << t << std::endl;

    std::vector<double> d(n, INF);
    std::vector<int> pred(n, -1);
    
    d[start_node] = 0.0;
    
    int top_level_l = (t > 0) ? static_cast<int>(ceil(logn / t)) : 1;
    
    BMSSPResult final_result = bounded_multi_source_shortest_path(
        top_level_l, 
        INF, 
        {start_node}, 
        graph, 
        d, 
        pred,
        k, t,
        verbose
    );

    if (verbose) {
        std::cout << "\n--- Shortest Path Results ---" << std::endl;
        for (int i = 0; i < n; ++i) {
            std::cout << "Distance from " << start_node << " to " << i << " is: ";
            if (d[i] == INF) {
                std::cout << "infinity" << std::endl;
            } else {
                std::cout << d[i] << std::endl;
            }
        }
    }
    return d;
}

// --- Standard Dijkstra's Algorithm for Comparison ---
std::vector<double> dijkstra(AdjacencyList& graph, int start_node) {
    int n = graph.size();
    std::vector<double> d(n, INF);
    d[start_node] = 0.0;
    
    std::priority_queue<PQNode, std::vector<PQNode>, std::greater<PQNode>> pq;
    pq.push({start_node, 0.0});
    
    while (!pq.empty()) {
        PQNode current = pq.top();
        pq.pop();
        
        int u = current.vertex;
        double dist = current.distance;
        
        if (dist > d[u]) continue;
        
        for (const auto& edge : graph[u]) {
            int v = edge.to;
            if (d[u] + edge.weight < d[v]) {
                d[v] = d[u] + edge.weight;
                pq.push({v, d[v]});
            }
        }
    }
    return d;
}

// --- Graph Generation for Benchmarking ---
AdjacencyList generate_random_graph(int n, int m) {
    AdjacencyList graph(n);
    std::random_device rd;
    std::mt19937 gen(rd());
    std::uniform_int_distribution<> vertex_dist(0, n - 1);
    std::uniform_real_distribution<> weight_dist(1.0, 100.0);
    
    for (int i = 0; i < m; ++i) {
        int u = vertex_dist(gen);
        int v = vertex_dist(gen);
        if (u == v) { // Avoid self-loops for simplicity
            i--;
            continue;
        }
        double w = weight_dist(gen);
        graph[u].push_back({v, w});
    }
    return graph;
}


int main() {
    // --- SSSP Performance Benchmark ---
    std::cout << "--- SSSP Performance Benchmark ---" << std::endl;
    
    std::vector<std::pair<int, int>> test_cases = {
        {50000, 250000},
        {100000, 500000},
        {150000, 750000},
        {200000, 1000000},
        {250000, 1250000},
        {300000, 1500000}
    };
    
    int test_num = 1;
    for (const auto& p : test_cases) {
        int n = p.first;
        int m = p.second;
        
        std::cout << "\n--- Test " << test_num++ << ": n=" << n << ", m=" << m << " ---" << std::endl;
        
        AdjacencyList graph = generate_random_graph(n, m);
        int start_node = 0;
        
        // Time New Algorithm
        auto start_new = std::chrono::high_resolution_clock::now();
        std::vector<double> res_new = solve_sssp(graph, start_node, false);
        auto end_new = std::chrono::high_resolution_clock::now();
        std::chrono::duration<double, std::milli> new_algo_time = end_new - start_new;
        
        // Time Dijkstra's Algorithm
        auto start_dijkstra = std::chrono::high_resolution_clock::now();
        std::vector<double> res_dijkstra = dijkstra(graph, start_node);
        auto end_dijkstra = std::chrono::high_resolution_clock::now();
        std::chrono::duration<double, std::milli> dijkstra_time = end_dijkstra - start_dijkstra;
        
        // Print results
        std::cout << std::fixed << std::setprecision(5);
        std::cout << "New Algorithm Time:         " << new_algo_time.count() << " ms" << std::endl;
        std::cout << "Dijkstra's Algorithm Time:  " << dijkstra_time.count() << " ms" << std::endl;
        std::cout << "Dijkstra's lagged by:       " << (dijkstra_time - new_algo_time).count() << " ms" << std::endl;

    }
    
    return 0;
}

