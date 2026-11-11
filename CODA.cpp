#include <iostream>
#include <fstream>
#include <sstream>
#include <vector>
#include <unordered_set>
#include <unordered_map>
#include <queue>
#include <algorithm>
#include <tuple>
#include <climits>
#include <numeric>
#include <functional>
#include <ctime>
#include <cmath>
#include <set>
#include <map>

// Wire capacity c(e^F) of every inter-FPGA link.
const int WIRE_CAPACITY = 50;
// The delay of a link carrying s signals is its TDM ratio ceil(s / c(e^F))
// rounded up to an even number, which equals 2 * ceil(s / (2 * c(e^F))).
// Internally, all delays are kept as ceil(s / tmp_ratio), i.e., half of the
// actual delay; reported critical path delays are multiplied by 2.
const int tmp_ratio = 2 * WIRE_CAPACITY;

struct FPGAGraph {
    int n, m;
    std::vector<std::vector<int>> adj;
    std::vector<std::vector<int>> dist;

    bool load(const std::string& filename) {
        std::ifstream fin(filename);
        if (!fin.is_open()) {
            return false;
        }
        fin >> n >> m;
        adj.assign(n, std::vector<int>());
        for (int i = 0; i < m; i++) {
            int u, v;
            fin >> u >> v;
            adj[u].push_back(v);
            adj[v].push_back(u);
        }
        return true;
    }

    void analyze() {
        dist.assign(n, std::vector<int>(n, -1));
        for (int s = 0; s < n; s++) {
            dist[s][s] = 0;
            std::queue<int> q;
            q.push(s);
            while (!q.empty()) {
                int u = q.front();
                q.pop();
                for (int v : adj[u]) {
                    if (dist[s][v] == -1) {
                        dist[s][v] = dist[s][u] + 1;
                        q.push(v);
                    }
                }
            }
        }
    }
};

struct HyperGraph {
    int n, m;
    std::vector<std::pair<int, std::vector<int>>> hyperedges;
    std::unordered_set<int> flip_flops;
};

struct SuperNode {
    int id;
    std::unordered_set<int> nodes;
    int weight;
    bool is_ff;
};

struct Net {
    std::unordered_set<int> sinks;
    int weight;
};

using SNGraph = std::unordered_map<int, std::vector<Net>>;

struct NetRoute {
    int driver;
    std::vector<int> sinks;
    std::unordered_map<int, std::vector<int>> sink_paths;
    int weight;
};

struct PartitionResult {
    std::unordered_map<int, int> placed_on;
    std::vector<int> fpga_used_weight;
    std::vector<std::vector<int>> d;
    std::unordered_map<int, std::vector<NetRoute>> r_star;
};

HyperGraph read_hypergraph(const std::string& hg_file, const std::string& ff_file) {
    HyperGraph hg;
    std::ifstream fin(hg_file);
    if (!fin) { std::cerr << "Cannot open " << hg_file << "\n"; exit(1); }
    std::string firstline;
    std::getline(fin, firstline);
    std::istringstream fss(firstline);
    fss >> hg.m >> hg.n;
    for (int i = 0; i < hg.m; i++) {
        std::string line;
        std::getline(fin >> std::ws, line);
        std::istringstream iss(line);
        int node;
        std::vector<int> nodes;
        while (iss >> node) nodes.push_back(node);
        int driver = nodes[0];
        std::vector<int> sinks(nodes.begin() + 1, nodes.end());
        hg.hyperedges.push_back({driver, sinks});
    }
    fin.close();
    std::ifstream fff(ff_file);
    if (!fff) { std::cerr << "Cannot open " << ff_file << "\n"; exit(1); }
    std::string line;
    while (std::getline(fff, line)) {
        if (line.empty() || line[0] == '#') continue;
        std::istringstream iss(line);
        int idx;
        if (iss >> idx) hg.flip_flops.insert(idx);
    }
    fff.close();
    return hg;
}

std::vector<int> compute_depth_initial(const HyperGraph& hg) {
    int n = hg.n;
    std::vector<int> indegree(n + 1, 0);
    std::vector<std::unordered_set<int>> adj(n + 1);
    for (auto& edge : hg.hyperedges) {
        int driver = edge.first;
        for (int s : edge.second) {
            if (!adj[driver].count(s)) {
                adj[driver].insert(s);
                indegree[s]++;
            }
        }
    }
    std::vector<int> color(n + 1, 0);
    std::vector<int> parent(n + 1, -1);
    std::function<bool(int)> dfs = [&](int u) -> bool {
        color[u] = 1;
        for (int v : adj[u]) {
            if (hg.flip_flops.count(v)) continue;
            if (color[v] == 1) {
                std::cerr << "Error: cycle detected.\n";
                exit(1);
            }
            if (color[v] == 0) {
                parent[v] = u;
                if (dfs(v)) return true;
            }
        }
        color[u] = 2;
        return false;
    };
    for (int i = 1; i <= n; i++)
        if (color[i] == 0 && !hg.flip_flops.count(i))
            dfs(i);
    std::vector<int> depth(n + 1, -1);
    std::queue<int> q;
    for (int i = 1; i <= n; i++) {
        if (hg.flip_flops.count(i) || indegree[i] == 0) {
            depth[i] = 1;
            q.push(i);
        }
    }
    while (!q.empty()) {
        int u = q.front(); q.pop();
        for (int v : adj[u]) {
            if (hg.flip_flops.count(v)) continue;
            depth[v] = std::max(depth[v], depth[u] + 1);
            if (--indegree[v] == 0) q.push(v);
        }
    }
    for (int i = 1; i <= n; i++) {
        if (depth[i] == -1) {
            std::cerr << "Error: node " << i << " unreachable after topo sort.\n";
            exit(1);
        }
    }
    return depth;
}

std::vector<SuperNode> build_initial_supernodes(const HyperGraph& hg) {
    std::vector<SuperNode> supernodes(hg.n + 1);
    for (int i = 1; i <= hg.n; i++) {
        supernodes[i].id = i;
        supernodes[i].nodes = {i};
        supernodes[i].weight = 1;
        supernodes[i].is_ff = hg.flip_flops.count(i) > 0;
    }
    return supernodes;
}

SNGraph build_initial_sn_graph(const HyperGraph& hg) {
    SNGraph g;
    for (auto& edge : hg.hyperedges) {
        int driver = edge.first;
        if (edge.second.size() > 200) continue;
        Net net;
        for (int s : edge.second) net.sinks.insert(s);
        net.weight = 1;
        g[driver].push_back(net);
    }
    return g;
}

std::vector<int> read_partition(const std::string& filename, int n) {
    std::vector<int> part(n + 1, -1);
    std::ifstream fin(filename);
    if (!fin) { std::cerr << "Cannot open partition file: " << filename << "\n"; exit(1); }
    for (int i = 1; i <= n; i++)
        fin >> part[i];
    fin.close();
    return part;
}

std::vector<int> map_partitions_to_fpgas(
    const std::vector<int>& raw_part,
    int num_supernodes,
    int num_partitions,
    const SNGraph& sn_graph,
    const std::vector<int>& candidate_fpgas,
    const FPGAGraph& graph)
{
    std::vector<std::vector<long long>> edge_count(
        num_partitions, std::vector<long long>(num_partitions, 0));
    for (const auto& pair : sn_graph) {
        int pu = raw_part[pair.first];
        for (const auto& net : pair.second) {
            for (int v : net.sinks) {
                int pv = raw_part[v];
                if (pu == pv) continue;
                edge_count[pu][pv] += net.weight;
            }
        }
    }

    int C = (int)candidate_fpgas.size();
    int K = num_partitions;
    if (C < K) {
        std::cerr << "Error: candidates (" << C << ") < partitions (" << K << ")\n";
        std::exit(1);
    }

    auto compute_cost = [&](const std::vector<int>& assign) -> long long {
        long long cost = 0;
        for (int i = 0; i < K; i++)
            for (int j = i + 1; j < K; j++)
                cost += (edge_count[i][j] + edge_count[j][i])
                        * (long long)graph.dist[assign[i]][assign[j]];
        return cost;
    };

    double enum_size = 1.0;
    for (int i = 0; i < K; i++) enum_size *= (double)(C - i);

    std::vector<int> best_assignment(K);
    long long best_cost = LLONG_MAX;

    if (enum_size <= 3e6) {
        std::cout << "Using exhaustive enumeration.\n";
        std::vector<int> selector(C, 0);
        for (int i = 0; i < K; i++) selector[C - K + i] = 1;
        do {
            std::vector<int> chosen;
            for (int i = 0; i < C; i++)
                if (selector[i]) chosen.push_back(candidate_fpgas[i]);
            do {
                long long cost = compute_cost(chosen);
                if (cost < best_cost) { best_cost = cost; best_assignment = chosen; }
            } while (std::next_permutation(chosen.begin(), chosen.end()));
        } while (std::next_permutation(selector.begin(), selector.end()));
    } else {
        std::cout << "Using greedy swap heuristic.\n";
        std::vector<int> assign(K);
        for (int p = 0; p < K; p++) assign[p] = candidate_fpgas[p];

        std::unordered_set<int> used(assign.begin(), assign.end());
        std::vector<int> free_fpgas;
        for (int f : candidate_fpgas)
            if (!used.count(f)) free_fpgas.push_back(f);

        long long cur_cost = compute_cost(assign);
        std::cout << "Initial cost: " << cur_cost << "\n";

        int iter = 0;
        while (true) {
            long long best_new_cost = cur_cost;
            int best_type = -1;
            int best_a = -1, best_b = -1;
            for (int i = 0; i < K; i++) {
                for (int j = i + 1; j < K; j++) {
                    std::swap(assign[i], assign[j]);
                    long long c = compute_cost(assign);
                    if (c < best_new_cost) {
                        best_new_cost = c; best_type = 0; best_a = i; best_b = j;
                    }
                    std::swap(assign[i], assign[j]);
                }
            }
            for (int i = 0; i < K; i++) {
                for (int k = 0; k < (int)free_fpgas.size(); k++) {
                    int old_fpga = assign[i];
                    assign[i] = free_fpgas[k];
                    long long c = compute_cost(assign);
                    if (c < best_new_cost) {
                        best_new_cost = c; best_type = 1; best_a = i; best_b = k;
                    }
                    assign[i] = old_fpga;
                }
            }
            if (best_type == -1) break;
            if (best_type == 0) {
                std::swap(assign[best_a], assign[best_b]);
            } else {
                int old_fpga = assign[best_a];
                assign[best_a] = free_fpgas[best_b];
                free_fpgas[best_b] = old_fpga;
            }
            cur_cost = best_new_cost;
            iter++;
            std::cout << "  Iter " << iter << ": cost = " << cur_cost << "\n";
        }
        best_cost = cur_cost;
        best_assignment = assign;
    }

    std::cout << "\n--- Best partition-to-FPGA assignment ---\n";
    std::cout << "Total hop cost: " << best_cost << "\n";
    for (int p = 0; p < K; p++)
        std::cout << "Partition " << p << " -> FPGA " << best_assignment[p] << "\n";

    std::vector<int> final_part(num_supernodes + 1, -1);
    for (int i = 1; i <= num_supernodes; i++)
        final_part[i] = best_assignment[raw_part[i]];
    return final_part;
}

std::vector<int> locally_dense_decomposition(
    const FPGAGraph& graph,
    int num_partitions,
    int rounds = 50,
    double eps = 1e-4)
{
    int n = graph.n;

    struct EdgeState { int u, v; double f_u, f_v; };
    std::vector<EdgeState> edges;
    edges.reserve(graph.m);
    for (int u = 0; u < n; ++u) {
        for (int v : graph.adj[u]) {
            if (u < v) edges.push_back({u, v, 0.5, 0.5});
        }
    }

    std::vector<double> load(n, 0.0);
    for (int i = 0; i < n; ++i) load[i] = (double)graph.adj[i].size() / 2.0;

    for (int r = 0; r < rounds; ++r) {
        for (auto& e : edges) {
            int i = e.u, j = e.v;
            if (load[i] > load[j]) {
                double d = std::min((load[i] - load[j]) / 2.0, e.f_u);
                if (d <= 0) continue;
                load[i] -= d;  load[j] += d;
                e.f_u  -= d;   e.f_v  += d;
            } else if (load[j] > load[i]) {
                double d = std::min((load[j] - load[i]) / 2.0, e.f_v);
                if (d <= 0) continue;
                load[j] -= d;  load[i] += d;
                e.f_v  -= d;   e.f_u  += d;
            }
        }
    }

    std::vector<int> order(n);
    std::iota(order.begin(), order.end(), 0);
    std::sort(order.begin(), order.end(),
              [&](int a, int b) { return load[a] > load[b]; });

    int cut = n;
    for (int i = num_partitions - 1; i < n - 1; ++i) {
        if (load[order[i]] - load[order[i + 1]] > eps) {
            cut = i + 1;
            break;
        }
    }

    std::vector<int> candidates(order.begin(), order.begin() + cut);

    std::cout << "[LDD] " << rounds << " rounds, num_partitions=" << num_partitions
              << ", kept " << candidates.size() << " of " << n << " FPGAs\n";
    std::cout << "[LDD] Loads (sorted desc, with cut marker):\n";
    for (int i = 0; i < n; ++i) {
        std::cout << "  FPGA " << order[i] << ": load=" << load[order[i]];
        if (i + 1 == cut) std::cout << "  <-- cut here";
        std::cout << "\n";
    }
    std::cout << "[LDD] candidate_fpgas = {";
    for (size_t i = 0; i < candidates.size(); ++i) {
        if (i) std::cout << ", ";
        std::cout << candidates[i];
    }
    std::cout << "}\n";

    return candidates;
}

PartitionResult initial_partitioning(
    const SNGraph& sn_graph,
    const std::vector<SuperNode>& supernodes,
    int num_supernodes,
    const FPGAGraph& graph,
    int FPGA_capacity)
{
    std::vector<std::vector<int>> hedges;
    for (const auto& pair : sn_graph) {
        int drv = pair.first;
        for (const auto& net : pair.second) {
            std::set<int> pin_set;
            pin_set.insert(drv);
            for (int sink : net.sinks) {
                pin_set.insert(sink);
            }
            if (pin_set.size() < 2) continue;
            hedges.emplace_back(pin_set.begin(), pin_set.end());
        }
    }

    int hedge_count = hedges.size();
    std::string aug_path = "/tmp/coda_kahypar.hgr";
    {
        std::ofstream fout(aug_path);
        fout << hedge_count << " " << num_supernodes << " 10\n";
        for (const auto& he : hedges) {
            bool first = true;
            for (int v : he) {
                if (!first) fout << " ";
                fout << v;
                first = false;
            }
            fout << "\n";
        }
        for (int i = 1; i <= num_supernodes; i++) {
            fout << supernodes[i].weight << "\n";
        }
        fout.close();
    }

    long long total_weight = 0;
    for (int i = 1; i <= num_supernodes; i++) {
        total_weight += supernodes[i].weight;
    }
    int num_partitions = (int)std::ceil(1.1 * (double)total_weight / (double)FPGA_capacity);
    if (num_partitions < 2) num_partitions = 2;
    if (num_partitions > graph.n) num_partitions = graph.n;
    std::cout << "Total weight: " << total_weight
              << ", FPGA capacity: " << FPGA_capacity
              << ", Num partitions: " << num_partitions
              << " (FPGAs available: " << graph.n << ")\n";
    
    int seed = -1;
    
    std::string cmd = "./kahypar/build/kahypar/application/KaHyPar "
                  "-h " + aug_path + " "
                  "-k " + std::to_string(num_partitions) + " "
                  "-e 0.05 "
                  "-o km1 "
                  "-m direct "
                  "-p ./kahypar/config/km1_kKaHyPar_sea20.ini "
                  "--seed=" + std::to_string(seed) + " "
                  "-w true";
                  
    std::cout << "Running: " << cmd << "\n";
    int ret = system(cmd.c_str());
    std::cout << "KaHyPar returned: " << ret << "\n";
    
    std::string part_file = aug_path + ".part" + std::to_string(num_partitions)
                      + ".epsilon0.05.seed" + std::to_string(seed) + ".KaHyPar";

    std::vector<int> raw_part = read_partition(part_file, num_supernodes);

    std::vector<int> candidate_fpgas = locally_dense_decomposition(graph, num_partitions);

    if ((int)candidate_fpgas.size() < num_partitions) {
        std::cerr << "[LDD] FATAL: returned " << candidate_fpgas.size()
                  << " FPGAs, need at least " << num_partitions << "\n";
        std::exit(1);
    }

    std::vector<int> part = map_partitions_to_fpgas(
        raw_part, num_supernodes, num_partitions,
        sn_graph, candidate_fpgas, graph);

    long long total_cuts = 0;
    for (auto& [driver, nets] : sn_graph) {
        int df = part[driver];
        for (auto& net : nets) {
            for (int sink : net.sinks) {
                if (part[sink] != df) total_cuts++;
            }
        }
    }
    std::cout << "Total net cut count (driver-sink cross-FPGA pairs): " << total_cuts << "\n";

    PartitionResult res;
    res.fpga_used_weight.assign(graph.n, 0);
    res.d.assign(graph.n, std::vector<int>(graph.n, 0));

    for (int i = 1; i <= num_supernodes; i++) {
        int fpga = part[i];
        res.placed_on[i] = fpga;
        res.fpga_used_weight[fpga] += supernodes[i].weight;
    }

    for (const auto& pair : sn_graph) {
        int sn_u = pair.first;
        for (const auto& net : pair.second) {
            NetRoute nr;
            nr.driver = sn_u;
            nr.weight = net.weight;
            int driver_fpga = res.placed_on[sn_u];
            std::unordered_set<int> target_fpgas_set;
            for (int v : net.sinks) {
                nr.sinks.push_back(v);
                if (res.placed_on[v] != driver_fpga) {
                    target_fpgas_set.insert(res.placed_on[v]);
                }
            }

            if (target_fpgas_set.empty()) {
                for (int v : net.sinks) {
                    nr.sink_paths[v] = {driver_fpga};
                }
                res.r_star[sn_u].push_back(nr);
                continue;
            }

            std::vector<int> targets(target_fpgas_set.begin(), target_fpgas_set.end());
            std::sort(targets.begin(), targets.end(), [&](int a, int b) {
                return graph.dist[driver_fpga][a] < graph.dist[driver_fpga][b];
            });

            std::unordered_set<int> reached_fpgas = {driver_fpga};
            std::unordered_map<int, int> parent;
            std::set<std::pair<int, int>> used_edges;

            for (size_t t_idx = 0; t_idx < targets.size(); ++t_idx) {
                int T = targets[t_idx];
                if (reached_fpgas.count(T)) continue;

                std::vector<int> rem_targets;
                for (size_t k = t_idx + 1; k < targets.size(); ++k) {
                    rem_targets.push_back(targets[k]);
                }

                int min_f = INT_MAX;
                std::vector<int> A;
                for (int w : reached_fpgas) {
                    if (graph.dist[w][T] + graph.dist[driver_fpga][w] == graph.dist[driver_fpga][T]) {
                        if (graph.dist[w][T] < min_f) {
                            min_f = graph.dist[w][T];
                            A.clear();
                            A.push_back(w);
                        } else if (graph.dist[w][T] == min_f) {
                            A.push_back(w);
                        }
                    }
                }

                int curr = -1;
                if (min_f == graph.dist[driver_fpga][T]) {
                    curr = driver_fpga;
                } else {
                    std::unordered_set<int> B;
                    for (int a : A) {
                        for (int y : graph.adj[a]) {
                            if (!reached_fpgas.count(y) && graph.dist[y][T] == min_f - 1) {
                                B.insert(y);
                            }
                        }
                    }

                    int best_y = -1;
                    int best_x = -1;
                    int max_gain = -1;
                    int min_res_d = INT_MAX;

                    for (int y : B) {
                        int x_y = -1;
                        int c_xy = INT_MAX;
                        for (int a : A) {
                            if (std::find(graph.adj[y].begin(), graph.adj[y].end(), a) != graph.adj[y].end()) {
                                if (res.d[a][y] < c_xy) {
                                    c_xy = res.d[a][y];
                                    x_y = a;
                                }
                            }
                        }

                        int gain_y = 0;
                        for (int S : rem_targets) {
                            int current_min_dist = INT_MAX;
                            for (int r : reached_fpgas) {
                                current_min_dist = std::min(current_min_dist, graph.dist[r][S]);
                            }
                            if (graph.dist[y][S] < current_min_dist) {
                                gain_y += (current_min_dist - graph.dist[y][S]);
                            }
                        }

                        if (gain_y > max_gain) {
                            max_gain = gain_y; best_y = y; best_x = x_y; min_res_d = c_xy;
                        } else if (gain_y == max_gain) {
                            if (c_xy < min_res_d) {
                                best_y = y; best_x = x_y; min_res_d = c_xy;
                            }
                        }
                    }

                    used_edges.insert({std::min(best_x, best_y), std::max(best_x, best_y)});
                    reached_fpgas.insert(best_y);
                    parent[best_y] = best_x;
                    curr = best_y;
                }

                while (curr != T) {
                    std::vector<int> V;
                    for (int v : graph.adj[curr]) {
                        if (!reached_fpgas.count(v) && graph.dist[v][T] == graph.dist[curr][T] - 1) {
                            V.push_back(v);
                        }
                    }

                    int best_v = -1;
                    int max_gain = -1;
                    int min_res_d = INT_MAX;

                    for (int v : V) {
                        int c_cv = res.d[curr][v];
                        int gain_v = 0;
                        for (int S : rem_targets) {
                            int current_min_dist = INT_MAX;
                            for (int r : reached_fpgas) {
                                current_min_dist = std::min(current_min_dist, graph.dist[r][S]);
                            }
                            if (graph.dist[v][S] < current_min_dist) {
                                gain_v += (current_min_dist - graph.dist[v][S]);
                            }
                        }

                        if (gain_v > max_gain) {
                            max_gain = gain_v; best_v = v; min_res_d = c_cv;
                        } else if (gain_v == max_gain) {
                            if (c_cv < min_res_d) {
                                best_v = v; min_res_d = c_cv;
                            }
                        }
                    }

                    used_edges.insert({std::min(curr, best_v), std::max(curr, best_v)});
                    reached_fpgas.insert(best_v);
                    parent[best_v] = curr;
                    curr = best_v;
                }
            }

            for (auto edge : used_edges) {
                res.d[edge.first][edge.second] += net.weight;
                res.d[edge.second][edge.first] += net.weight;
            }

            for (int v : net.sinks) {
                int F_s = res.placed_on[v];
                std::vector<int> path;
                int curr = F_s;
                while (curr != driver_fpga) {
                    path.push_back(curr);
                    curr = parent[curr];
                }
                path.push_back(driver_fpga);
                std::reverse(path.begin(), path.end());
                nr.sink_paths[v] = path;
            }
            res.r_star[sn_u].push_back(nr);
        }
    }

    int consumption=0;
    for (int i = 0; i < graph.n; ++i) {
        for (int j = 0; j < graph.n; ++j) {
            if(res.d[i][j]!=0&&i<j){
                std::cout<<"FPGA "<<i<<" and FPGA "<<j<<": "<<res.d[i][j]<<std::endl;
                consumption+=res.d[i][j];
            }
        }
    }
    std::cout<<"FPGA interconnection consumption: "<<consumption<<std::endl;

    return res;
}

int compute_critical_path_delay(
    const SNGraph& sn_graph,
    const std::vector<SuperNode>& supernodes,
    int num_supernodes,
    const PartitionResult& part_result,
    bool quiet = false)
{
    std::unordered_map<int, std::unordered_map<int, int>> pair_delay;
    for (const auto& u_pair : part_result.r_star) {
        for (const auto& nr : u_pair.second) {
            for (int sink : nr.sinks) {
                int dly = 0;
                const auto& path = nr.sink_paths.at(sink);
                if (path.size() > 1) {
                    for (size_t k = 0; k < path.size() - 1; ++k) {
                        int a = path[k];
                        int b = path[k+1];
                        dly += (int)std::ceil((double)part_result.d[a][b] / (double)tmp_ratio);
                    }
                }
                pair_delay[nr.driver][sink] = std::max(pair_delay[nr.driver][sink], dly);
            }
        }
    }

    std::unordered_map<int, std::unordered_map<int, int>> dir_adj;
    std::vector<int> indegree(num_supernodes + 1, 0);
    for (const auto& pair : sn_graph) {
        int u = pair.first;
        for (const auto& net : pair.second) {
            for (int v : net.sinks) {
                if (!dir_adj[u].count(v)) {
                    dir_adj[u][v] = pair_delay[u][v];
                    indegree[v]++;
                }
            }
        }
    }

    std::vector<int> arrival_time(num_supernodes + 1, 0);
    std::queue<int> q;
    for (int i = 1; i <= num_supernodes; i++) {
        if (supernodes[i].is_ff || indegree[i] == 0) {
            q.push(i);
        }
    }

    int max_critical_delay = 0;
    while (!q.empty()) {
        int u = q.front(); q.pop();
        if (!dir_adj.count(u)) continue;
        for (const auto& edge : dir_adj[u]) {
            int v = edge.first;
            int delay_uv = edge.second;
            int arr_v = arrival_time[u] + delay_uv;
            if (supernodes[v].is_ff) {
                max_critical_delay = std::max(max_critical_delay, arr_v);
            } else {
                arrival_time[v] = std::max(arrival_time[v], arr_v);
                if (--indegree[v] == 0) q.push(v);
            }
        }
    }
    if (!quiet) std::cout << "Max Critical Path Delay: " << 2 * max_critical_delay << "\n";
    return max_critical_delay;
}

struct NodeNetIndex {
    int driver_sn;
    int net_idx;
};

std::unordered_map<int, std::vector<NodeNetIndex>> build_node_to_nets(
    const PartitionResult& res)
{
    std::unordered_map<int, std::vector<NodeNetIndex>> node_nets;
    for (const auto& u_pair : res.r_star) {
        int drv = u_pair.first;
        for (int ni = 0; ni < (int)u_pair.second.size(); ++ni) {
            node_nets[drv].push_back({drv, ni});
            for (int sink : u_pair.second[ni].sinks) {
                if (sink != drv) node_nets[sink].push_back({drv, ni});
            }
        }
    }
    return node_nets;
}

struct STAState {
    int num_supernodes = 0;

    std::unordered_map<int, std::vector<int>> dir_succs;
    std::unordered_map<int, std::vector<int>> rev_preds;
    std::unordered_set<int> Q;
    std::vector<int> topo_arr;
    std::vector<int> topo_req;

    std::unordered_map<int, std::unordered_map<int, int>> pair_delay;
    std::vector<int> arr_time, arr_pi;
    std::vector<int> req_time, req_pi;
    int max_delay = 0;

    std::unordered_map<int, std::unordered_map<int, int>> pair_criticality;
    std::unordered_map<int, std::unordered_map<int, int>> pair_attention;
    std::vector<long long> node_criticality;
    std::vector<int> most_critical_path;
};

static inline int path_delay(const std::vector<int>& path,
                             const std::vector<std::vector<int>>& d) {
    if (path.size() <= 1) return 0;
    int dly = 0;
    for (size_t k = 0; k + 1 < path.size(); ++k)
        dly += (int)std::ceil((double)d[path[k]][path[k+1]] / (double)tmp_ratio);
    return dly;
}

static int recompute_pair_delay_one(int drv, int sink, const PartitionResult& res) {
    int best = 0;
    auto it = res.r_star.find(drv);
    if (it == res.r_star.end()) return 0;
    for (const NetRoute& nr : it->second) {
        auto sit = nr.sink_paths.find(sink);
        if (sit == nr.sink_paths.end()) continue;
        int d = path_delay(sit->second, res.d);
        if (d > best) best = d;
    }
    return best;
}

void sta_init_static(
    STAState& s,
    const SNGraph& sn_graph,
    const std::vector<SuperNode>& supernodes,
    int num_supernodes)
{
    s.num_supernodes = num_supernodes;
    s.dir_succs.clear();
    s.rev_preds.clear();
    s.Q.clear();
    s.topo_arr.assign(num_supernodes + 1, 0);
    s.topo_req.assign(num_supernodes + 1, 0);
    s.arr_time.assign(num_supernodes + 1, -1);
    s.arr_pi.assign(num_supernodes + 1, -1);
    s.req_time.assign(num_supernodes + 1, -1);
    s.req_pi.assign(num_supernodes + 1, -1);
    s.node_criticality.assign(num_supernodes + 1, 0);

    std::vector<int> indegree_orig(num_supernodes + 1, 0);
    for (const auto& pair : sn_graph) {
        int u = pair.first;
        std::unordered_set<int> seen;
        for (const Net& net : pair.second) {
            for (int v : net.sinks) {
                if (seen.insert(v).second) {
                    s.dir_succs[u].push_back(v);
                    s.rev_preds[v].push_back(u);
                    indegree_orig[v]++;
                }
            }
        }
    }

    for (int i = 1; i <= num_supernodes; ++i)
        if (supernodes[i].is_ff || indegree_orig[i] == 0) s.Q.insert(i);

    {
        std::vector<int> mod_indeg(num_supernodes + 1, 0);
        for (int u = 1; u <= num_supernodes; ++u) {
            if (supernodes[u].is_ff) continue;
            auto it = s.dir_succs.find(u);
            if (it == s.dir_succs.end()) continue;
            for (int v : it->second) mod_indeg[v]++;
        }
        int next_idx = 1;
        std::queue<int> qq;
        for (int i = 1; i <= num_supernodes; ++i)
            if (mod_indeg[i] == 0) { s.topo_arr[i] = next_idx++; qq.push(i); }
        while (!qq.empty()) {
            int u = qq.front(); qq.pop();
            if (supernodes[u].is_ff) continue;
            auto it = s.dir_succs.find(u);
            if (it == s.dir_succs.end()) continue;
            for (int v : it->second)
                if (--mod_indeg[v] == 0) { s.topo_arr[v] = next_idx++; qq.push(v); }
        }
        for (int i = 1; i <= num_supernodes; ++i)
            if (s.topo_arr[i] == 0) { std::cerr << "topo_arr[" << i << "]=0!\n"; std::exit(1); }
    }

    {
        std::vector<int> rmod_indeg(num_supernodes + 1, 0);
        for (int u = 1; u <= num_supernodes; ++u) {
            auto it = s.dir_succs.find(u);
            if (it == s.dir_succs.end()) continue;
            for (int v : it->second)
                if (!supernodes[v].is_ff) rmod_indeg[v]++;
        }
        int next_idx = 1;
        std::queue<int> qq;
        for (int i = 1; i <= num_supernodes; ++i)
            if (rmod_indeg[i] == 0) { s.topo_req[i] = next_idx++; qq.push(i); }
        while (!qq.empty()) {
            int u = qq.front(); qq.pop();
            auto it = s.dir_succs.find(u);
            if (it == s.dir_succs.end()) continue;
            for (int v : it->second) {
                if (supernodes[v].is_ff) continue;
                if (--rmod_indeg[v] == 0) { s.topo_req[v] = next_idx++; qq.push(v); }
            }
        }
        for (int i = 1; i <= num_supernodes; ++i)
            if (s.topo_req[i] == 0) { std::cerr << "topo_req[" << i << "]=0!\n"; std::exit(1); }
    }
}

static void sta_recompute_all_pair_delays(STAState& s, const PartitionResult& res) {
    s.pair_delay.clear();
    for (const auto& u_pair : res.r_star) {
        int drv = u_pair.first;
        for (const NetRoute& nr : u_pair.second) {
            for (int sink : nr.sinks) {
                auto sit = nr.sink_paths.find(sink);
                if (sit == nr.sink_paths.end()) continue;
                int d = path_delay(sit->second, res.d);
                int& cur = s.pair_delay[drv][sink];
                if (d > cur) cur = d;
            }
        }
    }
}

static inline std::pair<int,int> sta_compute_arr_for(int v, STAState& s) {
    auto rev_it = s.rev_preds.find(v);
    if (rev_it == s.rev_preds.end()) return {-1, -1};
    int best = -1, best_pi = -1;
    for (int p : rev_it->second) {
        auto pd_it = s.pair_delay.find(p);
        if (pd_it == s.pair_delay.end()) continue;
        auto e_it = pd_it->second.find(v);
        if (e_it == pd_it->second.end()) continue;
        int pd = e_it->second;
        int contrib;
        if (s.Q.count(p)) {
            contrib = pd;
        } else {
            if (s.arr_time[p] == -1) continue;
            contrib = s.arr_time[p] + pd;
        }
        if (contrib > best) { best = contrib; best_pi = p; }
    }
    return {best, best_pi};
}

static inline std::pair<int,int> sta_compute_req_for(
    int u, STAState& s, const std::vector<SuperNode>& supernodes)
{
    auto fwd_it = s.dir_succs.find(u);
    if (fwd_it == s.dir_succs.end()) return {-1, -1};
    auto pd_u_it = s.pair_delay.find(u);
    if (pd_u_it == s.pair_delay.end()) return {-1, -1};
    int best = -1, best_pi = -1;
    for (int v : fwd_it->second) {
        auto e_it = pd_u_it->second.find(v);
        if (e_it == pd_u_it->second.end()) continue;
        int pd = e_it->second;
        int contrib;
        if (supernodes[v].is_ff) {
            contrib = pd;
        } else {
            if (s.req_time[v] == -1) continue;
            contrib = s.req_time[v] + pd;
        }
        if (contrib > best) { best = contrib; best_pi = v; }
    }
    return {best, best_pi};
}

static void sta_full_arrival(STAState& s, const std::vector<SuperNode>& supernodes) {
    int N = s.num_supernodes;
    std::vector<int> order(N);
    std::iota(order.begin(), order.end(), 1);
    std::sort(order.begin(), order.end(),
              [&](int a, int b) { return s.topo_arr[a] < s.topo_arr[b]; });
    std::fill(s.arr_time.begin(), s.arr_time.end(), -1);
    std::fill(s.arr_pi.begin(), s.arr_pi.end(), -1);
    s.max_delay = 0;

    for (int v : order) {
        if (s.Q.count(v) && !supernodes[v].is_ff) continue;
        auto [arr, pi] = sta_compute_arr_for(v, s);
        s.arr_time[v] = arr;
        s.arr_pi[v] = pi;
        if (supernodes[v].is_ff && arr > s.max_delay) s.max_delay = arr;
    }
}

static void sta_full_required(STAState& s, const std::vector<SuperNode>& supernodes) {
    int N = s.num_supernodes;
    std::vector<int> order(N);
    std::iota(order.begin(), order.end(), 1);
    std::sort(order.begin(), order.end(),
              [&](int a, int b) { return s.topo_req[a] > s.topo_req[b]; });
    std::fill(s.req_time.begin(), s.req_time.end(), -1);
    std::fill(s.req_pi.begin(), s.req_pi.end(), -1);
    for (int u : order) {
        auto [req, pi] = sta_compute_req_for(u, s, supernodes);
        s.req_time[u] = req;
        s.req_pi[u] = pi;
    }
}

static void sta_recompute_max_delay(STAState& s, const std::vector<SuperNode>& supernodes) {
    s.max_delay = 0;
    for (int i = 1; i <= s.num_supernodes; ++i)
        if (supernodes[i].is_ff && s.arr_time[i] > s.max_delay) s.max_delay = s.arr_time[i];
}

void sta_run_full(STAState& s, const PartitionResult& res,
                  const std::vector<SuperNode>& supernodes) {
    sta_recompute_all_pair_delays(s, res);
    sta_full_arrival(s, supernodes);
    sta_full_required(s, supernodes);
    sta_recompute_max_delay(s, supernodes);
}

void sta_run_incremental(
    STAState& s,
    const PartitionResult& res,
    const std::vector<NodeNetIndex>& affected_nets,
    const std::vector<SuperNode>& supernodes)
{
    std::set<std::pair<int,int>> affected_edges;
    for (const NodeNetIndex& an : affected_nets) {
        int drv = an.driver_sn;
        auto vec_it = res.r_star.find(drv);
        if (vec_it == res.r_star.end()) continue;
        if (an.net_idx < 0 || an.net_idx >= (int)vec_it->second.size()) continue;
        const NetRoute& nr = vec_it->second[an.net_idx];
        for (int sink : nr.sinks) {
            if (sink == drv) continue;
            affected_edges.insert({drv, sink});
        }
    }

    std::unordered_set<int> seed_arr;
    std::unordered_set<int> seed_req;
    for (const auto& e : affected_edges) {
        int drv = e.first, sink = e.second;
        int new_pd = recompute_pair_delay_one(drv, sink, res);
        int old_pd = 0;
        auto pd_it = s.pair_delay.find(drv);
        if (pd_it != s.pair_delay.end()) {
            auto sit = pd_it->second.find(sink);
            if (sit != pd_it->second.end()) old_pd = sit->second;
        }
        if (new_pd != old_pd) {
            s.pair_delay[drv][sink] = new_pd;
            seed_arr.insert(sink);
            seed_req.insert(drv);
        }
    }

    auto cmp_fwd = [&](int a, int b) {
        if (s.topo_arr[a] != s.topo_arr[b]) return s.topo_arr[a] < s.topo_arr[b];
        return a < b;
    };
    std::set<int, decltype(cmp_fwd)> arr_wl(cmp_fwd);
    for (int v : seed_arr) arr_wl.insert(v);

    while (!arr_wl.empty()) {
        int v = *arr_wl.begin();
        arr_wl.erase(arr_wl.begin());

        if (s.Q.count(v) && !supernodes[v].is_ff) continue;

        auto [new_arr, new_pi] = sta_compute_arr_for(v, s);
        bool arr_changed = (new_arr != s.arr_time[v]);
        s.arr_time[v] = new_arr;
        s.arr_pi[v] = new_pi;

        if (arr_changed && !supernodes[v].is_ff) {
            auto it = s.dir_succs.find(v);
            if (it != s.dir_succs.end()) {
                for (int succ : it->second) arr_wl.insert(succ);
            }
        }
    }

    auto cmp_bwd = [&](int a, int b) {
        if (s.topo_req[a] != s.topo_req[b]) return s.topo_req[a] > s.topo_req[b];
        return a < b;
    };
    std::set<int, decltype(cmp_bwd)> req_wl(cmp_bwd);
    for (int u : seed_req) req_wl.insert(u);

    while (!req_wl.empty()) {
        int u = *req_wl.begin();
        req_wl.erase(req_wl.begin());

        auto [new_req, new_pi] = sta_compute_req_for(u, s, supernodes);
        bool req_changed = (new_req != s.req_time[u]);
        s.req_time[u] = new_req;
        s.req_pi[u] = new_pi;

        if (req_changed && !supernodes[u].is_ff) {
            auto it = s.rev_preds.find(u);
            if (it != s.rev_preds.end()) {
                for (int pred : it->second) req_wl.insert(pred);
            }
        }
    }

    sta_recompute_max_delay(s, supernodes);
}

void sta_extract_paths_and_criticality(
    STAState& s, const std::vector<SuperNode>& supernodes)
{
    int N = s.num_supernodes;
    s.pair_criticality.clear();
    s.pair_attention.clear();
    std::fill(s.node_criticality.begin(), s.node_criticality.end(), 0);
    s.most_critical_path.clear();

    std::vector<std::pair<int,int>> endpoints;
    endpoints.reserve(N);
    for (int i = 1; i <= N; ++i)
        if (supernodes[i].is_ff && s.arr_time[i] >= 0)
            endpoints.push_back({s.arr_time[i], i});
    std::sort(endpoints.rbegin(), endpoints.rend());

    std::vector<std::pair<int,int>> startpoints;
    startpoints.reserve(N);
    for (int i = 1; i <= N; ++i)
        if (s.Q.count(i) && s.req_time[i] >= 0)
            startpoints.push_back({s.req_time[i], i});
    std::sort(startpoints.rbegin(), startpoints.rend());

    std::vector<std::pair<int, std::vector<int>>> all_paths;

    for (int i = 0; i < std::min(100, (int)endpoints.size()); ++i) {
        int curr = endpoints[i].second;
        std::vector<int> path = {curr};
        curr = s.arr_pi[curr];
        if (curr == -1) continue;
        bool bad = false;
        while (!s.Q.count(curr)) {
            path.push_back(curr);
            curr = s.arr_pi[curr];
            if (curr == -1) { bad = true; break; }
        }
        if (bad) continue;
        path.push_back(curr);
        std::reverse(path.begin(), path.end());
        if (path.size() > 1) all_paths.push_back({endpoints[i].first, path});
    }

    for (int i = 0; i < std::min(100, (int)startpoints.size()); ++i) {
        int curr = startpoints[i].second;
        std::vector<int> path = {curr};
        curr = s.req_pi[curr];
        if (curr == -1) continue;
        bool bad = false;
        while (!supernodes[curr].is_ff) {
            path.push_back(curr);
            curr = s.req_pi[curr];
            if (curr == -1) { bad = true; break; }
        }
        if (bad) continue;
        path.push_back(curr);
        if (path.size() > 1) all_paths.push_back({startpoints[i].first, path});
    }

    std::sort(all_paths.rbegin(), all_paths.rend());
    int max_attention = std::min(200, (int)all_paths.size());
    if (!all_paths.empty()) s.most_critical_path = all_paths[0].second;

    for (int i = 0; i < max_attention; ++i) {
        int attention = max_attention - i;
        const auto& path = all_paths[i].second;
        for (size_t k = 0; k + 1 < path.size(); ++k) {
            int u = path[k], v = path[k+1];
            int pd = 0;
            auto pd_it = s.pair_delay.find(u);
            if (pd_it != s.pair_delay.end()) {
                auto e_it = pd_it->second.find(v);
                if (e_it != pd_it->second.end()) pd = e_it->second;
            }
            s.pair_criticality[u][v] += attention * pd;
            s.pair_attention[u][v] += attention;
        }
    }
    for (const auto& u_pair : s.pair_criticality) {
        for (const auto& v_pair : u_pair.second) {
            s.node_criticality[u_pair.first] += v_pair.second;
            s.node_criticality[v_pair.first] += v_pair.second;
        }
    }
}

struct CeilDSnapshot {
    std::map<std::pair<int,int>, int> ceils;
};

static CeilDSnapshot snapshot_ceil_d(const std::vector<std::vector<int>>& d, int n) {
    CeilDSnapshot snap;
    for (int i = 0; i < n; ++i)
        for (int j = i + 1; j < n; ++j)
            if (d[i][j] > 0)
                snap.ceils[{i, j}] = (int)std::ceil((double)d[i][j] / (double)tmp_ratio);
    return snap;
}

static bool ceil_d_unchanged(
    const CeilDSnapshot& before,
    const std::vector<std::vector<int>>& d_after,
    int n)
{
    for (int i = 0; i < n; ++i) {
        for (int j = i + 1; j < n; ++j) {
            int now = (d_after[i][j] > 0) ? (int)std::ceil((double)d_after[i][j] / (double)tmp_ratio) : 0;
            int was = 0;
            auto it = before.ceils.find({i, j});
            if (it != before.ceils.end()) was = it->second;
            if (now != was) return false;
        }
    }
    return true;
}

PartitionResult refine_partitioning(
    const SNGraph& sn_graph,
    const std::vector<SuperNode>& supernodes,
    int num_supernodes,
    const FPGAGraph& graph,
    int FPGA_capacity,
    PartitionResult current_res,
    int max_rounds,
    int max_fail_streak = 50)
{
    STAState sta;
    sta_init_static(sta, sn_graph, supernodes, num_supernodes);
    sta_run_full(sta, current_res, supernodes);
    sta_extract_paths_and_criticality(sta, supernodes);

    auto node_nets = build_node_to_nets(current_res);

    int current_max_delay = sta.max_delay;
    std::cout << "[ECO] Start Refinement. Initial Delay: " << 2 * current_max_delay
              << " | Rounds: " << max_rounds
              << " | MaxFailStreak: " << max_fail_streak << "\n";

    PartitionResult backup_res = current_res;
    STAState backup_sta = sta;
    int fail_streak = 0;
    std::unordered_set<int> locked_nodes;

    int incremental_count = 0, full_count = 0;

    for (int round = 0; round < max_rounds; ++round) {
        std::cout<<"round: "<<round<<std::endl;

        if (sta.most_critical_path.empty()) {
            std::cout << "  [CritPath @round " << round << "] (empty)\n";
        } else {
            std::cout << "  [CritPath @round " << round << "] nodes (node@FPGA): ";
            for (size_t i = 0; i < sta.most_critical_path.size(); ++i) {
                int nd = sta.most_critical_path[i];
                int fp = current_res.placed_on.count(nd) ? current_res.placed_on.at(nd) : -1;
                if (i) std::cout << " -> ";
                std::cout << nd << "@F" << fp;
                if (supernodes[nd].is_ff) std::cout << "(FF)";
            }
            std::cout << "\n";
        }

        long long max_crit = -1;
        int best_u = -1;
        for (int i = 1; i <= num_supernodes; ++i) {
            if (!locked_nodes.count(i) && sta.node_criticality[i] > max_crit) {
                max_crit = sta.node_criticality[i];
                best_u = i;
            }
        }
        if (best_u == -1 || max_crit <= 0) {
            std::cout << "  Round " << round + 1 << ": no movable node, stop.\n";
            break;
        }
        locked_nodes.insert(best_u);

        std::vector<NodeNetIndex> affected_nets =
            node_nets.count(best_u) ? node_nets[best_u] : std::vector<NodeNetIndex>();
        CeilDSnapshot snap = snapshot_ceil_d(current_res.d, graph.n);

        for (auto& an : affected_nets) {
            NetRoute& nr = current_res.r_star[an.driver_sn][an.net_idx];
            std::set<std::pair<int, int>> used_edges;
            for (auto& sp : nr.sink_paths) {
                const auto& path = sp.second;
                if (path.size() > 1) {
                    for (size_t k = 0; k < path.size() - 1; ++k) {
                        used_edges.insert({std::min(path[k], path[k+1]),
                                           std::max(path[k], path[k+1])});
                    }
                }
            }
            for (auto edge : used_edges) {
                current_res.d[edge.first][edge.second] -= nr.weight;
                current_res.d[edge.second][edge.first] -= nr.weight;
            }
        }
        current_res.fpga_used_weight[current_res.placed_on[best_u]] -= supernodes[best_u].weight;

        std::vector<std::pair<long long, int>> fpga_scores;
        for (int x = 0; x < graph.n; ++x) {
            if (current_res.fpga_used_weight[x] + supernodes[best_u].weight <= FPGA_capacity) {
                long long static_score = 0;
                for (auto& an : affected_nets) {
                    int drv = an.driver_sn;
                    NetRoute& nr = current_res.r_star[drv][an.net_idx];
                    if (drv == best_u) {
                        for (int sink : nr.sinks) {
                            int att = 0;
                            auto pa_it = sta.pair_attention.find(best_u);
                            if (pa_it != sta.pair_attention.end()) {
                                auto e_it = pa_it->second.find(sink);
                                if (e_it != pa_it->second.end()) att = e_it->second;
                            }
                            static_score += (long long)att * graph.dist[x][current_res.placed_on[sink]];
                        }
                    } else {
                        int att = 0;
                        auto pa_it = sta.pair_attention.find(drv);
                        if (pa_it != sta.pair_attention.end()) {
                            auto e_it = pa_it->second.find(best_u);
                            if (e_it != pa_it->second.end()) att = e_it->second;
                        }
                        static_score += (long long)att * graph.dist[current_res.placed_on[drv]][x];
                    }
                }
                fpga_scores.push_back({static_score, x});
            }
        }
        std::sort(fpga_scores.begin(), fpga_scores.end());
        int top_k = std::min(4, (int)fpga_scores.size());

        int best_fpga = (top_k > 0) ? fpga_scores[0].second : 0;
        long long best_total_cost = LLONG_MAX;
        std::vector<std::pair<int, NetRoute>> best_routed_nets;
        std::vector<std::vector<int>> best_d = current_res.d;

        for (int k = 0; k < top_k; ++k) {
            int cand_fpga = fpga_scores[k].second;
            current_res.placed_on[best_u] = cand_fpga;

            std::vector<std::vector<int>> temp_d = current_res.d;
            long long cand_cost = 0;
            std::vector<std::pair<int, NetRoute>> temp_routed_nets;

            for (auto& an : affected_nets) {
                int drv = an.driver_sn;
                NetRoute nr = current_res.r_star[drv][an.net_idx];
                int drv_fpga = current_res.placed_on[drv];

                std::unordered_map<int, long long> sink_fpga_att;
                for (int sink : nr.sinks) {
                    int snk_fpga = current_res.placed_on[sink];
                    if (snk_fpga == drv_fpga) continue;
                    int att = 0;
                    auto pa_it = sta.pair_attention.find(drv);
                    if (pa_it != sta.pair_attention.end()) {
                        auto e_it = pa_it->second.find(sink);
                        if (e_it != pa_it->second.end()) att = e_it->second;
                    }
                    sink_fpga_att[snk_fpga] += att;
                }

                std::vector<std::pair<long long, int>> sorted_sink_fpgas;
                for (auto& sf : sink_fpga_att) {
                    sorted_sink_fpgas.push_back({sf.second, sf.first});
                }
                std::sort(sorted_sink_fpgas.rbegin(), sorted_sink_fpgas.rend());

                std::unordered_set<int> reached_fpgas = {drv_fpga};
                std::unordered_map<int, int> tree_parent;
                std::set<std::pair<int, int>> net_used;

                for (auto& sf : sorted_sink_fpgas) {
                    long long total_att = sf.first;
                    int snk_fpga = sf.second;
                    if (reached_fpgas.count(snk_fpga)) continue;

                    std::vector<int> path;
                    if (total_att > 0) {
                        std::vector<long long> dj_dist(graph.n, LLONG_MAX);
                        std::vector<int> dj_parent(graph.n, -1);
                        std::priority_queue<std::pair<long long, int>,
                            std::vector<std::pair<long long, int>>,
                            std::greater<>> pq;
                        dj_dist[snk_fpga] = 0;
                        pq.push({0, snk_fpga});
                        int meet_node = -1;
                        while (!pq.empty()) {
                            auto [cost, u] = pq.top(); pq.pop();
                            if (cost > dj_dist[u]) continue;
                            if (reached_fpgas.count(u)) { meet_node = u; break; }
                            for (int v : graph.adj[u]) {
                                long long w = (long long)std::ceil((double)(temp_d[u][v] + 1) / (double)tmp_ratio);
                                if (dj_dist[u] + w < dj_dist[v]) {
                                    dj_dist[v] = dj_dist[u] + w;
                                    dj_parent[v] = u;
                                    pq.push({dj_dist[v], v});
                                }
                            }
                        }
                        std::vector<int> seg;
                        for (int curr = meet_node; curr != -1; curr = dj_parent[curr]) seg.push_back(curr);
                        std::vector<int> prefix;
                        int anchor = seg[0];
                        if (anchor != drv_fpga) {
                            int curr = anchor;
                            while (curr != drv_fpga) { prefix.push_back(curr); curr = tree_parent[curr]; }
                            prefix.push_back(drv_fpga);
                            std::reverse(prefix.begin(), prefix.end());
                        } else {
                            prefix.push_back(drv_fpga);
                        }
                        for (size_t s_idx = 1; s_idx < seg.size(); ++s_idx) prefix.push_back(seg[s_idx]);
                        path = prefix;
                    } else {
                        int min_dist_to_snk = INT_MAX;
                        for (int r : reached_fpgas)
                            min_dist_to_snk = std::min(min_dist_to_snk, graph.dist[r][snk_fpga]);
                        std::unordered_set<int> closest_nodes;
                        for (int r : reached_fpgas)
                            if (graph.dist[r][snk_fpga] == min_dist_to_snk) closest_nodes.insert(r);

                        std::vector<long long> sp_cost(graph.n, LLONG_MAX);
                        std::vector<int> sp_parent(graph.n, -1);
                        sp_cost[snk_fpga] = 0;
                        std::priority_queue<std::pair<long long, int>,
                            std::vector<std::pair<long long, int>>,
                            std::greater<>> pq;
                        pq.push({0, snk_fpga});
                        int meet_node = -1;
                        if (reached_fpgas.count(snk_fpga)) {
                            meet_node = snk_fpga;
                        } else {
                            while (!pq.empty()) {
                                auto [cost, u] = pq.top(); pq.pop();
                                if (cost > sp_cost[u]) continue;
                                if (closest_nodes.count(u)) { meet_node = u; break; }
                                for (int v : graph.adj[u]) {
                                    if (graph.dist[snk_fpga][v] == graph.dist[snk_fpga][u] + 1) {
                                        long long w = (long long)std::ceil((double)(temp_d[u][v] + 1) / (double)tmp_ratio);
                                        if (sp_cost[u] + w < sp_cost[v]) {
                                            sp_cost[v] = sp_cost[u] + w;
                                            sp_parent[v] = u;
                                            pq.push({sp_cost[v], v});
                                        }
                                    }
                                }
                            }
                        }
                        std::vector<int> seg;
                        for (int curr = meet_node; curr != -1; curr = sp_parent[curr]) seg.push_back(curr);
                        std::vector<int> prefix;
                        int anchor = seg[0];
                        if (anchor != drv_fpga) {
                            int curr = anchor;
                            while (curr != drv_fpga) { prefix.push_back(curr); curr = tree_parent[curr]; }
                            prefix.push_back(drv_fpga);
                            std::reverse(prefix.begin(), prefix.end());
                        } else {
                            prefix.push_back(drv_fpga);
                        }
                        for (size_t s_idx = 1; s_idx < seg.size(); ++s_idx) prefix.push_back(seg[s_idx]);
                        path = prefix;
                    }

                    for (size_t p = 1; p < path.size(); ++p) {
                        if (!tree_parent.count(path[p])) tree_parent[path[p]] = path[p-1];
                        reached_fpgas.insert(path[p]);
                        std::pair<int, int> edge = {std::min(path[p-1], path[p]), std::max(path[p-1], path[p])};
                        if (net_used.find(edge) == net_used.end()) {
                            net_used.insert(edge);
                            temp_d[edge.first][edge.second] += nr.weight;
                            temp_d[edge.second][edge.first] += nr.weight;
                        }
                    }
                }

                for (int sink : nr.sinks) {
                    int snk_fpga = current_res.placed_on[sink];
                    if (snk_fpga == drv_fpga) {
                        nr.sink_paths[sink] = {drv_fpga};
                        continue;
                    }
                    std::vector<int> path;
                    int curr = snk_fpga;
                    while (curr != drv_fpga) { path.push_back(curr); curr = tree_parent[curr]; }
                    path.push_back(drv_fpga);
                    std::reverse(path.begin(), path.end());
                    nr.sink_paths[sink] = path;

                    int att = 0;
                    auto pa_it = sta.pair_attention.find(drv);
                    if (pa_it != sta.pair_attention.end()) {
                        auto e_it = pa_it->second.find(sink);
                        if (e_it != pa_it->second.end()) att = e_it->second;
                    }
                    int cur_dly = path_delay(path, temp_d);
                    cand_cost += (long long)att * cur_dly;
                }
                temp_routed_nets.push_back({an.net_idx, nr});
            }

            if (cand_cost < best_total_cost) {
                best_total_cost = cand_cost;
                best_fpga = cand_fpga;
                best_routed_nets = temp_routed_nets;
                best_d = temp_d;
            }
        }

        current_res.placed_on[best_u] = best_fpga;
        current_res.fpga_used_weight[best_fpga] += supernodes[best_u].weight;
        current_res.d = best_d;
        for (size_t i = 0; i < affected_nets.size(); ++i) {
            int drv = affected_nets[i].driver_sn;
            int ni  = best_routed_nets[i].first;
            current_res.r_star[drv][ni] = best_routed_nets[i].second;
        }

        bool fast_ok = ceil_d_unchanged(snap, current_res.d, graph.n);
        if (fast_ok) {
            sta_run_incremental(sta, current_res, affected_nets, supernodes);
            incremental_count++;
        } else {
            sta_run_full(sta, current_res, supernodes);
            full_count++;
        }
        sta_extract_paths_and_criticality(sta, supernodes);
        int new_max_delay = sta.max_delay;

        if (new_max_delay < current_max_delay) {
            std::cout << "  Round " << round + 1
                      << " [" << (fast_ok ? "INC" : "FULL") << "]"
                      << ": Accept! Delay " << 2 * current_max_delay
                      << " -> " << 2 * new_max_delay << "\n";
            current_max_delay = new_max_delay;
            backup_res = current_res;
            backup_sta = sta;
            fail_streak = 0;
        } else {
            fail_streak++;
            std::cout << "  Round " << round + 1
                      << " [" << (fast_ok ? "INC" : "FULL") << "]"
                      << ": No improvement (new=" << 2 * new_max_delay
                      << " >= best=" << 2 * current_max_delay << "). fail_streak="
                      << fail_streak << "/" << max_fail_streak << "\n";
            if (fail_streak >= max_fail_streak) {
                std::cout << "  Round " << round + 1 << ": fail_streak limit, stop.\n";
                break;
            }
        }
    }

    std::cout << "[ECO] STA mode counts: incremental=" << incremental_count
              << " full=" << full_count << "\n";

    current_res = std::move(backup_res);
    return current_res;
}

int main(int argc, char* argv[]) {

    if (argc < 2) {
        std::cerr << "Usage: " << argv[0] << " <dataset_name>\n";
        std::cerr << "Example: " << argv[0] << " openCV\n";
        exit(1);
    }
    std::string name = argv[1];
    std::string hg_file = "./dataset/titan23/" + name + "/" + name + "_stratixiv_arch_timing.hgr";
    std::string ff_file = "./dataset/titan23/" + name + "/" + name + "_stratixiv_arch_timing_ff.txt";

    HyperGraph hg = read_hypergraph(hg_file, ff_file);
    std::cout << "Nodes: " << hg.n << ", Hyperedges: " << hg.m << "\n";
    std::cout << "Flip-flops: " << hg.flip_flops.size() << "\n";

    std::vector<int> init_depth = compute_depth_initial(hg);
    int max_depth = *std::max_element(init_depth.begin() + 1, init_depth.end());
    std::cout << "Max depth: " << max_depth << "\n";

    std::vector<SuperNode> supernodes = build_initial_supernodes(hg);
    SNGraph sn_graph = build_initial_sn_graph(hg);
    int num_supernodes = hg.n;

    long long initial_2pin_nets = 0;
    for (const auto& pair : sn_graph) {
        for (const auto& net : pair.second) {
            initial_2pin_nets += net.sinks.size();
        }
    }
    std::cout << "[Info] Total driver-sink pairs: " << initial_2pin_nets << "\n";

    FPGAGraph graph;
    if (!graph.load("./dataset/FPGA_Graph/MFS2")) {
        return 1;
    }
    graph.analyze();
    int FPGA_number = graph.n;
    int FPGA_capacity = (int)std::ceil(2 * num_supernodes / FPGA_number);
    std::cout<<"FPGA capacity:"<<FPGA_capacity<<std::endl;

    std::clock_t start_time = std::clock();
    std::cout << "\n==================================================\n";
    std::cout << "STAGE 1: Initial Solution Generation (partitioning + routing)\n";
    std::cout << "==================================================\n";
    PartitionResult init_res = initial_partitioning(
        sn_graph, supernodes, num_supernodes, graph, FPGA_capacity);

    int init_delay = compute_critical_path_delay(
        sn_graph, supernodes, num_supernodes, init_res);
    std::cout << "[Info] Initial critical path delay: " << 2 * init_delay << "\n";

    std::cout << "\n==================================================\n";
    std::cout << "STAGE 2: Criticality-Driven Refinement\n";
    std::cout << "==================================================\n";
    PartitionResult current_res = refine_partitioning(
        sn_graph, supernodes, num_supernodes, graph, FPGA_capacity, init_res, 500);

    std::clock_t end_time = std::clock();
    double cpu_time_used = static_cast<double>(end_time - start_time) / CLOCKS_PER_SEC;
    std::cout << "\nRunning time: " << cpu_time_used << " s\n";

    std::cout << "\n=== Final Critical Path Delay ===\n";
    compute_critical_path_delay(
        sn_graph, supernodes, num_supernodes, current_res);

    std::cout << "\n=== Final FPGA Interconnect Usage (res.d non-zero entries) ===\n";
    long long total_consumption = 0;
    for (int i = 0; i < graph.n; ++i) {
        for (int j = i + 1; j < graph.n; ++j) {
            if (current_res.d[i][j] != 0) {
                std::cout << "FPGA " << i << " <-> FPGA " << j
                          << ": " << current_res.d[i][j] << "\n";
                total_consumption += current_res.d[i][j];
            }
        }
    }
    std::cout << "Total interconnect consumption: " << total_consumption << "\n";

    std::cout << "\n=== Final FPGA Weight Distribution ===\n";
    for (int f = 0; f < graph.n; ++f) {
        std::cout << "FPGA " << f << ": " << current_res.fpga_used_weight[f]
                  << " / " << FPGA_capacity << "\n";
    }
    return 0;
}
