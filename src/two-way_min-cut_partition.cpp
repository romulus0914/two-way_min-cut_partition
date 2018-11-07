#include <iostream>
#include <fstream>
#include <vector>
#include <unordered_map>
#include <unordered_set>
#include <string>

#include <cmath>
#include <ctime>

using namespace std;

// area of each cell
vector<int> cells_area;
// map cell name to its id
unordered_map<string, int> cells_id;
// map id to its cell name
vector<string> cells_name;

// # cells
int num_cells;
// cell array
vector<unordered_set<int>> cells;
// # nets
int num_nets;
// net array
vector<unordered_set<int>> nets;

int total_area, A_area, B_area;
// |A - B| < n / 10
int area_constraint;
// max gain
int p_max;

// two-way partition
unordered_set<int> A, B;
// block each cell belongs to
vector<int> cells_block;
// nets distribution, A=0, B=1
vector<vector<int>> nets_distribution;
// gain of each cell
vector<int> cells_gain;

void ReadCellsFile(string filename)
{
    ifstream file;
    file.open(filename);

    string cell;
    int area;
    num_cells = 0;
    while (file >> cell >> area) {
        cells_area.emplace_back(area);
        total_area += area;
        cells_id[cell] = num_cells++;
        cells_name.emplace_back(cell);
    }

    area_constraint = total_area / 10;
    file.close();
}

void ReadNetsFile(string filename)
{
    ifstream file;
    file.open(filename);

    cells.insert(cells.begin(), num_cells, unordered_set<int>());
    nets.emplace_back(unordered_set<int>());

    num_nets = 1;
    string temp0, temp1, temp2, str;
    while (file >> temp0 >> temp1 >> temp2 >> str) {
        unordered_set<int> temp;
        while (str != "}") {
            int cell_id = cells_id[str];
            temp.insert(cell_id);
            cells[cell_id].insert(num_nets);
            file >> str;
        }
        nets.emplace_back(temp);
        num_nets++;
    }

    p_max = 0;
    int size = cells.size();
    for (int i = 0; i < size; i++) {
        int p = cells[i].size();
        if (p > p_max)
            p_max = p;
    }

    file.close();
}

void InitialCut()
{
    vector<int> temp(2, 0);
    for (int i = 0; i < num_nets; i++)
        nets_distribution.emplace_back(temp);

    A_area = 0;
    int min_area_diff = total_area;
    for (int i = 0; i < num_cells; i++) {
        int area_diff = abs(total_area - 2 * (A_area + cells_area[i]));
        if (area_diff < min_area_diff) {
            min_area_diff = area_diff;
            A_area += cells_area[i];
            A.insert(i);
            for (int j : cells[i])
                nets_distribution[j][0]++;
        }
        if (area_diff == 0)
            break;
    }

    B_area = total_area - A_area;
    cells_block.insert(cells_block.begin(), num_cells, 0);

    for (int i = 0; i < num_cells; i++) {
        if (A.find(i) == A.end()) {
            B.insert(i);
            cells_block[i] = 1;
            for (int j : cells[i])
                nets_distribution[j][1]++;
        }
    }
}

int InitialGain(vector<unordered_set<int>> &gain_bucket)
{
    cells_gain = vector<int>();
    int max_gain = -1;
    for (int i = 0; i < num_cells; i++) {
        int g = 0;
        int block = A.find(i) != A.end() ? 0 : 1;

        for (int j : cells[i]) {
            // if F(n) = 1, g = g + 1
            if (nets_distribution[j][block] == 1)
                g++;
            // if T(n) = 0, g = g - 1
            if (nets_distribution[j][1 - block] == 0)
                g--;
        }

        g += p_max;
        if (g > max_gain)
            max_gain = g;
        gain_bucket[g].insert(i);
        cells_gain.emplace_back(g);
    }

    return max_gain;
}

void UpdateGain(int base_cell, vector<int> &cells_lock_, 
                unordered_set<int> &A_, unordered_set<int> &B_, vector<vector<int>> &nets_distribution_,
                vector<unordered_set<int>> &gain_bucket_, vector<int> &cells_gain_)
{
    // Front block
    int F = A.find(base_cell) != A.end() ? 0 : 1;
    unordered_set<int> &F_block = F == 0 ? A_ : B_;
    // To block
    int T = 1 - F;
    unordered_set<int> &T_block = T == 1 ? B_ : A_;

    // lock the base cell and complement its block
    gain_bucket_[cells_gain_[base_cell]].erase(base_cell);
    cells_lock_[base_cell] = 1;
    F_block.erase(base_cell);
    T_block.insert(base_cell);

    for (int n : cells[base_cell]) {
        if (nets_distribution_[n][T] == 0) {
            for (int c : nets[n]) {
                if (cells_lock_[c] != 1) {
                    gain_bucket_[cells_gain_[c]++].erase(c);
                    gain_bucket_[cells_gain_[c]].insert(c);
                }
            }
        }
        else if (nets_distribution_[n][T] == 1) {
            for (int c : nets[n]) {
                if (T_block.find(c) != T_block.end() && cells_lock_[c] != 1) {
                    gain_bucket_[cells_gain_[c]--].erase(c);
                    gain_bucket_[cells_gain_[c]].insert(c);
                }
            }
        }

        nets_distribution_[n][F]--;
        nets_distribution_[n][T]++;

        if (nets_distribution_[n][F] == 0) {
            for (int c : nets[n]) {
                if (cells_lock_[c] != 1) {
                    gain_bucket_[cells_gain_[c]--].erase(c);
                    gain_bucket_[cells_gain_[c]].insert(c);
                }
            }
        }
        else if (nets_distribution_[n][F] == 1) {
            for (int c : nets[n]) {
                if (F_block.find(c) != F_block.end() && cells_lock_[c] != 1) {
                    gain_bucket_[cells_gain_[c]++].erase(c);
                    gain_bucket_[cells_gain_[c]].insert(c);
                }
            }
        }
    }
}

void Iteration(int max_gain, vector<unordered_set<int>> &gain_bucket)
{
    // maximum partial sum of gains
    int G = 0;

    do {
        unordered_set<int> A_temp(A);
        unordered_set<int> B_temp(B);
        vector<vector<int>> nets_distribution_temp = nets_distribution;
        vector<unordered_set<int>> gain_bucket_temp = gain_bucket;
        vector<int> cells_gain_temp(cells_gain);
        // cell lock
        vector<int> cells_lock(num_cells, 0);
        vector<int> cells_lock_temp(num_cells, 0);
        vector<int> cells_block_temp = cells_block;

        int A_area_temp = A_area, B_area_temp = B_area;

        // gain of each move
        vector<int> gains;
        // area difference after each move
        vector<int> area_diffs;
        // record move cells
        vector<int> moved_cells;
        // record max gains
        vector<int> max_gains;

        // total # cells moves
        for (int i = 0; i < num_cells; i++) {
            int base_cell = -1;
            int min_area_diff = total_area;
            while (base_cell == -1) {
                min_area_diff = total_area;
                int area_diff;
			    for (int j : gain_bucket_temp[max_gain]) {
                    if (cells_block_temp[j] == 0)
                        area_diff = abs((A_area_temp - cells_area[j]) - (B_area_temp + cells_area[j]));
                    else
                        area_diff = abs((A_area_temp + cells_area[j]) - (B_area_temp - cells_area[j]));

                    if (area_diff < area_constraint && area_diff < min_area_diff) {
                        min_area_diff = area_diff;
                        base_cell = j;
                    }
                }

                if (max_gain == 0 || base_cell != -1)
                    break;

                max_gain--;
            }

            if (base_cell == -1)
                break;

            // shift back to original distribution (-pmax ~ pmax)
            gains.emplace_back(max_gain - p_max);
            area_diffs.emplace_back(min_area_diff);
            moved_cells.emplace_back(base_cell);

            UpdateGain(base_cell, cells_lock_temp, A_temp, B_temp, nets_distribution_temp, gain_bucket_temp, cells_gain_temp);

            if (cells_block_temp[base_cell] == 0) {
                A_area_temp -= cells_area[base_cell];
                B_area_temp += cells_area[base_cell];
            }
            else {
                A_area_temp += cells_area[base_cell];
                B_area_temp -= cells_area[base_cell];
            }
            cells_block_temp[base_cell] = 1 - cells_block_temp[base_cell];

            for (int j = p_max * 2; j >= 0; j--) {
                if (gain_bucket_temp[j].size() != 0) {
                    max_gain = j;
                    break;
                }
            }
        }

        G = -p_max - 1;
        int num_moves = -1, partial_sum = 0;
        int size = gains.size();
        for (int i = 0; i < size; i++) {
            partial_sum += gains[i];
            if (partial_sum > G) {
                G = partial_sum;
                num_moves = i;
            }
            else if (partial_sum == G) {
                if (area_diffs[i] < area_diffs[num_moves])
                    num_moves = i;
            }
        }
        num_moves++;

        if (G <= 0)
            break;

        for (int i = 0; i < num_moves; i++) {
            int base_cell = moved_cells[i];

            UpdateGain(base_cell, cells_lock, A, B, nets_distribution, gain_bucket, cells_gain);

            // complement base cell block and update A, B area
            if (cells_block[base_cell] == 0) {
                A_area -= cells_area[base_cell];
                B_area += cells_area[base_cell];
            }
            else {
                A_area += cells_area[base_cell];
                B_area -= cells_area[base_cell];
            }
            cells_block[base_cell] = 1 - cells_block[base_cell];
        }

        max_gain = InitialGain(gain_bucket);
    } while (G > 0);
}

void Output(string filename)
{
    ofstream file;
    file.open(filename);

    int cut = 0;
    for (int i = 0; i < num_nets; i++)
        if (nets_distribution[i][0] != 0 && nets_distribution[i][1] != 0)
            cut++;

    file << "cut_size " << cut << '\n';

    file << "A " << A.size() << '\n';
    for (int c : A)
        file << cells_name[c] << '\n';
    file << "B " << B.size() << '\n';
    for (int c : B)
        file << cells_name[c] << '\n';

    file.close();
}

int main(int argc, char **argv)
{
    if (argc < 4) {
        cout << "Usage: \n";
        cout << "  ./two-way_min-cut_partition <path/to/cells_file> <path/to/nets_file> <path/to/output_file>\n";
        exit(1);
    }
    string cells_file = argv[1];
    string nets_file = argv[2];
    string outfile = argv[3];

    clock_t t0, t1, t2, t3;
    t0 = clock();

    ReadCellsFile(cells_file);
    ReadNetsFile(nets_file);
    
    t1 = clock();

    InitialCut();

    vector<unordered_set<int>> gain_bucket(p_max * 2 + 1);
    int max_gain = InitialGain(gain_bucket);

    Iteration(max_gain, gain_bucket);

    t2 = clock();

    Output(outfile);

    t3 = clock();
    cout << "IO time: " << (float)((t3 - t2) + (t1 - t0)) / CLOCKS_PER_SEC << '\n';
    cout << "FM time: " << (float)(t2 - t1) / CLOCKS_PER_SEC << '\n';
}
