#include <csignal>
#include <cstddef>
#include <fstream>
#include <iostream>
#include <list>
#include <string>
#include <tuple>
#include <type_traits>
#include <vector>

#include <boost/algorithm/string.hpp>

using namespace boost::algorithm;
using namespace std;

// var num, is_pos, clause num, is_watched
using ClauseType = tuple<int, int, int, int>;
// Clause num, pointer to clause, pointer to literal, is_assigned, value
using VarType = tuple<int, list<ClauseType> *, ClauseType *>;
using BCPVarsType = tuple<int, list<tuple<list<ClauseType> *, ClauseType *>>,
                          list<tuple<list<ClauseType> *, ClauseType *>>>;
// TODO: If unique values could use set for a better search
using BCPClauseType = vector<int>;
// var_num, val(2 if unassigned), is_unit, pointers to clause_list
using SetVarsType = tuple<int, int, int, list<int *>, list<int *>>;
typedef struct TermList {
  vector<list<ClauseType>> clauses;
  vector<list<VarType>> variables;
  vector<SetVarsType> set_vars;
  vector<int> is_unit;
  // vector<int[3]> clause_list;
} TermList;

int num_vars = 0;
int num_clauses = 0;
int verbose = 0;

void print_table(TermList *terms) {
  cout << "Clauses" << endl;
  for (auto const &i : terms->clauses) {
    for (auto const &j : i) {
      cout << get<1>(j) << " ";
    }
    cout << endl;
  }

  cout << "Variables" << endl;
  for (auto const &i : terms->variables) {
    for (auto const &j : i) {
      cout << get<1>(j) << " ";
    }
    cout << endl;
  }
  cout << endl;
}

void print_bcp(vector<BCPVarsType> *bcp_vars, vector<SetVarsType> *set_vars,
               vector<BCPClauseType> *bcp_clauses) {
  cout << "BCP Vars" << endl;
  int n = 1;
  for (auto &i : *bcp_vars) {
    cout << "Var: " << n << endl;
    // cout << "Value: " << get<0>(i) << endl;
    cout << "Value: " << get<1>((*set_vars)[n - 1]) << endl;
    cout << "Pos Clause Watched: ";
    for (auto const &term : get<1>(i)) {
      cout << get<2>(*get<1>(term)) << " ";
      // cout << term << " ";
    }
    cout << endl << "Neg Clause Watched: ";
    for (auto const &term : get<2>(i)) {
      cout << get<2>(*get<1>(term)) << " ";
      // cout << term << " ";
    }
    cout << endl;
    n++;
  }
  cout << "BCP Clauses" << endl;
  for (int i = 0; i < num_clauses; i++) {
    cout << "Clause " << i << ": ";
    BCPClauseType clause = (*bcp_clauses)[i];
    for (int j = 0; j < 2; j++) {
      cout << clause[j] << " ";
    }
    cout << endl;
  }
}

TermList read_terms(string file_name) {
  string lines = "";
  TermList terms;
  // open(file, 'r') as f:
  std::ifstream file;
  file.open(file_name);

  vector<string> line;
  string raw_line;
  getline(file, raw_line);
  trim(raw_line);
  split(line, raw_line, boost::is_any_of(" "));
  while (line[0] != "p") {
    getline(file, raw_line);
    trim(raw_line);
    split(line, raw_line, boost::is_any_of(" "));
  }

  trim(line[2]);
  trim(line[3]);
  num_vars = stoi(line[2]);
  if (line[3] == "") {
    num_clauses = stoi(line[4]);
  } else {
    num_clauses = stoi(line[3]);
  }

  terms.clauses.resize(num_clauses);
  terms.variables.resize(num_vars);
  terms.set_vars.resize(num_vars);
  terms.is_unit.resize(num_clauses);
  // terms.clause_list.resize(num_clauses);

  for (int i = 0; i < num_clauses; i++) {
    getline(file, raw_line);
    trim(raw_line);
    if (raw_line == "%" || raw_line == "0")
      continue;
    split(line, raw_line, boost::is_any_of(" "));
    for (auto &v : line) {
      trim(v);
      int var = stoi(v);
      if (var == 0)
        break;
      int is_pos = 1;
      if (var < 0) {
        is_pos = 0;
        var = abs(var);
      }

      terms.clauses[i].push_back(make_tuple(var, is_pos, i, 0));
      terms.variables[var - 1].push_back(
          make_tuple(i, &terms.clauses[i], &terms.clauses[i].back()));
      get<0>(terms.set_vars[var - 1]) = var;
      get<1>(terms.set_vars[var - 1]) = 2;
      get<2>(terms.set_vars[var - 1]) = 0;
      // if (is_pos == 1) {
      //   get<3>(terms.set_vars[var - 1]).push_back(terms.clause_list[i]);
      // } else {
      //   get<4>(terms.set_vars[var - 1]).push_back(terms.clause_list[i]);
      // }
      //  print_table(&terms);
    }
    // terms.clause_list[i][0] = terms.clauses[i].size();
    // terms.clause_list[i][1] = 0;
    // terms.clause_list[i][2] = 0;
  }

  terms.set_vars.resize(num_vars);

  return terms;
}

int unit_prop(vector<BCPVarsType> *bcp_vars, vector<BCPClauseType> *bcp_clauses,
              TermList *terms, int assign_var, int assign_val) {
  if (verbose) {
    cout << "----------------------------------" << endl;
    if (assign_val != -1) {
      cout << "Assigning to var " << assign_var << " value " << assign_val
           << endl;
    }
    // print_table(&terms);
    print_bcp(bcp_vars, &terms->set_vars, bcp_clauses);
  }
  /*
  list<tuple<list<ClauseType> *, ClauseType *>> *neg_list;
  if (assign_val == 1) {
    neg_list = &get<2>((*bcp_vars)[assign_var - 1]);
  } else if (assign_val == 0) {
    neg_list = &get<1>((*bcp_vars)[assign_var - 1]);
  }
  */

  list<tuple<list<ClauseType> *, ClauseType *>> *pos_list;
  list<tuple<list<ClauseType> *, ClauseType *>> *neg_list;
  if (assign_val == 1) {
    neg_list = &get<2>((*bcp_vars)[assign_var - 1]);
    pos_list = &get<1>((*bcp_vars)[assign_var - 1]);
  } else if (assign_val == 0) {
    neg_list = &get<1>((*bcp_vars)[assign_var - 1]);
    pos_list = &get<2>((*bcp_vars)[assign_var - 1]);
  }
  for (auto &clause_tup : *pos_list) {
    ClauseType *lit = get<1>(clause_tup);
    int clause_idx = get<2>(*lit);
    if (verbose) {
      cout << "Becoming Unit" << endl;
      cout << "Variable: " << assign_var << endl;
      cout << "Clause " << clause_idx << " is unit" << endl;
      cout << "Assigning value: " << get<1>(*lit) << endl;
      cout << "Unit Array Before: [";
      for (auto const &unit : terms->is_unit)
        cout << unit << " ";
      cout << "]" << endl;
    }
    terms->is_unit[clause_idx] = 1;
    if (verbose) {
      cout << "Unit Array After:  [";
      for (auto const &unit : terms->is_unit)
        cout << unit << " ";
      cout << "]" << endl;
    }
  }

  list<tuple<list<ClauseType> *, ClauseType *>> rem_list;
  rem_list.resize(neg_list->size());
  for (auto &clause_tup : *neg_list) {
    list<ClauseType> *clause = get<0>(clause_tup);
    ClauseType *literal = get<1>(clause_tup);
    list<tuple<int, ClauseType *>> lit_unassigned;
    list<tuple<int, ClauseType *>> lit_one_value;
    list<tuple<int, ClauseType *>> lit_zero_value;
    int clause_idx = get<2>(*literal);
    // Unit clause
    for (ClauseType &lit : *clause) {
      int var_idx = get<0>(lit) - 1;
      if (get<1>(terms->set_vars[var_idx]) == 2) {
        lit_unassigned.push_back(make_tuple(var_idx, &lit));
      } else {
        if (get<1>(terms->set_vars[var_idx]) == get<1>(lit)) {
          // terms->is_unit[get<2>(lit)] = 1;
          lit_one_value.push_back(make_tuple(var_idx, &lit));
        } else {
          lit_zero_value.push_back(make_tuple(var_idx, &lit));
        }
        // lit_assigned.push_back(make_tuple(var_idx, &lit));
      }
    }

    /*
    int is_watcher_one = 0;
    for (auto &var : (*bcp_clauses)[clause_idx]) {
      for (auto &lit : *clause) {
        if (get<1>(terms->set_vars[var - 1]) == get<1>(lit)) {
          is_watcher_one = 1;
        }
      }
    }
else if (is_watcher_one == 1) {
      terms->is_unit[get<2>(*literal)] = 1;
      // int var_idx = get<0>(lit_one_value.front());
      if (verbose) {
        cout << "Already Unit" << endl;
        // cout << "Var: " << var_idx + 1 << endl;
        cout << "Clause " << get<2>(*literal) << " is unit" << endl;
        cout << "Unit Array: [";
        for (auto const &unit : terms->is_unit)
          cout << unit << " ";
        cout << "]" << endl << endl;
      }
    }

    */
    if (lit_one_value.size() > 0) {
      terms->is_unit[get<2>(*literal)] = 1;
      int var_idx = get<0>(lit_one_value.front());
      if (verbose) {
        cout << "Already Unit" << endl;
        cout << "Var: " << var_idx + 1 << endl;
        cout << "Clause " << get<2>(*literal) << " is unit" << endl;
        cout << "Unit Array: [";
        for (auto const &unit : terms->is_unit)
          cout << unit << " ";
        cout << "]" << endl << endl;
      }
    } else if (lit_unassigned.size() >= 2) {
      BCPClauseType *curr_bcp_clause = &(*bcp_clauses)[clause_idx];
      ClauseType *lit = get<1>(lit_unassigned.front());
      int var_idx = get<0>(lit_unassigned.front());
      if (find(curr_bcp_clause->begin(), curr_bcp_clause->end(), var_idx + 1) !=
          curr_bcp_clause->end()) {
        auto lit_it = lit_unassigned.begin();
        advance(lit_it, 1);
        lit = get<1>(*lit_it);
        var_idx = get<0>(*lit_it);
      }
      list<tuple<list<ClauseType> *, ClauseType *>> *curr_list;
      int is_pos = get<1>(*lit);
      if (verbose) {
        cout << "Switching Watch Vars" << endl;
        cout << "Var: " << var_idx + 1 << endl;
        cout << "Reassigning clause " << get<2>(*literal) << endl << endl;
      }
      if (is_pos == 1) {
        curr_list = &get<1>((*bcp_vars)[var_idx]);
      } else if (is_pos == 0) {
        curr_list = &get<2>((*bcp_vars)[var_idx]);
      }
      replace(curr_bcp_clause->begin(), curr_bcp_clause->end(), assign_var,
              var_idx + 1);

      curr_list->push_back(make_tuple(clause, lit));
      rem_list.push_back(clause_tup);
    } else if (lit_unassigned.size() == 1) {
      ClauseType *lit = get<1>(lit_unassigned.front());
      int var_idx = get<0>(lit_unassigned.front());
      // get<2>((*bcp_vars)[assign_var - 1])
      //  Unit clause
      if (verbose) {
        cout << "Becoming Unit" << endl;
        cout << "Variable: " << var_idx + 1 << endl;
        cout << "Clause " << get<2>(*literal) << " is unit" << endl;
        cout << "Assigning value: " << get<1>(*lit) << endl;
        cout << "Unit Array: [";
        for (auto const &unit : terms->is_unit)
          cout << unit << " ";
        cout << "]" << endl;
      }

      get<1>(terms->set_vars[var_idx]) = get<1>(*lit);
      terms->is_unit[get<2>(*literal)] = 1;
      if (verbose)
        cout << "Propagating" << endl << endl;
      int prop = unit_prop(bcp_vars, bcp_clauses, terms, var_idx + 1,
                           get<1>(terms->set_vars[var_idx]));
      if (prop == 0)
        return 0;
      // list<tuple<list<ClauseType> *, ClauseType *>> *pos_unit_list;
      // if (assign_val == get<1>(*lit)) {
      //  cout << "It's the positive list!" << endl;
      //  pos_unit_list = &get<1>((*bcp_vars)[var_idx]);
      //} else {
      //  cout << "It's the negative list!" << endl;
      //  pos_unit_list = &get<2>((*bcp_vars)[var_idx]);
      //}

      // for (auto &clause_unit_tup : *pos_unit_list) {
      //   ClauseType *unit_lit = get<1>(clause_unit_tup);
      //   int unit_idx = get<2>(*unit_lit);
      //   cout << "Unit IDX: " << unit_idx << endl;
      //   terms->is_unit[unit_idx] = 1;
      // }
    } else if (lit_unassigned.size() == 0) {
      if (verbose) {
        cout << "Conflict" << endl;
        cout << "Clause " << get<2>(*literal) << " is unit" << endl;
        cout << "Unit Array: [";
        for (auto const &unit : terms->is_unit)
          cout << unit << " ";
        cout << "Backtracking" << endl << endl;
      }
      return 0;
    }
  }
  for (auto &i : rem_list) {
    remove(neg_list->begin(), neg_list->end(), i);
  }

  return 1;
}

int DPLL(vector<BCPVarsType> *bcp_vars, vector<BCPClauseType> *bcp_clauses,
         TermList terms, int assign_var, int assign_val) {
  // cout << "----------------------------------" << endl;
  // if (assign_val != -1) {
  //   cout << "Assigning to var " << assign_var << " value " << assign_val
  //        << endl;
  // }

  // if (verbose) {
  //   // print_table(&terms);
  //   print_bcp(bcp_vars, &terms.set_vars, bcp_clauses);
  // }

  if (assign_val != -1) {
    int prop = unit_prop(bcp_vars, bcp_clauses, &terms, assign_var, assign_val);
    if (prop == 0)
      return 0;
  }

  int is_unit = 1;
  for (auto &var : terms.is_unit) {
    if (var == 0) {
      is_unit = 0;
      break;
    }
  }
  if (is_unit == 1)
    return 1;

  if (verbose) {
    cout << "After bcp" << endl;
    // print_table(&terms);
    print_bcp(bcp_vars, &terms.set_vars, bcp_clauses);
  }

  /*
  long unsigned int neg_num_clauses = 0;
  int neg_var_num = -1;
  long unsigned int pos_num_clauses = 0;
  int pos_var_num = -1;
  for (int i = 0; i < num_vars; i++) {
    BCPVarsType bcp = (*bcp_vars)[i];
    // long unsigned int bcp_size = ;
    // cout << bcp_size << endl;
    //  if (get<1>(terms.set_vars[i]) == 2 && bcp_size > num_clauses) {
    if (get<1>(terms.set_vars[i]) == 2) {
      if (get<2>(bcp).size() > neg_num_clauses) {
        neg_num_clauses = get<2>(bcp).size();
        neg_var_num = i + 1;
      }
      if (get<1>(bcp).size() > pos_num_clauses) {
        pos_num_clauses = get<1>(bcp).size();
        pos_var_num = i + 1;
      }
    }
  }
*/
  long unsigned int num_clauses = 0;
  int var_num = -1;
  for (int i = 0; i < num_vars; i++) {
    BCPVarsType bcp = (*bcp_vars)[i];
    long unsigned int bcp_size = get<1>(bcp).size() + get<2>(bcp).size();
    if (get<1>(terms.set_vars[i]) == 2 && bcp_size > num_clauses) {
      // if (bcp_size > num_clauses) {
      num_clauses = bcp_size;
      var_num = i + 1;
    }
  }

  if (verbose) {
    cout << "Unit Array Post BCP: [";
    for (auto const &unit : terms.is_unit)
      cout << unit << " ";
    cout << "]" << endl;
    cout << "----------------------------------" << endl;
  }

  if (var_num == -1) {
    if (verbose)
      cout << "Patching solution" << endl;
    for (long unsigned int i = 0; i < terms.is_unit.size(); i++) {
      if (terms.is_unit[i] == 0) {
        // cout << "Fixing index: " << i;
        int is_unit = 0;
        for (auto &lit : terms.clauses[i]) {
          int var_idx = get<0>(lit) - 1;
          if (get<1>(terms.set_vars[var_idx]) == get<1>(lit)) {
            is_unit = 1;
          }
        }
        if (is_unit == 0) {
          cout << "Backtracking" << endl;
          return 0;
        }
        // cout << "Issue with index " << i << endl;
      }
    }
    return 1;
  }

  get<1>(terms.set_vars[var_num - 1]) = 1;
  // cout << "Neg Num Clauses: " << neg_num_clauses << endl;
  // cout << "Pos Num Clauses: " << pos_num_clauses << endl;
  // int prev_val = get<1>(terms.set_vars[neg_var_num - 1]);
  // get<1>(terms.set_vars[neg_var_num - 1]) = 1;
  // if (neg_num_clauses > 0 &&
  // DPLL(bcp_vars, bcp_clauses, terms, neg_var_num, 1) == 1) {
  if (DPLL(bcp_vars, bcp_clauses, terms, var_num, 1) == 1) {
    // for (long unsigned int i = 0; i < terms.is_unit.size(); i++) {
    //   int is_unit = 0;
    //   for (auto &lit : terms.clauses[i]) {
    //     int var_idx = get<0>(lit) - 1;
    //     if (get<1>(terms.set_vars[var_idx]) == get<1>(lit)) {
    //       is_unit = 1;
    //     }
    //     if (is_unit == 0)
    //       cout << "Issue with index " << i << endl;
    //   }
    // }
    return 1;
  } else {
    /*
    get<1>(terms.set_vars[neg_var_num - 1]) = prev_val;

    if (pos_num_clauses == 0) {
      cout << "Backtracking" << endl;
      return 0;
    }
    get<1>(terms.set_vars[pos_var_num - 1]) = 0;
    return DPLL(bcp_vars, bcp_clauses, terms, pos_var_num, 0);
    */
    get<1>(terms.set_vars[var_num - 1]) = 0;
    return DPLL(bcp_vars, bcp_clauses, terms, var_num, 0);
  }
}

int main(int argc, char *argv[]) {
  if (argc == 1) {
    cerr << "Please input a file" << endl;
    return 1;
  }

  std::string file;
  if (strcmp(argv[1], "-l") == 0) {
    verbose = 1;
    file = argv[2];
  } else {
    file = argv[1];
  }

  cout << "Input file: " << file << endl;

  TermList terms = read_terms(file);

  vector<BCPVarsType> bcp_vars;
  vector<BCPClauseType> bcp_clauses;
  bcp_vars.resize(num_vars);
  bcp_clauses.resize(num_clauses);

  for (auto &var : bcp_vars) {
    get<0>(var) = 2;
  }

  // vector<int[3]> clause_vals;
  // clause_vals.resize(num_clauses);
  int idx = 0;
  for (auto &clause : terms.clauses) {
    // clause_vals[idx][0] = int(clause.size());
    bcp_clauses[idx].resize(2);
    int idx2 = 0;
    for_each_n(clause.begin(), min(2, int(clause.size())),
               [&bcp_clauses, &bcp_vars, &clause, &idx, &idx2](auto &i) {
                 ClauseType *curr_clause = &i;
                 int var_idx = get<0>(*curr_clause);
                 bcp_clauses[idx][idx2] = var_idx;
                 auto var_tup = &bcp_vars[var_idx - 1];
                 int is_pos = get<1>(*curr_clause);
                 if (is_pos == 1) {
                   get<1>(*var_tup).push_back(make_tuple(&clause, curr_clause));
                 } else {
                   get<2>(*var_tup).push_back(make_tuple(&clause, curr_clause));
                 }
                 idx2++;
               });
    idx++;
  }

  if (verbose) {
    print_table(&terms);
  }
  int sat = DPLL(&bcp_vars, &bcp_clauses, terms, 0, -1);
  if (sat == 1) {
    cout << "This is satisfiable" << endl << endl;
  } else {
    cout << "This is not satisfiable" << endl << endl;
  }

  return 0;
}
