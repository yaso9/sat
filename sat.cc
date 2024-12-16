#include <list>
#include <cassert>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <optional>
#include <sstream>
#include <algorithm>
#include <string>
#include <vector>

using Var = std::uint16_t;

struct Literal {
  Var var;
  bool negated;
};

class Clause {
public:
  std::vector<Literal> lits;

  Clause() {}

  Clause(Clause &&c) : lits(std::move(c.lits)) {}

  void clear() {
    lits.clear();
  }

  void addLiteral(std::uint16_t var, bool negated) {
    lits.push_back({var, negated});
  }
};

class CNF {
public:
  std::uint16_t nVars;
  std::list<Clause> clauses;
  std::vector<ssize_t> nClauses;
  std::vector<ssize_t> varDirection;

  CNF(std::uint16_t nVars) : nVars(nVars), nClauses(nVars), varDirection(nVars) {}

  void addClause(Clause &&c) {
    for (const Literal &lit : c.lits) {
      nClauses[lit.var] += 1;
      varDirection[lit.var] += lit.negated ? -1 : 1;
    }
    clauses.push_back(std::move(c));
  }
};

struct ModelEntry {
  bool assigned;
  bool assignment;

  ModelEntry() : assigned(false) { }
};

class Model {
public:
  CNF &f;
  std::vector<ModelEntry> entries;

  Model(CNF &f) : f(f), entries(f.nVars) { }

  bool allAssigned() {
    for (const ModelEntry &e : entries) {
      if (!e.assigned)
        return false;
    }
    return true;
  }

  bool satisfied(const Literal &lit) {
    return !(lit.negated && entries[lit.var].assignment) &&
           (lit.negated || entries[lit.var].assignment);
  }

  bool satisfied(const Clause &c) {
    for (const Literal &lit : c.lits)
      if (satisfied(lit))
        return true;
    return false;
  }

  bool satisfied(const CNF &f) {
    for (const Clause &c : f.clauses)
      if (!satisfied(c))
        return false;
    return true;
  }

  bool assigned(Var v) {
    return entries[v].assigned;
  }

  bool get(Var v) {
    assert(assigned(v));
    return entries[v].assignment;
  }

  void assign(Var v, bool val) {
    entries[v].assigned = true;
    entries[v].assignment = val;
  }

  void unassign(Var v) {
    entries[v].assigned = false;
  }
};

struct ConflictClauseLit {
  bool present;
  bool presentNegated;

  ConflictClauseLit() : present(false), presentNegated(false) {}
};

class ConflictClause {
private:
  std::vector<ConflictClauseLit> lits;

public:
  ConflictClause(std::uint16_t nVars) : lits(nVars) {}

  bool present(Var v) const {
    return (lits[v].present || lits[v].presentNegated) &&
           !(lits[v].present && lits[v].presentNegated);
  }

  std::uint16_t nPresent() const {
    std::uint16_t n = 0;
    for (Var i = 0; i < lits.size(); i++) {
      if (present(i)) n++;
    }
    return n;
  }

  void resolve(const Clause &c) {
    for (const Literal &l : c.lits) {
      if (l.negated)
        lits[l.var].presentNegated = true;
      else
        lits[l.var].present = true;
    }
  }

  Clause toClause() const {
    Clause c;
    for (Var i = 0; i < lits.size(); i++) {
      if (lits[i].present && !lits[i].presentNegated)
        c.addLiteral(i, false);
      else if (!lits[i].present && lits[i].presentNegated)
        c.addLiteral(i, true);
    }
    return c;
  }
};

struct ImplicationEntry {
  Var v;
  const Clause &antecedent;
};

struct SolveStackEntry {
  Var v;
  std::list<ImplicationEntry> implied;

public:
  SolveStackEntry(Var v) : v(v) {}
};

class SolveStack {
private:
  Model &model;
  std::list<SolveStackEntry> stack;

  void pop() {
    assert(!stack.empty());

    for (auto it = std::rbegin(stack.back().implied);
         it != std::rend(stack.back().implied); it++) {
      model.unassign(it->v);
    }

    model.unassign(stack.back().v);
    stack.pop_back();
  }

public:
  SolveStack(Model &model) : model(model)  {}

  const SolveStackEntry &top() {
    return stack.back();
  }

  bool empty() {
    return stack.empty();
  }

  void pushDecision(Var v, bool val) {
    model.assign(v, val);
    stack.emplace_back(v);
  }

  void pushImplied(Var v, bool val, const Clause &antecedent) {
    model.assign(v, val);

    if (stack.empty())
      // We've made no decisions. so this assignment will never be undone
      return;

    stack.back().implied.push_back({.v = v, .antecedent = antecedent});
  }

  void backtrack(const ConflictClause &cc) {
    // We want to backtrack until we reach the assertion level of this clause

    // We assume the current level is the highest decision level in the clause,
    // so we always pop it
    pop();

    // Now we pop until we find a level that has a variable corresponding to a
    // literal in the conflict clause
    bool found = false;
    while (!stack.empty() && !found) {
      for (const ImplicationEntry &i : stack.back().implied) {
        if (cc.present(i.v)) {
          found = true;
          break;
        }
      }

      if (!found && cc.present(stack.back().v))
        found = true;

      if (!found)
        pop();
    }
  }
};

struct VariableCount {
  size_t pos;
  size_t neg;

  VariableCount() : pos(0), neg(0) {}
};

std::optional<Model> solve(CNF &f) {
  Model model(f);
  SolveStack stack(model);

  auto decide = [&] () {
    assert(!model.satisfied(f));
    assert(!model.allAssigned());

    std::vector<VariableCount> counts(f.nVars);
    for (const Clause &c : f.clauses) {
      if (model.satisfied(c))
        continue;

      for (const Literal &l : c.lits) {
        if (model.assigned(l.var))
          continue;

        if (l.negated)
          counts[l.var].neg += 1;
        else
          counts[l.var].pos += 1;
      }
    }

    auto maxEl = std::max_element(
      std::cbegin(counts), std::cend(counts),
      [](const VariableCount &a, const VariableCount &b) {
        return std::max(a.neg, a.pos) < std::max(b.neg, b.pos);
      });

    stack.pushDecision(maxEl - std::begin(counts), maxEl->neg < maxEl->pos);
  };

  auto evaluateClause = [&] (const Clause &c) {
    bool satisfied = false;
    size_t nUnassigned = 0;
    const Literal *unassigned = nullptr;
    for (const Literal &lit : c.lits) {
      if (model.assigned(lit.var)) {
        satisfied = satisfied || model.satisfied(lit);
      } else {
        nUnassigned++;
        unassigned = &lit;
      }
    }
    return std::make_tuple(satisfied, nUnassigned, unassigned);
  };

  auto handleConflict = [&] (const Clause &conflict) {
    // Empty stack + conflict means unsat
    assert(!stack.empty());

    ConflictClause cc(f.nVars);
    cc.resolve(conflict);

    auto rec = stack.top();
    for (auto it = std::rbegin(rec.implied); it != std::rend(rec.implied); it++) {
      if (cc.present(it->v)) {
        cc.resolve(it->antecedent);
      }
    }

    stack.backtrack(cc);
    f.addClause(cc.toClause());
  };

  while (true) {
    if (model.satisfied(f))
      return model;

    if (!model.allAssigned()) {
      decide();
    }

    bool retry;
    do {
      retry = false;
      for (const Clause &c : f.clauses) {
        auto [satisfied, nUnassigned, unassigned] = evaluateClause(c);

        if (!satisfied) {
          if (nUnassigned == 1) {
            stack.pushImplied(unassigned->var, !unassigned->negated, c);
            retry = true;
          } else if (nUnassigned == 0) {
            if (stack.empty())
              // We made no decisions and still have a conflict. Therefore,
              // unsat
              return std::nullopt;

            handleConflict(c);
            retry = true;
          }
        }
      }
    } while (retry);
  }
}

int main(int argc, char **argv) {
  // Check if filename is provided
  if (argc < 2) {
    std::cerr << "Usage: " << argv[0] << " <dimacs_cnf_file>" << std::endl;
    return 1;
  }

  // Open the DIMACS file
  std::ifstream file(argv[1]);
  if (!file) {
    std::cerr << "Error: Could not open file " << argv[1] << std::endl;
    return 1;
  }

  // Variables to parse the DIMACS file
  int num_vars = 0;
  int num_clauses = 0;
  std::string line;
  std::vector<int> current_clause;
  CNF f(0); // Will resize

  // Parse the DIMACS file
  while (std::getline(file, line)) {
    // Trim leading and trailing whitespace
    line.erase(0, line.find_first_not_of(" \t\r\n"));
    line.erase(line.find_last_not_of(" \t\r\n") + 1);

    // Skip empty lines and comments
    if (line.empty() || line[0] == 'c') continue;

    // Parse problem line
    if (line[0] == 'p') {
      std::istringstream iss(line);
      std::string p, cnf;
      iss >> p >> cnf >> num_vars >> num_clauses;
      f = CNF(num_vars);

      if (p != "p" || cnf != "cnf") {
        std::cerr << "Error: Invalid DIMACS format" << std::endl;
        return 1;
      }
      continue;
    }

    // Parse clause literals
    std::istringstream iss(line);
    int lit;
    while (iss >> lit) {
      if (lit == 0) {
        // Clause is complete, add it
        break;
      }
      current_clause.push_back(lit);
    }

    // If we hit 0
    if (lit == 0 && !current_clause.empty()) {
      // Create and add the clause to the solver
      Clause c;
      for (int literal : current_clause) {
        // In DIMACS, negative literals represent negation
        c.addLiteral(std::abs(literal) - 1, literal > 0);
      }
      f.addClause(std::move(c));

      // Clear for next clause
      current_clause.clear();
    }
  }

  // Final clause handling (in case file doesn't end with 0)
  if (!current_clause.empty()) {
    Clause c;
    for (int literal : current_clause) {
      c.addLiteral(std::abs(literal) - 1, literal > 0);
    }
    f.addClause(std::move(c));
  }

  std::cout << "clauses: " << f.clauses.size() << "\n";

  // Solve the SAT problem
  auto solution = solve(f);
  std::cout << "SAT: " << (bool)solution << "\n";

  // Print model (assignment) if SAT
  if (solution)
    for (Var i = 0; i < f.nVars; i++) {
      if (solution->assigned(i))
        std::cout << "X" << i << ": " << solution->get(i) << "\n";
  }

  return 0;
}
