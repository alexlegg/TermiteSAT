#include <iostream>
#include "Egraph.h"
#include "SimpSATSolver.h"
#include <vector>

using namespace std;
using namespace periplo;

int main()
{
    cout << "test" << endl;
    SATConfig config;
    config.verbosity = 7;
    SStore store = SStore(config);
    Egraph egraph = Egraph(config, store);
    SimpSATSolver solver(egraph, config);


    egraph.initializeSolver(&solver);

    solver.newVar();

    Var w = solver.newVar();
    Var x = solver.newVar();
    Var y = solver.newVar();
    Var z = solver.newVar();

    vec<Lit> clause;
    clause.push(mkLit(w));
    clause.push(mkLit(x));
    clause.push(mkLit(y, true));

    ipartitions_t partA = 0;
    setbit(partA, 1);

    ipartitions_t partB = 0;
    setbit(partB, 2);

    solver.addClause(clause, partA);
    solver.addClause(mkLit(x, true), partA);
    solver.addClause(mkLit(w, true), partA);

    clause.clear();
    clause.push(mkLit(y));

    solver.addClause(clause, partB);
    solver.addClause(mkLit(z), partB);

    cout << "1" << endl;

    bool status = solver.satSolve(false);
    if (status) {
        cout << "sat" << endl;
    } else { 
        cout << "unsat" << endl;
    }
    cout << "2" << endl;

    solver.createProofGraph();

    cout << "3" << endl;

    vector<Enode*> interpolants;
    solver.getSingleInterpolant(interpolants);

    return 0;
}
