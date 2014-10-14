#include "core/Solver.h"

using namespace Glucose;

struct glucose_solver_t : public Solver {
    vec<Lit> clause;
    vec<Lit> assumps;
};

extern "C" {

#include "glucose_wrapper.h"

    glucose_solver  *glucose_new() { return new glucose_solver_t(); }
    void            glucose_delete(glucose_solver *s) {delete s; }

    void addClause_addLit(glucose_solver *s, int lit)
    {
        if (lit > 0) {
            s->clause.push(mkLit(abs(lit)));
        } else {
            s->clause.push(mkLit(abs(lit)));
        }
    }

    bool addClause(glucose_solver *s)
    {
        bool r = s->addClause(s->clause);
        s->clause.clear();
        return r;
    }

    void addVar(glucose_solver *s)
    {
        s->newVar();
    }

    bool solve(glucose_solver *s)
    {
        return s->solve();
    }
}
