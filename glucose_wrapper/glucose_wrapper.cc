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
            s->clause.push(mkLit(abs(lit), false));
        } else {
            s->clause.push(mkLit(abs(lit), true));
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
        Var v = s->newVar();
    }

    bool solve(glucose_solver *s)
    {
        return s->solve();
    }

    int *model(glucose_solver *s)
    {
        int *model = (int *)malloc(sizeof(int) * (1 + s->model.size()));
        int mi = 0;

        for (int i = 1; i < s->model.size(); ++i)
        {
            if (s->model[i] == l_True) {
                model[mi] = i;
                mi++;
            } else if (s->model[i] == l_False) {
                model[mi] = -i;
                mi++;
            }
        }
        model[mi] = 0;

        return model;
    }
}
