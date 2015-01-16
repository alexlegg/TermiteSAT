#include "core/Solver.h"

using namespace Glucose;

struct glucose_solver_t : public Solver {
    vec<Lit> assumps;
    vec<Lit> clause;
};

extern "C" {

#include "glucose_wrapper.h"

    glucose_solver  *glucose_new() { return new glucose_solver_t(); }
    void            glucose_delete(glucose_solver *s) {delete s; }

    void addAssumption(glucose_solver *s, int lit)
    {
        if (lit > 0) {
            s->assumps.push(mkLit(abs(lit), false));
        } else {
            s->assumps.push(mkLit(abs(lit), true));
        }
    }

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
        bool r = s->addClause_(s->clause);
        s->clause.clear();
        return r;
    }

    bool addClauseVector(glucose_solver *s, int size, int *clause)
    {
        for (int i = 0; i != size; ++i)
        {
            if (clause[i] > 0) {
                s->clause.push(mkLit(abs(clause[i]), false));
            } else {
                s->clause.push(mkLit(abs(clause[i]), true));
            }
        }
        bool r = s->addClause_(s->clause);
        s->clause.clear();
        return r;
    }

    void addVar(glucose_solver *s)
    {
        Var v = s->newVar();
    }

    bool solve(glucose_solver *s)
    {
        return s->solve(s->assumps);
    }

    int *minimise_core(glucose_solver *s)
    {
        vec<bool> marks(s->assumps.size());
        for (int i = 0; i != marks.size(); ++i)
        {
            marks[i] = false;
        }

        for (int i = 0; i != s->assumps.size(); ++i)
        {
            vec<Lit> curr_assumps;
            for (int j = 0; j != marks.size(); ++j)
            {
                if (i == j) continue; //Omit current lit
                if (marks[j]) continue; //Omit previously marked lits
                curr_assumps.push(s->assumps[j]);
            }

            if (!s->solve(curr_assumps))
            {
                marks[i] = true;
            }
        }

        int core_size = 0;
        for (int i = 0; i != marks.size(); ++i)
        {
            if (!marks[i]) core_size++;
        }

        int *core = (int *)malloc(sizeof(int) * (1 + core_size));
        int ci = 0;
        for (int i = 0; i != marks.size(); ++i)
        {
            if (!marks[i]) {
                if (sign(s->assumps[i])) {
                    core[ci] = -var(s->assumps[i]);
                } else {
                    core[ci] = var(s->assumps[i]);
                }
                ci++;
            }
        }
        core[ci] = 0;
        return core;
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

    int *conflicts(glucose_solver *s)
    {
        int *conflicts = (int *)malloc(sizeof(int) * (1 + s->conflict.size()));

        int mi = 0;
        for (int i = 0; i < s->conflict.size(); ++i)
        {
            Lit lit = s->conflict[i];
            if (sign(lit)) {
                conflicts[mi] = var(lit);
                mi++;
            } else {
                conflicts[mi] = -var(lit);
                mi++;
            }
        }
        conflicts[mi] = 0;

        return conflicts;
    }
}
