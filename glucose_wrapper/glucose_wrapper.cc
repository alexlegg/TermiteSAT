#include "core/Solver.h"
#include <iostream>
#include <vector>

using namespace Glucose;
using namespace std;

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

    void clearAssumptions(glucose_solver *s)
    {
        s->assumps.clear();
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
            } else if (clause[i] == 0) {
                printf("error");
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

    vector<Lit> reduce(glucose_solver *s, vec<Lit> *cube)
    {
        vector<bool> marks(cube->size());
        for (int i = 0; i != marks.size(); ++i)
        {
            marks[i] = false;
        }

        for (int i = 0; i != cube->size(); ++i)
        {
            vec<Lit> curr_assumps;
            for (int j = 0; j != marks.size(); ++j)
            {
                if (i == j) continue; //Omit current lit
                if (marks[j]) continue; //Omit previously marked lits
                curr_assumps.push((*cube)[j]);
            }

            if (!s->solve(curr_assumps))
            {
                marks[i] = true;
            }
        }


        vector<Lit> reduced;
        for (int i = 0; i != marks.size(); ++i)
        {
            if (!marks[i]) {
                reduced.push_back((*cube)[i]);
            }
        }
        
        return reduced;
    }

    int **minimise_core(glucose_solver *s)
    {
        vector< vector<Lit> > cubes;
        cubes.push_back(reduce(s, &(s->assumps)));


///        for (int i = 0; i != cubes[0].size(); ++i)
///        {
///            vec<Lit> attempt;
///            for (int j = 0; j != s->assumps.size(); ++j)
///            {
///                if (cubes[0][i] == s->assumps[j]) continue;
///                attempt.push(s->assumps[j]);
///            }

///            if (!s->solve(attempt))
///            {
///                cubes.push_back(reduce(s, &attempt));
///            }
///        }

        int **cubes_arr = (int **)malloc(sizeof(int*) * (1 + cubes.size()));
        for (int i = 0; i != cubes.size(); ++i)
        {
            int *core_arr = (int *)malloc(sizeof(int) * (1 + cubes[i].size()));

            for (int j = 0; j != cubes[i].size(); ++j)
            {
                if (sign(cubes[i][j])) {
                    core_arr[j] = -var(cubes[i][j]);
                } else {
                    core_arr[j] = var(cubes[i][j]);
                }
            }

            core_arr[cubes[i].size()] = 0;
            cubes_arr[i] = core_arr;
        }
        cubes_arr[cubes.size()] = NULL;
        return cubes_arr;
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
