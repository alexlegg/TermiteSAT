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

}
