#include "PeriploContext.h"

using namespace periplo;

struct periplo_solver_t {
    PeriploContext *ctx;
    int b;
};

extern "C" {
#include "periplo_wrapper.h"

    periplo_solver *periplo_new()
    {
        periplo_solver *s = new periplo_solver_t();
        s->ctx = new PeriploContext();
        s->ctx->SetLogic("QF_BOOL");
        s->ctx->SetOption(":produce-interpolants", "true");
        s->ctx->setVerbosity(0);
        return s;
    }

    void periplo_delete(periplo_solver *s)
    {
        s->ctx->Reset();
        delete s->ctx;
        delete s;
    }
}
