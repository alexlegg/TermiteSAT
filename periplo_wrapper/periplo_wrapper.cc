#include "PeriploContext.h"

using namespace periplo;

struct periplo_solver_t {
    PeriploContext *ctx;
    int b;
    Enode *interpolant;
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

    void periplo_addClause(periplo_solver *s, bool partitionA, int length, int *clause)
    {

    }

    void periplo_delete(periplo_solver *s)
    {
        s->ctx->Reset();
        delete s->ctx;
        delete s;
    }

    Enode *enodeTrue(periplo_solver *s)
    {
        return s->ctx->mkTrue();
    }

    Enode *enodeFalse(periplo_solver *s)
    {
        return s->ctx->mkFalse();
    }

    Enode *enodeNot(periplo_solver *s, Enode *e)
    {
        return s->ctx->mkNot(e);
    }

    Enode *enodeAnd(periplo_solver *s, int length, Enode **es)
    {
        list<Enode*> lits;
        for (int i = 0; i != length; ++i)
        {
            lits.push_back(es[i]);
        }
        return s->ctx->mkAnd(s->ctx->mkCons(lits));
    }

    Enode *enodeOr(periplo_solver *s, int length, Enode **es)
    {
        list<Enode*> lits;
        for (int i = 0; i != length; ++i)
        {
            lits.push_back(es[i]);
        }
        return s->ctx->mkOr(s->ctx->mkCons(lits));
    }

    Enode *enodeVar(periplo_solver *s, int id)
    {
        s->ctx->DeclareFun("abc", NULL, s->ctx->mkSortBool());
        return s->ctx->mkVar("abc");
    }

    bool interpolate(periplo_solver *s, Enode *a, Enode *b)
    {
        s->ctx->Assert(a);
        s->ctx->Assert(b);
        s->ctx->CheckSATStatic();
        lbool r = s->ctx->getStatus();
        if (r == l_True) {
            return false;
            s->ctx->deleteProofGraph();
            s->ctx->Reset();
        }
        s->ctx->createProofGraph();
        s->ctx->setNumReductionLoops(2);
        s->ctx->setNumGraphTraversals(2);
        s->ctx->reduceProofGraph();
        s->ctx->setMcMillanInterpolation();
        s->ctx->enableRestructuringForStrongerInterpolant();

        vector<Enode*> interpolants;
        s->ctx->getSingleInterpolant(interpolants);
        bool result;

        if (interpolants.size() == 1) {
            result = true;;
            s->interpolant = interpolants[0];
        } else {
            result = false;
        }

        s->ctx->deleteProofGraph();
        s->ctx->Reset();
        return result;
    }

    Enode *interpolant(periplo_solver *s)
    {
        return s->interpolant;
    }
}
