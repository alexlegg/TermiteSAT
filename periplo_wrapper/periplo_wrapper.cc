#include "PeriploContext.h"
#include <string>

using namespace periplo;

struct periplo_solver_t {
    PeriploContext *ctx;
    int b;
    Enode *interpolant;
    set<int> vars;
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
        Enode *r = s->ctx->mkNot(s->ctx->mkCons(e));
        return r;
    }

    Enode *enodeAnd(periplo_solver *s, int length, Enode **es)
    {
        list<Enode*> lits;
        for (int i = 0; i != length; ++i)
        {
            lits.push_back(es[i]);
        }
        Enode *r = s->ctx->mkAnd(s->ctx->mkCons(lits));
        return r;
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
        if (s->vars.find(abs(id)) == s->vars.end())
        {
            s->ctx->DeclareFun(std::to_string(abs(id)).c_str(), NULL, s->ctx->mkSortBool());
            s->vars.insert(abs(id));
        }

        return s->ctx->mkVar(std::to_string(abs(id)).c_str());
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

    enode_type enodeType(Enode *e)
    {
        if (e == NULL) cout << "bad pointer in type" << endl;
        if (e->isVar()) {
            return ENODEVAR;
        } else if (e->isAnd()) {
            return ENODEAND;
        } else if (e->isOr()) {
            return ENODEOR;
        } else if (e->isNot()) {
            return ENODENOT;
        } else {
            return ENODEINVALID;
        }
    }

    int enodeVarId(Enode *e)
    {
        if (e == NULL) cout << "bad pointer in varId" << endl;
        string str = e->getCar()->getName();
        return std::stoi(str);
    }

    int enodeArity(Enode *e)
    {
        if (e == NULL) cout << "bad pointer in arity" << endl;
        return e->getArity();
    }

    Enode *enode1st(Enode *e)
    {
        if (e == NULL) cout << "bad pointer in 1st" << endl;
        if (e->get1st() == NULL) cout << "bad pointer in 1st" << endl;
        return e->get1st();
    }

    Enode *enode2nd(Enode *e)
    {
        if (e == NULL) cout << "bad pointer in 2nd" << endl;
        if (e->get2nd() == NULL) cout << "bad pointer in 2nd" << endl;
        return e->get2nd();
    }
}
