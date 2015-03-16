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

    Enode *expr_to_enode(PeriploContext *ctx, set<int> *vars, EnodeExpr *e);
    EnodeExpr *enode_to_expr(Enode *e);

    EnodeExpr *interpolate(EnodeExpr *a, EnodeExpr *b)
    {
        set<int> *vars = new set<int>();
        bool result;
        EnodeExpr *interp = NULL;
        Enode *ea, *eb;
        PeriploContext *ctx = new PeriploContext();

        ctx->SetLogic("QF_BOOL");
        ctx->SetOption(":produce-interpolants", "true");
        ctx->setVerbosity(0);

        ea = expr_to_enode(ctx, vars, a);
        eb = expr_to_enode(ctx, vars, b);
        delete vars;
        
///        cout << "ea:" << endl;
///        ea->print(cout);

///        cout << endl << "eb:" << endl;
///        eb->print(cout);

        ctx->Assert(ea);
        ctx->Assert(eb);
        ctx->CheckSATStatic();

        lbool r = ctx->getStatus();
        if (r == l_True) {
            result = false;
        } else {
            ctx->createProofGraph();
            ctx->setNumReductionLoops(2);
            ctx->setNumGraphTraversals(2);
            ctx->reduceProofGraph();
            ctx->setMcMillanInterpolation();
            ctx->enableRestructuringForStrongerInterpolant();

            vector<Enode*> interpolants;
            ctx->getSingleInterpolant(interpolants);

            if (interpolants.size() == 1) {
                result = true;
                interp = enode_to_expr(interpolants[0]);
            } else {
                result = false;
            }
        }


        ctx->deleteProofGraph();
        ctx->Reset();
        delete ctx;

        return interp;
    }

    Enode *expr_to_enode(PeriploContext *ctx, set<int> *vars, EnodeExpr *e)
    {
        Enode *r;
        int id = abs(e->enodeVarId);
        string str = std::to_string(id);
        list<Enode*> lits;

        switch (e->enodeType) {
            case ENODEVAR:
                if (vars->find(id) == vars->end())
                {
                    ctx->DeclareFun(str.c_str(), NULL, ctx->mkSortBool());
                    vars->insert(abs(id));
                }

                r = ctx->mkVar(str.c_str());
                break;

            case ENODEAND:
            case ENODEOR:
            case ENODENOT:
                for (int i = 0; i != e->enodeArity; ++i)
                {
                    Enode *c = expr_to_enode(ctx, vars, e->enodeChildren[i]);
                    lits.push_back(c);
                }

                if (e->enodeType == ENODEAND)
                {
                    r = ctx->mkAnd(ctx->mkCons(lits));
                } else if (e->enodeType == ENODEOR) {
                    r = ctx->mkOr(ctx->mkCons(lits));
                } else if (e->enodeType == ENODENOT) {
                    r = ctx->mkNot(ctx->mkCons(lits));
                }
                break;

            case ENODEINVALID:
            default:
                cout << "invalid" << endl;
                break;
        }
        assert(r != NULL);
        return r;
    }

    EnodeExpr *enode_to_expr(Enode *e)
    {
        assert (e->isTerm());
        if (e->isAnd() || e->isOr()) {
            assert(e->getArity() == 2);
            EnodeExpr *a = enode_to_expr(e->get1st());
            EnodeExpr *b = enode_to_expr(e->get2nd());

            EnodeExpr *r = (EnodeExpr*)malloc(sizeof(EnodeExpr));
            EnodeExpr **cs = (EnodeExpr**)malloc(2*sizeof(EnodeExpr*));
            cs[0] = a;
            cs[1] = b;

            if (e->isAnd()) {
                r->enodeType = ENODEAND;
            } else {
                r->enodeType = ENODEOR;
            }
            r->enodeVarId = 0;
            r->enodeChildren = cs;
            r->enodeArity = 2;

            return r;
        } else if (e->isNot()) {
            assert(e->getArity() == 1);
            EnodeExpr *a = enode_to_expr(e->get1st());

            EnodeExpr *r = (EnodeExpr*)malloc(sizeof(EnodeExpr));
            EnodeExpr **cs = (EnodeExpr**)malloc(1*sizeof(EnodeExpr*));
            cs[0] = a;

            r->enodeType = ENODENOT;
            r->enodeVarId = 0;
            r->enodeChildren = cs;
            r->enodeArity = 1;

            return r;
        } else if (e->isVar()) {
            string name = e->getCar()->getName();
            int id = std::stoi(name);
            EnodeExpr *r = (EnodeExpr*)malloc(sizeof(EnodeExpr));
            r->enodeType = ENODEVAR;
            r->enodeVarId = id;
            r->enodeChildren = NULL;
            r->enodeArity = 0;

            return r;
        } else {
            assert(false);
        }
    }

    void print_expr(EnodeExpr *e)
    {
        switch (e->enodeType) {
            case ENODEVAR:
                cout << "var ";
                cout << e->enodeVarId << endl;
                break;

            case ENODEAND:
                cout << "and" << endl;
                for (int i = 0; i != e->enodeArity; ++i)
                {
                    cout << "  ";
                    print_expr(e->enodeChildren[i]);
                }
                break;

            case ENODEOR:
                cout << "or" << endl;
                for (int i = 0; i != e->enodeArity; ++i)
                {
                    cout << "  ";
                    print_expr(e->enodeChildren[i]);
                }
                break;

            case ENODENOT:
                cout << "not ";
                print_expr(e->enodeChildren[0]);
                break;
                
            case ENODEINVALID:
            default:
                cout << "invalid" << endl;
                break;
        }
    }


///    periplo_solver *periplo_new()
///    {
///        periplo_solver *s = new periplo_solver_t();
///        s->ctx = new PeriploContext();
///        s->ctx->SetLogic("QF_BOOL");
///        s->ctx->SetOption(":produce-interpolants", "true");
///        s->ctx->setVerbosity(0);
///        return s;
///    }

///    void periplo_delete(periplo_solver *s)
///    {
///        s->ctx->Reset();
///        delete s->ctx;
///        delete s;
///    }

///    Enode *enodeTrue(periplo_solver *s)
///    {
///        return s->ctx->mkTrue();
///    }

///    Enode *enodeFalse(periplo_solver *s)
///    {
///        return s->ctx->mkFalse();
///    }

///    Enode *enodeNot(periplo_solver *s, Enode *e)
///    {
///        Enode *r = s->ctx->mkNot(s->ctx->mkCons(e));
///        return r;
///    }

///    Enode *enodeAnd(periplo_solver *s, int length, Enode **es)
///    {
///        list<Enode*> lits;
///        for (int i = 0; i != length; ++i)
///        {
///            lits.push_back(es[i]);
///        }
///        Enode *r = s->ctx->mkAnd(s->ctx->mkCons(lits));
///        return r;
///    }

///    Enode *enodeOr(periplo_solver *s, int length, Enode **es)
///    {
///        list<Enode*> lits;
///        for (int i = 0; i != length; ++i)
///        {
///            lits.push_back(es[i]);
///        }
///        return s->ctx->mkOr(s->ctx->mkCons(lits));
///    }

///    Enode *enodeVar(periplo_solver *s, int id)
///    {
///        if (s->vars.find(abs(id)) == s->vars.end())
///        {
///            s->ctx->DeclareFun(std::to_string(abs(id)).c_str(), NULL, s->ctx->mkSortBool());
///            s->vars.insert(abs(id));
///        }

///        return s->ctx->mkVar(std::to_string(abs(id)).c_str());
///    }

///    bool interpolate(periplo_solver *s, Enode *a, Enode *b)
///    {
///        s->ctx->Assert(a);
///        s->ctx->Assert(b);
///        s->ctx->CheckSATStatic();
///        lbool r = s->ctx->getStatus();
///        if (r == l_True) {
///            return false;
///            s->ctx->deleteProofGraph();
///            s->ctx->Reset();
///        }
///        s->ctx->createProofGraph();
///        s->ctx->setNumReductionLoops(2);
///        s->ctx->setNumGraphTraversals(2);
///        s->ctx->reduceProofGraph();
///        s->ctx->setMcMillanInterpolation();
///        s->ctx->enableRestructuringForStrongerInterpolant();

///        vector<Enode*> interpolants;
///        s->ctx->getSingleInterpolant(interpolants);
///        bool result;

///        if (interpolants.size() == 1) {
///            result = true;;
///            s->interpolant = interpolants[0];
///        } else {
///            result = false;
///        }

///        s->ctx->deleteProofGraph();
///        s->ctx->Reset();
///        return result;
///    }

///    Enode *interpolant(periplo_solver *s)
///    {
///        return s->interpolant;
///    }

///    enode_type enodeType(Enode *e)
///    {
///        if (e == NULL) cout << "bad pointer in type" << endl;
///        if (e->isVar()) {
///            return ENODEVAR;
///        } else if (e->isAnd()) {
///            return ENODEAND;
///        } else if (e->isOr()) {
///            return ENODEOR;
///        } else if (e->isNot()) {
///            return ENODENOT;
///        } else {
///            return ENODEINVALID;
///        }
///    }

///    int enodeVarId(Enode *e)
///    {
///        if (e == NULL) cout << "bad pointer in varId" << endl;
///        string str = e->getCar()->getName();
///        return std::stoi(str);
///    }

///    int enodeArity(Enode *e)
///    {
///        if (e == NULL) cout << "bad pointer in arity" << endl;
///        return e->getArity();
///    }

///    Enode *enode1st(Enode *e)
///    {
///        if (e == NULL) cout << "bad pointer in 1st" << endl;
///        if (e->get1st() == NULL) cout << "bad pointer in 1st" << endl;
///        return e->get1st();
///    }

///    Enode *enode2nd(Enode *e)
///    {
///        if (e == NULL) cout << "bad pointer in 2nd" << endl;
///        if (e->get2nd() == NULL) cout << "bad pointer in 2nd" << endl;
///        return e->get2nd();
///    }
}
