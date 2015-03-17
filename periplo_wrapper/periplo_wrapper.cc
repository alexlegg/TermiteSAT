#include "PeriploContext.h"
#include <string>
#include <cudd.h>

using namespace periplo;
using namespace std;

enum    VarStateValues                     	  { SETTRUE, SETFALSE, UNSET};

struct VarState {
	VarState(int _id, VarStateValues _state = UNSET) {id = _id;state = _state;}
	int id;
	VarStateValues state;
	 inline bool operator == (const VarState &o) const {
	        return id == o.id? true:false;
	 }
	 inline bool operator < (const VarState &o) const {
	        return id == o.id? true:false;
	 }

	 inline bool operator != (const VarState &o) const {
	        return id != o.id? true:false;
	 }
};

extern "C" {
#include "periplo_wrapper.h"

    //Helper functions
    Enode *expr_to_enode(PeriploContext *ctx, set<int> *vars, EnodeExpr *e);
    EnodeExpr *enode_to_expr(Enode *e);
    vector< vector<VarState> > enodeToBDD(Enode *e, vector<int> project, bool &success);
    DdNode* enodeToDdNode(DdManager *mgr, map<string, int> vars, Enode *f, bool &success);
    vector< vector<VarState> > reduceCubes(DdManager *mgr, DdNode *dd, map<int, int> rvars);

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
                bool success;
                vector<int> project;
                vector< vector<VarState> > reduced;
                reduced = enodeToBDD(interpolants[0], project, success);
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

    vector< vector<VarState> > enodeToBDD(Enode *e, vector<int> project, bool &success)
    {
        DdManager *mgr;
        DdNode *dd;
        vector< vector<VarState> > result;
        map<string, int> vars;
        map<int, int> rvars;

        int bdd_var = 0;
        for (auto p = project.begin(); p != project.end(); ++p)
        {
            stringstream s;
            s << *p;
            vars[s.str().c_str()] = bdd_var;
            rvars[bdd_var] = *p;
            bdd_var++;
        }

        mgr = Cudd_Init(project.size(), 0, CUDD_UNIQUE_SLOTS, CUDD_CACHE_SLOTS, 0);
        Cudd_AutodynEnable(mgr, CUDD_REORDER_GROUP_SIFT);
        Cudd_EnableReorderingReporting(mgr);

        assert(Cudd_DebugCheck(mgr) == 0);

        clock_t start = clock(), end;

        dd = enodeToDdNode(mgr, vars, e, success);
        end = clock();

        result.clear();
        if (!success) return result;

        assert(Cudd_DebugCheck(mgr) == 0);

        result = reduceCubes(mgr, dd, rvars);
        Cudd_RecursiveDeref(mgr, dd);

        assert(Cudd_DebugCheck(mgr) == 0);

        Cudd_RecursiveDeref(mgr, dd);

        Cudd_Quit(mgr);

        return result;
    }

    DdNode* enodeToDdNode(DdManager *mgr, map<string, int> vars, Enode *f, bool &success)
    {
        Enode *e;
        map<enodeid_t, DdNode*> cache;
        vector<Enode *> stack;

        stack.push_back(f);

        while (!stack.empty())
        {
            e = stack.back();
            stack.pop_back();

            if (e->isEnil()) return NULL;
            if (!e->isTerm()) return NULL;

            auto c = cache.find(e->getId());
            if (c != cache.end()) {
                //Already processed
                continue;
            }

            if (e->isVar()) {
                int var = vars[e->getCar()->getName()];
                cache[e->getId()] = Cudd_bddIthVar(mgr, var);
                Cudd_Ref(cache[e->getId()]);
            } else if (e->isAnd() || e->isOr()) {
                assert(e->getArity() == 2);
                auto ca = cache.find(e->get1st()->getId());
                auto cb = cache.find(e->get2nd()->getId());

                if (ca == cache.end() || cb == cache.end()) {
                    //Defer until children are cached
                    stack.push_back(e);

                    if (ca == cache.end()) stack.push_back(e->get1st());
                    if (cb == cache.end()) stack.push_back(e->get2nd());
                } else {
                    //Otherwise we can build this node now
                    DdNode *a = ca->second;
                    Cudd_Ref(a);
                    DdNode *b = cb->second;
                    Cudd_Ref(b);

                    if (e->isAnd()) {
                        cache[e->getId()] = Cudd_bddAnd(mgr, a, b);
                    } else if (e->isOr()) {
                        cache[e->getId()] = Cudd_bddOr(mgr, a, b);
                    }

                    Cudd_Ref(cache[e->getId()]);
                    Cudd_RecursiveDeref(mgr, a);
                    Cudd_RecursiveDeref(mgr, b);
                }
            } else if (e->isNot()) {
                assert(e->getArity() == 1);
                auto cn = cache.find(e->get1st()->getId());

                if (cn == cache.end()) {
                    //Defer until x in not(x) is true
                    stack.push_back(e);
                    stack.push_back(e->get1st());
                } else {
                    //It is processed, we can use it
                    cache[e->getId()] = Cudd_Not(cn->second);
                    Cudd_Ref(cache[e->getId()]);
                }
            }
        }

        DdNode* dd = cache[f->getId()];
        if (dd == NULL) {
            success = false;
            return NULL;
        } else {
            Cudd_Ref(dd);
        }

        //Clean up the cache
        for (auto cdd = cache.begin(); cdd != cache.end(); ++cdd)
        {
            Cudd_RecursiveDeref(mgr, cdd->second);
        }

        return dd;
    }

    vector< vector<VarState> > reduceCubes(DdManager *mgr, DdNode *dd, map<int, int> rvars)
    {
        vector< vector<VarState> > result;
        int length;
        DdGen *gen;
        DdNode *cube, *implicant, *tmp;
        int *c;
        CUDD_VALUE_TYPE v;

        Cudd_Ref(dd);

        assert(Cudd_DebugCheck(mgr) == 0);

        while (1)
        {
            cube = Cudd_LargestCube(mgr, dd, &length);
            if (cube == NULL) {
                Cudd_RecursiveDeref(mgr, dd);
                break;
            }
            Cudd_Ref(cube);

            assert(Cudd_DebugCheck(mgr) == 0);

            implicant = Cudd_bddMakePrime(mgr, cube, dd);
            if (implicant == NULL) {
                Cudd_RecursiveDeref(mgr, cube);
                Cudd_RecursiveDeref(mgr, dd);
                break;
            }
            Cudd_Ref(implicant);
            Cudd_RecursiveDeref(mgr, cube);

            Cudd_ForeachCube(mgr, implicant, gen, c, v)
            {
                vector<VarState> vs_cube;
                for (int i = 0; i != Cudd_ReadSize(mgr); ++i)
                {
                    if (c[i] == 0) {
                        vs_cube.push_back(VarState(rvars[i], SETFALSE));
                    } else if (c[i] == 1) {
                        vs_cube.push_back(VarState(rvars[i], SETTRUE));
                    }
                }
                result.push_back(vs_cube);
            }

            tmp = Cudd_bddAnd(mgr, dd, Cudd_Not(implicant));
            Cudd_Ref(tmp);
            Cudd_RecursiveDeref(mgr, dd);
            Cudd_RecursiveDeref(mgr, implicant);
            dd = tmp;
        }

        return result;
    }

}
