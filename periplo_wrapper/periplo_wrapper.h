#ifndef PERIPLO_WRAPPER_H
#define PERIPLO_WRAPPER_H

typedef enum {
    ENODEINVALID,
    ENODEVAR,
    ENODEAND,
    ENODEOR,
    ENODENOT,
    ENODETRUE,
    ENODEFALSE
} enode_type;

typedef struct EnodeExpr_t EnodeExpr;

struct EnodeExpr_t {
    enode_type enodeType;
    int enodeVarId;
    EnodeExpr **enodeChildren;
    int enodeArity;
};

typedef enum {
    VARFALSE,
    VARTRUE,
    VARUNSET
} sign_t;

typedef struct VarAssignment_t VarAssignment;

struct VarAssignment_t {
    sign_t sign;
    int id;
};

//This is a dirty hack
#ifndef PERIPLO_WRAPPER_GHC_ONLY
typedef Enode;
#endif

typedef struct PeriploSolver_t PeriploSolver;

PeriploSolver *newSolver();
void *deleteSolver(PeriploSolver *ctx);

Enode *mkConjunct(PeriploSolver *ctx, int size, Enode **cs);
Enode *mkDisjunct(PeriploSolver *ctx, int size, Enode **cs);
Enode *mkNegation(PeriploSolver *ctx, Enode *e);
Enode *mkVariable(PeriploSolver *ctx, int var);
Enode *mkTrue(PeriploSolver *ctx);
Enode *mkFalse(PeriploSolver *ctx);

int checkFml(PeriploSolver *ctx, Enode *fml);

VarAssignment **interpolate(PeriploSolver *ctx, int *ps, int szPs, Enode *a, Enode *b);

void print_expr(EnodeExpr *e);

#endif
