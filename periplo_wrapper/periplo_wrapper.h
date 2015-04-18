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

typedef struct PeriploSolver_t PeriploSolver;

PeriploSolver *newSolver();

VarAssignment **interpolate(PeriploSolver *ctx, EnodeExpr *a, EnodeExpr *b);

void print_expr(EnodeExpr *e);

#endif
