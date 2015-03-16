#ifndef PERIPLO_WRAPPER_H
#define PERIPLO_WRAPPER_H

typedef struct periplo_solver_t periplo_solver;

typedef enum {
    ENODEINVALID,
    ENODEVAR,
    ENODEAND,
    ENODEOR,
    ENODENOT
} enode_type;

typedef struct EnodeExpr_t EnodeExpr;

struct EnodeExpr_t {
    enode_type enodeType;
    int enodeVarId;
    EnodeExpr **enodeChildren;
    int enodeArity;
};

EnodeExpr *interpolate(EnodeExpr *a, EnodeExpr *b);

void print_expr(EnodeExpr *e);

#endif
