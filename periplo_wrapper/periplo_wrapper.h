#ifndef PERIPLO_WRAPPER_H
#define PERIPLO_WRAPPER_H

typedef struct periplo_solver_t periplo_solver;

periplo_solver  *periplo_new();
void            periplo_delete(periplo_solver *s);
void            periplo_addClause(periplo_solver *s, bool clause_A, int length, int *clause);

Enode           *enodeTrue(periplo_solver *s);
Enode           *enodeFalse(periplo_solver *s);
Enode           *enodeNot(periplo_solver *s, Enode *e);
Enode           *enodeAnd(periplo_solver *s, int length, Enode **es);
Enode           *enodeOr(periplo_solver *s, int length, Enode **es);

#endif
