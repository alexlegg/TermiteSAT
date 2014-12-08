#ifndef PERIPLO_WRAPPER_H
#define PERIPLO_WRAPPER_H

typedef struct periplo_solver_t periplo_solver;

periplo_solver  *periplo_new();
void            periplo_delete(periplo_solver *s);

#endif
