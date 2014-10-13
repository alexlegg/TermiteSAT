#ifndef GLUCOSE_WRAPPER_H
#define GLUCOSE_WRAPPER_H

typedef struct glucose_solver_t glucose_solver;

glucose_solver  *glucose_new();
void            glucose_delete(glucose_solver *s);

#endif