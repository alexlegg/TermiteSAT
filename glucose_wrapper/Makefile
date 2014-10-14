all: glucose_wrapper.h glucose_wrapper.cc
	g++ -c -I../glucose/ -o glucose_wrapper.o glucose_wrapper.cc
	ar x ../glucose/simp/libglucose.a
	ar rvs libglucose_wrapper.a glucose_wrapper.o Solver.or SimpSolver.or System.or Options.or

.PHONY: clean
clean:
	rm -rf *.o
	rm -rf *.or
	rm -rf *.a
