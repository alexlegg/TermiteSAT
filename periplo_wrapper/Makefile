BASE_PER=../periplo
BASE_CUDD=../cudd
INC_PER=-I${BASE_PER}/src/ -I${BASE_PER}/src/api/ -I${BASE_PER}/src/cnfizers/ -I${BASE_PER}/src/common/ \
		-I${BASE_PER}/src/egraph/ -I${BASE_PER}/src/minisat/ -I${BASE_PER}/src/proof/ -I${BASE_PER}/src/satsolvers/ \
		-I${BASE_PER}/src/simplifiers/ -I${BASE_PER}/src/sorts/ -I${BASE_PER}/src/minisat/core/ -I${BASE_PER}/src/minisat/mtl \
		-I${BASE_PER}/src/minisat/utils/ -I${BASE_CUDD}/include
	
all: periplo_wrapper.h periplo_wrapper.cc
	g++ -std=c++11 -c $(INC_PER) -o periplo_wrapper.o periplo_wrapper.cc -DPRODUCE_PROOF -DPERIPLO_WRAPPER_GHC_ONLY
	ar x ../periplo/build/src/.libs/libperiplolibrary.a
	ar x ${BASE_CUDD}/cudd/.libs/libcudd.a
	ar rs libperiplo_wrapper.a *.o

.PHONY: clean
clean:
	rm -rf *.o
	rm -rf *.or
	rm -rf *.a

