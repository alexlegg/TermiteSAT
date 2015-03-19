BASE_PER=../periplo
BASE_CUDD=../cudd
INC_PER=-I${BASE_PER}/src/ -I${BASE_PER}/src/api/ -I${BASE_PER}/src/cnfizers/ -I${BASE_PER}/src/common/ \
		-I${BASE_PER}/src/egraph/ -I${BASE_PER}/src/minisat/ -I${BASE_PER}/src/proof/ -I${BASE_PER}/src/satsolvers/ \
		-I${BASE_PER}/src/simplifiers/ -I${BASE_PER}/src/sorts/ -I${BASE_PER}/src/minisat/core/ -I${BASE_PER}/src/minisat/mtl \
		-I${BASE_PER}/src/minisat/utils/ -I${BASE_CUDD}/include
	
all: periplo_wrapper.h periplo_wrapper.cc
	g++ -std=c++11 -c $(INC_PER) -o periplo_wrapper.o periplo_wrapper.cc -DPRODUCE_PROOF
	ar x ../periplo/build/src/.libs/libperiplolibrary.a
	ar x ${BASE_CUDD}/cudd/libcudd.a
	ar x ${BASE_CUDD}/epd/libepd.a
	ar x ${BASE_CUDD}/util/libutil.a
	ar x ${BASE_CUDD}/dddmp/libdddmp.a
	ar x ${BASE_CUDD}/st/libst.a
	ar x ${BASE_CUDD}/mtr/libmtr.a
	ar rs libperiplo_wrapper.a *.o

.PHONY: clean
clean:
	rm -rf *.o
	rm -rf *.or
	rm -rf *.a

