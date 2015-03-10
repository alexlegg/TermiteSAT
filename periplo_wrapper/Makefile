BASE_PER=../periplo
INC_PER=-I${BASE_PER}/src/ -I${BASE_PER}/src/api/ -I${BASE_PER}/src/cnfizers/ -I${BASE_PER}/src/common/ \
		-I${BASE_PER}/src/egraph/ -I${BASE_PER}/src/minisat/ -I${BASE_PER}/src/proof/ -I${BASE_PER}/src/satsolvers/ \
		-I${BASE_PER}/src/simplifiers/ -I${BASE_PER}/src/sorts/ -I${BASE_PER}/src/minisat/core/ -I${BASE_PER}/src/minisat/mtl \
		-I${BASE_PER}/src/minisat/utils/
	

####PeRIPLO is assumed to have been built in a "build" directory
###LIB_PER=-L${BASE_PER}/build/src/.libs -static -lperiplolibrary
###LIB_GMP=-lgmpxx -lgmp 
###LIB_LZ=-lz

all: periplo_wrapper.h periplo_wrapper.cc
	g++ -std=c++11 -c $(INC_PER) -o periplo_wrapper.o periplo_wrapper.cc -DPRODUCE_PROOF
	ar x ../periplo/build/src/.libs/libperiplolibrary.a
	ar rs libperiplo_wrapper.a *.o

.PHONY: clean
clean:
	rm -rf *.o
	rm -rf *.or
	rm -rf *.a

