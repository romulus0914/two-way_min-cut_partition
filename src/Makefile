GXX = g++
GXXFLAG = -std=c++11

FLAG = -Wall -O3

SRC = two-way_min-cut_partition.cpp
EXE = two-way_min-cut_partition

all: cpp

cpp: $(SRC)
	$(GXX) $(GXXFLAG) $(FLAG) -o $(EXE) $(SRC)

clean:
	rm -rf $(EXE)
