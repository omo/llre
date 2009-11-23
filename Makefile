
FLAGS  = -I/opt/local/include/boost-1_34/ \
         `llvm-config --cxxflags --ldflags --libs core engine bitwriter` -Wall
FLAGS += -g

all: test

build: main llgrep

test: build
	./main
	./llgrep object /opt/local/include/llvm/*

main: main.cpp llre.hpp
	g++ ${FLAGS} main.cpp -o main
llgrep: llgrep.cpp llre.hpp
	g++ ${FLAGS} llgrep.cpp -o llgrep
clean:
	-rm ./main .gdb_history

.PHONY: test clean