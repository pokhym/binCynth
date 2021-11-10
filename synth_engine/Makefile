CC = g++
CFLAGS = -g -Wall -Wextra
LDFLAGS =

all: main


main: engine.o
	${CC} ${CFLAGS} engine.o main.cpp -o main

engine:
	${CC} ${CFLAGS} engine.hpp engine.cpp -o engine.o

clean:
	rm *.o main