CC = g++
CFLAGS = -g -Wall -Wextra
LDFLAGS =

all: main

main: engine
	echo "MAIN"
	${CC} ${CFLAGS} components.o engine.o main.cpp -o main

engine: components
	echo "ENGINE"
	${CC} ${CFLAGS} -c engine.hpp engine.cpp -I.

components:
	echo "COMPONENTS"
	${CC} ${CFLAGS} -c components.hpp components.cpp -I.



clean:
	rm *.o main