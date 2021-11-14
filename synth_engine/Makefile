CC = g++
CFLAGS = -g -Wall -Wextra
LDFLAGS =

all: main

components:
	echo "COMPONENTS"
	${CC} ${CFLAGS} -c components.hpp components.cpp

engine: components
	echo "ENGINE"
	${CC} ${CFLAGS} -c engine.hpp engine.cpp

main: engine
	echo "MAIN"
	${CC} ${CFLAGS} components.o engine.o main.cpp -o main

clean:
	rm *.o main