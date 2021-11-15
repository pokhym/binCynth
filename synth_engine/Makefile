CC = g++
CFLAGS = -g -Wall -Wextra
LDFLAGS =

all: main

main: engine
	echo "MAIN"
	${CC} ${CFLAGS} components.o engine.o synth_state.o main.cpp -o main

engine: components synth_state
	echo "ENGINE"
	${CC} ${CFLAGS} -c engine.hpp engine.cpp -I.

components:
	echo "COMPONENTS"
	${CC} ${CFLAGS} -c components.hpp components.cpp -I.

synth_state: component_state
	echo "SYNTH_STATE"
	${CC} ${CFLAGS} -c synth_state.hpp synth_state.cpp -I.

component_state:
	echo "COMPONENT_STATE"
	${CC} ${CFLAGS} -c component_state.hpp component_state.cpp -I.



clean:
	rm *.o *.gch main