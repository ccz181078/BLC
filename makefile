main: main.cpp
	g++ main.cpp -O2 -g3 -o main -Wall -Wextra -std=c++17

run: main
	./main

