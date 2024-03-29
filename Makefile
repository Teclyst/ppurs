all: ppurs.exe
	dune exec ./ppurs.exe test.purs
	gcc -g -no-pie test.s
	./a.out

ppurs.exe:
	dune build ./ppurs.exe

explain:
	menhir --base /tmp/parser --dump --explain parser.mly
	cat /tmp/parser.conflicts

clean:
	dune clean

.PHONY: all clean explain ppurs.exe