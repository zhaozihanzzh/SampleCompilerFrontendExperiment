CC=gcc
LEX=win_flex
RM=del

all: experiment1.exe

experiment1.exe: lex.yy.c
	$(CC) lex.yy.c -o experiment1.exe

lex.yy.c: scanner.l
	$(LEX) scanner.l

clean:
	$(RM) experiment1.exe lex.yy.c
