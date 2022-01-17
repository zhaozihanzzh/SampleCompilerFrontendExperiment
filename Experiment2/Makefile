CC=gcc
LEX=win_flex
YACC=win_bison
RM=del

all: experiment2.exe

experiment2.exe: lex.yy.c y.tab.c y.tab.h
	$(CC) lex.yy.c y.tab.c -o experiment2

lex.yy.c: scanner.l
	$(LEX) scanner.l

y.tab.c: parser.y
	$(YACC) -y parser.y

y.tab.h: parser.y
	$(YACC) -y -d parser.y

clean:
	$(RM) experiment2.exe lex.yy.c y.tab.c y.tab.h
