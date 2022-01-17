%{
#include <stdlib.h>
#include <string.h>
#include "y.tab.h"
// 行号，列号
unsigned int line_num = 1, row_num = 0;
// 保存已有的标识符的符号表
struct SymbolNode {
    const char *name;
    unsigned char type;
    struct SymbolNode *next;
} symbol_table_head;
struct SymbolNode *table_head = &symbol_table_head;
struct SymbolNode *table_tail = &symbol_table_head;
unsigned char find_symbol(const char *name);
void add_symbol(const char *name, const unsigned char type);
%}

LETTER [A-Za-z]
DIGIT [0-9]
SINGLE_DELIMITERS [*+-:.;,'=\/\<\>\(\)\[\]]
IDENTIFIER {LETTER}({LETTER}|{DIGIT})*
INTEGER {DIGIT}+
COMMENT \/\*[^\n]*\*\/
STRING ’[^’^\n]*’|'[^'^\n]*'

%%
[ \t\r\a]+ {
    row_num += strlen(yytext);
}
[\n] {
    ++line_num;
    row_num = 0;
}
and	return KW_AND;
array	return KW_ARRAY;
begin	return KW_BEGIN;
bool	return KW_BOOL;
call	return KW_CALL;
case	return KW_CASE;
char	return KW_CHAR;
constant	return KW_CONSTANT;
dim	return KW_DIM;
do	return KW_DO;
else	return KW_ELSE;
end	return KW_END;
false	return KW_FALSE;
for	return KW_FOR;
if	return KW_IF;
input	return KW_INPUT;
integer	return KW_INTEGER;
not	return KW_NOT;
of	return KW_OF;
or	return KW_OR;
output	return KW_OUTPUT;
procedure	return KW_PROCEDURE;
program	return KW_PROGRAM;
read	return KW_READ;
real	return KW_REAL;
repeat	return KW_REPEAT;
set	return KW_SET;
stop	return KW_STOP;
then	return KW_THEN;
to	return KW_TO;
true	return KW_TRUE;
until	return KW_UNTIL;
var	return KW_VAR;
while	return KW_WHILE;
write	return KW_WRITE;
\(	return LEFT_BRACKET;
\)	return RIGHT_BRACKET;
\*	return STAR;

\+	return PLUS;
,	return COMMA;
-	return MINUS;
\.	return SINGLE_DOT;
\.\.	return DOUBLE_DOT;
\/	return LEFT_DASH;
\/\*	return START_COMMENT;
:	return COLON;
:=	return ASSIGN;
;	return SEMICOLON;
\<	return LESSTHAN;
\<=	return LESSEQUALTHAN;
\<\>	return NOTEQUAL;
=	return EQUAL;
\>	return BIGGERTHAN;
\>=	return BIGGEREQUALTHAN;
\[	return LEFT_SQUARE_BRACKET;
\]	return RIGHR_SQUARE_BRACKET;
' return SINGLE_QUOTE;

{IDENTIFIER} {
    yylval.str = strdup(yytext);
    unsigned char id = find_symbol(yytext);
    if (id == 0) return TYPE_IDENTIFIER_INT;
    else if (id == 1) return TYPE_IDENTIFIER_BOOL;
    else return TYPE_IDENTIFIER_UNKNOWN;
}
{INTEGER} {
    yylval.num = atoi(yytext);
    return TYPE_INTEGER;
}
{STRING} return TYPE_STRING;
{COMMENT} {/* 直接忽略注释 */}
. return TYPE_UNKNOWN;
%%
/* [+-* /=<>()[]:.;,'] */

// 在符号表中查找给出的标识符的类型
// 0 - integer | 1 - bool |/* 2 - char */| 255 - unknown
unsigned char find_symbol(const char *name) {
    struct SymbolNode *p = table_head->next;
    while (p != NULL) {
        if (strcmp(p->name, name) == 0) {
            return p->type;
        }
        p = p->next;
    }
    return (unsigned char)255;
}
// 向符号表中添加标识符
void add_symbol(const char *name, const unsigned char type) {
    table_tail->next = (struct SymbolNode *)malloc(sizeof(struct SymbolNode));
    table_tail = table_tail->next;
    table_tail->name = name;
    table_tail->type = type;
    table_tail->next = NULL;
    // debug printf("Add symbol %s %u\n", name, type);
}
int yywrap() {
    return 1;
}