%{
#include <stdio.h>
#include <string.h>
#define TYPE_COMMENT -1
#define TYPE_UNKNOWN -2
#define TYPE_IDENTIFIER 36
#define TYPE_INTEGER 37
#define TYPE_STRING 38
// 行号，列号
unsigned int line_num = 1, row_num = 0;
// 保存已经有的标识符和常数
struct node {
    char elem[20];
    struct node *next;
};
struct node *head = 0;
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
and	return 1;
array	return 2;
begin	return 3;
bool	return 4;
call	return 5;
case	return 6;
char	return 7;
constant	return 8;
dim	return 9;
do	return 10;
else	return 11;
end	return 12;
false	return 13;
for	return 14;
if	return 15;
input	return 16;
integer	return 17;
not	return 18;
of	return 19;
or	return 20;
output	return 21;
procedure	return 22;
program	return 23;
read	return 24;
real	return 25;
repeat	return 26;
set	return 27;
stop	return 28;
then	return 29;
to	return 30;
true	return 31;
until	return 32;
var	return 33;
while	return 34;
write	return 35;
\(	return 39;
\)	return 40;
\*	return 41;

\+	return 43;
,	return 44;
-	return 45;
\.	return 46;
\.\.	return 47;
\/	return 48;
\/\*	return 49;
:	return 50;
:=	return 51;
;	return 52;
\<	return 53;
\<=	return 54;
\<\>	return 55;
=	return 56;
\>	return 57;
\>=	return 58;
\[	return 59;
\]	return 60;
' return 61;

{IDENTIFIER} return TYPE_IDENTIFIER;
{INTEGER} return TYPE_INTEGER;
{STRING} return TYPE_STRING;
{COMMENT} return TYPE_COMMENT;
. return TYPE_UNKNOWN;
%%
/* [+-* /=<>()[]:.;,'] */
void error_line(const char * msg) { // 终端输出红色错误
    printf("%c%s%c%s", 0x1b, "[31m错误：", 0x1b, "[0m");
    printf(msg);
}
int main() {
    system("chcp 65001"); // 使用 UTF-8 编码
    printf("请键入文件名: \n");
    char file_name[80];
    scanf("%s", &file_name);
    yyin = fopen(file_name, "r");
    if (!yyin) {
        error_line("找不到文件。\n");
        return 0;
    }

    int type;

    while (type = yylex()) {
        row_num += yyleng; // 更新列号
        if (type == TYPE_COMMENT) continue;
        if (type == TYPE_UNKNOWN) {
            error_line(NULL);
            printf("%d 行 %d 列有非法字符 %s\n", line_num, row_num, yytext);
        } else if (type == 61) {
            error_line(NULL);
            printf("%d 行缺少 ’\n", line_num);
        } else if (type == 49) {
            error_line(NULL);
            printf("%d 行缺少 */\n", line_num);
        } else if (type == TYPE_INTEGER | type == TYPE_STRING | type == TYPE_IDENTIFIER) {
            int id = 1;
            struct node *now = head;
            if (!now) {
                head = (struct node *) malloc(sizeof(struct node));
                memset(head, 0, sizeof(struct node));
                strcpy(head->elem, yytext);
            } else while (1) {
                if (!strcmp(now->elem, yytext)) {
                    break;
                } else {
                    if (now->next) {
                        now = now->next;
                        ++id;
                    } else {
                        now->next = (struct node *) malloc(sizeof(struct node));
                        memset(now->next, 0, sizeof(struct node));
                        strcpy(now->next->elem, yytext);
                        ++id;
                        break;
                    }
                }
            }
            printf("(%d, %d)\n", type, id);
        }
        else printf("(%d, %s)\n", type, "-");

    }
    while (head) {
        struct node *current = head;
        head = head->next;
        free(current);
    }
    fclose(yyin);
    return 0;
}
int yywrap() {
    return 1;
}