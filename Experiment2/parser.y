%{
    #include <stdio.h>
    #include <stdlib.h>
    #include <string.h>
    extern FILE *yyin;
    extern char * yytext;
    int out_num = 0;
    extern int line_num;
    extern int row_num;
    int temp_var_num = 0;
    // 这里存放输出的四元式，一个结点最多存放 128 条四元式
    struct Buffer {
        char *buffer[128];
        struct Buffer *next;
    };
    struct Buffer *buffer_head = 0;
    char * alloc_temp_var();
    struct BoolExp {
        char *var_name; // var_name = 0 说明此时不是最根部
        struct BoolExp * op1;
        int op_type; // 0 - not | 1 - and | 2 - or | 3 - < | 4 - <= | 5 - = | 6 - >= | 7 - > | 8 - <>
        struct BoolExp * op2;
        int true_exit;
        int false_exit;
        char *var_name_sec; // 第二操作数名称
        int length; // 执行这个 Exp 需要预留的行数
    };
    // 出口
    struct Exits {
        int true_exit;
        int false_exit;
    };
    void output_3AddrCode(int line_num, const char * ch1, const char * ch2, const char * ch3, const char * ch4);
    const struct Exits fill_back(int start_line, struct BoolExp * exp, int true_exit, int false_exit);
    void fill_chain(int chain_tail, int move_target);
    const char *get_op_str(int op_type_id);
    void finish_compile();
    // 链表保存在分析出变量类型前的变量名，以便稍后加入到符号表中
    struct StrList {
        const char *name;
        struct StrList *next;
    };
    extern void add_symbol(const char *name, const unsigned char type);
%}
// 只实现了文档里面给的要求，有大量的 token 定义了没用到（我是直接从那边复制进来的，没把多余的删掉）
%token TYPE_COMMENT
%token TYPE_UNKNOWN
%token TYPE_IDENTIFIER_UNKNOWN
%token TYPE_IDENTIFIER_INT
%token TYPE_IDENTIFIER_BOOL
%token TYPE_INTEGER
%token TYPE_STRING
// keywords 
%token KW_AND
%token KW_ARRAY
%token KW_BEGIN
%token KW_BOOL
%token KW_CALL
%token KW_CASE
%token KW_CHAR
%token KW_CONSTANT
%token KW_DIM
%token KW_DO
%token KW_ELSE
%token KW_END
%token KW_FALSE
%token KW_FOR
%token KW_IF
%token KW_INPUT
%token KW_INTEGER
%token KW_NOT
%token KW_OF
%token KW_OR
%token KW_OUTPUT
%token KW_PROCEDURE
%token KW_PROGRAM
%token KW_READ
%token KW_REAL
%token KW_REPEAT
%token KW_SET
%token KW_STOP
%token KW_THEN
%token KW_TO
%token KW_TRUE
%token KW_UNTIL
%token KW_VAR
%token KW_WHILE
%token KW_WRITE
// 符号
%token LEFT_BRACKET
%token RIGHT_BRACKET
%token STAR
%token PLUS
%token COMMA
%token MINUS
%token SINGLE_DOT
%token DOUBLE_DOT
%token LEFT_DASH
%token START_COMMENT
%token COLON
%token ASSIGN
%token SEMICOLON
%token LESSTHAN
%token LESSEQUALTHAN
%token NOTEQUAL
%token EQUAL
%token BIGGERTHAN
%token BIGGEREQUALTHAN
%token LEFT_SQUARE_BRACKET
%token RIGHR_SQUARE_BRACKET
%token SINGLE_QUOTE
%union {
    int num;
    char *str;
    unsigned char var_type; // 0 - integer | 1 - bool | 2 - char
    int range[3]; // range[0] - 起始行 | range[1] - 终止行 | range[2] - 语句出口
    void *bool_exp; // 跳转到链
    void *str_list; // 保存一次声明的所有变量的名字
}
%type <num> TYPE_INTEGER relation_op if then else while do repeat until// 这些表达式用的是 num
%type <str> TYPE_IDENTIFIER_UNKNOWN TYPE_IDENTIFIER_INT TYPE_IDENTIFIER_BOOL arithmetic_expression item factor arithmetic_value boolean_const// 这些表达式用的是 str
%type <var_type> KW_BOOL KW_CHAR KW_INTEGER type
%type <range> statement assignment_statement if_statement while_statement repeat_statement compound_statement statement_table
%type <bool_exp> boolean_expression boolean_item boolean_factor boolean_value
%type <str_list> identifier_table
%left PLUS MINUS
%left STAR LEFT_DASH
%right KW_NOT
%left KW_AND
%left KW_OR
%nonassoc IFX
%nonassoc KW_ELSE
%start program
%%
if: // 记录此时的行号
    KW_IF {$$ = out_num;};
then:
    KW_THEN {$$ = out_num;};
else:
    KW_ELSE {$$ = out_num++;};
while:
    KW_WHILE {$$ = out_num;};
do:
    KW_DO {$$ = out_num;};
repeat:
    KW_REPEAT {$$ = out_num;};
until:
    KW_UNTIL {$$ = out_num;};

program: // 程序
    program_line var_declaration compound_statement SINGLE_DOT {
        output_3AddrCode(out_num++, "sys", "-", "-", "-");
        fill_chain($3[2], out_num - 1);/* 回填语句块 */
        finish_compile();
        } ;
program_line: // 程序的第一行
    KW_PROGRAM TYPE_IDENTIFIER_UNKNOWN SEMICOLON {output_3AddrCode(out_num++, "program", $2, "-", "-");};
var_declaration: // 变量声明
    KW_VAR var_definition
    |
    ;
var_definition: // 变量定义，把标识符表里的变量都给记录上变量类型是 type
    identifier_table COLON type SEMICOLON var_definition {
        struct StrList *p = $1;
        while (p != NULL) {
            add_symbol(p->name, $3);
            p = p->next;
        }
    }
    |identifier_table COLON type SEMICOLON {
        struct StrList *p = $1;
        while (p != NULL) {
            add_symbol(p->name, $3);
            p = p->next;
        }
    };
identifier_table: // 标识符表
    TYPE_IDENTIFIER_UNKNOWN COMMA identifier_table {
        /*把 TYPE_IDENTIFIER 加入已有的表里*/
        struct StrList *new_node = malloc(sizeof(struct StrList));
        new_node->name = $1;
        new_node->next = $3;
        $$ = new_node;
    }
    |TYPE_IDENTIFIER_UNKNOWN {
        /* 新建表 */
        $$ = malloc(sizeof(struct StrList));
        struct StrList *p = $$;
        p->name = $1;
        p->next = NULL;
    };
type: // 类型
    KW_INTEGER {$$ = 0;}| KW_BOOL {$$ = 1;}| KW_CHAR {$$ = 2;};

compound_statement: // 复合语句
    KW_BEGIN statement_table KW_END {memcpy($$, $2 ,sizeof(int) * 3);};
statement_table: // 语句表
    statement SEMICOLON statement_table {$$[0]= $1[0]; $$[1] = $3[1]; fill_chain($1[2], $3[0]);/* 回填地址 $1[2] */ $$[2] = $3[2];} 
    | statement {memcpy($$, $1 ,sizeof(int)*3);};// 这里不回填
statement: // 语句
    assignment_statement  {memcpy($$, $1 ,sizeof(int) * 3);} // 把具体语句的范围和出口复制到 statement 里面
    | if_statement {memcpy($$, $1 ,sizeof(int) * 3);}
    | while_statement {memcpy($$, $1 ,sizeof(int) * 3);}
    | repeat_statement {memcpy($$, $1 ,sizeof(int) * 3);}
    | compound_statement {memcpy($$, $1 ,sizeof(int) * 3);};
assignment_statement: // 赋值句
    TYPE_IDENTIFIER_INT ASSIGN arithmetic_expression {
        $$[0] = out_num;
        $$[1] = out_num + 1;
        $$[2] = 0; // 赋值句不用被回填
        char name1[128];
        sprintf(name1, "%s", $3);
        char name2[128];
        sprintf(name2, "%s", $1);
        output_3AddrCode(out_num++, ":=", name1, "-", name2);
    }; 
if_statement: // if 语句
    if boolean_expression then statement %prec IFX {
        $$[0] = $1;
        $$[1] = $4[1];
        const struct Exits exit = fill_back($1, $2, 0, $4[2]); // 在外部调用此函数时，真假出口必须置 0 （0 是链首的标志）
        fill_chain(exit.true_exit, $3); // 直接把真链回填
        $$[2] = exit.false_exit; // 语句出口设为假链的尾部
    }
    |if boolean_expression then statement else statement {
        // debug printf("The exit of else-statement is %d\n", $6[2]);
        $$[0] = $1;
        $$[1] = $6[1];
        const struct Exits exit = fill_back($1, $2, 0, $4[2]); 
        fill_chain(exit.true_exit, $3);
        fill_chain(exit.false_exit, $5 + 1); // + 1 是因为要给 then 末尾的无条件跳转留下一行
        char num[128];
        sprintf(num, "%d", $6[2]);
        output_3AddrCode($5, "j", "-", "-", num); // 这行是 then 末尾的出口，指向链上的 else 出口
        $$[2] = $5;
    };
while_statement: // while 语句
    while boolean_expression do statement {
        $$[0] = $1;
        $$[1] = $4[1] + 1; // 末尾多一行跳转到条件判断，所以 + 1
        const struct Exits exit = fill_back($1, $2, 0, 0);
        $$[2] = exit.false_exit;
        fill_chain(exit.true_exit, $3);
        char num[128];
        sprintf(num, "%d", $1);
        output_3AddrCode(out_num++, "j", "-", "-", num); // 末尾跳回循环开头
        // debug printf("fill back %d\n", $4[2]);
        fill_chain($4[2], $1);
    };
repeat_statement: // repeat 语句
    repeat statement until boolean_expression {
        $$[0] = $1;
        $$[1] = $3 + ((struct BoolExp*)($4))->length;
        const struct Exits exit = fill_back($3, $4, 0, 0);
        fill_chain(exit.false_exit, $1); // repeat 里假出口反而是可以立即回填的
        $$[2] = exit.true_exit; // 出口是真出口
        fill_chain($2[2], $3);
    };

arithmetic_expression: // 算术表达式（我这里没有进行合并已知量）
    arithmetic_expression PLUS item { $$ = alloc_temp_var(); output_3AddrCode(out_num++, "+", $1, $3, $$);/* $$ = $1 + $3; */} |
    arithmetic_expression MINUS item {$$ = alloc_temp_var(); output_3AddrCode(out_num++, "-", $1, $3, $$);/* $$ = $1 - $3; */} |
    item {$$ = strdup($1);};
item: // 项
    item STAR factor { $$ = alloc_temp_var(); output_3AddrCode(out_num++, "*", $1, $3, $$);/* $$ = $1 * $3; */}|
    item LEFT_DASH factor { $$ = alloc_temp_var(); output_3AddrCode(out_num++, "/", $1, $3, $$);/* $$ = $1 / $3; */}|
    factor {$$ = strdup($1);};
factor: // 因子，要在这里赋值
    arithmetic_value {$$ = strdup($1);} |
    MINUS factor {/* $$ = -$1; */};
arithmetic_value: // 算术量
    TYPE_INTEGER {char temp[128]; sprintf(temp, "%d", $1); $$ = strdup(temp);}|
    TYPE_IDENTIFIER_INT {$$ = strdup($1);}|
    LEFT_BRACKET arithmetic_expression RIGHT_BRACKET {$$ = strdup($2);};

boolean_expression: // 布尔表达式，也要赋值
    boolean_expression KW_OR boolean_item {
            $$ = malloc(sizeof(struct BoolExp));
            struct BoolExp *p = (struct BoolExp*)$$;
            p->var_name = 0;
            p->op1 = $1;
            p->op_type = 2;
            p->op2 = $3;
            p->length = ((struct BoolExp*)$1)->length + ((struct BoolExp*)$3)->length;
        }|
    boolean_item {$$ = $1;};
boolean_item: // 布尔项，也要短路计算
    boolean_item KW_AND boolean_factor {
            $$ = malloc(sizeof(struct BoolExp));
            struct BoolExp *p = (struct BoolExp*)$$;
            p->var_name = 0;
            p->op1 = $1;
            p->op_type = 1;
            p->op2 = $3;
            p->length = ((struct BoolExp*)$1)->length + ((struct BoolExp*)$3)->length;
        } |
    boolean_factor {$$ = $1;};
boolean_factor: // 布因子
    boolean_value {$$ = $1;} |
    KW_NOT boolean_factor {
            $$ = malloc(sizeof(struct BoolExp));
            struct BoolExp *p = (struct BoolExp*)$$;
            p->var_name = (char *)1; // 这个地方不能为 0，0 是用来判断是否来到了布尔表达式的底层的
            p->var_name_sec = 0; // 不把 not 看成第二操作数，not 是通过 op_type = 0 来判断的
            p->op1 = $2;
            p->op_type = 0;
            p->op2 = 0;
            p->length = ((struct BoolExp*)$2)->length;
        } ;
boolean_value: // 布尔量
    boolean_const {
            $$ = malloc(sizeof(struct BoolExp));
            struct BoolExp *p = (struct BoolExp*)$$;
            p->var_name = $1;
            p->var_name_sec = 0;
            p->length = 2;
            out_num += 2;
        } | 
    TYPE_IDENTIFIER_BOOL {
            $$ = malloc(sizeof(struct BoolExp));
            struct BoolExp *p = (struct BoolExp*)$$;
            p->var_name = $1;
            p->var_name_sec = 0;
            p->length = 2;
            out_num += 2;
        } |
    LEFT_BRACKET boolean_expression RIGHT_BRACKET {$$ = $2;}|
    //TYPE_IDENTIFIER relation_op TYPE_IDENTIFIER | 文档里这句是和 arithmetic_value 有冲突的，在这里我选择把这种形式的交给 arithmetic_value 处理
    arithmetic_expression relation_op arithmetic_expression {
            $$ = malloc(sizeof(struct BoolExp));
            struct BoolExp *p = (struct BoolExp*)$$;
            p->var_name = $1;
            p->op_type = $2;
            p->var_name_sec = $3;
            p->length = 2;
            out_num += 2;
        };
relation_op: // 关系符  3 - < | 4 - <= | 5 - = | 6 - >= | 7 - > | 8 - <>
    LESSTHAN {$$ = 3;}|
    NOTEQUAL {$$ = 8;}|
    LESSEQUALTHAN {$$ = 4;}|
    BIGGEREQUALTHAN {$$ = 6;}|
    BIGGERTHAN {$$ = 7;}|
    EQUAL {$$ = 5;};
boolean_const:
    KW_TRUE {$$ = strdup("true");}|
    KW_FALSE {$$ = strdup("false");};
%%
void yyerror(const char * msg) { // 终端输出红色错误
    printf("%c%s%c%s", 0x1b, "[31m错误：", 0x1b, "[0m");
    printf("第 %d 行，第 %d 列：", line_num, row_num);
    printf("%s\n", yytext);
    printf(msg);
}
char * alloc_temp_var() { // 临时变量
    char *name = (char*) malloc(128);
    sprintf(name, "T%d", ++temp_var_num);
    return name;
}
// 把三地址语句（四元式）输出到缓冲区里面而不是立即输出到标准输出流中，
// 这一方面是因为在翻译时 while、if 等语句中会先输出 boolean_expression 后面的 statement，
// 另一方面是为了事后回填
void output_3AddrCode(int line_num, const char * ch1, const char * ch2, const char * ch3, const char * ch4) {
    if (!buffer_head) {
        buffer_head = (struct Buffer *) malloc(sizeof(struct Buffer));
        buffer_head->next = 0;
    }
    struct Buffer *p = buffer_head;
    int i = 1;
    while (1) {
        if ((i << 7) < line_num) {
            if (p->next == 0) {
                p->next = (struct Buffer *) malloc(sizeof(struct Buffer));
            }
            p = p->next;
            ++i;
        } else {
            p->buffer[line_num % 128] = malloc(128);
            sprintf(p->buffer[line_num % 128], "(%d) (%s, %s, %s, %s)\n", line_num, ch1, ch2, ch3, ch4);
            break;
        }
    }
}
void finish_compile() { // 编译完成，输出缓冲区里的四元式
    struct Buffer *p = buffer_head;
    for (int i = 0; i < out_num; ++i) {
        if (i % 128 == 0 && i != 0) {
            p = p->next;
        }
        printf(p->buffer[i % 128]);
    }
}
const char *get_op_str(int op_type_id) {
    // 0 - not | 1 - and | 2 - or | 3 - < | 4 - <= | 5 - = | 6 - >= | 7 - > | 8 - <>
    if (op_type_id == 0) return "not";
    if (op_type_id == 1) return "and";
    if (op_type_id == 2) return "or";
    if (op_type_id == 3) return "j<";
    if (op_type_id == 4) return "j<=";
    if (op_type_id == 5) return "j=";
    if (op_type_id == 6) return "j>=";
    if (op_type_id == 7) return "j>";
    if (op_type_id == 8) return "j<>";
}
// 返回真假两条链
const struct Exits fill_back(int start_line, struct BoolExp * exp, int true_exit, int false_exit) {
    if (exp->var_name && exp->var_name_sec) { // 最底层， A < B 这种的
        char *true_exit_str = (char *) malloc(128);
        sprintf(true_exit_str, "%d", true_exit);
        char *false_exit_str = (char *) malloc(128);
        sprintf(false_exit_str, "%d", false_exit);
        output_3AddrCode(start_line, get_op_str(exp->op_type), exp->var_name, exp->var_name_sec, true_exit_str);
        output_3AddrCode(start_line + 1, "j", "-", "-", false_exit_str);
        const struct Exits exit = {start_line, start_line + 1};
        return exit;
    } else if (exp->var_name) { // 最底层，A ， true 这种的；或者 not Exp
        if (exp->op_type == 0) { // not Exp
            struct Exits exit = fill_back(start_line, exp->op1, false_exit, true_exit);
            int exchange = exit.true_exit;
            exit.true_exit = exit.false_exit;
            exit.false_exit = exchange;
            return exit;
        } else {
            char *true_exit_str = (char *) malloc(128);
            sprintf(true_exit_str, "%d", true_exit);
            char *false_exit_str = (char *) malloc(128);
            sprintf(false_exit_str, "%d", false_exit);
            output_3AddrCode(start_line, "j=", exp->var_name, "true", true_exit_str);
            output_3AddrCode(start_line + 1, "j", "-", "-", false_exit_str);
            const struct Exits exit = {start_line, start_line + 1};
            return exit;
        }
    } else { // 非底层
        if (exp->op_type == 1) { // and
            int return_exit = fill_back(start_line, exp->op1, start_line + exp->op1->length, false_exit).false_exit;
            return fill_back(start_line + exp->op1->length, exp->op2, true_exit, return_exit);
        } else if (exp->op_type == 2) { // or
            int return_exit = fill_back(start_line, exp->op1, true_exit, start_line + exp->op1->length).true_exit;
            return fill_back(start_line + exp->op1->length, exp->op2, return_exit, false_exit);
        }
    }
}
// 回填
void fill_chain(int chain_tail, const int move_target) {
    char ch1[128], ch2[128], ch3[128];
    while (chain_tail != 0) {
        // debug printf("tail=%d, moveto%d\n", chain_tail, move_target);
        // 先找到对应的组，
        int i = 128;
        struct Buffer *p = buffer_head;
        while (i < chain_tail) {
            i = i + 128;
            if (p->next) p = p->next;
            else {yyerror("访问不存在的缓冲区。\n"); return;}
        }
        int line_num, predecessor = -1;
        sscanf(p->buffer[chain_tail % 128], "(%d) (%s %s %s %d)\n", &line_num, ch1, ch2, ch3, &predecessor);
        if (predecessor == -1) {
            // 来到了链首了
            yyerror("真假链没有正确连接。\n");
            return;
        }
        sprintf(p->buffer[chain_tail % 128], "(%d) (%s %s %s %d)\n", line_num, ch1, ch2, ch3, move_target);
        chain_tail = predecessor;
    }
}
int main() {
    system("chcp 65001"); // 使用 UTF-8 编码，从而能够在 Windows 控制台输出中文
    printf("请键入文件名: \n");
    char file_name[80];
    scanf("%s", &file_name);
    yyin = fopen(file_name, "r");
    if (!yyin) {
        yyerror("找不到文件。\n");
        return 0;
    }
    yyparse();
    fclose(yyin);
    return 0;
}
