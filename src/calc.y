%code requires{
    #include "ast.h"
}

%{
    #include <cstdio>
    #include "asm.h"
    #include <fstream>
    #include <iostream>
    using namespace std;
    int yylex();
    extern int yylineno;
    void yyerror(const char * s){
        fprintf(stderr, "Line: %d, error: %s\n", yylineno, s);
    }

    #define YYERROR_VERBOSE 1

    Asm assemblyFile;

    void writeFile(string name){
        ofstream file;
        file.open(name);
        file << assemblyFile.data << endl
        << assemblyFile.global <<endl
        << assemblyFile.text << endl;
        file.close();
    }
%}

%union{
    float float_t;
    char * string_t;
    Expr * expr_t;
    Statement * statement_t;
    ExprList * expr_list_t;
    StatementList * statement_list_t;
    list<string> * string_list_t;
}

%token EOL
%token SUB FLOAT_TYPE DIV IF THEN ENDIF ELSE LET READ_FLOAT PRINT RETURN EQUAL
%token<float_t> FLOAT
%token<string_t> ID STRING
%type<expr_t> exp factor term additive_expr relational_expr
%type<expr_list_t> expression_list
%type<statement_list_t> statements calc_list
%type<statement_t> statement
%type<string_list_t> ids

%%

start: calc_list{
    assemblyFile.global = ".globl main";
    assemblyFile.data = ".data\n";
    assemblyFile.text = ".text\n";
    string code;
    list<Statement *>::iterator it = $1->begin();
    while(it != $1->end()){
        code += (*it)->genCode();
        it++;
    }
    assemblyFile.text += code;
    writeFile("result.s");
}

calc_list: /* nada */ {$$ = new StatementList;}
         | calc_list statement EOL  {$$ = $1; $$->push_back($2);}
         | calc_list LET FLOAT_TYPE ID '(' ids  ')' '=' statements EOL {$$ = $1;  $$->push_back(new MethodDefinitionStatement($4, *$9, *$6, false));}
         | calc_list LET FLOAT_TYPE ID '(' ')' '=' statements EOL {$$ = $1;  $$->push_back(new MethodDefinitionStatement($4, *$8, *(new list<string>), false));}
         | calc_list LET ID '(' ids  ')' '=' statements EOL {$$ = $1;  $$->push_back(new MethodDefinitionStatement($3, *$8, *$5, true));}
         | calc_list LET ID '(' ')' '=' statements EOL {$$ = $1;  $$->push_back(new MethodDefinitionStatement($3, *$7, *(new list<string>), true));}
         ;

ids: ids ',' ID {$$ = $1; $$->push_back($3);}
   | ID {$$ = new list<string>; $$->push_back($1);}
   ;

statement: IF exp THEN statements ENDIF  {$$ = new IfStatement($2, *$4, *(new StatementList)); }
        |  IF exp THEN statements ELSE statements ENDIF {$$ = new IfStatement($2, *$4, *$6); }
        |  PRINT '(' STRING ',' expression_list ')' {$$ = new PrintStatement($3, *$5);}
        |  exp { $$ = new ExprStatement($1);}
        |  ID '=' exp {$$ = new AssignationStatement($1, $3, *(new ExprList));}
        |  RETURN exp  {$$ = new ReturnStatement($2);}
        ;

statements: statement { $$ = new StatementList; $$->push_back($1); }
          | statements ';' statement { $$ = $1; $$->push_back($3); }
          ;

expression_list: exp { $$ = new ExprList; $$->push_back($1); }
               | expression_list ',' exp { $$ = $1; $$->push_back($3); }
               ;



exp: exp EQUAL relational_expr {$$ = new EqExpr($1, $3);}
    | relational_expr {$$ = $1;}

relational_expr:  relational_expr '>' additive_expr {$$ = new GteExpr($1, $3);}
    | relational_expr '<' additive_expr {$$ = new LteExpr($1, $3);}
    | additive_expr {$$ = $1;}
    ;

 additive_expr: additive_expr SUB factor {$$ = new SubExpr($1, $3); }
    | factor { $$ = $1; }
    ;

factor: factor DIV term { $$ = new DivExpr($1, $3); }
    | term { $$ = $1; }
    ;

term: FLOAT { $$ = new FloatExpr($1); }
    | '('exp')' { $$ = $2; }
    | ID { $$ = new IdExpr($1);}
    | ID '(' expression_list ')' { $$ = new MethodInvocationExpr($1, *$3);}
    | READ_FLOAT '(' ')' {$$ = new ReadFloatExpr();}
    ;

%%
