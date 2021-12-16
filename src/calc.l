%option noyywrap
%option yylineno

%{
    #include "tokens.h"
%}

%%
"-" { return SUB; }
"=" { return '='; }
"==" { return EQUAL; }
"/" { return DIV; }
"(" { return '('; }
")" { return ')'; }
"," { return ','; }
";" { return ';'; }
">" { return '>'; }
"<" { return '<'; }
"let" { return LET; }
"if" { return IF; }
"endif" { return ENDIF; }
"else" { return ELSE; }
"then" { return THEN; }
"readFloat" { return READ_FLOAT; }
"printf" { return PRINT; }
"float" { return FLOAT_TYPE; }
"return" { return RETURN; }
[0-9]+"."[0-9]+ { yylval.float_t = atof(yytext); return FLOAT; }
[a-zA-Z][a-zA-Z0-9]* { yylval.string_t = strdup(yytext); return ID; }
\".*\" { yylval.string_t = strdup(yytext); return STRING;}
[\n] { return EOL; }
[ \t] { /* ignorar */ }
. { printf("invalido %c\n", yytext[0]); }
%%