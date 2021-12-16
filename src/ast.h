#ifndef _AST_H_
#define _AST_H_

#include <list>
#include <string>
#include "code.h"

using namespace std;

enum StatementKind{
    IF_STATEMENT,
    EXPRESSION_STATEMENT,
    ASSIGNATION_STATEMENT,
    PRINT_STATEMENT,
    RETURN_STATEMENT,
    METHOD_DEFINITION_STATEMENT
};

class Expr{
    public:
        virtual void genCode(Code &code) = 0;
};

class Statement;

typedef list<Statement *> StatementList;
typedef list<Expr *> ExprList;

class BinaryExpr: public Expr{
    public:
        BinaryExpr(Expr * expr1, Expr * expr2){
            this->expr1 = expr1;
            this->expr2 = expr2;
        }
        Expr * expr1;
        Expr * expr2;
};

class EqExpr: public BinaryExpr{
    public:
        EqExpr(Expr * expr1, Expr * expr2): BinaryExpr(expr1, expr2){

        }
        void genCode(Code &code);
};

class SubExpr : public BinaryExpr{
    public:
        SubExpr(Expr * expr1, Expr * expr2): BinaryExpr(expr1, expr2){

        }
        void genCode(Code &code);
};

class DivExpr : public BinaryExpr{
    public:
        DivExpr(Expr * expr1, Expr * expr2): BinaryExpr(expr1, expr2){

        }
        void genCode(Code &code);
};

class GteExpr : public BinaryExpr{
    public:
        GteExpr(Expr * expr1, Expr * expr2): BinaryExpr(expr1, expr2){

        }
        void genCode(Code &code);
};

class LteExpr : public BinaryExpr{
    public:
        LteExpr(Expr * expr1, Expr * expr2): BinaryExpr(expr1, expr2){

        }
        void genCode(Code &code);
};

class FloatExpr: public Expr{
    public:
        FloatExpr(float number){
            this->number = number;
        }
        float number;
        void genCode(Code &code);
};

class IdExpr : public Expr{
    public:
        IdExpr(string id){
            this->id = id;
        }
        string id;
        void genCode(Code &code);
};

class MethodInvocationExpr : public Expr{
    public:
        MethodInvocationExpr(string id, ExprList expressions){
            this->id = id;
            this->expressions = expressions;
        }
        string id;
        void genCode(Code &code);
        ExprList expressions;
};


class ReadFloatExpr: public Expr{
    public:
        ReadFloatExpr(){

        }
    void genCode(Code &code);
};


class Statement{
    public:
        virtual string genCode() = 0;
        virtual StatementKind getKind() = 0;
};

class IfStatement : public Statement{
    public:
        IfStatement(Expr * conditionalExpr, StatementList trueStatement, StatementList falseStatement){
            this->conditionalExpr = conditionalExpr;
            this->trueStatement = trueStatement;
            this->falseStatement = falseStatement;
        }
        Expr * conditionalExpr;
        StatementList trueStatement;
        StatementList falseStatement;
        string genCode();
        StatementKind getKind(){return IF_STATEMENT;}
};

class ExprStatement : public Statement{
    public:
        ExprStatement(Expr * expr){
            this->expr = expr;
        }
        Expr * expr;
        string genCode();
        StatementKind getKind(){return EXPRESSION_STATEMENT;}
};

class MethodDefinitionStatement : public Statement{
    public:
        MethodDefinitionStatement(string id, StatementList stmts, list<string> params, bool isVoid){
            this->id = id;
            this->stmts = stmts;
            this->params = params;
            this->isVoid = isVoid;
        }
        string id;
        StatementList stmts;
        list<string> params;
        bool isVoid;
        string genCode();
        StatementKind getKind(){return METHOD_DEFINITION_STATEMENT;}
};

class AssignationStatement: public Statement{
    public:
        AssignationStatement(string id, Expr * value, ExprList expressions){
            this->id = id;
            this->value = value;
            this->expressions = expressions;
        }
        string id;
        Expr * value;
        ExprList expressions;
        string genCode();
        StatementKind getKind(){return ASSIGNATION_STATEMENT;}
};

class PrintStatement: public Statement{
    public:
        PrintStatement(string id, ExprList expressions){
            this->id = id;
            this->expressions = expressions;
        }
        string id;
        ExprList expressions;
        string genCode();
        StatementKind getKind(){return PRINT_STATEMENT;}
};

class ReturnStatement: public Statement{
    public:
        ReturnStatement(Expr * expr){
            this->expr = expr;
        }
        Expr * expr;
        string genCode();
        StatementKind getKind(){return RETURN_STATEMENT;}
};
#endif