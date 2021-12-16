#include "ast.h"
#include <iostream>
#include <sstream>
#include <set>
#include "asm.h"


const char * floatTemps[] = {"$f0","$f1","$f2","$f3","$f4","$f5","$f6","$f7","$f8","$f9","$f10","$f11","$f12","$f13","$f14","$f15","$f16","$f17","$f18","$f19","$f20","$f21","$f22","$f23","$f24","$f25","$f26","$f27","$f28","$f29","$f30","$f31"};


#define FLOAT_TEMP_COUNT 32
set<string> intTempMap;
set<string> floatTempMap;
map<string, VariableInfo *> codeGenerationVars;

extern Asm assemblyFile;
int labelCounter = 0;
int globalStackPointer = 0;

string getNewLabel(string prefix){ 
    stringstream ss;
    ss<<prefix << labelCounter;
    labelCounter++;
    return ss.str();
}

string saveState(){
    set<string>::iterator it = floatTempMap.begin();
    stringstream ss;
    ss<<"sw $ra, " <<globalStackPointer<< "($sp)\n";
    globalStackPointer+=4;
    return ss.str();
}

string retrieveState(string state){
    std::string::size_type n = 0;
    string s = "sw";
    while ( ( n = state.find( s, n ) ) != std::string::npos )
    {
    state.replace( n, s.size(), "lw" );
    n += 2;
    globalStackPointer-=4;
    }
    return state;
}

class VariableInfo{
    public:
        VariableInfo(int offset, bool isParameter){
            this->offset = offset;
            this->isParameter = isParameter;
        }
        int offset;
        bool isParameter;
};

string getFloatTemp(){
    for (int i = 0; i < FLOAT_TEMP_COUNT; i++)
    {
        if(floatTempMap.find(floatTemps[i]) == floatTempMap.end()){
            floatTempMap.insert(floatTemps[i]);
            return string(floatTemps[i]);
        }
    }
    cout<<"No more float registers!"<<endl;
    return "";
}

void releaseFloatTemp(string temp){
    floatTempMap.erase(temp);
}

void FloatExpr::genCode(Code &code){
    string floatTemp = getFloatTemp();
    code.place = floatTemp;
    stringstream ss;
    ss << "li.s " << floatTemp <<", "<< this->number <<endl;
    code.code = ss.str();
}

void SubExpr::genCode(Code &code){
    Code leftCode, rightCode;
    stringstream ss;
    this->expr1->genCode(leftCode);
    this->expr2->genCode(rightCode);
    releaseFloatTemp(leftCode.place);
    releaseFloatTemp(rightCode.place);
    ss << leftCode.code << endl
    << rightCode.code <<endl
    << floatArithmetic(leftCode, rightCode, code, '-')<<endl;
    code.code = ss.str();
}

void DivExpr::genCode(Code &code){
    Code leftCode, rightCode;
    stringstream ss;
    this->expr1->genCode(leftCode);
    this->expr2->genCode(rightCode);
    releaseFloatTemp(leftCode.place);
    releaseFloatTemp(rightCode.place);
    ss << leftCode.code << endl
    << rightCode.code <<endl
    << floatArithmetic(leftCode, rightCode, code, '/')<<endl;
    code.code = ss.str();
}

void IdExpr::genCode(Code &code){
    string floatTemp = getFloatTemp();
    code.place = floatTemp;
    code.code = "l.s "+ floatTemp + ", " + to_string(codeGenerationVars[this->value]->offset) +"($sp)\n";
}

string ExprStatement::genCode(){
    return "Expr statement code generation\n";
}

string IfStatement::genCode(){
    stringstream code;
    string elseLabel = getNewLabel("elseif");
    string endIfLabel = getNewLabel("endElseif");
    Code exprCode;
    string floatTemp = getFloatTemp();
    this->conditionalExpr->genCode(exprCode);
    code << exprCode.code << endl;
    ss << "li.s " << floatTemp <<", 0.0"<<endl;
    ss << "c.eq.s " << exprCode.place << ", " << floatTemp + "\n";
    ss << "bc1t " << elseLabel  + "\n";

    list<Statement *>::iterator iTrue = this->trueStatement.begin(); //IF
    while (iTrue != this->trueStatement.end()){
        Statement * dec = *iTrue;
        if(dec != NULL){
            code<<dec->genCode() << endl;
        }
        iTrue++;
    }
    code << "j " <<endIfLabel << endl
    << elseLabel <<": " <<endl;

    list<Statement *>::iterator itFalse = this->falseStatement.begin();//ELSE
    while (itFalse != this->falseStatement.end()){
        Statement * dec = *itFalse;
        if(dec != NULL){
            code<<dec->genCode() << endl;
        }
        itFalse++;
    }

    code << endIfLabel <<":"<< endl;
    releaseFloatTemp(exprCode.place);
    return code.str();

}

void MethodInvocationExpr::genCode(Code &code){
    list<Expr *>::iterator it = this->expressions.begin();
    list<Code> codes;
    stringstream ss;
    Code argCode;
    while (it != this->expressions.end())
    {
        (*it)->genCode(argCode);
        ss << argCode.code <<endl;
        codes.push_back(argCode);
        it++;
    }

    int i = 0;
    list<Code>::iterator placesIt = codes.begin();
    while (placesIt != codes.end())
    {
        releaseRegister((*placesIt).place);
        ss << "mfc1 $a"<<i<<", "<< (*placesIt).place<<endl;
        i++;
        placesIt++;
    }

    ss<< "jal "<< this->id->id<<endl;
    string reg;
    reg = getFloatTemp();
    ss << "mtc1 $v0, "<< reg<<endl;
    
    code.code = ss.str();
    code.place = reg;
    code.type = methods[this->id->id]->returnType;
}

string AssignationStatement::genCode(){
    return "Assignation statement code generation\n";
}

void GteExpr::genCode(Code &code){
    Code leftSideCode; 
    Code rightSideCode;
    stringstream ss;
    this->expr1->genCode(leftSideCode);
    this->expr2->genCode(rightSideCode);
    ss << leftSideCode.code << endl
    << rightSideCode.code <<endl;
    string temp = getFloatTemp();
    string label = getNewLabel("label");
    string finalLabel = getNewLabel("finalLabel");
     ss <<" li.s " << temp <<" , 0.0"<<endl;
    ss << "c.le.s " << leftSideCode.place << ", " << rightSideCode.place + "\n"; 
    ss << "bc1f " << label  + "\n";
    ss << " j " << finalLabel <<endl;
    ss<< label <<":"<<endl<< "add.s " << temp << ", $zero, 1.0"<<endl<<finalLabel<<":"<<endl;
    code.place = temp;
    releaseRegister(leftSideCode.place);
    releaseRegister(rightSideCode.place);
    code.code = ss.str();
}

void LteExpr::genCode(Code &code){
    Code leftSideCode; 
    Code rightSideCode;
    stringstream ss;
    this->expr1->genCode(leftSideCode);
    this->expr2->genCode(rightSideCode);
    ss << leftSideCode.code << endl
    << rightSideCode.code <<endl;
    string temp = getFloatTemp();
    string label = getNewLabel("label");
    string finalLabel = getNewLabel("finalLabel");
    ss <<" li.s " << temp <<" , 0.0"<<endl;
    ss << "c.lt.s " << leftSideCode.place << ", " << rightSideCode.place + "\n";
    ss << "bc1t " << label  + "\n";
    ss << " j " << finalLabel <<endl;
    ss<< label <<":"<<endl<< "add.s " << temp << ", $zero, 1.0"<<endl<<finalLabel<<":"<<endl;
    code.place = temp;
    releaseRegister(leftSideCode.place);
    releaseRegister(rightSideCode.place);
    code.code = ss.str();
}

void EqExpr::genCode(Code &code){
    Code leftSideCode; 
    Code rightSideCode;
    this->expr1->genCode(leftSideCode);
    this->expr2->genCode(rightSideCode);
    stringstream ss;
    code.type = FLOAT;
    toFloat(leftSideCode);
    toFloat(rightSideCode);
    ss << leftSideCode.code << endl
    << rightSideCode.code <<endl;
    string temp = getFloatTemp();
    string label = getNewLabel("label");
    string finalLabel = getNewLabel("finalLabel");
    ss <<" li.s " << temp <<" , 0.0"<<endl;
    ss << "c.eq.s " << leftSideCode.place << ", " << rightSideCode.place + "\n";
    ss << "bc1t " << label  + "\n";
    ss << " j " << finalLabel <<endl;
    ss<< label <<":"<<endl<< "add.s " << temp << ", $zero, 1.0"<<endl<<finalLabel<<":"<<endl;
    code.place = temp;
    releaseRegister(leftSideCode.place);
    releaseRegister(rightSideCode.place);
  
    code.code = ss.str();

}

void ReadFloatExpr::genCode(Code &code){
    
}

string PrintStatement::genCode(){
 list<Expr *>::iterator ite =  this->expressions.begin();
    stringstream code;
    code << "la $a0, "<< this->id<<endl 
    << "li $v0, 4"<<endl
    << "syscall"<<endl;

    while (ite != this->expressions.end())
    {
            Expr * expr = *ite;  
            Code exprCode;
            expr->genCode(exprCode);
            code<< exprCode.code<<endl;
            code << "mov.s $f12, "<< exprCode.place<<endl
            << "li $v0, 2"<<endl
            << "syscall"<<endl;
             
            releaseRegister(exprCode.place);
            ite++;
    }
  
    return code.str();
}

string ReturnStatement::genCode(){Code exprCode;
    this->expr->genCode(exprCode);
    releaseRegister(exprCode.place);
    stringstream ss;
    ss << exprCode.code << endl;
    ss<< "mfc1 $v0, "<<exprCode.place<<endl;
    return ss.str();
}

string MethodDefinitionStatement::genCode(){
    if(this->stmts == NULL)
        return "";

    int stackPointer = 4;
    globalStackPointer = 0;
    stringstream code;
    code << this->id<<": "<<endl;
    string state = saveState();
    code <<state<<endl;
    if(this->params.size() > 0){
        list<string *>::iterator it = this->params.begin();
        for(int i = 0; i< this->params.size(); i++){
            code << "sw $a"<<i<<", "<< stackPointer<<"($sp)"<<endl;
            codeGenerationVars[(*it)] = new VariableInfo(stackPointer, true);
            stackPointer +=4;
            globalStackPointer +=4;
            it++;
        }
    }
    list<Statement *>::iterator statem = this->stmts.begin();
    while (statem != this->stmts.end()){
        Statement * dec = *itFalse;
        if(dec != NULL){
            code<<dec->genCode() << endl;
        }
        statem++;
    }
    stringstream sp;
    int currentStackPointer = globalStackPointer;
    sp << endl<<"addiu $sp, $sp, -"<<currentStackPointer<<endl;
    code << retrieveState(state);
    code << "addiu $sp, $sp, "<<currentStackPointer<<endl;
    code <<"jr $ra"<<endl;
    codeGenerationVars.clear();
    string result = code.str();
    result.insert(id.size() + 2, sp.str());
    return result;
}

string floatArithmetic(Code &leftCode, Code &rightCode, Code &code, char op){
    stringstream ss;
    code.place = getFloatTemp();
    switch (op)
    {
        case '-':
            ss << "sub.s "<< code.place<<", "<< leftCode.place <<", "<< rightCode.place;
            break;
        case '/':
            ss << "div.s "<< code.place<<", "<< leftCode.place <<", "<< rightCode.place;
            break;
        default:
            break;
    }
    return ss.str();
}