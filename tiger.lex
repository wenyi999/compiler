%{
/* Lab2 Attention: You are only allowed to add code in this file and start at Line 26.*/
#include <string.h>
#include "util.h"
#include "symbol.h"
#include "absyn.h"
#include "y.tab.h"
#include "errormsg.h"


int charPos=1;
char * str = NULL;

int yywrap(void)
{
 charPos=1;
 return 1;
}

void adjust(void)
{
 EM_tokPos=charPos;
 charPos+=yyleng;
}

/*
* Please don't modify the lines above.
* You can add C declarations of your own below.
*/

/* @function: getstr
 * @input: a string literal
 * @output: the string value for the input which has all the escape sequences 
 * translated into their meaning.
 */
char *getstr(const char *str)
{
	//optional: implement this function if you need it
	return NULL;
}
const int plen = 100;
int len, mlen;

void str_init() {
    str = checked_malloc(plen);
    mlen = plen;
    str[0] = '\0';
    len = 0;
}

void str_add(char c) {
    if (len + 1 == mlen) {
        str = realloc(str, mlen+plen);
        if (!str) {
            printf("malloc error!\n");
            exit(1);
        }
        mlen += plen;
    }
    str[len++] = c;
    str[len] = '\0';
}


%}
  /* You can add lex definitions here. */
%x COMMENT STR 

%%
  /* 
  * Below is an example, which you can wipe out
  * and write reguler expressions and actions of your own.
  */ 
    int comment = 0;

<COMMENT>{
    "/*" {adjust(); comment++;}
    "*/" {adjust(); comment--; if(!comment) BEGIN(0);}
    \n   {adjust(); EM_newline(); continue;}
    . adjust();
    <<EOF>> {adjust(); EM_error(EM_tokPos,"EOF in comment"); return 0;}

}

<STR>{
    \" {charPos+=yyleng; yylval.sval = strlen(str) ? String(str) : 0; BEGIN(0); return STRING;}
    \\\n[ \t]*\\ {charPos+=yyleng;}
    \\n  {charPos+=yyleng; str_add('\n');}
    \\t {charPos+=yyleng; str_add('\t');}
    \\^[A-Z] {charPos+=yyleng; str_add(yytext[2]-'A'+1);}
    \\[0-9][0-9][0-9]  {charPos+=yyleng; str_add(atoi(yytext+1));}
    \\\"    {charPos+=yyleng; str_add('\"');}
    \\\\    {charPos+=yyleng; str_add('\\');}
    . {charPos+=yyleng; str_add(yytext[0]);}
    <<EOF>> {adjust(); EM_error(EM_tokPos,"EOF in string");  return 0;}
}

"/*" {adjust(); comment++; BEGIN(COMMENT);}

\"   {adjust(); str_init(); BEGIN(STR);}

[ \t]*   {adjust(); continue;}

\n {adjust(); EM_newline(); continue;}

","  {adjust(); return COMMA;}
":"  {adjust(); return COLON;}
";"  {adjust(); return SEMICOLON;}
"("  {adjust(); return LPAREN;}
")"  {adjust(); return RPAREN;}
"["  {adjust(); return LBRACK;}
"]"  {adjust(); return RBRACK;}
"{"  {adjust(); return LBRACE;}
"}"  {adjust(); return RBRACE;}
"."  {adjust(); return DOT;}
"+"  {adjust(); return PLUS;}
"-"  {adjust(); return MINUS;}
"*"  {adjust(); return TIMES;}
"/"  {adjust(); return DIVIDE;}
"="  {adjust(); return EQ;}
"<>" {adjust(); return NEQ;}
"<"  {adjust(); return LT;}
"<=" {adjust(); return LE;}
">"  {adjust(); return GT;}
">=" {adjust(); return GE;}
"&"  {adjust(); return AND;}
"|"  {adjust(); return OR;}
":=" {adjust(); return ASSIGN;}
array   {adjust(); return ARRAY;}
if      {adjust(); return IF;}
then    {adjust(); return THEN;}
else    {adjust(); return ELSE;}
while   {adjust(); return WHILE;}
for     {adjust(); return FOR;}
to      {adjust(); return TO;}
do      {adjust(); return DO;}
let     {adjust(); return LET;}
in      {adjust(); return IN;}
end     {adjust(); return END;}
of      {adjust(); return OF;}
break   {adjust(); return BREAK;}
nil     {adjust(); return NIL;}
function {adjust(); return FUNCTION;}
var     {adjust(); return VAR;}
type    {adjust(); return TYPE;}

[a-zA-Z]+[a-zA-Z0-9_]*  {adjust(); yylval.sval = String(yytext); return ID;}
[0-9]+   {adjust(); yylval.ival=atoi(yytext); return INT;}

.    {adjust(); EM_error(EM_tokPos,"illegal token");}

<<EOF>> return 0;


