/* Copyright (c) 2007, 2012 by Ian Piumarta
 * All rights reserved.
 *
 * Permission is hereby granted, free of charge, to any person obtaining a
 * copy of this software and associated documentation files (the 'Software'),
 * to deal in the Software without restriction, including without limitation
 * the rights to use, copy, modify, merge, publish, distribute, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, provided that the above copyright notice(s) and this
 * permission notice appear in all copies of the Software.  Acknowledgement
 * of the use of this Software in supporting documentation would be
 * appreciated but is not required.
 *
 * THE SOFTWARE IS PROVIDED 'AS IS'.  USE ENTIRELY AT YOUR OWN RISK.
 *
 * Last edited: 2013-06-06 12:24:20 by piumarta on ubuntu
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include <stdarg.h>

#ifdef WIN32
# undef inline
# define inline __inline
#endif

#include "version.h"
#include "tree.h"

static int yyl(void)
{
    static int prev= 0;
    return ++prev;
}

static void charClassSet  (unsigned int bits[], int c) {
    bits[c >> sizeof(unsigned int)] |=  (1 << (c % (sizeof(int) * 8)));
}

static void charClassClear(unsigned int bits[], int c) {
    bits[c >> sizeof(unsigned int)] &= ~(1 << (c % (sizeof(int) * 8)));
}

typedef void (*setter)(unsigned int bits[], int c);

static inline int ishex(int c) {
    return ('0' <= c && c <= '9') ||
        ('a' <= c && c <= 'f') ||
        ('A' <= c && c <= 'F');
}

static inline int hex2num(int c) {
    if('0' <= c && c <= '9') return c - '0';
    else if('a' <= c && c <= 'f') return c - 'a';
    else return c - 'A';
}


static int cnext(unsigned char **ccp)
{
    unsigned char *cclass= *ccp;
    int c = *cclass++;
    if (c) {
        if ('\\' == c && *cclass) {
            switch (c = *cclass++) {
            case 'a':  c = '\a';   break;    /* bel */
            case 'b':  c = '\b';   break;    /* bs */
            case 'e':  c = '\033'; break;    /* esc */
            case 'f':  c = '\f';   break;    /* ff */
            case 'n':  c = '\n';   break;    /* nl */
            case 'r':  c = '\r';   break;    /* cr */
            case 't':  c = '\t';   break;    /* ht */
            case 'v':  c = '\v';   break;    /* vt */
            case 'u':
            default:
                       if (ishex(c)) {
                           c = hex2num(c);
                           if (ishex(*cclass)) c = (c * 16) + hex2num(*cclass++);
                           if (ishex(*cclass)) c = (c * 16) + hex2num(*cclass++);
                       }
                       break;
            }
        }
        *ccp= cclass;
    }
    return c;
}

static char *makeCharClass(unsigned char *cclass)
{
#define VECTOR_LENGTH (256 / (sizeof(unsigned int) * 8))
    unsigned int bits[VECTOR_LENGTH];
    setter set;
    int    c, prev= -1;
    static char  string[256];
    char *ptr;

    if ('^' == *cclass) {
        memset(bits, 255, sizeof(unsigned int) * VECTOR_LENGTH);
        set= charClassClear;
        ++cclass;
    }
    else {
        memset(bits, 0, sizeof(unsigned int) * VECTOR_LENGTH);
        set= charClassSet;
    }
    while (*cclass) {
        if ('-' == *cclass && cclass[1] && prev >= 0) {
            ++cclass;
            for (c = cnext(&cclass);  prev <= c;  ++prev)
                set(bits, prev);
            prev= -1;
        }
        else {
            c = cnext(&cclass);
            set(bits, prev= c);
        }
    }

    ptr= string;
    for (c = 0; c < VECTOR_LENGTH; c++) {
        ptr += sprintf(ptr, ",%d", bits[c]);
    }

    return string;
}

static int indent_level = 0;

static void indent(FILE *fp) {
    int i;
    for (i = 0; i < indent_level; i++) {
        fprintf(fp, "    ");
    }
}

static void printfN_(FILE *fp, const char *fmt, ...) {
    va_list ap;
    va_start(ap, fmt);
    indent(fp);
    vfprintf(fp, fmt, ap);
    va_end(ap);
}

static void begin(void) {}
static void end(void)   {}
static void label(int n){}
static void jump(int n) {}
static void save(int n) {
    //printfN_(output, "int yypos%d= yy->__pos, yythunkpos%d= yy->__thunkpos;\n", n, n);
}
static void restore(int n) {
    //printfN_(output, "yy->__pos= yypos%d; yy->__thunkpos= yythunkpos%d;\n", n, n);
}

#define ARGS "NameSpace ns, TokenContext Context, SyntaxTree ParentTree, SyntaxPattern pattern"

#define NODE_TYPE_LIST(OP) \
    OP(Unknown) OP(Rule) OP(Variable) OP(Name) OP(Dot) OP(Character)\
    OP(String) OP(Class) OP(Action) OP(Predicate) OP(Error) OP(Alternate)\
    OP(Sequence) OP(PeekFor) OP(PeekNot) OP(Query) OP(Star) OP(Plus)
static const char *node_type(Node *node) {
    switch (node->type) {
#define CASE(TYPE) case TYPE : return #TYPE;
        NODE_TYPE_LIST(CASE)
    }
    return "";
}

static void Node_compile_c_ko(Node *node, int ko)
{
    Node *root = node;
    assert(node);
    if(node->type != Name) {
        printfN_(output, "SyntaxTree %s%d(" ARGS ") {\n", node_type(node), node->node_id);
    }
    switch (node->type) {
    case Rule:
        printfN_(stderr, "\ninternal error #1 (%s)\n", node->rule.name);
        exit(1);
        break;

    case Dot:
        printfN_(output, "if (!MatchDot(Context)) {\n");
        indent_level += 1;
        printfN_(output, "return Failed(Context, ParentTree, \"\");\n");
        indent_level -= 1;
        printfN_(output, "}\n");
        printfN_(output, "return new SyntaxTree(null, ns, GetToken(Context), null);\n");
        indent_level -= 1;
        printfN_(output, "}\n");
        break;

    case Name:
        printfN_(output, "Tree = yy_%s(ns, Context, Tree, pattern);\n", node->name.rule->rule.name);
        return;

    case Character:
    case String:
        {
            int len= strlen(node->string.value);
            indent_level += 1;
            if (1 == len) {
                const char *t1 = node->string.value;
                if ('\"' == node->string.value[0]) {
                    t1 = "\"";
                }
                printfN_(output, "if (!MatchChar(Context, \"%s\")) {\n", t1);

            }
            else {
                const char *fmt = "\"";
                const char *func = "MatchString";
                //if (2 == len && '\\' == node->string.value[0]) {
                //    fmt = "'";
                //    func = "MatchChar";
                //}
                printfN_(output, "if (!%s(Context, %s%s%s)) {\n", func, fmt, node->string.value, fmt);

            }

            indent_level += 1;
            printfN_(output, "return Failed(Context, ParentTree, \"\");\n");
            indent_level -= 1;
            printfN_(output, "}\n");
            printfN_(output, "return new SyntaxTree(null, ns, GetToken(Context), null);\n");
            indent_level -= 1;
            printfN_(output, "}\n");
        }
        break;

    case Class:
        indent_level += 1;
        printfN_(output, "if (!MatchClass(Context %s)) {\n", makeCharClass(node->cclass.value));

        indent_level += 1;
        printfN_(output, "return Failed(Context, ParentTree, \"\");\n");
        indent_level -= 1;
        printfN_(output, "}\n");
        printfN_(output, "return new SyntaxTree(null, ns, GetToken(Context), null);\n");
        indent_level -= 1;
        printfN_(output, "}\n");
        break;

    case Action:
        indent_level += 1;
        printfN_(output, "return yy%s(ns, Context, ParentTree, pattern);\n", node->action.name);
        indent_level -= 1;
        printfN_(output, "}\n");
        break;

    case Predicate:
        printfN_(output, "Pred  yyText(yy, yy->__begin, yy->__end);  if (!(%s)) goto l%d;\n", node->action.text, ko);
        break;

    case Error:
        {
            int eok= yyl(), eko= yyl();
            Node_compile_c_ko(node->error.element, eko);
            jump(eok);
            label(eko);
            printfN_(output, "yyText(yy, yy->__begin, yy->__end);  {\n");
            printfN_(output, "%s;\n", node->error.text);
            printfN_(output, "}");
            jump(ko);
            label(eok);
        }
        break;

    case Alternate:
        {
            int ok= yyl();
            save(ok);
            indent_level += 1;
            printfN_(output, "SyntaxTree Tree = null;\n");
            for (node= node->alternate.first;  node;  node= node->alternate.next) {
                Node_compile_c_ko(node, ko);
                printfN_(output, "if (IsFailed(Tree)) {\n");
                indent_level += 1;
                printfN_(output, "return Failed(Context, Tree);\n");
                indent_level -= 1;
                printfN_(output, "}\n");
            }
            printfN_(output, "return Tree;\n");
            indent_level -= 1;
            printfN_(output, "}\n");
            end();
            label(ok);
        }
        break;

    case Sequence:
        {
            int current_indent_level = indent_level;
            indent_level += 1;
            printfN_(output, "SyntaxTree Head = new SyntaxTree(ParentTree, ns, GetToken(Context), pattern);\n");
            printfN_(output, "SyntaxTree Tree = null;\n");
            for (node= node->sequence.first;  node;  node= node->sequence.next) {
                Node_compile_c_ko(node, ko);
                printfN_(output, "if (!IsFailed(Tree)) {\n");
                indent_level += 1;
                if (node->sequence.next) {
                    printfN_(output, "AppendParsedTree(Head, Tree);\n");
                }
            }
            printfN_(output, "return Tree;\n");
            while (indent_level > current_indent_level + 1) {
                indent_level -= 1;
                printfN_(output, "}\n");
            }
            printfN_(output, "return Failed(Context, Tree);\n");
            indent_level -= 1;
            printfN_(output, "}\n");
        }
        break;

    case PeekFor:
        {
            int ok= yyl();
            begin();
            save(ok);
            Node_compile_c_ko(node->peekFor.element, ko);
            restore(ok);
            end();
            printfN_(output, "new ERROR();\n");
        }
        break;

    case PeekNot:
        {
            int ok= yyl();
            indent_level += 1;
            printfN_(output, "SyntaxTree Tree = null;\n");
            Node_compile_c_ko(node->star.element, ok);
            printfN_(output, "if (!IsFailed(Tree)) {\n");
            indent_level += 1;
            printfN_(output, "return null;\n");
            indent_level -= 1;
            printfN_(output, "}\n");
            printfN_(output, "return Tree\n");

            //Node_compile_c_ko(node->peekFor.element, ok);
        }
        break;

    case Query:
        {
            int qok= yyl();
            indent_level += 1;
            printfN_(output, "SyntaxTree Tree = null;\n");
            Node_compile_c_ko(node->star.element, qok);
            printfN_(output, "if (IsFailed(Tree)) {\n");
            indent_level += 1;
            printfN_(output, "SyntaxTree NullTree = new SyntaxTree(null, ns, GetToken(Context), null);\n");
            printfN_(output, "return NullTree;\n");
            indent_level -= 1;
            printfN_(output, "}\n");
            printfN_(output, "return Tree\n");
        }
        break;

    case Star:
        {
            int out = yyl();
            indent_level += 1;
            printfN_(output, "SyntaxTree Head = new SyntaxTree(ParentTree, ns, GetToken(Context), pattern);\n");
            printfN_(output, "SyntaxTree Tree = null;\n");
            printfN_(output, "while(true) {\n");
            indent_level += 1;
            Node_compile_c_ko(node->star.element, out);
            printfN_(output, "if (IsFailed(Tree)) {\n");
            indent_level += 1;
            printfN_(output, "break;\n");
            indent_level -= 1;
            printfN_(output, "}\n");
            printfN_(output, "AppendParsedTree(Head, Tree);\n");
            indent_level -= 1;
            printfN_(output, "}\n");
            printfN_(output, "return Head;\n");
            indent_level -= 1;
            printfN_(output, "}\n");
        }
        break;

    case Plus:
        {
            int out= yyl();
            indent_level += 1;
            printfN_(output, "SyntaxTree Head = null;\n");
            printfN_(output, "SyntaxTree Tree = ParentTree;\n");
            Node_compile_c_ko(node->plus.element, ko);
            printfN_(output, "if (IsFailed(Tree)) {\n");
            indent_level += 1;
            printfN_(output, "return Failed(Context, Tree);\n");
            indent_level -= 1;
            printfN_(output, "}\n");
            printfN_(output, "while(true) {\n");
            indent_level += 1;
            Node_compile_c_ko(node->star.element, out);
            printfN_(output, "if (IsFailed(Tree)) {\n");
            indent_level += 1;
            printfN_(output, "break;\n");
            indent_level -= 1;
            printfN_(output, "}\n");
            printfN_(output, "AppendParsedTree(Head, Tree);\n");
            indent_level -= 1;
            printfN_(output, "}\n");
            printfN_(output, "return Head;\n");
            indent_level -= 1;
            printfN_(output, "}\n");

        }
        break;

    default:
        printfN_(stderr, "\nNode_compile_c_ko: illegal node type %d\n", node->type);
        exit(1);
    }
    printfN_(output, "Tree = %s%d(ns, Context, Tree, pattern);\n", node_type(root), root->node_id);
}


static void defineVariables(Node *node)
{
    int count= 0;
    while (node) {
        fprintf(output, "#define %s yy->__val[%d]\n", node->variable.name, --count);
        node->variable.offset= count;
        node= node->variable.next;
    }
    fprintf(output, "#define __ yy->__\n");
    fprintf(output, "#define yypos yy->__pos\n");
    fprintf(output, "#define yythunkpos yy->__thunkpos\n");
}

static void undefineVariables(Node *node)
{
    fprintf(output, "#undef yythunkpos\n");
    fprintf(output, "#undef yypos\n");
    fprintf(output, "#undef yy\n");
    while (node) {
        fprintf(output, "#undef %s\n", node->variable.name);
        node= node->variable.next;
    }
}


static void Rule_compile_green2(Node *node)
{
    assert(node);
    assert(Rule == node->type);

    if (!node->rule.expression)
        fprintf(stderr, "rule '%s' used but not defined\n", node->rule.name);
    else {
        int ko= yyl(), safe;

        if ((!(RuleUsed & node->rule.flags)) && (node != start))
            fprintf(stderr, "rule '%s' defined but not used\n", node->rule.name);

        safe= ((Query == node->rule.expression->type) || (Star == node->rule.expression->type));

        fprintf(output, "\n");
        fprintf(output, "SyntaxTree yy_%s(" ARGS ") {\n", node->rule.name);
        indent_level += 1;
        printfN_(output, "SyntaxTree Head = new SyntaxTree(ParentTree, ns, GetToken(Context), pattern);\n");
        printfN_(output, "SyntaxTree Tree = Head;\n");
        if (!safe) save(0);
        fprintf(output, "\n    debug(\"%s\");\n", node->rule.name);
        Node_compile_c_ko(node->rule.expression, ko);
        if (!safe) {
            label(ko);
            printfN_(output, "if (!IsFailed(Tree)) {\n");
            indent_level += 1;
            printfN_(output, "return Tree;\n");
            indent_level -= 1;
            printfN_(output, "}\n");
            restore(0);
            printfN_(output, "return Failed(Context, Tree, \"%s\");\n", node->rule.name);
        }
        indent_level -= 1;
        fprintf(output, "}\n");
    }

    if (node->rule.next)
        Rule_compile_green2(node->rule.next);
}

static char *header= ""
"class Token {}\n"
"class NameSpace {}\n"
"class TokenContext {}\n"
"class SyntaxPattern {}\n"
"\n"
"class SyntaxTree {\n"
"    constructor(SyntaxTree Parent, NameSpace ns, Token token, SyntaxPattern pattern) {\n"
"    }\n"
"}\n"
"\n"
"void debug(String message) { println(message); }\n"
"boolean MatchString(TokenContext Context, String Text) {\n"
"    debug(Text);\n"
"    return true;\n"
"}\n"
"boolean MatchDot(TokenContext Context) {\n"
"    return true;\n"
"}\n"
"boolean MatchChar(TokenContext Context, String Text) {\n"
"    debug(Text);\n"
"    return true;\n"
"}\n"
"boolean MatchClass(TokenContext Context, int Class0, int Class1, int Class2, int Class3, int Class4, int Class5, int Class6, int Class7) {\n"
"    return true;\n"
"}\n"
"boolean IsFailed(SyntaxTree Tree) {\n"
"    return true;\n"
"}\n"
"SyntaxTree Failed(TokenContext Context, SyntaxTree Tree) {\n"
"    return null;\n"
"}\n"
"Token GetToken(TokenContext Context) {\n"
"    return null;\n"
"}\n"
"SyntaxTree Failed(TokenContext Context, SyntaxTree Tree, String Text) {\n"
"    return null;\n"
"}\n"
"void AppendParsedTree(SyntaxTree Parent, SyntaxTree Tree) {\n"
"}\n"
;

void Rule_compile_green_header(void)
{
    fprintf(output, "/* A recursive-descent parser generated by peg %d.%d.%d */\n", PEG_MAJOR, PEG_MINOR, PEG_LEVEL);
    fprintf(output, "\n");
    fprintf(output, "%s", header);
    //fprintf(output, "#define YYRULECOUNT %d\n", ruleCount);
}

int consumeInput2(Node *node)
{
    if (!node) return 0;

    switch (node->type) {
    case Rule:
        {
            int result= 0;
            if (RuleReached & node->rule.flags)
                fprintf(stderr, "possible infinite left recursion in rule '%s'\n", node->rule.name);
            else
            {
                node->rule.flags |= RuleReached;
                result= consumeInput2(node->rule.expression);
                node->rule.flags &= ~RuleReached;
            }
            return result;
        }
        break;

    case Dot:       return 1;
    case Name:      return consumeInput2(node->name.rule);
    case Character:
    case String:    return strlen(node->string.value) > 0;
    case Class:     return 1;
    case Action:    return 0;
    case Predicate: return 0;
    case Error:     return consumeInput2(node->error.element);

    case Alternate:
                       {
                           Node *n;
                           for (n= node->alternate.first;  n;  n= n->alternate.next)
                               if (!consumeInput2(n))
                                   return 0;
                       }
                       return 1;

    case Sequence:
                       {
                           Node *n;
                           for (n= node->alternate.first;  n;  n= n->alternate.next)
                               if (consumeInput2(n))
                                   return 1;
                       }
                       return 0;

    case PeekFor: return 0;
    case PeekNot: return 0;
    case Query:   return 0;
    case Star:    return 0;
    case Plus:    return consumeInput2(node->plus.element);

    default:
                  fprintf(stderr, "\nconsumeInput2: illegal node type %d\n", node->type);
                  exit(1);
    }
    return 0;
}


void Rule_compile_green(Node *node)
{
    Node *n;

    for (n= rules;  n;  n= n->rule.next) {
        consumeInput2(n);
    }

    for (n= node;  n;  n= n->rule.next) {
        fprintf(output, "SyntaxTree yy_%s(" ARGS "); /* %d */\n", n->rule.name, n->rule.id);
    }
    fprintf(output, "\n");
    for (n= actions;  n;  n= n->action.list) {
        fprintf(output, "SyntaxTree yy%s(" ARGS ") {\n", n->action.name);
        //defineVariables(n->action.rule->rule.variables);
        fprintf(output, "%s;\n", n->action.text);
        //undefineVariables(n->action.rule->rule.variables);
        fprintf(output, "}\n");
    }
    Rule_compile_green2(node);
    //fprintf(output, footer, start->rule.name);
}
