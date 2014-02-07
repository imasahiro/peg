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

static char *buffer = NULL;
static int bufpos = -1;
static int buflen = -1;

static void clearbuffer() {
    free(buffer);
    bufpos = buflen = -1;
    buffer = NULL;
}

static void makebuffer() {
    if (buffer) {
        clearbuffer();
    }
    buflen = 1024;
    buffer = malloc(buflen);
    bufpos = 0;
}

static void expandbuf(int length) {
    while (buflen - bufpos < length + 1) {
        buflen *= 2;
        buffer = realloc(buffer, buflen);
    }
    memset(buffer + bufpos, 0, buflen - bufpos);
}

static void insert(const char *fmt) {
    char tmp[buflen + 1];
    memcpy(tmp, buffer, buflen);
    expandbuf(strlen(fmt));
    memcpy(buffer, fmt, strlen(fmt));
    memcpy(buffer + strlen(fmt), tmp, bufpos);
    bufpos += strlen(fmt);
}

static void writebuf(const char *fmt, ...) {
    va_list ap;
    va_start(ap, fmt);
    char tmp[1024];
    int len = vsprintf(tmp, fmt, ap);
    va_end(ap);
    expandbuf(len + 1);
    memcpy(buffer + bufpos, tmp, len);
    assert(bufpos + len = strlen(buffer));
    bufpos += len;
}


static int yyl(void)
{
    static int prev= 0;
    return ++prev;
}

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

static void charClassSet  (unsigned char bits[], int c) {
    bits[c] =  1;
}

static void charClassClear(unsigned char bits[], int c) {
    bits[c] = 0;
}

typedef void (*setter)(unsigned char bits[], int c);


static char *makeCharClass(unsigned char *cclass)
{
#define VECTOR_LENGTH (256)
    unsigned char bits[VECTOR_LENGTH];
    setter set;
    int    c, prev= -1;
    static char string[512] = {};
    char *ptr;

    memset(string, 0, 512);
    if ('^' == *cclass) {
        memset(bits, 255, sizeof(unsigned char) * VECTOR_LENGTH);
        set= charClassClear;
        ++cclass;
    }
    else {
        memset(bits, 0, sizeof(unsigned char) * VECTOR_LENGTH);
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
        if (bits[c]) {
            switch (c) {
            case '\a':  *ptr++ = '\\'; *ptr++ = 'a'; break;    /* bel */
            case '\b':  *ptr++ = '\\'; *ptr++ = 'b'; break;    /* bs */
            case '\f':  *ptr++ = '\\'; *ptr++ = 'f'; break;    /* ff */
            case '\n':  *ptr++ = '\\'; *ptr++ = 'n'; break;    /* nl */
            case '\r':  *ptr++ = '\\'; *ptr++ = 'r'; break;    /* cr */
            case '\t':  *ptr++ = '\\'; *ptr++ = 't'; break;    /* ht */
            case '\v':  *ptr++ = '\\'; *ptr++ = 'v'; break;    /* vt */
            default:
                       if (c >= 0x20) {
                           ptr += sprintf(ptr, "%c", c);
                       }
            }
        }
    }

    return string;
}

static void Node_compile_c_ko(Node *node, int ko)
{
    assert(node);
    int i = 0;
    int ok = 0;
    int qok = 0;
    int out = 0;
    switch (node->type) {
    case Rule:
        fprintf(stderr, "\ninternal error #1 (%s)\n", node->rule.name);
        exit(1);
        break;

    case Dot:
        writebuf("any");
        break;

    case Name:
        writebuf("%s", node->name.rule->rule.name);
        return;

    case Character:
    case String:
        writebuf("string(\"%s\")", node->string.value);
        break;

    case Class:
        writebuf("charctor(\"%s\")", makeCharClass(node->cclass.value));
        break;

    case Action:
        {
            insert("seq(apply(");
            bufpos -= 2;
            writebuf("),");
            writebuf("new YY%s())", node->action.name);
            break;
        }

    case Predicate:
        writebuf("predicate:%s", node->action.text);
        break;

    case Error:
        break;

    case Alternate:
        writebuf("or(");
        for (node= node->alternate.first; node; node= node->alternate.next) {
            if (i != 0) { writebuf(", "); }
            Node_compile_c_ko(node, ko);
            i++;
        }
        writebuf(")");
        break;

    case Sequence:
        writebuf("seq(");
        for (node= node->sequence.first; node; node= node->sequence.next) {
            if (i != 0) { writebuf(", "); }
            Node_compile_c_ko(node, ko);
            i++;
        }
        writebuf(")");
        break;

    case PeekFor:
        writebuf("peekfor(");
        Node_compile_c_ko(node->peekFor.element, ko);
        writebuf(")");
        break;

    case PeekNot:
        writebuf("not(");
        Node_compile_c_ko(node->star.element, ok);
        writebuf(")");
        break;

    case Query:
        writebuf("opt(");
        Node_compile_c_ko(node->star.element, qok);
        writebuf(")");
        break;

    case Star:
        writebuf("repeat(");
        Node_compile_c_ko(node->star.element, out);
        writebuf(")");
        break;

    case Plus:
        writebuf("repeat1(");
        Node_compile_c_ko(node->plus.element, ko);
        writebuf(")");
        break;

    default:
        fprintf(stderr, "\nNode_compile_c_ko: illegal node type %d\n", node->type);
        exit(1);
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

        fprintf(output, "%s.Target = ", node->rule.name);
        makebuffer();
        Node_compile_c_ko(node->rule.expression, ko);
        fprintf(output, "%s;\n", buffer);
        clearbuffer();
    }

    if (node->rule.next)
        Rule_compile_green2(node->rule.next);
}


void Rule_compile_green_header(void)
{
    fprintf(output, "/* A recursive-descent parser generated by peg %d.%d.%d */\n", PEG_MAJOR, PEG_MINOR, PEG_LEVEL);
    fprintf(output, "\n");
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
                           for (n = node->alternate.first; n; n = n->alternate.next)
                               if (!consumeInput2(n))
                                   return 0;
                       }
                       return 1;

    case Sequence:
                       {
                           Node *n;
                           for (n = node->alternate.first; n; n = n->alternate.next)
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

    for (n = actions; n; n = n->action.list) {
        fprintf(output, "class YY%s implements Transformer<T1, T2> {\n", n->action.name);
        fprintf(output, "\t@Override\n");
        fprintf(output, "\tpublic T2 apply(final T1 param) {\n");
        fprintf(output, "\t\t%s\n", n->action.text);
        fprintf(output, "\t}\n");
        fprintf(output, "}\n");
    }

    fprintf(output, "class %sParser {\n", start->rule.name);
    fprintf(output, "\tpublic static Parser<Object> NewInstance() {\n");
    for (n = node; n; n = n->rule.next) {
        fprintf(output, "SymbolParser<Object> %s = symbol(null); /* %d */\n", n->rule.name, n->rule.id);
    }
    fprintf(output, "\n");


    for (n = rules; n; n = n->rule.next) {
        consumeInput2(n);
    }

    Rule_compile_green2(node);
    fprintf(output, "\t\treturn %s;\n", start->rule.name);
    fprintf(output, "\t}\n");
    fprintf(output, "}\n");
}
