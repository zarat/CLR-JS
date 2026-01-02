// Program.cs - MiniJs: JS-like-ish interpreter with CLR interop + WinForms helpers + tasks
// Build: dotnet build
// Run:   dotnet run -- [file]

using System;
using System.IO;
using System.Text;
using System.Linq;
using System.Globalization;
using System.Collections;
using System.Collections.Generic;
using System.Reflection;
using System.Linq.Expressions;
using System.Runtime.CompilerServices;
using System.Threading;
using System.Threading.Tasks;
using System.ComponentModel;
using System.Windows.Forms;

namespace MiniJs
{
    enum TokType
    {
        EOF_TOK,

        IDENT, NUMBER, STRING,
        TRUE_TOK, FALSE_TOK, NULL_TOK,

        LET, VAR, FUNCTION, CLASS, NEW, THIS, RETURN, IF, ELSE,
        WHILE, FOR, FOREACH, IN, BREAK, CONTINUE,

        IMPORT, AS,

        TASK, YIELD, LOCK,
        AWAIT, JOIN,

        LPAREN, RPAREN,
        LBRACE, RBRACE,
        LBRACK, RBRACK,
        COMMA, SEMI, DOT, COLON,

        ASSIGN, // =
        PLUS_ASSIGN, MINUS_ASSIGN, MUL_ASSIGN, DIV_ASSIGN, MOD_ASSIGN,

        EQ, NEQ, LT, GT, LEQ, GEQ,

        PLUS, MINUS, MUL, DIV, MOD,
        POW,           // **

        BITAND, BITXOR, BITOR,
        AND, OR,

        INC, DEC,      // ++ --

        BITNOT,        // ~
        BANG           // !
    }

    static class Tok
    {
        public static string Name(TokType t) => t switch
        {
            TokType.EOF_TOK => "EOF",
            TokType.IDENT => "IDENT",
            TokType.NUMBER => "NUMBER",
            TokType.STRING => "STRING",
            TokType.TRUE_TOK => "TRUE",
            TokType.FALSE_TOK => "FALSE",
            TokType.NULL_TOK => "NULL",

            TokType.LET => "LET",
            TokType.VAR => "VAR",
            TokType.FUNCTION => "FUNCTION",
            TokType.CLASS => "CLASS",
            TokType.NEW => "NEW",
            TokType.THIS => "THIS",
            TokType.RETURN => "RETURN",
            TokType.IF => "IF",
            TokType.ELSE => "ELSE",
            TokType.WHILE => "WHILE",
            TokType.FOR => "FOR",
            TokType.FOREACH => "FOREACH",
            TokType.IN => "IN",
            TokType.BREAK => "BREAK",
            TokType.CONTINUE => "CONTINUE",

            TokType.IMPORT => "IMPORT",
            TokType.AS => "AS",

            TokType.TASK => "TASK",
            TokType.YIELD => "YIELD",
            TokType.LOCK => "LOCK",
            TokType.AWAIT => "AWAIT",
            TokType.JOIN => "JOIN",

            TokType.LPAREN => "(",
            TokType.RPAREN => ")",
            TokType.LBRACE => "{",
            TokType.RBRACE => "}",
            TokType.LBRACK => "[",
            TokType.RBRACK => "]",
            TokType.COMMA => ",",
            TokType.SEMI => ";",
            TokType.DOT => ".",
            TokType.COLON => ":",

            TokType.ASSIGN => "=",
            TokType.PLUS_ASSIGN => "+=",
            TokType.MINUS_ASSIGN => "-=",
            TokType.MUL_ASSIGN => "*=",
            TokType.DIV_ASSIGN => "/=",
            TokType.MOD_ASSIGN => "%=",

            TokType.EQ => "==",
            TokType.NEQ => "!=",
            TokType.LT => "<",
            TokType.GT => ">",
            TokType.LEQ => "<=",
            TokType.GEQ => ">=",

            TokType.PLUS => "+",
            TokType.MINUS => "-",
            TokType.MUL => "*",
            TokType.DIV => "/",
            TokType.MOD => "%",
            TokType.POW => "**",

            TokType.BITAND => "&",
            TokType.BITXOR => "^",
            TokType.BITOR => "|",
            TokType.AND => "&&",
            TokType.OR => "||",

            TokType.INC => "++",
            TokType.DEC => "--",

            TokType.BITNOT => "~",
            TokType.BANG => "!",

            _ => "?"
        };
    }

    readonly struct Token
    {
        public readonly TokType Type;
        public readonly string Lexeme;
        public readonly int Pos;

        public Token(TokType type, string lexeme, int pos)
        {
            Type = type;
            Lexeme = lexeme;
            Pos = pos;
        }

        public override string ToString() => $"{Tok.Name(Type)} '{Lexeme}' @{Pos}";
    }

    sealed class Lexer
    {
        private readonly string _src;
        private int _i;

        public Lexer(string s) { _src = s; _i = 0; }

        private bool AtEnd => _i >= _src.Length;
        private char Cur => AtEnd ? '\0' : _src[_i];
        private char Peek(int n = 1) => (_i + n >= _src.Length) ? '\0' : _src[_i + n];
        private void Advance() { if (!AtEnd) _i++; }

        private void SkipWs()
        {
            while (!AtEnd)
            {
                char c = Cur;
                if (c is ' ' or '\t' or '\r' or '\n') { Advance(); continue; }

                if (c == '/' && Peek() == '/')
                {
                    while (!AtEnd && Cur != '\n') Advance();
                    continue;
                }

                if (c == '/' && Peek() == '*')
                {
                    Advance(); Advance();
                    while (!AtEnd && !(Cur == '*' && Peek() == '/')) Advance();
                    if (!AtEnd) { Advance(); Advance(); }
                    continue;
                }

                break;
            }
        }

        private static bool IsIdentStart(char c) => char.IsLetter(c) || c == '_' || c == '@';
        private static bool IsIdent(char c) => char.IsLetterOrDigit(c) || c == '_' || c == '@';

        public Token Next()
        {
            SkipWs();
            int pos = _i;

            if (AtEnd) return new Token(TokType.EOF_TOK, "", pos);

            char c = Cur;

            if (IsIdentStart(c))
            {
                var sb = new StringBuilder();
                while (!AtEnd && IsIdent(Cur)) { sb.Append(Cur); Advance(); }
                string s = sb.ToString();

                return s switch
                {
                    "let" => new Token(TokType.LET, s, pos),
                    "var" => new Token(TokType.VAR, s, pos),
                    "function" => new Token(TokType.FUNCTION, s, pos),
                    "class" => new Token(TokType.CLASS, s, pos),
                    "new" => new Token(TokType.NEW, s, pos),
                    "this" => new Token(TokType.THIS, s, pos),
                    "return" => new Token(TokType.RETURN, s, pos),
                    "if" => new Token(TokType.IF, s, pos),
                    "else" => new Token(TokType.ELSE, s, pos),
                    "while" => new Token(TokType.WHILE, s, pos),
                    "for" => new Token(TokType.FOR, s, pos),
                    "foreach" => new Token(TokType.FOREACH, s, pos),
                    "in" => new Token(TokType.IN, s, pos),
                    "break" => new Token(TokType.BREAK, s, pos),
                    "continue" => new Token(TokType.CONTINUE, s, pos),

                    "import" => new Token(TokType.IMPORT, s, pos),
                    "as" => new Token(TokType.AS, s, pos),

                    "task" => new Token(TokType.TASK, s, pos),
                    "yield" => new Token(TokType.YIELD, s, pos),
                    "lock" => new Token(TokType.LOCK, s, pos),
                    "await" => new Token(TokType.AWAIT, s, pos),
                    "join" => new Token(TokType.JOIN, s, pos),

                    "true" => new Token(TokType.TRUE_TOK, s, pos),
                    "false" => new Token(TokType.FALSE_TOK, s, pos),
                    "null" => new Token(TokType.NULL_TOK, s, pos),
                    _ => new Token(TokType.IDENT, s, pos)
                };
            }

            if (char.IsDigit(c))
            {
                var sb = new StringBuilder();
                while (!AtEnd && char.IsDigit(Cur)) { sb.Append(Cur); Advance(); }
                if (!AtEnd && Cur == '.' && char.IsDigit(Peek()))
                {
                    sb.Append(Cur); Advance();
                    while (!AtEnd && char.IsDigit(Cur)) { sb.Append(Cur); Advance(); }
                }
                return new Token(TokType.NUMBER, sb.ToString(), pos);
            }

            if (c == '"')
            {
                Advance();
                var sb = new StringBuilder();
                while (!AtEnd && Cur != '"')
                {
                    if (Cur == '\\')
                    {
                        Advance();
                        if (AtEnd) break;
                        char e = Cur;
                        sb.Append(e switch
                        {
                            'n' => '\n',
                            't' => '\t',
                            'r' => '\r',
                            '"' => '"',
                            '\\' => '\\',
                            _ => e
                        });
                        Advance();
                    }
                    else
                    {
                        sb.Append(Cur);
                        Advance();
                    }
                }
                if (Cur == '"') Advance();
                return new Token(TokType.STRING, sb.ToString(), pos);
            }

            if (c == '*' && Peek() == '*') { Advance(); Advance(); return new Token(TokType.POW, "**", pos); }
            if (c == '+' && Peek() == '+') { Advance(); Advance(); return new Token(TokType.INC, "++", pos); }
            if (c == '-' && Peek() == '-') { Advance(); Advance(); return new Token(TokType.DEC, "--", pos); }

            if (c == '+' && Peek() == '=') { Advance(); Advance(); return new Token(TokType.PLUS_ASSIGN, "+=", pos); }
            if (c == '-' && Peek() == '=') { Advance(); Advance(); return new Token(TokType.MINUS_ASSIGN, "-=", pos); }
            if (c == '*' && Peek() == '=') { Advance(); Advance(); return new Token(TokType.MUL_ASSIGN, "*=", pos); }
            if (c == '/' && Peek() == '=') { Advance(); Advance(); return new Token(TokType.DIV_ASSIGN, "/=", pos); }
            if (c == '%' && Peek() == '=') { Advance(); Advance(); return new Token(TokType.MOD_ASSIGN, "%=", pos); }

            if (c == '=' && Peek() == '=') { Advance(); Advance(); return new Token(TokType.EQ, "==", pos); }
            if (c == '!' && Peek() == '=') { Advance(); Advance(); return new Token(TokType.NEQ, "!=", pos); }
            if (c == '<' && Peek() == '=') { Advance(); Advance(); return new Token(TokType.LEQ, "<=", pos); }
            if (c == '>' && Peek() == '=') { Advance(); Advance(); return new Token(TokType.GEQ, ">=", pos); }
            if (c == '&' && Peek() == '&') { Advance(); Advance(); return new Token(TokType.AND, "&&", pos); }
            if (c == '|' && Peek() == '|') { Advance(); Advance(); return new Token(TokType.OR, "||", pos); }

            Token One(TokType tp, string lex) { Advance(); return new Token(tp, lex, pos); }

            return c switch
            {
                '(' => One(TokType.LPAREN, "("),
                ')' => One(TokType.RPAREN, ")"),
                '{' => One(TokType.LBRACE, "{"),
                '}' => One(TokType.RBRACE, "}"),
                '[' => One(TokType.LBRACK, "["),
                ']' => One(TokType.RBRACK, "]"),
                ',' => One(TokType.COMMA, ","),
                ';' => One(TokType.SEMI, ";"),
                '.' => One(TokType.DOT, "."),
                ':' => One(TokType.COLON, ":"),
                '+' => One(TokType.PLUS, "+"),
                '-' => One(TokType.MINUS, "-"),
                '*' => One(TokType.MUL, "*"),
                '/' => One(TokType.DIV, "/"),
                '%' => One(TokType.MOD, "%"),
                '=' => One(TokType.ASSIGN, "="),
                '<' => One(TokType.LT, "<"),
                '>' => One(TokType.GT, ">"),
                '&' => One(TokType.BITAND, "&"),
                '|' => One(TokType.BITOR, "|"),
                '^' => One(TokType.BITXOR, "^"),
                '~' => One(TokType.BITNOT, "~"),
                '!' => One(TokType.BANG, "!"),
                _ => throw new Exception($"Lexer error at pos {_i}: unexpected '{c}'")
            };
        }
    }

    enum NodeType
    {
        Program, Block,

        LetDecl, FunctionDecl,
        ClassDecl, MethodDecl, FieldDecl,

        ReturnStmt, IfStmt,
        WhileStmt, ForStmt, ForeachStmt,
        BreakStmt, ContinueStmt,

        ImportStmt,
        TaskStmt,
        YieldStmt,
        LockStmt,
        AwaitStmt,

        ExprStmt,

        Assign, Binary, Unary, Postfix,
        Var, Literal,

        ArrayLit, ObjectLit, FunctionExpr,
        Member, Index, Call, NewExpr,

        TaskExpr,
        AwaitExpr,
        TaskBlock
    }

    sealed class Node
    {
        public NodeType Type;
        public Token Tok;
        public string Text = "";
        public List<Node?> Kids = new();

        public Node(NodeType t) { Type = t; Tok = default; }
        public Node(NodeType t, Token tk) { Type = t; Tok = tk; }
    }

    sealed class Parser
    {
        private readonly Lexer _lex;
        private Token _cur;

        public Parser(Lexer l) { _lex = l; _cur = _lex.Next(); }

        private Exception Err(string msg) =>
          new Exception($"Parse error at pos {_cur.Pos}: {msg} (got {Tok.Name(_cur.Type)} '{_cur.Lexeme}')");

        private bool Match(TokType t)
        {
            if (_cur.Type == t) { _cur = _lex.Next(); return true; }
            return false;
        }

        private Token Consume(TokType t, string what)
        {
            if (_cur.Type != t) throw Err("expected " + what);
            Token o = _cur;
            _cur = _lex.Next();
            return o;
        }

        public Node ParseProgram()
        {
            var p = new Node(NodeType.Program);
            while (_cur.Type != TokType.EOF_TOK) p.Kids.Add(Statement());
            return p;
        }

        private Node Statement()
        {
            if (_cur.Type == TokType.IMPORT) return ImportStmt();
            if (_cur.Type == TokType.TASK) return TaskStmt();
            if (_cur.Type == TokType.YIELD) return YieldStmt();
            if (_cur.Type == TokType.LOCK) return LockStmt();
            if (_cur.Type == TokType.AWAIT || _cur.Type == TokType.JOIN) return AwaitStmt();

            if (_cur.Type == TokType.LBRACE) return Block();
            if (_cur.Type == TokType.LET || _cur.Type == TokType.VAR) return LetDecl(withSemi: true);
            if (_cur.Type == TokType.FUNCTION) return FunctionDecl();
            if (_cur.Type == TokType.CLASS) return ClassDecl();
            if (_cur.Type == TokType.RETURN) return ReturnStmt();
            if (_cur.Type == TokType.IF) return IfStmt();
            if (_cur.Type == TokType.WHILE) return WhileStmt();
            if (_cur.Type == TokType.FOR) return ForStmt();
            if (_cur.Type == TokType.FOREACH) return ForeachStmt();
            if (_cur.Type == TokType.BREAK) return BreakStmt();
            if (_cur.Type == TokType.CONTINUE) return ContinueStmt();

            var e = Expression();
            Match(TokType.SEMI);
            var s = new Node(NodeType.ExprStmt);
            s.Kids.Add(e);
            return s;
        }

        private Node ImportStmt()
        {
            Token it = Consume(TokType.IMPORT, "'import'");

            Token first = Consume(TokType.IDENT, "import name");
            var full = new StringBuilder(first.Lexeme);
            while (Match(TokType.DOT))
            {
                Token part = Consume(TokType.IDENT, "import name part");
                full.Append('.').Append(part.Lexeme);
            }

            Token aliasTok;
            if (Match(TokType.AS))
                aliasTok = Consume(TokType.IDENT, "alias after 'as'");
            else
                aliasTok = new Token(TokType.IDENT, full.ToString().Split('.').Last(), it.Pos);

            Match(TokType.SEMI);

            var n = new Node(NodeType.ImportStmt, aliasTok);
            n.Text = full.ToString();
            return n;
        }

        private Node TaskStmt()
        {
            Token tt = Consume(TokType.TASK, "'task'");

            Node expr;
            if (_cur.Type == TokType.LBRACE) expr = TaskBlockExpr(tt);
            else expr = Expression();

            Match(TokType.SEMI);
            var n = new Node(NodeType.TaskStmt, tt);
            n.Kids.Add(expr);
            return n;
        }

        private Node TaskBlockExpr(Token taskTok)
        {
            Consume(TokType.LBRACE, "'{' after task");
            var b = new Node(NodeType.TaskBlock, taskTok);
            while (_cur.Type != TokType.RBRACE && _cur.Type != TokType.EOF_TOK)
                b.Kids.Add(Statement());
            Consume(TokType.RBRACE, "'}' after task block");
            return b;
        }

        private Node YieldStmt()
        {
            Token yt = Consume(TokType.YIELD, "'yield'");
            Match(TokType.SEMI);
            return new Node(NodeType.YieldStmt, yt);
        }

        private Node LockStmt()
        {
            Token lt = Consume(TokType.LOCK, "'lock'");
            Consume(TokType.LPAREN, "'(' after lock");
            var expr = Expression();
            Consume(TokType.RPAREN, "')' after lock(expr)");
            var body = Statement();

            var n = new Node(NodeType.LockStmt, lt);
            n.Kids.Add(expr);
            n.Kids.Add(body);
            return n;
        }

        private Node AwaitStmt()
        {
            Token at = _cur;
            if (_cur.Type == TokType.AWAIT) Consume(TokType.AWAIT, "'await'");
            else Consume(TokType.JOIN, "'join'");
            var expr = Expression();
            Match(TokType.SEMI);
            var n = new Node(NodeType.AwaitStmt, at);
            n.Kids.Add(expr);
            return n;
        }

        private Node Block()
        {
            Consume(TokType.LBRACE, "'{'");
            var b = new Node(NodeType.Block);
            while (_cur.Type != TokType.RBRACE && _cur.Type != TokType.EOF_TOK) b.Kids.Add(Statement());
            Consume(TokType.RBRACE, "'}'");
            return b;
        }

        private Node LetDecl(bool withSemi)
        {
            if (_cur.Type == TokType.LET) Consume(TokType.LET, "'let'");
            else Consume(TokType.VAR, "'var'");

            Token name = Consume(TokType.IDENT, "identifier");
            var n = new Node(NodeType.LetDecl, name);

            if (Match(TokType.ASSIGN)) n.Kids.Add(Expression());
            else n.Kids.Add(new Node(NodeType.Literal, new Token(TokType.NULL_TOK, "null", name.Pos)));

            if (withSemi) Match(TokType.SEMI);
            return n;
        }

        private Node FunctionDecl()
        {
            Consume(TokType.FUNCTION, "'function'");
            Token name = Consume(TokType.IDENT, "function name");

            Consume(TokType.LPAREN, "'('");
            var paramsTok = new List<Token>();
            if (_cur.Type != TokType.RPAREN)
            {
                paramsTok.Add(Consume(TokType.IDENT, "param"));
                while (Match(TokType.COMMA)) paramsTok.Add(Consume(TokType.IDENT, "param"));
            }
            Consume(TokType.RPAREN, "')'");

            var body = Block();

            var fd = new Node(NodeType.FunctionDecl, name);
            var plist = new Node(NodeType.Block);
            foreach (var p in paramsTok) plist.Kids.Add(new Node(NodeType.Var, p));
            fd.Kids.Add(plist);
            fd.Kids.Add(body);
            return fd;
        }

        private Node ReturnStmt()
        {
            Token rt = Consume(TokType.RETURN, "'return'");
            var n = new Node(NodeType.ReturnStmt, rt);

            if (_cur.Type != TokType.SEMI && _cur.Type != TokType.RBRACE && _cur.Type != TokType.EOF_TOK)
                n.Kids.Add(Expression());
            else
                n.Kids.Add(new Node(NodeType.Literal, new Token(TokType.NULL_TOK, "null", rt.Pos)));

            Match(TokType.SEMI);
            return n;
        }

        private Node BreakStmt()
        {
            Token bt = Consume(TokType.BREAK, "'break'");
            var n = new Node(NodeType.BreakStmt, bt);
            Match(TokType.SEMI);
            return n;
        }

        private Node ContinueStmt()
        {
            Token ct = Consume(TokType.CONTINUE, "'continue'");
            var n = new Node(NodeType.ContinueStmt, ct);
            Match(TokType.SEMI);
            return n;
        }

        private Node IfStmt()
        {
            Token it = Consume(TokType.IF, "'if'");
            Consume(TokType.LPAREN, "'('");
            var cond = Expression();
            Consume(TokType.RPAREN, "')'");

            var thenS = Statement();
            Node? elseS = null;
            if (Match(TokType.ELSE)) elseS = Statement();

            var n = new Node(NodeType.IfStmt, it);
            n.Kids.Add(cond);
            n.Kids.Add(thenS);
            n.Kids.Add(elseS ?? new Node(NodeType.Block));
            return n;
        }

        private Node WhileStmt()
        {
            Token wt = Consume(TokType.WHILE, "'while'");
            Consume(TokType.LPAREN, "'('");
            var cond = Expression();
            Consume(TokType.RPAREN, "')'");
            var body = Statement();

            var n = new Node(NodeType.WhileStmt, wt);
            n.Kids.Add(cond);
            n.Kids.Add(body);
            return n;
        }

        private Node ForStmt()
        {
            Token ft = Consume(TokType.FOR, "'for'");
            Consume(TokType.LPAREN, "'('");

            Node? init = null;
            if (_cur.Type == TokType.SEMI) Consume(TokType.SEMI, "';'");
            else
            {
                init = (_cur.Type == TokType.LET || _cur.Type == TokType.VAR) ? LetDecl(withSemi: false) : Expression();
                Consume(TokType.SEMI, "';'");
            }

            Node? cond = null;
            if (_cur.Type == TokType.SEMI) Consume(TokType.SEMI, "';'");
            else
            {
                cond = Expression();
                Consume(TokType.SEMI, "';'");
            }

            Node? post = null;
            if (_cur.Type == TokType.RPAREN) Consume(TokType.RPAREN, "')'");
            else
            {
                post = Expression();
                Consume(TokType.RPAREN, "')'");
            }

            var body = Statement();

            var n = new Node(NodeType.ForStmt, ft);
            n.Kids.Add(init);
            n.Kids.Add(cond);
            n.Kids.Add(post);
            n.Kids.Add(body);
            return n;
        }

        private Node ForeachStmt()
        {
            Token ft = Consume(TokType.FOREACH, "'foreach'");
            Consume(TokType.LPAREN, "'('");

            Token v1 = Consume(TokType.IDENT, "loop variable");
            Token v2 = new Token(TokType.IDENT, "", v1.Pos);
            bool hasV2 = false;

            if (Match(TokType.COMMA))
            {
                v2 = Consume(TokType.IDENT, "second loop variable");
                hasV2 = true;
            }

            Consume(TokType.IN, "'in'");
            var iterable = Expression();
            Consume(TokType.RPAREN, "')'");

            var body = Statement();

            var n = new Node(NodeType.ForeachStmt, ft);
            n.Kids.Add(new Node(NodeType.Var, v1));
            n.Kids.Add(hasV2 ? new Node(NodeType.Var, v2) : null);
            n.Kids.Add(iterable);
            n.Kids.Add(body);
            return n;
        }

        private Node ClassDecl()
        {
            Consume(TokType.CLASS, "'class'");
            Token name = Consume(TokType.IDENT, "class name");
            Consume(TokType.LBRACE, "'{'");

            var c = new Node(NodeType.ClassDecl, name);

            while (_cur.Type != TokType.RBRACE && _cur.Type != TokType.EOF_TOK)
            {
                if (_cur.Type == TokType.VAR)
                {
                    Consume(TokType.VAR, "'var' in class body");
                    Token fname = Consume(TokType.IDENT, "field name");
                    var fd = new Node(NodeType.FieldDecl, fname);

                    if (Match(TokType.ASSIGN)) fd.Kids.Add(Expression());
                    else fd.Kids.Add(new Node(NodeType.Literal, new Token(TokType.NULL_TOK, "null", fname.Pos)));

                    Match(TokType.SEMI);
                    c.Kids.Add(fd);
                    continue;
                }

                Token mname = Consume(TokType.IDENT, "method name");
                Consume(TokType.LPAREN, "'('");
                var paramsTok = new List<Token>();
                if (_cur.Type != TokType.RPAREN)
                {
                    paramsTok.Add(Consume(TokType.IDENT, "param"));
                    while (Match(TokType.COMMA)) paramsTok.Add(Consume(TokType.IDENT, "param"));
                }
                Consume(TokType.RPAREN, "')'");

                var body = Block();

                var md = new Node(NodeType.MethodDecl, mname);
                var plist = new Node(NodeType.Block);
                foreach (var p in paramsTok) plist.Kids.Add(new Node(NodeType.Var, p));
                md.Kids.Add(plist);
                md.Kids.Add(body);
                c.Kids.Add(md);
            }

            Consume(TokType.RBRACE, "'}'");
            Match(TokType.SEMI);
            return c;
        }

        private Node Expression() => Assignment();

        private Node Assignment()
        {
            var left = LogicalOr();

            bool IsAssignOp(TokType t) =>
              t == TokType.ASSIGN ||
              t == TokType.PLUS_ASSIGN || t == TokType.MINUS_ASSIGN ||
              t == TokType.MUL_ASSIGN || t == TokType.DIV_ASSIGN ||
              t == TokType.MOD_ASSIGN;

            if (IsAssignOp(_cur.Type))
            {
                Token op = _cur; _cur = _lex.Next();
                var n = new Node(NodeType.Assign, op);
                n.Kids.Add(left);
                n.Kids.Add(Assignment());
                return n;
            }

            return left;
        }

        private Node LogicalOr()
        {
            var n = LogicalAnd();
            while (_cur.Type == TokType.OR)
            {
                Token op = _cur; _cur = _lex.Next();
                var b = new Node(NodeType.Binary, op);
                b.Kids.Add(n);
                b.Kids.Add(LogicalAnd());
                n = b;
            }
            return n;
        }

        private Node LogicalAnd()
        {
            var n = BitwiseOr();
            while (_cur.Type == TokType.AND)
            {
                Token op = _cur; _cur = _lex.Next();
                var b = new Node(NodeType.Binary, op);
                b.Kids.Add(n);
                b.Kids.Add(BitwiseOr());
                n = b;
            }
            return n;
        }

        private Node BitwiseOr()
        {
            var n = BitwiseXor();
            while (_cur.Type == TokType.BITOR)
            {
                Token op = _cur; _cur = _lex.Next();
                var b = new Node(NodeType.Binary, op);
                b.Kids.Add(n);
                b.Kids.Add(BitwiseXor());
                n = b;
            }
            return n;
        }

        private Node BitwiseXor()
        {
            var n = BitwiseAnd();
            while (_cur.Type == TokType.BITXOR)
            {
                Token op = _cur; _cur = _lex.Next();
                var b = new Node(NodeType.Binary, op);
                b.Kids.Add(n);
                b.Kids.Add(BitwiseAnd());
                n = b;
            }
            return n;
        }

        private Node BitwiseAnd()
        {
            var n = Equality();
            while (_cur.Type == TokType.BITAND)
            {
                Token op = _cur; _cur = _lex.Next();
                var b = new Node(NodeType.Binary, op);
                b.Kids.Add(n);
                b.Kids.Add(Equality());
                n = b;
            }
            return n;
        }

        private Node Equality()
        {
            var n = Comparison();
            while (_cur.Type == TokType.EQ || _cur.Type == TokType.NEQ)
            {
                Token op = _cur; _cur = _lex.Next();
                var b = new Node(NodeType.Binary, op);
                b.Kids.Add(n);
                b.Kids.Add(Comparison());
                n = b;
            }
            return n;
        }

        private Node Comparison()
        {
            var n = Term();
            while (_cur.Type == TokType.LT || _cur.Type == TokType.LEQ || _cur.Type == TokType.GT || _cur.Type == TokType.GEQ)
            {
                Token op = _cur; _cur = _lex.Next();
                var b = new Node(NodeType.Binary, op);
                b.Kids.Add(n);
                b.Kids.Add(Term());
                n = b;
            }
            return n;
        }

        private Node Term()
        {
            var n = Factor();
            while (_cur.Type == TokType.PLUS || _cur.Type == TokType.MINUS)
            {
                Token op = _cur; _cur = _lex.Next();
                var b = new Node(NodeType.Binary, op);
                b.Kids.Add(n);
                b.Kids.Add(Factor());
                n = b;
            }
            return n;
        }

        private Node Factor()
        {
            var n = Power();
            while (_cur.Type == TokType.MUL || _cur.Type == TokType.DIV || _cur.Type == TokType.MOD)
            {
                Token op = _cur; _cur = _lex.Next();
                var b = new Node(NodeType.Binary, op);
                b.Kids.Add(n);
                b.Kids.Add(Power());
                n = b;
            }
            return n;
        }

        private Node Power()
        {
            var n = Unary();
            if (_cur.Type == TokType.POW)
            {
                Token op = _cur; _cur = _lex.Next();
                var b = new Node(NodeType.Binary, op);
                b.Kids.Add(n);
                b.Kids.Add(Power());
                return b;
            }
            return n;
        }

        private Node Unary()
        {
            if (_cur.Type == TokType.TASK)
            {
                Token tt = Consume(TokType.TASK, "'task'");
                var u = new Node(NodeType.TaskExpr, tt);
                if (_cur.Type == TokType.LBRACE) u.Kids.Add(TaskBlockExpr(tt));
                else u.Kids.Add(Unary());
                return u;
            }

            if (_cur.Type == TokType.AWAIT || _cur.Type == TokType.JOIN)
            {
                Token at = _cur;
                if (_cur.Type == TokType.AWAIT) Consume(TokType.AWAIT, "'await'");
                else Consume(TokType.JOIN, "'join'");
                var u = new Node(NodeType.AwaitExpr, at);
                u.Kids.Add(Unary());
                return u;
            }

            if (_cur.Type == TokType.BANG || _cur.Type == TokType.PLUS || _cur.Type == TokType.MINUS ||
                _cur.Type == TokType.BITNOT || _cur.Type == TokType.INC || _cur.Type == TokType.DEC)
            {
                Token op = _cur; _cur = _lex.Next();
                var u = new Node(NodeType.Unary, op);
                u.Kids.Add(Unary());
                return u;
            }
            return Postfix();
        }

        private Node Postfix()
        {
            var n = Primary();

            while (true)
            {
                if (Match(TokType.DOT))
                {
                    Token prop = Consume(TokType.IDENT, "property name");
                    var m = new Node(NodeType.Member, new Token(TokType.DOT, ".", prop.Pos));
                    m.Kids.Add(n);
                    m.Kids.Add(new Node(NodeType.Var, prop));
                    n = m;
                    continue;
                }

                if (Match(TokType.LBRACK))
                {
                    var idxExpr = Expression();
                    Consume(TokType.RBRACK, "']'");
                    var ix = new Node(NodeType.Index, new Token(TokType.LBRACK, "[", idxExpr?.Tok.Pos ?? _cur.Pos));
                    ix.Kids.Add(n);
                    ix.Kids.Add(idxExpr);
                    n = ix;
                    continue;
                }

                if (_cur.Type == TokType.LPAREN)
                {
                    Token ct = Consume(TokType.LPAREN, "'('");
                    var args = new Node(NodeType.Block, ct); // arg-list holder
                    if (_cur.Type != TokType.RPAREN)
                    {
                        args.Kids.Add(Expression());
                        while (Match(TokType.COMMA)) args.Kids.Add(Expression());
                    }
                    Consume(TokType.RPAREN, "')'");

                    var c = new Node(NodeType.Call, new Token(TokType.LPAREN, "call", ct.Pos));
                    c.Kids.Add(n);
                    c.Kids.Add(args);
                    n = c;
                    continue;
                }

                break;
            }

            if (_cur.Type == TokType.INC || _cur.Type == TokType.DEC)
            {
                Token op = _cur; _cur = _lex.Next();
                var p = new Node(NodeType.Postfix, op);
                p.Kids.Add(n);
                n = p;
            }

            return n;
        }

        private Node Primary()
        {
            if (_cur.Type == TokType.NUMBER || _cur.Type == TokType.STRING ||
                _cur.Type == TokType.TRUE_TOK || _cur.Type == TokType.FALSE_TOK || _cur.Type == TokType.NULL_TOK)
            {
                Token lit = _cur; _cur = _lex.Next();
                return new Node(NodeType.Literal, lit);
            }

            if (_cur.Type == TokType.THIS)
            {
                Token th = _cur; _cur = _lex.Next();
                return new Node(NodeType.Var, th);
            }

            if (_cur.Type == TokType.IDENT)
            {
                Token id = _cur; _cur = _lex.Next();
                return new Node(NodeType.Var, id);
            }

            if (Match(TokType.LPAREN))
            {
                var e = Expression();
                Consume(TokType.RPAREN, "')'");
                return e;
            }

            if (Match(TokType.NEW))
            {
                Token first = Consume(TokType.IDENT, "type/class name after new");
                var full = new StringBuilder(first.Lexeme);
                while (Match(TokType.DOT))
                {
                    Token part = Consume(TokType.IDENT, "type name part");
                    full.Append('.').Append(part.Lexeme);
                }

                Consume(TokType.LPAREN, "'(' after new X");
                var args = new Node(NodeType.Block);
                if (_cur.Type != TokType.RPAREN)
                {
                    args.Kids.Add(Expression());
                    while (Match(TokType.COMMA)) args.Kids.Add(Expression());
                }
                Consume(TokType.RPAREN, "')'");

                var n = new Node(NodeType.NewExpr, first);
                n.Text = full.ToString();
                n.Kids.Add(args);
                return n;
            }

            if (Match(TokType.LBRACK))
            {
                var arr = new Node(NodeType.ArrayLit, new Token(TokType.LBRACK, "[", _cur.Pos));
                if (_cur.Type != TokType.RBRACK)
                {
                    arr.Kids.Add(Expression());
                    while (Match(TokType.COMMA))
                    {
                        if (_cur.Type == TokType.RBRACK) break;
                        arr.Kids.Add(Expression());
                    }
                }
                Consume(TokType.RBRACK, "']'");
                return arr;
            }

            if (Match(TokType.LBRACE))
            {
                var obj = new Node(NodeType.ObjectLit, new Token(TokType.LBRACE, "{", _cur.Pos));

                string ParseKey()
                {
                    if (_cur.Type == TokType.IDENT) return Consume(TokType.IDENT, "object key").Lexeme;
                    if (_cur.Type == TokType.STRING) return Consume(TokType.STRING, "string key").Lexeme;
                    throw Err("expected object key (identifier or string)");
                }

                if (_cur.Type != TokType.RBRACE)
                {
                    while (true)
                    {
                        string key = ParseKey();
                        Consume(TokType.COLON, "':'");
                        var val = Expression();
                        obj.Kids.Add(new Node(NodeType.Literal, new Token(TokType.STRING, key, _cur.Pos)));
                        obj.Kids.Add(val);

                        if (!Match(TokType.COMMA)) break;
                        if (_cur.Type == TokType.RBRACE) break; // trailing comma
                    }
                }

                Consume(TokType.RBRACE, "'}'");
                return obj;
            }

            if (_cur.Type == TokType.FUNCTION)
            {
                Token ftok = Consume(TokType.FUNCTION, "'function'");

                Token nameTok = new Token(TokType.IDENT, "", ftok.Pos);
                if (_cur.Type == TokType.IDENT) nameTok = Consume(TokType.IDENT, "function name");

                Consume(TokType.LPAREN, "'('");
                var paramsTok = new List<Token>();
                if (_cur.Type != TokType.RPAREN)
                {
                    paramsTok.Add(Consume(TokType.IDENT, "param"));
                    while (Match(TokType.COMMA)) paramsTok.Add(Consume(TokType.IDENT, "param"));
                }
                Consume(TokType.RPAREN, "')'");

                var body = Block();

                var fe = new Node(NodeType.FunctionExpr, nameTok);
                var plist = new Node(NodeType.Block);
                foreach (var p in paramsTok) plist.Kids.Add(new Node(NodeType.Var, p));
                fe.Kids.Add(plist);
                fe.Kids.Add(body);
                return fe;
            }

            throw Err("unexpected token in primary");
        }
    }

    // ---------------- Script runtime types ----------------

    sealed class JsArray { public List<object?> Items = new(); }

    sealed class JsObject
    {
        public Dictionary<string, object?> Props = new();
        public List<string> Order = new();
        public ClassDef? Klass;
    }

    sealed class Env
    {
        private readonly object _lock = new();
        public Env? Parent;
        public Dictionary<string, object?> Vars = new();

        public Env(Env? p = null) { Parent = p; }

        public object? Get(string k)
        {
            lock (_lock)
            {
                if (Vars.TryGetValue(k, out var v)) return v;
            }
            if (Parent != null) return Parent.Get(k);
            throw new Exception("ReferenceError: " + k + " is not defined");
        }

        public bool TryGetHere(string k, out object? v)
        {
            lock (_lock) return Vars.TryGetValue(k, out v);
        }

        public bool ContainsHere(string k)
        {
            lock (_lock) return Vars.ContainsKey(k);
        }

        public void Set(string k, object? v)
        {
            lock (_lock)
            {
                if (Vars.ContainsKey(k)) { Vars[k] = v; return; }
            }
            if (Parent != null) { Parent.Set(k, v); return; }
            lock (_lock) Vars[k] = v;
        }

        public void Declare(string k, object? v)
        {
            lock (_lock) Vars[k] = v;
        }
    }

    sealed class Function
    {
        public List<string> Params = new();
        public Node? Body;            // Block node
        public Env? Closure;
        public bool IsNative = false;
        public Func<List<object?>, object?, object?>? Native;
    }

    sealed class ClassDef
    {
        public string Name = "";
        public Dictionary<string, Function> Methods = new();           // includes "constructor"
        public List<(string name, Node? initExpr)> Fields = new();     // (name, initExpr)
        public Env? Closure;                                           // for field init eval
    }

    sealed class ReturnSignal : Exception { public object? Value; public ReturnSignal(object? v) { Value = v; } }
    sealed class BreakSignal : Exception { }
    sealed class ContinueSignal : Exception { }

    sealed class ClrNamespace
    {
        public string Name;
        public ClrNamespace(string n) { Name = n; }
        public override string ToString() => $"[namespace {Name}]";
    }

    sealed class ClrCallable
    {
        public object? Target; // instance or Type
        public string Name;
        public ClrCallable(object? target, string name) { Target = target; Name = name; }
        public override string ToString() => "[clr-callable]";
    }

    sealed class JsTask
    {
        private readonly Task<object?> _task;

        public JsTask(Task<object?> task) { _task = task; }
        public bool Done => _task.IsCompleted;
        public string Status => _task.Status.ToString();
        public object? Result => _task.IsCompletedSuccessfully ? _task.Result : null;
        public object? Wait() => _task.GetAwaiter().GetResult();
        internal Task<object?> Task => _task;
        public override string ToString() => "[task]";
    }

    // ---------------- Helpers ----------------

    static class Rt
    {
        public static bool IsTruthy(object? v) => v switch
        {
            null => false,
            bool b => b,
            double d => d != 0.0,
            float f => f != 0.0f,
            int i => i != 0,
            long l => l != 0,
            string s => !string.IsNullOrEmpty(s),
            _ => true
        };

        public static string ToJsString(object? v)
        {
            if (v is null) return "null";
            if (v is bool b) return b ? "true" : "false";
            if (v is string s) return s;

            if (v is double d) return d.ToString(CultureInfo.InvariantCulture);
            if (v is float f) return f.ToString(CultureInfo.InvariantCulture);
            if (v is int i) return i.ToString(CultureInfo.InvariantCulture);
            if (v is long l) return l.ToString(CultureInfo.InvariantCulture);

            if (v is Enum en) return en.ToString();

            if (v is JsArray a)
            {
                List<object?> snap;
                lock (a) snap = a.Items.ToList();
                return "[" + string.Join(", ", snap.Select(ToJsString)) + "]";
            }

            if (v is JsObject o)
            {
                List<string> keys;
                Dictionary<string, object?> propsSnap;
                lock (o)
                {
                    keys = (o.Order.Count > 0 ? o.Order : o.Props.Keys.ToList()).ToList();
                    propsSnap = new Dictionary<string, object?>(o.Props);
                }
                var parts = new List<string>();
                foreach (var k in keys)
                {
                    if (!propsSnap.TryGetValue(k, out var vv)) continue;
                    parts.Add(k + ": " + ToJsString(vv));
                }
                return "{" + string.Join(", ", parts) + "}";
            }

            if (v is Function) return "[function]";
            if (v is ClassDef) return "[class]";
            if (v is ClrNamespace ns) return ns.ToString();
            if (v is Type t) return $"[type {t.FullName}]";
            if (v is ClrCallable) return "[clr-callable]";
            if (v is JsTask) return "[task]";

            return v.ToString() ?? "";
        }

        public static bool IsNumeric(object? v) =>
            v is byte or sbyte or short or ushort or int or uint or long or ulong or float or double or decimal;

        public static double ToNumber(object? v)
        {
            try
            {
                return v switch
                {
                    null => 0.0,
                    double d => d,
                    float f => f,
                    decimal m => (double)m,
                    int i => i,
                    long l => l,
                    bool b => b ? 1.0 : 0.0,
                    string s => string.IsNullOrEmpty(s) ? 0.0 : double.Parse(s, CultureInfo.InvariantCulture),
                    Enum e => Convert.ToDouble(e, CultureInfo.InvariantCulture),
                    _ => double.Parse(ToJsString(v), CultureInfo.InvariantCulture)
                };
            }
            catch
            {
                throw;
            }
        }

        public static int ToInt32(object? v)
        {
            double d = ToNumber(v);
            if (double.IsNaN(d) || double.IsInfinity(d) || d == 0.0) return 0;
            double two32 = 4294967296.0;
            double n = d >= 0 ? Math.Floor(d) : Math.Ceiling(d);
            n = n % two32;
            if (n < 0) n += two32;
            uint u = (uint)n;
            return unchecked((int)u);
        }
    }

    // ---------------- Task manager (queue + limit) ----------------

    sealed class TaskManager
    {
        private readonly object _cfgLock = new();
        private SemaphoreSlim _sem;
        private int _maxConcurrency;
        private int _queueLimit;
        private int _queued;

        public TaskManager(int maxConcurrency, int queueLimit)
        {
            _maxConcurrency = Math.Max(1, maxConcurrency);
            _queueLimit = Math.Max(1, queueLimit);
            _sem = new SemaphoreSlim(_maxConcurrency, _maxConcurrency);
        }

        public int MaxConcurrency { get { lock (_cfgLock) return _maxConcurrency; } }
        public int QueueLimit { get { lock (_cfgLock) return _queueLimit; } }
        public int Queued => Volatile.Read(ref _queued);

        public void SetMaxConcurrency(int n)
        {
            n = Math.Max(1, n);
            lock (_cfgLock)
            {
                if (n == _maxConcurrency) return;
                _maxConcurrency = n;
                _sem = new SemaphoreSlim(_maxConcurrency, _maxConcurrency);
            }
        }

        public void SetQueueLimit(int n)
        {
            n = Math.Max(1, n);
            lock (_cfgLock) _queueLimit = n;
        }

        public Task<object?> Enqueue(Func<object?> work)
        {
            int q = Interlocked.Increment(ref _queued);
            int limit = QueueLimit;
            if (q > limit)
            {
                Interlocked.Decrement(ref _queued);
                throw new Exception($"Task queue overflow (limit={limit})");
            }

            SemaphoreSlim sem;
            lock (_cfgLock) sem = _sem;

            return Task.Run(async () =>
            {
                await sem.WaitAsync().ConfigureAwait(false);
                try
                {
                    return work();
                }
                finally
                {
                    sem.Release();
                    Interlocked.Decrement(ref _queued);
                }
            });
        }
    }

    // ---------------- AST dump (optional) ----------------

    static class AstDump
    {
        public static void Dump(Node? n, int indent = 0)
        {
            if (n == null)
            {
                Console.WriteLine(new string(' ', indent) + "(null)");
                return;
            }

            string pad = new string(' ', indent);
            Console.Write(pad + n.Type);

            if (n.Tok.Type != TokType.EOF_TOK || !string.IsNullOrEmpty(n.Tok.Lexeme))
                Console.Write($"  tok={Tok.Name(n.Tok.Type)} '{n.Tok.Lexeme}' @{n.Tok.Pos}");

            if (!string.IsNullOrEmpty(n.Text))
                Console.Write($"  text='{n.Text}'");

            Console.WriteLine();
            foreach (var k in n.Kids) Dump(k, indent + 2);
        }
    }

    // ---------------- Interpreter ----------------

    readonly struct EventKey
    {
        public readonly object Target;
        public readonly string EventName;
        public EventKey(object target, string eventName) { Target = target; EventName = eventName; }
    }

    sealed class EventKeyComparer : IEqualityComparer<EventKey>
    {
        public bool Equals(EventKey x, EventKey y) =>
            ReferenceEquals(x.Target, y.Target) && StringComparer.Ordinal.Equals(x.EventName, y.EventName);

        public int GetHashCode(EventKey obj) =>
            (RuntimeHelpers.GetHashCode(obj.Target) * 397) ^ StringComparer.Ordinal.GetHashCode(obj.EventName);
    }

    sealed class Interpreter
    {
        public Env Global;

        private readonly TaskManager _taskMgr;

        private readonly object _namedLocksGuard = new();
        private readonly Dictionary<string, object> _namedLocks = new(StringComparer.Ordinal);

        private readonly object _eventSubsGuard = new();
        private readonly Dictionary<EventKey, List<Delegate>> _eventSubs = new(new EventKeyComparer());

        private readonly Dictionary<string, Type?> _typeCache = new(StringComparer.Ordinal);

        public Interpreter()
        {
            Global = new Env();
            _taskMgr = new TaskManager(Math.Max(1, Environment.ProcessorCount), 5000);

            // builtin print(...)
            var pf = new Function
            {
                IsNative = true,
                Native = (args, _) =>
                {
                    for (int i = 0; i < args.Count; i++)
                    {
                        if (i != 0) Console.Write(" ");
                        Console.Write(Rt.ToJsString(args[i]));
                    }
                    Console.WriteLine();
                    return null;
                }
            };
            Global.Declare("print", pf);

            // root namespace
            Global.Declare("System", new ClrNamespace("System"));

            // task tuning
            Global.Declare("setTaskLimit", new Function
            {
                IsNative = true,
                Native = (args, _) =>
                {
                    int n = args.Count > 0 ? (int)Rt.ToNumber(args[0]) : Environment.ProcessorCount;
                    _taskMgr.SetMaxConcurrency(n);
                    return null;
                }
            });

            Global.Declare("setTaskQueueLimit", new Function
            {
                IsNative = true,
                Native = (args, _) =>
                {
                    int n = args.Count > 0 ? (int)Rt.ToNumber(args[0]) : 5000;
                    _taskMgr.SetQueueLimit(n);
                    return null;
                }
            });

            Global.Declare("taskStats", new Function
            {
                IsNative = true,
                Native = (_, __) =>
                {
                    var o = new JsObject();
                    lock (o)
                    {
                        o.Order.Add("MaxConcurrency"); o.Props["MaxConcurrency"] = (double)_taskMgr.MaxConcurrency;
                        o.Order.Add("QueueLimit"); o.Props["QueueLimit"] = (double)_taskMgr.QueueLimit;
                        o.Order.Add("Queued"); o.Props["Queued"] = (double)_taskMgr.Queued;
                    }
                    return o;
                }
            });

            // UI marshal helpers
            Global.Declare("ui", new Function
            {
                IsNative = true,
                Native = (args, _) =>
                {
                    if (args.Count < 2) throw new Exception("TypeError: ui(control, fn) expects 2 args");
                    object? target = args[0];
                    object? fnObj = args[1];

                    object? Run()
                    {
                        if (fnObj is Function f) return CallFunction(f, new List<object?>(), target);
                        if (fnObj is Delegate d) return d.DynamicInvoke();
                        throw new Exception("TypeError: ui(control, fn) fn must be a function");
                    }

                    if (target is Control c)
                    {
                        try { if (!c.IsHandleCreated) _ = c.Handle; } catch { }
                        if (c.InvokeRequired) return c.Invoke(new Func<object?>(Run));
                        return Run();
                    }

                    if (target is ISynchronizeInvoke sync)
                    {
                        if (sync.InvokeRequired) return sync.Invoke(new Func<object?>(Run), Array.Empty<object>());
                        return Run();
                    }

                    throw new Exception("TypeError: ui(control, fn) requires WinForms Control (or ISynchronizeInvoke)");
                }
            });

            Global.Declare("uiAsync", new Function
            {
                IsNative = true,
                Native = (args, _) =>
                {
                    if (args.Count < 2) throw new Exception("TypeError: uiAsync(control, fn) expects 2 args");
                    object? target = args[0];
                    object? fnObj = args[1];

                    void Run()
                    {
                        if (fnObj is Function f) { CallFunction(f, new List<object?>(), target); return; }
                        if (fnObj is Delegate d) { d.DynamicInvoke(); return; }
                        throw new Exception("TypeError: uiAsync(control, fn) fn must be a function");
                    }

                    if (target is Control c)
                    {
                        try { if (!c.IsHandleCreated) _ = c.Handle; } catch { }
                        if (c.InvokeRequired) return c.BeginInvoke(new System.Windows.Forms.MethodInvoker(Run));
                        Run();
                        return null;
                    }

                    if (target is ISynchronizeInvoke sync)
                    {
                        if (sync.InvokeRequired) return sync.BeginInvoke(new System.Windows.Forms.MethodInvoker(Run), Array.Empty<object>());
                        Run();
                        return null;
                    }

                    throw new Exception("TypeError: uiAsync(control, fn) requires WinForms Control (or ISynchronizeInvoke)");
                }
            });
        }

        // ---------------- Script function call ----------------

        public object? CallFunction(Function fn, List<object?> args, object? thisVal)
        {
            if (fn.IsNative) return fn.Native!(args, thisVal);

            var fenv = new Env(fn.Closure);
            fenv.Declare("this", thisVal);

            for (int i = 0; i < fn.Params.Count; i++)
            {
                var v = (i < args.Count) ? args[i] : null;
                fenv.Declare(fn.Params[i], v);
            }

            try
            {
                return Eval(fn.Body!, fenv);
            }
            catch (ReturnSignal rs)
            {
                return rs.Value;
            }
        }

        // ---------------- CLR type resolution ----------------

        private Type? ResolveClrType(string fullName)
        {
            lock (_typeCache)
            {
                if (_typeCache.TryGetValue(fullName, out var cached)) return cached;
            }

            Type? found = null;
            foreach (var asm in AppDomain.CurrentDomain.GetAssemblies())
            {
                found = asm.GetType(fullName, throwOnError: false, ignoreCase: false);
                if (found != null) break;
            }

            // small helper: allow "System.Collections.Generic.List" -> List`1<object>
            if (found == null)
            {
                string gen1 = fullName + "`1";
                Type? gdef = null;
                foreach (var asm in AppDomain.CurrentDomain.GetAssemblies())
                {
                    gdef = asm.GetType(gen1, false, false);
                    if (gdef != null) break;
                }
                if (gdef != null && gdef.IsGenericTypeDefinition && gdef.GetGenericArguments().Length == 1)
                {
                    try { found = gdef.MakeGenericType(typeof(object)); } catch { }
                }
            }

            lock (_typeCache) _typeCache[fullName] = found;
            return found;
        }

        // ---------------- Reflection member resolution (fixes ambiguous Controls) ----------------

        private static PropertyInfo? GetMostDerivedProperty(Type t, string name, bool isStatic)
        {
            var flags = BindingFlags.Public | BindingFlags.Instance | BindingFlags.Static;
            if (isStatic) flags = BindingFlags.Public | BindingFlags.Static;
            else flags = BindingFlags.Public | BindingFlags.Instance;

            for (Type? cur = t; cur != null; cur = cur.BaseType)
            {
                var props = cur.GetProperties(flags | BindingFlags.DeclaredOnly)
                               .Where(p => p.Name == name)
                               .ToArray();
                if (props.Length > 0) return props[0];
            }
            return null;
        }

        private static FieldInfo? GetMostDerivedField(Type t, string name, bool isStatic)
        {
            var flags = BindingFlags.Public | BindingFlags.Instance | BindingFlags.Static;
            if (isStatic) flags = BindingFlags.Public | BindingFlags.Static;
            else flags = BindingFlags.Public | BindingFlags.Instance;

            for (Type? cur = t; cur != null; cur = cur.BaseType)
            {
                var fld = cur.GetField(name, flags | BindingFlags.DeclaredOnly);
                if (fld != null) return fld;
            }
            return null;
        }

        private static EventInfo? GetMostDerivedEvent(Type t, string name, bool isStatic)
        {
            var flags = BindingFlags.Public | BindingFlags.Instance | BindingFlags.Static;
            if (isStatic) flags = BindingFlags.Public | BindingFlags.Static;
            else flags = BindingFlags.Public | BindingFlags.Instance;

            for (Type? cur = t; cur != null; cur = cur.BaseType)
            {
                var evs = cur.GetEvents(flags | BindingFlags.DeclaredOnly)
                             .Where(e => e.Name == name)
                             .ToArray();
                if (evs.Length > 0) return evs[0];
            }
            return null;
        }

        private static MethodInfo[] GetAllMethods(Type t, string name, bool isStatic)
        {
            var flags = BindingFlags.Public | BindingFlags.Instance | BindingFlags.Static;
            if (isStatic) flags = BindingFlags.Public | BindingFlags.Static;
            else flags = BindingFlags.Public | BindingFlags.Instance;

            return t.GetMethods(flags).Where(m => m.Name == name).ToArray();
        }

        // ---------------- Conversions / overload resolution ----------------

        private static bool IsNullableType(Type t) =>
            t.IsGenericType && t.GetGenericTypeDefinition() == typeof(Nullable<>);

        private object? ConvertArg(object? arg, Type targetType)
        {
            if (targetType == typeof(object)) return arg;

            if (arg == null)
            {
                if (!targetType.IsValueType || IsNullableType(targetType)) return null;
                throw new Exception($"TypeError: cannot convert null to {targetType.Name}");
            }

            var argType = arg.GetType();
            if (targetType.IsAssignableFrom(argType)) return arg;

            if (targetType.IsEnum)
            {
                if (arg is string s) return Enum.Parse(targetType, s, ignoreCase: true);
                if (Rt.IsNumeric(arg)) return Enum.ToObject(targetType, Convert.ChangeType(arg, Enum.GetUnderlyingType(targetType), CultureInfo.InvariantCulture)!);
            }

            // Function -> Delegate
            if (typeof(Delegate).IsAssignableFrom(targetType) && arg is Function fn)
            {
                return CreateDelegateFromFunction(targetType, fn, thisValForCall: null);
            }

            // numbers
            if (targetType == typeof(int)) return (int)Rt.ToNumber(arg);
            if (targetType == typeof(long)) return (long)Rt.ToNumber(arg);
            if (targetType == typeof(float)) return (float)Rt.ToNumber(arg);
            if (targetType == typeof(double)) return Rt.ToNumber(arg);
            if (targetType == typeof(bool)) return Rt.IsTruthy(arg);
            if (targetType == typeof(string)) return Rt.ToJsString(arg);

            try
            {
                if (arg is IConvertible && typeof(IConvertible).IsAssignableFrom(targetType))
                    return Convert.ChangeType(arg, targetType, CultureInfo.InvariantCulture);

                // string -> type via TypeConverter
                if (arg is string str)
                {
                    var conv = TypeDescriptor.GetConverter(targetType);
                    if (conv != null && conv.CanConvertFrom(typeof(string)))
                        return conv.ConvertFromInvariantString(str);
                }
            }
            catch { }

            throw new Exception($"TypeError: cannot convert {argType.Name} to {targetType.Name}");
        }

        private sealed class Candidate
        {
            public MethodBase M;
            public int Score;
            public object?[] FinalArgs;
            public Candidate(MethodBase m, int score, object?[] finalArgs) { M = m; Score = score; FinalArgs = finalArgs; }
        }

        private MethodBase SelectBestOverload(IEnumerable<MethodBase> methods, List<object?> args, out object?[] finalArgs)
        {
            Candidate? best = null;

            foreach (var mb in methods)
            {
                var ps = mb.GetParameters();
                bool hasParams = ps.Length > 0 && ps[^1].GetCustomAttributes(typeof(ParamArrayAttribute), false).Any();

                int minCount = 0;
                for (int i = 0; i < ps.Length; i++)
                {
                    if (hasParams && i == ps.Length - 1) break;
                    if (!ps[i].IsOptional) minCount++;
                }

                if (!hasParams)
                {
                    if (args.Count < minCount) continue;
                    if (args.Count > ps.Length) continue;
                }
                else
                {
                    if (args.Count < minCount) continue;
                }

                var built = new List<object?>();
                int score = 0;

                try
                {
                    int fixedCount = hasParams ? ps.Length - 1 : ps.Length;

                    // fixed parameters
                    for (int i = 0; i < fixedCount; i++)
                    {
                        if (i < args.Count)
                        {
                            var a = args[i];
                            var conv = ConvertArg(a, ps[i].ParameterType);
                            built.Add(conv);
                            score += ScoreArg(a, conv, ps[i].ParameterType);
                        }
                        else
                        {
                            built.Add(ps[i].DefaultValue);
                            score += 5; // penalty for default
                        }
                    }

                    // params array
                    if (hasParams)
                    {
                        Type elemType = ps[^1].ParameterType.GetElementType() ?? typeof(object);
                        int extra = Math.Max(0, args.Count - fixedCount);
                        Array arr = Array.CreateInstance(elemType, extra);
                        for (int j = 0; j < extra; j++)
                        {
                            var a = args[fixedCount + j];
                            var conv = ConvertArg(a, elemType);
                            arr.SetValue(conv, j);
                            score += ScoreArg(a, conv, elemType);
                        }
                        built.Add(arr);
                    }
                    else
                    {
                        // remaining optional (if any) already covered by exact count check
                    }

                    // prefer non-params / fewer defaults
                    if (hasParams) score += 2;

                    var cand = new Candidate(mb, score, built.ToArray());
                    if (best == null || cand.Score < best.Score) best = cand;
                }
                catch
                {
                    continue;
                }
            }

            if (best == null) throw new Exception("TypeError: no matching overload");

            finalArgs = best.FinalArgs;
            return best.M;
        }

        private static int ScoreArg(object? original, object? converted, Type targetType)
        {
            if (original == null && converted == null) return 0;
            if (original != null && converted != null && original.GetType() == converted.GetType()) return 0;
            if (targetType == typeof(object)) return 3;
            if (targetType == typeof(string)) return 3;
            if (targetType.IsEnum) return 2;
            return 1;
        }

        private Delegate CreateDelegateFromFunction(Type delegateType, Function fn, object? thisValForCall)
        {
            var invoke = delegateType.GetMethod("Invoke") ?? throw new Exception("TypeError: invalid delegate type");
            var pars = invoke.GetParameters();
            var paramExprs = pars.Select(p => Expression.Parameter(p.ParameterType, p.Name ?? "p")).ToArray();

            // build: (p1,p2,...) => { call script fn with args (boxed), return default(T) }
            var argsArrExpr = Expression.NewArrayInit(
                typeof(object),
                paramExprs.Select(pe => Expression.Convert(pe, typeof(object)))
            );

            var callHelper = typeof(Interpreter).GetMethod(nameof(InvokeScriptFromDelegate), BindingFlags.Instance | BindingFlags.NonPublic)!;

            var callExpr = Expression.Call(
                Expression.Constant(this),
                callHelper,
                Expression.Constant(fn, typeof(Function)),
                Expression.Constant(thisValForCall, typeof(object)),
                argsArrExpr
            );

            Expression body;
            if (invoke.ReturnType == typeof(void))
            {
                body = callExpr;
            }
            else
            {
                // convert result to return type (best-effort)
                var convertHelper = typeof(Interpreter).GetMethod(nameof(ConvertReturnForDelegate), BindingFlags.Instance | BindingFlags.NonPublic)!;
                var converted = Expression.Call(
                    Expression.Constant(this),
                    convertHelper,
                    callExpr,
                    Expression.Constant(invoke.ReturnType, typeof(Type))
                );
                body = Expression.Convert(converted, invoke.ReturnType);
            }

            var lambda = Expression.Lambda(delegateType, body, paramExprs);
            return lambda.Compile();
        }

        private object? ConvertReturnForDelegate(object? v, Type returnType)
        {
            if (returnType == typeof(object)) return v;
            if (returnType == typeof(void)) return null;
            return ConvertArg(v, returnType);
        }

        private object? InvokeScriptFromDelegate(Function fn, object? thisVal, object[] args)
        {
            var list = new List<object?>();
            foreach (var a in args) list.Add(a);

            // JS-ish: if fn has fewer params, pass only that many
            if (fn.Params.Count >= 0 && list.Count > fn.Params.Count)
                list = list.Take(fn.Params.Count).ToList();

            return CallFunction(fn, list, thisVal);
        }

        // ---------------- Event bridging (generic) ----------------

        private void SetEventHandler(object target, EventInfo ev, object? newVal)
        {
            var key = new EventKey(target, ev.Name);

            // remove old
            lock (_eventSubsGuard)
            {
                if (_eventSubs.TryGetValue(key, out var oldList))
                {
                    foreach (var d in oldList)
                        ev.RemoveEventHandler(target, d);
                    _eventSubs.Remove(key);
                }
            }

            if (newVal == null) return;

            if (newVal is not Function fn)
                throw new Exception($"TypeError: event '{ev.Name}' expects function or null");

            var del = CreateDelegateFromFunction(ev.EventHandlerType!, fn, thisValForCall: target);

            ev.AddEventHandler(target, del);

            lock (_eventSubsGuard)
            {
                if (!_eventSubs.TryGetValue(key, out var list))
                {
                    list = new List<Delegate>();
                    _eventSubs[key] = list;
                }
                list.Add(del);
            }
        }

        // ---------------- LValue get/set for ++, assignments ----------------

        // kind: 0=var, 1=member, 2=index
        private object? EvalLValueGet(Node target, Env env, ref object? outRecv, ref string outProp, ref object? outIdx, ref int outKind)
        {
            if (target.Type == NodeType.Var)
            {
                outKind = 0;
                outProp = target.Tok.Lexeme;
                return env.Get(outProp);
            }

            if (target.Type == NodeType.Member)
            {
                outKind = 1;
                outRecv = Eval(target.Kids[0]!, env);
                outProp = target.Kids[1]!.Tok.Lexeme;

                if (outRecv is JsObject jo)
                {
                    lock (jo)
                    {
                        if (jo.Props.TryGetValue(outProp, out var v)) return v;
                        if (jo.Klass != null && jo.Klass.Methods.TryGetValue(outProp, out var mfn)) return mfn;
                    }
                    return null;
                }

                if (outRecv is Type tStatic)
                {
                    // static access
                    if (tStatic.IsEnum)
                    {
                        try { return Enum.Parse(tStatic, outProp, ignoreCase: true); } catch { return null; }
                    }

                    var p = GetMostDerivedProperty(tStatic, outProp, isStatic: true);
                    if (p != null && p.GetMethod != null) return p.GetValue(null);

                    var f = GetMostDerivedField(tStatic, outProp, isStatic: true);
                    if (f != null) return f.GetValue(null);

                    var ev = GetMostDerivedEvent(tStatic, outProp, isStatic: true);
                    if (ev != null) return null;

                    var ms = GetAllMethods(tStatic, outProp, isStatic: true);
                    if (ms.Length > 0) return new ClrCallable(tStatic, outProp);

                    return null;
                }

                if (outRecv is ClrNamespace ns)
                {
                    // namespace resolution: return nested namespace or type
                    string full = ns.Name + "." + outProp;
                    var ty = ResolveClrType(full);
                    if (ty != null) return ty;
                    return new ClrNamespace(full);
                }

                if (outRecv != null)
                {
                    var t = outRecv.GetType();

                    var p = GetMostDerivedProperty(t, outProp, isStatic: false);
                    if (p != null && p.GetMethod != null) return p.GetValue(outRecv);

                    var f = GetMostDerivedField(t, outProp, isStatic: false);
                    if (f != null) return f.GetValue(outRecv);

                    var ev = GetMostDerivedEvent(t, outProp, isStatic: false);
                    if (ev != null) return null;

                    var ms = GetAllMethods(t, outProp, isStatic: false);
                    if (ms.Length > 0) return new ClrCallable(outRecv, outProp);

                    return null;
                }

                return null;
            }

            if (target.Type == NodeType.Index)
            {
                outKind = 2;
                outRecv = Eval(target.Kids[0]!, env);
                outIdx = Eval(target.Kids[1]!, env);

                if (outRecv is JsArray ja)
                {
                    long i = (long)Rt.ToNumber(outIdx);
                    lock (ja)
                    {
                        if (i < 0 || i >= ja.Items.Count) return null;
                        return ja.Items[(int)i];
                    }
                }

                if (outRecv is JsObject jo)
                {
                    string key = Rt.ToJsString(outIdx);
                    lock (jo)
                    {
                        if (jo.Props.TryGetValue(key, out var v)) return v;
                        return null;
                    }
                }

                if (outRecv is Array arr)
                {
                    int i = (int)Rt.ToNumber(outIdx);
                    if (i < 0 || i >= arr.Length) return null;
                    return arr.GetValue(i);
                }

                if (outRecv is IList list)
                {
                    int i = (int)Rt.ToNumber(outIdx);
                    if (i < 0 || i >= list.Count) return null;
                    return list[i];
                }

                if (outRecv is IDictionary dict)
                {
                    var key = outIdx;
                    return dict.Contains(key) ? dict[key] : null;
                }

                throw new Exception("TypeError: index access on non-array/object");
            }

            throw new Exception("Invalid assignment target");
        }

        private void EvalLValueSet(Node target, Env env, object? recv, string prop, object? idx, int kind, object? newVal)
        {
            if (kind == 0)
            {
                env.Set(prop, newVal);
                return;
            }

            if (kind == 1)
            {
                if (recv is JsObject jo)
                {
                    lock (jo)
                    {
                        if (!jo.Props.ContainsKey(prop)) jo.Order.Add(prop);
                        jo.Props[prop] = newVal;
                    }
                    return;
                }

                if (recv is Type tStatic)
                {
                    var p = GetMostDerivedProperty(tStatic, prop, isStatic: true);
                    if (p != null && p.SetMethod != null)
                    {
                        var cv = ConvertArg(newVal, p.PropertyType);
                        p.SetValue(null, cv);
                        return;
                    }

                    var f = GetMostDerivedField(tStatic, prop, isStatic: true);
                    if (f != null && !f.IsInitOnly)
                    {
                        var cv = ConvertArg(newVal, f.FieldType);
                        f.SetValue(null, cv);
                        return;
                    }

                    var ev = GetMostDerivedEvent(tStatic, prop, isStatic: true);
                    if (ev != null) throw new Exception("TypeError: cannot assign static event this way");

                    throw new Exception($"TypeError: cannot set member '{prop}' on type '{tStatic.FullName}'");
                }

                if (recv == null) throw new Exception("TypeError: member set on null");

                var t = recv.GetType();

                // event assign bridge
                var ev2 = GetMostDerivedEvent(t, prop, isStatic: false);
                if (ev2 != null)
                {
                    SetEventHandler(recv, ev2, newVal);
                    return;
                }

                var p2 = GetMostDerivedProperty(t, prop, isStatic: false);
                if (p2 != null && p2.SetMethod != null)
                {
                    var cv = ConvertArg(newVal, p2.PropertyType);
                    p2.SetValue(recv, cv);
                    return;
                }

                var f2 = GetMostDerivedField(t, prop, isStatic: false);
                if (f2 != null && !f2.IsInitOnly)
                {
                    var cv = ConvertArg(newVal, f2.FieldType);
                    f2.SetValue(recv, cv);
                    return;
                }

                throw new Exception($"TypeError: cannot set member '{prop}' on '{t.Name}'");
            }

            if (kind == 2)
            {
                if (recv is JsArray ja)
                {
                    long i = (long)Rt.ToNumber(idx);
                    if (i < 0) throw new Exception("RangeError: negative index");
                    int ui = (int)i;
                    lock (ja)
                    {
                        while (ja.Items.Count <= ui) ja.Items.Add(null);
                        ja.Items[ui] = newVal;
                    }
                    return;
                }

                if (recv is JsObject jo)
                {
                    string k = Rt.ToJsString(idx);
                    lock (jo)
                    {
                        if (!jo.Props.ContainsKey(k)) jo.Order.Add(k);
                        jo.Props[k] = newVal;
                    }
                    return;
                }

                if (recv is Array arr)
                {
                    int i = (int)Rt.ToNumber(idx);
                    if (i < 0 || i >= arr.Length) throw new Exception("RangeError: index out of range");
                    var cv = ConvertArg(newVal, arr.GetType().GetElementType() ?? typeof(object));
                    arr.SetValue(cv, i);
                    return;
                }

                if (recv is IList list)
                {
                    int i = (int)Rt.ToNumber(idx);
                    if (i < 0) throw new Exception("RangeError: negative index");
                    while (list.Count <= i) list.Add(null);
                    list[i] = newVal;
                    return;
                }

                if (recv is IDictionary dict)
                {
                    dict[idx!] = newVal;
                    return;
                }

                throw new Exception("TypeError: index assign on non-array/object");
            }
        }

        // ---------------- CLR invoke ----------------

        private object? InvokeClrMethod(object? targetOrType, string name, List<object?> args)
        {
            if (targetOrType is Type t)
            {
                var methods = GetAllMethods(t, name, isStatic: true).Cast<MethodBase>().ToArray();
                if (methods.Length == 0) throw new Exception($"TypeError: method not found: {t.FullName}.{name}");

                var mb = SelectBestOverload(methods, args, out var finalArgs);
                return mb.Invoke(null, finalArgs);
            }
            else
            {
                if (targetOrType == null) throw new Exception("TypeError: call on null");
                var t2 = targetOrType.GetType();

                var methods = GetAllMethods(t2, name, isStatic: false).Cast<MethodBase>().ToArray();
                if (methods.Length == 0) throw new Exception($"TypeError: method not found: {t2.Name}.{name}");

                var mb = SelectBestOverload(methods, args, out var finalArgs);
                return mb.Invoke(targetOrType, finalArgs);
            }
        }

        private object? CreateClrInstance(Type t, List<object?> args)
        {
            if (t.IsAbstract && t.IsSealed)
                throw new Exception($"Cannot dynamically create an instance of type '{t.FullName}'. Reason: Cannot create a static class.");

            if (t.IsAbstract)
                throw new Exception($"Cannot dynamically create an instance of type '{t.FullName}'. Reason: Cannot create an abstract class.");

            var ctors = t.GetConstructors(BindingFlags.Public | BindingFlags.Instance).Cast<MethodBase>().ToArray();
            if (ctors.Length == 0)
            {
                if (args.Count == 0) return Activator.CreateInstance(t);
                throw new Exception($"TypeError: no public constructors for {t.FullName}");
            }

            var mb = SelectBestOverload(ctors, args, out var finalArgs);
            return ((ConstructorInfo)mb).Invoke(finalArgs);
        }

        // ---------------- Binary ops ----------------

        private object? BinaryPlus(object? l, object? r)
        {
            if (l is string || r is string)
                return Rt.ToJsString(l) + Rt.ToJsString(r);
            return Rt.ToNumber(l) + Rt.ToNumber(r);
        }

        private static bool StrictEq(object? a, object? b)
        {
            if (a == null && b == null) return true;
            if (a == null || b == null) return false;

            if (Rt.IsNumeric(a) && Rt.IsNumeric(b))
                return Rt.ToNumber(a) == Rt.ToNumber(b);

            if (a.GetType() != b.GetType()) return false;

            // for reference types, keep JS-ish strictness by reference equality
            if (!a.GetType().IsValueType)
                return ReferenceEquals(a, b);

            return a.Equals(b);
        }

        // ---------------- Eval / Exec ----------------

        public object? Eval(Node n, Env env)
        {
            if (n == null) return null;

            switch (n.Type)
            {
                case NodeType.Program:
                    {
                        object? last = null;
                        foreach (var s in n.Kids) last = Exec(s!, env);
                        return last;
                    }

                case NodeType.Block:
                    {
                        var benv = new Env(env);
                        object? last = null;
                        foreach (var s in n.Kids) last = Exec(s!, benv);
                        return last;
                    }

                case NodeType.Literal:
                    {
                        if (n.Tok.Type == TokType.NUMBER) return double.Parse(n.Tok.Lexeme, CultureInfo.InvariantCulture);
                        if (n.Tok.Type == TokType.STRING) return n.Tok.Lexeme;
                        if (n.Tok.Type == TokType.TRUE_TOK) return true;
                        if (n.Tok.Type == TokType.FALSE_TOK) return false;
                        return null;
                    }

                case NodeType.Var:
                    return env.Get(n.Tok.Lexeme);

                case NodeType.ArrayLit:
                    {
                        var a = new JsArray();
                        lock (a)
                        {
                            foreach (var k in n.Kids) a.Items.Add(Eval(k!, env));
                        }
                        return a;
                    }

                case NodeType.ObjectLit:
                    {
                        var o = new JsObject();
                        lock (o)
                        {
                            for (int i = 0; i + 1 < n.Kids.Count; i += 2)
                            {
                                var keyNode = n.Kids[i]!;
                                var valNode = n.Kids[i + 1]!;
                                string k = keyNode.Tok.Lexeme;
                                if (!o.Props.ContainsKey(k)) o.Order.Add(k);
                                o.Props[k] = Eval(valNode, env);
                            }
                        }
                        return o;
                    }

                case NodeType.FunctionExpr:
                    {
                        var fn = new Function { Closure = env, Body = n.Kids[1]! };
                        foreach (var p in n.Kids[0]!.Kids) fn.Params.Add(p!.Tok.Lexeme);
                        return fn;
                    }

                case NodeType.TaskBlock:
                    {
                        // internal: used by task expression
                        var fn = new Function { Closure = env, Body = n };
                        return fn;
                    }

                case NodeType.Unary:
                    {
                        object? r = Eval(n.Kids[0]!, env);

                        switch (n.Tok.Type)
                        {
                            case TokType.BANG: return !Rt.IsTruthy(r);
                            case TokType.PLUS: return Rt.ToNumber(r);
                            case TokType.MINUS: return -Rt.ToNumber(r);
                            case TokType.BITNOT: return ~Rt.ToInt32(r);

                            case TokType.INC:
                            case TokType.DEC:
                                {
                                    var target = n.Kids[0]!;
                                    object? recv = null; object? idx = null; string prop = ""; int kind = -1;
                                    object? oldVal = EvalLValueGet(target, env, ref recv, ref prop, ref idx, ref kind);
                                    double x = Rt.ToNumber(oldVal);
                                    double nx = (n.Tok.Type == TokType.INC) ? (x + 1.0) : (x - 1.0);
                                    var newVal = (object?)nx;
                                    EvalLValueSet(target, env, recv, prop, idx, kind, newVal);
                                    return newVal;
                                }

                            default:
                                throw new Exception("Unknown unary op");
                        }
                    }

                case NodeType.Postfix:
                    {
                        var target = n.Kids[0]!;
                        object? recv = null; object? idx = null; string prop = ""; int kind = -1;
                        object? oldVal = EvalLValueGet(target, env, ref recv, ref prop, ref idx, ref kind);
                        double x = Rt.ToNumber(oldVal);
                        double nx = (n.Tok.Type == TokType.INC) ? (x + 1.0) : (x - 1.0);
                        var newVal = (object?)nx;
                        EvalLValueSet(target, env, recv, prop, idx, kind, newVal);
                        return oldVal;
                    }

                case NodeType.Binary:
                    {
                        if (n.Tok.Type == TokType.AND)
                        {
                            var l = Eval(n.Kids[0]!, env);
                            if (!Rt.IsTruthy(l)) return l;
                            return Eval(n.Kids[1]!, env);
                        }
                        if (n.Tok.Type == TokType.OR)
                        {
                            var l = Eval(n.Kids[0]!, env);
                            if (Rt.IsTruthy(l)) return l;
                            return Eval(n.Kids[1]!, env);
                        }

                        var l2 = Eval(n.Kids[0]!, env);
                        var r2 = Eval(n.Kids[1]!, env);

                        switch (n.Tok.Type)
                        {
                            case TokType.PLUS: return BinaryPlus(l2, r2);
                            case TokType.MINUS: return Rt.ToNumber(l2) - Rt.ToNumber(r2);
                            case TokType.MUL: return Rt.ToNumber(l2) * Rt.ToNumber(r2);
                            case TokType.DIV: return Rt.ToNumber(l2) / Rt.ToNumber(r2);
                            case TokType.MOD: return Rt.ToNumber(l2) % Rt.ToNumber(r2);
                            case TokType.POW: return Math.Pow(Rt.ToNumber(l2), Rt.ToNumber(r2));

                            case TokType.LT: return Rt.ToNumber(l2) < Rt.ToNumber(r2);
                            case TokType.LEQ: return Rt.ToNumber(l2) <= Rt.ToNumber(r2);
                            case TokType.GT: return Rt.ToNumber(l2) > Rt.ToNumber(r2);
                            case TokType.GEQ: return Rt.ToNumber(l2) >= Rt.ToNumber(r2);

                            case TokType.BITAND: return Rt.ToInt32(l2) & Rt.ToInt32(r2);
                            case TokType.BITOR: return Rt.ToInt32(l2) | Rt.ToInt32(r2);
                            case TokType.BITXOR: return Rt.ToInt32(l2) ^ Rt.ToInt32(r2);

                            case TokType.EQ: return StrictEq(l2, r2);
                            case TokType.NEQ: return !StrictEq(l2, r2);

                            default:
                                throw new Exception("Unknown binary op");
                        }
                    }

                case NodeType.Member:
                    {
                        object? recv = Eval(n.Kids[0]!, env);
                        string prop = n.Kids[1]!.Tok.Lexeme;

                        // namespace: System.X
                        if (recv is ClrNamespace ns)
                        {
                            string full = ns.Name + "." + prop;
                            var ty = ResolveClrType(full);
                            if (ty != null) return ty;
                            return new ClrNamespace(full);
                        }

                        // Type: static access / enum access
                        if (recv is Type tStatic)
                        {
                            if (tStatic.IsEnum)
                            {
                                try { return Enum.Parse(tStatic, prop, ignoreCase: true); } catch { return null; }
                            }

                            var p = GetMostDerivedProperty(tStatic, prop, isStatic: true);
                            if (p != null && p.GetMethod != null) return p.GetValue(null);

                            var f = GetMostDerivedField(tStatic, prop, isStatic: true);
                            if (f != null) return f.GetValue(null);

                            var ev = GetMostDerivedEvent(tStatic, prop, isStatic: true);
                            if (ev != null) return null;

                            var ms = GetAllMethods(tStatic, prop, isStatic: true);
                            if (ms.Length > 0) return new ClrCallable(tStatic, prop);

                            return null;
                        }

                        // script array
                        if (recv is JsArray ja2)
                        {
                            if (prop == "length")
                            {
                                int len;
                                lock (ja2) len = ja2.Items.Count;
                                return (double)len;
                            }
                            return null;
                        }

                        // script object
                        if (recv is JsObject jo)
                        {
                            lock (jo)
                            {
                                // echte property gewinnt (falls user obj.length = 123 setzt)
                                if (jo.Props.TryGetValue(prop, out var v)) return v;

                                // fallback: length = Anzahl Properties
                                if (prop == "length")
                                    return (double)jo.Props.Count; // oder jo.Order.Count, je nachdem was du willst

                                if (jo.Klass != null && jo.Klass.Methods.TryGetValue(prop, out var mfn))
                                    return mfn;
                            }
                            return null;
                        }

                        // CLR object
                        if (recv != null)
                        {
                            var t = recv.GetType();

                            // arrays: expose Length
                            if (recv is Array arr && prop == "Length") return (double)arr.Length;
                            if (recv is IList list && prop == "Count") return (double)list.Count;

                            var p = GetMostDerivedProperty(t, prop, isStatic: false);
                            if (p != null && p.GetMethod != null) return p.GetValue(recv);

                            var f = GetMostDerivedField(t, prop, isStatic: false);
                            if (f != null) return f.GetValue(recv);

                            var ev = GetMostDerivedEvent(t, prop, isStatic: false);
                            if (ev != null) return null;

                            var ms = GetAllMethods(t, prop, isStatic: false);
                            if (ms.Length > 0) return new ClrCallable(recv, prop);

                            return null;
                        }

                        throw new Exception("TypeError: member access on null");
                    }

                case NodeType.Index:
                    {
                        object? recv = Eval(n.Kids[0]!, env);
                        object? idx = Eval(n.Kids[1]!, env);

                        if (recv is JsArray ja)
                        {
                            long i = (long)Rt.ToNumber(idx);
                            lock (ja)
                            {
                                if (i < 0 || i >= ja.Items.Count) return null;
                                return ja.Items[(int)i];
                            }
                        }

                        if (recv is JsObject jo)
                        {
                            string key = Rt.ToJsString(idx);
                            lock (jo)
                            {
                                if (jo.Props.TryGetValue(key, out var v)) return v;
                                return null;
                            }
                        }

                        if (recv is Array arr)
                        {
                            int i = (int)Rt.ToNumber(idx);
                            if (i < 0 || i >= arr.Length) return null;
                            return arr.GetValue(i);
                        }

                        if (recv is IList list)
                        {
                            int i = (int)Rt.ToNumber(idx);
                            if (i < 0 || i >= list.Count) return null;
                            return list[i];
                        }

                        if (recv is IDictionary dict)
                        {
                            return dict.Contains(idx) ? dict[idx] : null;
                        }

                        throw new Exception("TypeError: index access on non-array/object");
                    }

                case NodeType.Call:
                    {
                        var calleeNode = n.Kids[0]!;
                        var argsNode = n.Kids[1]!;

                        object? thisVal = null;
                        if (calleeNode.Type == NodeType.Member) thisVal = Eval(calleeNode.Kids[0]!, env);
                        else if (calleeNode.Type == NodeType.Index) thisVal = Eval(calleeNode.Kids[0]!, env);

                        object? fnv = Eval(calleeNode, env);

                        var args = new List<object?>();
                        foreach (var a in argsNode.Kids) args.Add(Eval(a!, env));

                        if (fnv is Function fn)
                            return CallFunction(fn, args, thisVal);

                        if (fnv is Delegate del)
                            return del.DynamicInvoke(args.ToArray());

                        if (fnv is ClrCallable cc)
                            return InvokeClrMethod(cc.Target, cc.Name, args);

                        throw new Exception("TypeError: call of non-function");
                    }

                case NodeType.NewExpr:
                    {
                        // 1) if identifier resolves to script class or Type, use that
                        object? sym = null;
                        bool symExists = false;
                        try { sym = env.Get(n.Tok.Lexeme); symExists = true; } catch { symExists = false; }

                        var args = new List<object?>();
                        foreach (var a in n.Kids[0]!.Kids) args.Add(Eval(a!, env));

                        if (symExists)
                        {
                            if (sym is ClassDef clsSym)
                                return NewScriptInstance(clsSym, args);

                            if (sym is Type typeSym)
                                return CreateClrInstance(typeSym, args);

                            // NEW: namespace alias support: new WinForms.Form()
                            if (sym is ClrNamespace nsSym)
                            {
                                // n.Text is like "WinForms.Form.SubType"
                                string prefix = n.Tok.Lexeme;            // "WinForms"
                                string suffix = "";

                                if (n.Text.Length > prefix.Length)
                                    suffix = n.Text.Substring(prefix.Length); // ".Form..."

                                string clrName = nsSym.Name + suffix;    // "System.Windows.Forms" + ".Form"
                                var _ty = ResolveClrType(clrName);
                                if (_ty != null) return CreateClrInstance(_ty, args);

                                throw new Exception($"TypeError: CLR type not found: {clrName}");
                            }
                        }

                        // 2) resolve by n.Text
                        string name = n.Text;
                        // script class by name
                        try
                        {
                            var v = env.Get(name);
                            if (v is ClassDef cls) return NewScriptInstance(cls, args);
                            if (v is Type ty2) return CreateClrInstance(ty2, args);
                        }
                        catch { }

                        // CLR type by name
                        var ty = ResolveClrType(name);
                        if (ty != null) return CreateClrInstance(ty, args);

                        throw new Exception($"TypeError: type/class not found: {name}");
                    }

                case NodeType.Assign:
                    {
                        var target = n.Kids[0]!;
                        object? rhs = Eval(n.Kids[1]!, env);

                        object? recv = null; object? idx = null; string prop = ""; int kind = -1;
                        object? oldVal = EvalLValueGet(target, env, ref recv, ref prop, ref idx, ref kind);

                        object? newVal = n.Tok.Type switch
                        {
                            TokType.ASSIGN => rhs,
                            TokType.PLUS_ASSIGN => BinaryPlus(oldVal, rhs),
                            TokType.MINUS_ASSIGN => Rt.ToNumber(oldVal) - Rt.ToNumber(rhs),
                            TokType.MUL_ASSIGN => Rt.ToNumber(oldVal) * Rt.ToNumber(rhs),
                            TokType.DIV_ASSIGN => Rt.ToNumber(oldVal) / Rt.ToNumber(rhs),
                            TokType.MOD_ASSIGN => Rt.ToNumber(oldVal) % Rt.ToNumber(rhs),
                            _ => throw new Exception("Unknown assignment operator")
                        };

                        EvalLValueSet(target, env, recv, prop, idx, kind, newVal);
                        return newVal;
                    }

                case NodeType.TaskExpr:
                    {
                        // task <unary>  OR task { ... }
                        var expr = n.Kids[0]!;
                        var t = _taskMgr.Enqueue(() =>
                        {
                            try
                            {
                                // run in same interpreter, shared env (thread-safe Env)
                                if (expr.Type == NodeType.TaskBlock)
                                {
                                    var benv = new Env(env);
                                    object? last = null;
                                    foreach (var st in expr.Kids) last = Exec(st!, benv);
                                    return last;
                                }
                                return Eval(expr, env);
                            }
                            catch (ReturnSignal rs)
                            {
                                return rs.Value;
                            }
                        });

                        return new JsTask(t);
                    }

                case NodeType.AwaitExpr:
                    {
                        var v = Eval(n.Kids[0]!, env);

                        if (v is JsTask jt) return jt.Wait();

                        if (v is Task task)
                        {
                            task.GetAwaiter().GetResult();
                            var ttype = task.GetType();
                            if (ttype.IsGenericType && ttype.GetGenericTypeDefinition() == typeof(Task<>))
                            {
                                var propRes = ttype.GetProperty("Result");
                                return propRes?.GetValue(task);
                            }
                            return null;
                        }

                        return v;
                    }

                default:
                    throw new Exception("eval(): unexpected node type");
            }
        }

        private object? NewScriptInstance(ClassDef cls, List<object?> args)
        {
            var obj = new JsObject { Klass = cls };

            // init fields (declare first)
            lock (obj)
            {
                foreach (var f in cls.Fields)
                {
                    if (!obj.Props.ContainsKey(f.name)) obj.Order.Add(f.name);
                    obj.Props[f.name] = null;
                }
            }

            // run initializers in class closure
            if (cls.Fields.Count > 0)
            {
                var initEnv = new Env(cls.Closure);
                initEnv.Declare("this", obj);

                lock (obj)
                {
                    foreach (var f in cls.Fields)
                    {
                        object? fv = null;
                        if (f.initExpr != null) fv = Eval(f.initExpr, initEnv);
                        obj.Props[f.name] = fv;
                    }
                }
            }

            // call constructor
            if (cls.Methods.TryGetValue("constructor", out var ctor))
                CallFunction(ctor, args, obj);

            return obj;
        }

        public object? Exec(Node n, Env env)
        {
            if (n == null) return null;

            switch (n.Type)
            {
                case NodeType.ImportStmt:
                    {
                        // import X.Y as Alias;
                        string full = n.Text;
                        Type? ty = ResolveClrType(full);
                        if (ty != null) env.Declare(n.Tok.Lexeme, ty);
                        else env.Declare(n.Tok.Lexeme, new ClrNamespace(full));
                        return null;
                    }

                case NodeType.TaskStmt:
                    {
                        // schedule and ignore
                        _ = Eval(new Node(NodeType.TaskExpr, n.Tok) { Kids = { n.Kids[0] } }, env);
                        return null;
                    }

                case NodeType.YieldStmt:
                    {
                        Thread.Sleep(1);
                        return null;
                    }

                case NodeType.LockStmt:
                    {
                        var keyObj = Eval(n.Kids[0]!, env);

                        object lockObj;
                        if (keyObj == null)
                            throw new Exception("TypeError: lock(expr) expr evaluated to null");

                        if (keyObj is string s)
                        {
                            lock (_namedLocksGuard)
                            {
                                if (!_namedLocks.TryGetValue(s, out lockObj!))
                                {
                                    lockObj = new object();
                                    _namedLocks[s] = lockObj;
                                }
                            }
                        }
                        else if (keyObj.GetType().IsValueType)
                        {
                            string k = "val:" + Rt.ToJsString(keyObj);
                            lock (_namedLocksGuard)
                            {
                                if (!_namedLocks.TryGetValue(k, out lockObj!))
                                {
                                    lockObj = new object();
                                    _namedLocks[k] = lockObj;
                                }
                            }
                        }
                        else
                        {
                            lockObj = keyObj;
                        }

                        lock (lockObj)
                        {
                            return Exec(n.Kids[1]!, env);
                        }
                    }

                case NodeType.AwaitStmt:
                    {
                        var v = Eval(n.Kids[0]!, env);
                        if (v is JsTask jt) { jt.Wait(); return null; }
                        if (v is Task task) { task.GetAwaiter().GetResult(); return null; }
                        return null;
                    }

                case NodeType.LetDecl:
                    {
                        object? v = Eval(n.Kids[0]!, env);
                        env.Declare(n.Tok.Lexeme, v);
                        return v;
                    }

                case NodeType.FunctionDecl:
                    {
                        var fn = new Function { Closure = env, Body = n.Kids[1]! };
                        foreach (var p in n.Kids[0]!.Kids) fn.Params.Add(p!.Tok.Lexeme);
                        env.Declare(n.Tok.Lexeme, fn);
                        return fn;
                    }

                case NodeType.ClassDecl:
                    {
                        var cls = new ClassDef { Name = n.Tok.Lexeme, Closure = env };

                        foreach (var child0 in n.Kids)
                        {
                            var child = child0;
                            if (child == null) continue;

                            if (child.Type == NodeType.MethodDecl)
                            {
                                var fn = new Function { Closure = env, Body = child.Kids[1]! };
                                foreach (var p in child.Kids[0]!.Kids) fn.Params.Add(p!.Tok.Lexeme);
                                cls.Methods[child.Tok.Lexeme] = fn;
                            }
                            else if (child.Type == NodeType.FieldDecl)
                            {
                                Node? initExpr = (child.Kids.Count > 0) ? child.Kids[0] : null;
                                cls.Fields.Add((child.Tok.Lexeme, initExpr));
                            }
                            else
                            {
                                throw new Exception("Internal: unexpected child node in class body");
                            }
                        }

                        env.Declare(n.Tok.Lexeme, cls);
                        return cls;
                    }

                case NodeType.ExprStmt:
                    return Eval(n.Kids[0]!, env);

                case NodeType.ReturnStmt:
                    {
                        object? v = Eval(n.Kids[0]!, env);
                        throw new ReturnSignal(v);
                    }

                case NodeType.BreakStmt:
                    throw new BreakSignal();

                case NodeType.ContinueStmt:
                    throw new ContinueSignal();

                case NodeType.IfStmt:
                    {
                        object? cond = Eval(n.Kids[0]!, env);
                        if (Rt.IsTruthy(cond)) return Exec(n.Kids[1]!, env);
                        return Exec(n.Kids[2]!, env);
                    }

                case NodeType.WhileStmt:
                    {
                        while (Rt.IsTruthy(Eval(n.Kids[0]!, env)))
                        {
                            try
                            {
                                Exec(n.Kids[1]!, env);
                            }
                            catch (ContinueSignal) { }
                            catch (BreakSignal) { break; }
                        }
                        return null;
                    }

                case NodeType.ForStmt:
                    {
                        var loopEnv = new Env(env);

                        var init = n.Kids[0];
                        var cond = n.Kids[1];
                        var post = n.Kids[2];
                        var body = n.Kids[3]!;

                        if (init != null)
                        {
                            if (init.Type == NodeType.LetDecl) Exec(init, loopEnv);
                            else Eval(init, loopEnv);
                        }

                        while (true)
                        {
                            if (cond != null)
                                if (!Rt.IsTruthy(Eval(cond, loopEnv))) break;

                            try
                            {
                                Exec(body, loopEnv);
                            }
                            catch (ContinueSignal) { }
                            catch (BreakSignal) { break; }

                            if (post != null) Eval(post, loopEnv);
                        }

                        return null;
                    }

                case NodeType.ForeachStmt:
                    {
                        var v1 = n.Kids[0]!;
                        var v2 = n.Kids[1];
                        var iterableNode = n.Kids[2]!;
                        var body = n.Kids[3]!;

                        object? itv = Eval(iterableNode, env);

                        var loopEnv = new Env(env);
                        string name1 = v1.Tok.Lexeme;
                        string name2 = v2 != null ? v2.Tok.Lexeme : "";

                        loopEnv.Declare(name1, null);
                        if (v2 != null) loopEnv.Declare(name2, null);

                        // script array
                        if (itv is JsArray ja)
                        {
                            List<object?> snap;
                            lock (ja) snap = ja.Items.ToList();

                            for (int i = 0; i < snap.Count; i++)
                            {
                                if (v2 != null)
                                {
                                    loopEnv.Set(name1, (double)i);
                                    loopEnv.Set(name2, snap[i]);
                                }
                                else
                                {
                                    loopEnv.Set(name1, snap[i]);
                                }

                                try { Exec(body, loopEnv); }
                                catch (ContinueSignal) { continue; }
                                catch (BreakSignal) { break; }
                            }
                            return null;
                        }

                        // script object
                        if (itv is JsObject jo)
                        {
                            List<string> keys;
                            Dictionary<string, object?> propsSnap;
                            lock (jo)
                            {
                                keys = (jo.Order.Count > 0 ? jo.Order : jo.Props.Keys.ToList()).ToList();
                                propsSnap = new Dictionary<string, object?>(jo.Props);
                            }

                            foreach (var k in keys)
                            {
                                if (!propsSnap.TryGetValue(k, out var vv)) continue;

                                if (v2 != null)
                                {
                                    loopEnv.Set(name1, k);
                                    loopEnv.Set(name2, vv);
                                }
                                else
                                {
                                    loopEnv.Set(name1, vv);
                                }

                                try { Exec(body, loopEnv); }
                                catch (ContinueSignal) { continue; }
                                catch (BreakSignal) { break; }
                            }
                            return null;
                        }

                        // CLR IEnumerable
                        if (itv is IEnumerable en)
                        {
                            int idx = 0;
                            foreach (var item in en)
                            {
                                if (v2 != null)
                                {
                                    loopEnv.Set(name1, (double)idx);
                                    loopEnv.Set(name2, item);
                                }
                                else
                                {
                                    loopEnv.Set(name1, item);
                                }

                                try { Exec(body, loopEnv); }
                                catch (ContinueSignal) { idx++; continue; }
                                catch (BreakSignal) { break; }

                                idx++;
                            }
                            return null;
                        }

                        throw new Exception("TypeError: foreach on non-array/object/enumerable");
                    }

                case NodeType.Block:
                    return Eval(n, env);

                case NodeType.Program:
                    return Eval(n, env);

                default:
                    return Eval(n, env);
            }
        }
    }

    static class Program
    {
        static string ReadFile(string path) => File.ReadAllText(path);

        [STAThread]
        static void Main(string[] args)
        {
            try
            {
                try
                {
                    Application.EnableVisualStyles();
                    Application.SetCompatibleTextRenderingDefault(false);
                }
                catch { }

                string code;

                if (args.Length >= 1)
                    code = ReadFile(args[0]);
                else
                    code = "print(\"MiniJs ready\");\n";

                var lx = new Lexer(code);
                var ps = new Parser(lx);
                var ast = ps.ParseProgram();

                // Debug AST (optional)
                //AstDump.Dump(ast);

                var it = new Interpreter();
                it.Eval(ast, it.Global);
            }
            catch (Exception e)
            {
                Exception ex = e;

                if (ex is TargetInvocationException tie && tie.InnerException != null)
                    ex = tie.InnerException;

                if (ex is AggregateException ae && ae.InnerExceptions.Count > 0)
                    ex = ae.InnerExceptions[0];

                Console.Error.WriteLine(ex.Message);
                Console.Error.WriteLine(ex.StackTrace);
                Environment.Exit(1);
            }
        }
    }
}
