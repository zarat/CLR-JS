// Program.cs - tiny JavaScript-like interpreter (subset, JS-like-ish)
//
// Added:
// - CLR interop via Reflection (namespace/type/method/property/field/indexer/ctor)
// - import ... as ...; for CLR namespaces/types
// - generic CLR event handling: obj.SomeEvent = function(sender, e){...}
// - overload resolution now supports:
//    * optional parameters
//    * params (ParamArray) like DataGridViewRowCollection.Add(params object[])
//
// Build (WinForms):
//   <TargetFramework>net8.0-windows</TargetFramework>
//   <UseWindowsForms>true</UseWindowsForms>

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

using System.Windows.Forms; // only if you target net*-windows + UseWindowsForms

namespace MiniJs
{
    enum TokType
    {
        EOF_TOK,

        // literals/ident
        IDENT, NUMBER, STRING,
        TRUE_TOK, FALSE_TOK, NULL_TOK,

        // keywords
        LET, VAR, FUNCTION, CLASS, NEW, THIS, RETURN, IF, ELSE,
        WHILE, FOR, FOREACH, IN, BREAK, CONTINUE,
        IMPORT, AS,

        // punctuation
        LPAREN, RPAREN,
        LBRACE, RBRACE,
        LBRACK, RBRACK,
        COMMA, SEMI, DOT, COLON,

        // operators
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

                // // comment
                if (c == '/' && Peek() == '/')
                {
                    while (!AtEnd && Cur != '\n') Advance();
                    continue;
                }

                // /* comment */
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

            // identifiers / keywords
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
                    "true" => new Token(TokType.TRUE_TOK, s, pos),
                    "false" => new Token(TokType.FALSE_TOK, s, pos),
                    "null" => new Token(TokType.NULL_TOK, s, pos),
                    _ => new Token(TokType.IDENT, s, pos)
                };
            }

            // numbers
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

            // strings "..."
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

            // multi-char ops (order matters)
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

            // single-char
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

        ExprStmt,

        Assign, Binary, Unary, Postfix,
        Var, Literal,

        ArrayLit, ObjectLit, FunctionExpr,
        Member, Index, Call, NewExpr
    }

    sealed class Node
    {
        public NodeType Type;
        public Token Tok;
        public string Text = ""; // used for NewExpr/ImportStmt: full dotted name
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

            // dotted name: IDENT ('.' IDENT)*
            Token first = Consume(TokType.IDENT, "import name");
            var full = new StringBuilder(first.Lexeme);
            while (Match(TokType.DOT))
            {
                Token part = Consume(TokType.IDENT, "import name part");
                full.Append('.').Append(part.Lexeme);
            }

            // optional alias
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
            if (_cur.Type == TokType.SEMI)
            {
                Consume(TokType.SEMI, "';'");
            }
            else
            {
                init = (_cur.Type == TokType.LET || _cur.Type == TokType.VAR) ? LetDecl(withSemi: false) : Expression();
                Consume(TokType.SEMI, "';'");
            }

            Node? cond = null;
            if (_cur.Type == TokType.SEMI)
            {
                Consume(TokType.SEMI, "';'");
            }
            else
            {
                cond = Expression();
                Consume(TokType.SEMI, "';'");
            }

            Node? post = null;
            if (_cur.Type == TokType.RPAREN)
            {
                Consume(TokType.RPAREN, "')'");
            }
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
                // FIELD: var x; or var x = expr;
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

                // METHOD
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

        // expression := assignment
        private Node Expression() => Assignment();

        // assignment := logical_or ( ( '=' | '+=', ... ) assignment )?
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
                n.Kids.Add(Assignment()); // right-assoc
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

        // right-associative **
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

        // postfix := primary ( '.' IDENT | '[' expr ']' | '(' args ')' )* ( '++' | '--' )?
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

            // new TypeName(...)
            if (Match(TokType.NEW))
            {
                // dotted type name: IDENT ('.' IDENT)*
                Token first = Consume(TokType.IDENT, "type name after new");
                var full = new StringBuilder(first.Lexeme);
                while (Match(TokType.DOT))
                {
                    Token part = Consume(TokType.IDENT, "type name part");
                    full.Append('.').Append(part.Lexeme);
                }

                Consume(TokType.LPAREN, "'(' after new Type");
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

            // array literal
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

            // object literal: {a: expr, "b": expr}
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

            // function expression: function(a,b){...} or function name(a,b){...}
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

    // -------- Runtime --------

    sealed class JsArray { public List<object?> Items = new(); }

    sealed class JsObject
    {
        public Dictionary<string, object?> Props = new();
        public List<string> Order = new();
        public ClassDef? Klass;
    }

    sealed class Env
    {
        public Env? Parent;
        public Dictionary<string, object?> Vars = new();

        public Env(Env? p = null) { Parent = p; }

        public object? Get(string k)
        {
            if (Vars.TryGetValue(k, out var v)) return v;
            if (Parent != null) return Parent.Get(k);
            throw new Exception("ReferenceError: " + k + " is not defined");
        }

        // sloppy-set: if exists up chain -> set there, else set in global root
        public void Set(string k, object? v)
        {
            if (Vars.ContainsKey(k)) { Vars[k] = v; return; }
            if (Parent != null) { Parent.Set(k, v); return; }
            Vars[k] = v;
        }

        public void Declare(string k, object? v) => Vars[k] = v;
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

    // CLR bridge: namespace prefix like "System" or "System.Collections"
    sealed class ClrNamespace
    {
        public string Name;
        public ClrNamespace(string n) { Name = n; }
        public override string ToString() => $"[namespace {Name}]";
    }

    // CLR bridge: bound method group (instance or static)
    sealed class ClrCallable
    {
        public object? Target; // instance or Type for static
        public string Name;
        public ClrCallable(object? target, string name) { Target = target; Name = name; }
        public override string ToString() => "[clr-callable]";
    }

    sealed class ReturnSignal : Exception { public object? Value; public ReturnSignal(object? v) { Value = v; } }
    sealed class BreakSignal : Exception { }
    sealed class ContinueSignal : Exception { }

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

            if (v is JsArray a)
                return "[" + string.Join(", ", a.Items.Select(ToJsString)) + "]";

            if (v is JsObject o)
            {
                IEnumerable<string> keys = o.Order.Count > 0 ? o.Order : o.Props.Keys;
                var parts = new List<string>();
                foreach (var k in keys)
                {
                    if (!o.Props.TryGetValue(k, out var vv)) continue;
                    parts.Add(k + ": " + ToJsString(vv));
                }
                return "{" + string.Join(", ", parts) + "}";
            }

            if (v is Function) return "[function]";
            if (v is ClassDef) return "[class]";
            if (v is ClrNamespace ns) return ns.ToString();
            if (v is Type t) return $"[type {t.FullName}]";
            if (v is ClrCallable) return "[clr-callable]";

            return v.ToString() ?? "";
        }

        public static double ToNumber(object? v)
        {
            try
            {
                return v switch
                {
                    null => 0.0,
                    double d => d,
                    float f => f,
                    int i => i,
                    long l => l,
                    bool b => b ? 1.0 : 0.0,
                    string s => string.IsNullOrEmpty(s) ? 0.0 : double.Parse(s, CultureInfo.InvariantCulture),
                    _ => double.Parse(ToJsString(v), CultureInfo.InvariantCulture)
                };
            }
            catch
            {
                throw;
            }
        }

        // JS-like ToInt32
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

    readonly struct EventKey
    {
        public readonly object Target; // reference identity (instance or Type)
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

        // event subscriptions installed from script (so we can replace/remove on reassign)
        private readonly Dictionary<EventKey, List<Delegate>> _eventSubs = new(new EventKeyComparer());

        public Interpreter()
        {
            Global = new Env();

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

            // CLR root namespace
            Global.Declare("System", new ClrNamespace("System"));
        }

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

        private object? BinaryPlus(object? l, object? r)
        {
            if (l is string || r is string)
                return Rt.ToJsString(l) + Rt.ToJsString(r);
            return Rt.ToNumber(l) + Rt.ToNumber(r);
        }

        private static bool EqualsForRuntime(object? a, object? b)
        {
            if (a is null && b is null) return true;
            if (a is null || b is null) return false;

            if (a.GetType() != b.GetType()) return false;

            return a switch
            {
                double da when b is double db => da == db,
                bool ba when b is bool bb => ba == bb,
                string sa when b is string sb => sa == sb,
                JsObject oa when b is JsObject ob => ReferenceEquals(oa, ob),
                JsArray aa when b is JsArray ab => ReferenceEquals(aa, ab),
                Function fa when b is Function fb => ReferenceEquals(fa, fb),
                ClassDef ca when b is ClassDef cb => ReferenceEquals(ca, cb),
                Type ta when b is Type tb => ReferenceEquals(ta, tb),
                _ => a.Equals(b)
            };
        }

        // ---------------- CLR reflection helpers ----------------

        private static int InheritanceDistance(Type start, Type? declaring)
        {
            int d = 0;
            var cur = start;
            while (cur != null)
            {
                if (cur == declaring) return d;
                cur = cur.BaseType!;
                d++;
            }
            return 9999;
        }

        private static PropertyInfo? FindBestProperty(Type t, string name, BindingFlags flags)
        {
            var props = t.GetProperties(flags)
                .Where(p => p.Name == name && p.GetIndexParameters().Length == 0)
                .ToArray();

            if (props.Length == 0) return null;

            // pick most-derived (smallest distance)
            return props
                .OrderBy(p => InheritanceDistance(t, p.DeclaringType))
                .First();
        }

        private static FieldInfo? FindBestField(Type t, string name, BindingFlags flags)
        {
            // Fields can also be hidden; do same approach for robustness
            var fields = t.GetFields(flags).Where(f => f.Name == name).ToArray();
            if (fields.Length == 0) return null;

            return fields
                .OrderBy(f => InheritanceDistance(t, f.DeclaringType))
                .First();
        }

        private static EventInfo? FindBestEvent(Type t, string name, BindingFlags flags)
        {
            var evs = t.GetEvents(flags).Where(e => e.Name == name).ToArray();
            if (evs.Length == 0) return null;

            return evs
                .OrderBy(e => InheritanceDistance(t, e.DeclaringType))
                .First();
        }


        private static Type? ResolveClrType(string fullName)
        {
            static Type? FindType(string name)
            {
                var t0 = Type.GetType(name, throwOnError: false, ignoreCase: false);
                if (t0 != null) return t0;

                foreach (var asm in AppDomain.CurrentDomain.GetAssemblies())
                {
                    try
                    {
                        var t = asm.GetType(name, throwOnError: false, ignoreCase: false);
                        if (t != null) return t;
                    }
                    catch { }
                }
                return null;
            }

            // aliases (optional safety)
            fullName = fullName switch
            {
                "System.Collections.Generic.ArrayList" => "System.Collections.ArrayList",
                _ => fullName
            };

            var t1 = FindType(fullName);
            if (t1 != null) return t1;

            // generic fallback: Foo -> Foo`1<object>, Foo`2<object,object>, etc.
            for (int arity = 1; arity <= 4; arity++)
            {
                var open = FindType(fullName + "`" + arity);
                if (open != null && open.IsGenericTypeDefinition)
                {
                    var args = Enumerable.Repeat(typeof(object), arity).ToArray();
                    return open.MakeGenericType(args);
                }
            }

            return null;
        }

        private static bool IsNullableOrRef(Type t) => !t.IsValueType || Nullable.GetUnderlyingType(t) != null;

        private static bool IsNumericType(Type t)
        {
            t = Nullable.GetUnderlyingType(t) ?? t;
            return t == typeof(byte) || t == typeof(sbyte) ||
                   t == typeof(short) || t == typeof(ushort) ||
                   t == typeof(int) || t == typeof(uint) ||
                   t == typeof(long) || t == typeof(ulong) ||
                   t == typeof(float) || t == typeof(double) ||
                   t == typeof(decimal);
        }

        private static object? ConvertArg(object? arg, Type targetType)
        {
            if (arg == null)
            {
                if (!IsNullableOrRef(targetType))
                    throw new Exception($"TypeError: cannot pass null to {targetType.Name}");
                return null;
            }

            var nn = Nullable.GetUnderlyingType(targetType) ?? targetType;

            if (nn == typeof(object)) return arg;
            if (nn.IsInstanceOfType(arg)) return arg;

            if (arg is double d)
            {
                if (nn == typeof(double)) return d;
                if (nn == typeof(float)) return (float)d;
                if (nn == typeof(decimal)) return (decimal)d;
                if (nn == typeof(int)) return (int)d;
                if (nn == typeof(long)) return (long)d;
                if (nn == typeof(short)) return (short)d;
                if (nn == typeof(byte)) return (byte)d;
                if (nn == typeof(uint)) return (uint)d;
                if (nn == typeof(ulong)) return (ulong)d;
                if (nn == typeof(bool)) return d != 0.0;
            }

            if (nn == typeof(string)) return Rt.ToJsString(arg);

            if (nn.IsEnum)
            {
                if (arg is string es) return Enum.Parse(nn, es, ignoreCase: true);
                if (arg is double ed) return Enum.ToObject(nn, (int)ed);
            }

            try
            {
                return Convert.ChangeType(arg, nn, CultureInfo.InvariantCulture);
            }
            catch
            {
                if (arg is string s && IsNumericType(nn))
                {
                    if (nn == typeof(double)) return double.Parse(s, CultureInfo.InvariantCulture);
                    if (nn == typeof(int)) return int.Parse(s, CultureInfo.InvariantCulture);
                    if (nn == typeof(long)) return long.Parse(s, CultureInfo.InvariantCulture);
                }
                throw new Exception($"TypeError: cannot convert '{Rt.ToJsString(arg)}' to {targetType.Name}");
            }
        }

        private static int ScoreArg(object? arg, Type paramType)
        {
            if (arg == null) return IsNullableOrRef(paramType) ? 2 : int.MaxValue;

            var nn = Nullable.GetUnderlyingType(paramType) ?? paramType;
            if (nn.IsInstanceOfType(arg)) return 0;

            if (arg is double && IsNumericType(nn)) return 3;
            if (arg is string && nn == typeof(string)) return 0;

            try { ConvertArg(arg, paramType); return 6; }
            catch { return int.MaxValue; }
        }

        private static bool HasParamArray(ParameterInfo[] ps) =>
            ps.Length > 0 && ps[^1].IsDefined(typeof(ParamArrayAttribute), inherit: false);

        private static object?[] PrepareInvokeArgs(ParameterInfo[] ps, IList<object?> args)
        {
            bool hasParams = HasParamArray(ps);

            // optional params (no param-array)
            if (!hasParams)
            {
                if (args.Count > ps.Length) throw new Exception("TypeError: too many arguments");

                var conv = new object?[ps.Length];

                // provided args
                for (int i = 0; i < args.Count; i++)
                    conv[i] = ConvertArg(args[i], ps[i].ParameterType);

                // fill missing optional args
                for (int i = args.Count; i < ps.Length; i++)
                {
                    if (!ps[i].IsOptional)
                        throw new Exception("TypeError: not enough arguments");

                    // Let reflection apply default value
                    conv[i] = Type.Missing;
                }

                return conv;
            }

            // params array case: pack remaining arguments into last array parameter
            int fixedCount = ps.Length - 1;
            if (args.Count < fixedCount) throw new Exception("TypeError: not enough arguments");

            var res = new object?[ps.Length];

            for (int i = 0; i < fixedCount; i++)
                res[i] = ConvertArg(args[i], ps[i].ParameterType);

            var arrParamType = ps[^1].ParameterType;
            var elemType = arrParamType.GetElementType() ?? typeof(object);

            // If caller already passed an array as the last arg AND counts match, accept it directly
            if (args.Count == ps.Length && args[^1] != null && arrParamType.IsInstanceOfType(args[^1]))
            {
                res[^1] = args[^1];
                return res;
            }

            int varCount = args.Count - fixedCount;
            Array packed = Array.CreateInstance(elemType, varCount);

            for (int j = 0; j < varCount; j++)
                packed.SetValue(ConvertArg(args[fixedCount + j], elemType), j);

            res[^1] = packed;
            return res;
        }

        private static MethodInfo SelectBestMethod(IEnumerable<MethodInfo> methods, IList<object?> args)
        {
            MethodInfo? best = null;
            int bestScore = int.MaxValue;

            foreach (var m in methods)
            {
                var ps = m.GetParameters();
                bool hasParams = HasParamArray(ps);

                if (!hasParams)
                {
                    if (args.Count > ps.Length) continue;

                    // missing must be optional
                    bool ok = true;
                    for (int i = args.Count; i < ps.Length; i++)
                        if (!ps[i].IsOptional) { ok = false; break; }
                    if (!ok) continue;

                    int score = 0;
                    for (int i = 0; i < args.Count; i++)
                    {
                        int s = ScoreArg(args[i], ps[i].ParameterType);
                        if (s == int.MaxValue) { ok = false; break; }
                        score += s;
                    }
                    if (!ok) continue;

                    // small penalty for each optional param not supplied
                    score += (ps.Length - args.Count) * 5;

                    if (score < bestScore) { bestScore = score; best = m; }
                }
                else
                {
                    int fixedCount = ps.Length - 1;
                    if (args.Count < fixedCount) continue;

                    bool ok = true;
                    int score = 0;

                    // fixed part
                    for (int i = 0; i < fixedCount; i++)
                    {
                        int s = ScoreArg(args[i], ps[i].ParameterType);
                        if (s == int.MaxValue) { ok = false; break; }
                        score += s;
                    }
                    if (!ok) continue;

                    // var part against element type
                    var elemType = ps[^1].ParameterType.GetElementType() ?? typeof(object);
                    for (int j = fixedCount; j < args.Count; j++)
                    {
                        int s = ScoreArg(args[j], elemType);
                        if (s == int.MaxValue) { ok = false; break; }
                        score += s + 1; // tiny penalty per packed element
                    }
                    if (!ok) continue;

                    if (score < bestScore) { bestScore = score; best = m; }
                }
            }

            if (best == null) throw new Exception("TypeError: no matching overload");
            return best;
        }

        private static ConstructorInfo SelectBestCtor(IEnumerable<ConstructorInfo> ctors, IList<object?> args)
        {
            ConstructorInfo? best = null;
            int bestScore = int.MaxValue;

            foreach (var c in ctors)
            {
                var ps = c.GetParameters();
                bool hasParams = HasParamArray(ps);

                if (!hasParams)
                {
                    if (args.Count > ps.Length) continue;

                    bool ok = true;
                    for (int i = args.Count; i < ps.Length; i++)
                        if (!ps[i].IsOptional) { ok = false; break; }
                    if (!ok) continue;

                    int score = 0;
                    for (int i = 0; i < args.Count; i++)
                    {
                        int s = ScoreArg(args[i], ps[i].ParameterType);
                        if (s == int.MaxValue) { ok = false; break; }
                        score += s;
                    }
                    if (!ok) continue;

                    score += (ps.Length - args.Count) * 5;

                    if (score < bestScore) { bestScore = score; best = c; }
                }
                else
                {
                    int fixedCount = ps.Length - 1;
                    if (args.Count < fixedCount) continue;

                    bool ok = true;
                    int score = 0;

                    for (int i = 0; i < fixedCount; i++)
                    {
                        int s = ScoreArg(args[i], ps[i].ParameterType);
                        if (s == int.MaxValue) { ok = false; break; }
                        score += s;
                    }
                    if (!ok) continue;

                    var elemType = ps[^1].ParameterType.GetElementType() ?? typeof(object);
                    for (int j = fixedCount; j < args.Count; j++)
                    {
                        int s = ScoreArg(args[j], elemType);
                        if (s == int.MaxValue) { ok = false; break; }
                        score += s + 1;
                    }
                    if (!ok) continue;

                    if (score < bestScore) { bestScore = score; best = c; }
                }
            }

            if (best == null) throw new Exception("TypeError: no matching constructor");
            return best;
        }

        private static object? GetClrMember(object recvOrTypeOrNs, string name)
        {
            // namespace: append & maybe resolve to Type
            if (recvOrTypeOrNs is ClrNamespace ns)
            {
                string candidate = ns.Name + "." + name;
                var t = ResolveClrType(candidate);
                if (t != null) return t;
                return new ClrNamespace(candidate);
            }

            // static via Type
            if (recvOrTypeOrNs is Type st)
            {
                var flags = BindingFlags.Public | BindingFlags.Static;

                var evS = FindBestEvent(st, name, flags);
                if (evS != null) return evS; // optional: falls du Events auch "lesen" willst (meist nicht nötig)

                var p = FindBestProperty(st, name, flags);
                if (p != null) return p.GetValue(null);

                var f = FindBestField(st, name, flags);
                if (f != null) return f.GetValue(null);

                return null;
            }

            // instance
            var recv = recvOrTypeOrNs;
            var rt = recv.GetType();
            var iflags = BindingFlags.Public | BindingFlags.Instance;

            var ip = FindBestProperty(rt, name, iflags);
            if (ip != null) return ip.GetValue(recv);

            var iff = FindBestField(rt, name, iflags);
            if (iff != null) return iff.GetValue(recv);

            var ims = rt.GetMethods(iflags).Where(m => m.Name == name).ToArray();
            if (ims.Length > 0) return new ClrCallable(recv, name);

            return null;
        }

        // ---------- Generic event handling: obj.Event = function(...) {...} ----------

        private object? InvokeScriptForEvent(Function fn, object?[] args)
        {
            var list = new List<object?>(args.Length);
            for (int i = 0; i < args.Length; i++) list.Add(args[i]);

            object? thisVal = args.Length > 0 ? args[0] : null; // sender
            return CallFunction(fn, list, thisVal);
        }

        private static object? CoerceReturn(object? v, Type retType)
        {
            if (retType == typeof(void)) return null;

            if (v == null)
                return retType.IsValueType ? Activator.CreateInstance(retType) : null;

            if (retType.IsInstanceOfType(v)) return v;
            return ConvertArg(v, retType);
        }

        private Delegate MakeClrEventDelegate(Type delegateType, Function fn)
        {
            var invoke = delegateType.GetMethod("Invoke") ?? throw new Exception("TypeError: invalid event handler type");
            var ps = invoke.GetParameters();

            var paramExprs = ps.Select(p => Expression.Parameter(p.ParameterType, p.Name ?? "p")).ToArray();

            var argsArray = Expression.NewArrayInit(
                typeof(object),
                paramExprs.Select(p => Expression.Convert(p, typeof(object)))
            );

            var callMi = typeof(Interpreter).GetMethod(nameof(InvokeScriptForEvent), BindingFlags.Instance | BindingFlags.NonPublic)!;
            var call = Expression.Call(Expression.Constant(this), callMi, Expression.Constant(fn), argsArray);

            Expression body;
            if (invoke.ReturnType == typeof(void))
            {
                body = Expression.Block(call, Expression.Empty());
            }
            else
            {
                var coerceMi = typeof(Interpreter).GetMethod(nameof(CoerceReturn), BindingFlags.Static | BindingFlags.NonPublic)!;
                var coerced = Expression.Call(coerceMi, call, Expression.Constant(invoke.ReturnType, typeof(Type)));
                body = Expression.Convert(coerced, invoke.ReturnType);
            }

            return Expression.Lambda(delegateType, body, paramExprs).Compile();
        }

        private void SetClrEventHandler(object? instanceTarget, Type? staticTypeKey, EventInfo ev, object? value)
        {
            object keyTarget = staticTypeKey != null ? (object)staticTypeKey : (instanceTarget ?? throw new Exception("TypeError: event on null"));
            var key = new EventKey(keyTarget, ev.Name);

            // remove previous script handlers for this event
            if (_eventSubs.TryGetValue(key, out var oldList))
            {
                foreach (var d in oldList)
                    ev.RemoveEventHandler(instanceTarget, d);
                _eventSubs.Remove(key);
            }

            // assign null => clear
            if (value == null) return;

            if (value is Function fn)
            {
                var delType = ev.EventHandlerType ?? throw new Exception("TypeError: event has no handler type");
                var del = MakeClrEventDelegate(delType, fn);

                ev.AddEventHandler(instanceTarget, del);
                _eventSubs[key] = new List<Delegate> { del };
                return;
            }

            throw new Exception($"TypeError: event '{ev.Name}' expects a function");
        }

        private void SetClrMember(object recvOrType, string name, object? value)
        {
            if (recvOrType is Type st)
            {
                var flags = BindingFlags.Public | BindingFlags.Static;

                // events (static)
                var evS = st.GetEvent(name, flags);
                if (evS != null)
                {
                    SetClrEventHandler(null, st, evS, value);
                    return;
                }

                var p = st.GetProperty(name, flags);
                if (p != null)
                {
                    p.SetValue(null, ConvertArg(value, p.PropertyType));
                    return;
                }

                var f = st.GetField(name, flags);
                if (f != null)
                {
                    f.SetValue(null, ConvertArg(value, f.FieldType));
                    return;
                }

                throw new Exception($"TypeError: static member '{name}' not found or not settable");
            }

            var recv = recvOrType;
            var rt = recv.GetType();
            var flagsI = BindingFlags.Public | BindingFlags.Instance;

            // events (instance)
            var evI = rt.GetEvent(name, flagsI);
            if (evI != null)
            {
                SetClrEventHandler(recv, null, evI, value);
                return;
            }

            var ip = rt.GetProperty(name, flagsI);
            if (ip != null)
            {
                if (!ip.CanWrite) throw new Exception($"TypeError: property '{name}' is read-only");
                ip.SetValue(recv, ConvertArg(value, ip.PropertyType));
                return;
            }

            var iff = rt.GetField(name, flagsI);
            if (iff != null)
            {
                iff.SetValue(recv, ConvertArg(value, iff.FieldType));
                return;
            }

            throw new Exception($"TypeError: member '{name}' not found or not settable");
        }

        private static object? GetClrIndex(object recv, object? idx)
        {
            if (recv is Array arr)
            {
                int i = (int)Rt.ToNumber(idx);
                return arr.GetValue(i);
            }

            if (recv is IList list)
            {
                int i = (int)Rt.ToNumber(idx);
                return list[i];
            }

            if (recv is IDictionary dict)
            {
                var key = idx;
                if (key is double d) key = (int)d;
                if (key is null) key = "";
                return dict[key];
            }

            // default indexer Item[...]
            var t = recv.GetType();
            var props = t.GetDefaultMembers().OfType<PropertyInfo>().ToArray();
            foreach (var p in props)
            {
                var ps = p.GetIndexParameters();
                if (ps.Length == 1)
                {
                    var key = ConvertArg(idx, ps[0].ParameterType);
                    return p.GetValue(recv, new[] { key });
                }
            }

            throw new Exception("TypeError: index access on non-indexable CLR object");
        }

        private static void SetClrIndex(object recv, object? idx, object? val)
        {
            if (recv is Array arr)
            {
                int i = (int)Rt.ToNumber(idx);
                var et = arr.GetType().GetElementType() ?? typeof(object);
                arr.SetValue(ConvertArg(val, et), i);
                return;
            }

            if (recv is IList list)
            {
                int i = (int)Rt.ToNumber(idx);
                list[i] = val;
                return;
            }

            if (recv is IDictionary dict)
            {
                var key = idx;
                if (key is double d) key = (int)d;
                if (key is null) key = "";
                dict[key] = val;
                return;
            }

            // default indexer Item[...]
            var t = recv.GetType();
            var props = t.GetDefaultMembers().OfType<PropertyInfo>().ToArray();
            foreach (var p in props)
            {
                var ps = p.GetIndexParameters();
                if (ps.Length == 1 && p.CanWrite)
                {
                    var key = ConvertArg(idx, ps[0].ParameterType);
                    var vv = ConvertArg(val, p.PropertyType);
                    p.SetValue(recv, vv, new[] { key });
                    return;
                }
            }

            throw new Exception("TypeError: index assign on non-indexable CLR object");
        }

        private static object? InvokeClrCallable(ClrCallable c, List<object?> args)
        {
            if (c.Target is Type st)
            {
                var flags = BindingFlags.Public | BindingFlags.Static;
                var ms = st.GetMethods(flags).Where(m => m.Name == c.Name);
                var best = SelectBestMethod(ms, args);
                var conv = PrepareInvokeArgs(best.GetParameters(), args);
                return best.Invoke(null, conv);
            }
            else
            {
                var recv = c.Target ?? throw new Exception("TypeError: null target");
                var t = recv.GetType();
                var flags = BindingFlags.Public | BindingFlags.Instance;
                var ms = t.GetMethods(flags).Where(m => m.Name == c.Name);
                var best = SelectBestMethod(ms, args);
                var conv = PrepareInvokeArgs(best.GetParameters(), args);
                return best.Invoke(recv, conv);
            }
        }

        private static object CreateClrInstance(Type t, List<object?> args)
        {
            // optional: treat static classes as "Type handles"
            if (t.IsAbstract && t.IsSealed)
            {
                if (args.Count != 0)
                    throw new Exception($"TypeError: cannot construct static class '{t.FullName}' with arguments");
                return t;
            }

            if (t.IsAbstract || t.IsInterface)
                throw new Exception($"TypeError: cannot instantiate abstract/interface type '{t.FullName}'");

            var ctors = t.GetConstructors(BindingFlags.Public | BindingFlags.Instance);
            if (ctors.Length == 0)
            {
                if (args.Count == 0) return Activator.CreateInstance(t)!;
                throw new Exception("TypeError: type has no public constructors");
            }

            var best = SelectBestCtor(ctors, args);
            var conv = PrepareInvokeArgs(best.GetParameters(), args);
            return best.Invoke(conv);
        }

        // ---------------- LValue Get/Set (vars, jsobj, jsarr, clr) ----------------

        // outKind: 0=var, 1=member, 2=index
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
                    if (jo.Props.TryGetValue(outProp, out var v)) return v;
                    if (jo.Klass != null && jo.Klass.Methods.TryGetValue(outProp, out var mfn))
                        return mfn;
                    return null;
                }

                if (outRecv is null) throw new Exception("TypeError: member access on null");

                return GetClrMember(outRecv, outProp);
            }

            if (target.Type == NodeType.Index)
            {
                outKind = 2;
                outRecv = Eval(target.Kids[0]!, env);
                outIdx = Eval(target.Kids[1]!, env);

                if (outRecv is JsArray a)
                {
                    long i = (long)Rt.ToNumber(outIdx);
                    if (i < 0 || i >= a.Items.Count) return null;
                    return a.Items[(int)i];
                }

                if (outRecv is JsObject o)
                {
                    string key = Rt.ToJsString(outIdx);
                    if (o.Props.TryGetValue(key, out var v)) return v;
                    return null;
                }

                if (outRecv is null) throw new Exception("TypeError: index access on null");

                return GetClrIndex(outRecv, outIdx);
            }

            throw new Exception("Invalid assignment target");
        }

        private void EvalLValueSet(Node target, Env env, object? recv, string prop, object? idx, int kind, object? newVal)
        {
            if (kind == 0) { env.Set(prop, newVal); return; }

            if (kind == 1)
            {
                if (recv is JsObject o)
                {
                    if (!o.Props.ContainsKey(prop)) o.Order.Add(prop);
                    o.Props[prop] = newVal;
                    return;
                }

                if (recv is null) throw new Exception("TypeError: member assign on null");
                SetClrMember(recv, prop, newVal);
                return;
            }

            if (kind == 2)
            {
                if (recv is JsArray a)
                {
                    long i = (long)Rt.ToNumber(idx);
                    if (i < 0) throw new Exception("RangeError: negative index");
                    int ui = (int)i;
                    while (a.Items.Count <= ui) a.Items.Add(null);
                    a.Items[ui] = newVal;
                    return;
                }

                if (recv is JsObject o)
                {
                    string k = Rt.ToJsString(idx);
                    if (!o.Props.ContainsKey(k)) o.Order.Add(k);
                    o.Props[k] = newVal;
                    return;
                }

                if (recv is null) throw new Exception("TypeError: index assign on null");
                SetClrIndex(recv, idx, newVal);
                return;
            }
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
                        foreach (var k in n.Kids) a.Items.Add(Eval(k!, env));
                        return a;
                    }

                case NodeType.ObjectLit:
                    {
                        var o = new JsObject();
                        for (int i = 0; i + 1 < n.Kids.Count; i += 2)
                        {
                            var keyNode = n.Kids[i]!;
                            var valNode = n.Kids[i + 1]!;
                            string k = keyNode.Tok.Lexeme;
                            if (!o.Props.ContainsKey(k)) o.Order.Add(k);
                            o.Props[k] = Eval(valNode, env);
                        }
                        return o;
                    }

                case NodeType.FunctionExpr:
                    {
                        var fn = new Function { Closure = env, Body = n.Kids[1]! };
                        foreach (var p in n.Kids[0]!.Kids) fn.Params.Add(p!.Tok.Lexeme);
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
                            case TokType.BITNOT: return (double)(~Rt.ToInt32(r));

                            case TokType.INC:
                            case TokType.DEC:
                                {
                                    var target = n.Kids[0]!;
                                    object? recv = null; object? idx = null; string prop = ""; int kind = -1;
                                    object? oldVal = EvalLValueGet(target, env, ref recv, ref prop, ref idx, ref kind);
                                    double x = Rt.ToNumber(oldVal);
                                    double nx = (n.Tok.Type == TokType.INC) ? (x + 1.0) : (x - 1.0);
                                    object? newVal = nx;
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
                        object? newVal = nx;
                        EvalLValueSet(target, env, recv, prop, idx, kind, newVal);
                        return oldVal;
                    }

                case NodeType.Binary:
                    {
                        if (n.Tok.Type == TokType.AND)
                        {
                            object? l = Eval(n.Kids[0]!, env);
                            if (!Rt.IsTruthy(l)) return l;
                            return Eval(n.Kids[1]!, env);
                        }
                        if (n.Tok.Type == TokType.OR)
                        {
                            object? l = Eval(n.Kids[0]!, env);
                            if (Rt.IsTruthy(l)) return l;
                            return Eval(n.Kids[1]!, env);
                        }

                        object? l2 = Eval(n.Kids[0]!, env);
                        object? r2 = Eval(n.Kids[1]!, env);

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

                            case TokType.BITAND: return (double)(Rt.ToInt32(l2) & Rt.ToInt32(r2));
                            case TokType.BITOR: return (double)(Rt.ToInt32(l2) | Rt.ToInt32(r2));
                            case TokType.BITXOR: return (double)(Rt.ToInt32(l2) ^ Rt.ToInt32(r2));

                            case TokType.EQ: return EqualsForRuntime(l2, r2);
                            case TokType.NEQ: return !EqualsForRuntime(l2, r2);

                            default:
                                throw new Exception("Unknown binary op");
                        }
                    }

                case NodeType.Member:
                    {
                        object? recv = Eval(n.Kids[0]!, env);
                        string prop = n.Kids[1]!.Tok.Lexeme;

                        if (recv is JsArray a)
                        {
                            if (prop == "length") return (double)a.Items.Count;
                            return null;
                        }

                        if (recv is JsObject o)
                        {
                            if (o.Props.TryGetValue(prop, out var v)) return v;
                            if (o.Klass != null && o.Klass.Methods.TryGetValue(prop, out var mfn))
                                return mfn;
                            return null;
                        }

                        if (recv is null) throw new Exception("TypeError: member access on null");
                        return GetClrMember(recv, prop);
                    }

                case NodeType.Index:
                    {
                        object? recv = Eval(n.Kids[0]!, env);
                        object? idx = Eval(n.Kids[1]!, env);

                        if (recv is JsArray a)
                        {
                            long i = (long)Rt.ToNumber(idx);
                            if (i < 0 || i >= a.Items.Count) return null;
                            return a.Items[(int)i];
                        }

                        if (recv is JsObject o)
                        {
                            string key = Rt.ToJsString(idx);
                            if (o.Props.TryGetValue(key, out var v)) return v;
                            return null;
                        }

                        if (recv is null) throw new Exception("TypeError: index access on null");
                        return GetClrIndex(recv, idx);
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

                        if (fnv is ClrCallable cc)
                            return InvokeClrCallable(cc, args);

                        if (fnv is Delegate del)
                            return del.DynamicInvoke(args.ToArray());

                        throw new Exception("TypeError: call of non-function");
                    }

                case NodeType.NewExpr:
                    {
                        // 1) Script class preferred: new Test(...)
                        string firstIdent = n.Tok.Lexeme;
                        object? sym = null;
                        bool hasSym = true;
                        try { sym = env.Get(firstIdent); }
                        catch { hasSym = false; }

                        if (hasSym && sym is ClassDef sc)
                        {
                            var obj = new JsObject { Klass = sc };
                            object thisVal = obj;

                            if (sc.Fields.Count > 0)
                            {
                                foreach (var f in sc.Fields)
                                {
                                    if (!obj.Props.ContainsKey(f.name)) obj.Order.Add(f.name);
                                    obj.Props[f.name] = null;
                                }

                                var initEnv = new Env(sc.Closure);
                                initEnv.Declare("this", thisVal);

                                foreach (var f in sc.Fields)
                                {
                                    object? fv = null;
                                    if (f.initExpr != null) fv = Eval(f.initExpr, initEnv);
                                    obj.Props[f.name] = fv;
                                }
                            }

                            var sargs = new List<object?>();
                            foreach (var a in n.Kids[0]!.Kids) sargs.Add(Eval(a!, env));

                            if (sc.Methods.TryGetValue("constructor", out var ctor))
                                CallFunction(ctor, sargs, thisVal);

                            return obj;
                        }

                        // 2) CLR class: new System.X.Y.Type(...) OR new Alias.Type(...)
                        Type? t = null;

                        // Allow: let T = System.String; new T("x")
                        if (hasSym && sym is Type st)
                            t = st;

                        // Allow: import System.Windows.Forms as WinForms; new WinForms.Form()
                        if (t == null && hasSym && sym is ClrNamespace ns)
                        {
                            string full = n.Text; // e.g. WinForms.Form
                            if (full == firstIdent) full = ns.Name;
                            else if (full.StartsWith(firstIdent + ".", StringComparison.Ordinal))
                                full = ns.Name + full.Substring(firstIdent.Length);

                            t = ResolveClrType(full);
                        }

                        if (t == null) t = ResolveClrType(n.Text);
                        if (t == null) throw new Exception($"TypeError: CLR type not found: {n.Text}");

                        var args = new List<object?>();
                        foreach (var a in n.Kids[0]!.Kids) args.Add(Eval(a!, env));

                        return CreateClrInstance(t, args);
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

                default:
                    throw new Exception("eval(): unexpected node type");
            }
        }

        public object? Exec(Node n, Env env)
        {
            if (n == null) return null;

            switch (n.Type)
            {
                case NodeType.ImportStmt:
                    {
                        string alias = n.Tok.Lexeme;
                        string full = n.Text;

                        object? val = ResolveClrType(full);
                        if (val == null) val = new ClrNamespace(full);

                        env.Declare(alias, val);
                        return val;
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
                            try { Exec(n.Kids[1]!, env); }
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
                            {
                                if (!Rt.IsTruthy(Eval(cond, loopEnv))) break;
                            }

                            try { Exec(body, loopEnv); }
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

                        if (itv is JsArray a)
                        {
                            for (int i = 0; i < a.Items.Count; i++)
                            {
                                if (v2 != null)
                                {
                                    loopEnv.Set(name1, (double)i);
                                    loopEnv.Set(name2, a.Items[i]);
                                }
                                else loopEnv.Set(name1, a.Items[i]);

                                try { Exec(body, loopEnv); }
                                catch (ContinueSignal) { continue; }
                                catch (BreakSignal) { break; }
                            }
                            return null;
                        }

                        if (itv is JsObject o)
                        {
                            IEnumerable<string> keys = o.Order.Count > 0 ? o.Order : o.Props.Keys;
                            foreach (var k in keys)
                            {
                                if (!o.Props.TryGetValue(k, out var vv)) continue;

                                if (v2 != null)
                                {
                                    loopEnv.Set(name1, k);
                                    loopEnv.Set(name2, vv);
                                }
                                else loopEnv.Set(name1, vv);

                                try { Exec(body, loopEnv); }
                                catch (ContinueSignal) { continue; }
                                catch (BreakSignal) { break; }
                            }
                            return null;
                        }

                        if (itv is IEnumerable en)
                        {
                            int i = 0;
                            foreach (var item in en)
                            {
                                if (v2 != null)
                                {
                                    loopEnv.Set(name1, (double)i);
                                    loopEnv.Set(name2, item);
                                }
                                else loopEnv.Set(name1, item);

                                i++;

                                try { Exec(body, loopEnv); }
                                catch (ContinueSignal) { continue; }
                                catch (BreakSignal) { break; }
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

    static class Program
    {
        static string ReadFile(string path) => File.ReadAllText(path);

        [STAThread]
        static void Main(string[] args)
        {
            try
            {
                // WinForms init (required for UI behavior)
                try
                {
                    Application.EnableVisualStyles();
                    Application.SetCompatibleTextRenderingDefault(false);
                }
                catch { }

                string code;

                if (args.Length >= 1)
                {
                    code = ReadFile(args[0]);
                }
                else
                {
                    code =
                        "import System.Windows.Forms as WinForms;\n" +
                        "let form = new WinForms.Form();\n" +
                        "form.Text = \"DGV Demo\";\n" +
                        "form.Width = 800;\n" +
                        "form.Height = 400;\n" +
                        "\n" +
                        "let dgv = new WinForms.DataGridView();\n" +
                        "dgv.Dock = WinForms.DockStyle.Fill;\n" +
                        "dgv.AllowUserToAddRows = false;\n" +
                        "dgv.AutoSizeColumnsMode = WinForms.DataGridViewAutoSizeColumnsMode.Fill;\n" +
                        "\n" +
                        "dgv.Columns.Add(\"colName\", \"Name\");\n" +
                        "dgv.Columns.Add(\"colValue\", \"Value\");\n" +
                        "\n" +
                        "dgv.Rows.Add(\"Alice\", \"123\");\n" +
                        "dgv.Rows.Add(\"Bob\", \"456\");\n" +
                        "\n" +
                        "form.Controls.Add(dgv);\n" +
                        "form.ShowDialog();\n";
                }

                var lx = new Lexer(code);
                var ps = new Parser(lx);
                var ast = ps.ParseProgram();

                // optional
                AstDump.Dump(ast);

                var it = new Interpreter();
                it.Eval(ast, it.Global);
            }
            catch (Exception e)
            {
                Console.Error.WriteLine(e.Message);
                Environment.Exit(1);
            }
        }
    }
}
