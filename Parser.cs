using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace MiniJS
{

    public enum NodeType
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

    public class Node
    {
        public NodeType Type;
        public Token Tok;
        public string Text = "";
        public List<Node?> Kids = new();

        public Node(NodeType t) { Type = t; Tok = default; }
        public Node(NodeType t, Token tk) { Type = t; Tok = tk; }
    }

    public class Parser
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


}
