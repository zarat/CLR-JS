using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace MiniJS
{

    public enum TokType
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

    public static class Tok
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

    readonly public struct Token
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

    public class Lexer
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


}
