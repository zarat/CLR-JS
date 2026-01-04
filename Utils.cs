// Program.cs - MiniJs: JS-like-ish interpreter with CLR interop + WinForms helpers + tasks

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
using System.Runtime.Loader;

namespace MiniJS
{


    // ---------------- Script runtime types ----------------

    sealed class JsArray { public List<object?> Items = new(); }

    sealed class JsObject
    {
        public Dictionary<string, object?> Props = new();
        public List<string> Order = new();
        public ClassDef? Klass;
    }

    public class Env
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

    public class Function
    {
        public List<string> Params = new();
        public Node? Body;            // Block node
        public Env? Closure;
        public bool IsNative = false;
        public Func<List<object?>, object?, object?>? Native;
    }

    public class ClassDef
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

    public class Rt
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

        static string EscapeJsString(string s)
        {
            return s
                .Replace("\\", "\\\\")
                .Replace("\"", "\\\"")
                .Replace("\r", "\\r")
                .Replace("\n", "\\n")
                .Replace("\t", "\\t");
        }

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
                /*
                List<object?> snap;
                lock (a) snap = a.Items.ToList();
                return "[" + string.Join(", ", snap.Select(ToJsString)) + "]";
                */
                List<object?> snap;
                lock (a) snap = a.Items.ToList();

                var parts = new List<string>(snap.Count);

                foreach (var elem in snap)
                {
                    parts.Add(ToJsString(elem)); 
                }

                return "[" + string.Join(", ", parts) + "]";
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

                    if(vv is string)
                        parts.Add(k + ": \"" + ToJsString(vv) + "\"");
                    else
                        parts.Add(k + ": " + ToJsString(vv));

                }
                return "{" + string.Join(", ", parts) + "}";
            }

            if (v is Function) return "[function]";
            if (v is ClassDef) return "[class]";
            if (v is ClrNamespace ns) return ns.ToString();
            if (v is Type t) return $"[MiniJS.Type {t.FullName}]";
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


}