using System;
using System.Collections;
using System.Collections.Generic;
using System.ComponentModel;
using System.Globalization;
using System.Linq;
using System.Linq.Expressions;
using System.Reflection;
using System.Runtime.Loader;
using System.Text;
using System.Threading.Tasks;

namespace MiniJS
{
    public class Interpreter
    {
        public Env Global;

        private readonly TaskManager _taskMgr;

        private readonly object _namedLocksGuard = new();
        private readonly Dictionary<string, object> _namedLocks = new(StringComparer.Ordinal);

        private readonly object _eventSubsGuard = new();
        private readonly Dictionary<EventKey, List<Delegate>> _eventSubs = new(new EventKeyComparer());

        private readonly Dictionary<string, Type?> _typeCache = new(StringComparer.Ordinal);

        private readonly string[] _tpa;
        private readonly Dictionary<string, Assembly> _asmByPath = new(StringComparer.OrdinalIgnoreCase);

        private static readonly object _asmResolveLock = new();
        private static bool _asmResolverInstalled = false;
        private static readonly HashSet<string> _probeDirs = new(StringComparer.OrdinalIgnoreCase);

        public Interpreter()
        {
            Global = new Env();
            _taskMgr = new TaskManager(Math.Max(1, Environment.ProcessorCount), 5000);
            _tpa = ((string?)AppContext.GetData("TRUSTED_PLATFORM_ASSEMBLIES"))?.Split(Path.PathSeparator) ?? Array.Empty<string>();

            EnsureAsmResolverInstalled();

            Global.Declare("loadDll", new Function
            {
                IsNative = true,
                Native = (args, _) =>
                {
                    if (args.Count < 1) throw new Exception("TypeError: loadDll(path) expects 1 arg");

                    var input = Rt.ToJsString(args[0]).Trim();
                    if (string.IsNullOrWhiteSpace(input))
                        throw new Exception("TypeError: loadDll(path) expects a non-empty path");

                    string fullPath;

                    // wenn nur "CsvHelper" übergeben wird -> "CsvHelper.dll" suchen
                    if (!input.EndsWith(".dll", StringComparison.OrdinalIgnoreCase))
                        input += ".dll";

                    // relativ: erst CWD, dann EXE-Ordner
                    if (Path.IsPathRooted(input))
                    {
                        fullPath = Path.GetFullPath(input);
                    }
                    else
                    {
                        var cand1 = Path.GetFullPath(Path.Combine(Environment.CurrentDirectory, input));
                        var cand2 = Path.GetFullPath(Path.Combine(AppContext.BaseDirectory, input));
                        fullPath = File.Exists(cand1) ? cand1 : cand2;
                    }

                    if (!File.Exists(fullPath))
                        throw new Exception("File not found: " + fullPath);

                    // Probe-Dir merken (für Dependencies)
                    AddProbeDir(Path.GetDirectoryName(fullPath)!);

                    // Laden
                    if (!_asmByPath.TryGetValue(fullPath, out var asm))
                    {
                        asm = AssemblyLoadContext.Default.LoadFromAssemblyPath(fullPath);
                        _asmByPath[fullPath] = asm;
                    }

                    return asm.FullName ?? asm.GetName().Name ?? "loaded";
                }
            });

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

        private static void AddProbeDir(string dir)
        {
            if (string.IsNullOrWhiteSpace(dir)) return;
            dir = Path.GetFullPath(dir);
            lock (_asmResolveLock) _probeDirs.Add(dir);
        }

        private static void EnsureAsmResolverInstalled()
        {
            lock (_asmResolveLock)
            {
                if (_asmResolverInstalled) return;

                // Standard-Probe: EXE-Ordner + aktuelles Working Directory
                AddProbeDir(AppContext.BaseDirectory);
                AddProbeDir(Environment.CurrentDirectory);

                AssemblyLoadContext.Default.Resolving += (ctx, asmName) =>
                {
                    var file = (asmName.Name ?? "") + ".dll";
                    string[] dirs;
                    lock (_asmResolveLock) dirs = _probeDirs.ToArray();

                    foreach (var d in dirs)
                    {
                        var cand = Path.Combine(d, file);
                        if (File.Exists(cand))
                            return ctx.LoadFromAssemblyPath(Path.GetFullPath(cand));
                    }
                    return null;
                };

                _asmResolverInstalled = true;
            }
        }

        private Type? ResolveClrType(string fullName)
        {

            //return null; // disable c# types

            lock (_typeCache)
                if (_typeCache.TryGetValue(fullName, out var cached) && cached != null)
                    return cached;

            Type? found = null;

            // 1) already loaded
            foreach (var asm in AppDomain.CurrentDomain.GetAssemblies())
            {
                found = asm.GetType(fullName, false, false);
                if (found != null) goto FOUND;
            }

            // 2) try load likely framework assemblies from TPA list
            // build prefixes: "System.Security.Cryptography.Aes" -> try "System.Security.Cryptography", "System.Security"
            string ns = fullName;
            int lastDot = ns.LastIndexOf('.');
            if (lastDot > 0) ns = ns.Substring(0, lastDot);

            var parts = ns.Split('.');
            var prefixes = new List<string>();
            for (int i = Math.Min(parts.Length, 4); i >= 1; i--)
                prefixes.Add(string.Join(".", parts.Take(i)));

            foreach (var prefix in prefixes)
            {
                foreach (var path in _tpa)
                {
                    var file = Path.GetFileNameWithoutExtension(path);
                    if (!file.StartsWith(prefix, StringComparison.OrdinalIgnoreCase)) continue;

                    if (!_asmByPath.TryGetValue(path, out var a))
                    {
                        try
                        {
                            a = AssemblyLoadContext.Default.LoadFromAssemblyPath(path);
                            _asmByPath[path] = a;
                        }
                        catch { continue; }
                    }

                    found = a.GetType(fullName, false, false);
                    if (found != null) goto FOUND;
                }
            }

        FOUND:
            if (found != null)
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

        /*
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
        */
        private static bool StrictEq(object? a, object? b)
        {
            if (a == null && b == null) return true;
            if (a == null || b == null) return false;

            // ✅ FIX: strings immer nach INHALT vergleichen (nicht ReferenceEquals)
            if (a is string sa && b is string sb)
                return string.Equals(sa, sb, StringComparison.Ordinal);

            if (Rt.IsNumeric(a) && Rt.IsNumeric(b))
                return Rt.ToNumber(a) == Rt.ToNumber(b);

            if (a.GetType() != b.GetType()) return false;

            // für andere reference types weiter "strict" per Referenz
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

                        string calleeShape =
                            calleeNode.Type == NodeType.Var ? $"var '{calleeNode.Tok.Lexeme}'" :
                            calleeNode.Type == NodeType.Member ? $"member '.{calleeNode.Kids[1]!.Tok.Lexeme}'" :
                            calleeNode.Type == NodeType.Index ? "index '[..]'" :
                            calleeNode.Type.ToString();

                        string gotType = fnv == null ? "null" : fnv.GetType().FullName ?? "(no type)";
                        string gotVal = Rt.ToJsString(fnv);

                        throw new Exception(
                            $"TypeError: call of non-function at pos {n.Tok.Pos} (callee={calleeShape}) -> {gotType} value={gotVal}"
                        );
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


}
