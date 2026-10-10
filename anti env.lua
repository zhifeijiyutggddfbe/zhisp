local AntiEnv = {}
AntiEnv.NAME    = "AntiEnv"
AntiEnv.VERSION = "1.0.0"

local _G_REF = _G

local _type         = type
local _pairs        = pairs
local _ipairs       = ipairs
local _next         = next
local _rawget       = rawget
local _rawset       = rawset
local _rawequal     = rawequal
local _tostring     = tostring
local _tonumber     = tonumber
local _pcall        = pcall
local _xpcall       = xpcall
local _select       = select
local _error        = error
local _setmetatable = setmetatable
local _getmetatable = getmetatable
local _tconcat      = table and table.concat
local _tinsert      = table and table.insert
local _tremove      = table and table.remove
local _tsort        = table and table.sort
local _sformat      = string and string.format
local _ssub         = string and string.sub
local _srep         = string and string.rep
local _sfind        = string and string.find
local _os_clock     = os and os.clock
local _os_time      = os and os.time
local _math_floor   = math and math.floor
local _io_write     = io and io.write

local _D_GETINFO      = nil
local _D_GETMETATABLE = nil
local _D_GETUPVALUE   = nil
local _D_GETHOOK      = nil
local _D_TRACEBACK    = nil

do
    local d = _G_REF and _G_REF.debug
    if _type(d) == "table" then
        _D_GETINFO      = d.getinfo
        _D_GETMETATABLE = d.getmetatable
        _D_GETUPVALUE   = d.getupvalue
        _D_GETHOOK      = d.gethook
        _D_TRACEBACK    = d.traceback
    end
end

local State = {
    Initialized   = false,
    Halted        = false,
    Status        = "UNINITIALIZED",
    Baseline      = nil,
    LastResult    = nil,
    LastCheckTime = 0,
    CheckCount    = 0,
    IssueTotal    = 0,
    Transitions   = {},
}

local DEFAULT_CONFIG = {
    Strict                 = false,
    RuntimeCheck           = false,
    DetectHooks            = true,
    DetectMetatableChanges = true,
    DetectGlobalChanges    = true,
    DetectStdLib           = true,
    DetectDebug            = true,
    DetectLoader           = true,
    DetectWrapping         = true,
    DetectBehavior         = true,
    CheckInterval          = 5,
    Level                  = 2,
    SafeThreshold          = 85,
    Response               = "log",
    OnDetect               = nil,
    Logger                 = nil,
    AllowDebugRemoval      = false,
    Whitelist              = {},
    IgnoreList             = {},
    TrackNewGlobals        = false,
}

local Config = {}
do
    for k, v in _pairs(DEFAULT_CONFIG) do
        Config[k] = v
    end
end

local SEVERITY = {
    critical = { weight = 30, rank = 5 },
    high     = { weight = 18, rank = 4 },
    medium   = { weight = 9,  rank = 3 },
    low      = { weight = 4,  rank = 2 },
    info     = { weight = 0,  rank = 1 },
}

local function sevWeight(s)
    local e = SEVERITY[s]
    return e and e.weight or 9
end

local function sevRank(s)
    local e = SEVERITY[s]
    return e and e.rank or 3
end

local function defaultLogger(msg)
    if _io_write then
        _pcall(_io_write, msg, "\n")
    end
end

local MONITORED_GLOBALS = {
    "_G", "_VERSION",
    "print", "type", "pairs", "ipairs", "next", "select",
    "error", "assert", "tostring", "tonumber",
    "rawget", "rawset", "rawequal", "rawlen",
    "setmetatable", "getmetatable", "collectgarbage",
    "unpack", "load", "loadstring", "loadfile", "dofile",
    "require", "module", "newproxy", "gcinfo",
    "getfenv", "setfenv",
    "string", "table", "math", "os", "io",
    "coroutine", "debug", "package",
    "bit32", "utf8", "bit", "jit",
}

local MONITORED_LIBS = {
    "string", "table", "math", "os", "io",
    "coroutine", "debug", "package",
    "bit32", "utf8",
}

local function isLibName(n)
    for i = 1, #MONITORED_LIBS do
        if MONITORED_LIBS[i] == n then return true end
    end
    return false
end

local function isListed(lst, name)
    if _type(lst) ~= "table" then return false end
    if lst[name] ~= nil then return true end
    for i = 1, #lst do
        if lst[i] == name then return true end
    end
    return false
end

local function isWhitelisted(name)
    return isListed(Config.Whitelist, name) or isListed(Config.IgnoreList, name)
end

local function nowTime()
    if _os_clock then
        local ok, v = _pcall(_os_clock)
        if ok and _type(v) == "number" then return v end
    end
    if _os_time then
        local ok, v = _pcall(_os_time)
        if ok and _type(v) == "number" then return v end
    end
    return 0
end

local function rawIterate(t, fn)
    if _type(t) ~= "table" then return false end
    local ok, k, v = _pcall(_next, t)
    if not ok then return false end
    while k ~= nil do
        local rok = _pcall(fn, k, v)
        if not rok then return false end
        local ok2
        ok2, k, v = _pcall(_next, t, k)
        if not ok2 then return false end
    end
    return true
end

local function rawMT(obj)
    if _type(_D_GETMETATABLE) == "function" then
        local ok, mt = _pcall(_D_GETMETATABLE, obj)
        if ok then return mt end
    end
    local ok, mt = _pcall(_getmetatable, obj)
    if ok then return mt end
    return nil
end

local function safeGetInfo(f, what)
    if _type(_D_GETINFO) ~= "function" then return nil end
    local ok, info = _pcall(_D_GETINFO, f, what or "S")
    if ok and _type(info) == "table" then return info end
    return nil
end

local function safeGetUpvalues(f)
    if _type(_D_GETUPVALUE) ~= "function" then return nil end
    if _type(f) ~= "function" then return nil end
    local ups = {}
    local i = 1
    while i <= 128 do
        local ok, name, val = _pcall(_D_GETUPVALUE, f, i)
        if not ok or name == nil then break end
        ups[i] = { name = name, value = val }
        i = i + 1
    end
    return ups
end

local function detectEnvironment()
    local jit = _rawget(_G_REF, "jit")
    if _type(jit) == "table" then
        local jv = _rawget(jit, "version")
        if _type(jv) == "string" then return jv end
    end
    local ver = _rawget(_G_REF, "_VERSION")
    if _type(ver) == "string" then return ver end
    return "Unknown Lua"
end

local function newReport()
    return {
        Safe        = true,
        Score       = 100,
        Environment = "Unknown",
        Issues      = {},
        Checks      = {},
        Counts      = { critical = 0, high = 0, medium = 0, low = 0, info = 0 },
        Timestamp   = nowTime(),
        Version     = AntiEnv.VERSION,
        Status      = "CLEAN",
        _seen       = {},
    }
end

local function addIssue(report, category, message, severity, detail)
    if not SEVERITY[severity] then severity = "medium" end
    local key = category .. "\0" .. message
    if report._seen[key] then return nil end
    report._seen[key] = true

    local iss = {
        Category = category,
        Message  = message,
        Severity = severity,
        Detail   = detail,
        Time     = nowTime(),
    }
    _tinsert(report.Issues, iss)
    report.Counts[severity] = (report.Counts[severity] or 0) + 1
    return iss
end

local function addCheck(report, name, passed, info)
    _tinsert(report.Checks, {
        Name   = name,
        Passed = passed and true or false,
        Info   = info,
    })
end

local function snapshotLibrary(libName, lib)
    local entry = {}
    local count = 0
    _pcall(rawIterate, lib, function(k, v)
        if _type(k) == "string" then
            entry[k] = { ref = v, vtype = _type(v) }
            count = count + 1
        end
    end)
    return { ref = lib, entries = entry, count = count }
end

local function buildMetatableSnapshot()
    local snap = {}
    local targets = {
        { "_G",        _G_REF },
        { "string",    _rawget(_G_REF, "string") },
        { "table",     _rawget(_G_REF, "table") },
        { "math",      _rawget(_G_REF, "math") },
        { "os",        _rawget(_G_REF, "os") },
        { "io",        _rawget(_G_REF, "io") },
        { "coroutine", _rawget(_G_REF, "coroutine") },
        { "debug",     _rawget(_G_REF, "debug") },
        { "package",   _rawget(_G_REF, "package") },
    }
    for i = 1, #targets do
        local name, obj = targets[i][1], targets[i][2]
        if obj ~= nil then
            snap[name] = { target = obj, mt = rawMT(obj) }
        end
    end
    snap["__string_meta"] = { target = "", mt = rawMT("") }
    snap["__number_meta"] = { target = 0, mt = rawMT(0) }
    return snap
end

local function buildBaseline()
    local b = {
        Time    = nowTime(),
        Version = _rawget(_G_REF, "_VERSION"),
        Globals = {},
        Libs    = {},
        MTs     = {},
        Ups     = {},
    }

    for i = 1, #MONITORED_GLOBALS do
        local name = MONITORED_GLOBALS[i]
        local v = _rawget(_G_REF, name)
        if v ~= nil then
            b.Globals[name] = { ref = v, vtype = _type(v) }
        end
    end

    for i = 1, #MONITORED_LIBS do
        local libName = MONITORED_LIBS[i]
        local lib = _rawget(_G_REF, libName)
        if _type(lib) == "table" then
            b.Libs[libName] = snapshotLibrary(libName, lib)
        end
    end

    local critical = {
        { "string", "gsub" }, { "string", "format" }, { "string", "find" },
        { "table",  "concat" }, { "table", "insert" }, { "table", "sort" },
        { "math",   "floor" }, { "math", "max" },
    }
    for i = 1, #critical do
        local libName, fnName = critical[i][1], critical[i][2]
        local lib = _rawget(_G_REF, libName)
        if _type(lib) == "table" then
            local fn = _rawget(lib, fnName)
            if _type(fn) == "function" then
                local info = safeGetInfo(fn, "S")
                if info and info.what == "Lua" then
                    b.Ups[libName .. "." .. fnName] = safeGetUpvalues(fn)
                end
            end
        end
    end

    b.MTs = buildMetatableSnapshot()
    return b
end

local function stageGlobalSelf(report)
    local g = _rawget(_G_REF, "_G")
    if _rawequal(g, _G_REF) then
        addCheck(report, "GlobalSelfReference", true)
    else
        addCheck(report, "GlobalSelfReference", false, "_G._G ~= _G")
        addIssue(report, "Global", "Global modified: _G self-reference changed", "critical")
    end

    local ver = _rawget(_G_REF, "_VERSION")
    if _type(ver) ~= "string" then
        addCheck(report, "VersionTag", false)
        addIssue(report, "Global", "Global modified: _VERSION missing or invalid", "high")
    else
        addCheck(report, "VersionTag", true, ver)
    end
end

local function stageReferences(report, baseline)
    if not Config.DetectGlobalChanges then
        addCheck(report, "GlobalReferences", true, "disabled")
        return 0
    end
    local changed = 0
    for name, rec in _pairs(baseline.Globals) do
        if not isLibName(name) and not isWhitelisted(name) then
            local cur = _rawget(_G_REF, name)
            if cur == nil and rec.ref ~= nil then
                changed = changed + 1
                addIssue(report, "Global", "Global removed: " .. name, "high",
                    { expected = rec.vtype, got = "nil" })
            elseif _type(cur) ~= rec.vtype then
                changed = changed + 1
                addIssue(report, "Global",
                    "Global type changed: " .. name .. " (" .. rec.vtype .. " -> " .. _type(cur) .. ")",
                    "critical")
            elseif not _rawequal(cur, rec.ref) then
                changed = changed + 1
                addIssue(report, "Global", "Global modified: " .. name, "high")
            end
        end
    end
    addCheck(report, "GlobalReferences", changed == 0, changed .. " change(s)")
    return changed
end

local function stageLibraries(report, baseline)
    if not Config.DetectStdLib then
        addCheck(report, "StandardLibraries", true, "disabled")
        return 0
    end
    local total = 0
    for libName, libSnap in _pairs(baseline.Libs) do
        local lib = _rawget(_G_REF, libName)
        if _type(lib) ~= "table" then
            total = total + 1
            addCheck(report, "StdLib." .. libName, false, "not a table")
            addIssue(report, "StdLib",
                "Standard library modified: " .. libName .. " is not a table", "critical")
        elseif not _rawequal(lib, libSnap.ref) then
            total = total + 1
            addCheck(report, "StdLib." .. libName, false, "table replaced")
            addIssue(report, "StdLib",
                "Standard library replaced: " .. libName, "critical")
        else
            local localChanged = 0
            for k, rec in _pairs(libSnap.entries) do
                local cur = _rawget(lib, k)
                if cur == nil then
                    localChanged = localChanged + 1
                    addIssue(report, "StdLib",
                        "Standard library modified: " .. libName .. "." .. k .. " removed", "high")
                elseif _type(cur) ~= rec.vtype then
                    localChanged = localChanged + 1
                    addIssue(report, "StdLib",
                        "Standard library modified: " .. libName .. "." .. k ..
                        " type changed (" .. rec.vtype .. " -> " .. _type(cur) .. ")", "critical")
                elseif not _rawequal(cur, rec.ref) then
                    localChanged = localChanged + 1
                    addIssue(report, "StdLib",
                        "Function reference changed: " .. libName .. "." .. k, "high")
                end
            end
            if localChanged > 0 then
                addCheck(report, "StdLib." .. libName, false, localChanged .. " change(s)")
            else
                addCheck(report, "StdLib." .. libName, true)
            end
            total = total + localChanged
        end
    end
    return total
end

local function stageMetatables(report, baseline)
    if not Config.DetectMetatableChanges then
        addCheck(report, "Metatables", true, "disabled")
        return 0
    end
    local changed = 0
    for name, rec in _pairs(baseline.MTs) do
        local cur = rawMT(rec.target)
        if not _rawequal(cur, rec.mt) then
            changed = changed + 1
            addIssue(report, "Metatable", "Metatable changed: " .. name, "high",
                { before = _tostring(rec.mt), after = _tostring(cur) })
        end
    end

    local gmt = rawMT(_G_REF)
    if gmt ~= nil then
        changed = changed + 1
        addIssue(report, "Metatable", "Metatable changed: _G has a metatable", "critical")
    end

    local gm = _rawget(_G_REF, "getmetatable")
    if _type(gm) == "function" then
        local ok, r1 = _pcall(gm, {})
        if not ok or r1 ~= nil then
            changed = changed + 1
            addIssue(report, "Metatable", "Metatable changed: getmetatable behavior abnormal", "medium")
        end
    end

    local smt = rawMT("")
    if _type(smt) == "table" then
        local idx = _rawget(smt, "__index")
        local strlib = _rawget(_G_REF, "string")
        if idx ~= nil and strlib ~= nil and not _rawequal(idx, strlib) then
            changed = changed + 1
            addIssue(report, "Metatable", "Metatable changed: string __index mismatch", "high")
        end
    end

    addCheck(report, "Metatables", changed == 0, changed .. " change(s)")
    return changed
end

local function stageDebug(report)
    if not Config.DetectDebug then
        addCheck(report, "DebugEnvironment", true, "disabled")
        return 0
    end
    local issues = 0
    local dbg = _rawget(_G_REF, "debug")

    if dbg == nil then
        if Config.AllowDebugRemoval then
            addCheck(report, "DebugEnvironment", true, "removed (allowed)")
        else
            issues = issues + 1
            addCheck(report, "DebugEnvironment", false, "missing")
            addIssue(report, "Debug", "Debug environment abnormal: debug library missing", "high")
        end
        return issues
    end

    if _type(dbg) ~= "table" then
        issues = issues + 1
        addCheck(report, "DebugEnvironment", false, "not a table")
        addIssue(report, "Debug", "Debug environment abnormal: debug is not a table", "critical")
        return issues
    end

    if _type(_D_GETINFO) == "function" then
        local ok, info = _pcall(_D_GETINFO, _D_GETINFO, "S")
        if ok and _type(info) == "table" then
            if info.what ~= "C" then
                issues = issues + 1
                addIssue(report, "Debug",
                    "Debug environment abnormal: debug.getinfo reports non-C source", "high")
            end
            if info.func ~= nil and not _rawequal(info.func, _D_GETINFO) then
                issues = issues + 1
                addIssue(report, "Debug",
                    "Debug environment abnormal: debug.getinfo self-report mismatch", "critical")
            end
        else
            issues = issues + 1
            addIssue(report, "Debug",
                "Debug environment abnormal: debug.getinfo call failed", "high")
        end
    end

    local curGI = _rawget(dbg, "getinfo")
    if not _rawequal(curGI, _D_GETINFO) then
        issues = issues + 1
        addIssue(report, "Debug",
            "Debug environment abnormal: debug.getinfo replaced", "critical")
    end

    local curGM = _rawget(dbg, "getmetatable")
    if _D_GETMETATABLE ~= nil and not _rawequal(curGM, _D_GETMETATABLE) then
        issues = issues + 1
        addIssue(report, "Debug",
            "Debug environment abnormal: debug.getmetatable replaced", "high")
    end

    if Config.DetectHooks then
        local gh = _rawget(dbg, "gethook")
        if _type(gh) == "function" then
            local ok, hook, mask, count = _pcall(gh)
            if ok and hook ~= nil then
                issues = issues + 1
                addIssue(report, "Debug",
                    "Debug environment abnormal: active debug hook detected", "high",
                    { mask = mask, count = count })
            end
        end
    end

    addCheck(report, "DebugEnvironment", issues == 0, issues .. " issue(s)")
    return issues
end

local function stageLoader(report)
    if not Config.DetectLoader then
        addCheck(report, "LoaderEnvironment", true, "disabled")
        return 0
    end
    local issues = 0

    local requireFn = _rawget(_G_REF, "require")
    if requireFn == nil then
        issues = issues + 1
        addIssue(report, "Loader", "Loader environment changed: require missing", "high")
    elseif _type(requireFn) ~= "function" then
        issues = issues + 1
        addIssue(report, "Loader",
            "Loader environment changed: require is not a function", "critical")
    end

    local loadFn = _rawget(_G_REF, "load")
    local loadstringFn = _rawget(_G_REF, "loadstring")
    local loadfileFn = _rawget(_G_REF, "loadfile")
    local dofileFn = _rawget(_G_REF, "dofile")

    if loadFn ~= nil and _type(loadFn) ~= "function" then
        issues = issues + 1
        addIssue(report, "Loader", "Loader environment changed: load is not a function", "critical")
    end
    if loadstringFn ~= nil and _type(loadstringFn) ~= "function" then
        issues = issues + 1
        addIssue(report, "Loader",
            "Loader environment changed: loadstring is not a function", "critical")
    end
    if loadfileFn ~= nil and _type(loadfileFn) ~= "function" then
        issues = issues + 1
        addIssue(report, "Loader",
            "Loader environment changed: loadfile is not a function", "critical")
    end
    if dofileFn ~= nil and _type(dofileFn) ~= "function" then
        issues = issues + 1
        addIssue(report, "Loader",
            "Loader environment changed: dofile is not a function", "critical")
    end

    local pkg = _rawget(_G_REF, "package")
    if _type(pkg) == "table" then
        local loaded = _rawget(pkg, "loaded")
        if _type(loaded) == "table" then
            for i = 1, #MONITORED_LIBS do
                local libName = MONITORED_LIBS[i]
                local lib = _rawget(_G_REF, libName)
                local cached = _rawget(loaded, libName)
                if lib ~= nil and cached ~= nil and not _rawequal(lib, cached) then
                    issues = issues + 1
                    addIssue(report, "Loader",
                        "Loader environment changed: package.loaded." .. libName .. " mismatch",
                        "medium")
                end
            end
        end
    end

    addCheck(report, "LoaderEnvironment", issues == 0, issues .. " issue(s)")
    return issues
end

local function stageWrapping(report, baseline)
    if not Config.DetectWrapping then
        addCheck(report, "FunctionWrapping", true, "disabled")
        return 0
    end
    if _type(_D_GETINFO) ~= "function" then
        addCheck(report, "FunctionWrapping", true, "debug.getinfo unavailable")
        return 0
    end

    local suspicious = 0

    for libName, libSnap in _pairs(baseline.Libs) do
        local lib = _rawget(_G_REF, libName)
        if _type(lib) == "table" then
            for k, rec in _pairs(libSnap.entries) do
                if rec.vtype == "function" then
                    local cur = _rawget(lib, k)
                    if _type(cur) == "function" then
                        local prevInfo = safeGetInfo(rec.ref, "S")
                        local curInfo  = safeGetInfo(cur, "S")
                        if prevInfo and curInfo then
                            if prevInfo.what and curInfo.what and prevInfo.what ~= curInfo.what then
                                suspicious = suspicious + 1
                                addIssue(report, "Hook",
                                    "Function wrapping detected: " .. libName .. "." .. k ..
                                    " (" .. _tostring(prevInfo.what) .. " -> " .. _tostring(curInfo.what) .. ")",
                                    "high")
                            end
                            if prevInfo.what == "C" and curInfo.what == "Lua" then
                                suspicious = suspicious + 1
                                addIssue(report, "Hook",
                                    "Function wrapping detected: " .. libName .. "." .. k ..
                                    " replaced by Lua wrapper", "critical")
                            end
                        end
                    end
                end
            end
        end
    end

    for key, ups in _pairs(baseline.Ups) do
        local libName, fnName = key:match("^([^.]+)%.(.+)$")
        if libName and fnName then
            local lib = _rawget(_G_REF, libName)
            if _type(lib) == "table" then
                local fn = _rawget(lib, fnName)
                if _type(fn) == "function" then
                    local curUps = safeGetUpvalues(fn)
                    if curUps and ups then
                        local n1, n2 = #ups, #curUps
                        if n1 ~= n2 then
                            suspicious = suspicious + 1
                            addIssue(report, "Hook",
                                "Function upvalue count changed: " .. key, "high")
                        else
                            for i = 1, n1 do
                                if ups[i].name ~= curUps[i].name then
                                    suspicious = suspicious + 1
                                    addIssue(report, "Hook",
                                        "Function upvalue name changed: " .. key .. "[" .. i .. "]", "high")
                                    break
                                end
                                local a, b = ups[i].value, curUps[i].value
                                if _type(a) == "function" or _type(b) == "function"
                                   or _type(a) == "table" or _type(b) == "table" then
                                    if not _rawequal(a, b) then
                                        suspicious = suspicious + 1
                                        addIssue(report, "Hook",
                                            "Function upvalue reference changed: " .. key .. "[" .. i .. "]", "high")
                                        break
                                    end
                                elseif a ~= b then
                                    suspicious = suspicious + 1
                                    addIssue(report, "Hook",
                                        "Function upvalue value changed: " .. key .. "[" .. i .. "]", "high")
                                    break
                                end
                            end
                        end
                    end
                end
            end
        end
    end

    addCheck(report, "FunctionWrapping", suspicious == 0, suspicious .. " suspicious")
    return suspicious
end

local PROBES = {
    { "type", function()
        local f = _rawget(_G_REF, "type")
        if _type(f) ~= "function" then return false end
        return f(1) == "number" and f("") == "string" and f(nil) == "nil" and f(true) == "boolean"
    end },
    { "tostring", function()
        local f = _rawget(_G_REF, "tostring")
        if _type(f) ~= "function" then return false end
        return f(nil) == "nil" and f(true) == "true" and f(123) == "123"
    end },
    { "tonumber", function()
        local f = _rawget(_G_REF, "tonumber")
        if _type(f) ~= "function" then return false end
        return f("42") == 42 and f("10", 16) == 16
    end },
    { "string.upper", function()
        local s = _rawget(_G_REF, "string")
        return _type(s) == "table" and _type(s.upper) == "function" and s.upper("abc") == "ABC"
    end },
    { "string.rep", function()
        local s = _rawget(_G_REF, "string")
        return _type(s) == "table" and _type(s.rep) == "function" and s.rep("a", 3) == "aaa"
    end },
    { "string.sub", function()
        local s = _rawget(_G_REF, "string")
        return _type(s) == "table" and _type(s.sub) == "function" and s.sub("hello", 2, 3) == "el"
    end },
    { "string.format", function()
        local s = _rawget(_G_REF, "string")
        return _type(s) == "table" and _type(s.format) == "function"
            and s.format("%d-%s", 7, "x") == "7-x"
    end },
    { "table.concat", function()
        local t = _rawget(_G_REF, "table")
        return _type(t) == "table" and _type(t.concat) == "function"
            and t.concat({ "a", "b", "c" }, ",") == "a,b,c"
    end },
    { "table.insert/remove", function()
        local t = _rawget(_G_REF, "table")
        if _type(t) ~= "table" or _type(t.insert) ~= "function" or _type(t.remove) ~= "function" then
            return false
        end
        local a = {}
        t.insert(a, "x")
        t.insert(a, "y")
        return #a == 2 and t.remove(a) == "y" and #a == 1
    end },
    { "math.floor", function()
        local m = _rawget(_G_REF, "math")
        return _type(m) == "table" and _type(m.floor) == "function"
            and m.floor(3.7) == 3 and m.floor(-1.2) == -2
    end },
    { "math.max", function()
        local m = _rawget(_G_REF, "math")
        return _type(m) == "table" and _type(m.max) == "function"
            and m.max(1, 5, 3) == 5
    end },
    { "select", function()
        local f = _rawget(_G_REF, "select")
        if _type(f) ~= "function" then return false end
        return f("#", 1, 2, 3) == 3 and f(2, "a", "b", "c") == "b"
    end },
    { "pcall", function()
        local f = _rawget(_G_REF, "pcall")
        if _type(f) ~= "function" then return false end
        local ok, err = f(function() _error("probe") end)
        return ok == false and err == "probe"
    end },
    { "rawequal", function()
        local f = _rawget(_G_REF, "rawequal")
        if _type(f) ~= "function" then return false end
        return f(1, 1) == true and f({}, {}) == false
    end },
    { "rawget", function()
        local f = _rawget(_G_REF, "rawget")
        if _type(f) ~= "function" then return false end
        return f({ a = 1 }, "a") == 1 and f({}, "b") == nil
    end },
    { "coroutine", function()
        local c = _rawget(_G_REF, "coroutine")
        if _type(c) ~= "table" or _type(c.create) ~= "function" or _type(c.resume) ~= "function" then
            return false
        end
        local co = c.create(function(a) return a + 1 end)
        local ok, v = c.resume(co, 41)
        return ok == true and v == 42
    end },
}

local function stageBehavior(report)
    if not Config.DetectBehavior then
        addCheck(report, "BehaviorProbes", true, "disabled")
        return 0
    end
    local fails = 0
    for i = 1, #PROBES do
        local p = PROBES[i]
        local ok, passed = _pcall(p[2])
        if not ok or passed ~= true then
            fails = fails + 1
            addIssue(report, "Behavior",
                "Function behavior changed: " .. p[1], "high",
                { error = (not ok) and _tostring(passed) or nil })
        end
    end
    addCheck(report, "BehaviorProbes", fails == 0, fails .. " failure(s)")
    return fails
end

local function computeStatus(report)
    if report.Counts.critical > 0 or report.Counts.high > 0 then
        return "TAMPERED"
    elseif report.Counts.medium > 0 or report.Counts.low > 0 then
        return "SUSPICIOUS"
    end
    return "CLEAN"
end

local function finalizeReport(report)
    local score = 100
    for i = 1, #report.Issues do
        score = score - sevWeight(report.Issues[i].Severity)
    end
    if score < 0 then score = 0 end

    if Config.Strict and #report.Issues > 0 then
        if _math_floor then
            score = _math_floor(score * 0.9)
        else
            score = score * 0.9
        end
    end

    report.Score = score
    report.Safe  = (report.Counts.critical == 0)
                   and (report.Counts.high == 0)
                   and (score >= (Config.SafeThreshold or 85))
    report.Status = computeStatus(report)
    report._seen = nil
    return report
end

local function transitionState(report)
    local prev = State.Status
    local nxt  = computeStatus(report)
    if State.Halted then nxt = "LOCKDOWN" end
    if prev ~= nxt then
        _tinsert(State.Transitions, { from = prev, to = nxt, time = nowTime() })
    end
    State.Status = nxt
    report.Status = nxt
end

local function applyResponse(report)
    if report.Safe then return end
    local resp = Config.Response
    if resp == nil or resp == "none" then return end

    if resp == "log" or resp == "warn" then
        local lines = {
            "[AntiEnv] " .. _tostring(resp):upper() ..
            " - environment tampering detected (score=" .. _tostring(report.Score) .. ")"
        }
        for i = 1, #report.Issues do
            local iss = report.Issues[i]
            _tinsert(lines, "  [" .. iss.Severity .. "] " .. iss.Category .. ": " .. iss.Message)
        end
        local msg = _tconcat(lines, "\n")
        if _type(Config.Logger) == "function" then
            _pcall(Config.Logger, msg, report)
        else
            _pcall(defaultLogger, msg)
        end

    elseif resp == "error" then
        local first = report.Issues[1]
        _error("[AntiEnv] Environment tampering detected: " ..
            (first and first.Message or "unknown"), 0)

    elseif resp == "halt" then
        State.Halted = true
        State.Status = "LOCKDOWN"
        local first = report.Issues[1]
        _error("[AntiEnv] LOCKDOWN: " ..
            (first and first.Message or "environment tampering"), 0)

    elseif resp == "custom" then
        if _type(Config.OnDetect) == "function" then
            _pcall(Config.OnDetect, report)
        end
    end
end

local function applyLevelDefaults(opts)
    opts = opts or {}
    local lvl = _tonumber(Config.Level) or 2
    local map
    if lvl <= 1 then
        map = {
            DetectMetatableChanges = false,
            DetectWrapping         = false,
            DetectBehavior         = false,
            DetectHooks            = true,
            DetectDebug            = true,
        }
    elseif lvl == 2 then
        map = {
            DetectMetatableChanges = true,
            DetectWrapping         = true,
            DetectBehavior         = false,
            DetectHooks            = true,
            DetectDebug            = true,
        }
    else
        map = {
            DetectMetatableChanges = true,
            DetectWrapping         = true,
            DetectBehavior         = true,
            DetectHooks            = true,
            DetectDebug            = true,
        }
    end
    for k, v in _pairs(map) do
        if opts[k] == nil then
            Config[k] = v
        end
    end
end

function AntiEnv.Init(opts)
    opts = opts or {}

    for k, v in _pairs(DEFAULT_CONFIG) do
        Config[k] = v
    end
    Config.Whitelist  = {}
    Config.IgnoreList = {}

    for k, v in _pairs(opts) do
        Config[k] = v
    end

    applyLevelDefaults(opts)

    State.Initialized   = true
    State.Halted        = false
    State.Status        = "CLEAN"
    State.CheckCount    = 0
    State.IssueTotal    = 0
    State.Transitions   = {}
    State.LastResult    = nil
    State.LastCheckTime = 0

    State.Baseline = buildBaseline()

    return true
end

function AntiEnv.Snapshot()
    State.Baseline = buildBaseline()
    return true
end

function AntiEnv.Check(force)
    if not State.Initialized then
        return {
            Safe        = false,
            Score       = 0,
            Environment = "unknown",
            Issues      = { {
                Category = "System",
                Message  = "AntiEnv not initialized",
                Severity = "critical",
            } },
            Checks      = {},
            Status      = "UNINITIALIZED",
            Error       = "NOT_INITIALIZED",
        }
    end

    if State.Halted then
        return {
            Safe        = false,
            Score       = 0,
            Environment = detectEnvironment(),
            Issues      = { {
                Category = "System",
                Message  = "AntiEnv in LOCKDOWN state",
                Severity = "critical",
            } },
            Checks      = {},
            Status      = "LOCKDOWN",
            Error       = "LOCKDOWN",
        }
    end

    local t = nowTime()

    if not force and Config.RuntimeCheck and State.LastResult then
        local elapsed = t - State.LastCheckTime
        if elapsed >= 0 and elapsed < (Config.CheckInterval or 5) then
            local cached = State.LastResult
            cached.Cached = true
            return cached
        end
    end

    local report = newReport()
    report.Environment = detectEnvironment()
    report.Level       = Config.Level
    State.CheckCount   = State.CheckCount + 1

    if not State.Baseline then
        State.Baseline = buildBaseline()
        report.Note = "Baseline created on first check"
    end

    local B = State.Baseline

    stageGlobalSelf(report)
    stageReferences(report, B)
    stageLibraries(report, B)
    stageMetatables(report, B)
    stageDebug(report)
    stageLoader(report)
    stageWrapping(report, B)
    stageBehavior(report)

    finalizeReport(report)
    transitionState(report)

    report.Cached = false
    State.LastResult    = report
    State.LastCheckTime = t
    State.IssueTotal    = State.IssueTotal + #report.Issues

    applyResponse(report)

    return report
end

function AntiEnv.Tick()
    return AntiEnv.Check(false)
end

function AntiEnv.Verify()
    return AntiEnv.Check(true)
end

function AntiEnv.GetStatus()
    return State.Status, {
        Initialized = State.Initialized,
        Halted      = State.Halted,
        CheckCount  = State.CheckCount,
        IssueTotal  = State.IssueTotal,
        Transitions = State.Transitions,
    }
end

function AntiEnv.GetLastResult()
    return State.LastResult
end

function AntiEnv.GetBaseline()
    return State.Baseline
end

function AntiEnv.Reset()
    State.Halted        = false
    State.Status        = State.Initialized and "CLEAN" or "UNINITIALIZED"
    State.LastResult    = nil
    State.LastCheckTime = 0
    State.CheckCount    = 0
    State.IssueTotal    = 0
    State.Transitions   = {}
    return true
end

function AntiEnv.GetConfig()
    local out = {}
    for k, v in _pairs(Config) do
        if _type(v) ~= "table" then
            out[k] = v
        else
            local copy = {}
            for kk, vv in _pairs(v) do copy[kk] = vv end
            out[k] = copy
        end
    end
    return out
end

function AntiEnv.SetConfig(key, value)
    if key == nil then return false end
    Config[key] = value
    return true
end

function AntiEnv.AddWhitelist(name)
    if _type(name) ~= "string" then return false end
    Config.Whitelist[name] = true
    return true
end

function AntiEnv.AddIgnore(name)
    if _type(name) ~= "string" then return false end
    Config.IgnoreList[name] = true
    return true
end

function AntiEnv.Format(report)
    report = report or State.LastResult
    if not report then return "AntiEnv: no report" end
    local lines = {
        "=== AntiEnv Report ===",
        "Environment : " .. _tostring(report.Environment),
        "Status      : " .. _tostring(report.Status),
        "Safe        : " .. _tostring(report.Safe),
        "Score       : " .. _tostring(report.Score),
        "Issues      : " .. _tostring(#report.Issues),
        "Checks      : " .. _tostring(#report.Checks),
    }
    if #report.Issues > 0 then
        _tinsert(lines, "--- Issues ---")
        for i = 1, #report.Issues do
            local iss = report.Issues[i]
            _tinsert(lines, _sformat("  [%s] %s :: %s",
                iss.Severity, iss.Category, iss.Message))
        end
    end
    return _tconcat(lines, "\n")
end

return AntiEnv