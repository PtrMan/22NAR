module DebugUtils

// helper to emit log
let dbgLog3 (systemPrefix:string) (en:bool) (level:int) (msg:string) =
    if en then
        printfn "DBG[%i]: %s: %s" level systemPrefix msg;
    else
        ();

