module Nal9stdlibA

open Term
open GoalSystem
open GoalSystemUtils

// some basic NAL9 ops

// call a single op or a sequence of ops and inject an event
let nal9op_callAndInj (goalMem:GoalMem0) (args: Term list) =
    
    let calledOpsTerm: Term = args.[1]; // singe op or sequence of ops to be called
    let injEventTerm: Term = args.[2]; // arg [2] is the event to be injected

    // * compose list of ops to be called in sequence
    let mutable opsToCall: Term list = // ops to call
        match calledOpsTerm with
        | Seq seqItems ->
            seqItems
        | _ -> // only a single op to call
            [calledOpsTerm]
    

    // * call ops
    for iOpToCall in opsToCall do
        match (matchOp iOpToCall) with // parse term of op as op-name and args 
        | Some opAndArgs ->
            goalSystem__invokeOpByName goalMem opAndArgs.name opAndArgs.args false;
        | None ->
            // soft error - can't parse the term as a op!, ignore
            ()

        ()

    // * inject event
    printfn "TODO";

    ()
