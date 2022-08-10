// module for global config stuff
module GlobalConfig

open System

open Sentence
open DebugUtils

let mutable DBG_LOGDERIVER:bool = false; // log the done derivations? useful for collecting training data for NN

// log a derivation
// TODO REFACTOR< move this to "DeriverLogUtils.fs" >
let deriver_log__derivation (premises: Sentence list) (concl: Sentence) (ruleName:string) =
    if DBG_LOGDERIVER then
        let idsOfPremisesAsStr:string = premises |> List.map (fun iv->sprintf "%d%s" iv.uniqueId iv.punctation) |> String.concat "+";
        dbgLog3 "DRVR" true 0 (sprintf "DERIVE %s=%d%s %s" idsOfPremisesAsStr concl.uniqueId concl.punctation ruleName)
        ()
    else
        ()

// 
// TODO REFACTOR< move this to "DeriverLogUtils.fs" >
let deriver_log__input (src:string) (sentence: Sentence) =
    if DBG_LOGDERIVER then
        dbgLog3 "DRVR" true 0 (sprintf "INPUT %s %d%s" src sentence.uniqueId sentence.punctation);
        ()
    else
        ()


