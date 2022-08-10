module Nal9routine

open GoalSystem

// routines which can be triggered by NAL-9 ops

let StrategyInflight = struct {
    mutable state: int;
    arg: Term; // actual used argument
    strategyName: string; // name of strategy

    mutable flagDeleteMe: bool; // delete this strategy soon?
}

// FIXME< global variables are bad >
let mutable nal9routine__strategiesInFlight: StrategyInflight list = [];

// callable as op
let op_nal9__strategyTrigger (mem:BeliefMem0) (timeNow:int64) (args: Term list): (Term * Term) list =
    let argStrategynameOpt: string option = match args.[1] with
    | Name name -> Some name
    | _ -> None
    let arg2Term = args.[2];
    
    match argStrategynameOpt with
    | Some argStrategyname ->
        
        // queue up strategy as active strategy
        let createdStrategy: StrategyInflight = {
            state = 0;
            arg = arg2Term;
            strategyName = argStrategyname;
            flagDeleteMe = false;
        }

        // queue up
        nal9routine__strategiesInFlight <- createdStrategy ::nal9routine__strategiesInFlight;
        ()
    | None ->
        ()

// TODO< call in main loop ! >
// called from some main-loop to process and manage the nal9 strategies which require processing
let nal9strategy__process (goalMem:GoalMem0) =
    
    for iStrategyInFlight in nal9routine__strategiesInFlight do
        match iStrategyInFlight.state with
        | 0 -> // initialize me state
            
            match iStrategyInFlight.strategyName with
            | "STARTA" -> // "STARTA" strategy should be started
                // add goal
                // TODO TODO TODO TODO

                iStrategyInFlight.state <- 1;
                ()
            | _ ->
                () // soft internal error - ignore
            
            ()
        | 1 ->

            match iStrategyInFlight.strategyName with
            | "STARTA" -> 
                // TODO TODO TODO TODO - monitor for signal that the goal was processed by looking for a signal which is set by a NAL9 op which is called when the execution completes
                
                ()
            | _ ->
                () // soft internal error - ignore

            ()
        
        ()
    
    // remove strategies which should get deleted
    nal9routine__strategiesInFlight <- nal9routine__strategiesInFlight |> List.filter (fun iv->not iv.flagDeleteMe);

    ()

