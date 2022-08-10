module ManualTestNarDeriver_concludeFromImpl

open Sentence
open Truth
open Term
open TermUtils // for debugging
open Stamp

open BeliefMem // for debugging
open GoalSystem // for debugging
open Nar

open ManualDebugHelper


// manual test to see if the deriver derives the correct conclusions from a given belief and input events
// UUT is Nar

let manualTest_narDeriver_concludeFromImpl_0 () =
    
    let mutable nar:Nar0 = nar_create 300;
    nar.babbleImplList <- [SimpleMotorBabbling 0.0]; // disable motor babbling

    let mutable opWasCalled_say = false;
    let mutable opWasCalledAnytime_say = false;

    // register op
    let op0:RegisteredOp = {
        callable=(fun goalSystem args ->
            printfn "DBG[0]: OP ^say WAS CALLED!";
            opWasCalled_say <- true;
            ());
    }
    nar.goalSystem.registeredOps <- Map.add "^say" op0 nar.goalSystem.registeredOps;




    // add belief
    let op0Term:Term = Inh ((SetExt [   Prod [SetExt [Word "SELF"]; (Word "c")]    ]), (Word "^say"));
    let belief0: Sentence = sentenceCreate (Imp (And [Seq [UVar 0; Word "is"; UVar 1]; Seq [UVar 1; Word "is"; Word "c"]],    PredImp (Seq [UVar 0; Word "is"; op0Term], Word "G"))) TRUTH_DEFAULT (stampNew ()) ".";
    nar_sync__inputBelief nar belief0;

    nar_sync__step nar;
    nar_sync__advanceTime nar;


    // input events of sequence "a is b"
    manualDebugHelper_playbackEvents nar [Word "a"; Word "is"; Word "b"];

    // pause
    for i=1 to 3 do
        nar_sync__step nar;
        nar_sync__advanceTime nar;

    // input events of sequence "b is c"
    manualDebugHelper_playbackEvents nar [Word "b"; Word "is"; Word "c"];


    // add goal
    let goal0: Sentence = sentenceCreate (Word "G") TRUTH_DEFAULT (stampNew ()) "!";
    nar_sync__inputGoalEvent nar goal0;

    // give way more resources
    for i=1 to 50 do
        nar_sync__step nar;
    

    // test if NAR can derive the correct action

    printfn "SECTION: test";

    manualDebugHelper_playbackEvents nar [Word "a"; Word "is"];
    



    // wait for execution of goal
    for i=1 to 50 do

        nar_sync__step nar;

        if opWasCalled_say then
            opWasCalledAnytime_say <- true;
            
            // inject G
            let s0:Sentence = sentenceCreate (Word "G") TRUTH_DEFAULT (stampNew ()) ".";
            nar_sync__inputEvent nar s0 |> ignore;

            ()
        else
            ()
        
        opWasCalled_say <- false;

        ()
    
    
    // expect execution of op
    printfn "DBG: ^say was called = %b" opWasCalledAnytime_say;


    // debug if it has derived the intended conclusion
    printfn "DBG: beliefs:";
    beliefMem_dbg_printAllBeliefs nar.beliefMem;

    printfn "DBG: memory belief stats:";
    beliefMem_dbg_printBeliefStats nar.beliefMem;



    printfn "DBG: goals:";
    goalSystem_printAll nar.goalSystem;



    ()
