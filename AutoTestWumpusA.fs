module AutoTestWumpusA

// automated test for a wumpus like world

open EnvWumpusA
//open SpatialModule // commented because it is planed but not yet used!

open Nar
open NarHelpers
open Sentence
open GoalSystem
open BeliefMem
open Term
open Stamp
open Truth
open Fifo



let AutoTestWumpusA__run () =
    // higher confidence for faster learning, maybe that's a problem
    ANTICIPATION_POS_CONF <- 0.08*4.0;
    ANTICIPATION_NEG_CONF <- 0.06*4.0;

    //GOALSYS_EN_GOALDRIVEN_CURIOSITY <- true; // enable EXPERIMENTAL FEATURE: goal driven curiosity
    GOALSYS__GOALDRIVEN_CURIOSITY__BABBLE_PROB <- 0.2;

    //DBG_FIFO_VERBOSITY <- 2; // enable debug of FIFO
    //DBG_GOALSYS_VERBOSITY <- 2; // enable debug of Goalsystem
    //DBG_GOALSYS_KILL <- 2;

    let mutable AUTOTEST_WUMPUS_EPISODES:int = 50; // number of tested episodes per run
    //AUTOTEST_WUMPUS_EPISODES <- 120;
    AUTOTEST_WUMPUS_EPISODES <- 120;

    let mutable env: EnvWumpus = {
        objs = [];
        agent = {pos={x=3;y=3};dir=0;};
        nKeys=0;
        eventPickedUpKey=false;
        wallBitmap=[];
        wallBitmapWidth=0;
        wallBitmapHeight=0;
    }


    let maxNConcepts = 3000;
    let mutable nar:Nar0 = nar_create maxNConcepts;


    let mutable wasAnyOpCalled = false;

    
    let op1:RegisteredOp = {
        callable=(fun goalSystem args ->
            printfn "^rotL WAS CALLED!"

            wasAnyOpCalled <- true;

            wumpus__worldAgentDoRotate env.agent LEFT;
        );
    }
    nar.goalSystem.registeredOps <- Map.add "^rotL" op1 nar.goalSystem.registeredOps;

    let op2:RegisteredOp = {
        callable=(fun goalSystem args ->
            printfn "^rotR WAS CALLED!"

            wasAnyOpCalled <- true;

            wumpus__worldAgentDoRotate env.agent RIGHT;
        );
    }
    nar.goalSystem.registeredOps <- Map.add "^rotR" op2 nar.goalSystem.registeredOps;
    


    
    let op3:RegisteredOp = {
        callable=(fun goalSystem args ->
            printfn "^f WAS CALLED!"

            wasAnyOpCalled <- true;

            wumpus__worldAgentMoveForward env env.agent;
        );
    }
    nar.goalSystem.registeredOps <- Map.add "^f" op3 nar.goalSystem.registeredOps;



    nar.babbleImplList <- (CuriosityMotorBabbling 0.2)  ::nar.babbleImplList; // add non-goal driven curiosity





    let mutable envStatAccu_timeTillKeyPickedUp: int option  list = [];

    // simulation loop
    for iEpoch=0 to AUTOTEST_WUMPUS_EPISODES do // iterate over learning epochs

        // reset environment
        env <- {
            objs = [{type_=KEY;pos={x=3;y=5};isActivated=false;}];
            agent = {pos={x=3;y=3};dir=1;};
            nKeys=0;
            eventPickedUpKey=false;
            wallBitmap=[];
            wallBitmapWidth=0;
            wallBitmapHeight=0;
        }
        wumpus__envWallAlloc env 12 12;
        wumpus__envWriteWall env 2 4 true;
        wumpus__envWriteWall env 3 4 true;
        wumpus__envWriteWall env 4 4 true;
        wumpus__envWriteWall env 5 4 true;
        wumpus__envWriteWall env 6 4 true;

        wumpus__envWriteWall env 2 2 true;
        wumpus__envWriteWall env 3 2 true;
        wumpus__envWriteWall env 4 2 true;
        wumpus__envWriteWall env 5 2 true;
        wumpus__envWriteWall env 6 2 true;

        wumpus__envWriteWall env 6 3 true;
        wumpus__envWriteWall env 2 3 true;



        let mutable envStat_timeTillKeyPickedUp: int option = None; // time till the first key was picked up - is a statistic

        let mutable maxCycles = 140;

        for iEnvCycle=1 to maxCycles do // iterate over environment cycles
            printfn "ENV iEpoch=%i iEnvCycle=%i" iEpoch iEnvCycle;



            // perception of environment
            let projectedObjs = wumpus__projectByAgent env;
            for iProjObj in projectedObjs do
                let convIntToNarseseStr (v:int): string =
                    let s = sprintf "%i" v
                    s.Replace("-", "M")
                
                let posAsTermStr:string = sprintf "%sQ%s" (convIntToNarseseStr iProjObj.pos.x) (convIntToNarseseStr iProjObj.pos.y);

                let term:Term = 
                    match iProjObj.type_ with
                    | KEY -> Inh ((SetExt [Word posAsTermStr]), (Word "objKey"));
                    | CLOSEDDOOR -> Inh ((SetExt [Word posAsTermStr]), (Word "objClosedDoor"));
                
                let s0:Sentence = sentenceCreate term TRUTH_DEFAULT (stampNew ()) ".";
                nar_sync__inputEvent nar s0;


            nar_helper__inputGoalEventTermName nar "K"; // must grab key


            wasAnyOpCalled <- false;

            // give NAR cycles
            for it=1 to 5 do
                nar_sync__advanceTime nar;
            
            for iNarStep=1 to 1 do
                nar_sync__step nar;

            nar_sync__advanceTime nar; // need this to get rid of environment events which happen at the same time as events from execution of ops


            // handle environment interactions
            envCheck env;

            if env.eventPickedUpKey then
                printfn "ENV KEY was picked up!";


                // track statistic
                if not envStat_timeTillKeyPickedUp.IsSome then
                    envStat_timeTillKeyPickedUp <- Some iEnvCycle;
                    ()
                else
                    ()


                // notify agent that key was picked up

                let s0: Sentence = sentenceCreate (Word "K") TRUTH_DEFAULT (stampNew ()) ".";
                nar_sync__inputEvent nar s0;

                ()
            else
                ()


            // print visualization of environment
            printfn "ENV iEpoch=%i iEnvCycle=%i state ASCII:" iEpoch iEnvCycle;
            let linesAscii = envPrintAscii env;
            for iLine in linesAscii do
                printfn "%s" iLine;
        

        envStatAccu_timeTillKeyPickedUp <- envStat_timeTillKeyPickedUp :: envStatAccu_timeTillKeyPickedUp;


    printfn "ENV stat.time till key was first picked up:";
    for ivOpt in envStatAccu_timeTillKeyPickedUp do
        let str = match ivOpt with
            | Some iv -> (sprintf "%i" iv)
            | None -> "-"
        
        printfn "%s" str;

    // compute score
    let mutable score = 0.0;
    for ivOpt in envStatAccu_timeTillKeyPickedUp do
        match ivOpt with
            | Some iv ->
                score <- score + (exp (-0.08*((float)iv)));
                ()
            | None -> ()
    
    printfn "ENV score.episodesAvg=%f" (score / (float AUTOTEST_WUMPUS_EPISODES));


    
    printfn "DBG: beliefs:";
    beliefMem_dbg_printAllBeliefs nar.beliefMem;

    // debug all goals
    printfn "";
    printfn "";
    printfn "";
    if true then
        goalSystem_printAll nar.goalSystem;
        ()
    else
        ()



