module AutoTestMontezumaA

open System

open Nar
open Term
open Sentence
open GoalSystem
open Truth
open Stamp
open TermUtils
open GlobalConfig
open BeliefMem

open EnvMontezumaA
open NarHelpers
open Vec2i



let AutoTestMontezumaA__run () =
    DBG_LOGDERIVER <- true; // show derivations

    // higher confidence for faster learning, maybe that's a problem
    ANTICIPATION_POS_CONF <- 0.08*4.0;
    ANTICIPATION_NEG_CONF <- 0.06*4.0;


    let mutable AUTOTEST_MONTEZUMA_EPISODES:int = 50; // number of tested episodes per run
    AUTOTEST_MONTEZUMA_EPISODES <- 120;
    AUTOTEST_MONTEZUMA_EPISODES <- 1;
    


    let mutable env: EnvMontezuma = {
        agent = {pos={x=3;y=3};};
        objs = [];
        eventPickedUpKey=false;
        backgroundTiles=[];
        backgroundTilesWidth=0;
        backgroundTilesHeight=0;
    }


    let maxNConcepts = 6000;
    let mutable nar:Nar0 = nar_create maxNConcepts;


    let mutable wasAnyOpCalled = false;

    
    let op1:RegisteredOp = {
        callable=(fun goalSystem args ->
            printfn "^l WAS CALLED!"

            wasAnyOpCalled <- true;

            envMontezuma__agentTryMove env env.agent {x=(-1);y=0;}; 
        );
    }
    nar.goalSystem.registeredOps <- Map.add "^l" op1 nar.goalSystem.registeredOps;

    let op2:RegisteredOp = {
        callable=(fun goalSystem args ->
            printfn "^r WAS CALLED!"

            wasAnyOpCalled <- true;

            envMontezuma__agentTryMove env env.agent {x=1;y=0;};
        );
    }
    nar.goalSystem.registeredOps <- Map.add "^r" op2 nar.goalSystem.registeredOps;
    


    


    //let mutable envStatAccu_timeTillKeyPickedUp: int option  list = [];






    // compute encoding of relative distance
    let convRelToStringEncoding (relX:int) (relY:int): string =
        match (relX,relY) with
        | ( 0, 0) -> "cc"
        | (-1, 0) -> "nc"
        | ( 1, 0) -> "pc"
        | ( 0, 1) -> "cp"
        | ( 1, 1) -> "pp"
        | (-1, 1) -> "np"
        | ( 0,-1) -> "cn"
        | ( 1,-1) -> "pn"
        | (-1,-1) -> "nn"





    // simulation loop
    for iEpoch=0 to AUTOTEST_MONTEZUMA_EPISODES do // iterate over learning epochs

        // reset environment
        env <- {
            agent = {pos={x=3;y=5};};
            objs=[{type_=KEY;pos={x=4;y=4};isActivated=false;}];
            eventPickedUpKey=false;
            backgroundTiles=[];
            backgroundTilesWidth=0;
            backgroundTilesHeight=0;
        }
        envMontezuma__envAlloc env 12 12;

        envMontezuma__envWriteTile env 2 4 {type_=FULLGROUND};
        envMontezuma__envWriteTile env 2 4 {type_=FULLGROUND};

        envMontezuma__envWriteTile env 5 0 {type_=FULLGROUND};
        envMontezuma__envWriteTile env 5 8 {type_=FULLGROUND};

        envMontezuma__envWriteTile env 6 0 {type_=FULLGROUND};
        envMontezuma__envWriteTile env 6 1 {type_=FULLGROUND};
        envMontezuma__envWriteTile env 6 2 {type_=FULLGROUND};
        envMontezuma__envWriteTile env 6 3 {type_=FULLGROUND};
        envMontezuma__envWriteTile env 6 4 {type_=FULLGROUND};
        envMontezuma__envWriteTile env 6 5 {type_=FULLGROUND};
        envMontezuma__envWriteTile env 6 6 {type_=FULLGROUND};
        envMontezuma__envWriteTile env 6 7 {type_=FULLGROUND};
        envMontezuma__envWriteTile env 6 8 {type_=FULLGROUND};

        envMontezuma__envWriteTile env 5 4 {type_=LADDER}; // LADDER



        let mutable envStat_timeTillKeyPickedUp: int option = None; // time till the first key was picked up - is a statistic


        let mutable maxCycles = 400;

        for iEnvCycle=1 to maxCycles do // iterate over environment cycles
            printfn "ENV iEpoch=%i iEnvCycle=%i" iEpoch iEnvCycle;





            // perception of environment
            let mutable closestKeyTerm: Term = Inh (SetExt [Word "NONE"], Word "objKey");

            let projectedObjs = envMontezuma__agentProjectByAgent env;
            for iProjObj in projectedObjs do
                let convIntToNarseseStr (v:int): string =
                    let s = sprintf "%i" v
                    s.Replace("-", "M")

                let posAsTermStr:string = sprintf "%sQ%s" (convIntToNarseseStr iProjObj.pos.x) (convIntToNarseseStr iProjObj.pos.y);


                let term:Term = 
                    match iProjObj.type_ with
                    | KEY -> Inh ((SetExt [Word posAsTermStr]), (Word "objKey"));
                closestKeyTerm <- term; // assign    NOTE< we assume that there is only one key present in the world!!! >

                (* commented because this is the way how we perceive the object, but we still can't do this like that because the perception of NAR can't build "parallel conjunction" from events
                let s0:Sentence = {
                    term=term;
                    truth=TRUTH_DEFAULT;
                    stamp=stampNew ();
                    punctation=".";
                }
                
                nar_sync__inputEvent nar s0;
                *)
                
                ()
                

            // we compute the closest ladder to give the agent the information
            let mutable closestLadderTerm: Term = Inh (SetExt [Word "NONE"], Word "ladder");

            let closestLadderTupleOpt: (EnvMzTile*Vec2i) option = envMontezuma__envCalcClosestLadder env env.agent.pos  6; // in range 6
            match closestLadderTupleOpt with
            | Some (ladderObj,relativeDistance) -> // found a closest ladder

                let mutable relYAbs:int = 0;
                if relativeDistance.y < 0 then
                    relYAbs <- -1;
                if relativeDistance.y > 0 then
                    relYAbs <- 1;

                let mutable relXAbs:int = 0;
                if relativeDistance.x < 0 then
                    relXAbs <- -1;
                if relativeDistance.x > 0 then
                    relXAbs <- 1;
                
                let relDistEncodingStr: string = convRelToStringEncoding relXAbs relYAbs;
                
                // encode it as a term
                closestLadderTerm <- Inh (SetExt [Word relDistEncodingStr], Word "ladder");

                ()
            | None ->
                ()
            


            // closest key



            let mutable perceptConcurrentTerms: Term list = []; // list of concurrently happening terms
            perceptConcurrentTerms <- closestLadderTerm::perceptConcurrentTerms;
            perceptConcurrentTerms <- closestKeyTerm::perceptConcurrentTerms;


            // actual perceive
            let perceivedTerm: Term = Par perceptConcurrentTerms;
            let s0:Sentence = sentenceCreate perceivedTerm TRUTH_DEFAULT (stampNew ()) ".";
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
            envMontezuma__timestep env;


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







            // debug env state
            envMontezuma__debugState env;

            printfn "env perceived term=%s" (convTermToStr perceivedTerm);







    printfn "DBG: beliefs:";
    beliefMem_dbg_printAllBeliefs nar.beliefMem;

    // debug all goals
    if false then
        printfn "";
        printfn "";
        printfn "";
        goalSystem_printAll nar.goalSystem;
    
    
