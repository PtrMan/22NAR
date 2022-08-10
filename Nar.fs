module Nar

open System

open NEvent
open Sentence
open SentenceUtils
open Stamp
open Term
open Truth

open Fifo
open GoalSystem
open GoalSystemGc
open PerceiveModule
open BeliefMem
open BeliefMemGc
open GlobalConfig
open TermUtils

let mutable DBG_NAR_VERBOSITY:int = 1; // debug verbosity for NAR stuff

type Nar0 = {
    goalSystem: GoalMem0; // goal system
    perceive: Perceive0; // perception module

    beliefMem: BeliefMem0; // memory for beliefs

    mutable babbleImplList: Babble list; // implementation of used motor babbling

    mutable cycleCounter0: int64;
}

// interface for specific strategy on motor babbling/curiosity/etc.
and Babble =
    abstract member signalBabbleChance : Nar0 -> unit











let nar_sync__inputBelief (nar:Nar0) (belief:Sentence) =
    beliefMem_put nar.beliefMem belief nar.perceive.timeNow

let nar_sync__inputEvent (nar:Nar0) (eventSentence:Sentence) =
    if DBG_NAR_VERBOSITY >= 1 then
        printfn "DBG[1]: NAR: input event=%s" (convSentenceToStr eventSentence);
        ()
    else
        ()
    
    deriver_log__input "IN" eventSentence; // log input

    // NOTE< we only handle non-temporal inputs!, else we would need to know "minOccTime" and "occTime" >
    let event:NEvent = {
        minOccTime=nar.perceive.timeNow; // used for sequences etc. is the time of the first event of a sequence etc. is used for composition
        occTime=nar.perceive.timeNow;
        sentence=eventSentence;
        isDerived=false;
    }

    // insert into FIFO as perceived event
    fifoPut fifoLevel0 event;

let nar_sync__inputGoalEvent (nar:Nar0) (goal:Sentence) =
    goalPut nar.goalSystem goal nar.perceive.timeNow |> ignore;

// syncronous function
let nar_sync__step (nar:Nar0) =
    goalSystem__beforeExecBestOp nar.goalSystem nar.perceive.timeNow;
    goalSystem_execBestOp nar.goalSystem nar.beliefMem nar.perceive.timeNow;

    fifo_giveResource (); // give compute to FIFO


    perceive_stepInternal0 nar.perceive nar.beliefMem; // give compute to the perception
    
    goalSystem_deriveStep nar.goalSystem nar.beliefMem nar.perceive.timeNow; // give compute to the goal system

    goalSystem_doWorker0 nar.goalSystem; // give compute to goal system

    // do keep belief memory keep under AIKR
    if (nar.cycleCounter0 % 51L) = 0L then
        beliefMemGc_do nar.beliefMem nar.perceive.timeNow;
        ()

    // do keep goal memory keep under AIKR
    if (nar.cycleCounter0 % 101L) = 0L then
        goalSystemGc_do nar.goalSystem nar.perceive.timeNow;
        ()
    
    nar.cycleCounter0 <- nar.cycleCounter0 + 1L;

    ()

let nar_sync__advanceTime (nar:Nar0) =
    for iBabbleImpl in nar.babbleImplList do
        iBabbleImpl.signalBabbleChance nar;

    perceive_advanceTime nar.perceive;

    // we need to eventually allocate new buckets and keep it under AIKR
    fifo_advanceTime fifoLevel0 nar.perceive.timeNow;
    fifo_advanceTime fifoLevel1 nar.perceive.timeNow;






type SimpleMotorBabbling(chancePerCycle:float) =  
    interface Babble with
        member this.signalBabbleChance (nar:Nar0) =
            let rng = new Random();
            if rng.NextDouble() < chancePerCycle then
                let opsAsList = Map.toList nar.goalSystem.registeredOps;
                if opsAsList.Length > 0 then
                    let selIdx:int = rng.Next(opsAsList.Length);
                    let selOpName, selfOpData = opsAsList.[selIdx];

                    
                    // * invoke selected op by adding goal event now
                    let goalTerm: Term = Inh ((SetExt [Prod [SetExt [Word "SELF"]; Word "dummy0"]]), (Word selOpName));
                    let goal: Sentence = sentenceCreate goalTerm TRUTH_DEFAULT (stampNew ()) "!";

                    printfn "DBG: babble.simple: babble op= %s" selOpName;
                    nar_sync__inputGoalEvent nar goal;

                    ();
                else
                    ();
            else
                ();



// implementation of non-goal driven artificial curiosity
type CuriosityMotorBabbling(chancePerCycle: float) =
    interface Babble with
        member this.signalBabbleChance (nar:Nar0) =
            let rng = new Random();
            if rng.NextDouble() < chancePerCycle then
                let events: NEvent list = fifo_viewAsSeq ();
                if events.Length > 0 then
                    let currentEvent: NEvent = events.[0];

                    // * lookup beliefs of currentEvent=C   <(C,^X) =/> D>.
                    let mutable candidates: Sentence list = [];

                    match (Map.tryFind currentEvent.sentence.term nar.beliefMem.mapToConcepts) with
                    | Some selConcept ->
                        for iBelief in selConcept.predImplBeliefs.taskContent do
                            // filter for correct pred impl
                            match iBelief.sentence.term with
                            | PredImp (s,p) ->
                                match s with
                                | Seq seqItems ->
                                    if seqItems.[0] = currentEvent.sentence.term then
                                        candidates <- iBelief.sentence ::candidates;
                                | _ ->
                                    ()
                            | _ ->
                                ()
                    | None ->
                        ()
                    
                    printfn "DBG:babble.curiosity current event term=%s" (convTermToStr currentEvent.sentence.term);
                    printfn "DBG:babble.curiosity list of possible babbable contingencies:";
                    for iCandidate in candidates do
                        printfn "DBG: babble.curiosity candidateSentence=%s" (convSentenceToStr iCandidate);

                    // * decide on which stuff to babble best (by op)
                    // TODO TODO TODO TODO TODO TODO
                    // TODO TODO TODO TODO TODO TODO
                    // TODO TODO TODO TODO TODO TODO
                    // TODO TODO TODO TODO TODO TODO
                    // TODO TODO TODO TODO TODO TODO
                    // TODO TODO TODO TODO TODO TODO
                    
                    ()
    




let nar_create (maxNConcepts:int): Nar0 =
    let CONFIG_goalsPerConcept = 20; // TODO< we need to let it get configured from the outside >
    let CONFIG_beliefsPerConcept = 20; // TODO< we need to let it get configured from the outside >
    //let CONFIG_maxNConcepts = 100; // TODO< we need to let it get configured from the outside >

    let beliefMem = createBeliefMem0 CONFIG_beliefsPerConcept maxNConcepts;
    let goalSystem = createGoalMem0 CONFIG_goalsPerConcept;
    let perceive = perceive_create goalSystem;

    // HACK< we init the FIFO again, is a HACK because the FIFO shouldn't be global! >
    fifoInit_internal fifoLevel0;
    fifoInit_internal fifoLevel1;

    {
        goalSystem = goalSystem;
        perceive = perceive;
        beliefMem = beliefMem;

        babbleImplList = [new SimpleMotorBabbling(0.1)]; // use simple motor babbling by default

        cycleCounter0 = 0L;
    }