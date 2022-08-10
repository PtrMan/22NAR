module PerceiveModule

open Fifo
open GoalSystem
open BeliefMem
open Unifier
open Rules

open VarUtils
open VarIntro
open Term
open TermUtils
open NEvent
open Truth
open Stamp
open Sentence
open SentenceUtils

// module for perception & action

let DBG_level_perception:int = 0; // debug level for perception module

let perceive_dbg_internal (msg:string) =
    if DBG_level_perception > 0 then printfn "DBG: %A" msg;
    ()



type Perceive0 = {
    mutable timeNow: int64; // current time

    goalSystem: GoalMem0; // goal system to use
}

let perceive_create (goalSystem: GoalMem0): Perceive0 =
    {
        timeNow = 0;
        goalSystem = goalSystem;
    }

// does one working step for the perceive system
let perceive_stepInternal0 (perceiveSystem: Perceive0) (beliefMem:BeliefMem0) =

    // * receive new events from FIFO, process them and flush the buffer
    //
    //   we put the events into memory
    for iInputOrDerivedEvent in fifoConclBuffer do
        perceive_dbg_internal (sprintf "perceive_stepInternal0(): perceive sentence = %s" (convSentenceToStr iInputOrDerivedEvent.sentence));

        // try to put it into memory
        let tryPutMem () =
            let term = iInputOrDerivedEvent.sentence.term;
            
            let mutable put = true; // put this into memory?

            match term with
            | Imp (a,c) ->
                // filter: only put in ==> if both sides have same vars!
                perceive_dbg_internal (sprintf "perceive_stepInternal0(): try to put into memory : = %s" (convSentenceToStr iInputOrDerivedEvent.sentence));
                
                // intro vars
                let term2 = termIntroVarDotWhereCnt2 term;

                perceive_dbg_internal (sprintf "perceive_stepInternal0():  after var intro: term = %s" (convTermToStr term2));
                

                // do the variables of A ==> C overlap? 
                let isVarOverlap = match term2 with
                | Imp (a,c) ->
                    let aVars = retExistingVars a;
                    let cVars = retExistingVars c;
                    let isVarOverlap = checkVarOverlap aVars cVars;
                    isVarOverlap
                | _ ->
                    false // internal error when we are here, ignore

                // add it only to memory when variables overlap (when A and C talk about the same variables)
                put <- isVarOverlap;
                perceive_dbg_internal (sprintf "perceive_stepInternal0(): result: put=%A" put);
            ///| PredImp _ ->
            ///    put <- true; // put it into memory by default!
            | _ ->
                ();
            
            if put then
                beliefMem_put beliefMem iInputOrDerivedEvent.sentence perceiveSystem.timeNow;
                ()
            else
                ()
        tryPutMem ();



        // this tries to derive conclusions which can be put into memory
        // TODO ATTENTION< investigate how attention should be allocated here! >
        let tryDerive () =
            let mutable concls: Sentence list = []; // list of conclusions

            for iSubterm in calcConceptualTerms iInputOrDerivedEvent.sentence.term do
                match beliefMem_TryLookupConcept beliefMem iSubterm with
                | Some concept ->
                    // try to derive conclusions
                    
                    // * iterate over beliefs, check for no overlap, try to unify, etc.
                    for iImplBelief in concept.implBeliefs.taskContent do
                        if not (stampCheckOverlap iImplBelief.sentence.stamp iInputOrDerivedEvent.sentence.stamp) then

                            let termA: Term = iInputOrDerivedEvent.sentence.term;
                            let tvA: Truth = iInputOrDerivedEvent.sentence.truth;
                            let termB: Term = iImplBelief.sentence.term;
                            let tvB: Truth = iImplBelief.sentence.truth;

                            let res0 = nal5_conjMatch termA tvA termB tvB;
                            let res1 = nal5_conjMatchAndReduce termA tvA termB tvB;

                            let mutable resCollection: (Term*Truth) list = [];
                            match res0 with
                            | Some x -> resCollection <- x :: resCollection;
                            | None -> ();

                            match res1 with
                            | Some x -> resCollection <- x :: resCollection;
                            | None -> ();

                            // transfer to conclusions
                            for iResTerm, iResTruth in resCollection do
                                let conclSentence: Sentence = sentenceCreate iResTerm iResTruth (stampMerge iInputOrDerivedEvent.sentence.stamp iImplBelief.sentence.stamp) ".";

                                perceive_dbg_internal (sprintf "perceive_stepInternal0(): derive");
                                perceive_dbg_internal (sprintf "perceive_stepInternal0():    premise event  %s" (convSentenceToStr iInputOrDerivedEvent.sentence));
                                perceive_dbg_internal (sprintf "perceive_stepInternal0():    premise belief %s" (convSentenceToStr iImplBelief.sentence));
                                perceive_dbg_internal (sprintf "perceive_stepInternal0():       |- %s" (convSentenceToStr conclSentence));

                                concls <- conclSentence :: concls;

                            ();
                        else
                            ();

                    ();
                | None -> ();
            
            // put conclusions into memory
            for iConcl in concls do
                beliefMem_put beliefMem iConcl perceiveSystem.timeNow;

            ();
        tryDerive ();

        // perceive event from outside in goal system
        goalSystem_perceiveCallback perceiveSystem.goalSystem beliefMem iInputOrDerivedEvent perceiveSystem.timeNow;

        ();

    fifoConclBuffer <- []; // flush


    // * inject events from GoalSystem
    for iEventTermFromGoalSystem in perceiveSystem.goalSystem.outPerceivedEvents do
        let createdSentence: Sentence = sentenceCreate iEventTermFromGoalSystem TRUTH_DEFAULT (stampNew ()) ".";

        let createdEvent: NEvent = {
            minOccTime = perceiveSystem.timeNow; // used for sequences etc. is the time of the first event of a sequence etc. is used for composition
            occTime = perceiveSystem.timeNow;
            sentence = createdSentence;
            isDerived =false; // not derived because it was perceived as if it came from the environment!
        }

        // insert into FIFO as perceived event
        fifoPut fifoLevel0 createdEvent;

    perceiveSystem.goalSystem.outPerceivedEvents <- []; // flush because we processed the queue

    ()

let perceive_advanceTime (perceiveSystem: Perceive0) =
    perceiveSystem.timeNow <- perceiveSystem.timeNow + 1L;

    ()
