module BeliefMemGc

open BeliefMem
open Sentence
open Truth
open TermUtils
open SentenceUtils
open AttentionDeclarative
open DebugUtils

let mutable beliefMemGc_debugVerbosity: int = 0;



// helper to emit log
let beliefMemGc__dbgLog2 (en:bool) (level:int) (msg:string) =
    dbgLog3 "beliefMem.gc" en level msg; 

// helper to emit log
let beliefMemGc__dbgLog (level:int) (msg:string) =
    beliefMemGc__dbgLog2 (level <= beliefMemGc_debugVerbosity) level msg;



// "garbage collector" for concepts of belief memory to keep memory and thus the system under AIR

let beliefMemGc_do (mem:BeliefMem0) (currTime:int64) =
    // function to calculate score
    // HACK< really basic and simple formulas >
    let calcScoreImpl (iBelief:Belief) = iBelief.sentence.truth.c*1.0* (declAv__calcUsage iBelief.av currTime)
    let calcScorePredImpl (iBelief:Belief) = (calcExp iBelief.sentence.truth)*1.0* (declAv__calcUsage iBelief.av currTime)

    // store a snapshot of all keys of the concept, this needs to be SYNCRONOUS
    let keys2 = mem.mapToConcepts.Keys;

    // now we can compute the usefulness of each concept in parallel
    // TODO< compute parallel and independent of main-thread >
    let mutable scoreOfConcept = [];
    for iKey in keys2 do
        let iConcept = mem.mapToConcepts.[iKey];

        let mutable maxScore = 0.0;

        beliefMemGc__dbgLog 5 (sprintf "beliefMem.gc: GC for concept=%s" (convTermToStr iKey));

        for iBelief in iConcept.implBeliefs.taskContent do
            let score = calcScoreImpl iBelief;
            beliefMemGc__dbgLog 5 (sprintf " belief=%s score=%f" (convSentenceToStr iBelief.sentence) score);
            maxScore <- max maxScore score;
            ()
        
        for iBelief in iConcept.predImplBeliefs.taskContent do
            let score = calcScorePredImpl iBelief;
            beliefMemGc__dbgLog 5 (sprintf " belief=%s score=%f" (convSentenceToStr iBelief.sentence) score);
            maxScore <- max maxScore score;
            ()
        
        scoreOfConcept <- (iKey,maxScore) :: scoreOfConcept; // store the score of this concept
        ()
    
    // sort by importance
    let sortedScoreOfConcept = List.sortByDescending (fun (iKey, iScore) -> iScore) scoreOfConcept;

    // DEBUG score of concepts
    for iKey, iScore in sortedScoreOfConcept do
        beliefMemGc__dbgLog 2 (sprintf "concept=%s  score=%f" (convTermToStr iKey) iScore);
        ()


    // now we remove the concepts which have a to low score and take up to much memory (approximated by the whole concept)
    let removeKeysList = 
        if sortedScoreOfConcept.Length > mem.maxNConcepts then 
            List.removeManyAt 0 mem.maxNConcepts sortedScoreOfConcept |> List.map (fun (iKey, iScore) -> iKey)
        else
            []

    // TODO< do this in parallel while the other processes are running >
    for iKey in removeKeysList do
        beliefMemGc__dbgLog 2 (sprintf "remove concept=%s" (convTermToStr iKey));
        mem.mapToConcepts <- Map.remove iKey mem.mapToConcepts;

    ()
