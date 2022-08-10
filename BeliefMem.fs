module BeliefMem

open System

open GContainer
open Term
open TermUtils
open Sentence
open SentenceUtils
open Stamp
open Truth
open AttentionDeclarative;

type Belief = {
    mutable sentence: Sentence
    av: DeclAv;
}

type BeliefMemConcept0 = {
    mutable implBeliefs: GContainer<Belief>; // all impl beliefs
    mutable predImplBeliefs: GContainer<Belief>; // all pred impl beliefs
}

// memory for beliefs
type BeliefMem0 = {
    mutable mapToConcepts: Map<Term, BeliefMemConcept0>;

    maxNConcepts:int; // maximal number of concepts stored in memory


    beliefsPerConcept:int; // config
}

let createBeliefMem0 (beliefsPerConcept:int) (maxNConcepts:int): BeliefMem0 =
    {mapToConcepts=Map.empty<Term, BeliefMemConcept0>; maxNConcepts=maxNConcepts; beliefsPerConcept=beliefsPerConcept; }

let beliefMem_TryLookupConcept (mem:BeliefMem0) (key:Term): BeliefMemConcept0 option =
    Map.tryFind key mem.mapToConcepts

let beliefMem_put (mem:BeliefMem0) (sentence:Sentence) (timeNow:int64) =
    for iConceptTerm in calcConceptualTerms sentence.term do // iterate over all concepts which can be adressed by a term!
        // * add concept if it doesn't exist
        if Map.containsKey iConceptTerm mem.mapToConcepts then
            ();
        else
            let sentenceCmpFn a b = a.sentence = b.sentence; // compare function for sentence
            let sentenceRankingFn a = (calcExp a.sentence.truth); // ranking function for sentence

            let createdConcept:BeliefMemConcept0 = {
                implBeliefs=(GContainer_create sentenceCmpFn sentenceRankingFn mem.beliefsPerConcept);
                predImplBeliefs=(GContainer_create sentenceCmpFn sentenceRankingFn mem.beliefsPerConcept);};
            mem.mapToConcepts <- Map.add iConceptTerm createdConcept mem.mapToConcepts;
            ();

        let concept:BeliefMemConcept0 = Map.find iConceptTerm mem.mapToConcepts;

        // helper to update
        let updateHelper (beliefTable:GContainer<Belief>) =
            // try to revise
            let mutable wasRevisionApplied = false;
            let mutable break2 = false;
            for iIdx = 0 to beliefTable.taskContent.Length-1 do
                if not break2 then
                    
                    let iBeliefSentence = beliefTable.taskContent.[iIdx].sentence;

                    if iBeliefSentence.term = sentence.term && not (stampCheckOverlap iBeliefSentence.stamp sentence.stamp) then
                        wasRevisionApplied <- true;
                        break2 <- true;

                        let truth = calcBinaryTruth "revision" sentence.truth iBeliefSentence.truth;
                        let stamp = stampMerge sentence.stamp iBeliefSentence.stamp;

                        let revised: Sentence = sentenceCreate iBeliefSentence.term truth stamp ".";

                        declAv__update_read beliefTable.taskContent.[iIdx].av timeNow;
                        declAv__update_write beliefTable.taskContent.[iIdx].av timeNow;
                        beliefTable.taskContent.[iIdx].sentence <- revised;
                        //beliefTable.taskContent <- List.updateAt iIdx revised beliefTable.taskContent; // OLD CODE
                        ()
                    else
                        ()

            let mutable beliefWithTermExists = false; // does a belief with the term already exist?
            let mutable wasChoiceApplied = false;
            if not wasRevisionApplied then
                // choice rule
                for iIdx = 0 to beliefTable.taskContent.Length-1 do
                    let iBeliefSentence = beliefTable.taskContent.[iIdx].sentence;

                    if iBeliefSentence.term = sentence.term then
                        beliefWithTermExists <- true; // belief with the same term exists already!

                        if (*&& stampCheckOverlap iBeliefSentence.stamp sentence.stamp*) sentence.truth.c >= iBeliefSentence.truth.c then
                            wasChoiceApplied <- true;

                            declAv__update_write beliefTable.taskContent.[iIdx].av timeNow;
                            beliefTable.taskContent.[iIdx].sentence <- sentence; 
                            //beliefTable.taskContent <- List.updateAt iIdx sentence beliefTable.taskContent; // OLD CODE
                            ()
                        else
                            ()
                    else
                        ()

            if not wasChoiceApplied && not beliefWithTermExists && not wasRevisionApplied then
                GContainer_put beliefTable {sentence=sentence;av=(declAv__create timeNow);} |> ignore;
                ()
            else
                ()
        
        match sentence.term with
        | Imp _ ->
            updateHelper concept.implBeliefs; // do update
            ();
        | PredImp _ ->
            updateHelper concept.predImplBeliefs; // do update
            ();
        | _ -> // didn't match a pattern which we are directly supporting
            // just ignore it
            //OUTDATED printfn "SOFT ERROR: beliefMem_put(): called neither for ==> nor for =/>! ignored";
            ();
        
        ()

// return the names of all concepts
// mainly used for debugging
//let beliefMem_retConceptNames (mem:BeliefMem0) =
//    Map.keys mem.mapToConcepts

// print all beliefs to console
let beliefMem_dbg_printAllBeliefs (mem:BeliefMem0) =
    for iKey in Map.keys mem.mapToConcepts do
        printfn "%s" (convTermToStr iKey)

        let iConcept = Map.find iKey mem.mapToConcepts;

        for iBelief in iConcept.implBeliefs.taskContent do
            printfn "   %s" (convSentenceToStr2 iBelief.sentence)
        
        for iBelief in iConcept.predImplBeliefs.taskContent do
            printfn "   %s" (convSentenceToStr2 iBelief.sentence)


// print memory statistics to console
let beliefMem_dbg_printBeliefStats (mem:BeliefMem0) =
    printfn "number of concepts = n_concepts = %i" (Map.keys mem.mapToConcepts |> Seq.length);

