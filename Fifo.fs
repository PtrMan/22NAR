module Fifo

open System

open Stamp
open Term
open Sentence
open SentenceUtils
open Truth
open NEvent
open Rules
open GoalSystemUtils
open DebugUtils
open GlobalConfig

let mutable DBG_FIFO_VERBOSITY:int = 0; // debug verbosity for FIFO stuff

// helper to emit log
let fifo__dbgLog2 (en:bool) (level:int) (msg:string) =
    dbgLog3 "FIFO" en level msg; 


// helper to emit log
let fifo_dbgLog (level:int) (msg:string) =
    fifo__dbgLog2 (level <= DBG_FIFO_VERBOSITY) level msg;

let mutable FIFO_BUILD_IMPL:bool = false; // enable !!!EXPERIMENTAL!!! building of implications?


// checks if the predictive implication is valid
let checkIsValidPredImpl (term:Term): bool =
    match term with
    | PredImp (s,p) ->
        if not (checkIsOp p) then
            match s with
            | Seq seq -> not (checkIsOp seq.[0]) // is not valid if first is op
            | _ -> not (checkIsOp s) // is not valid if subject is op!
        else
            false // is not valid if predicate is op!
    | _ ->
        printfn "WARN: checkIsValidPredImpl() called for non- =/> !";
        false // is not a predictive implication and thus not valid

// tries to combine two events to a predictive implication
let temporalCombineAsPredImpl a b maxDt: NEvent option =
    if stampCheckOverlap a.sentence.stamp b.sentence.stamp then
        None
    else if checkIsOp b.sentence.term then
        None // because building <BLA =/> ^OP> is not valid! because it leads to nonsense
    else
        let dt = b.occTime - a.occTime

        if dt > 0 && dt < maxDt then
            let tv:Truth = calcBinaryTruth "induction" a.sentence.truth b.sentence.truth;
            let concl: Sentence = sentenceCreate (PredImp (a.sentence.term, b.sentence.term)) tv (stampMerge a.sentence.stamp b.sentence.stamp) ".";
            deriver_log__derivation [a.sentence;b.sentence] concl "nal7predImpl";

            Some {minOccTime = a.minOccTime; occTime = b.occTime; sentence = concl; isDerived=true;}
        else
            None


// tries to combine events to sequence
let temporalCombineAsSeqV2 (events: NEvent list) maxDt: NEvent option =
    let mutable conclTruth = events.Head.sentence.truth;
    let mutable conclStamp = events.Head.sentence.stamp;
    let mutable anyOverlap = false;
    for iEvent in events.Tail do
        anyOverlap <- anyOverlap || (stampCheckOverlap conclStamp iEvent.sentence.stamp);
        conclStamp <- stampMerge conclStamp iEvent.sentence.stamp;
        conclTruth <- calcBinaryTruth "intersection" conclTruth iEvent.sentence.truth;
    
    if anyOverlap then
        None // no conclusion because overlap
    else
        let lastEventOccTime = events.[events.Length-1].occTime;
        let dt = lastEventOccTime - events.Head.occTime;

        if dt > -maxDt then
            let concl: Sentence = sentenceCreate (Seq (List.map (fun iv -> iv.sentence.term) events)) conclTruth conclStamp ".";
            deriver_log__derivation (events |> List.map (fun iv->iv.sentence)) concl "nal7seq";

            Some {minOccTime = events.Head.minOccTime; occTime = lastEventOccTime; sentence = concl; isDerived=true;}
        else
            None

let combineAsImpl (a:NEvent) (b:NEvent): NEvent option =
    if stampCheckOverlap a.sentence.stamp b.sentence.stamp then
        None
    else
        // TODO< compute truth >
        let concl: Sentence = sentenceCreate (Imp (a.sentence.term, b.sentence.term)) TRUTH_DEFAULT (stampMerge a.sentence.stamp b.sentence.stamp) ".";
        deriver_log__derivation [a.sentence;b.sentence] concl "nal6impl";

        Some {minOccTime = a.minOccTime; occTime = b.occTime; sentence = concl; isDerived=true;}


// events with roughtly the same occurence time in a bucket of the FIFO
type Fifo0Bucket = {
    mutable events : NEvent list;  
    minTime : int64; // minimal time that the events can get put into this bucket
}


// the actual FIFO datastructure
type Fifo0 = {
    //let mutable prop : string = null 
    mutable buckets : Fifo0Bucket list;// = Array.empty  
    bucketSpan : int64; // timespan of the time of each bucket

    maxBuckets: int; // maximal count of buckets - to keep under AIKR
}

type Collector0 = {
    mutable map: Map<string, NEvent>;
    mutable col: NEvent list;
}

let mutable CONFIG_fifomaxbuckets = 15;
let mutable CONFIG_fifo_debugPut = true; // debug put into FIFO of derived conclusions
let mutable fifoLevel0:Fifo0 = {buckets = []; bucketSpan=8; maxBuckets=CONFIG_fifomaxbuckets;}; // only raw events
let mutable fifoLevel1:Fifo0 = {buckets = []; bucketSpan=8; maxBuckets=CONFIG_fifomaxbuckets;}; // only sequences built from raw events
let mutable predImplCollector: Collector0 = { map = Map.empty<string, NEvent>; col = [] }; // collector for predictive implications
let mutable implCollector: Collector0 = { map = Map.empty<string, NEvent>; col = [] }; // collector for implications

// buffer for derived events derived by the FIFO to put into the consumer of the FIFO output
let mutable fifoConclBuffer:NEvent list = [];


// helper to initialize FIFO
let fifoInit_internal (fifo:Fifo0) =
    fifo.buckets <- [{events = [];minTime=0;}]

// advance time in FIFO
let fifo_advanceTime (fifo:Fifo0) (currentTime:int64) =
    // * we eventually need to allocate new buckets and remove old buckets to keep under AIKR
    // ** advance buckets
    if currentTime >= fifo.buckets.[0].minTime + fifo.bucketSpan then // note< last item >
        let createdBucket: Fifo0Bucket = {
            events = [];
            minTime = fifo.buckets.[0].minTime + fifo.bucketSpan;
        }
        fifo.buckets <- createdBucket :: fifo.buckets;
    else
        ();

    // ** keep under AIKR
    if fifo.buckets.Length > fifo.maxBuckets then
        fifo.buckets <- List.removeAt (fifo.buckets.Length-1) fifo.buckets; // remove last bucket
    else
        ();



// put a event into the FIFO
let fifoPut (fifo:Fifo0) (event:NEvent) =
    // debug if it was derived
    if event.isDerived && CONFIG_fifo_debugPut then
        fifo_dbgLog 1 (sprintf "FIFO put|- %s" (convSentenceToStr event.sentence));
        ()
    else
        ()

    // we put it into the buffer too because it was either perceived or derived by the FIFO
    fifoConclBuffer <- event :: fifoConclBuffer;

    //printfn "DBG:verbose=1: FIFO: hereA";
    let minTime = fifo.buckets.[fifo.buckets.Length-1].minTime; // min time of first bucket
    //printfn "DBG:verbose=1: %A" fifo.buckets;
    //printfn "DBG:verbose=1: FIFO: hereB";

    //printfn "%A %A" event.occTime minTime; // DBG
    
    if event.occTime < minTime then // is the event happening before the smallest time captured by the FIFO?
        None // ignore
    else
        let bucketIdx = int((event.occTime - minTime) / fifo.bucketSpan); // compute index of bucket where we have to put event into
        
        //printfn "DBG:verbose=1: FIFO: hereC";
        //printfn "                     bucketIdx=%i" bucketIdx;
        //printfn "                     len      =%i" fifo.buckets.Length;
        let bucketIdx2 = (fifo.buckets.Length-1) - int(bucketIdx); // bucket index from back
        fifo.buckets.[bucketIdx2].events <- (event :: fifo.buckets.[bucketIdx2].events); // append event to FIFO
        //printfn "DBG:verbose=1: FIFO: hereD";

        None

// helper
// returns the events in the bucket of the queryEvent and the events before that (currently the bucket before)
let fifoQueryBucketNPlusOffset (fifo:Fifo0) (queryEvent:NEvent) (offset:int) =
    let minTime = fifo.buckets.[fifo.buckets.Length-1].minTime; // min time of first bucket
    let bucketIdx = (queryEvent.occTime - minTime) / fifo.bucketSpan; // compute index of bucket

    // accumulator of events: we want to have all the events of this bucket
    //printfn "DBG99 %i %i %i" queryEvent.occTime minTime (int(bucketIdx)); // debugging for finding bug
    let mutable acc =
        // 05.06.2022: hacky way to circument a crash when the index is negative for some reason
        if int(bucketIdx)>=0 then
            fifo.buckets.[int(bucketIdx)].events
        else
            []


    if int(bucketIdx) + offset >= 0 && int(bucketIdx) + offset < fifo.buckets.Length then
        // and the bucket before
        acc <- fifo.buckets.[int(bucketIdx) + offset].events @ acc;
        None
    else
        None
    |> ignore

    acc

// select events which follow each other
let fifoSelFollowing (fifo:Fifo0): NEvent list = 
    let mutable events = []; // all events
    for iBucket in fifo.buckets do
        events <- iBucket.events @ events;


    let objRandom = new Random();
    
    let selLen = if objRandom.Next(2) = 1 then 2 else 3; // length of sequence

    if events.Length >= selLen then
        let startIdx: int = objRandom.Next(events.Length-selLen);
        
        events
        |> List.skip startIdx |> List.take selLen // select sub-range
        |> List.rev // reverse because else the order is reversed which is wrong!
    else
        [] // we can't return any sequence!



// returns the events before the queryEvent
let fifoBeforeAsMultiple (fifo:Fifo0) (queryEvent:NEvent) =
    let candidateEvents = fifoQueryBucketNPlusOffset fifo queryEvent -1;

    // filter by time occuring before the "queryEvent"
    candidateEvents |> List.filter (fun iv -> iv.occTime < queryEvent.minOccTime)

let fifoBeforeAsSingle (fifo:Fifo0) (queryEvent:NEvent) =
    let candidateEvents = fifoBeforeAsMultiple fifo queryEvent;
    
    (* this version only selects the first event which is bad for sampling!
    let sortedEvents = List.sortBy (fun iv -> iv.occTime) candidateEvents;

    if sortedEvents.Length > 0 then
        Some sortedEvents.Head
    else
        None
    *)

    if candidateEvents.Length > 0 then
        let objrandom = new Random();
        let selIdx = objrandom.Next(candidateEvents.Length);
        let selEvent = candidateEvents.[selIdx];
        Some selEvent
    else
        None


// returns the events after the queryEvent
let fifoAfterAsMultiple (fifo:Fifo0) (queryEvent:NEvent) =
    let candidateEvents = fifoQueryBucketNPlusOffset fifo queryEvent 1;

    // filter by time occuring after the "queryEvent"
    candidateEvents |> List.filter (fun iv -> iv.occTime > queryEvent.occTime)

let fifoAfterAsSingle (fifo:Fifo0) (queryEvent:NEvent) =
    let candidateEvents = fifoAfterAsMultiple fifo queryEvent;
    
    if candidateEvents.Length > 0 then
        let objrandom = new Random();
        let selIdx = objrandom.Next(candidateEvents.Length);
        let selEvent = candidateEvents.[selIdx];
        Some selEvent
    else
        None


// sample random event from FIFO
let fifoSampleRandom (fifo:Fifo0) =
    let objrandom = new Random();

    if fifo.buckets.Length > 0 then
        // TODO LOW< make more efficient by only selecting among full buckets! >
        let idxBucket = objrandom.Next(fifo.buckets.Length);

        //printfn "DBG: fifoSampleRandom(): idxBucket= %A" idxBucket;

        let selBucket = fifo.buckets.[idxBucket];
        if selBucket.events.Length > 0 then

            let idx = objrandom.Next(selBucket.events.Length);
            //printfn "DBG: fifoSampleRandom(): idx= %A" idx;

            Some selBucket.events.[idx]
        else
            None
    else
        None






// sample random from collector
let collectorSampleRandomWhereT (collector:Collector0) (tMax:int64) =
    // TODO< implement a filter if tMax is lower than Int64.MaxValue ! >

    let objrandom = new Random();

    if collector.col.Length > 0 then
        let idx = objrandom.Next(collector.col.Length);
        let selCandidate = collector.col.[idx];
        if selCandidate.occTime < tMax then
            Some collector.col.[idx]
        else
            None
    else
        None

open TermUtils


// tries to add a item to a collector if it doesn't already exist
let collectorPut (collector:Collector0) (item:NEvent) =
    // TODO< implement existence test with (string of sentence+string of stamp)
    let (hash:string) = convTermToStr item.sentence.term + "|" + stampConvToStr item.sentence.stamp;

    let mutable exists = false;
    exists <- match Map.tryFind hash collector.map with
    | Some _ -> true
    | None -> false;

    if not exists then
        collector.map <- collector.map.Add (hash, item);
        collector.col <- item :: collector.col;
        true
    else
        false




// composes sequence
let composeSeqA() =
    let sampledEvent0Opt = fifoSampleRandom fifoLevel0;
    match sampledEvent0Opt with
    | Some sampledEvent0 ->
        let sampledEventBefore0Opt = fifoBeforeAsSingle fifoLevel0 sampledEvent0;
        
        match sampledEventBefore0Opt with
        | Some sampledEventBefore0 ->
            let maxDt = 30; // maximal difference of time to combine

            let conclOpt = temporalCombineAsSeqV2 [sampledEventBefore0; sampledEvent0] maxDt;
            match conclOpt with
            | Some concl ->
                // store conclusion in FIFO
                fifo_dbgLog 1 "FIFO derive: composeSeqA(): put concl level0>level1";
                fifo_dbgLog 1 (sprintf "|-%s" (convTermToStr concl.sentence.term));
                fifoPut fifoLevel1 concl |> ignore;
                ///printfn "FIFO derive: put DONE"; // DBG

                ()
            | None -> ()
        | None -> ()
    | None -> ()


// compose seq by selecting following events
// BUG< sequence has wrong order !!! ???? >
let composeSeqB() =
    let events = fifoSelFollowing fifoLevel0;
    if events.Length > 0 then
        let maxDt = 30; // maximal difference of time to combine

        let conclOpt: NEvent option = temporalCombineAsSeqV2 events maxDt;
        match conclOpt with
        | Some concl ->
            // store conclusion in FIFO
            fifo_dbgLog 1 "FIFO derive: composeSeqB(): put concl level0>level1";
            fifo_dbgLog 1 (sprintf "|- %s" (convTermToStr concl.sentence.term));
            fifoPut fifoLevel1 concl |> ignore;
            ()
        | None ->
            ()
    else
        ()

let composeSeq() =
    let objrandom = new Random();

    // select between various ways on how we can build sequences
    if objrandom.Next(2) = 0 then
        composeSeqA()
    else
        composeSeqB()


open VarIntro

// compose SEQ =/> EVENT > and collect
let composePredImpl () =
    let selSeqOpt = fifoSampleRandom fifoLevel1;
    match selSeqOpt with
    | Some selSeq ->
        let selPredicateOpt = fifoAfterAsSingle fifoLevel0 selSeq;
        match selPredicateOpt with
        | Some selPredicate ->
            let maxPredImplBuildDt = 30;

            let conclPredImplOpt = temporalCombineAsPredImpl selSeq selPredicate maxPredImplBuildDt;
            match conclPredImplOpt with
            | Some conclPredImpl ->
                if checkIsValidPredImpl conclPredImpl.sentence.term then
                    fifo_dbgLog 1 "FIFO derive: put concl level1>predImplCollector";
                    fifo_dbgLog 1 (sprintf "predImpl|- %s" (convTermToStr conclPredImpl.sentence.term));

                    collectorPut predImplCollector conclPredImpl |> ignore; // add conclusion to collector
                    fifoConclBuffer <- conclPredImpl :: fifoConclBuffer; // add conclusion to conclusions

                    ()
                else
                    ()
            | None -> ()
        | None -> ()
    | None -> ()



///
///// try to build 2nd order ==> and simplify the term to && ==>
///// /param seedEvent is the event which is ==> which is used as a basis
///// /param termWithourVarIntro is the term of "seedEvent" without variables
///let build2ndOrderImpl (seedEvent:NEvent) (termWithourVarIntro:Term) =
///    printfn "DBG: FIFO: ==>==> seedEvent.minOccTime = %i" (seedEvent.minOccTime);
///
///    let mutable previousEventOpt = collectorSampleRandomWhereT predImplCollector seedEvent.minOccTime; // retrieve a candidate
///    
///    // select if we want to build it with a sequence
///    if (new Random()).Next(2) = 0 then
///        // * select candidate sequences which happen before consequent
///        let (antedecentCandidates:NEvent list) = fifoBeforeAsMultiple fifoLevel1 seedEvent;
///
///        if antedecentCandidates.Length > 0 then
///            // * select one sequence as antedecent which happens before consequent
///            let (selIdx:int) = (new Random()).Next(antedecentCandidates.Length);
///
///            let selAntecedent:NEvent = antedecentCandidates.[selIdx];
///            previousEventOpt <- Some selAntecedent;
///
///    match previousEventOpt with
///    | Some _ -> printfn "DBG: FIFO: ==>==>: sel some as previous event";
///    | None   -> printfn "DBG: FIFO: ==>==>: sel none as previous event";
///    
///    match previousEventOpt with
///    | Some previousEvent ->
///
///        // * now we can build our candidate term
///        let candidateTerm:Term = Imp (previousEvent.sentence.term, termWithourVarIntro);
///        printfn "DBG: FIFO: ==>==>: built candidate= %s" (convTermToStr candidateTerm);
///
///        // * now we have to intro variables the right way
///        let candidateTerm2:Term = termIntroVarDotWhereCnt2 candidateTerm;
///        let candidateTerm3:Term = normalizeVar candidateTerm2;
///        printfn "DBG: FIFO: ==>==>: candidate after var intro+normalize= %s" (convTermToStr candidateTerm);
///
///
///        // * now we have to transform the term from ==> ==> to && ==>
///        let foldedTermOpt:Term option = ruleNal5_fold candidateTerm3;
///
///        match foldedTermOpt with
///        | Some foldedTerm ->
///            printfn "DBG: FIFO: ==>==>: ... folded to = %s" (convTermToStr foldedTerm);
///
///            // * now we have to put the term back into memory and register it as conclusion result
///
///            // TODO< compute truth the right way! >
///            let truth:Truth = seedEvent.sentence.truth; // HACK
///
///            // TODO< check for stamp overlap of premises! >
///            // TODO< compute stamp correctly >
///            let stamp:Stamp = seedEvent.sentence.stamp;
///
///            let (concl3Sentence:Sentence) = {term = foldedTerm; truth=truth; stamp=stamp; punctation=seedEvent.sentence.punctation};
///            let (concl3Event:NEvent) = {minOccTime=previousEvent.minOccTime; occTime=seedEvent.occTime; sentence=concl3Sentence; isDerived=true;};
///
///            if DBG_FIFO_VERBOSITY > 0 then printfn "FIFO derive: put concl ==>==>>implCollector";
///            if DBG_FIFO_VERBOSITY > 0 then printfn "  %s" (convTermToStr concl3Event.sentence.term);
///
///            collectorPut implCollector concl3Event |> ignore;
///            fifoConclBuffer <- concl3Event :: fifoConclBuffer; // add conclusion to conclusions
///
///            ()
///        | None ->
///            ()
///
///        ()
///    | None ->
///        ()
///    
///    ()


// helper to see FIFO content as sequence of events
let fifo_viewAsSeq () =
    let mutable seqAcc = []; // sequence accumulator

    //if true then printfn "FIFO nBuckets=%i" fifoLevel0.buckets.Length; // DBG

    for iBucket in fifoLevel0.buckets do
        //if true then printfn "FIFO iBucket nEvents=%i" iBucket.events.Length; // DBG

        let sortedEventsOfBucketByOccTime = List.sortBy (fun iv -> iv.occTime) iBucket.events;
        seqAcc <- List.append seqAcc sortedEventsOfBucketByOccTime;
        ()

    //if false then printfn "DBG: FIFO: fifo_viewAsSeq() res len = %i" (seqAcc.Length); // DBG

    seqAcc



// new way to build ==>==> |- &&==> by "partioning" the perceived sequence of events
// NOTE< this function doesn't check if "seq" argument has events which follow each other!, this invariant must be ensured externally >
let fifo_partitionImplImpl (seq: NEvent list) =
    let maxDt = 30;

    if seq.Length >= (3+3+3) then
        let a0 = seq.[seq.Length-1-2];
        let a1 = seq.[seq.Length-1-1];
        let a2 = seq.[seq.Length-1-0];

        let b0 = seq.[seq.Length-1-2-3];
        let b1 = seq.[seq.Length-1-1-3];
        let b2 = seq.[seq.Length-1-0-3];
        
        let c0 = seq.[seq.Length-1-2-3-3];
        let c1 = seq.[seq.Length-1-1-3-3];
        let c2 = seq.[seq.Length-1-0-3-3];
        


        let seqAOpt = temporalCombineAsSeqV2 [a0;a1] maxDt;
        match seqAOpt with
        | Some seqA ->
            let aPredImplOpt:NEvent option = temporalCombineAsPredImpl seqA a2 maxDt;
            match aPredImplOpt with
            | Some aPredImpl ->
                let completeATerm = aPredImpl.sentence.term;
                let completeATv = aPredImpl.sentence.truth;
                let completeAStamp = aPredImpl.sentence.stamp;


                let seqBOpt = temporalCombineAsSeqV2 [b0;b1;b2] maxDt;

                let seqCOpt = temporalCombineAsSeqV2 [c0;c1;c2] maxDt;

                if seqBOpt.IsSome && seqCOpt.IsSome then
                    //let folded0:Term = Imp (seqCOpt.Value.sentence.term, seqBOpt.Value.sentence.term);
                    
                    //let folded0:Term = Imp (seqCOpt.Value.sentence.term, seqBOpt.Value.sentence.term);
                    //let candidateTerm:Term = Imp (folded0, aPredImpl.sentence.term);

                    let folded0:Term = Imp (seqBOpt.Value.sentence.term, aPredImpl.sentence.term);
                    let candidateTerm:Term = Imp (seqCOpt.Value.sentence.term, folded0);
                    
                    // now "candidateTerm" is ==>==>

                    // * now we have to intro variables the right way
                    for iTermWithVar in (termIntroVarCalcCandidates candidateTerm) do
                        let candidateTerm3:Term = normalizeVar iTermWithVar;
                        printfn "DBG: FIFO: ==>==>: candidate after var intro+normalize= %s" (convTermToStr candidateTerm3);


                        // * now we have to transform the term from ==> ==> to && ==>
                        let foldedTermOpt:Term option = ruleNal5_fold candidateTerm3;
                        match foldedTermOpt with
                        | Some foldedTerm ->
                            printfn "DBG: FIFO: ==>==>: ... folded to = %s" (convTermToStr foldedTerm);

                            // * now we have to put the term back into memory and register it as conclusion result

                            // TODO< compute truth the right way! >
                            let truth:Truth = completeATv; // HACK

                            // TODO< check for stamp overlap of premises! >
                            // TODO< compute stamp correctly >
                            let stamp:Stamp = completeAStamp;

                            let concl3Sentence:Sentence = sentenceCreate foldedTerm truth stamp ".";
                            // deriver_log__derivation [TODO] concl3Sentence "TODOnameme"; // TODO< log derivation >
                            let concl3Event:NEvent = {minOccTime=a2.minOccTime; occTime=a2.occTime; sentence=concl3Sentence; isDerived=true;}; // minOccTime is BUGGY

                            if DBG_FIFO_VERBOSITY > 0 then printfn "FIFO derive: put concl ==>==>>implCollector";
                            if DBG_FIFO_VERBOSITY > 0 then printfn "  %s" (convTermToStr concl3Event.sentence.term);

                            collectorPut implCollector concl3Event |> ignore;
                            fifoConclBuffer <- concl3Event :: fifoConclBuffer; // add conclusion to conclusions

                            ()
                        | None ->
                            ()
                else
                    ()
            | None -> ()
        | None ->
            ()

        ()
    else // it's impossible to partition!
        ()





// build   pred impl ==> pred impl
let composeImplA () =
    // TODO< implement more efficient better sampling algorithm like in composeImplB() >
    let aOpt = collectorSampleRandomWhereT predImplCollector Int64.MaxValue;
    let bOpt = collectorSampleRandomWhereT predImplCollector Int64.MaxValue;
    match aOpt with
    | Some a ->
        match bOpt with
        | Some b ->
            let mutable a2 = a;
            let mutable b2 = b;

            if a2.occTime > b2.occTime then
                // swap
                let temp = a2;
                a2 <- b2;
                b2 <- temp;
                ()
            else
                ()

            if DBG_FIFO_VERBOSITY > 0 then printfn "DBG:";
            if DBG_FIFO_VERBOSITY > 0 then printfn "DBG: composeImplA(): build ==>: sel a %s" (convTermToStr a2.sentence.term);
            if DBG_FIFO_VERBOSITY > 0 then printfn "DBG: composeImplA(): build ==>: sel b %s" (convTermToStr b2.sentence.term);

            //printfn "DBG: composeImplA(): cmp: %b" (a2.occTime < b2.occTime);
            if a2.occTime < b2.occTime then // only this order makes sense!
                let conclOpt = combineAsImpl a2 b2
                match conclOpt with
                | Some concl ->
                    // we introduce variables here
                    for iTermWithVar in (termIntroVarCalcCandidates concl.sentence.term) do
                        let concl3Term:Term = normalizeVar iTermWithVar; // we need to normalize var
                        let (concl3Sentence:Sentence) = sentenceCreate concl3Term concl.sentence.truth concl.sentence.stamp concl.sentence.punctation;
                        // TODO< log derivation ! >
                        let (concl3Event:NEvent) = {minOccTime=concl.minOccTime; occTime=concl.occTime; sentence=concl3Sentence; isDerived=true;};

                        if DBG_FIFO_VERBOSITY > 0 then printfn "FIFO derive: put concl predImplCollector>implCollector";
                        if DBG_FIFO_VERBOSITY > 0 then printfn "  %s" (convTermToStr concl3Event.sentence.term);

                        collectorPut implCollector concl3Event |> ignore;
                        fifoConclBuffer <- concl3Event :: fifoConclBuffer; // add conclusion to conclusions

                        ///build2ndOrderImpl concl3Event concl.sentence.term; // give a chance to build higher order ==>

                    ignore
                | None -> ignore
            else
                ignore
        | None -> ignore
    | None -> ignore


// build    seq ==> pred impl
let composeImplB() =
    let conseqentOpt = collectorSampleRandomWhereT predImplCollector Int64.MaxValue;
    match conseqentOpt with
    | Some consequent ->
        // * select candidate sequences which happen before consequent
        let (antedecentCandidates:NEvent list) = fifoBeforeAsMultiple fifoLevel1 consequent;

        if antedecentCandidates.Length > 0 then
            // * select one sequence as antedecent which happens before consequent
            let objrandom = new Random();
            let (selIdx:int) = objrandom.Next(antedecentCandidates.Length);

            let selAntecedent:NEvent = antedecentCandidates.[selIdx];

            printfn "DBG: FIFO: composeImplB(): sel %s+%s" (convTermToStr selAntecedent.sentence.term) (convTermToStr consequent.sentence.term);

            // * build conclusion and put into memory
            let conclOpt = combineAsImpl selAntecedent consequent;
            match conclOpt with
            | Some concl ->
                // we introduce variables here
                for iTermWithVar in (termIntroVarCalcCandidates concl.sentence.term) do
                    let concl3Term:Term = normalizeVar iTermWithVar; // we need to normalize var
                    let concl3Sentence:Sentence = sentenceCreate concl3Term concl.sentence.truth concl.sentence.stamp concl.sentence.punctation;
                    //TODO< log derivation >
                    let concl3Event:NEvent = {minOccTime=concl.minOccTime; occTime=concl.occTime; sentence=concl3Sentence; isDerived=true;};

                    if DBG_FIFO_VERBOSITY > 0 then printfn "FIFO derive: put concl predImplCollector>implCollector";
                    if DBG_FIFO_VERBOSITY > 0 then printfn "  %s" (convTermToStr concl3Event.sentence.term);

                    collectorPut implCollector concl3Event |> ignore;
                    fifoConclBuffer <- concl3Event :: fifoConclBuffer; // add conclusion to conclusions

                    ///build2ndOrderImpl concl3Event concl.sentence.term; // give a chance to build higher order ==>

                ignore
            | None ->
                ignore
        else
            ignore
    | None ->
        ignore


let composeImpl () =
    let objrandom = new Random();

    // select between various ways on how we can build sequences
    if objrandom.Next(2) = 0 then
        composeImplA()
    else
        composeImplB()




let fifo_partitionPredImpl (seq: NEvent list) =
    let maxDt = 30;

    //printfn "HERE A"; // DBGvvvvvvvvvvv

    if seq.Length >= (3) then
        //printfn "HERE B"; // DBG

        let a0 = seq.[seq.Length-1-2];
        let a1 = seq.[seq.Length-1-1];
        let a2 = seq.[seq.Length-1-0];

        fifo_dbgLog 2 (sprintf "before inference  a0=%s" (convEventToStr a0));
        fifo_dbgLog 2 (sprintf "before inference  a1=%s" (convEventToStr a1));
        fifo_dbgLog 2 (sprintf "before inference  a2=%s" (convEventToStr a2));

        let seqEventOpt: NEvent option = temporalCombineAsSeqV2 [a0;a1] maxDt;
        match seqEventOpt with
        | Some seqEvent ->
            //printfn "HERE SEQ"; // DBG

            let predImplEventOpt: NEvent option = temporalCombineAsPredImpl seqEvent a2 maxDt;
            match predImplEventOpt with
            | Some predImplEvent ->
                //printfn "HERE PREDIMPL"; // DBG

                if checkIsValidPredImpl predImplEvent.sentence.term then

                    fifo_dbgLog 2 (sprintf "a0=%s" (convEventToStr a0));
                    fifo_dbgLog 2 (sprintf "a1=%s" (convEventToStr a1));
                    fifo_dbgLog 2 (sprintf "a2=%s" (convEventToStr a2));

                    fifo__dbgLog2 true 1 "FIFO derive: put concl level1>predImplCollector";
                    fifo__dbgLog2 true 1 (sprintf "origin=fifo_partitionPredImpl() predImpl|- %s" (convTermToStr predImplEvent.sentence.term));

                    collectorPut predImplCollector predImplEvent |> ignore; // add conclusion to collector
                    fifoConclBuffer <- predImplEvent :: fifoConclBuffer; // add conclusion to conclusions
                    ()
                else
                    ()
            | None ->
                ()

            ()
        | None ->
            ()



        ()
    else
        ()




let mutable FIFO_perCycle_composeSeq = 20;
let mutable FIFO_perCycle_composePredImpl = 15;
let mutable FIFO_perCycle_composeImpl = 7;

// function to give cycle(s) to FIFO(s)
let fifo_giveResource () =
    if true then
        let fifoSeq: NEvent list = fifo_viewAsSeq (); // view FIFO content as sequence of events
        fifo_partitionPredImpl fifoSeq;
        ()
    else
        ()

    for i = 1 to FIFO_perCycle_composeSeq do
        composeSeq ();

    for i = 1 to FIFO_perCycle_composePredImpl do
        composePredImpl ();

    if FIFO_BUILD_IMPL then
        for i = 1 to FIFO_perCycle_composeImpl do
            composeImpl ();
        ()
    else
        ()
    
    if FIFO_BUILD_IMPL then
        // try to compose ==>==>
        let fifoSeq: NEvent list = fifo_viewAsSeq (); // view FIFO content as sequence of events
        fifo_partitionImplImpl fifoSeq; // partition and put into memory if it yielded a successful derivation
        ()
    else
        ()

    ()

