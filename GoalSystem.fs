module GoalSystem

open System
open System.Diagnostics // for debugging/diagnostics
open System.Threading

open Term
open TermUtils // for debugging
open Sentence
open SentenceUtils
open Stamp
open Rules
open BeliefMem
open NEvent
open GContainer
open Truth
open TaskPriorityQueue
open GoalSystemUtils
open DebugUtils
open AttentionDeclarative
open Fifo
//open GlobalConfig // commented because not used


let mutable DBG_GOALSYS_VERBOSITY:int = 0; // debug verbosity for goalsystem
let mutable DBG_GOALSYS_KILL:int = 0; // debug verbosity for goalsystem.kill 

// feature flags
let mutable GOALSYS_EN_GOALDRIVEN_CURIOSITY = false; // EXPERIMENTAL FEATURE  enable goal driven curiosity?
let mutable GOALSYS__GOALDRIVEN_CURIOSITY__MINMAL_CONF = 0.15; // minimal confidence for curriosity to consider action
let mutable GOALSYS__GOALDRIVEN_CURIOSITY__BABBLE_PROB = 0.07; // babble probability per cycle


// helper to emit log
let goalsystem__dbgLog2 (en:bool) (level:int) (msg:string) =
    dbgLog3 "GOALsys" en level msg; 

// helper to emit log
let goalsystem__dbgLog (level:int) (msg:string) =
    goalsystem__dbgLog2 (level <= DBG_GOALSYS_VERBOSITY) level msg;




type GoalTask0 = {
    term: Term; // term to point to goal "GoalTaskOfConcept"
}

// origin of the goal
type GoalTaskOriginEnum =
    | PredImplDetach // was derived from =/>
    | SeqDetach      // was derived from sequence
    | Input          // was input

// task for a active goal inside a concept
type GoalTaskOfConcept = {
    sentence: Sentence;

    parentGoalTerm: Term option; // points to the parent goal
                                 // we store it to be able to kill it!
    
    goalUsedRootBeliefOpt: Term option; // root belief which was used to derive the goal for the op,  for example <(a,^b) =/> c>

    depth: int; // depth of the goal

    origin: GoalTaskOriginEnum; // origin of the goal


    lastUpdateTime: int64; // time of last update
}



// bucket by depth
type GoalDepthBucket0 = {
    mutable tasks: GContainer<GoalTask0>;

    thisDepth: int; // depth of this bucket

    thisProb: float; // probability of sampling - cached
}

// concept of goal
type GoalConcept = {
    name: Term;

    mutable content: GContainer<GoalTaskOfConcept>;

    // used to store goal-tasks which have the "name" as a parent, necessary to effectivly be able to "kill" sub-goals if parent was archived
    mutable contentChildren: GContainer<GoalTaskOfConcept>;
}

// concept based memory of active goals
type GoalConceptMem = {
    mutable mapToGoalConcepts: Map<Term, GoalConcept>; // map to "goal concepts" by name which is the term!

    maxNActiveGoals: int;
}




// origin of the pending op
//type EnumPendingOpOrigin =
//| BABBLING
//| DERIVED

// used to store meta-information of pending op
type PendingOp = {
    opAndArgs: OpAndArgs;
    goalUsedRootBeliefOpt: Term option; // root belief which was used to derive the goal for the op,  for example <(a,^b) =/> c>
    //origin: EnumPendingOpOrigin;
}




// candidate for the motor actions of goal based curiosity
type GoalBasedCuriosity__Candidate = {
    parentGoalTerm: Term; // sequence on which the candidate is based, is used for curiosity based "babbling"
    tv: Truth; // truth of the conclusion from which this sequence was derived
}

// memory of goal system
type GoalMem0 = {
    mutable goalDepthBuckets: GoalDepthBucket0 list; // list of depth based goal buckets, index [0] is for depth=0, etc.

    mutable goalConcepts: GoalConceptMem;

    // ops which are considered for execution
    // TODO< use a type to store meta information! >
    mutable pendingOps: GContainer<PendingOp>;

    mutable registeredOps: Map<string, RegisteredOp>;

    // feedback to the perception module
    // contains the events which were executed and thus have to be perceived as soon as possible for feedback
    mutable outPerceivedEvents: Term list;

    mutable decisionThreshold: float;

    // EXPERIMENTAL FEATURE - list of all candidates for "motor babbling" based on "goal driven curiosity"
    mutable goalBasedCuriosity__candidates: GoalBasedCuriosity__Candidate list;
    //                        list of recently used candidates for "motor babbling" based on "goal driven curiosity"
    mutable goalBasedCuriosity__recentlyUsed: GoalBasedCuriosity__Candidate list;

    // queue used for updates of implication
    implUpdateQueue : TaskPriorityQueue;

    goalPerConcept: int; // maximal number of goals in concept
}
and RegisteredOp = {
    // parameters: 
    // [0]=goal memory (used for NAL9 ops)
    // [1]=args
    mutable callable: GoalMem0 -> Term list -> unit;
}









let mutable procedural_bucketProb: float list = []; // sampling probabilities of buckets
procedural_bucketProb <- 0.0 (* (2.0/3.0 + 0.5)*0.5 *) ::procedural_bucketProb; // first bucket should have high priority
procedural_bucketProb <- 0.0 (* 0.3 *) ::procedural_bucketProb;

// fill with exponentially less important sampling priorities
for j=1 to (10-2+1) do
  procedural_bucketProb <- (exp (procedural_bucketProb.[1] * -0.1*(float j))) ::procedural_bucketProb;


// compute accumulated sampling probability
let temp_acc: float = procedural_bucketProb |> List.sum;

// normalize that it is distributed over remaining mass
let remaining_mass_: float = 1.0 - ((2.0/3.0 + 0.5)*0.5 + 0.3);
procedural_bucketProb <- procedural_bucketProb |> List.map (fun iv -> iv / (temp_acc * remaining_mass_) );

procedural_bucketProb <- procedural_bucketProb |> List.updateAt 0 ((2.0/3.0 + 0.5)*0.5);
procedural_bucketProb <- procedural_bucketProb |> List.updateAt 1 (0.3);

// normalize
let temp_acc2: float = procedural_bucketProb |> List.sum;
procedural_bucketProb <- procedural_bucketProb |> List.map (fun iv -> iv / temp_acc2);







let createGoalMem0 (goalPerConcept:int): GoalMem0 =
    let goalConceptMem = {mapToGoalConcepts = Map.empty<Term, GoalConcept>; maxNActiveGoals=200; };
    let mutable goalMem = {
        goalDepthBuckets = [];
        goalConcepts = goalConceptMem;
        pendingOps=GContainer_create (fun a b -> false) (fun v -> 0.0) 20;
        registeredOps=Map.empty<string, RegisteredOp>;
        outPerceivedEvents = [];
        decisionThreshold = 0.5;
        goalBasedCuriosity__candidates = [];
        goalBasedCuriosity__recentlyUsed = [];
        implUpdateQueue = TaskPriorityQueue(15);
        goalPerConcept = goalPerConcept;
    }

    let maxDepth:int = 10;
    for iDepth = 0 to maxDepth-1 do
        let bucket_capacity:int = 2000; // how many goals can fit into one bucket?

        let sentenceRankingFn a = 0.0; // ranking function for task - TODO TODO TODO

        let thisProb: float = procedural_bucketProb.[maxDepth-iDepth]; // lookup probability

        let createdGoalDepthBucket:GoalDepthBucket0 = {
            tasks=(GContainer_create (fun a b -> a.term = b.term) sentenceRankingFn bucket_capacity);
            thisDepth=maxDepth-iDepth;
            thisProb=thisProb;
        }
        goalMem.goalDepthBuckets <- createdGoalDepthBucket :: goalMem.goalDepthBuckets;

    goalMem


// * get the goals which have "goalTerm" as it's parent
let retChildrenGoalTerms (goalMem:GoalMem0) (goalTerm:Term): Term list =
    if Map.containsKey goalTerm goalMem.goalConcepts.mapToGoalConcepts then
        let selGoalConcept:GoalConcept = Map.find goalTerm goalMem.goalConcepts.mapToGoalConcepts;

        selGoalConcept.contentChildren.taskContent
        |> List.filter (fun iv -> iv.parentGoalTerm.IsSome && iv.parentGoalTerm.Value = goalTerm)  // make sure that only goals are considered which are sub-goals of the goal
        |> List.map (fun iv -> iv.sentence.term)
    else
        []



// kills a goal
// is used to avoid the realization of a already archived goal and it's subgoals
// /param killDepth depth of recursive call, is used for debugging!
// /param alreadyKilledGoals set of all goals which were already killed, used to avoid cycles
let rec goalKill2Rec (goalMem:GoalMem0) (goalTerm:Term) (killDepth:int) (alreadyKilledGoals: Set<Term>) =
    let GOALSYS_KILL_MAXDEPTH:int = 3;
    
    goalsystem__dbgLog2 (false && (DBG_GOALSYS_KILL > 0)) 1 (sprintf "goalKillRec() called with depth=%i goalTerm=%s" killDepth (convTermToStr goalTerm));

    if killDepth < GOALSYS_KILL_MAXDEPTH && not (alreadyKilledGoals.Contains(goalTerm)) then // only kill if it wasn't already killed to avoid infinite recursion
        // * kill goal(s) in buckets
        for iBucket in goalMem.goalDepthBuckets do
            iBucket.tasks.taskContent <- List.filter (fun iv -> not(iv.term = goalTerm)) iBucket.tasks.taskContent;


        // * get the goals which have "goalTerm" as it's parent
        let childrenGoalTerms: Term list = retChildrenGoalTerms goalMem goalTerm;




        // * kill goal(s) in concept
        //
        let killInConcept () =
            if Map.containsKey goalTerm goalMem.goalConcepts.mapToGoalConcepts then
                let selGoalConcept:GoalConcept = Map.find goalTerm goalMem.goalConcepts.mapToGoalConcepts;

                // kill goals
                selGoalConcept.content.taskContent <- selGoalConcept.content.taskContent |> List.filter (fun iv -> iv.sentence.term = goalTerm);

                ()
            else
                () // nothing to do here, done

            ()
        killInConcept ();

        let alreadyKilledGoals2 = alreadyKilledGoals.Add(goalTerm);

        // call recursivly to kill sub-goals
        for iSubGoalTerm in childrenGoalTerms do
            goalKill2Rec goalMem iSubGoalTerm (killDepth+1) alreadyKilledGoals2;
        
        ()
    else
        ()


let goalKillRec (goalMem:GoalMem0) (goalTerm:Term) (killDepth:int) =
    let alreadyKilledGoals: Set<Term> = Set.empty;
    goalKill2Rec goalMem goalTerm killDepth alreadyKilledGoals





// helper: add a goal to the goals
// /return was the goal added?
let goalPut2Internal (goalMem:GoalMem0) (goal:Sentence)  (depth:int) (parentGoalTermOpt:Term option) (goalUsedRootBeliefOpt:Term option) (origin:GoalTaskOriginEnum) (timeNow:int64): bool =

    let selBucketIdx = min depth (goalMem.goalDepthBuckets.Length-1); // index of the selected bucket

    let createdTask: GoalTask0 = {term = goal.term}; // create the task

    GContainer_put goalMem.goalDepthBuckets.[selBucketIdx].tasks createdTask |> ignore;

    let isGoalAlreadyPresent:bool =
        if Map.containsKey goal.term goalMem.goalConcepts.mapToGoalConcepts then
            // check if goal is already present in concept
            let selConcept:GoalConcept = Map.find goal.term goalMem.goalConcepts.mapToGoalConcepts;


            ///let existsGoal:bool = List.exists (fun iv -> checkSentenceSame iv.sentence goal) selConcept.content.taskContent; // compute if goal already exists // commented because it's the old handling which is BUGGY because it leads to duplicated goals            
            // TODO< handling is to strict, we need to implement adding of goal correctly with choice rule >
            let existsGoal:bool = List.exists (fun iv -> iv.sentence.term = goal.term) selConcept.content.taskContent; // compute if goal already exists
            
        
            existsGoal
        else
            false
    
    let ignoreThisGoal: bool = goal.truth.c < 0.0005; // rule to ignore goals which aren't to important
    
    //printfn "DBG[9]: goalPut2Internal(): %s %b" (convTermToStr goal.term) isGoalAlreadyPresent;

    // * goal: add goalConcept if it is not already present!
    if ignoreThisGoal || isGoalAlreadyPresent then
        false // return false because we didn't need to add goal
    else
        // function to ensure that a goal concept exists, creates one if it is not present
        let ensureGoalConceptExists (term:Term) =
            if Map.containsKey term goalMem.goalConcepts.mapToGoalConcepts then
                // concept already exists, goal-task is not present
                ()
            else
                // we need to create concept + goal-task
                let rankingFn a = (calcExp a.sentence.truth); // ranking function for sentence
                let createdGoalConcept:GoalConcept = {name = term; content = GContainer_create (fun a b -> a = b) rankingFn goalMem.goalPerConcept; contentChildren = GContainer_create (fun a b -> a = b) rankingFn goalMem.goalPerConcept;}
                goalMem.goalConcepts.mapToGoalConcepts <- Map.add createdGoalConcept.name createdGoalConcept goalMem.goalConcepts.mapToGoalConcepts;
                ()

        // ** ensure that the concept exists
        ensureGoalConceptExists goal.term;

        // ** we need to create and add goal task
        let selConcept:GoalConcept = Map.find goal.term goalMem.goalConcepts.mapToGoalConcepts;
        let createdGoalTask:GoalTaskOfConcept = {
            sentence = goal;
            parentGoalTerm = parentGoalTermOpt;
            goalUsedRootBeliefOpt=goalUsedRootBeliefOpt;
            depth=depth; 
            origin=origin;

            lastUpdateTime=timeNow;
        }
        
        GContainer_put selConcept.content createdGoalTask |> ignore;
        



        // * keep "contentChildren" up to date
        match parentGoalTermOpt with
        | Some parentGoalTerm ->
            // ** ensure that the concept for the parentGoalTerm exists
            ensureGoalConceptExists parentGoalTerm;

            let selConcept2:GoalConcept = Map.find parentGoalTerm goalMem.goalConcepts.mapToGoalConcepts;
            //let createdGoalTask2:GoalTaskOfConcept = {sentence = goal; parentGoalTerm = parentGoalTermOpt; depth=depth; origin=origin;};
        
            GContainer_put selConcept2.contentChildren createdGoalTask |> ignore;

            ()        
        | None ->
            ()


        true // return true because the goal was added

// add a goal to the goals
// /return was the goal added?
let goalPut2 (goalMem:GoalMem0) (goal:Sentence)  (depth:int) (parentGoalTerm:Term option) (goalUsedRootBeliefOpt:Term option)  (origin:GoalTaskOriginEnum) (timeNow:int64): bool =
    goalsystem__dbgLog 3 (sprintf "goalPut2()  goal=%s" (convSentenceToStr goal));
    
    match matchOp goal.term with
    | Some opAndArgs ->

        if (calcExp goal.truth) > goalMem.decisionThreshold then
            // special handling for adding op
            //

            goalsystem__dbgLog 2 (sprintf "add op to goalMem.pendingOps  goal.term=%s" (convTermToStr goal.term));

            // we add op to queue of op's to be executed at the next oportunity
            let thisPendingOp: PendingOp = {
                opAndArgs=opAndArgs; 
                //parentGoalTerm=parentGoalTerm; // commented because it was just an idea and is not necessary!
                goalUsedRootBeliefOpt = goalUsedRootBeliefOpt;
                //origin = DERIVED;
            }
            GContainer_put goalMem.pendingOps thisPendingOp |> ignore;

            ()
    | None ->
        ()// not a op
    
    goalPut2Internal goalMem goal  depth parentGoalTerm goalUsedRootBeliefOpt origin timeNow;


let goalPut (goalMem:GoalMem0) (goal:Sentence) (timeNow:int64) = goalPut2 goalMem goal 0 None None Input timeNow;











// higher order procedural knowledge
// << (A,^X)=/>G0 > --> ^nal9_believe>.



// blackboard values for NAL9 communication with 'native' code
let mutable NAL9_goalSystem__concls: (Sentence*Term option*GoalTaskOriginEnum) list = []; // list with all conclusions - used as scratchpad between invocations of different ops

let mutable NAL9_goalSystem__goalUsedRootBeliefOpt:Term option = None;



let mutable NAL9_goalSystem__GoalTermGenCnt: int64 = 1; // counter used to generate unique names of goals

let mutable NAL9_goalSystem__goalDerive2_blackboard_sentencesByName: (string * Sentence) list = []; // blackboard with pending goal sentences by unique name

// op to derive goals by "higher order procedural knowledge"
// ex: <({SELF} * predImpl * NAME_48489 * %1)  --> ^nal9_goalDerive2>!
//    last parameter will be unified with ID of the conclusions!
// /return tuple to unify results with
let op_nal9__goalDerive2 (mem:BeliefMem0) (timeNow:int64) (args: Term list): (Term * Term) list =
    printfn "op_nal9__goalDerive2: entry...";
    
    let sw = new Stopwatch (); // for performance metrics
    sw.Start();
    
    let goalTermName: Term = args.[2];
    let usedGoalBlackboardName: string option = match goalTermName with
    | Word word -> Some word
    | _ -> None

    let usedBeliefType: string option = match args.[1] with // extract type of belief to use
    | Word word -> Some word
    | _ -> None

    //printfn "   usedGoalBlackboardName=%s" usedGoalBlackboardName.Value; //DBG
    //printfn "   usedBeliefType        =%s" usedBeliefType.Value; // DBG

    
    // we need to fetch the goal which is used as the premise for the derivation
    
    // + helper to retrieve and remove the 'goal sentence' from "NAL9_goalSystem__goalDerive2_blackboard_sentencesByName"
    let helper__retUsedGoalSentence (): Sentence option =
        let mutable matchIdxOpt: int option = None;
        if usedGoalBlackboardName.IsSome then // we can only look for name if name is set
            for iIdx=0 to NAL9_goalSystem__goalDerive2_blackboard_sentencesByName.Length-1 do
                let iGoalName, iGoalSentence = NAL9_goalSystem__goalDerive2_blackboard_sentencesByName.[iIdx];
                if iGoalName = usedGoalBlackboardName.Value then
                    matchIdxOpt <- Some iIdx;
                    ()
                else
                    ()
        else
            ()
        
        match matchIdxOpt with
        | Some matchIdx ->
            // retrive
            let goalName, goalSentence = NAL9_goalSystem__goalDerive2_blackboard_sentencesByName.[matchIdx];

            // remove
            NAL9_goalSystem__goalDerive2_blackboard_sentencesByName <- List.removeAt matchIdx NAL9_goalSystem__goalDerive2_blackboard_sentencesByName;

            Some goalSentence
        | None ->
            None
    
    let mutable usedGoalSentenceOpt: Sentence option = helper__retUsedGoalSentence ();

    if usedGoalSentenceOpt.IsSome then
        let usedGoalSentence = usedGoalSentenceOpt.Value;

        let beliefConceptOpt: BeliefMemConcept0 option = beliefMem_TryLookupConcept mem usedGoalSentence.term;
        match beliefConceptOpt with
        | Some concept ->
            let usedBeliefsOfConcept: Belief list = match usedBeliefType.Value with
            | "predImpl" -> concept.predImplBeliefs.taskContent
            | _ -> concept.implBeliefs.taskContent // else we use beliefs as higher order knowledge

            // filter beliefs for * --> ^nal9_believe when usedBeliefType="decl" 
            let filterPredicateFn (belief:Belief): bool =
                match belief.sentence.term with
                | Inh (s,Word "^nal9_believe") -> true
                | _ -> false

            let relevantBeliefs = match usedBeliefType.Value with
                | "predImpl" -> usedBeliefsOfConcept // then we don't need to filter beliefs
                | _ -> List.filter filterPredicateFn usedBeliefsOfConcept // then we need to filter for higher-order beliefs

            // extract beliefs and sentences
            let extractBeliefFn (belief:Belief): (Belief * Sentence) option =
                match usedBeliefType.Value with
                | "predImpl" ->
                    Some (belief, belief.sentence)
                | _ ->
                    match belief.sentence.term with
                    | Inh (s,Word "^nal9_believe") -> 
                        let translatedSentence: Sentence = sentenceCreate s belief.sentence.truth belief.sentence.stamp belief.sentence.punctation;
                        Some (belief, translatedSentence)
                    | _ ->
                        None
            let usedBeliefs = match usedBeliefType.Value with
                | "predImpl" ->
                    relevantBeliefs |> List.map extractBeliefFn |> List.map (fun iv -> iv.Value) // OPTIMIZATION< we don't need to filter! >
                | _ ->
                    relevantBeliefs |> List.map extractBeliefFn |> List.filter (fun iv -> iv.IsSome) |> List.map (fun iv -> iv.Value);

            /////////////
            // now we can do the actual goal derivation


            let mutable concls: (Sentence*Term option*GoalTaskOriginEnum) list = []; // list with all conclusions

            // * try to derive sub-goal(s) by just looking at the goal
            match nal7_detachSeq usedGoalSentence.term usedGoalSentence.truth with
            | Some (conclTerm, conclTruth) ->
                let createdSentence:Sentence = sentenceCreate conclTerm conclTruth usedGoalSentence.stamp "!";
                //TODO< log derivation >
                concls <- (createdSentence, NAL9_goalSystem__goalUsedRootBeliefOpt, SeqDetach) :: concls;
                ()
            | None ->
                ()
            
            let sw2 = new Stopwatch (); // for performance metrics
            sw.Start();

            // iterate over beliefs and try to derive something with it
            for iBelief, iBeliefTranslatedSentence in usedBeliefs do
                if not (stampCheckOverlap iBeliefTranslatedSentence.stamp usedGoalSentence.stamp) then

                    declAv__update_read iBelief.av timeNow; // update read "usage"

                    // try to derive
                    match nal7_detachPredImpl usedGoalSentence.term usedGoalSentence.truth iBeliefTranslatedSentence.term iBeliefTranslatedSentence.truth with
                    | Some (conclTerm,conclTruth) ->
                        match conclTerm with
                        | Seq seq when (matchOp seq.[seq.Length-1]).IsSome -> // only allow derivation if last seq element is op!
                            let concl:Sentence = sentenceCreate conclTerm conclTruth (stampMerge usedGoalSentence.stamp iBeliefTranslatedSentence.stamp) "!";
                            // TODO< log derivation >

                            let goalUsedParentBeliefOpt: Term option =
                                match NAL9_goalSystem__goalUsedRootBeliefOpt with
                                | Some goalUsedRootBelief -> Some goalUsedRootBelief // used belief is the belief of the goal
                                | None -> Some iBeliefTranslatedSentence.term // used belief is the premise belief
                            
                            concls <- (concl, goalUsedParentBeliefOpt, PredImplDetach) :: concls;
                            ();
                        | _ -> ()

                    | None ->
                        ();
                else
                    ();
            
            sw2.Stop();
            let timeUs:int64 = (sw2.Elapsed.Ticks * 100L) / 1000L; // compute elapsed time in us
            printfn "DBG DIAG: NAL9 ^nal9_goalDerive2: derivation took %ius for nBeliefs=%i" timeUs usedBeliefs.Length;


            NAL9_goalSystem__concls <- concls; // set blackboard result to current result

            ()
        | None ->
            ()
    else // when the 'goal sentence' associated with the parameter wasn't found in the global blackboard
        ()

    sw.Stop();
    let timeUs:int64 = (sw.Elapsed.Ticks * 100L) / 1000L; // compute elapsed time in us
    printfn "DBG DIAG: NAL9 ^nal9_goalDerive2 took %ius" timeUs;
    [] // HACK - we return no unified parameters as return parameters






///println "TODO - NAL9: ^nal9_goalDerive2: implement storage of goals";
////// TODO TODO TODO implement like in core of 22NAR











// derive (new) goals from a selected goal and return
// this does NOT put the conclusions back into memory!!!
//
// callable as NAL9-op
//
// returns list of tuples (conclusion, goalUsedParentBelief)
let goalDerive (beliefMem:BeliefMem0) (goal:Sentence) (goalUsedRootBeliefOpt:Term option) (timeNow:int64): (Sentence*Term option*GoalTaskOriginEnum) list =
    // invoke NAL9 operator to derive goals

    // setup "NAL9_goalSystem__goalUsedRootBeliefOpt"
    NAL9_goalSystem__goalUsedRootBeliefOpt <- goalUsedRootBeliefOpt;

    // generate argument for pass to NAL9 op
    let usedGoalName: string = sprintf "G__%i" NAL9_goalSystem__GoalTermGenCnt;
    NAL9_goalSystem__GoalTermGenCnt <- NAL9_goalSystem__GoalTermGenCnt + 1L;
    // + push goal into table of goals
    NAL9_goalSystem__goalDerive2_blackboard_sentencesByName <- (usedGoalName,goal) :: NAL9_goalSystem__goalDerive2_blackboard_sentencesByName;

    // setup args and  build args passed to NAL9 op
    let mutable nal9op_args: Term list = [];
    nal9op_args <- UVar 0 :: nal9op_args; // variable for result value
    nal9op_args <- Word usedGoalName :: nal9op_args;
    nal9op_args <- Word "predImpl" :: nal9op_args;
    nal9op_args <- SetExt [Word "SELF"] :: nal9op_args; // {SELF}

    // invoke NAL-9 op
    op_nal9__goalDerive2 beliefMem timeNow nal9op_args |> ignore;
    

    // now we need to return the conclusions
    NAL9_goalSystem__concls
    





// select a random goal if possible for inference based on a distribution
let goalSystem_SelectRandom (goalMem:GoalMem0): GoalConcept option =
    // we only care about buckets which have content!
    let candidateBuckets =
        goalMem.goalDepthBuckets
        |> List.filter (fun iv -> iv.tasks.taskContent.Length > 0);

    let probMass: float = candidateBuckets |> List.map (fun iv->iv.thisProb) |> List.sum; // compute probability mass for selection

    if candidateBuckets.Length > 0 then
        let rng = new Random();

        // select bucket by depth based distribution
        let selProbMass: float = rng.NextDouble()*probMass;
        let mutable accProbMass: float = 0.0;
        let mutable selBucketIdxOpt:int option = None;
        for idx=0 to candidateBuckets.Length-1 do
            match selBucketIdxOpt with
            | Some _ ->
                ()
            | None -> // index wasn't yet selected - carry on
                accProbMass <- accProbMass + candidateBuckets.[idx].thisProb;
                if accProbMass > selProbMass then
                    selBucketIdxOpt <- Some idx;
                ()

        // select last one if nothing was selected
        selBucketIdxOpt <- match selBucketIdxOpt with
        | None -> Some (candidateBuckets.Length - 1)
        | Some _ -> selBucketIdxOpt


        let selBucketIdx:int = selBucketIdxOpt.Value; //rng.Next(candidateBuckets.Length);
        let selBucket:GoalDepthBucket0 = candidateBuckets.[selBucketIdx];
        let selTaskIdx:int = rng.Next(selBucket.tasks.taskContent.Length);
        let selGoalTask0:GoalTask0 = selBucket.tasks.taskContent.[selTaskIdx];

        // fetch concept adressed by goal-task
        if Map.containsKey selGoalTask0.term goalMem.goalConcepts.mapToGoalConcepts then
            let selGoalConcept:GoalConcept = Map.find selGoalTask0.term goalMem.goalConcepts.mapToGoalConcepts;
            Some selGoalConcept
        else
            printfn "INTERNAL warning: concept for active goal was not found!!!, ignore"; // should never happen!
            None
    else
        None




// gives resources to the goal deriver
//
// select goal and derives sub-goals
let goalSystem_deriveStep (goalMem:GoalMem0) (beliefMem:BeliefMem0) (timeNow:int64) =
    let sw = new Stopwatch (); // for performance metrics
    sw.Start();
    
    // select random goal and derive sub-goals
    match goalSystem_SelectRandom goalMem with
    | Some selGoalConcept ->
        // ** select premise
        let rng = new Random();
        let selContentIdx:int = rng.Next(selGoalConcept.content.taskContent.Length);
        let selGoal:GoalTaskOfConcept = selGoalConcept.content.taskContent.[selContentIdx];

        // ** derive sub-goals
        let goalConcls: (Sentence*Term option*GoalTaskOriginEnum) list = goalDerive beliefMem selGoal.sentence selGoal.goalUsedRootBeliefOpt timeNow;

        // debug goals
        printfn "DBG: concl goals:";
        for iGoalConclSentence, iGoalUsedRootBeliefOpt, iGoalConclOrigin in goalConcls do
            printfn "DBG: |- %s %A" (convSentenceToStr iGoalConclSentence) iGoalConclOrigin;

        // ** put sub-goals back into memory
        for iGoalConclSentence, iGoalUsedRootBeliefOpt, iGoalConclOrigin in goalConcls do
            goalPut2 (goalMem:GoalMem0) iGoalConclSentence (selGoal.depth+1) (Some selGoal.sentence.term) iGoalUsedRootBeliefOpt iGoalConclOrigin timeNow |> ignore;

        ();
    | None ->
        ();
    
    sw.Stop();
    let timeUs:int64 = (sw.Elapsed.Ticks * 100L) / 1000L; // compute elapsed time in us
    printfn "DBG DIAG: goalSystem_deriveStep() took %ius" timeUs;

    ();




// anticipation mechanism

// give positive/negative evidence for anticipation because (maybe) anticipated event happened
// /param revisionTv is the (virtual) truth which is added
// returns the term of the belief for which the update was done, for example <A =/> E>. when "eventTerm" was "E"
let anticipate_revise (goalMem:GoalMem0) (beliefMem:BeliefMem0) (eventTerm:Term) (revisionTv:Truth) (timeNow:int64): Term option =
    // A =/> E. E. :|: where E = "eventTerm"
    // lookup goal "E!" for a goal 


    //let conceptTermsWithEventTermAsParent: Term list = retChildrenGoalTerms goalMem eventTerm; // fetch terms of parent goals. Ex: will yield "A =/> E"
    //let predImplConceptTermsWithEventAsParent: Term list = conceptTermsWithEventTermAsParent |> List.filter (fun iv -> match iv with | PredImp (s,p) -> true | _ -> false) // filter for "A =/> E" seq

    //printfn "DBG: %A" conceptTermsWithEventTermAsParent;
    //printfn "DBG: %A" predImplConceptTermsWithEventAsParent;

    // helper to update the belief <A =/> E>.
    // returns the term of the belief for which the update was done, for example <A =/> E>. when "eventTerm" was "E"
    let updateBelief (): Term option =
        let mutable result: Term option = None;

        let beliefConceptOpt = beliefMem_TryLookupConcept beliefMem eventTerm;
        match beliefConceptOpt with
        | Some beliefConcept ->
            // find index where A =/> B. and B. is "eventTerm"

            let mutable break2 = false;
            for iIdx = 0 to beliefConcept.predImplBeliefs.taskContent.Length-1 do
                if not break2 then
                    let iBelief = beliefConcept.predImplBeliefs.taskContent.[iIdx];
                    match iBelief.sentence.term with
                    | PredImp (s,p) when p = eventTerm ->
                        // add virtual positive/negative evidence
                        let newTruth:Truth = calcBinaryTruth "revision" iBelief.sentence.truth revisionTv;

                        //printfn "old truth = %f %f" beliefConcept.predImplBeliefs.taskContent.[iIdx].truth.f beliefConcept.predImplBeliefs.taskContent.[iIdx].truth.c;
                        //printfn "new truth = %f %f" newTruth.f newTruth.c;
                        
                        declAv__update_read iBelief.av timeNow;
                        declAv__update_write iBelief.av timeNow;

                        beliefConcept.predImplBeliefs.taskContent.[iIdx].sentence.truth <- newTruth; // update truth
                        //beliefConcept.predImplBeliefs.taskContent <- List.updateAt iIdx beliefConcept.predImplBeliefs.taskContent.[iIdx] beliefConcept.predImplBeliefs.taskContent;

                        goalsystem__dbgLog2 true 2 (sprintf "anticipate_revise(): Update: was successful! to sentence=%s" (convSentenceToStr beliefConcept.predImplBeliefs.taskContent.[iIdx].sentence));

                        break2 <- true;
                        result <- Some iBelief.sentence.term;
                        ()
                    | _ ->
                        ()
            result
        | None ->
            None
    
    updateBelief ()

    (* this code scans for the goal, is commented because this function can be called when the goal is no longer present!

    for iTerm in conceptTermsWithEventTermAsParent do
        // try to fetch concept
        if Map.containsKey iTerm goalMem.goalConcepts.mapToGoalConcepts then
            let selGoalConcept:GoalConcept = Map.find iTerm goalMem.goalConcepts.mapToGoalConcepts;

            printfn "DEV DBG: anticipate_revise(): found goal concept for term = %s" (convTermToStr iTerm);

            printfn "%A" selGoalConcept;

            // search for right entry(s)
            for iContent in selGoalConcept.content.taskContent do
                match iContent.origin with
                | PredImplDetach when iContent.parentGoalTerm.Value = eventTerm -> // we only care about goals derived from detachment and if the terms are the same
                    printfn "DEV DBG: anticipate_revise(): found SPECIFIC GOAL!";


                    // we found the coresponding goal, now we can update the belief
                    updateBelief ();


                    ()
                | _ -> 
                    ()

            ()
        else
            () // nothing to do here, done
    
    *)

    







let mutable ANTICIPATION_POS_CONF = 0.08;
let mutable ANTICIPATION_NEG_CONF = 0.06;


// helper to add evidence for ==>
// /param goalUsedRootBelief is the root belief used for the procedural knowledge for which ==> relates, for example (a, ^b) =/> c
// /param sign is the "direction" of the evidence, positive (+1) or negative (-1)
let goalSystem_implication_addEvidence (goalMem:GoalMem0) (beliefMem:BeliefMem0) (goalUsedRootBelief:Term) (sign:int) (timeNow:int64) =
    printfn "DBG[4] goal system: goalSystem_implication_addEvidence() called with sign=%i goalUsedRootBelief=%s" sign (convTermToStr goalUsedRootBelief);

    let beliefConceptOpt = beliefMem_TryLookupConcept beliefMem goalUsedRootBelief;
    match beliefConceptOpt with
    | Some beliefConcept ->
        printfn "DBG[4] goal system: sel belief";

        // TODO TODO TODO TODO TODO< filter for ==> and filter for  pred of ==> >
        let relevantImplBeliefs = beliefConcept.implBeliefs.taskContent;

        // add tasks to add negative evidence to beliefs
        for iBelief in relevantImplBeliefs do
            declAv__update_read iBelief.av timeNow; // update because we read it
            
            printfn "DBG[5] enqueue evidence task with sign=%i for  sentence=%s" sign (convSentenceToStr iBelief.sentence);
            goalMem.implUpdateQueue.Enqueue {sentence=iBelief.sentence;sign=sign;}; // queue task for later deferred processing
            ()
        
        printfn "DBG[4] goal system: ...done";

        ()
    | None ->
        ()



// callback which is called when ever a (novel) event is perceived from the environment
let goalSystem_perceiveCallback (goalMem:GoalMem0) (beliefMem:BeliefMem0) (event:NEvent) (timeNow:int64) =
    goalsystem__dbgLog 2 (sprintf "goalSystem_perceiveCallback() called for event sentence=%s" (convSentenceToStr event.sentence));


    // first we need to give positive evidence for anticipations
    let goalUsedRootBeliefOpt: Term option = anticipate_revise goalMem beliefMem event.sentence.term (Truth(1.0,ANTICIPATION_POS_CONF)) timeNow;
    
    // * pos evidence for ==> where =/> appear
    // we need to add negative evidence for all ==> beliefs where the exact =/> appears as pred of ==>
    match goalUsedRootBeliefOpt with
    | Some goalUsedRootBelief ->
        goalSystem_implication_addEvidence goalMem beliefMem goalUsedRootBelief (+1) timeNow;
        ()
    | None ->
        ()
    
    // we satisfy goals in here which match to the event


    // * we need to handle goal completion by deriving goals and handling anticipation
    
    // this tries to derive the remainder of seq if "event" is fitting to a goal which is a sub-goal of a seq
    // ex: "event"=A.:|: goal=A! parent=(A,B)
    //     we derive B!
    //
    // ex: "event"=A.:|: goal=A! parent=(A,B,C)
    //     we derive (B,C)!

    // TODO MAYBE< make it work for perception of sequence
    //       ex: (a, b). :|:  , (a, b, c)! we derive |- c!
    //       ex: (a, b). :|:  , (a, b, c, d)! we derive |- (c, d)!
    //       note also that we need to derive a sequence if the remainder is a sequence with more than two elements, else it's just derived as non-sequence goal
    //     >
    
    let deriveGoalOfSeq () =
        // lookup goal
        let containsKey: bool = (Map.containsKey event.sentence.term goalMem.goalConcepts.mapToGoalConcepts);
        //goalsystem__dbgLog 2 (sprintf "containsKey=%b" containsKey);
        
        if containsKey then
            let goalConcept:GoalConcept = Map.find event.sentence.term goalMem.goalConcepts.mapToGoalConcepts;
            
            let fittingGoalTasks = List.filter (fun iv -> iv.sentence.term = event.sentence.term) goalConcept.content.taskContent; // we only care about goals with term = "event".sentence.term
            for iGoalTask in fittingGoalTasks do
                let isParentTermSeq =
                    match iGoalTask.parentGoalTerm with
                    | Some (Seq _) -> true;
                    | _ -> false;

                if isParentTermSeq then
                    //printfn "DBG: goalSystem_perceiveCallback(): parent is seq";


                    match iGoalTask.parentGoalTerm with
                    | Some parentGoalTerm ->
                        // lookup parent goal by iGoalTask.parentGoalTerm and derive based on that!
                        let fittingGoalParentTaskOpt =
                            if Map.containsKey parentGoalTerm goalMem.goalConcepts.mapToGoalConcepts then
                                let parentGoalConcept:GoalConcept = Map.find parentGoalTerm goalMem.goalConcepts.mapToGoalConcepts;

                                let fittingGoalTasks2 = List.filter (fun iv -> iv.sentence.term = parentGoalTerm) parentGoalConcept.content.taskContent; // filter tasks - we only care about the right task(s)

                                match fittingGoalTasks.Length with
                                | 0 -> 
                                    printfn "INTERNAL warn: concept referenced by iGoalTask.parentGoalTerm was not found! ignored";
                                    None
                                | _ ->
                                    Some (fittingGoalTasks.Head) // HACK< we just take the first one >
                            else
                                printfn "INTERNAL warn: concept referenced by iGoalTask.parentGoalTerm was not found! ignored";
                                None

                        match fittingGoalParentTaskOpt with
                        | Some fittingGoalParentTask ->

                            match parentGoalTerm with
                            | Seq s ->
                                let seqRemainder = s.Tail;

                                let conclTermOpt:Term option = // term of conclusion
                                    match seqRemainder.Length with
                                    | 0 -> 
                                        // invalid - ignore
                                        printfn "INTERNAL warn: encountered ill-formed seq with length=1! ignored";
                                        None
                                    | 1 ->
                                        Some seqRemainder.[0]
                                    | _ ->
                                        Some (Seq seqRemainder)

                                match conclTermOpt with
                                | Some conclTerm ->
                                    // build conclusion goal
                                    let conclTv: Truth = fittingGoalParentTask.sentence.truth; // HACK // TODO< compute TV correctly! >
                                    
                                    
                                    let conclSentence: Sentence = sentenceCreate conclTerm conclTv (stampMerge fittingGoalParentTask.sentence.stamp event.sentence.stamp) "!";
                                    
                                    // IMPLEMENTATION of goal driven curiosity
                                    if GOALSYS_EN_GOALDRIVEN_CURIOSITY then
                                        // debug "conclSentence" together with all information
                                        //    GDC means "goal driven curiosity"
                                        goalsystem__dbgLog2 false 2  (sprintf "goal driven curiosity: SITE_GDC_A parentGoalTerm= %s" (convTermToStr parentGoalTerm));
                                        goalsystem__dbgLog2 false 2  (sprintf "goal driven curiosity: SITE_GDC_A based on derivation.sentence= %s" (convSentenceToStr conclSentence));
                                        
                                        // * decide which is viable and has highest rating
                                        // formula to decide iff viable  isViable=exp (Truth(sentence.truth.f,sentence.truth.c + 0.55)) > 0.5 // HACKY formula which takes cofidence and frequency into account
                                        let isViable:bool = calcExp (Truth(conclTv.f,conclTv.c + 0.55)) > 0.5; // HACKY formula which takes cofidence and frequency into account

                                        if isViable && conclTv.c >= GOALSYS__GOALDRIVEN_CURIOSITY__MINMAL_CONF then // check to make sure that this is viable for curiosity
                                            // helper to check if goal was already used recently by goal driven babbling
                                            let rec checkWasRecentlyUsedForGoalDrivenCuriosity (v:GoalBasedCuriosity__Candidate) (rem:GoalBasedCuriosity__Candidate list) =
                                                if rem.Length > 0 then
                                                    if rem.Head = v then
                                                        true
                                                    else
                                                        checkWasRecentlyUsedForGoalDrivenCuriosity v rem.Tail
                                                else
                                                    false
                                            
                                            let candidate: GoalBasedCuriosity__Candidate = {parentGoalTerm=parentGoalTerm;tv=conclTv;};
                                            if not (checkWasRecentlyUsedForGoalDrivenCuriosity candidate goalMem.goalBasedCuriosity__recentlyUsed) then

                                                //type EnumQueueAction =
                                                //| NOTPRESENT // it is not present
                                                //| BETTERCHOICE // is the candidate a better choice?
                                                //| DONTADD // don't add because it is worse

                                                //let mutable actionBetterChoice = NOTPRESENT;

                                                // queue it as curiosity based motor babbling candidate
                                                let mutable idx=0;

                                                let mutable termExists:bool = false;

                                                let mutable bestChoiceExp: float = calcExp conclTv;
                                                let mutable bestChoiceIdx: int option = None;
                                                while idx < goalMem.goalBasedCuriosity__candidates.Length do
                                                    let sel = goalMem.goalBasedCuriosity__candidates.[idx];

                                                    if sel.parentGoalTerm = parentGoalTerm then
                                                        termExists <- true;
                                                        
                                                        if (calcExp sel.tv) > bestChoiceExp then
                                                            //action <- BETTERCHOICE;
                                                            bestChoiceExp <- (calcExp sel.tv);
                                                            bestChoiceIdx <- Some idx;
                                                            ()
                                                        else
                                                            // term is equal but this is not a better option
                                                            ()
                                                    else
                                                        ()
                                                    
                                                    idx <- idx+1;
                                                
                                                let actionBetterChoice = bestChoiceIdx.IsSome; // it this a bettter choice than an existing one?
                                                if actionBetterChoice then
                                                    // then we need to overwrite it with a better one

                                                    goalMem.goalBasedCuriosity__candidates <- List.updateAt bestChoiceIdx.Value {parentGoalTerm=parentGoalTerm;tv=conclTv;} goalMem.goalBasedCuriosity__candidates;
                                                    ()
                                                else if termExists then
                                                    // if the term exists and this is not a better choice then we don't do anything
                                                    ()
                                                else
                                                    // else we queue it

                                                    // queue it as curiosity based motor babbling candidate
                                                    goalMem.goalBasedCuriosity__candidates <- {parentGoalTerm=parentGoalTerm;tv=conclTv;} :: goalMem.goalBasedCuriosity__candidates;
                                                    ()
                                            else
                                                ()

                                            ()
                                        else
                                            ()
                                    else
                                        ()

                                    // put into memory
                                    goalPut2 goalMem conclSentence  (fittingGoalParentTask.depth+1) (Some parentGoalTerm) iGoalTask.goalUsedRootBeliefOpt SeqDetach timeNow |> ignore;
                                    ();
                                | None ->
                                    ();

                            | _ -> (); // is unreachable
                        | None -> (); // ignore
                    | _ -> 
                        (); // actually not reachable, ignore
                else
                    ();
            
            ();
        else
            ();
    deriveGoalOfSeq ();
    




    // * we need to do goal satisfaction
    goalKillRec goalMem event.sentence.term 0; // for now we just kill the goal

    ()


// helper (which is useful to outside for NAL9 ops for example) 
// which invokes a op by name
//
// /param perceiveCall queue up the event as perceived event?
let goalSystem__invokeOpByName (goalMem:GoalMem0) (invokedName:string) (args:Term list) (perceiveCall:bool) =
    let selOp = Map.find invokedName goalMem.registeredOps;
    goalsystem__dbgLog2 true 0 (sprintf "EXEC invoke op = %s" invokedName);
    selOp.callable goalMem args; // call op

    if perceiveCall then
        goalMem.outPerceivedEvents <- (Inh (SetExt [Prod args], Word invokedName)) :: goalMem.outPerceivedEvents; // queue up as a event to be perceived
        ()
    else
        ()


let goalSystem_execBestOp (goalMem:GoalMem0) (beliefMem:BeliefMem0) (timeNow:int64) =
    if goalMem.pendingOps.taskContent.Length > 0 then
        let selPendingOp: PendingOp = goalMem.pendingOps.taskContent.[0]; // HACK< we just select the first one >
        let selOpData:OpAndArgs = selPendingOp.opAndArgs;

        //goalsystem__dbgLog 1 (sprintf "try EXEC op = %s" selOpData.name);

        // lookup and execute
        if Map.containsKey selOpData.name goalMem.registeredOps then
            goalSystem__invokeOpByName goalMem selOpData.name selOpData.args true; // invoke op
            goalsystem__dbgLog 0 (sprintf "EXEC op selOpData.term = %s" (convTermToStr selOpData.term));
            


            // print all beliefs to console for debugging
            ///beliefMem_dbg_printAllBeliefs beliefMem;


            // we need to give negative evidence for executed anticipated consequences
            match selPendingOp.goalUsedRootBeliefOpt with
            | Some goalUsedRootBelief ->
                goalsystem__dbgLog 3 (sprintf "goalUsedRootBelief = %s" (convTermToStr goalUsedRootBelief));

                match goalUsedRootBelief with
                | PredImp (s,p) ->
                    let consequenceTerm = p;

                    let giveNegEvidence () =
                        goalsystem__dbgLog 2 (sprintf "giveNegEvidence() term = %s" (convTermToStr consequenceTerm));

                        // * anticipation
                        anticipate_revise goalMem beliefMem consequenceTerm (Truth(0.0,ANTICIPATION_NEG_CONF)) timeNow |> ignore;


                        // * neg evidence for ==> where =/> appear
                        // we need to add negative evidence for all ==> beliefs where the exact =/> appears as pred of ==>
                        goalSystem_implication_addEvidence goalMem beliefMem goalUsedRootBelief (-1) timeNow;


                    giveNegEvidence ();
                | _ ->
                    // unexpected, is probably a internal error, ignore
                    ();

                ()
            | None ->
                ()
            

    


            ();
        else
            printfn "WARN: op=%s was not registed! ignore" selOpData.name;
            ();

        goalMem.pendingOps.taskContent <- []; // HACK< we just flush all queued ops >
    else
        ();
    
    ()


// gives the goal system a chance to do processing before executing the next best op
let goalSystem__beforeExecBestOp (goalMem:GoalMem0) (timeNow:int64) =

    // EXPERIMENTAL feature: goal driven curiosity
    if GOALSYS_EN_GOALDRIVEN_CURIOSITY then

        // we need the recent events
        // TODO< project truth of recent events with some function by current time >
        // HACK< we just consider the last event >
        let mutable consideredEvents: NEvent list = []; // the considered last events
        let fifoSeq: NEvent list = fifo_viewAsSeq (); // view FIFO content as sequence of events
        if fifoSeq.Length > 0 then
            consideredEvents <- [fifoSeq.[fifoSeq.Length-1]];
            ()
        else
            ()

        let rng = new Random();
        if rng.NextDouble() < GOALSYS__GOALDRIVEN_CURIOSITY__BABBLE_PROB then

            // debug candidates
            for iCandidate in goalMem.goalBasedCuriosity__candidates do
                goalsystem__dbgLog2 true 2  (sprintf "goal driven curiosity: SITE_GDC_C: candidate=%s candidateTvExp=%f" (convTermToStr iCandidate.parentGoalTerm) (calcExp iCandidate.tv));
                ()


            if goalMem.goalBasedCuriosity__candidates.Length > 0 && consideredEvents.Length > 0 then
                // helper to filter the candidates
                let candidateFilterPredicateFn (candidate:GoalBasedCuriosity__Candidate): bool =
                    match candidate.parentGoalTerm with
                    | Seq seq ->
                        seq.[0] = consideredEvents.[0].sentence.term // filter for condidates where 
                    | _ ->
                        false // not a seq so it can't match first item of seq by definition

                let consideredCandidates: GoalBasedCuriosity__Candidate list = List.filter candidateFilterPredicateFn goalMem.goalBasedCuriosity__candidates;
                
                if consideredCandidates.Length > 0 then // we can only act on a candidate if at least one is present

                    let selCandidate: GoalBasedCuriosity__Candidate = consideredCandidates.[0]; // HACK< select first >
                    goalMem.goalBasedCuriosity__candidates <- []; // HACK< flush >

                    goalMem.goalBasedCuriosity__recentlyUsed <- selCandidate :: goalMem.goalBasedCuriosity__recentlyUsed; // add it because we selected it
                    
                    // keep under AIKR
                    if goalMem.goalBasedCuriosity__recentlyUsed.Length >= 3 then
                        goalMem.goalBasedCuriosity__recentlyUsed <- List.removeAt (goalMem.goalBasedCuriosity__recentlyUsed.Length-1) goalMem.goalBasedCuriosity__recentlyUsed;
                        ()
                    else
                        ()

                    match selCandidate.parentGoalTerm with
                    | Seq seq ->
                        let opTermMaybe: Term = seq.[1]; // we expect 2nd to be a op term

                        // TODO< check that it is a op term! >


                        // * invoke selected op by adding goal event now
                        let goal: Sentence = sentenceCreate opTermMaybe TRUTH_DEFAULT (stampNew ()) "!";

                        goalsystem__dbgLog2 true 2  (sprintf "goal driven curiosity: SITE_GDC_B: babble goalTerm = %s" (convTermToStr goal.term));
                        goalPut goalMem goal timeNow |> ignore;

                        ()
                    | _ ->
                        () // ignore
                    
                    ()
                else
                    ()
            else
                ()
        else
            ()
    else
        ()

    ()



// print all goals to console
// used for debugging
let goalSystem_printAll (goalMem:GoalMem0) =
    printfn "GOAL content::tasks :";

    for iBucket in goalMem.goalDepthBuckets do
        for iTask in iBucket.tasks.taskContent do
            let conceptName:Term = iTask.term;
            printfn "bucketDepth=%i  %s" iBucket.thisDepth (convTermToStr conceptName);
            ();
        ();
    
    printfn "GOAL content::goals :";
    for iConcept in goalMem.goalConcepts.mapToGoalConcepts.Values do
        printfn "  concept=%s" (convTermToStr iConcept.name);

        printfn "    content :";
        for iGoal in iConcept.content.taskContent do
            let parentGoalTermAsStr:string =
                match iGoal.parentGoalTerm with
                | Some term -> convTermToStr term;
                | None -> "<<NULL>>";
            printfn "       depth=%i : %s  parent=%s" iGoal.depth (convSentenceToStr iGoal.sentence) parentGoalTermAsStr;
        ();

        printfn "    contentChildren :";
        for iGoal in iConcept.contentChildren.taskContent do
            let parentGoalTermAsStr:string =
                match iGoal.parentGoalTerm with
                | Some term -> convTermToStr term;
                | None -> "<<NULL>>";
            printfn "       depth=%i : %s  parent=%s" iGoal.depth (convSentenceToStr iGoal.sentence) parentGoalTermAsStr;
        ();

    ()


// do work in a async worker
let goalSystem_doWorker0 (goalMem:GoalMem0) =
    async {
        for i=0 to 10 do
            let taskOpt = goalMem.implUpdateQueue.retMaxTask();
            match taskOpt with
            | Some task ->
                goalMem.implUpdateQueue.deleteMaxTask(); // remove task from memory

                if 2 >= 2 then
                    printfn "DBG[2] goal system: exec task: decrease freq  term=%s" (convTermToStr task.sentence.term);
                    ()
                else
                    ()
                
                // add virtual negative evidence
                let truth = task.sentence.truth;
                let revEvidenceTruth: Truth =
                    match task.sign with
                    | 1 -> Truth(1.0,ANTICIPATION_POS_CONF*0.1) // positive
                    | -1 -> Truth(0.0,ANTICIPATION_NEG_CONF*0.1) // negative
                    | _ -> Truth(0.0,ANTICIPATION_NEG_CONF*0.1) // HACK< default to make compiler happy >
                let newTruth:Truth = calcBinaryTruth "revision" truth revEvidenceTruth;
                task.sentence.truth <- newTruth; // update truth



                if 2 >= 2 then
                    printfn "DBG[2] goal system: exec task: concl sentence = %s" (convSentenceToStr task.sentence);
                    ()
                else
                    ()
                


                ()
            | None ->
                ()

        ()
    } |> Async.RunSynchronously

    ()















