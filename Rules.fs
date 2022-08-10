// module for inference rules
module Rules

open Unifier

open Term
open TermUtils // for debugging
open Truth

// see: NAL reference  page 43
// <a0 ==> <a1 ==> c1>>. |-
// <(a0 && a1) ==> c1>.
let ruleNal5_fold (term:Term): Term option =
    match term with
    | Imp (a0,c0) ->
        match c0 with
        | Imp (a1,c1) ->
            // rewrite
            Some (Imp (And [a0;a1], c1))
        | _ -> None
    | _ -> None




// list helper
// find first index where it matches
//let listIndexOf (v:Term) (l:Term list): int option =
//    if List.exists (fun iv -> iv = v) l then
//        Some (List.findIndex (fun iv -> iv = v) l)
//    else
//        None

// list helper
// find first index where it unifies
let listIndexOfFirstUnify (v:Term) (l:Term list): int option =
    let rec r0 (l2:Term list) (currIdx:int) =
        if l2.Length > 0 then
            let head = l2.Head;
            let unifyResultOpt = unifier_try v head;
            match unifyResultOpt with
            | Some unifyResult ->
                Some currIdx // return hit index
            | None ->
                r0 l2.Tail (currIdx+1) // continue search with next element
        else
            None // couldn't find
    
    r0 l 0



// inference rule
// A., <(A && B) ==> C>. |- B ==> C.
// A., <(B && A && C) ==> C>. |- (B && C) ==> C.
let nal5_conjMatchAndReduce (a:Term) (aTv:Truth) (b:Term) (bTv:Truth): (Term*Truth) option =
    match b with
    | Imp ((And andList),bc) -> // A has to match
        let (indexOfAOpt:int option) = listIndexOfFirstUnify a andList; // we need to find the A
        match indexOfAOpt with
        | Some indexOfA ->
            let selTerm = andList.[indexOfA];
            let unifyResultOpt = unifier_try a selTerm;
            let unifyResult = unifyResultOpt.Value;

            let andListWithoutA = List.removeAt indexOfA andList; // we need to remove A

            // we need to return a valid term
            let concjAsTerm =
                if andListWithoutA.Length = 1 then
                    andListWithoutA.Head
                else
                    And andListWithoutA

            let conclTerm = Imp (concjAsTerm, bc);
            let conclTerm2 = unifier_apply unifyResult conclTerm; // apply unify variables

            // TODO< compute TV >
            Some (conclTerm2, TRUTH_DEFAULT)
        | None ->
            None
    | _ -> None




// inference rule
// A., <A ==> C>. |- C.
let nal5_conjMatch (a:Term) (aTv:Truth) (b:Term) (bTv:Truth): (Term*Truth) option =
    match b with
    | Imp (ba,bc) when (unifier_try a ba).IsSome -> // A has to match
        let unifyResultOpt = unifier_try a ba;
        let unifyResult = unifyResultOpt.Value;

        let bc2 = unifier_apply unifyResult bc;
        
        // TODO< compute TV >
        Some (bc2, TRUTH_DEFAULT)
    | _ -> 
        None



// inference rule
// detach
// B!, A =/> B. |- A!
let nal7_detachPredImpl (goalTerm:Term) (goalTv:Truth) (otherTerm:Term) (otherTv:Truth): (Term*Truth) option =
    match otherTerm with
    | PredImp (otherA, otherB) when otherB = goalTerm ->
        // check if we derive a legal conclusion
        let isLegal:bool = match otherA with
        | Seq otherASeqTerms -> not (otherASeqTerms.[0] = goalTerm) // ex: illegal: (a, b) =/> a
        | _ -> true
        
        if isLegal then
            let truth = calcBinaryTruth "deduction" otherTv goalTv; // see https://github.com/opennars/OpenNARS-for-Applications/blob/06c65f6c08ecf22943b1f28764a60d1c146403f3/src/Inference.c#L107
            Some (otherA, truth)
        else
            printfn "AVOIDED non-legal %s %s" (convTermToStr otherTerm) (convTermToStr goalTerm);
            
            None
    | _ ->
        None

// inference rule
// detach
// (A, B)! |- A!
let nal7_detachSeq (t:Term) (tv:Truth): (Term*Truth) option =
    match t with
    | Seq l ->
        Some (l.Head, tv)
    | _ ->
        None

