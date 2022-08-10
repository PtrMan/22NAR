module VarIntro

open System

open Term



// count occurrences of (sub)term
let termCountOccurencesOfSubterm (term:Term): Map<Term,int> =
    let mutable (map:Map<Term,int>) = Map.empty<Term,int>;

    // helper to increment counter
    let inc (t:Term) =
        if Map.containsKey t map then
            let (v:int) = (Map.find t map) + 1;
            map <- Map.add t v map;
            ()
        else
            map <- Map.add t 1 map;
            ()
        
        ()

    let rec work (t:Term) =
        inc t;

        match t with
        | Inh (s,p) ->
            work s;
            work p;
        | Imp (s,p) ->
            work s;
            work p;
        | PredImp (s,p) ->
            work s;
            work p;
        | SetExt l ->
            for iv in l do
                work iv;
        | Prod l ->
            for iv in l do
                work iv;
        | Seq l ->
            for iv in l do
                work iv;
        | Par l ->
            for iv in l do
                work iv;
        | And l ->
            for iv in l do
                work iv;
        | _ -> ()
        
        ()
    work term;
    
    map


// returns variables terms which can be introduced as variables
//
// note that it doesn't proceed recursivly if it found a candidate, ex: ((a,c), b, (a,c)) will return [(a,c)] but not [a]
let calcVarIntroducible (term:Term): Term list =
    // algorithm:
    // * count number of occurences of sub-terms
    // * Introduce variable if count>=2

    let (subtermCountsMap:Map<Term,int>) = termCountOccurencesOfSubterm term;

    //printfn "%A" subtermCountsMap;
    
    // filter by count >= 2
    let (candidateTerms:Term list) = 
        subtermCountsMap
        |> Map.toList
        |> List.filter (fun (iTerm, iCnt) -> iCnt >= 2)
        |> List.map (fun (iTerm, iCnt) -> iTerm) // get rid of count
    
    candidateTerms



let termIntroVarSpecific (term:Term) (candidateTerms:Term list): Term =
    // algorithm:
    // * introduce variables
    // * replace terms with vars recursively

    let mutable uniqueVarName:int64 = 0; // counter used for unique variable name
    
    // give each term to replace a unique variablename
    let mutable uniqueVarNames:Map<Term,int64> = Map.empty<Term,int64>;
    for iTerm in candidateTerms do
        let iVarname = uniqueVarName;
        uniqueVarName <- uniqueVarName + 1L;
        uniqueVarNames <- Map.add iTerm iVarname uniqueVarNames;
    
    // substitute

    let rec subst (t:Term): Term =
        if Map.containsKey t uniqueVarNames then
            let (varname:int64) = Map.find t uniqueVarNames;
            UVar varname
        else
            match t with
            | Inh (s, p) ->
                Inh ((subst s), (subst p))
            | SetExt l ->
                SetExt (List.map subst l)
            | Prod l ->
                Prod (List.map subst l)
            | Imp (s, p) ->
                Imp ((subst s), (subst p))
            | PredImp (s, p) ->
                PredImp ((subst s), (subst p))
            | And l ->
                And (List.map subst l)
            | Seq l ->
                Seq (List.map subst l)
            | Par l ->
                Par (List.map subst l)
            | _ -> t

    let res = subst term;
    res


// algorithm to introduce var if count of (sub)-term is >= 2
let termIntroVarDotWhereCnt2 (term:Term): Term =
    // algorithm:
    // * compute variable candidates
    // * introduce variables
    // * replace terms with vars recursively

    let (candidateTerms:Term list) = calcVarIntroducible term;
    
    termIntroVarSpecific term candidateTerms





// helper to get variations of map without one item
let helper_list_candidatesWithoutOne (list:Term list): Term list list =
    if list.Length > 0 then
        let mutable res = [];
        
        for iRemoveIdx=0 to list.Length-1 do
            let listWithRemoved = List.removeAt iRemoveIdx list;
            res <- listWithRemoved :: res;

        res
    else
        []


let isVar (term:Term): bool =
    match term with
    | UVar _ -> true
    | _ -> false


// computes if the term with var's is to general
//
// example for to general terms are
// examples:
//    (%0, %1)  is to general because nothing in the sequence is specified
//    %0 =/> %1 is to general because it applies to everything
let termIsVarToGeneral (term:Term): bool =
    match term with
    | Seq items when List.forall isVar items -> true
    | Par items when List.forall isVar items -> true
    | PredImp (s,p) when isVar s || isVar p -> true
    | Imp (s,p) when isVar s || isVar p -> true
    | Inh (s,p) when isVar s && isVar p -> true
    | Prod items when List.forall isVar items -> true
    | _ ->
        false // else it's not to general

// recursive version
let rec termIsVarToGeneralRec (term:Term): bool =
    if termIsVarToGeneral term then
        true
    else
        match term with
        | Word _ -> false
        | UVar _ -> false
        | Inh (s,p) -> termIsVarToGeneralRec s || termIsVarToGeneralRec p
        | SetExt items -> List.exists termIsVarToGeneralRec items
        | Prod items -> List.exists termIsVarToGeneralRec items
        | Imp (s,p) -> termIsVarToGeneralRec s || termIsVarToGeneralRec p
        | PredImp (s,p) -> (termIsVarToGeneralRec s || termIsVarToGeneralRec p) || isVar p // note that it's to generic when p is a variable!
        | Seq items -> List.exists termIsVarToGeneralRec items
        | Par items -> List.exists termIsVarToGeneralRec items
        | And items -> List.exists termIsVarToGeneralRec items





// returns a list of terms where variables are introduced according to some hardcoded var-intro rules
// * don't return terms which have to general variables
let termIntroVarCalcCandidates (term:Term): Term list =

    let introducibleVars: Term list = calcVarIntroducible term; // get terms which are introducible as vars
    
    let a: Term list  list = helper_list_candidatesWithoutOne introducibleVars; // get combinations of introducible variables for term
    let b: Term list  list = introducibleVars :: a; // we also want to consider the version where all vars are introduced

    // do actual substitutions
    let outCandidates: Term list =
        List.map (fun iv -> termIntroVarSpecific term iv) b |>
        List.filter (fun iv -> not (termIsVarToGeneralRec iv)); // we don't want to later consider with to general terms
    
    outCandidates
