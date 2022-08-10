module VarUtils

open Term

// utilities for variables

// return all existing variables of the term
let retExistingVars (t:Term) =
    let mutable thisMap = Map.empty<int64,bool>;
    
    let rec helper t2 =
        match t2 with
        | Word _ ->
            ()
        | UVar name ->
            thisMap <- Map.add name true thisMap;
        | Inh (s,p) ->
            helper s;
            helper p;
        | SetExt tList ->
            for it in tList do
                helper it;
        | Prod tList ->
            for it in tList do
                helper it;
        | Imp (a,c) ->
            helper a;
            helper c;
        | PredImp (s,p) ->
            helper s;
            helper p;
        | Seq  tList ->
            for it in tList do
                helper it;
        | Par  tList ->
            for it in tList do
                helper it;
        | And  tList ->
            for it in tList do
                helper it;

    helper t;

    thisMap |> Map.toList |> List.map (fun (k,v) -> k) |> Set.ofList

// checks if the set of variables overlap
let checkVarOverlap (a:Set<int64>) (b:Set<int64>) =
    (Set.intersect a b |> Set.count) > 0


