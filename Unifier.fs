module Unifier

open Term

// hold the result of the unification
type UnifyResult = {
    varAssignments: Map<int64, Term>
}

// tries to unify variables with terms
let unifier_try (a:Term) (b:Term) : UnifyResult option =
    let mutable varAssignments: Map<int64, Term> = Map.empty<int64, Term>; // contains variable assignments

    let rec unifyRecursive (ta:Term) (tb:Term) =
        match ta, tb with
        | Word tan, Word tbn when tan = tbn ->
            true
        | Inh (tas, tap), Inh (tbs, tbp) ->
            (unifyRecursive tas tbs) && (unifyRecursive tap tbp)
        | Imp (tas, tap), Imp (tbs, tbp) ->
            (unifyRecursive tas tbs) && (unifyRecursive tap tbp)
        | PredImp (tas, tap), PredImp (tbs, tbp) ->
            (unifyRecursive tas tbs) && (unifyRecursive tap tbp)
        
        | SetExt sa, SetExt sb when sa.Length = sb.Length ->
            List.map2 unifyRecursive sa sb |> List.reduce (&&)
        | Prod sa, Prod sb when sa.Length = sb.Length ->
            List.map2 unifyRecursive sa sb |> List.reduce (&&)
        | Seq sa, Seq sb when sa.Length = sb.Length ->
            List.map2 unifyRecursive sa sb |> List.reduce (&&)
        | Par sa, Seq sb when sa.Length = sb.Length ->
            List.map2 unifyRecursive sa sb |> List.reduce (&&)
        | And sa, And sb when sa.Length = sb.Length ->
            List.map2 unifyRecursive sa sb |> List.reduce (&&)
        
        | UVar va, UVar vb ->
            false // variables don't unify with each other!
        | UVar va, other ->
            if Map.containsKey va varAssignments then
                other = (Map.find va varAssignments)
            else
                varAssignments <- Map.add va other varAssignments;
                true
        | other, UVar vb ->
            if Map.containsKey vb varAssignments then
                other = (Map.find vb varAssignments)
            else
                varAssignments <- Map.add vb other varAssignments;
                true
        
        | _ -> false

    if unifyRecursive a b then // did unify?
        Some {varAssignments=varAssignments;} // return unify result
    else
        None


let rec unifier_apply (unify:UnifyResult) (term:Term): Term =
    match term with
    | Word _ -> term
    | UVar varId ->
        if Map.containsKey varId unify.varAssignments then
            Map.find varId unify.varAssignments
        else
            term
    | Inh (s,p) ->
        Inh (unifier_apply unify s, (unifier_apply unify p))
    | Imp (a,c) ->
        Imp (unifier_apply unify a, (unifier_apply unify c))
    | PredImp (s,p) ->
        PredImp (unifier_apply unify s, (unifier_apply unify p))
    | SetExt list ->
        SetExt (list |> List.map (unifier_apply unify))
    | Prod list ->
        Prod (list |> List.map (unifier_apply unify))
    | Seq list ->
        Seq (list |> List.map (unifier_apply unify))
    | Par list ->
        Par (list |> List.map (unifier_apply unify))
    | And list ->
        And (list |> List.map (unifier_apply unify))

