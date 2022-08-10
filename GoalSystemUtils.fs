module GoalSystemUtils

open Term

// utilities for goal system related to goal system


type OpAndArgs = {
    term: Term; // complete term of op, mainly used for feedback to procedural reasoner
    name: string;
    args: Term list;
}

// tries to interpret the term as a operator call
// /return None if it can't be interpreted as such
let matchOp (term:Term): OpAndArgs option =
    match term with
    | Inh (s0,Word name) when name.Length >= 1 && name[0] = '^' ->
        match s0 with
        | SetExt [set0] ->
            match set0 with
            | Prod args ->
                Some {term=term; name=name; args=args}
            | _ -> None
        | _ -> None
    | _ -> None

// returns if the term is a valid op
let checkIsOp (term:Term): bool =
    (matchOp term).IsSome

