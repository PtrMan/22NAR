module TermUtils

open Term


let rec convTermToStr (term:Term) =
    match term with
    | UVar id -> sprintf "%%%i" id
    | Word w -> w
    | Inh (s, p) -> sprintf "<%s --> %s>" (convTermToStr s) (convTermToStr p)
    | Imp (s, p) -> sprintf "<%s ==> %s>" (convTermToStr s) (convTermToStr p)
    | PredImp (s, p) -> sprintf "<%s =/> %s>" (convTermToStr s) (convTermToStr p)
    | Prod l ->
        let lStr = l |> List.map (fun iv -> convTermToStr iv);
        let lStr2 = String.concat "*" lStr
        sprintf "(%s)" lStr2
    | And l ->
        let lStr = l |> List.map (fun iv -> convTermToStr iv);
        let lStr2 = String.concat " && " lStr
        sprintf "(%s)" lStr2
    | Seq l -> 
        let lStr = l |> List.map (fun iv -> convTermToStr iv);
        let lStr2 = String.concat "," lStr
        sprintf "(%s)" lStr2
    | Par l -> 
        let lStr = l |> List.map (fun iv -> convTermToStr iv);
        let lStr2 = String.concat " &| " lStr
        sprintf "(%s)" lStr2
    | SetExt l ->
        let lStr = l |> List.map (fun iv -> convTermToStr iv);
        let lStr2 = String.concat " " lStr
        sprintf "{%s}" lStr2

// return all sub-terms which are relevant for conceptual lookup
let rec calcConceptualTerms (term:Term): Term list =
    // TODO LOW< return a set as a list of the obtained result for more efficiency downstream >

    match term with
    | Word _ -> [term]
    | Inh (s, p) -> List.concat [[term]; calcConceptualTerms s; calcConceptualTerms p]
    | Imp (s, p) -> List.concat [[term]; calcConceptualTerms s; calcConceptualTerms p]
    | PredImp (s, p) -> List.concat [[term]; calcConceptualTerms s; calcConceptualTerms p]
    | Prod l ->
        List.concat [[term];l |> List.map (fun iv -> calcConceptualTerms iv) |> List.concat]
    | And l ->
        List.concat [[term];l |> List.map (fun iv -> calcConceptualTerms iv) |> List.concat]
    | Seq l ->
        List.concat [[term];l |> List.map (fun iv -> calcConceptualTerms iv) |> List.concat]
    | Par l ->
        List.concat [[term];l |> List.map (fun iv -> calcConceptualTerms iv) |> List.concat]
    | SetExt l ->
        List.concat [[term];l |> List.map (fun iv -> calcConceptualTerms iv) |> List.concat]
    | _ -> []

// normalizes variables of a term
let normalizeVar (t:Term): Term =
    let mutable normalizedVarCnt: int64 = 0L; // counter for normalized variables
    let mutable m: Map<int64, int64> = Map.empty<int64, int64>; // map from unnormalized variables to normalized variables
    
    let rec recFn (t2:Term) =
        match t2 with
        | Word w ->
            t2
        | UVar varname ->
            let varnameOut =
                if Map.containsKey varname m then
                    Map.find varname m
                else
                    let thisNormalizedVar: int64 = normalizedVarCnt;
                    m <- Map.add varname thisNormalizedVar m;
                    normalizedVarCnt <- normalizedVarCnt + 1L;
                    thisNormalizedVar

            UVar varnameOut
        | Inh (s,p) ->
            Inh (recFn s, recFn p)
        | SetExt list ->
            SetExt (List.map recFn list)
        | Prod list ->
            Prod (List.map recFn list)
        | Imp (s,p) ->
            Imp (recFn s, recFn p)
        | PredImp (s,p) ->
            PredImp (recFn s, recFn p)
        | Seq list ->
            Seq (List.map recFn list)
        | Par list ->
            Par (List.map recFn list)
        | And list ->
            And (List.map recFn list)
    
    recFn t
