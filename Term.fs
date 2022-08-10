module Term

// LICENSE: MIT
type Term = | Word of string 
            | UVar of int64 // universal variable - type is determined by context
            | Inh of Term * Term
//            | Sim of Term * Term
            | SetExt of Term list    // {}
//            | SetInt of Term list  // []
            | Prod of Term list
            | Imp of Term * Term     //| Equ of Term * Term
            | PredImp of Term * Term
        //  | ConImp of Term * Term    | RetImp of Term * Term
        //    | ConEqu of Term * Term  | PreEqu of Term * Term
            | Seq of Term list     
            | Par of Term list
            | And of Term list
//    | Or of Term * Term        | Not of Term


//            | IVar of int            | DVar of int              | QVar of int
//            | ExtInt of Term * Term  | IntInt of Term * Term
//            | ExtDif of Term * Term  | IntDif of Term * Term
//            | ExtImg1 of Term * Term | ExtImg2 of Term * Term
//            | IntImg1 of Term * Term | IntImg2 of Term * Term
