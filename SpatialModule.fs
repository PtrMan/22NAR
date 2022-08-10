module SpatialModule

open System

open Sentence
open SentenceUtils

type StimulusA = {
    dat: Sentence;

    outLinks: ALink list; // links going out from this stimulus
}
// link between stimulus
and ALink = {
    origin: StimulusA;
    target: StimulusA;
}


// sample a path with the length
let samplePathBeta (s:StimulusA) (pathLen:int) =
    let mutable trace = [];

    let mutable curr = s;

    let rng = new Random();    

    for i=1 to pathLen do
        if s.outLinks.Length > 0 then
            let idx0 = rng.Next(s.outLinks.Length);
            let selLink = s.outLinks.[idx0];

            printfn "%s" (convSentenceToStr s.dat);
            trace <- s.dat :: trace;

            curr <- selLink.target;
            ()
        else
            ()

    trace











//A B
//    C

type GridPerceiveField = {
    arr: Sentence list list; // array of perception in the field
    width: int;
    height: int;
}

// helper
let gridRetByPos (field:GridPerceiveField) (y:int) (x:int) =
    if x>=0 && x<field.width && y>=0 && y<field.height then
        field.arr.[field.width*y + x]
    else
        []

// helper
(*
let gridCalcPaths (origin:Sentence list) (other:Sentence list) =
    let mutable res = [];
    
    for a in origin do
        for b in other do
            res <- List.append res (TODOcombine a b);
    
    res



let gridPerceive_ (field:GridPerceiveField) =
    let mutable arr = [];
    
    for iy=0 to field.height-1 do
        for ix=0 to field.width-1 do
            let c = gridRetByPos field iy ix;
            let cmx = gridRetByPos field iy (ix-1);
            let cpx = gridRetByPos field iy (ix+1);
            let cmy = gridRetByPos field (iy-1) ix;
            let cpy = gridRetByPos field (iy+1) ix;

            for iv in [cmx;cpx;cmy;cpy] do
                let a = gridCalcPaths c iv;
                arr <- List.append arr a;
                ()

    arr
*)



