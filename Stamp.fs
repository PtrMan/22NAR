
// LICENSE: MIT
module Stamp

open System
open System.Linq

(* not needed
let rec interleave xs ys =
    match xs, ys with
    |    [],    [] -> []
    | x::xs,    [] -> x::interleave xs []
    |    [], y::ys -> y::interleave [] ys
    | x::xs, y::ys -> x::y::interleave xs ys
*)

let rec revInterleave xs ys acc =
    match xs, ys with
    |    [],    [] -> acc
    | x::xs,    [] -> revInterleave xs [] (x::acc)
    |    [], y::ys -> revInterleave [] ys (y::acc)
    | x::xs, y::ys -> revInterleave xs ys (y::x::acc)

let merge e1 e2 =
    revInterleave e1 e2 []
    |> List.truncate 40 |> List.rev // Not necessary to check for distinct as the sets are non-overlapping



type Stamp = {
    ids: int64 list;
}

let mutable stampIdCnt:int64 = 1L;

let stampNewId (): int64 =
    let id = stampIdCnt;
    stampIdCnt <- stampIdCnt + 1L;
    id

let stampCheckOverlap (a:Stamp) (b:Stamp): bool =
    let checkOverlap (a: 'a seq) (b: 'a seq) = a.Intersect(b).Count() > 0;
    checkOverlap a.ids b.ids

let stampMerge (a:Stamp) (b:Stamp): Stamp =
    {ids = merge a.ids b.ids}

let stampMergeMany (stamps:Stamp list): Stamp =
    let mutable ids = stamps.Head.ids;
    for iStamp in stamps.Tail do
        ids <- merge ids iStamp.ids;

    {ids = ids}

let stampNew (): Stamp =
    {ids = [stampNewId ()]}

let checkStampSame (a:Stamp) (b:Stamp): bool =
    a.ids = b.ids

let stampConvToStr (stamp:Stamp): string =
    let lStr = stamp.ids |> List.map (fun iv -> Convert.ToString iv);
    let str = String.concat " " lStr;
    str
