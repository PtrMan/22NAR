module Sentence

open Term
open Stamp
open Truth

type Sentence = {
    term : Term;
    mutable truth: Truth;
    stamp : Stamp;
    punctation: string;

    uniqueId: int64; // unique id 
}

let mutable SENTENCE_uniqueIdCounter: int64 = 1;

let sentenceCreate (term:Term) (truth:Truth) (stamp:Stamp) (punctation:string): Sentence =
    let thisId: int64 = SENTENCE_uniqueIdCounter;
    SENTENCE_uniqueIdCounter <- SENTENCE_uniqueIdCounter + 1L;

    {term=term;truth=truth;stamp=stamp;punctation=punctation;uniqueId=thisId}
