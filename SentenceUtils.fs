module SentenceUtils

open Sentence
open TermUtils
open Stamp

// with stamp
let convSentenceToStr2 (s:Sentence): string =
    let termStr = convTermToStr s.term;
    sprintf "%s%s {%f %f} %A" termStr s.punctation s.truth.f s.truth.c s.stamp.ids


let convSentenceToStr (s:Sentence): string =
    let termStr = convTermToStr s.term;
    sprintf "%s%s {%f %f}" termStr s.punctation s.truth.f s.truth.c

// check if the sentence is the same
let checkSentenceSame (a:Sentence) (b:Sentence): bool =
    a.term = b.term && a.punctation = b.punctation && checkStampSame a.stamp b.stamp && abs(a.truth.f-b.truth.f) < 0.001 && abs(a.truth.c-b.truth.c) < 0.001
