module NEvent

open Sentence
open SentenceUtils

type NEvent = {
    minOccTime : int64 // used for sequences etc. is the time of the first event of a sequence etc. is used for composition
    occTime : int64
    sentence : Sentence
    isDerived : bool; // was the event derived? is used for debugging
}

// util
let convEventToStr (event:NEvent): string =
    sprintf "%s occTime=%i" (convSentenceToStr event.sentence) event.occTime
