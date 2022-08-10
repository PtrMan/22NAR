module NarHelpers

open Nar
open Sentence
open Truth
open Stamp
open Term

// helpers for NAR stuff used mainly for environment tests


// helper to feed single term goal to NAR
let nar_helper__inputGoalEventTermName (nar:Nar0) (goalTermName:string) =
    let goal0: Sentence = sentenceCreate (Word goalTermName) TRUTH_DEFAULT (stampNew ()) "!";
    nar_sync__inputGoalEvent nar goal0;
