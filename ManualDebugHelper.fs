module ManualDebugHelper

open Nar
open Term
open Sentence
open Truth
open Stamp

// helper to play back events
let manualDebugHelper_playbackEvents (nar:Nar0) (eventsTerms: Term list) =
    for iEventTermToPlayback in eventsTerms do
        if true then
            let s0:Sentence = sentenceCreate iEventTermToPlayback TRUTH_DEFAULT (stampNew ()) ".";
            nar_sync__inputEvent nar s0 |> ignore;
            ();
        else
            ();

        // give reasoner resources
        for i=1 to 3 do
            nar_sync__step nar;
            nar_sync__advanceTime nar;

    ()