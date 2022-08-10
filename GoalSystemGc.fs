module GoalSystemGc

open Term
open GoalSystem

type GoalTaskWithScore = {
    goalTask: GoalTaskOfConcept;
    score: float;
}

let goalSystemGc_do (goalMem:GoalMem0) (timeNow:int64) =
    // NOTE< syncronous implementation >

    
    // * rank active goals by score function
    let mutable goalTasksWithScore: GoalTaskWithScore list = [];
    for iGoalConceptKey in goalMem.goalConcepts.mapToGoalConcepts.Keys do
        let iGoalConcept = goalMem.goalConcepts.mapToGoalConcepts.[iGoalConceptKey];
        
        for iGoalTask in iGoalConcept.content.taskContent do
            let score: float = (float (exp ((float (timeNow - iGoalTask.lastUpdateTime))*(-0.01))))*(iGoalTask.sentence.truth.c) ;// compute score
            goalTasksWithScore <- {goalTask=iGoalTask; score=score} ::goalTasksWithScore;
            ()

    // * rank by sorting
    let rankedGoalTasksWithScore: GoalTaskWithScore list = goalTasksWithScore |> List.sortByDescending (fun iv -> iv.score);

    // * decide which goals should get removed
    let removeGoalTasksWithScoreList: GoalTaskWithScore list = 
        if rankedGoalTasksWithScore.Length > goalMem.goalConcepts.maxNActiveGoals then 
            rankedGoalTasksWithScore |> List.removeManyAt 0 goalMem.goalConcepts.maxNActiveGoals
        else
            []

    // * remove goals from goal concepts and "goalMem.goalDepthBuckets"
    for iGoalWithScoreToRemove in removeGoalTasksWithScoreList do
        let iGoalTerm: Term = iGoalWithScoreToRemove.goalTask.sentence.term;

        goalMem.goalConcepts.mapToGoalConcepts <- goalMem.goalConcepts.mapToGoalConcepts |> Map.remove iGoalTerm;
        ()
    
    for iGoalWithScoreToRemove in removeGoalTasksWithScoreList do
        let iGoalTerm: Term = iGoalWithScoreToRemove.goalTask.sentence.term;

        for iGoalBucket in goalMem.goalDepthBuckets do
            iGoalBucket.tasks.taskContent <- iGoalBucket.tasks.taskContent |> List.filter (fun iv -> iv.term <> iGoalTerm);

    ()

