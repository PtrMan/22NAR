// license is MIT

module TaskPriorityQueue

open C5
open Sentence

// task which carries work unit to get processed
type Task0 = {
    // TODO< add attention value >

    sentence: Sentence;
    sign: int; // sign of revision evidence    -1 is neg evidence, 1 is pos evidence
}


type TaskPriorityQueue(maxSize : int) =
    let q = IntervalHeap<Task0>(maxSize) :> IPriorityQueue<Task0>
    let map = HashDictionary<Sentence, IPriorityQueueHandle<Task0>>() :>IDictionary<Sentence, IPriorityQueueHandle<Task0>>


    let addTask key (task : Task0) h =
        q.Add(h, task) |> ignore
        map.Add(key, h.Value)

    let deleteMinTask () =
        let (deleted, h) = q.DeleteMin()
        let h = ref h;
        match map.Remove(deleted.sentence, h ) with
        | true -> ()
        | false -> failwith "TaskPriorityQueue.Insert() : failed to remove on maxSize"
        h.Value
    


    let update (key, task) =
        if key > q[map[key]].sentence then
            let h = map.[key]
            q.[h] <- task

    member _.Enqueue(task) =
        if map.Contains task.sentence then
            update(task.sentence, task)
        elif map.Count >= maxSize then
            if task >= q.FindMin() then
                ref <| deleteMinTask()
                |> addTask task.sentence task
        else
            addTask task.sentence task (ref null)

    member _.Decay() = 
        for kvp in map do
            ()
            //let qh = kvp.Value
            //q[qh] <- {q[qh] with AV = {STI = q[qh].AV.STI * q[qh].AV.LTI; LTI = q[qh].AV.LTI}}

            // TODO< implement >
    
    member _.deleteMaxTask () =
        let (deleted, h) = q.DeleteMax();
        let h = ref h;
        match map.Remove(deleted.sentence, h ) with
        | true -> ()
        | false -> (); //IGNORE //failwith "TaskPriorityQueue.Insert() : failed to remove"
                       // TODO< search for cause why this fails >
        ()
    
    member _.retMaxTask() =
        match q.IsEmpty with
        | true  -> None
        | false -> Some (q.FindMax())

    member _.GetTasks() = q |> Seq.toList
