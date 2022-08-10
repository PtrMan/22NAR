module GContainer

// general container for tasks or beliefs of a certain type
type GContainer<'TaskType> = {
    mutable taskContent: 'TaskType list;

    fnCmp: 'TaskType -> 'TaskType -> bool; // compare function used for contain test


    capacity: int;
    fnRanking: 'TaskType -> float; // used to keep under AIKR while sorting the most important itemes
    // TODO high< add maximal number of items "capacity" to keep under AIKR together with a fnRanking: 'TaskType -> 'TaskType -> int >
}

let GContainer_create<'TaskType> (fnCmp:'TaskType -> 'TaskType -> bool) (fnRanking:'TaskType -> float) (capacity:int): GContainer<'TaskType> =
    {taskContent=[]; fnCmp =fnCmp; fnRanking=fnRanking; capacity=capacity; }

let GContainer_put<'TaskType> (container:GContainer<'TaskType>) (task:'TaskType): bool =
    let has = List.exists (fun iv -> container.fnCmp iv task) container.taskContent; // compute if the task already exists
    if not has then
        container.taskContent <- task :: container.taskContent;
        container.taskContent <- container.taskContent |> List.sortBy container.fnRanking |> List.truncate container.capacity; // keep under AIKR
        ();
    else
        ();
    not has
