module AttentionDeclarative

type DeclAv = {
    // usage
    // TODO< make fields atomic!!! >
    mutable readCount: int64;
    mutable lastReadUse: int64;
    mutable lastWriteUse: int64;
}

let declAv__create (timeNow:int64): DeclAv =
    {readCount=0;lastReadUse=0;lastWriteUse=timeNow;}

// https://github.com/opennars/OpenNARS-for-Applications/blob/master/src/Usage.c#L27
let declAv__calcUsage (av:DeclAv) (timeNow:int64): float =
    let classicalLastUse: int64 = max av.lastReadUse av.lastWriteUse; // "fold" the two values into classical ONA metric

    let recency: float = (float)timeNow - (float)classicalLastUse;
    let usefulnessToNormalize: float = ((double) av.readCount) / (recency + 1.0);
    usefulnessToNormalize / (usefulnessToNormalize + 1.0)

let declAv__update_read (av:DeclAv) (timeNow:int64) =
    av.readCount <- av.readCount + 1L;
    av.lastReadUse <- timeNow;
    ()

let declAv__update_write (av:DeclAv) (timeNow:int64) =
    av.lastWriteUse <- timeNow;
    ()
