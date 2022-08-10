module EnvMontezumaA

open System

open Vec2i

// simple version of Montezuma's revenge


type EnvMzAgent = {
    mutable pos: Vec2i;
}



type EnumEnvMzObjType =
| KEY

type EnvMzObj = {
    type_: EnumEnvMzObjType;
    pos: Vec2i;
    mutable isActivated: bool; // was a key picked up? was a door opened?
}

type EnumEnvMzTileType =
| VOID // air
| LADDER
| FULLGROUND // one complete tile with ground which can't get passed

type EnvMzTile = {
    type_: EnumEnvMzTileType;
}

type EnvMontezuma = {
    mutable objs: EnvMzObj list; // list of all objects
    agent: EnvMzAgent; // controlled agent

    mutable eventPickedUpKey:bool; // used to notify controller when a key was picked up

    mutable backgroundTiles: EnvMzTile list;
    mutable backgroundTilesWidth: int;
    mutable backgroundTilesHeight: int;
}

// note: write is not bound checked!
let envMontezuma__envWriteTile (env:EnvMontezuma) (y:int) (x:int) (tile:EnvMzTile) =
    let idx = x + y * env.backgroundTilesWidth;
    env.backgroundTiles <- List.updateAt idx tile env.backgroundTiles;



let envMontezuma__envAlloc (env:EnvMontezuma) (height:int) (width:int) =
    env.backgroundTiles <- [];
    env.backgroundTilesWidth <- width;
    env.backgroundTilesHeight <- height;
    for i=1 to width*height do
        env.backgroundTiles <- {type_=VOID;} :: env.backgroundTiles;



let envMontezuma__tileRead (env:EnvMontezuma) (pos:Vec2i): EnvMzTile option =
    if pos.x >= 0 && pos.x < env.backgroundTilesWidth && pos.y >= 0 && pos.y < env.backgroundTilesHeight then // TODO< implement range tests >
        let selTile = env.backgroundTiles.[pos.x + env.backgroundTilesWidth*pos.y];
        Some selTile
    else
        None

// tries to move the agent in the step delta, agent doesn't move if blocked etc.
let envMontezuma__agentTryMove (env:EnvMontezuma) (agent:EnvMzAgent) (delta:Vec2i) =
    let updatedPos: Vec2i = vec2iAdd agent.pos delta;
    let isMoveValid = match (envMontezuma__tileRead env updatedPos) with 
    | Some tile ->
        match tile.type_ with
        | LADDER -> true
        | VOID -> true // will lead to fall of agent
        | _ -> false
    | None ->
        false // can't move because the tile is outside of the world and thus not valid
    
    if isMoveValid then
        agent.pos <- updatedPos;



// fall logic of agent
let envMontezuma__agentTryFall (env:EnvMontezuma) (agent:EnvMzAgent) =
    // check if ladder is under the agent, which prevents falling
    let tileOpt: EnvMzTile option = envMontezuma__tileRead env (vec2iAdd agent.pos {x=0;y=1});
    let isLadderBelow = match tileOpt with
    | Some tile -> tile.type_ = LADDER
    | None -> false
    
    if isLadderBelow then
        () // can't fall if ladder is under agent
    else
        envMontezuma__agentTryMove env agent {x=0;y=(1);};



// implements perspective of all objects relative to agent
let envMontezuma__agentProjectByAgent (env:EnvMontezuma): EnvMzObj list =
    let mutable projObjs = []; // projected objects
    for iObj in env.objs do
        let diffPos:Vec2i = vec2iSub iObj.pos env.agent.pos;
        
        let iProjObj = {
            type_=iObj.type_;
            pos=diffPos;
            isActivated=iObj.isActivated;
        }
        projObjs <- iProjObj :: projObjs;

    projObjs



// helper to find closest relative to center ladder tile together with the relative position to center
// returns None if no tile was found
let envMontezuma__envCalcClosestLadder (env:EnvMontezuma) (center:Vec2i)    (maxRange:float) : (EnvMzTile*Vec2i) option =
    let mutable res: (EnvMzTile*Vec2i) option = None;
    let mutable closestDistance: float = 10e10;

    for iy=0 to env.backgroundTilesHeight-1 do
        for ix=0 to env.backgroundTilesWidth-1 do
            let diff:Vec2i = vec2iSub {x=ix;y=iy;} center;
            let iDiff:float = sqrt (float (diff.x*diff.x+diff.y*diff.y));

            let iTileOpt:EnvMzTile option = envMontezuma__tileRead env {x=ix;y=iy;};
            match iTileOpt with
            | Some iTile ->
                match iTile.type_ with
                | LADDER ->
                    if iDiff < closestDistance then
                        closestDistance <- iDiff;
                        res <- Some (iTile,diff);
                | _ ->
                    ()
            | None ->
                ()
    
    res



let envMontezuma__timestep (env:EnvMontezuma) =
    envMontezuma__agentTryFall env env.agent;



    // pickup logic for keys
    env.eventPickedUpKey <- false; // reset signal

    // check if any key way picked up
    for iObj in env.objs do
        if (vec2iSame iObj.pos env.agent.pos) then
            iObj.isActivated <- true;

            env.eventPickedUpKey <- true; // send signal
            ()
        else
            ()
    
    env.objs <- List.filter (fun iv -> not iv.isActivated) env.objs;



    // TODO< implement remaining world interaction >



let envMontezuma__debugState (env:EnvMontezuma) =
    printfn "env.montezuma";
    printfn "x=%i y=%i" env.agent.pos.x env.agent.pos.y;









