module EnvWumpusA

open Vec2i

//enum EnumAgentDir =
//| PX
//| NX
//| PY
//| NY

type Agent = {
    mutable pos: Vec2i;
    mutable dir: int; // code of direction, clockwise, starting at 12'o'clock
}

type EnumObjType =
| KEY
| CLOSEDDOOR

type Obj = {
    type_: EnumObjType;
    pos: Vec2i;
    mutable isActivated: bool; // was a key picked up? was a door opened?
}


type EnvWumpus = {
    mutable objs: Obj list; // list of all objects
    agent: Agent; // controlled agent

    mutable nKeys:int; // number of picked up keys

    mutable eventPickedUpKey:bool; // used to notify controller when a key was picked up

    mutable wallBitmap:bool list; // bitmap "image" of walls
    mutable wallBitmapWidth:int;
    mutable wallBitmapHeight:int;
}


let wumpus__envReadWall (env:EnvWumpus) (y:int) (x:int): bool =
    if x>=0 && x<env.wallBitmapWidth && y>=0 && y<env.wallBitmapHeight then
        let idx = x + y * env.wallBitmapWidth;
        env.wallBitmap.[idx]
    else
        false

// note: write is not bound checked!
let wumpus__envWriteWall (env:EnvWumpus) (y:int) (x:int) (v:bool) =
    let idx = x + y * env.wallBitmapWidth;
    env.wallBitmap <- List.updateAt idx v env.wallBitmap;

let wumpus__envWallAlloc (env:EnvWumpus) (height:int) (width:int) =
    env.wallBitmap <- [];
    env.wallBitmapWidth <- width;
    env.wallBitmapHeight <- height;
    for i=1 to width*height do
        env.wallBitmap <- false :: env.wallBitmap;


type EnumRotDir =
| LEFT
| RIGHT

let wumpus__worldAgentDoRotate (agent:Agent) (rotDir:EnumRotDir) =
    let delta = match rotDir with
    | LEFT -> -1
    | RIGHT -> 1
    
    agent.dir <- (agent.dir + 4 + delta) % 4;




let wumpus__calcAgentDirVec (dir:int): Vec2i =
    match dir with
    | 0 -> {x=0;y=(-1);}
    | 1 -> {x=1;y=0;}
    | 2 -> {x=0;y=1;}
    | 3 -> {x=(-1);y=0;}


let wumpus__worldAgentMoveForward (env:EnvWumpus) (agent:Agent) =
    let dirVec = wumpus__calcAgentDirVec agent.dir;

    if not (wumpus__envReadWall env (agent.pos.y+dirVec.y) (agent.pos.x+dirVec.x)) then // agent can't move into walls!
        agent.pos <- vec2iAdd agent.pos dirVec;
        ()
    else
        ()




// check for changed stuff in the world
let envCheck (env:EnvWumpus) =
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


// convert world to ASCII for debugging
let envPrintAscii (env:EnvWumpus): string list =
    let width:int = 10;
    let height:int = 10;
    
    let mutable arr: string list = [];

    for i=1 to width*height do
        arr <- " " :: arr;
    
    let writeAt (y:int) (x:int) (char:string) =
        if y>=0 && y<height && x>=0 && x<width then
            arr <- List.updateAt (x+y*width) char arr;
            ()
        else
            ()
    
    // draw wall
    for iy=0 to env.wallBitmapHeight-1 do
        for ix=0 to env.wallBitmapWidth-1 do
            let isWall: bool = wumpus__envReadWall env iy ix;
            if isWall then
                writeAt iy ix "W";
                ()
            else
                ()
            ()

    // draw objects
    for iObj in env.objs do
        let sign = match iObj.type_ with
        | KEY -> "K";
        | CLOSEDDOOR -> "D";

        writeAt iObj.pos.y iObj.pos.x sign;

        ()
    
    
    // draw agent
    let agentLetter = match env.agent.dir with
        | 0 -> "^"
        | 1 -> ">"
        | 2 -> "V"
        | 3 -> "<"

    writeAt env.agent.pos.y env.agent.pos.x agentLetter;



    let mutable res = [];

    for iy1=0 to height-1 do
        let iy=(height-1)-iy1;

        let mutable line = "";

        for ix=0 to width-1 do
            line <- line + arr.[ix+iy*width];
        
        res <- line :: res;
    
    res

// TODO< implement walls and interaction of walls! >




// implements perspective of all objects relative to agent
let wumpus__projectByAgent (env:EnvWumpus) =
    let agentDirVec:Vec2i = wumpus__calcAgentDirVec env.agent.dir;
    let agentTangentVec:Vec2i = vec2iCalcTangent agentDirVec;

    let mutable projObjs = []; // projected objects
    for iObj in env.objs do
        let diffPos:Vec2i = vec2iSub iObj.pos env.agent.pos;
        let iProjPos:Vec2i = {
            x=vec2iDot agentTangentVec diffPos;
            y=vec2iDot agentDirVec diffPos;
        }
        
        let iProjObj = {
            type_=iObj.type_;
            pos=iProjPos;
            isActivated=iObj.isActivated;
        }
        projObjs <- iProjObj :: projObjs;

    projObjs

