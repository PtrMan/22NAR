module Vec2i

type Vec2i = {
    x: int;
    y: int;
}

let vec2iAdd (a:Vec2i) (b:Vec2i): Vec2i =
    {x=a.x+b.x;y=a.y+b.y}

let vec2iSub (a:Vec2i) (b:Vec2i): Vec2i =
    {x=a.x-b.x;y=a.y-b.y}

let vec2iSame (a:Vec2i) (b:Vec2i): bool =
    a.x=b.x && a.y=b.y

let vec2iCalcTangent (v:Vec2i): Vec2i =
    {x=(-v.y);y=v.x}

let vec2iDot (a:Vec2i) (b:Vec2i): int =
    a.x*b.x + a.y*b.y
