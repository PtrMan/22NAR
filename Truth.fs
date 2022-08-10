module Truth

type Truth = struct
  val f : float;
  val c : float;
  new(f_,c_)={f=f_;c=c_};
end

// default truth
let mutable TRUTH_DEFAULT = Truth(1.0,0.94);

let TRUTH_EVIDENTAL_HORIZON = 1.0

let truthAnd2 (a: float) (b: float) = a*b
let truthAnd3 (a: float) (b: float) (c: float) = a*b*c
let truthAnd4 (a: float) (b: float) (c: float) (d: float) = a*b*c*d
let truthOr (a: float) (b: float) = 1.0 - ((1.0 - a) * (1.0 - b))

let truthWToC (w: float) = w / (w + TRUTH_EVIDENTAL_HORIZON)
let truthCToW (c: float) = TRUTH_EVIDENTAL_HORIZON * c / (1.0 - c)


let rec calcBinaryTruth(fn:string) (v1:Truth) (v2:Truth): Truth =
  let negation(v1:Truth): Truth =
    let f = 1.0 - v1.f;
    let c = v1.c;
    Truth(f, c)

  let deduction(v1:Truth) (v2:Truth): Truth = 
    let f1 = v1.f;
    let f2 = v2.f;
    let c1 = v1.c;
    let c2 = v2.c;

    Truth(truthAnd2 f1 f2, truthAnd2 (truthAnd2 c1 c2) (truthAnd2 f1 f2))

  let deductionWithReliance (v1:Truth) (reliance: float): Truth =
    let f1 = v1.f;
    let c1 = v1.c;
    let c = truthAnd3 f1 c1 reliance;
    Truth(f1, c)



  let f1 = v1.f;
  let f2 = v2.f;
  let c1 = v1.c;
  let c2 = v2.c;

  let truthFunctions = dict[
    "deduction", fun() -> deduction v1 v2;
    "abduction", fun() -> 
      let c = truthAnd3 f2 c1 c2 |> truthWToC;
      Truth(f1, c)
    "induction", fun() -> calcBinaryTruth "abduction" v2 v1;
//    "exemplification", fun() ->
//      let c = truthAnd4 f1 f2 c1 c2 |> truthWToC;
//      Truth(1.0, c)
    "intersection", fun() ->
      let f = truthAnd2 f1 f2;
      let c = truthAnd2 c1 c2;
      Truth(f, c)
//    "reduce-conjunction", fun() ->
//      let v0 = calcBinaryTruth "intersection" (negation v1) v2;
//      deductionWithReliance v0 1.0 |> negation
//    "comparison", fun() ->
//      let f0 = truthOr f1 f2;
//      let f = if (f0 = 0.0) then 0.0 else ((truthAnd2 f1 f2) / f0);
//      let c = truthAnd3 f0 c1 c2 |> truthWToC;
//      Truth(f, c)
    "revision", fun() ->
      let w1 = truthCToW v1.c;
      let w2 = truthCToW v2.c;
      let w = w1 + w2;

      let f = (w1 * f1 + w2 * f2) / w;
      let c = truthWToC w;
      Truth(f, c)
//    "analogy", fun() ->
//      let f = truthAnd2 f1 f2;
//      let c = truthAnd3 c1 c2 f2;
//      Truth(f, c)
    ]


  truthFunctions.[fn]()

let calcExp (tv:Truth): float =
  tv.c*(tv.f - 0.5) + 0.5
