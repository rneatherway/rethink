//
// The sorts of the Rethink Intermediate Language (RIL).
//  
// Currently the sorts correspond to Hindley Milner types, i.e. there are two
// stratifications, the monosorts and the sort schemes.  We just call the sort
// schemes "Sort" because every monosort can be thought of as a sort scheme
// with no quantified variables (this is effected via the function "promote"). 
// 
// Sort schemes correspond to types with all universal quantification happening
// at the front (i.e. rank 1 in prenex form).  If we wanted to look at the core
// language of GHC for example, we would need to upgrade the sort language to 
// allow sort quantification underneath arrows (rank > 1) and then we would get
// no advantage from assuming prenex form (all quantifiers out the front) so 
// we would lose the stratification and just have one representation which 
// included forall as a type constructor. 
//
namespace Rethink

/// Sort variables.
type StVar = String

/// Monosorts.
//
// Notes:
//   
//   The reason that we have our own type for sorts
//   (and do not just rely on the provided type FSharpType)
//   is that FSharpType does not implement useful interfaces
//   such as IComparable, so that e.g. it is not possible
//   to put them in a Set.  It is more convenient just to have
//   our own type that only contains information we actually
//   use and hence we know what e.g. comparison should be like.
//
type MonoSort =
  | Var of StVar
  | Fun of String * List<MonoSort>
  | Arrow of MonoSort * MonoSort

/// Sort schemes.
//
//  A sort scheme e.g. { Vars=[a;b]; Mono=a->b } should be thought of as:
//    forall a b. a -> b
//  and indeed it will sprint like this.
//
type Sort = 
  {
    Vars:List<StVar>
    Mono:MonoSort
  }

type SortBinding = String * Sort


[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module Sort =

  let mkVar v = Var v
  let mkFun f ss = Fun (f, ss)
  let mkArrow s1 s2 = Arrow (s1, s2)
  let mkTuple ss = mkFun "Tuple" ss
  let mkForall xs m = 
    { Vars=xs; Mono=m }

  /// Returns a further generalised sort in which additionally the variables in
  /// the given argument are quantified out (no checks are made that this is a
  /// good idea).
  let generalise (xs:List<StVar>) (s:Sort) : Sort =
    { s with Vars = xs @ s.Vars } 

  /// Returns the free variables in a monosort (note all variables are free in
  /// a monosort).
  let rec vars (s:MonoSort) : Set<String> =
    match s with
    | Var x -> set [x]
    | Fun (f,ss) -> List.fold (fun tt s' -> vars s' + tt) (set []) ss
    | Arrow (u,v) -> vars u + vars v

  /// Return the sort obtained by generalising over none of the free variables
  /// in the given monosort.
  let promote (m:MonoSort) : Sort =
    { Mono=m; Vars=[] }

  /// Returns the sort obtained by generalising all the free variables
  /// in the monosort.
  let generaliseAll (m:MonoSort) : Sort =
    let tyParams = List.ofSeq (vars m)
    generalise tyParams (promote m) 

  let sprintMono (s:MonoSort) : String = 

    let bracket (b:bool) (s: String) : String =
      if b then "(" + s + ")" else s

    let rec spr prec s =
      match s with
      | Var x -> x
      | Fun (f,ms) -> 
          if f = "Tuple" then 
            let str = sprintf "%s" (List.print (spr 8) "" " * " "" ms)
            bracket (prec > 8) str
          else
            let argStr =
              if ms.Length = 0 then 
                "" 
              else 
                List.print (spr 0) "<" ", " ">" ms
            let str = sprintf "%s%s" f argStr
            bracket (prec > 10) str
      | Arrow (m,n) ->
          bracket (prec > 5) (sprintf "%s -> %s" (spr 6 m) (spr 5 n))

    spr 0 s

  let sprint (s:Sort) : String =
    let monoStr = sprintMono s.Mono
    let varsStr = List.print (fun x -> x) "" " " "" s.Vars
    if List.isEmpty s.Vars then
      monoStr
    else
      sprintf "forall %s. %s" varsStr monoStr

  /// Substitute into a sort, avoiding bound variables -- e.g.
  ///   subst [(x,m); (y,n)] (forall x. x -> y) == forall x. x -> n 
  let private subst (sub: Map<String,MonoSort>) (s:Sort) : Sort =
    // Do not substitute for bound variables
    let sub' = Map.filter (fun k _ -> not (List.contains k s.Vars)) sub 
    let rec subMono m =
      match m with
      | Var v -> 
          match Map.tryFind v sub' with
          | None -> m
          | Some t -> t
      | Fun (f,ss) -> let tt = List.map subMono ss in Fun (f,tt)
      | Arrow (u,v) -> Arrow (subMono u, subMono v)
    { s with Mono = subMono s.Mono }

  /// Instantiate the first quantified variable in sort ss by monotype m.
  let inst (m:MonoSort) (ss:Sort) : Sort =
    let (x::xs) = ss.Vars
    let sub = Map.singleton x m
    subst sub { ss with Vars=xs }

  /// Returns the result of applying a function sort (an arrow) to its argument
  /// i.e. projects out the second component of the arrow. 
  /// 
  /// May fail if the argument is not an arrow.a
  //
  //  Note: You would expect that apply takes two arguments, namely an arrow 
  //        type and an argument type, and then checks that the first component
  //        of the arrow is a supertype of the argument and, if so, returns
  //        the second component of the arrow.  Instead we only take the arrow
  //        and immediately return the second component because we are assuming
  //        that the program from which the sorts derive was already well typed
  //        so this check has already been done.  
  //
  let apply (s:Sort) : Sort =
    match s.Mono with
    | Arrow (u,v) -> { s with Mono=v }
    | _ -> failwithf "Sort %s not an arrow" (sprint s)