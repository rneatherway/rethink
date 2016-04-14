//
// The terms of the Rethink Intermediate Language (RIL).
//
// The language is essentially an applied System F, although this should be
// taken modulo the fact that the sort language is restricted to the rank 1
// fragment in prenex form.  This means that although type abstraction and 
// application are explicit, they will always occur in restricted places.  
// Namely, we will be assuming that type abstraction occurs only at lets and
// type application occurs immediately before term application.  However, this
// is not enforced by this representation except in that type application, 
// "Inst", and type abstraction, "Gen", are restricted to monosorts only.
// 
// Additionally we have terms for conditionals, lets, error and unknown ---
// the latter covers all the cases that we have not yet implemented from the 
// source language.
// 

namespace Rethink

open Microsoft.FSharp.Compiler.SourceCodeServices

type TmVar = String

type Range = 
  | Fake 
  | Real of startLine:Int * startCol:Int * endLine:Int * endCol:Int

/// RIL expressions.
type Exp =
  | Var of TmVar 
  | Const of String 
  | App of Term * Term
  | If of Term * Term * Term
  | Gen of StVar * Term
  | Inst of Term * MonoSort
  | Lam of TmVar * MonoSort * Term
  | Let of TmVar * Sort * Term * Term
  | Error 
  | Unk of String

/// RIL terms include source location (Range) and sort.
and Term = {
    Expr: Exp
    Range: Range
    Sort: Sort
  }

[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module Term =
  
  let private mkTerm e r s = { Expr=e; Range=r; Sort=s}

  let mkVar s rng sort         = mkTerm (Var s) rng sort
  let mkConst s rng sort       = mkTerm (Const s) rng sort
  let mkApp u v rng sort       = mkTerm (App (u,v)) rng sort
  let mkIf u v w rng sort      = mkTerm (If (u,v,w)) rng sort
  let mkGen x t rng sort       = mkTerm (Gen (x,t)) rng sort
  let mkLam x s t rng sort     = mkTerm (Lam (x,s,t)) rng sort
  let mkInst t s rng sort      = mkTerm (Inst (t,s)) rng sort
  let mkLet x srt s t rng sort = mkTerm (Let (x,srt,s,t)) rng sort
  let mkUnk s rng sort         = mkTerm (Unk s) rng sort
  let mkError rng sort         = mkTerm Error rng sort

  let private varNum = ref 0

  /// Return a fresh variable name
  let freshVar () =
    do incr varNum
    "x" + (!varNum).ToString ()
    
  let sprint (m: Term) : String = 
    let bracket b s = if b then "(" + s + ")" else s
    let rec pp pr n =
      match n.Expr with
      | Var v      -> sprintf "%s" v 
      | Const c    -> sprintf "%s" c 
      | App (u,v)  -> 
          let ustr = pp 4 u 
          let vstr = pp 3 v
          bracket (pr > 4) (sprintf "%s %s" ustr vstr)
      | If (u,v,w) -> 
          let ustr = pp 1 u
          let vstr = pp 1 v
          let wstr = pp 1 w
          bracket (pr > 1) (sprintf "if %s then %s else %s" ustr vstr wstr)
      | Gen (x,t) ->
          let tstr = pp 0 t
          bracket (pr > 0) (sprintf "/\%s. %s" x tstr)
      | Lam (x,s,t) ->
          let tstr = pp 0 t
          let sort = Sort.sprintMono s
          bracket (pr > 0) (sprintf "\%s: %s. %s" x sort tstr)
      | Inst (u,s) ->
          let ustr = pp 3 u
          let sstr = Sort.sprintMono s
          bracket (pr > 4) (sprintf "%s [%s]" ustr sstr)
      | Let (x,srt,s,t) ->
          let sstr = pp 0 s
          let srtStr = Sort.sprint srt
          let tstr = pp 0 t
          bracket (pr > 2) (sprintf "let %s : %s = %s in %s" x srtStr sstr tstr)
      | Error ->
          sprintf "Error"
      | Unk s ->
          sprintf "{..?..}"
    pp 0 m

      

