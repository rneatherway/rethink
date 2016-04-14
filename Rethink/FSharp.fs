//
// Translation from the FSharp Compiler Services representation to RIL.
//
// There is a naming scheme for many of the functions implemented in this 
// module, which is as follows:
//  
//    FSharp.<<FSharpThing>>To<<CoreThing>>
//
// You can try and remember that the FSharp thing precedes the Core
// thing that it is translated to because it naturally follows the
// module name FSharp.
//
// Beware of the FSharp type inferrer confusing the namespace 
// Microsoft.FSharp with Rethink.FSharp!
//
module Rethink.FSharp

open Microsoft.FSharp.Compiler
open Microsoft.FSharp.Compiler.SourceCodeServices

/// Short helper for getting the GenericParameter field of FSharpTypes
//
//  Note: Assumes the argument is actually a generic parameter.
// 
let private getGPData (f:FSharpType) : FSharpGenericParameter =
  f.GenericParameter

/// Returns the mono sort corresponding to a given F# type.  May fail in
/// case of any F# type that we haven't yet thought about.
let typeToMonoSort (fsty: FSharpType) : MonoSort =
  let rec mkMonoType (ft:FSharpType) =
    if ft.HasTypeDefinition then
      // Outermost constructor is a named entity (e.g. union type)
      let args = List.ofSeq (Seq.map mkMonoType ft.GenericArguments)
      Sort.mkFun ft.TypeDefinition.DisplayName args
    elif ft.IsFunctionType then
      // Outermost constructor is the arrow
      let args = List.ofSeq (Seq.map mkMonoType ft.GenericArguments)
      Sort.mkArrow args.[0] args.[1]
    elif ft.IsGenericParameter then
      // Type is a variable
      Sort.mkVar ft.GenericParameter.DisplayName
    elif ft.IsTupleType then
      // Outermost constructor is the tuple constructor
      let args = List.ofSeq (Seq.map mkMonoType ft.GenericArguments)
      Sort.mkFun "Tuple" args   
    else
      failwithf "*** Did not think to handle %O..." ft
  mkMonoType fsty

let genericParametersToStVars (gps:Seq<FSharpGenericParameter>) : List<StVar> =
  let addToList (gp:FSharpGenericParameter) xs = gp.DisplayName :: xs
  Seq.foldBack addToList gps []

let memberOrFunctionOrValueToSort (mfv:FSharpMemberOrFunctionOrValue) : Sort =
  let tyParams = genericParametersToStVars mfv.GenericParameters
  let monoSort = typeToMonoSort mfv.FullType
  Sort.mkForall tyParams monoSort

// Returns a core language range from an FSharp range
let rangeToRange (r:Range.range) : Range =
  Real (r.StartLine, r.StartColumn, r.EndLine, r.EndColumn)

// I don't currently understand why the arguments to functions are always 
// given as a list of lists.  Current strategy is to just take the first 
// element of the outermost list and assume that this is really the list 
// of arguments...
//
// I've not yet seen a list of lists with more than one element in the outer 
// list yet in code that I have processed.
//
// For now let's keep the code to deal with this separate in case it needs to 
// change once we are enlightened.
//
let private unwrapArguments (args:List<List<'a>>) : List<'a> =
  List.map (fun (arg:List<_>) -> arg.[0]) args

/// Given a collection of sort definitions (describing the constants, such as
/// constructors, destructors and discriminators associated with union types), 
/// returns the term corresponding to the given F# expression.  Returns
/// the special term UNK for anything we don't currently handle.
//
// Notes:
// 
//   This function compiles terms into RIL, which involves transformations:
//     * Exception raises are compiled into the Error term.
//     * Calls and Applications are handled in the same way which decomposes 
//       the call into an explicit sequence of type and then term applications.
//     * Decision trees (which come from match expressions) are stuck back 
//       together, which is possibly less efficient in the long run, but more 
//       understandable for now.
//     * Union case *structor uses are decomposed into ordinary type followed 
//       by term applications (F# treats e.g. constructors as special syntax 
//       not just as ordinary functions, we undo this). 
// 
//   I don't currently know exactly why FSharp sometimes describes
//   function applications as "Application"s and sometimes as "Call"s,
//   but I guess it has something to do with the shape of the operator.
//
//   The list of FSharpExpr given to the recursive calls is a list of decision 
//   tree outcomes for the purpose of gluing the decision tree back together.
//
let exprToTerm (sdefs: Map<String,SortDefn>) (expr: FSharpExpr) : Term =
  let rec toTerm (ocs:List<FSharpExpr>) (exp:FSharpExpr) : Term =
    match exp with
    | BasicPatterns.Value mfv ->
        let srt = memberOrFunctionOrValueToSort mfv
        Term.mkVar mfv.DisplayName (rangeToRange exp.Range) srt 
    | BasicPatterns.Const (obj, s) ->
        let srt = Sort.promote (typeToMonoSort s)
        Term.mkConst (obj.ToString ()) (rangeToRange exp.Range) srt

    | BasicPatterns.Call (_, mfv, _, _, _) when mfv.DisplayName = "raise" ->
        let range = rangeToRange exp.Range
        let sort  = Sort.promote (typeToMonoSort exp.Type)
        Term.mkError range sort

    | BasicPatterns.Call (_, mfv, _, ss, es) ->
        let mfvSort = memberOrFunctionOrValueToSort mfv
        let operator = 
          let range = rangeToRange mfv.DeclarationLocation
          if mfv.IsModuleValueOrMember then
            Term.mkVar mfv.DisplayName range mfvSort
          else
            Term.mkConst mfv.DisplayName range mfvSort
        let sortApps =
          let inst (t:Term) srt = 
            let instSort = typeToMonoSort srt 
            let exprSort = Sort.inst instSort t.Sort
            Term.mkInst t instSort Range.Fake exprSort 
          List.fold inst operator ss
        let termApps =
          let apply t e = 
            Term.mkApp t (toTerm ocs e) Range.Fake (Sort.apply t.Sort)
          List.fold apply sortApps es
        termApps 

    | BasicPatterns.Application (e, ss, es) -> 
        let tm = toTerm ocs e
        let sortApps =
          let inst (t:Term) srt = 
            let instSort = typeToMonoSort srt 
            let exprSort = Sort.inst instSort t.Sort
            Term.mkInst t instSort Range.Fake exprSort 
          List.fold inst tm ss
        let termApps =
          let apply t e = 
            Term.mkApp t (toTerm ocs e) Range.Fake (Sort.apply t.Sort)
          List.fold apply sortApps es
        termApps 

    | BasicPatterns.IfThenElse (e1, e2, e3) ->
        let t1 = toTerm ocs e1
        let t2 = toTerm ocs e2
        let t3 = toTerm ocs e3
        Term.mkIf t1 t2 t3 (rangeToRange exp.Range) t2.Sort // (= t3.Sort)

    | BasicPatterns.Let ((x,s),t) ->
        let x' = x.DisplayName
        let s' = toTerm ocs s
        let t' = toTerm ocs t
        let srt = s'.Sort
        Term.mkLet x' srt s' t' (rangeToRange exp.Range) (t'.Sort)

    | BasicPatterns.DecisionTree (tree, outcomes) ->
        let ocs = List.map snd outcomes
        toTerm ocs tree

    | BasicPatterns.DecisionTreeSuccess (i, _) ->
        // At the moment its not clear what the list part is for, though
        // using a "when" guard seems to cause it to be non-empty
        toTerm [] ocs.[i]

    | BasicPatterns.Lambda (mfv, e) ->
        let x = mfv.DisplayName
        // We suppose xSort is really a monosort, i.e xSort.Vars = []
        // because inference is Hindley Milner
        let xSort = memberOrFunctionOrValueToSort mfv
        let t = toTerm ocs e
        let range = rangeToRange exp.Range
        let sort  = Sort.promote (typeToMonoSort exp.Type)
        Term.mkLam x xSort.Mono t range sort

    | BasicPatterns.UnionCaseGet (expr, ty, uc, f) ->
        let tm = toTerm ocs expr
        let tycon = ty.TypeDefinition.DisplayName
        let getter = sdefs.[tycon].Destructors.[uc.DisplayName,f.Name]
        let getConst = Term.mkConst getter.Name Range.Fake getter.Sort 
        let sortArgs = Seq.map typeToMonoSort ty.GenericArguments
        let tyApp = 
          let instantiate tm srt =
            Term.mkInst tm srt Range.Fake (Sort.inst srt tm.Sort)
          Seq.fold instantiate getConst sortArgs
        // Should be the case that we have applied the getter to all of
        // its type arguments so expr.Type is the same monotype as if we 
        // did the application ourselves using Sort.apply, which is cheaper
        Term.mkApp tyApp tm (rangeToRange exp.Range) (Sort.apply tyApp.Sort) 

    | BasicPatterns.UnionCaseTest (expr, ty, uc) ->
        let tm = toTerm ocs expr
        let tycon = ty.TypeDefinition.DisplayName
        let tester = sdefs.[tycon].Discriminators.[uc.DisplayName]
        let testConst = Term.mkConst tester.Name Range.Fake tester.Sort
        let sortArgs = Seq.map typeToMonoSort expr.Type.GenericArguments
        let tyApp = 
          let instantiate tm srt =
            Term.mkInst tm srt Range.Fake (Sort.inst srt tm.Sort)
          Seq.fold instantiate testConst sortArgs
        Term.mkApp tyApp tm (rangeToRange exp.Range) (Sort.apply tyApp.Sort)

    | BasicPatterns.NewUnionCase (ty, uc, exprs) ->
        let tycon = ty.TypeDefinition.DisplayName
        let creator = sdefs.[tycon].Constructors.[uc.DisplayName]
        let creatorConst = Term.mkConst creator.Name Range.Fake creator.Sort
        let sortArgs = Seq.map typeToMonoSort expr.Type.GenericArguments
        let tyApp = 
          let tyapply tm srt = 
            Term.mkInst tm srt Range.Fake (Sort.inst srt tm.Sort)
          Seq.fold tyapply creatorConst sortArgs
        let tmApp = 
          let apply tm expr =
            Term.mkApp tm (toTerm ocs expr) Range.Fake (Sort.apply tm.Sort)
          List.fold apply tyApp exprs
        tmApp

    | BasicPatterns.TypeLambda (xs, expr) ->
        let tm = toTerm ocs expr
        let exprSort = typeToMonoSort expr.Type
        let tyAbs =
          let gen (t:Term) (x:FSharpGenericParameter) = 
            let genSort = Sort.generalise [x.DisplayName] t.Sort
            Term.mkGen x.DisplayName t Range.Fake genSort
          List.fold gen tm xs
        tyAbs     
    
    | _ ->
        let range = rangeToRange exp.Range
        //Sort.promote (typeToMonoSort exp.Type)
        let sort  = Sort.promote (Sort.mkVar "?") 
        Term.mkUnk (sprintf "%A" exp) range sort
  toTerm [] expr 

let fieldToMonoSort (f:FSharpField) : MonoSort = 
  typeToMonoSort f.FieldType

let unionCaseToConstructor (uc:FSharpUnionCase) : Structor =
  let monoSort =
    let arrowOfField fld sort = Sort.mkArrow (fieldToMonoSort fld) sort 
    Seq.foldBack arrowOfField uc.UnionCaseFields (typeToMonoSort uc.ReturnType)
  let tyParams = 
    Seq.map getGPData uc.ReturnType.GenericArguments
  let sortScheme = Sort.mkForall (genericParametersToStVars tyParams) monoSort
  Structor.mkStructor uc.DisplayName sortScheme

let mkDiscriminatorName (caseName:String) : String =
  "_is" + caseName

let unionCaseToDiscriminator (uc:FSharpUnionCase) : Structor =
  let monoSort =
    Sort.mkArrow (typeToMonoSort uc.ReturnType) (Sort.mkFun "bool" [])
  let tyParams = 
    Seq.map getGPData uc.ReturnType.GenericArguments
  let sortScheme = Sort.mkForall (genericParametersToStVars tyParams) monoSort
  Structor.mkStructor (mkDiscriminatorName uc.DisplayName) sortScheme

let mkDestructorName (caseName:String) (fieldName:String) : String =
  "_get" + caseName + fieldName

let unionCaseToDestructors (uc:FSharpUnionCase) : Map<String*String,Structor> =
  let srt = typeToMonoSort uc.ReturnType
  let mkDestructor (f:FSharpField) : Structor =
    let monoSort = Sort.mkArrow srt (fieldToMonoSort f)
    let tyParams = Seq.map getGPData uc.ReturnType.GenericArguments
    let sort = Sort.mkForall (genericParametersToStVars tyParams) monoSort
    Structor.mkStructor (mkDestructorName uc.DisplayName f.Name) sort
  let addDestr m (f:FSharpField) = 
    Map.add (uc.DisplayName, f.Name) (mkDestructor f) m
  Seq.fold addDestr Map.empty uc.UnionCaseFields

/// A fold algebra to accumulate all the definitions corresponding to an F#
/// implementation file declaration.
//
//  Note: This function does some transformation:
//          * For each FSharpEntities representing a union type we generate
//            new term constants (actually Structors) representing the 
//            constructors, destructors and discriminators for the type.
//            In FSharp these are not just ordinary constants but are special
//            language constructs (hence e.g. constructors cannot be partially
//            applied).
//          * For each function definition, we make all the abstractions 
//            explicit, so that e.g. the definition f x y = t is represented
//            as f = \x. \y. t.  However, if t is actually of arrow type,
//            we don't look into this, so the result of our transform is not 
//            necessarily in eta-long form (unless the FSharp compiler has 
//            already done this?).
//          * For each function definition we make all the type abstractions
//            that are implicitly outermost around the function body
//            explicit.
//
//        It is currently implemented to be used as the argument to a fold 
//        function, so its first argument is accumulating the definitions in 
//        two kinds: 
//          * A map of the name of type constructors (e.g. "List") to their 
//            definition (a description of the constants generated for them, 
//            e.g. constructors, destructors, discriminators)
//          * A list of function definitions
//  
let implementationFileDeclarationToDefns 
      (sm: Map<String,SortDefn>, fdefs: List<FunDefn>)
      (d: FSharpImplementationFileDeclaration) 
      : Map<String,SortDefn> * List<FunDefn> =
  let processDecl d =
    match d with
    | Entity (ent:FSharpEntity,dls) ->
        if ent.IsFSharpUnion then
          let name = ent.DisplayName
          let vars = genericParametersToStVars ent.GenericParameters
          let args = List.map Sort.mkVar vars
          let sort = Sort.mkFun name args
          let cases = ent.UnionCases
          let conss =
            let addNewCons (cm:Map<String,Structor>) (uc:FSharpUnionCase) =
              Map.add uc.DisplayName (unionCaseToConstructor uc) cm
            Seq.fold addNewCons Map.empty cases
          let dess = 
            let addNewDes dm (uc:FSharpUnionCase) =
              Map.union (unionCaseToDestructors uc) dm
            Seq.fold addNewDes Map.empty cases
          let diss =
            let addNewDis (cm:Map<String,Structor>) (uc:FSharpUnionCase) =
              Map.add uc.DisplayName (unionCaseToDiscriminator uc) cm
            Seq.fold addNewDis Map.empty cases
          let sortDef = SortDefn.mk sort vars conss dess diss
          (Map.add name sortDef sm, [])
        else
          failwithf "*** Entity %A not currently handled" ent       
    | MemberOrFunctionOrValue (vf,args,def) -> 
        let args = unwrapArguments args
        let tyParams = genericParametersToStVars vf.GenericParameters
        let body = exprToTerm sm def
        let absBody = 
          let abstrac (arg:FSharpMemberOrFunctionOrValue) (b:Term) = 
            let argSort = typeToMonoSort arg.FullType
            let arrow = Sort.promote (Sort.mkArrow argSort b.Sort.Mono)
            let range = rangeToRange def.Range
            Term.mkLam arg.DisplayName argSort b range arrow
          List.foldBack abstrac args body
        let tyAbs (gp:FSharpGenericParameter) bdy = 
          Term.mkGen gp.DisplayName bdy bdy.Range bdy.Sort
        let tyAbsBody = Seq.foldBack tyAbs vf.GenericParameters absBody 
        let sort = Sort.generalise tyParams tyAbsBody.Sort
        (sm, { Name=vf.DisplayName; Sort=sort; Impl=tyAbsBody } :: fdefs)
    | InitAction e ->
        failwithf "*** InitAction %A not handled" e
  try processDecl d with
  // FSharp Compiler Services frequently is unable to process some part 
  // of the source so we have to catch the System.Exception that it generates.
  | :? System.Exception as ex -> 
      if ex.Message.StartsWith "FSharp.Compiler.Service cannot yet" then 
        (sm, fdefs) 
      else 
        reraise ()
