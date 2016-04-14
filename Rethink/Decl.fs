//
// Internal representation of top level definitions, which are
// either function definitions or algebraic data type (union type)
// declarations.  
//
// This may, at least in part, be moved to the FSharp specific code at some
// point because the language we analyse may do away with
// top level definitions in favour of a giant let expression.
//

namespace Rethink

open Microsoft.FSharp.Compiler.SourceCodeServices

/// Top level function definitions. 
type FunDefn =
  {
    Name:String
    Sort:Sort
    Impl:Term
  }

/// The internal representation of a constructor, destructor or discriminator.
//
//  Note: these are all generated automatically from the data type definition
//        and are essentially sort axioms giving the sort of a basic constant
//        because they do not have any actual implementation.
//
type Structor =
  {
    Name:String
    Sort:Sort
  }

/// Top level algebraic data type definitions.
//
//  Note: the bits we need are the type variables by which the sort
//        is parametrised and the associated *structors.
//
type SortDefn =
  {
    Sort: MonoSort
    Vars: List<String>
    Constructors: Map<String,Structor>
    Destructors: Map<String*String,Structor>
    Discriminators: Map<String,Structor>
  }

[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module FunDefn =
  
  let sprint (d: FunDefn) : String =
    let srtstr = Sort.sprint d.Sort
    let tStr = Term.sprint d.Impl
    sprintf "%s: %s = %s" d.Name srtstr tStr

[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module Structor =

  let mkStructor s srt =
    { Name=s; Sort=srt }
 
  let sprint (s:Structor) : String =
    let srtstr = Sort.sprint s.Sort
    sprintf "%s : %s" s.Name srtstr 

[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module SortDefn =

  let mk srt vs cs ds diss =
    { Sort=srt; Vars=vs; Constructors=cs; Destructors=ds; Discriminators=diss }
  
  let sprint (s:SortDefn) : String =
    let sortStr = Sort.sprintMono s.Sort
    let css = 
      Map.fold (fun cs _ v -> Structor.sprint v :: cs) [] s.Constructors
    let dss = 
      Map.fold (fun ds _ v -> Structor.sprint v :: ds) [] s.Destructors
    let diss = 
      Map.fold (fun ds _ v -> Structor.sprint v :: ds) [] s.Discriminators
    let cstr = List.print (fun x -> x) "" "\n" "" css
    let dstr = List.print (fun x -> x) "" "\n" "" dss
    let istr = List.print (fun x -> x) "" "\n" "" diss
    sortStr + "\n" + cstr + "\n" + dstr + "\n" + istr
  

