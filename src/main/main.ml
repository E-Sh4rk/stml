open Parsing.IO
open System
open Types.Base
open Types.Additions
open Parsing
open Parsing.Variable
open Types.Tvar

type def = Variable.t * Ast.annot_expr * typ option

type typecheck_result =
| TSuccess of typ * Env.t * float
| TFailure of (Position.t list) * string * float

module Reconstruct = Reconstruction.Make ()

let generalize_all ~uncorrelate t =
  let aux = if uncorrelate then uncorrelate_tvars else Utils.identity in
  Subst.apply (generalize (vars t)) t |> aux |> bot_instance |> simplify_typ

exception IncompatibleType of typ
let type_check_def tenv env (var,expr,typ_annot) =
  let time0 = Unix.gettimeofday () in
  let expr = Msc.remove_patterns_and_fixpoints expr in
  let (expr, addition) = Msc.remove_toplevel expr in
  let nf_expr = Msc.convert_to_msc expr in
  let nf_addition = addition |> List.map (fun (v,e) -> v, Msc.convert_to_msc e) in
  let retrieve_time () =
    let time1 = Unix.gettimeofday () in
    (time1 -. time0 ) *. 1000.
  in
  let type_additionnal env (v, nf) =
    Utils.log "%a@." Msc.pp_e nf ;
    let typ = Reconstruct.typeof_infer tenv env nf |> generalize_all ~uncorrelate:true in
    (* NOTE: ~uncorrelate:false can reduce the number of tvars in fixpoint instances,
       BUT it might also yield an unprecise type (expansion becomes necessary)... *)
    Env.add v typ env
  in
  try
    Utils.log "%a@." Msc.pp_e nf_expr ;
    let env = List.fold_left type_additionnal env nf_addition in
    let typ = Reconstruct.typeof_infer tenv env nf_expr |> generalize_all ~uncorrelate:true in
    let typ =
      match typ_annot with
      | None -> typ
      | Some typ' ->
        if subtype_poly typ typ'
        then typ' |> generalize_all ~uncorrelate:false
        else raise (IncompatibleType typ)
    in
    let env = Env.add var typ env in
    TSuccess (typ, env, retrieve_time ())
  with
  | Algorithmic.Untypeable (pos, str) ->
    TFailure (pos, str, retrieve_time ())
  | IncompatibleType _ ->
    TFailure (Variable.get_locations var,
      "the type inferred is not a subtype of the type specified",
      retrieve_time ())

type parsing_result =
| PSuccess of type_env * ((int * def) list)
| PFailure of Position.t * string

let builtin_functions =
  let arith_operators_typ =
    mk_arrow int_typ (mk_arrow int_typ int_typ)
  in
  [
    ("+", arith_operators_typ) ;
    ("-", arith_operators_typ) ;
    ("*", arith_operators_typ) ;
    ("/", arith_operators_typ) ;
    ("%", arith_operators_typ)
  ]

let initial_varm =
  builtin_functions |> List.fold_left (fun varm (name, _) ->
    let var = Variable.create_other (Some name) in
    StrMap.add name var varm
  ) Ast.empty_name_var_map

let initial_env =
  builtin_functions |> List.fold_left (fun env (name, t) ->
    let var = StrMap.find name initial_varm in
    Env.add var t env
  ) Msc.initial_env

let parse_and_resolve f varm =
  let last_pos = ref Position.dummy in
  try
    let ast =
      match f with
        `File fn -> parse_program_file fn
      | `String s -> parse_program_string s
    in
    let treat_elem (tenv,varm,defs) (annot, elem) =
      last_pos := Position.position annot ;
      match elem with
      | Ast.Definition (log, (name, expr, tyo)) ->
        let tyo = match tyo with
        | None -> None
        | Some expr -> let (t, _) = type_expr_to_typ tenv empty_vtenv expr in Some t
        in
        let expr = Ast.parser_expr_to_annot_expr tenv empty_vtenv varm expr in
        let var = Variable.create_other (Some name) in
        Variable.attach_location var (Position.position annot) ;
        let varm = StrMap.add name var varm in
        (tenv,varm,(log,(var,expr,tyo))::defs)
      | Ast.Types lst ->
        let tenv = define_types tenv empty_vtenv lst in
        (tenv,varm,defs)
      | Ast.AbsType (name, vs) ->
        let tenv = define_abstract tenv name vs in
        (tenv,varm,defs)
    in
    let (tenv, _, defs) =
      List.fold_left treat_elem (empty_tenv, varm, []) ast in
    PSuccess (tenv, List.rev defs)
  with
    | Ast.LexicalError(pos, msg) -> PFailure (pos, msg)
    | Ast.SyntaxError (pos, msg) -> PFailure (pos, msg)
    | Ast.SymbolError msg -> PFailure (!last_pos, msg)
    | TypeDefinitionError msg -> PFailure (!last_pos, msg)
