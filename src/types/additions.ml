open Base
open Tvar

module StrMap = Map.Make(String)
module StrSet = Set.Make(String)
module LabelMap = Sstt.LabelMap
module VarMap = Sstt.VarMap

exception TypeDefinitionError of string

(* Construction of types *)

type type_base =
    | TInt of Z.t option * Z.t option | TCharInt of char * char | TSString of string
    | TBool | TTrue | TFalse | TUnit | TChar | TAny | TEmpty | TNil
    | TString | TList | TFloat | TArrowAny | TTupleAny | TTupleN of int | TAtomAny | TRecordAny 

type type_regexp = type_expr Sstt.Extensions.Lists.regexp

and type_expr =
    | TVar of string | TVarWeak of string
    | TBase of type_base
    | TCustom of type_expr list * string
    | TTuple of type_expr list
    | TRecord of bool * (string * type_expr * bool) list
    | TSList of type_regexp
    | TCons of type_expr * type_expr
    | TArrow of type_expr * type_expr
    | TCup of type_expr * type_expr
    | TCap of type_expr * type_expr
    | TDiff of type_expr * type_expr
    | TNeg of type_expr
    | TWhere of type_expr * (string * string list * type_expr) list

type type_def = string * string list * type_expr
type type_env = typ StrMap.t (* User-defined non-parametric types *) * StrSet.t (* Atoms *) * type_def list (* History of definitions *)
type var_type_env = TVar.t StrMap.t (* Var types *)

let empty_tenv = (StrMap.empty, StrSet.empty, [])
let empty_vtenv = StrMap.empty

let type_base_to_typ t =
    match t with
    | TInt (lb,ub) -> interval lb ub
    | TFloat -> float_typ
    | TCharInt (c1, c2) -> char_interval c1 c2
    | TSString str -> single_string str
    | TBool -> bool_typ | TNil -> nil_typ
    | TTrue -> true_typ | TFalse -> false_typ
    | TUnit -> unit_typ | TChar -> char_typ
    | TAny -> any | TEmpty -> empty
    | TString -> string_typ | TList -> list_typ
    | TArrowAny -> arrow_any
    | TTupleAny -> tuple_any
    | TTupleN n -> tuple_n n
    | TAtomAny -> atom_any
    | TRecordAny -> record_any

let get_non_parametric_type env name = StrMap.find_opt name env

let derecurse_types history env venv defs =
    let venv =
        let h = Hashtbl.create 16 in
        StrMap.iter (fun n v -> Hashtbl.add h n v) venv ;
        h
    in
    let henv = Hashtbl.create 16 in
    let eqs = ref [] in
    List.iter (fun (name, params, def) ->
        Hashtbl.add henv name (def, params, [])) history ;
    let rec derecurse_types defs =
        List.iter (fun (name, params, def) ->
            Hashtbl.add henv name (def, params, [])) defs ;
        let rec get_name args name =
            match Hashtbl.find henv name with
            | def, params, lst ->
                let cached = lst |> List.find_opt (fun (args',_) ->
                    try List.for_all2 (==) args args' with Invalid_argument _ -> false) in
                begin match cached with
                | None ->
                    begin try
                        let v = TVar.mk_unregistered () in
                        Hashtbl.replace henv name (def, params, (args, v)::lst);
                        let local = List.combine params args |> List.to_seq |> StrMap.of_seq in
                        let t = aux local def in
                        eqs := (v,t)::!eqs ;
                        v
                    with Invalid_argument _ ->
                        raise (TypeDefinitionError (Printf.sprintf "Wrong arity for type %s!" name))
                    end
                | Some (_, v) -> v
                end
            | exception Not_found ->
                begin match get_non_parametric_type env name with
                | Some t ->
                    let v = TVar.mk_unregistered () in
                    eqs := (v,t)::!eqs ;
                    v
                | None -> raise (TypeDefinitionError (Printf.sprintf "Type %s undefined!" name))
                end
        and aux lcl t =
            match t with
            | TVar v ->
                begin match StrMap.find_opt v lcl, Hashtbl.find_opt venv v with
                | Some n, _ -> n
                | None, Some t -> TVar.typ t
                | None, None ->
                    let t = TVar.mk_mono ~infer:false (Some v) in
                    Hashtbl.add venv v t ;
                    TVar.typ t
                end
            | TVarWeak v ->
                begin match Hashtbl.find_opt venv v with
                | Some t -> TVar.typ t
                | None ->
                    let t = TVar.mk_mono ~infer:true (Some v) in
                    Hashtbl.add venv v t ;
                    TVar.typ t
                end
            | TBase tb -> type_base_to_typ tb
            | TCustom (args, n) ->
                let args = args |> List.map (aux lcl) in
                get_name args n |> Sstt.Ty.mk_var
            | TTuple ts -> mk_tuple (List.map (aux lcl) ts)
            | TRecord (is_open, fields) ->
                let aux' (label,t,opt) = (label, (opt, aux lcl t)) in
                mk_record is_open (List.map aux' fields)
            | TSList lst -> aux_re lcl lst
            | TCons (t1,t2) -> mk_cons (aux lcl t1) (aux lcl t2)
            | TArrow (t1,t2) -> mk_arrow (aux lcl t1) (aux lcl t2)
            | TCup (t1,t2) ->
                let t1 = aux lcl t1 in
                let t2 = aux lcl t2 in
                cup t1 t2
            | TCap (t1,t2) ->
                let t1 = aux lcl t1 in
                let t2 = aux lcl t2 in
                cap t1 t2
            | TDiff (t1,t2) ->
                let t1 = aux lcl t1 in
                let t2 = aux lcl t2 in
                diff t1 t2
            | TNeg t -> neg (aux lcl t)
            | TWhere (t, defs) ->
                begin match derecurse_types (("", [], t)::defs) with
                | ("", [], n)::_ -> TVar.typ n
                | _ -> assert false
                end
        and aux_re lcl re =
            let open Sstt.Extensions.Lists in
            let rec aux_re re =
                match re with
                | Epsilon -> Epsilon
                | Symbol ty -> Symbol (aux lcl ty)
                | Concat lst -> Concat (List.map aux_re lst)
                | Union lst -> Union (List.map aux_re lst)
                | Star r -> Star (aux_re r)
                | Option r -> Option (aux_re r)
                | Plus r -> Plus (aux_re r)
            in
            aux_re re |> build
        in
        let res = defs |> List.map (fun (name, params, _) ->
            let params = List.map (fun _ -> TVar.mk_unregistered ()) params in
            let args = params |> List.map TVar.typ in
            let node = get_name args name in
            name, params, node) in
        List.iter (fun (name, _, _) -> Hashtbl.remove henv name) defs ;
        res
    in
    let res = derecurse_types defs in
    let tys = Sstt.Ty.of_eqs !eqs |> VarMap.of_list in
    let res = res |> List.map (fun (n,p,node) -> (n,p,VarMap.find node tys)) in
    let venv = Hashtbl.fold StrMap.add venv StrMap.empty in
    (res, venv)

let type_expr_to_typ (tenv, _, history) venv t =
    match derecurse_types history tenv venv [ ("", [], t) ] with
    | ([ "", [], t ], venv) -> (t, venv)
    | _ -> assert false

let type_exprs_to_typs env venv ts =
    let venv = ref venv in
    let ts = List.map (fun t ->
        let (t, venv') = type_expr_to_typ env !venv t in
        venv := venv' ; t
    ) ts in
    (ts, !venv)

let define_types (tenv, aenv, h) venv defs =
    let (res, _) = derecurse_types h tenv venv defs in
    let (tenv, h) = List.fold_left2
        (fun (tenv, h) (name, params, typ) def ->
            if params = []
            then begin
                register name typ ; (StrMap.add name typ tenv, h)
            end else (tenv, def::h))
        (tenv, h) res defs
    in (tenv, aenv, h)

let define_atom (env, atoms, h) name =
    if StrMap.mem name env
    then raise (TypeDefinitionError (Printf.sprintf "Atom %s already defined!" name))
    else (StrMap.add name (mk_atom name) env, StrSet.add name atoms, h)

let has_atom (_, atoms, _) name = StrSet.mem name atoms

let get_atom_type ((env, _, _) as e) name =
    match has_atom e name, get_non_parametric_type env name with
    | true, Some t -> t
    | _ -> raise (TypeDefinitionError (Printf.sprintf "Atom type %s undefined!" name))

(* Operations on types *)

let is_test_type t =
    let exception NotTestType in
    try
        Sstt.Ty.nodes t |> List.iter (fun t ->
            Sstt.Ty.def t |> Sstt.VDescr.dnf |> List.iter (fun (ps,ns,d) ->
                if ps <> [] || ns <> [] then raise NotTestType ;
                let open Sstt.Descr in
                components d |> List.iter (function
                    | Atoms _ | Intervals _ | Tuples _ | Records _
                    | Tags _ -> ()
                    | Arrows a ->
                        let t = mk_arrows a |> Sstt.Ty.mk_descr in
                        if (is_empty t || subtype arrow_any t) |> not
                        then raise NotTestType
                )
            )
        ) ; true
    with NotTestType -> false

let branch_type lst =
    if lst = [] then arrow_any
    else begin
        lst
        |> List.map (fun (a, b) -> mk_arrow a b)
        |> conj
    end
let tuple_branch_type ts = mk_tuple ts
let cons_branch_type (a, b) = mk_cons a b
let record_branch_type (fields, o) = mk_record o fields

(* Simplification of types *)

let simplify_typ = Sstt.Transform.simplify

(* Record manipulation *)

let record_any_with l = mk_record true [l, (false, any)]

let record_any_without l = mk_record true [l, (true, empty)]

let remove_field_info t label =
    let t = remove_field t label in
    let singleton = mk_record false [label, (true, any)] in
    merge_records t singleton

(* Operations on type variables *)

let instantiate ss t =
    List.map (fun s -> Subst.apply s t) ss
    |> conj

let bot_instance =
    clean_type ~pos:empty ~neg:any

let top_instance =
    clean_type ~pos:any ~neg:empty

let clean_types ~pos ~neg lst =
    let pols = List.map vars_with_polarity lst in
    let vars = lst |> List.map vars_poly |> TVarSet.union_many in
    vars |> TVarSet.destruct |> List.map (fun v ->
        if pols |> List.for_all (fun lst -> lst
            |> List.for_all (fun (v', k) -> (TVar.equal v v' |> not) || k = `Pos)
        ) then (v, pos)
        else if pols |> List.for_all (fun lst -> lst
            |> List.for_all (fun (v', k) -> (TVar.equal v v' |> not) || k = `Neg)
        ) then (v, neg)
        else (v, TVar.typ v)
    ) |> Subst.construct

let subtypes_poly lst =
    let m = lst |> List.map snd |> List.map vars
        |> TVarSet.union_many |> monomorphize
    in
    let c = lst |> List.map fst |> clean_types ~pos:empty ~neg:any in
    lst
    |> List.map (fun (t1, t2) -> (Subst.apply c t1, Subst.apply m t2))
    |> test_tallying
let supertypes_poly lst =
    let m = lst |> List.map snd |> List.map vars
        |> TVarSet.union_many |> monomorphize
    in
    let c = lst |> List.map fst |> clean_types ~pos:any ~neg:empty in
    lst
    |> List.map (fun (t1, t2) -> (Subst.apply m t2, Subst.apply c t1))
    |> test_tallying

let subtype_poly t1 t2 = subtypes_poly [t1,t2]
let supertype_poly t1 t2 = supertypes_poly [t1,t2]
let is_empty_poly t = [bot_instance t,empty] |> test_tallying

let subtype_expand ~max_exp t1 t2 =
    assert (vars_poly t2 |> TVarSet.is_empty) ;
    let refresh t = refresh (vars_poly t) in
    let rec test_subtype exp =
        if List.length exp > max_exp then None
        else
            match tallying [(instantiate exp t1, t2)] with
            | [] -> test_subtype ((refresh t1)::exp)
            | sol::_ ->
                let inst = exp |> List.map (Subst.compose_restr sol) in
                Some inst
    in
    test_subtype [refresh t1]

let subtypes_expand ~max_exp t1 t2s =
    let res = List.map (subtype_expand ~max_exp t1) t2s in
    if List.mem None res
    then None
    else Some (List.map Option.get res |> List.flatten)

let rec uncorrelate_tvars keep t =
    if TVarSet.diff (vars_poly t) keep |> TVarSet.is_empty
    then t
    else
        let dnf, non_arrow = dnf t, cap t (neg arrow_any) in
        (* Refresh branches *)
        let dnf = dnf |> List.map (fun arrows ->
            arrows |> List.map (fun (a,b) ->
                let to_rename = TVarSet.diff (vars_poly a) keep in
                let rename = refresh to_rename in
                let keep = TVarSet.union keep (Subst.vars rename) in
                let a = Subst.apply rename a in
                let b = Subst.apply rename b |> uncorrelate_tvars keep in
                (a, b)
            )
        ) in
        (* Avoid useless branches *)
        let mono = monomorphize keep in
        let dnf = dnf |> List.map (fun arrows ->
            arrows |> Utils.filter_among_others (fun c lst ->
            let others = List.map (fun a -> branch_type [a] |> Subst.apply mono) lst in
            let current = branch_type [c] |> Subst.apply mono in
            others |> List.exists (fun o -> subtype_poly o current) |> not
        ) |> Utils.filter_among_others (fun c lst ->
            let others = branch_type lst |> Subst.apply mono in
            let current = branch_type [c] |> Subst.apply mono in
            subtype_poly others current |> not
        )) in
        (* Rebuild type *)
        let t = List.map branch_type dnf |> disj in
        cup t non_arrow

let uncorrelate_tvars = uncorrelate_tvars TVarSet.empty