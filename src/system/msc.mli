open Parsing
open Types.Base
open Parsing.Variable

(** Type for atoms of canonical forms. *)
type a =
  | Alias of Variable.t
  | Abstract of typ
  | Const of Ast.const
  | Atom of atom
  | Tag of tag * Variable.t
  | Lambda of (typ list) * Variable.t * e
  | Ite of Variable.t * typ * Variable.t * Variable.t
  | App of Variable.t * Variable.t
  | Tuple of Variable.t list
  | Cons of Variable.t * Variable.t
  | Projection of Ast.projection * Variable.t
  | RecordUpdate of Variable.t * string * Variable.t option
  | Let of Variable.t * Variable.t
  | TypeConstr of Variable.t * typ list
  | TypeCoercion of Variable.t * typ list

(** Type for canonical forms. *)
and e =
  | Bind of Variable.t * a * e
  | Var of Variable.t

(** Initial environment to be passed to the type-checker.
    Contains definitions for built-in operators used
    for the encoding of AST expressions into MSC forms. *)
val initial_env : Env.t

(** [remove_patterns_and_fixpoints e] eliminates pattern matching and
    recursive function constructs by encoding them using other constructs. *)
val remove_patterns_and_fixpoints :
  Ast.annot_expr -> Ast.annot_expr

(** [remove_toplevel e] eliminates TopLevel constructs in the expression [e].
    Returns a pair containing the resulting expression and a list of
    intermediate definitions that need to be typed first.
    This function assumes that there is no fixpoint nor pattern matching in [e]. *)
val remove_toplevel :
  Ast.annot_expr -> Ast.annot_expr * (Variable.t * Ast.annot_expr) list

(** [convert_to_msc e] assumes that there is no fixpoint nor pattern matching
    in [e]. Thus, [remove_patterns_and_fixpoints] should be called beforehand. *)
val convert_to_msc : Ast.annot_expr -> e

val map_e : (e -> e) -> (a -> a) -> e -> e
val map_a : (e -> e) -> (a -> a) -> a -> a
val fold_e : (e -> 'b list -> 'b) -> (a -> 'b list -> 'b) -> e -> 'b
val fold_a : (e -> 'b list -> 'b) -> (a -> 'b list -> 'b) -> a -> 'b

val bv_a : a -> VarSet.t
val bv_e : e -> VarSet.t
val fv_a : a -> VarSet.t
val fv_e : e -> VarSet.t

val pp_a : Format.formatter -> a -> unit
val pp_e : Format.formatter -> e -> unit
val show_a : a -> string
val show_e : e -> string
