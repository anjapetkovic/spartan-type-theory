(** Concrete syntax as parsed by the parser. *)

(* Patterns *)

type pattern = plain_pattern Location.located

and plain_pattern =
  | PVar of Name.ident
  | PSucc of Name.ident
  | PZero


(** Parsed expression. *)
and expr = expr' Location.located
and expr' =
  | Var of Name.ident
  | Type
  | Nat
  | Zero
  | Succ of expr
  (* | Match of expr * (match_case list) *)
  | MatchNat of expr * expr * (Name.ident * expr)
  | Prod of (Name.ident list * ty) list * ty
  | Lambda of (Name.ident list * ty option) list * ty
  | Apply of expr * expr
  | Arrow of expr * expr
  | Ascribe of expr * ty
  | Sum of (Name.ident list * ty) list * ty
  | Pair of expr * expr
  | Times of expr * expr
  | Fst of expr
  | Snd of expr

(** Parsed type (equal to expression). *)
and ty = expr

and match_case = pattern * expr

(** Parsed top-level command. *)
type toplevel = toplevel' Location.located
and toplevel' =
  | TopLoad of string
  | TopDefinition of Name.ident * expr
  | TopCheck of expr
  | TopEval of expr
  | TopAxiom of Name.ident * expr
