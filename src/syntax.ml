(** Abstract syntax of expressions, before they are type-checked. *)

(** De Bruijn index *)
type index = int

(** Expressions *)
type expr = expr' Location.located
and expr' =
  | Var of index
  | Type
  | Nat
  | Zero
  | Succ of expr
  | Prod of (Name.ident * ty) * ty
  | Sum of (Name.ident * ty) * ty
  | Lambda of (Name.ident * ty option) * expr
  | Apply of expr * expr
  | Pair of expr * expr
  | Fst of expr
  | Snd of expr
  | Ascribe of expr * ty
  | MatchNat of expr * expr * (Name.ident * expr)

(** Types (equal to expressions at this point). *)
and ty = expr

(** Top-level commands. *)
type toplevel = toplevel' Location.located
and toplevel' =
  | TopLoad of toplevel list
  | TopDefinition of Name.ident * expr
  | TopCheck of expr
  | TopEval of expr
  | TopAxiom of Name.ident * expr

(** Shift all indices greter than or equal to [n] by [k]. *)
let rec shift n k {Location.data=e'; loc} =
  let e' = shift' n k e' in
  Location.locate ~loc e'

and shift' n k = function

  | Var j -> if j >= n then Var (j + k) else Var j

  | Type -> Type

  | Nat ->  Nat

  | Zero -> Zero

  | Succ e ->
    let e = shift n k e in
    Succ e

  | Prod ((x, t), u) ->
    let t = shift_ty n k t
    and u = shift_ty (n + 1) k u in
    Prod ((x, t), u)

  | Sum ((x, t), u) ->
    let t = shift_ty n k t
    and u = shift_ty (n + 1) k u in
    Sum ((x, t), u)  

  | Lambda ((x, topt), e) ->
    let t = shift_tyopt n k topt
    and e = shift (n + 1) k e in
    Lambda ((x, t), e)

  | Apply (e1, e2) ->
    let e1 = shift n k e1
    and e2 = shift n k e2 in
    Apply (e1, e2)

  | Pair (e1, e2) ->
    let e1 = shift n k e1
    and e2 = shift n k e2 in
    Pair (e1, e2)

  | Fst e ->
    let e = shift n k e in
    Fst e

  | Snd e ->
    let e = shift n k e in
    Snd e

  | Ascribe (e, t) ->
    let e = shift n k e
    and t = shift_ty n k t in
    Ascribe (e, t)

  | MatchNat (e, ez, (m, esuc)) ->
    let e = shift n k e
    and ez = shift n k ez
    and esuc = shift (n+1) k esuc in
    MatchNat (e, ez, (m, esuc))

and shift_ty n k t = shift n k t

and shift_tyopt n k = function
  | None -> None
  | Some t -> Some (shift_ty n k t)
