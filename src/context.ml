(** Typing context and definitional equalities. *)

(** Each entry in the context is bound to an atom and a type. *)
type entry = TT.atom * TT.ty

(** Each definitiona equality maps an atom to an expression. *)
type definition = TT.atom * TT.expr

(** Each type constructor definition maps an atom to a type of the argument and a type of the constructor. *)
type constructor_type = Name.ident * (TT.ty * TT.ty)

(** A typing context is a list of known identifiers and definitional equalities. *)
type context =
  {
    idents : entry list ;
    defs : definition list;
    types : constructor_type list
  }

(** The initial, empty typing context. *)
let initial = { idents = [] ; defs = []; types = [] }

(** The list of names which should not be used for printing bound variables. *)
let penv {idents; _} = List.map (fun ((x, _), _) -> x) idents

(** Extend the context with an identifier. *)
let extend_ident a t ctx = { ctx with idents = (a, t) :: ctx.idents }

(** Extend the context with a definitional equality. *)
let extend_def a e ctx = { ctx with defs = (a, e) :: ctx.defs }

(** Extend the context with a definitional equality. *)
let extend_types a e1 e2 ctx = { ctx with types = (a, (e1, e2)) :: ctx.types }

(** Lookup the type and value of the given de Bruijn index [k] *)
let lookup k {idents; _} =
  let rec search m = function
    | [] -> None
    | et :: lst -> if m = 0 then Some et else search (m - 1) lst
  in
  search k idents

(** Lookup the type of the given atom [a]. *)
let lookup_atom_ty a {idents; _} =
  try
    Some (List.assoc a idents)
  with
    Not_found -> None

(** Lookup the definitional equality of the given atom [a]. *)
let lookup_def a {defs; _} =
  try
    let e = List.assoc a defs in
    Some e
  with Not_found -> None

(** Lookup the type of the given constructor atom [a]. *)
let lookup_types a {types; _} =
  try
    let e = List.assoc a types in
    Some e
  with Not_found -> None

(** lookup all the constructors of a given type*)
let lookup_constructors ty {types; _} = 
  let rec search_construcotrs acc = function
    | [] -> acc
    | (constr_name, (ty_arg, ty_constr)) :: constructors ->
      if ty_constr = ty then (search_construcotrs (constr_name :: acc) constructors) else 
        search_construcotrs acc constructors in
  search_construcotrs [] types

let print_entry (a, ty) ppf =
  Print.print ppf "%t : %t" (TT.print_atom a) (TT.print_ty ~penv:[] ty)

let print_context ctx ppf =
  Print.sequence print_entry ", " ctx.idents ppf