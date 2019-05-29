(** Spartan type checking. *)

(** Type errors *)
type type_error =
  | InvalidIndex of int
  | TypeExpected of TT.ty * TT.ty
  | TypeExpectedButFunction of TT.ty
  | TypeExpectedButPair of TT.ty
  | FunctionExpected of TT.ty
  | NatExpected of TT.ty
  | CannotInferArgument of Name.ident
  | CannotInferType

(** Exception signalling a type error. *)
exception Error of type_error Location.located

(** [error ~loc err] raises the given type-checking error. *)
let error ~loc err = Pervasives.raise (Error (Location.locate ~loc err))

(** Print error description. *)
let print_error ~penv err ppf =
  match err with

  | InvalidIndex k -> Format.fprintf ppf "invalid de Bruijn index %d, please report" k

  | TypeExpected (ty_expected, ty_actual) ->
    Format.fprintf ppf "this expression should have type %t but has type %t"
      (TT.print_ty ~penv ty_expected)
      (TT.print_ty ~penv ty_actual)

  | TypeExpectedButFunction ty ->
    Format.fprintf ppf "this expression is a function but should have type %t"
      (TT.print_ty ~penv ty)

  | TypeExpectedButPair ty ->
    Format.fprintf ppf "this expression is a pair but should have type %t"
      (TT.print_ty ~penv ty)

  | FunctionExpected ty ->
    Format.fprintf ppf "this expression should be a function but has type %t"
      (TT.print_ty ~penv ty)

  | NatExpected ty ->
    Format.fprintf ppf "this expression should be a natural number but has type %t"
      (TT.print_ty ~penv ty)

  | CannotInferArgument x ->
    Format.fprintf ppf "cannot infer the type of %t" (Name.print_ident x)

  | CannotInferType ->
    Format.fprintf ppf "cannot infer the type of this expression"


(** [infer ctx e] infers the type [ty] of expression [e]. It returns
    the processed expression [e] and its type [ty].  *)
let rec infer ctx ({Location.data=e'; loc} as e) =
  Print.debug "%t ? => ?" (Context.print_context ctx);
  let (e'', ty) = infer' ctx e in
  (* Print.debug "%t => %t" (TT.print_expr ~penv:(Context.penv ctx) e'') (TT.print_ty ~penv:(Context.penv ctx) ty); *)
  (e'', ty)
and infer' ctx {Location.data=e'; loc}= 
  match e' with
  | Syntax.Var k ->
    begin
      Print.debug "%d" (k);
      match Context.lookup k ctx with
      | None -> error ~loc (InvalidIndex k)
      | Some (a, t) -> TT.Atom a, t
    end

  | Syntax.Type ->
    TT.Type, TT.ty_Type

  | Syntax.Nat ->
    TT.Nat, TT.ty_Type

  | Syntax.Zero -> 
    TT.Zero, TT.Ty TT.Nat

  | Syntax.Succ e ->
    let e1, t = infer ctx e in
    Print.debug "%t : %t" (TT.print_expr ~penv:(Context.penv ctx) e1)  (TT.print_ty ~penv:(Context.penv ctx) t);
    begin
      match Equal.as_nat ctx t with
      | None -> error ~loc (NatExpected t)
      | Some t ->
        TT.Succ e1, TT.Ty t
    end

  | Syntax.Prod ((x, t), u) ->
    let t = check_ty ctx t in
    let x' = TT.new_atom x in
    let ctx = Context.extend_ident x' t ctx in
    let u = check_ty ctx u in
    let u = TT.abstract_ty x' u in
    TT.Prod ((x, t), u),
    TT.ty_Type

  | Syntax.Sum ((x, t), u) ->
    let t = check_ty ctx t in
    let x' = TT.new_atom x in
    let ctx = Context.extend_ident x' t ctx in
    let u = check_ty ctx u in
    let u = TT.abstract_ty x' u in
    TT.Sum ((x, t), u),
    TT.ty_Type

  | Syntax.Lambda ((x, Some t), e) ->
    let t = check_ty ctx t in
    let x' = TT.new_atom x in
    let ctx  = Context.extend_ident x' t ctx in
    let e, u = infer ctx e in
    let e = TT.abstract x' e in
    let u = TT.abstract_ty x' u in
    TT.Lambda ((x, t), e),
    TT.Ty (TT.Prod ((x, t), u))

  | Syntax.Lambda ((x, None), _) ->
    error ~loc (CannotInferArgument x)

  | Syntax.Pair (e1, e2) ->
    error ~loc CannotInferType 

  | Syntax.Fst e ->
    let e1, t = infer ctx e in
    begin
      match Equal.as_sum ctx t with
      | None -> error ~loc (FunctionExpected t)
      | Some ((x, t), u) ->
        TT.Fst e1, t
    end

  | Syntax.Snd e ->
    let e1, t = infer ctx e in
    begin
      match Equal.as_sum ctx t with
      | None -> error ~loc (FunctionExpected t)
      | Some ((x, t), u) ->
        TT.Snd e1, TT.instantiate_ty 0 e1 u
    end


  | Syntax.Apply (e1, e2) ->
    let e1, t1 = infer ctx e1 in
    begin
      match Equal.as_prod ctx t1 with
      | None -> error ~loc (FunctionExpected t1)
      | Some ((x, t), u) ->
        let e2 = check ctx e2 t in
        TT.Apply (e1, e2),
        TT.instantiate_ty 0 e2 u
    end

  | Syntax.MatchNat (e, ez, (m, esuc)) ->
    let e1, nat = infer ctx e in
    begin
      match Equal.as_nat ctx nat with
      | None -> error ~loc (NatExpected nat)
      | Some nat1 ->
        let ez1, t = infer ctx ez in
        let m' = TT.new_atom m in
        let ctx'  = Context.extend_ident m' (TT.Ty nat1) ctx in
        Print.debug "kaj je esuc?";
        let esuc = check ctx' esuc t in
        Print.debug "imamo esuc!";
        let esuc = TT.abstract m' esuc in
        TT.MatchNat (e1, ez1, (m, esuc)), t
    end


  | Syntax.Ascribe (e, t) ->
    (* print_endline "a je tip?"; *)
    let t = check_ty ctx t in
    (* print_endline "a ima pravi tip?"; *)
    let e = check ctx e t in
    e, t

(** [check ctx e ty] checks that [e] has type [ty] in context [ctx].
    It returns the processed expression [e]. *)
and check ctx ({Location.data=e'; loc} as e) ty =
  match e' with

  | Syntax.Lambda ((x, None), e) ->
    begin
      match Equal.as_prod ctx ty with
      | None -> error ~loc (TypeExpectedButFunction ty)
      | Some ((x, t), u) ->
        let x' = TT.new_atom x in
        let ctx = Context.extend_ident x' t ctx
        and u = TT.unabstract_ty x' u in
        check ctx e u
    end

  | Syntax.Pair (e1, e2) ->
    begin
      match Equal.as_sum ctx ty with
      | None -> error ~loc (TypeExpectedButPair ty)
      | Some ((x, t), (TT.Ty u)) ->
        let e1' = check ctx e1 t in
        let e2' = check ctx e2 (TT.Ty (TT.instantiate 0 e1' u)) in
        TT.Pair (e1', e2')
    end

  | Syntax.MatchNat (e1, ez, (m, esuc)) ->
    let e1 = check ctx e1 (TT.Ty TT.Nat)
    and ez = check ctx ez ty in
    let m' = TT.new_atom m in
    let ctx = Context.extend_ident m' (TT.Ty TT.Nat) ctx in
    let esuc = check ctx esuc ty in (** double check esuc is ok, since m' is not instantiated? *)
    TT.MatchNat (e1, ez, (m, esuc))


  | Syntax.Lambda ((_, Some _), _)
  | Syntax.Apply _
  | Syntax.Prod _
  | Syntax.Sum _
  | Syntax.Var _
  | Syntax.Fst _
  | Syntax.Snd _
  | Syntax.Nat
  | Syntax.Zero
  | Syntax.Succ _
  | Syntax.Type
  | Syntax.Ascribe _ ->
    let e, ty' = infer ctx e in
    if Equal.ty ctx ty ty'
    then
      e
    else
      error ~loc (TypeExpected (ty, ty'))


(** [check_ty ctx t] checks that [t] is a type in context [ctx]. It returns the processed
    type [t]. *)
and check_ty ctx t =
  let t = check ctx t TT.ty_Type in
  TT.Ty t

(** Type-check a top-level command. *)
let rec toplevel ~quiet ctx {Location.data=tc; loc} =
  let ctx = toplevel' ~quiet ctx tc in
  ctx

and toplevel' ~quiet ctx = function

  | Syntax.TopLoad lst ->
    topfile ~quiet ctx lst

  | Syntax.TopDefinition (x, e) ->
    let e, ty = infer ctx e in
    let x' = TT.new_atom x in
    let ctx = Context.extend_ident x' ty ctx in
    let ctx = Context.extend_def x' e ctx in
    if not quiet then Format.printf "%t is defined.@." (Name.print_ident x) ;
    ctx

  | Syntax.TopCheck e ->
    let e, ty = infer ctx e in
    Format.printf "@[<hov>%t@]@\n     : @[<hov>%t@]@."
      (TT.print_expr ~penv:(Context.penv ctx) e)
      (TT.print_ty ~penv:(Context.penv ctx) ty) ;
    ctx

  | Syntax.TopEval e ->
    let e, ty = infer ctx e in
    let e = Equal.norm_expr ~strategy:Equal.CBV ctx e in
    Format.printf "@[<hov>%t@]@\n     : @[<hov>%t@]@."
      (TT.print_expr ~penv:(Context.penv ctx) e)
      (TT.print_ty ~penv:(Context.penv ctx) ty) ;
    ctx

  | Syntax.TopAxiom (x, ty) ->
    let ty = check_ty ctx ty in
    let x' = TT.new_atom x in
    let ctx = Context.extend_ident x' ty ctx in
    if not quiet then Format.printf "%t is assumed.@." (Name.print_ident x) ;
    ctx

(** Type-check the contents of a file. *)
and topfile ~quiet ctx lst =
  let rec fold ctx = function
    | [] -> ctx
    | top_cmd :: lst ->
      let ctx = toplevel ~quiet ctx top_cmd in
      fold ctx lst
  in
  fold ctx lst
