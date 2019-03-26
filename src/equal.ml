(** Equality and normalization. *)

(** A normalization strategy. *)
type strategy =
  | WHNF (** normalize to weak head-normal form *)
  | CBV (** call-by-value normalization *)

(** Normalize an expression. *)
let rec norm_expr ~strategy ctx e =
  match e with
  | TT.Bound k -> assert false

  | TT.Type -> e

  | TT.Nat -> e

  | TT.Zero -> e

  | TT.Succ e' -> TT.Succ (norm_expr ~strategy ctx e')

  | TT.Atom x ->
    begin
      match Context.lookup_def x ctx with
      | None -> e
      | Some e -> norm_expr ~strategy ctx e
    end

  | TT.Prod _ -> e

  | TT.Sum _ -> e

  | TT.Lambda _ -> e

  | TT.Apply (e1, e2) ->
    let e1 = norm_expr ~strategy ctx e1
    and e2 =
      begin
        match strategy with
        | WHNF -> e2
        | CBV -> norm_expr ~strategy ctx e2
      end
    in
    begin
      match e1 with
      | TT.Lambda (_, e') ->
        let e' = TT.instantiate 0 e2 e' in
        norm_expr ~strategy ctx e'
      | _ -> TT.Apply (e1, e2)
    end

  | TT.Pair (e1, e2) ->
    let e1 = norm_expr ~strategy ctx e1
    and e2 = norm_expr ~strategy ctx e2
    in
    TT.Pair(e1,e2)

  | TT.Fst e' ->
    let e' = norm_expr ~strategy ctx e'
    in
    begin
      match e' with
      | TT.Pair (e1, _) ->
        norm_expr ~strategy ctx e1
      | _ -> TT.Fst e'
    end

  | TT.Snd e' ->
    let e' = norm_expr ~strategy ctx e'
    in
    begin
      match e' with
      | TT.Pair (_, e2) ->
        norm_expr ~strategy ctx e2
      | _ -> TT.Snd e'
    end

(** Normalize a type *)
let norm_ty ~strategy ctx (TT.Ty ty) =
  let ty = norm_expr ~strategy ctx ty in
  TT.Ty ty

(** Normalize a type to a product. *)
let as_prod ctx t =
  let TT.Ty t' = norm_ty ~strategy:WHNF ctx t in
  match t' with
  | TT.Prod ((x, t), u) -> Some ((x, t), u)
  | _ -> None

(** Normalize a type to a sum. *)
let as_sum ctx t =
  let TT.Ty t' = norm_ty ~strategy:WHNF ctx t in
  match t' with
  | TT.Sum ((x, t), u) -> Some ((x, t), u)
  | _ -> None

(** Normalize a type to Nat. *)
let as_nat ctx t =
  let TT.Ty t' = norm_ty ~strategy:WHNF ctx t in
  match t' with
  | TT.Nat -> Some TT.Nat
  | _ -> None

(** Compare expressions [e1] and [e2] at type [ty]? *)
let rec expr ctx e1 e2 ty =
  (* Print.debug "%t =?= %t : %t" (TT.print_expr ~penv:(Context.penv ctx) e1) (TT.print_expr ~penv:(Context.penv ctx) e2) (TT.print_ty ~penv:(Context.penv ctx) ty); *)
  (* short-circuit *)
  (e1 == e2) ||
  begin
    (* The type directed phase *)
    let TT.Ty ty' = norm_ty ~strategy:WHNF ctx ty in
    match  ty' with

    | TT.Prod ((x, t), u) ->
      (* Apply function extensionality. *)
      let x' = TT.new_atom x in
      let ctx = Context.extend_ident x' t ctx
      and e1 = TT.Apply (e1, TT.Atom x')
      and e2 = TT.Apply (e2, TT.Atom x')
      and u = TT.unabstract_ty x' u in
      expr ctx e1 e2 u

    | TT.Sum ((x, t), u) ->
      (* Compare componentwise use Fst and Snd *)
      (expr ctx (TT.Fst e1) (TT.Fst e2) t) && (expr ctx (TT.Snd e1) (TT.Snd e2)  (TT.instantiate_ty 0 (TT.Fst e1) u))

    | TT.Type
    | TT.Apply _
    | TT.Fst _
    | TT.Snd _
    | TT.Nat 
    | TT.Zero
    | TT.Succ _
    | TT.Bound _
    | TT.Atom _ ->
      (* Type-directed phase is done, we compare normal forms. *)
      let e1 = norm_expr ~strategy:WHNF ctx e1
      and e2 = norm_expr ~strategy:WHNF ctx e2 in
      expr_whnf ctx e1 e2

    | TT.Pair _
    | TT.Lambda _ ->
      (* A type should never normalize to an abstraction *)
      assert false
  end

(** Structurally compare weak head-normal expressions [e1] and [e2]. *)
and expr_whnf ctx e1 e2 =
  (* Print.debug "%t =whnf= %t" (TT.print_expr ~penv:(Context.penv ctx) e1) (TT.print_expr ~penv:(Context.penv ctx) e2); *)
  match e1, e2 with

  | TT.Type, TT.Type -> true

  | TT.Bound k1, TT.Bound k2 ->
    (* We should never be in a situation where we compare bound variables,
       as that would mean that we forgot to unabstract a lambda or a product. *)
    assert false

  | TT.Atom x, TT.Atom y -> x = y

  | TT.Nat, TT.Nat -> true

  | TT.Zero, TT.Zero -> true

  | TT.Succ e1, TT.Succ e2 -> expr_whnf ctx e1 e2

  | TT.Prod ((x, t1), u1), TT.Prod ((_, t2), u2)  ->
    ty ctx t1 t2 &&
    begin
      let x' = TT.new_atom x in
      let ctx = Context.extend_ident x' t1 ctx
      and u1 = TT.unabstract_ty x' u1
      and u2 = TT.unabstract_ty x' u2 in
      ty ctx u1 u2
    end

  | TT.Sum ((x, t1), u1), TT.Sum ((_, t2), u2)  ->
    ty ctx t1 t2 &&
    begin
      let x' = TT.new_atom x in
      let ctx = Context.extend_ident x' t1 ctx
      and u1 = TT.unabstract_ty x' u1
      and u2 = TT.unabstract_ty x' u2 in
      ty ctx u1 u2
    end

  | TT.Lambda ((x, t1), e1), TT.Lambda ((_, t2), e2)  ->
    (* We should never have to compare two lambdas, as that would mean that the
       type-directed phase did not figure out that these have product types. *)
    assert false

  | TT.Apply (e11, e12), TT.Apply (e21, e22) ->
    (* Print.debug "{%t} %t =whnf_apply= {%t} %t" (TT.print_expr ~penv:(Context.penv ctx) e11) (TT.print_expr ~penv:(Context.penv ctx) e12) (TT.print_expr ~penv:(Context.penv ctx) e21) (TT.print_expr ~penv:(Context.penv ctx) e22); *)
    let rec collect sp1 sp2 e1 e2 =
      match e1, e2 with
      | TT.Apply (e11, e12), TT.Apply (e21, e22) ->
        collect (e12 :: sp1) (e22 :: sp2) e11 e21
      | TT.Atom a1, TT.Atom a2 ->
        Some ((a1, sp1), (a2, sp2))
      | _, _ -> None
    in
    begin
      match collect [e12] [e22] e11 e21 with
      | None -> false
      | Some ((a1, sp1), (a2, sp2)) -> 
        (* Print.debug "%t =whnf_app_collect= %t" (TT.print_expr ~penv:(Context.penv ctx) (TT.Atom a1)) (TT.print_expr ~penv:(Context.penv ctx) (TT.Atom a2)); *)
        spine ctx (a1, sp1) (a2, sp2)
    end

  | TT.Pair (e11, e12), TT.Pair(e21, e22) ->
    (* We should never have to compare two pairs, as that would mean that the
       type-directed phase did not figure out that these have sum types. *)
    assert false

  | TT.Fst e1, TT.Fst e2 ->
    (* Since e1 and e2 are normalised, we can only get to atoms or applications. Atoms don't care about 
       the types, applications compute them from the context *)
    expr_whnf ctx e1 e2 

  | TT.Snd e1, TT.Snd e2 ->
    (* Since e1 and e2 are normalised, we can only get to atoms or applications. Atoms don't care about 
       the types, applications compute them from the context *)
    expr_whnf ctx e1 e2

  | (TT.Type | TT.Bound _ | TT.Atom _ | TT.Prod _ | TT.Sum _ ), _ -> false
  | (TT.Lambda _ | TT.Pair _ | TT.Apply _ | TT.Fst _ | TT.Snd _ ), _ -> false
  | (TT.Nat | TT.Zero | TT.Succ _ ), _ -> false


(** Compare two types. *)
and ty ctx (TT.Ty ty1) (TT.Ty ty2) =
  expr ctx ty1 ty2 TT.ty_Type

(** Compare two spines of equal lengths.

    A spine is a nested application of the form [a e1 e2 ... en]
    where [a] is an atom.
*)
and spine ctx (a1, sp1) (a2, sp2) =
  a1 = a2 &&
  begin
    let rec fold ty sp1 sp2 =
      match as_prod ctx ty with
      | None -> assert false
      | Some ((x, t), u) -> 
        begin
          match sp1, sp2 with
          | [e1], [e2] -> expr ctx e1 e2 t 
          | e1 :: sp1, e2 :: sp2 ->
            expr ctx e1 e2 t &&
            begin
              let u = TT.instantiate_ty 0 e1 u in
              fold u sp1 sp2
            end
          | _, _ ->
            (* We should never be here, as the lengths of the spines should match. *)
            assert false
        end 
    in
    match Context.lookup_atom_ty a1 ctx with
    | None -> assert false
    | Some ty -> fold ty sp1 sp2
  end
