open Pp
open CErrors
open Result
open Environ
open Names
open Constr
open Vars
open Primred
open Inductive

(* TODO:
  - Make all conversions accessible
  - Fixed non-head reduction "at"
*)

(* lazy1 si j'ai le temps *)
(* later: plugin potentiel: eval "red" at "pat", comme le message de Clément *)

(* do not use repeat step cbv, but let rec rscbv () := try (step cbv; rscbv ()) in rscbv () *)

(* real UIP conversion not applied: replace any expr from an invertible type to the only constructor *)
(* match let bindings should not be a thing, it should be a syntax that adds lets at the start of the branch or a syntactic sugar that is completely expanded *)

(* UTILITY *)

let array_with a n x = let a = Array.copy a in Array.unsafe_set a n x; a

let or_step f x g =
  match x with
  | Some x -> Some (f x)
  | None -> g ()

let or_else x f =
  match x with
  | None -> f ()
  | _ -> x

let for_step f e =
  let rec aux i = if i = e then None else or_else (f i) (fun _ -> aux (i + 1))
  in aux

let array_step_n f a =
  for_step (fun i -> Option.map (array_with a i) (f (Array.unsafe_get a i))) (Array.length a)

let array_step f a = array_step_n f a 0

let slist_step f s =
  let (p, s) =
    SList.Smart.fold_left_map
      ( fun acc x ->
        if acc then true, x else
          match f x with
          | Some x -> true, x
          | None -> false, x
      )
      false
      s
  in if p then Some s else None

let force msg = function
| Some x -> x
| None -> user_err (str msg)


(* ESSENTIALS *)

module KNativeEntries =
  struct
    type elem = constr
    type args = constr array
    type evd = unit
    type uinstance = UVars.Instance.t
    open UnsafeMonomorphic

    let get = Array.unsafe_get

    let get_int () e =
      match kind e with
      | Int i -> i
      | _ -> raise NativeDestKO

    let get_float () e =
      match kind e with
      | Float f -> f
      | _ -> raise NativeDestKO

    let get_string () e =
      match kind e with
      | String s -> s
      | _ -> raise NativeDestKO

    let get_parray () e =
      match kind e with
      | Array (_, t, def, _) -> Parray.of_array t def
      | _ -> raise NativeDestKO

    let mkInt _ = mkInt

    let mkFloat _ = mkFloat

    let mkString _ = mkString

    let mkBool env b =
      let ct, cf = get_bool_constructors env in
      mkConstruct (if b then ct else cf)

    let mkCarry env b e =
      let int_ty = mkConst @@ get_int_type env in
      let c0, c1 = get_carry_constructors env in
      mkApp (mkConstruct (if b then c1 else c0), [| int_ty; e |])

  let mkIntPair env e1 e2 =
    let int_ty = mkConst @@ get_int_type env in
    let c = get_pair_constructor env in
    mkApp (mkConstruct c, [| int_ty; int_ty; e1; e2 |])

  let mkFloatIntPair env f i =
    let float_ty = mkConst @@ get_float_type env in
    let int_ty = mkConst @@ get_int_type env in
    let c = get_pair_constructor env in
    mkApp (mkConstruct c, [| float_ty; int_ty; f; i |])

  let mkLt env =
    let _, lt, _ = get_cmp_constructors env in
    mkConstruct lt

  let mkEq env =
    let eq, _, _ = get_cmp_constructors env in
    mkConstruct eq

  let mkGt env =
    let _, _, gt = get_cmp_constructors env in
    mkConstruct gt

  let mkFLt env =
    let _, lt, _, _ = get_f_cmp_constructors env in
    mkConstruct lt

  let mkFEq env =
    let eq, _, _, _ = get_f_cmp_constructors env in
    mkConstruct eq

  let mkFGt env =
    let _, _, gt, _ = get_f_cmp_constructors env in
    mkConstruct gt

  let mkFNotComparable env =
    let _, _, _, nc = get_f_cmp_constructors env in
    mkConstruct nc

  let mkPNormal env =
    let pNormal, _, _, _, _, _, _, _, _ = get_f_class_constructors env in
    mkConstruct pNormal

  let mkNNormal env =
    let _, nNormal, _, _, _, _, _, _, _ = get_f_class_constructors env in
    mkConstruct nNormal

  let mkPSubn env =
    let _, _, pSubn, _, _, _, _, _, _ = get_f_class_constructors env in
    mkConstruct pSubn

  let mkNSubn env =
    let _, _, _, nSubn, _, _, _, _, _ = get_f_class_constructors env in
    mkConstruct nSubn

  let mkPZero env =
    let _, _, _, _, pZero, _, _, _, _ = get_f_class_constructors env in
    mkConstruct pZero

  let mkNZero env =
    let _, _, _, _, _, nZero, _, _, _ = get_f_class_constructors env in
    mkConstruct nZero

  let mkPInf env =
    let _, _, _, _, _, _, pInf, _, _ = get_f_class_constructors env in
    mkConstruct pInf

  let mkNInf env =
    let _, _, _, _, _, _, _, nInf, _ = get_f_class_constructors env in
    mkConstruct nInf

  let mkNaN env =
    let _, _, _, _, _, _, _, _, nan = get_f_class_constructors env in
    mkConstruct nan

  let mkArray env u t ty =
    let t, def = Parray.to_array t in
    mkArray (u, t, def, ty)

  end

module KredNative = RedNative(KNativeEntries)

let substn x =
  let rec aux n c =
    match kind c with
    | Rel i -> if i = n then x else c
    | _ -> map_with_binders succ aux n c
  in aux

let unlift c =
  let rec aux n c =
    match kind c with
    | Rel i ->
      ( match () with
        | () when i < n -> c
        | () when i > n -> mkRel (i - 1)
        | () -> raise DestKO
      )
    | _ -> map_with_binders succ aux n c
  in try Some (aux 1 c) with DestKO -> None

(* Term zipper
type zipper_of_term =
  | ZEvar      of Evar.t * constr SList.t (* TODO *)
  | ZCast      of zipper_of_term * cast_kind * types
  | ZProd1     of (Name.t, ERelevance.t) Context.pbinder_annot * zipper_of_term * types
  | ZProd2     of (Name.t, ERelevance.t) Context.pbinder_annot * types * zipper_of_term
  | ZLambdaT   of (Name.t, ERelevance.t) Context.pbinder_annot * zipper_of_term * constr
  | ZLambdaC   of (Name.t, ERelevance.t) Context.pbinder_annot * types * zipper_of_term
  | ZLetInT    of (Name.t, ERelevance.t) Context.pbinder_annot * constr * zipper_of_term * constr
  | ZLetInC1   of (Name.t, ERelevance.t) Context.pbinder_annot * zipper_of_term * types * constr
  | ZLetInC2   of (Name.t, ERelevance.t) Context.pbinder_annot * constr * types * zipper_of_term
  | ZApp       of int * zipper_of_term * constr array
  | ZCase      of case_info * EInstance.t * constr array * (types, ERelevance.t) pcase_return * constr pcase_invert * constr * (constr, ERelevance.t) pcase_branch array (* TODO *)
  | ZFix       of (constr, types, ERelevance.t) pfixpoint (* TODO *)
  | ZCoFix     of (constr, types, ERelevance.t) pcofixpoint (* TODO *)
  | ZProj      of Projection.t * ERelevance.t * zipper_of_term
  | ZArrayT    of EInstance.t * constr array * constr * zipper_of_term
  | ZArrayC    of EInstance.t * int * zipper_of_term * constr array * types
*)


(* COMMON REDUCTION PROCEDURES *)

(* No need to case on args, of_kind already ensures invariants *)
let beta_lambda_red head args =
  mkApp (subst1 (Array.unsafe_get args 0) head, CArray.tl args)

let delta_prim_red env (kn, u) args =
  match (lookup_constant kn env).const_body with
  | Primitive op ->
    let nargs = CPrimitives.arity op in
    let len = Array.length args in
    let fred args =
      match KredNative.red_prim env () op u args with
      | Some x -> Ok x
      | None -> Error "primitive cannot be reduced with provided arguments"
    in
    ( match () with
      | () when len < nargs -> Error "primitive applied to too few arguments"
      | () when len > nargs ->
        Result.map
          (fun head -> mkApp (head, Array.sub args nargs (len - nargs)))
          (fred (Array.sub args 0 nargs))
      | () -> fred args
    )
  | _ -> Error "not a primitive"

let delta_var_red env id =
  match lookup_named id env with
  | LocalDef (_, c, _) -> Some c
  | LocalAssum _  -> None

let delta_const_red env sp =
  try Ok (constant_value_in env sp)
  with NotEvaluableConst x -> Error x

let eta_prime_red env evm t c =
  try
    let head, args = destApp c in
    let nargs = Array.length args in
    let arg = Array.unsafe_get args (nargs - 1) in
    if arg != mkRel 1 then Error "Argument of the application under abstraction is not the bound variable." else
    match unlift (if nargs = 1 then head else mkApp (head, Array.sub args 0 (nargs - 1))) with
    | None -> Error "Variable bound by the abstraction is used more than once."
    | Some c ->
      let _, k, _ = EConstr.destProd evm (Retyping.get_type_of env evm (EConstr.of_constr c)) in
      match Reductionops.infer_conv env evm (EConstr.of_constr t) k with
      | Some _ -> Ok c
      | None -> Error "Performing eta reduction would change type."
  with DestKO -> Error "Term under abstraction is not an application."

let is_fix_reducible env ((reci, i), _) args =
  let argi = Array.unsafe_get reci i in
  argi < Array.length args &&
    match kind (Array.unsafe_get args argi) with
    | Construct _ -> true
    | App (head, _) -> isConstruct head
    | Const (kn, _) ->
      ( match (lookup_constant kn env).const_body with
        | Symbol true -> true (* Unholy rewrite get out of this kernel *)
        | _ -> false
      )
    | _ -> false

let fix_red env f args =
  if is_fix_reducible env f args
  then Some (mkApp (contract_fix f, args))
  else None

let proj_red pn args =
  let n = let open Projection in npars pn + arg pn in
  if n >= Array.length args then anomaly (str "Struct members missing.");
  Array.unsafe_get args n

let get_match_context env ci u pms =
  let mib, oib = lookup_mind_specif env ci.ci_ind in
  let paramsubst = Vars.subst_of_rel_context_instance (Vars.subst_instance_context u mib.mind_params_ctxt) pms in
  oib, paramsubst

let get_match_branch oib ps u brs c =
  let open Declarations in
  let binds, _ = Array.unsafe_get oib.mind_nf_lc c in
  let nbinds = Array.unsafe_get oib.mind_consnrealdecls c in
  let binds = CList.firstn nbinds binds in
  let nas, br = Array.unsafe_get brs c in
  Inductive.instantiate_context u ps nas binds, nas, br

let match_red env ci u c brs args =
  let nbrs = Array.length brs in
  if nbrs < c then anomaly (str "Not a constructor of the matched type.");
  let pms, args = CArray.chop ci.ci_npar args in
  let oib, ps = get_match_context env ci u pms in
  let c = c - 1 in
  let binds, _, br = get_match_branch oib ps u brs c in
  let term = Term.it_mkLambda_or_LetIn br binds in
  mkApp (term, args)

let match_uip_red = function
| [||] -> None
(* UIP is a stupid incorrect conversion that should be removed from Rocq. *)
| [| [||] , br |] -> Some br
| _ -> anomaly (str "UIP on a type which doesn't have a unique constructor with no parameters.")

(* Zeta in match bindings (breaks property of "one location = one reduction") and one-stepping now becomes harder *)
let zeta_match_red br nas brs c brn n =
  let br' = substn c n br in
  if br == br' then None else Some (array_with brs brn (nas, br'))

let projsurj_red env ind args =
  let get_record n c =
    let pn, _, bdy = destProj c in
    if not (eq_ind_chk (Projection.inductive pn) ind) || Projection.arg pn != n then raise DestKO;
    bdy
  in
  let mib = lookup_mind (fst ind) env in
  Result.bind
    ( match mib.mind_record with
      | PrimRecord x -> let _, x, _, _ = Array.unsafe_get x (snd ind) in Ok (Array.length x)
      | _ -> Error "Not a record constructor."
    )
    ( fun nproj ->
      let nargs = Array.length args in
      if mib.mind_nparams + nproj != nargs then Error "Record constructor applied to too few arguments." else
      try
        let base_c = get_record 0 (Array.unsafe_get args mib.mind_nparams) in
        let rec arg_loop n =
          let cn = n - mib.mind_nparams in
          if cn = 0 then Ok base_c else
          if Constr.equal (get_record cn (Array.unsafe_get args n)) base_c
          then arg_loop (n - 1)
          else Error "Terms under projections are not the same."
        in
        arg_loop (nargs - 1)
      with DestKO -> Error "Wrong projection."
    )

let app_head env head args =
  match kind head with
  | Lambda (_, _, c) -> Some (beta_lambda_red c args)
  | Fix f -> fix_red env f args
  | Const c -> Result.to_option (delta_prim_red env c args)
  | Construct ((ind, _), _) -> Result.to_option (projsurj_red env ind args)
  | _ -> None

let const_head env sp =
  match delta_const_red env sp with
  | Ok x -> Some x
  | Error (HasRules _) -> Feedback.msg_warning (str "Cannot reduce symbols."); None (* Rules should be removed from Rocq *)
  | Error _ -> None

let match_head env ci u pms bi iv c brs =
  match kind c with
  | Construct ((_, c), _) -> Some (match_red env ci u c brs [||])
  | CoFix cf -> Some (mkCase (ci, u, pms, bi, iv, contract_cofix cf, brs))
  | App (head, args) ->
    ( match kind head with
      | Construct ((_, c), _) -> Some (match_red env ci u c brs args)
      | CoFix cf -> Some (mkCase (ci, u, pms, bi, iv, mkApp (contract_cofix cf, args), brs))
      | _ -> None
    )
  | _ -> None

let zeta_match_head env ci u pms brs =
  let oib, ps = get_match_context env ci u pms in
  for_step
    ( fun i ->
      let nargs = Array.unsafe_get ci.ci_cstr_nargs i in
      let ndecls = Array.unsafe_get ci.ci_cstr_ndecls i in
      if nargs = ndecls then None else
      let binds, nas, br = get_match_branch oib ps u brs i in
      let rec bind_mapper n = let open Context.Rel.Declaration in function
      | [] -> None
      | LocalAssum _ :: t -> bind_mapper (n + 1) t
      | LocalDef (_, c, _) :: t ->
        or_else (zeta_match_red br nas brs c i n) (fun _ -> bind_mapper (n + 1) t)
      in
      bind_mapper 1 binds
    )
    (Array.length brs)
    0

let proj_head pn r c =
  if Projection.unfolded pn
  then
    ( match kind c with
      (* Construct impossible because `proj {||}` and `proj {| proj := |}` are not a thing *)
      | Construct _ -> anomaly (str "Projection on an empty struct.")
      | CoFix cf -> Some (mkProj (pn, r, contract_cofix cf))
      | App (head, args) ->
        ( match kind head with
          | Construct _ -> Some (proj_red pn args)
          | CoFix cf -> Some (mkProj (pn, r, mkApp (contract_cofix cf, args)))
          | _ -> None
        )
      | _ -> None
    )
  else Some (mkProj (Projection.unfold pn, r, c))


(* REDUCTION TACTICS *)

let cast_step c =
  match kind c with
  | Cast (ct, _, _) -> ct
  | _ -> user_err (str "No cast at head.")

let beta_step env c =
  try
    let head, args = destApp c in
    let _, _, c = destLambda head in
    beta_lambda_red c args
  with DestKO -> user_err (str "No applied lambda at head.")

let zeta_step c =
  match kind c with
  | LetIn (_, b, _, c) -> subst1 b c
  | _ -> user_err (str "No let-in at head.")

let zeta_match_step env ty brn n c =
  match kind c with
  | Case (ci, u, pms, bi, iv, c, brs) ->
    if not (eq_ind_chk ty ci.ci_ind) then user_err (str "Match at head is not matching on provided inductive.");
    let oib, ps = get_match_context env ci u pms in
    let binds, nas, br = get_match_branch oib ps u brs brn in
    let rec aux n k = let open Context.Rel.Declaration in function
    | [] -> user_err (str "Match at head has no such let bindings.")
    | LocalAssum _ :: t -> aux n (k + 1) t
    | LocalDef (_, c, _) :: t ->
      if n != 0 then aux (n - 1) (k + 1) t else
      force "Match let binding is already reduced." (zeta_match_red br nas brs c brn k)
    in
    mkCase (ci, u, pms, bi, iv, c, aux n 1 binds)
  | _ -> user_err (str "No match at head.")

(* TODO: find more elegant solution, but wait for "at" *)
let delta_step env e c =
  let open Evaluable in
  let open Projection in
  match kind c with
  | Var id ->
    ( match e with
      | Some (EvalVarRef i) when id = i -> ()
      | None -> ()
      | _ -> user_err (str "Name at head do not match.")
    ); force "Variable at head has no unfoldable definition." (delta_var_red env id)
  | Const sp ->
    ( match e with
      | Some (EvalConstRef cr) when cr = fst sp -> ()
      | None -> ()
      | _ -> user_err (str "Name at head do not match.")
    );
    ( match delta_const_red env sp with
      | Ok x -> x
      | Error Opaque -> user_err (str "Constant at head is opaque.")
      | Error NoBody -> user_err (str "Constant at head has no definition.")
      | Error (IsPrimitive _) -> user_err (str "Constant at head is a primitive.")
      | Error (HasRules _) -> user_err (str "Constant at head is a symbol with custom rewrite rules.")
    )
  | App (head, args) ->
    ( match kind head with
      | Const c ->
        ( match e with
          | Some (EvalConstRef cr) when cr = fst c -> ()
          | None -> ()
          | _ -> user_err (str "Name at head do not match.")
        );
        ( match delta_prim_red env c args with
          | Ok x -> x
          | Error x -> user_err (str ("Could not reduce primitive at head: " ^ x ^ "."))
        )
      | _ -> user_err (str "No applied primitive at head.")
    )
  | Proj (pn, r, c) when not (unfolded pn) ->
    ( match e with
      | Some (EvalProjectionRef p) when repr pn = p -> ()
      | None -> ()
      | _ -> user_err (str "Name at head do not match.")
    ); mkProj (unfold pn, r, c)
  | _ -> user_err (str "No unfoldable name at head.")

let eta_step env evm c =
  match kind (EConstr.Unsafe.to_constr (snd (Typing.type_of env evm (EConstr.of_constr c)))) with
  | Prod (na, k, _) -> mkLambda (na, k, mkApp (lift 1 c, [| mkRel 1 |]))
  | _ -> user_err (str "Head is not a function.")

let eta_prime_step env evm c =
  match kind c with
  | Lambda (_, t, c) ->
    ( match eta_prime_red env evm t c with
      | Ok x -> x
      | Error m -> user_err (str m)
    )
  | App (head, args) ->
    ( match kind head with
      | Construct ((ind, _), _)->
          ( match projsurj_red env ind args with
            | Ok x -> x
            | Error x -> user_err (str x)
          )
      | _ -> user_err (str "Application of a non constructor at head.")
    )
  | _ -> user_err (str "No abstraction or applied constructor at head.")

let evar_step evm c =
  match kind c with
  | Evar ev -> force "Evar at head has no unfoldable definition." (Evd.existential_opt_value0 evm ev)
  | _ -> user_err (str "No evar at head.")

let fix_prime_step c =
  match kind c with
  | Fix f -> contract_fix f
  | _ -> user_err (str "No fixpoint at head.")

let fix_step env c =
  try
    let head, args = destApp c in
    let f = destFix head in
    force "Fixpoint at head is not reducible." (fix_red env f args)
  with DestKO -> user_err (str "No applied fixpoint at head.")

let cofix_step c =
  match kind c with
  | Proj (pn, r, c) ->
    ( match kind c with
      | CoFix cf -> mkProj (pn, r, contract_cofix cf)
      | App (head, args) ->
        ( match kind head with
          | CoFix cf -> mkProj (pn, r, mkApp (contract_cofix cf, args))
          | _ -> user_err (str "Projection argument is not a cofix.")
        )
      | _ -> user_err (str "Projection argument is not a cofix.")
    )
  | Case (ci, u, pms, bi, iv, c, brs) ->
    ( match kind c with
      | CoFix cf -> mkCase (ci, u, pms, bi, iv, contract_cofix cf, brs)
      | App (head, args) ->
        ( match kind head with
          | CoFix cf -> mkCase (ci, u, pms, bi, iv, mkApp (contract_cofix cf, args), brs)
          | _ -> user_err (str "Not matching on a cofix.")
        )
      | _ -> user_err (str "Not matching on a cofix.")
    )
  | _ -> user_err (str "No match or primitive projection at head.")

let cofix_prime_step c =
  match kind c with
  | CoFix cf -> contract_cofix cf
  | _ -> user_err (str "No cofixpoint at head.")

let match_step env c =
  match kind c with
  | Proj (pn, r, c) when Projection.unfolded pn ->
    ( try
        (* Construct impossible because primitive have at least one projection *)
        let head, args = destApp c in
        if isConstruct head then proj_red pn args
        else raise DestKO
      with DestKO -> user_err (str "Projection argument is not a constructor at head.")
    )
  | Case (ci, u, pms, bi, iv, c, brs) ->
    ( match kind c with
      | Construct ((_, c), _) -> match_red env ci u c brs [||]
      | App (head, args) ->
        ( match kind head with
          | Construct ((_, c), _) -> match_red env ci u c brs args
          | _ -> user_err (str "Not matching on a constructor at head.")
        )
      | _ -> user_err (str "Not matching on a constructor at head.")
    )
  | _ -> user_err (str "No match or primitive projection at head.")

let match_uip_step c =
  match kind c with
  | Case (_, _, _, _, CaseInvert _, _, brs) ->
    force "No matched type with UIP at head." (match_uip_red brs)
  | _ -> user_err (str "No matched type with UIP at head.")

let head_step env evm c =
  match kind c with
  | Var id -> delta_var_red env id
  | Evar ev -> Evd.existential_opt_value0 evm ev
  | Cast (ct, _, _) -> Some ct
  | LetIn (na, b, u, c) -> Some (subst1 b c)
  | App (head, args) -> app_head env head args
  | Const sp -> const_head env sp
  | Case (ci, u, pms, bi, iv, c, brs) ->
    or_else (match_head env ci u pms bi iv c brs)
      ( fun _ ->
        or_else (match iv with CaseInvert _ -> match_uip_red brs | _ -> None)
          ( fun _ ->
            Option.map (fun brs -> mkCase (ci, u, pms, bi, iv, c, brs))
              (zeta_match_head env ci u pms brs)
          )
      )
  | Proj (pn, r, c) -> proj_head pn r c
  | Lambda (_, t, c) -> Result.to_option (eta_prime_red env evm t c)
  | Rel _ | Meta _ | Sort _ | Prod _ | Ind _ | Construct _ | Fix _ | CoFix _ | Int _ | Float _ | String _ | Array _ -> None

(* TODO NEXT: reduction order *)
let global_step evm env c =
  let rec cbv_aux env c =
    match kind c with
    | Var id -> delta_var_red env id
    | Evar (evi, ev) ->
      (* Evar solving is not considered progress :( *)
      or_step (fun ev -> mkEvar (evi, ev)) (slist_step (cbv_aux env) ev)
        (fun _ -> Evd.existential_opt_value0 evm (evi, ev))
    | Cast (ct, k, ck) ->
      (* Cast might be useful for performance until term below is fully reduced
        but cast stripping is not considered progress :(
      *)
      Some (match cbv_aux env ct with Some ct -> mkCast (ct, k, ck) | None -> ct)
    | Prod (na, t, u) ->
      or_step (fun t -> mkProd (na, t, u)) (cbv_aux env t)
        (fun _ -> Option.map (fun u -> mkProd (na, t, u)) (cbv_aux (push_rel (LocalAssum (na, t)) env) u))
    | Lambda (na, t, c) ->
      or_step (fun c -> mkLambda (na, t, c)) (cbv_aux (push_rel (LocalAssum (na, t)) env) c)
        (fun _ ->
          or_step (fun t -> mkLambda (na, t, c)) (cbv_aux env t)
            (fun _ -> Result.to_option (eta_prime_red env evm t c))
        )
    | LetIn (na, b, u, c) ->
      Some (
        match cbv_aux env b with Some b -> mkLetIn (na, b, u, c)
        | None ->
          match cbv_aux (push_rel (LocalDef (na, b, u)) env) c with Some c -> mkLetIn (na, b, u, c)
          | None -> subst1 b c
      )
    | App (head, args) ->
      or_step (fun head -> mkApp (head, args)) (cbv_aux env head)
        ( fun _ ->
          or_step (fun hd -> mkApp (head, array_with args 0 hd)) (cbv_aux env (Array.unsafe_get args 0))
            ( fun _ ->
              or_else (app_head env head args)
                (fun _ -> Option.map (fun args -> mkApp (head, args)) (array_step_n (cbv_aux env) args 1))
            )
        )
    | Const sp -> const_head env sp
    | Case (ci, u, pms, bi, iv, c, brs) ->
      or_step (fun c -> mkCase (ci, u, pms, bi, iv, c, brs)) (cbv_aux env c)
        ( fun _ ->
          or_else (match_head env ci u pms bi iv c brs)
            ( fun _ ->
              or_step (fun pms -> mkCase (ci, u, pms, bi, iv, c, brs)) (array_step (cbv_aux env) pms)
                ( fun _ ->
                  or_else (match iv with CaseInvert _ -> match_uip_red brs | _ -> None)
                    ( fun _ ->
                      or_step
                        (fun brs -> mkCase (ci, u, pms, bi, iv, c, brs))
                        (zeta_match_head env ci u pms brs)
                        ( fun _ ->
                          let mib, oib = lookup_mind_specif env ci.ci_ind in
                          let pd = Vars.subst_instance_context u mib.mind_params_ctxt in
                          let ps = Vars.subst_of_rel_context_instance pd pms in
                          or_step (fun brs -> mkCase (ci, u, pms, bi, iv, c, brs))
                            ( for_step
                              ( fun i ->
                                let binds, nas, br = get_match_branch oib ps u brs i in
                                Option.map (fun br -> array_with brs i (nas, br))
                                  (cbv_aux (push_rel_context binds env) br)
                              )
                              (Array.length brs)
                              0
                            )
                            ( fun _ ->
                              let (nas, p), rp = bi in
                              Option.map (fun p -> mkCase (ci, u, pms, ((nas, p), rp), iv, c, brs))
                                ( cbv_aux
                                  (push_rel_context (expand_arity (mib, oib) (ci.ci_ind, u) pms nas) env)
                                  p
                                )
                            )
                        )
                    )
                )
            )
        )
    | Fix (si, (names, tys, bds)) ->
      or_step (fun bds -> mkFix (si, (names, tys, bds)))
        (array_step (cbv_aux (push_rec_types (names, tys, bds) env)) bds)
        ( fun _ ->
          Option.map (fun tys -> mkFix (si, (names, tys, bds)))
            (array_step (cbv_aux env) tys)
        )
    | CoFix (ri, (names, tys, bds)) ->
      or_step (fun bds -> mkCoFix (ri, (names, tys, bds)))
        (array_step (cbv_aux (push_rec_types (names, tys, bds) env)) bds)
        ( fun _ ->
          Option.map (fun tys -> mkCoFix (ri, (names, tys, bds)))
            (array_step (cbv_aux env) tys)
        )
    | Proj (pn, r, c) ->
      or_step (fun c -> mkProj (pn, r, c)) (cbv_aux env c) (fun _ -> proj_head pn r c)
    | Array (u, t, def, ty) ->
      or_step (fun def -> mkArray (u, t, def, ty)) (cbv_aux env def)
        ( fun _ ->
          or_step (fun t -> mkArray (u, t, def, ty)) (array_step (cbv_aux env) t)
            (fun _ -> Option.map (fun ty -> mkArray (u, t, def, ty)) (cbv_aux env ty))
        )
    | Rel _ | Meta _ | Sort _ | Ind _ | Construct _ | Int _ | Float _ | String _ -> None
  in force "Term is fully reduced." (cbv_aux env c)

type ('a, 'b) reduction =
(*| RHRule (* Rewrite rules *)*)
| RHCast (* Head cast removal *)
| RHBeta (* Head beta: applied lambda to substitution *)
| RHZeta (* Head zeta: letin to substitution *)
| RHZetaMatch of 'a (* Head zetamatch: match-letin to substitution *)
| RHDelta of 'b option (* Head delta: name resolution *)
| RHEta (* Head eta expansion: expand lambda *)
| RHEtaPrime
(* Head eta reduction:
    - lambda over application on the only occurence of the variable
    - constructor on respective primitive projections
*)
| RHEvar (* Head evar: evar resolution + context substitution *)
| RHFix (* Head fix: push fixpoint inward when allowed to *)
| RHFixPrime (* Head fixprime: push fixpoint inward *)
| RHCofix (* Head cofix: match or project a cofix *)
| RHCofixPrime (* Head cofixprime: push cofix inward *)
| RHMatch (* Head match: match or project on a constructor *)
(* TODO: match UIP? *)
| RHInferUnique (* Head unique value inference: reduce match on a UIP type *)
| RHead (* Any head reduction *)
| RCbv (* Next reduction step of a call-by-value strategy *)
| RCbn (* Next reduction step of a call-by-name strategy *)
| RLazy (* Next reduction step of a call-by-need / lazy strategy *)

let map_reduction f g = function
| RHZetaMatch x -> RHZetaMatch (f x)
| RHDelta a -> RHDelta (Option.map g a)
| ( RHCast | RHBeta | RHZeta | RHEta | RHEtaPrime | RHEvar
  | RHFix | RHFixPrime | RHCofix | RHCofixPrime | RHMatch | RHInferUnique
  | RHead | RCbv | RCbn | RLazy as s
  ) -> s

let step red env evm c =
  let f =
    match red with
    | RHCast -> cast_step
    | RHBeta -> beta_step env
    | RHZeta -> zeta_step
    | RHZetaMatch (ind, n, m) -> zeta_match_step env ind (n - 1) (m - 1)
    | RHDelta t -> delta_step env t
    | RHEta -> eta_step env evm
    | RHEtaPrime -> eta_prime_step env evm
    | RHEvar -> evar_step evm
    | RHFix -> fix_step env
    | RHFixPrime -> fix_prime_step
    | RHCofix -> cofix_step
    | RHCofixPrime -> cofix_prime_step
    | RHMatch -> match_step env
    | RHInferUnique -> match_uip_step
    | RHead -> fun x -> force "Term at head is not reducible." (head_step env evm x)
    | RCbv -> global_step evm env (* LATER *)
    | RCbn -> global_step evm env (* LATER *)
    | RLazy -> global_step evm env (* LATER *)
  in
  evm, EConstr.of_constr (f (EConstr.Unsafe.to_constr c))