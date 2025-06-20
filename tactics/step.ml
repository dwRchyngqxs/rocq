open Pp
open CErrors
open Environ
open Names
open Constr
open EConstr
open Vars
open Reductionops
open Context.Rel.Declaration

(* TODO: custom rewrites do not accept "in" so I have to make the tactic separate _enough_ from the rewrite
  before trying to rebase controlled_red (aka. intergration in ltac and vernac) and fix it
*)
(* do not use repeat step cbv, but let rec rscbv () := try (step cbv; rscbv ()) in rscbv () *)

(* UTILITY *)

let id x = x

let map_left2 f1 f2 a1 a2 =
  let l = Array.length a1 in
  if Int.equal l 0 then [||], [||] else begin
    let r = Array.make l (f1 (Array.unsafe_get a1 0)) in
    let s = Array.make l (f2 (Array.unsafe_get a2 0)) in
    for i = 1 to l - 1 do
      Array.unsafe_set r i (f1 (Array.unsafe_get a1 i));
      Array.unsafe_set s i (f2 (Array.unsafe_get a2 i))
    done;
    r, s
  end

let array_with a n x = let a = Array.copy a in a.(n) <- x; a

let or_step f x g =
  match x with
  | Some x -> Some (f x)
  | None -> g ()

let rec first_step = function
| [] -> None
| h :: t ->
  match h () with
  | Some x -> Some x
  | None -> first_step t

let first_success msg l =
  let rec aux errs = function
  | [] -> Error errs
  | h :: t ->
    match h () with
    | Ok x -> Ok x
    | Error e -> aux (e :: errs) t
  in
  Result.map_error
    (fun l -> msg ++ pr_vertical_list id l)
    (aux [] l)

let opt_or x f =
  match x with
  | None -> f ()
  | Some x -> Some x

let for_step f e =
  let rec aux i =
    if i = e then None else opt_or (f i) (fun _ -> aux (i + 1))
  in aux

let array_step_n f a =
  for_step (fun i -> Option.map (array_with a i) (f (Array.unsafe_get a i))) (Array.length a)

let array_step f a = array_step_n f a 0

let slist_step f =
  let open SList in
  let rec aux = function
  | Nil -> None
  | Default (n, t) -> Option.map (defaultn n) (aux t)
  | Cons (h, t) -> or_step (fun h -> cons h t) (f h) (fun _ -> Option.map (cons h) (aux t))
  in aux

let to_result msg = function
| None -> Error msg
| Some x -> Ok x

let force msg = function
| Some x -> x
| None -> user_err (str msg)

let force' msg = function
| Some x -> x
| None -> anomaly (str msg)


(* REDUCTIONS ON TERMS *)

let beta_red head args = mkApp (subst1 args.(0) head, CArray.tl args)

let delta_prim_red env evm (op, u) args =
  let nargs = CPrimitives.arity op in
  let len = Array.length args in
  let fred args =
    to_result (str "cannot be reduced with provided arguments.")
      (CredNative.red_prim env evm op u args)
  in
  match () with
  | () when len < nargs -> Error (str "applied to too few arguments.")
  | () when len > nargs ->
    Result.map
      (fun head -> mkApp (head, Array.sub args nargs (len - nargs)))
      (fred (Array.sub args 0 nargs))
  | () -> fred args

let delta_var_red env id =
  match lookup_named id env with
  | LocalDef (_, c, _) -> Ok c
  | LocalAssum _  ->
    Error (
      str "variable "
      ++ Id.print id
      ++ str " has no unfoldable definition."
    )

let delta_const_red env evm (c, u) =
  try Ok (constant_value_in env evm (c, u))
  with NotEvaluableConst x -> Error x

let unlift evm c =
  let rec aux n c =
    match kind evm c with
    | Rel i -> (
      match () with
      | () when i < n -> c
      | () when i > n -> mkRel (i - 1)
      | () -> raise_notrace Exit
    )
    | _ -> map_with_binders evm succ aux n c
  in try Some (aux 1 c) with Exit -> None

let eta_lambda_red env evm t c =
  match kind evm c with
  | App (h, a) when isRelN evm 1 (CArray.last a) ->
    let nargs = Array.length a in
    ( match
        unlift evm
          (if nargs = 1 then h else mkApp (h, Array.sub a 0 (nargs - 1)))
      with
      | None -> Error (str "the variable bound by the abstraction is used more than once.")
      | Some c ->
        let tyc = Retyping.get_type_of env evm c in
        let _, k, _ = destProd evm tyc in
        if is_conv env evm t k
        then Ok c
        else Error (str "performing an eta reduction would change the type of the term.")
    )
  | _ -> Error (str "the term under the abstraction must be an application with the bound variable appearing only as the last argument of this application.")

(* primitive projection eta reduction *)
let eta_prim_red env evm ind args =
  let mib, mip = lookup_mind_specif env ind in
  Result.bind
    ( match mip.mind_record with
      | PrimRecord (_, x, _, _) -> Ok x
      | _ ->
        Error (
          str "type "
          ++ Printer.pr_inductive env ind
          ++ str " is not a primitive record."
        )
    )
    ( fun projs ->
      let get_record n c =
        match kind evm c with
        | Proj (pn, _, bdy) ->
          if QInd.equal env (Projection.inductive pn) ind
          then
            if Projection.arg pn = n then Ok bdy
            else
              Error (
                pr_nth (n + mib.mind_nparams + 1)
                ++ str " argument is the wrong projection; expected "
                ++ Id.print projs.(n)
                ++ str " got "
                ++ Projection.print pn
                ++ str "."
              )
          else
            Error (
              pr_nth n
              ++ str " argument is a projection of the wrong type; expected "
              ++ Printer.pr_inductive env (Projection.inductive pn)
              ++ str " got "
              ++ Printer.pr_inductive env ind
              ++ str "."
            )
        | _ -> Error (pr_nth n ++ str " argument is not a projection.")
      in
      let nproj = Array.length projs in
      let nargs = Array.length args in
      if mib.mind_nparams + nproj != nargs
      then
        Error (
          str "record constructor is not fully applied; expected "
          ++ int (mib.mind_nparams + nproj)
          ++ str " arguments, got "
          ++ int nargs
          ++ str "."
        )
      else
        Result.bind (get_record 0 args.(mib.mind_nparams)) (fun base_c ->
          let rec arg_loop n =
            let cn = n - mib.mind_nparams in
            if cn = 0 then Ok base_c else
            Result.bind (get_record cn args.(n)) (fun new_c ->
              if eq_constr evm base_c new_c then arg_loop (n - 1)
              else
                Error (
                  str "term under the projection differ between the "
                  ++ pr_nth (mib.mind_nparams + 1)
                  ++ str " and "
                  ++ pr_nth (cn + 1)
                  ++ str " argument."
                )
            )
          in arg_loop (nargs - 1)
        )
    )

let is_fix_reducible env evm ((reci, i), _) args =
  let argi = reci.(i) in
  argi < Array.length args &&
  match kind evm args.(argi) with
  | Construct _ -> true
  | App (head, _) -> isConstruct evm head
  | Const (kn, _) -> (
    match (lookup_constant env evm kn).const_body with
    | Symbol true -> true (* Unholy rewrite get out of this kernel *)
    | _ -> false
  )
  | _ -> false

let iota_fix_red env evm ((reci, i), (nas, _, _) as f) args =
  if is_fix_reducible env evm f args
  then Ok (mkApp (contract_fix evm f, args))
  else
    Error (
      pr_nth (reci.(i) + 1)
      ++ str "argument of fixpoint "
      ++ Name.print nas.(i).binder_name
      ++ str " is not an applied constructor."
    )

let proj_red pn args =
  let n = Projection.(npars pn + arg pn) in
  if n >= Array.length args then anomaly (str "Struct members missing.");
  args.(n)

let bind_to_index =
  let rec aux k m = function
  | [] -> user_err (str "Invalid let binding for zeta_match.")
  | LocalAssum _ :: t -> aux (k + 1) m t
  | LocalDef (_, _, _) :: t -> if m != 1 then aux (k + 1) (m - 1) t else k
  in aux 0

let iota_match_red env ci u c brs args =
  let nbrs = Array.length brs in
  if nbrs < c then anomaly (str "Not a constructor of the matched type.");
  let c = c - 1 in
  let pms, args = CArray.chop ci.ci_npar args in
  let nas, br = Array.unsafe_get brs c in
  let ctx = case_branch_context env (ci.ci_ind, u) pms nas c in
  mkApp (it_mkLambda_or_LetIn br ctx, args)

let iota_uip_specif env evm (mib, mip) ps indices = function
| [||] -> Error (str "cannot eliminate a type without constructors in SProp.")
| [| [||] , br |] ->
  let open Declarations in
  let expect_indices =
    try snd (Constr.destApp (snd mip.mind_nf_lc.(0)))
    with DestKO -> [||]
  in
  let nind = Array.length indices in
  let rec loop i =
    if Int.equal nind i then Ok br else
    let expected = expect_indices.(mib.mind_nparams + i) in
    let expected = substl ps (of_constr expected) in
    if Reductionops.is_conv env evm expected indices.(i)
    then loop (i + 1)
    else Error (
      pr_nth (mib.mind_nparams + i)
      ++ str " parameter prevents elimination in SProp; expected "
      ++ quote (hov 0 (Printer.pr_econstr_env env evm expected))
      ++ str " got "
      ++ quote (hov 0 (Printer.pr_econstr_env env evm indices.(i)))
      ++ str "."
    )
  in loop 0
| _ -> anomaly (str "Cannot eliminate a type with several constructors in SProp.")

let iota_uip_red env evm ci u pms iv brs =
  let open Constr in
  match iv with
  | CaseInvert {indices} ->
    let mib, mip = lookup_mind_specif env ci.ci_ind in
    let ps = case_parameter_context_specif mib u pms in
    iota_uip_specif env evm (mib, mip) ps indices brs
  | NoInvert -> Error (str "type cannot be eliminated in SProp.")

let substn evm x =
  let rec aux n c =
    match kind evm c with
    | Rel i -> if Int.equal i n then x else c
    | _ -> map_with_binders evm succ aux n c
  in aux

(* Zeta in match bindings
  (breaks property of "one location = one reduction")
  and one-stepping now becomes harder
*)
let zeta_match_red evm br nas brs c brn n =
  let br' = substn evm c n br in
  if br == br' then Error (str "match let binding is already reduced.")
  else Ok (array_with brs brn (nas, br'))


(* HEAD AND REDUCTION STRATEGY HELPERS *)

let app_head env evm head args =
  match kind evm head with
  | Lambda (_, _, c) -> Ok (beta_red c args)
  | Fix f -> iota_fix_red env evm f args
  | Const (c, u) -> (
    match get_primitive env c with
    | Some op -> delta_prim_red env evm (op, u) args
    | None -> Error (str "No reduction applicable.")
  )
  | Construct ((ind, _), _) -> eta_prim_red env evm ind args
  | _ -> Error (str "No reduction applicable.")

let const_head env evm sp =
  let the_const () = str "constant " ++ Printer.pr_constant env (fst sp) in
  Result.map_error
    ( function
      | NoBody -> the_const () ++ str " has no definition."
      | Opaque -> the_const () ++ str " is opaque."
      | IsPrimitive _ -> the_const () ++ str " is an unapplied primitive."
      | HasRules _ -> (* Rules should be removed from Rocq *)
        Feedback.msg_warning (str "Cannot reduce symbols.");
        the_const () ++ str " is a symbol with custom rewrite rules."
    )
    (delta_const_red env evm sp)

let iota_match_head env evm (ci, u, pms, bi, iv, c, brs) =
  match kind evm c with
  | Construct ((_, c), _) -> Ok (iota_match_red env ci u c brs [||])
  | CoFix cf -> Ok (mkCase (ci, u, pms, bi, iv, contract_cofix evm cf, brs))
  | App (head, args) -> (
    match kind evm head with
    | Construct ((_, c), _) -> Ok (iota_match_red env ci u c brs args)
    | CoFix cf ->
      Ok (mkCase (ci, u, pms, bi, iv, mkApp (contract_cofix evm cf, args), brs))
    | _ -> Error (str "Failed iota reduction: scrutinee is not an applied constructor or cofix.")
  )
  | _ -> Error (str "Failed iota reduction: scrutinee is not an applied constructor or cofix.")

let zeta_match_step evm brn n env (ci, u, pms, bi, iv, c, brs) =
  let nas, br = brs.(brn) in
  let ctx = case_branch_context env (ci.ci_ind, u) pms nas brn in
  let bind =
    match List.nth ctx n with
    | LocalDef (_, c, _) -> c
    | _ -> assert false
  in
  Result.map (fun brs -> mkCase (ci, u, pms, bi, iv, c, brs))
    (zeta_match_red evm br nas brs bind brn (n + 1))

let zeta_match_head env evm ci u pms brs =
  let mib, mip = lookup_mind_specif env ci.ci_ind in
  let ps = case_parameter_context_specif mib u pms in
  to_result
    (str "Failed zeta reduction: all the let bindings are already reduced")
    ( for_step
      ( fun i ->
        let nargs = ci.ci_cstr_nargs.(i) in
        let ndecls = ci.ci_cstr_ndecls.(i) in
        if nargs = ndecls then None else
        let nas, br = brs.(i) in
        let ctx = case_branch_context_specif mip ps u nas i in
        let rec bind_mapper n = function
        | [] -> None
        | LocalAssum _ :: t -> bind_mapper (n + 1) t
        | LocalDef (na, c, _) :: t ->
          opt_or (Result.to_option (zeta_match_red evm br nas brs c i n))
            (fun _ -> bind_mapper (n + 1) t)
        in
        bind_mapper 1 ctx
      )
      (Array.length brs)
      0
    )

let proj_head evm pn r c =
  match kind evm c with
  (* Construct impossible because `proj {||}` and `proj {| proj := |}` are not a thing *)
  | Construct _ -> anomaly (str "Projection on an empty struct.")
  | CoFix cf -> Ok (mkProj (pn, r, contract_cofix evm cf))
  | App (head, args) -> (
    match kind evm head with
    | Construct _ -> Ok (proj_red pn args)
    | CoFix cf -> Ok (mkProj (pn, r, mkApp (contract_cofix evm cf, args)))
    | _ -> Error (str "Failed iota reduction: scrutinee is not an applied constructor or cofix.")
  )
  | _ -> Error (str "Failed iota reduction: scrutinee is not an applied constructor or cofix.")

let proj_step evm pn r c =
  if Projection.unfolded pn then proj_head evm pn r c
  else Ok (mkProj (Projection.unfold pn, r, c))


(* ZIPPERS, MUTATOR, VISITOR *)

(* Evar context zipper *)
module TermSListZipper = struct
  open SList

  type t =
  { mutable left: constr SList.t;
    mutable right: constr SList.t;
    (* keep old term and slist to preserve sharing *)
    mutable cache: constr option
  }
  type t_const =
  { cleft: constr SList.t;
    cright: constr SList.t
  }

  let make =
    let rec aux acc = function
    | Nil -> None
    | Cons (h, t) -> Some ({left = acc; right = t; cache = Some h}, h)
    | Default (n, t) -> aux (SList.defaultn n acc) t
    in aux empty

  let to_const {left; right; _} = {cleft = left; cright = right}

  let update_cache cache old knew =
    Option.bind cache (fun h -> if h == old then Some knew else None)

  let update s old l r knew =
    s.left <- l;
    s.right <- r;
    s.cache <- update_cache s.cache old knew

  let rec rev_append acc = function
  | Nil -> acc
  | Cons (h, t) -> rev_append (cons h acc) t
  | Default (n, t) -> rev_append (defaultn n acc) t

  let unzip {left; right; cache} t =
    match cache with
    | Some h when t == h -> None
    | _ -> Some (rev_append (SList.cons t right) left)

  let rec unzip_one acc = function
  | SList.Nil -> Error acc
  | SList.Cons (h, t) -> Ok (t, h, acc)
  | SList.Default (n, t) -> unzip_one (SList.defaultn n acc) t

  let move s t =
    let use_cache sl =
      Error (
        match s.cache with
        | Some h when t == h -> None
        | _ -> Some sl
      )
    in function
    | Either.Left () -> (
      match unzip_one (cons t s.right) s.left with
      | Ok (left, h, right) -> update s t left right h; Ok h
      | Error sl -> use_cache sl
    )
    | Either.Right () ->
      match unzip_one (cons t s.left) s.right with
      | Ok (right, h, left) -> update s t left right h; Ok h
      | Error sl -> use_cache sl

  let _ = make, to_const, unzip, move
end

module TermZipper = struct
  type 't tern_pos = TLeft of 't | TMiddle | TRight
  type case_pos = CMatchee | CParams of int | CArity | CBranch of int

  (* zipper keeping old term to preserve sharing *)
  type context =
  | CEvar   of Evar.t (* Looking at evar ctx zipper *)
  | CEvarC  of TermSListZipper.t (* Looking at part of the evar ctx *)
  | CCast   of constr * cast_kind * types (* Never touch cast type *)
  | CProd   of (unit, unit) Either.t * Name.t binder_annot * types * types
  | CLambda of (unit, unit) Either.t * Name.t binder_annot * types * constr
  | CLetIn  of unit tern_pos * Name.t binder_annot * constr * types * constr
  | CApp    of (unit, int) Either.t * constr * constr array
  | CCase   of case_pos * case
  | CFix    of (int, int) Either.t * fixpoint
  | CCoFix  of (int, int) Either.t * cofixpoint
  | CProj   of Projection.t * ERelevance.t * constr
  | CArray  of int tern_pos * EInstance.t * constr array * constr * types

  (* Aggressive cache: All superterms are trashed as soon as they are invalidated. *)
  type t =
  { mutable rel_ctx: rel_context; (* local beta/zeta *)
    mutable ctx: context list;
    mutable cache: constr list
  }
  type t_const =
  { crel_ctx: rel_context;
    cctx: context list
  }

  let make = {rel_ctx = []; ctx = []; cache = []}

  let make_open rel_ctx = {rel_ctx; ctx = []; cache = []}

  let to_const {rel_ctx; ctx; _} = {crel_ctx = rel_ctx; cctx = ctx}

  let pop_cache tz =
    match tz.cache with
    | [] -> None
    | h :: t -> tz.cache <- t; Some h

  let unzip_evar ev z t =
    Option.map (fun sl -> mkEvar (ev, sl)) (TermSListZipper.unzip z t)

  let unzip_one_no_cache x = function
  | CEvar _ | CEvarC _ -> anomaly (str "Ill formed evar context.")
  | CCast (c, k, t) -> mkCast (x, k, t)
  | CProd (p, na, k, t) -> (
    match p with
    | Either.Left () -> mkProd (na, x, t)
    | Either.Right () -> mkProd (na, k, x)
  )
  | CLambda (p, na, t, c) -> (
    match p with
    | Either.Left () -> mkLambda (na, x, c)
    | Either.Right () -> mkLambda (na, t, x)
  )
  | CLetIn (p, na, b, t, c) -> (
    match p with
    | TLeft () -> mkLetIn (na, b, x, c)
    | TMiddle -> mkLetIn (na, x, t, c)
    | TRight -> mkLetIn (na, b, t, x)
  )
  | CApp (p, head, args) -> (
    match p with
    | Either.Left () -> mkApp (x, args)
    | Either.Right n -> mkApp (head, array_with args n x)
  )
  | CCase (pos, (ci, u, pms, p, iv, c, brs)) -> (
    match pos with
    | CMatchee -> mkCase (ci, u, pms, p, iv, x, brs)
    | CParams n -> mkCase (ci, u, array_with pms n x, p, iv, c, brs)
    | CArity -> let p, r = p in mkCase (ci, u, pms, ((fst p, x), r), iv, c, brs)
    | CBranch n ->
      let na, b = brs.(n) in
      mkCase (ci, u, pms, p, iv, c, array_with brs n (na, x))
  )
  | CFix (p, (si, (nas, tys, bds))) -> (
    match p with
    | Either.Left n -> mkFix (si, (nas, array_with tys n x, bds))
    | Either.Right n -> mkFix (si, (nas, tys, array_with bds n x))
  )
  | CCoFix (p, (ri, (nas, tys, bds))) -> (
    match p with
    | Either.Left n -> mkCoFix (ri, (nas, array_with tys n x, bds))
    | Either.Right n -> mkCoFix (ri, (nas, tys, array_with bds n x))
  )
  | CProj (pn, r, c) -> mkProj (pn, r, x)
  | CArray (p, u, ts, def, ty) ->
    match p with
    | TLeft n -> mkArray (u, array_with ts n x, def, ty)
    | TMiddle -> mkArray (u, ts, x, ty)
    | TRight -> mkArray (u, ts, def, x)

  let unzip {ctx; cache; _} t =
    let rec aux_no_cache x = function
    | [] -> x
    | CEvarC z :: CEvar ev :: t ->
      aux_no_cache
        (mkEvar (ev, TermSListZipper.(rev_append (SList.cons x z.right) z.left)))
        t
    | h :: t -> aux_no_cache (unzip_one_no_cache x h) t
    in
    let rec aux x = function
    | CEvarC _ :: CEvar _ :: ctx, c :: cache
    | _ :: ctx, c :: cache -> aux c (ctx, cache)
    | ctx, [] -> aux_no_cache x ctx
    | _ -> anomaly (str "Ill formed context.")
    in aux t (ctx, cache)

  let move_up_evarc tz cz t =
    match tz.ctx with
    | CEvar ev :: ctx ->
      tz.ctx <- ctx;
      first_step [
        (fun _ -> pop_cache tz);
        (fun _ -> unzip_evar ev cz t);
        fun _ -> anomaly (str "Inconsistent cache.")
      ]
    | [] -> None
    | _ -> anomaly (str "Ill formed context.")

  let unzip_evarc tz cz t =
    match tz.ctx with
    | CEvar ev :: ctx ->
      unzip tz (
        force' "Inconsistent cache." (
          opt_or (pop_cache tz) (fun _ -> unzip_evar ev cz t)
        )
      )
    | _ -> anomaly (str "Ill formed context.")

  let rel_ctx_skipn tz n =
    try tz.rel_ctx <- CList.skipn n tz.rel_ctx
    with Failure _ -> anomaly (str "Ill formed context.")

  let pop_context env tz = function
  | CProd (Right (), _, _, _) | CLambda (Right (), _, _, _)
  | CLetIn (TRight, _, _, _, _) -> rel_ctx_skipn tz 1
  | CCase (CArity, (ci, _, _, _, _, _, _)) ->
    let _, oib = lookup_mind_specif env ci.ci_ind in
    rel_ctx_skipn tz (oib.mind_nrealdecls + 1)
  | CCase (CBranch n, (ci, _, _, _, _, _, _)) ->
    let _, oib = lookup_mind_specif env ci.ci_ind in
    rel_ctx_skipn tz (oib.mind_consnrealdecls.(n))
  | CFix (Right n, (_, (nas, _, _))) | CCoFix (Right n, (_, (nas, _, _))) ->
    rel_ctx_skipn tz (Array.length nas)
  | _ -> ()

  type unzip_res = Fail | Term of constr | EvarContext of TermSListZipper.t
  let move_up env tz t =
    match tz.ctx with
    | [] -> Fail
    | CEvar _ :: _ -> anomaly (str "Evar context must be unzipped with move_up_evarc.")
    | CEvarC cz :: ctx -> tz.ctx <- ctx; EvarContext cz
    | h :: ctx ->
      tz.ctx <- ctx;
      pop_context env tz h;
      Term (
        match pop_cache tz with
        | Some t -> t
        | None -> unzip_one_no_cache t h
      )

  let zip_evar tz ev sl = tz.ctx <- CEvar ev :: tz.ctx; TermSListZipper.make sl

  let zip_evarc tz cz t = tz.ctx <- CEvarC cz :: tz.ctx; t

  let zip_cast tz c k t = tz.ctx <- CCast (c, k, t) :: tz.ctx; c

  (* TODO HERE: push rel_context *)
  let zip_prod tz d na b c =
    tz.ctx <- CProd (d, na, b, c) :: tz.ctx;
    match d with
    | Either.Left () -> b
    | Either.Right () -> c

  (* TODO HERE: push rel_context *)
  let zip_lambda tz d na t c =
    tz.ctx <- CLambda (d, na, t, c) :: tz.ctx;
    match d with
    | Either.Left () -> t
    | Either.Right () -> c

  (* TODO HERE: push rel_context *)
  let zip_letin tz d na b u c =
    tz.ctx <- CLetIn (d, na, b, u, c) :: tz.ctx;
    match d with
    | TLeft () -> u
    | TMiddle -> b
    | TRight -> c

  let zip_app tz d head args =
    tz.ctx <- CApp (d, head, args) :: tz.ctx;
    match d with
    | Either.Left () -> Some head
    | Either.Right k when 0 <= k && k < Array.length args ->
      Some (Array.unsafe_get args k)
    | _ -> None

  (* TODO HERE: push rel_context *)
  let zip_case tz d (_, _, pms, ((_, p), _), _, c, brs as case) =
    tz.ctx <- CCase (d, case) :: tz.ctx;
    match d with
    | CMatchee -> Some c
    | CParams k when 0 <= k && k < Array.length pms ->
      Some (Array.unsafe_get pms k)
    | CArity -> Some p
    | CBranch k when 0 <= k && k < Array.length brs ->
      Some (snd (Array.unsafe_get brs k))
    | _ -> None

  (* TODO HERE: push rel_context *)
  let zip_fix tz d (_, (_, tys, bds) as f) =
    tz.ctx <- CFix (d, f) :: tz.ctx;
    match d with
    | Either.Left k when 0 <= k && k < Array.length tys ->
      Some (Array.unsafe_get tys k)
    | Either.Right k when 0 <= k && k < Array.length bds ->
      Some (Array.unsafe_get bds k)
    | _ -> None

  (* TODO HERE: push rel_context *)
  let zip_cofix tz d (_, (_, tys, bds) as cf) =
    tz.ctx <- CCoFix (d, cf) :: tz.ctx;
    match d with
    | Either.Left k when 0 <= k && k < Array.length tys ->
      Some (Array.unsafe_get tys k)
    | Either.Right k when 0 <= k && k < Array.length bds ->
      Some (Array.unsafe_get bds k)
    | _ -> None

  let zip_proj tz pn r c = tz.ctx <- CProj (pn, r, c) :: tz.ctx; c

  let zip_array tz d u ts def ty =
    tz.ctx <- CArray (d, u, ts, def, ty) :: tz.ctx;
    match d with
    | TLeft k when 0 <= k && k < Array.length ts ->
      Some (Array.unsafe_get ts k)
    | TMiddle -> Some def
    | TRight -> Some ty
    | _ -> None

  let _ =
    TLeft (),
    TMiddle,
    TRight,
    CMatchee,
    CParams 0,
    CArity,
    CBranch 0,
    make,
    make_open,
    to_const,
    unzip,
    move_up_evarc,
    unzip_evarc,
    move_up,
    zip_evar,
    zip_evarc,
    zip_cast,
    zip_prod,
    zip_lambda,
    zip_letin,
    zip_app,
    zip_case,
    zip_fix,
    zip_cofix,
    zip_proj,
    zip_array
end

module TermMutator = struct
  type 't mutation =
  { trigger: 't -> bool;
    rewrite: 't -> (constr, Pp.t) Result.t
  }
  type t =
  { rel: (env * int) mutation option;
    var: (env * Id.t) mutation option;
    meta: metavariable mutation option;
    evar: existential mutation option;
    sort: ESorts.t mutation option;
    cast: (constr * cast_kind * types) mutation option;
    prod: (Name.t binder_annot * types * types) mutation option;
    lambda: (env * Name.t binder_annot * types * constr) mutation option;
    letin: (Name.t binder_annot * constr * types * constr) mutation option;
    app: (env * constr * constr array) mutation option;
    const: (env * Constant.t * EInstance.t) mutation option;
    ind: (inductive * EInstance.t) mutation option;
    construct: (constructor * EInstance.t) mutation option;
    case: (env * case) mutation option;
    fix: fixpoint mutation option;
    cofix: cofixpoint mutation option;
    proj: (env * Projection.t * ERelevance.t * constr) mutation option;
    int: Uint63.t mutation option;
    float: Float64.t mutation option;
    string: Pstring.t mutation option;
    array: (EInstance.t * constr array * constr * types) mutation option
  }

  let idle_mutator = {
    rel = None;
    var = None;
    meta = None;
    evar = None;
    sort = None;
    cast = None;
    prod = None;
    lambda = None;
    letin = None;
    app = None;
    const = None;
    ind = None;
    construct = None;
    case = None;
    fix = None;
    cofix = None;
    proj = None;
    int = None;
    float = None;
    string = None;
    array = None
  }

  type occ_count =
  { mutable atleastone: bool;
    mutable occs: Locusops.occurrences_count
  }

  let mutate evm occs mutator env t =
    let count = {
      atleastone = occs != Locus.AtLeastOneOccurrence;
      occs = Locusops.initialize_occurrence_counter occs
    } in
    let update_cnt () =
      let ok, count' = Locusops.update_occurrence_counter count.occs in
      count.occs <- count';
      ok
    in
    let add_occ occ ft = function
    | Ok t -> count.atleastone <- true; t
    | Error e ->
      if Locusops.is_all_occurrences occs then ft ()
      else user_err (str "Error at " ++ pr_nth occ ++ str " occurence: " ++ e)
    in
    let f_leaf s d t =
      match s with
      | Some {trigger; rewrite} when trigger d && update_cnt () ->
        add_occ
          (Locusops.current_occurrence count.occs)
          (fun _ -> t)
          (rewrite d)
      | _ -> t
    in
    let prep_node s d =
      Option.bind s (fun {trigger; rewrite} ->
        if trigger d && update_cnt ()
        then Some (rewrite, Locusops.current_occurrence count.occs)
        else None
      )
    in
    let step_node ft d = function
    | Some (rw, occ) -> add_occ occ ft (rw d)
    | None -> ft ()
    in
    let array_phys_eq = Array.for_all2 (==) in
    let rec traverse env t =
      if Locusops.occurrences_done count.occs then (* Shortcut *) t else
      match kind evm t with
      | Rel i -> f_leaf mutator.rel (env, i) t
      | Var id -> f_leaf mutator.var (env, id) t
      | Meta m -> f_leaf mutator.meta m t
      | Evar (ev, sl) ->
        let rw = prep_node mutator.evar (ev, sl) in
        let sl' = SList.Smart.map (traverse env) sl in
        step_node
          (fun _ -> if sl == sl' then t else mkEvar (ev, sl'))
          (ev, sl')
          rw
      | Sort s -> f_leaf mutator.sort s t
      | Cast (c, k, ty) ->
        let rw = prep_node mutator.cast (c, k, ty) in
        let c' = traverse env c in
        step_node
          (fun _ -> if c == c' then t else mkCast (c', k, ty))
          (c', k, ty)
          rw
      | Prod (na, b, c) ->
        let rw = prep_node mutator.prod (na, b, c) in
        let b' = traverse env b in
        let c' = traverse (push_rel (LocalAssum (na, b')) env) c in
        step_node
          (fun _ -> if b == b' && c == c' then t else mkProd (na, b', c'))
          (na, b', c')
          rw
      | Lambda (na, ty, c) ->
        let rw = prep_node mutator.lambda (env, na, ty, c) in
        let ty' = traverse env ty in
        let c' = traverse (push_rel (LocalAssum (na, ty')) env) c in
        step_node
          (fun _ -> if ty == ty' && c == c' then t else mkLambda (na, ty', c'))
          (env, na, ty', c')
          rw
      | LetIn (na, b, ty, c) ->
        let rw = prep_node mutator.letin (na, b, ty, c) in
        let ty' = traverse env ty in
        let b' = traverse env b in
        let c' = traverse (push_rel (LocalDef (na, b', ty')) env) c in
        step_node
          ( fun _ ->
            if ty == ty' && b == b' && c == c' then t
            else mkLetIn (na, b', ty', c')
          )
          (na, b', ty', c')
          rw
      | App (h, a) ->
        let rw = prep_node mutator.app (env, h, a) in
        let h' = traverse env h in
        let a' = CArray.map_left (traverse env) a in
        step_node
          ( fun _ ->
            if h == h' && array_phys_eq a a' then t else mkApp (h', a')
          )
          (env, h', a')
          rw
      | Const (kn, u) -> f_leaf mutator.const (env, kn, u) t
      | Ind ind -> f_leaf mutator.ind ind t
      | Construct c -> f_leaf mutator.construct c t
      | Case (ci, u, pms, (p, r), iv, c, bl) ->
        let rw =
          prep_node mutator.case (env, (ci, u, pms, (p, r), iv, c, bl))
        in
        let c' = traverse env c in
        let pms' = CArray.map_left (traverse env) pms in
        let bl0, p0 = case_expand_contexts env (ci.ci_ind, u) pms (fst p) bl in
        let f_ctx (nas, c) ctx = nas, traverse (push_rel_context ctx env) c in
        let p' = f_ctx p p0 in
        let bl' = CArray.map2 f_ctx bl bl0 in
        step_node
          (fun _ ->
            if
              c == c'
              && array_phys_eq pms pms'
              && snd p == snd p'
              && Array.for_all2 (fun (_, x) (_, y) -> x == y) bl bl'
            then t
            else mkCase (ci, u, pms', (p', r), iv, c', bl')
          )
          (env, (ci, u, pms', (p', r), iv, c', bl'))
          rw
      | Fix (i, (nas, tl, bl)) ->
        let rw = prep_node mutator.fix (i, (nas, tl, bl)) in
        let env' = push_rec_types (nas, tl, bl) env in
        let tl', bl' = map_left2 (traverse env) (traverse env') tl bl in
        step_node
          ( fun _ ->
            if array_phys_eq tl tl' && array_phys_eq bl bl' then t
            else mkFix (i, (nas, tl', bl'))
          )
          (i, (nas, tl', bl'))
          rw
      | CoFix (i, (nas, tl, bl)) ->
        let rw = prep_node mutator.cofix (i, (nas, tl, bl)) in
        let env' = push_rec_types (nas, tl, bl) env in
        let tl', bl' = map_left2 (traverse env) (traverse env') tl bl in
        step_node
          ( fun _ ->
            if array_phys_eq tl tl' && array_phys_eq bl bl' then t
            else mkCoFix (i, (nas, tl', bl'))
          )
          (i, (nas, tl', bl'))
          rw
      | Proj (pn, r, c) ->
        let rw = prep_node mutator.proj (env, pn, r, c) in
        let c' = traverse env c in
        step_node
          (fun _ -> if c == c' then t else mkProj (pn, r, c'))
          (env, pn, r, c')
          rw
      | Int i -> f_leaf mutator.int i t
      | Float f -> f_leaf mutator.float f t
      | String s -> f_leaf mutator.string s t
      | Array (u, a, def, ty) ->
        let rw = prep_node mutator.array (u, a, def, ty) in
        let a' = CArray.map_left (traverse env) a in
        let def' = traverse env def in
        let ty' = traverse env ty in
        step_node
          ( fun _ ->
            if array_phys_eq a a' && def == def' && ty == ty' then t
            else mkArray (u, a', def', ty')
          )
          (u, a', def', ty')
          rw
    in
    let t = traverse env t in
    Locusops.check_used_occurrences count.occs;
    if count.atleastone then t else user_err (str "No occurence to rewrite.")
end

(* TODO HERE: rule reduction, check cclosure?
  Environ.lookup_rewrite_rules kn env -> rewrite_rule list
  check how they are applied in Reductionops.apply_rule
  (CClosure.match_elim is too complicated)

  write mutual recursive functions for PE PH PA?
*)
module TermReduction = struct
  open TermZipper
  type red_case = RIota | RZeta of int * int
  (* rewrite rule: constant.t + number ? *)

  (* TODO/LATER?
  let reduce_rel tz n =
    let rec aux n = function
    | [] -> None
    | (_, h) :: t ->
      match h with
      | CProd (Right (), _, _, _) -> if n > 0 then aux (n - 1) t else None
      | CLetIn (TRight, _, c, _, _) -> if n > 0 then aux (n - 1) t else Some c
      | CFix (Either.Right _, (_, (_, _, bds))) ->
        let k = n - Array.length bds in
        if k >= 0 then aux k t else Some bds.(n)
      | CCoFix (Either.Right _, (_, (_, _, bds))) ->
        let k = n - Array.length bds in
        if k >= 0 then aux k t else Some bds.(n)
      | CLambda (Right (), _, _, _) ->
        if n > 0 then aux (n - 1) t
        else ... (* TODO *)
      | CCase (*case_pos * case*) -> (* TODO *)
      | _ -> aux n t
    in
    aux n tz.ctx
    (* Option.bind (List.nth_opt tz.rel_ctx n)
      Context.Rel.Declaration.(function LocalDef (_, c, _) -> Some c | LocalAssum _ -> None)
    *)
  *)

  let reduce_helper tz =
    Option.map (fun (ctx, t) ->
      tz.cache <- [];
      tz.ctx <- ctx;
      t
    )

  let reduce_lambda tz t =
    let (*rec*) aux t = function
    | CApp (Either.Left (), _, args) :: ctx ->
      Some (ctx, beta_red t args)
    | _ -> None (* LATER: traverse letin and other stuff like it *)
    in reduce_helper tz (aux t tz.ctx)

  let reduce_app tz env evm head args =
    let r =
      match kind evm head with
      | Lambda (_, _, c) -> Some (beta_red c args)
      | Fix f -> Result.to_option (iota_fix_red env evm f args)
      | Const (c, u) -> (* TODO: rule reduction *)
        Option.bind (get_primitive env c)
          (fun op -> Result.to_option (delta_prim_red env evm (op, u) args))
      | Construct ((_, c), _) -> (
        match tz.ctx with
        | CCase (CMatchee, (ci, u, _, _, _, _, brs)) :: ctx ->
          tz.ctx <- ctx;
          Some (iota_match_red env ci u c brs args)
        | CProj (pn, _, _) :: ctx -> tz.ctx <- ctx; Some (proj_red pn args)
        | _ -> None
      )
      | CoFix cf -> (
        match tz.ctx with
        | (CCase _ | CProj _) :: _ -> Some (contract_cofix evm cf)
        | _ -> None
      )
      | _ -> None
    in if Option.has_some r then tz.cache <- []; r

  (*
  let rule_red env evm kn u tz =
    let open Declarations in
    let rec aux = function
    | [] -> None
    | {lhs_pat = (pu, elims); nvars; rhs} :: t ->
      let psubst = Partial_subst.make nvars in
      match UVars.Instance.pattern_match pu (EInstance.kind evm u) psubst with
      | None -> aux t
      | Some psubst ->
        ...
        let subst, qsubst, usubst = Partial_subst.to_arrays psubst in
        let usubst = UVars.Instance.of_array (qsubst, usubst) in
        ...
        return new headterm

    in aux (lookup_rewrite_rules kn env)
  *)

  let reduce_const tz env evm (kn, u) =
    let r =
      match (lookup_constant env evm kn).const_body with
      | Def x -> Some (subst_instance_constr u (of_constr x))
      | Primitive p -> (
        match tz.ctx with
        | CApp (Either.Left (), _, args) :: ctx -> (
          match delta_prim_red env evm (p, u) args with
          | Ok v -> tz.ctx <- ctx; Some v
          | Error _ -> None
        )
        | _ -> None
      )
      (* | Symbol b ->
        match rule_red env evm kn tz with
        | Some ... -> ...
        | None ->
          if b
          then ...
          else ...
      *)
      | Symbol b when b -> ((* TODO: rule reduction (remove 'when b') *)
        match tz.ctx with
        | CApp (Either.Right k, head, args) :: ctx -> (
          match kind evm head with
          | Fix ((reci, i), _ as f) when reci.(i) = k ->
            tz.ctx <- ctx; Some (mkApp (contract_fix evm f, args))
          | _ -> None
        )
        | _ -> None
      )
      | _ -> None
    in if Option.has_some r then tz.cache <- []; r

  let reduce_contruct tz env evm c =
    reduce_helper tz (
      match tz.ctx with
      | CCase (CMatchee, (ci, u, _, _, _, _, brs)) :: ctx ->
        Some (ctx, iota_match_red env ci u c brs [||])
      | CApp (Either.Left (), _, args) :: CCase (CMatchee, (ci, u, _, _, _, _, brs)) :: ctx ->
        Some (ctx, iota_match_red env ci u c brs args)
      | CApp (Either.Left (), _, args) :: CProj (pn, _, _) :: ctx ->
        Some (ctx, proj_red pn args)
      | CApp (Either.Right k, head, args) :: ctx -> (
        match kind evm head with
        | Fix ((reci, i), _ as f) when reci.(i) = k ->
          Some (ctx, mkApp (contract_fix evm f, args))
        | _ -> None
      )
      | _ -> None
    )

  let reduce_case tz env evm (ci, u, pms, p, iv, c, brs as case) rd =
    let r =
      match rd with
      | RIota -> Result.to_option (iota_match_head env evm case)
      | RZeta (brn, lbn) ->
        let ind, tyi = ci.ci_ind in
        let oib = (lookup_mind ind env).mind_packets.(tyi) in
        let bindings =
          CList.firstn
            (oib.mind_consnrealdecls.(brn))
            (fst oib.mind_nf_lc.(brn))
        in
        Result.to_option (
          zeta_match_step evm brn
            (bind_to_index lbn bindings)
            env case
        )
    in if Option.has_some r then tz.cache <- []; r

  let reduce_fix tz env evm f =
    match tz.ctx with
    | CApp (Either.Left (), _, args) :: ctx ->
      let r = iota_fix_red env evm f args in
      if Result.is_ok r
      then begin
        tz.ctx <- ctx;
        tz.cache <- []
      end;
      r
    | _ -> Error (str "fixpoint is not applied.")

  let reduce_cofix tz evm cf =
    match tz.ctx with
    | CApp (Either.Left (), _, _) :: CCase (CMatchee, _) :: _
    | CCase (CMatchee, _) :: _ ->
      tz.cache <- []; Some (contract_cofix evm cf)
    | _ -> None

  let _ =
    RIota,
    RZeta (0, 0),
    reduce_lambda,
    reduce_app,
    reduce_const,
    reduce_contruct,
    reduce_case,
    reduce_fix,
    reduce_cofix
end

let _ = TermReduction.RIota

(*
module TermVisitor = struct
  type ('r, 'c) control = Stop of 'r | Act of 'c | Up
  type ('m, 'r) action_kind = Down of 'm | Reduce of 'r
  type action =
  | ARel of red_rel
  | AVar
  | AEvar of (unit, unit) action_kind
  | ACast of (unit, unit) action_kind
  | AProd of (unit, unit) Either.t
  | ALambda of ((unit, unit) Either.t, unit) action_kind
  | ALetIn of (unit tern_pos, unit) action_kind
  | AApp of ((unit, int) Either.t, unit) action_kind
  | AConst of unit
  | AConstruct of unit
  | ACase of (case_pos, red_case) action_kind
  | AFix of ((int, int) Either.t, unit) action_kind
  | ACofix of ((int, int) Either.t, unit) action_kind
  | AProj of (unit, unit) action_kind
  | AArray of int tern_pos

  class type ['t] t = object
    method term: TermZipper.t -> constr -> ('t, action) control
    method evarc: TermZipper.t -> TermSListZipper.t -> constr -> ('t, unit tern_pos) control
  end

  (* TODO HERE: finish this maybe *)
  let visit env evm cb t =
    let tz = TermZipper.make t in
    let rec aux_term t =
      match cb#term tz t of
      | Stop v -> v, TermZipper.unzip tz t
      | Up -> (
        match TermZipper.move_up tz t with
        | Either.Left t -> aux_term t
        | Either.Right cz -> aux_evarc cz t
      )
      | Act a ->
        (* TODO: use reductions from TermReduction
        match a, kind t with
        | ARel r, Rel i -> (* TODO *)
        | AVar, Var id -> aux_term (delta_var_red env id)
        | AEvar a, Evar (ev, sl) -> (
          match a with
          | Move () ->
            tz.ctx <- (t, CEvar ev) :: tz.ctx;
            (* TODO *)
            aux_evarc (TermSListZipper.make sl)
          | Reduce () -> aux_term (Evd.existential_opt_value0 evm ev)
        )
        | ACast a, Cast (c, k, ct) -> (
          match a with
          | Move () -> tz.ctx <- (t, CCast c k ct) :: tz.ctx; aux_term c
          | Reduce () -> aux_term c
        )
        | AProd d, Prod (na, t, b) -> (* TODO *) 
        | ALambda a, Lambda (na, t, b) -> (
          match a with
          | Move
          | Reduce
        )
        | ALetIn a, LetIn (na, b, u, c) -> (
          match a with
          | Move
          | Reduce () -> aux_term (subst1 b c)
        )
        | AApp a, App (h, al) -> (
          match a with
          | Move
          | Reduce
        )
        | AConst r, Const sp ->
        | AConstruct r, Construct c ->
        | ACase a, Case (ci, u, pms, p, iv, b, bl) -> (
          match a with
          | Move
          | Reduce
        )
        | AFix a, Fix f -> (
          match a with
          | Move
          | Reduce () -> fix_red env f ...
        )
        | ACoFix a, CoFix cf -> (
          match a with
          | Move
          | Reduce () -> contract_cofix
        )
        | AProj a, Proj (p, r, b) -> (
          match a with
          | Move () -> aux_term b
          | Reduce () -> aux_term (proj_step)
        )
        | AArray d, Array (u, t, def, ty) ->
        | _ -> anomaly (str "Not an anomaly? rather a dev error? depends on the reduction fonction provided")
        *)
    and aux_evarc cz t =
      match cb#evarc tz cz t of
      | Stop v -> v, TermZipper.unzip_evarc tz cz t
      | Up -> aux_term (TermZipper.move_up_evarc tz cz t)
      | Act a ->
        let move d =
          match TermSListZipper.move cz t d with
          | Error _ -> anomaly (str "Forbidden zipper movement.")
          | Ok t -> aux_evarc cz t
        in
        match a with
        | TLeft () -> move (Either.Left ())
        | TRight -> move (Either.Right ())
        | TMiddle -> tz.ctx <- EvarC cz :: tz.ctx; aux_term t
    in aux_term t
end
*)


(* REDUCTION TACTICS *)

type 'e eta_kind =
| EBoth
| ELambda of Id.t option
| EPrim of 'e option

let match_binder b = function
| Name na -> Id.equal na b
| Anonymous -> false

let match_opt_binder na = function
| None -> true
| Some b -> match_binder b Context.(na.binder_name)

let cast_mutator = {
  TermMutator.idle_mutator with cast = Some {
    trigger = (fun _ -> true);
    rewrite = fun (c, _, _) -> Ok c
  }
}

let beta_mutator evm b = {
  TermMutator.idle_mutator with app =
    let rewrite (_, h, a) =
      let _, _, h = destLambda evm h in Ok (beta_red h a)
    in
    match b with
    | Some b ->
      Some {rewrite; trigger = fun (_, h, _) ->
        match kind evm h with
        | Lambda (na, _, _) -> match_binder b na.binder_name
        | _ -> false
      }
    | None -> Some {rewrite; trigger = fun (_, h, _) -> isLambda evm h}
}

let zeta_mutator b = {
  TermMutator.idle_mutator with letin =
    let rewrite (_, b, _, c) = Ok (subst1 b c) in
    match b with
    | Some b ->
      Some {rewrite;
        trigger = fun (na, _, _, _) -> match_binder b na.binder_name
      }
    | None -> Some {rewrite; trigger = fun (na, _, _, _) -> true}
}

let zeta_match_mutator evm ty brn n = {
  TermMutator.idle_mutator with case = Some {
    trigger = (fun (env, (ci, _, _, _, _, _, _)) -> QInd.equal env ty ci.ci_ind);
    rewrite = fun (env, case) -> zeta_match_step evm brn n env case
  }
}

let delta_mutator evm e = let open Evaluable in {
  TermMutator.idle_mutator with
  var = (
    let rewrite (env, id) = delta_var_red env id in
    match e with
    | Some (EvalVarRef i) ->
      Some {rewrite; trigger = fun (_, id) -> Id.equal id i}
    | None -> Some {rewrite; trigger = fun _ -> true}
    | _ -> None
  );
  const = (
    let rewrite (env, c, u) =
      let the_const () = str "constant " ++ Constant.print c in
      Result.map_error
        ( function
          | NoBody -> the_const () ++ str " has no definition."
          | Opaque -> the_const () ++ str " is opaque."
          | IsPrimitive _ -> assert false
          | HasRules _ ->
            the_const () ++ str " is a symbol with custom rewrite rules."
        )
        (delta_const_red env evm (c, u))
    in
    match e with
    | Some (EvalConstRef cr) ->
      Some {rewrite; trigger = fun (env, c, _) ->
        QConstant.equal env cr c && not (is_primitive env c)
      }
    | None ->
      Some {rewrite; trigger = fun (env, c, _) -> not (is_primitive env c)}
    | _ -> None
  );
  proj = (
    let rewrite (_, pn, r, c) = Ok (mkProj (Projection.unfold pn, r, c)) in
    match e with
    | Some (EvalProjectionRef p) ->
      Some {rewrite; trigger = fun (env, pn, _, _) ->
        QProjection.Repr.equal env p (Projection.repr pn)
        && not (Projection.unfolded pn)
      }
    | None ->
      Some {rewrite;
        trigger = fun (_, pn, _, _) -> not (Projection.unfolded pn)
      }
    | _ -> None
  );
  app =
    let rewrite (env, h, a) =
      let c, u = destConst evm h in
      let p = Option.get (get_primitive env c) in
      Result.map_error
        (fun e -> str "primitive " ++ Constant.print c ++ spc () ++ e)
        (delta_prim_red env evm (p, u) a)
    in
    match e with
    | Some (EvalConstRef cr) ->
      Some {rewrite; trigger = fun (env, h, _) ->
        match kind evm h with
        | Const (c, _) -> QConstant.equal env cr c && is_primitive env c
        | _ -> false
      }
    | None ->
      Some {rewrite; trigger = fun (env, h, _) ->
        match kind evm h with
        | Const (c, _) -> is_primitive env c
        | _ -> false
      }
    | _ -> None
}

let is_primitive_record env ind =
  match (snd (lookup_mind_specif env ind)).mind_record with
  | PrimRecord _ -> true
  | _ -> false

let eta_mutator evm ek = {
  TermMutator.idle_mutator with
  lambda = (
    let rewrite (env, na, t, c) = eta_lambda_red env evm t c in
    match ek with
    | ELambda (Some b) ->
      Some {rewrite; trigger = fun (_, na, _, c) ->
        match kind evm c with
        | App (_, a) ->
          isRelN evm 1 (CArray.last a) && match_binder b na.binder_name
        | _ -> false
      }
    | EPrim _ -> None
    | _ ->
      Some {rewrite; trigger = fun (_, na, _, c) ->
        match kind evm c with
        | App (_, a) -> isRelN evm 1 (CArray.last a)
        | _ -> false
      }
  );
  app =
    let rewrite (env, h, a) =
      let (ind, _), _ = destConstruct evm h in
      eta_prim_red env evm ind a
    in
    match ek with
    | EPrim (Some (ind, None)) ->
      Some {rewrite; trigger = fun (env, h, _) ->
        match kind evm h with
        | Construct ((ind', _), _) ->
          QInd.equal env ind ind' && is_primitive_record env ind'
        | _ -> false
      }
    | EPrim (Some (ind, Some n)) ->
        Some {rewrite; trigger = fun (env, h, _) ->
          match kind evm h with
          | Construct ((ind', n'), _) ->
            QInd.equal env ind ind' && n = n' && is_primitive_record env ind'
          | _ -> false
      }
    | ELambda _ -> None
    | _ ->
      Some {rewrite; trigger = fun (env, h, _) ->
        match kind evm h with
        | Construct ((ind, _), _) -> is_primitive_record env ind
        | _ -> false
      }
}

let fix_prime_mutator evm b = {
  TermMutator.idle_mutator with fix = Some (
    let rewrite f = Ok (contract_fix evm f) in
    match b with
    | Some b ->
      { rewrite;
        trigger = fun ((_, i), (nas, _, _)) ->
          match_binder b nas.(i).binder_name
      }
    | None -> {rewrite; trigger = fun _ -> true}
  )
}

let fix_mutator evm b = {
  TermMutator.idle_mutator with app = Some (
    let rewrite (env, h, a) = iota_fix_red env evm (destFix evm h) a in
    match b with
    | Some b ->
      { rewrite; trigger = fun (_, h, a) ->
        match kind evm h with
        | Fix ((reci, i), (nas, _, _)) ->
          match_binder b nas.(i).binder_name && reci.(i) < Array.length a
        | _ -> false
      }
    | None ->
      { rewrite; trigger = fun (_, h, a) ->
        match kind evm h with
        | Fix ((reci, i), _) -> reci.(i) < Array.length a
        | _ -> false
      }
  )
}

let cofix_prime_mutator evm b = {
  TermMutator.idle_mutator with cofix = Some (
    let rewrite cf = Ok (contract_cofix evm cf) in
    match b with
    | Some b ->
      { rewrite;
        trigger = fun (i, (nas, _, _)) -> match_binder b nas.(i).binder_name
      }
    | None -> {rewrite; trigger = fun _ -> true}
  )
}

let cofix_mutator evm b =
  let extract_cofix c =
    match kind evm c with
    | CoFix cf -> Some (cf, [||])
    | App (h, a) -> (
      match kind evm h with
      | CoFix cf -> Some (cf, a)
      | _ -> None
    )
    | _ -> None
  in
  { TermMutator.idle_mutator with
    case = Some (
      let rewrite (_, (ci, u, pms, bi, iv, c, bl)) =
        let cf, a = Option.get (extract_cofix c) in
        Ok (mkCase (ci, u, pms, bi, iv, mkApp (contract_cofix evm cf, a), bl))
      in
      match b with
      | Some b ->
        { rewrite; trigger = fun (_, (_, _, _, _, _, c, _)) ->
          match extract_cofix c with
          | Some ((i, (nas, _, _)), _) -> match_binder b nas.(i).binder_name
          | None -> false
        }
      | None ->
        { rewrite; trigger = fun (_, (_, _, _, _, _, c, _)) ->
          Option.has_some (extract_cofix c)
        }
    );
    proj = Some (
      let rewrite (_, pn, r, c) =
        let cf, a = Option.get (extract_cofix c) in
        Ok (mkProj (pn, r, mkApp (contract_cofix evm cf, a)))
      in
      match b with
      | Some b ->
        { rewrite; trigger = fun (_, pn, _, c) ->
          match extract_cofix c with
          | Some ((i, (nas, _, _)), _) ->
            Projection.unfolded pn && match_binder b nas.(i).binder_name
          | None -> false
        }
      | None ->
        { rewrite; trigger = fun (_, pn, _, c) ->
          Projection.unfolded pn && Option.has_some (extract_cofix c)
        }
    )
  }

let match_mutator evm tyc =
  let extract_construct t =
    match kind evm t with
    | Construct c -> Some (c, [||])
    | App (h, a) -> (
      match kind evm h with
      | Construct c -> Some (c, a)
      | _ -> None
    )
    | _ -> None
  in
  { TermMutator.idle_mutator with
    case = Some (
      let rewrite (env, (ci, u, pms, _, iv, c, brs)) =
        match extract_construct c with
        | Some (((_, c), _), a) -> Ok (iota_match_red env ci u c brs a)
        | None ->
          Result.map_error
            (fun e -> str "scrutinee is not an applied constructor and " ++ e)
            (iota_uip_red env evm ci u pms iv brs)
      in
      match tyc with
      | Some (ind, Some n) ->
        { rewrite; trigger = fun (env, (_, _, _, _, _, c, _)) ->
          match extract_construct c with
          | Some (((ind', c), _), _) -> QInd.equal env ind ind' && n == c
          | None -> false
        }
      | Some (ind, None) ->
        { rewrite;
          trigger = fun (env, (ci, _, _, _, _, _, _)) -> QInd.equal env ind ci.ci_ind
        }
      | None -> {rewrite; trigger = fun _ -> true}
    );
    proj = Some (
      let rewrite (env, pn, _, c) =
        match extract_construct c with
        | Some (_, a) -> Ok (proj_red pn a)
        | None -> Error (str "scrutinee is not an applied constructor.")
      in
      match tyc with
      | Some (ind, _) ->
        { rewrite; trigger = fun (env, pn, _, _) ->
          Projection.unfolded pn && QInd.equal env ind (Projection.inductive pn)
        }
      | None -> {rewrite; trigger = fun (_, pn, _, _) -> Projection.unfolded pn}
    )
  }

let root_step env evm c =
  match kind evm c with
  | Var id ->
    Result.map_error (fun e -> str "Failed delta reduction : " ++ e)
      (delta_var_red env id)
  | Cast (ct, _, _) -> Ok ct
  | LetIn (na, b, u, c) -> Ok (subst1 b c)
  | App (head, args) -> app_head env evm head args
  | Const sp ->
    Result.map_error (fun e -> str "Failed delta reduction: " ++ e)
      (const_head env evm sp)
  | Case (ci, u, pms, bi, iv, c, brs) ->
    first_success (str "Failed reduction of match,") [
      (fun _ -> iota_match_head env evm (ci, u, pms, bi, iv, c, brs));
      ( fun _ ->
        Result.map_error (fun e -> str "SProp elimination: " ++ e)
          (iota_uip_red env evm ci u pms iv brs)
      );
      fun _ ->
        Result.map (fun brs -> mkCase (ci, u, pms, bi, iv, c, brs))
          (zeta_match_head env evm ci u pms brs)
    ]
  | Proj (pn, r, c) -> proj_step evm pn r c
  | Lambda (_, t, c) ->
    Result.map_error (fun e -> str "Failed eta reduction : " ++ e)
      (eta_lambda_red env evm t c)
  | Rel _ | Meta _ | Evar _ | Sort _ | Prod _
  | Ind _ | Construct _ | Fix _ | CoFix _ | Int _
  | Float _ | String _ | Array _ -> Error (str "No reduction applicable.")

let head_step evm _ec (* TODO *) env c =
  let rec aux c =
    match kind evm c with
    | Var id -> Result.to_option (delta_var_red env id)
    | Cast (c, k, t) ->
      Some (
        match aux c with
        | Some c -> mkCast (c, k, t)
        | None -> c
      )
    | LetIn (na, b, u, c) -> Some (subst1 b c)
    | App (head, args) ->
      opt_or
        ( match kind evm head with
          | Fix ((reci, i), f) ->
            let i = reci.(i) in
            if i < Array.length args
            then
              Option.map (fun c -> mkApp (head, array_with args i c))
                (aux args.(i))
            else None
          | _ -> Option.map (fun h -> mkApp (h, args)) (aux head)
        )
        (fun _ -> Result.to_option (app_head env evm head args))
    | Const sp -> Result.to_option (const_head env evm sp)
    | Case (ci, u, pms, bi, iv, c, brs) ->
      first_step [
        (fun _ -> Result.to_option (iota_uip_red env evm ci u pms iv brs));
        ( fun _ ->
          Option.map (fun c -> mkCase (ci, u, pms, bi, iv, c, brs)) (aux c)
        );
        fun _ ->
          Result.to_option
            (iota_match_head env evm (ci, u, pms, bi, iv, c, brs))
      ]
    | Proj (pn, r, c) ->
      if Projection.unfolded pn
      then
        or_step (fun c -> mkProj (pn, r, c)) (aux c)
          (fun _ -> Result.to_option (proj_head evm pn r c))
      else Some (mkProj (Projection.unfold pn, r, c))
    | Rel _ | Meta _ | Evar _ | Sort _ | Prod _ | Lambda _
    | Ind _ | Construct _ | Fix _ | CoFix _
    | Int _ | Float _ | String _ | Array _ -> None
  in force "Term at head is not reducible." (aux c)

let cbv_reduce env evm =
  let rec aux c =
    match kind evm c with
    | Var id -> Result.to_option (delta_var_red env id)
    | Cast (ct, k, ck) ->
      (* Cast might be useful for performance until term below is fully reduced
        but cast stripping is not considered progress :(
      *)
      Some (match aux ct with Some ct -> mkCast (ct, k, ck) | None -> ct)
    | Prod (na, t, u) ->
      or_step (fun t -> mkProd (na, t, u)) (aux t)
        (fun _ -> Option.map (fun u -> mkProd (na, t, u)) (aux u))
    | LetIn (na, b, u, c) ->
      Some (
        match aux b with
        | Some b -> mkLetIn (na, b, u, c)
        | None -> subst1 b c
      )
    | App (head, args) ->
      first_step [
        (fun _ -> Option.map (fun head -> mkApp (head, args)) (aux head));
        ( fun _ ->
          Option.map (fun hd -> mkApp (head, array_with args 0 hd))
            (aux args.(0))
        );
        (fun _ -> Result.to_option (app_head env evm head args));
        fun _ ->
          Option.map (fun args -> mkApp (head, args)) (array_step_n aux args 1)
      ]
    | Const sp -> Result.to_option (const_head env evm sp)
    | Case (ci, u, pms, bi, iv, c, brs) ->
      first_step [
        ( fun _ ->
          Option.map (fun c -> mkCase (ci, u, pms, bi, iv, c, brs)) (aux c)
        );
        ( fun _ ->
          Result.to_option
            (iota_match_head env evm (ci, u, pms, bi, iv, c, brs))
        );
        ( fun _ ->
          Option.map (fun pms -> mkCase (ci, u, pms, bi, iv, c, brs))
            (array_step aux pms)
        );
        fun _ -> Result.to_option (iota_uip_red env evm ci u pms iv brs)
      ]
    | Proj (pn, r, c) -> Result.to_option (proj_step evm pn r c)
    | Rel _ | Meta _ | Evar _ | Sort _ | Lambda _
    | Ind _ | Construct _ | Fix _ | CoFix _
    | Int _ | Float _ | String _ | Array _ -> None
  in aux

let cbv_normalize evm =
  let rec aux env c =
    let reduce_or_normalize f c =
      opt_or (cbv_reduce env evm c) (fun _ -> aux (f env) c)
    in
    match kind evm c with
    | Evar (evi, ev) ->
      Option.map (fun ev -> mkEvar (evi, ev))
        (slist_step (reduce_or_normalize id) ev)
    | Prod (na, t, u) ->
      or_step (fun t -> mkProd (na, t, u)) (aux env t) (fun _ ->
        Option.map (fun u -> mkProd (na, t, u))
          (aux (push_rel (LocalAssum (na, t)) env) u)
      )
    | Lambda (na, t, c) ->
      first_step [
        ( fun _ ->
          Option.map (fun c -> mkLambda (na, t, c))
          (reduce_or_normalize (push_rel (LocalAssum (na, t))) c)
        );
        ( fun _ ->
          Option.map (fun t -> mkLambda (na, t, c)) (reduce_or_normalize id t)
        );
        fun _ -> Result.to_option (eta_lambda_red env evm t c)
      ]
    | App (head, args) ->
      or_step (fun head -> mkApp (head, args)) (aux env head) (fun _ ->
        Option.map (fun args -> mkApp (head, args)) (array_step (aux env) args)
      )
    | Case (ci, u, pms, bi, iv, c, brs) ->
      first_step [
        ( fun _ ->
          Option.map (fun c -> mkCase (ci, u, pms, bi, iv, c, brs)) (aux env c)
        );
        ( fun _ ->
          Option.map (fun pms -> mkCase (ci, u, pms, bi, iv, c, brs))
            (array_step (aux env) pms)
        );
        ( fun _ ->
          match zeta_match_head env evm ci u pms brs with
          | Ok brs -> Some (mkCase (ci, u, pms, bi, iv, c, brs))
          | Error _ -> None
        );
        fun _ ->
          let mib, mip = lookup_mind_specif env ci.ci_ind in
          let ps = case_parameter_context_specif mib u pms in
          or_step (fun brs -> mkCase (ci, u, pms, bi, iv, c, brs))
            ( for_step
              ( fun i ->
                let nas, br = brs.(i) in
                let ctx = case_branch_context_specif mip ps u nas i in
                Option.map (fun br -> array_with brs i (nas, br))
                  (reduce_or_normalize (push_rel_context ctx) br)
              )
              (Array.length brs)
              0
            )
            ( fun _ ->
              let (nas, p), rp = bi in
              Option.map
                (fun p -> mkCase (ci, u, pms, ((nas, p), rp), iv, c, brs))
                ( reduce_or_normalize
                  ( push_rel_context
                    (case_arity_context_specif mip ps (ci.ci_ind, u) nas)
                  )
                  p
                )
            )
      ]
    | Fix (si, (nas, tys, bds)) ->
      or_step (fun bds -> mkFix (si, (nas, tys, bds)))
        (array_step (reduce_or_normalize (push_rec_types (nas, tys, bds))) bds)
        ( fun _ ->
          Option.map (fun tys -> mkFix (si, (nas, tys, bds)))
            (array_step (reduce_or_normalize id) tys)
        )
    | CoFix (ri, (nas, tys, bds)) ->
      or_step (fun bds -> mkCoFix (ri, (nas, tys, bds)))
        (array_step (reduce_or_normalize (push_rec_types (nas, tys, bds))) bds)
        ( fun _ ->
          Option.map (fun tys -> mkCoFix (ri, (nas, tys, bds)))
            (array_step (reduce_or_normalize id) tys)
        )
    | Proj (pn, r, c) -> Option.map (fun c -> mkProj (pn, r, c)) (aux env c)
    | Array (u, ts, def, ty) ->
      first_step [
        ( fun _ ->
          Option.map (fun def -> mkArray (u, ts, def, ty))
            (reduce_or_normalize id def)
        );
        ( fun _ ->
          Option.map (fun ts -> mkArray (u, ts, def, ty))
            (array_step (reduce_or_normalize id) ts)
        );
        fun _ ->
          Option.map (fun ty -> mkArray (u, ts, def, ty))
            (reduce_or_normalize id ty)
      ]
    | Var _ | Rel _ | Meta _ | Sort _
    | Cast _ | Const _ | Ind _ | Construct _
    | Int _ | Float _ | String _ -> None
    | LetIn _ -> assert false
  in aux

let cbv_step evm ec env c =
  force "Term is fully reduced."
    (opt_or (cbv_reduce env evm c) (fun _ -> cbv_normalize evm env c))

let global_step evm ec env c =
  let rec aux env c =
    match kind evm c with
    | Var id -> Result.to_option (delta_var_red env id)
    | Evar (evi, ev) ->
      Option.map (fun ev -> mkEvar (evi, ev)) (slist_step (aux env) ev)
    | Cast (ct, k, ck) ->
      (* Cast might be useful for performance until term below is fully reduced
        but cast stripping is not considered progress :(
      *)
      Some (match aux env ct with Some ct -> mkCast (ct, k, ck) | None -> ct)
    | Prod (na, t, u) ->
      or_step (fun t -> mkProd (na, t, u)) (aux env t) (fun _ ->
        Option.map (fun u -> mkProd (na, t, u))
          (aux (push_rel (LocalAssum (na, t)) env) u)
      )
    | Lambda (na, t, c) ->
      first_step [
        ( fun _ ->
          Option.map (fun c -> mkLambda (na, t, c))
            (aux (push_rel (LocalAssum (na, t)) env) c)
        );
        (fun _ -> Option.map (fun t -> mkLambda (na, t, c)) (aux env t));
        fun _ -> Result.to_option (eta_lambda_red env evm t c)
      ]
    | LetIn (na, b, u, c) ->
      Some (
        match aux env b with
        | Some b -> mkLetIn (na, b, u, c)
        | None ->
          match aux (push_rel (LocalDef (na, b, u)) env) c with
          | Some c -> mkLetIn (na, b, u, c)
          | None -> subst1 b c
      )
    | App (head, args) ->
      first_step [
        (fun _ -> Option.map (fun head -> mkApp (head, args)) (aux env head));
        ( fun _ ->
          Option.map (fun hd -> mkApp (head, array_with args 0 hd))
            (aux env args.(0))
        );
        (fun _ -> Result.to_option (app_head env evm head args));
        fun _ ->
          Option.map (fun args -> mkApp (head, args))
            (array_step_n (aux env) args 1)
      ]
    | Const sp -> Result.to_option (const_head env evm sp)
    | Case (ci, u, pms, bi, iv, c, brs) ->
      first_step [
        ( fun _ ->
          Option.map (fun c -> mkCase (ci, u, pms, bi, iv, c, brs)) (aux env c)
        );
        ( fun _ ->
          Result.to_option
            (iota_match_head env evm (ci, u, pms, bi, iv, c, brs))
        );
        ( fun _ ->
          Option.map (fun pms -> mkCase (ci, u, pms, bi, iv, c, brs))
            (array_step (aux env) pms)
        );
        fun _ ->
          let mib, mip = lookup_mind_specif env ci.ci_ind in
          let ps = case_parameter_context_specif mib u pms in
          first_step [
            ( fun _ ->
              match iv with
              | CaseInvert {indices} ->
                Result.to_option
                  (iota_uip_specif env evm (mib, mip) ps indices brs)
              | _ -> None
            );
            ( fun _ ->
              match zeta_match_head env evm ci u pms brs with
              | Ok brs -> Some (mkCase (ci, u, pms, bi, iv, c, brs))
              | Error _ -> None
            );
            ( fun _ ->
              Option.map (fun brs -> mkCase (ci, u, pms, bi, iv, c, brs))
                ( for_step
                  ( fun i ->
                    let nas, br = brs.(i) in
                    let ctx = case_branch_context_specif mip ps u nas i in
                    Option.map (fun br -> array_with brs i (nas, br))
                      (aux (push_rel_context ctx env) br)
                  )
                  (Array.length brs)
                  0
                )
            );
            fun _ ->
              let (nas, p), rp = bi in
              Option.map
                (fun p -> mkCase (ci, u, pms, ((nas, p), rp), iv, c, brs))
                ( aux
                  ( push_rel_context
                    (case_arity_context_specif mip ps (ci.ci_ind, u) nas)
                    env
                  )
                  p
                )
          ]
      ]
    | Fix (si, (nas, tys, bds)) ->
      or_step (fun bds -> mkFix (si, (nas, tys, bds)))
        (array_step (aux (push_rec_types (nas, tys, bds) env)) bds)
        ( fun _ ->
          Option.map (fun tys -> mkFix (si, (nas, tys, bds)))
            (array_step (aux env) tys)
        )
    | CoFix (ri, (nas, tys, bds)) ->
      or_step (fun bds -> mkCoFix (ri, (nas, tys, bds)))
        (array_step (aux (push_rec_types (nas, tys, bds) env)) bds)
        ( fun _ ->
          Option.map (fun tys -> mkCoFix (ri, (nas, tys, bds)))
            (array_step (aux env) tys)
        )
    | Proj (pn, r, c) ->
      or_step (fun c -> mkProj (pn, r, c)) (aux env c)
        (fun _ -> Result.to_option (proj_step evm pn r c))
    | Array (u, ts, def, ty) ->
      first_step [
        ( fun _ ->
          Option.map (fun def -> mkArray (u, ts, def, ty)) (aux env def)
        );
        ( fun _ ->
          Option.map (fun t -> mkArray (u, ts, def, ty))
            (array_step (aux env) ts)
        );
        fun _ -> Option.map (fun ty -> mkArray (u, ts, def, ty)) (aux env ty)
      ]
    | Rel _ | Meta _ | Sort _ | Ind _ | Construct _
    | Int _ | Float _ | String _ -> None
  in force "Term is fully reduced." (aux env c)

type 'c end_condition =
| ECNat of int
| ECLocal of 'c
| ECGlobal of 'c

type ('occ, 'endc, 'tycons, 'zeta, 'delta) reduction =
(*| SRRule (* Rewrite rules *)*)
| Cast of 'occ Locus.occurrences_gen (* Cast removal *)
| Beta of Id.t option * 'occ Locus.occurrences_gen
(* Beta: applied lambda to substitution *)
| Zeta of Id.t option * 'occ Locus.occurrences_gen
(* Zeta: letin to substitution *)
| ZetaMatch of 'zeta * 'occ Locus.occurrences_gen
(* Zeta-match: match-letin to substitution *)
| Delta of 'delta option * 'occ Locus.occurrences_gen
(* Delta: name resolution (including application of primitives) *)
| Eta of 'tycons eta_kind * 'occ Locus.occurrences_gen
(* Eta:
    - lambda over application on the only occurence of the variable
    - constructor on respective primitive projections
*)
| Evar
(* Evar: evar resolution + context substitution, not sure about this one *)
| IotaFix of Id.t option * 'occ Locus.occurrences_gen
(* Iota-fix: push fixpoint inward when allowed to *)
| IotaFixPrime of Id.t option * 'occ Locus.occurrences_gen
(* Iota-fix-prime: push fixpoint inward, maybe unfold and refold too? *)
| IotaCofix of Id.t option * 'occ Locus.occurrences_gen
(* Iota-cofix: match or project a cofix *)
| IotaCofixPrime of Id.t option * 'occ Locus.occurrences_gen
(* Iota-cofix-prime: push cofix inward, maybe unfold and refold too? *)
| IotaMatch of 'tycons option * 'occ Locus.occurrences_gen
(* Iota-match: match or project on a constructor + inversion in SProp *)
| Root (* Any reduction applicable at the root of the whole term *)
| Head of 'endc end_condition (* Any reduction at head *)
| Cbv of 'endc end_condition (* Next reduction step of a call-by-value strategy *)
| Cbn of 'endc end_condition (* Next reduction step of a call-by-name strategy *)
| Lazy of 'endc end_condition (* Next reduction step of a call-by-need / lazy strategy *)

let map_end_condition f = function
| ECNat n -> ECNat n
| ECLocal x -> ECLocal (f x)
| ECGlobal x -> ECGlobal (f x)

let map_eta_kind f = function
| EPrim x -> EPrim (Option.map f x)
| EBoth | ELambda _ as x -> x

let map_reduction focc fend ftyc fz fd = function
| Cast occ -> Cast (focc occ)
| Beta (b, occ) -> Beta (b, focc occ)
| Zeta (b, occ) -> Zeta (b, focc occ)
| ZetaMatch (z, occ) -> ZetaMatch (fz z, focc occ)
| Delta (d, occ) -> Delta (Option.map fd d, focc occ)
| Eta (tyc, occ) -> Eta (map_eta_kind ftyc tyc, focc occ)
| IotaFix (b, occ) -> IotaFix (b, focc occ)
| IotaFixPrime (b, occ) -> IotaFixPrime (b, focc occ)
| IotaCofix (b, occ) -> IotaCofix (b, focc occ)
| IotaCofixPrime (b, occ) -> IotaCofixPrime (b, focc occ)
| IotaMatch (tyc, occ) -> IotaMatch (Option.map ftyc tyc, focc occ)
| Head e -> Head (map_end_condition fend e)
| Cbv e -> Cbv (map_end_condition fend e)
| Cbn e -> Cbn (map_end_condition fend e)
| Lazy e -> Lazy (map_end_condition fend e)
| Evar | Root as s -> s

let pr_tycons env (ind, opn) =
  Printer.pr_inductive env ind ++ pr_opt int opn

let pr_zeta_raw (sg, x) =
  let open Pputils in
  pr_or_by_notation Libnames.pr_qualid sg ++ pr_opt (pr_or_var int) x

let pr_zeta_glob env (gr, x) =
  Termops.pr_global_env env gr ++ pr_opt (Pputils.pr_or_var int) x

let pr_zeta env (ind, n, m) = (* TODO REDO *)
  let rec index_to_bind n m = function
  | LocalDef (na, _, _) :: t ->
    if m = 0 then na, n else index_to_bind (n + 1) (m - 1) t
  | LocalAssum _ :: t when m > 0 -> index_to_bind n (m - 1) t
  | _ -> anomaly (str "Invalid zeta_match index.")
  in
  let _, oib = lookup_mind_specif env ind in
  let na, m = index_to_bind 0 m (fst oib.mind_nf_lc.(n)) in
  if oib.mind_record = NotRecord
  then Id.print oib.mind_consnames.(n) ++ spc () ++ int m
  else
    match na.binder_name with
    | Name id -> Id.print id
    | Anonymous -> Printer.pr_inductive env ind ++ spc () ++ int m

let pr_end_condition pr = function
| ECNat n -> pr_arg int n
| ECLocal x -> pr_arg str "until_focused" ++ pr_arg pr x
| ECGlobal x -> pr_arg str "until_global" ++ pr_arg pr x

let pr_eta_kind pr = function
| EBoth -> mt ()
| EPrim x -> pr_arg str "prim" ++ pr_opt pr x
| ELambda s -> pr_arg str "lambda" ++ pr_opt Id.print s

let pr_reduction pr_occs pr_closure pr_tycons pr_zeta pr_delta = function
| Cast occ -> str "cast" ++ pr_occs occ
| Beta (b, occ) -> str "beta" ++ pr_opt Id.print b ++ pr_occs occ
| Zeta (b, occ) -> str "zeta" ++ pr_opt Id.print b ++ pr_occs occ
| ZetaMatch (z, occ) -> str "zeta_match" ++ pr_arg pr_zeta z ++ pr_occs occ
| Delta (t, occ) -> str "delta" ++ pr_opt pr_delta t ++ pr_occs occ
| Eta (tyc, occ) -> str "eta" ++ pr_eta_kind pr_tycons tyc ++ pr_occs occ
| Evar -> str "evar"
| IotaFix (b, occ) -> str "iota_fix" ++ pr_opt Id.print b ++ pr_occs occ
| IotaFixPrime (b, occ) -> str "iota_fix'" ++ pr_opt Id.print b ++ pr_occs occ
| IotaCofix (b, occ) -> str "iota_cofix" ++ pr_opt Id.print b ++ pr_occs occ
| IotaCofixPrime (b, occ) -> str "iota_cofix'" ++ pr_opt Id.print b ++ pr_occs occ
| IotaMatch (tyc, occ) -> str "iota_match" ++ pr_opt pr_tycons tyc ++ pr_occs occ
| Root -> str "root"
| Head e -> str "head" ++ pr_end_condition pr_closure e
| Cbv e -> str "cbv" ++ pr_end_condition pr_closure e
| Cbn e -> str "cbn" ++ pr_end_condition pr_closure e
| Lazy e -> str "lazy" ++ pr_end_condition pr_closure e

let interp_tycons env gr =
  let open GlobRef in
  let fail () = user_err (Termops.pr_global_env env gr ++ str " does not describe a type, constructor nor projection.") in
  match gr with
  | ConstRef c -> (
    try
      let open Structures in
      let open Structure in
      (Structure.find_from_projection env c).name, Some 1
    with Not_found -> fail ()
  )
  | IndRef ind -> ind, None
  | ConstructRef (ind, n) -> ind, Some n
  | _ -> fail ()

let interp_zeta env (gr, x) =
  let zmargs =
    let open GlobRef in
    match gr, x with
    | ConstRef _, Some _ -> user_err (str "Too many arguments to zeta_match.")
    | ConstRef c, None -> (
      try
        let open Structures in
        let open Structure in
        let s = Structure.find_from_projection env c in
        let rec count_binds n = function
        | {proj_body = Some c'; proj_true = false; _} :: _ when QConstant.equal env c c' -> Some n
        | {proj_true = pt; _} :: l -> count_binds (if pt then n else n + 1) l
        | _ -> None
        in
        match count_binds 1 s.projections with
        | None -> user_err (str "Projection has no definition to delta reduce.")
        | Some n -> Some (s.name, Some 1, Some (Locus.ArgArg n))
      with Not_found -> None
    )
    | IndRef ind, x -> Some (ind, None, x)
    | ConstructRef (ind, n), x -> Some (ind, Some n, x)
    | _ -> None
  in
  ( match zmargs with
    | None -> user_err (str "Argument of zeta_match is neither a type, constructor, nor projection.")
    | Some ((ind, tyi), x, y) ->
      let oib = (lookup_mind ind env).mind_packets.(tyi) in
      let nbrs = Array.length oib.mind_nf_lc in
      let n =
        match x with
        | Some n -> n - 1
        | None ->
          if nbrs != 1 then user_err (str "Use of type as argument for zeta_match is only allowed for types with a single constructor.");
          0
      in
      if n >= nbrs then user_err (str "Invalid branch for zeta_match.");
      let rec no_binding n = function
      | [] -> ()
      | LocalAssum _ :: t -> no_binding n t
      | LocalDef (na, _, _) :: t ->
        if match_opt_binder na n
        then user_err (str "Non unique let binding for zeta_match.")
        else no_binding n t
      in
      let rec single_binding n k = function
      | [] -> user_err (str "No let binding for zeta_match.")
      | LocalAssum _ :: t -> single_binding n (k + 1) t
      | LocalDef (na, _, _) :: t ->
        if match_opt_binder na n then (no_binding n t; k)
        else single_binding n (k + 1) t
      in
      let m =
        let bindings = CList.firstn (oib.mind_consnrealdecls.(n)) (fst oib.mind_nf_lc.(n)) in
        match y with
        | Some (Locus.ArgArg m) -> bind_to_index m bindings
        | Some (Locus.ArgVar m) -> single_binding (Some m.v) 0 bindings
        | None -> single_binding None 0 bindings
      in
      (ind, tyi), n, m
  )

let step red env evm c =
  let f =
    match red with
    | Cast occ -> TermMutator.mutate evm occ cast_mutator
    | Beta (b, occ) -> TermMutator.mutate evm occ (beta_mutator evm b)
    | Zeta (b, occ) -> TermMutator.mutate evm occ (zeta_mutator b)
    | ZetaMatch ((ind, n, m), occ) ->
      TermMutator.mutate evm occ (zeta_match_mutator evm ind n m)
    | Delta (t, occ) -> TermMutator.mutate evm occ (delta_mutator evm t)
    | Eta (ek, occ) -> TermMutator.mutate evm occ (eta_mutator evm ek)
    | Evar -> fun _ -> nf_evar evm
    | IotaFix (b, occ) -> TermMutator.mutate evm occ (fix_mutator evm b)
    | IotaFixPrime (b, occ) -> TermMutator.mutate evm occ (fix_prime_mutator evm b)
    | IotaCofix (b, occ) -> TermMutator.mutate evm occ (cofix_mutator evm b)
    | IotaCofixPrime (b, occ) -> TermMutator.mutate evm occ (cofix_prime_mutator evm b)
    | IotaMatch (tyc, occ) -> TermMutator.mutate evm occ (match_mutator evm tyc)
    | Root ->
      ( fun env t ->
        match root_step env evm t with
        | Ok t -> t
        | Error e -> user_err (str "Term is not reducible at root: " ++ e)
      )
    | Head ec -> head_step evm ec (* TODO *)
    | Cbv ec -> cbv_step evm ec
    | Cbn ec -> global_step evm ec (* LATER *)
    | Lazy ec -> global_step evm ec (* LATER *)
  in
  evm, f env c
