(* Type and term parameters *)
type name = string

(* The various ways type checking can fail *)
type tyck_error =
  | Ambiguous     (* Unable to infer the type of the expression *)
  | InequalTypes  (* Actual type does not match expected types *)
  | NotAFunction  (* Attempted to call something that's not a function *)
  | OccursCheck   (* Attempted to unify a recursive type *)
  | UndefinedName (* No such name in scope *)

(* Type language *)
module Type = struct
  type t =
    | Unit
    | Name of name
    | Fun of t * t
    | Forall of name * t
    | Var of var ref

  and var =
    | Unbound of string
    | Bound of t
end

(* Term language *)
module Expr = struct
  type t =
    | Unit
    | Name of name
    | Fun of name * t
    | App of t * t
    | Anno of t * Type.t
end

(* The context binds names to their types. *)
type ctx = { ctx : (name * Type.t) list; fresh : int }
let empty = { ctx = []; fresh = 0 }

module Ctx = struct
  type 'a t = ctx -> (ctx * 'a, tyck_error) result

  let return x : 'a t = fun ctx -> Ok (ctx, x)
  let fail e : 'a t = fun ctx -> Error e

  let bind: 'a t -> ('a -> 'b t) -> 'b t =
    fun value f ctx ->
      match value ctx with
      | Ok (ctx, x) -> f x ctx
      | Error e -> Error e

  let (let*) = bind
end

let with_anno param ty : unit Ctx.t =
  fun { ctx; fresh } ->
    Ok ({ ctx = (param, ty) :: ctx; fresh }, ())

let fresh : Type.t Ctx.t =
  fun { ctx; fresh } ->
    let name = "'" ^ (Int.to_string fresh) in
    Ok ({ ctx; fresh = fresh + 1}, Type.Var (ref (Type.Unbound name)))

let lookup name : Type.t Ctx.t =
  fun { ctx; fresh } ->
    match List.assoc_opt name ctx with
    | Some ty -> Ok ({ ctx; fresh }, ty)
    | None -> Error UndefinedName

let unify ~expected ~actual : unit Ctx.t =
  let open Ctx in
  let rec helper eq_names =
    let names_equal n m =
      if n = m then return () 
      else
        let pred = fun (a, b) -> (a = n && b = m) || (a = m && b = n) in
        match List.find_opt pred eq_names with
        | Some _ -> return ()
        | None -> fail InequalTypes
    in

    let rec doesnt_occur var =
      function
        | Type.Unit | Type.Name _ -> return ()
        | Type.Fun (t, u) ->
            begin
              let* () = doesnt_occur var t in
              doesnt_occur var u
            end
        | Type.Forall (_, t) -> doesnt_occur var t
        | Type.Var war ->
            if var = war then fail OccursCheck
            else return ()
    in

    function
      | Type.Unit, Type.Unit -> return ()
      | Type.Name n, Type.Name m -> names_equal n m
      | Type.Fun (t1, u1), Type.Fun (t2, u2) ->
          begin
            let* () = helper eq_names (t1, t2) in
            helper eq_names (u1, u2)
          end
      | Type.Forall (n, t), Type.Forall (m, u) ->
          helper ((n, m) :: eq_names) (t, u)
      | Type.Var ({ contents = Type.Unbound _ } as var), t
      | t, Type.Var ({ contents = Type.Unbound _ } as var) ->
          begin
            let* () = doesnt_occur var t in
            var := Type.Bound t;
            return ()
          end
      | Type.Var ({ contents = Type.Bound t}), u
      | t, Type.Var ({ contents = Type.Bound u }) -> helper eq_names (t, u)
      | _ -> fail InequalTypes
  in
  helper [] (expected, actual)

let instantiate ty : Type.t Ctx.t =
  let open Ctx in
  let rec helper name_map =
    function
      | Type.Unit -> return Type.Unit
      | Type.Name n ->
          begin
            match List.assoc_opt n name_map with
            | Some t -> return t
            | None -> return (Type.Name n)
          end
      | Type.Fun (t, u) ->
          begin
            let* t = helper name_map t in
            let* u = helper name_map u in
            return (Type.Fun (t, u))
          end
      | Type.Forall (n, t) ->
          begin
            let* t = helper name_map t in
            return (Type.Forall (n, t))
          end
      | Type.Var { contents = Bound t } -> helper name_map t
      | Type.Var { contents = Unbound _ } as t -> return t
  in

  let rec instantiate name_map =
    function
      | Type.Forall (n, t) ->
          begin
            let* var = fresh in
            instantiate ((n, var) :: name_map) t
          end
      | Type.Var { contents = Bound t } ->
          instantiate name_map t
      | ty -> helper name_map ty
  in

  instantiate [] ty

let fun_type : Type.t -> (Type.t * Type.t) Ctx.t =
  let open Ctx in
  function
  | Type.Fun (t, u) -> return (t, u)
  | _ -> fail NotAFunction
