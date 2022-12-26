(** bdf2 - some implicit instantiation *)

open Lang
open Ctx

let rec check =
  function
    | Expr.Unit, Type.Unit -> return ()
    | Expr.Fun (param, body), Type.Fun (t, u) -> 
        begin
          let* () = with_anno param t in
          check (body, u)
        end
    | Expr.Fun _ as ex, Type.Forall (_, ty) -> check (ex, ty)
    | ex, expected ->
        begin
          let* actual = infer ex in
          unify ~expected ~actual
        end

and infer =
  function
    | Expr.Name name -> 
        begin
          let* ty = lookup name in
          instantiate ty
        end
    | Expr.App (f, x) ->
        begin
          let* f_ty = infer f in
          let* f_ty = instantiate f_ty in
          let* (t, u) = fun_type f_ty in
          let* () = check (x, t) in
          return u
        end
    | Expr.Anno (ex, ty) ->
        let* () = check (ex, ty) in
        return ty
    | _ -> fail Ambiguous

