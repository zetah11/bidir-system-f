(** bdf1 - bidirectional checking of a lambda calculus that's effectively simply
    typed. *)

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
    | ex, expected ->
        begin
          let* actual = infer ex in
          unify ~expected ~actual
        end

and infer =
  function
    | Expr.Name name -> lookup name
    | Expr.App (f, x) ->
        begin
          let* f_ty = infer f in
          let* (t, u) = fun_type f_ty in
          let* () = check (x, t) in
          return u
        end
    | Expr.Anno (ex, ty) ->
        let* () = check (ex, ty) in
        return ty
    | _ -> fail Ambiguous

