# A bidirectional and unifying type-checker for System F

This project is a simple implementation of a type checker for a System
F-inspired lambda calculus. At its core, the checker is *bidirectional*, which
means it has a pair of mutually recursive functions:

- `check (expr, ty)` takes some expression and a type, and checks the expression
  against that type
- `infer expr` takes some expression and infers its type

In contrast to the "normal" System F, this language completely lacks explicit
type lambdas and instantiations. Instead, it tries to figure out when a
`forall`-quantified type should be instantiated and when it should not. The
instantiated type is solved using a unification procedure.

The System F term

$$
((\Lambda \alpha. \lambda x:a.x) : \forall a.a\to a)\;1\;(() : 1)
$$

where $()$ is a unit value and $1$ is the unit type, is written in this language
as

```
((fun x. x) : forall a. a -> a) (() : 1)
```

The type checker will "unwrap" the `forall` and check the lambda `fun x. x`
against the type `a -> a`, where `a` is treated as some abstract type. When it
tries to infer the type of the overall application, it sees that the function is
universally quantified, and so instantiates it with a fresh type variable. The
term `() : 1` then unifies with that type variable, and the final type of this
term is `1`.

One of the nifty things about System F is its higher rank powers. This means we
can define functions that take in generic functions, such as this one:

$$
(\lambda id^{\forall a.a\to a}.(id\;(1\to1)\;((\lambda x^1.x):1\to 1))\;(id\;1\;())):(\forall a. a\to a)\to 1
$$

Things get a bit messy when we write everything out as one term, but this is an
anonymous function of type $(\forall a.a\to a)\to 1$, which takes as parameter a
generic function of type $\forall a.a\to a$ (the identity function) and returns
a unit value. Inside the definition, this identity parameter is applied first to
a function taking and immediately returning a unit value, and *that* function is
applied to the result of applying the identity parameter to a unit value.

In this language, that would be written as

```
(fun id. (id ((fun x. x) : 1 -> 1)) (id (() : 1))) : (forall a. a -> a) -> 1
```

Within the lambda, `id` has a polymorphic type which is instantiated with a
fresh unification variable on every application.

The above term can be applied to a function like

```
(fun x. x) : forall a. a -> a
```

which will *not* be instantiated, since it's expected to be polymorphic.

---

This article implements several type checkers, starting with a simple
bidirectional checker for an almost-simply-typed variant, gradually adding
features to produce something more powerful. Each version is named `bdfN.ml`,
and can be tested in an OCaml top-level like so:

```
$ ocamlc lang.ml
$ ocaml
        OCaml version 4.12.0

# #load "lang.cmo";;
# #use "bdf1.ml";;
val check : Lang.Expr.t * Lang.Type.t -> unit Lang.Ctx.t = <fun>
val infer : Lang.Expr.t -> Lang.Type.t Lang.Ctx.t = <fun>
# check (Expr.Unit, Type.Unit) empty;;
- : (Lang.ctx * unit, Lang.tyck_error) result =
Ok ({ctx = []; fresh = 0}, ())
# 
```

## Preliminaries

The file `lang.ml` defines the syntax trees for the terms and the types, as well
as a state monad for keeping track of the typing context. The specifics of this
are a bit outside the scope here, but take a look at the file for more details.

The language consists of terms and types. Types look like

```ocaml
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
```

`Unit` is the unit type, `Name n` is a type name (those introduced by `forall`),
`Fun (t, u)` is the function type `t -> u`, `Forall (n, t)` is a type `t` with a
universally quantified type variable `n`, and `Var v` is a unification variable.

Terms look like

```ocaml
module Expr = struct
  type t =
    | Unit
    | Name of name
    | Fun of name * t
    | App of t * t
    | Anno of t * Type.t
end
```

An expression is either a unit expression, a named variable (those introduced by
`fun`), a function abstraction like `fun n. x`, a function application, or an
expression annotated with a type.

## `bdf1.ml`

This is the starting framework. We have two mutually recursive functions,
`check` and `infer`.

```ocaml
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
```

This corresponds to the following typing rules:

Unit checks against unit

$$
\frac{}{\vdash ()\Leftarrow1}
$$

Lambdas check against function types

$$
\frac{\Gamma,n:t\vdash x\Leftarrow u}
{\Gamma\vdash \mathtt{fun}\;n.x \Leftarrow t\to u}
$$

The subsumption rule switches from checking to inferring, making sure that the
types are equal.

$$
\frac{\Gamma\vdash x\Rightarrow t \quad t\sim u}{\Gamma\vdash x\Leftarrow u}
$$

Names infer their bound type

$$
\frac{x:t\in\Gamma}{\Gamma\vdash x\Rightarrow t}
$$

Applications infer the return type of the function being applied

$$
\frac{\Gamma\vdash f\Rightarrow t\to u \quad \Gamma\vdash x\Leftarrow t}
{\Gamma\vdash f\;x\Rightarrow u}
$$

Annotations infer the annotated type

$$
\frac{\Gamma\vdash x\Leftarrow t}{\Gamma\vdash x:t\Rightarrow t}
$$

Note that in the subsumption rule, we're calling the `unify` function. In this
case, since there are no type variables, it corresponds exactly to a type
equality check.

## `bdf2.ml`

Now, let's add on some type variables. One thing to note about the previous
checker is that a variable like `id: forall a. a -> a` is unusable, since
there's no rule that handles this case.

In this checker, we'll amend the inference rule for names. Similar to
Hindley-Milner-like type checkers, all polymorphic names will be instantiated on
use. The change is relatively simple:

```ocaml
and infer = 
  function
    | Expr.Name name ->
        begin
          let* ty = lookup name in
          instantiate ty
        end
    (* ...*)
```

`instantiate ty` is a function that replaces the outermost `forall`-bound type
variables with unification variables. For instance, instantiating a type like 
`forall a. (forall b. b -> b) -> a` produces the type `(forall b. b -> b) ->
'1`, where `'1` is a fresh unification variable.

Note that only the outermost `forall`s are "removed". For instance,
`1 -> (forall a. a -> a)` does not change during instantiation.

The new name rule looks like this:

$$
\frac{x:t\in\Gamma \quad u=\mathrm{inst}(t)}
{\Gamma\vdash x\Rightarrow u}
$$

At this stage, we can also add implicit type lambdas. The idea here is that a
type like $\forall a. t$ is always the type of something like $\Lambda\alpha.x$.
As such, we can just implicitly place a lambda there, and check `x` against `t`,
treating `a` as some abstract type.

For various reasons, however, always "unwrapping" a `forall` like that when
checking would be a bit too eager. Instead, we can make a choice and see that
*most of the time* when we want to implicitly assume a type lambda, it will be
in front of a term lambda.

In code, this looks like adding an extra case to the `check` function:

```ocaml
let rec check =
  function
    (* ... *)
        end
    | Type.Fun _ as ex, Type.Forall (_, ty) -> check (ex, ty)
    | ex, expected ->
        begin
    (* ...*)
```

If your type checker is more like an elaborator - as in, if it also "lowers" the
syntax to something like a more explicit core language, then this is where you'd
add a type lambda. In this case, we just want to check, so we throw away the
`forall`-bound name.

$$
\frac{\Gamma\vdash\lambda n.x \Leftarrow t \quad a\notin\mathrm{free}(t)}
{\Gamma\vdash\lambda n.x \Leftarrow\forall a.t}
$$

Finally, look at the application case:

```ocaml
    | Expr.App (f, x) ->
        begin
          let* f_ty = infer f in
          let* f_ty = instantiate f_ty in
          let* (t, u) = fun_type f_ty in
          let* () = check (x, t) in
          return u
        end
```

The `fun_type` function here gets the argument and return type from a function
type, or errors if the given type is not a function type. We might want to
support something like

```
((fun x. x) : forall a. a -> a) (() : 1)
```

Note that the polymorphic function is immediately applied. To do this, we need
to instantiate the function. This might seem like it's a bit too eager of a
thing to do, but note that the instantiation function only removes the outermost
`forall`s, so no higher-rank shenaningans would be lost.

$$
\frac{\Gamma\vdash f\Rightarrow t \quad \Gamma\vdash x\Leftarrow u \quad (u\to v)=\mathrm{inst}(t)}
{\Gamma\vdash f\;x\Rightarrow v}
$$

## `bdf3.ml`

At this point, we can type check most things you can write in a
Hindley-Milner-style type system. We can also write higher-rank functions that
typecheck, but we can't use them *that* well yet.

As an example, if you have the name-type pairs `id: forall a. a -> a` and
`f: (forall a. a -> a) -> 1`, then something like `f (fun x. x)` will check, but
`f id` won't. This is because `f` is instantiated first (which in this case does
nothing), then `id` is instantiated to `'1 -> '1`, and then that is unified with
`forall a. a -> a`. This *doesn't* unify (and in the general case it shouldn't).
The problem is the second instantiation - in this case, because we're expecting
a polymorphic value, `id` shouldn't be instantiated but left as-is.

How do we deal with this? Note that currently, instantiation only happens in two
places:

1. The function expression during function application
2. The inferred type of a name

The first is, as mentioned above, never problematic. And in this case, it is in
fact the second rule that is troublesome. We could simply *not* instantiate the
type, but that would make "obviously okay" things like `apply id (() : 1)` not
type check.

> You *can* go this route, if you want. Expressions like `id (() : 1)` still
> check, since the function application rule instantiates the type of `id`. But
> higher-order functions like `map` and such would require explicit
> instantiations when used with arguments that are polymorphic, which is perhaps
> a bit annoying.

Another approach is to add a checking rule for names. Note that in most cases
where the type checker instantiates too eagerly, we're actually in a position
where we're checking a name against some polymorphic type. But because there's
no checking rule for a name, we end up inferring its type (thereby instantiating
it) and then attempting to unify that monomorphic type with some polymorphic
type.

Let's address this by adding a checking rule for names. Where the inference rule
instantiates the name, the checking rule unifies it with the expected type.

```ocaml
let rec check =
  function
    | Expr.Unit, Type.Unit -> return ()
    | Expr.Name name, expected ->
        begin
          let* actual = lookup name in
          unify ~expected ~actual
        end
    | Expr.Fun (param, body), Type.Fun (t, u) -> 
        begin
    (* ... *)
```

$$
\frac{x:t\in\Gamma \quad t\sim u}
{\Gamma\vdash x\Leftarrow u}
$$

