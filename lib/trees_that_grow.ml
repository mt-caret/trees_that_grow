open Core

module Type = struct
  type t =
    | Int
    | Fun of t * t
  [@@deriving equal]
end

type lit = [ `lit ]
type var = [ `var ]
type ann = [ `ann ]
type abs = [ `abs ]
type app = [ `app ]
type exp = [ `exp ]

type non_exp =
  [ lit
  | var
  | ann
  | abs
  | app
  ]

module Exp = struct
  type undecorated = [ `undecorated ]
  type type_ = [ `type_ ]
  type partial_eval = [ `partial_eval ]

  type (_, _) ext =
    | Undecorated_exp : Nothing.t -> (exp, undecorated) ext
    | Undecorated : ([< non_exp ], undecorated) ext
    (* App takes an additional Type.t, and Exp does not exist: *)
    | Type_app : Type.t -> (app, type_) ext
    | Type_exp : Nothing.t -> (exp, type_) ext
    | Type_ : ([< lit | var | ann | abs ], type_) ext
    (* We have an additional variant that takes a value : int *)
    | Partial_eval_exp : { value : int } -> (exp, partial_eval) ext
    | Partial_eval : ([< non_exp ], partial_eval) ext

  type 'ext t =
    | Lit of (lit, 'ext) ext * int
    | Var of (var, 'ext) ext * string
    | Ann of (ann, 'ext) ext * 'ext t * Type.t
    | Abs of (abs, 'ext) ext * string * 'ext t
    | App of (app, 'ext) ext * 'ext t * 'ext t
    | Exp of (exp, 'ext) ext

  let rec type_check : type_ t -> Type.t String.Map.t -> Type.t -> bool =
   fun t env type_ ->
    match t with
    | Lit (Type_, _) ->
      (match type_ with
      | Int -> true
      | Fun _ -> false)
    | Var (Type_, var) ->
      Map.find env var |> Option.value_map ~default:false ~f:(Type.equal type_)
    | Ann (Type_, t', type_') -> Type.equal type_ type_' && type_check t' env type_
    | Abs (Type_, var, t') ->
      (match type_ with
      | Int -> false
      | Fun (a, b) -> type_check t' (Map.add_exn env ~key:var ~data:a) b)
    | App (Type_app a, l, m) -> type_check l env (Fun (a, type_)) && type_check m env a
    | Exp (Type_exp _) -> .
 ;;
end

(* module Boolang = struct
  type 'a t =
    | Base of 'a
    | Or of ('a t * 'a t)
    | And of ('a t * 'a t)
  (* Implies of ('a t * 'a t)*)
end *)

module Boolang = struct
  (* type ('case, 'mode) ext =
  |  *)
  type base = [ `base ]
  type not = [ `not ]
  type or_ = [ `or_ ]
  type and_ = [ `and_ ]
  type extra = [ `extra ]

  type rest =
    [ base
    | not
    | or_
    | and_
    ]

  type minimal = [ `minimal ]
  type with_implication = [ `with_implication ]

  type ('variant, _, 'kind) ext =
    | Minimal_extra : Nothing.t -> (extra, _, minimal) ext
    | Minimal : ([< rest ], _, minimal) ext
    | With_implication_extra :
        { if_ : ('a, with_implication) t
        ; then_ : ('a, with_implication) t
        }
        -> (extra, 'a, with_implication) ext
    | With_implication : ([< rest ], _, with_implication) ext

  and ('a, 'kind) t =
    | Base of ((base, 'a, 'kind) ext * 'a)
    | Not of ((not, 'a, 'kind) ext * ('a, 'kind) t)
    | Or of ((or_, 'a, 'kind) ext * ('a, 'kind) t * ('a, 'kind) t)
    | And of ((and_, 'a, 'kind) ext * ('a, 'kind) t * ('a, 'kind) t)
    | Extra of (extra, 'a, 'kind) ext

  let rec evaluate_minimal : type a. (a, minimal) t -> (a -> bool) -> bool =
    fun (type v) (t : (v, minimal) t) f ->
     match t with
     | Base (Minimal, x) -> f x
     | Not (Minimal, a) -> not (evaluate_minimal a f)
     | Or (Minimal, a, b) -> evaluate_minimal a f || evaluate_minimal b f
     | And (Minimal, a, b) -> evaluate_minimal a f && evaluate_minimal b f
     | Extra (Minimal_extra _) -> .
  ;;

  let rec evaluate_with_implication
      : type a. (a, with_implication) t -> (a -> bool) -> bool
    =
    fun (type v) (t : (v, with_implication) t) f ->
     match t with
     | Base (With_implication, x) -> f x
     | Not (With_implication, a) -> not (evaluate_with_implication a f)
     | Or (With_implication, a, b) ->
       evaluate_with_implication a f || evaluate_with_implication b f
     | And (With_implication, a, b) ->
       evaluate_with_implication a f && evaluate_with_implication b f
     | Extra (With_implication_extra { if_; then_ }) ->
       (not (evaluate_with_implication if_ f)) || evaluate_with_implication then_ f
  ;;

  let rec to_minimal : type a. (a, with_implication) t -> (a, minimal) t =
    fun (type v) (t : (v, with_implication) t) ->
     match t with
     | Base (With_implication, x) -> Base (Minimal, x)
     | Not (With_implication, a) -> Not (Minimal, to_minimal a)
     | Or (With_implication, a, b) -> Or (Minimal, to_minimal a, to_minimal b)
     | And (With_implication, a, b) -> And (Minimal, to_minimal a, to_minimal b)
     | Extra (With_implication_extra { if_; then_ }) ->
       Or (Minimal, Not (Minimal, to_minimal if_), to_minimal then_)
  ;;
end
