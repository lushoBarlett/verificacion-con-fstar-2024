module Clase3.GADT

type l_ty =
  | Int
  | Bool
  
type expr : l_ty -> Type =
  | EInt : int -> expr Int
  | EBool : bool -> expr Bool
  | EAdd : expr Int -> expr Int -> expr Int
  | EEq : expr Int -> expr Int -> expr Bool
  | EIf :
    #ty:_ ->
    expr Bool -> expr ty -> expr ty -> expr ty

let lift (ty : l_ty) : Type =
  match ty with
  | Int -> int
  | Bool -> bool

let rec eval_int : expr Int -> Tot int =
  fun e ->
  match e with
  | EInt n -> n
  | EAdd e1 e2 -> eval_int e1 + eval_int e2
  | EIf b e1 e2 -> if eval_bool b then eval_int e1 else eval_int e2
and eval_bool : expr Bool -> Tot bool =
  fun e ->
  match e with
  | EBool b -> b
  | EEq e1 e2 -> eval_int e1 = eval_int e2
  | EIf b e1 e2 -> if eval_bool b then eval_bool e1 else eval_bool e2

val eval (#ty:l_ty) (e : expr ty) : Tot (lift ty)

let eval (#ty:l_ty) (e : expr ty) : Tot (lift ty) =
  match ty with
  | Int -> eval_int e
  | Bool -> eval_bool e

// CONSULTA: por qué la versión con una sola llamada recursiva
// no puede probar terminación? Hay una forma de hacerlo con una sola?
// está mal hacerlo así? hay valores no representables?