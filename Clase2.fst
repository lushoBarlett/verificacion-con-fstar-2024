module Clase2

(* Polimorfismo paramétrico y lógica constructiva. *)

(* La identidad polimórfica *)
val id0_exp : (a:Type) -> a -> a
let id0_exp = fun (a:Type) -> fun (x:a) -> x

// let id0_exp = fun (a:Type) -> fun (x:a) -> x
let id_int  : int  -> int  = id0_exp _
let id_bool : bool -> bool = id0_exp _

let _ = assert (id_int 1 == 1)
let _ = assert (id_bool true == true)

(* El símbolo # marca un argumento * implícito. Estos argumentos
se insertan automáticamente por el typechecker cuando son requeridos.
Si hay una única forma de resolverlos, dada otras restricciones en el contexto,
F* usará esa solución. Si por alguna razón no puede resolverse automáticamente,
siempre pueden darse de forma explícita usando un # en la aplicación. *)

let id (#a:Type) (x:a) : a = x
// let id = fun (#a:Type) -> fun (x:a) -> x
let id_int'  : int -> int   = id
let id_bool' : bool -> bool = id

let _ = assert (id 1 == 1)
let _ = assert (id true == true)

(* Un tipo verdaderemente dependiente *)
val raro : bool -> Type0
let raro (b:bool) : Type =
  if b
  then int
  else string

(* Una función con el tipo `raro`: devuelve un entero o una
cadena según su argumento. *)
let f_raro (x:bool) : raro x =
  if x then 123 else "hola"

let _ = assert (f_raro true == 123)
let _ = assert (f_raro false == "hola")

(* (listas)^n de a *)
let rec nlist (a:Type) (n:nat) : Type =
  match n with
  | 0 -> a
  | n -> list (nlist a (n-1))

let rec n_singleton (#a:_) (x:a) (n:nat) : nlist a n =
  match n with
  | 0 -> x
  | n -> [n_singleton x (n-1)]

let _ = assert (n_singleton 1 0 == 1)
let _ = assert (n_singleton 1 1 == [1])
let _ = assert (n_singleton 1 2 == [[1]])

(* Lógica constructiva *)

(*
De la librería estándar de F*:

        type tuple2 'a 'b = | Mktuple2 : _1: 'a -> _2: 'b -> tuple2 'a 'b
        let fst (x: tuple2 'a 'b) : 'a = Mktuple2?._1 x
        let snd (x: tuple2 'a 'b) : 'b = Mktuple2?._2 x

        type either a b =
        | Inl : v: a -> either a b
        | Inr : v: b -> either a b

`a & b` es azúcar para `tuple2 a b`
`(x,y)` es azúcar para `Mktuple2 x y`
*)
type yy (a b : Type) = a & b
type oo (a b : Type) = either a b
type falso =
type verd = falso -> falso
type no (a : Type) = a -> falso

let vv : verd = id

(* La conjunción conmuta *)
let comm_yy (#a #b : Type) : yy a b -> yy b a =
  fun p -> (snd p, fst p)
//   fun (x, y) -> (y, x)

(* verd es neutro para la conjunción *)
let neutro_yy (#a:Type) : yy a verd -> a =
  fun (x, _) -> x

let neutro_yy' (#a:Type) : a -> yy a verd =
  fun (x:a) -> (x, vv)

(* La disjunción conmuta *)
(* `function` es azúcar para `fun` con un pattern matching inmediato al argumento. *)
let comm_oo (#a #b : Type) : oo a b -> oo b a =
  function
  | Inl x -> Inr x
  | Inr y -> Inl y

(* Principio de explosión: falso no tiene constructores,
así que con un match vacío podemos demostrar cualquier cosa *)
let ex_falso (#a:Type) (f : falso) : a =
  match f with

(* Demostrar *)
let neu1 (#a:Type) : oo a falso -> a =
  function
  | Inl x -> x
  | Inr f -> ex_falso f

(* Demostrar *)
let neu2 (#a:Type) : a -> oo a falso = Inl

(* Distribución de `yy` sobre `oo`, en ambas direcciones *)
let distr_yyoo_1 (#a #b #c : Type)
  : yy a (oo b c) -> oo (yy a b) (yy a c)
  // a /\ (b \/ c)  ==>  (a /\ b) \/ (a /\ c)
  // a * (b + c)    ==>  (a * b) + (a * c)
=
  fun (x, yz) ->
  match yz with
  | Inl y -> Inl (x, y)
  | Inr z -> Inr (x, z)

let distr_yyoo_2 (#a #b #c : Type)
  : oo (yy a b) (yy a c) -> yy a (oo b c)
=
  function
  | Inl (x, y) -> (x, Inl y)
  | Inr (x, z) -> (x, Inr z)

let distr_ooyy_1 (#a #b #c : Type)
  : oo a (yy b c) -> yy (oo a b) (oo a c)
=
  function
  | Inl x -> (Inl x, Inl x)
  | Inr (y, z) -> (Inr y, Inr z)

let distr_ooyy_2 (#a #b #c : Type)
  : yy (oo a b) (oo a c) -> oo a (yy b c)
=
  fun (xy, xz) ->
  match xy, xz with
  | Inl x, _ -> Inl x
  | _, Inl x -> Inl x
  | Inr y, Inr z -> Inr (y, z)

let modus_tollens (#a #b : Type)
  : (a -> b) -> (no b -> no a)
=
  fun f ->
    fun fb ->
      fun a -> fb (f a) // a -> b + b -> falso = a -> falso
  (* Vale la recíproca? *)

let modus_tollens_rec (#a #b : Type)
  : (no b -> no a) -> (a -> b)
=
  fun fnobnoa ->
    fun a ->
      let fnob = fun b -> magic() in
      let fnoa = fnobnoa (fnob) in
      let b = ex_falso (fnoa a) in b
  // no vale la recíproba porque debo construir un tipo (b -> falso) y no puedo
  // construir una función que retorne falso, desde cero, ya que falso no tiene habitantes

let modus_tollendo_ponens (#a #b : Type)
  : (oo a b) -> (no a -> b)
=
  function
  | Inl x -> fun f -> ex_falso (f x) // tiene tipo b por explosión
  | Inr y -> fun _ -> y              // tiene tipo b naturalmente
  (* Vale la recíproca? *)

let modus_tollendo_ponens_rec (#a #b : Type)
  : (no a -> b) -> oo a b
=
  fun fnoab ->
    let fnoa = fun a -> magic() in
    let b = fnoab fnoa in
    Inr b
  // fun fnoab ->
  //   let a = magic() in
  //   Inl a
  // tengo que construir un a, o un b
  // para construir un b, tendría que llamar a una cierta
  // función que dada una función (a -> falso) me devuelve un b
  // para eso necesito darle una función de (a -> falso)
  // pero no puedo construir ninguna. Tampoco puedo construir un a porque
  // todo lo que me dan es una función que toma (a -> falso)

let modus_ponendo_tollens (#a #b : Type)
  : no (yy a b) -> (a -> no b)
=
  fun ftuplexy ->
    fun x ->
      fun y ->
        ftuplexy (x, y)
  (* Vale la recíproca? *)

let modus_ponendo_tollens_rec (#a #b : Type)
  : (a -> no b) -> no (yy a b)
=
  fun fxy ->
    fun (x, y) -> fxy x y

(* Declare y pruebe, si es posible, las leyes de De Morgan
para `yy` y `oo`. ¿Son todas intuicionistas? *)

let demorgan1_ida (#a #b : Type) : oo (no a) (no b) -> no (yy a b) =
  function
  | Inl fnoa -> fun (x, _) -> ex_falso (fnoa x)
  | Inr fnob -> fun (_, y) -> ex_falso (fnob y)

let demorgan1_vuelta (#a #b : Type) : no (yy a b) -> oo (no a) (no b) =
  fun fnoab ->
    let fnoa = fun a -> fnoab (a, magic()) in
    Inl fnoa
  // fun fnoab ->
  //   let fnob = fun b -> fnoab (magic(), b) in
  //   Inr fnob
  // para poder devolver falso, necesito pasarle a la función que me dan
  // como argumento tanto un a como un b, pero solo puedo construir
  // un testigo de tomar un a, o un testigo de tomar un b, me falta siempre uno

let demorgan2_ida (#a #b : Type) : yy (no a) (no b) -> no (oo a b) =
  fun (fx, fy) ->
    function
    | Inl x -> fx x
    | Inr y -> fy y

let demorgan2_vuelta (#a #b : Type) : no (oo a b) -> yy (no a) (no b) =
  fun fxoy -> (
    (fun x -> fxoy (Inl x)),
    (fun y -> fxoy (Inr y))
  )

 (* P y no P no pueden valer a la vez. *)
let no_contradiccion (#a:Type) : no (yy a (no a)) =
  fun (x, f) -> f x

(* Mientras "quede" una negación, sí podemos eliminar doble
negaciones. Pero no podemos llegar a una prueba de a.

Ver también el embebimiento de lógica clásica en lógica intuicionista
via doble negación (spoiler: p se embebe como no (no p), y resulta equivalente
a la lógica clásica. *)
let elim_triple_neg (#a:Type) : no (no (no a)) -> no a =
  fun f a -> f (fun g -> g a)

(* Ejercicio. ¿Se puede en lógica intuicionista? *)
let ley_impl1 (p q : Type) : (p -> q) -> oo (no p) q =
  fun fpq ->
    let fnop = fun p -> magic() in
    Inl fnop 
  // fun fpq ->
  //   let q = fpq (magic()) in
  //   Inr q
  // o construyo q (no puedo, porque no tengo p)
  // o construyo una función p -> falso, que tampoco puedo hacer

(* Ejercicio. ¿Se puede en lógica intuicionista? *)
let ley_impl2 (p q : Type) : oo (no p) q -> (p -> q) =
  function
  | Inl fp -> fun p -> ex_falso (fp p)
  | Inr q  -> fun _ -> q

(* Ejercicio. ¿Se puede en lógica intuicionista? *)
let ley_impl3 (p q : Type) : no (p -> q) -> yy p (no q) =
  fun fnopq ->
    let p = magic() in
    let fnoq = fun q -> fnopq (fun _ -> q) in
    (p, fnoq)
  // en base a una función que toma una p -> q y me da falso
  // tengo que construir un p, y una q -> falso
  // no hay forma de construir p que quede en el contexto

(* Ejercicio. ¿Se puede en lógica intuicionista? *)
let ley_impl4 (p q : Type) : yy p (no q) -> no (p -> q) =
  fun (p, fnoq) ->
    fun fpq ->
      fnoq (fpq p)

(* Tipos para axiomas clásicos *)
type eliminacion_doble_neg = (#a:Type) -> no (no a) -> a
type tercero_excluido = (#a:Type) -> oo a (no a)

(* Ejercicio *)
let lte_implica_edn (lte : tercero_excluido) (#a:Type) : eliminacion_doble_neg =
  fun (#a:Type) ->
    match lte #a with
    | Inl a'   -> fun _ -> a'
    | Inr fnoa -> fun fnofnoa -> fnofnoa fnoa

(* Ejercicio. ¡Difícil! *)
let edn_implica_lte (edn : eliminacion_doble_neg) (#a:Type) : tercero_excluido =
  fun (#a:Type) ->
    let neg: no (yy (no a) (no (no a))) = fun (x, f) -> f x in // completamos
    let impl: no (oo a (no a)) -> yy (no a) (no (no a)) = demorgan2_vuelta in // lo único que nos sale aplicar en este tipo
    let double_neg: no (no (oo a (no a))) = modus_tollens impl neg in // a -> b && (no b) yo te doy (no a). a === no (oo x (no x))
    edn double_neg // no (no <loquesea>) se puede construir siempre!
    // Estos comentarios se leen al revés!

(* Ejercicio: ¿la ley de Peirce es intuicionista o clásica?
Demuestrelá sin axiomas para demostrar que es intuicionista,
o demuestre que implica el tercero excluido para demostrar que
es clásica. *)

type peirce = (#a:Type) -> (#b:Type) -> ((a -> b) -> a) -> a

let lte_implica_peirce (lte : tercero_excluido) : peirce =
  fun (#a:Type) -> fun (#b:Type) -> fun f ->
    match lte #a with
    | Inl a  -> a
    | Inr fnoa -> f (fun a -> ex_falso (fnoa a))

let peirce_implica_lte (pp : peirce) : tercero_excluido =
  fun (#a:Type) ->
    let ff: (oo a (no a) -> a) -> oo a (no a) = magic() in
    pp ff