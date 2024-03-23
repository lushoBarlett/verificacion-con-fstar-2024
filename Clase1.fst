module Clase1

(* Hace que '*' sea la multiplicación de enteros, en vez del constructor de tuplas. *)
open FStar.Mul
open FStar.List.Tot

let suma (x y : int) : int = x + y

(* Defina una función suma sobre naturales *)
let addnat (x y : nat) : nat = x + y

(* Defina una función suma de 3 argumentos, que use la anterior. *)
let suma3 (x y z : int) : int = suma x (suma y z)

(* Defina una función que incremente un número en 1. *)
let incr (x:int) : int = x + 1

(* Dé más tipos a la función de incremento. ¿Cómo se comparan
estos tipos? *)
let incr'   (x:nat) : int = x + 1
let incr''  (x:nat) : nat = x + 1
let incr''' (x:nat) : y:int{y = x+1} = x + 1

(* Un tipo refinado es un subtipo del tipo base, se puede
usar sin coerción. El subtipado es también consciente de funciones. *)
let addnat' (x y : nat) : int = x + y

let debilitar1 (f : int -> int) : nat -> int = f
let debilitar2 (f : nat -> nat) : nat -> int = f
let debilitar3 (f : int -> nat) : nat -> int = f

let par   (x:int) : bool = x % 2 = 0
let impar (x:int) : bool = x % 2 = 1

(* Dadas estas definiciones, dé un tipo a incr que diga
que dado un número par, devuelve un número impar. *)
// let incr'''' (x:...) : .... = x+1

(* ¿Por qué falla la siguiente definición? Arreglarla. *)
// El atributo expect_failure causa que F* chequeé que la definición
// subsiguiente falle. Borrarlo para ver el error real.
let muldiv (a:int) (b:nonzero{a % b = 0}) : y:int{y = a} = (a / b) * b
// Falla porque es posible dividir por cero
// y además porque el truncamiento vuelve a la división no reversible

(* Defina una función de valor absoluto *)
let abs (x:int) : nat = if x < 0 then -x else x

(* Defina una función que calcule el máximo de dos enteros. *)
let max (x y : int) : z:int{(z = x || z = y) && z >= x && z >= y} = if x < y then y else x

(* Dé tipos más expresivos a max.
   1- Garantizando que el resultado es igual a alguno de los argumentos
   2- Además, garantizando que el resultado es mayor o igual a ambos argumentos. *)

(* Defina la función de fibonacci, de enteros a enteros,
o alguna restricción apropiada. *)
let rec fib (x:nat) : nat =
   if x = 0
      then 0
   else if x = 1
      then 1
   else
      fib (x-1) + fib (x-2)

(* Defina un tipo 'digito' de naturales de un sólo dígito. *)
type digito = n:nat{0 <= n && n <= 9}

(* Defina una función que compute el máximo de tres dígitos, usando
alguna definición anterior. El resultado debe ser de tipo digito.
¿Por qué funciona esto? ¿De cuáles partes anteriores del archivo
depende, exactamente? *)
let max_digito (x y z : digito) : digito = max x (max y z)
// funciona porque digito es un entero (refinement subtyping)
// por lo que max acepta estos argumentos, y además el verificador
// sabe que el resultado es exáctamente uno de los argumentos
// que son ambos dígitos, por lo que (max x:digito y:digito) : digito

(* Defina la función factorial. ¿Puede darle un mejor tipo? *)
let rec fac (x:nat) : nat = if x = 0 then 1 else x * fac (x-1)

(* Defina una función que sume los números naturales de 0 a `n`. *)
let rec triang (n:nat) : nat = if n = 0 then 0 else n + triang (n-1)

(* Intente darle un tipo a fib que diga que el resultado es siempre
mayor o igual al argumento. Si el chequeo falla, dé hipótesis de por qué. *)
let rec fib' (x:nat) : y:pos{y >= x} =
   if x = 0 then 1
   else if x = 1 then 1
   else fib' (x-1) + fib' (x-2)
// En este caso tenemos las siguientes ecuaciones en la tercer branch:
// x >= 2 && fib' (x-1) >= x-1 && fib' (x-2) >= x-2
// por lo que no se puede probar que
// fib' (x-1) + fib' (x-2) >= x - 1 + x - 2 = 2x - 3
// pero 2x - 3 >= x <=> 2x >= x + 3 <=> x >= 3
// por lo que hace falta agregar un caso base para x = 2
// o alternativamente, cambiar el tipo de retorno de fib' a positivo (???)

// CONSULTA:
// Como falta un punto, x = 2, SMT prueba ese caso individualmente?
// fib' 1 + fib' 0 = 1 + 1 = 2 >= 2

(* Idem para la función factorial. *)
let rec fac' (x:nat) : y:pos{y >= x} = if x = 0 then 1 else x * fac' (x-1)
// En este caso tenemos las siguientes ecuaciones en la segunda branch:
// x >= 1 && fac' (x-1) >= x-1 >= 0
// por lo que no se puede probar que x * fac' (x-1) >= x >= 1
// (puede ser 0) y no es tan fácil darse cuenta para el SMT
// expandir una llamada recursiva y darse cuenta del caso problemático.
// Las dos soluciones posible son:
// 1- Agregar un caso base donde x = 1 devuelva 1
// 2- Refinar el tipo de retorno de fac' para que sea positivo

(* Defina la siguiente función que suma una lista de enteros. *)
val sum_int : list int -> int
let rec sum_int xs = match xs with
   | [] -> 0
   | x::xs' -> x + sum_int xs'

(* Defina la siguiente función que revierte una lista de enteros. *)
val rev_int : list int -> list int
let rec rev_int xs = match xs with
   | [] -> []
   | x::xs' -> (rev_int xs') @ [x]