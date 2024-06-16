module Trabajo.Final

open FStar.Mul
open FStar.Real
open FStar.Matrix

type complex: Type = real & real

let cprod (z w: complex) : complex =
  // (a + bi)(c + di) = ac + adi + bci + bdi^2 = ac - bd + (ad + bc)i
  let a, b = z in
  let c, d = w in
    a *. c -. b *. d,
    a *. d +. b *. c

let i: complex = 0.0R, 1.0R

let creal (z: complex) : real =
  let a, _ = z in a

let cimag (z: complex) : real =
  let _, b = z in b

let neg (a: real) : real =
  0.0R -. a

let _prodexample =
  assert (creal (cprod i i) = neg 1.0R)

type qbit = matrix complex 2 1

let matrix_scalar_product_generator (#m #n: pos) (ma: matrix complex m n) (a: complex) 
  : matrix_generator complex m n = fun i j -> a `cprod` (ijth ma i j)

let mzero (m n: pos) : matrix complex m n =
  init (fun i j -> (0.0R, 0.0R))

let mident (m n: pos) : matrix complex m n =
  let gen: matrix_generator complex m n = fun i j -> if i = j then 1.0R, 0.0R else 0.0R, 0.0R in
  init gen

let matrix_tensor_generator (#m #n #p #q: pos) (ma: matrix complex m n) (mb: matrix complex p q)
  : matrix_generator complex (m * p) (n * q) = fun i j ->
    let i1, i2 = i / p, i % p in
    let j1, j2 = j / q, j % q in
    (ijth ma i1 j1) `cprod` (ijth mb i2 j2)

let tensor (#m #n #p #q: pos) (ma: matrix complex m n) (mb: matrix complex p q) : matrix complex (m * p) (n * q) =
  init (matrix_tensor_generator ma mb)

let zero: qbit = init (fun i _ -> if i = 0 then 1.0R, 0.0R else 0.0R, 0.0R)
let one: qbit = init (fun i _ -> if i = 1 then 1.0R, 0.0R else 0.0R, 0.0R)

let _tensorexample =
  let zeroone = zero `tensor` zero
  in
    assert (ijth zeroone 0 0 = (1.0R, 0.0R));
    assert (ijth zeroone 1 0 = (0.0R, 0.0R));
    assert (ijth zeroone 2 0 = (0.0R, 0.0R));
    assert (ijth zeroone 3 0 = (0.0R, 0.0R))

type operator = matrix complex 2 2

let identity: operator = mident 2 2
let paulix: operator = init (fun i j -> if i <> j then 1.0R, 0.0R else 0.0R, 0.0R)
let pauliy: operator = init (fun i j -> if i = 0 && j = 1 then 0.0R, 1.0R else if i = 1 && j = 0 then 0.0R, neg 1.0R else 0.0R, 0.0R)
let pauliz: operator = init (fun i j -> if i = 1 && j = 1 then 1.0R, 0.0R else if i = 0 && j = 0 then neg 1.0R, 0.0R else 0.0R, 0.0R)

let isqrt2: real = 1.0R /. sqrt_2

let hadamard: operator = init (fun i j -> if i = 1 && j = 1 then neg isqrt2, 0.0R else isqrt2, 0.0R)

let cconj (z: complex) : complex =
  let a, b = z in
    a, neg b

let conjugate (op: operator) : operator =
  init (fun i j -> cconj (ijth op i j))

let transpose (op: operator) : operator =
  init (fun i j -> ijth op j i)

assume
val matrix_mult (#m #n #p: pos) (ma: matrix complex m n) (mb: matrix complex n p) : matrix complex m p

let dagger (op: operator) : operator =
  transpose (conjugate op)

let is_same_matrix (#m #n: pos) (ma mb: matrix complex m n) : Prims.prop =
  forall i j. ijth ma i j = ijth mb i j

let is_not_same_matrix (#m #n: pos) (ma mb: matrix complex m n) : Prims.prop =
  ~ (is_same_matrix ma mb)

let is_unitary (op: operator) : Prims.prop =
  let opdag = dagger op in
  let opopdag = op `matrix_mult` opdag in
  let opdagop = opdag `matrix_mult` op in
    opopdag `is_same_matrix` mident 2 2 /\ opdagop `is_same_matrix` mident 2 2

let no_cloning_theorem (u: operator) (psi phi: qbit)
  : Lemma (requires is_unitary u)
          (ensures (u `matrix_mult` (psi `tensor` phi)) `is_not_same_matrix` (psi `tensor` psi)) = admit()