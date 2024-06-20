module Trabajo.Final

open FStar.Mul
open FStar.Real
open FStar.Matrix
open FStar.Math.Lemmas
open FStar.Algebra.CommMonoid.Equiv

type complex: Type = real & real

let creal (z: complex) : real =
  let a, _ = z in a

let cimag (z: complex) : real =
  let _, b = z in b

let neg (a: real) : real =
  0.0R -. a

let lemma_neg_is_neg (a: real)
  : Lemma (requires a >. 0.0R) (ensures neg a <. 0.0R) = ()

let lemma_neg_is_opposite (a: real)
  : Lemma (neg a +. a == 0.0R) = ()

let ceq (z w: complex) : Prims.prop =
  let a, b = z in
  let c, d = w in
    a == c /\ b == d

let creflexive (z: complex)
  : Lemma (z `ceq` z) = ()

let csymmetric (z w: complex)
  : Lemma (requires z `ceq` w) (ensures w `ceq` z) = ()

let ctransitive (z w x: complex)
  : Lemma (requires z `ceq` w /\ w `ceq` x) (ensures z `ceq` x) = ()

let c_is_equiv = EQ ceq creflexive csymmetric ctransitive

let czero = 0.0R, 0.0R

let cadd (z w: complex) : complex =
  let a, b = z in
  let c, d = w in
    a +. c, b +. d

let cadd_identity (z: complex)
  : Lemma (cadd z czero `ceq` z) = ()

let cadd_associative (z w x: complex)
  : Lemma (cadd z (cadd w x) `ceq` cadd (cadd z w) x) = ()

let cadd_commutative (z w: complex)
  : Lemma (cadd z w `ceq` cadd w z) = ()

let cadd_congruent (x y z w: complex)
  : Lemma (requires x `ceq` z /\ y `ceq` w) (ensures cadd x y `ceq` cadd z w) = ()

let c_addition_is_comm_monoid: cm complex c_is_equiv
  = CM czero cadd cadd_identity cadd_associative cadd_commutative cadd_congruent

let cone = 1.0R, 0.0R

let cmult (z w: complex) : complex =
  let a, b = z in
  let c, d = w in
    a *. c -. b *. d,
    a *. d +. b *. c

let cmult_identity (z: complex)
  : Lemma (cmult z cone `ceq` z) = ()

let minus_is_neg (a b: real) : Lemma (a -. b == a +. neg b) = ()

// TODO: CHECK THIS!
let cmult_associative (z w x: complex)
  : Lemma (cmult z (cmult w x) `ceq` cmult (cmult z w) x) =
  let z1, z2 = z in
  let w1, w2 = w in
  let x1, x2 = x in

  let wx1 = w1 *. x1 -. w2 *. x2 in
  let wx2 = w1 *. x2 +. w2 *. x1 in
  let zw1 = z1 *. w1 -. z2 *. w2 in
  let zw2 = z1 *. w2 +. z2 *. w1 in

  let zwx1_first = zw1 *. x1 -. zw2 *. x2 in
  let zwx2_first = zw1 *. x2 +. zw2 *. x1 in
  let zwx1_second = z1 *. wx1 -. z2 *. wx2 in
  let zwx2_second = z1 *. wx2 +. z2 *. wx1 in

  calc (==) {
    zwx1_first;
    = { () }
    zw1 *. x1 -. zw2 *. x2;
    = { () }
    (z1 *. w1 -. z2 *. w2) *. x1 -. (z1 *. w2 +. z2 *. w1) *. x2;
    = { admit() }
    z1 *. w1 *. x1 -. z2 *. w2 *. x1 -. (z1 *. w2 *. x2 +. z2 *. w1 *. x2);
    = { () }
    z1 *. w1 *. x1 -. z2 *. w2 *. x1 -. z1 *. w2 *. x2 -. z2 *. w1 *. x2;
    = { admit() }
    z1 *. (w1 *. x1 -. w2 *. x2) -. z2 *. (w2 *. x1 +. w1 *. x2);
    = { () }
    z1 *. wx1 -. z2 *. wx2;
    = { () }
    zwx1_second;
  };

  calc (==) {
    zwx2_first;
    = { () }
    zw1 *. x2 +. zw2 *. x1;
    = { () }
    (z1 *. w1 -. z2 *. w2) *. x2 +. (z1 *. w2 +. z2 *. w1) *. x1;
    = { admit() }
    z1 *. w1 *. x2 -. z2 *. w2 *. x2 +. z1 *. w2 *. x1 +. z2 *. w1 *. x1;
    = { () }
    z1 *. w1 *. x2 -. z2 *. w2 *. x2 +. z1 *. w2 *. x1 +. z2 *. w1 *. x1;
    = { admit() }
    z1 *. (w1 *. x2 +. w2 *. x1) +. z2 *. (w2 *. x2 -. w1 *. x1);
    = { () }
    z1 *. wx2 +. z2 *. neg wx1;
    = { admit() }
    zwx2_second;
  }

let cmult_congruent (x y z w: complex)
  : Lemma (requires x `ceq` z /\ y `ceq` w) (ensures cmult x y `ceq` cmult z w) = ()

let c_multiplication_is_comm_monoid: cm complex c_is_equiv
  = CM cone cmult cmult_identity cmult_associative cadd_commutative cmult_congruent

let i: complex = 0.0R, 1.0R

let _prodexample =
  assert (creal (cmult i i) == neg 1.0R)

type qbit = matrix complex 2 1

type operator (n:pos) = matrix complex (pow2 n) (pow2 n)

let square_generator (n:pos) = matrix_generator complex n n

let operator_generator (n:pos) = square_generator (pow2 n)

let scalar_product_generator (#n: pos) (u: operator n) (a: complex) 
  : operator_generator n = fun i j -> a `cmult` (ijth u i j)

let mzero (n: pos) : operator n =
  init (fun i j -> (0.0R, 0.0R))

let mident (n: pos) : operator n =
  let gen: operator_generator n = fun i j -> if i = j then 1.0R, 0.0R else 0.0R, 0.0R in
  init gen

// Can't find this lemma in the math library
let nat_div (n:nat) (p:pos) : Lemma (n / p >= 0) = ()

let tensor_generator (#n #m: pos) (u: operator n) (v: operator m)
  : operator_generator (n + m) = fun i j ->

    calc (<) {
      i;
      < { () }
      pow2 (n + m);
      = { pow2_plus n m }
      pow2 n * pow2 m;
    };

    lemma_div_lt_nat i (n + m) m;
    lemma_div_lt_nat j (n + m) m;

    nat_div i (pow2 m);
    nat_div j (pow2 m);

    let i1, j1 = i / pow2 m, j / pow2 m in
    let i2, j2 = i % pow2 m, j % pow2 m in

    (ijth u i1 j1) `cmult` (ijth v i2 j2)

let tensor (#m #n: pos) (u: operator n) (v: operator m) : operator (n + m) =
  init (tensor_generator u v)

let zero: qbit = init (fun i _ -> if i = 0 then 1.0R, 0.0R else 0.0R, 0.0R)
let one: qbit = init (fun i _ -> if i = 1 then 1.0R, 0.0R else 0.0R, 0.0R)

let identity (n:pos): (operator n) = mident n
let paulix: (operator 1) = init (fun i j -> if i <> j then 1.0R, 0.0R else 0.0R, 0.0R)
let pauliy: (operator 1) = init (fun i j -> if i = 0 && j = 1 then 0.0R, 1.0R else if i = 1 && j = 0 then 0.0R, neg 1.0R else 0.0R, 0.0R)
let pauliz: (operator 1) = init (fun i j -> if i = 1 && j = 1 then 1.0R, 0.0R else if i = 0 && j = 0 then neg 1.0R, 0.0R else 0.0R, 0.0R)

let isqrt2: real = 1.0R /. sqrt_2

let hadamard: (operator 1) = init (fun i j -> if i = 1 && j = 1 then neg isqrt2, 0.0R else isqrt2, 0.0R)

let cconj (z: complex) : complex =
  let a, b = z in
    a, neg b

let conjugate (#n:pos) (op: operator n) : operator n =
  init (fun i j -> cconj (ijth op i j))

let transpose (#n:pos) (op: operator n) : operator n =
  init (fun i j -> ijth op j i)

type row (n:pos) = matrix complex 1 n
type col (n:pos) = matrix complex n 1

let row_vector (#n:pos) (op: operator n) : row n =
  init ((fun i _ -> ijth op 0 i) <: matrix_generator complex 1 n)

let col_vector (#n:pos) (op: operator n) : col n =
  init ((fun _ j -> ijth op j 0) <: matrix_generator complex n 1)

let inner_product (#n:pos) (r: row n) (c: col n) : complex =
  magic() // something something dot product

let operator_mult (#n: pos) (u: operator n) (v: operator n) : operator n
  = matrix_mul c_addition_is_comm_monoid c_multiplication_is_comm_monoid u v

let dagger (#n:pos) (op: operator n) : operator n =
  transpose (conjugate op)

let same_matrix (#m #n: pos) (ma mb: matrix complex m n) : Prims.prop =
  forall i j. ijth ma i j == ijth mb i j

let not_same_matrix (#m #n: pos) (ma mb: matrix complex m n) : Prims.prop =
  ~ (same_matrix ma mb)

let is_unitary (#n:pos) (op: operator n) : Prims.prop =
  let opdag = dagger op in
  let opopdag = op `operator_mult` opdag in
  let opdagop = opdag `operator_mult` op in
    opopdag `same_matrix` (identity n) /\ opdagop `same_matrix` (identity n)

let no_cloning_theorem (#n:pos) (u: operator n)
  : Lemma (requires is_unitary u)
          (ensures (exists (psi phi:qbit). u `operator_mult` (psi `tensor` phi) `not_same_matrix` (psi `tensor` psi)))
= admit()
// Conviene hacerlo así? O conviene hacer un ~ (exists u. forall psi phi. ...)?