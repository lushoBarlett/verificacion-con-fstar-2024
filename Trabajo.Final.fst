module Trabajo.Final

open FStar.Mul
open FStar.Real
open FStar.Matrix
open FStar.Math.Lemmas
open FStar.Algebra.CommMonoid.Equiv
open FStar.IntegerIntervals

// For some reason, neither of these proofs are accepted in this file,
// it only works in the module for the reals, but these are both axioms.
let mul_dist_left (x:real) (y:real) (z:real)
  : Lemma (x *. (y +. z) == (x *. y) +. (x *.z)) = admit()

let mult_associates (a b c: real)
  : Lemma (a *. (b *. c) == (a *. b) *. c) = admit()

type complex: Type = real & real

let creal (z: complex) : real =
  let a, _ = z in a

let cimag (z: complex) : real =
  let _, b = z in b

let neg (a: real) : real =
  0.0R -. a

let c_is_equiv = EQ (==) (fun _ -> ()) (fun _ _ -> ()) (fun _ _ _ -> ())

let czero = 0.0R, 0.0R

let cadd (z w: complex) : complex =
  let a, b = z in
  let c, d = w in
    a +. c, b +. d

let c_addition_is_comm_monoid: cm complex c_is_equiv
  = CM czero cadd (fun _ -> ()) (fun _ _ _ -> ()) (fun _ _ -> ()) (fun _ _ _ _ -> ())

let cone = 1.0R, 0.0R

let cmult (z w: complex) : complex =
  let a, b = z in
  let c, d = w in
    a *. c -. b *. d,
    a *. d +. b *. c

let neg_is_times_neg_one (a: real) : Lemma (neg a == neg 1.0R *. a)
= calc (==) {
    neg a;
    == { () }
    1.0R +. neg 1.0R +. neg a; // somehow the solver figures it out here
    == { () }
    neg 1.0R *. a;
  }

let neg_applies_once_left (a b: real) : Lemma (neg (a *. b) == neg a *. b)
= calc (==) {
    neg (a *. b);
    == { neg_is_times_neg_one (a *. b) }
    (neg 1.0R) *. (a *. b);
    == { mult_associates (neg 1.0R) a b }
    ((neg 1.0R) *. a) *. b;
    == { neg_is_times_neg_one a }
    neg a *. b;
  }

let neg_applies_once_right (a b: real) : Lemma (neg (a *. b) == a *. neg b)
= calc (==) {
    neg (a *. b);
    == { neg_applies_once_left b a }
    neg b *. a;
  }

let subtraction_is_neg_addition (a b: real) : Lemma (a -. b == a +. neg b) = ()

let mul_dist_right (x:real) (y:real) (z:real)
  : Lemma ((x +. y) *. z == (x *. z) +. (y *. z))
= calc (==) {
    (x +. y) *. z;
    == { mul_dist_left z x y }
    (x *. z) +. (y *. z);
  }

let cmult_associative (z w x: complex)
  : Lemma (cmult z (cmult w x) == cmult (cmult z w) x) =
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
    == { () }
    (z1 *. w1 -. z2 *. w2) *. x1 -. (z1 *. w2 +. z2 *. w1) *. x2;
    == { subtraction_is_neg_addition (z1 *. w1) (z2 *. w2) }
    (z1 *. w1 +. neg (z2 *. w2)) *. x1 -. (z1 *. w2 +. z2 *. w1) *. x2;
    == {
      mul_dist_right (z1 *. w1) (neg (z2 *. w2)) x1;
      mul_dist_right (z1 *. w2) (z2 *. w1) x2
    }
    z1 *. w1 *. x1 +. neg (z2 *. w2) *. x1 -. (z1 *. w2 *. x2 +. z2 *. w1 *. x2);
    == { neg_applies_once_left (z2 *. w2) x1 }
    z1 *. w1 *. x1 +. neg (z2 *. w2 *. x1) -. z1 *. w2 *. x2 -. z2 *. w1 *. x2;
    == {
      subtraction_is_neg_addition (z1 *. w1 *. x1) (z2 *. w2 *. x1);
      subtraction_is_neg_addition (z1 *. w2 *. x2) (z2 *. w1 *. x2)
    }
    z1 *. w1 *. x1 +. neg (z2 *. w2 *. x1) +. neg (z1 *. w2 *. x2) +. neg (z2 *. w1 *. x2);
    == { () }
    z1 *. w1 *. x1 +. neg (z1 *. w2 *. x2) +. neg (z2 *. w2 *. x1) +. neg (z2 *. w1 *. x2);
    == {
      mult_associates z1 w1 x1;
      mult_associates z1 w2 x2;
      mult_associates z2 w2 x1;
      mult_associates z2 w1 x2;
      neg_applies_once_right z1 (w2 *. x2);
      neg_applies_once_right z2 (w2 *. x1);
      neg_applies_once_right z2 (w1 *. x2)
    }
    z1 *. (w1 *. x1) +. z1 *. neg (w2 *. x2) +. z2 *. neg (w2 *. x1) +. z2 *. neg (w1 *. x2);
    == {
      mul_dist_left z1 (w1 *. x1) (neg (w2 *. x2));
      mul_dist_left z2 (neg (w2 *. x1)) (neg (w1 *. x2))
    }
    z1 *. (w1 *. x1 +. neg (w2 *. x2)) +. z2 *. (neg (w2 *. x1) +. neg (w1 *. x2));
    == {
      neg_applies_once_right z2 (w2 *. x1 +. w1 *. x2)
    }
    z1 *. (w1 *. x1 +. neg (w2 *. x2)) +. neg (z2 *. (w2 *. x1 +. w1 *. x2));
    == { () }
    zwx1_second;
  };

  calc (==) {
    zwx2_first;
    == { () }
    (z1 *. w1 -. z2 *. w2) *. x2 +. (z1 *. w2 +. z2 *. w1) *. x1;
    == { subtraction_is_neg_addition (z1 *. w1) (z2 *. w2) }
    (z1 *. w1 +. neg (z2 *. w2)) *. x2 +. (z1 *. w2 +. z2 *. w1) *. x1;
    == {
      mul_dist_right (z1 *. w1) (neg (z2 *. w2)) x2;
      mul_dist_right (z1 *. w2) (z2 *. w1) x1
    }
    z1 *. w1 *. x2 +. neg (z2 *. w2) *. x2 +. (z1 *. w2 *. x1 +. z2 *. w1 *. x1);
    == { neg_applies_once_left (z2 *. w2) x2 }
    z1 *. w1 *. x2 +. neg (z2 *. w2 *. x2) +. z1 *. w2 *. x1 +. z2 *. w1 *. x1;
    == {
      subtraction_is_neg_addition (z1 *. w1 *. x2) (z2 *. w2 *. x2);
      subtraction_is_neg_addition (z1 *. w2 *. x1) (z2 *. w1 *. x1)
    }
    z1 *. w1 *. x2 +. neg (z2 *. w2 *. x2) +. z1 *. w2 *. x1 +. z2 *. w1 *. x1;
    == { () }
    z1 *. w1 *. x2 +. z1 *. w2 *. x1 +. neg (z2 *. w2 *. x2) +. z2 *. w1 *. x1;
    == {
      mult_associates z1 w1 x2;
      mult_associates z1 w2 x1;
      mult_associates z2 w2 x2;
      mult_associates z2 w1 x1;
      neg_applies_once_right z2 (w2 *. x2)
    }
    z1 *. (w1 *. x2) +. z1 *. (w2 *. x1) +. z2 *. neg (w2 *. x2) +. z2 *. (w1 *. x1);
    == {
      mul_dist_left z1 (w1 *. x2) (w2 *. x1);
      mul_dist_left z2 (neg (w2 *. x2)) (w1 *. x1)
    }
    z1 *. (w1 *. x2 +. w2 *. x1) +. z2 *. (neg (w2 *. x2) +. w1 *. x1);
    == { () }
    zwx2_second;
  }

let c_multiplication_is_comm_monoid: cm complex c_is_equiv
  = CM cone cmult (fun _ -> ()) cmult_associative (fun _ _ -> ()) (fun _ _ _ _ -> ())

let madd (#m #n: pos) (ma mb: matrix complex m n) = ma `matrix_add #_ #_ #m #n c_addition_is_comm_monoid` mb

type qbit (#n: pos) = matrix complex (pow2 n) 1

type operator (n:pos) = matrix complex (pow2 n) (pow2 n)

let mscalar (#n #m: pos) (a: complex) (ma: matrix complex n m)
  : matrix complex n m = init (fun i j -> a `cmult` (ijth ma i j))

let tensorv (#n #m: pos) (u: matrix complex n 1) (v: matrix complex m 1)
  : matrix complex (n * m) 1 = init (fun i _ ->
    let i1, i2 = i / m, i % m in
    (ijth u i1 0) `cmult` (ijth v i2 0))

let zero: qbit #1 = init (fun i _ -> if i = 0 then 1.0R, 0.0R else 0.0R, 0.0R)
let one: qbit #1  = init (fun i _ -> if i = 1 then 1.0R, 0.0R else 0.0R, 0.0R)

let invsqrt2: real = 1.0R /. sqrt_2

let cinvsqrt2: complex = invsqrt2, 0.0R

let csqrt2: complex = sqrt_2, 0.0R

let plus: qbit = (cinvsqrt2 `mscalar` zero) `madd` (cinvsqrt2 `mscalar` one)

let cconj (z: complex) : complex =
  let a, b = z in
    a, neg b

let conjugate (#m #n:pos) (ma: matrix complex m n) : matrix complex m n =
  init (fun i j -> cconj (ijth ma i j))

let transpose (#m #n:pos) (ma: matrix complex m n) : matrix complex n m =
  init (fun i j -> ijth ma j i)

let row_vector (#n:pos) (op: operator n) : matrix complex 1 (pow2 n) =
  init ((fun i _ -> ijth op 0 i) <: matrix_generator complex 1 (pow2 n))

let col_vector (#n:pos) (op: operator n) : matrix complex (pow2 n) 1 =
  init ((fun _ j -> ijth op j 0) <: matrix_generator complex (pow2 n) 1)

let inner_product (#n:pos) (r: matrix complex 1 n) (c: matrix complex n 1) : complex =
  let m11 = matrix_mul c_addition_is_comm_monoid c_multiplication_is_comm_monoid r c in
  ijth m11 0 0

let mprod (#n #m #p: pos) (ma: matrix complex n m) (mb: matrix complex m p) : matrix complex n p
  = matrix_mul c_addition_is_comm_monoid c_multiplication_is_comm_monoid ma mb

let dagger (#n #m: pos) (ma: matrix complex n m) : matrix complex m n =
  transpose (conjugate ma)

assume val sqrt (x: real) : r:real{ r *. r == x }

let norm (#n:pos) (v: matrix complex n 1) : real =
  let qdag = dagger v in
  let norm2 = inner_product qdag v in
  sqrt (creal norm2)

let cabs (z: complex) : real =
  let a, b = z in
  sqrt (a *. a +. b *. b)

let vnorm_distributes_over_scalars (#n: pos) (a: complex) (v: qbit #n)
  : Lemma (norm (a `mscalar` v) == (cabs a) *. (norm v)) = admit()

let unitary_matrices_preserve_norm (#n: pos) (op: operator n)
  : prop = forall v. norm (op `mprod` v) == norm v

let clona_todo_2 (u: operator 2) : prop =
  forall (psi phi: qbit #1). u `mprod` (psi `tensorv` phi) == psi `tensorv` psi

let tensor_distributes_over_sum (#n: pos) (v: qbit #n) (w: qbit #n) (x: qbit #n)
  : Lemma (v `tensorv` (w `madd` x) == (v `tensorv` w) `madd` (v `tensorv` x)) = admit()

let tensor_distributes_over_scalar (#n: pos) (a: complex) (v: qbit #n) (c: qbit #n)
  : Lemma (v `tensorv` (a `mscalar` c) == a `mscalar` (v `tensorv` c)) = admit()

let product_is_linear_1 (#n: pos) (u: operator n) (v: qbit #n) (w: qbit #n)
  : Lemma (u `mprod` (v `madd` w) == (u `mprod` v) `madd` (u `mprod` w)) = admit()

let product_is_linear_2 (#n: pos) (u: operator n) (a: complex) (v: qbit #n)
  : Lemma (u `mprod` (a `mscalar` v) == a `mscalar` (u `mprod` v)) = admit()

let product_distributes_over_scalar_sum (#n: pos) (a b: complex) (v: qbit #n)
  : Lemma ((a `mscalar` v) `madd` (b `mscalar` v) == (a `cadd` b) `mscalar` v) = admit()

let no_cloning_theorem_contradiction (u: operator 2)
  : Lemma (requires clona_todo_2 u /\ unitary_matrices_preserve_norm u)
          (ensures False)
=
  assume (norm (zero `tensorv` plus) == 1.0R);
  assume (norm (zero `tensorv` zero) == 1.0R);
  assume (norm (zero `tensorv` one) == 1.0R);
  assume (norm (zero `tensorv` one) == 1.0R);
  assume (1.0R <> sqrt 2.0R);
  assume (cinvsqrt2 `cadd` cinvsqrt2 == csqrt2);
  assume (cabs csqrt2 == sqrt 2.0R);
  calc (==) {
    1.0R;

    == { () }
    norm (zero `tensorv` plus);

    == { () <: squash (unitary_matrices_preserve_norm u) }
    norm (u `mprod` (zero `tensorv` plus));

    == { () }
    norm (u `mprod` (zero `tensorv` ((cinvsqrt2 `mscalar` zero) `madd` (cinvsqrt2 `mscalar` one))));

    == { tensor_distributes_over_sum zero (cinvsqrt2 `mscalar` zero) (cinvsqrt2 `mscalar` one) }
    norm (u `mprod` ((zero `tensorv` (cinvsqrt2 `mscalar` zero)) `madd` (zero `tensorv` (cinvsqrt2 `mscalar` one))));

    == {
      tensor_distributes_over_scalar cinvsqrt2 zero zero;
      tensor_distributes_over_scalar cinvsqrt2 zero one
    }
    norm (u `mprod` ((cinvsqrt2 `mscalar` (zero `tensorv` zero)) `madd` (cinvsqrt2 `mscalar` (zero `tensorv` one))));

    == { product_is_linear_1 u (cinvsqrt2 `mscalar` (zero `tensorv` zero)) (cinvsqrt2 `mscalar` (zero `tensorv` one)) }
    norm ((u `mprod` (cinvsqrt2 `mscalar` (zero `tensorv` zero))) `madd` (u `mprod` (cinvsqrt2 `mscalar` (zero `tensorv` one))));

    == {
      product_is_linear_2 u cinvsqrt2 (zero `tensorv` zero);
      product_is_linear_2 u cinvsqrt2 (zero `tensorv` one)
    }
    norm ((cinvsqrt2 `mscalar` (u `mprod` (zero `tensorv` zero))) `madd` (cinvsqrt2 `mscalar` (u `mprod` (zero `tensorv` one))));

    == { () <: squash (clona_todo_2 u) }
    norm ((cinvsqrt2 `mscalar` (zero `tensorv` zero)) `madd` (cinvsqrt2 `mscalar` (zero `tensorv` zero)));

    == { product_distributes_over_scalar_sum #2 cinvsqrt2 cinvsqrt2 (zero `tensorv` zero) }
    norm ((cinvsqrt2 `cadd` cinvsqrt2) `mscalar` (zero `tensorv` zero));

    == { () }
    norm (csqrt2 `mscalar` (zero `tensorv` zero));

    == { vnorm_distributes_over_scalars #2 csqrt2 (zero `tensorv` zero) }
    (cabs csqrt2) *. norm (zero `tensorv` zero);

    == { () }
    (cabs csqrt2) *. 1.0R;

    == { () }
    sqrt 2.0R;
  }

let no_cloning_theorem (#n:pos) (u: operator 2)
  : Lemma (requires unitary_matrices_preserve_norm u)
          (ensures ~ (clona_todo_2 u))
= Classical.move_requires no_cloning_theorem_contradiction u
