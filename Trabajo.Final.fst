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
  : Lemma (x *. (y +. z) == (x *. y) +. (x *.z))
  = admit()

let mult_associates (a b c: real)
  : Lemma (a *. (b *. c) == (a *. b) *. c)
  = admit()

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

let c_is_equiv = EQ (==) (fun _ -> ()) (fun _ _ -> ()) (fun _ _ _ -> ())

let czero = 0.0R, 0.0R

let cadd (z w: complex) : complex =
  let a, b = z in
  let c, d = w in
    a +. c, b +. d

let cadd_identity (z: complex)
  : Lemma (cadd z czero == z) = ()

let cadd_associative (z w x: complex)
  : Lemma (cadd z (cadd w x) == cadd (cadd z w) x) = ()

let cadd_commutative (z w: complex)
  : Lemma (cadd z w == cadd w z) = ()

let cadd_congruent (x y z w: complex)
  : Lemma (requires x == z /\ y == w) (ensures cadd x y == cadd z w) = ()

let c_addition_is_comm_monoid: cm complex c_is_equiv
  = CM czero cadd cadd_identity cadd_associative cadd_commutative cadd_congruent

let cone = 1.0R, 0.0R

let cmult (z w: complex) : complex =
  let a, b = z in
  let c, d = w in
    a *. c -. b *. d,
    a *. d +. b *. c

let cmult_identity (z: complex)
  : Lemma (cmult z cone == z) = ()

let minus_is_neg (a b: real) : Lemma (a -. b == a +. neg b) = ()

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

let cmult_congruent (x y z w: complex)
  : Lemma (requires x == z /\ y == w) (ensures cmult x y == cmult z w) = ()

let c_multiplication_is_comm_monoid: cm complex c_is_equiv
  = CM cone cmult cmult_identity cmult_associative cadd_commutative cmult_congruent

let madd (#m #n: pos) (ma mb: matrix complex m n) = ma `matrix_add #_ #_ #m #n c_addition_is_comm_monoid` mb

let i: complex = 0.0R, 1.0R

let _prodexample =
  assert (creal (cmult i i) == neg 1.0R)

type qbit (#n: pos) = matrix complex (pow2 n) 1 // add constraints to make it a unit vector?

type operator (n:pos) = matrix complex (pow2 n) (pow2 n)

let square_generator (n:pos) = matrix_generator complex n n

let operator_generator (n:pos) = square_generator (pow2 n)

let mscalar (#n #m: pos) (a: complex) (ma: matrix complex n m)
  : matrix complex n m = init (fun i j -> a `cmult` (ijth ma i j))

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

let tensorv (#n #m: pos) (u: matrix complex n 1) (v: matrix complex m 1)
  : matrix complex (n * m) 1 = init (fun i _ ->
    let i1, i2 = i / m, i % m in
    (ijth u i1 0) `cmult` (ijth v i2 0))

let tensor (#m #n: pos) (u: operator n) (v: operator m) : operator (n + m) =
  init (tensor_generator u v)

let zero: qbit #1 = init (fun i _ -> if i = 0 then 1.0R, 0.0R else 0.0R, 0.0R)
let one: qbit #1  = init (fun i _ -> if i = 1 then 1.0R, 0.0R else 0.0R, 0.0R)

let invsqrt2: real = 1.0R /. sqrt_2

let csqrt2: complex = invsqrt2, 0.0R

let plus: qbit = (csqrt2 `mscalar` zero) `madd` (csqrt2 `mscalar` one)

let cconj (z: complex) : complex =
  let a, b = z in
    a, neg b

let conjugate (#m #n:pos) (ma: matrix complex m n) : matrix complex m n =
  init (fun i j -> cconj (ijth ma i j))

let transpose (#m #n:pos) (ma: matrix complex m n) : matrix complex n m =
  init (fun i j -> ijth ma j i)

type row (n:pos) = matrix complex 1 n
type col (n:pos) = matrix complex n 1

let row_vector (#n:pos) (op: operator n) : row n =
  init ((fun i _ -> ijth op 0 i) <: matrix_generator complex 1 n)

let col_vector (#n:pos) (op: operator n) : col n =
  init ((fun _ j -> ijth op j 0) <: matrix_generator complex n 1)

let inner_product (#n:pos) (r: row n) (c: col n) : complex =
  let m11 = matrix_mul c_addition_is_comm_monoid c_multiplication_is_comm_monoid r c in
  ijth m11 0 0

let mprod (#n #m #p: pos) (ma: matrix complex n m) (mb: matrix complex m p) : matrix complex n p
  = matrix_mul c_addition_is_comm_monoid c_multiplication_is_comm_monoid ma mb

let dagger (#n #m: pos) (ma: matrix complex n m) : matrix complex m n =
  transpose (conjugate ma)

assume val sqrt (x: real) : r:real{ r *. r == x }

let vnorm (#n:pos) (v: matrix complex (pow2 n) 1) : real =
  let vdag = dagger v in
  let vnorm2 = inner_product vdag v in
  sqrt (creal vnorm2)

let cabs (z: complex) : real =
  let a, b = z in
  sqrt (a *. a +. b *. b)

let vnorm_distributes_over_scalars (#n: pos) (a: complex) (v: matrix complex (pow2 n) 1)
  : Lemma (vnorm #n (a `mscalar` v) == (cabs a) *. (vnorm #n v))
= admit()

let unitary_matrices_preserve_norm_v (#n:pos) (op: operator n) (v: matrix complex (pow2 n) 1)
  : Prims.prop = vnorm (op `mprod` v) == vnorm v

let unitary_matrices_preserve_norm (#n:pos) (op: operator n)
  : Prims.prop = forall v. unitary_matrices_preserve_norm_v op v

let clona_todo_2 (u : operator 2) : prop =
  forall (psi phi:qbit #1). u `mprod` (psi `tensorv` phi) == psi `tensorv` psi

let tensor_distributes_over_sum (a: matrix complex 2 1) (b: matrix complex 2 1) (c: matrix complex 2 1)
  : Lemma (a `tensorv` (b `madd` c) == (a `tensorv` b) `madd` (a `tensorv` c))
= admit()

let tensor_distributes_over_scalar (b: matrix complex 2 1) (a: complex) (c: matrix complex 2 1)
  : Lemma (b `tensorv` (a `mscalar` c) == a `mscalar` (b `tensorv` c))
= admit()

let complexunit (z: complex) : Lemma (z == (1.0R, 0.0R) `cmult` z) = ()

let complexunitprod (ma: matrix complex 2 1) : Lemma (ma == (1.0R, 0.0R) `mscalar` ma)
  =
  // assert (ijth ma 0 0 == ijth ((1.0R, 0.0R) `mscalar` ma) 0 0);
  // assert (ijth ma 1 0 == ijth ((1.0R, 0.0R) `mscalar` ma) 1 0);
  // let _ = () <: squash (forall (i: under 2) (j: under 1). ijth ma i j == ijth ((1.0R, 0.0R) `mscalar` ma) i j) in
  // matrix_equiv_from_element_eq c_is_equiv ma ((1.0R, 0.0R) `mscalar` ma);
  admit()

let no_cloning_theorem_try (u: operator 2)
  : Lemma (requires clona_todo_2 u /\ unitary_matrices_preserve_norm u)
          (ensures False)
=
  assume (vnorm #2 (zero `tensorv` plus) == 1.0R);
  assume (vnorm #2 (zero `tensorv` zero) == 1.0R);
  assume (vnorm #2 (zero `tensorv` one) == 1.0R);
  assume (vnorm #2 (zero `tensorv` one) == 1.0R);
  assume (1.0R <> sqrt 2.0R);
  calc (==) {
    1.0R;
    == { () }
    vnorm #2 (zero `tensorv` plus);
    == { admit() }
    vnorm #2 (u `mprod` (zero `tensorv` plus));
    == { admit() }
    vnorm #2 (u `mprod` (zero `tensorv` ((csqrt2 `mscalar` zero) `madd` (csqrt2 `mscalar` one))));
    == { tensor_distributes_over_sum zero (csqrt2 `mscalar` zero) (csqrt2 `mscalar` one) }
    vnorm #2 (u `mprod` ((zero `tensorv` (csqrt2 `mscalar` zero)) `madd` (zero `tensorv` (csqrt2 `mscalar` one))));
    == { tensor_distributes_over_scalar zero csqrt2 zero; tensor_distributes_over_scalar zero csqrt2 one }
    vnorm #2 (u `mprod` ((csqrt2 `mscalar` (zero `tensorv` zero)) `madd` (csqrt2 `mscalar` (zero `tensorv` one))));
    == { admit() }
    vnorm #2 ((u `mprod` (csqrt2 `mscalar` (zero `tensorv` zero))) `madd` (u `mprod` (csqrt2 `mscalar` (zero `tensorv` one))));
    == { admit() }
    vnorm #2 ((csqrt2 `mscalar` (u `mprod` (zero `tensorv` zero))) `madd` (csqrt2 `mscalar` (u `mprod` (zero `tensorv` one))));
    == { () <: squash (clona_todo_2 u) }
    vnorm #2 ((csqrt2 `mscalar` (zero `tensorv` zero)) `madd` (csqrt2 `mscalar` (zero `tensorv` zero)));
    == { admit() }
    vnorm #2 (((2.0R, 0.0R) `cmult` csqrt2) `mscalar` (zero `tensorv` zero));
    == { admit() }
    vnorm #2 (csqrt2 `mscalar` (zero `tensorv` zero));
    == { vnorm_distributes_over_scalars #2 csqrt2 (zero `tensorv` zero) }
    (cabs csqrt2) *. vnorm #2 (zero `tensorv` zero);
    == { () }
    (cabs csqrt2) *. 1.0R;
    == { admit() }
    sqrt 2.0R;
  }

let no_cloning_theorem (#n:pos) (u: operator 2)
  : Lemma (requires unitary_matrices_preserve_norm u)
          (ensures ~ (clona_todo_2 u))
= Classical.move_requires no_cloning_theorem_try u
