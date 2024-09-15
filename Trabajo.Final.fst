module Trabajo.Final

module SP = FStar.Seq.Permutation
module SB = FStar.Seq

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

let mequals (#m #n: pos) (ma mb: matrix complex m n) = (matrix_equiv c_is_equiv m n).eq ma mb

let madd (#m #n: pos) (ma mb: matrix complex m n) = ma `matrix_add #_ #_ #m #n c_addition_is_comm_monoid` mb

type qbit (n: pos) = matrix complex (pow2 n) 1

type operator (n:pos) = matrix complex (pow2 n) (pow2 n)

let mscalar (#n #m: pos) (a: complex) (ma: matrix complex n m)
  : matrix complex n m = init (fun i j -> a `cmult` (ijth ma i j))

let tensorv (#n #m: pos) (u: matrix complex n 1) (v: matrix complex m 1)
  : matrix complex (n * m) 1 = init (fun i _ ->
    let i1, i2 = i / m, i % m in
    (ijth u i1 0) `cmult` (ijth v i2 0))

let ijth_tensorv (#n #m: pos) (u: matrix complex n 1) (v: matrix complex m 1) (i: under (n * m)) (j: under 1)
  : Lemma (ijth (u `tensorv` v) i j == (ijth u (i / m) 0) `cmult` (ijth v (i % m) 0)) = ()

let zero: qbit 1 = init (fun i _ -> if i = 0 then 1.0R, 0.0R else 0.0R, 0.0R)
let one: qbit 1  = init (fun i _ -> if i = 1 then 1.0R, 0.0R else 0.0R, 0.0R)

let invsqrt2: real = 1.0R /. sqrt_2

let cinvsqrt2: complex = invsqrt2, 0.0R

let csqrt2: complex = sqrt_2, 0.0R

let plus: qbit 1 = (cinvsqrt2 `mscalar` zero) `madd` (cinvsqrt2 `mscalar` one)

let cconj (z: complex) : complex = let a, b = z in a, neg b

let conjugate (#m #n:pos) (ma: matrix complex m n)
  : r:(matrix complex m n){ forall i j. ijth r i j == cconj (ijth ma i j) }
= init ((fun i j -> cconj (ijth ma i j)) <: matrix_generator complex m n)

let transpose (#m #n:pos) (ma: matrix complex m n)
  : r:(matrix complex n m){ forall i j. ijth r j i == ijth ma i j }
= init (fun i j -> ijth ma j i)

let mprod (#n #m #p: pos) (ma: matrix complex n m) (mb: matrix complex m p) : matrix complex n p
  = matrix_mul c_addition_is_comm_monoid c_multiplication_is_comm_monoid ma mb

let inner_product (#n:pos) (r: matrix complex 1 n) (c: matrix complex n 1) : complex =
  ijth (mprod r c) 0 0

let dagger (#n #m: pos) (ma: matrix complex n m) : matrix complex m n =
  transpose (conjugate ma)

assume val sqrt (x: real{x >=. 0.0R}) : r:real{ r >=. 0.0R /\ r *. r == x }

let cabs (z: complex) : real =
  let a, b = z in
  sqrt (a *. a +. b *. b)

let is_real_nonneg (c:complex) : prop =
  creal c >=. 0.0R  /\ cimag c == 0.0R

let complex_times_conjugate_is_abs_squared (z: complex)
  : Lemma (creal (z `cmult` cconj z) == cabs z *. cabs z)
= let a, b = z in
  calc (==) {
    creal (z `cmult` (cconj z));
    == { () }
    a *. a -. b *. neg b;
    == { neg_applies_once_right b b }
    a *. a -. neg (b *. b);
    == { () }
    a *. a +. b *. b;
    == { () }
    cabs z *. cabs z;
  }

let __difference_of_squares (a b: real)
  : Lemma (a *. a -. b *. b == (a +. b) *. (a -. b))
= calc (==) {
    a *. a +. a *. b -. b *. b -. a *. b;
    == {
      neg_applies_once_left b a;
      neg_applies_once_right b b
    }
    a *. a +. a *. b +. neg b *. b +. neg b *. a;
    == {
      mul_dist_left a a b;
      mul_dist_left (neg b) b a
    }
    a *. (a +. b) +. neg b *. (a +. b);
    == {
      mul_dist_right a (neg b) (a +. b)
    }
    (a -. b) *. (a +. b);
  }

let root_of_squared (x: real{x >=. 0.0R}) : Lemma (sqrt (x *. x) == x)
= let r = sqrt (x *. x) in
  assert (r *. r -. x *. x == 0.0R);
  __difference_of_squares r x;
  assert (r -. x == 0.0R)

let complex_times_conjugate_is_real_nonneg (z: complex)
  : Lemma (is_real_nonneg (z `cmult` cconj z))
= complex_times_conjugate_is_abs_squared z;
  let a, b = z in
  calc (==) {
    cimag (z `cmult` (cconj z));
    == { () }
    a *. neg b +. b *. a;
    == { neg_applies_once_left b a }
    neg (a *. b) +. b *. a;
    == { () }
    0.0R;
  }

let downgrade_left_to_reals (z w: complex)
  : Lemma (requires is_real_nonneg z)
          (ensures creal (z `cmult` w) == creal z *. creal w) = ()

let downgrade_right_to_reals (z w: complex)
  : Lemma (requires is_real_nonneg z)
          (ensures creal (z `cmult` w) == creal z *. creal w) = ()

let conj_vec (#n:pos) (v : SB.lseq complex n) : SB.lseq complex n =
  SB.init n (fun i -> cconj (SB.index v i))

let __seq_of_products_conj_self (#n: pos) (v: SB.lseq complex n) (i: under n)
  : Lemma (is_real_nonneg (SB.index (seq_of_products c_multiplication_is_comm_monoid (conj_vec v) v) i))
= let vi = SB.index v i in
  calc (==) {
    SB.index (seq_of_products c_multiplication_is_comm_monoid (conj_vec v) v) i;
    == { () }
    SB.index (conj_vec v) i `cmult` vi;
    == { () }
    cconj vi `cmult` vi;
    == { assert (forall z w. z `cmult` w == w `cmult` z) } // why commutation so hard
    vi `cmult` cconj vi;
  };
  complex_times_conjugate_is_real_nonneg vi

let __foldm_stable (#a:Type) (pred : a -> prop) (s : SB.seq a)
  (#eq : equiv a) (c : cm a eq)
  : Lemma (requires pred c.unit /\ (forall x y. pred x /\ pred y ==> pred (c.mult x y)))
          (ensures pred (SP.foldm_snoc c s))
  = admit()

let __foldm_add_nonneg (#n : pos) (s : SB.lseq complex n)
  : Lemma (requires forall (i: under n). is_real_nonneg (SB.index s i))
          (ensures is_real_nonneg (SP.foldm_snoc c_addition_is_comm_monoid s))
  = __foldm_stable is_real_nonneg s c_addition_is_comm_monoid

let __inner_conj_vec (#n: pos) (v: SB.lseq complex n)
  : Lemma (ensures is_real_nonneg (dot c_addition_is_comm_monoid c_multiplication_is_comm_monoid (conj_vec v) v))
  // so much gymnastics for this, assert forall didn't work
  = let proof (i: under n)
      : Lemma (is_real_nonneg (SB.index (conj_vec v) i `cmult` SB.index v i))
      = __seq_of_products_conj_self v i in
    Classical.forall_intro proof;
    __foldm_add_nonneg #n (seq_of_products c_multiplication_is_comm_monoid (conj_vec v) v)

let row_dagger_is_conj_col (#m #n:pos) (mm: matrix complex m n) (i: under n)
  : Lemma (ensures row (dagger mm) i == conj_vec #m (col mm i))
  = assert (row (dagger mm) i `Seq.equal` conj_vec #m (col mm i))

let __inner_product_with_dagger_is_real_and_positive
  (#m #n:pos)
  (mm: matrix complex m n)
  (i : nat{i < n})
  : Lemma (ensures is_real_nonneg (ijth (mprod (dagger mm) mm) i i))
= calc (==) {
    ijth (mprod (dagger mm) mm) i i <: complex;
    == { matrix_mul_ijth c_addition_is_comm_monoid c_multiplication_is_comm_monoid (dagger mm) mm i i }
    dot c_addition_is_comm_monoid c_multiplication_is_comm_monoid (row (dagger mm) i) (col mm i);
    == {}
    SP.foldm_snoc c_addition_is_comm_monoid
      (seq_of_products c_multiplication_is_comm_monoid
        (row (dagger mm) i)
        (col mm i));
    == { row_dagger_is_conj_col mm i }
    SP.foldm_snoc c_addition_is_comm_monoid
      (seq_of_products c_multiplication_is_comm_monoid
        (conj_vec #m (col mm i))
        (col mm i));
  };
  Classical.forall_intro (__seq_of_products_conj_self #m (col mm i));
  __foldm_add_nonneg #m (seq_of_products c_multiplication_is_comm_monoid (conj_vec #m (col mm i)) (col mm i))

let inner_product_with_dagger_is_real_and_positive (#n:pos) (m: matrix complex n 1)
  : Lemma (ensures creal (inner_product (dagger m) m) >=. 0.0R)
=
  let dm = dagger m in
  calc (>=.) {
    creal (inner_product dm m);
    == { () }
    creal (ijth (mprod dm m) 0 0);
    >=. { __inner_product_with_dagger_is_real_and_positive m 0 }
    0.0R;
  }

let norm (#n:pos) (v: matrix complex n 1): x:real{x >=. 0.0R} =
  let qdag = dagger v in
  let norm2 = inner_product qdag v in
  inner_product_with_dagger_is_real_and_positive #n v;
  sqrt (creal norm2)

#set-options "--query_stats"

let transpose_scalar (#n: pos) (a: complex) (v: qbit n)
  : Lemma ((transpose (a `mscalar` v)) `mequals` (a `mscalar` (transpose v)))

= let proof (i: under 1) (j: under (pow2 n))
    : Lemma (ijth (transpose (a `mscalar` v)) i j == ijth (a `mscalar` (transpose v)) i j) = () in

  matrix_equiv_from_proof c_is_equiv (transpose (a `mscalar` v)) (a `mscalar` (transpose v)) proof

let ijth_conjugate (#m #n: pos) (ma: matrix complex m n) (i: under m) (j: under n)
  : Lemma (ijth (conjugate ma) i j == cconj (ijth ma i j)) = ()

let ijth_scalar (#m #n: pos) (a: complex) (ma: matrix complex m n) (i: under m) (j: under n)
  : Lemma (ijth (a `mscalar` ma) i j == a `cmult` (ijth ma i j)) = ()

let cconj_cmult (z w: complex)
  : Lemma (cconj (z `cmult` w) == cconj z `cmult` cconj w)
= let a, b = z in
  let c, d = w in
  calc (==) {
    cconj (z `cmult` w);
    == { () }
    cconj (
      a *. c -. b *. d,
      a *. d +. b *. c
    );
    == { () }
    a *. c -. b *. d,
    neg (a *. d +. b *. c);
    == { () }
    a *. c -. b *. d,
    neg (a *. d) +. neg(b *. c);
    == {
      neg_applies_once_right a d;
      neg_applies_once_left b c
    }
    a *. c -. b *. d,
    a *. neg d +. neg b *. c;
    == { () }
    a *. c +. neg (b *. d),
    a *. neg d +. neg b *. c;
    == { neg_applies_once_left b d }
    a *. c +. neg (neg (neg b *. d)),
    a *. neg d +. neg b *. c;
    == { neg_applies_once_right (neg b) d }
    a *. c -. neg b *. neg d,
    a *. neg d +. neg b *. c;
    == { () }
    (a, neg b) `cmult` (c, neg d);
    == { () }
    cconj z `cmult` cconj w;
  }

let conjugate_scalar (#n: pos) (a: complex) (v: qbit n)
  : Lemma (conjugate (a `mscalar` v) `mequals` (cconj a `mscalar` conjugate v))
= let proof (i: under (pow2 n)) (j: under 1)
    : Lemma (ijth (conjugate (a `mscalar` v)) i j == ijth ((cconj a) `mscalar` (conjugate v)) i j)
  = calc (==) {
      ijth (conjugate (a `mscalar` v)) i j <: complex;
      == { ijth_conjugate (a `mscalar` v) i j }
      cconj (ijth (a `mscalar` v) i j) <: complex;
      == { ijth_scalar a v i j }
      cconj (a `cmult` (ijth v i j)) <: complex;
      == { cconj_cmult a (ijth v i j) }
      cconj a `cmult` cconj (ijth v i j) <: complex;
      == { ijth_conjugate v i j }
      cconj a `cmult` ijth (conjugate v) i j <: complex;
      == { ijth_scalar (cconj a) (conjugate v) i j }
      ijth ((cconj a) `mscalar` (conjugate v)) i j <: complex;
    }
  in
  matrix_equiv_from_proof c_is_equiv (conjugate (a `mscalar` v)) (cconj a `mscalar` conjugate v) proof

let provable_equality_implies_equivalence (#m #n: pos) (ma : matrix complex m n)
  : Lemma (ensures ma `mequals` ma) [SMTPat (ma `mequals` ma)]
= let proof (i: under m) (j: under n)
    : Lemma (ijth ma i j == ijth ma i j) = () in
  matrix_equiv_from_proof c_is_equiv ma ma proof

let provable_equality_implies_equivalence2 (#m #n: pos) (ma mb: matrix complex m n)
  : Lemma (requires ma == mb) (ensures ma `mequals` mb)
= ()

// LB: el módulo de matrices cuenta con una relación de equivalencia
// pero no encontré la forma de transformar eso en igualdad demostrable
// así que me inventé este hack para usarlo igual.

// GM: ok asumir
let matrix_ext (#m #n: pos) (ma mb : matrix complex m n)
  : Lemma (requires forall i j. ijth ma i j == ijth mb i j)
          (ensures ma == mb)
  = admit()

let equivalence_implies_provable_equality (#m #n: pos) (ma mb: matrix complex m n)
  : Lemma (requires ma `mequals` mb) (ensures ma == mb)
= let aux (i:under m) (j: under n) : Lemma (ijth ma i j == ijth mb i j) =
    matrix_equiv_ijth c_is_equiv ma mb i j
  in
  Classical.forall_intro_2 aux;
  matrix_ext ma mb

let dagger_scalar (#n: pos) (a: complex) (v: qbit n)
  : Lemma ((dagger (a `mscalar` v)) == (cconj a `mscalar` dagger v))
= calc (==) {
    dagger (a `mscalar` v);
    == { () }
    transpose (conjugate (a `mscalar` v));
    == {
      conjugate_scalar a v;
      equivalence_implies_provable_equality (conjugate (a `mscalar` v)) ((cconj a) `mscalar` conjugate v)
    }
    transpose ((cconj a) `mscalar` conjugate v);
    == {
      transpose_scalar (cconj a) (conjugate v);
      equivalence_implies_provable_equality
        (transpose ((cconj a) `mscalar` conjugate v))
        (cconj a `mscalar` transpose (conjugate v))
    }
    (cconj a `mscalar` transpose (conjugate v));
    == { () }
    cconj a `mscalar` dagger v;
  }

// Because of technicalities in our inner_product definition, it is actually antilinear in the left argument
// because the vector must be passed as conjugated, which means the scalar comes conjugated when it actually isn't.
let inner_product_left_linearity (#n: pos) (a: complex) (u: matrix complex 1 n) (v: matrix complex n 1)
  : Lemma (inner_product (cconj a `mscalar` u) v == a `cmult` inner_product u v) = admit()

let inner_product_right_linearity (#n: pos) (a: complex) (u: matrix complex 1 n) (v: matrix complex n 1)
  : Lemma (inner_product u (a `mscalar` v) == cconj a `cmult` inner_product u v) = admit()

let vnorm_distributes_over_scalars (#n: pos) (a: complex) (v: qbit n)
  : Lemma (norm (a `mscalar` v) == (cabs a) *. (norm v))
= //let test: x:real{x >=. 0.0R} = creal (inner_product (dagger (a `mscalar` v)) (a `mscalar` v)) in
  admit();
  calc (==) {
    norm (a `mscalar` v) <: x:real{x >=. 0.0R};
    == { () }
    sqrt (creal (inner_product (dagger (a `mscalar` v)) (a `mscalar` v)) <: x:real{x >=. 0.0R});
    == { dagger_scalar a v }
    sqrt (creal (inner_product (cconj a `mscalar` dagger v) (a `mscalar` v))) <: x:real{x >=. 0.0R};
    == {
      inner_product_left_linearity (cconj a) (dagger v) (a `mscalar` v);
      inner_product_right_linearity a (dagger v) v
    }
    sqrt (creal (a `cmult` (cconj a `cmult` (inner_product (dagger v) v)))) <: x:real{x >=. 0.0R};
    == { cmult_associative a (cconj a) (inner_product (dagger v) v) }
    sqrt (creal ((a `cmult` cconj a) `cmult` (inner_product (dagger v) v))) <: x:real{x >=. 0.0R};
    == { complex_times_conjugate_is_real_nonneg a }
    sqrt (creal ((a `cmult` cconj a) `cmult` (inner_product (dagger v) v))) <: x:real{x >=. 0.0R};
  };
  admit()

let is_isometry (#n: pos) (op: operator n)
  : prop = forall v. norm (op `mprod` v) == norm v

let clona_todo_2 (u: operator 2) : prop =
  forall (psi phi: qbit 1). u `mprod` (psi `tensorv` phi) == psi `tensorv` psi

let ijth_madd (#m #n: pos) (ma mb: matrix complex m n) (i: under m) (j: under n)
  : Lemma (ijth (ma `madd` mb) i j == ijth ma i j `cadd` ijth mb i j) = ()

let cmult_distributes_over_cadd_left (z w x: complex)
  : Lemma (z `cmult` (w `cadd` x) == (z `cmult` w) `cadd` (z `cmult` x))
= let za, zb = z in
  let wa, wb = w in
  let xa, xb = x in
  calc (==) {
    z `cmult` (w `cadd` x);
    == { neg_applies_once_left zb (wb +. xb) }
    za *. (wa +. xa) +. (neg zb) *. (wb +. xb),
    za *. (wb +. xb) +. zb *. (wa +. xa);
    == {
      mul_dist_left za wa xa;
      mul_dist_left (neg zb) wb xb;
      mul_dist_left za wb xb;
      mul_dist_left zb wa xa
    }
    za *. wa +. za *. xa +. (neg zb) *. wb +. (neg zb) *. xb,
    za *. wb +. za *. xb +. zb *. wa +. zb *. xa;
    == { neg_applies_once_left zb wb; neg_applies_once_left zb xb }
    za *. wa -. zb *. wb +. za *. xa -. zb *. xb,
    za *. wb +. zb *. wa +. za *. xb +. zb *. xa;
    == {
      mul_dist_left za wa xa;
      mul_dist_left (neg zb) wb xb;
      mul_dist_left za wb xb;
      mul_dist_left zb wa xa
    }
    (z `cmult` w) `cadd` (z `cmult` x);
  }

let cmult_distributes_over_cadd_right (z w x: complex)
  : Lemma ((w `cadd` x) `cmult` z == (w `cmult` z) `cadd` (x `cmult` z))
= calc (==) {
    (w `cadd` x) `cmult` z;
    == { () }
    z `cmult` (w `cadd` x);
    == { cmult_distributes_over_cadd_left z w x }
    (z `cmult` w) `cadd` (z `cmult` x);
    == { () }
    (w `cmult` z) `cadd` (x `cmult` z);
  }

// for some reason fails with implicit arguments
// sometimes it just takes longer to solve
// seems trivial but Z3 is not happy with it
let underdiv (n m: pos) (a: under (pow2 n * pow2 m)): under (pow2 n) = a / pow2 m

let tensor_distributes_over_sum (#n #m: pos) (v: qbit n) (w: qbit m) (x: qbit m)
  : Lemma ((v `tensorv` (w `madd` x)) == ((v `tensorv` w) `madd` (v `tensorv` x)))
= let proof (i: under (pow2 n * pow2 m)) (j: under 1)
    : Lemma (ijth (v `tensorv` (w `madd` x)) i j == ijth ((v `tensorv` w) `madd` (v `tensorv` x)) i j)
  = let i_n: under (pow2 n) = underdiv n m i in
    let i_m: under (pow2 m) = assert(i % pow2 m < pow2 m); i % pow2 m in
    calc (==) {
      ijth (v `tensorv` (w `madd` x)) i j <: complex;
      == { ijth_tensorv v (w `madd` x) i j }
      (ijth v i_n 0) `cmult` (ijth (w `madd` x) i_m 0) <: complex;
      == { ijth_madd w x i_m 0 }
      (ijth v i_n 0) `cmult` (ijth w i_m 0 `cadd` ijth x i_m 0) <: complex;
      == { cmult_distributes_over_cadd_left (ijth v i_n 0) (ijth w i_m 0) (ijth x i_m 0) }
      (ijth v i_n 0 `cmult` ijth w i_m 0) `cadd` (ijth v i_n 0 `cmult` ijth x i_m 0) <: complex;
      == {
        ijth_tensorv v w i j;
        ijth_tensorv v x i j
      }
      (ijth (v `tensorv` w) i j) `cadd` (ijth (v `tensorv` x) i j) <: complex;
      == { ijth_madd (v `tensorv` w) (v `tensorv` x) i j }
      ijth ((v `tensorv` w) `madd` (v `tensorv` x)) i j <: complex;
    } in

  matrix_equiv_from_proof c_is_equiv (v `tensorv` (w `madd` x)) ((v `tensorv` w) `madd` (v `tensorv` x)) proof;
  equivalence_implies_provable_equality (v `tensorv` (w `madd` x)) ((v `tensorv` w) `madd` (v `tensorv` x))

// takes long, and retries, but it gets there. Don't know why
let tensor_distributes_over_scalar (#n: pos) (a: complex) (v: qbit n) (c: qbit n)
  : Lemma (v `tensorv` (a `mscalar` c) == a `mscalar` (v `tensorv` c))
= let proof (i: under (pow2 n * pow2 n)) (j: under 1)
    : Lemma (ijth (v `tensorv` (a `mscalar` c)) i j == ijth (a `mscalar` (v `tensorv` c)) i j)
  = let i_n: under (pow2 n) = underdiv n n i in
    let i_m: under (pow2 n) = i % pow2 n in
    calc (==) {
      ijth (v `tensorv` (a `mscalar` c)) i j <: complex;
      == { ijth_tensorv v (a `mscalar` c) i j }
      (ijth v i_n 0) `cmult` (ijth (a `mscalar` c) i_m 0) <: complex;
      == { ijth_scalar a c i_m 0 }
      (ijth v i_n 0) `cmult` (a `cmult` (ijth c i_m 0)) <: complex;
      == { () }
      (a `cmult` (ijth c i_m 0)) `cmult` (ijth v i_n 0) <: complex;
      == { cmult_associative a (ijth c i_m 0) (ijth v i_n 0) }
      a `cmult` ((ijth c i_m 0) `cmult` (ijth v i_n 0)) <: complex;
      == { () }
      a `cmult` ((ijth v i_n 0) `cmult` (ijth c i_m 0)) <: complex;
      == { () }
      a `cmult` (ijth (v `tensorv` c) i j) <: complex;
      == { ijth_scalar a (v `tensorv` c) i j }
      ijth (a `mscalar` (v `tensorv` c)) i j <: complex;
    } in

  matrix_equiv_from_proof c_is_equiv (v `tensorv` (a `mscalar` c)) (a `mscalar` (v `tensorv` c)) proof;
  equivalence_implies_provable_equality (v `tensorv` (a `mscalar` c)) (a `mscalar` (v `tensorv` c))

// LB: traté de usar algo del módulo de matrices que no había usado antes, como para dejar una linea
// hecha, de por dónde creo que está la solución, pero no me tipa.
let product_is_linear_1 (#n: pos) (u: operator n) (v: qbit n) (w: qbit n)
  : Lemma (u `mprod` (v `madd` w) == (u `mprod` v) `madd` (u `mprod` w))
= let proof (i: under (pow2 n)) (j: under 1)
    : Lemma (ijth (u `mprod` (v `madd` w)) i j == ijth ((u `mprod` v) `madd` (u `mprod` w)) i j)
  //= calc (==) {
  //  ijth (u `mprod` (v `madd` w)) i j;
  //  == { matrix_mul_ijth c_addition_is_comm_monoid c_multiplication_is_comm_monoid u (v `madd` w) i j }
  //  // doesn't even work? why?
  //  dot c_addition_is_comm_monoid c_multiplication_is_comm_monoid (row u i) (col (v `madd` w) j);
  //  == { admit() }
  //  (magic());
  //} in
  = admit() in

  matrix_equiv_from_proof c_is_equiv (u `mprod` (v `madd` w)) ((u `mprod` v) `madd` (u `mprod` w)) proof;
  equivalence_implies_provable_equality (u `mprod` (v `madd` w)) ((u `mprod` v) `madd` (u `mprod` w))

// LB: ídem arriba.
let product_is_linear_2 (#n: pos) (u: operator n) (a: complex) (v: qbit n)
  : Lemma (u `mprod` (a `mscalar` v) == a `mscalar` (u `mprod` v))
= let proof (i: under (pow2 n)) (j: under 1)
    : Lemma (ijth (u `mprod` (a `mscalar` v)) i j == ijth (a `mscalar` (u `mprod` v)) i j)
  //= calc (==) {
  //  ijth (u `mprod` (a `mscalar` v)) i j;
  //  == { matrix_mul_ijth c_addition_is_comm_monoid c_multiplication_is_comm_monoid u (a `mscalar` v) i j }
  //  dot c_addition_is_comm_monoid c_multiplication_is_comm_monoid (row u i) (col (a `mscalar` v) j);
  //  == { () }
  //  (magic());
  //} in
  = admit() in

  matrix_equiv_from_proof c_is_equiv (u `mprod` (a `mscalar` v)) (a `mscalar` (u `mprod` v)) proof;
  equivalence_implies_provable_equality (u `mprod` (a `mscalar` v)) (a `mscalar` (u `mprod` v))

let product_distributes_over_scalar_sum (#n: pos) (a b: complex) (v: qbit n)
  : Lemma ((a `mscalar` v) `madd` (b `mscalar` v) == (a `cadd` b) `mscalar` v)
= let proof (i: under (pow2 n)) (j: under 1)
    : Lemma (ijth ((a `mscalar` v) `madd` (b `mscalar` v)) i j == ijth ((a `cadd` b) `mscalar` v) i j)
  = calc (==) {
      ijth ((a `mscalar` v) `madd` (b `mscalar` v)) i j <: complex;
      == { ijth_madd (a `mscalar` v) (b `mscalar` v) i j }
      ijth (a `mscalar` v) i j `cadd` ijth (b `mscalar` v) i j <: complex;
      == { () }
      (a `cmult` ijth v i j) `cadd` (b `cmult` ijth v i j) <: complex;
      == { cmult_distributes_over_cadd_right (ijth v i j) a b }
      (a `cadd` b) `cmult` ijth v i j <: complex;
      == { () }
      ijth ((a `cadd` b) `mscalar` v) i j <: complex;
    } in

  matrix_equiv_from_proof c_is_equiv ((a `mscalar` v) `madd` (b `mscalar` v)) ((a `cadd` b) `mscalar` v) proof;
  equivalence_implies_provable_equality ((a `mscalar` v) `madd` (b `mscalar` v)) ((a `cadd` b) `mscalar` v)

// This is also an axiom of the reals
let existence_of_multiplicative_inverse (a: real)
  : Lemma (requires a =!= 0.0R) (ensures a *. (1.0R /. a) == 1.0R) = admit ()

let specific_addition ()
  : Lemma (cinvsqrt2 `cadd` cinvsqrt2 == csqrt2)
= calc (==) {
    (invsqrt2 +. invsqrt2, 0.0R +. 0.0R);
    == { () }
    (2.0R *. invsqrt2, 0.0R);
    == { () }
    (sqrt_2 *. sqrt_2 *. invsqrt2, 0.0R);
    == { mult_associates sqrt_2 sqrt_2 invsqrt2 }
    (sqrt_2 *. (sqrt_2 *. invsqrt2), 0.0R);
    == { () }
    (sqrt_2 *. (sqrt_2 *. (1.0R /. sqrt_2)), 0.0R);
    == { existence_of_multiplicative_inverse sqrt_2 }
    (sqrt_2 *. 1.0R, 0.0R);
    == { () }
    (sqrt_2, 0.0R);
  }

let sq_sign_eq (a b : real)
  : Lemma (requires a *. a == b *. b /\ a >=. 0.0R /\ b >=. 0.0R)
          (ensures a == b)
  = admit ()

// LB: en algún momento me dejó de andar sq_sign_eq, y no sé por qué.
// Tuve que instalar F* localmente en vez de usar el container porque se me rompió
// y no tenía ganas de arreglarlo, puede ser por algo de eso, igual instalé
// la versión que nos pediste.
let specific_absolute_value ()
  : Lemma (cabs csqrt2 == sqrt_2)
= calc (==) {
    cabs csqrt2;
    == { () }
    sqrt (sqrt_2 *. sqrt_2);
    == { () }
    sqrt 2.0R;
    == { admit(); sq_sign_eq sqrt_2 (sqrt 2.0R) } // now this fails?
    sqrt_2;
  }

let no_cloning_theorem_contradiction (u: operator 2)
  : Lemma (requires clona_todo_2 u /\ is_isometry u)
          (ensures False)
=
  assume (norm (zero `tensorv` plus) == 1.0R);
  assume (norm (zero `tensorv` zero) == 1.0R);
  assume (norm (zero `tensorv` one) == 1.0R);
  assume (norm (zero `tensorv` one) == 1.0R);
  calc (==) {
    1.0R;

    == { () }
    norm (zero `tensorv` plus);

    == { () <: squash (is_isometry u) }
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

    == { specific_addition () }
    norm (csqrt2 `mscalar` (zero `tensorv` zero));

    == { vnorm_distributes_over_scalars #2 csqrt2 (zero `tensorv` zero) }
    (cabs csqrt2) *. norm (zero `tensorv` zero);

    == { () }
    (cabs csqrt2) *. 1.0R;

    == { specific_absolute_value () }
    sqrt_2;
  }

let no_cloning_theorem (#n:pos) (u: operator 2)
  : Lemma (requires is_isometry u)
          (ensures ~ (clona_todo_2 u))
= Classical.move_requires no_cloning_theorem_contradiction u
