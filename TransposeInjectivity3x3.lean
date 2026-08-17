import Mathlib

open Matrix
open scoped BigOperators Matrix

namespace TransposeInjectivityFin3

variable {R : Type*} [CommSemiring R]

abbrev V3 (R : Type*) := Fin 3 -> R
abbrev M3 (R : Type*) := Matrix (Fin 3) (Fin 3) R

def next3 : Fin 3 -> Fin 3 := ![1, 2, 0]

def prev3 (i : Fin 3) : Fin 3 := next3 (next3 i)

@[simp] lemma next3_zero : next3 (0 : Fin 3) = 1 := rfl
@[simp] lemma next3_one : next3 (1 : Fin 3) = 2 := rfl
@[simp] lemma next3_two : next3 (2 : Fin 3) = 0 := rfl
@[simp] lemma prev3_zero : prev3 (0 : Fin 3) = 2 := rfl
@[simp] lemma prev3_one : prev3 (1 : Fin 3) = 0 := rfl
@[simp] lemma prev3_two : prev3 (2 : Fin 3) = 1 := rfl

lemma next3_ne_self (i : Fin 3) : next3 i ≠ i := by
  fin_cases i <;> decide

lemma prev3_ne_self (i : Fin 3) : prev3 i ≠ i := by
  fin_cases i <;> decide

lemma next3_ne_prev3 (i : Fin 3) : next3 i ≠ prev3 i := by
  fin_cases i <;> decide

lemma fin3_eq_self_or_next_or_prev (i p : Fin 3) :
    p = i \/ p = next3 i \/ p = prev3 i := by
  fin_cases i <;> fin_cases p <;> simp [next3, prev3]

lemma fin3_eq_next_or_prev_of_ne {i p : Fin 3} (h : p ≠ i) :
    p = next3 i \/ p = prev3 i := by
  rcases fin3_eq_self_or_next_or_prev i p with rfl | hnext | hprev
  · exact (h rfl).elim
  · exact Or.inl hnext
  · exact Or.inr hprev

lemma fin3_cover_of_pairwise {a b c : Fin 3}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (p : Fin 3) :
    p = a \/ p = b \/ p = c := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases p <;>
    simp_all

lemma mulVec_fin3 (M : M3 R) (v : V3 R) (i : Fin 3) :
    M.mulVec v i =
      M i 0 * v 0 + (M i 1 * v 1 + M i 2 * v 2) := by
  simp [Matrix.mulVec_apply_eq_sum, Fin.sum_univ_succ]

lemma mul_apply_fin3 (M N : M3 R) (i j : Fin 3) :
    (M * N) i j =
      M i 0 * N 0 j + (M i 1 * N 1 j + M i 2 * N 2 j) := by
  simp [Matrix.mul_apply, Fin.sum_univ_succ]

def paritySymmetrizer (A : M3 R) (p t : Fin 3) : M3 R :=
  Matrix.of fun r q =>
    if r = 0 then
      if q = t then A 1 q * A 2 p else A 1 p * A 2 q
    else if r = 1 then
      if q = t then A 0 p * A 2 q else A 0 q * A 2 p
    else
      if q = t then A 0 q * A 1 p else A 0 p * A 1 q

lemma transpose_mul_paritySymmetrizer
    (A : M3 R) {p t : Fin 3} (hpt : p ≠ t) :
    A.transpose * paritySymmetrizer A p t =
      (paritySymmetrizer A p t).transpose * A := by
  ext i j
  fin_cases i <;> fin_cases j <;> fin_cases p <;> fin_cases t <;>
    simp_all [paritySymmetrizer, mul_apply_fin3] <;> ring

lemma paritySymmetrizer_mulVec_eq
    (A : M3 R) {x y : V3 R}
    (hT : Function.Injective A.transpose.mulVec)
    (hxy : A.mulVec x = A.mulVec y)
    {p t : Fin 3} (hpt : p ≠ t) :
    (paritySymmetrizer A p t).mulVec x =
      (paritySymmetrizer A p t).mulVec y := by
  apply hT
  calc
    A.transpose.mulVec ((paritySymmetrizer A p t).mulVec x) =
        (A.transpose * paritySymmetrizer A p t).mulVec x :=
      Matrix.mulVec_mulVec _ _ _
    _ = ((paritySymmetrizer A p t).transpose * A).mulVec x := by
      rw [transpose_mul_paritySymmetrizer A hpt]
    _ = (paritySymmetrizer A p t).transpose.mulVec (A.mulVec x) := by
      rw [Matrix.mulVec_mulVec]
    _ = (paritySymmetrizer A p t).transpose.mulVec (A.mulVec y) := by
      rw [hxy]
    _ = ((paritySymmetrizer A p t).transpose * A).mulVec y := by
      rw [Matrix.mulVec_mulVec]
    _ = (A.transpose * paritySymmetrizer A p t).mulVec y := by
      rw [transpose_mul_paritySymmetrizer A hpt]
    _ = A.transpose.mulVec ((paritySymmetrizer A p t).mulVec y) := by
      rw [Matrix.mulVec_mulVec]

def twoRowVector (A : M3 R) (i p t : Fin 3) : V3 R :=
  fun q =>
    if q = t then A i t * A (next3 i) p
    else A i p * A (next3 i) q

lemma twoRow_relation
    (A : M3 R) {x y : V3 R}
    (hT : Function.Injective A.transpose.mulVec)
    (hxy : A.mulVec x = A.mulVec y)
    (i : Fin 3) {p t : Fin 3} (hpt : p ≠ t) :
    dotProduct (twoRowVector A i p t) x =
      dotProduct (twoRowVector A i p t) y := by
  have hP := paritySymmetrizer_mulVec_eq A hT hxy hpt
  have hrow := congrFun hP (prev3 i)
  fin_cases i <;> fin_cases p <;> fin_cases t <;>
    simp [twoRowVector, paritySymmetrizer, prev3, next3,
      Matrix.mulVec_apply_eq_sum, dotProduct, Fin.sum_univ_succ]
      at hpt hrow ⊢ <;>
    ring_nf at hrow ⊢ <;>
    exact hrow

def isolator (A : M3 R) (i t : Fin 3) : M3 R :=
  Matrix.of fun r q =>
    if r = i then
      if q = t then 0 else A (next3 i) q
    else if r = next3 i then
      if q = t then A i t else 0
    else 0

lemma transpose_mulVec_isolator_eq
    (A : M3 R) {x y : V3 R}
    (hT : Function.Injective A.transpose.mulVec)
    (hxy : A.mulVec x = A.mulVec y)
    (i t : Fin 3) :
    A.transpose.mulVec ((isolator A i t).mulVec x) =
      A.transpose.mulVec ((isolator A i t).mulVec y) := by
  funext p
  by_cases hp : p = t
  · subst p
    have hrow := congrFun hxy (next3 i)
    have hscaled := congrArg (fun z => A i t * z) hrow
    fin_cases i <;> fin_cases t <;>
      simp [isolator, next3, mulVec_fin3] at hscaled ⊢ <;>
      ring_nf at hscaled ⊢ <;>
      exact hscaled
  · have hminor := twoRow_relation A hT hxy i hp
    fin_cases i <;> fin_cases p <;> fin_cases t <;>
      simp [isolator, twoRowVector, next3, mulVec_fin3,
        dotProduct, Fin.sum_univ_succ] at hp hminor ⊢ <;>
      ring_nf at hminor ⊢ <;>
      exact hminor

lemma individual_summand_eq_fin3
    (A : M3 R) {x y : V3 R}
    (hT : Function.Injective A.transpose.mulVec)
    (hxy : A.mulVec x = A.mulVec y)
    (i t : Fin 3) :
    A i t * x t = A i t * y t := by
  have hQ : (isolator A i t).mulVec x = (isolator A i t).mulVec y :=
    hT (transpose_mulVec_isolator_eq A hT hxy i t)
  have hrow := congrFun hQ (next3 i)
  fin_cases i <;> fin_cases t <;>
    simpa [isolator, next3, mulVec_fin3] using hrow

lemma balanced_entry
    (a c0 c1 rho sigma : R) (h : a * rho = a * sigma) :
    a * (c0 * rho + c1 * sigma) =
      a * (c0 * sigma + c1 * rho) := by
  calc
    a * (c0 * rho + c1 * sigma) =
        c0 * (a * rho) + c1 * (a * sigma) := by ring
    _ = c0 * (a * sigma) + c1 * (a * sigma) := by
      exact congrArg (fun z => c0 * z + c1 * (a * sigma)) h
    _ = c0 * (a * sigma) + c1 * (a * rho) := by
      exact congrArg (fun z => c0 * (a * sigma) + c1 * z) h.symm
    _ = a * (c0 * sigma + c1 * rho) := by ring

def cofactorEven (A : M3 R) (t : Fin 3) : V3 R :=
  ![
    A 1 (next3 t) * A 2 (prev3 t),
    A 0 (prev3 t) * A 2 (next3 t),
    A 0 (next3 t) * A 1 (prev3 t)
  ]

def cofactorOdd (A : M3 R) (t : Fin 3) : V3 R :=
  ![
    A 1 (prev3 t) * A 2 (next3 t),
    A 0 (next3 t) * A 2 (prev3 t),
    A 0 (prev3 t) * A 1 (next3 t)
  ]

def maximalU (A : M3 R) (t : Fin 3) (rho sigma : R) : V3 R :=
  fun i => cofactorEven A t i * rho + cofactorOdd A t i * sigma

def maximalV (A : M3 R) (t : Fin 3) (rho sigma : R) : V3 R :=
  fun i => cofactorEven A t i * sigma + cofactorOdd A t i * rho

lemma transpose_maximalU_eq_maximalV
    (A : M3 R) (t : Fin 3) (rho sigma : R)
    (hcol : forall i, A i t * rho = A i t * sigma) :
    A.transpose.mulVec (maximalU A t rho sigma) =
      A.transpose.mulVec (maximalV A t rho sigma) := by
  funext p
  by_cases hpt : p = t
  · subst p
    simp only [Matrix.mulVec_apply_eq_sum, Matrix.transpose_apply]
    apply Finset.sum_congr rfl
    intro i hi
    exact balanced_entry
      (A i t) (cofactorEven A t i) (cofactorOdd A t i) rho sigma (hcol i)
  · rcases fin3_eq_next_or_prev_of_ne hpt with rfl | rfl
    · fin_cases t <;>
        simp [maximalU, maximalV, cofactorEven, cofactorOdd,
          next3, prev3, mulVec_fin3] <;> ring
    · fin_cases t <;>
        simp [maximalU, maximalV, cofactorEven, cofactorOdd,
          next3, prev3, mulVec_fin3] <;> ring

def descentU (A : M3 R) (c : Fin 3) (rho sigma : R) : V3 R :=
  ![A 1 c * sigma, A 0 c * rho, 0]

def descentV (A : M3 R) (c : Fin 3) (rho sigma : R) : V3 R :=
  ![A 1 c * rho, A 0 c * sigma, 0]

lemma transpose_descentU_eq_descentV
    (A : M3 R) (t c d : Fin 3) (rho sigma : R)
    (htc : t ≠ c) (htd : t ≠ d) (hcd : c ≠ d)
    (hcol : forall i, A i t * rho = A i t * sigma)
    (hE :
      (A 0 c * A 1 d) * rho + (A 0 d * A 1 c) * sigma =
        (A 0 c * A 1 d) * sigma + (A 0 d * A 1 c) * rho) :
    A.transpose.mulVec (descentU A c rho sigma) =
      A.transpose.mulVec (descentV A c rho sigma) := by
  funext p
  rcases fin3_cover_of_pairwise htc htd hcd p with hp | hp | hp
  · subst p
    have h0 := hcol 0
    have h1 := hcol 1
    simp [descentU, descentV, mulVec_fin3]
    calc
      A 0 t * (A 1 c * sigma) + A 1 t * (A 0 c * rho) =
          A 1 c * (A 0 t * sigma) + A 0 c * (A 1 t * rho) := by ring
      _ = A 1 c * (A 0 t * rho) + A 0 c * (A 1 t * sigma) := by
        rw [← h0, h1]
      _ = A 0 t * (A 1 c * rho) + A 1 t * (A 0 c * sigma) := by ring
  · subst p
    simp [descentU, descentV, mulVec_fin3]
    ring
  · subst p
    simp [descentU, descentV, mulVec_fin3]
    convert hE using 1 <;> ring

lemma remove_column_coefficient_fin3
    (A : M3 R)
    (hT : Function.Injective A.transpose.mulVec)
    (t : Fin 3) (rho sigma : R)
    (hcol : forall i, A i t * rho = A i t * sigma) :
    rho = sigma := by
  let c : Fin 3 := next3 t
  let d : Fin 3 := prev3 t
  have htc : t ≠ c := by
    dsimp [c]
    exact (next3_ne_self t).symm
  have htd : t ≠ d := by
    dsimp [d]
    exact (prev3_ne_self t).symm
  have hcd : c ≠ d := by
    dsimp [c, d]
    exact next3_ne_prev3 t

  have hmax : maximalU A t rho sigma = maximalV A t rho sigma :=
    hT (transpose_maximalU_eq_maximalV A t rho sigma hcol)
  have hEcd :
      (A 0 c * A 1 d) * rho + (A 0 d * A 1 c) * sigma =
        (A 0 c * A 1 d) * sigma + (A 0 d * A 1 c) * rho := by
    have h2 := congrFun hmax 2
    simpa [maximalU, maximalV, cofactorEven, cofactorOdd, c, d] using h2

  have hdescC : descentU A c rho sigma = descentV A c rho sigma :=
    hT (transpose_descentU_eq_descentV A t c d rho sigma
      htc htd hcd hcol hEcd)
  have hA0c : A 0 c * rho = A 0 c * sigma := by
    have h1 := congrFun hdescC 1
    simpa [descentU, descentV] using h1

  have hEdc :
      (A 0 d * A 1 c) * rho + (A 0 c * A 1 d) * sigma =
        (A 0 d * A 1 c) * sigma + (A 0 c * A 1 d) * rho := by
    simpa [add_comm] using hEcd.symm

  have hdescD : descentU A d rho sigma = descentV A d rho sigma :=
    hT (transpose_descentU_eq_descentV A t d c rho sigma
      htd htc hcd.symm hcol hEdc)
  have hA0d : A 0 d * rho = A 0 d * sigma := by
    have h1 := congrFun hdescD 1
    simpa [descentU, descentV] using h1

  let u : V3 R := ![rho, 0, 0]
  let v : V3 R := ![sigma, 0, 0]
  have huv_image : A.transpose.mulVec u = A.transpose.mulVec v := by
    funext p
    rcases fin3_cover_of_pairwise htc htd hcd p with rfl | rfl | rfl
    · simpa [u, v, mulVec_fin3] using hcol 0
    · simpa [u, v, mulVec_fin3] using hA0c
    · simpa [u, v, mulVec_fin3] using hA0d
  have huv : u = v := hT huv_image
  have h0 := congrFun huv 0
  simpa [u, v] using h0

theorem injective_of_transpose_injective_fin3
    (A : M3 R) (hT : Function.Injective A.transpose.mulVec) :
    Function.Injective A.mulVec := by
  intro x y hxy
  funext t
  apply remove_column_coefficient_fin3 A hT t (x t) (y t)
  intro i
  exact individual_summand_eq_fin3 A hT hxy i t

theorem mulVec_injective_iff_transpose_mulVec_injective_fin3 (A : M3 R) :
    Function.Injective A.mulVec ↔
      Function.Injective A.transpose.mulVec := by
  constructor
  · intro hA
    have h := injective_of_transpose_injective_fin3 (A := A.transpose) (by
      simpa using hA)
    simpa using h
  · exact injective_of_transpose_injective_fin3 A

end TransposeInjectivityFin3

#print axioms TransposeInjectivityFin3.mulVec_injective_iff_transpose_mulVec_injective_fin3
