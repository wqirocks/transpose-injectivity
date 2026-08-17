import Mathlib

open Matrix
open scoped BigOperators Matrix

namespace TransposeInjectivityGeneral

noncomputable section

variable {R : Type*} [CommSemiring R]
variable {n : Nat}

abbrev Vec (R : Type*) (n : Nat) := Fin n -> R
abbrev Mat (R : Type*) (n : Nat) := Matrix (Fin n) (Fin n) R

inductive Parity
  | even
  | odd
  deriving DecidableEq, Repr

namespace Parity

def flip : Parity -> Parity
  | even => odd
  | odd => even

@[simp] theorem flip_even : flip even = odd := rfl
@[simp] theorem flip_odd : flip odd = even := rfl
@[simp] theorem flip_flip (e : Parity) : flip (flip e) = e := by
  cases e <;> rfl

@[simp] theorem flip_eq_iff {e f : Parity} : e.flip = f ↔ e = f.flip := by
  cases e <;> cases f <;> simp

end Parity

def permParity {k : Nat} (sigma : Equiv.Perm (Fin k)) : Parity :=
  if Equiv.Perm.sign sigma = 1 then .even else .odd

theorem permParity_decomposeFin_symm {k : Nat}
    (r : Fin (k + 1)) (tau : Equiv.Perm (Fin k)) :
    permParity (Equiv.Perm.decomposeFin.symm (r, tau)) =
      if r = 0 then permParity tau else (permParity tau).flip := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign tau) with ht | ht <;>
    by_cases hr : r = 0 <;>
    simp [permParity, Equiv.Perm.decomposeFin.symm_sign, ht, hr]

def minorHalf (A : Matrix (Fin n) (Fin n) R) (e : Parity) {k : Nat}
    (I C : Fin k -> Fin n) : R :=
  ∑ sigma : Equiv.Perm (Fin k),
    if permParity sigma = e then
      ∏ c : Fin k, A (I (sigma c)) (C c)
    else 0

def dropRow {k n : Nat} (I : Fin (k + 1) -> Fin n) (r : Fin (k + 1)) :
    Fin k -> Fin n :=
  fun j => I (Equiv.swap 0 r (Fin.succ j))

def dropEmbedding {k n : Nat} (I : Fin (k + 1) ↪ Fin n)
    (r : Fin (k + 1)) : Fin k ↪ Fin n where
  toFun := dropRow I r
  inj' := I.injective.comp ((Equiv.swap 0 r).injective.comp (Fin.succ_injective _))

@[simp] theorem coe_dropEmbedding {k n : Nat} (I : Fin (k + 1) ↪ Fin n)
    (r : Fin (k + 1)) :
    (dropEmbedding I r : Fin k -> Fin n) = dropRow I r := rfl

theorem minorHalf_cons (A : Matrix (Fin n) (Fin n) R)
    (e : Parity) {k : Nat} (I : Fin (k + 1) -> Fin n)
    (C : Fin k -> Fin n) (p : Fin n) :
    minorHalf A e I (Fin.cons p C) =
      ∑ r : Fin (k + 1),
        A (I r) p * minorHalf A (if r = 0 then e else e.flip) (dropRow I r) C := by
  classical
  unfold minorHalf
  let f : Equiv.Perm (Fin (k + 1)) -> R := fun sigma =>
    if permParity sigma = e then
      ∏ c : Fin (k + 1),
        A (I (sigma c)) ((@Fin.cons k (fun _ => Fin n) p C) c)
    else 0
  calc
    ∑ sigma, (if permParity sigma = e then
        ∏ c : Fin (k + 1),
          A (I (sigma c)) ((@Fin.cons k (fun _ => Fin n) p C) c)
      else 0) = ∑ sigma, f sigma := rfl
    _ = ∑ z : Fin (k + 1) × Equiv.Perm (Fin k),
        f (Equiv.Perm.decomposeFin.symm z) := by
      apply Fintype.sum_equiv Equiv.Perm.decomposeFin
      intro sigma
      simp
    _ = ∑ r : Fin (k + 1), ∑ tau : Equiv.Perm (Fin k),
        f (Equiv.Perm.decomposeFin.symm (r, tau)) := by
      rw [Fintype.sum_prod_type]
    _ = ∑ r : Fin (k + 1),
        A (I r) p *
          (∑ sigma : Equiv.Perm (Fin k),
            if permParity sigma = (if r = 0 then e else e.flip) then
              ∏ c : Fin k, A (dropRow I r (sigma c)) (C c)
            else 0) := by
      apply Finset.sum_congr rfl
      intro r hr
      simp only [f, permParity_decomposeFin_symm, Fin.prod_univ_succ,
        Equiv.Perm.decomposeFin_symm_apply_zero, Fin.cons_zero,
        Equiv.Perm.decomposeFin_symm_apply_succ, Fin.cons_succ, dropRow]
      by_cases h0 : r = 0
      · simp [h0, Finset.mul_sum]
      · simp [h0, Finset.mul_sum]
    _ = ∑ r : Fin (k + 1),
        A (I r) p * minorHalf A (if r = 0 then e else e.flip) (dropRow I r) C := by
      rfl

@[simp] theorem minorHalf_empty_even (A : Matrix (Fin n) (Fin n) R)
    (I C : Fin 0 -> Fin n) : minorHalf A .even I C = 1 := by
  rw [minorHalf, Fintype.sum_unique]
  simp [permParity]

@[simp] theorem minorHalf_empty_odd (A : Matrix (Fin n) (Fin n) R)
    (I C : Fin 0 -> Fin n) : minorHalf A .odd I C = 0 := by
  rw [minorHalf, Fintype.sum_unique]
  simp [permParity]

@[simp] theorem minorHalf_singleton_even (A : Matrix (Fin n) (Fin n) R)
    (I C : Fin 1 -> Fin n) : minorHalf A .even I C = A (I 0) (C 0) := by
  rw [minorHalf, Fintype.sum_unique]
  simp [permParity]

@[simp] theorem minorHalf_singleton_odd (A : Matrix (Fin n) (Fin n) R)
    (I C : Fin 1 -> Fin n) : minorHalf A .odd I C = 0 := by
  rw [minorHalf, Fintype.sum_unique]
  simp [permParity]

theorem permParity_mul_swap {k : Nat} (sigma : Equiv.Perm (Fin k))
    {u v : Fin k} (huv : u ≠ v) :
    permParity (sigma * Equiv.swap u v) = (permParity sigma).flip := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign sigma) with hs | hs <;>
    simp [permParity, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap huv, hs]

theorem minorHalf_swapColumns (A : Matrix (Fin n) (Fin n) R)
    (e : Parity) {k : Nat} (I C : Fin k -> Fin n)
    {u v : Fin k} (huv : u ≠ v) :
    minorHalf A e I (fun c => C (Equiv.swap u v c)) =
      minorHalf A e.flip I C := by
  classical
  let tau : Equiv.Perm (Fin k) := Equiv.swap u v
  have htau : Equiv.Perm.sign tau = -1 := by
    exact Equiv.Perm.sign_swap huv
  unfold minorHalf
  apply Fintype.sum_equiv (Equiv.mulRight tau)
  intro sigma
  have hpar : permParity (sigma * tau) = (permParity sigma).flip := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign sigma) with hs | hs <;>
      simp [permParity, Equiv.Perm.sign_mul, htau, hs]
  change (if permParity sigma = e then
      ∏ c : Fin k, A (I (sigma c)) (C (tau c)) else 0) =
    if permParity (sigma * tau) = e.flip then
      ∏ c : Fin k, A (I ((sigma * tau) c)) (C c) else 0
  rw [hpar]
  by_cases hp : permParity sigma = e
  · simp only [hp, if_true]
    apply Fintype.prod_equiv (Equiv.swap u v)
    intro c
    simp [tau, Equiv.Perm.mul_apply]
  · have hp' : (permParity sigma).flip ≠ e.flip := by
      intro h
      apply hp
      have hh := congrArg Parity.flip h
      simpa using hh
    simp [hp, hp']

theorem swappedFunction_eq_of_eq {α β : Type*} [DecidableEq α]
    (C : α -> β) {u v : α}
    (hC : C u = C v) :
    (fun c => C (Equiv.swap u v c)) = C := by
  funext c
  by_cases hcu : c = u
  · subst c
    simp [hC]
  · by_cases hcv : c = v
    · subst c
      simp [hC]
    · simp [Equiv.swap_apply_of_ne_of_ne hcu hcv]

theorem minorHalf_eq_flip_of_repeated (A : Matrix (Fin n) (Fin n) R)
    (e : Parity) {k : Nat} (I C : Fin k -> Fin n)
    {u v : Fin k} (huv : u ≠ v) (hC : C u = C v) :
    minorHalf A e I C = minorHalf A e.flip I C := by
  have hfun := swappedFunction_eq_of_eq C hC
  calc
    minorHalf A e I C =
        minorHalf A e I (fun c => C (Equiv.swap u v c)) := by rw [hfun]
    _ = minorHalf A e.flip I C := minorHalf_swapColumns A e I C huv

theorem minorHalf_eq_of_not_injective_columns
    (A : Matrix (Fin n) (Fin n) R) {k : Nat} (I C : Fin k -> Fin n)
    (hC : ¬Function.Injective C) (e f : Parity) :
    minorHalf A e I C = minorHalf A f I C := by
  obtain ⟨u, v, huvC, huv⟩ := Function.not_injective_iff.mp hC
  cases e <;> cases f
  · rfl
  · exact minorHalf_eq_flip_of_repeated A .even I C huv huvC
  · exact (minorHalf_eq_flip_of_repeated A .even I C huv huvC).symm
  · rfl

theorem eq_of_not_mem_range_codim_one {k : Nat}
    (I : Fin k ↪ Fin (k + 1)) {a b : Fin (k + 1)}
    (ha : a ∉ Set.range I) (hb : b ∉ Set.range I) : a = b := by
  let L : Fin (k + 1) ↪ Fin (k + 1) := Fin.Embedding.snoc I ha
  have hLsurj : Function.Surjective L :=
    ((Fintype.bijective_iff_injective_and_card L).2 ⟨L.injective, by simp⟩).2
  obtain ⟨r, hr⟩ := hLsurj b
  cases r using Fin.lastCases with
  | last =>
      simpa [L, Fin.Embedding.snoc_last] using hr
  | cast r =>
      exfalso
      apply hb
      refine ⟨r, ?_⟩
      simpa [L, Fin.Embedding.snoc_castSucc] using hr

theorem exists_not_mem_range_of_embedding {k n : Nat}
    (I : Fin k ↪ Fin n) (hkn : k < n) :
    ∃ s : Fin n, s ∉ Set.range I := by
  by_contra h
  have hsurj : Function.Surjective I := by
    intro s
    by_contra hs
    exact h ⟨s, hs⟩
  have hcard := Fintype.card_le_of_surjective I hsurj
  simp only [Fintype.card_fin] at hcard
  omega

theorem swapEnds_cons_snoc {α : Type*} {k : Nat}
    (p q : α) (J : Fin k -> α) :
    (fun c => (@Fin.cons (k + 1) (fun _ => α) p
        (@Fin.snoc k (fun _ => α) J q))
      (Equiv.swap (0 : Fin (k + 2)) (Fin.last (k + 1)) c)) =
        @Fin.cons (k + 1) (fun _ => α) q
          (@Fin.snoc k (fun _ => α) J p) := by
  funext c
  cases c using Fin.cases with
  | zero => simp
  | succ c =>
      cases c using Fin.lastCases with
      | last => simp
      | cast c =>
          simp [Equiv.swap_apply_of_ne_of_ne]

theorem minorHalf_swapEnds
    (A : Matrix (Fin n) (Fin n) R) (e : Parity) {k : Nat}
    (I : Fin (k + 2) -> Fin n) (J : Fin k -> Fin n) (p q : Fin n) :
    minorHalf A e I (Fin.cons q (Fin.snoc J p)) =
      minorHalf A e.flip I (Fin.cons p (Fin.snoc J q)) := by
  let Cpq : Fin (k + 2) -> Fin n := Fin.cons p (Fin.snoc J q)
  have hends :
      (fun c => Cpq
        (Equiv.swap (0 : Fin (k + 2)) (Fin.last (k + 1)) c)) =
          Fin.cons q (Fin.snoc J p) := by
    simpa [Cpq] using swapEnds_cons_snoc p q J
  have h := minorHalf_swapColumns A e I Cpq
    (u := (0 : Fin (k + 2))) (v := Fin.last (k + 1)) (by simp)
  rwa [hends] at h

def scatterVec {k n : Nat} (I : Fin k ↪ Fin n) (w : Fin k -> R) : Fin n -> R :=
  fun s => ∑ r : Fin k, if I r = s then w r else 0

@[simp] theorem scatterVec_apply (I : Fin k ↪ Fin n) (w : Fin k -> R)
    (r : Fin k) : scatterVec I w (I r) = w r := by
  classical
  simp [scatterVec, I.injective.eq_iff]

theorem transpose_mulVec_scatterVec
    (A : Matrix (Fin n) (Fin n) R) {k : Nat}
    (I : Fin k ↪ Fin n) (w : Fin k -> R) (p : Fin n) :
    A.transpose.mulVec (scatterVec I w) p =
      ∑ r : Fin k, A (I r) p * w r := by
  classical
  simp only [Matrix.mulVec_apply, dotProduct, scatterVec, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  simp

def scatterRows {k n : Nat} (I : Fin k ↪ Fin n)
    (B : Fin k -> Fin n -> R) : Matrix (Fin n) (Fin n) R :=
  fun s q => ∑ r : Fin k, if I r = s then B r q else 0

@[simp] theorem scatterRows_apply (I : Fin k ↪ Fin n)
    (B : Fin k -> Fin n -> R) (r : Fin k) (q : Fin n) :
    scatterRows I B (I r) q = B r q := by
  classical
  simp [scatterRows, I.injective.eq_iff]

theorem scatterRows_mulVec (I : Fin k ↪ Fin n)
    (B : Fin k -> Fin n -> R) (x : Fin n -> R) :
    (scatterRows I B).mulVec x =
      scatterVec I (fun r => dotProduct (B r) x) := by
  classical
  funext s
  change (∑ q : Fin n, scatterRows I B s q * x q) =
    scatterVec I (fun r => ∑ q : Fin n, B r q * x q) s
  simp only [scatterRows, scatterVec, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  by_cases h : I r = s
  · simp [h]
  · simp [h]

theorem transpose_mulVec_scatterRows_mulVec
    (A : Matrix (Fin n) (Fin n) R) {k : Nat}
    (I : Fin k ↪ Fin n) (B : Fin k -> Fin n -> R)
    (x : Fin n -> R) (p : Fin n) :
    A.transpose.mulVec ((scatterRows I B).mulVec x) p =
      ∑ r : Fin k, A (I r) p * dotProduct (B r) x := by
  rw [scatterRows_mulVec]
  exact transpose_mulVec_scatterVec A I _ p

def laplaceCofactorVector
    (A : Matrix (Fin n) (Fin n) R) {k : Nat}
    (L : Fin (k + 1) ↪ Fin n) (C : Fin k -> Fin n)
    (e : Parity) : Fin (k + 1) -> R :=
  fun r => minorHalf A (if r = 0 then e else e.flip) (dropEmbedding L r) C

theorem minorHalf_cons_vector_eq
    (A : Matrix (Fin n) (Fin n) R) {k : Nat}
    (L : Fin (k + 1) ↪ Fin n) (C : Fin k -> Fin n)
    (e : Parity) :
    (fun q : Fin n => minorHalf A e L (Fin.cons q C)) =
      A.transpose.mulVec (scatterVec L (laplaceCofactorVector A L C e)) := by
  funext q
  rw [transpose_mulVec_scatterVec]
  exact minorHalf_cons A e L C q

theorem dotProduct_minorHalf_cons_eq_of_mulVec_eq
    (A : Matrix (Fin n) (Fin n) R) {k : Nat}
    (L : Fin (k + 1) ↪ Fin n) (C : Fin k -> Fin n)
    (e : Parity) {x y : Fin n -> R} (hxy : A.mulVec x = A.mulVec y) :
    dotProduct (fun q : Fin n => minorHalf A e L (Fin.cons q C)) x =
      dotProduct (fun q : Fin n => minorHalf A e L (Fin.cons q C)) y := by
  let u := scatterVec L (laplaceCofactorVector A L C e)
  have hvec := minorHalf_cons_vector_eq A L C e
  calc
    dotProduct (fun q : Fin n => minorHalf A e L (Fin.cons q C)) x =
        dotProduct x (A.transpose.mulVec u) := by rw [hvec, dotProduct_comm]
    _ = dotProduct u (A.mulVec x) := Matrix.dotProduct_transpose_mulVec A x u
    _ = dotProduct u (A.mulVec y) := by rw [hxy]
    _ = dotProduct y (A.transpose.mulVec u) :=
      (Matrix.dotProduct_transpose_mulVec A y u).symm
    _ = dotProduct (fun q : Fin n => minorHalf A e L (Fin.cons q C)) y := by
      rw [hvec, dotProduct_comm]

theorem transpose_mul_scatterRows_apply
    (A : Matrix (Fin n) (Fin n) R) {k : Nat}
    (I : Fin k ↪ Fin n) (B : Fin k -> Fin n -> R)
    (p q : Fin n) :
    (A.transpose * scatterRows I B) p q =
      ∑ r : Fin k, A (I r) p * B r q := by
  classical
  rw [Matrix.mul_apply]
  change (∑ s : Fin n, A s p * scatterRows I B s q) = _
  simp only [scatterRows, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  simp

def separationParity (e : Parity) (t q : Fin n) : Parity :=
  if q = t then e.flip else e

def separationVector (A : Matrix (Fin n) (Fin n) R) {m : Nat}
    (I : Fin (m + 1) ↪ Fin n) (J : Fin m ↪ Fin n)
    (t : Fin n) (e : Parity) : Fin n -> R :=
  fun q =>
    minorHalf A (separationParity e t q) I (Fin.snoc J q)

def SeparationStage (A : Matrix (Fin n) (Fin n) R)
    (x y : Fin n -> R) (m : Nat) : Prop :=
  ∀ (I : Fin (m + 1) ↪ Fin n) (J : Fin m ↪ Fin n) (t : Fin n),
    t ∉ Set.range J -> ∀ e : Parity,
      dotProduct (separationVector A I J t e) x =
        dotProduct (separationVector A I J t e) y

def emptyEmbedding (n : Nat) : Fin 0 ↪ Fin n where
  toFun := Fin.elim0
  inj' := fun i => Fin.elim0 i

def singletonEmbedding (i : Fin n) : Fin 1 ↪ Fin n where
  toFun := fun _ => i
  inj' := fun _ _ _ => Subsingleton.elim _ _

def separationCofactorRows
    (A : Matrix (Fin n) (Fin n) R) {k : Nat}
    (L : Fin (k + 2) ↪ Fin n) (J : Fin k -> Fin n)
    (t : Fin n) (e : Parity) : Fin (k + 2) -> Fin n -> R :=
  fun r q =>
    minorHalf A
      (if r = 0 then separationParity e t q else (separationParity e t q).flip)
      (dropEmbedding L r) (Fin.snoc J q)

def separationMatrix
    (A : Matrix (Fin n) (Fin n) R) {k : Nat}
    (L : Fin (k + 2) ↪ Fin n) (J : Fin k -> Fin n)
    (t : Fin n) (e : Parity) : Matrix (Fin n) (Fin n) R :=
  scatterRows L (separationCofactorRows A L J t e)

theorem transpose_mul_separationMatrix_apply
    (A : Matrix (Fin n) (Fin n) R) {k : Nat}
    (L : Fin (k + 2) ↪ Fin n) (J : Fin k -> Fin n)
    (t : Fin n) (e : Parity) (p q : Fin n) :
    (A.transpose * separationMatrix A L J t e) p q =
      minorHalf A (separationParity e t q) L
        (Fin.cons p (Fin.snoc J q)) := by
  rw [separationMatrix, transpose_mul_scatterRows_apply]
  exact (minorHalf_cons A (separationParity e t q) L (Fin.snoc J q) p).symm

theorem separationFullMinor_symmetric_top {k : Nat}
    (A : Matrix (Fin (k + 2)) (Fin (k + 2)) R)
    (L : Fin (k + 2) ↪ Fin (k + 2))
    (J : Fin k ↪ Fin (k + 2)) (t : Fin (k + 2))
    (htJ : t ∉ Set.range J) (e : Parity) (p q : Fin (k + 2)) :
    minorHalf A (separationParity e t q) L
        (Fin.cons p (Fin.snoc J q)) =
      minorHalf A (separationParity e t p) L
        (Fin.cons q (Fin.snoc J p)) := by
  classical
  let Cpq : Fin (k + 2) -> Fin (k + 2) := Fin.cons p (Fin.snoc J q)
  let Cqp : Fin (k + 2) -> Fin (k + 2) := Fin.cons q (Fin.snoc J p)
  have hends :
      (fun c => Cpq
        (Equiv.swap (0 : Fin (k + 2)) (Fin.last (k + 1)) c)) = Cqp := by
    simpa [Cpq, Cqp] using swapEnds_cons_snoc p q J
  have hswap :
      minorHalf A (separationParity e t p) L Cqp =
        minorHalf A (separationParity e t p).flip L Cpq := by
    have h := minorHalf_swapColumns A (separationParity e t p) L Cpq
      (u := (0 : Fin (k + 2))) (v := Fin.last (k + 1)) (by simp)
    rwa [hends] at h
  change minorHalf A (separationParity e t q) L Cpq =
    minorHalf A (separationParity e t p) L Cqp
  rw [hswap]
  by_cases hC : Function.Injective Cpq
  · have hcons := Fin.cons_injective_iff.mp hC
    have hpTail := hcons.1
    have htail := Fin.snoc_injective_iff.mp hcons.2
    have hqJ : q ∉ Set.range J := htail.2
    have hpdata : p ≠ q ∧ ∀ j : Fin k, J j ≠ p := by
      simpa [Fin.range_snoc] using hpTail
    have hpq : p ≠ q := hpdata.1
    have hpJ : p ∉ Set.range J := by
      rintro ⟨j, hj⟩
      exact hpdata.2 j hj
    have hpar :
        separationParity e t q = (separationParity e t p).flip := by
      by_cases hpt : p = t
      · have hqt : q ≠ t := by
          intro hqt
          exact hpq (hpt.trans hqt.symm)
        simp [separationParity, hpt, hqt]
      · let Jp : Fin (k + 1) ↪ Fin (k + 2) := Fin.Embedding.snoc J hpJ
        have htJp : t ∉ Set.range Jp := by
          rintro ⟨j, hj⟩
          cases j using Fin.lastCases with
          | last =>
              have : t = p := by simpa [Jp, Fin.Embedding.snoc_last] using hj.symm
              exact hpt this.symm
          | cast j =>
              apply htJ
              refine ⟨j, ?_⟩
              simpa [Jp, Fin.Embedding.snoc_castSucc] using hj
        have hqJp : q ∉ Set.range Jp := by
          rintro ⟨j, hj⟩
          cases j using Fin.lastCases with
          | last =>
              have : q = p := by simpa [Jp, Fin.Embedding.snoc_last] using hj.symm
              exact hpq this.symm
          | cast j =>
              apply hqJ
              refine ⟨j, ?_⟩
              simpa [Jp, Fin.Embedding.snoc_castSucc] using hj
        have htq : t = q := eq_of_not_mem_range_codim_one Jp htJp hqJp
        simp [separationParity, hpt, htq.symm]
    rw [hpar]
  · exact minorHalf_eq_of_not_injective_columns A L Cpq hC _ _

theorem separationStage_top
    (A : Matrix (Fin (k + 2)) (Fin (k + 2)) R)
    (hT : Function.Injective A.transpose.mulVec)
    {x y : Fin (k + 2) -> R} (hxy : A.mulVec x = A.mulVec y) :
    SeparationStage A x y k := by
  intro I J t htJ e
  obtain ⟨s, hs⟩ := exists_not_mem_range_of_embedding I (by omega)
  let L : Fin (k + 2) ↪ Fin (k + 2) := Fin.Embedding.cons I hs
  let P := separationMatrix A L J t e
  have hsymm : A.transpose * P = (A.transpose * P).transpose := by
    ext p q
    change (A.transpose * P) p q = (A.transpose * P) q p
    dsimp [P]
    rw [transpose_mul_separationMatrix_apply,
      transpose_mul_separationMatrix_apply]
    exact separationFullMinor_symmetric_top A L J t htJ e p q
  have hintertwine : A.transpose * P = P.transpose * A := by
    calc
      A.transpose * P = (A.transpose * P).transpose := hsymm
      _ = P.transpose * A := by simp
  have hP : P.mulVec x = P.mulVec y := by
    apply hT
    calc
      A.transpose.mulVec (P.mulVec x) = (A.transpose * P).mulVec x :=
        Matrix.mulVec_mulVec _ _ _
      _ = (P.transpose * A).mulVec x := by rw [hintertwine]
      _ = P.transpose.mulVec (A.mulVec x) := by rw [Matrix.mulVec_mulVec]
      _ = P.transpose.mulVec (A.mulVec y) := by rw [hxy]
      _ = (P.transpose * A).mulVec y := by rw [Matrix.mulVec_mulVec]
      _ = (A.transpose * P).mulVec y := by rw [hintertwine]
      _ = A.transpose.mulVec (P.mulVec y) := by rw [Matrix.mulVec_mulVec]
  have hrow := congrFun hP (L 0)
  dsimp [P] at hrow
  simp only [separationMatrix, scatterRows_mulVec] at hrow
  simp only [scatterVec_apply] at hrow
  have hdrop : dropRow L 0 = (I : Fin (k + 1) -> Fin (k + 2)) := by
    funext j
    simp [L, dropRow]
  have hB : separationCofactorRows A L J t e 0 =
      separationVector A I J t e := by
    funext q
    simp [separationCofactorRows, separationVector, separationParity,
      dropEmbedding, hdrop]
  simpa [hB] using hrow

theorem separationStage_step
    (A : Matrix (Fin n) (Fin n) R)
    (hT : Function.Injective A.transpose.mulVec)
    {x y : Fin n -> R} (hxy : A.mulVec x = A.mulVec y)
    (m : Nat) (hmn : m + 2 < n)
    (hnext : SeparationStage A x y (m + 1)) :
    SeparationStage A x y m := by
  intro I J t htJ e
  obtain ⟨s, hs⟩ := exists_not_mem_range_of_embedding I (by omega)
  let L : Fin (m + 2) ↪ Fin n := Fin.Embedding.cons I hs
  let P := separationMatrix A L J t e
  have hHxy : (A.transpose * P).mulVec x = (A.transpose * P).mulVec y := by
    funext p
    change dotProduct ((A.transpose * P) p) x =
      dotProduct ((A.transpose * P) p) y
    by_cases hpJ : p ∈ Set.range J
    · have hrow : (A.transpose * P) p =
          fun q : Fin n =>
            minorHalf A e.flip L (Fin.cons q (Fin.snoc J p)) := by
        funext q
        dsimp [P]
        rw [transpose_mul_separationMatrix_apply]
        let Cpq : Fin (m + 2) -> Fin n := Fin.cons p (Fin.snoc J q)
        have hnoninj : ¬Function.Injective Cpq := by
          intro hC
          have hpTail := (Fin.cons_injective_iff.mp hC).1
          apply hpTail
          rw [Fin.range_snoc]
          exact Set.mem_insert_iff.mpr (Or.inr hpJ)
        calc
          minorHalf A (separationParity e t q) L Cpq =
              minorHalf A e L Cpq :=
            minorHalf_eq_of_not_injective_columns A L Cpq hnoninj _ _
          _ = minorHalf A e.flip L (Fin.cons q (Fin.snoc J p)) :=
            by simpa using (minorHalf_swapEnds A e.flip L J p q).symm
      rw [hrow]
      exact dotProduct_minorHalf_cons_eq_of_mulVec_eq
        A L (Fin.snoc J p) e.flip hxy
    · by_cases hpt : p = t
      · subst p
        have hrow : (A.transpose * P) t =
            fun q : Fin n =>
              minorHalf A e.flip L (Fin.cons q (Fin.snoc J t)) := by
          funext q
          dsimp [P]
          rw [transpose_mul_separationMatrix_apply]
          by_cases hqt : q = t
          · subst q
            simp [separationParity]
          · have hsep : separationParity e t q = e := by
              simp [separationParity, hqt]
            rw [hsep]
            simpa using (minorHalf_swapEnds A e.flip L J t q).symm
        rw [hrow]
        exact dotProduct_minorHalf_cons_eq_of_mulVec_eq
          A L (Fin.snoc J t) e.flip hxy
      · have hpJ' : p ∉ Set.range J := hpJ
        let Jp : Fin (m + 1) ↪ Fin n := Fin.Embedding.cons J hpJ'
        have htJp : t ∉ Set.range Jp := by
          rintro ⟨j, hj⟩
          cases j using Fin.cases with
          | zero =>
              have : p = t := by simpa [Jp] using hj
              exact hpt this
          | succ j =>
              apply htJ
              refine ⟨j, ?_⟩
              simpa [Jp] using hj
        have hstage := hnext L Jp t htJp e
        have hrow : (A.transpose * P) p = separationVector A L Jp t e := by
          funext q
          dsimp [P]
          rw [transpose_mul_separationMatrix_apply]
          simp [separationVector, Jp, Fin.cons_snoc_eq_snoc_cons]
        simpa [hrow] using hstage
  have hP : P.mulVec x = P.mulVec y := by
    apply hT
    calc
      A.transpose.mulVec (P.mulVec x) = (A.transpose * P).mulVec x :=
        Matrix.mulVec_mulVec _ _ _
      _ = (A.transpose * P).mulVec y := hHxy
      _ = A.transpose.mulVec (P.mulVec y) := by rw [Matrix.mulVec_mulVec]
  have hrow := congrFun hP (L 0)
  dsimp [P] at hrow
  simp only [separationMatrix, scatterRows_mulVec] at hrow
  simp only [scatterVec_apply] at hrow
  have hdrop : dropRow L 0 = (I : Fin (m + 1) -> Fin n) := by
    funext j
    simp [L, dropRow]
  have hB : separationCofactorRows A L J t e 0 =
      separationVector A I J t e := by
    funext q
    simp [separationCofactorRows, separationVector, separationParity,
      dropEmbedding, hdrop]
  simpa [hB] using hrow

theorem separationStage_bottom
    (A : Matrix (Fin n) (Fin n) R) {x y : Fin n -> R}
    (hzero : SeparationStage A x y 0) (i t : Fin n) :
    A i t * x t = A i t * y t := by
  have ht : t ∉ Set.range (emptyEmbedding n) := by
    rintro ⟨j, _⟩
    exact Fin.elim0 j
  have h := hzero (singletonEmbedding i) (emptyEmbedding n) t ht .odd
  have hsnoc :
      (@Fin.snoc 0 (fun _ => Fin n) (fun j : Fin 0 => Fin.elim0 j) t)
        (0 : Fin 1) = t := by
    exact @Fin.snoc_last 0 (fun _ => Fin n) t (fun j : Fin 0 => Fin.elim0 j)
  have hvec : separationVector A (singletonEmbedding i) (emptyEmbedding n) t .odd =
      fun q => if q = t then A i t else 0 := by
    funext q
    by_cases hqt : q = t
    · subst q
      simp [separationVector, separationParity, singletonEmbedding, emptyEmbedding, hsnoc]
    · simp [separationVector, separationParity, singletonEmbedding, emptyEmbedding, hqt]
  rw [hvec] at h
  simpa [dotProduct] using h

def Balanced (E O rho sigma : R) : Prop :=
  E * rho + O * sigma = E * sigma + O * rho

def MinorBalanced (A : Matrix (Fin n) (Fin n) R) {k : Nat}
    (I C : Fin k -> Fin n) (rho sigma : R) : Prop :=
  Balanced (minorHalf A .even I C) (minorHalf A .odd I C) rho sigma

def CoefficientStage (A : Matrix (Fin n) (Fin n) R) (t : Fin n)
    (rho sigma : R) (k : Nat) : Prop :=
  ∀ (I K : Fin k ↪ Fin n),
    (∀ j : Fin k, K j ≠ t) -> MinorBalanced A I K rho sigma

def coefficientEvenCofactor
    (A : Matrix (Fin n) (Fin n) R) {k : Nat}
    (L : Fin (k + 1) ↪ Fin n) (K : Fin k -> Fin n) (r : Fin (k + 1)) : R :=
  minorHalf A (if r = 0 then .even else .odd) (dropEmbedding L r) K

def coefficientOddCofactor
    (A : Matrix (Fin n) (Fin n) R) {k : Nat}
    (L : Fin (k + 1) ↪ Fin n) (K : Fin k -> Fin n) (r : Fin (k + 1)) : R :=
  minorHalf A (if r = 0 then .odd else .even) (dropEmbedding L r) K

def coefficientU
    (A : Matrix (Fin n) (Fin n) R) {k : Nat}
    (L : Fin (k + 1) ↪ Fin n) (K : Fin k -> Fin n)
    (rho sigma : R) : Fin n -> R :=
  scatterVec L (fun r =>
    coefficientEvenCofactor A L K r * rho +
      coefficientOddCofactor A L K r * sigma)

def coefficientV
    (A : Matrix (Fin n) (Fin n) R) {k : Nat}
    (L : Fin (k + 1) ↪ Fin n) (K : Fin k -> Fin n)
    (rho sigma : R) : Fin n -> R :=
  scatterVec L (fun r =>
    coefficientEvenCofactor A L K r * sigma +
      coefficientOddCofactor A L K r * rho)

theorem transpose_mulVec_coefficientU
    (A : Matrix (Fin n) (Fin n) R) {k : Nat}
    (L : Fin (k + 1) ↪ Fin n) (K : Fin k -> Fin n)
    (rho sigma : R) (p : Fin n) :
    A.transpose.mulVec (coefficientU A L K rho sigma) p =
      minorHalf A .even L (Fin.cons p K) * rho +
        minorHalf A .odd L (Fin.cons p K) * sigma := by
  rw [coefficientU, transpose_mulVec_scatterVec,
    minorHalf_cons, minorHalf_cons]
  simp only [coefficientEvenCofactor, coefficientOddCofactor, mul_add]
  rw [Finset.sum_add_distrib, Finset.sum_mul, Finset.sum_mul]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro r hr <;>
    by_cases h0 : r = 0 <;> simp [h0, dropEmbedding] <;> ring

theorem transpose_mulVec_coefficientV
    (A : Matrix (Fin n) (Fin n) R) {k : Nat}
    (L : Fin (k + 1) ↪ Fin n) (K : Fin k -> Fin n)
    (rho sigma : R) (p : Fin n) :
    A.transpose.mulVec (coefficientV A L K rho sigma) p =
      minorHalf A .even L (Fin.cons p K) * sigma +
        minorHalf A .odd L (Fin.cons p K) * rho := by
  rw [coefficientV, transpose_mulVec_scatterVec,
    minorHalf_cons, minorHalf_cons]
  simp only [coefficientEvenCofactor, coefficientOddCofactor, mul_add]
  rw [Finset.sum_add_distrib, Finset.sum_mul, Finset.sum_mul]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro r hr <;>
    by_cases h0 : r = 0 <;> simp [h0, dropEmbedding] <;> ring

theorem minorHalf_cons_mul_eq_of_column
    (A : Matrix (Fin n) (Fin n) R) {k : Nat}
    (I : Fin (k + 1) -> Fin n) (K : Fin k -> Fin n)
    (t : Fin n) (rho sigma : R)
    (hcol : ∀ i : Fin n, A i t * rho = A i t * sigma)
    (e : Parity) :
    minorHalf A e I (Fin.cons t K) * rho =
      minorHalf A e I (Fin.cons t K) * sigma := by
  classical
  unfold minorHalf
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro pi hpi
  by_cases hp : permParity pi = e
  · simp only [hp, if_true, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
    calc
      (A (I (pi 0)) t * ∏ c : Fin k, A (I (pi c.succ)) (K c)) * rho =
          (∏ c : Fin k, A (I (pi c.succ)) (K c)) *
            (A (I (pi 0)) t * rho) := by ring
      _ = (∏ c : Fin k, A (I (pi c.succ)) (K c)) *
            (A (I (pi 0)) t * sigma) := by rw [hcol]
      _ = (A (I (pi 0)) t * ∏ c : Fin k, A (I (pi c.succ)) (K c)) * sigma := by
        ring
  · simp [hp]

theorem minorBalanced_of_not_injective_columns
    (A : Matrix (Fin n) (Fin n) R) {k : Nat}
    (I C : Fin k -> Fin n) (hC : ¬Function.Injective C)
    (rho sigma : R) : MinorBalanced A I C rho sigma := by
  have hEO := minorHalf_eq_of_not_injective_columns A I C hC .even .odd
  simp [MinorBalanced, Balanced, hEO, add_comm]

theorem coefficientStage_top
    (A : Matrix (Fin (k + 2)) (Fin (k + 2)) R)
    (hT : Function.Injective A.transpose.mulVec)
    (t : Fin (k + 2)) (rho sigma : R)
    (hcol : ∀ i : Fin (k + 2), A i t * rho = A i t * sigma) :
    CoefficientStage A t rho sigma (k + 1) := by
  intro I K hKt
  have htK : t ∉ Set.range K := by
    rintro ⟨j, hj⟩
    exact hKt j hj
  obtain ⟨s, hs⟩ := exists_not_mem_range_of_embedding I (by omega)
  let L : Fin (k + 2) ↪ Fin (k + 2) := Fin.Embedding.cons I hs
  let u := coefficientU A L K rho sigma
  let v := coefficientV A L K rho sigma
  have himage : A.transpose.mulVec u = A.transpose.mulVec v := by
    funext p
    dsimp [u, v]
    rw [transpose_mulVec_coefficientU, transpose_mulVec_coefficientV]
    change MinorBalanced A L (Fin.cons p K) rho sigma
    by_cases hpK : p ∈ Set.range K
    · apply minorBalanced_of_not_injective_columns A L (Fin.cons p K)
      intro hC
      exact (Fin.cons_injective_iff.mp hC).1 hpK
    · have hpt : p = t := eq_of_not_mem_range_codim_one K hpK htK
      subst p
      have hE := minorHalf_cons_mul_eq_of_column A L K t rho sigma hcol .even
      have hO := minorHalf_cons_mul_eq_of_column A L K t rho sigma hcol .odd
      unfold MinorBalanced Balanced
      rw [hE, hO]
  have huv : u = v := hT himage
  have hrow := congrFun huv (L 0)
  dsimp [u, v] at hrow
  simp only [coefficientU, coefficientV, scatterVec_apply] at hrow
  have hdrop : dropRow L 0 = (I : Fin (k + 1) -> Fin (k + 2)) := by
    funext j
    simp [L, dropRow]
  simpa [MinorBalanced, Balanced, coefficientEvenCofactor,
    coefficientOddCofactor, dropEmbedding, hdrop] using hrow

theorem coefficientStage_step
    (A : Matrix (Fin n) (Fin n) R)
    (hT : Function.Injective A.transpose.mulVec)
    (t : Fin n) (rho sigma : R)
    (hcol : ∀ i : Fin n, A i t * rho = A i t * sigma)
    (k : Nat) (hkn : k < n)
    (hnext : CoefficientStage A t rho sigma (k + 1)) :
    CoefficientStage A t rho sigma k := by
  intro I K hKt
  have htK : t ∉ Set.range K := by
    rintro ⟨j, hj⟩
    exact hKt j hj
  obtain ⟨s, hs⟩ := exists_not_mem_range_of_embedding I hkn
  let L : Fin (k + 1) ↪ Fin n := Fin.Embedding.cons I hs
  let u := coefficientU A L K rho sigma
  let v := coefficientV A L K rho sigma
  have himage : A.transpose.mulVec u = A.transpose.mulVec v := by
    funext p
    dsimp [u, v]
    rw [transpose_mulVec_coefficientU, transpose_mulVec_coefficientV]
    change MinorBalanced A L (Fin.cons p K) rho sigma
    by_cases hpK : p ∈ Set.range K
    · apply minorBalanced_of_not_injective_columns A L (Fin.cons p K)
      intro hC
      exact (Fin.cons_injective_iff.mp hC).1 hpK
    · by_cases hpt : p = t
      · subst p
        have hE := minorHalf_cons_mul_eq_of_column A L K t rho sigma hcol .even
        have hO := minorHalf_cons_mul_eq_of_column A L K t rho sigma hcol .odd
        unfold MinorBalanced Balanced
        rw [hE, hO]
      · let Kp : Fin (k + 1) ↪ Fin n := Fin.Embedding.cons K hpK
        have hKpt : ∀ j : Fin (k + 1), Kp j ≠ t := by
          intro j
          cases j using Fin.cases with
          | zero =>
              simpa [Kp] using hpt
          | succ j =>
              simpa [Kp] using hKt j
        simpa [Kp] using hnext L Kp hKpt
  have huv : u = v := hT himage
  have hrow := congrFun huv (L 0)
  dsimp [u, v] at hrow
  simp only [coefficientU, coefficientV, scatterVec_apply] at hrow
  have hdrop : dropRow L 0 = (I : Fin k -> Fin n) := by
    funext j
    simp [L, dropRow]
  simpa [MinorBalanced, Balanced, coefficientEvenCofactor,
    coefficientOddCofactor, dropEmbedding, hdrop] using hrow

theorem coefficientStage_bottom
    (A : Matrix (Fin n) (Fin n) R) (t : Fin n) (rho sigma : R)
    (hzero : CoefficientStage A t rho sigma 0) : rho = sigma := by
  have havoid : ∀ j : Fin 0, (emptyEmbedding n) j ≠ t := by
    intro j
    exact Fin.elim0 j
  have h := hzero (emptyEmbedding n) (emptyEmbedding n) havoid
  simpa [MinorBalanced, Balanced] using h

theorem descendToZero (P : Nat -> Prop) :
    ∀ N : Nat, P N -> (∀ m : Nat, m < N -> P (m + 1) -> P m) -> P 0
  | 0, h0, _ => h0
  | N + 1, htop, hstep =>
      descendToZero P N
        (hstep N (Nat.lt_succ_self N) htop)
        (fun m hm hnext =>
          hstep m (Nat.lt_trans hm (Nat.lt_succ_self N)) hnext)

structure MinorDescentCertificate (A : Matrix (Fin n) (Fin n) R) where
  separationTop :
    ∀ (_h2 : 2 ≤ n) (_hT : Function.Injective A.transpose.mulVec)
      (x y : Fin n -> R), A.mulVec x = A.mulVec y ->
        SeparationStage A x y (n - 2)
  separationStep :
    ∀ (_h2 : 2 ≤ n) (_hT : Function.Injective A.transpose.mulVec)
      (x y : Fin n -> R) (_hxy : A.mulVec x = A.mulVec y) (m : Nat),
      m < n - 2 -> SeparationStage A x y (m + 1) -> SeparationStage A x y m
  separationBottom :
    ∀ (_h2 : 2 ≤ n) (_hT : Function.Injective A.transpose.mulVec)
      (x y : Fin n -> R) (_hxy : A.mulVec x = A.mulVec y),
      SeparationStage A x y 0 ->
        ∀ i t : Fin n, A i t * x t = A i t * y t
  coefficientTop :
    ∀ (_h2 : 2 ≤ n) (_hT : Function.Injective A.transpose.mulVec)
      (t : Fin n) (rho sigma : R),
      (∀ i : Fin n, A i t * rho = A i t * sigma) ->
        CoefficientStage A t rho sigma (n - 1)
  coefficientStep :
    ∀ (_h2 : 2 ≤ n) (_hT : Function.Injective A.transpose.mulVec)
      (t : Fin n) (rho sigma : R)
      (_hcol : ∀ i : Fin n, A i t * rho = A i t * sigma) (k : Nat),
      k < n - 1 -> CoefficientStage A t rho sigma (k + 1) ->
        CoefficientStage A t rho sigma k
  coefficientBottom :
    ∀ (_h2 : 2 ≤ n) (_hT : Function.Injective A.transpose.mulVec)
      (t : Fin n) (rho sigma : R)
      (_hcol : ∀ i : Fin n, A i t * rho = A i t * sigma),
      CoefficientStage A t rho sigma 0 -> rho = sigma

theorem minorDescentCertificate_addTwo
    (A : Matrix (Fin (k + 2)) (Fin (k + 2)) R) :
    MinorDescentCertificate A where
  separationTop := by
    intro h2 hT x y hxy
    simpa using separationStage_top A hT hxy
  separationStep := by
    intro h2 hT x y hxy m hm hnext
    apply separationStage_step A hT hxy m (by omega) hnext
  separationBottom := by
    intro h2 hT x y hxy hzero i t
    exact separationStage_bottom A hzero i t
  coefficientTop := by
    intro h2 hT t rho sigma hcol
    simpa using coefficientStage_top A hT t rho sigma hcol
  coefficientStep := by
    intro h2 hT t rho sigma hcol m hm hnext
    apply coefficientStage_step A hT t rho sigma hcol m (by omega) hnext
  coefficientBottom := by
    intro h2 hT t rho sigma hcol hzero
    exact coefficientStage_bottom A t rho sigma hzero

theorem separationStage_zero_of_certificate
    (A : Matrix (Fin n) (Fin n) R) (cert : MinorDescentCertificate A)
    (h2 : 2 ≤ n) (hT : Function.Injective A.transpose.mulVec)
    {x y : Fin n -> R} (hxy : A.mulVec x = A.mulVec y) :
    SeparationStage A x y 0 := by
  apply descendToZero (fun m => SeparationStage A x y m) (n - 2)
  · exact cert.separationTop h2 hT x y hxy
  · intro m hm hnext
    exact cert.separationStep h2 hT x y hxy m hm hnext

theorem individualSummand_of_certificate
    (A : Matrix (Fin n) (Fin n) R) (cert : MinorDescentCertificate A)
    (h2 : 2 ≤ n) (hT : Function.Injective A.transpose.mulVec)
    {x y : Fin n -> R} (hxy : A.mulVec x = A.mulVec y)
    (i t : Fin n) : A i t * x t = A i t * y t := by
  exact cert.separationBottom h2 hT x y hxy
    (separationStage_zero_of_certificate A cert h2 hT hxy) i t

theorem coefficientStage_zero_of_certificate
    (A : Matrix (Fin n) (Fin n) R) (cert : MinorDescentCertificate A)
    (h2 : 2 ≤ n) (hT : Function.Injective A.transpose.mulVec)
    (t : Fin n) (rho sigma : R)
    (hcol : ∀ i : Fin n, A i t * rho = A i t * sigma) :
    CoefficientStage A t rho sigma 0 := by
  apply descendToZero (fun m => CoefficientStage A t rho sigma m) (n - 1)
  · exact cert.coefficientTop h2 hT t rho sigma hcol
  · intro m hm hnext
    exact cert.coefficientStep h2 hT t rho sigma hcol m hm hnext

theorem removeColumnCoefficient_of_certificate
    (A : Matrix (Fin n) (Fin n) R) (cert : MinorDescentCertificate A)
    (h2 : 2 ≤ n) (hT : Function.Injective A.transpose.mulVec)
    (t : Fin n) (rho sigma : R)
    (hcol : ∀ i : Fin n, A i t * rho = A i t * sigma) : rho = sigma := by
  exact cert.coefficientBottom h2 hT t rho sigma hcol
    (coefficientStage_zero_of_certificate A cert h2 hT t rho sigma hcol)

theorem injective_of_transpose_injective_of_certificate
    (A : Matrix (Fin n) (Fin n) R) (cert : MinorDescentCertificate A)
    (h2 : 2 ≤ n) (hT : Function.Injective A.transpose.mulVec) :
    Function.Injective A.mulVec := by
  intro x y hxy
  funext t
  apply removeColumnCoefficient_of_certificate A cert h2 hT t (x t) (y t)
  intro i
  exact individualSummand_of_certificate A cert h2 hT hxy i t

theorem mulVec_injective_iff_transpose_mulVec_injective_of_certificates
    (A : Matrix (Fin n) (Fin n) R) (h2 : 2 ≤ n)
    (certA : MinorDescentCertificate A)
    (certAT : MinorDescentCertificate A.transpose) :
    Function.Injective A.mulVec ↔ Function.Injective A.transpose.mulVec := by
  constructor
  · intro hA
    have h := injective_of_transpose_injective_of_certificate
      (A := A.transpose) certAT h2 (by simpa using hA)
    simpa using h
  · exact injective_of_transpose_injective_of_certificate A certA h2

theorem injective_of_transpose_injective_addTwo
    (A : Matrix (Fin (k + 2)) (Fin (k + 2)) R)
    (hT : Function.Injective A.transpose.mulVec) :
    Function.Injective A.mulVec :=
  injective_of_transpose_injective_of_certificate A
    (minorDescentCertificate_addTwo A) (by omega) hT

theorem mulVec_injective_iff_transpose_mulVec_injective_addTwo
    (A : Matrix (Fin (k + 2)) (Fin (k + 2)) R) :
    Function.Injective A.mulVec ↔ Function.Injective A.transpose.mulVec := by
  constructor
  · intro hA
    have h := injective_of_transpose_injective_addTwo (A := A.transpose) (by simpa using hA)
    simpa using h
  · exact injective_of_transpose_injective_addTwo A

theorem mulVec_injective_fin0
    (A : Matrix (Fin 0) (Fin 0) R) : Function.Injective A.mulVec := by
  intro x y h
  funext i
  exact Fin.elim0 i

theorem mulVec_injective_iff_transpose_mulVec_injective_fin0
    (A : Matrix (Fin 0) (Fin 0) R) :
    Function.Injective A.mulVec ↔ Function.Injective A.transpose.mulVec := by
  constructor <;> intro _
  · exact mulVec_injective_fin0 A.transpose
  · exact mulVec_injective_fin0 A

omit [CommSemiring R] in
theorem transpose_eq_self_fin1
    (A : Matrix (Fin 1) (Fin 1) R) : A.transpose = A := by
  ext i j
  fin_cases i
  fin_cases j
  rfl

theorem mulVec_injective_iff_transpose_mulVec_injective_fin1
    (A : Matrix (Fin 1) (Fin 1) R) :
    Function.Injective A.mulVec ↔ Function.Injective A.transpose.mulVec := by
  rw [transpose_eq_self_fin1 A]

theorem mulVec_injective_iff_transpose_mulVec_injective
    (A : Matrix (Fin n) (Fin n) R) :
    Function.Injective A.mulVec ↔ Function.Injective A.transpose.mulVec := by
  cases n with
  | zero =>
      exact mulVec_injective_iff_transpose_mulVec_injective_fin0 A
  | succ n =>
      cases n with
      | zero => exact mulVec_injective_iff_transpose_mulVec_injective_fin1 A
      | succ k => exact mulVec_injective_iff_transpose_mulVec_injective_addTwo A

#print axioms TransposeInjectivityGeneral.mulVec_injective_iff_transpose_mulVec_injective

end

end TransposeInjectivityGeneral
