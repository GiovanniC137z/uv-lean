import UV.VerifyCurvatureProductMoments
import UV.RevisionOSWick

/-! Exact Isserlis pairings of finite lists of signed sector-plane modes.
The product moment recurrence uses independent real coordinates, while
`osWickMoment` enumerates the individual partner choices. -/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace UV.VerifyCurvaturePairings

open UV.NextCurvatureLaw UV.VerifyCurvatureProductMoments

variable {ι : Type*} [DecidableEq ι]

def diagonalCovariance (σ : ι → ℝ) (i j : ι) : ℝ := if i = j then σ i else 0

private def factorProduct (μ : ι → ℕ → ℝ) (s : Finset ι) (l : List ι) : ℝ :=
  ∏ i ∈ s, μ i (l.count i)

private theorem count_selected_eraseIdx (l : List ι) (k : ℕ) (hk : k < l.length)
    (i : ι) (he : l[k] = i) : (l.eraseIdx k).count i = l.count i - 1 := by
  have h := (List.getElem_cons_eraseIdx_perm hk).count_eq i
  rw [he, List.count_cons_self] at h
  omega

private theorem count_other_eraseIdx (l : List ι) (k : ℕ) (hk : k < l.length)
    (i : ι) (hi : l[k] ≠ i) : (l.eraseIdx k).count i = l.count i := by
  have h := (List.getElem_cons_eraseIdx_perm hk).count_eq i
  simpa only [List.count_cons_of_ne hi] using h

private theorem factorProduct_cons (μ : ι → ℕ → ℝ) {s : Finset ι}
    {a : ι} (ha : a ∈ s) (l : List ι) : factorProduct μ s (a :: l) =
      μ a (l.count a + 1) * ∏ i ∈ s.erase a, μ i (l.count i) := by
  unfold factorProduct
  rw [← Finset.mul_prod_erase s (fun i => μ i ((a :: l).count i)) ha, List.count_cons_self]
  apply congrArg (μ a (l.count a + 1) * ·)
  exact Finset.prod_congr rfl fun i hi => by rw [List.count_cons_of_ne (Ne.symm (Finset.ne_of_mem_erase hi))]

private theorem factorProduct_erase_partner (μ : ι → ℕ → ℝ) {s : Finset ι}
    {a : ι} (ha : a ∈ s) (l : List ι) (k : ℕ) (hk : k < l.length) (he : l[k] = a) :
    factorProduct μ s (l.eraseIdx k) =
      μ a (l.count a - 1) * ∏ i ∈ s.erase a, μ i (l.count i) := by
  unfold factorProduct
  rw [← Finset.mul_prod_erase s (fun i => μ i ((l.eraseIdx k).count i)) ha,
    count_selected_eraseIdx l k hk a he]
  apply congrArg (μ a (l.count a - 1) * ·)
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [count_other_eraseIdx l k hk i (fun hh => Finset.ne_of_mem_erase hi (he.symm.trans hh).symm)]

private theorem sum_indicator_count (l : List ι) (i : ι) (x : ℝ) :
    (l.map fun j => if j = i then x else 0).sum = (l.count i : ℝ) * x := by
  induction l with
  | nil => simp
  | cons j l ih =>
    by_cases h : j = i
    · subst j
      simp only [List.map_cons, List.sum_cons, if_true, List.count_cons_self, Nat.cast_add,
        Nat.cast_one, ih]
      ring
    · simp only [List.map_cons, List.sum_cons, if_neg h, List.count_cons_of_ne h, zero_add, ih]

private theorem sum_zipped_indicator_count (l : List ι) (i : ι) (x : ℝ) :
    ((l.zipIdx 0).map fun j => if j.1 = i then x else 0).sum = (l.count i : ℝ) * x := by
  have h : ((l.zipIdx 0).map fun j => if j.1 = i then x else 0) =
      l.map fun j => if j = i then x else 0 := by
    calc
      _ = ((l.zipIdx 0).map Prod.fst).map (fun j => if j = i then x else 0) := by
        rw [List.map_map]
        rfl
      _ = _ := by rw [List.zipIdx_map_fst]
  rw [h, sum_indicator_count]

/-- The recursive sum over all partners is exactly the product of the
one-coordinate moment recurrences for a diagonal covariance. -/
theorem diagonal_wick_factorization (σ : ι → ℝ) (μ : ι → ℕ → ℝ)
    (hzero : ∀ i, μ i 0 = 1) (hone : ∀ i, μ i 1 = 0)
    (hstep : ∀ i q, μ i (q+2) = ((q : ℝ)+1) * σ i * μ i q)
    (s : Finset ι) (m : ℕ) (l : List ι) (hs : ∀ i ∈ l, i ∈ s) (hm : l.length ≤ 2*m) :
    osWickMoment (diagonalCovariance σ) m l = ∏ i ∈ s, μ i (l.count i) := by
  change osWickMoment (diagonalCovariance σ) m l = factorProduct μ s l
  induction m generalizing l with
  | zero =>
    have hl : l = [] := List.eq_nil_of_length_eq_zero (by simpa using hm)
    subst l
    simp [osWickMoment, factorProduct, hzero]
  | succ m ih =>
    cases l with
    | nil => simp [osWickMoment, factorProduct, hzero]
    | cons a l =>
      have ha := hs a List.mem_cons_self
      let R := μ a (l.count a - 1) * ∏ i ∈ s.erase a, μ i (l.count i)
      have heq : ((l.zipIdx 0).map fun (j, k) => diagonalCovariance σ a j *
          osWickMoment (diagonalCovariance σ) m (l.eraseIdx k)) =
          (l.zipIdx 0).map (fun j => if j.1 = a then σ a * R else 0) := by
        apply List.map_congr_left
        rintro ⟨j,k⟩ hMem
        by_cases hj : j = a
        · subst j
          obtain ⟨_,hk,he⟩ := List.mem_zipIdx hMem
          have hk' : k < l.length := by simpa only [zero_add] using hk
          have he' : l[k] = a := by simpa only [Nat.sub_zero] using he.symm
          have hsub (i : ι) (hi : i ∈ l.eraseIdx k) : i ∈ s :=
            hs i (List.mem_cons_of_mem _ ((l.eraseIdx_sublist k).subset hi))
          have hlen : (l.eraseIdx k).length ≤ 2*m := by
            rw [List.length_eraseIdx_of_lt hk']
            simp only [List.length_cons] at hm
            omega
          change diagonalCovariance σ a a * osWickMoment (diagonalCovariance σ) m
            (l.eraseIdx k) = if a = a then σ a * R else 0
          rw [ih _ hsub hlen, factorProduct_erase_partner μ ha l k hk' he']
          simp only [diagonalCovariance, if_true, R]
        · simp only [diagonalCovariance, if_neg hj, if_neg (Ne.symm hj), zero_mul]
      simp only [osWickMoment, heq, sum_zipped_indicator_count, factorProduct_cons μ ha]
      have hrec : μ a (l.count a + 1) = (l.count a : ℝ) * σ a * μ a (l.count a - 1) := by
        cases h : l.count a with
        | zero => simp [hone]
        | succ q =>
          rw [show q.succ + 1 = q + 2 by omega, hstep]
          simp only [Nat.succ_sub_one, Nat.cast_succ]
      rw [hrec]
      dsimp only [R]
      ring

/-- The standard curvature preparation's actual finite-coordinate
moments equal the existing recursive Wick pairing sum. Repeated factors,
odd products, colors, and the two distinct fields are all included. -/
theorem coordinate_list_wick {n : ℕ} (l : List (ModeSlot n)) (m : ℕ) (hm : l.length ≤ 2*m) :
    Integrable (fun X => (l.map fun i => X i).prod) (commonGaussian n) ∧
    (∫ X, (l.map fun i => X i).prod ∂commonGaussian n) =
      osWickMoment (diagonalCovariance (fun _ => (1/2 : ℝ))) m l := by
  have h := coordinate_list_moment l
  refine ⟨h.1, h.2.trans ?_⟩
  symm
  have hstep (q : ℕ) : scalarPairMoment (q+2) = ((q : ℝ)+1)*(1/2)*scalarPairMoment q := by
    rw [scalarPairMoment]
    ring
  rw [diagonal_wick_factorization (fun _ => (1/2 : ℝ)) (fun _ => scalarPairMoment)
    (fun _ => rfl) (fun _ => rfl) (fun _ q => hstep q) l.toFinset m l
    (fun i hi => List.mem_toFinset.mpr hi) hm]
  refine Finset.prod_congr rfl fun i _ => ?_
  congr 1
  simp only [List.count_eq_countP]
  exact List.countP_congr fun j _ => by simp only [beq_iff_eq]

/-- Each leg scaling belongs to the unique pair which uses that position.
Different occurrences of the same coordinate may carry different scales. -/
theorem osWickMoment_scaled {α β : Type*} (c : β → β → ℝ) (slot : α → β)
    (w : α → ℝ) (m : ℕ) (l : List α) :
    osWickMoment (fun i j => w i * w j * c (slot i) (slot j)) m l =
      (l.map w).prod * osWickMoment c m (l.map slot) := by
  induction m generalizing l with
  | zero => cases l <;> simp [osWickMoment]
  | succ m ih =>
    cases l with
    | nil => simp [osWickMoment]
    | cons a l =>
      simp only [osWickMoment, List.map_cons, List.prod_cons, List.zipIdx_map, List.map_map]
      rw [← List.sum_map_mul_left]
      apply congrArg List.sum
      apply List.map_congr_left
      rintro ⟨b,k⟩ hMem
      change w a * w b * c (slot a) (slot b) *
          osWickMoment (fun i j => w i * w j * c (slot i) (slot j)) m (l.eraseIdx k) =
        w a * (l.map w).prod * (c (slot a) (slot b) * osWickMoment c m ((l.map slot).eraseIdx k))
      obtain ⟨_,hk,he⟩ := List.mem_zipIdx hMem
      have hk' : k < l.length := by simpa only [zero_add] using hk
      have he' : l[k] = b := by simpa only [Nat.sub_zero] using he.symm
      have hw := ((List.getElem_cons_eraseIdx_perm hk').map w).prod_eq
      simp only [List.map_cons, List.prod_cons, he'] at hw
      rw [ih, List.eraseIdx_map, ← hw]
      ring

/-- Exact Wick evaluation of a finite product with separate amplitudes
for interaction legs, probes, and any other fixed occurrences. -/
theorem weighted_coordinate_list_wick {α : Type*} {n : ℕ} (slot : α → ModeSlot n) (w : α → ℝ)
    (l : List α) (m : ℕ) (hm : l.length ≤ 2*m) :
    Integrable (fun X => (l.map fun i => w i * X (slot i)).prod) (commonGaussian n) ∧
    (∫ X, (l.map fun i => w i * X (slot i)).prod ∂commonGaussian n) =
      osWickMoment (fun i j => w i * w j * diagonalCovariance (fun _ => (1/2 : ℝ)) (slot i) (slot j)) m l := by
  have h := coordinate_list_wick (l.map slot) m (by simpa only [List.length_map] using hm)
  have hprod (X : ModeSlot n → ℝ) : (l.map fun i => w i * X (slot i)).prod =
      (l.map w).prod * ((l.map slot).map fun j => X j).prod := by
    rw [List.prod_map_mul, List.map_map]
    rfl
  simp_rw [hprod]
  refine ⟨h.1.const_mul _, ?_⟩
  rw [integral_const_mul, h.2, osWickMoment_scaled]

end UV.VerifyCurvaturePairings
