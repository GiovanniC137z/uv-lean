import UV.ContinueFourierHoppingGraph
import UV.ContinueWilsonGraphHopSum

/-! Absolute summation over all independent hopping counts and polynomially
many marked positions per charged circulation, after simultaneous integration
over the scalar, transverse and charged momentum variables. -/

noncomputable section

open MeasureTheory UV.SectorPlane

namespace UV

variable {E V : Type*} [Fintype E] [DecidableEq E] [Fintype V] {n : ℕ} {A : E → Fin n → ℝ}

abbrev HoppingFourierPlacements (d N : V → ℕ) := (v : V) → Fin (d v) → Fin (N v+2)

private theorem weighted_hops (M : ℕ) {r : ℝ} (hr : 0 ≤ r) (hr' : r<1) (B : ℝ) (hB : 0 ≤ B) :
    Summable (fun n : ℕ => ((n:ℝ)+2)^M*(B*r^n)) := by
  have h := wilson_marked_hop_summable M (show 0 ≤ r/2 by positivity) (show 2*(r/2)<1 by linarith)
  rw [show 2*(r/2)=r by ring] at h
  apply Summable.of_nonneg_of_le (fun _ => by positivity) _ (h.mul_left (2^M*B))
  intro n
  have hle : ((n:ℝ)+2)^M ≤ (2*(1+(n:ℝ)))^M := pow_le_pow_left₀ (by positivity) (by linarith [Nat.cast_nonneg (α := ℝ) n]) _
  apply (mul_le_mul_of_nonneg_right hle (mul_nonneg hB (pow_nonneg hr _))).trans_eq
  rw [mul_pow]
  ring

/-- Each marked endpoint or coordinate choice can be independently assigned
to any of the n+2 hops of its loop. The number of such choices is polynomial
at fixed electric order. The common geometric ratio is |g|/m. -/
theorem hopping_fourier_graph_summable [DecidableEq V] (B : WilsonIncidenceBasis A)
    (kind : E → OrderedPhotonKind) (ij : E → Fin 3 × Fin 3) (b : Fin n → OSFourSpace)
    {a m σ g : ℝ} (ha : 0<a) (hg : 2*|g|<m) (hσ : 0<σ) (M : ℕ) (d : V → ℕ)
    (L : (N : V → ℕ) → HoppingFourierPlacements d N → (v : V) →
      (B.Chord → OSFourSpace) → HoppingFourierLoop (N v))
    (hL : ∀ N f v q, (L N f v q).valid m M)
    (hMeas : ∀ N f v, Measurable (fun z : (B.Chord → OSFourSpace) × (ℝ × Spatial) => (L N f v z.1).word g σ z.2))
    (R : ∀ N f q, HoppingFourierMark (L N f · q) ≃ HoppingScalarEnd kind)
    (hr : ∀ N f q (i : HoppingFourierMark (L N f · q)), ((L N f i.1 q).time i.2.1).marks.get i.2.2 =
      hoppingScalarFrequency kind (B.flow b q) (R N f q i)) :
    let G := fun N f => hoppingFourierGraph B kind ij b a g σ (L N f)
    (∀ N f, Integrable (G N f)) ∧ Summable (fun N : V → ℕ => ∑ f : HoppingFourierPlacements d N, ∫ z, ‖G N f z‖) := by
  classical
  intro G
  have hm : 0<m := by linarith [abs_nonneg g]
  have hcost N f := hopping_fourier_graph_absolute B kind ij b ha hm hσ M (L N f) (hL N f) (hMeas N f) (R N f) (hr N f)
  refine ⟨fun N f => (hcost N f).1,?_⟩
  let D := hoppingFourierBudget m g hσ M
  let r := |g|/m
  let W := ∏ c : B.Chord, ∫ p, (kind c).envelope a p
  let S := fun v (k : ℕ) => ((k:ℝ)+2)^(d v)*(D*r^k)
  have hD : 0 ≤ D := hopping_fourier_budget_nonneg hm _ hσ _
  have hr₀ : 0 ≤ r := div_nonneg (abs_nonneg _) hm.le
  have hr₁ : r<1 := (div_lt_one hm).mpr (by linarith [abs_nonneg g])
  have hsum := wilson_summable_independent_lengths (g := S) (fun v k => by dsimp [S]; positivity)
    (fun v => weighted_hops _ hr₀ hr₁ D hD)
  apply Summable.of_nonneg_of_le (fun N => Finset.sum_nonneg fun f _ => integral_nonneg fun _ => norm_nonneg _)
    _ (hsum.mul_left W)
  intro N
  apply (Finset.sum_le_sum (s := Finset.univ) (fun f _ => (hcost N f).2)).trans_eq
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,HoppingFourierPlacements,Fintype.card_pi,
    Finset.prod_const,Fintype.card_fin,Nat.cast_prod,Nat.cast_pow,Nat.cast_add,Nat.cast_ofNat]
  simp only [S,Finset.prod_mul_distrib,W,D,r]
  ring

end UV
