import UV.ContinuePinnedNormalForest
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! Relative source derivatives of the equal-position pinned normal
kernel. Finite product bounds and the chain rule preserve the same
positive duration majorant at every fixed derivative order. -/

noncomputable section
open Real Set MeasureTheory
open scoped BigOperators ContDiff Topology
namespace UV

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

private def pinnedForestValue {N : ℕ} (F : Finset (Finset (Fin N)))
    (τ : Fin N → X → ℝ) (x : X) : ℝ :=
  ∑ S ∈ F, ∏ e ∈ Sᶜ, τ e x

private theorem pinnedForestValue_smooth {N m : ℕ} (F : Finset (Finset (Fin N)))
    (τ : Fin N → X → ℝ) {U : Set X} (hτ : ∀ e, ContDiffOn ℝ m (τ e) U) :
    ContDiffOn ℝ m (pinnedForestValue F τ) U :=
  ContDiffOn.sum (fun _ _ => contDiffOn_prod fun e _ => hτ e)

private def pinnedMonomialJetFactor {N : ℕ} (S : Finset (Fin N)) (C : ℝ) (k : ℕ) :=
  (∑ p ∈ S.sym k, ((p : Multiset (Fin N)).multinomial : ℝ)) * C^S.card

private theorem pinnedMonomialJetFactor_nonneg {N : ℕ} (S : Finset (Fin N)) {C : ℝ} (hC : 0 ≤ C) (k : ℕ) :
    0 ≤ pinnedMonomialJetFactor S C k := by
  unfold pinnedMonomialJetFactor
  positivity

private theorem pinned_monomial_jet_bound {N m k : ℕ} (S : Finset (Fin N)) (τ : Fin N → X → ℝ)
    {U : Set X} (hU : UniqueDiffOn ℝ U) {x : X} (hx : x ∈ U) (hk : k ≤ m)
    (hτ : ∀ e, ContDiffOn ℝ m (τ e) U)
    {C : ℝ} (hjet : ∀ e j, j ≤ m → ‖iteratedFDerivWithin ℝ j (τ e) U x‖ ≤ C*τ e x) :
    ‖iteratedFDerivWithin ℝ k (fun y => ∏ e ∈ S, τ e y) U x‖ ≤
      pinnedMonomialJetFactor S C k * ∏ e ∈ S, τ e x := by
  refine (norm_iteratedFDerivWithin_prod_le (u := S) (f := τ) (fun e _ => hτ e) hU hx
    (by exact_mod_cast hk)).trans ?_
  calc
    _ ≤ ∑ p ∈ S.sym k, ((p : Multiset (Fin N)).multinomial : ℝ) *
        (C^S.card * ∏ e ∈ S, τ e x) := by
      apply Finset.sum_le_sum
      intro p _
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      have h (e : Fin N) : (p : Multiset (Fin N)).count e ≤ m := by
        apply le_trans _ hk
        simpa only [Sym.card_coe] using Multiset.count_le_card e (p : Multiset (Fin N))
      have hh := Finset.prod_le_prod (s := S)
        (f := fun e => ‖iteratedFDerivWithin ℝ ((p : Multiset (Fin N)).count e) (τ e) U x‖)
        (g := fun e => C*τ e x) (fun _ _ => norm_nonneg _) (fun e _ => hjet e _ (h e))
      rwa [Finset.prod_mul_distrib,Finset.prod_const] at hh
    _ = _ := by rw [← Finset.sum_mul,pinnedMonomialJetFactor,mul_assoc]

private theorem pinned_forest_jet_bound {N m : ℕ} (F : Finset (Finset (Fin N))) (τ : Fin N → X → ℝ)
    {U : Set X} (hU : UniqueDiffOn ℝ U) (hτ : ∀ e, ContDiffOn ℝ m (τ e) U)
    (hpos : ∀ x ∈ U, ∀ e, 0 < τ e x) {C : ℝ} (hC : 0 ≤ C)
    (hjet : ∀ x ∈ U, ∀ e j, j ≤ m → ‖iteratedFDerivWithin ℝ j (τ e) U x‖ ≤ C*τ e x) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ x ∈ U, ∀ k ≤ m,
      ‖iteratedFDerivWithin ℝ k (pinnedForestValue F τ) U x‖ ≤ K*pinnedForestValue F τ x := by
  let g := fun (S : Finset (Fin N)) j => pinnedMonomialJetFactor Sᶜ C j
  let K := 1 + ∑ S ∈ F, ∑ j ∈ Finset.range (m+1), g S j
  have hg (S : Finset (Fin N)) (j : ℕ) : 0 ≤ g S j := pinnedMonomialJetFactor_nonneg _ hC _
  refine ⟨K,le_add_of_nonneg_right (Finset.sum_nonneg fun S _ => Finset.sum_nonneg fun j _ => hg S j),?_⟩
  intro x hx k hk
  have hK (S : Finset (Fin N)) (hS : S ∈ F) : g S k ≤ K := by
    exact (Finset.single_le_sum (fun j _ => hg S j) (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))).trans
      ((Finset.single_le_sum (fun T _ => Finset.sum_nonneg fun j _ => hg T j) hS).trans
        (le_add_of_nonneg_left zero_le_one))
  unfold pinnedForestValue
  rw [iteratedFDerivWithin_sum_apply hU hx
    (fun S _ => (contDiffOn_prod fun e (_ : e ∈ Sᶜ) => (hτ e).of_le (by exact_mod_cast hk)) x hx)]
  calc
    _ ≤ ∑ S ∈ F, ‖iteratedFDerivWithin ℝ k (fun y => ∏ e ∈ Sᶜ, τ e y) U x‖ := norm_sum_le _ _
    _ ≤ ∑ S ∈ F, K * ∏ e ∈ Sᶜ, τ e x := by
      apply Finset.sum_le_sum
      intro S hS
      exact (pinned_monomial_jet_bound Sᶜ τ hU hx hk hτ (hjet x hx)).trans
        (mul_le_mul_of_nonneg_right (hK S hS) (Finset.prod_nonneg fun e _ => (hpos x hx e).le))
    _ = _ := (Finset.mul_sum _ _ _).symm

omit [NormedAddCommGroup X] [NormedSpace ℝ X] in
private theorem pinnedForestValue_pos {N : ℕ} (F : Finset (Finset (Fin N))) (hF : F.Nonempty)
    (τ : Fin N → X → ℝ) (x : X) (hp : ∀ e, 0 < τ e x) : 0 < pinnedForestValue F τ x :=
  Finset.sum_pos (fun _ _ => Finset.prod_pos fun e _ => hp e) hF

private theorem pinned_forest_power_jet_bound {N m : ℕ} (F : Finset (Finset (Fin N))) (hF : F.Nonempty)
    (τ : Fin N → X → ℝ) {U : Set X} (hU : UniqueDiffOn ℝ U) (hτ : ∀ e, ContDiffOn ℝ m (τ e) U)
    (hpos : ∀ x ∈ U, ∀ e, 0 < τ e x) {C : ℝ} (hC : 0 ≤ C)
    (hjet : ∀ x ∈ U, ∀ e j, j ≤ m → ‖iteratedFDerivWithin ℝ j (τ e) U x‖ ≤ C*τ e x) (a : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x ∈ U,
      ‖iteratedFDerivWithin ℝ m (fun y => pinnedForestValue F τ y ^ a) U x‖ ≤
        K*pinnedForestValue F τ x ^ a := by
  let P := pinnedForestValue F τ
  let g := fun s : ℝ => s^a
  let V := Ioi (0:ℝ)
  have hP : ContDiffOn ℝ m P U := pinnedForestValue_smooth F τ hτ
  have hP₀ (x : X) (hx : x ∈ U) : 0 < P x := pinnedForestValue_pos F hF τ x (hpos x hx)
  have hg : ContDiffOn ℝ m g V := fun _ hx => (contDiffAt_rpow_const_of_ne (mem_Ioi.mp hx).ne').contDiffWithinAt
  let M := ∑ j ∈ Finset.range (m+1), ‖iteratedFDerivWithin ℝ j g V 1‖
  have hM : 0 ≤ M := Finset.sum_nonneg fun _ _ => norm_nonneg _
  obtain ⟨K,hK,hKjet⟩ := pinned_forest_jet_bound F τ hU hτ hpos hC hjet
  have hK₀ : 0 ≤ K := zero_le_one.trans hK
  refine ⟨(m.factorial:ℝ)*M*K^m,by positivity,?_⟩
  intro x hx
  let f := fun y : X => (P x)⁻¹ • P y
  have hpx := hP₀ x hx
  have hf : ContDiffOn ℝ m f U := hP.const_smul _
  have hfx : f x = 1 := by unfold f; rw [smul_eq_mul,inv_mul_cancel₀ hpx.ne']
  have hMaps : MapsTo f U V := fun y hy => mul_pos (inv_pos.mpr hpx) (hP₀ y hy)
  have hh := norm_iteratedFDerivWithin_comp_le hg hf (le_refl (m : WithTop ℕ∞))
    isOpen_Ioi.uniqueDiffOn hU hMaps hx (C := M) (D := K) (n := m) (by
      intro j hj
      rw [hfx]
      exact Finset.single_le_sum (f := fun i : ℕ => ‖iteratedFDerivWithin ℝ i g V 1‖)
        (fun i _ => norm_nonneg _) (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))) (by
      intro j hj hjm
      have hDiff : ContDiffWithinAt ℝ j P U x := (hP x hx).of_le (by exact_mod_cast hjm)
      change ‖iteratedFDerivWithin ℝ j ((P x)⁻¹ • P) U x‖ ≤ K^j
      rw [iteratedFDerivWithin_const_smul_apply hDiff hU hx,norm_smul,
        Real.norm_of_nonneg (inv_pos.mpr hpx).le]
      calc
        _ ≤ (P x)⁻¹*(K*P x) := mul_le_mul_of_nonneg_left (hKjet x hx j hjm) (inv_pos.mpr hpx).le
        _ = K := by rw [mul_left_comm,inv_mul_cancel₀ hpx.ne',mul_one]
        _ ≤ _ := le_self_pow₀ hK (Nat.one_le_iff_ne_zero.mp hj))
  have he : EqOn (fun y => P y^a) (P x ^ a • (g ∘ f)) U := by
    intro y hy
    have hPfx : P x * f y = P y := by unfold f; rw [smul_eq_mul,← mul_assoc,mul_inv_cancel₀ hpx.ne',one_mul]
    change P y^a = P x^a*(f y)^a
    rw [← mul_rpow hpx.le (hMaps hy).le,hPfx]
  change ‖iteratedFDerivWithin ℝ m (fun y => P y^a) U x‖ ≤ _
  rw [iteratedFDerivWithin_congr he hx,iteratedFDerivWithin_const_smul_apply ((hg.comp hf hMaps) x hx) hU hx,
    norm_smul,Real.norm_of_nonneg (rpow_nonneg hpx.le _),mul_comm]
  exact mul_le_mul_of_nonneg_right hh (rpow_nonneg hpx.le _)

/-- At equal held positions, every fixed ordinary source derivative
of the integrated normal heat kernel obeys the original duration majorant. -/
theorem pinnedHeld_heat_relative_source_jet {L N d m : ℕ} {B : Type*} (b : B)
    (G : SimpleGraph (Fin L ⊕ B)) (src dst : Fin N → Fin L ⊕ B) (hG : G.Connected)
    (hcover : ∀ u v, G.Adj u v → ∃ e, (src e = u ∧ dst e = v) ∨ (src e = v ∧ dst e = u))
    {D : ℝ} (hD : 0 < D) (τ : Fin N → X → ℝ) {U : Set X} (hU : IsOpen U)
    (hτ : ∀ e, ContDiffOn ℝ m (τ e) U) (hpos : ∀ x ∈ U, ∀ e, 0 < τ e x) {C : ℝ} (hC : 0 ≤ C)
    (hjet : ∀ x ∈ U, ∀ e j, j ≤ m → ‖iteratedFDerivWithin ℝ j (τ e) U x‖ ≤ C*τ e x) :
    let F := fun x : X => (∫ y : Fin d → EuclideanSpace ℝ (Fin L),
      pinnedHeldHeatProduct src dst D (fun e => τ e x) y)
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x ∈ U, ‖iteratedFDerivWithin ℝ m F U x‖ ≤ K*F x := by
  dsimp only
  let P := pinnedRootedForestSelections src dst
  let H := fun x : X => pinnedForestValue P τ x^(-(d:ℝ)/2)
  let c := (4*π*D)^(-((N:ℝ)-L)*((d:ℝ)/2))
  have hc : 0 ≤ c := rpow_nonneg (by positivity) _
  have hP := pinnedRootedForestSelections_nonempty b G src dst hG hcover
  have hH : ContDiffOn ℝ m H U := by
    intro x hx
    have hp := pinnedForestValue_pos P hP τ x (hpos x hx)
    exact (contDiffAt_rpow_const_of_ne hp.ne').comp_contDiffWithinAt x
      ((pinnedForestValue_smooth P τ hτ) x hx)
  have he : EqOn (fun x : X => (∫ y : Fin d → EuclideanSpace ℝ (Fin L),
      pinnedHeldHeatProduct src dst D (fun e => τ e x) y)) (c • H) U :=
    fun x hx => pinnedHeldHeatIntegral_forest b G src dst hG hcover hD _ (hpos x hx)
  obtain ⟨K,hK,h⟩ := pinned_forest_power_jet_bound P hP τ hU.uniqueDiffOn hτ hpos hC hjet (-(d:ℝ)/2)
  refine ⟨K,hK,fun x hx => ?_⟩
  have hv : (∫ y : Fin d → EuclideanSpace ℝ (Fin L), pinnedHeldHeatProduct src dst D (fun e => τ e x) y) =
      c*H x := he hx
  rw [iteratedFDerivWithin_congr he hx,hv,iteratedFDerivWithin_const_smul_apply (hH x hx) hU.uniqueDiffOn hx,
    norm_smul,Real.norm_of_nonneg hc,mul_left_comm K c]
  exact mul_le_mul_of_nonneg_left (h x hx) hc

end UV
