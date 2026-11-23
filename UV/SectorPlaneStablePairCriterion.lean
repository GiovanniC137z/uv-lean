import UV.SectorPlaneStableMassiveSquare
import UV.SectorPlaneMasslessStableSquare
import UV.SectorPlanePinchWitness

/-! Exact boundary criterion for two stable-half scalar lines with identical
routed four-momentum, arbitrary nonnegative depths and masses, one locked
plane and one common positive height. -/

noncomputable section

namespace UV.SectorPlane

open Filter Set UV.Carrier
open scoped Topology ContDiff

variable {E : Type*} [NormedAddCommGroup E]

def Plane.HasStablePairBoundary (diamond : Plane E) (ε₁ ε₂ : Evolution) (a b m₁ m₂ : ℝ) : Prop :=
  let φ := fun z => Complex.exp (-principalSqrt z)
  ∀ K : TopologicalSpace.Compacts MassiveMomentum, ∃ T : CompactMomentumTest K →L[ℂ] ℂ,
    ∀ f : CompactMomentumTest K, Tendsto (fun h => diamond.twoLinePairing ε₁ ε₂ h φ φ a b m₁ m₂ f.value)
      poleBoundaryHeights (𝓝 (directed (T f)))

private theorem finite_on_test (diamond : Plane E) {ε₁ ε₂ : Evolution} {a b m₁ m₂ : ℝ}
    (H : diamond.HasStablePairBoundary ε₁ ε₂ a b m₁ m₂) {f : MassiveMomentum → ℝ}
    (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) :
    let φ := fun z => Complex.exp (-principalSqrt z)
    ∃ z, Tendsto (fun h => diamond.twoLinePairing ε₁ ε₂ h φ φ a b m₁ m₂ (fun q => (f q:ℂ))) poleBoundaryHeights (𝓝 z) := by
  intro φ
  let K : TopologicalSpace.Compacts MassiveMomentum := ⟨tsupport f,hs⟩
  let g := CompactMomentumTest.ofFunction K (fun q => (f q:ℂ))
    (Complex.ofRealCLM.contDiff.comp (contDiff_infty.mp hf 2)) (fun q hq => by
      change (f q : ℂ) = 0
      rw [image_eq_zero_of_notMem_tsupport (show q ∉ tsupport f from hq),Complex.ofReal_zero])
  obtain ⟨T,hT⟩ := H K
  exact ⟨directed (T g),hT g⟩

private theorem eta_injective (diamond : Plane E) : Function.Injective diamond.eta := by
  rintro e₁ e₂ he
  rcases diamond with ⟨s,b,G⟩
  cases s <;> cases e₁ <;> cases e₂ <;> norm_num [Plane.eta,sectorSign,evolutionSign] at *

/-- Equality of the two squared masses is admissible exactly on a common
prescribed side at strictly positive mass. In each excluded case some
smooth compact test precludes a finite directed boundary. -/
theorem Plane.stable_pair_boundary_iff (diamond : Plane E) (ε₁ ε₂ : Evolution) {a b m₁ m₂ : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (h₁ : 0 ≤ m₁) (h₂ : 0 ≤ m₂) :
    diamond.HasStablePairBoundary ε₁ ε₂ a b m₁ m₂ ↔
      m₁^2 ≠ m₂^2 ∨ (0 < m₁ ∧ diamond.eta ε₁ = diamond.eta ε₂) := by
  by_cases hm : m₁^2 = m₂^2
  · have heqm := (sq_eq_sq₀ h₁ h₂).mp hm
    subst m₂
    simp only [ne_self_iff_false,false_or]
    constructor
    · intro H
      have hside : diamond.eta ε₁ = diamond.eta ε₂ := by
        by_contra hd
        have hrev := (eq_or_eq_neg_of_sq_eq_sq (diamond.eta ε₂) (diamond.eta ε₁)
          ((diamond.eta_sq ε₂).trans (diamond.eta_sq ε₁).symm)).resolve_left (Ne.symm hd)
        let u : UnitVector Spatial := ⟨EuclideanSpace.single (0 : Fin 3) (1:ℝ),by simp⟩
        obtain ⟨f,hf,hs,_,hno⟩ := diamond.stable_pinch_smooth_witness ε₁ ε₂ hrev u ha hb h₁
        exact hno (finite_on_test diamond H hf hs)
      refine ⟨?_,hside⟩
      have e := eta_injective diamond hside
      subst ε₂
      rcases h₁.eq_or_lt with h | h
      · subst m₁
        obtain ⟨f,hf,hs,hno⟩ := diamond.massless_same_side_stable_no_boundary ε₁ ha hb
        exact False.elim (hno (finite_on_test diamond H hf hs))
      · exact h
    · rintro ⟨hm,hside⟩
      have e := eta_injective diamond hside
      subst ε₂
      exact fun K => diamond.massive_same_side_stable_distribution ε₁ K hm ha hb
  · exact ⟨fun _ => Or.inl hm,fun _ K => diamond.distinct_stable_scalar_distribution ε₁ ε₂ K ha hb h₁ h₂ hm⟩

end UV.SectorPlane
