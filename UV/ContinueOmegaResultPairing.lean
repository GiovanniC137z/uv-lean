import UV.ContinueOmegaResultChiral
import Mathlib.CategoryTheory.Groupoid

/-! The mass-pairing test for an entire connected component of support
arrows. A choice of arrows from the base realizes the explicit extension
of an intertwiner for its isotropy group. -/

noncomputable section

open CategoryTheory

namespace UV

structure OmegaUnitaryTransport {X : Type*} [Groupoid X] (V : X → Type*) [∀ x, NormedAddCommGroup (V x)]
    [∀ x, InnerProductSpace ℂ (V x)] where
  along : ∀ {x y : X}, (x ⟶ y) → V x ≃ₗᵢ[ℂ] V y
  along_comp : ∀ {x y z : X} (a : x ⟶ y) (b : y ⟶ z) (v : V x), along (a ≫ b) v = along b (along a v)

theorem omega_component_pairing_iff {X : Type*} [Groupoid X] {V W : X → Type*}
    [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℂ (V x)]
    [∀ x, NormedAddCommGroup (W x)] [∀ x, InnerProductSpace ℂ (W x)]
    (P : OmegaUnitaryTransport V) (R : OmegaUnitaryTransport W)
    (Q : ∀ x, V x → V x) (S : ∀ x, W x → W x)
    (hq : ∀ {x y} (f : x ⟶ y) v, P.along f (Q x v) = Q y (P.along f v))
    (hs : ∀ {x y} (f : x ⟶ y) v, R.along f (S x v) = S y (R.along f v))
    (o : X) (a : ∀ x, o ⟶ x) :
    (∃ J : ∀ x, V x ≃ₗᵢ[ℂ] W x, (∀ x v, J x (Q x v) = S x (J x v)) ∧
      ∀ {x y} (f : x ⟶ y) v, J y (P.along f v) = R.along f (J x v)) ↔
    (∃ J : V o ≃ₗᵢ[ℂ] W o, (∀ v, J (Q o v) = S o (J v)) ∧
      ∀ (h : o ⟶ o) v, J (P.along h v) = R.along h (J v)) := by
  constructor
  · rintro ⟨J,H,N⟩
    exact ⟨J o,H o,fun f => N f⟩
  · rintro ⟨B,H,N⟩
    let J := fun x => (((P.along (a x)).symm.trans B).trans (R.along (a x)))
    have ha x v : J x (P.along (a x) v) = R.along (a x) (B v) := by simp [J]
    refine ⟨J,?_,?_⟩
    · intro x v
      obtain ⟨u,rfl⟩ := (P.along (a x)).surjective v
      rw [←hq,ha,ha,H,hs]
    · intro x y f v
      obtain ⟨u,rfl⟩ := (P.along (a x)).surjective v
      let h : o ⟶ o := (a x ≫ f) ≫ Groupoid.inv (a y)
      have he : h ≫ a y = a x ≫ f := by simp [h]
      rw [←P.along_comp,←he,P.along_comp,ha,N,←R.along_comp,he,R.along_comp,ha]

end UV
