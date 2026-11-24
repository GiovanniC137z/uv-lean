import Mathlib.Data.Fintype.Perm

/-! Finite incidence data of the ordered two-band photon sewing. -/

namespace UV.SectorPlane

/-- An internal pair has one common Coulomb or transverse channel. External
marks in the two-point bound use transverse polarizations. -/
structure OrderedSewingTopology (m : ℕ) where
  pathOrder : Equiv.Perm (Fin m)
  mate : Equiv.Perm (Fin m)
  coulomb : Fin m → Bool
  pair_twice : ∀ i, mate (mate i) = i
  same_channel : ∀ i, coulomb (mate i) = coulomb i
  external_transverse : ∀ i, mate i = i → coulomb i = false

end UV.SectorPlane
