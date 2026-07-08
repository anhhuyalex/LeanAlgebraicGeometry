sed -i -e '367,367c\
  have h2 : (Pic0Scheme C).left.residueField ((identitySection C).base default) ⟶ CommRingCat.of k := sorry\
  have h3 : CommRingCat.of k ⟶ (Pic0Scheme C).left.residueField ((identitySection C).base default) := sorry\
  have h4 : h2 ≫ h3 = 𝟙 _ := sorry\
  have h5 : h3 ≫ h2 = 𝟙 _ := sorry\
  exact ⟨Iso.mk h2 h3 h4 h5⟩' AlgebraicJacobian/Picard/Pic0AbelianVariety.lean
