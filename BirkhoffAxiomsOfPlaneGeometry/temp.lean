import Mathlib

lemma angle_def_aux01 (x : ℝ) (H : x ∈ Set.Icc (-Real.pi) Real.pi)
    (H0 : 0 ≤ (Real.Angle.coe x).toReal) :
    x = - Real.pi ∨ x ∈ Set.Icc 0 Real.pi := by
  have H1 : x = - Real.pi ∨ x ∈ Set.Ioc (- Real.pi) Real.pi := by grind
  obtain H1 | H1 := H1
  · left; exact H1
  · right
    contrapose! H0
    simp at *
    obtain ⟨H2, H3⟩ := H1
    apply eq_or_lt_of_le at H3
    obtain H3 | H3 := H3
    · rw [H3] at H0
      linarith [H0 Real.pi_nonneg]
    · obtain H4 | H4 := lt_or_ge x 0
      · rw [Real.Angle.toReal_coe,
           (toIocMod_eq_self Real.two_pi_pos).mpr ⟨by linarith, by linarith⟩]
        exact H4
      · linarith [H0 H4]
