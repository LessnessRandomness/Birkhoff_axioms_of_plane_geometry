import Mathlib

namespace tinkering

open InnerProductGeometry
open scoped RealInnerProductSpace

variable {V : Type*}
variable [NormedAddCommGroup V]
variable [InnerProductSpace ℝ V]

noncomputable def normalize (x : V) : V := ‖x‖⁻¹ • x

@[simp]
theorem normalize_zero_eq_zero : normalize (0 : V) = 0 := by
  simp [normalize]

@[simp]
lemma norm_normalize_eq_one_iff {x : V} : ‖normalize x‖ = 1 ↔ x ≠ 0 := by
  constructor
  · contrapose!
    rintro rfl
    simp
  · intro h
    simp [normalize, norm_smul, show ‖x‖ ≠ 0 by simp [h]]

@[simp]
lemma normalize_eq_self_of_norm_one {x : V} (h : ‖x‖ = 1) : normalize x = x := by
  simp [normalize, h]

@[simp]
theorem normalize_normalize (x : V) : normalize (normalize x) = normalize x := by
  by_cases hx : x = 0
  · simp [hx]
  rw [← ne_eq, ← norm_normalize_eq_one_iff] at hx
  simp [hx]

theorem normalize_smul_of_pos {r : ℝ} (hr : 0 < r) (x : V) :
    normalize (r • x) = normalize x := by
  by_cases hx : x = 0
  · simp [hx]
  rw [normalize, normalize, smul_smul, norm_smul]
  congr
  simp; field_simp; rw [abs_of_pos hr]

theorem normalize_neg (x : V) : normalize (- x) = - normalize x := by
  by_cases hx : x = 0
  · simp [hx]
  simp [normalize]

theorem normalize_smul_of_neg {r : ℝ} (hr : r < 0) (x : V) :
    normalize (r • x) = - normalize x := by
  rw [← normalize_neg, ← normalize_smul_of_pos (r := - r) (by linarith) (- x)]
  simp

@[simp]
lemma inner_self_eq_one {x : V} (hx : ‖x‖ = 1) : ⟪x, x⟫ = 1 :=
  (inner_eq_one_iff_of_norm_one hx hx).mpr rfl

lemma neg_one_le_inner {x y : V} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) : -1 ≤ ⟪x, y⟫ := by
  have H := neg_le_of_abs_le (abs_real_inner_le_norm x y)
  rw [hx, hy] at H
  norm_num at H
  exact H
lemma neg_one_le_inner_normalize_normalize (x y : V) :
    (-1 : ℝ) ≤ ⟪normalize x, normalize y⟫ := by
  by_cases hx : x = 0
  · simp [hx]
  by_cases hy : y = 0
  · simp [hy]
  have H: ‖normalize x‖ = 1 := by
    simpa [norm_normalize_eq_one_iff]
  have H0: ‖normalize y‖ = 1 := by
    simpa [norm_normalize_eq_one_iff]
  exact neg_one_le_inner H H0

/-- Gets the orthogonal direction of one vector relative to another. -/
noncomputable def ortho (y x : V) : V := x - ⟪x, y⟫ • y

lemma inner_ortho_nonneg {x y : V} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) : 0 ≤ ⟪x, ortho y x⟫ := by
  rw [ortho, inner_sub_right, real_inner_smul_right, inner_self_eq_one hx]
  simp only [← sq, sub_nonneg, sq_le_one_iff_abs_le_one]
  have H := abs_real_inner_le_norm x y
  rw [hx, hy] at H
  norm_num at H
  exact H

@[simp]
lemma inner_normalize_ortho (x : V) {y : V} (hy : ‖y‖ = 1) :
    ⟪y, normalize (ortho y x)⟫ = 0 := by
  rw [ortho, normalize, real_inner_smul_right,
     inner_sub_right, real_inner_comm x y, real_inner_smul_right]
  simp_all

lemma inner_normalize_ortho_sq_add_inner_sq_eq_one {x y : V} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ⟪x, normalize (ortho y x)⟫ ^ 2 + ⟪x, y⟫ ^ 2 = 1 := by
  rw [ortho, normalize, real_inner_smul_right, inner_sub_right, real_inner_smul_right]
  by_cases h₁ : x = y
  · simp [h₁, hy]
  by_cases h₂ : x = - y
  · simp [h₂, hy]
  rw [real_inner_self_eq_norm_sq, hx]
  have H1 : ‖x - ⟪x, y⟫ • y‖ ≠ 0 := by
    simp only [ne_eq, norm_eq_zero];
    intro H2; rw [sub_eq_zero] at H2
    rw [H2, norm_smul, hy] at hx
    simp only [Real.norm_eq_abs, mul_one] at hx
    apply eq_or_eq_neg_of_abs_eq at hx
    rcases hx with hx | hx
    · simp only [one_smul, hx] at H2; tauto
    · simp only [neg_smul, one_smul, hx] at H2; tauto
  field_simp
  rw [← real_inner_self_eq_norm_sq]
  rw [inner_sub_left, inner_sub_right, inner_sub_right]
  rw [real_inner_smul_right, real_inner_smul_left]
  rw [real_inner_smul_right, real_inner_smul_left]
  rw [real_inner_comm x y]
  rw [real_inner_self_eq_norm_sq, hx, real_inner_self_eq_norm_sq, hy]
  ring


lemma inner_eq_cos_angle {x y : V} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ⟪x, y⟫ = Real.cos (angle x y) := by
  simp [cos_angle, hx, hy]

lemma inner_ortho_right_eq_sin_angle {x y : V} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ⟪x, normalize (ortho y x)⟫ = Real.sin (angle x y) := by
  have H : ⟪x, normalize (ortho y x)⟫ ^ 2 = Real.sin (angle x y) ^ 2 := by
    simp [Real.sin_sq, ← inner_eq_cos_angle hx hy,
      ← inner_normalize_ortho_sq_add_inner_sq_eq_one hx hy]
  rw [sq_eq_sq_iff_abs_eq_abs] at H
  rw [abs_of_nonneg (sin_angle_nonneg x y)] at H
  have H0 : 0 ≤ ⟪x, normalize (ortho y x)⟫ := by
    rw [normalize, real_inner_smul_right]
    have H1 := inner_ortho_nonneg hx hy
    have H2 := norm_nonneg (ortho y x)
    have H3 := inv_nonneg_of_nonneg H2
    exact Left.mul_nonneg H3 H1
  rw [abs_of_nonneg H0] at H
  exact H

/-- If the inner product of two unit vectors is `-1`, then the two vectors are opposite. -/
theorem inner_eq_neg_one_iff_of_norm_one {x y : V} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ⟪x, y⟫ = -1 ↔ x = -y := by
  have H := inner_eq_one_iff_of_norm_one (𝕜 := ℝ) (x := x) (y := -y)
  simp only [norm_neg, inner_neg_right] at H
  rw [← H hx hy, neg_eq_iff_eq_neg]

theorem real_inner_self_eq_norm_sq (x : V) : ⟪x, x⟫ = ‖x‖ ^ 2 := by
  rw [pow_two, real_inner_self_eq_norm_mul_norm]


lemma angle_le_angle_add_angle_aux {x y : V} (Hx : ‖x‖ = 1) (Hy : ‖y‖ = 1) :
    x = Real.cos (angle x y) • y + Real.sin (angle x y) • normalize (ortho y x) := by
  rw [← inner_ortho_right_eq_sin_angle Hx Hy]
  rw [← inner_eq_cos_angle Hx Hy]
  by_cases hxy : x - ⟪x, y⟫ • y = 0
  · simp [ortho, hxy, ← sub_eq_zero]
  simp only [ortho]
  rw [normalize, real_inner_smul_right, inner_sub_right, real_inner_smul_right]
  rw [real_inner_self_eq_norm_sq, Hx, ← sq, mul_smul, ← smul_assoc]
  norm_num
  have H : 1 - ⟪x, y⟫ ^ 2 ≠ 0 := by
    rw [sub_ne_zero, ne_comm, sq_ne_one_iff]
    constructor <;> contrapose! hxy
    · rw [inner_eq_one_iff_of_norm_one Hx Hy] at hxy
      simp [inner_self_eq_one, hxy, Hy]
    · rw [inner_eq_neg_one_iff_of_norm_one Hx Hy] at hxy
      simp [inner_self_eq_one, hxy, Hy]
  rw [← smul_assoc]
  simp; field_simp
  rw [← real_inner_self_eq_norm_sq]
  have H0 : ⟪x - ⟪x, y⟫ • y, x - ⟪x, y⟫ • y⟫ = 1 - ⟪x, y⟫ ^ 2 := by
    rw [inner_sub_left, inner_sub_right, inner_sub_right, inner_self_eq_one Hx]
    rw [real_inner_smul_right, ← sq]
    field_simp
    rw [real_inner_smul_left, real_inner_smul_left, real_inner_smul_right]
    rw [inner_self_eq_one Hy, real_inner_comm y x]
    ring
  rw [H0]
  field_simp; simp

lemma angle_le_angle_add_angle {x y z : V} (Hx : ‖x‖ = 1) (Hy : ‖y‖ = 1) (Hz : ‖z‖ = 1) :
    angle x z ≤ angle x y + angle y z := by
  rcases lt_or_ge Real.pi (angle x y + angle y z) with H | H
  · linarith [angle_le_pi x z]
  have H0 : 0 ≤ angle x y + angle y z :=
    add_nonneg (angle_nonneg x y) (angle_nonneg y z)
  have H1 : ⟪x, z⟫ = ⟪x, z⟫ := rfl
  nth_rw 2 [angle_le_angle_add_angle_aux Hx Hy] at H1
  nth_rw 2 [angle_le_angle_add_angle_aux Hz Hy] at H1
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right] at H1
  simp only [real_inner_comm y (normalize _), real_inner_self_eq_norm_sq, Hy,
    angle_comm z y, inner_normalize_ortho] at H1
  norm_num at H1
  rw [mul_comm (Real.cos (angle y z))] at H1
  have H2 := neg_one_le_inner_normalize_normalize (ortho y x) (ortho y z)
  have H3 : 0 ≤ Real.sin (angle x y) * Real.sin (angle y z) :=
    mul_nonneg (sin_angle_nonneg x y) (sin_angle_nonneg y z)
  have H4 : Real.cos (angle x y + angle y z) ≤ Real.cos (angle x z) := by
    rw [Real.cos_add, ← inner_eq_cos_angle Hx Hz]
    rw [neg_le_iff_add_nonneg] at H2
    rw [H1]
    field_simp
    linarith [mul_nonneg H3 H2]
  rwa [Real.strictAntiOn_cos.le_iff_ge ⟨H0, H⟩ ⟨angle_nonneg x z, angle_le_pi x z⟩] at H4


lemma aux00 {a b : V} (Ha : ‖a‖ = 1) (Hb : ‖b‖ = 1) (k : ℝ) :
    a = k • b → (k = 1 ∨ k = - 1) := by
  intro H
  rw [H, norm_smul] at Ha
  simp at Ha
  rw [Hb] at Ha; simp at Ha
  have H0 := abs_cases k
  grind

lemma aux03 (x y : V) (k : ℝ) (Hk : k ≠ 0) :
    x = y ↔ k • x = k • y := by
  constructor <;> intro H7
  · rw [H7]
  · have H8 : k⁻¹ • (k • x) = k⁻¹ • (k • y) := by
      rw [H7]
    rw [← smul_assoc, ← smul_assoc] at H8
    rw [smul_eq_mul] at H8
    field_simp at H8
    simp at H8
    exact H8

lemma aux01 {a b : V} (Ha : a ≠ 0) (Hb : b ≠ 0) :
    normalize a = - normalize b ↔
    ∃ (k : ℝ), 0 < k ∧ a = - k • b := by
  constructor <;> intro H
  · unfold normalize at H
    have H0 : ‖a‖ ≠ 0 := norm_ne_zero_iff.mpr Ha
    rw [aux03 _ _ _ H0] at H
    rw [← smul_assoc, smul_eq_mul] at H
    field_simp at H; simp at H
    have H1 : ‖b‖ ≠ 0 := norm_ne_zero_iff.mpr Hb
    rw [← smul_assoc, smul_eq_mul] at H
    use (‖a‖ * ‖b‖⁻¹)
    constructor
    · have H2 : 0 < ‖a‖ := norm_pos_iff.mpr Ha
      have H3 : 0 < ‖b‖ := norm_pos_iff.mpr Hb
      have H4 : 0 < ‖b‖⁻¹ := inv_pos.mpr H3
      exact mul_pos H2 H4
    · nth_rw 1 [H]
      module
  · obtain ⟨k, ⟨Hk1, Hk2⟩⟩ := H
    rw [Hk2]
    simp
    rw [normalize_neg]; congr 1
    exact normalize_smul_of_pos Hk1 b


lemma aux04 (x z : V) (kx kz : ℝ) (H : kx • x + kz • z ≠ 0) (H0 : kx ≠ 0) :
    x - (‖kx • x + kz • z‖⁻¹ * ⟪x, kx • x + kz • z⟫) • ‖kx • x + kz • z‖⁻¹ • (kx • x + kz • z) =
    -(kz / kx) • (z - (‖kx • x + kz • z‖⁻¹ * ⟪z, kx • x + kz • z⟫) •
    ‖kx • x + kz • z‖⁻¹ • (kx • x + kz • z)) := by
  match_scalars <;>
  · field_simp
    rw [← real_inner_self_eq_norm_sq]
    simp [inner_add_left, inner_smul_left]
    ring

lemma aux05 {x y : V} (Hx : ‖x‖ = 1) (Hy : ‖y‖ = 1) (H : angle x y ≠ 0) (H0 : angle x y ≠ Real.pi) :
    ortho x y ≠ 0 := by
  intro H1
  unfold ortho at H1
  rw [sub_eq_zero] at H1
  have Hy' := Hy
  rw [H1, norm_smul, Hx] at Hy
  simp at Hy
  obtain ⟨H2, H3⟩ | ⟨H2, H3⟩ := abs_cases ⟪y, x⟫
  · rw [Hy, inner_eq_cos_angle Hy' Hx, angle_comm] at H2
    symm at H2
    rw [cos_eq_one_iff_angle_eq_zero] at H2
    tauto
  · rw [Hy, inner_eq_cos_angle Hy' Hx, angle_comm] at H2
    have H4 : Real.cos (angle x y) = -1 := by rw [H2]; simp
    rw [cos_eq_neg_one_iff_angle_eq_pi] at H4
    tauto



set_option maxHeartbeats 1000000 in
-- asdf qwerty
lemma aux06 {x y z : V} (Hx : ‖x‖ = 1) (Hy : ‖y‖ = 1) (Hz : ‖z‖ = 1)
    (kx kz : ℝ) (Hkx : 0 < kx) (Hkz : 0 < kz) :
    angle x y ≠ 0 → angle x y ≠ Real.pi →
    angle y z ≠ 0 → angle y z ≠ Real.pi →
    y = normalize (kx • x + kz • z) →
    angle x y + angle y z ≤ Real.pi →
    angle x z = angle x y + angle y z := by
  intros h1 h2 h3 h4 H H'
  have H0 : 0 ≤ angle x y + angle y z :=
    add_nonneg (angle_nonneg x y) (angle_nonneg y z)
  have H1 : ⟪x, z⟫ = ⟪x, z⟫ := rfl
  nth_rw 2 [angle_le_angle_add_angle_aux Hx Hy] at H1
  nth_rw 2 [angle_le_angle_add_angle_aux Hz Hy] at H1
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right] at H1
  simp only [real_inner_comm y (normalize _), real_inner_self_eq_norm_sq, Hy,
    angle_comm z y, inner_normalize_ortho] at H1
  norm_num at H1
  rw [mul_comm (Real.cos (angle y z))] at H1
  have H2 : ortho y x ≠ 0 := by
    apply aux05 Hy Hx
    · rwa [angle_comm]
    · rwa [angle_comm]
  have H3 : ortho y z ≠ 0 := by
    apply aux05 Hy Hz <;> assumption
  have H4 : ‖normalize (ortho y x)‖ = 1 := by
    exact norm_normalize_eq_one_iff.mpr H2
  have H5 : ‖normalize (ortho y z)‖ = 1 := by
    exact norm_normalize_eq_one_iff.mpr H3
  have H6 : ⟪normalize (ortho y x), normalize (ortho y z)⟫ = - 1 := by
    rw [inner_eq_neg_one_iff_of_norm_one H4 H5]
    rw [aux01] <;> try assumption
    unfold ortho
    rw [H]
    unfold normalize
    rw [real_inner_smul_right, real_inner_smul_right]
    use (kz / kx)
    constructor
    · exact div_pos Hkz Hkx
    · apply aux04
      · intro H6
        rw [H6] at H; simp at H
        rw [H] at Hy; simp at Hy
      · exact Ne.symm (ne_of_lt Hkx)
  rw [H6] at H1; ring_nf at H1
  rw [mul_comm, ← Real.cos_add, inner_eq_cos_angle Hx Hz, add_comm] at H1
  apply Real.injOn_cos ⟨angle_nonneg x z, angle_le_pi x z⟩ ⟨H0, H'⟩ at H1
  exact H1

set_option maxHeartbeats 1000000 in
-- asdf qwerty
lemma aux07 {x y : V} (Hx : x ≠ 0) :
    angle (normalize x) y = angle x y := by
  unfold normalize
  rw [angle_smul_left_of_pos]
  simpa

lemma aux08 {x y : V} (Hx : x ≠ 0) (Hy : y ≠ 0) :
    angle (normalize x) (normalize y) = angle x y := by
  rw [aux07 Hx, angle_comm, aux07 Hy, angle_comm]

lemma aux08_1 {x y : V} (Hx : ‖x‖ = 1) (Hy : ‖y‖ = 1) (H : angle x y = Real.pi) :
    x = -y := by
  rw [angle_eq_pi_iff] at H
  obtain ⟨_, ⟨r, ⟨H, H0⟩⟩⟩ := H
  have H1 := H0
  apply aux00 Hy Hx at H0
  have H2 : r = -1 := by grind
  rw [H2] at H1
  rw [H1]; simp

lemma aux09 {x y z : V} (Hx : ‖x‖ = 1) (Hy : ‖y‖ = 1) (Hz : ‖z‖ = 1)
    {k : ℝ} (Hk : 0 < k) :
    angle x z ≠ 0 →
    angle x z ≠ Real.pi → y = normalize (x + k • z) → angle x y + angle y z ≤ Real.pi := by
  intros H'' H' H
  unfold angle; rw [Hx, Hy, Hz]; simp
  have H0 : 0 ≤ Real.sin (Real.arccos ⟪x, y⟫ + Real.arccos ⟪y, z⟫) := by
    rw [Real.sin_add, Real.sin_arccos, Real.sin_arccos, Real.cos_arccos, Real.cos_arccos]
    · rw [H]
      unfold normalize
      have H0 : ‖x + k • z‖ ≠ 0 := by
        intros H0
        simp at H0
        have H1 : x = (-k) • z := by
          rw [← sub_eq_zero]; simp; exact H0
        apply aux00 Hx Hz at H1
        have H2 : k = 1 := by grind
        rw [H2] at H0
        simp at H0
        rw [add_eq_zero_iff_eq_neg] at H0
        apply H'
        rw [angle_eq_pi_iff]
        constructor
        · intro H3; rw [H3] at Hx; simp at Hx
        · use (-1); simp; rw [H0]; simp
      have H1 : 1 - ⟪x, ‖x + k • z‖⁻¹ • (x + k • z)⟫ ^ 2 =
                (‖x + k • z‖ ^ 2 - ⟪x, x + k • z⟫ ^ 2) / (‖x + k • z‖ ^ 2) := by
        field_simp
        rw [mul_sub, real_inner_smul_right]
        field_simp
      rw [H1, Real.sqrt_div' _ (sq_nonneg ‖x + k • z‖)]; clear H1
      simp only [norm_nonneg, Real.sqrt_sq]
      rw [real_inner_smul_left]
      field_simp
      rw [real_inner_smul_right]
      field_simp
      rw [Real.sqrt_div' _ (sq_nonneg ‖x + k • z‖)]
      simp only [norm_nonneg, Real.sqrt_sq]
      field_simp
      rw [div_nonneg_iff]; left
      constructor
      · ring_nf
        rw [← real_inner_self_eq_norm_sq]
        have H1 : ⟪x + k • z, x + k • z⟫ = 1 + k ^ 2 + 2 * k * ⟪x, z⟫ := by
          rw [inner_add_right, inner_add_left, real_inner_smul_left, real_inner_smul_right,
              inner_add_left,
              real_inner_smul_left,
              real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
              Hx, Hz]
          simp; rw [real_inner_comm]; ring
        rw [H1]
        have H2 : ⟪x, x + k • z⟫ = 1 + k * ⟪x, z⟫ := by
          rw [inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq, Hx]; simp
        have H3 : ⟪x + k • z, z⟫ = ⟪x, z⟫ + k := by
          rw [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq, Hz]; simp
        rw [H2, H3]; clear H1 H2 H3
        ring_nf
        rw [inner_eq_cos_angle Hx Hz]
        rw [← Real.sin_sq, Real.sqrt_sq (sin_angle_nonneg x z)]
        rw [show k ^ 2 - k ^ 2 * Real.cos (angle x z) ^ 2 =
                (1 - Real.cos (angle x z) ^ 2) * k ^ 2 by ring]
        rw [← Real.sin_sq, Real.sqrt_mul (sq_nonneg (Real.sin (angle x z)))]
        rw [Real.sqrt_sq (sin_angle_nonneg x z)]
        rw [Real.sqrt_sq (by linarith)]
        have H1 : k * Real.cos (angle x z) * Real.sin (angle x z) + k * (Real.sin (angle x z) * k) +
                  Real.cos (angle x z) * (Real.sin (angle x z) * k) + Real.sin (angle x z) =
                  Real.sin (angle x z) * (1 + k ^ 2 + 2 * k * Real.cos (angle x z)) := by
          ring
        rw [H1]; clear H1
        rw [mul_nonneg_iff]; left
        constructor
        · exact sin_angle_nonneg x z
        · have H1 : 1 + k ^ 2 + 2 * k * Real.cos (angle x z) =
                    (1 - k) ^ 2 + 2 * k * (1 + Real.cos (angle x z)) := by ring
          have H2 : 0 ≤ (1 - k) ^ 2 := sq_nonneg (1 - k)
          have H3 : 0 ≤ 2 * k * (1 + Real.cos (angle x z)) := by
            rw [mul_nonneg_iff]; left; constructor
            · simp; linarith
            · have H3 : -1 ≤ Real.cos (angle x z) := Real.neg_one_le_cos (angle x z)
              linarith
          linarith
      · exact sq_nonneg ‖x + k • z‖
    · exact neg_one_le_inner Hx Hy
    · rw [inner_eq_cos_angle Hx Hy]
      exact Real.cos_le_one (angle x y)
    · exact neg_one_le_inner Hy Hz
    · rw [inner_eq_cos_angle Hy Hz]
      exact Real.cos_le_one (angle y z)
  · have H1 : Real.arccos ⟪x, y⟫ = angle x y := by
      unfold angle; rw [Hx, Hy]; simp
    have H2 : Real.arccos ⟪y, z⟫ = angle y z := by
      unfold angle; rw [Hy, Hz]; simp
    rw [H1, H2] at H0 ⊢
    have H3 : angle x y ≤ Real.pi := angle_le_pi x y
    have H4 : angle y z ≤ Real.pi := angle_le_pi y z
    obtain H5 | H5 := eq_or_ne (angle x y + angle y z) (2 * Real.pi)
    · have H6 : angle x y = Real.pi := by linarith
      have H7 : angle y z = Real.pi := by linarith
      apply aux08_1 Hx Hy at H6
      apply aux08_1 Hy Hz at H7
      have H8 : x = z := by
        rw [H6, H7]; simp
      rw [H8] at H''
      unfold angle at H''
      rw [real_inner_self_eq_norm_sq, Hz] at H''
      simp at H''
    · contrapose! H0
      have H3 := @Real.sin_neg_of_neg_of_neg_pi_lt (angle x y + angle y z - 2 * Real.pi)
                (by grind) (by linarith)
      simp at H3; exact H3

lemma aux09_1 {x y z : V} (Hx : x ≠ 0) (Hy : y ≠ 0) (Hz : z ≠ 0)
    {kx kz : ℝ} (Hkx : 0 < kx) (Hkz : 0 < kz) :
    angle x z ≠ 0 →
    angle x z ≠ Real.pi → y = kx • x + kz • z → angle x y + angle y z ≤ Real.pi := by
  intros H H0 H1
  have H2 := @aux09 V _ _ (normalize x) (normalize ((‖x‖⁻¹ * kx⁻¹) • y)) (normalize z)
    (norm_normalize_eq_one_iff.mpr Hx)
  have H3 : ‖normalize ((‖x‖⁻¹ * kx⁻¹) • y)‖ = 1 := by
    refine norm_normalize_eq_one_iff.mpr ?_
    simp
    refine ⟨⟨Hx, by grind⟩, Hy⟩
  have Hx1 : 0 < ‖x‖ := norm_pos_iff.mpr Hx
  have Hz1 : 0 < ‖z‖ := norm_pos_iff.mpr Hz
  have H4 : 0 < kz / ‖x‖ / kx * ‖z‖ := by
    rw [mul_pos_iff]; left
    simp [Hz1]
    rw [div_pos_iff]; left
    simp [Hkx]
    rw [div_pos_iff]; left
    simp_all
  have H5 : ‖normalize z‖ = 1 := norm_normalize_eq_one_iff.mpr Hz
  rw [aux08 Hx Hz] at H2
  have H6 : normalize ((‖x‖⁻¹ * kx⁻¹) • y) =
            normalize (normalize x + (kz / ‖x‖ / kx * ‖z‖) • normalize z) := by
    congr 1
    rw [H1]
    unfold normalize
    match_scalars
    · field_simp
    · field_simp
  have H7 : (‖x‖⁻¹ * kx⁻¹) • y ≠ 0 := by
    simp
    refine ⟨⟨Hx, by grind⟩, Hy⟩
  rw [aux08 Hx H7] at H2
  rw [aux08 H7 Hz] at H2
  have H8 : 0 < ‖x‖⁻¹ * kx⁻¹ := by
    rw [mul_pos_iff]; left
    constructor
    · exact inv_pos.mpr Hx1
    · exact inv_pos.mpr Hkx
  rw [angle_smul_right_of_pos x y H8] at H2
  rw [angle_smul_left_of_pos y z H8] at H2
  apply H2 H3 H5 H4 H H0 H6


set_option maxHeartbeats 1000000 in
-- asdf qwerty
lemma aux10 {x y z : V} (Hx : x ≠ 0) (Hy : y ≠ 0) (Hz : z ≠ 0)
    (kx kz : ℝ) (Hkx : 0 < kx) (Hkz : 0 < kz) :
    angle x y ≠ 0 → angle x y ≠ Real.pi →
    angle y z ≠ 0 → angle y z ≠ Real.pi →
    angle x z ≠ 0 → angle x z ≠ Real.pi →
    y = kx • x + kz • z →
    angle x z = angle x y + angle y z := by
  intros H1 H2 H3 H4' H4 H5 H6
  rw [← aux08 Hx Hz, ← aux08 Hx Hy, ← aux08 Hy Hz]
  apply aux06
  · exact norm_normalize_eq_one_iff.mpr Hx
  · exact norm_normalize_eq_one_iff.mpr Hy
  · exact norm_normalize_eq_one_iff.mpr Hz
  · have temp : 0 < kx * ‖x‖ := by
      rw [mul_pos_iff]
      left; simp; tauto
    exact temp
  · have temp : 0 < kz * ‖z‖ := by
      rw [mul_pos_iff]
      left; simp; tauto
    exact temp
  · rw [aux08] <;> assumption
  · rw [aux08] <;> assumption
  · rw [aux08] <;> assumption
  · rw [aux08] <;> assumption
  · rw [H6]
    congr 1
    unfold normalize
    match_scalars <;> field_simp
  · rw [aux08 Hy Hz, aux08 Hx Hy]
    apply aux09_1 Hx Hy Hz Hkx Hkz H4 H5 H6

lemma aux11 {x y z : V} (Hx : x ≠ 0) (Hy : y ≠ 0) (Hz : z ≠ 0)
    (kx kz : ℝ) (Hkx : 0 < kx) (Hkz : 0 < kz) :
    angle x z ≠ Real.pi → y = kx • x + kz • z →
    angle x z = angle x y + angle y z := by
  intros H H0
  obtain H1 | H1 := eq_or_ne (angle x z) 0
  · rw [H1]
    rw [angle_eq_zero_iff] at H1
    obtain ⟨_, ⟨r, ⟨H1, H2⟩⟩⟩ := H1
    rw [H2] at H0
    have H3 : y = (kx + kz * r) • x := by
      rw [H0]; module
    have H4 : 0 < kx + kz * r := by nlinarith
    rw [H3]
    rw [angle_smul_right_of_pos x x H4]
    rw [H2, angle_smul_left_of_pos _ _ H4, angle_smul_right_of_pos _ _ H1]
    rw [angle_self Hx]
    simp
  obtain H2 | H2 := eq_or_ne (angle x y) 0
  · rw [H2]; simp
    rw [angle_eq_zero_iff] at H2
    obtain ⟨_, ⟨r, ⟨H2, H3⟩⟩⟩ := H2
    rw [H3, angle_smul_left_of_pos _ _ H2]
  obtain H3 | H3 := eq_or_ne (angle x y) Real.pi
  · rw [angle_eq_pi_iff] at H3
    obtain ⟨_, ⟨r, ⟨H3, H4⟩⟩⟩ := H3
    exfalso
    apply H
    rw [H0] at H4
    have H5 : (kx - r) • x = (-kz) • z := by
      rw [sub_smul]
      rw [← H4]
      module
    have H6 : angle ((kx - r) • x) ((-kz) • z) = 0 := by
      rw [H5, angle_self]
      simp_all
      linarith
    rw [angle_smul_left_of_pos _ _ (by linarith)] at H6
    rw [angle_smul_right_of_neg _ _ (by linarith)] at H6
    rw [angle_neg_right] at H6
    linarith
  obtain H4 | H4 := eq_or_ne (angle y z) 0
  · rw [H4]; simp
    rw [angle_eq_zero_iff] at H4
    obtain ⟨_, ⟨r, ⟨H4, H5⟩⟩⟩ := H4
    rw [H5, angle_smul_right_of_pos _ _ H4]
  obtain H5 | H5 := eq_or_ne (angle y z) Real.pi
  · rw [angle_comm, angle_eq_pi_iff] at H5
    obtain ⟨_, ⟨r, ⟨H5, H6⟩⟩⟩ := H5
    exfalso
    apply H
    rw [H0] at H6
    have H7 : kx • x = (r - kz) • z := by
      rw [sub_smul, ← H6]
      module
    have H8 : angle (kx • x) ((r - kz) • z) = 0 := by
      rw [H7, angle_self]
      simp_all
      linarith
    rw [angle_smul_left_of_pos _ _ Hkx] at H8
    rw [angle_smul_right_of_neg _ _ (by linarith)] at H8
    rw [angle_neg_right] at H8
    linarith
  apply aux10 (kx := kx) (kz := kz) <;> try assumption

lemma aux12 {x y z : V} (Hx : ‖x‖ = 1) (Hy : ‖y‖ = 1) (Hz : ‖z‖ = 1) :
    angle x z ≠ 0 → angle x z ≠ Real.pi →
    angle x y ≠ 0 → angle x y ≠ Real.pi →
    angle y z ≠ 0 → angle y z ≠ Real.pi →
    angle x z = angle x y + angle y z →
    Real.sin (angle x z) • y = Real.sin (angle y z) • x + Real.sin (angle x y) • z := by
  intros H H0 H1 H2 H3 H4 H5
  have H6 : ⟪x, z⟫ = ⟪x, z⟫ := rfl
  nth_rw 2 [angle_le_angle_add_angle_aux Hx Hy] at H6
  nth_rw 2 [angle_le_angle_add_angle_aux Hz Hy] at H6
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right] at H6
  simp only [real_inner_comm y (normalize _),
              real_inner_self_eq_norm_sq, Hy, angle_comm z y, inner_normalize_ortho] at H6
  norm_num at H6
  have H7 : ⟪x, z⟫ = Real.cos (angle x y + angle y z) := by
    rw [← H5]
    exact inner_eq_cos_angle Hx Hz
  rw [H7] at H6
  rw [Real.cos_add] at H6
  ring_nf at H6
  have T (a b : ℝ) : a - b = a + b * (-1) := by simp; rfl
  rw [T] at H6
  simp only [add_right_inj] at H6
  have Hw : Real.sin (angle x y) * Real.sin (angle y z) ≠ 0 := by
    intros Hw; simp at Hw
    obtain Hw | Hw := Hw
    · rw [sin_eq_zero_iff_angle_eq_zero_or_angle_eq_pi] at Hw
      tauto
    · rw [sin_eq_zero_iff_angle_eq_zero_or_angle_eq_pi] at Hw
      tauto
  have H8 : ⟪normalize (ortho y x), normalize (ortho y z)⟫ = - 1 := by
    grind
  have H9 : ortho y x ≠ 0 := by
    apply aux05 Hy Hx
    · rw [angle_comm]; assumption
    · rw [angle_comm]; assumption
  have H10 : ortho y z ≠ 0 := by
    apply aux05 Hy Hz <;> assumption
  have H11 : ‖normalize (ortho y x)‖ = 1 := by
    exact norm_normalize_eq_one_iff.mpr H9
  have H12 : ‖normalize (ortho y z)‖ = 1 := by
    exact norm_normalize_eq_one_iff.mpr H10
  rw [inner_eq_neg_one_iff_of_norm_one H11 H12] at H8
  nth_rw 2 [angle_le_angle_add_angle_aux Hx Hy]
  nth_rw 3 [angle_le_angle_add_angle_aux Hz Hy]
  rw [H8]
  rw [smul_add, smul_add]
  simp
  match_scalars
  · norm_num
    rw [H5, Real.sin_add]
    rw [angle_comm z y]
    ring
  · rw [angle_comm z y]
    ring

lemma aux13 {x y z : V} (Hx : ‖x‖ = 1) (Hy : ‖y‖ = 1) (Hz : ‖z‖ = 1) :
    angle x z ≠ Real.pi → angle x z = angle x y + angle y z →
    Real.sin (angle x z) • y = Real.sin (angle y z) • x + Real.sin (angle x y) • z := by
  intros H H0
  obtain H1 | H1 := eq_or_ne (angle x z) 0
  · rw [H1]; simp
    rw [H1] at H
    have H2 : angle x y = 0 := by linarith [angle_nonneg x y, angle_nonneg y z]
    have H3 : angle y z = 0 := by linarith [angle_nonneg y z]
    rw [H2, H3]; simp
  obtain H2 | H2 := eq_or_ne (angle x y) Real.pi
  · rw [H2] at H0 ⊢
    have H3 : angle x z = Real.pi := by
      linarith [angle_nonneg y z, angle_le_pi x z]
    tauto
  obtain H3 | H3 := eq_or_ne (angle y z) Real.pi
  · rw [H3] at H0 ⊢
    have H4 : angle x z = Real.pi := by
      linarith [angle_nonneg x y, angle_le_pi x z]
    tauto
  obtain H4 | H4 := eq_or_ne (angle x y) 0
  · rw [H4] at H0 ⊢
    simp at H0 ⊢
    rw [H0]
    rw [angle_eq_zero_iff] at H4
    obtain ⟨H4, ⟨r, ⟨H5, H6⟩⟩⟩ := H4
    rw [H6] at Hy
    rw [norm_smul] at Hy
    simp at Hy; rw [Hx] at Hy
    simp at Hy
    have H7 : r = 1 := by
      have H7 := abs_cases r; grind
    rw [H7] at H6; simp at H6
    rw [H6]
  obtain H5 | H5 := eq_or_ne (angle y z) 0
  · rw [H5] at H0 ⊢
    simp at H0 ⊢
    rw [H0]
    rw [angle_eq_zero_iff] at H5
    obtain ⟨H5, ⟨r, ⟨H6, H7⟩⟩⟩ := H5
    rw [H7] at Hz
    rw [norm_smul] at Hz
    simp at Hz
    rw [Hy] at Hz
    simp at Hz
    have H8 : r = 1 := by
      have H7 := abs_cases r; grind
    rw [H8] at H7; simp at H7
    rw [H7]
  apply aux12 <;> assumption

theorem thm {x y z : V} (Hx : x ≠ 0) (Hy : y ≠ 0) (Hz : z ≠ 0) (Hxz : angle x z ≠ Real.pi) :
    (∃ (kx kz : ℝ), 0 ≤ kx ∧ 0 ≤ kz ∧ y = kx • x + kz • z) ↔
    angle x z = angle x y + angle y z := by
  constructor <;> intro H
  · obtain ⟨kx, ⟨kz, ⟨Hkx, ⟨Hkz, H⟩⟩⟩⟩ := H
    have H0 : kx = 0 ∨ 0 < kx := by exact Or.symm (LE.le.lt_or_eq' Hkx)
    have H1 : kz = 0 ∨ 0 < kz := by exact Or.symm (LE.le.lt_or_eq' Hkz)
    obtain H0 | H0 := H0 <;> obtain H1 | H1 := H1
    · subst kx kz; simp at H; tauto
    · subst kx; simp at H
      rw [H, angle_smul_right_of_pos x z H1, angle_smul_left_of_pos z z H1]
      simp
      exact angle_self Hz
    · subst kz; simp at H
      rw [H, angle_smul_right_of_pos x x H0, angle_smul_left_of_pos x z H0]
      simp
      exact angle_self Hx
    · exact aux11 Hx Hy Hz kx kz H0 H1 Hxz H
  · obtain H0 | H0 := eq_or_ne (angle x z) 0
    · have H1 : angle x y = 0 := by linarith [angle_nonneg x y, angle_nonneg y z]
      rw [angle_eq_zero_iff] at H1
      obtain ⟨_, ⟨r1, ⟨H3, H4⟩⟩⟩ := H1
      use r1, 0; simp
      constructor
      · linarith
      · exact H4
    · have H1 : Real.sin (angle x z) ≠ 0 := by
        intros H1
        rw [sin_eq_zero_iff_angle_eq_zero_or_angle_eq_pi] at H1
        tauto
      have Hx' : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr Hx
      have Hy' : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr Hy
      have Hz' : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr Hz
      have H3 : Real.sin (angle x z) / ‖y‖ ≠ 0 := div_ne_zero H1 Hy'
      use (Real.sin (angle y z)) / Real.sin (angle x z) / ‖x‖ * ‖y‖,
          (Real.sin (angle x y)) / Real.sin (angle x z) / ‖z‖ * ‖y‖
      refine ⟨?_, ?_, ?_⟩
      · field_simp
        rw [div_nonneg_iff]; left
        constructor
        · rw [mul_nonneg_iff]; left
          constructor
          · exact sin_angle_nonneg y z
          · exact norm_nonneg y
        · rw [mul_nonneg_iff]; left
          constructor
          · exact sin_angle_nonneg x z
          · exact norm_nonneg x
      · rw [mul_nonneg_iff]; left
        constructor
        · rw [div_nonneg_iff]; left
          constructor
          · rw [div_nonneg_iff]; left
            constructor
            · exact sin_angle_nonneg x y
            · exact sin_angle_nonneg x z
          · exact norm_nonneg z
        · exact norm_nonneg y
      · rw [aux03 _ _ (Real.sin (angle x z) / ‖y‖) H3]
        rw [smul_add, ← smul_assoc, ← smul_assoc, smul_eq_mul, smul_eq_mul]
        field_simp
        have H4 : ‖normalize y‖ = 1 := norm_normalize_eq_one_iff.mpr Hy
        have H5 : ‖normalize x‖ = 1 := norm_normalize_eq_one_iff.mpr Hx
        have H6 : ‖normalize z‖ = 1 := norm_normalize_eq_one_iff.mpr Hz
        have H7 := aux13 H5 H4 H6
        rw [aux08 Hy Hz, aux08 Hx Hz, aux08 Hx Hy] at H7
        have H8 := H7 Hxz H
        unfold normalize at H8
        rw [← smul_assoc, smul_eq_mul] at H8
        have H9 : Real.sin (angle x z) * ‖y‖⁻¹ = Real.sin (angle x z) / ‖y‖ := by
          field_simp
        rw [H9] at H8
        rw [H8]
        match_scalars <;> field_simp


end tinkering
