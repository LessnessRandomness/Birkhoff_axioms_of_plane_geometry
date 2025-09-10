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

lemma angle_normalize_left {x y : V} (Hx : x ≠ 0) :
    angle (normalize x) y = angle x y := by
  unfold normalize
  rw [angle_smul_left_of_pos]
  simpa

lemma angle_normalize_right {x y : V} (Hy : y ≠ 0) :
    angle x (normalize y) = angle x y := by
  rw [angle_comm, angle_normalize_left Hy, angle_comm]


theorem inner_le_one_of_norm_one {x y : V} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) : ⟪x, y⟫ ≤ 1 := by
  have H := real_inner_le_norm x y
  simp_all

theorem neg_one_le_inner_of_norm_one {x y : V} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) : -1 ≤ ⟪x, y⟫ := by
  have H := neg_le_of_abs_le (abs_real_inner_le_norm x y)
  simp_all


---- this is where https://github.com/leanprover-community/mathlib4/pull/26129 ends


lemma aux00 {a b : V} (Ha : ‖a‖ = 1) (Hb : ‖b‖ = 1) (k : ℝ) :
    a = k • b → (k = 1 ∨ k = - 1) := by
  intro H
  rw [H, norm_smul] at Ha
  simp at Ha
  rw [Hb] at Ha; simp at Ha
  have H0 := abs_cases k
  grind

lemma aux01 {a b : V} (Ha : a ≠ 0) (Hb : b ≠ 0) :
    normalize a = normalize b ↔
    ∃ (k : ℝ), 0 < k ∧ a = k • b := by
  constructor <;> intro H
  · unfold normalize at H
    have H0 : ‖a‖ ≠ 0 := norm_ne_zero_iff.mpr Ha
    have H1 : ‖b‖ ≠ 0 := norm_ne_zero_iff.mpr Hb
    rw [← smul_right_inj H0, ← smul_assoc, smul_eq_mul] at H
    field_simp at H; simp [← smul_assoc, smul_eq_mul] at H
    use (‖a‖ * ‖b‖⁻¹)
    refine ⟨?_, H⟩
    have H2 : 0 < ‖a‖ := norm_pos_iff.mpr Ha
    have H3 : 0 < ‖b‖ := norm_pos_iff.mpr Hb
    have H4 : 0 < ‖b‖⁻¹ := inv_pos.mpr H3
    exact mul_pos H2 H4
  · obtain ⟨k, ⟨Hk1, Hk2⟩⟩ := H
    rw [Hk2, normalize_smul_of_pos Hk1]

lemma aux01_neg {a b : V} (Ha : a ≠ 0) (Hb : b ≠ 0) :
    normalize a = - normalize b ↔
    ∃ (k : ℝ), k < 0 ∧ a = k • b := by
  rw [← normalize_neg, aux01 Ha (neg_ne_zero.mpr Hb)]
  constructor <;> intro H
  · obtain ⟨k, ⟨Hk1, Hk2⟩⟩ := H
    use (-k); subst Hk2; simp [Hk1]
  · obtain ⟨k, ⟨Hk1, Hk2⟩⟩ := H
    use (-k); subst Hk2; simp [Hk1]

lemma aux05 {x y : V} (Hx : ‖x‖ = 1) (Hy : ‖y‖ = 1) (H : angle x y ≠ 0) (H0 : angle x y ≠ Real.pi) :
    ortho x y ≠ 0 := by
  intro H1; unfold ortho at H1
  rw [sub_eq_zero] at H1
  apply (aux00 Hy Hx) at H1
  obtain H1 | H1 := H1
  · rw [inner_eq_one_iff_of_norm_one Hy Hx] at H1
    rw [H1] at H
    apply H; rw [angle_self]
    intros H2; rw [H2] at Hx; simp at Hx
  · rw [inner_eq_neg_one_iff_of_norm_one Hy Hx] at H1
    rw [H1] at H0
    apply H0; rw [angle_neg_right, angle_self] <;> simp
    intros H2; rw [H2] at Hx; simp at Hx

lemma aux08_1 {x y : V} (Hx : ‖x‖ = 1) (Hy : ‖y‖ = 1) (H : angle x y = 0) : x = y := by
  rw [angle_eq_zero_iff, ← aux01] at H
  · simp_all [normalize_eq_self_of_norm_one]
  · intro H0; simp [H0] at Hy
  · tauto

lemma aux08_2 {x y : V} (Hx : ‖x‖ = 1) (Hy : ‖y‖ = 1) (H : angle x y = Real.pi) : x = -y := by
  rw [show -y = - 1 • y by module]
  rw [angle_eq_pi_iff, ← aux01_neg] at H
  · simp_all [normalize_eq_self_of_norm_one]
  · intro H0; simp [H0] at Hy
  · tauto

lemma aux09 {x z : V} (Hx : ‖x‖ = 1) (Hz : ‖z‖ = 1) {k : ℝ} (Hk : 0 ≤ k) :
    let y := normalize (x + k • z)
    angle x y + angle y z ≤ Real.pi := by
  intros y
  obtain H | H := eq_or_ne (angle x z) Real.pi
  · have H0 : x = -z := aux08_2 Hx Hz H
    subst H0; clear Hx H
    have Hz' : z ≠ 0 := by
      intro H; rw [H] at Hz; simp at Hz
    have H1 : -z + k • z = (k - 1) • z := by module
    obtain H2 | H2 | H2 := lt_trichotomy k 1
    · have H3 : y = -z := by
        unfold y
        rw [H1, normalize_smul_of_neg (by linarith), normalize_eq_self_of_norm_one Hz]
      rw [H3, angle_neg_left, angle_comm]; ring_nf; apply le_refl
    · have H3 : y = 0 := by
        unfold y
        rw [H1, H2]; simp
      rw [H3]; simp
    · have H3 : y = z := by
        unfold y
        rw [H1, normalize_smul_of_pos (by linarith), normalize_eq_self_of_norm_one Hz]
      rw [H3, angle_neg_left]; ring_nf; apply le_refl
  have Hz' : z ≠ 0 := by
    intro H1; rw [H1] at Hz; simp at Hz
  obtain H0 | H0 := eq_or_ne (angle x z) 0
  · apply aux08_1 Hx Hz at H0
    have H1 : y = z := by
      unfold y
      rw [H0, show z + k • z = (1 + k) • z by module, normalize_smul_of_pos (by linarith)]
      rw [normalize_eq_self_of_norm_one Hz]
    rw [H0, H1, angle_self Hz']; simp [Real.pi_nonneg]
  have Hy' : x + k • z ≠ 0 := by
    intros H2; have H3 := H2; unfold y at *
    rw [add_eq_zero_iff_eq_neg, ← neg_smul] at H2
    apply aux00 Hx Hz at H2
    obtain H2 | H2 := H2
    · linarith
    · simp at H2
      rw [H2, add_eq_zero_iff_eq_neg] at H3; simp at H3
      rw [H3, angle_neg_left, angle_self Hz'] at H; simp at H
  have Hy : ‖y‖ = 1 := norm_normalize_eq_one_iff.mpr Hy'
  obtain H1 | H1 := eq_or_ne (angle x y + angle y z) (2 * Real.pi)
  · have H2 : angle x y = Real.pi := by linarith [angle_le_pi x y, angle_le_pi y z]
    have H3 : angle y z = Real.pi := by linarith [angle_le_pi y z]
    apply aux08_2 Hx Hy at H2
    apply aux08_2 Hy Hz at H3
    rw [H2, H3] at H0
    simp [angle_self Hz'] at H0
  have H2 : 0 ≤ Real.sin (angle x y + angle y z) := by
    unfold angle; rw [Hx, Hy, Hz]; simp
    rw [Real.sin_add, Real.sin_arccos, Real.sin_arccos,
        Real.cos_arccos (neg_one_le_inner Hy Hz) (inner_le_one_of_norm_one Hy Hz),
        Real.cos_arccos (neg_one_le_inner Hx Hy) (inner_le_one_of_norm_one Hx Hy)]
    unfold y normalize
    set w := x + k • z
    have H1 : 1 - ⟪x, ‖w‖⁻¹ • w⟫ ^ 2 = (‖w‖ ^ 2 - ⟪x, w⟫ ^ 2) / (‖w‖ ^ 2) := by
      rw [real_inner_smul_right]; field_simp
    have H2 : 1 - ⟪‖w‖⁻¹ • w, z⟫ ^ 2 = (‖w‖ ^ 2 - ⟪w, z⟫ ^ 2) / (‖w‖ ^ 2) := by
      rw [real_inner_smul_left]; field_simp
    rw [H1, H2, Real.sqrt_div' _ (sq_nonneg ‖w‖), Real.sqrt_div' _ (sq_nonneg ‖w‖),
        Real.sqrt_sq (norm_nonneg w)]
    rw [real_inner_smul_left, real_inner_smul_right]
    field_simp
    rw [div_nonneg_iff]; left; refine ⟨?_, sq_nonneg ‖w‖⟩
    set p := ⟪x, z⟫
    have H3: ‖w‖ ^ 2 = 1 + k ^ 2 + 2 * k * p := by
      unfold w; rw [← real_inner_self_eq_norm_sq]
      rw [inner_add_right, inner_add_left, inner_add_left]
      rw [real_inner_smul_left, real_inner_smul_right, real_inner_smul_left,
          real_inner_smul_right]
      rw [inner_self_eq_one Hx, inner_self_eq_one Hz, real_inner_comm x z]
      ring
    have H4 : ⟪x, w⟫ = 1 + k * p := by
      unfold w
      rw [inner_add_right, real_inner_smul_right, inner_self_eq_one Hx]
    have H5 : ⟪w, z⟫ = k + p := by
      unfold w p
      rw [inner_add_left, real_inner_smul_left, inner_self_eq_one Hz]
      ring
    rw [H3, H4, H5]
    have H6 : 1 + k ^ 2 + 2 * k * p - (1 + k * p) ^ 2 = k ^ 2 * (1 - p ^ 2) := by
      ring
    have H7 : (1 + k ^ 2 + 2 * k * p - (k + p) ^ 2) = 1 - p ^ 2 := by
      ring
    rw [H6, H7, Real.sqrt_mul (sq_nonneg k), Real.sqrt_sq Hk]
    rw [show k * √(1 - p ^ 2) * (k + p) + (1 + k * p) * √(1 - p ^ 2) =
              √(1 - p ^ 2) * (1 + 2 * k * p + k ^ 2) by ring]
    rw [mul_nonneg_iff]; left; refine ⟨Real.sqrt_nonneg (1 - p ^ 2), ?_⟩
    rw [show 1 + 2 * k * p + k ^ 2 = (1 - k) ^ 2 + ((1 + p) * (2 * k)) by ring]
    have H9 : -1 ≤ p := by
      unfold p; exact neg_one_le_inner_of_norm_one Hx Hz
    nlinarith
  contrapose! H2
  rw [← Real.sin_sub_two_pi]
  have H3 := angle_le_pi x y
  have H4 := angle_le_pi y z
  apply Real.sin_neg_of_neg_of_neg_pi_lt <;> grind

lemma aux06 {x z : V} (Hx : ‖x‖ = 1) (Hz : ‖z‖ = 1) {k : ℝ} (Hk : 0 ≤ k) :
    let y := normalize (x + k • z)
    angle x z = angle x y + angle y z := by
  intros y
  have Hz' : z ≠ 0 := by
    intro H; rw [H] at Hz; simp at Hz
  obtain H | H := eq_or_ne (angle x z) Real.pi
  · have H0 : x = -z := aux08_2 Hx Hz H
    subst H0; clear Hx H
    have H1 : -z + k • z = (k - 1) • z := by module
    obtain H2 | H2 | H2 := lt_trichotomy k 1
    · have H3 : y = -z := by
        unfold y
        rw [H1, normalize_smul_of_neg (by linarith), normalize_eq_self_of_norm_one Hz]
      rw [H3]; simp; exact angle_self Hz'
    · have H3 : y = 0 := by
        unfold y
        rw [H1, H2]; simp
      rw [H3]; simp; exact angle_neg_self_of_nonzero Hz'
    · have H3 : y = z := by
        unfold y
        rw [H1, normalize_smul_of_pos (by linarith), normalize_eq_self_of_norm_one Hz]
      rw [H3]; simp; exact angle_self Hz'
  obtain H0 | H0 := eq_or_ne (angle x z) 0
  · apply aux08_1 Hx Hz at H0
    have H1 : y = z := by
      unfold y
      rw [H0, show z + k • z = (1 + k) • z by module, normalize_smul_of_pos (by linarith)]
      rw [normalize_eq_self_of_norm_one Hz]
    rw [H0, H1, angle_self Hz']; simp
  have Hy' : x + k • z ≠ 0 := by
    intros H2; have H3 := H2; unfold y at *
    rw [add_eq_zero_iff_eq_neg, ← neg_smul] at H2
    apply aux00 Hx Hz at H2
    obtain H2 | H2 := H2
    · linarith
    · simp at H2
      rw [H2, add_eq_zero_iff_eq_neg] at H3; simp at H3
      rw [H3, angle_neg_left, angle_self Hz'] at H; simp at H
  have Hy : ‖y‖ = 1 := by
    unfold y
    exact norm_normalize_eq_one_iff.mpr Hy'
  obtain H1 | H1 := eq_or_ne (angle x y) 0
  · have H2 : x = y := by
      apply aux08_1 Hx Hy at H1
      exact H1
    rw [H1, H2]; simp
  obtain H2 | H2 := eq_or_ne (angle y z) 0
  · have H3 : y = z := by
      apply aux08_1 Hy Hz at H2
      exact H2
    rw [H2, H3]; simp
  have Hxyz : angle x y + angle y z ≤ Real.pi := aux09 Hx Hz Hk
  obtain H3 | H3 := eq_or_ne (angle x y) Real.pi
  · have H5 : angle y z = 0 := by linarith [angle_nonneg y z]
    tauto
  obtain H4 | H4 := eq_or_ne (angle y z) Real.pi
  · have H6 : angle x y = 0 := by linarith [angle_nonneg x y]
    tauto
  obtain Hk' | Hk' := eq_or_ne k 0
  · subst k
    have Hx' : x ≠ 0 := by intro H5; simp only [H5, norm_zero, zero_ne_one] at Hx
    unfold y; simp only [zero_smul, add_zero]
    rw [normalize_eq_self_of_norm_one Hx, angle_self Hx']; simp
  have H5 : ⟪x, z⟫ = ⟪x, z⟫ := rfl
  nth_rw 2 [angle_le_angle_add_angle_aux Hx Hy] at H5
  nth_rw 2 [angle_le_angle_add_angle_aux Hz Hy] at H5
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right] at H5
  simp only [real_inner_comm y (normalize _), real_inner_self_eq_norm_sq, Hy,
    angle_comm z y, inner_normalize_ortho] at H5
  norm_num at H5
  rw [mul_comm (Real.cos (angle y z))] at H5
  have H6 : ortho y x ≠ 0 := by
    apply aux05 Hy Hx <;> rwa [angle_comm]
  have H7 : ortho y z ≠ 0 := by
    apply aux05 Hy Hz <;> assumption
  have H8 : ‖normalize (ortho y x)‖ = 1 := norm_normalize_eq_one_iff.mpr H6
  have H9 : ‖normalize (ortho y z)‖ = 1 := norm_normalize_eq_one_iff.mpr H7
  have H10 : ⟪normalize (ortho y x), normalize (ortho y z)⟫ = - 1 := by
    rw [inner_eq_neg_one_iff_of_norm_one H8 H9]
    rw [aux01_neg] <;> try assumption
    unfold ortho y normalize
    rw [real_inner_smul_right, real_inner_smul_right]
    use -k; constructor
    · grind
    · match_scalars <;> field_simp <;> rw [← real_inner_self_eq_norm_sq] <;>
      simp [inner_add_left, inner_smul_left]
  rw [H10] at H5; ring_nf at H5
  rw [mul_comm, ← Real.cos_add, inner_eq_cos_angle Hx Hz, add_comm] at H5
  exact Real.injOn_cos ⟨angle_nonneg x z, angle_le_pi x z⟩
    ⟨by linarith [angle_nonneg x y, angle_nonneg y z], Hxyz⟩ H5

lemma aux10 {x z : V} (Hx : x ≠ 0) (Hz : z ≠ 0) {kx kz : ℝ} (Hkx : 0 ≤ kx) (Hkz : 0 ≤ kz) :
    let y := kx • x + kz • z
    y ≠ 0 → angle x z = angle x y + angle y z := by
  intro y H
  have H' : 0 < kx ∨ 0 < kz := by
    unfold y at H
    obtain H0 | H0 := em (kx = 0 ∧ kz = 0)
    · obtain ⟨H0, H1⟩ := H0
      subst H0 H1; simp at H
    · grind
  obtain H0 | H0 := em (0 < kx)
  · have H1 : 0 ≤ kz / ‖x‖ * ‖z‖ / kx := by
      rw [div_nonneg_iff]; left
      simp only [norm_pos_iff, ne_eq, not_false_eq_true, mul_nonneg_iff_of_pos_right, and_true,
                Hz, Hkx]
      rw [div_nonneg_iff]; left; simp only [norm_nonneg, and_self, Hkz]
    have H2 : normalize x + (kz / ‖x‖ * ‖z‖ / kx) • normalize z ≠ 0 := by
      intros H3; apply H; unfold y; unfold normalize at H3
      have H4 : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr Hx
      rw [← smul_assoc, smul_eq_mul, ← smul_right_inj H4] at H3
      rw [smul_add, ← smul_assoc, ← smul_assoc, smul_eq_mul, smul_eq_mul] at H3
      field_simp at H3
      have H5 : kx ≠ 0 := (ne_of_lt H0).symm
      rw [← smul_right_inj H5, smul_add, ← smul_assoc, ← smul_assoc, smul_eq_mul, smul_eq_mul] at H3
      field_simp at H3; simp at H3; exact H3
    have H3 : normalize x + (kz / ‖x‖ * ‖z‖ / kx) • normalize z = (‖x‖⁻¹ / kx) • y := by
      unfold y normalize
      match_scalars <;> field_simp
    have H4 := aux06 (norm_normalize_eq_one_iff.mpr Hx) (norm_normalize_eq_one_iff.mpr Hz) H1
    simp at H4
    rw [angle_normalize_left Hx, angle_normalize_left Hx, angle_normalize_left H2,
        angle_normalize_right Hz, angle_normalize_right H2, angle_normalize_right Hz] at H4
    have H5 : 0 < ‖x‖⁻¹ / kx := by
      have H6 : 0 < ‖x‖ := norm_pos_iff.mpr Hx
      have H7 : 0 < ‖x‖⁻¹ := inv_pos.mpr H6
      exact div_pos H7 H0
    rw [H3, angle_smul_right_of_pos _ _ H5, angle_smul_left_of_pos _ _ H5] at H4
    exact H4
  · have H1 : kx = 0 := by linarith
    subst H1; simp only [lt_self_iff_false, false_or] at H'
    have H1 : y = kz • z := by unfold y; simp
    rw [H1, angle_smul_left_of_pos _ _ H', angle_smul_right_of_pos _ _ H', angle_self Hz, add_zero]

lemma aux12 {x y z : V} (Hx : ‖x‖ = 1) (Hy : ‖y‖ = 1) (Hz : ‖z‖ = 1) :
    angle x z ≠ Real.pi → angle x z = angle x y + angle y z →
    Real.sin (angle x z) • y = Real.sin (angle y z) • x + Real.sin (angle x y) • z := by
  intros H H0
  obtain H1 | H1 := eq_or_ne (angle x z) 0
  · have H2 : angle x y = 0 := by linarith [angle_nonneg x y, angle_nonneg y z]
    have H3 : angle y z = 0 := by linarith
    rw [H1, H2, H3]; simp
  obtain H2 | H2 := eq_or_ne (angle x y) 0
  · rw [H2]; simp
    apply aux08_1 Hx Hy at H2
    rw [H2]
  obtain H3 | H3 := eq_or_ne (angle y z) 0
  · rw [H3]; simp
    apply aux08_1 Hy Hz at H3
    rw [H3]
  obtain H4 | H4 := eq_or_ne (angle x y) Real.pi
  · rw [H4] at H0
    have H5 : angle y z = 0 := by linarith [angle_le_pi x z, angle_nonneg y z]
    tauto
  obtain H5 | H5 := eq_or_ne (angle y z) Real.pi
  · rw [H5] at H0
    have H6 : angle x y = 0 := by linarith [angle_le_pi x z, angle_nonneg x y]
    tauto
  have H6 : ⟪x, z⟫ = ⟪x, z⟫ := rfl
  nth_rw 2 [angle_le_angle_add_angle_aux Hx Hy] at H6
  nth_rw 2 [angle_le_angle_add_angle_aux Hz Hy] at H6
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
             real_inner_comm y (normalize _),
            real_inner_self_eq_norm_sq, Hy, angle_comm z y, inner_normalize_ortho] at H6
  norm_num at H6
  have H7 : ⟪x, z⟫ = Real.cos (angle x y + angle y z) := by
    rw [← H0]
    exact inner_eq_cos_angle Hx Hz
  rw [H7] at H6
  rw [Real.cos_add] at H6
  ring_nf at H6
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
    apply aux05 Hy Hx <;> rwa [angle_comm]
  have H10 : ortho y z ≠ 0 := by
    apply aux05 Hy Hz <;> assumption
  have H11 : ‖normalize (ortho y x)‖ = 1 := norm_normalize_eq_one_iff.mpr H9
  have H12 : ‖normalize (ortho y z)‖ = 1 := norm_normalize_eq_one_iff.mpr H10
  rw [inner_eq_neg_one_iff_of_norm_one H11 H12] at H8
  nth_rw 2 [angle_le_angle_add_angle_aux Hx Hy]
  nth_rw 3 [angle_le_angle_add_angle_aux Hz Hy]
  rw [H8, smul_add, smul_add]; simp
  match_scalars
  · norm_num
    rw [H0, Real.sin_add, angle_comm z y]
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
    rw [H0, aux08_1 Hx Hy H4]
  obtain H5 | H5 := eq_or_ne (angle y z) 0
  · rw [H5, add_zero] at H0
    rw [H5, Real.sin_zero, zero_smul, zero_add, H0, aux08_1 Hy Hz H5]
  apply aux12 <;> assumption

theorem thm {x y z : V} (Hx : x ≠ 0) (Hy : y ≠ 0) (Hz : z ≠ 0) (Hxz : angle x z ≠ Real.pi) :
    (∃ (kx kz : ℝ), 0 ≤ kx ∧ 0 ≤ kz ∧ y = kx • x + kz • z) ↔
    angle x z = angle x y + angle y z := by
  constructor <;> intro H
  · obtain ⟨kx, ⟨kz, ⟨Hkx, ⟨Hkz, H⟩⟩⟩⟩ := H
    have H0 := aux10 Hx Hz Hkx Hkz
    rw [← H] at H0
    exact H0 Hy
  · obtain H0 | H0 := eq_or_ne (angle x z) 0
    · have H1 : angle x y = 0 := by linarith [angle_nonneg x y, angle_nonneg y z]
      rw [angle_eq_zero_iff] at H1
      obtain ⟨_, ⟨r1, ⟨H3, H4⟩⟩⟩ := H1
      use r1, 0
      simp only [le_refl, zero_smul, add_zero, true_and]
      exact ⟨le_of_lt H3, H4⟩
    · have H1 : Real.sin (angle x z) ≠ 0 := by
        intros H1
        rw [sin_eq_zero_iff_angle_eq_zero_or_angle_eq_pi] at H1
        tauto
      have Hx' : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr Hx
      have Hy' : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr Hy
      have Hz' : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr Hz
      use (Real.sin (angle y z)) / Real.sin (angle x z) / ‖x‖ * ‖y‖,
          (Real.sin (angle x y)) / Real.sin (angle x z) / ‖z‖ * ‖y‖
      refine ⟨?_, ?_, ?_⟩
      · rw [mul_nonneg_iff]; left; simp only [norm_nonneg, and_true]
        rw [div_nonneg_iff]; left; simp only [norm_nonneg, and_true]
        rw [div_nonneg_iff]; left
        exact ⟨sin_angle_nonneg y z, sin_angle_nonneg x z⟩
      · rw [mul_nonneg_iff]; left; simp only [norm_nonneg, and_true]
        rw [div_nonneg_iff]; left; simp only [norm_nonneg, and_true]
        rw [div_nonneg_iff]; left
        exact ⟨sin_angle_nonneg x y, sin_angle_nonneg x z⟩
      · have H3 : Real.sin (angle x z) / ‖y‖ ≠ 0 := div_ne_zero H1 Hy'
        rw [← smul_right_inj H3, smul_add, ← smul_assoc, ← smul_assoc, smul_eq_mul, smul_eq_mul]
        field_simp
        have H4 : ‖normalize y‖ = 1 := norm_normalize_eq_one_iff.mpr Hy
        have H5 : ‖normalize x‖ = 1 := norm_normalize_eq_one_iff.mpr Hx
        have H6 : ‖normalize z‖ = 1 := norm_normalize_eq_one_iff.mpr Hz
        have H7 := aux13 H5 H4 H6
        rw [angle_normalize_left Hx, angle_normalize_right Hz, angle_normalize_left Hx,
            angle_normalize_right Hy, angle_normalize_left Hy, angle_normalize_right Hz] at H7
        have H8 := H7 Hxz H
        unfold normalize at H8
        rw [← smul_assoc, ← smul_assoc, ← smul_assoc, smul_eq_mul, smul_eq_mul, smul_eq_mul] at H8
        field_simp at H8
        exact H8


end tinkering
