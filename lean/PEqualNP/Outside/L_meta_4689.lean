import PEqualNP.Defs
import Mathlib

namespace PEqualNP.Outside.L_meta_4689

theorem core (g a b e : ℕ) (hg : g ≤ 4512) (hs : a + b ≤ g + 1) (hab : a ≤ b)
    (he : e ≤ a * b) (h : e * e ≤ b * (a * (a - 1) + e)) : e ≤ 24 * g := by
  rcases Nat.eq_zero_or_pos a with h0 | ha
  · subst h0
    simp at he
    omega
  by_contra hc0
  have hc : 24 * g < e := Nat.lt_of_not_le hc0
  have ha1 : 1 ≤ a := ha
  have h' : (e : ℤ) * e ≤ b * (a * ((a : ℤ) - 1) + e) := by
    have h2 := h
    zify [ha1] at h2
    exact h2
  have hc' : (24 : ℤ) * g + 1 ≤ e := by exact_mod_cast hc
  have hg' : (g : ℤ) ≤ 4512 := by exact_mod_cast hg
  have hs' : (a : ℤ) + b ≤ g + 1 := by exact_mod_cast hs
  have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha1
  have hab' : (a : ℤ) ≤ b := by exact_mod_cast hab
  -- replace e by F = 24 g + 1
  have hF : ((24 : ℤ) * g + 1) * (24 * g + 1) ≤ b * (a * ((a : ℤ) - 1) + (24 * g + 1)) := by
    have hm : (0 : ℤ) ≤ ((e : ℤ) - (24 * g + 1)) * ((e : ℤ) + (24 * g + 1) - b) := by
      apply mul_nonneg <;> linarith
    nlinarith
  rcases lt_or_eq_of_le hab with hlt | heq
  · -- a < b
    have hlt' : (a : ℤ) + 1 ≤ b := by exact_mod_cast hlt
    have hq : (0 : ℤ) ≤ a * ((a : ℤ) - 1) + (24 * g + 1) := by
      have : (0 : ℤ) ≤ a * ((a : ℤ) - 1) := mul_nonneg (by linarith) (by linarith)
      linarith
    have hB : (b : ℤ) * (a * ((a : ℤ) - 1) + (24 * g + 1))
        ≤ ((g : ℤ) + 1 - a) * (a * ((a : ℤ) - 1) + (24 * g + 1)) :=
      mul_le_mul_of_nonneg_right (by linarith) hq
    obtain ⟨D, hD⟩ : ∃ D : ℤ, (g : ℤ) = 2 * a + D := ⟨(g : ℤ) - 2 * a, by ring⟩
    have hD0 : 0 ≤ D := by linarith
    have p1 : (0 : ℤ) ≤ (a : ℤ) * a * (4512 - g) := by
      apply mul_nonneg
      · positivity
      · linarith
    have p2 : (0 : ℤ) ≤ (a : ℤ) * D * (4466 - a) := by
      apply mul_nonneg
      · apply mul_nonneg <;> linarith
      · linarith
    have hDD : (0 : ℤ) ≤ D * D := mul_nonneg hD0 hD0
    rw [hD] at hF hB p1
    nlinarith
  · -- a = b
    have heq' : (a : ℤ) = b := by exact_mod_cast heq
    rw [← heq'] at hF hs'
    have hF0 : ((48 : ℤ) * a - 23) * (48 * a - 23) ≤ a * (a * ((a : ℤ) - 1) + (48 * a - 23)) := by
      have hm : (0 : ℤ) ≤ ((24 : ℤ) * g + 1 - (48 * a - 23)) * ((24 : ℤ) * g + 1 + (48 * a - 23) - a) := by
        apply mul_nonneg <;> linarith
      nlinarith
    have hA : (a : ℤ) ≤ 2256 := by linarith
    have p : (0 : ℤ) ≤ (a : ℤ) * (((a : ℤ) - 1) * (2256 - a)) := by
      apply mul_nonneg
      · linarith
      · apply mul_nonneg <;> linarith
    nlinarith

end PEqualNP.Outside.L_meta_4689

theorem PEqualNP.Outside.L_meta_4689 : ∀ (x1 x2 x3 x4 : ℕ), x1 ≤ (4512 : ℕ) → x2 + x3 ≤ x1 + (1 : ℕ) → x4 ≤ x2 * x3 → x4 * x4 ≤ x3 * (x2 * (x2 - (1 : ℕ)) + x4) → x4 * x4 ≤ x2 * (x3 * (x3 - (1 : ℕ)) + x4) → x4 ≤ (24 : ℕ) * x1 := by
  intro g a b e hg hs he h1 h2
  rcases le_total a b with hab | hba
  · exact PEqualNP.Outside.L_meta_4689.core g a b e hg hs hab he h1
  · exact PEqualNP.Outside.L_meta_4689.core g b a e hg (by omega) hba (by rw [Nat.mul_comm]; exact he) h2
