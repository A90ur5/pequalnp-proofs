import Mathlib
import PEqualNP.Defs

-- Monotonicity plus the value on the two-vertex minterm of the chosen edge.

theorem PEqualNP.Outside.L_meta_4777 : ∀ (x1 : List (ℕ × ℕ)) (x2 : (Fin (14 : ℕ) → Bool) → Bool), (x1.all fun (x3 : ℕ × ℕ) => Decidable.decide (x3.1 < x3.2)) = Bool.true → (∀ (x4 x5 : Fin (14 : ℕ) → Bool), (∀ (x6 : Fin (14 : ℕ)), x4 x6 = Bool.true → x5 x6 = Bool.true) → x2 x4 = Bool.true → x2 x5 = Bool.true) → (∀ (x5 : Fin (14 : ℕ) → Bool), ((∃ (x6 : Fin (14 : ℕ)) (x7 : Fin (14 : ℕ)), (↑x6, ↑x7) ∈ x1 ∧ x5 x6 = Bool.true ∧ x5 x7 = Bool.true) ∧ ∀ (x6 : Fin (14 : ℕ)), x5 x6 = Bool.true → ¬∃ (x8 : Fin (14 : ℕ)) (x9 : Fin (14 : ℕ)), (↑x8, ↑x9) ∈ x1 ∧ Function.update x5 x6 Bool.false x8 = Bool.true ∧ Function.update x5 x6 Bool.false x9 = Bool.true) → x5 (0 : Fin (14 : ℕ)) = Bool.false ∨ x5 (7 : Fin (14 : ℕ)) = Bool.false → (x2 x5 = Bool.true ↔ ∃ (x8 : Fin (14 : ℕ)) (x9 : Fin (14 : ℕ)), (↑x8, ↑x9) ∈ x1 ∧ x5 x8 = Bool.true ∧ x5 x9 = Bool.true)) → ∀ (x6 : Fin (14 : ℕ) → Bool), (∃ (x7 : Fin (14 : ℕ)) (x8 : Fin (14 : ℕ)), (↑x7, ↑x8) ∈ x1 ∧ (x7 ≠ (0 : Fin (14 : ℕ)) ∨ x8 ≠ (7 : Fin (14 : ℕ))) ∧ x6 x7 = Bool.true ∧ x6 x8 = Bool.true) → x2 x6 = Bool.true := by
  intro x1 x2 hall hmono hmin x6 hx6
  obtain ⟨a, b, hab, hne, ha, hb⟩ := hx6
  have hlt : ∀ p ∈ x1, p.1 < p.2 := by
    intro p hp
    have := List.all_eq_true.mp hall p hp
    simpa using this
  have hablt : (a : ℕ) < b := hlt _ hab
  let m : Fin 14 → Bool := fun v => decide (v = a ∨ v = b)
  have hma : m a = true := by simp [m]
  have hmb : m b = true := by simp [m]
  have hmem : ∀ v, m v = true → v = a ∨ v = b := by
    intro v hv
    simpa [m] using hv
  have key : x2 m = true := by
    have hm := hmin m
    refine (hm ⟨⟨a, b, hab, hma, hmb⟩, ?_⟩ ?_).mpr ⟨a, b, hab, hma, hmb⟩
    · intro v hv
      rintro ⟨c, d, hcd, hc, hd⟩
      have hcdlt : (c : ℕ) < d := hlt _ hcd
      have hcv : c ≠ v := by
        intro h; subst h; simp at hc
      have hdv : d ≠ v := by
        intro h; subst h; simp at hd
      rw [Function.update_of_ne hcv] at hc
      rw [Function.update_of_ne hdv] at hd
      have hc' := hmem c hc
      have hd' := hmem d hd
      have hv' := hmem v hv
      have hcd' : c ≠ d := by
        intro h; subst h; exact lt_irrefl _ hcdlt
      apply hcd'
      rcases hc' with h1 | h1 <;> rcases hd' with h2 | h2 <;> rcases hv' with h3 | h3 <;>
        (subst_vars; first | rfl | exact absurd rfl hcv | exact absurd rfl hdv)
    · by_contra h
      push Not at h
      obtain ⟨h0, h7⟩ := h
      have h0' := hmem 0 (by simpa using h0)
      have h7' := hmem 7 (by simpa using h7)
      have hab' : a ≠ b := by
        intro h; subst h; exact lt_irrefl _ hablt
      rcases h0' with h0' | h0' <;> rcases h7' with h7' | h7'
      · exact absurd (h0'.trans h7'.symm) (by decide)
      · subst h0'; subst h7'; simp at hne
      · subst h0'; subst h7'; exact absurd hablt (by decide)
      · exact absurd (h0'.trans h7'.symm) (by decide)
  exact hmono m x6 (fun v hv => by rcases hmem v hv with rfl | rfl <;> assumption) key
