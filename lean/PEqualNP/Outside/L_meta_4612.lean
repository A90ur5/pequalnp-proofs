import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4612

def Gt (S : List ℕ) (g : ℕ) : Prop :=
  ∃ a ∈ S, ∃ b ∈ S, g = a &&& b ∨ g = a ||| b

def Prog (B L : List ℕ) : Prop :=
  ∀ (i : Fin L.length), ∃ a ∈ B ++ List.take (↑i) L, ∃ b ∈ B ++ List.take (↑i) L,
    L.get i = a &&& b ∨ L.get i = a ||| b

theorem gt_mono {S T : List ℕ} {g : ℕ} (h : Gt S g) (hST : ∀ v ∈ S, v ∈ T) : Gt T g := by
  obtain ⟨a, ha, b, hb, h⟩ := h
  exact ⟨a, hST a ha, b, hST b hb, h⟩

theorem prog_nil (B : List ℕ) : Prog B [] := fun i => i.elim0

theorem prog_snoc {B L : List ℕ} {g : ℕ} (hL : Prog B L) (hg : Gt (B ++ L) g) :
    Prog B (L ++ [g]) := by
  intro i
  have hi : (i : ℕ) < L.length + 1 := by simpa using i.2
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
  · obtain ⟨a, ha, b, hb, hab⟩ := hL ⟨i, h⟩
    have e1 : List.take (↑i) (L ++ [g]) = List.take (↑i) L := by
      rw [List.take_append_of_le_length (by omega)]
    have e2 : (L ++ [g]).get i = L.get ⟨i, h⟩ := by
      simp [List.getElem_append_left h]
    refine ⟨a, ?_, b, ?_, ?_⟩
    · rw [e1]; exact ha
    · rw [e1]; exact hb
    · rw [e2]; exact hab
  · have e1 : List.take (↑i) (L ++ [g]) = L := by
      rw [h, List.take_left' rfl]
    have e2 : (L ++ [g]).get i = g := by
      simp [h]
    obtain ⟨a, ha, b, hb, hab⟩ := hg
    refine ⟨a, ?_, b, ?_, ?_⟩
    · rw [e1]; exact ha
    · rw [e1]; exact hb
    · rw [e2]; exact hab

theorem prog_unsnoc {B L : List ℕ} {g : ℕ} (h : Prog B (L ++ [g])) :
    Prog B L ∧ Gt (B ++ L) g := by
  constructor
  · intro i
    have hi : (i : ℕ) < (L ++ [g]).length := by simp only [List.length_append, List.length_singleton]; omega
    obtain ⟨a, ha, b, hb, hab⟩ := h ⟨i, hi⟩
    have e1 : List.take (↑i) (L ++ [g]) = List.take (↑i) L := by
      rw [List.take_append_of_le_length (by omega)]
    have e2 : (L ++ [g]).get ⟨i, hi⟩ = L.get i := by
      simp [List.getElem_append_left i.2]
    refine ⟨a, ?_, b, ?_, ?_⟩
    · rw [← e1]; exact ha
    · rw [← e1]; exact hb
    · rw [← e2]; exact hab
  · have hi : L.length < (L ++ [g]).length := by simp
    obtain ⟨a, ha, b, hb, hab⟩ := h ⟨L.length, hi⟩
    have e1 : List.take L.length (L ++ [g]) = L := List.take_left' rfl
    have e2 : (L ++ [g]).get ⟨L.length, hi⟩ = g := by simp
    refine ⟨a, ?_, b, ?_, ?_⟩
    · rw [← e1]; exact ha
    · rw [← e1]; exact hb
    · rw [← e2]; exact hab

theorem prog_append {B L C : List ℕ} (hL : Prog B L) (hC : ∀ v ∈ C, v ∈ B ++ L) :
    ∀ M : List ℕ, Prog C M → Prog B (L ++ M) := by
  intro M
  induction M using List.reverseRecOn with
  | nil => intro _; simpa using hL
  | append_singleton M g ih =>
    intro hM
    obtain ⟨hM1, hg⟩ := prog_unsnoc hM
    have := prog_snoc (ih hM1) (gt_mono hg (by
      intro v hv
      rcases List.mem_append.mp hv with h | h
      · have := hC v h
        simp only [List.mem_append] at this ⊢
        tauto
      · simp only [List.mem_append]; tauto))
    simpa [List.append_assoc] using this

theorem prune (B : List ℕ) : ∀ L : List ℕ, Prog B L →
    ∃ L' : List ℕ, L'.length ≤ L.length ∧ L'.Nodup ∧ (∀ v ∈ L', v ∉ B) ∧ Prog B L' ∧
      ∀ v ∈ L, v ∈ B ∨ v ∈ L' := by
  intro L
  induction L using List.reverseRecOn with
  | nil => intro _; exact ⟨[], le_rfl, List.nodup_nil, by simp, prog_nil B, by simp⟩
  | append_singleton L g ih =>
    intro hL
    obtain ⟨hL1, hg⟩ := prog_unsnoc hL
    obtain ⟨L', hlen, hnd, hdis, hP, hcov⟩ := ih hL1
    have hg' : Gt (B ++ L') g := gt_mono hg (by
      intro v hv
      rcases List.mem_append.mp hv with h | h
      · exact List.mem_append_left _ h
      · rcases hcov v h with h' | h'
        · exact List.mem_append_left _ h'
        · exact List.mem_append_right _ h')
    by_cases hgm : g ∈ B ∨ g ∈ L'
    · refine ⟨L', by simp; omega, hnd, hdis, hP, ?_⟩
      intro v hv
      rcases List.mem_append.mp hv with h | h
      · exact hcov v h
      · simp at h; subst h; exact hgm
    · rw [not_or] at hgm
      refine ⟨L' ++ [g], by simp; omega, ?_, ?_, prog_snoc hP hg', ?_⟩
      · rw [List.nodup_append]
        refine ⟨hnd, List.nodup_singleton g, ?_⟩
        intro a ha b hb
        simp at hb; subst hb
        intro e; subst e; exact hgm.2 ha
      · intro v hv
        rcases List.mem_append.mp hv with h | h
        · exact hdis v h
        · simp at h; subst h; exact hgm.1
      · intro v hv
        rcases List.mem_append.mp hv with h | h
        · rcases hcov v h with h' | h'
          · exact Or.inl h'
          · exact Or.inr (List.mem_append_left _ h')
        · simp at h; subst h; exact Or.inr (List.mem_append_right _ (List.mem_singleton_self _))

end PEqualNP.Outside.L_meta_4612

theorem PEqualNP.Outside.L_meta_4612 :
    have x1 : List ℕ → List ℕ → Prop := fun (x1 x2 : List ℕ) => ∀ (x3 : Fin x2.length), ∃ x4 ∈ x1 ++ List.take (↑x3) x2, ∃ x5 ∈ x1 ++ List.take (↑x3) x2, x2.get x3 = x4 &&& x5 ∨ x2.get x3 = x4 ||| x5; ∀ (x2 x3 x4 x5 : List ℕ), ∀ x6 ∉ x2, x1 x2 x3 → (∀ x9 ∈ x4, x9 ∈ x2 ++ x3) → x1 x4 x5 → x6 ∈ x4 ++ x5 → ∃ (x12 : List ℕ), x12.length ≤ x3.length + x5.length ∧ x12.Nodup ∧ (∀ x13 ∈ x12, x13 ∉ x2) ∧ x6 ∈ x12 ∧ x1 x2 x12 := by
  intro x1 x2 x3 x4 x5 x6 hx6 h3 h4 h5 hmem
  have hP : PEqualNP.Outside.L_meta_4612.Prog x2 (x3 ++ x5) :=
    PEqualNP.Outside.L_meta_4612.prog_append h3 h4 x5 h5
  obtain ⟨L', hlen, hnd, hdis, hP', hcov⟩ := PEqualNP.Outside.L_meta_4612.prune x2 _ hP
  refine ⟨L', by simpa using hlen, hnd, hdis, ?_, hP'⟩
  have hin : x6 ∈ x3 ++ x5 := by
    rcases List.mem_append.mp hmem with h | h
    · rcases List.mem_append.mp (h4 x6 h) with h' | h'
      · exact absurd h' hx6
      · exact List.mem_append_left _ h'
    · exact List.mem_append_right _ h
  rcases hcov x6 hin with h | h
  · exact absurd h hx6
  · exact h
