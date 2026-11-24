import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2978_517
    (normalOne : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.NoFourCycle G → (∃ c : Fin n → Bool, ∀ u v : Fin n, G.Adj u v → c u ≠ c v) → PEqualNP.TopForm.IsAO2 n C → PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsLeastAO G D ∧ PEqualNP.TopForm.TopForm G D ∧ (PEqualNP.TopForm.junk G D).card ≤ 1)
    (chargeLow : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (D : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.NoFourCycle G → (∃ c : Fin n → Bool, ∀ u v : Fin n, G.Adj u v → c u ≠ c v) → PEqualNP.TopForm.IsLeastAO G D → PEqualNP.TopForm.TopForm G D → (PEqualNP.TopForm.junk G D).card ≤ 1 → ∃ K : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G K ∧ G.edgeFinset.card + K.card ≤ D.size + 1)
    (synthesize : ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2 → Prop) [DecidableRel x3] (T : Finset (Fin (x1+x2))), (∀ p l, x3 p l → Fin.castAdd x2 p ∈ T ∨ Fin.natAdd x1 l ∈ T) → ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit) (x10 : Finset ℕ) (x11 : Finset ℕ), PEqualNP.TopForm.IsAO2 (x1 + x2) x9 ∧ (∀ (x12 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x9 x12 = Decidable.decide (∃ (x13 : Fin x1) (x14 : Fin x2), x3 x13 x14 ∧ x12 (Fin.castAdd x2 x13) = Bool.true ∧ x12 (Fin.natAdd x1 x14) = Bool.true)) ∧ x9.size ≤ (PEqualNP.ReadTwo.incid x3).card + T.card - 1 ∧ (∀ x12 ∈ x10, x12 < x1 ∨ ∃ x14 < x9.gates.length, x12 = x1 + x2 + x14 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x14).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x15 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x14).inputs, x15 ∈ x10) ∧ (∀ x12 ∈ x11, x1 ≤ x12 ∧ x12 < x1 + x2 ∨ ∃ x14 < x9.gates.length, x12 = x1 + x2 + x14 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x14).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x15 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x14).inputs, x15 ∈ x11) ∧ ∀ x12 < x9.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x12).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x15 : ℕ) (x16 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x12).inputs = [x15, x16] ∧ x15 ∈ x11 ∧ x16 ∈ x10) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x6 x7 : Fin x1) (x8 x9 : Fin x2), x6 ≠ x7 → x8 ≠ x9 → ¬(x3 x6 x8 ∧ x3 x6 x9 ∧ x3 x7 x8 ∧ x3 x7 x9)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x5 → (∀ (x8 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x5 x8 = Decidable.decide (∃ (x9 : Fin x1) (x10 : Fin x2), x3 x9 x10 ∧ x8 (Fin.castAdd x2 x9) = Bool.true ∧ x8 (Fin.natAdd x1 x10) = Bool.true)) → ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit) (x10 : Finset ℕ) (x11 : Finset ℕ), PEqualNP.TopForm.IsAO2 (x1 + x2) x9 ∧ (∀ (x12 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x9 x12 = Decidable.decide (∃ (x13 : Fin x1) (x14 : Fin x2), x3 x13 x14 ∧ x12 (Fin.castAdd x2 x13) = Bool.true ∧ x12 (Fin.natAdd x1 x14) = Bool.true)) ∧ x9.size ≤ x5.size ∧ (∀ x12 ∈ x10, x12 < x1 ∨ ∃ x14 < x9.gates.length, x12 = x1 + x2 + x14 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x14).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x15 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x14).inputs, x15 ∈ x10) ∧ (∀ x12 ∈ x11, x1 ≤ x12 ∧ x12 < x1 + x2 ∨ ∃ x14 < x9.gates.length, x12 = x1 + x2 + x14 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x14).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x15 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x14).inputs, x15 ∈ x11) ∧ ∀ x12 < x9.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x12).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x15 : ℕ) (x16 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x12).inputs = [x15, x16] ∧ x15 ∈ x11 ∧ x16 ∈ x10 := by
  intro x1 x2 x3 x4 x5 h4 hao hfun
  classical
  obtain ⟨G, hG⟩ : ∃ G : SimpleGraph (Fin (x1 + x2)), ∀ a b, G.Adj a b ↔
      ∃ (p : Fin x1) (l : Fin x2), x3 p l ∧ ((a = Fin.castAdd x2 p ∧ b = Fin.natAdd x1 l) ∨
        (a = Fin.natAdd x1 l ∧ b = Fin.castAdd x2 p)) := by
    refine ⟨SimpleGraph.mk (fun a b => ∃ (p : Fin x1) (l : Fin x2), x3 p l ∧
        ((a = Fin.castAdd x2 p ∧ b = Fin.natAdd x1 l) ∨ (a = Fin.natAdd x1 l ∧ b = Fin.castAdd x2 p)))
      ?_ ?_, fun a b => Iff.rfl⟩
    · constructor
      intro a b h
      obtain ⟨p, l, h, e⟩ := h
      rcases e with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · exact ⟨p, l, h, Or.inr ⟨e2, e1⟩⟩
      · exact ⟨p, l, h, Or.inl ⟨e2, e1⟩⟩
    · constructor
      intro a h
      obtain ⟨p, l, -, e⟩ := h
      have := p.isLt
      rcases e with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · have := congrArg Fin.val (e1.symm.trans e2)
        simp at this
        omega
      · have := congrArg Fin.val (e1.symm.trans e2)
        simp at this
        omega
  have hval : ∀ u v, G.Adj u v → ∃ (p : Fin x1) (l : Fin x2), x3 p l ∧
      ((u.val = p.val ∧ v.val = x1 + l.val) ∨ (u.val = x1 + l.val ∧ v.val = p.val)) := by
    intro u v h
    obtain ⟨p, l, h, e⟩ := (hG u v).1 h
    refine ⟨p, l, h, ?_⟩
    rcases e with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
  have hC4 : PEqualNP.TopForm.NoFourCycle G := by
    intro a b hab
    rw [Finset.card_le_one]
    intro w1 hw1 w2 hw2
    by_contra hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw1 hw2
    have hu' : a.val ≠ b.val := fun e => hab (Fin.ext e)
    have hv' : w1.val ≠ w2.val := fun e => hw (Fin.ext e)
    obtain ⟨p11, l11, h11, e11⟩ := hval a w1 hw1.1
    obtain ⟨p12, l12, h12, e12⟩ := hval a w2 hw2.1
    obtain ⟨p21, l21, h21, e21⟩ := hval b w1 hw1.2
    obtain ⟨p22, l22, h22, e22⟩ := hval b w2 hw2.2
    have b11 := p11.isLt
    have b12 := p12.isLt
    have b21 := p21.isLt
    have b22 := p22.isLt
    by_cases hs : a.val < x1
    · have q1 : p11 = p12 := Fin.ext (by omega)
      have q2 : p21 = p22 := Fin.ext (by omega)
      have q3 : l11 = l21 := Fin.ext (by omega)
      have q4 : l12 = l22 := Fin.ext (by omega)
      subst q1 q2 q3 q4
      exact h4 p11 p21 l11 l12 (fun e => hu' (by rw [Fin.ext_iff] at e; omega))
        (fun e => hv' (by rw [Fin.ext_iff] at e; omega)) ⟨h11, h12, h21, h22⟩
    · have q1 : p11 = p21 := Fin.ext (by omega)
      have q2 : p12 = p22 := Fin.ext (by omega)
      have q3 : l11 = l12 := Fin.ext (by omega)
      have q4 : l21 = l22 := Fin.ext (by omega)
      subst q1 q2 q3 q4
      exact h4 p11 p12 l11 l21 (fun e => hv' (by rw [Fin.ext_iff] at e; omega))
        (fun e => hu' (by rw [Fin.ext_iff] at e; omega)) ⟨h11, h21, h12, h22⟩
  have hbip : ∃ c : Fin (x1 + x2) → Bool, ∀ u v : Fin (x1 + x2), G.Adj u v → c u ≠ c v := by
    refine ⟨fun a => decide (a.val < x1), ?_⟩
    intro u v h
    obtain ⟨p, l, -, e⟩ := hval u v h
    have := p.isLt
    rcases e with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · have h1 : u.val < x1 := by omega
      have h2 : ¬ v.val < x1 := by omega
      simp [h1, h2]
    · have h1 : ¬ u.val < x1 := by omega
      have h2 : v.val < x1 := by omega
      simp [h1, h2]
  have hF : PEqualNP.MetaComplexity.circuitFun (x1 + x2) x5 =
      PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ := by
    funext x
    rw [hfun x]
    unfold PEqualNP.MetaComplexity.NestedCover.graphFun
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨p, l, h, hp, hl⟩
      exact Or.inr ⟨Fin.castAdd x2 p, Fin.natAdd x1 l, (hG _ _).2 ⟨p, l, h, Or.inl ⟨rfl, rfl⟩⟩, hp, hl⟩
    · rintro (⟨a, ha, -⟩ | ⟨u, v, huv, hu, hv⟩)
      · simp at ha
      · obtain ⟨p, l, h, e⟩ := (hG u v).1 huv
        rcases e with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨p, l, h, hu, hv⟩
        · exact ⟨p, l, h, hv, hu⟩
  obtain ⟨D, hD, hTD, hjD⟩ := normalOne (x1 + x2) G x5 hC4 hbip hao hF
  obtain ⟨K, hK, hKc⟩ := chargeLow (x1 + x2) G D hC4 hbip hD hTD hjD
  have hK' : ∀ p l, x3 p l → Fin.castAdd x2 p ∈ K ∨ Fin.natAdd x1 l ∈ K := by
    intro p l h
    exact hK _ _ ((hG _ _).2 ⟨p, l, h, Or.inl ⟨rfl, rfl⟩⟩)
  have hE : G.edgeFinset.card = (PEqualNP.ReadTwo.incid x3).card := by
    have himg : G.edgeFinset = (PEqualNP.ReadTwo.incid x3).image
        (fun e : Fin x1 × Fin x2 => Sym2.mk (Fin.castAdd x2 e.1) (Fin.natAdd x1 e.2)) := by
      ext z
      induction z using Sym2.ind with
      | h a b =>
        rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, hG, Finset.mem_image]
        unfold PEqualNP.ReadTwo.incid
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Sym2.eq_iff]
        constructor
        · rintro ⟨p, l, h, e⟩
          refine ⟨(p, l), h, ?_⟩
          rcases e with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact Or.inl ⟨rfl, rfl⟩
          · exact Or.inr ⟨rfl, rfl⟩
        · rintro ⟨e, h, he⟩
          refine ⟨e.1, e.2, h, ?_⟩
          rcases he with ⟨e1, e2⟩ | ⟨e1, e2⟩
          · exact Or.inl ⟨e1.symm, e2.symm⟩
          · exact Or.inr ⟨e2.symm, e1.symm⟩
    rw [himg]
    apply Finset.card_image_of_injective
    intro a b h
    simp only [Sym2.eq_iff] at h
    have ha := a.1.isLt
    have hb := b.1.isLt
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have e1 := congrArg Fin.val h1
      have e2 := congrArg Fin.val h2
      simp only [Fin.val_castAdd, Fin.val_natAdd] at e1 e2
      exact Prod.ext (Fin.ext e1) (Fin.ext (by omega))
    · have e1 := congrArg Fin.val h1
      simp only [Fin.val_castAdd, Fin.val_natAdd] at e1
      omega
  obtain ⟨x9, x10, x11, s1, s2, s3, s4, s5, s6⟩ := @synthesize x1 x2 x3 x4 K hK'
  have hDC := hD.2.2 x5 hao hF
  refine ⟨x9, x10, x11, s1, s2, ?_, s4, s5, s6⟩
  omega
