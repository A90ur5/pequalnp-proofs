import Mathlib.Tactic.IntervalCases
import PEqualNP.Defs

/- The live-set normalization, the frontier certificate checker and its kernel proofs are copied
from the merged L_meta_722.lean (by Digger-Rockwell, from public PR 801 of brilliant-hq/pequalnp-proofs,
source commit ea90309308dd46a22d4a469766e46dd63f4484d0). The function, rows, score pool and
frontier data are new and computed for this graph. The single block-swap symmetry of L_meta_722 is
replaced by the eight automorphisms of this graph (vertices 0 1 3 4), applied as lists of masked swaps. -/

namespace PEqualNP.Outside.L_meta_14810

open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

def kept {α : Type} (b : Bool) (x : α) (xs : List α) : List α :=
  if b then x :: xs else xs

def Run {α : Type} (inv : α → α) (meet join : α → α → α) (y : α) (t : ℕ) (ws : List α) : Prop :=
  ∀ P : ℕ → List α → Prop, P 0 [y] →
    (∀ {s xs zs}, List.Perm xs zs → P s xs → P s zs) →
    (∀ {s a r} (save : Bool), P s (inv a :: kept save a r) → P (s + 1) (a :: r)) →
    (∀ {s a b r} (c ka kb : Bool),
      P s ((if c then meet a b else join a b) :: kept ka a (kept kb b r)) →
      P (s + 1) (a :: b :: r)) → P t ws

section
variable {α : Type} {inv : α → α} {meet join : α → α → α} {y : α}

theorem Run.done : Run inv meet join y 0 [y] := fun _ d _ _ _ => d

theorem Run.perm {s xs zs} (p : List.Perm xs zs) (h : Run inv meet join y s xs) :
    Run inv meet join y s zs := fun P d q u b => q p (h P d q u b)

theorem Run.one {s a r} (save : Bool)
    (h : Run inv meet join y s (inv a :: kept save a r)) :
    Run inv meet join y (s + 1) (a :: r) := fun P d q u b => u save (h P d q u b)

theorem Run.two {s a b r} (c ka kb : Bool)
    (h : Run inv meet join y s ((if c then meet a b else join a b) :: kept ka a (kept kb b r))) :
    Run inv meet join y (s + 1) (a :: b :: r) := fun P d q u v => v c ka kb (h P d q u v)

theorem Run.fold {P : ∀ t ws, Run inv meet join y t ws → Prop}
    (done : P 0 [y] Run.done)
    (perm : ∀ {s xs zs} (hp : List.Perm xs zs) (h : Run inv meet join y s xs),
      P s xs h → P s zs (Run.perm hp h))
    (one : ∀ {s a r} (save : Bool)
      (h : Run inv meet join y s (inv a :: kept save a r)),
      P _ _ h → P _ _ (Run.one save h))
    (two : ∀ {s a b r} (c ka kb : Bool)
      (h : Run inv meet join y s ((if c then meet a b else join a b) :: kept ka a (kept kb b r))),
      P _ _ h → P _ _ (Run.two c ka kb h))
    {t ws} (h : Run inv meet join y t ws) : P t ws h := by
  have hex := h (fun s xs => ∃ h' : Run inv meet join y s xs, P s xs h')
    ⟨Run.done, done⟩
    (fun hp ⟨h', ih⟩ => ⟨Run.perm hp h', perm hp h' ih⟩)
    (fun k ⟨h', ih⟩ => ⟨Run.one k h', one k h' ih⟩)
    (fun c a b ⟨h', ih⟩ => ⟨Run.two c a b h', two c a b h' ih⟩)
  exact hex.elim fun _ hp => hp

end

theorem kept_map {α β : Type} (e : α → β) (b : Bool) (x : α) (xs : List α) :
    (kept b x xs).map e = kept b (e x) (xs.map e) := by
  cases b <;> simp [kept]

theorem mem_kept {α : Type} (b : Bool) (x a : α) (xs : List α) :
    a ∈ kept b x xs ↔ (b = true ∧ a = x) ∨ a ∈ xs := by
  cases b <;> simp [kept]

theorem nodup_kept {α : Type} (b : Bool) (x : α) (xs : List α) (h : xs.Nodup) (hx : x ∉ xs) :
    (kept b x xs).Nodup := by
  cases b
  · simpa [kept] using h
  · simpa [kept] using And.intro hx h

theorem Run.map {α β : Type} (e : α → β) {inv : α → α} {meet join : α → α → α}
    {inv' : β → β} {meet' join' : β → β → β}
    (hi : ∀ a, e (inv a) = inv' (e a)) (hm : ∀ a b, e (meet a b) = meet' (e a) (e b))
    (hj : ∀ a b, e (join a b) = join' (e a) (e b))
    {y : α} {s : ℕ} {ws : List α} (h : Run inv meet join y s ws) :
    Run inv' meet' join' (e y) s (ws.map e) := by
  induction h using Run.fold with
  | done => exact Run.done
  | perm hp _ ih => exact Run.perm (hp.map e) ih
  | @one s a rest save _ ih =>
    have e1 : (inv a :: kept save a rest).map e
        = inv' (e a) :: kept save (e a) (rest.map e) := by
      simp [kept_map, hi]
    rw [e1] at ih
    exact Run.one save ih
  | @two s a b rest conj ka kb _ ih =>
    have e1 : ((if conj then meet a b else join a b) :: kept ka a (kept kb b rest)).map e
        = (if conj then meet' (e a) (e b) else join' (e a) (e b))
            :: kept ka (e a) (kept kb (e b) (rest.map e)) := by
      cases conj <;> simp [kept_map, hm, hj]
    rw [e1] at ih
    exact Run.two conj ka kb ih

abbrev BFn (n : ℕ) := (Fin n → Bool) → Bool

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_nil (w : List Bool) : wiresFrom [] w = w := rfl

theorem wiresFrom_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wiresFrom (g :: gs) w =
      wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

theorem wiresFrom_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    wiresFrom (gs₁ ++ gs₂) w = wiresFrom gs₂ (wiresFrom gs₁ w) :=
  List.foldl_append

theorem length_wiresFrom (gs : List Gate) : ∀ w : List Bool,
    (wiresFrom gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wiresFrom]
  | cons g gs ih =>
    intro w
    rw [wiresFrom_cons, ih]
    simp
    omega

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom]⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    exact ⟨[g.op.eval (g.inputs.map fun i => w.getD i false)] ++ t, by
      rw [wiresFrom_cons, ht, List.append_assoc]⟩

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht⟩ := wiresFrom_prefix gs w
  rw [ht]
  exact List.getD_append _ _ _ _ h

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

theorem split_at (gs : List Gate) (p : ℕ) (g : Gate) (hp : gs[p]? = some g) :
    ∃ pre post, gs = pre ++ g :: post ∧ pre.length = p := by
  have hlt : p < gs.length := (List.getElem?_eq_some_iff.1 hp).1
  have hgp : gs[p] = g := (List.getElem?_eq_some_iff.1 hp).2
  refine ⟨gs.take p, gs.drop (p + 1), ?_, by simp [hlt.le]⟩
  calc gs = gs.take p ++ gs.drop p := (List.take_append_drop p gs).symm
    _ = gs.take p ++ gs[p] :: gs.drop (p + 1) := by rw [List.drop_eq_getElem_cons hlt]
    _ = gs.take p ++ g :: gs.drop (p + 1) := by rw [hgp]

def val (gs : List Gate) (n : ℕ) (a : ℕ) : BFn n :=
  fun x => (wiresFrom gs (List.ofFn x)).getD a false

theorem val_input (gs : List Gate) (n : ℕ) (i : Fin n) : val gs n i = fun x => x i := by
  funext x
  unfold val
  rw [getD_wiresFrom _ _ _ (by simp)]
  simp

theorem val_gate (n : ℕ) (gs : List Gate) (p : ℕ) (g : Gate) (hp : gs[p]? = some g)
    (hlt : ∀ a ∈ g.inputs, a < n + p) (x : Fin n → Bool) :
    val gs n (n + p) x = g.op.eval (g.inputs.map fun a => val gs n a x) := by
  obtain ⟨pre, post, rfl, hlen⟩ := split_at gs p g hp
  unfold val
  have h1 : wiresFrom (pre ++ g :: post) (List.ofFn x) = wiresFrom post
      (wiresFrom pre (List.ofFn x) ++
        [g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn x)).getD i false)]) := by
    rw [wiresFrom_append]; rfl
  have hl : (wiresFrom pre (List.ofFn x)).length = n + p := by
    rw [length_wiresFrom]; simp [hlen]
  rw [h1, getD_wiresFrom _ _ _ (by simp [hl]), getD_snoc_len _ _ _ _ hl]
  congr 1
  apply List.map_congr_left
  intro a ha
  have hal := hlt a ha
  have e1 := getD_wiresFrom post (wiresFrom pre (List.ofFn x) ++
        [g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn x)).getD i false)]) a
        (by simp [hl]; omega)
  rw [e1, List.getD_append _ _ _ _ (by omega)]

def SCleanGate (m : ℕ) (g : Gate) : Prop :=
  (g.op = GateOp.not ∧ ∃ j, j < m ∧ g.inputs = [j]) ∨
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ j k, j < m ∧ k < m ∧ j ≠ k ∧ g.inputs = [j, k])

theorem SCleanGate.lt {m : ℕ} {g : Gate} (h : SCleanGate m g) : ∀ a ∈ g.inputs, a < m := by
  rcases h with ⟨_, j, hj, hin⟩ | ⟨_, j, k, hj, hk, _, hin⟩ <;> rw [hin] <;> simp_all

def SCleanL (n : ℕ) (gs : List Gate) : Prop :=
  ∀ p g, gs[p]? = some g → SCleanGate (n + p) g

def statVal (w : List Bool) : Sum Bool ℕ → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def statValid (m : ℕ) : Sum Bool ℕ → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

theorem statValid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Sum Bool ℕ, statValid m s → statValid m' s
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h

theorem statVal_append (w t : List Bool) : ∀ s : Sum Bool ℕ, statValid w.length s →
    statVal (w ++ t) s = statVal w s
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj

def simpNot (m : ℕ) : List (Sum Bool ℕ) → Option Gate × Sum Bool ℕ
  | [] => (none, Sum.inl true)
  | Sum.inl c :: _ => (none, Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not, [j]⟩, Sum.inr m)

def simpAnd (m : ℕ) : List (Sum Bool ℕ) → Option Gate × Sum Bool ℕ
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, if c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, if c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] =>
      if j = k then (none, Sum.inr j) else (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simpOr (m : ℕ) : List (Sum Bool ℕ) → Option Gate × Sum Bool ℕ
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, if c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, if c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] =>
      if j = k then (none, Sum.inr j) else (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simplify (op : GateOp) (m : ℕ) (ins : List (Sum Bool ℕ)) : Option Gate × Sum Bool ℕ :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Sum.inl false)

theorem simplify_clean (op : GateOp) (m : ℕ) (ins : List (Sum Bool ℕ))
    (hv : ∀ s ∈ ins, statValid m s) :
    ∀ g ∈ (simplify op m ins).1, SCleanGate m g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
    · simp [simpAnd] at hg
    · cases a <;> simp [simpAnd] at hg
    · cases a <;> cases b <;> simp only [simpAnd, Option.mem_def] at hg
      all_goals try contradiction
      rename_i j k
      by_cases hjk : j = k
      · simp [hjk] at hg
      · simp only [hjk, ite_false, Option.some.injEq] at hg
        subst hg
        exact Or.inr ⟨Or.inl rfl, j, k, hv (Sum.inr j) (by simp), hv (Sum.inr k) (by simp), hjk, rfl⟩
    · simp [simpAnd] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
    · simp [simpOr] at hg
    · cases a <;> simp [simpOr] at hg
    · cases a <;> cases b <;> simp only [simpOr, Option.mem_def] at hg
      all_goals try contradiction
      rename_i j k
      by_cases hjk : j = k
      · simp [hjk] at hg
      · simp only [hjk, ite_false, Option.some.injEq] at hg
        subst hg
        exact Or.inr ⟨Or.inr rfl, j, k, hv (Sum.inr j) (by simp), hv (Sum.inr k) (by simp), hjk, rfl⟩
    · simp [simpOr] at hg
  · rcases ins with _ | ⟨a, l⟩
    · simp [simpNot] at hg
    · cases a <;> simp only [simpNot, Option.mem_def] at hg
      · contradiction
      · rename_i j
        cases hg
        exact Or.inl ⟨rfl, j, hv (Sum.inr j) (by simp), rfl⟩
  · simp at hg
  · simp at hg

theorem simplify_sound (op : GateOp)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List (Sum Bool ℕ)) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, statValid w.length s) :
    statValid (w.length + (simplify op w.length ins).1.toList.length) (simplify op w.length ins).2 ∧
    statVal (wiresFrom (simplify op w.length ins).1.toList w) (simplify op w.length ins).2
      = op.eval (ins.map (statVal w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a <;> cases b
      · simp [simplify, simpAnd, statValid, statVal, GateOp.eval]
      · rename_i c j; cases c <;> simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
      · rename_i j c; cases c <;> simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
      · rename_i j k
        by_cases hjk : j = k
        · subst hjk
          simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
        · simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a <;> cases b
      · simp [simplify, simpOr, statValid, statVal, GateOp.eval]
      · rename_i c j; cases c <;> simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
      · rename_i j c; cases c <;> simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
      · rename_i j k
        by_cases hjk : j = k
        · subst hjk
          simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
        · simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, statValid, statVal, GateOp.eval, wiresFrom]

def simpStep (n : ℕ) (acc : List (Sum Bool ℕ) × List Gate) (g : Gate) :
    List (Sum Bool ℕ) × List Gate :=
  let r := simplify g.op (n + acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Sum.inl false))
  (acc.1 ++ [r.2], acc.2 ++ r.1.toList)

def simpPass (n : ℕ) (gs : List Gate) (acc : List (Sum Bool ℕ) × List Gate) :
    List (Sum Bool ℕ) × List Gate :=
  gs.foldl (simpStep n) acc

theorem simpPass_len (n : ℕ) (gs : List Gate) : ∀ acc : List (Sum Bool ℕ) × List Gate,
    (simpPass n gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [simpPass]
  | cons g gs ih =>
    intro acc
    have h1 := ih (simpStep n acc g)
    have h2 : (simpStep n acc g).2.length ≤ acc.2.length + 1 := by
      simp only [simpStep, List.length_append]
      cases (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 <;> simp
    have h3 : simpPass n (g :: gs) acc = simpPass n gs (simpStep n acc g) := rfl
    rw [h3, List.length_cons]
    omega

def SimpInv (n : ℕ) (x : List Bool) (w : List Bool) (acc : List (Sum Bool ℕ) × List Gate) : Prop :=
  acc.1.length = w.length ∧
  SCleanL n acc.2 ∧
  ∀ i : ℕ,
    statValid (n + acc.2.length) (acc.1.getD i (Sum.inl false)) ∧
    statVal (wiresFrom acc.2 x) (acc.1.getD i (Sum.inl false)) = w.getD i false

theorem simpPass_inv (n : ℕ) (x : List Bool) (hx : x.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List (Sum Bool ℕ) × List Gate),
      (∀ g ∈ gs,
        (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2) →
      SimpInv n x w acc →
      SimpInv n x (wiresFrom gs w) (simpPass n gs acc) := by
  induction gs with
  | nil => intro w acc _ h; exact h
  | cons g gs ih =>
    intro w acc hok h
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (simpStep n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl, hcl, hi⟩ := h
    set w' := wiresFrom acc.2 x with hw'
    have lw' : w'.length = n + acc.2.length := by rw [hw', length_wiresFrom, hx]
    set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
    have hgok := hok g List.mem_cons_self
    have hvins : ∀ s ∈ ins, statValid (n + acc.2.length) s := by
      intro s hs
      obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
      exact (hi a).1
    have hs := simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
      (by rw [lw']; exact hvins)
    rw [lw'] at hs
    set r := simplify g.op (n + acc.2.length) ins with hr
    have hvals : ins.map (statVal w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) x = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht⟩ := wiresFrom_prefix r.1.toList w'
    have hcl' : SCleanL n (acc.2 ++ r.1.toList) := by
      intro p g' hpg'
      cases hr1 : r.1 with
      | none =>
        rw [hr1] at hpg'
        simp only [Option.toList_none, List.append_nil] at hpg'
        exact hcl p g' hpg'
      | some g0 =>
        rw [hr1] at hpg'
        simp only [Option.toList_some] at hpg'
        by_cases hp : p < acc.2.length
        · rw [List.getElem?_append_left hp] at hpg'
          exact hcl p g' hpg'
        · have hpe : p = acc.2.length := by
            have := (List.getElem?_eq_some_iff.1 hpg').1
            simp at this
            omega
          subst hpe
          rw [List.getElem?_append_right le_rfl] at hpg'
          simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at hpg'
          subst hpg'
          exact simplify_clean g.op (n + acc.2.length) ins hvins g0 (by simp [← hr, hr1])
    refine ⟨by simp [simpStep, hl], hcl', ?_⟩
    intro i
    show statValid (n + (acc.2 ++ r.1.toList).length) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) ∧
      statVal (wiresFrom (acc.2 ++ r.1.toList) x) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_len _ _ _ _ rfl, hl, getD_snoc_len _ _ _ _ rfl]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨statValid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, statVal_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2

theorem exists_sclean {n : ℕ} (f : BFn n) (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y') (s : ℕ)
    (h : HasCircuitSize n f s) :
    ∃ gs o, gs.length ≤ s ∧ SCleanL n gs ∧ o < n + gs.length ∧ ∀ x, val gs n o x = f x := by
  obtain ⟨C, hfan, hsz, hev⟩ := h
  have hok : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    obtain ⟨hop, hlen⟩ := hfan g hg
    refine ⟨?_, hlen⟩
    rcases hop with h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr h1)
  set init : List (Sum Bool ℕ) := List.ofFn fun i : Fin n => Sum.inr i.val
  set acc := simpPass n C.gates (init, [])
  have hinit : ∀ x : Fin n → Bool, SimpInv n (List.ofFn x) (List.ofFn x) (init, []) := by
    intro x
    refine ⟨by simp [init], by intro p g hg; simp at hg, ?_⟩
    intro i
    by_cases hi : i < n
    · simp [init, hi, statValid, statVal, wiresFrom]
    · rw [List.getD_eq_default _ _ (by simp [init]; omega),
          List.getD_eq_default _ _ (by simp; omega)]
      exact ⟨trivial, rfl⟩
  have hinv : ∀ x : Fin n → Bool,
      SimpInv n (List.ofFn x) (wiresFrom C.gates (List.ofFn x)) acc := fun x =>
    simpPass_inv n (List.ofFn x) (by simp) C.gates (List.ofFn x) (init, []) hok (hinit x)
  have hlen : acc.2.length ≤ s := by
    have := simpPass_len n C.gates (init, [])
    simp only [List.length_nil, zero_add] at this
    exact le_trans this hsz
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    have h1 := ((hinv y).2.2 C.output).2
    have h2 := ((hinv y').2.2 C.output).2
    rw [hst] at h1 h2
    have e1 : wiresFrom C.gates (List.ofFn y) = C.wires (List.ofFn y) := rfl
    have e2 : wiresFrom C.gates (List.ofFn y') = C.wires (List.ofFn y') := rfl
    rw [← hev y, ← hev y']
    show (C.wires (List.ofFn y)).getD C.output false = (C.wires (List.ofFn y')).getD C.output false
    rw [← e1, ← e2, ← h1, ← h2]
    rfl
  | inr o =>
    obtain ⟨y, _, _⟩ := hnc
    have ho : o < n + acc.2.length := by
      have hv := ((hinv y).2.2 C.output).1
      rw [hst] at hv
      exact hv
    refine ⟨acc.2, o, hlen, (hinv y).2.1, ho, ?_⟩
    intro x
    have hv := ((hinv x).2.2 C.output).2
    rw [hst] at hv
    have e1 : wiresFrom C.gates (List.ofFn x) = C.wires (List.ofFn x) := rfl
    rw [← hev x]
    show (wiresFrom acc.2 (List.ofFn x)).getD o false = (C.wires (List.ofFn x)).getD C.output false
    rw [← e1, ← hv]
    rfl

def redir (m a : ℕ) : ℕ := if m < a then a - 1 else a

theorem redir_lt {m b a : ℕ} (hm : m ≤ b) (ha : a < b + 1) (hne : a ≠ m) : redir m a < b := by
  unfold redir
  split <;> omega

theorem redir_inj {m a b : ℕ} (ha : a ≠ m) (hb : b ≠ m) (heq : redir m a = redir m b) :
    a = b := by
  unfold redir at heq
  split at heq <;> split at heq <;> omega

theorem getD_drop_wire (w₁ u : List Bool) (b : Bool) (a : ℕ) (hne : a ≠ w₁.length) :
    (w₁ ++ u).getD (redir w₁.length a) false = (w₁ ++ [b] ++ u).getD a false := by
  unfold redir
  by_cases hlt : w₁.length < a
  · simp only [hlt, ite_true]
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega)]
    have hlen : (w₁ ++ [b]).length = w₁.length + 1 := by simp
    rw [List.getElem?_append_right (by omega), hlen]
    congr 2
    omega
  · simp only [hlt, ite_false]
    have ha : a < w₁.length := by omega
    rw [List.getD_append _ _ _ _ ha]
    rw [List.append_assoc, List.getD_append _ _ _ _ ha]

theorem wiresFrom_drop_dead (w₁ : List Bool) (b : Bool) (post : List Gate) :
    ∀ u : List Bool,
      (∀ g ∈ post, w₁.length ∉ g.inputs) →
      ∃ u',
        wiresFrom (post.map fun g => ⟨g.op, g.inputs.map (redir w₁.length)⟩) (w₁ ++ u) = w₁ ++ u' ∧
        wiresFrom post (w₁ ++ [b] ++ u) = w₁ ++ [b] ++ u' := by
  induction post with
  | nil => intro u _; exact ⟨u, rfl, rfl⟩
  | cons g gs ih =>
    intro u hdead
    have hg : w₁.length ∉ g.inputs := hdead g List.mem_cons_self
    have hmap : (g.inputs.map (redir w₁.length)).map (fun i => (w₁ ++ u).getD i false)
        = g.inputs.map (fun i => (w₁ ++ [b] ++ u).getD i false) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro a ha
      exact getD_drop_wire w₁ u b a (fun e => hg (e ▸ ha))
    set c := g.op.eval (g.inputs.map fun i => (w₁ ++ [b] ++ u).getD i false)
    obtain ⟨u', h1, h2⟩ := ih (u ++ [c]) (fun g' hg' => hdead g' (List.mem_cons_of_mem _ hg'))
    refine ⟨u', ?_, ?_⟩
    · simp only [List.map_cons, wiresFrom_cons, hmap]
      rw [List.append_assoc]
      exact h1
    · rw [wiresFrom_cons, List.append_assoc, List.append_assoc]
      rw [← List.append_assoc w₁ [b] (u ++ [c])]
      exact h2

theorem erase_dead (n : ℕ) (gs : List Gate) (o p : ℕ) (hcl : SCleanL n gs)
    (ho : o < n + gs.length) (hp : p < gs.length) (hne : n + p ≠ o)
    (hdead : ∀ (q : ℕ) (g : Gate), gs[q]? = some g → n + p ∉ g.inputs) :
    ∃ gs' o', gs'.length + 1 = gs.length ∧ SCleanL n gs' ∧ o' < n + gs'.length ∧
      ∀ x, val gs' n o' x = val gs n o x := by
  let gs' := gs.take p ++ (gs.drop (p + 1)).map fun g => ⟨g.op, g.inputs.map (redir (n + p))⟩
  let o' := redir (n + p) o
  have hlen' : gs'.length + 1 = gs.length := by
    simp [gs']
    omega
  have ho' : o' < n + gs'.length := redir_lt (by omega) (by omega) (Ne.symm hne)
  have hcl' : SCleanL n gs' := by
    intro q g hqg
    by_cases hqp : q < p
    · have h1 : gs'[q]? = gs[q]? := by
        simp only [gs']
        rw [List.getElem?_append_left (by simp; omega)]
        exact List.getElem?_take_of_lt hqp
      rw [h1] at hqg
      exact hcl q g hqg
    · have hlt' : q < gs'.length := (List.getElem?_eq_some_iff.1 hqg).1
      have hq1 : q + 1 < gs.length := by omega
      have h1 : gs'[q]? = ((gs.drop (p + 1)).map fun g => ⟨g.op, g.inputs.map (redir (n + p))⟩)[q - p]? := by
        simp only [gs']
        rw [List.getElem?_append_right (by simp; omega)]
        simp [Nat.min_eq_left (Nat.le_of_lt hp)]
      rw [h1, List.getElem?_map, List.getElem?_drop] at hqg
      have hidx : p + 1 + (q - p) = q + 1 := by omega
      rw [hidx] at hqg
      obtain ⟨g0, hg0, rfl⟩ := Option.map_eq_some_iff.1 hqg
      have hcl0 := hcl (q + 1) g0 hg0
      have hd0 := hdead (q + 1) g0 hg0
      rcases hcl0 with ⟨hop, j, hj, hin⟩ | ⟨hop, j, k, hj, hk, hjk, hin⟩
      · refine Or.inl ⟨hop, redir (n + p) j, ?_, by simp [hin]⟩
        exact redir_lt (by omega) (by omega) (fun e => hd0 (by rw [hin]; simp [e]))
      · refine Or.inr ⟨hop, redir (n + p) j, redir (n + p) k, ?_, ?_, ?_, by simp [hin]⟩
        · exact redir_lt (by omega) (by omega) (fun e => hd0 (by rw [hin]; simp [e]))
        · exact redir_lt (by omega) (by omega) (fun e => hd0 (by rw [hin]; simp [e]))
        · intro heq
          exact hjk (redir_inj (fun e => hd0 (by rw [hin]; simp [e]))
            (fun e => hd0 (by rw [hin]; simp [e])) heq)
  refine ⟨gs', o', hlen', hcl', ho', ?_⟩
  intro x
  unfold val
  have hsplit : gs = gs.take p ++ gs[p] :: gs.drop (p + 1) := by
    calc gs = gs.take p ++ gs.drop p := (List.take_append_drop p gs).symm
      _ = gs.take p ++ gs[p] :: gs.drop (p + 1) := by rw [List.drop_eq_getElem_cons hp]
  set w₁ := wiresFrom (gs.take p) (List.ofFn x)
  have lw₁ : w₁.length = n + p := by
    rw [length_wiresFrom]
    simp [Nat.min_eq_left (Nat.le_of_lt hp)]
  have hdead_post : ∀ g ∈ gs.drop (p + 1), w₁.length ∉ g.inputs := by
    intro g hg
    obtain ⟨k, hk, hgk⟩ := List.getElem_of_mem hg
    rw [List.getElem_drop] at hgk
    rw [lw₁]
    have hlt_k : p + 1 + k < gs.length := by simp at hk; omega
    exact hdead (p + 1 + k) g (by rw [List.getElem?_eq_getElem hlt_k, hgk])
  set b := gs[p].op.eval (gs[p].inputs.map fun i => w₁.getD i false)
  obtain ⟨u', hu1, hu2⟩ := wiresFrom_drop_dead w₁ b (gs.drop (p + 1)) [] hdead_post
  have heq1 : wiresFrom gs' (List.ofFn x) = w₁ ++ u' := by
    simp only [gs', wiresFrom_append]
    rw [← lw₁]
    simpa [w₁] using hu1
  have heq2 : wiresFrom gs (List.ofFn x) = w₁ ++ [b] ++ u' := by
    conv_lhs => rw [hsplit]
    rw [wiresFrom_append, wiresFrom_cons]
    simpa [w₁, b] using hu2
  rw [heq1, heq2]
  show (w₁ ++ u').getD (redir (n + p) o) false = (w₁ ++ [b] ++ u').getD o false
  rw [← lw₁]
  exact getD_drop_wire w₁ u' b o (by rw [lw₁]; exact Ne.symm hne)

def Live (gs : List Gate) (o p a : ℕ) : Prop :=
  a = o ∨ ∃ q, p ≤ q ∧ ∃ g, gs[q]? = some g ∧ a ∈ g.inputs

open Classical in
noncomputable def liveList (gs : List Gate) (n o p : ℕ) : List ℕ :=
  (List.range (n + p)).filter (fun a => decide (Live gs o p a))

theorem mem_liveList (gs : List Gate) (n o p a : ℕ) :
    a ∈ liveList gs n o p ↔ a < n + p ∧ Live gs o p a := by
  simp [liveList]

theorem nodup_liveList (gs : List Gate) (n o p : ℕ) : (liveList gs n o p).Nodup :=
  List.Nodup.filter _ List.nodup_range

abbrev invF {n : ℕ} : BFn n → BFn n := fun a x => !a x
abbrev meetF {n : ℕ} : BFn n → BFn n → BFn n := fun a b x => a x && b x
abbrev joinF {n : ℕ} : BFn n → BFn n → BFn n := fun a b x => a x || b x

theorem live_succ (n : ℕ) (gs : List Gate) (o : ℕ) (hcl : SCleanL n gs)
    (hnd : ∀ p, p < gs.length → n + p = o ∨ ∃ (q : ℕ) (g : Gate), gs[q]? = some g ∧ n + p ∈ g.inputs)
    (p : ℕ) (g : Gate) (hg : gs[p]? = some g) (a : ℕ) :
    a ∈ liveList gs n o (p + 1) ↔
      a = n + p ∨ (a ∈ liveList gs n o p ∧ (a ∈ g.inputs → Live gs o (p + 1) a)) := by
  have hplt : p < gs.length := (List.getElem?_eq_some_iff.1 hg).1
  rw [mem_liveList, mem_liveList]
  constructor
  · rintro ⟨hlt, hl⟩
    by_cases ha : a = n + p
    · exact Or.inl ha
    · refine Or.inr ⟨⟨by omega, ?_⟩, fun _ => hl⟩
      rcases hl with h | ⟨q, hq, g', hg', hin⟩
      · exact Or.inl h
      · exact Or.inr ⟨q, by omega, g', hg', hin⟩
  · rintro (rfl | ⟨⟨hlt, hl⟩, himp⟩)
    · refine ⟨by omega, ?_⟩
      rcases hnd p hplt with h | ⟨q, g', hg', hin⟩
      · exact Or.inl h
      · refine Or.inr ⟨q, ?_, g', hg', hin⟩
        have := (hcl q g' hg').lt _ hin
        omega
    · refine ⟨by omega, ?_⟩
      rcases hl with h | ⟨q, hq, g', hg', hin⟩
      · exact Or.inl h
      · by_cases hqp : q = p
        · subst hqp
          rw [hg] at hg'
          cases hg'
          exact himp hin
        · exact Or.inr ⟨q, by omega, g', hg', hin⟩

open Classical in
theorem run_live (n : ℕ) (gs : List Gate) (o : ℕ) (hcl : SCleanL n gs) (ho : o < n + gs.length)
    (hnd : ∀ p, p < gs.length → n + p = o ∨ ∃ (q : ℕ) (g : Gate), gs[q]? = some g ∧ n + p ∈ g.inputs) :
    ∀ d p, p + d = gs.length →
      Run (invF (n := n)) meetF joinF (val gs n o) d ((liveList gs n o p).map (val gs n)) := by
  intro d
  induction d with
  | zero =>
    intro p hp
    have hperm : [o].Perm (liveList gs n o p) := by
      refine (List.perm_ext_iff_of_nodup (List.nodup_singleton o) (nodup_liveList _ _ _ _)).2 ?_
      intro a
      rw [mem_liveList, List.mem_singleton]
      constructor
      · rintro rfl; exact ⟨by omega, Or.inl rfl⟩
      · rintro ⟨_, h | ⟨q, hq, g', hg', _⟩⟩
        · exact h
        · have := (List.getElem?_eq_some_iff.1 hg').1
          omega
    exact Run.perm (hperm.map (val gs n)) Run.done
  | succ d ih =>
    intro p hp
    have hplt : p < gs.length := by omega
    obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hplt⟩
    have IH := ih (p + 1) (by omega)
    have hstep := live_succ n gs o hcl hnd p g hg
    have hin : ∀ a ∈ g.inputs, a ∈ liveList gs n o p := fun a ha =>
      (mem_liveList _ _ _ _ _).2 ⟨(hcl p g hg).lt a ha, Or.inr ⟨p, le_rfl, g, hg, ha⟩⟩
    have hnew : ∀ a ∈ liveList gs n o p, a ≠ n + p := fun a ha =>
      Nat.ne_of_lt ((mem_liveList _ _ _ _ _).1 ha).1
    have hvg := val_gate n gs p g hg (hcl p g hg).lt
    have hnd0 := nodup_liveList gs n o p
    rcases hcl p g hg with ⟨hop, j, hj, hinp⟩ | ⟨hop, j, k, hj, hk, hjk, hinp⟩
    · have hjm := hin j (by simp [hinp])
      have hp1 : (liveList gs n o p).Perm (j :: (liveList gs n o p).erase j) :=
        List.perm_cons_erase hjm
      have hnr : ((liveList gs n o p).erase j).Nodup := hnd0.erase j
      have hp2 : (liveList gs n o (p + 1)).Perm
          ((n + p) :: kept (decide (Live gs o (p + 1) j)) j ((liveList gs n o p).erase j)) := by
        refine (List.perm_ext_iff_of_nodup (nodup_liveList _ _ _ _) ?_).2 ?_
        · refine List.nodup_cons.2 ⟨?_, nodup_kept _ _ _ hnr (by simp [hnd0.mem_erase_iff])⟩
          rw [mem_kept]
          rintro (⟨_, h⟩ | h)
          · exact hnew j hjm h.symm
          · exact hnew _ (List.mem_of_mem_erase h) rfl
        · intro a
          rw [hstep a, List.mem_cons, mem_kept, hnd0.mem_erase_iff]
          simp only [decide_eq_true_eq, hinp, List.mem_cons, List.not_mem_nil, or_false]
          constructor
          · rintro (h | ⟨h1, h2⟩)
            · exact Or.inl h
            · by_cases haj : a = j
              · exact Or.inr (Or.inl ⟨haj ▸ h2 haj, haj⟩)
              · exact Or.inr (Or.inr ⟨haj, h1⟩)
          · rintro (h | ⟨h1, rfl⟩ | ⟨h1, h2⟩)
            · exact Or.inl h
            · exact Or.inr ⟨hjm, fun _ => h1⟩
            · exact Or.inr ⟨h2, fun h => absurd h h1⟩
      have hval : val gs n (n + p) = invF (val gs n j) := by
        funext x
        rw [hvg x, hop, hinp]
        simp [GateOp.eval, invF]
      have IH' := Run.perm (hp2.map (val gs n)) IH
      rw [List.map_cons, kept_map, hval] at IH'
      exact Run.perm (hp1.map (val gs n)).symm (Run.one _ IH')
    · have hjm := hin j (by simp [hinp])
      have hkm := hin k (by simp [hinp])
      have hke : k ∈ (liveList gs n o p).erase j :=
        (hnd0.mem_erase_iff).2 ⟨fun e => hjk e.symm, hkm⟩
      have hnr : ((liveList gs n o p).erase j).Nodup := hnd0.erase j
      have hnr2 : (((liveList gs n o p).erase j).erase k).Nodup := hnr.erase k
      have hp1 : (liveList gs n o p).Perm
          (j :: k :: ((liveList gs n o p).erase j).erase k) :=
        (List.perm_cons_erase hjm).trans ((List.perm_cons_erase hke).cons j)
      have hmr : ∀ a, a ∈ ((liveList gs n o p).erase j).erase k ↔
          a ≠ k ∧ a ≠ j ∧ a ∈ liveList gs n o p := by
        intro a
        rw [hnr.mem_erase_iff, hnd0.mem_erase_iff]
      have hp2 : (liveList gs n o (p + 1)).Perm
          ((n + p) :: kept (decide (Live gs o (p + 1) j)) j
            (kept (decide (Live gs o (p + 1) k)) k
              (((liveList gs n o p).erase j).erase k))) := by
        refine (List.perm_ext_iff_of_nodup (nodup_liveList _ _ _ _) ?_).2 ?_
        · refine List.nodup_cons.2 ⟨?_, nodup_kept _ _ _ (nodup_kept _ _ _ hnr2 ?_) ?_⟩
          · rw [mem_kept, mem_kept]
            rintro (⟨_, h⟩ | ⟨_, h⟩ | h)
            · exact hnew j hjm h.symm
            · exact hnew k hkm h.symm
            · exact hnew _ ((hmr _).1 h).2.2 rfl
          · rw [hmr]; simp
          · rw [mem_kept, hmr]
            rintro (⟨_, h⟩ | h)
            · exact hjk h
            · exact h.2.1 rfl
        · intro a
          rw [hstep a, List.mem_cons, mem_kept, mem_kept, hmr a]
          simp only [decide_eq_true_eq, hinp, List.mem_cons, List.not_mem_nil, or_false]
          constructor
          · rintro (h | ⟨h1, h2⟩)
            · exact Or.inl h
            · by_cases haj : a = j
              · exact Or.inr (Or.inl ⟨haj ▸ h2 (Or.inl haj), haj⟩)
              · by_cases hak : a = k
                · exact Or.inr (Or.inr (Or.inl ⟨hak ▸ h2 (Or.inr hak), hak⟩))
                · exact Or.inr (Or.inr (Or.inr ⟨hak, haj, h1⟩))
          · rintro (h | ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, h2, h3⟩)
            · exact Or.inl h
            · exact Or.inr ⟨hjm, fun _ => h1⟩
            · exact Or.inr ⟨hkm, fun _ => h1⟩
            · exact Or.inr ⟨h3, fun h => by rcases h with h | h <;> contradiction⟩
      have IH' := Run.perm (hp2.map (val gs n)) IH
      have hval : val gs n (n + p) = (if decide (g.op = GateOp.and)
          then meetF (val gs n j) (val gs n k) else joinF (val gs n j) (val gs n k)) := by
        funext x
        rw [hvg x, hinp]
        rcases hop with hop | hop <;> rw [hop] <;> simp [GateOp.eval, meetF, joinF]
      rw [List.map_cons, kept_map, kept_map, hval] at IH'
      exact Run.perm (hp1.map (val gs n)).symm (Run.two _ _ _ IH')

open Classical in
theorem exists_run {n : ℕ} (f : BFn n) (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y') (s : ℕ)
    (h : HasCircuitSize n f s) :
    ∃ s', s' ≤ s ∧ ∃ ws : List (BFn n),
      ws.Sublist (List.ofFn fun (i : Fin n) => (fun x : Fin n → Bool => x i)) ∧
      Run (invF (n := n)) meetF joinF f s' ws := by
  have hex : ∃ m, ∃ gs o, gs.length = m ∧ SCleanL n gs ∧ o < n + gs.length ∧ ∀ x, val gs n o x = f x := by
    obtain ⟨gs, o, hl, hcl, ho, hev⟩ := exists_sclean f hnc s h
    exact ⟨gs.length, gs, o, rfl, hcl, ho, hev⟩
  set m := Nat.find hex
  have hm_le : m ≤ s := by
    obtain ⟨gs, o, hl, hcl, ho, hev⟩ := exists_sclean f hnc s h
    exact le_trans (Nat.find_min' hex ⟨gs, o, rfl, hcl, ho, hev⟩) hl
  obtain ⟨gs, o, hlen, hcl, ho, hev⟩ := Nat.find_spec hex
  have hnd : ∀ p, p < gs.length → n + p = o ∨
      ∃ (q : ℕ) (g : Gate), gs[q]? = some g ∧ n + p ∈ g.inputs := by
    intro p hp
    by_contra! hbad
    obtain ⟨hne, hdead⟩ := hbad
    obtain ⟨gs', o', hlen', hcl', ho', hev'⟩ := erase_dead n gs o p hcl ho hp hne hdead
    have hlt : gs'.length < m := by omega
    exact Nat.find_min hex hlt ⟨gs', o', rfl, hcl', ho', fun x => (hev' x).trans (hev x)⟩
  refine ⟨gs.length, by omega, (liveList gs n o 0).map (val gs n), ?_, ?_⟩
  · have e : (List.ofFn fun (i : Fin n) => (fun x : Fin n → Bool => x i))
        = (List.range n).map (val gs n) := by
      apply List.ext_getElem
      · simp
      · intro i h1 h2
        simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range]
        exact (val_input gs n ⟨i, by simpa using h1⟩).symm
    rw [e]
    exact (List.filter_sublist).map _
  · have hf : val gs n o = f := funext hev
    rw [← hf]
    exact run_live n gs o hcl ho hnd gs.length 0 (by omega)

abbrev fG : BFn 8 := fun x : Fin 8 → Bool =>
  (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 0 && x 6) || (x 1 && x 6) || (x 3 && x 6) || (x 4 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 2 && x 7) || (x 3 && x 7) || (x 4 && x 7)

theorem run_len {α inv meet join y s xs} (h : @Run α inv meet join y s xs) :
    xs.length ≤ s + 1 := by
  induction h using Run.fold with
  | done => simp
  | perm hp _ ih => rwa [← hp.length_eq]
  | one save h ih => cases save <;> simp_all [kept] <;> omega
  | two conj ka kb h ih => cases ka <;> cases kb <;> simp_all [kept] <;> omega

abbrev NatRun (m : Nat) := Run (· ^^^ m) (· &&& ·) (· ||| ·)

theorem run_bits {m y s xs} (h : NatRun m y s xs) (i j : Nat)
    (hm : m.testBit i = m.testBit j)
    (hw : ∀ w ∈ xs, w.testBit i = w.testBit j) : y.testBit i = y.testBit j := by
  induction h using Run.fold with
  | done => exact hw _ (by simp)
  | perm hp _ ih => exact ih (fun w h => hw w (hp.mem_iff.1 h))
  | one save h ih =>
    apply ih
    have ha := hw _ List.mem_cons_self
    intro w hmem
    cases save <;> simp only [Bool.false_eq_true, ite_false, ite_true, kept, List.mem_cons] at hmem
    · rcases hmem with rfl | hr
      · simp [ha, hm]
      · exact hw _ (by simp [hr])
    · rcases hmem with rfl | rfl | hr
      · simp [ha, hm]
      · exact ha
      · exact hw _ (by simp [hr])
  | two conj ka kb h ih =>
    apply ih
    have ha := hw _ List.mem_cons_self
    have hb := hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro w hmem
    cases conj <;> cases ka <;> cases kb <;> simp only [Bool.false_eq_true,
      ite_false, ite_true, kept, List.mem_cons] at hmem <;>
      rcases hmem with rfl | hr <;> first | simp [ha, hb] | exact hw _ (by simp only [List.mem_cons]; tauto)

def diff (k w : Nat) : Nat := w ^^^ (w >>> k)

def cov (k : Nat) : List Nat → Nat
  | [] => 0
  | a :: t => diff k a ||| cov k t

theorem cov_bit (k i : Nat) (ws : List Nat) : (cov k ws).testBit i = true ↔
    ∃ a ∈ ws, a.testBit i ≠ a.testBit (k + i) := by
  induction ws with
  | nil => simp [cov]
  | cons a t ih =>
    simp only [cov, Nat.testBit_or, Bool.or_eq_true, ih, diff, Nat.testBit_xor,
      Nat.testBit_shiftRight, List.mem_cons]
    cases hx : a.testBit i <;> cases hy : a.testBit (k + i) <;> simp_all

def lo (k : Nat) := 2 ^ k - 1
def mask (k : Nat) := lo (k + k)
def goal (k : Nat) := lo k <<< k

theorem required {k s ws} (h : NatRun (mask k) (goal k) s ws) :
    (cov k ws &&& lo k) = lo k := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  by_cases hi : i < k
  · have hm : (mask k).testBit i = (mask k).testBit (k + i) := by
      simp [mask, lo, Nat.testBit_two_pow_sub_one, show i < k + k by omega, show k + i < k + k by omega]
    have hy : (goal k).testBit i ≠ (goal k).testBit (k + i) := by
      simp [goal, lo, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one, hi, show ¬ k ≤ i by omega]
    have hc : (cov k ws).testBit i = true := by
      apply (cov_bit k i ws).2
      by_contra! hh
      exact hy (run_bits h i (k + i) hm hh)
    simp [hc]
  · simp [lo, Nat.testBit_two_pow_sub_one, hi]

theorem keep_perm {α : Type} {xs ys : List α} (p : xs.Perm ys) (b : Bool) (a : α) :
    (kept b a xs).Perm (kept b a ys) := by cases b <;> simpa [kept] using p

def next (m : Nat) (slack : Nat) (ws : List Nat) (f : List Nat → Bool) : Bool :=
  ws.any fun a =>
    let ra := ws.erase a
    (slack ≥ 1 &&
      (let w := a ^^^ m
       f (w :: ra) || (slack ≥ 2 && f (w :: a :: ra)))) ||
    ra.any fun b =>
      a ≤ b && (let r := ra.erase b
        [false, true].any fun conj =>
          let w := if conj then a &&& b else a ||| b
          f (w :: r) || (slack ≥ 1 && (f (w :: a :: r) || f (w :: b :: r))) ||
            (slack ≥ 2 && f (w :: a :: b :: r)))

theorem next_one {k a rest} {save : Bool} {s ws} (p : (a :: rest).Perm ws)
    (h : NatRun (mask k) (goal k) s ((a ^^^ mask k) :: kept save a rest))
    (f : List Nat → Bool)
    (hf : ∀ ys, NatRun (mask k) (goal k) s ys → f ys = true) :
    next (mask k) (s + 2 - ws.length) ws f = true := by
  have ha := p.mem_iff.1 List.mem_cons_self
  have pr : rest.Perm (ws.erase a) := (p.trans (List.perm_cons_erase ha)).cons_inv
  have hh := run_len h
  have hl := p.length_eq
  simp only [List.length_cons] at hl hh
  have hsl : 1 ≤ s + 2 - ws.length := by cases save <;> simp [kept] at hh <;> omega
  apply List.any_eq_true.2 ⟨a, ha, ?_⟩
  rw [Bool.or_eq_true]; left
  rw [Bool.and_eq_true]; refine ⟨decide_eq_true hsl, ?_⟩
  have ht := hf _ (Run.perm ((keep_perm pr save a).cons _) h)
  cases save with
  | false => simp [kept] at ht; simp [ht]
  | true =>
    simp [kept] at ht hh
    have hsl2 : 2 ≤ s + 2 - ws.length := by omega
    simp [ht, hsl2]

theorem next_two_sorted {k a b rest} {conj ka kb : Bool} {s ws} (hab : a ≤ b)
    (p : (a :: b :: rest).Perm ws)
    (h : NatRun (mask k) (goal k) s
      ((if conj then a &&& b else a ||| b) :: kept ka a (kept kb b rest)))
    (f : List Nat → Bool)
    (hf : ∀ ys, NatRun (mask k) (goal k) s ys → f ys = true) :
    next (mask k) (s + 2 - ws.length) ws f = true := by
  have ha := p.mem_iff.1 List.mem_cons_self
  have pp := (p.trans (List.perm_cons_erase ha)).cons_inv
  have hb := pp.mem_iff.1 List.mem_cons_self
  have pr := (pp.trans (List.perm_cons_erase hb)).cons_inv
  have hh := run_len h
  have hl := p.length_eq
  simp only [List.length_cons] at hl hh
  apply List.any_eq_true.2 ⟨a, ha, ?_⟩
  rw [Bool.or_eq_true]; right
  apply List.any_eq_true.2 ⟨b, hb, ?_⟩
  rw [Bool.and_eq_true]; refine ⟨decide_eq_true hab, ?_⟩
  apply List.any_eq_true.2 ⟨conj, by cases conj <;> simp, ?_⟩
  have ht := hf _ (Run.perm ((keep_perm (keep_perm pr kb b) ka a).cons _) h)
  cases ka <;> cases kb <;> simp [kept] at ht hh <;>
    simp only [ht, Bool.true_or, Bool.or_true, Bool.and_true] <;>
    first | (simp [show 2 ≤ s + 2 - ws.length by omega]) | (simp [show 1 ≤ s + 2 - ws.length by omega])

theorem next_two {k a b rest} {conj ka kb : Bool} {s ws}
    (p : (a :: b :: rest).Perm ws)
    (h : NatRun (mask k) (goal k) s
      ((if conj then a &&& b else a ||| b) :: kept ka a (kept kb b rest)))
    (f : List Nat → Bool)
    (hf : ∀ ys, NatRun (mask k) (goal k) s ys → f ys = true) :
    next (mask k) (s + 2 - ws.length) ws f = true := by
  rcases le_total a b with hab | hba
  · exact next_two_sorted hab p h f hf
  · apply next_two_sorted (conj := conj) (ka := kb) (kb := ka) hba ((List.Perm.swap _ _ _).trans p) _ f hf
    have he : (if conj then a &&& b else a ||| b) = (if conj then b &&& a else b ||| a) := by
      cases conj <;> simp [Nat.and_comm, Nat.or_comm]
    rw [he] at h
    apply Run.perm (List.Perm.cons _ ?_) h
    cases ka <;> cases kb <;> simp [kept]
    exact List.Perm.swap _ _ _

theorem zero_done {α inv meet join y t ws} (h : @Run α inv meet join y t ws) :
    t = 0 → ws = [y] := by
  induction h using Run.fold with
  | done => simp
  | perm p h ih => intro ht; rw [ih ht] at p; exact List.perm_singleton.1 p.symm
  | one => simp
  | two => simp

theorem next_complete {k t ws} (h : NatRun (mask k) (goal k) t ws) :
    ∀ s, t = s + 1 → ∀ zs, ws.Perm zs → ∀ f : List Nat → Bool,
      (∀ ys, NatRun (mask k) (goal k) s ys → f ys = true) →
      next (mask k) (s + 2 - zs.length) zs f = true := by
  induction h using Run.fold with
  | done => simp
  | perm p h ih => intro s he zs q; exact ih s he zs (p.trans q)
  | one save h ih => intro s he zs p f hf; cases he; exact next_one p h f hf
  | two conj ka kb h ih => intro s he zs p f hf; cases he; exact next_two p h f hf

def pt (n : ℕ) (v : ℕ) : Fin n → Bool := fun i => v.testBit i

def encL {n : ℕ} (a : BFn n) : List ℕ → ℕ
  | [] => 0
  | v :: t => Nat.bit (a (pt n v)) (encL a t)

theorem encL_testBit {n : ℕ} (a : BFn n) : ∀ (l : List ℕ) (j : ℕ),
    (encL a l).testBit j = (l.map fun v => a (pt n v)).getD j false
  | [], j => by simp [encL]
  | v :: t, 0 => by simp [encL]
  | v :: t, j + 1 => by simp [encL, Nat.testBit_bit_succ, encL_testBit a t j]

theorem encL_inv {n : ℕ} (a : BFn n) (l : List ℕ) :
    encL (invF a) l = encL a l ^^^ (2 ^ l.length - 1) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_xor, Nat.testBit_two_pow_sub_one, encL_testBit, encL_testBit]
  by_cases h : j < l.length
  · simp [h]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    simp [h]

theorem encL_and {n : ℕ} (a b : BFn n) (l : List ℕ) :
    encL (meetF a b) l = encL a l &&& encL b l := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and, encL_testBit, encL_testBit, encL_testBit]
  by_cases h : j < l.length
  · simp [h]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    rfl

theorem encL_or {n : ℕ} (a b : BFn n) (l : List ℕ) :
    encL (joinF a b) l = encL a l ||| encL b l := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_or, encL_testBit, encL_testBit, encL_testBit]
  by_cases h : j < l.length
  · simp [h]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    rfl

def moveBits (tag d w : Nat) : Nat :=
  ((w &&& tag) <<< d) ||| ((w >>> d) &&& tag)

theorem moved (tag d i w : Nat) (h : (tag &&& (tag <<< d)) = 0) :
    (moveBits tag d w).testBit i =
      (if tag.testBit i then w.testBit (d + i)
       else if (tag <<< d).testBit i then w.testBit (i - d) else false) := by
  have ht := congrArg (fun v : Nat => v.testBit i) h
  simp only [Nat.testBit_and, Nat.zero_testBit] at ht
  simp only [moveBits, Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_and, Nat.testBit_shiftRight] at *
  by_cases hi : d ≤ i <;> simp [hi] at * <;> grind

theorem move_hom (tag d : Nat) (h : (tag &&& (tag <<< d)) = 0) (a b : Nat) :
    moveBits tag d (a &&& b) = (moveBits tag d a &&& moveBits tag d b) ∧
    moveBits tag d (a ||| b) = (moveBits tag d a ||| moveBits tag d b) ∧
    moveBits tag d (a ^^^ b) = (moveBits tag d a ^^^ moveBits tag d b) := by
  refine ⟨?_, ?_, ?_⟩ <;> apply Nat.eq_of_testBit_eq <;> intro i <;>
    simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor, moved tag d i _ h] <;>
    split_ifs <;> simp

theorem move_run {k s ws} (h : NatRun (mask k) (goal k) s ws) (tag d : Nat)
    (hz : (tag &&& (tag <<< d)) = 0) (hm : moveBits tag d (mask k) = mask k)
    (hy : moveBits tag d (goal k) = goal k) :
    NatRun (mask k) (goal k) s (ws.map (moveBits tag d)) := by
  rw [← hy]
  exact Run.map _ (fun a => (move_hom tag d hz a (mask k)).2.2.trans (by rw [hm]))
    (fun a b => (move_hom tag d hz a b).1) (fun a b => (move_hom tag d hz a b).2.1) h

theorem bits_le {m y s ws} (h : NatRun m y s ws) (hl : ws.length = s + 1) (i j : Nat)
    (hw : ∀ a ∈ ws, a.testBit i ≤ a.testBit j) : y.testBit i ≤ y.testBit j := by
  induction h using Run.fold with
  | done => exact hw _ (by simp)
  | perm hp _ ih =>
    exact ih (hp.length_eq.trans hl) (fun a ha => hw a (hp.mem_iff.1 ha))
  | one save h ih =>
    have hh := run_len h
    cases save <;> simp [kept] at hh hl <;> omega
  | two conj ka kb h ih =>
    have hh := run_len h
    cases ka <;> cases kb <;> simp [kept] at hh hl <;> try omega
    apply ih (by simp [kept]; omega)
    have ha := hw _ List.mem_cons_self
    have hb := hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro a had
    simp only [kept, Bool.false_eq_true, ite_false, List.mem_cons] at had
    rcases had with rfl | ht
    · cases conj <;> simp only [ite_true, Bool.false_eq_true, ite_false, Nat.testBit_or, Nat.testBit_and] <;>
        grind
    · exact hw _ (by simp [ht])

def diffUp (k w : Nat) : Nat := (w >>> k) &&& (w ^^^ lo k)

def covUp (k : Nat) : List Nat → Nat
  | [] => 0
  | a :: t => diffUp k a ||| covUp k t

theorem covUp_bit (k i : Nat) (hi : i < k) (ws : List Nat) : (covUp k ws).testBit i = true ↔
    ∃ a ∈ ws, a.testBit i = false ∧ a.testBit (k + i) = true := by
  induction ws with
  | nil => simp [covUp]
  | cons a t ih =>
    simp [covUp, diffUp, lo, hi, ih, and_comm]

theorem required_up {k s ws} (h : NatRun (mask k) (goal k) s ws) (hl : ws.length = s + 1) :
    (covUp k ws &&& lo k) = lo k := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  by_cases hi : i < k
  · have hy : ¬ (goal k).testBit (k + i) ≤ (goal k).testBit i := by
      simp [goal, lo, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one, hi, show ¬ k ≤ i by omega]
    have hc : (covUp k ws).testBit i = true := by
      apply (covUp_bit k i hi ws).2
      by_contra! hh
      apply hy
      apply bits_le h hl
      intro a ha
      specialize hh a ha
      cases hx : a.testBit i <;> cases hy : a.testBit (k + i) <;> simp_all
    simp [hc]
  · simp [lo, Nat.testBit_two_pow_sub_one, hi]

def covers (k s : Nat) (ws : List Nat) : Bool :=
  if ws.length == s + 1 then covUp k ws &&& lo k == lo k else cov k ws &&& lo k == lo k

theorem covers_ok {k s ws} (h : NatRun (mask k) (goal k) s ws) : covers k s ws = true := by
  by_cases he : ws.length = s + 1
  · simp [covers, he, required_up h he]
  · simp [covers, he, required h]

def value6 (a b c d e f : Bool) : Nat :=
  let x := b.toNat + c.toNat
  let y := (!e).toNat + (!f).toNat
  if a then (if d then y else max x (max y (x + y - 1))) else (if d then 0 else x)

theorem value6_and : ∀ a b c d e f g h i j l m : Bool,
    value6 (a && g) (b && h) (c && i) (d && j) (e && l) (f && m)
      ≤ value6 a b c d e f + value6 g h i j l m := by decide +kernel

theorem value6_or : ∀ a b c d e f g h i j l m : Bool,
    value6 (a || g) (b || h) (c || i) (d || j) (e || l) (f || m)
      ≤ value6 a b c d e f + value6 g h i j l m := by decide +kernel

theorem score_bound {m y s ws} (h : NatRun m y s ws) (hl : ws.length = s + 1)
    (v : Nat → Nat) (hand : ∀ a b, v (a &&& b) ≤ v a + v b)
    (hor : ∀ a b, v (a ||| b) ≤ v a + v b) :
    v y ≤ (ws.map v).sum := by
  induction h using Run.fold with
  | done => simp
  | perm p h ih =>
    rw [← (p.map v).sum_eq]
    exact ih (p.length_eq.trans hl)
  | one save h ih =>
    have hh := run_len h
    cases save <;> simp [kept] at hh hl <;> omega
  | two conj ka kb h ih =>
    have hh := run_len h
    cases ka <;> cases kb <;> simp [kept] at hh hl <;> try omega
    have ih' := ih (by simp [kept]; omega)
    cases conj <;> simp [kept] at ih' ⊢ <;>
      first | grw [← Nat.add_assoc, ← hand]; exact ih' | grw [← Nat.add_assoc, ← hor]; exact ih'

def eval6 (a b c d e f v : Nat) := value6 (v.testBit a) (v.testBit b) (v.testBit c)
    (v.testBit d) (v.testBit e) (v.testBit f)

theorem eval6_bound {m y s ws} (h : NatRun m y s ws) (hl : ws.length = s + 1)
    (a b c d e f : Nat) : eval6 a b c d e f y ≤ (ws.map (eval6 a b c d e f)).sum := by
  apply score_bound h hl
  · intro v w
    simpa only [eval6, Nat.testBit_and] using value6_and
      (v.testBit a) (v.testBit b) (v.testBit c) (v.testBit d) (v.testBit e) (v.testBit f)
      (w.testBit a) (w.testBit b) (w.testBit c) (w.testBit d) (w.testBit e) (w.testBit f)
  · intro v w
    simpa only [eval6, Nat.testBit_or] using value6_or
      (v.testBit a) (v.testBit b) (v.testBit c) (v.testBit d) (v.testBit e) (v.testBit f)
      (w.testBit a) (w.testBit b) (w.testBit c) (w.testBit d) (w.testBit e) (w.testBit f)

def scoreCheck (k s : Nat) (ws : List Nat) (code : Nat) : Bool :=
  if code = 0 then false else
    let a := code &&& 1023
    let b := (code >>> 10) &&& 1023
    let c := (code >>> 20) &&& 1023
    let d := (code >>> 30) &&& 1023
    let e := (code >>> 40) &&& 1023
    let f := (code >>> 50) &&& 1023
    ws.length == s + 1 && (ws.map (eval6 a b c d e f)).sum < eval6 a b c d e f (goal k)

theorem scoreCheck_no {k s ws} (h : NatRun (mask k) (goal k) s ws) (code : Nat) :
    scoreCheck k s ws code = false := by
  unfold scoreCheck
  split
  · rfl
  · dsimp only
    by_cases hl : ws.length = s + 1
    · simp [hl, Nat.not_lt_of_ge (eval6_bound h hl _ _ _ _ _ _)]
    · simp [hl]

def span (f : Nat → Bool) : Nat → Nat → Bool
  | 0, _ => true
  | n + 1, i => f i && span f n (i + 1)

theorem span_ok {f n o} (h : span f n o = true) : ∀ i, o ≤ i → i < o + n → f i = true := by
  induction n generalizing o with
  | zero => omega
  | succ n ih =>
    simp only [span, Bool.and_eq_true] at h
    intro i hi hj
    rcases Nat.eq_or_lt_of_le hi with rfl | hi
    · exact h.1
    · exact ih h.2 i (by omega) (by omega)

theorem span_join {f a o b} (ha : span f a o = true) (hb : span f b (o + a) = true) :
    span f (a + b) o = true := by
  induction a generalizing o with
  | zero => simpa using hb
  | succ a ih =>
    simp only [span, Bool.and_eq_true] at ha
    rw [Nat.succ_add, span, Bool.and_eq_true]
    exact ⟨ha.1, ih ha.2 (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hb)⟩

def fld (T w i : Nat) : Nat := (T >>> (w * i)) &&& (2 ^ w - 1)

def bsr (T w h : Nat) : Nat → Nat → Nat → Nat
  | 0, lo, _ => lo
  | f + 1, lo, hi =>
    if lo + 1 < hi then
      (if fld T w ((lo + hi) / 2) ≤ h then bsr T w h f ((lo + hi) / 2) hi
       else bsr T w h f lo ((lo + hi) / 2))
    else lo

def hw (w : Nat) : Nat := (w % 11400714819323198549 + 317) ^ 3 % 11400714819323198549 + 1

def hz : List Nat → Nat
  | [] => 0
  | w :: t => hw w + hz t

def hk (zs : List Nat) : Nat := hz zs % 4294967291

def found (S : Nat → Nat → List Nat) (N : Nat → Nat) (idx : Nat → List Nat → Nat)
    (s : Nat) (zs : List Nat) : Bool :=
  decide (idx s zs < N s) && zs.isPerm (S s (idx s zs))

def scr (k s : Nat) (pool : List Nat) (zs : List Nat) : Bool :=
  zs.length == s + 1 && pool.any (scoreCheck k s zs)

theorem scr_no {k s : Nat} (pool : List Nat) {zs : List Nat}
    (h : NatRun (mask k) (goal k) s zs) : scr k s pool zs = false := by
  unfold scr
  rw [Bool.and_eq_false_iff]
  right
  rw [List.any_eq_false]
  intro x _
  rw [scoreCheck_no h x]
  simp

def bar (k : Nat) (S : Nat → Nat → List Nat) (N : Nat → Nat) (idx : Nat → List Nat → Nat)
    (ori : List Nat → List Nat) (pool : List Nat) : Nat → Nat → Bool
  | 0, i => !(S 0 i == [goal k])
  | s + 1, i =>
    let ws := S (s + 1) i
    !(next (mask k) (s + 2 - ws.length) ws fun zs =>
        covers k s zs && !(scr k s pool zs) && !(found S N idx s (ori zs)))

theorem bar_sound {k S N idx ori pool} {s i : Nat} (hb : bar k S N idx ori pool s i = true)
    (hr : ∀ {u ys}, NatRun (mask k) (goal k) u ys → NatRun (mask k) (goal k) u (ori ys))
    (h : NatRun (mask k) (goal k) s (S s i)) :
    ∃ q < s, ∃ j < N q, NatRun (mask k) (goal k) q (S q j) := by
  cases s with
  | zero => simp [bar, zero_done h rfl] at hb
  | succ s =>
    by_contra! hn
    let F (zs : List Nat) :=
      covers k s zs && !(scr k s pool zs) && !(found S N idx s (ori zs))
    have hF (zs) (hz : NatRun (mask k) (goal k) s zs) : F zs = true := by
      simp only [F, covers_ok hz, scr_no pool hz, Bool.not_false, Bool.true_and, found]
      simp only [Bool.not_eq_true', Bool.and_eq_false_imp, decide_eq_true_eq]
      intro hj
      by_contra! hp
      have p := List.isPerm_iff.1 (Bool.eq_true_of_not_eq_false hp)
      exact hn s (by omega) _ hj (Run.perm p (hr hz))
    have hN := next_complete h s rfl _ (List.Perm.refl _) F hF
    change !(next _ _ _ F) = true at hb
    rw [hN] at hb
    contradiction

theorem bar_all {k S N idx ori pool} {cap : Nat}
    (hr : ∀ {u ys}, NatRun (mask k) (goal k) u ys → NatRun (mask k) (goal k) u (ori ys))
    (hc : ∀ s ≤ cap, ∀ i < N s, bar k S N idx ori pool s i = true) :
    ∀ s ≤ cap, ∀ i < N s, ¬ NatRun (mask k) (goal k) s (S s i) := by
  intro s
  induction s using Nat.strong_induction_on with
  | ind s ih =>
    intro hs i hi hh
    obtain ⟨q, hq, j, hj, h⟩ := bar_sound (hc s hs i hi) hr hh
    exact ih q hq (by omega) j hj h

def mv (m c : Nat) (ws : List Nat) : List Nat :=
  let a := ws.getD (c % 16) 0
  let b := ws.getD (c / 16 % 16) 0
  let op := c / 256 % 4
  let r := if op < 2 then ws.erase a else (ws.erase a).erase b
  (if op = 0 then a else if op = 1 then a ^^^ m else if op = 2 then a &&& b else a ||| b) ::
    kept (decide (c / 1024 % 2 = 1)) a (kept (decide (2 ≤ op ∧ c / 2048 % 2 = 1)) b r)


def moveF (tag d keep w : Nat) : Nat :=
  ((w &&& tag) <<< d) ||| ((w >>> d) &&& tag) ||| (w &&& keep)

theorem movedF (tag d keep i w : Nat) (h : (tag &&& (tag <<< d)) = 0) (h2 : (keep &&& tag) = 0)
    (h3 : (keep &&& (tag <<< d)) = 0) :
    (moveF tag d keep w).testBit i =
      (if tag.testBit i then w.testBit (d + i)
       else if (tag <<< d).testBit i then w.testBit (i - d)
       else if keep.testBit i then w.testBit i else false) := by
  have ht := congrArg (fun v : Nat => v.testBit i) h
  have ht2 := congrArg (fun v : Nat => v.testBit i) h2
  have ht3 := congrArg (fun v : Nat => v.testBit i) h3
  simp only [Nat.testBit_and, Nat.zero_testBit] at ht ht2 ht3
  simp only [moveF, Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_and, Nat.testBit_shiftRight] at *
  by_cases hi : d ≤ i <;> simp [hi] at * <;> grind

theorem moveF_hom (tag d keep : Nat) (h : (tag &&& (tag <<< d)) = 0) (h2 : (keep &&& tag) = 0)
    (h3 : (keep &&& (tag <<< d)) = 0) (a b : Nat) :
    moveF tag d keep (a &&& b) = (moveF tag d keep a &&& moveF tag d keep b) ∧
    moveF tag d keep (a ||| b) = (moveF tag d keep a ||| moveF tag d keep b) ∧
    moveF tag d keep (a ^^^ b) = (moveF tag d keep a ^^^ moveF tag d keep b) := by
  refine ⟨?_, ?_, ?_⟩ <;> apply Nat.eq_of_testBit_eq <;> intro i <;>
    simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor, movedF tag d keep i _ h h2 h3] <;>
    split_ifs <;> simp

theorem moveF_run {k s ws} (h : NatRun (mask k) (goal k) s ws) (tag d keep : Nat)
    (hz : (tag &&& (tag <<< d)) = 0) (h2 : (keep &&& tag) = 0) (h3 : (keep &&& (tag <<< d)) = 0)
    (hm : moveF tag d keep (mask k) = mask k) (hy : moveF tag d keep (goal k) = goal k) :
    NatRun (mask k) (goal k) s (ws.map (moveF tag d keep)) := by
  rw [← hy]
  exact Run.map _ (fun a => (moveF_hom tag d keep hz h2 h3 a (mask k)).2.2.trans (by rw [hm]))
    (fun a b => (moveF_hom tag d keep hz h2 h3 a b).1) (fun a b => (moveF_hom tag d keep hz h2 h3 a b).2.1) h

def okMove (k : Nat) (m : Nat × Nat × Nat) : Bool :=
  ((m.1 &&& (m.1 <<< m.2.1)) == 0) && ((m.2.2 &&& m.1) == 0) && ((m.2.2 &&& (m.1 <<< m.2.1)) == 0) &&
    (moveF m.1 m.2.1 m.2.2 (mask k) == mask k) && (moveF m.1 m.2.1 m.2.2 (goal k) == goal k)

def mvs (ms : List (Nat × Nat × Nat)) (w : Nat) : Nat := ms.foldl (fun w m => moveF m.1 m.2.1 m.2.2 w) w

theorem mvs_run {k : Nat} : ∀ (ms : List (Nat × Nat × Nat)) {s : Nat} {ws : List Nat},
    ms.all (okMove k) = true → NatRun (mask k) (goal k) s ws → NatRun (mask k) (goal k) s (ws.map (mvs ms))
  | [], s, ws, _, h => by
    have e : ws.map (mvs []) = ws := by
      conv_rhs => rw [← List.map_id ws]
      rfl
    rw [e]; exact h
  | m :: ms, s, ws, hok, h => by
    simp only [List.all_cons, Bool.and_eq_true] at hok
    obtain ⟨hm, hms⟩ := hok
    simp only [okMove, Bool.and_eq_true, beq_iff_eq] at hm
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hm
    have h' := moveF_run h m.1 m.2.1 m.2.2 h1 h2 h3 h4 h5
    have e : ws.map (mvs (m :: ms)) = (ws.map (moveF m.1 m.2.1 m.2.2)).map (mvs ms) := by
      rw [List.map_map]
      rfl
    rw [e]
    exact mvs_run ms hms h'

def pickMin (zs : List Nat) (b : List Nat) (g : List (Nat × Nat × Nat)) : List Nat :=
  if hk (zs.map (mvs g)) < hk b then zs.map (mvs g) else b

theorem pick_run {k : Nat} {s : Nat} {zs : List Nat} (hz : NatRun (mask k) (goal k) s zs) :
    ∀ (gs : List (List (Nat × Nat × Nat))) (b : List Nat), gs.all (fun g => g.all (okMove k)) = true →
      NatRun (mask k) (goal k) s b → NatRun (mask k) (goal k) s (gs.foldl (pickMin zs) b)
  | [], b, _, hb => hb
  | g :: gs, b, hok, hb => by
    simp only [List.all_cons, Bool.and_eq_true] at hok
    simp only [List.foldl_cons]
    apply pick_run hz gs _ hok.2
    unfold pickMin
    split
    · exact mvs_run g hok.1 hz
    · exact hb

def rowsG : List ℕ := [8, 16, 1, 2, 10, 24, 17, 24, 3, 17, 3, 10, 12, 20, 5, 6, 14, 28, 21, 28, 7, 21, 7, 14, 32, 4, 33, 34, 40, 48, 5, 6, 12, 20, 35, 49, 42, 56, 7, 21, 14, 28, 40, 48, 33, 34, 42, 56, 49, 56, 35, 49, 35, 42, 64, 64, 64, 64, 1, 2, 8, 16, 3, 17, 10, 24, 68, 68, 68, 68, 5, 6, 12, 20, 7, 21, 14, 28, 96, 96, 96, 96, 33, 34, 40, 48, 35, 49, 42, 56, 96, 68, 128, 128, 128, 128, 1, 2, 8, 16, 3, 17, 10, 24, 128, 4, 5, 6, 12, 20, 7, 21, 14, 28, 160, 160, 160, 160, 33, 34, 40, 48, 35, 49, 42, 56, 160, 192, 192, 192, 192, 192, 68, 224, 224, 224, 224, 224, 7, 21, 7, 14, 14, 28, 21, 28, 35, 49, 35, 42, 42, 56, 49, 56, 68, 68, 224, 224, 7, 21, 14, 28, 35, 49, 42, 56, 68, 224, 7, 21, 7, 14, 14, 28, 21, 28, 14, 28, 21, 28, 7, 21, 7, 14, 35, 49, 35, 42, 42, 56, 49, 56, 42, 56, 49, 56, 35, 49, 35, 42, 68, 68, 68, 68, 224, 224, 224, 224, 7, 21, 7, 14, 14, 28, 21, 28, 14, 28, 21, 28, 7, 21, 7, 14, 35, 49, 35, 42, 42, 56, 49, 56, 42, 56, 49, 56, 35, 49, 35, 42, 68, 68, 68, 68, 224, 224, 224, 224, 7, 21, 14, 28, 35, 49, 42, 56, 68, 224, 9, 18, 9, 18, 11, 25, 19, 26, 11, 25, 19, 26, 13, 22, 13, 22, 15, 29, 23, 30, 15, 29, 23, 30, 36, 36, 37, 38, 44, 52, 37, 38, 44, 52, 39, 53, 46, 60, 39, 53, 46, 60, 41, 50, 41, 50, 43, 57, 51, 58, 43, 57, 51, 58, 65, 66, 72, 80, 65, 66, 72, 80, 67, 81, 74, 88, 69, 70, 76, 84, 69, 70, 76, 84, 71, 85, 78, 92, 97, 98, 104, 112, 97, 98, 104, 112, 99, 113, 106, 120, 100, 100, 129, 130, 136, 144, 129, 130, 136, 144, 131, 145, 138, 152, 132, 132, 133, 134, 140, 148, 135, 149, 142, 156, 161, 162, 168, 176, 161, 162, 168, 176, 163, 177, 170, 184, 164, 193, 194, 200, 208, 196, 196, 225, 226, 232, 240, 228, 9, 9, 18, 18, 9, 9, 18, 18, 9, 9, 18, 18, 9, 9, 18, 18, 9, 18, 9, 18, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 65, 65, 66, 66, 72, 72, 80, 80, 65, 65, 66, 66, 72, 72, 80, 80, 65, 65, 66, 66, 72, 72, 80, 80, 65, 65, 66, 66, 72, 72, 80, 80, 65, 66, 72, 80, 65, 66, 72, 80, 129, 129, 130, 130, 136, 136, 144, 144, 129, 129, 130, 130, 136, 136, 144, 144, 129, 129, 130, 130, 136, 136, 144, 144, 129, 129, 130, 130, 136, 136, 144, 144, 129, 130, 136, 144, 129, 130, 136, 144, 132, 132, 132, 132, 132, 132, 132, 132, 132, 132]

def xsG : List ℕ := [0x440c0c0c0c440c0c0c0c0053333082311310c4431131131177533111dd5dd433007447744700744774470cc11d1c000c40c43100c40c40c41d10cc44744744, 0x8830303030883030303000acccc104522521488522522522dda5522376b7685500d11dd11d00d11dd11d154074740014814852014814814834615488d18d18, 0xffc00000000000000000003ff00000861000ffc003000fff000000fffffffc0010f0f0000ffff0f0000ffff43cc03fc100003fe0008003ffc000003c3c2fff000, 0x110c0c0c0c110c0c0c0c00053333208c44c43110c44c44c44bb5cc442ed6ed4cc008bb88bb8008bb88bb83302e2e000310310c4031031031022c731108b18b1, 0x22303030302230303030000acccc410a88a82a20a88a88a88eeaaa883babba8aa002ee22ee2002ee22ee22a838b88002a02a0a802a02a02a00b8aaa202e22e2, 0x3ff00000f81fff000003fff000000fffffffc000002f0f0ffff0000f0ffff0000bc33fc03e07ffc000007ffc000003ffc3c3d000000, 0x3fffffffffc0000000ffe000000003fffffffff0000000000000300ff00000000ff00000000c03c0003ff800000000c03c03c03c0000000000000, 0xffffffffffffc00000000000000000fffffffffffc0000000000000000000000200f000000000f00000000080300003efc03c0100f00000000000000000000000]

theorem rowsG_len : rowsG.length = 516 := by decide +kernel

theorem enc_inputsG :
    (List.ofFn fun (i : Fin 8) => (fun x : Fin 8 → Bool => x i)).map (fun a => encL a rowsG)
      = xsG := by decide +kernel

theorem enc_goalG : encL fG rowsG = goal 258 := by decide +kernel

theorem maskG : mask 258 = 2 ^ rowsG.length - 1 := by rw [rowsG_len]; simp [mask, lo]

theorem proper_failG : ∀ zs ∈ xsG.sublists, zs ≠ xsG →
    (cov 258 zs &&& lo 258) ≠ lo 258 := by decide +kernel

theorem no_subG (noRunFull : ∀ s ≤ 11, ¬ NatRun (mask 258) (goal 258) s xsG) :
    ∀ s ≤ 11, ∀ zs : List ℕ, zs.Sublist xsG → NatRun (mask 258) (goal 258) s zs → False := by
  intro s hs zs hz h
  by_cases e : zs = xsG
  · subst e; exact noRunFull s hs h
  · exact proper_failG zs (List.mem_sublists.2 hz) e (required h)

theorem mainG (noRunFull : ∀ s ≤ 11, ¬ NatRun (mask 258) (goal 258) s xsG) :
    ¬ HasCircuitSize 8 fG 11 := by
  intro h
  obtain ⟨s', hs', ws, hsub, hrun⟩ :=
    exists_run fG ⟨fun _ => false, fun _ => true, by decide⟩ 11 h
  have hr : NatRun (mask 258) (encL fG rowsG) s' (ws.map fun a => encL a rowsG) :=
    Run.map (fun a : BFn 8 => encL a rowsG)
      (fun a => by rw [maskG]; exact encL_inv a rowsG)
      (fun a b => encL_and a b rowsG) (fun a b => encL_or a b rowsG) hrun
  rw [enc_goalG] at hr
  refine no_subG noRunFull s' hs' _ ?_ hr
  rw [← enc_inputsG]
  exact hsub.map _

def NN : Nat → Nat
  | 5 => 26
  | 6 => 164
  | 7 => 602
  | 8 => 1293
  | 9 => 739
  | 10 => 38
  | 11 => 1
  | _ => 0

def HT : Nat → Nat
  | 5 => 0xd4535fce9e15da32909cf3bf6a9544996320835359be8b12551040e554827a60532608644463228143177cad422018da3487cd502ef0d66d27c199f0215096741aeded571901ddfc15dd81e10867783206b1dfc9063f816905cc70a9046e010e0282a33100f7706d
  | 6 => 0xfa023c93f9f5db05f36154e8efa0b90decdeeaecebfe3df5ebb6dca2e8f55c29df2ad561cfbecdeace884d92c7e765e7c532118ac164fbebbd7b6d28b8035492a465c192a10131169c4216b799b82289972a04869589757a92b5f1689206348c909cf3bf9086b3828eb18b1b8cf2655f873cc9d5845d9eba7dbb09a07a188e8879f7856a79d12d3574cba1ce74a877e2744ce88374040205708ba7bb6f93c3506f7f4a1c6f14208668388d8461d298b8619a60bb60af55835f4b60555eb2f8615b744fd95aa1686e5535935d53ff350f52c1528c52208e934d5307f14d50f6ac4cca6d2f4c8a7eec4c32ab774b3b47a44b30f0e34b2a1f9049bd4a5848b5f4cd47a3d9da472d5275417f90bc4168ff4740a2e57e3f78cd983f181df93e4f08ea3dc290603d0f19683c205c3c3b25792c3b146a0a3a207b8239f9c86339afc91f3964db7738c035a9389a52b9347aec7030bb990f2fa3389b2efef7312c83beb42a6be21a2a6bc53e29d0ecd6298563b42980e42829110611289bd2862885460e28555dec27f946fd27eaadf02776d70a26c1c88a269ee9b326988e6a25d55ad2254c4101254934ca2522a2a92494dc2423296c3b2202dc122163e409214f487e2107f2d01fdb5d401f8acc5e1f7128f61ef8b0ab1d774ed01d3aa7f61c92ea6d1c1bcf6f1960d0311837c21417a34f5e16a32de614f58bf71425ca8713504d5e134091c5130f10b3129287411273a220126adab110fe7bd8100ba2520e88d10f0d88139a0c0725190b39e72d0b3598190b1f83cc0ae24dcd0aa4c4670a129f3708e5b20d081bc4b0077638ac076f24ec076dafa106ff55b20547be2a05008b3804e3fcb7049a2f14045a95d6042ba2c004029ec503ced5d30385083002e5f2610282a331012300c00104300900af23fd
  | 7 => 0xff655a9ffe122298fda8600efcd39ea7fb2eef2cfb271e21fa68776cf9081810f8558c82f84dd6a3f374bea0f36154e8f3025251f1a23dfff0a845f8f03132f6ee6ed3a4ee03aa0eed56c618ec2d8ea5ec03ac69ead48cc1e933cdfae82beacee6c8a6bfe41d637be09178c1e07f6ac9e02f5667dfc60d00df9edf0bde789b47dcdcefb1dc958e5eda63d961d51553b0d22527cdd045f536cf8a8b74cf5bd3f7cf3f0eddce9d8565ce343bfecd5f6264ccd3e7a2cbb772d2cb8cfe5dca83c33ac8468247c7e765e7c6517da6c164fbebc06f1a44bfd37458bf7dcf79bf6752acbf5a9dc0be1ef5dcbbdbd9d4baac36d6ba579db4ba410d40ba1f9816b9ecb048b92ca223b886c938b5ee201db5d682edb5057bc8b4965dadb22b01a9b16300b0b11b9f5db004bf47af69195bae8311ccadc815fcad8f6530abe099b3abdc423dab337f82aa993561a982554ba8e9bc2da8e2064ea832dbdca71d13cba6a13c93a67a2daba6437d90a598c688a4fb89aca10fcb7fa0a0adc9a02ad8f9a00385a69fd12fae9fcd35719ea4a4449d1ce5119b5faad99b3685ba9ace44ab9a9aa1219a699e9d99dc6e2a99b82289992f660098e7e850987dd779982d909d9565e7c79544734e94a82039938928de92f28af392b47bc9923fd6e691ebda96917c0b5c911c2fb590b817b390a90e7d90652b46901369dd8e5fa0698dac4c9c8d78cd848cbe1d6d8cac7d768c54d4068c5356098c03babb8b69709a87d53b9586d6386a85eedf3a85cdbcf1847c062983ab0e6c8367a6d7830398e782ec5bff82ea762881d57be9819c5a9d81908645818a00b680b32121804dbcb6804221d27fefc12c7f475de67d68174d7d04696d7cb8ecdb7c42227979a95911799a6ee778fdcbd678eebc2378eb2f3478a40ce2789a78e6782f4f5078233170781b7b9177c2e4427743b25f76fe8e3676ada76e76436a9375ce0d7875bfb87d75378d3f752a4a80749bec9e744ce88372c6ed437280e0c271d629ba71b99050710349ef70be5d4e6fd269dc6f4d37656cd23b4f6c89eec56bf1c8726b369ea36ab411966a479a9469fe036569ca844d69b18a78697e25f56685a4c2662b43f565aa538a659bd73e648f7ea363eb086963bc97386339aa70616afe6460af5583603ca2be600a8d645f3b78895ee4cb995ed22f225e7d3a185dc8834c5d94a9185d8121f95cde89b15cb6993b5b53c9645b269c7e5ad7e8c65aa0d2fa5a3e4396595530c0593b412d5908038058586ca6577087275660be2a563262dc5565cd505540740f5428ebce53d9aed85322f392531b3db352b14a7451f6668151a7d96e518cfa5850bf08a450927bef4f840b7f4f586c4e4f0cb3cb4ea18a354e88289c4dcd6b644d881fc04cb819084cb537604ca18c904c8b1fe84c4639954b641af14ae9ae734a9abf864a7faa684a2af04c49e915cb49b7ba1b4968878349657b4c4916a5f4490fec4e48de0b9c479bebc5476686e64687530645a1337e458f6739456b8f004540dc7644bad9a64467447743c2fc014366abcf433f42d14324a93842ff404f42800a41426493ab423ee48442360d05423120ff41d31d6a4193955240edcbe640d9883d40af30ef40a2e57e409e097f40969bd7403cbf32403815f13f4f77443e0d90733d87d5783ccd1d083c1460713bf6d7b73b7beea63b710e333b01b9883afdcd493acab6bf3abf74683a850df93a4813ea3a3064893a1b4bb839fb7636399c1b4039724d5739649bcf3960e98b3953d3a8392480103911d279385beb0f38161d5736b1aa603687213336777bb635d13fa7351ac25a34ad7b883464029b3427e8d433f96f3c33f8849833d3489333b4a6a333adfa8d335be07c32fa96df32efe35b32e6e146329c12f2328c1f5632585acd32317027322dbd31320357b631fda70031e202d33169ba92314a03d0313f774a30c9cc2e2f70f6792f4aabd52f292eea2ef98cb62ef832282eda14542ec7a3842e941a472e358a6a2e20dad22df301e42dc0fb5f2d71c7c92d01f88f2cad051b2bd7461f2bd0d3fb2b89f6232b64f9bd2b4afd3a2b0d5f0d2b0791c12b0261b62a7122a62a6c4ae62a05f91029d71ef428e133522885460e2848c0a627c31b7627a14eb227375b73272d291d2712cc3626de362c269ee9b3268b67d426642e02261f98db25df8cc52546e269253f4742240a55742401d23623aac04523918108232ad3a1230b9f5722f727d822f3799b22d3b45022664908221c5c65220a57cf2119af5b210cfa6b210a17f920fed84420b4f177209ccd5c206d703f205c686e202762921ff87de71fe4317d1fab60ff1f9516081f67f6431f3b00e71f2db1d01f28c32b1f2528c51eb946971e910f101e80bdb91e79099b1e4d51ec1dfb1d9f1d69ca441cf159a51cba88451c6b7c281c11c97e1c03afb61bf047e41bb9d26d1ba12e0d1b86097b1b7627701b6d0fa61b3c81541b3a72b21b32abe21af2dd1c1a9bf9b41a90d0881a54c7c41a1eb0571a16c4d619fffb3d19f3594219cdd28819cc49531960d03118aac51918a5b45d18269cd117f9ab3517f5fa6d17c4901a17bcaffe1785514e177d9b6f1753db34172711a516b7ebf216a6d1f91666286315f3bf5215b77f2115a58a7115a35bef151cc35b14d13cbe14a152a414925cd5148509ba14803b6c1450c6e3142c1bb5142321a913d94ef713bcff9413a502e9139a5c101384e1cb134693a1133610a912eb9727124a4ba4124518fa124295c5121bf05b11df8d9211b97f8411b1f34a116e99e71103e9bb11015f6b10f3b3ba10a29f6e10976876106a84c7101d24ef101a847c0fefca7a0fc871760f8b2f5c0f83b75e0f57572b0f4585670f2f42520f096ef50edf21ea0e1bba020df9e1890d741aa80d2b2f180d1037200cf5c52e0c7a22640c5d06810c0ff99e0c01212b0b70e9170b660c1f0b3a428a0b1c0c7c0aa78d280a907e6b0a7961f80a76872e0a5b666d0a3925d40a3294c00a319eb70a2035720a1f296409f891020996a566097c030a0971aeba095e1416092d522b08ffd22908fc0feb08cc27c908c3d27808c2a712087189eb0860d7660854bd6c08405a030808410c0801bab107f8e1fc0797c772078e8256076ca5d7074431ce06e15db706b52407067ee612066c009c06439926060921ad05e7c4a005ca2bde05afb0890555d5da05303e83052c89c004ce314704c24f78049ae34e04768881043928cf0425c07504131b140410ce9403ee26b603bbf71703b1b5a6038afd1c03850830034d28470313cfeb02efd7d402cdc29d02b5e4cb02a3bcbe028790f7024f1b5c024e011d020d1f930204641301e4a86301d287ed0104698400a0097b00705d000061475b
  | 8 => 0xffa2aaa9ff7ae5ccfd5afc74fca26315fc9adf9cfc03bb73fb95b5cbfa67a4fff9b72d50f9b3970bf9706545f9319a32f9110d15f8e626c4f865a5dcf7e6cf8bf77d8624f6416e4ff5815177f524faeef48de2e2f47c27a6f3ab211af35b555ff305da7cf3018891f2f02bc9f25ad6e4f2580320f243c7ebf1cc989ff197c2b4f0f02e24f06b3e23f00e2d51f00542b9efb115eaefa944dfef790f1aef1bfe11eef62b5aee8a7191ee6ed3a4ee03aa0eecd56b87eca99d37ec357d93ec03ac69ebcc342ceafd963beaf48f06e94f6be7e91e5f4ce8ca65bde8b180d7e7bd7b02e721d516e7149900e6c8a6bfe5de7a75e4aa3c1ee48ecb3ce48b60c6e285d0cce2759b39e1a0f6aee0f3d110e072e5e2e05a87ecdffb0adbdf9edf0bdf505b1cdf29a7d9de9302c6dd60668edd2ffb4adcb80cd4dc1382eadb921800db8ce985db21bfefdb1fabb1da876889da63d961da635353da443120da0eba31d9b661fdd921c24ad88db076d737e384d71f9d61d624ddc6d57f4732d4b3804ed48d98e1d42105c9d3e6bca0d3802bbed3764324d3664707d32aa2fbd2ed7c0ed0597806d036e3a3cffce035cf5aaccacee6001fcd0e1ea7ccd8be68ccd3e7a2ccbcf4eccc4d9155cc4cb8e2cbe00ddbcb59189dca96742dc91a79d4c84cafc7c7e765e7c7e36660c781ef42c68011a8c5c3541ac5aef477c56c4ca9c55b9bffc52389f6c4bcf44bc49fced6c4471f7bc3db75bec39812d7c3127852c2db44d7c2b45789c1a35acdc0eb53e5c06f1a44bf8e2b1dbf7bf15bbf5a9dc0bed44773be31a6cfbd6927dcbd32ad10bc7550a3bc6ce3e2bb3317dcba38af27b9f1fd83b8315c3bb7e5bc93b7e2521db7bab94eb7a9b669b7a56f60b7a39d72b75b4bf4b6d0c24bb6082118b5f81232b5ce00e7b5a1dd45b57cbbc4b576aabbb5387637b5057bc8b4f14102b45066f7b42fb05fb2a11c9ab19f41ceb11b9f5db0cc2e6eb0c8c3f8b092fb3db06f9c8bb03ba511b03209fbb004bf47afecfac3aee5ad7eae6ed706ae397f9dae0818dfad8d3025ad722640ac78b3a1abe4a1cdabdc423dabd462c6ab40a202aa047713a9a6be30a9a353baa982554ba96d5e7ca9390b52a8d3a8d9a8cd1335a8372096a777f720a6437d90a5a64738a583d79aa5287da4a4755115a40c07aea3565dc6a3245434a2d0ee62a23cf176a1c0d448a149fb83a120afefa0b35e1da05e68fb9f59886c9e39b53e9dd2f7e89da1a2bb9d6f97c39d62b5509d2b48419d22d5289d1a12589c0353159b91b84c9b31ebd59b2363519a8799d59987012d99805a10994179da9938f8bd98fa581e98b8332098349219982d909d9827afa697326715972c58a196a06b2c96946f6f9646e5f496237751960b48e095acbe9094daa3d094bbe291943c861993fdf31393f6c18c93eb690993db62c193d61ea393a453a1936193719350d8e292ebb25492d0fe4692b68ec1923fd6e6915f59b690643868904730389018d8f08fc47bf88f77b7068ed854188e97870b8e9723318e8a09338e63e1168e4261798e17aa458e1414008dc0dc3a8dbc574a8d85fd488d32d1da8cbd2cb38cab93938c7a66828c7352d48c236fb78be1dcc58b0d23378ac0f7458aa1eb448a478a778a00e26e89e1ce6c89ce4feb89c69a0c88dca49b88cd9c128875d67288483259880fcb6b87c0f16d87707b0e86a444e0862d1594860081e1859c0ff2854ba67e853a3e7184fcc86e84b9495a84b417ad8476cc2f8474015883ac2aba83929668837a5fa6830f1c6082eaee86829dd19e81e31d3f81b40ded81b288fa819070f4815f0a36812ea43480c91797809b30d980610a48804dbcb67fd70c497fc1c2c47f5decc77f575bc17f3785707efbf2297e86804f7e3fd2fc7dafe8dc7d7177427d68174d7cd370b77c7908437c6a27507c4222797bff60277bd160617ba6823e7b760d667b74105c7af4b7207af123947ad3555c7a457c117a0933f679f0e2ef79af89727939891578fb232a78ede363787f6efb77db6e507744032a76d546d576cd90f676b574ac76965ab7767cf9c9766b40407612ad0374e03d9f74a67dd47478c13f747483c8745b87d07449bcb0743ad9997421141b741d830473dac9cd73b55a5273b2ddb97386c9fa73442bb3731b1d3572fffe5071fafabb71aa7e167165e0d670f08b5270c6891a70416a4d6f5f0ed76f3fd19c6f05f4f56ee7e57e6ec3d0486eb706086e6ea5b46e0bb13d6e055c4d6df9b2596d6bd2976d33251d6d2c32d06cfa521e6cbff5116cadce236b5fea8e6b4ef4926b3473c36ac5f3e76a862d2e6a7e5c2369cc941f69caef4b69ca844d69bd7a0069b9b3fd69acfaf569a75a16699dd74b6981f62c6960385a69442e006933a00a68ca56a36817a296678b1ff0677cac1a66ce4b2f669c50c3668fe3636680da2d666c4b2b664038e165cd03a765a0646f658570ad6584f15665765bef65273a4d6521c2cd650a12686481bd0c63bb29bf639c52d1638b5bcc6380758463767dae62844926625238aa616e9b9c614443e0612ccb5361217eb4610c158360e9638a60b88b3560ad35d7608a23e060419d4d60408ad0600167485fee73375f8d54b55eefac4b5ee6fd415ea1547b5e6f2d3f5e4cab0b5d7557ed5d5ae8105d58aca25d480b6c5d17bdd35cb945fe5ca544ea5ca19b9a5c78afb75bf6e04c5ba588a15b70faae5b4c1bd15b42746d5af2494f5aa0d2fa5a9072c55a7fc4ab5a550d775a4dda7c59be1e9c5995d91d5987d614598406eb5982da1c595e78215955014d5936ea03593427955930a7b55911a56158f3014958dbb6ae58db649758da525758b678555853b9c557719079576851f556ebcbd656e89a2e569d2d9c56904121566792bc5619ed8255fe495555f4c2f5558601145585b00255664a525558d923553a0e96550aff4454d1935d54ce123854ca1faf549e7f415404c5d75366f2575358f8505349b36852fa0b3452cb35f45257e85b524fd097524a5063523b73285205b6a051e7ddad51d97324519b7f55516227f2513a2ba0507ea7d150078e354ff204ee4fd6302e4f968db34f401be54f36e1e24f3652aa4f2c1c7b4f2851b84f1f49154f1ea8384f1d15bb4ef61d0d4edb34d04ed597864e8891684e844fda4db0918a4d9e7dd74d9aaff24d935f314d581b2d4d14caed4d067ac94d002e684cfbb6134cb1ed734ca18c904c85731e4c8430fa4c74ef4b4c44d4ba4c3752814c1b36434ba5d9284b93f0af4b7e2d2f4b7220984b5f79014b5703d04b53a1f54b4e975c4b2f12b84b1e61974b0f58ef4ae9ae734ad6ea1d4a9691ce4a439f1c4a153c7849e915cb49bb176348f5cfa348cb2e66487e5e39483934594826a664481e18b847b5c492479bebc5477adfeb46fdb6bd467163c046189c4b45fe8f6a45eca63645bf5f5445aa358c4551ec12452cab63452940ed450b438545085e8944b913de4442c4ec440b5b0644048e5b43da046f43acd9544383e96542ef8ecb42e3423142d58d1942b87da442abde1d4261ba75425ce64c425b9cf642147f1941c9942241c5970b41a24da2419eea4b418b81a1415c4da4413d995a41255ce0410e6a5340c389c040b6247140660d23405ae63640479fe4403cbf323fab56ab3fa24ffd3f8de0873f8956283f818ee53f3f68783f3697a13f28ebab3f1ce6443f149c723f07bf423eeed4973eca455a3ead170a3ea16af53e5ecf123e3af6d93de88fd53cf2da553cc4fa913c83ed503c7f0ce93c5f10a03c51add33c3613a83c328f713c1c570a3c1240ef3c0eaaaa3bde95263bd8f6803bce2a0a3bb94b5a3ba4f9ab3b60adfe3b4358273b33fb843b0cc09c3b0c9a3a3acf47b83aceca193abfea773a9ee55c3a7f58f13a3064893a2d46a33a16abe839c40ddb39bfa27139b2133639a46ca93994d699398a459039736ef039724d5738f6ad4738b6516838b11bf438a1503c389c81ee3856038d384862373807c45437c1496b37757a07376d68d53765cab6375dff6d3757de8637072bac367637f13670bfbb362814ca3607672635e2591435cc6a3535a1ce96354866be3520dab23520303d35112a9e350ffa3c350002d034f680e934f240f934bee5f034bc974934b4aa313478700b3473812e34720169346392f5341de7e93407d10d3402f58a33d7f87e33a65c52335be07c33554073333d829f3325b577331d4f41331796cb3306737f325657883213237e320e9fa531c61e9631a39c6231493e5b3147759a312c7da230ed0f2030e5853030d0253b30b1d9673073fefc305e7ca42feac3f32fdf96f92fc658462fac58562f83e0462f56890c2f2ab25a2f11cb6e2f0b27902ec0da782ebc2c912eb412802eacc4ed2e92b2142e7e96c22e76fa5a2e233a782e027cf52df5c93e2dd677dd2dcb6dd52dbe8cde2d8df53c2d79ca232d7633de2d5e35d62d5ad5132d15438a2cff725a2c8ddb5a2c58b4ba2c5358e72c23dd2e2bffc73b2bb4733a2bb40df42b66e9b52b6310282b2376fa2acd0ed92ac6221f2aac90712a919f9e2a8552f92a77d0562a7152ac2a5366652a3a7dc02a0e8a8c2a040b222a01c1aa29ec9b7229cbf70b29a2073e299afca229984b42297e5aa92959afe72948d0422943ee4a293153872900ffb328f6e19d28bef3cc28ab2cde28a7266728556f51284206f7283ec479282884b42808cd3827a14eb2277fa51e2777f2682764c608274e7a6a27375b7326fa88a926f7074626def8af26cecaa3266d052c266a479f26277466260664be25e5d3b625cb4731258f3572258163d325614f17255a5f87252a7c562517b58925130025251194a2250b597824ef4bc924d6936124c9057824c7b04424c0037d247955e52477608d24572c172454b3392431b9d12402fa8423f9dfdf23c5fa0923c37c7b23b141e8236d63ef236bc4d423649dff2360fe102348f64522e8101f22da90ce22a686cd22a381cd22656d4a224dbde9224d0e642244ead22238a51822322627221c5c6521fc4bd421f83ecf21f40bef21eab63a21d4ec5e21c02fe921b201f621926dd7215435c8213c2aba212f2bd92117db1d210ef68f20d62acb20cb5f1420ac5e26208dafc8206ecb6a206d7b8a20542fc8200f2eb71fef76ac1fe639e61fe42bf51fd8ac521fc386de1f8290db1f7639eb1efd73161ecb4cfa1eaa934c1ea2283a1e888e241e7cf3f71e52b92a1e38bbac1e08552e1de125051ddacee11dcf1acd1dc66bb91daff8a21da072131d49d5c41d1208ba1cf5bde21ce08c5d1cd723901c71d3091c4542341c1ba9571bfa3b7a1bd0f8031ba12e0d1b51a5f91b366fa71b33c5c01b33803f1afd81dc1ae4c2531ac9b09a1ac84fc91aac97a61aa2a3001a920c2c1a6e63b31a5d19c21a04283a19e9173419a11be4198ae2a519813ec7195580c1194aa4ce18ff612818fdb60218fc74e818647de11853dbbd1840c4fb18269cd117df86e617cd818b17ca54d117c61fba17b5e80f17b029f91799b64317910527178a6a811785514e177d9b6f1746884a170a7ed716f8500316e4fce416b1b2ab16b173a71681599f1668ebcd165373c7164fb2a71638380c16148ae21600cf2815f87a9515b937e715a58a71158f21291585e8dc15805bea15721a461534d5b2152058bb14e272f814bf649314abc1e014a63a0b14925cd5147b5a69145571541452c7ae143c777f141be24d140dbdd81401dc3a13ea7ee513e6873f13d6aeb813bda7ae13afd88e13a74f83139e913b1354bdbf135174531333ccf31328e80f1318d61312fc5ab612f7b0f712e15d5512ac36b11283c1191267b0a2124a44491246c0b912447fd1123bf29c123116a91226d10d120465c111fa76aa11ba024a11b4eb1e118a20951187c5e611868a501180459411657878115be665114653f5112eb7dd10f9ecbb10f19d2910d9853810a29f6e1080281e107c938f1070dc5c106b94e9106a9984106a2aa9105c3baa100e7769100d05ab0fd68a5b0fd341e60fd00f8d0fbea8120fba4ce00fb6f14e0fb6515a0fa38a2b0f7961b20f3025960f0548190ef5e0d60eec637d0ee229ba0ed75fc40ea5f9060ea45a900e82a2040e4a055c0e30056c0e25f0260e1461940e1006670dfaee3b0dc8e4d30dbc31c20daf559d0da657ab0d9f5adc0d859af50d8437fa0d66a99e0d61c4ae0d4b7b740d27e2590d27db1b0d006dca0ce110790cd88d4a0cc9b52e0cae78e10c9a8f870c8503160c73953c0c69c3e90c5df8290c4cc03c0c43285c0c3beb450c3618200c1f2b960c09a75a0bf9e0f40bd946660bcb43b90bbaa3480ba90b570b50a0680b5095db0b480b8f0b2c37c90b28f8b70b2128380b16825e0b10a2940b0383ef0ad4465b0acbb23a0ac8ce6d0a7f47360a6884810a632c270a5e374f0a36475c0a35802a0a2e16330a27b12f09d13aec09d0504809cae55e09c0dc9f09ab144309a31b67097f48fa097f062109473e770938f85a091c31a408eaea7c08de812908bf43ee088421f30874ef3608651612084ebdc20848e40d083fae11083b6eed0839aa020839a054082c44c10826bf040825642e0815d747080c55b608093bd708018add07fca70f07e9b93907d838d307c8ba5f07c79b6007b5826707af618007ae255007a7692b075ec26407585a47072d94a9071dc03e071742fa06eff06106ed3fce06d69ff706d12b3c06aad62106a2a47a069e1719066aa9d5065f70ab06189c0c06159abe060b2d54060991b205ff736505fab78f05e7c4a005e0a73d05c65dcb05c0210f05a25db5057c509805785dac05695a9f05692130055de356055cd4dc0544b2b205356af80517a2e104f8d7ee04eeecf804d7e1a504cff30504b7fbfd04aecd7d04a3672f049bb150048a6d5a0467e5dd04667593045fa2f604570956044b9cee044aa88004466c8f043d9f28042d2d52041d2a7a03e2538703c92fd703c8a2ed03c439c503bb123c03b56dfb03acc36d03a8831903a74ba103a362db0395ddce035183fc034d2847034c952b03295bcb031d499d031c930d03181eb603076ae0030349ad02f9430a02d7b81302c3a05202ae9d7002ac57200284d0cb02741554026577fc0261ae2b025d0085025912c502590672024e36d2021d549d0202c6c501b23a2401b072b6019714e80151d832014425e0013f06a30138a91901265e180124254500fc492200f9363800d18bec00d0bb7a00cd2535009d4847008dfc85006a42eb001aab13000f55b5000ad095
  | 9 => 0xffae5e82ffa2aaa9ff2cb406fed81ae4fe82f889fdd2a87ffc03bb73fbf867aefbaaa3bffb681b38fadd63fffa908171f9caccf0f9c647fef9b72d50f91b8d15f8fb220ff8ecf379f8e626c4f7cd146ff77e3ecdf6bd6204f6ae93ecf63e92c3f40b55aaf376f34cf34862f4f2920ec5f10e3b52ef755f1fef5bd06eeed586ccee8a7191edeed156ecc0c08aec68f649ec51830eec03ac69ebfface2eb81d82dea74c06aea20cac4e9438f26e6d54331e6cc1149e6043ca5e5e4d156e537f4e9e4e35bc7e48ecb3ce48b60c6e4684a08e413b0e6e296cda4e14ef392e1040374dfc30042df9edf0bdf5f6aa0d921c24ad90d8784d8ff7ef9d89d4fa8d89b6bfdd76a11e5d650c185d42105c9d2f7cf15d1a976a7d15d184fd05083c0cee6001fcdc304b2cdbe9b3bcd5551d4cce2bd0bccbcf4eccc4f9397cb2405c6c887ff08c7e83f5ec71ac731c59e6be9c40a77a1c3db75bec1d96de0c13f1baabf4f7981bd9ca092bd6a724fbce50763bc041600bb3317dcbaeea738b8969c84b81a3995b576aabbb4f14102b481457fb2b3cd8db1ebfc18b14f185cb0f98b9fb03ba511b004bf47af463fd5ae461294ae397f9dae0818dfad722640ad1fced0ad0faf34acb0f66eac6478dbab108957a8b87a97a8512dbda7fe4caca777f720a5d583ada5c7fdb8a5287da4a4b7775ba4b409a6a3d7056ea294c09ca20f56e3a18c15a5a08cf80ea05e68fb9fc2c8c09ef5ee789ec5b0cf9e9bffc49e257a789d6f97c39d59baf29d55cf979d22d5289b93c0db9b4418599b262ec09a903c21996fde87994c5a8c9938f8bd98ed4dd198b3108798026adb976db9139708214496730ca19646e5f494960d019409727f940153ae938d30fb92c76531925669069215f8db906438688f878cc38f50ba458e5cb71a8e26c4f38e17aa458deaef2c8dc3a0988dba1dcd8d7c7edc8be0c4908b8cdcb38a8dada48994366d893e094f88cd9c12880212ce87d770418719f341869838f186570e9e860d1c4d859c0ff284fcc86e84a66a62844baace83905f1e8364fbd582eaee86829dd19e825ab28481deed9781b40ded81186db280d58c8080c18b6c7fa0388c7f7b1f6a7f6443a87eab74897e677aae7cf7fd307ce7e9a87c63fc147bd160617b35c0267a8375c67a46275e7a293dfe79af8972799871de7936d0a8791eef0f78f49c0278ede36378d2a61478c8c6fd774dec89773ce2ad772df6c5768617f175ebb1f37548701c72ba25d37230de00720560ea71fafabb701468a06fcfc6506f734a526f3aa8196f19458a6f05f4f56ed223ce6e9c7d606e6ea5b46e055c4d6c9aa4bb6bd20b146b595c326b3351aa6b291afb6a93ae416a5f129b699a4657693697fe673e0d8d66d4c42666cd9f536699bc4064b100b5645f482064412044643fce0d63eb34eb621e7a32620307e36199be7c6161edb8615eb69660347ee1600158805f5042065ecd64eb5e6f2d3f5e4da2225e4cab0b5de7f0be5dc6d4125d638d545d5ae8105ce374885cd4bc255c2bc5b85c240ad65b8cbb955b89af575b7a45ef5b53b0ff5b23722e5ae144b059110526590722dc58f8715b58da5257586af49658647017582304c557fd5bb957323df456e9e4a156e1366056bb3bc0569d2d9c563a961c55f4c2f555ee805a5542c0ef552cfc3e54d1935d54cadb74546e198a542d35d853e29ec853433b8352c20d5552bb34ff52a46f7651dad36050dc2eb350c8ef44509cfab45079719c504d8a305037b9ce4f3313e04ef61d0d4ee9555b4e1e082c4dda671d4c9e47544bcc62654ba1a6da4ba129094b6ac0ec4b61f50a4b53a1f54a79baba49bb1763499e1fb54933fc0b480e48c647b07a0747a4ff5f4769f779470456a146c0d8f846974854468f2186466a046b4662c70a4618925645fe8f6a45c1baa345a156ac4558713c4554daf7453eb510451d695644d76d48449d590044602e2d4442c4ec440d82e5433f338b42b87da4428491904254b96a420e8bcd41e2b23b41c5377c418b81a14185b88f40b49ac84050de8f40479fe43fe59ace3f28fd0b3f28fc6b3ed5260c3ea4e78c3db36a1d3c2a98c43c1ca6073c1432ee3bccd3ba3bc42c0c3bac5fee3b0143663aebe4b83aaf72ce3a98fbfb3a94fee43a917ac83a547e8e3a2d46a33a2bb57d3a0f36383a009e3239f0ad9739ddd22c39511c343919be4a3871b7d63861c2013858be01383135d4382a5683382a045a37f6658837f2f53a37850ef2375b6669371036b036e81d2d36a6b1db36a45c763660c65336373214362814ca358e3aac357744da353e54c334c38aab34bee5f034b2da01341ed9bf33b856e9337b70bf334c6c18333d829f33307852331ca54b331227583306737f32f1c6a032ef50d932d71f723242d4f8323282d93225d32d322517c63174bb9a316d35ed3160dacd309cab52305e7ca4303b7218301425b62fc658462fac58562f5fdbc92f459fca2f27eced2f20a7ca2f13fc992eb1c0ed2e826e192e35cb7c2e1b11032db44b2f2d88e4d12d79ca232d7633de2d4dcac62d3878262d0cdf872ceacd832c5be8722c4057f92becb71a2b49f5f32b3929002b1804c32af2e6792abfbb172a8831db2a18a6342a040b2229f9ab3f29e6863429dc432629b995832943ee4a2900ffb328fd67d028f4282728ec9add28b60d902892866f284ddf27283ec479282c11a527d758be27c6376d27c50ae127bfa95d274b5c84273cd53e2739901f268de84f2652ce9a26192ddd260664be259aa007258f3572255b4d2525406bc7252a7c5625225e6e24dd3b1b24d290f6247e8fd92472aa33246e1da02433200a23f6d8b723f3ec0b23b3698d238f739923758cae235e244822cc446d224d0e6421ff3fc421fe8a7521dcfbd121d0678c214aec2c210b948220bea99c20ab7cbc206ecb6a205b9880201a93e81fc19f9c1f8c8e9f1f59ffb71f39af781f252d1f1e38bbac1ddd61951dd0ac111dce05c51dbfdf1e1d913ec31d897fd91d2d539c1d1991e51d1208ba1cece1401ce275c81cda5de61c9561e21c56e8581c0fe6821b66beb81b33803f1aaf39761a97e0041a8aabef1a5188f51a1d19361a074a9d19b051481950579a1949d702194161e1190b4ad218fa91bc1853dbbd184931ce182ae6db17cddf1017422108172b714b17222103171dcf181705b6a116bcad8b16b71dec16aa6d5416a650f91681599f165ee3d0164db2191648269216339509161f159416193d9d16148ae215f87a9515e3d4a315aff4361593e3c61574ec50156e578f155cda5a153d3d7f15242f9d14c6a04714a2110a13f9882f13bf8c1213bda7ae13b953aa1397b7a213568f2e13247a9f131271e112f60e6612efe13112e15d5512b8d9a912ad4b5312a14a06129e84681293cbf1127827c01248923712413bbf123b8240123b7e521227d3bc11fea9ad11daf13f11cbdcc11191170a1187c5e61172fdef115543cf10f1b20e10a98043105f60571017e65d0ffa6d5c0feee5390fe4a0950fe487e30fba4ce00fa38a2b0f9fc3780f937d2e0f7ade1d0f3e18fb0f16d4810f02481e0eb659480e8e1d180e59200a0e4a055c0e25f0260e036e030dcb164c0dbc4a2b0daa3b8e0d8975290d7dd3ff0d61c4ae0d4ac2420d36b20e0d0dcad10cf77e0f0cebda700c6571010c4fbf8e0c488b6b0c16a6e90c14880c0c0c91e70bae697e0b87bbe10b50a0680b37187b0aed7ad80ac9de830abf67b20abd0f7a0a5b468a0a49cd190a417c360a27d7610a080f9a09fb0502099d2e390997425309154e4f08d8d3bf08ab6f8c08a2a9bf0898b7dc0809cb580792b39007432a7a06fad11306ed3fce06d65f2d06c371220691e1c006664f0c0665dddf0646423006159abe0612836105ec742d05bd3d350586e2d2057cc4840571f19e04c40d5804bc7ee0048f2c690474e59504671f8d041d1cb90413209303d673d303c92fd7039c7fa6039a6184035db2320349499a0332a0c3031d499d031bc24902a0a2c5024cf3de0249da390244f3e50221819a021b276501bbb16701b2fa8b01b07fd201a70c7f017b7b3c0159a6e9014ff18301150e62010f15ea00dfd62800dbbd8f00d8a3b000d0bb7a008bce18005cc9d8005414a20020b5ca000f55b5
  | 10 => 0xf7cd146fd42105c9c13f1baab576aabbab108957a5c7fdb8a294c09c98026adb7f6443a87a8375c6673e0d8d66d4c4266699bc40546e198a509cfab44ef61d0d4a79baba49bb176332ef50d93225d32d2fc658462d88e4d12d79ca232739901f22cc446d224d0e6421d0678c214aec2c1f8c8e9f1b33803f1a97e00418fa91bc182ae6db12b8d9a90ffa6d5c0b50a0680898b7dc04132093
  | 11 => 0x4ef61d0d
  | _ => 0

def PT : Nat → Nat
  | 5 => 0x49819282143150ec062a2240c544381928490315072062a0e00c540da19a860c30501cc66a22c040005019280b831506e862a0a10c5419a19280943150aa064a1300c9448a10203fc330080862a05e8c541f01928034100
  | 6 => 0x49c0c020c10c5045818b077033649c02001840cd86c03929ca030637c06407e40c591c8100a4503163d2062c8a00400bb818b06103162b086288982c4054018b1980316198862c6480c58f8219012d0306318062a6dc08146601811f4431622a062a7690c08b1818b158032618b864c6301c54f6819b14903261bb862c0de0c989b819314b032036c86066d50c0ceb819b1d103362ac040a6610c08e6818b0bb4330318020a0472c087401b01b30316192062c5c00c50668198158631614786624618d8417919b1ef0100340062c2840c985c819019f0336060462c5e58d40c901930c303200fd064c1780c5861a1b005b83260ea064025004000681180036326278862c4e0040061a1a0179433030606623bd0c58c0819b0c3432608044602210c0cb7819313cc3142c8062c2490c5864e1820d2c36135002003150c80b0819315f0316057062c6050cc126018b18c210000ec40a3740c500ff19301fa3202aa062c5500cd84931820a903413f3860838004006c008294b032623086822e48c9857a18b179a34009b866c4f00c987f21931390326268062c1f90c8017918b0920303250064c4700c584a008298c0b1519a866c8610810fa21020a94306230064c4540c9889018b0bb63601a406a21808c585da1829a80720193c6061d50c9902019001141001de064c5c10c581c518b0d80b251d6062c0bc0c507fc10211563163f346065628c4c548198954036145f062c31a0c986e81930f4c3161b0064a3480cd837b18b0904336
  | 7 => 0x2b808002a010689204071e40dc1b605833af020350406e325c0c9caf018b9330b1626c062e4cc0c5a3f850b1ae0205924064080d0dc22981b848903718f8062ec28080656010247f010088806e0a3c0c526e808307d031768606601080c9c1e018b83603278ce06e12082808048193933071698c020d4040c9e7d818bce6031789c02011dc0dc5ce8101c3d03719b906621768c5e6e858b2224100a12042a0d80c5c9185834dd031693c0201254040267018bbd50371308862ef0c040221010a4fc032783a0200eac0dc1d481b840103718fe020d20804024c019824603167b6062f0d00dc65a019393e4b6590606212bc0c9e6e838b4ac031740e0663194040202850113407169460662f2c0dc2048102c5f01008b002004d02c1804818b9330a0627c820d138041a4c01988d86361502062e7f00c0a710580bf30317914064f1c80d049185010c523616fe062ef600896400193a220b05178464eae80c05c281b8a220a356d8062d3481c053b218a8d943176f8064046f0cddb600803d603028e0062f074041a36818bcc60b068be160271b1c9a330198a3c03706b606403730cde3101939c10b02054140cf6c084a1e81a0c5d031787806a316c0cdd2b850149505000da864ec340c5cf5218ab2b03710eb060d23c0cc2368102c8f03706d80e2c4cc1841788183cd2070248606611000c5df321819b9037061206610f00cdc51218bcdd0b066a4042a024081e19818bc8bc360882020d0a80c5db5a193a5e43149fc062f388280a70850133e02025a00200b600dc523e1b89be420583a162cb280dc56481b8bb4010098a06041110cde0f81939c6c316295864f1c80d8454818b98ce30492e060f1b008855401b882e030219f0680ccd0c9d4901b828a037079f06e2fe80c9ded8103cc60a015000640bbc0885f50193be903177ca064edfd0c0db60083284010092a1e022730c5c8de18bb6c430229844608e40dc21e81b0921836087806e31382c18e3658b4b9070138d8e2c83d0c158301131ae031768e06a030a8c488131a0294020574e04606fd8dc22fe518c5b03275020404a300dc6710080326010625c06c0b600d047d21a01348b020130626e800c9dcd818b9c5037138606e31fc2c18dd81902b7034009d04023400dc0d401b8a1f020261a860642e0c5c8c40802b0010045c04093bc0dc0c5c1a01534341704062edfc0c9e2085b036c4b026f8064eac12d94dd918811847402ba462ede00c5dbb819396b03605a0020c2028c5db5818b9188b264e6046c7042809b643812be010080a0200ae4040033b19394203702680200d740cc5ad8193a2241033be040cc810c153b318b9c601006a2062f194280900e11311883260458406e6908409381b81cb02052b2020110404016b818834303313480406a4c0d4067a19833b0317508020c9e90d019c81989330a02670062e52f0c5d9b0193967c3371bc06e0a310d445fc193a01c3165c006e048c0401930082984020533e0640848089968a188118c71002d86a029c0dc1680581834233159406a2574080cbf118b891037111c06807fa0c5d2b808016b0370546c6269340400110193bb80100243066064a0c9c3b01b8357c31495c0620c240cdd840193b06033701c060e19c0cc23ba1b09684317516c6c11fc1c583af1b848b43703d4c62e4250c5c9681014bf8313444020caa00d0409419bad00b165a016080740dc19300800e20314216040a33d0cdd3131012b04a3570a06c2b840c5cc391b82dc033748246e24621c98b021902d003163fcc6a2b708cc26ec5812c303277d686e0b040c5d9300819c6031438686c20a81c41580082bf4431019e86e04619cc0b531b8ab20317444960ca310d84ad81130a202052300ec0a11ac18acb5009c6010606a8680a0a0cc4a5010b2a503178b704420b90c5ce080802a2032709206627fa0c59bec1b8078021492b1c05228085ca0810b12b831794604065fe0dc1d73100af88370532064e4ff0c5cc5b1a81570213230964085a0dc21421b8a9303408bf9662db02c588c63902b04b6067a04033700c1ce811b828203276860680a000c9e4bc18190c631790606e0ac00418a7618ba76033731786609cc0c5cc7b0804d20a0220e46e27148d8539018b9184320282464ea10a8046c01a09c607144d0066e1b10c5d32819bd0c02029ba0200fd10d8130018bc950e017ac86e056404192f118b86c23131b0c6e294c0c9cab810ba47831659686c02fc0859248198a4803377700e409180c5d0131b8ab00103236062a9100c9c59810b15363718e6040efd90dc09f008293401062b216044cc041890b1a822201055a00e2d384040083b1a8a3403377bac6e1400085517018bbcf0316246020ce1d8dc0e3058a13f220538a06a31f20c0c7bf1b8118010601204063148dc50f818bc2c42065a0d60c9798c58c62183a150327428062e0298c5c7fe1b808a23012b6866f2fc0c1c67a1a84274370410066e91e0d0483f1a0a0103177861428a4d8cc19881008c5434171846e224f0c5c7480800754350318860a4840d003701829f703170884660adc8dc020810810ca20432504082090dc13d11881c60b265b006c219d0cdd47818bc7fcb0238c162722e0d00f5019ba8ba3407d2c4085a58c5d6501b092e03700248660b240d84b03193c72c3713b8064e564ac18ec818b98f2106256c46c74c0c9d47818b05683072e906e262d0d80e5818b9ca03372a686c266e0c85380100ab70360166864e68f8d00e301934c601007e886e02298c114591a83db032022e86e106008057c91881bb032792b9e0414d0dc034918bb0442055a04e4069c0d415401b0acb4370
  | 8 => 0x21c03274440ee05800c5c6d01988c7061017e16ec404041d7080838bf01052760610474040156010a8c903131c2140c9a52dc14c81c02980330276060eb700400ea00800900b765a8020c31c281d3b05b80ac03380320e0ea382dc4a281c029d02084720442b24081d1b81842a6022552c02007f80c492d85009d80b071b4040c7f00c488703938610b0217e020e9d80dc14701b8ad9022140c07007dc1dc15001021f60720274142cb18081c4e8083a3a0208574044275c08041a85938350770120020eaf404189f05839f303013340e0ea082dc0ea05b883203280c40202aa4381812818c15903084220200a080dc1580083aa3034145207003d90c612f818399c0b073b00e40b880c612a81c027c03814d8140eb502dd95480831e50380360042e7900e000c8503a8c020547406609cc0e047a83b81dd03803380c205c00884b801839a60b7554e020e87408116341988000102340040e96c2818c18110a62030157a0a0cb700405500083ad401073cc0410af42c593281c006c6b7640207006800c5c31051099c06175521c02afc0c615e818b2bc031852c020ea2c089cf78110a6702082a80442ac02c5d61050327d030807ac4429c408954103b02a905062020e0e93c0e0455810416602213a00442ac00c5d1c810195202274d804281b1841d54870b13e0a0255806508cc281cea05009e903601a00ea0a9c2c9ca9018b8df0321560020288a1c804805b8260020541007000d404014325b82bd0f1650c020ca0008214801c0804831834c144a6701c5d538193aa00b17494140643828055e0194260032157a0e2c2741c1d1105b8279020857b1e04a0804187a850a2a003170a60e0aa1804014080800b00221160040ea780c610a018324902154660e408880dc16301b8a21038049e07002440c8558038ba7a01003e4060ea600ce154878b08902074ea020ca8004043631b0a3b0206496060e7a40dc0fbc3901f6873013646504241c41338110a6c01074ea0c209fc0d011a01030d0076017e16ea8a108195383939a203800700700a08040118018427a4f0251806507d82c814305bb24f434048e042c984041d708080244021751406707ec0e0150038b9f90380440044296c0418fb0190223030851c020eac02c1d2c0080277010050416ec08a0e055d01042e1071757a1c2ca582dc4ba0110a83033153006501af0c844f03b80f50b400e58442a8c0dc4308580a6c0a102ae0410944040154858316e222109896ec4300c1d1103b024a01000d8d6c2b4808a1288528a0d430850c020eab00d413a85bb04c4105136461080128148281c006642214fa0624b300884c600800d243131a00ee096c1c1d6301040610100450046c26c8c1cfa818383422214840200b842808ec008023d0106504020eac0185d38818c0cc430108686e0a1804106f0110a3102075520a001c48c1ce5819811203804cb066034028d41a839011c630846c040e9a404193d808381a433003e0e80131041c7c810424c0208428042c6f504013b8083a7601074c2162e9d4041d34018c04823071ea06e02550c611580832960b071e00e2045c0d402891a822bc1004b616ec0b9041d2c81182bd0b063ee0ec08880418fb03b826103174e40442131040930018c0a603805521e0c07d0400d601c027b070155e040e9442c055701018bf0b054a216a23e10dc038b1a02690107200042c8348cc570830119c0100018041085804193d07821fc0232254564c22004016f01c028b0307422020c8f4180d65019886b43074f41c0297c0e012d8503a610101090c6809e8140072318328923703ab06607a50d013b00802690104012440e96c041c4f03a023307012104ee0a8004011e85bb104c38056014047b008850645031eb021748606702300e0049a1a80af034021c020080004192831808fe433126e86029000c60ec81982a70b074ae040c5bc080cfd0083aa90a0135c040aa6c1c096a0380a3b031849402023d42dc11c819406c67713ee020c7d8041d4705b8072c20756c06263412dd95e878305203803b8046e4530ca0d43103a2b0b761a4c624a280c21508198261071707886608d00c4cb101838d04105484020252e0c20f50110a21833059804608882dd89f0580a3d01072f8040630308181581041ae432857a1c0c0aa08141801c00190a405bc06601cb0c9c7a808010c831215ec6a05dd8d40ec030b9490b700988206a8028100fc583265037027a068059c0c20682080220033843e06708582dd83781c018c0a5051c02003dd8c5c4c01040d302082de040c2218d003f01842110b7642c020a4cc8d010605b88c6622135e044289828192b01a016723071a0820eb740860ed008318103813b0020e8b0041d2e0110a56038010f06500880d851580839058350350042e4f804014b05011e9038043c06c07dc0400d281139f601001c2140e3c40c5122018384203302f282007bc08211100838e203600580442295841c8981a810c035008506e08000400ac010912e4a3540016ec718040140010395702071a082064708c157085008a6c3074d816806f4041cfcc19820001053f80610a74081cfd058b9b7010719e46247008e0058c1031c7036042c020e0cd0e00a495baa864a400000000b240820fb059385a4a1648e840c29b8d01348080108272031c044251c0dc13c8103a1101075a404068ac2d8446a11094402043ec162e7e81c407b618ba0c01070a6842427a1cc08413a003c036004406823620400a391a81fd03185400c0885c08189f81029fc03184f60e0e7e80c5c1e21a81b40203596044292c0884fb01939a601062f404623b20884fa818c06d4b7145c04064b408140c85080d0036038086a01d40c2019011099c010759e07004170d8030618c06c6731400020e0b91c1c4f05b81f8422114346a098428088f03838886b062ee460e5068cc04191a89350380234840e3da0d448901129eb032804406e24f50ca00283081ce431738c14045940898fb8083a8e077127416043890c20b001138d007304a3946257008996381c0237030741e040c7c80e0026208089e037022007027d81c4145818b957021715a860c7682dd867818380001003b0164e558088480838b894038112607007612c0c1bd1c005a8b271a4460a3490c1ced00828b2c10000444027570c2069a10390f82062fe02004300d8165810405a81061e306308840dc10fc10283883400f207004690c5c23618426101003b806302209cc0ba8083177033028ec7001b5041d3b03b804323803b0064e3880c1c65218413303701bc040a3dd0d4457b18c0a30207041444245d0dc02d419386a03700c8070025b88c0ec038b8f1831703f0e603402dc0e801941fa0a40254540c7380c608403b01cd0338110c20c72c0ce0843083a9e02121a8444220f8e0492010b06f036036e164e5dd0d00de808302cc20526a86803240818b0e52006f83702c2020e1312dd4c8b1b01b9231800a140e4cc0e0154e79304283403f40e2e8e8080865a18081aa34014d86a03400dc0db8083282077040096ea7d81c9c93f19821c0221315862e2da0c601e01b81da01074d8142843c08981901838b60205292020c5800c4c6805b01d4010722a04067a70cc0b0e0800e0638034c16ec38b0d00a20083959430459407000f58dc47c01a003383070b2040c2789c80a9018186d410031507022219d004f308013e01070df86803798ca09d00839ae03181e056e06980414f5818427a0e0403407004f48c800ce5902d00a1741b46c096d2808ce0593822035134506806712c0cb381b0046a34025c020c6940ce0c2010421601030ecc4420740d44b6910312a01074d216ec5730c194f81181eb030734806305119c5c9d818196f020423886807e40dc07c21b01c743503f40e804ac04006921840dd02264b014047548c1d4b05388b743180f0564c1cc08948f00831b7010243c0700af62c0884539812a61000d88e826780ce0ce019389e6b761fc44603602c1d5201c015702031a4046e4b00819460110941434005484423e4081d628184236020851606103740818cc019c0620721110c2066f52c1869b1021f5030821c020e5460e00bb81c009e076020f844256c0884860184095431736e948c44d8d80840083141636037a948c1f98c1928318a9d8072706fc6a099c081cc981989bd01040b50e4e8b0840009e18c18f031834c020e52c0c1c16619c2c20a0703e86806340c603411a02a9ce0257b1c4c45f0d0075b1109e10301368440e3ad881cc4819c1da4b752ea16ec6dc04101e11a00f501072ea944a420adc038b1c008383411be041002d0c607800830eb420815d063007f1dc1369103a89834012686e02aa8c58ba8082a6c061414006a00050c603201810ac022107484421b01d84a210800b44312058044a5ec0ce0b981c0015420713e0442668041ca7a1a009b02170a28610094080c2d65931d543401e2062a2648d808411b8173035058c07021218e00d300811610b271a00e405d6040c29019814543401c0c6a01b1adc44d61a00424360026040a26d8c14df4184038230713cc20e63004080fa083a7902211a0020c1e808582d6080134022136f164c1b00d04971081982060443c86a0a4c08844425a012c42210560642b88080c594083ae1020257a02009b01c1c3561c01490b762d00630948088525819387163301a546088348d40a0a1839620318098944a04588845f808319163800d8c6e25102c5d54c7131496b600d686a056c0ca008910201dc31854f1606524041469c10185a02160b2042c5640ce12d01809570328168c6105500ca0c32180a3682030d606805480c608f03019752b7525cd6ea5d4041cb42102231620803e8e4033e0c2059008320c4100078870021f088439a19c18d0313096042c1e60cc0bea10214b032851e07002a30884a0a1a80696230092044c1ac0e0053019813a01061c4860a4e82c1ca3c1a018143710d856821218cc09705bb108010036486622780418a2018bad40707254164e23d8884ce039381f0b400ba8630460ad44688182150033028347000ec084891b18ba8a83040e2c6a05398885342102a824720106862e4fc0c6055118c13b03180aa84104b80415050110a0a020757b9c0424004188f05bb12a010649c07004e82c1825e18329043614a006300e08d4036108008801071fec68033e8d400ec18b8e843283d706069dc28583c00801442a0432346a00f50e0437a1a80884b0710606c27008dc0ba8081037232113606086240c043c0083892e313092440c0688dc096818c2856380312063010e0d011b819384683504d2148c69a04009381a80c6220655607003412dd48e0183a880380512c7022818dc08705939fd620422607001218d403600832166b051ee0702296adc47001b81b7a10045616e24202dd94491a80d2631803406a01e0a918c8b1818554204292020e3a10884e801a811b03180c202048140c045011c017b03181c006808b129000aa1040af0360322468026d8cc158008013f42031e00200168041c67a1a01440101442044201808593d4701099633020a46802a80c51388104062010014886502918884a2230208827504661402a0c080cfe810103363401e2844e3090e010e0103912031801706024cd0d403d010304263504a0862e0e4082002110284c01061ed06827558c1840b1908f00b7621c064e635080c4c91b803f6230163042c8340c1c4c81c01c0a3400f0964e5258400e381c02a343511e0420e4150cc05091c028943804a39662898a81c50b198a4342175800406a9c04009d008007e635057a9e4c0dc8c1c55318babf020324ac7006f42c1c2301b0290037124646305ec0808cdc1108a1837029844623fc0d209700839d5430515c840646d08187e018c11c630345a8700aa404010f11a0055420325602021e10418e3b1a00a5c1002540204aa43c0889e1a02a303811328680154081ced251aac6c20329202041fb8c1019a1a81c54380522044239808854d8501037034006a020e1681858ea05b806e02211f0070071a280497208016743501e206708582dd55e8280043835023c020e5800c611ea3839db422122e870009908153501c02aa0208
  | 9 => 0x702e180e81938080506000020407c29c40705038080b760260c080741c1c0385c381c070701c02020443c040e030b808010500e02020142e040087a980c0a0602c1cec03c3dd80a070180f0f360221e08074181c040283811050002615020881400078703813060704a0f00020041c03808401d07270361702018040812010201a0b2700a02100303c180a07030200b800100a0a000294006070301d0a170101eec0002e080a03838220b700380e2e0002d480385b88240500038142c08004001101b800f0e03046040a09038040e05830060a2103f0e60000042007873b0160b7502a96a207c2e000705a00080f65048020e04c1c200d851081a0a1704216a007c0e0003030282501020281e0e018182004078301907400101cec0881d801183040160f7503815000903810116710006062104602100640d800c051b00b6a060480a0e058289412058b81307040481c8e04c1c1c02854001f0770044020c0900c5c0a078180b060200a0442014081c0e01830110e040441ec00503c181202808168e050221c0e0642d800593838240101042020e05839d40c81b80090b860181e6005c1c040b07128230b280020c0c08004200405ba8070b810380c0e02498180985808240f17044020007c041c1207a38230328000170008839c002830381c07060440a0c00a3d0412038b80d41040441cc0058399402831080e070803a02000882dd81180810220e16012966000914180f008101d06210080c080092dd80f05400010b8003216e000938980120828186a30002170c088141c0407ba8210b870101ce007c040003c5108000b81044020e0372c200122838130608040165008c1ca004851b003230703f0660038290003854080b470403e170e009041c0701040070b010281c0e07008580385208240f040090e0e03718201107bb0160f720441e2c084042012070b81b06070221e0e009040801228281605020360e0e07404200405828024f7602e8e060800408022302803634003c17040093c9804470a8050a0701c0e2001c29c40f808401c01070064e0e05d28c404073a81943400380e200002a000595c301b0a80002148c09004000e030b0020f030360442068085c0b854000e060803c021002038180c35b801f0b710181e0e0051c1c0b838a0160f2502c1ce40203c140b27180024f650380c0c0942d4004073280006210268c0406c041c0d00840070707032020e0742ca000051080b0b810049e6a009040c11073b0240a0403a020e0122ca001573881f03700289c02016180c03838202301000360c420642e0002408381c0b870340c2e03828200f05a801c010601a0c0e0120ca001273b007470200e0c0e03038c00f03c000aca600400f000542a000c81c000b0621018140e0282d800193c001d860301a06c002b04180b070800b27270080c0402d181c04f31081d01020059e6c0352c9c0b830080b2a2602d8a0005d040402408100d4b40030020e00000000d03818218b800380210068182002030381c0b81026140208c28140b8083824060402d1e0c05804180560840048104036170e0402dc00d05940190b870481c0e070040411671301f0b700481e0206c04000085c0825038000e168200d9d400d008381a0b08027164206404180ca59801e01000059e0c03c1c1c0ca3b00090f45034065002b04080b93830048728034160e02c9c5806a184012460502e0c2e05d840001208080f0f0602b9442030381c0bb38b0050100032020000b3dc002638400701000080e4a00a38d40ac30380a8b860049ce603c3c0c0e238101b01080378c060702e0006818381a0102015168002da8840c808400b41000041ee60972cc01183028098100034020005504000003010220f70030020007428840bb51b01d0a0700f0c0403d3c0407870300b07060051ce00412cc00491108128a2101595000602e1c0d03038024b750221c020362d8001770b01c071602517020881dc006a5238250b80038150207408840c008301605060320208007180c0f85380168f05030d500061a9800b85c380707080101c0a0670cc01085c08028f0202c16ec0370d0003850080b610802b8c4205c04180923038028e0201b960a02c18100bb302013010102c1c4c05804140d01840170a81032970c02dae08090083809cb4203214c00681ca00a85c08034b8104394e008c288406a38401947700041e460680c1c0ba3038014a80000946004e1c0808808000b022601f1e2c0933c9c07870b0028e65040966004c290407808300b6102008948e0041c5c0c008401f0b8101a0e0e04b1c1c0b028380a0a400064e800361d001181108186b4001c040e00dae000d458180b02060059c4607a2cc00142818148f010199e200248418070308004010002e02100083c5801670181cc6020020e0c05a39c00b008380aca700280a0e0093dd40b27900160e2002017000903c1c0c0081803638003e0f000052e1c0e83040166f1001a820002caa000ba30100142210121500054042000a083003410801a021001118200f05c081c0610028020e0453c080c15b00170103016020e02a289805008380b472402c020405c18580b028280e4a20012020e0852cc00515980170b80030d70005d2e18049084012ca8002c1eec04808840ba5988160f260099442024ae0404270081a070701c0e0e0359d800195838088f160340e10020385801b1980028f7101617000651e0004b52080b06260059e4a009289404008301001000059ce403e38040b930a01d070800e020e0251c5c0545c00220f10025148202729000985c080f06030119e2a0802d40096080023062103c17000482e1c0985a0804c22102d1ee0038181c00a0840210b700074e60018040005830300a810002e0e0e01b180c04908182181000059c0a061acc010852080d430501e0a0c0083c4c0383040078b210491c0400a3dc80b27030092f87030d48003c3c1c01b1a802247200028c0e00518840925b8802ee0102ece0800504000263018194a46020170203c2dd80f01c000d0b0703f166003238400bb5c08050a21008021006a0c0c0c85a00174a010128e0c00894040190800000100012968007c2a040263108028e1301e1c6c009b85400a08201681000050a0405729800177908134a2101a8e0a0443808116793003ab3003054e0092389c04a51800b860302496a208838401127900024e4104316800593cc008828081546050130c0e00ab8840e81038084f010041c6c0203dc00565b80024e750260210008041804c3838240f0201e0a0e0093c040900840120621024148005f1c080e85938170b0102e0e2e0661cc00b07b28022f1502b04420342ca006c081001010702e4c240093894088080815ca40016170e04b2980070590017c712009164e0282e1c0127828024e06002948005d1818118301825010001a020e00dad400185a0010010800e0c0805c180c0780838186b86012170e02c041804a5c00200380
  | 10 => 0x73b0000b750001eea00028940047028000e750001c4a00039940007b900005020001e4a00039c80027180000e100018a00000000000478300001060000a0c0023c140005bb0000e26000020a000141c00473800001070009e40000388000378800001020000a0a0003dd80007930008f700009c0c00204000027980000f65
  | _ => 0

def FU : Nat → Nat
  | 0 => 2
  | 1 => 2
  | 2 => 2
  | 3 => 2
  | 4 => 2
  | 5 => 6
  | 6 => 9
  | 7 => 11
  | 8 => 12
  | 9 => 11
  | 10 => 7
  | 11 => 2
  | _ => 0

def grpG : List (List (Nat × Nat × Nat)) := [[(0x3030303000303030300000c0c0000000000000000000000c00000030030000000c0c0c0c000c0c0c0c0000303000000000000000000000030000000c00c0, 4, 0xffffccccccccffccccccccffff3333fffffffffffffffffffff33fffffccfccffffff33333333ff33333333fffccccfffffffffffffffffffffccffffff33f33f), (0x880000000088000000000000000104022020088022022022002002200080080022000000002200000000000000004100880802200880880880080088002002, 2, 0xffd57fffffffd57fffffffffffffffaebf55f5fd57f55f55f55ff5ff55ffd7fd7ff55ffffffff55fffffffffffffffebafd57d7f55fd57d57d57fd7fd57ff5ff5), (0x154004444444400444444445501111000500501400500500500110550004404405500111111110011111111154044440014014050014014014004415400110110, 1, 0xc03ff33333333ff3333333300fccccfff0ff0fc3ff0ff0ff0ffccf00fff33f33f00ffccccccccffccccccccc03f3333ffc3fc3f0ffc3fc3fc3ff33c03ffccfccf)], [(0xcccccccc00cccccccc000333300000000000000000000033000000cc0cc000003333333300333333330000cccc000000000000000000000cc00000330330, 2, 0xffffc00000003fc00000003fff0000fffffffffffffffffffff00fffffc03c03fffff00000000ff00000000fffc0003ffffffffffffffffffffc03fffff00f00f), (0x8954000000015400000000225000028a25525095425525525500522550014014225500000000550000000008940000a289549425509549549540148954005005, 1, 0xe6403fffffffc03ffffffff990ffff86190090e403900900900ff09900ffc3fc39900ffffffff00ffffffffe643fffe18640243900e402402403fc26403ff0ff0)], [(0x3030303000303030300000c0c0000000000000000000000c00000030030000000c0c0c0c000c0c0c0c0000303000000000000000000000030000000c00c0, 4, 0xffffccccccccffccccccccffff3333fffffffffffffffffffff33fffffccfccffffff33333333ff33333333fffccccfffffffffffffffffffffccffffff33f33f), (0x880000000088000000000000000104022020088022022022002002200080080022000000002200000000000000004100880802200880880880080088002002, 2, 0xffd57fffffffd57fffffffffffffffaebf55f5fd57f55f55f55ff5ff55ffd7fd7ff55ffffffff55fffffffffffffffebafd57d7f55fd57d57d57fd7fd57ff5ff5), (0x154004444444400444444445501111000500501400500500500110550004404405500111111110011111111154044440014014050014014014004415400110110, 1, 0xc03ff33333333ff3333333300fccccfff0ff0fc3ff0ff0ff0ffccf00fff33f33f00ffccccccccffccccccccc03f3333ffc3fc3f0ffc3fc3fc3ff33c03ffccfccf), (0xcccccccc00cccccccc000333300000000000000000000033000000cc0cc000003333333300333333330000cccc000000000000000000000cc00000330330, 2, 0xffffc00000003fc00000003fff0000fffffffffffffffffffff00fffffc03c03fffff00000000ff00000000fffc0003ffffffffffffffffffffc03fffff00f00f), (0x8954000000015400000000225000028a25525095425525525500522550014014225500000000550000000008940000a289549425509549549540148954005005, 1, 0xe6403fffffffc03ffffffff990ffff86190090e403900900900ff09900ffc3fc39900ffffffff00ffffffffe643fffe18640243900e402402403fc26403ff0ff0)], [(0xc0c0c0c000c0c0c0c0000303000000000000000000000030000000c00c0000003030303000303030300000c0c0000000000000000000000c00000030030, 4, 0xfffff33333333ff33333333fffccccfffffffffffffffffffffccffffff33f33fffffccccccccffccccccccffff3333fffffffffffffffffffff33fffffccfccf), (0x11111111001111111100004444000000000000000000000440000011011000000444444440044444444000111100000000000000000000011000000440440, 1, 0xffffccccccccffccccccccffff3333fffffffffffffffffffff33fffffccfccffffff33333333ff33333333fffccccfffffffffffffffffffffccffffff33f33f), (0xcc440000000044000000003300000082311310c443113113110013311000400433110000000011000000000cc00000208c44c43110c44c44c44004cc44001001, 2, 0xc02abfffffffeabffffffff00fffffd750aa0ac2ab0aa0aa0aaffa00aaffebfeb00aaffffffffaaffffffffc03fffff5d42a82b0aac2a82a82abfe802abffaffa)], [(0x1414141400141414140000505000000000000000000000050000001401400000050505050005050505000014140000000000000000000001400000050050, 5, 0xffffd6969696bfd6969696bfff5a5afffffffffffffffffffff5afffffd6bd6bfffff5a5a5a5aff5a5a5a5afffd696bffffffffffffffffffffd6bfffff5af5af), (0xcc00000000cc0000000000000001860330300cc0330330330030033000c00c0033000000003300000000000000006180cc0c03300cc0cc0cc00c00cc003003, 2, 0xffc03fffffffc03fffffffffffffff861f00f0fc03f00f00f00ff0ff00ffc3fc3ff00ffffffff00fffffffffffffffe187c03c3f00fc03c03c03fc3fc03ff0ff0), (0x44002828282800282828281100a0a0001001004001001001000a01100028028011000a0a0a0a000a0a0a0a0440282800040040100040040040028044000a00a0, 3, 0xd9bfe96969697fe9696969766fa5a5fff6ff6fdbff6ff6ff6ffa5f66ffe97e97f66ffa5a5a5a5ffa5a5a5a5d9be9697ffdbfdbf6ffdbfdbfdbfe97d9bffa5fa5f), (0x88000000000000000000002200000000200200800200200200000220000000002200000000000000000000088000000008008020008008008000008800000000, 1, 0xe67ffffffffffffffffffff99ffffffff9ff9fe7ff9ff9ff9fffff99fffffffff99ffffffffffffffffffffe67fffffffe7fe7f9ffe7fe7fe7ffffe67ffffffff)], [(0x3030303000303030300000c0c0000000000000000000000c00000030030000000c0c0c0c000c0c0c0c0000303000000000000000000000030000000c00c0, 4, 0xffffccccccccffccccccccffff3333fffffffffffffffffffff33fffffccfccffffff33333333ff33333333fffccccfffffffffffffffffffffccffffff33f33f), (0x880000000088000000000000000104022020088022022022002002200080080022000000002200000000000000004100880802200880880880080088002002, 2, 0xffd57fffffffd57fffffffffffffffaebf55f5fd57f55f55f55ff5ff55ffd7fd7ff55ffffffff55fffffffffffffffebafd57d7f55fd57d57d57fd7fd57ff5ff5), (0x154004444444400444444445501111000500501400500500500110550004404405500111111110011111111154044440014014050014014014004415400110110, 1, 0xc03ff33333333ff3333333300fccccfff0ff0fc3ff0ff0ff0ffccf00fff33f33f00ffccccccccffccccccccc03f3333ffc3fc3f0ffc3fc3fc3ff33c03ffccfccf), (0x404040400040404040000101000000000000000000000010000000400400000010101010001010101000004040000000000000000000000400000010010, 7, 0xffffdf9f9f9fbfdf9f9f9fbfff7e7efffffffffffffffffffff7efffffdfbdfbfffff7e7e7e7eff7e7e7e7efffdf9fbffffffffffffffffffffdfbfffff7ef7ef), (0x808080800080808080000202000000000000000000000020000000800800000020202020002020202000008080000000000000000000000800000020020, 5, 0xffffef6f6f6f7fef6f6f6f7fffbdbdfffffffffffffffffffffbdfffffef7ef7fffffbdbdbdbdffbdbdbdbdfffef6f7ffffffffffffffffffffef7fffffbdfbdf), (0x882020202088202020200050808104022020088022022022082002202082080022080808082208080808001420204100880802200880880882080088082082, 1, 0xffe679f9f9f9e679f9f9f9fff0e7e7cf3f99f9fe67f99f99f99e79ff99f9e79e7ff99e7e7e7e799e7e7e7e7ffc39f9f3cfe67e7f99fe67e67e679e7fe67e79e79), (0x44441010101044101010101100404082111110444111111111041111101041041111040404041104040404044010102084444411104444444441044444041041, 3, 0xd999b6f6f6f6d9b6f6f6f6f66fdbdbb6d66666d99b666666666db66666f6db6db6666dbdbdbdb66dbdbdbdbd9bf6f6edb59999b666d99999999b6d9999bdb6db6)], [(0x404040400040404040000101000000000000000000000010000000400400000010101010001010101000004040000000000000000000000400000010010, 7, 0xffffdf9f9f9fbfdf9f9f9fbfff7e7efffffffffffffffffffff7efffffdfbdfbfffff7e7e7e7eff7e7e7e7efffdf9fbffffffffffffffffffffdfbfffff7ef7ef), (0x808080800080808080000202000000000000000000000020000000800800000020202020002020202000008080000000000000000000000800000020020, 5, 0xffffef6f6f6f7fef6f6f6f7fffbdbdfffffffffffffffffffffbdfffffef7ef7fffffbdbdbdbdffbdbdbdbdfffef6f7ffffffffffffffffffffef7fffffbdfbdf), (0x882020202088202020200050808104022020088022022022082002202082080022080808082208080808001420204100880802200880880882080088082082, 1, 0xffe679f9f9f9e679f9f9f9fff0e7e7cf3f99f9fe67f99f99f99e79ff99f9e79e7ff99e7e7e7e799e7e7e7e7ffc39f9f3cfe67e7f99fe67e67e679e7fe67e79e79), (0x44441010101044101010101100404082111110444111111111041111101041041111040404041104040404044010102084444411104444444441044444041041, 3, 0xd999b6f6f6f6d9b6f6f6f6f66fdbdbb6d66666d99b666666666db66666f6db6db6666dbdbdbdb66dbdbdbdbd9bf6f6edb59999b666d99999999b6d9999bdb6db6)]]

theorem grpG_ok : grpG.all (fun g => g.all (okMove 258)) = true := by decide +kernel

def St : Nat → Nat → Nat → List Nat
  | 0, _, _ => xsG
  | d + 1, s, j =>
    let e := fld (PT s) 27 j
    if e = 0 then xsG else
      let r := mv (mask 258) (e % 8192) (St d (s + 1) (e / 65536))
      let gi := e / 8192 % 8
      if gi = 0 then r else r.map (mvs (grpG.getD (gi - 1) []))

def S (s j : Nat) : List Nat := St (11 - s) s j

def idx (s : Nat) (zs : List Nat) : Nat := bsr (HT s) 32 (hk zs) (FU s) 0 (NN s)

def ori (zs : List Nat) : List Nat := grpG.foldl (pickMin zs) zs

theorem ori_ok {u ys} (h : NatRun (mask 258) (goal 258) u ys) :
    NatRun (mask 258) (goal 258) u (ori ys) := pick_run h grpG ys grpG_ok h

def poolG : List Nat := [0x3c88a359c0415bd, 0x3cc8c351be411bb, 0x3cc8d341ba409bf, 0x3c08f34dbd40dc0, 0x3c491345bb409be, 0x3b8ea1f9e87958f, 0x390740bd2f765d4, 0x398750c52e75dd2, 0x380720cd2f761d5, 0x384720c92d751d9, 0x2a0a01695654112, 0x2a89f1695754514, 0x3c0ab1351152939, 0x3c4a91351052d38, 0xb47f26dad8015f, 0xb080269ab7fd5e]

def Z (s : Nat) := bar 258 S NN idx ori poolG s

theorem h11y0 : span (Z 11) 1 0 = true := by decide +kernel
theorem z11 : span (Z 11) 1 0 = true := h11y0
theorem h10y0 : span (Z 10) 12 0 = true := by decide +kernel
theorem h10y1 : span (Z 10) 12 12 = true := by decide +kernel
theorem h10y2 : span (Z 10) 12 24 = true := by decide +kernel
theorem h10y3 : span (Z 10) 2 36 = true := by decide +kernel
theorem z10 : span (Z 10) 38 0 = true := (@span_join (Z 10) 24 0 14 (@span_join (Z 10) 12 0 12 h10y0 h10y1) (@span_join (Z 10) 12 24 2 h10y2 h10y3))
theorem h9y0 : span (Z 9) 12 0 = true := by decide +kernel
theorem h9y1 : span (Z 9) 12 12 = true := by decide +kernel
theorem h9y2 : span (Z 9) 12 24 = true := by decide +kernel
theorem h9y3 : span (Z 9) 12 36 = true := by decide +kernel
theorem h9y4 : span (Z 9) 12 48 = true := by decide +kernel
theorem h9y5 : span (Z 9) 12 60 = true := by decide +kernel
theorem h9y6 : span (Z 9) 12 72 = true := by decide +kernel
theorem h9y7 : span (Z 9) 12 84 = true := by decide +kernel
theorem h9y8 : span (Z 9) 12 96 = true := by decide +kernel
theorem h9y9 : span (Z 9) 12 108 = true := by decide +kernel
theorem h9y10 : span (Z 9) 12 120 = true := by decide +kernel
theorem h9y11 : span (Z 9) 12 132 = true := by decide +kernel
theorem h9y12 : span (Z 9) 12 144 = true := by decide +kernel
theorem h9y13 : span (Z 9) 12 156 = true := by decide +kernel
theorem h9y14 : span (Z 9) 12 168 = true := by decide +kernel
theorem h9y15 : span (Z 9) 12 180 = true := by decide +kernel
theorem h9y16 : span (Z 9) 12 192 = true := by decide +kernel
theorem h9y17 : span (Z 9) 12 204 = true := by decide +kernel
theorem h9y18 : span (Z 9) 12 216 = true := by decide +kernel
theorem h9y19 : span (Z 9) 12 228 = true := by decide +kernel
theorem h9y20 : span (Z 9) 12 240 = true := by decide +kernel
theorem h9y21 : span (Z 9) 12 252 = true := by decide +kernel
theorem h9y22 : span (Z 9) 12 264 = true := by decide +kernel
theorem h9y23 : span (Z 9) 12 276 = true := by decide +kernel
theorem h9y24 : span (Z 9) 12 288 = true := by decide +kernel
theorem h9y25 : span (Z 9) 12 300 = true := by decide +kernel
theorem h9y26 : span (Z 9) 12 312 = true := by decide +kernel
theorem h9y27 : span (Z 9) 12 324 = true := by decide +kernel
theorem h9y28 : span (Z 9) 12 336 = true := by decide +kernel
theorem h9y29 : span (Z 9) 12 348 = true := by decide +kernel
theorem h9y30 : span (Z 9) 12 360 = true := by decide +kernel
theorem h9y31 : span (Z 9) 12 372 = true := by decide +kernel
theorem h9y32 : span (Z 9) 12 384 = true := by decide +kernel
theorem h9y33 : span (Z 9) 12 396 = true := by decide +kernel
theorem h9y34 : span (Z 9) 12 408 = true := by decide +kernel
theorem h9y35 : span (Z 9) 12 420 = true := by decide +kernel
theorem h9y36 : span (Z 9) 12 432 = true := by decide +kernel
theorem h9y37 : span (Z 9) 12 444 = true := by decide +kernel
theorem h9y38 : span (Z 9) 12 456 = true := by decide +kernel
theorem h9y39 : span (Z 9) 12 468 = true := by decide +kernel
theorem h9y40 : span (Z 9) 12 480 = true := by decide +kernel
theorem h9y41 : span (Z 9) 12 492 = true := by decide +kernel
theorem h9y42 : span (Z 9) 12 504 = true := by decide +kernel
theorem h9y43 : span (Z 9) 12 516 = true := by decide +kernel
theorem h9y44 : span (Z 9) 12 528 = true := by decide +kernel
theorem h9y45 : span (Z 9) 12 540 = true := by decide +kernel
theorem h9y46 : span (Z 9) 12 552 = true := by decide +kernel
theorem h9y47 : span (Z 9) 12 564 = true := by decide +kernel
theorem h9y48 : span (Z 9) 12 576 = true := by decide +kernel
theorem h9y49 : span (Z 9) 12 588 = true := by decide +kernel
theorem h9y50 : span (Z 9) 12 600 = true := by decide +kernel
theorem h9y51 : span (Z 9) 12 612 = true := by decide +kernel
theorem h9y52 : span (Z 9) 12 624 = true := by decide +kernel
theorem h9y53 : span (Z 9) 12 636 = true := by decide +kernel
theorem h9y54 : span (Z 9) 12 648 = true := by decide +kernel
theorem h9y55 : span (Z 9) 12 660 = true := by decide +kernel
theorem h9y56 : span (Z 9) 12 672 = true := by decide +kernel
theorem h9y57 : span (Z 9) 12 684 = true := by decide +kernel
theorem h9y58 : span (Z 9) 12 696 = true := by decide +kernel
theorem h9y59 : span (Z 9) 12 708 = true := by decide +kernel
theorem h9y60 : span (Z 9) 12 720 = true := by decide +kernel
theorem h9y61 : span (Z 9) 7 732 = true := by decide +kernel
theorem z9 : span (Z 9) 739 0 = true := (@span_join (Z 9) 372 0 367 (@span_join (Z 9) 180 0 192 (@span_join (Z 9) 84 0 96 (@span_join (Z 9) 36 0 48 (@span_join (Z 9) 12 0 24 h9y0 (@span_join (Z 9) 12 12 12 h9y1 h9y2)) (@span_join (Z 9) 24 36 24 (@span_join (Z 9) 12 36 12 h9y3 h9y4) (@span_join (Z 9) 12 60 12 h9y5 h9y6))) (@span_join (Z 9) 48 84 48 (@span_join (Z 9) 24 84 24 (@span_join (Z 9) 12 84 12 h9y7 h9y8) (@span_join (Z 9) 12 108 12 h9y9 h9y10)) (@span_join (Z 9) 24 132 24 (@span_join (Z 9) 12 132 12 h9y11 h9y12) (@span_join (Z 9) 12 156 12 h9y13 h9y14)))) (@span_join (Z 9) 96 180 96 (@span_join (Z 9) 48 180 48 (@span_join (Z 9) 24 180 24 (@span_join (Z 9) 12 180 12 h9y15 h9y16) (@span_join (Z 9) 12 204 12 h9y17 h9y18)) (@span_join (Z 9) 24 228 24 (@span_join (Z 9) 12 228 12 h9y19 h9y20) (@span_join (Z 9) 12 252 12 h9y21 h9y22))) (@span_join (Z 9) 48 276 48 (@span_join (Z 9) 24 276 24 (@span_join (Z 9) 12 276 12 h9y23 h9y24) (@span_join (Z 9) 12 300 12 h9y25 h9y26)) (@span_join (Z 9) 24 324 24 (@span_join (Z 9) 12 324 12 h9y27 h9y28) (@span_join (Z 9) 12 348 12 h9y29 h9y30))))) (@span_join (Z 9) 180 372 187 (@span_join (Z 9) 84 372 96 (@span_join (Z 9) 36 372 48 (@span_join (Z 9) 12 372 24 h9y31 (@span_join (Z 9) 12 384 12 h9y32 h9y33)) (@span_join (Z 9) 24 408 24 (@span_join (Z 9) 12 408 12 h9y34 h9y35) (@span_join (Z 9) 12 432 12 h9y36 h9y37))) (@span_join (Z 9) 48 456 48 (@span_join (Z 9) 24 456 24 (@span_join (Z 9) 12 456 12 h9y38 h9y39) (@span_join (Z 9) 12 480 12 h9y40 h9y41)) (@span_join (Z 9) 24 504 24 (@span_join (Z 9) 12 504 12 h9y42 h9y43) (@span_join (Z 9) 12 528 12 h9y44 h9y45)))) (@span_join (Z 9) 96 552 91 (@span_join (Z 9) 48 552 48 (@span_join (Z 9) 24 552 24 (@span_join (Z 9) 12 552 12 h9y46 h9y47) (@span_join (Z 9) 12 576 12 h9y48 h9y49)) (@span_join (Z 9) 24 600 24 (@span_join (Z 9) 12 600 12 h9y50 h9y51) (@span_join (Z 9) 12 624 12 h9y52 h9y53))) (@span_join (Z 9) 48 648 43 (@span_join (Z 9) 24 648 24 (@span_join (Z 9) 12 648 12 h9y54 h9y55) (@span_join (Z 9) 12 672 12 h9y56 h9y57)) (@span_join (Z 9) 24 696 19 (@span_join (Z 9) 12 696 12 h9y58 h9y59) (@span_join (Z 9) 12 720 7 h9y60 h9y61))))))
theorem h8y0 : span (Z 8) 12 0 = true := by decide +kernel
theorem h8y1 : span (Z 8) 12 12 = true := by decide +kernel
theorem h8y2 : span (Z 8) 12 24 = true := by decide +kernel
theorem h8y3 : span (Z 8) 12 36 = true := by decide +kernel
theorem h8y4 : span (Z 8) 12 48 = true := by decide +kernel
theorem h8y5 : span (Z 8) 12 60 = true := by decide +kernel
theorem h8y6 : span (Z 8) 12 72 = true := by decide +kernel
theorem h8y7 : span (Z 8) 12 84 = true := by decide +kernel
theorem h8y8 : span (Z 8) 12 96 = true := by decide +kernel
theorem h8y9 : span (Z 8) 12 108 = true := by decide +kernel
theorem h8y10 : span (Z 8) 12 120 = true := by decide +kernel
theorem h8y11 : span (Z 8) 12 132 = true := by decide +kernel
theorem h8y12 : span (Z 8) 12 144 = true := by decide +kernel
theorem h8y13 : span (Z 8) 12 156 = true := by decide +kernel
theorem h8y14 : span (Z 8) 12 168 = true := by decide +kernel
theorem h8y15 : span (Z 8) 12 180 = true := by decide +kernel
theorem h8y16 : span (Z 8) 12 192 = true := by decide +kernel
theorem h8y17 : span (Z 8) 12 204 = true := by decide +kernel
theorem h8y18 : span (Z 8) 12 216 = true := by decide +kernel
theorem h8y19 : span (Z 8) 12 228 = true := by decide +kernel
theorem h8y20 : span (Z 8) 12 240 = true := by decide +kernel
theorem h8y21 : span (Z 8) 12 252 = true := by decide +kernel
theorem h8y22 : span (Z 8) 12 264 = true := by decide +kernel
theorem h8y23 : span (Z 8) 12 276 = true := by decide +kernel
theorem h8y24 : span (Z 8) 12 288 = true := by decide +kernel
theorem h8y25 : span (Z 8) 12 300 = true := by decide +kernel
theorem h8y26 : span (Z 8) 12 312 = true := by decide +kernel
theorem h8y27 : span (Z 8) 12 324 = true := by decide +kernel
theorem h8y28 : span (Z 8) 12 336 = true := by decide +kernel
theorem h8y29 : span (Z 8) 12 348 = true := by decide +kernel
theorem h8y30 : span (Z 8) 12 360 = true := by decide +kernel
theorem h8y31 : span (Z 8) 12 372 = true := by decide +kernel
theorem h8y32 : span (Z 8) 12 384 = true := by decide +kernel
theorem h8y33 : span (Z 8) 12 396 = true := by decide +kernel
theorem h8y34 : span (Z 8) 12 408 = true := by decide +kernel
theorem h8y35 : span (Z 8) 12 420 = true := by decide +kernel
theorem h8y36 : span (Z 8) 12 432 = true := by decide +kernel
theorem h8y37 : span (Z 8) 12 444 = true := by decide +kernel
theorem h8y38 : span (Z 8) 12 456 = true := by decide +kernel
theorem h8y39 : span (Z 8) 12 468 = true := by decide +kernel
theorem h8y40 : span (Z 8) 12 480 = true := by decide +kernel
theorem h8y41 : span (Z 8) 12 492 = true := by decide +kernel
theorem h8y42 : span (Z 8) 12 504 = true := by decide +kernel
theorem h8y43 : span (Z 8) 12 516 = true := by decide +kernel
theorem h8y44 : span (Z 8) 12 528 = true := by decide +kernel
theorem h8y45 : span (Z 8) 12 540 = true := by decide +kernel
theorem h8y46 : span (Z 8) 12 552 = true := by decide +kernel
theorem h8y47 : span (Z 8) 12 564 = true := by decide +kernel
theorem h8y48 : span (Z 8) 12 576 = true := by decide +kernel
theorem h8y49 : span (Z 8) 12 588 = true := by decide +kernel
theorem h8y50 : span (Z 8) 12 600 = true := by decide +kernel
theorem h8y51 : span (Z 8) 12 612 = true := by decide +kernel
theorem h8y52 : span (Z 8) 12 624 = true := by decide +kernel
theorem h8y53 : span (Z 8) 12 636 = true := by decide +kernel
theorem h8y54 : span (Z 8) 12 648 = true := by decide +kernel
theorem h8y55 : span (Z 8) 12 660 = true := by decide +kernel
theorem h8y56 : span (Z 8) 12 672 = true := by decide +kernel
theorem h8y57 : span (Z 8) 12 684 = true := by decide +kernel
theorem h8y58 : span (Z 8) 12 696 = true := by decide +kernel
theorem h8y59 : span (Z 8) 12 708 = true := by decide +kernel
theorem h8y60 : span (Z 8) 12 720 = true := by decide +kernel
theorem h8y61 : span (Z 8) 12 732 = true := by decide +kernel
theorem h8y62 : span (Z 8) 12 744 = true := by decide +kernel
theorem h8y63 : span (Z 8) 12 756 = true := by decide +kernel
theorem h8y64 : span (Z 8) 12 768 = true := by decide +kernel
theorem h8y65 : span (Z 8) 12 780 = true := by decide +kernel
theorem h8y66 : span (Z 8) 12 792 = true := by decide +kernel
theorem h8y67 : span (Z 8) 12 804 = true := by decide +kernel
theorem h8y68 : span (Z 8) 12 816 = true := by decide +kernel
theorem h8y69 : span (Z 8) 12 828 = true := by decide +kernel
theorem h8y70 : span (Z 8) 12 840 = true := by decide +kernel
theorem h8y71 : span (Z 8) 12 852 = true := by decide +kernel
theorem h8y72 : span (Z 8) 12 864 = true := by decide +kernel
theorem h8y73 : span (Z 8) 12 876 = true := by decide +kernel
theorem h8y74 : span (Z 8) 12 888 = true := by decide +kernel
theorem h8y75 : span (Z 8) 12 900 = true := by decide +kernel
theorem h8y76 : span (Z 8) 12 912 = true := by decide +kernel
theorem h8y77 : span (Z 8) 12 924 = true := by decide +kernel
theorem h8y78 : span (Z 8) 12 936 = true := by decide +kernel
theorem h8y79 : span (Z 8) 12 948 = true := by decide +kernel
theorem h8y80 : span (Z 8) 12 960 = true := by decide +kernel
theorem h8y81 : span (Z 8) 12 972 = true := by decide +kernel
theorem h8y82 : span (Z 8) 12 984 = true := by decide +kernel
theorem h8y83 : span (Z 8) 12 996 = true := by decide +kernel
theorem h8y84 : span (Z 8) 12 1008 = true := by decide +kernel
theorem h8y85 : span (Z 8) 12 1020 = true := by decide +kernel
theorem h8y86 : span (Z 8) 12 1032 = true := by decide +kernel
theorem h8y87 : span (Z 8) 12 1044 = true := by decide +kernel
theorem h8y88 : span (Z 8) 12 1056 = true := by decide +kernel
theorem h8y89 : span (Z 8) 12 1068 = true := by decide +kernel
theorem h8y90 : span (Z 8) 12 1080 = true := by decide +kernel
theorem h8y91 : span (Z 8) 12 1092 = true := by decide +kernel
theorem h8y92 : span (Z 8) 12 1104 = true := by decide +kernel
theorem h8y93 : span (Z 8) 12 1116 = true := by decide +kernel
theorem h8y94 : span (Z 8) 12 1128 = true := by decide +kernel
theorem h8y95 : span (Z 8) 12 1140 = true := by decide +kernel
theorem h8y96 : span (Z 8) 12 1152 = true := by decide +kernel
theorem h8y97 : span (Z 8) 12 1164 = true := by decide +kernel
theorem h8y98 : span (Z 8) 12 1176 = true := by decide +kernel
theorem h8y99 : span (Z 8) 12 1188 = true := by decide +kernel
theorem h8y100 : span (Z 8) 12 1200 = true := by decide +kernel
theorem h8y101 : span (Z 8) 12 1212 = true := by decide +kernel
theorem h8y102 : span (Z 8) 12 1224 = true := by decide +kernel
theorem h8y103 : span (Z 8) 12 1236 = true := by decide +kernel
theorem h8y104 : span (Z 8) 12 1248 = true := by decide +kernel
theorem h8y105 : span (Z 8) 12 1260 = true := by decide +kernel
theorem h8y106 : span (Z 8) 12 1272 = true := by decide +kernel
theorem h8y107 : span (Z 8) 9 1284 = true := by decide +kernel
theorem z8 : span (Z 8) 1293 0 = true := (@span_join (Z 8) 648 0 645 (@span_join (Z 8) 324 0 324 (@span_join (Z 8) 156 0 168 (@span_join (Z 8) 72 0 84 (@span_join (Z 8) 36 0 36 (@span_join (Z 8) 12 0 24 h8y0 (@span_join (Z 8) 12 12 12 h8y1 h8y2)) (@span_join (Z 8) 12 36 24 h8y3 (@span_join (Z 8) 12 48 12 h8y4 h8y5))) (@span_join (Z 8) 36 72 48 (@span_join (Z 8) 12 72 24 h8y6 (@span_join (Z 8) 12 84 12 h8y7 h8y8)) (@span_join (Z 8) 24 108 24 (@span_join (Z 8) 12 108 12 h8y9 h8y10) (@span_join (Z 8) 12 132 12 h8y11 h8y12)))) (@span_join (Z 8) 84 156 84 (@span_join (Z 8) 36 156 48 (@span_join (Z 8) 12 156 24 h8y13 (@span_join (Z 8) 12 168 12 h8y14 h8y15)) (@span_join (Z 8) 24 192 24 (@span_join (Z 8) 12 192 12 h8y16 h8y17) (@span_join (Z 8) 12 216 12 h8y18 h8y19))) (@span_join (Z 8) 36 240 48 (@span_join (Z 8) 12 240 24 h8y20 (@span_join (Z 8) 12 252 12 h8y21 h8y22)) (@span_join (Z 8) 24 276 24 (@span_join (Z 8) 12 276 12 h8y23 h8y24) (@span_join (Z 8) 12 300 12 h8y25 h8y26))))) (@span_join (Z 8) 156 324 168 (@span_join (Z 8) 72 324 84 (@span_join (Z 8) 36 324 36 (@span_join (Z 8) 12 324 24 h8y27 (@span_join (Z 8) 12 336 12 h8y28 h8y29)) (@span_join (Z 8) 12 360 24 h8y30 (@span_join (Z 8) 12 372 12 h8y31 h8y32))) (@span_join (Z 8) 36 396 48 (@span_join (Z 8) 12 396 24 h8y33 (@span_join (Z 8) 12 408 12 h8y34 h8y35)) (@span_join (Z 8) 24 432 24 (@span_join (Z 8) 12 432 12 h8y36 h8y37) (@span_join (Z 8) 12 456 12 h8y38 h8y39)))) (@span_join (Z 8) 84 480 84 (@span_join (Z 8) 36 480 48 (@span_join (Z 8) 12 480 24 h8y40 (@span_join (Z 8) 12 492 12 h8y41 h8y42)) (@span_join (Z 8) 24 516 24 (@span_join (Z 8) 12 516 12 h8y43 h8y44) (@span_join (Z 8) 12 540 12 h8y45 h8y46))) (@span_join (Z 8) 36 564 48 (@span_join (Z 8) 12 564 24 h8y47 (@span_join (Z 8) 12 576 12 h8y48 h8y49)) (@span_join (Z 8) 24 600 24 (@span_join (Z 8) 12 600 12 h8y50 h8y51) (@span_join (Z 8) 12 624 12 h8y52 h8y53)))))) (@span_join (Z 8) 324 648 321 (@span_join (Z 8) 156 648 168 (@span_join (Z 8) 72 648 84 (@span_join (Z 8) 36 648 36 (@span_join (Z 8) 12 648 24 h8y54 (@span_join (Z 8) 12 660 12 h8y55 h8y56)) (@span_join (Z 8) 12 684 24 h8y57 (@span_join (Z 8) 12 696 12 h8y58 h8y59))) (@span_join (Z 8) 36 720 48 (@span_join (Z 8) 12 720 24 h8y60 (@span_join (Z 8) 12 732 12 h8y61 h8y62)) (@span_join (Z 8) 24 756 24 (@span_join (Z 8) 12 756 12 h8y63 h8y64) (@span_join (Z 8) 12 780 12 h8y65 h8y66)))) (@span_join (Z 8) 84 804 84 (@span_join (Z 8) 36 804 48 (@span_join (Z 8) 12 804 24 h8y67 (@span_join (Z 8) 12 816 12 h8y68 h8y69)) (@span_join (Z 8) 24 840 24 (@span_join (Z 8) 12 840 12 h8y70 h8y71) (@span_join (Z 8) 12 864 12 h8y72 h8y73))) (@span_join (Z 8) 36 888 48 (@span_join (Z 8) 12 888 24 h8y74 (@span_join (Z 8) 12 900 12 h8y75 h8y76)) (@span_join (Z 8) 24 924 24 (@span_join (Z 8) 12 924 12 h8y77 h8y78) (@span_join (Z 8) 12 948 12 h8y79 h8y80))))) (@span_join (Z 8) 156 972 165 (@span_join (Z 8) 72 972 84 (@span_join (Z 8) 36 972 36 (@span_join (Z 8) 12 972 24 h8y81 (@span_join (Z 8) 12 984 12 h8y82 h8y83)) (@span_join (Z 8) 12 1008 24 h8y84 (@span_join (Z 8) 12 1020 12 h8y85 h8y86))) (@span_join (Z 8) 36 1044 48 (@span_join (Z 8) 12 1044 24 h8y87 (@span_join (Z 8) 12 1056 12 h8y88 h8y89)) (@span_join (Z 8) 24 1080 24 (@span_join (Z 8) 12 1080 12 h8y90 h8y91) (@span_join (Z 8) 12 1104 12 h8y92 h8y93)))) (@span_join (Z 8) 84 1128 81 (@span_join (Z 8) 36 1128 48 (@span_join (Z 8) 12 1128 24 h8y94 (@span_join (Z 8) 12 1140 12 h8y95 h8y96)) (@span_join (Z 8) 24 1164 24 (@span_join (Z 8) 12 1164 12 h8y97 h8y98) (@span_join (Z 8) 12 1188 12 h8y99 h8y100))) (@span_join (Z 8) 36 1212 45 (@span_join (Z 8) 12 1212 24 h8y101 (@span_join (Z 8) 12 1224 12 h8y102 h8y103)) (@span_join (Z 8) 24 1248 21 (@span_join (Z 8) 12 1248 12 h8y104 h8y105) (@span_join (Z 8) 12 1272 9 h8y106 h8y107)))))))
theorem h7y0 : span (Z 7) 12 0 = true := by decide +kernel
theorem h7y1 : span (Z 7) 12 12 = true := by decide +kernel
theorem h7y2 : span (Z 7) 12 24 = true := by decide +kernel
theorem h7y3 : span (Z 7) 12 36 = true := by decide +kernel
theorem h7y4 : span (Z 7) 12 48 = true := by decide +kernel
theorem h7y5 : span (Z 7) 12 60 = true := by decide +kernel
theorem h7y6 : span (Z 7) 12 72 = true := by decide +kernel
theorem h7y7 : span (Z 7) 12 84 = true := by decide +kernel
theorem h7y8 : span (Z 7) 12 96 = true := by decide +kernel
theorem h7y9 : span (Z 7) 12 108 = true := by decide +kernel
theorem h7y10 : span (Z 7) 12 120 = true := by decide +kernel
theorem h7y11 : span (Z 7) 12 132 = true := by decide +kernel
theorem h7y12 : span (Z 7) 12 144 = true := by decide +kernel
theorem h7y13 : span (Z 7) 12 156 = true := by decide +kernel
theorem h7y14 : span (Z 7) 12 168 = true := by decide +kernel
theorem h7y15 : span (Z 7) 12 180 = true := by decide +kernel
theorem h7y16 : span (Z 7) 12 192 = true := by decide +kernel
theorem h7y17 : span (Z 7) 12 204 = true := by decide +kernel
theorem h7y18 : span (Z 7) 12 216 = true := by decide +kernel
theorem h7y19 : span (Z 7) 12 228 = true := by decide +kernel
theorem h7y20 : span (Z 7) 12 240 = true := by decide +kernel
theorem h7y21 : span (Z 7) 12 252 = true := by decide +kernel
theorem h7y22 : span (Z 7) 12 264 = true := by decide +kernel
theorem h7y23 : span (Z 7) 12 276 = true := by decide +kernel
theorem h7y24 : span (Z 7) 12 288 = true := by decide +kernel
theorem h7y25 : span (Z 7) 12 300 = true := by decide +kernel
theorem h7y26 : span (Z 7) 12 312 = true := by decide +kernel
theorem h7y27 : span (Z 7) 12 324 = true := by decide +kernel
theorem h7y28 : span (Z 7) 12 336 = true := by decide +kernel
theorem h7y29 : span (Z 7) 12 348 = true := by decide +kernel
theorem h7y30 : span (Z 7) 12 360 = true := by decide +kernel
theorem h7y31 : span (Z 7) 12 372 = true := by decide +kernel
theorem h7y32 : span (Z 7) 12 384 = true := by decide +kernel
theorem h7y33 : span (Z 7) 12 396 = true := by decide +kernel
theorem h7y34 : span (Z 7) 12 408 = true := by decide +kernel
theorem h7y35 : span (Z 7) 12 420 = true := by decide +kernel
theorem h7y36 : span (Z 7) 12 432 = true := by decide +kernel
theorem h7y37 : span (Z 7) 12 444 = true := by decide +kernel
theorem h7y38 : span (Z 7) 12 456 = true := by decide +kernel
theorem h7y39 : span (Z 7) 12 468 = true := by decide +kernel
theorem h7y40 : span (Z 7) 12 480 = true := by decide +kernel
theorem h7y41 : span (Z 7) 12 492 = true := by decide +kernel
theorem h7y42 : span (Z 7) 12 504 = true := by decide +kernel
theorem h7y43 : span (Z 7) 12 516 = true := by decide +kernel
theorem h7y44 : span (Z 7) 12 528 = true := by decide +kernel
theorem h7y45 : span (Z 7) 12 540 = true := by decide +kernel
theorem h7y46 : span (Z 7) 12 552 = true := by decide +kernel
theorem h7y47 : span (Z 7) 12 564 = true := by decide +kernel
theorem h7y48 : span (Z 7) 12 576 = true := by decide +kernel
theorem h7y49 : span (Z 7) 12 588 = true := by decide +kernel
theorem h7y50 : span (Z 7) 2 600 = true := by decide +kernel
theorem z7 : span (Z 7) 602 0 = true := (@span_join (Z 7) 300 0 302 (@span_join (Z 7) 144 0 156 (@span_join (Z 7) 72 0 72 (@span_join (Z 7) 36 0 36 (@span_join (Z 7) 12 0 24 h7y0 (@span_join (Z 7) 12 12 12 h7y1 h7y2)) (@span_join (Z 7) 12 36 24 h7y3 (@span_join (Z 7) 12 48 12 h7y4 h7y5))) (@span_join (Z 7) 36 72 36 (@span_join (Z 7) 12 72 24 h7y6 (@span_join (Z 7) 12 84 12 h7y7 h7y8)) (@span_join (Z 7) 12 108 24 h7y9 (@span_join (Z 7) 12 120 12 h7y10 h7y11)))) (@span_join (Z 7) 72 144 84 (@span_join (Z 7) 36 144 36 (@span_join (Z 7) 12 144 24 h7y12 (@span_join (Z 7) 12 156 12 h7y13 h7y14)) (@span_join (Z 7) 12 180 24 h7y15 (@span_join (Z 7) 12 192 12 h7y16 h7y17))) (@span_join (Z 7) 36 216 48 (@span_join (Z 7) 12 216 24 h7y18 (@span_join (Z 7) 12 228 12 h7y19 h7y20)) (@span_join (Z 7) 24 252 24 (@span_join (Z 7) 12 252 12 h7y21 h7y22) (@span_join (Z 7) 12 276 12 h7y23 h7y24))))) (@span_join (Z 7) 156 300 146 (@span_join (Z 7) 72 300 84 (@span_join (Z 7) 36 300 36 (@span_join (Z 7) 12 300 24 h7y25 (@span_join (Z 7) 12 312 12 h7y26 h7y27)) (@span_join (Z 7) 12 336 24 h7y28 (@span_join (Z 7) 12 348 12 h7y29 h7y30))) (@span_join (Z 7) 36 372 48 (@span_join (Z 7) 12 372 24 h7y31 (@span_join (Z 7) 12 384 12 h7y32 h7y33)) (@span_join (Z 7) 24 408 24 (@span_join (Z 7) 12 408 12 h7y34 h7y35) (@span_join (Z 7) 12 432 12 h7y36 h7y37)))) (@span_join (Z 7) 72 456 74 (@span_join (Z 7) 36 456 36 (@span_join (Z 7) 12 456 24 h7y38 (@span_join (Z 7) 12 468 12 h7y39 h7y40)) (@span_join (Z 7) 12 492 24 h7y41 (@span_join (Z 7) 12 504 12 h7y42 h7y43))) (@span_join (Z 7) 36 528 38 (@span_join (Z 7) 12 528 24 h7y44 (@span_join (Z 7) 12 540 12 h7y45 h7y46)) (@span_join (Z 7) 24 564 14 (@span_join (Z 7) 12 564 12 h7y47 h7y48) (@span_join (Z 7) 12 588 2 h7y49 h7y50))))))
theorem h6y0 : span (Z 6) 12 0 = true := by decide +kernel
theorem h6y1 : span (Z 6) 12 12 = true := by decide +kernel
theorem h6y2 : span (Z 6) 12 24 = true := by decide +kernel
theorem h6y3 : span (Z 6) 12 36 = true := by decide +kernel
theorem h6y4 : span (Z 6) 12 48 = true := by decide +kernel
theorem h6y5 : span (Z 6) 12 60 = true := by decide +kernel
theorem h6y6 : span (Z 6) 12 72 = true := by decide +kernel
theorem h6y7 : span (Z 6) 12 84 = true := by decide +kernel
theorem h6y8 : span (Z 6) 12 96 = true := by decide +kernel
theorem h6y9 : span (Z 6) 12 108 = true := by decide +kernel
theorem h6y10 : span (Z 6) 12 120 = true := by decide +kernel
theorem h6y11 : span (Z 6) 12 132 = true := by decide +kernel
theorem h6y12 : span (Z 6) 12 144 = true := by decide +kernel
theorem h6y13 : span (Z 6) 8 156 = true := by decide +kernel
theorem z6 : span (Z 6) 164 0 = true := (@span_join (Z 6) 84 0 80 (@span_join (Z 6) 36 0 48 (@span_join (Z 6) 12 0 24 h6y0 (@span_join (Z 6) 12 12 12 h6y1 h6y2)) (@span_join (Z 6) 24 36 24 (@span_join (Z 6) 12 36 12 h6y3 h6y4) (@span_join (Z 6) 12 60 12 h6y5 h6y6))) (@span_join (Z 6) 36 84 44 (@span_join (Z 6) 12 84 24 h6y7 (@span_join (Z 6) 12 96 12 h6y8 h6y9)) (@span_join (Z 6) 24 120 20 (@span_join (Z 6) 12 120 12 h6y10 h6y11) (@span_join (Z 6) 12 144 8 h6y12 h6y13))))
theorem h5y0 : span (Z 5) 12 0 = true := by decide +kernel
theorem h5y1 : span (Z 5) 12 12 = true := by decide +kernel
theorem h5y2 : span (Z 5) 2 24 = true := by decide +kernel
theorem z5 : span (Z 5) 26 0 = true := (@span_join (Z 5) 12 0 14 h5y0 (@span_join (Z 5) 12 12 2 h5y1 h5y2))
theorem z4 : span (Z 4) 0 0 = true := rfl
theorem z3 : span (Z 3) 0 0 = true := rfl
theorem z2 : span (Z 2) 0 0 = true := rfl
theorem z1 : span (Z 1) 0 0 = true := rfl
theorem z0 : span (Z 0) 0 0 = true := rfl

theorem checked (s : Nat) (hs : s ≤ 11) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => span_ok z0 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z1 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z2 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z3 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z4 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z5 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z6 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z7 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z8 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z9 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z10 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z11 i (Nat.zero_le i) hi

theorem scr_xs7 : scr 258 7 poolG xsG = true := by decide +kernel
theorem root8 : S 8 735 = xsG := by decide +kernel
theorem root9 : S 9 422 = xsG := by decide +kernel
theorem root10 : S 10 22 = xsG := by decide +kernel
theorem root11 : S 11 0 = xsG := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 11) (h : NatRun (mask 258) (goal 258) s xsG) : False := by
  interval_cases s
  · have := run_len h; simp [xsG] at this
  · have := run_len h; simp [xsG] at this
  · have := run_len h; simp [xsG] at this
  · have := run_len h; simp [xsG] at this
  · have := run_len h; simp [xsG] at this
  · have := run_len h; simp [xsG] at this
  · have := run_len h; simp [xsG] at this
  · have h1 := scr_no poolG h
    rw [scr_xs7] at h1
    contradiction
  · rw [← root8] at h
    exact bar_all ori_ok checked 8 (by decide) 735 (by decide) h
  · rw [← root9] at h
    exact bar_all ori_ok checked 9 (by decide) 422 (by decide) h
  · rw [← root10] at h
    exact bar_all ori_ok checked 10 (by decide) 22 (by decide) h
  · rw [← root11] at h
    exact bar_all ori_ok checked 11 (by decide) 0 (by decide) h

def witness : List Gate := [⟨.and, [0, 3]⟩, ⟨.or, [0, 3]⟩, ⟨.and, [1, 4]⟩, ⟨.or, [1, 4]⟩, ⟨.or, [5, 7]⟩, ⟨.and, [2, 12]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [8, 10]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [13, 15]⟩, ⟨.and, [14, 16]⟩, ⟨.or, [17, 18]⟩]

theorem witnessBasis : ∀ g ∈ witness,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem witnessCorrect : ∀ x : Fin 8 → Bool,
    Circuit.eval ⟨witness, 19⟩ (List.ofFn x) = fG x := by
  decide +kernel

theorem graph_correct : ∀ x : Fin 8 → Bool, fG x = decide (∃ i < ([0, 3, 1, 4, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  decide +kernel

end PEqualNP.Outside.L_meta_14810

theorem PEqualNP.Outside.L_meta_14810 :
∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o legal _oneNot computes
  have large : 12 ≤ gates.length := by
    by_contra hs
    exact PEqualNP.Outside.L_meta_14810.mainG PEqualNP.Outside.L_meta_14810.noRunFull ⟨⟨gates, o⟩, legal, by change gates.length ≤ 11; omega, fun x => (computes x).trans (PEqualNP.Outside.L_meta_14810.graph_correct x).symm⟩
  have hw : PEqualNP.Outside.L_meta_14810.witness.length = 12 := rfl
  exact ⟨PEqualNP.Outside.L_meta_14810.witness, 19, PEqualNP.Outside.L_meta_14810.witnessBasis, by omega, fun x => (PEqualNP.Outside.L_meta_14810.witnessCorrect x).trans (PEqualNP.Outside.L_meta_14810.graph_correct x)⟩
