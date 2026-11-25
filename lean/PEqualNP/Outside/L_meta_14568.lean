import Mathlib
import PEqualNP.Defs

/- The live-set normalization, the frontier certificate checker and its kernel proofs are copied
from the merged L_meta_722.lean (by Digger-Rockwell, from public PR 801 of brilliant-hq/pequalnp-proofs,
source commit ea90309308dd46a22d4a469766e46dd63f4484d0). The function, rows, score pool and
frontier data are new and computed for this graph; the symmetry map is dropped. -/

namespace PEqualNP.Outside.L_meta_14568

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
  (x 0 && x 5) || (x 1 && x 5) || (x 0 && x 6) || (x 1 && x 6) || (x 2 && x 6) || (x 0 && x 7) || (x 2 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 5 && x 7) || (x 6 && x 7)

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

def rowsG : List ℕ := [32, 1, 32, 2, 3, 36, 5, 36, 6, 7, 40, 9, 40, 10, 11, 44, 13, 44, 14, 15, 48, 17, 48, 18, 19, 52, 21, 52, 22, 23, 56, 25, 56, 26, 27, 60, 29, 60, 30, 31, 64, 1, 64, 2, 3, 64, 4, 5, 6, 7, 72, 9, 72, 10, 11, 72, 12, 13, 14, 15, 80, 17, 80, 18, 19, 80, 20, 21, 22, 23, 88, 25, 88, 26, 27, 88, 28, 29, 30, 31, 96, 96, 96, 36, 104, 104, 104, 44, 112, 112, 112, 52, 120, 120, 120, 60, 128, 1, 130, 3, 128, 4, 5, 130, 6, 7, 128, 8, 9, 130, 10, 11, 12, 13, 14, 15, 128, 16, 17, 130, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 128, 32, 130, 36, 40, 44, 48, 52, 56, 60, 128, 64, 130, 72, 80, 88, 96, 104, 112, 120, 31, 60, 120, 130, 31, 60, 120, 130, 31, 60, 120, 130, 31, 60, 120, 130, 31, 60, 120, 130, 31, 60, 120, 130, 31, 60, 120, 130, 31, 60, 120, 130, 31, 60, 120, 130, 31, 60, 120, 130, 31, 60, 120, 130, 33, 33, 34, 34, 35, 37, 37, 38, 38, 39, 41, 41, 42, 42, 43, 45, 45, 46, 46, 47, 49, 49, 50, 50, 51, 53, 53, 54, 54, 55, 57, 57, 58, 58, 59, 61, 61, 62, 62, 63, 65, 65, 66, 66, 67, 68, 68, 69, 70, 71, 73, 73, 74, 74, 75, 76, 76, 77, 78, 79, 81, 81, 82, 82, 83, 84, 84, 85, 86, 87, 89, 89, 90, 90, 91, 92, 92, 93, 94, 95, 97, 98, 100, 100, 105, 106, 108, 108, 113, 114, 116, 116, 121, 122, 124, 124, 129, 129, 131, 131, 132, 132, 133, 134, 134, 135, 136, 136, 137, 138, 138, 139, 140, 141, 142, 143, 144, 144, 145, 146, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 160, 162, 164, 168, 172, 176, 180, 184, 188, 192, 192, 194, 200, 208, 216, 224, 232, 240, 248, 33, 33, 33, 33, 34, 34, 34, 34, 65, 65, 65, 65, 66, 66, 66, 66, 68, 68, 68, 68, 129, 129, 129, 129, 132, 132, 132, 132, 136, 136, 136, 136, 144, 144, 144, 144, 160, 160, 160, 160, 192, 192, 192, 192]

def xsG : List ℕ := [0xf00f0f00000aaa92a493c444693a4e93a4e739ce739cc4444444444400002aaa4a924a0000a4a92a4a9294a5294a52, 0xf0f001004ccce338e30888b1cc731cc739ce739ce7266666666664040133338ce38c0000c6318c6318c6318c6318, 0xf0f0000002a8f0f03c0fc33333e0f83e0f83e0f83e0f80ccccccccccc00aa3c3c0f03608888f03c0f03c0f83e0f83e0, 0xf0000000aa330ff003ff003c3c3ff003ff003ff003ff001ddddddddddea8cc3fc00fd800f0f0ffc00ffc00ffc00ffc00, 0xf00000000cc3c0ffffc00003fc03ffffc00003ffffc00001ddddddddddf30f03fff600000ff00fffff00000fffff00000, 0xf0000000fff03ff0000000003fffc0000000003fffffffffd9999999999bc0fe8000000000ffff0000000000294a5294a5, 0xf00000fff00ffc000000000003fffffffffffffc000000000111111111113fa000000000000777709425094250000000000, 0xffffff00000ffffffffffffffc0000000000000000000000022222222222005014000902495000000000000000000000000]

theorem rowsG_len : rowsG.length = 396 := by decide +kernel

theorem enc_inputsG :
    (List.ofFn fun (i : Fin 8) => (fun x : Fin 8 → Bool => x i)).map (fun a => encL a rowsG)
      = xsG := by decide +kernel

theorem enc_goalG : encL fG rowsG = goal 198 := by decide +kernel

theorem maskG : mask 198 = 2 ^ rowsG.length - 1 := by rw [rowsG_len]; simp [mask, lo]

theorem proper_failG : ∀ zs ∈ xsG.sublists, zs ≠ xsG →
    (cov 198 zs &&& lo 198) ≠ lo 198 := by decide +kernel

theorem no_subG (noRunFull : ∀ s ≤ 10, ¬ NatRun (mask 198) (goal 198) s xsG) :
    ∀ s ≤ 10, ∀ zs : List ℕ, zs.Sublist xsG → NatRun (mask 198) (goal 198) s zs → False := by
  intro s hs zs hz h
  by_cases e : zs = xsG
  · subst e; exact noRunFull s hs h
  · exact proper_failG zs (List.mem_sublists.2 hz) e (required h)

theorem mainG (noRunFull : ∀ s ≤ 10, ¬ NatRun (mask 198) (goal 198) s xsG) :
    ¬ HasCircuitSize 8 fG 10 := by
  intro h
  obtain ⟨s', hs', ws, hsub, hrun⟩ :=
    exists_run fG ⟨fun _ => false, fun _ => true, by decide⟩ 10 h
  have hr : NatRun (mask 198) (encL fG rowsG) s' (ws.map fun a => encL a rowsG) :=
    Run.map (fun a : BFn 8 => encL a rowsG)
      (fun a => by rw [maskG]; exact encL_inv a rowsG)
      (fun a b => encL_and a b rowsG) (fun a b => encL_or a b rowsG) hrun
  rw [enc_goalG] at hr
  refine no_subG noRunFull s' hs' _ ?_ hr
  rw [← enc_inputsG]
  exact hsub.map _

def NN : Nat → Nat
  | 5 => 26
  | 6 => 239
  | 7 => 772
  | 8 => 655
  | 9 => 90
  | 10 => 1
  | _ => 0

def HT : Nat → Nat
  | 5 => 0xf75d8a1be7fc3d19e512d6c3e1fc881fd16c3dc0c4052619ae983c9fab84d589aadc1d939af1a39c8f46bf33823047157dd28b307ccb361d79dffe1d78cafa4075494b004f6b8f5a4c2db3c44250601c412c1cf7387faf4931b43bfd21b945010ab182d30401f1a4
  | 6 => 0xffb15602ff6769e0ff55dd2fff257846fdfae46ffd5f66ddfb7d3b12fa1af0d4f9e5dc5af97dccaaf974c91af8c95bd4f87f24edf7ce1209f6609d39f6200944f6182a1af50b57cbf338599af1a81beff187f88ff0a1580fee155e93ed3a59adec430af7e939f0c5e8e0c9fce868b9e3e7ffd04ce703ad7ce3fd7929e3b6b1b5e2b60e9ae1df1501e12a230be0ba271edf7136d8da4ac35dd952c405d83e530bd822bf1cd7f979e3d6cbbb06d45564b3d409c8b7d38825c7d36a3c61d26f1ce3d240397bd1732dedd071a5e0cefc0e38cd9e7409cc2eee55cb80117bcb14d3fdcb0c94e8c95d2e5fc936bbdec89f965dc1dbe8f6c0263b89bcbdce6dbb9aace7bab28a16b7552337b71ec008b664eb34b592e16ab368a34db34791cab32175b8b0bb3c6bb024740aae66df33aa460249a9733132a9432e42a845fafda7fdd38ea6c0e1c9a52692c9a3de1d4aa3d02939a04c92aba03126639fddea629fdde16d9f8afea99f556ca79f372fca9e8246329bc59f579acc156b9a25edb199f6d16a99701af697d6c64c979b7f64974021f6969a204996176a8f95ad4c229283807092594086925014df9199946f8fa42aef8cb3486e8b99f5d789cce744898308cd8610c25c85b04bcb856f2b5f84ed226d8467d64c8188ca2480f3e4157e7276de7d397dd67a888cf479bc1cf97962f4357947f13778f611d77873a67877877f4876a1239174570c017267530b7210292371cb60d97196470a6fbe9ad76f5c8b226e71c6c46c4487116c3136126b1bcfaa6af5b3986aef5d2a6aa0b12769c43787683f0424658e071565362a8b62fc820f62d403fc62478a66600e9d3e5f9296765d5c3e415cb7fb815c3ac5b85b3bdd085844a33e5818374255670588547d14c253a2f0af5136037f51249dff4fbe0f4b4f278e484f1803ca4d780b934cba9e434c2cb4ce4b43c77e4a0da9df49d379894916662a48c8bd2647b8778e4766b20947513a6b45bf05bd44a37bf44419168040bf7c6b4026896d3df85b353d43693f3ac319b7397cd8913950dc2c394400b336919d69361a967435d07758349caad631b02b662ed4974b2ec977f52c4b1a6e2b9cf50f2b1f04242a5b705629e94b2629c1158828f38525284e3f4c2657d5ba259bac4423c2d8d71e70714d1df0384b1a68b725199ef01218ee8d491734c14716f1319b16000fb815ebd10115b21aaa1338063c12743f14124e230211f5fb9e1121075110980d020edc6d690e9d59450d86776b0d09c1af0cd4829f0c25bdf50ba674170b9e91d30b8f8dd209eff1a009e4d68a0714f9b005fb19fc0443785d04190e320349e842032cf8b8
  | 7 => 0xff71a86aff0c6110feb55d6afe59fffcfe2c4bd7fdb1a45ffdaf8779fccf615dfc3a828ffb8d0c4dfaf58dc2fa9b0cf4fa3fed5df9a6cfddf983e091f9633280f95320a8f92498bef8b960e2f8ae58a2f89299edf78e9880f753a353f6f83e1df6f33fc4f6e69655f6214e3df53641aff5024094f4d6f9dcf41773f0f3c9e2baf2ca7c4af28e5d31f227bb2af2115144f1341520f0b03312f0a1580ff09aa532f05347c3efca6d62eecd69d5ee9cacb8ee6578c2edf7ecb9edba7c83ed783f81ecca29d1ec840559ec5c03b9ec334ab4ec196dd1ebdbb97beb617494ea76b783ea4ddff6ea434465ea20f10de96d625de95707b8e913ce73e8a0d35fe85ccedae80dc21be7cbceefe6f1eedae6b0bd68e5fb009fe5d944a9e5c15b57e58c54e4e58b8785e4db7f14e4c62f91e4821638e35d0d4ae3566c13e28aabb3e153b9b1e0ef6434e0edf884e0c4df3be0a94285e0347756e0114745e00b26c7dfe57b5ddfe268b1dfbf5f4bdf2552e5df215047def16785de680a64de20a9abdddc5b7addbf9bfddd522633dd37bce6dd0c1919dca059a2db1f922bdaf7b3b4da7b8a7ada7afdf8da45bee8d9e41a96d97e9187d9355d86d91c1dafd90fce1cd8b3b9c8d8234275d820ccf4d8056e4ad7ce2398d7bc7335d7612de9d75612d3d717019bd694f91fd6620fa5d624f772d5c4072ad5560285d4e7bea4d4942905d4522127d3d32e12d3c868a5d2a8e446d22bb576d1db2871d1b4378dd169829bd0de99e9d0501b93cfc173d5cf58e22acf5638bccf528bbccdd3c8f6cda473aecd9ef762cd227812cca7e51bcc85cde9cc67d7f4cb80117bcadaea7ccad6bdf6cad5d301ca166015c99afb13c8c01261c8b8c3fac75f79d8c75718a8c6f0d18fc63d39cbc6079240c59a77f0c53f4e57c5010366c4c1c117c46b2486c41ba565c3e59158c3d4c63cc3d2dfaec3d1d987c3c4ac82c3bd744fc3914592c364d7c0c2bf55edc20b619cc1d287b7c1a6b211c0a8b1d6bfba8fd8bf87275abf06b78fbef1c366bee9ad79bee230a0beaf7080bdad0776bd7be262bd27b217bcd04a10bc32731dbc19b6c9bb0f721ebb05437cb9f680ecb9bae44db996679db962fc0cb89e5569b80cb290b75b58c4b71643b2b5e4149db5b03f55b4fb3141b49aff97b4217d6eb3e99870b2ee192cb1b346f2b1950e5eb17d6d58b1688bf9b1647257b0ed578fb0845fbeb006d902afe29b2cafde3804aee74e31aee0f91baed25594ae5d81f8ae527ac5addb1be4adc1b834ad8b26d6ad23a989ace27326acc4d1beacc332f8ac56aca2ac00099aab9f91b2aaf47931aa279076a9fd205ea9c5dbc2a9c2fbaca8e4b5f8a8118ad9a78749c7a6c40053a6bb232ca5f32905a5ad27dea44c6503a411a1aaa3e005a2a370506fa36bc3c4a321d2fda2cea342a2be3f99a2ac79e1a29354a7a26864c9a1f37339a19b7421a16736f2a14dd3fca107dce0a0db78afa0941df1a0593ba49f628b8d9f08610f9ebc6fc09e9a66759e4cb7ad9e36c0789db40abe9cba3dfe9c856b7d9c5084089c3fb5409afbfd0e9a9553849a20209f99a02aa3997a3a3899231050987f465c9839f48697f8e01e9758c65597313dfe96e1fa6896d18204966f724f9626e1be95eef98295a810d4953d037795235540940c6034936f1f309349c556934480e4933cfd6e932060ef930cf11b91f98b7e91917bad90ef0e8c90db84a390daf38e90caa0b290b363b7906832598f8da51a8f2386f28f21cefc8ed74fb78eb475278e5167998e25f62d8e0caa5e8dd3a70f8dad628b8cfc23788c39ba008c0425aa8bba52d38b4949418a86c5948a42cf4a8a0f565489ca299b89a1f0e4895a719388d2a85688314cbb87a3f463878db38987649eb08721846b86b319aa86726ae6860d49598600203e85fd258385f7694c85b570fa8501d1a784c65f8584905c388449ef4984311465840227c4836eb37883041db8824ec435824cc2e8824a463881fdab6e81e9806581969eda813607c081280c7c80e4916680b8ce1880a2379e8092b206806143e47f0d74797eb6fc127de2cac67d9c98407d82c20b7d654b587c56c5057bf35b5f7b64dd097b4619c47b3acb3d7a4214727a03f33a79952d2c798e1d1a796801087962f435790daf767909d20b77b1eb08775fcee27725e97876e92af376e8a854768f9e1775b7374b7576c2517484dc9c74204a1a73cd8570733f9bfb73273d5772fe76f872e1538072b86fd972a602487297cf1772716a707252d52a723a34c372147c577196470a7120910c70e091f66fee91da6f8e91df6f1647fb6e7999366e703bd06ce648896cc6a8f56ca86c186c3136126bfa742b6be8d1206baf49c46b788b836b5a3ced6b38a77e6b32ec386ac3cd5d6abb7d916a60185b6a1555d769f328ef69efaafd69387f696919a2e568e6edf668dd90ed6782508a66d5078866b47f4366813823659012bb65679157650cbbb2650b4262650a328264ed9c6264d04e1d6441d92d642cb0796410f0286388a6dd632d489b62e8879e6248a8ac61d600e461cd5300615a40b460d0bf5d60bbd336609ff529605be21c5fae26ad5f4164545eb48af85d70d8335d38311d5d2d0f155d15673d5d0450725cf0e47c5ce397b45ce35e855cc9e6c05c7d14615c4dddde5bf93a835bee960b5be573385bcce0e25b9527535b15e16a5af3c5725ab3031259d0ec9d59c7759e594f7a0058c13e2e58963234585d90095859f3805797d45656c42e775640c61a55e77e78558e37d3554b024454e4e45a54b6864554aa3a9054573e72534c04cf53218819530b0ff252e067ad528d2d2352710202523021f8522451545171e0a7515b2a205073c9a2506396655053ced0500600394f6126794f0352384ef5e0344e7fd2884df0f10c4db04b094da8c8b04da24b494d6abce74d1d15c84ce2f5be4cba9e434be3b32c4bb5b6af4b4bfecd4b3fed184ae79cd64a684e3749e40df749c18aca475476b6474c1385473ade9b46bc374946b92d8546ad5392466ebbca464f1e9a461a049a45fdac564594fb64458a2cbb44b420b8448971104446742744125fdf43f7882743caea1543b7f5d1436ddeea429ba10c4266a7444231caee420364c1419545364164a168413ac65e4111e98140b4928c400174763fc9575f3f55c9843f3c9d273ef287ed3e533d783e47a8743e16b3e23dea9bdf3de599113db5bc673d3690143cfeb82e3ccdc7703cabba013c82dc923c209e383bff5ad33bfae5cc3bf611003b9e46183b7bb87d3aeaca4139d8e231394ba34d392c18b738f3e54938931245388ebc9d388d0bf83866efe63803668c378ccd5c375d9e79373e0c2a36ccb1fe365ea5cf35c75d7435b040723590a6ad3584311935097be834f5b2c334b85214348c3e5a345d06a334145ce333e769cc3348cc6033120eb232ff436332bb421732a274ff328d47cb317f6aed30f7bdb730921cec2feadf7b2f66c9092f54971e2f2883712de2a4d32d5e5b2a2c7772342c1458872b2bf55f2ad561ed2ab9d7802a7d699c29a3050129906d2029698a5828e42a19283a2842280a6ef02803fec4279422d5272d41df26c43d34269ec389267a5112258cd87a24e7006524e65a5524be8adf2365b0b622bf078522b4b02421f1f15621e7375c215f863d1ffddb7e1ff28e681fda15301f076bf01ee0f93b1ec5efe51e95da4d1e6710e51de2166a1dd83a561dbff8451d862be61d6849331d2f4b991cacbf751c98ca961c5218581c16d5351b4ee2ad1b0353501ad4a66b1ab29f061a2bda9119b37fb6198a9b74197002a3189adfc117b43f411798d9781639f97415f8dc6a14a661de147122ce145bec30144d40df14118f3a13bea7a9132c2e011301e0d312a7117f12a56f2012984605128414f312733f9311f14b7111d7bb6311925a59118a52ce115eaf01113796d8108b45c81084950c1082133f104528e2100e4d4e0ff3b12e0fa78f7e0f88d7e20e9b24090e92854b0e81a62c0e7a717a0e1694ae0d97c5bb0d69283b0cf0ef2b0c7ede170c77cc390c4c4ab30c4070d40c0d27a30bd074720b6997830b3b39000aea07440ae838270ac998e70ab4a58d09e85dfe09cb576c09c8f5cc098ddf260926854008f1fc3308b096ef07feabd1079c19be076f04e6070607bb07040a1406c2187a065ed39705f81baf0596820705225322051dcda4051cf70804f955eb046058830451df7804264f0504145a0303d1da2d031b63b6030373b80247229f020ee818020de72401fb554f01c902ba01aa021d019d0363019485f6015daa8f00e54c7000c166b70065ab3700305a7a
  | 8 => 0xffd4fb34ff3629a2ff185577ff12be24fe68fa00fe63b527fe3ca05bfe29e8c8fe0c26a1fe035935fd2a90cbfcc5d367fcbec482fc99bfbafc3a828ffbcc85a1fbaab493fb5c057afaf58dc2facf9773f9a4ac80f980e7c2f973be93f8469e36f81696dff6d45b02f6556662f65028f2f62421c3f617cd77f5ab648bf50a1107f5055f1ef4b1de8ff49e7e28f316fc75f2fe14c3f2e79494f2b812e2f27fcb45f2026be3f0ff9e64f0ca14e6f0c6703bf0ade240f05dfbe1f025ec6df00cc5edefd2f98eef4b2ac1ef496b4fef23da29eed0c286eecd69d5ec78a839ec523584ec13ea93eba7ef64eb3c2dcbeae5c6dbea1dfbbeea05deb3e9c354a1e988117ee981c509e958c67de95453d1e8b9993ee845e2b4e813d1b0e7e03cafe78dae9fe6c0a527e5d944a9e5d6f217e5bad7bce4e82922e4c00d3be3fe0a77e3ab7ca9e370a30be364b40be3566c13e2179e27e1e25f17e11b31b6e0edf884dfbfe2a4df0396a2de6e3ff1ddb6652bdca059a2dc0c6052dbef1533dbebadc3dbe0a281dafd6497d9fbb19ed9b1ad1dd97e63ecd8bab402d78346f4d72ae4bed6894e93d50d5607d50754d8d4f79a36d4e0412fd47b8c21d43312c5d307be50d28e3351d1d32d0ad1d194ccd1978b4ed074b001cfaf1859cf3768b3cf0e815bceaa31fecdf622e5cdd6e780cd3fdc91cd097877cd061032cc2699b8cbfae7c4cbc420d6cb8c0624cb640b45cb1d601ecaaf1fc6ca409dabc9d126c6c9abbeddc8bc1503c8b8c3fac8a0a93ec8741ebac7e453bfc789426ac5923335c5921652c4c4dfa1c3d95149c3928a8bc3529c6dc2af0559c282ed71c272ec63c1f323dfc1885272c0de934dc0bf1ee7c0738f08bfea910abfd0a76cbf922d89bf808aa3bf790ffcbf4cdbb3bf0ce287bebc16dabd8291b8bc363c6dbb8eb894bb692907bb383563bb2bb8d1bae97bcfba576811ba3b661fb9cd4007b94cf5c9b8c6ff5cb8307b3bb7e7f3d1b7c3b106b6de9eabb68025aab60fbe3ab5d707e8b599b08eb54cd392b527c705b4c3a86cb4692ecbb45463d1b43fed06b33297a5b324348eb2fd9132b2fcc3d3b2cd3a00b1f35286af9ddb17ae60a082ae54bca1ada5b3a4ac928c95abd946b2ab6bca49aaba279baa701022aa5adfc8a9bb3221a981a9e1a8e04a46a848eeeda7d08cfda7924df1a6efcdd5a6bb232ca67ea4f2a57da9f8a495a938a4365cd5a370b5d0a2cea342a2c73ed3a154fb9fa01be68ba01a20949ffa6bad9f8ab1a49e4fd6379e1f031b9d4fb4db9cca1e789cc7750a9cbff56f9c6b82c29b83a1599afbfd0e9a93b4609a4a157d9a1921699a115e2599f70a3799be1dfc9984519d996caa7a9847142a97abfaf29740bb4f96c50df0962a00489626e1be95ff9c4095be4c5595b85d429595d581950e84b393d9671a93d55bec93cb8b86938104e49356f30292fc011592d4d67e9245d365923fa89992243f8e9177e8ed90d1e76e90575077900b1c408fece7308f8e633c8f0773948e71654a8d5cd4b88d2bcc268caf2b248c62ffb48c4b98d88bdfc1a88b3f97a68a6ba4908a41865e895713fe881a40fc87e5465187e3a68a87a326c68767bd3a872c209b86d94360866111bc8600203e85c2b4cf85a7d7b4851f623a84aebca684895535838ffb8e8361fc80834628b7834525ac83017d3881fbcbd981e980658192b9bc809aa598805f557a7f064aac7eb4707c7dd36d5e7d7815507d53d77a7d0795fa7c5235697b2052c87afc63247a4d689d7a346f4679f52410794ce3b1792303437910ce0078a9200577c07d2e7786b0cf772c137a766a02af762f0c2275c712277576c251750e97ef750b0d4674e4ad48742c5f7a73dee4ce73d3fd4473cd85707367b7ca731e642c730e1193729d37f2729be20772532738709e6d0370930f4b707cdfb470781811705c09dd6fd9a1176fc6c2286f7bd5016f64af876f07c4536e675de36d1a061e6d1093836ce8c2006cd3c7db6c9d13e86c8a3c916c73c47c6c5e0fba6c5829bc6c2dac0e6c0157106bfa742b6bc78ab16b65c92e6b5f33ea6b25470c6acc14096abb7d916a1c44496904aebb68a82c63687e546368778895686d395c684dad8b677022ed672c3bc06653208b656a1c6c6555560465513578653d823e6530270265299b0f64a27a4c645336b6641b967063e0ae9d638b0c09636035d062b11bd862ae3fc56295063f61cd53006137093360ebc95e60b49e5e60ae39bc60927cc3607e2d695fa00dcc5e267ef25e0720805d7616f95cf088565cea660f5c94c3405c4510225a8e48ac59f229d059aaf64e597561f857e0489457d9c17f57b4833d573b65e957132d3256f1f5ba56677e4b5643e4a455d56dd055500c16551530b1549d345054573e7254434e11543ac81a54216831536e61d15368a59a52eeda67528d2d23527fb4a2523e23ea521dab1a5138f9e150dfefc6507c71855061d94150120dca4fcf8fb84ef116e54eeb96ee4e55cdb44dd280324d26ccea4bd03b364baa45474b540714496497ad48b7561247ff2aad46ff596846d93d5646a9cd41467c1c53467b0e59461e6b5e45dcae3a45810b0344d2df7244a3399144991313448514c7445a67414449d4624446742743b7f5d14280bd1e41758260413ec1be40528fce4029ac273fab71113f8abf5e3ee04c9a3ecf1d1c3eae84793df5ea363da79e993d30dfe53d16029f3cffce2d3c880fd83c209e383c1391dd3bc0d7933bb02cd43b870b343b3a37243ad18ed63a85b7933a14c800398626c03871962e384a7e05382cb9df37f2d61336ccb1fe36ba76ab363818b135f9122834f02cb0344643d6342be56633d2f91133cbb76232d2ad02327c7eb0325ed8b03223c763322001d131fb1f543164b81530fb452b30a0c65330741ee12fc37e1c2f5f8e4f2e9112ff2e2d0f842d5e5b2a2d1f62fb2d02a65c2cf5a79a2cd2ffda2c58341d2bf37f6e2a758cc029ee50af296a76d1293ee226290663a128a76d2328871db827f8339d27d398a12738b1ec26dd63f926b1763d2664a14526327a7c262de9a225daa7b725944e1e255c9874253f33092522cc1524ce44cb2454ffc724356ac523eaf5ec23ea281b2374e90e23414b3f22ff7421229ff37f2227c29321c87ac021a8d0912186472820e6eb4320debaac2071b6962070d4a71fe23e501f076bf01ee258181ebc65551c325aee1bf10ed61b2187571b1387971a89f0ad1a7c9f181a2bda911a0fdfc219e2458f19a144631928209d1926f2fd18fb4f30184a7a031829a35217d6fa6817c31a4417b43f4117554a451744bab51697146315e92946154bce29151201ca14bd4fd3147d6c1813dff81813dd1103136ee8a4130637b212f9378311faad5e11b7b07511899eb511217afc1080498f1077ab5e104d371e0fa78f7e0f05fb2a0e604ef50e4053000e25ceda0dd143bb0d25f83a0d24b1820d1bba420cec2bdb0cb997370c92b7a20c25afde0beb97f70b87f0300b5bd82d0b26f8b50ab19c210a6ff47c09ff15770991da86090f826608ea84e50866a0e307d20c0007b87a8a07b8788f0665219705fff8eb053390dd04f74c8804d2832f04af4878049ef923043c461e041f004b02f56d6702bffb6d01d93f8801ca82740158a61a00f701c800c4aef600ba08ae003c6cd3002c7e65
  | 9 => 0xfacf9773fa443c23f81696dff3058a67f15b6464eef78371ede2f2dfede210f0ec78a839e5bbb64ce35a658fe14e4d4cdefadafeddf185d8da2ad380d1ad8267cc83fa72ca9bcd19c9abbeddc93dc1efc91bf0e1c8cd41c8c789426ac3c16540b4feeaedb3482e65ae8c6e04a278912698fd427298d54793988e9c6c962a004892243f8e914a8d97902041a78ff429bf8cea4c4a8c7e1ed587e5465184895535830aecdc8299035381c5a01f7b2052c8765186947541c94b75038a3f742c5f7a71a7992370e1f21e6d6ba7fb6ce8c200686d395c651d374063299990627fc1015333f11d510137dc4c25acca47bea4eb449d4fc843a04870413ec1be3dee1c023d37fe763c209e383a81cfd139fb78df382cb9df36ba76ab3675eb0935ef90b134f02cb0329ad75d2e03b9112a5ba25d293ee226255184e223d8ba99220e709e21c87ac01f8ee7681d834a1811b7b0750d25f83a0cec2bdb09f94c260991da8601d93f8800c4aef6
  | 10 => 0x991da86
  | _ => 0

def PT : Nat → Nat
  | 5 => 0x8718198631314d6a2210c50e21918523153486620b1c941318a1c4312174608438d00165aa10e3500f86a84b8c8c481181587152a068c4b8c48ad5a88d03133ac6a8562d503b1a08c6346
  | 6 => 0x410c8c4a1a8258312504628d00d817e181c243148ac607330d519418281231458420af10d42611994e43049586a9020c52dd080606304848627028d405a1893923128146c1020c4d0318a87c3235106c0c82d95e71a830ab547b0606f38d82dd0822fab653286250f0d51055b09ec103ac4608230cc70219198e3169bd604ca0c1add0813f8354614201798c8cb319bd623509486060e8cc4181a0b3c302a946a1588d82521b0104312a20609430d80bf1b04de105b9c6634b8c0cf65a1b20303a18606338cd4f6598332365184e6d6e841594181a8a30358560a0b8c4e3e1a81ecf548ac6087b2d0030192c7c360a84663338c4e2b1a80943037886c1090c56e91a02723609bd607798c4a2b1b040831501ce6d3784024b189e023360d56c2250d81411b28f03203d94a1090d863d191bd83046e86605f8c10d61893d83505b16a1028d02d319a8c2b65868624f60d81bb182586315af066b6e840dd8189b76350678608748d52b038b130b238146066f0d95bb1b03d432379c6094c1c999e1a83c432330c687449c58075b0b3c3602cc6cb409c9807198b0a1055f8609532d84981030323129ac62cb60416a51b04d43147886094b8d809e181d10303b75686610c4e6f0820123135146a00b8c51441a80de3323bc660330d0d451b0030b0217c6656ebd52b05b2d4a3038b062a818cc24c5b0c4a3151286081b0c4d44181c36716a616cb44ad94361b29ec104a056ca9e8c8cd618a036365788625290d426f5aa258323ba46c0b60406a51822c2100584203238c0d031b0562303a5c60ae80c58bf1a820231379c661430c16df1aa47c302b346a92b8c119919bcd43133286470dad9647182d6e354640e2d580d0d871a39e835140c609238d818218aafa7166a56c34e8d529b1991ec1056896c31b0c11731ab9ec1004e4681468d511c189b0a1045b0200c52d842e18a47c303
  | 7 => 0x8e44208d0d02111b2b68f650b4206e00d420718ac143422a020c260c0ca80800841035b560d038c4ca118a2d63309886e0e10d81301892dab0548c20a9f8cc11d08206a3500686c0fc0c55fe1029303146956c0e10dc2401822be3035606a0168408101b021c3200786e0218c48421891dc31788160e498c14071b0374b0240c208f40d51e61aa10610678c6a8b0ad95e21a1cf8105284626f08d088f1b03bc35448d6a9228401c51838603234386e0d18d815f1b81643709746604c0c4d235b20203039f0e08120c49d11aa39e3547386a8800dc1a31b832836006c626038c09d21a81c8b02390208c40d81a55103763036506e0a3ad96590831903382506c0240d04dd0828ac10640c200a02d52455318ac100038647308d813c5bb48a7326206e0bc0c14001b8280b4087c64026841804191b763548e142aea8d40b41a42de221a34646bb0d828c19188410607060a420cc28a189c8a10548d6ca912dd9a7181b4aa104756a919a8563c0834ca3505d86e0dc0d41b01aa470106984607208d811d5a01741042e420a168419407b2b523546d16c2a02d41d218205a732690648cd8819ed1b0206b54584604668d027c380cca3049746e1310c8e45081150104228680e70dc09f1814823034ec609238c0e571894ac3234756a12cac153f1834323045146c1298c49a2181b2e100a2c404308dc09a0828ce3202e56a881a9824b1898e03505f86caa28dc2241821c8b5435c6a0dc0c10b95b213e3706d14c06ead946419b27630348462b3e0418e45a040c1055c0686a02981e41a82603036d02011a8c4d6b1a021c30688462641a804881b82c03427a460a8c8c16590802ba3430706c0800c11021a84ba3044754c0dd0400e47b2ac2b049642025d2d51da1981c8b502e56cb138c0c851a02aa3438246a1130dc1f21b00703364f060621040056082174b4085c6a11e8cc4b9581c3235086062ab09d418119809a1042a16a92284185c1b80841047d46a08c8c0df81894483034e06a8542d004d5312c27609946069a0d0e471833c83042696caf90c1238080c4c3608b4662908c592b1aa1e0210464609048c08ba5a809837047c6ed198404de181a423140b42088b8d51f51821c8a60880663468d01ee18289ab430b54c6dd04052308221834342c6ca212981091aa150b5041c6ca800c15051b289ab536d020aee8d02385b03c83233fc687310c48fd1aa38a3053d060b120c168e1833b437051d6a12cad82721a015c350a2c40c9f8c801c1b82c2b506546400d0dc21818a478b037086a1340d01a50831e23431356a4e58d02330800282212e94c0f78810565aa02037081820d2e8c5a471824f810465c203310c14d61b0038303910404038dc0e01a1a32307159680508dc44d5aa38831440d6c2e10c11b45a81b036594864c212d51ef1903362039f14c0542981891a005ab53220608688d94c8182430313928e4e41a8164639bb2ea603306a8d18d404d5a1084b6199d6e2658d0e09181c0c705a386e016ad52371a04701003206ed1c9cdd611820acb503106caed0c11781b035631446460d3f8840425b109af656206a1308dc1a318216c343109ecab084182d5a196a3432d06ecb09c122c18b48a1047d46062e0c14dd5822c2350040604f70c0e3c082b283052e42084f8c15475b01363157f4660420dc1611b03103045e06067c0c155818243230363844216bd944c1821383435b86a09d8c161a1a00383128cc20ca38402411b808a31448ce80dd0419470832603059f16a8440c1611193a801054d4608478d5056530246a14915687079cde2c5b8aec3036d020c9d8d80425a84043408a56e322ad4dba5021721004fc6e1420d828618b260360018608918419610801da3201f06cac28d413b1b83c83707906243d8d0dab189a3a1057086071c2d94bb1a83fc2211d86a919ad941a18234a1001cc6a8980dc06f1a19727405146a1108dc5c918b0cc35465c20c080c14611aa4f43044fc608ca0c127c3818bc34340d6a0f18c9903082c94b7601c6082e0c10e318221c330108e25232dc6455aa38a30340d4a3230cc4be1a009830576862cec0cda3c5b2bfcb724006c0280d0dee19008a315484626268cc9cf193472b76370442e28c19351a81bc305a0140742ac992f189b2830372462ef38c108f1b821c3040e46ca2104096d08086e34339020a26840dc31a00683650cc6868f8cd1f21b81ba106620604608c10de1b0500710400606b084051a191c8af65458647308c14291a1cc43049946c07c0c19bb38b83430589c6c1310d801f1aa03c3545856c00e8d50de1b80363654246265cac08ba5080323432e5428f90c09fb19823a7169946e0bb0c104d5991643058e160a090c90f81838223438b16e6d81c5e3c5824803058cd60c068d0c07182c1eb7189c624e32dc54708097410583c6625c8419a738bc7810059c420bb0c814008334a726118421428814001aa2801002c860c4a0dc28a1b2b74b61109624da04068319250235464ce2e540414b21819b63146c96e28e84192e1a02461006b06088e8400d7189c8e30591c6e04d04189a08034a1059b0686f20d814518193e3609a86cb108c54dd0800963063e0606cb8415a57b282c22140c20cd29c95975b0a06b400f06812c0d0e571a1c40b06134200c08d0093182430361134e645f0c4c881b00823209486a8478cc2501aa49e354a1564e4f8c0e4a1aa1603402d8625208c16181b8c0e3148246c0120d00de1892f8b711594211d8d0ce40831423158246e0168400a21919c8100280626fc0c5206500ada1068cd60a26a98c88181abe3058d8684ddadd89e191c8a10338c60af90c0d6d0800ac10526062a212d00991893ea3608c86a8bc0dc1610828b83607b86c0640c4db45a89ea3504d4606b6080e38082c583548ac648b0ac0c4d082bea3704f0e2e16ac4d61381360b76228626740d81ee1b811231388462c2104144d0814661058986a9118c91a75bb09836047c6293e1c16271b834ab658f1605108c521f1a1c2c3052e820caf8c1a1c1aa24471736c6245d04005c18192630351c20afe8dc1615811823056956a1138d4077191a98b710b420acbac5540082326b76
  | 8 => 0x12081c171a1028b50060a0a080dc005083064b0501020c1cad802a5b881aa6102c6261cadd8031a00301061186ca228d440552883010000820c1008142608085cb6505420e01040c140838823041086ca0a9cc82e58a88238004420e128418143a180c10200420e0b0dc04308201e3420cd6c20004182550a0867400982000a29c05753a04af76144e8602040c005308001040c962c129c58011b000410206c200021d001828004cb150502002a8cc0435b882c3401086081704000d0838ae1061306a01f8c0c0d08004cb65061cc812ad94041890305040b962c239d005153a07e2061406a219bdd8255ba80230212c66004841c3f1b2872360024e64038d00101b00a21060e46e0168d00113828a8370044e0828840c255ba036b610bc680172c14265b084cb0510d4e01f88843e19288c20604c660198400013b004ab7605c44221ad8006083884303150606031cc8255020727500b46a02008181b08280a107044e0602041c551c000a1000956c81e8d503c1928763520c8200250cc01b5398041070056040c04105753804cf7609c6a0011cc83958200636005420a0c3d5038102028105061ca81b0d941218380210104420a00041c155398442060a960a21a9d01b5aa094350060a0c0a29d0055308867410e420a0dad900c10300633014040a23088459083808a70138626289c040719808610615c20e268c4c065018983130556a821a9840d0828623651546c0180d500c102866b710bc64a2488141d1a002ab641546082688841b5b1846370080408048414395b804638014420e0dad9432538072b0314068204a9cc155b18063500b46ca0a2d902c1aa01ab5106d6e20c2d502e0828b2a0406d6a606ad84281aa030b400556ca0a2d94095aa036b7209c6a408ad94060828a2a040e56040dbdd81d198012b640516e20aad4c251aa0263400194e6120814145aa06837001420a020414265b884c105061eca208c1c531108041050616a008a9c04c11080aa710516e402adc40d5b289036009420a0c3d00095b185e3500016c00a3dd82c1a0004a730a960c210d80161a800cb540356a0168d801870100210600020a0e8dc0065b2012b6507040c2b9c04045aa072a1515464e0029d0255aa004b540116c821841c3a08300ca02061ea0200814011b8030f64061c0204ad4c57082804b640806a81c841c065b181ab600e4e04002d40185300943400994e0090c102010180ab6111440a150400097bb07e2050196ca012d8c1b38903c35213864e2b9c100108006610614420a0e0884055b2808b650746ca2bad500d5b88641010e46a0032d4c515398243060096ca148884055a80363430b94ea2a0e00575b2008b71061cc0002d902c1a800cb710156a20a1c48461028361020646ca089c044118281aa7006ce82258d00171aa004b530942000d8410161b2802b760b82022ba8101218184a7540e4608022dc8013b8000b6513970428ad50151a18ac36004c64a0d9cc018732808f760096e20d9d00515b200ab601106c01504041408106e3700e4e081329d4101b2858330108700002d50101a002a10400c6e02bad94421b8072b5010c680210d401b5a184aa15054e02078d501018184a75309820c28ad8c5738185ca7016044224881c551a8074a050586c012841c1b58901836505568600adc0351018a2b65094208058c943a0838422060996c0208c0c0d08081234312440c1588844308285033004861002a9c001182030f030e4202040d94115020aa3700406a00c3940071a90a2b5305162421ad00161c00b2a06024208009c105010204a1030806621d1c183308389cb810fce50021c48231b000638000160821ad50595028367430c820e0d9cc4351b00243051486a0030d0c39181086b64025686011c800608089cb8315060a19a9c0201a885034010d6a00e8d40573830ae705018208118c14031b2804343044e0c0a9d0c000800081020b820e022d80393b000874106d4e80b8d4804082004101005608008c14023a007277001c6a00104102a08384820609540a208c183b1a803610606d4a221ad943b110828b040196860b8d00171a802aa7406c2060a9d0851501854a0306020a240dc02608386e3600156020f88840f1a903a3800806240a8418025a18702210516c0128404140830442210b466019ad801508184a7430242000884180a10281aa51024e860a04100458906a35002c4420b0cc0541830aa36515c208002dc40c11080270208c608012c041872001aa7110c200258d40531928a4365150608288d0c1870187210600560a188c9c385c102a1021486c00684181b189012a7408440e0a040c1d1b007eb87024e84280d50015818a2104010200020d00475010783500d06c0278d94063a184034108c6061984042d1c009c36505c6260484183a50205a370008200268d94320830983520e56ca04840c141890342210c96e219ac1406500872100008e86098d40395ba80473012c6a80c3c08515a1802b6004062627088419110800a700407000329d00000002a707018e840c3c0401382830f600b820c178cc020101008a740b96e2022d000908108e7501286a4021d0c060830503500094e80328101b083808b50008e84129c5c0608189e221
  | 9 => 0x83000f4300020600395000731000e74001e8400394800081000502001ec4003d80007a8000f30001c400038c000283000e6400020e003dc400281800e53000e640039c80073a800505001ee0003d0400280800e42001e6400041400539800f65001cca003d4400283800e630016a8002d90007b0800f01001c82002d8c00730800e01001ea8002d94007b2000e21001c64002d4c005b8800f76001ce6003dcc007ba800500001ec6003cc400730000f74000e40003d4c007a9000343001e4000394000080800740001c800039d800082000e70001e4200390c005a1800f72001e8000141000580800e71001c62000400003a1800730001ca20000000053a000742
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
  | 8 => 11
  | 9 => 8
  | 10 => 2
  | _ => 0

def St : Nat → Nat → Nat → List Nat
  | 0, _, _ => xsG
  | d + 1, s, j =>
    let e := fld (PT s) 23 j
    if e = 0 then xsG else mv (mask 198) (e % 8192) (St d (s + 1) (e / 8192))

def S (s j : Nat) : List Nat := St (10 - s) s j

def idx (s : Nat) (zs : List Nat) : Nat := bsr (HT s) 32 (hk zs) (FU s) 0 (NN s)

def ori (zs : List Nat) : List Nat := zs

theorem ori_ok {u ys} (h : NatRun (mask 198) (goal 198) u ys) :
    NatRun (mask 198) (goal 198) u (ori ys) := h

def poolG : List Nat := [0x2749f2796049986, 0x2246a155895c12a, 0x1a45327576324cb, 0x2b4811750d5f929, 0x270b619d4d4a560, 0x12c6a2c9303c189, 0x1f0602617260978, 0x5c6226d2d35177, 0x1942a274f14b973, 0x2e0aa30ce14716e, 0x268ac064dc4613a]

def Z (s : Nat) := bar 198 S NN idx ori poolG s

theorem h10y0 : span (Z 10) 1 0 = true := by decide +kernel
theorem z10 : span (Z 10) 1 0 = true := h10y0
theorem h9y0 : span (Z 9) 20 0 = true := by decide +kernel
theorem h9y1 : span (Z 9) 20 20 = true := by decide +kernel
theorem h9y2 : span (Z 9) 20 40 = true := by decide +kernel
theorem h9y3 : span (Z 9) 20 60 = true := by decide +kernel
theorem h9y4 : span (Z 9) 10 80 = true := by decide +kernel
theorem z9 : span (Z 9) 90 0 = true := (@span_join (Z 9) 40 0 50 (@span_join (Z 9) 20 0 20 h9y0 h9y1) (@span_join (Z 9) 20 40 30 h9y2 (@span_join (Z 9) 20 60 10 h9y3 h9y4)))
theorem h8y0 : span (Z 8) 20 0 = true := by decide +kernel
theorem h8y1 : span (Z 8) 20 20 = true := by decide +kernel
theorem h8y2 : span (Z 8) 20 40 = true := by decide +kernel
theorem h8y3 : span (Z 8) 20 60 = true := by decide +kernel
theorem h8y4 : span (Z 8) 20 80 = true := by decide +kernel
theorem h8y5 : span (Z 8) 20 100 = true := by decide +kernel
theorem h8y6 : span (Z 8) 20 120 = true := by decide +kernel
theorem h8y7 : span (Z 8) 20 140 = true := by decide +kernel
theorem h8y8 : span (Z 8) 20 160 = true := by decide +kernel
theorem h8y9 : span (Z 8) 20 180 = true := by decide +kernel
theorem h8y10 : span (Z 8) 20 200 = true := by decide +kernel
theorem h8y11 : span (Z 8) 20 220 = true := by decide +kernel
theorem h8y12 : span (Z 8) 20 240 = true := by decide +kernel
theorem h8y13 : span (Z 8) 20 260 = true := by decide +kernel
theorem h8y14 : span (Z 8) 20 280 = true := by decide +kernel
theorem h8y15 : span (Z 8) 20 300 = true := by decide +kernel
theorem h8y16 : span (Z 8) 20 320 = true := by decide +kernel
theorem h8y17 : span (Z 8) 20 340 = true := by decide +kernel
theorem h8y18 : span (Z 8) 20 360 = true := by decide +kernel
theorem h8y19 : span (Z 8) 20 380 = true := by decide +kernel
theorem h8y20 : span (Z 8) 20 400 = true := by decide +kernel
theorem h8y21 : span (Z 8) 20 420 = true := by decide +kernel
theorem h8y22 : span (Z 8) 20 440 = true := by decide +kernel
theorem h8y23 : span (Z 8) 20 460 = true := by decide +kernel
theorem h8y24 : span (Z 8) 20 480 = true := by decide +kernel
theorem h8y25 : span (Z 8) 20 500 = true := by decide +kernel
theorem h8y26 : span (Z 8) 20 520 = true := by decide +kernel
theorem h8y27 : span (Z 8) 20 540 = true := by decide +kernel
theorem h8y28 : span (Z 8) 20 560 = true := by decide +kernel
theorem h8y29 : span (Z 8) 20 580 = true := by decide +kernel
theorem h8y30 : span (Z 8) 20 600 = true := by decide +kernel
theorem h8y31 : span (Z 8) 20 620 = true := by decide +kernel
theorem h8y32 : span (Z 8) 15 640 = true := by decide +kernel
theorem z8 : span (Z 8) 655 0 = true := (@span_join (Z 8) 320 0 335 (@span_join (Z 8) 160 0 160 (@span_join (Z 8) 80 0 80 (@span_join (Z 8) 40 0 40 (@span_join (Z 8) 20 0 20 h8y0 h8y1) (@span_join (Z 8) 20 40 20 h8y2 h8y3)) (@span_join (Z 8) 40 80 40 (@span_join (Z 8) 20 80 20 h8y4 h8y5) (@span_join (Z 8) 20 120 20 h8y6 h8y7))) (@span_join (Z 8) 80 160 80 (@span_join (Z 8) 40 160 40 (@span_join (Z 8) 20 160 20 h8y8 h8y9) (@span_join (Z 8) 20 200 20 h8y10 h8y11)) (@span_join (Z 8) 40 240 40 (@span_join (Z 8) 20 240 20 h8y12 h8y13) (@span_join (Z 8) 20 280 20 h8y14 h8y15)))) (@span_join (Z 8) 160 320 175 (@span_join (Z 8) 80 320 80 (@span_join (Z 8) 40 320 40 (@span_join (Z 8) 20 320 20 h8y16 h8y17) (@span_join (Z 8) 20 360 20 h8y18 h8y19)) (@span_join (Z 8) 40 400 40 (@span_join (Z 8) 20 400 20 h8y20 h8y21) (@span_join (Z 8) 20 440 20 h8y22 h8y23))) (@span_join (Z 8) 80 480 95 (@span_join (Z 8) 40 480 40 (@span_join (Z 8) 20 480 20 h8y24 h8y25) (@span_join (Z 8) 20 520 20 h8y26 h8y27)) (@span_join (Z 8) 40 560 55 (@span_join (Z 8) 20 560 20 h8y28 h8y29) (@span_join (Z 8) 20 600 35 h8y30 (@span_join (Z 8) 20 620 15 h8y31 h8y32))))))
theorem h7y0 : span (Z 7) 20 0 = true := by decide +kernel
theorem h7y1 : span (Z 7) 20 20 = true := by decide +kernel
theorem h7y2 : span (Z 7) 20 40 = true := by decide +kernel
theorem h7y3 : span (Z 7) 20 60 = true := by decide +kernel
theorem h7y4 : span (Z 7) 20 80 = true := by decide +kernel
theorem h7y5 : span (Z 7) 20 100 = true := by decide +kernel
theorem h7y6 : span (Z 7) 20 120 = true := by decide +kernel
theorem h7y7 : span (Z 7) 20 140 = true := by decide +kernel
theorem h7y8 : span (Z 7) 20 160 = true := by decide +kernel
theorem h7y9 : span (Z 7) 20 180 = true := by decide +kernel
theorem h7y10 : span (Z 7) 20 200 = true := by decide +kernel
theorem h7y11 : span (Z 7) 20 220 = true := by decide +kernel
theorem h7y12 : span (Z 7) 20 240 = true := by decide +kernel
theorem h7y13 : span (Z 7) 20 260 = true := by decide +kernel
theorem h7y14 : span (Z 7) 20 280 = true := by decide +kernel
theorem h7y15 : span (Z 7) 20 300 = true := by decide +kernel
theorem h7y16 : span (Z 7) 20 320 = true := by decide +kernel
theorem h7y17 : span (Z 7) 20 340 = true := by decide +kernel
theorem h7y18 : span (Z 7) 20 360 = true := by decide +kernel
theorem h7y19 : span (Z 7) 20 380 = true := by decide +kernel
theorem h7y20 : span (Z 7) 20 400 = true := by decide +kernel
theorem h7y21 : span (Z 7) 20 420 = true := by decide +kernel
theorem h7y22 : span (Z 7) 20 440 = true := by decide +kernel
theorem h7y23 : span (Z 7) 20 460 = true := by decide +kernel
theorem h7y24 : span (Z 7) 20 480 = true := by decide +kernel
theorem h7y25 : span (Z 7) 20 500 = true := by decide +kernel
theorem h7y26 : span (Z 7) 20 520 = true := by decide +kernel
theorem h7y27 : span (Z 7) 20 540 = true := by decide +kernel
theorem h7y28 : span (Z 7) 20 560 = true := by decide +kernel
theorem h7y29 : span (Z 7) 20 580 = true := by decide +kernel
theorem h7y30 : span (Z 7) 20 600 = true := by decide +kernel
theorem h7y31 : span (Z 7) 20 620 = true := by decide +kernel
theorem h7y32 : span (Z 7) 20 640 = true := by decide +kernel
theorem h7y33 : span (Z 7) 20 660 = true := by decide +kernel
theorem h7y34 : span (Z 7) 20 680 = true := by decide +kernel
theorem h7y35 : span (Z 7) 20 700 = true := by decide +kernel
theorem h7y36 : span (Z 7) 20 720 = true := by decide +kernel
theorem h7y37 : span (Z 7) 20 740 = true := by decide +kernel
theorem h7y38 : span (Z 7) 12 760 = true := by decide +kernel
theorem z7 : span (Z 7) 772 0 = true := (@span_join (Z 7) 380 0 392 (@span_join (Z 7) 180 0 200 (@span_join (Z 7) 80 0 100 (@span_join (Z 7) 40 0 40 (@span_join (Z 7) 20 0 20 h7y0 h7y1) (@span_join (Z 7) 20 40 20 h7y2 h7y3)) (@span_join (Z 7) 40 80 60 (@span_join (Z 7) 20 80 20 h7y4 h7y5) (@span_join (Z 7) 20 120 40 h7y6 (@span_join (Z 7) 20 140 20 h7y7 h7y8)))) (@span_join (Z 7) 100 180 100 (@span_join (Z 7) 40 180 60 (@span_join (Z 7) 20 180 20 h7y9 h7y10) (@span_join (Z 7) 20 220 40 h7y11 (@span_join (Z 7) 20 240 20 h7y12 h7y13))) (@span_join (Z 7) 40 280 60 (@span_join (Z 7) 20 280 20 h7y14 h7y15) (@span_join (Z 7) 20 320 40 h7y16 (@span_join (Z 7) 20 340 20 h7y17 h7y18))))) (@span_join (Z 7) 200 380 192 (@span_join (Z 7) 100 380 100 (@span_join (Z 7) 40 380 60 (@span_join (Z 7) 20 380 20 h7y19 h7y20) (@span_join (Z 7) 20 420 40 h7y21 (@span_join (Z 7) 20 440 20 h7y22 h7y23))) (@span_join (Z 7) 40 480 60 (@span_join (Z 7) 20 480 20 h7y24 h7y25) (@span_join (Z 7) 20 520 40 h7y26 (@span_join (Z 7) 20 540 20 h7y27 h7y28)))) (@span_join (Z 7) 100 580 92 (@span_join (Z 7) 40 580 60 (@span_join (Z 7) 20 580 20 h7y29 h7y30) (@span_join (Z 7) 20 620 40 h7y31 (@span_join (Z 7) 20 640 20 h7y32 h7y33))) (@span_join (Z 7) 40 680 52 (@span_join (Z 7) 20 680 20 h7y34 h7y35) (@span_join (Z 7) 20 720 32 h7y36 (@span_join (Z 7) 20 740 12 h7y37 h7y38))))))
theorem h6y0 : span (Z 6) 20 0 = true := by decide +kernel
theorem h6y1 : span (Z 6) 20 20 = true := by decide +kernel
theorem h6y2 : span (Z 6) 20 40 = true := by decide +kernel
theorem h6y3 : span (Z 6) 20 60 = true := by decide +kernel
theorem h6y4 : span (Z 6) 20 80 = true := by decide +kernel
theorem h6y5 : span (Z 6) 20 100 = true := by decide +kernel
theorem h6y6 : span (Z 6) 20 120 = true := by decide +kernel
theorem h6y7 : span (Z 6) 20 140 = true := by decide +kernel
theorem h6y8 : span (Z 6) 20 160 = true := by decide +kernel
theorem h6y9 : span (Z 6) 20 180 = true := by decide +kernel
theorem h6y10 : span (Z 6) 20 200 = true := by decide +kernel
theorem h6y11 : span (Z 6) 19 220 = true := by decide +kernel
theorem z6 : span (Z 6) 239 0 = true := (@span_join (Z 6) 120 0 119 (@span_join (Z 6) 60 0 60 (@span_join (Z 6) 20 0 40 h6y0 (@span_join (Z 6) 20 20 20 h6y1 h6y2)) (@span_join (Z 6) 20 60 40 h6y3 (@span_join (Z 6) 20 80 20 h6y4 h6y5))) (@span_join (Z 6) 60 120 59 (@span_join (Z 6) 20 120 40 h6y6 (@span_join (Z 6) 20 140 20 h6y7 h6y8)) (@span_join (Z 6) 20 180 39 h6y9 (@span_join (Z 6) 20 200 19 h6y10 h6y11))))
theorem h5y0 : span (Z 5) 20 0 = true := by decide +kernel
theorem h5y1 : span (Z 5) 6 20 = true := by decide +kernel
theorem z5 : span (Z 5) 26 0 = true := (@span_join (Z 5) 20 0 6 h5y0 h5y1)
theorem z4 : span (Z 4) 0 0 = true := rfl
theorem z3 : span (Z 3) 0 0 = true := rfl
theorem z2 : span (Z 2) 0 0 = true := rfl
theorem z1 : span (Z 1) 0 0 = true := rfl
theorem z0 : span (Z 0) 0 0 = true := rfl

theorem checked (s : Nat) (hs : s ≤ 10) : ∀ i < NN s, Z s i = true := by
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

theorem scr_xs7 : scr 198 7 poolG xsG = true := by decide +kernel
theorem root8 : S 8 25 = xsG := by decide +kernel
theorem root9 : S 9 2 = xsG := by decide +kernel
theorem root10 : S 10 0 = xsG := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 10) (h : NatRun (mask 198) (goal 198) s xsG) : False := by
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
    exact bar_all ori_ok checked 8 (by decide) 25 (by decide) h
  · rw [← root9] at h
    exact bar_all ori_ok checked 9 (by decide) 2 (by decide) h
  · rw [← root10] at h
    exact bar_all ori_ok checked 10 (by decide) 0 (by decide) h

def witness : List Gate := [⟨.and, [2, 6]⟩, ⟨.or, [0, 8]⟩, ⟨.or, [1, 7]⟩, ⟨.or, [2, 3]⟩, ⟨.or, [4, 9]⟩, ⟨.or, [5, 6]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [11, 12]⟩, ⟨.and, [7, 15]⟩, ⟨.and, [13, 14]⟩, ⟨.or, [16, 17]⟩]

theorem witnessBasis : ∀ g ∈ witness,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem witnessCorrect : ∀ x : Fin 8 → Bool,
    Circuit.eval ⟨witness, 18⟩ (List.ofFn x) = fG x := by
  decide +kernel

theorem graph_correct : ∀ x : Fin 8 → Bool, fG x = decide (∃ i < ([0, 5, 1, 5, 0, 6, 1, 6, 2, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 5, 1, 5, 0, 6, 1, 6, 2, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 5, 1, 5, 0, 6, 1, 6, 2, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  decide +kernel

end PEqualNP.Outside.L_meta_14568

open PEqualNP.Outside.L_meta_14568 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.L_meta_14568 :
∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 5, 1, 5, 0, 6, 1, 6, 2, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 5, 1, 5, 0, 6, 1, 6, 2, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 5, 1, 5, 0, 6, 1, 6, 2, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 5, 1, 5, 0, 6, 1, 6, 2, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 5, 1, 5, 0, 6, 1, 6, 2, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 5, 1, 5, 0, 6, 1, 6, 2, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o legal _oneNot computes
  have h : HasCircuitSize 8 fG gates.length :=
    ⟨⟨gates, o⟩, legal, le_rfl, fun x => (computes x).trans (graph_correct x).symm⟩
  have large : 11 ≤ gates.length := by
    by_contra hs
    exact mainG noRunFull ⟨⟨gates, o⟩, legal, by change gates.length ≤ 10; omega, fun x => (computes x).trans (graph_correct x).symm⟩
  have hw : witness.length = 11 := rfl
  exact ⟨witness, 18, witnessBasis, by omega, fun x => (witnessCorrect x).trans (graph_correct x)⟩
