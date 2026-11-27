import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25662

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

section Live

variable {α : Type} [DecidableEq α] (bop : α → α → Finset α) (uop : α → Finset α) (goal : α)

def build : ℕ → Finset α → Prop
  | 0, av => goal ∈ av
  | k + 1, av => build k av ∨
      (∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ z ∈ bop a b, build k (insert z av)) ∨
      (∃ a ∈ av, ∃ z ∈ uop a, build k (insert z av))

def live : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k + 1, s => live k s ∨
      (∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ bop a b, z ∉ s ∧
        ∃ rest : Finset α, s = insert a (insert b rest) ∧ live k (insert z rest)) ∨
      (∃ a ∈ s, ∃ z ∈ uop a, z ∉ s ∧
        ∃ rest : Finset α, s = insert a rest ∧ live k (insert z rest))

variable {bop uop goal}

theorem compress {k : ℕ} {av : Finset α} (h : build bop uop goal k av) :
    ∃ s ⊆ av, live bop uop goal k s := by
  induction k generalizing av with
  | zero => exact ⟨{goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩ | ⟨a, ha, z, hz, tail⟩
    · obtain ⟨s, hs, hrun⟩ := ih skip
      exact ⟨s, hs, Or.inl hrun⟩
    · obtain ⟨t, ht, hrun⟩ := ih tail
      by_cases sub : t ⊆ av
      · exact ⟨t, sub, Or.inl hrun⟩
      · have hzmem : z ∈ t := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : z ∉ av := by
          intro hh
          exact sub ((Finset.insert_eq_of_mem hh) ▸ ht)
        let rest := t.erase z
        have hrest : rest ⊆ av := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (ht hu'.2)).resolve_left hu'.1
        let s := insert a (insert b rest)
        have hs : s ⊆ av := Finset.insert_subset ha (Finset.insert_subset hb hrest)
        refine ⟨s, hs, Or.inr (Or.inl ⟨a, by simp [s], b, by simp [s], hab, z, hz,
          fun h => hzout (hs h), rest, rfl, ?_⟩)⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun
    · obtain ⟨t, ht, hrun⟩ := ih tail
      by_cases sub : t ⊆ av
      · exact ⟨t, sub, Or.inl hrun⟩
      · have hzmem : z ∈ t := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : z ∉ av := by
          intro hh
          exact sub ((Finset.insert_eq_of_mem hh) ▸ ht)
        let rest := t.erase z
        have hrest : rest ⊆ av := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (ht hu'.2)).resolve_left hu'.1
        let s := insert a rest
        have hs : s ⊆ av := Finset.insert_subset ha hrest
        refine ⟨s, hs, Or.inr (Or.inr ⟨a, by simp [s], z, hz,
          fun h => hzout (hs h), rest, rfl, ?_⟩)⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun

theorem live_card {k : ℕ} {s : Finset α} (h : live bop uop goal k s) : s.card ≤ k + 1 := by
  induction k generalizing s with
  | zero => change s = {goal} at h; simp [h]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩ |
        ⟨a, ha, z, hz, hout, rest, rfl, tail⟩
    · exact (ih skip).trans (by omega)
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a (insert b rest)
      have h₂ := Finset.card_insert_le b rest
      omega
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a rest
      omega

theorem live_separates (D : α → Prop) (hd : D goal)
    (hops : ∀ a b, ∀ z ∈ bop a b, D z → D a ∨ D b) (hun : ∀ a, ∀ z ∈ uop a, D z → D a)
    {k : ℕ} {s : Finset α} (h : live bop uop goal k s) : ∃ w ∈ s, D w := by
  induction k generalizing s with
  | zero => change s = {goal} at h; exact ⟨goal, by simp [h], hd⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩ |
        ⟨a, ha, z, hz, hout, rest, rfl, tail⟩
    · exact ih skip
    · obtain ⟨w, hw, hD⟩ := ih tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rcases hops a b w hz hD with h | h
        · exact ⟨a, ha, h⟩
        · exact ⟨b, hb, h⟩
      · exact ⟨w, by simp [hw], hD⟩
    · obtain ⟨w, hw, hD⟩ := ih tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact ⟨a, ha, hun a w hz hD⟩
      · exact ⟨w, by simp [hw], hD⟩

theorem live_tight (D : α → Prop) (hd : D goal)
    (hops : ∀ a b, ∀ z ∈ bop a b, D z → D a ∨ D b)
    {k : ℕ} {s : Finset α} (h : live bop uop goal k s) (hc : s.card = k + 1) : ∃ w ∈ s, D w := by
  induction k generalizing s with
  | zero => change s = {goal} at h; exact ⟨goal, by simp [h], hd⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩ |
        ⟨a, ha, z, hz, hout, rest, rfl, tail⟩
    · have := live_card skip
      omega
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := live_card tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a (insert b rest)
      have h₂ := Finset.card_insert_le b rest
      have hc' : (insert z rest).card = k + 1 := by
        rw [Finset.card_insert_of_notMem hzrest]; omega
      obtain ⟨w, hw, hD⟩ := ih tail hc'
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rcases hops a b w hz hD with h | h
        · exact ⟨a, ha, h⟩
        · exact ⟨b, hb, h⟩
      · exact ⟨w, by simp [hw], hD⟩
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := live_card tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a rest
      omega

theorem build_mono {k : ℕ} {av : Finset α} (h : build bop uop goal k av) :
    ∀ j, k ≤ j → build bop uop goal j av := by
  intro j hj
  induction hj with
  | refl => exact h
  | step _ ih => exact Or.inl ih

end Live

section Lists

def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

theorem pick_one {α : Type} {a : α} {ws : List α} (h : a ∈ ws) :
    ∃ rest, (a, rest) ∈ singles ws ∧ ws.Perm (a :: rest) := by
  induction ws with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with e | h
    · subst x; exact ⟨xs, by simp [singles], .refl _⟩
    · obtain ⟨rest, hm, hp⟩ := ih h
      refine ⟨x :: rest, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a, rest), hm, rfl⟩), ?_⟩
      exact (hp.cons x).trans (.swap _ _ _)

theorem pick_two {α : Type} {a b : α} {ws : List α} (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
    ∃ rest, ((a, b, rest) ∈ pairs ws ∨ (b, a, rest) ∈ pairs ws) ∧
      ws.Perm (a :: b :: rest) := by
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with h | ha
    · subst x
      obtain ⟨r, hm, hp⟩ := pick_one ((List.mem_cons.mp hb).resolve_left (Ne.symm hne))
      exact ⟨r, .inl (List.mem_append_left _ (List.mem_map.mpr ⟨(b, r), hm, rfl⟩)), hp.cons a⟩
    · rcases List.mem_cons.mp hb with h | hb
      · subst x
        obtain ⟨r, hm, hp⟩ := pick_one (ws := xs) (a := a) (by assumption)
        exact ⟨r, .inr (List.mem_append_left _ (List.mem_map.mpr ⟨(a, r), hm, rfl⟩)),
          (hp.cons b).trans (.swap _ _ _)⟩
      · obtain ⟨r, hm, hp⟩ := ih ha hb
        refine ⟨x :: r, ?_,
          (hp.cons x).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons a))⟩
        rcases hm with hm | hm
        · exact .inl (List.mem_append_right _ (List.mem_map.mpr ⟨(a, b, r), hm, rfl⟩))
        · exact .inr (List.mem_append_right _ (List.mem_map.mpr ⟨(b, a, r), hm, rfl⟩))

def keepChoices (a b : ℕ) (r : List ℕ) : List (List ℕ) := [r, a :: r, b :: r, a :: b :: r]

theorem recover_kept {ws r : List ℕ} {a b : ℕ} {needed : Finset ℕ}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v
    simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by
      rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a :: b :: r, by simp [keepChoices], habr, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨a :: r, by simp [keepChoices], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b :: r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

theorem recover_kept1 {ws r : List ℕ} {a : ℕ} {needed : Finset ℕ}
    (hp : ws.Perm (a :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a needed) :
    ∃ kept ∈ [r, a :: r], kept.Nodup ∧ kept.toFinset = needed := by
  have har := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a r.toFinset := by
    ext v
    simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a := by
    intro v
    have he : (v ∈ insert a r.toFinset) ↔ v ∈ insert a needed := by
      rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons] at har
    grind
  by_cases ha : a ∈ needed
  · refine ⟨a :: r, by simp, har, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp, (List.nodup_cons.mp har).2, ?_⟩
    ext v; simp [henne]; grind

theorem singleton_list {ws : List ℕ} {goal : ℕ} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) :
    ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

theorem all_of_chunks {β : Type} (L : List β) (f : β → Bool) (B n : ℕ) (hlen : L.length ≤ B * n)
    (h : ∀ i < n, ((L.drop (B * i)).take B).all f = true) : L.all f = true := by
  rw [List.all_eq_true]
  intro x hx
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
  have hB : 0 < B := by
    rcases Nat.eq_zero_or_pos B with h0 | h0
    · subst h0; rw [Nat.zero_mul] at hlen; omega
    · exact h0
  have hi : j / B < n := by
    rw [Nat.div_lt_iff_lt_mul hB]; rw [Nat.mul_comm] at hlen; omega
  have hmod := Nat.mod_lt j hB
  have hdm := Nat.div_add_mod j B
  have hc := List.all_eq_true.mp (h (j / B) hi)
  apply hc
  rw [List.mem_iff_getElem]
  refine ⟨j % B, ?_, ?_⟩
  · simp only [List.length_take, List.length_drop]
    omega
  · simp only [List.getElem_take, List.getElem_drop]
    congr 1
    all_goals omega

end Lists

section Search

def enc : List Bool → ℕ
  | [] => 0
  | b :: l => b.toNat + 2 * enc l

theorem testBit_enc (l : List Bool) (i : ℕ) : (enc l).testBit i = l.getD i false := by
  induction l generalizing i with
  | nil => simp [enc]
  | cons b l ih =>
    cases i with
    | zero =>
      simp only [enc, Nat.testBit_zero, List.getD_cons_zero]
      cases b <;> simp <;> omega
    | succ i =>
      rw [Nat.testBit_add_one, List.getD_cons_succ, ← ih i]
      congr 1
      simp only [enc]
      cases b <;> simp <;> omega

def maskN (N : ℕ) : ℕ := enc (List.replicate N true)

theorem maskN_testBit (N r : ℕ) : (maskN N).testBit r = decide (r < N) := by
  rw [maskN, testBit_enc]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate]
  by_cases h : r < N <;> simp [h]

variable (goal mask : ℕ) (prs : List (ℕ × ℕ)) (N J : ℕ)

def prsOf : List (ℕ × ℕ) := (List.range J).map (fun j => (N + j, N + J + j))

def sepF (ws : List ℕ) : Bool :=
  (ws.foldr (fun w acc => acc ||| ((w >>> N) ^^^ (w >>> (N + J)))) 0 &&& maskN J) == maskN J

def monF (ws : List ℕ) : Bool :=
  (ws.foldr (fun w acc => acc ||| ((w >>> N) &&& (maskN J ^^^ (w >>> (N + J))))) 0 &&& maskN J)
    == maskN J

theorem foldr_or_testBit (f : ℕ → ℕ) (ws : List ℕ) (i : ℕ) :
    (ws.foldr (fun w acc => acc ||| f w) 0).testBit i = ws.any (fun w => (f w).testBit i) := by
  induction ws with
  | nil => simp
  | cons w ws ih =>
    simp only [List.foldr_cons, Nat.testBit_or, ih, List.any_cons]
    exact Bool.or_comm _ _

def bop (a b : ℕ) : Finset ℕ := {a &&& b, a ||| b}
def uop (a : ℕ) : Finset ℕ := {mask ^^^ a}

def sepOK (ws : List ℕ) : Bool :=
  prs.all (fun pq => ws.any (fun w => w.testBit pq.1 != w.testBit pq.2))

def monOK (ws : List ℕ) : Bool :=
  prs.all (fun pq => ws.any (fun w => w.testBit pq.1 && !w.testBit pq.2))

theorem sepF_of {ws : List ℕ} (h : sepOK (prsOf N J) ws = true) : sepF N J ws = true := by
  simp only [sepOK, prsOf, List.all_map, List.all_eq_true, List.mem_range, Function.comp_def,
    List.any_eq_true, bne_iff_ne] at h
  simp only [sepF, beq_iff_eq]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, maskN_testBit, foldr_or_testBit]
  by_cases hi : i < J
  · obtain ⟨w, hw, hd⟩ := h i hi
    simp only [hi, decide_true, Bool.and_true, List.any_eq_true]
    refine ⟨w, hw, ?_⟩
    rw [Nat.testBit_xor, Nat.testBit_shiftRight, Nat.testBit_shiftRight]
    revert hd
    cases w.testBit (N + i) <;> cases w.testBit (N + J + i) <;> simp
  · simp [hi]

theorem monF_of {ws : List ℕ} (h : monOK (prsOf N J) ws = true) : monF N J ws = true := by
  simp only [monOK, prsOf, List.all_map, List.all_eq_true, List.mem_range, Function.comp_def,
    List.any_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at h
  simp only [monF, beq_iff_eq]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, maskN_testBit, foldr_or_testBit]
  by_cases hi : i < J
  · obtain ⟨w, hw, hd1, hd2⟩ := h i hi
    simp only [hi, decide_true, Bool.and_true, List.any_eq_true]
    refine ⟨w, hw, ?_⟩
    rw [Nat.testBit_and, Nat.testBit_xor, Nat.testBit_shiftRight, Nat.testBit_shiftRight,
      maskN_testBit, hd1, hd2]
    simp [hi]
  · simp [hi]

variable (nt : Bool)

def uopN (a : ℕ) : Finset ℕ := if nt then {mask ^^^ a} else ∅

def chk (k : ℕ) (ws : List ℕ) : Bool :=
  decide (ws.length ≤ k + 2) && sepF N J ws && ((nt && ws.length != k + 2) || monF N J ws)

def LS : ℕ → List ℕ → Bool
  | 0, ws => ws == [goal]
  | k + 1, ws => ws == [goal] ||
      (chk N J nt k ws &&
        ((pairs ws).any (fun t => [t.1 &&& t.2.1, t.1 ||| t.2.1].any (fun z =>
            !ws.contains z && (keepChoices t.1 t.2.1 t.2.2).any (fun kept => LS k (z :: kept)))) ||
         (nt && (singles ws).any (fun t => !ws.contains (mask ^^^ t.1) &&
            [t.2, t.1 :: t.2].any (fun kept => LS k ((mask ^^^ t.1) :: kept))))))

theorem chk_mono {k : ℕ} {ws : List ℕ} (h : chk N J nt k ws = true) : chk N J nt (k + 1) ws = true := by
  simp only [chk, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne] at h ⊢
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨⟨by omega, h2⟩, ?_⟩
  rcases h3 with ⟨hn, hl⟩ | h
  · exact Or.inl ⟨hn, by omega⟩
  · exact Or.inr h

theorem LS_mono : ∀ k ws, LS goal mask N J nt k ws = true → LS goal mask N J nt (k + 1) ws = true := by
  intro k
  induction k with
  | zero =>
    intro ws h
    simp only [LS] at h ⊢
    simp [h]
  | succ k ih =>
    intro ws h
    rw [LS] at h
    rw [LS]
    simp only [Bool.or_eq_true, Bool.and_eq_true, List.any_eq_true] at h ⊢
    rcases h with h | ⟨hc, h⟩
    · exact Or.inl h
    · refine Or.inr ⟨chk_mono N J nt hc, ?_⟩
      rcases h with ⟨t, ht, z, hz, hc, kept, hk, hr⟩ | ⟨hnt, t, ht, hc, kept, hk, hr⟩
      · exact Or.inl ⟨t, ht, z, hz, hc, kept, hk, ih _ hr⟩
      · exact Or.inr ⟨hnt, t, ht, hc, kept, hk, ih _ hr⟩

theorem bop_comm (a b : ℕ) : bop a b = bop b a := by
  simp [bop, Nat.land_comm, Nat.lor_comm, Finset.pair_comm]

def Dpq (pq : ℕ × ℕ) (w : ℕ) : Prop := w.testBit pq.1 ≠ w.testBit pq.2

theorem bop_D (pq : ℕ × ℕ) (a b z : ℕ) (hz : z ∈ bop a b) (hdz : Dpq pq z) : Dpq pq a ∨ Dpq pq b := by
  simp only [bop, Finset.mem_insert, Finset.mem_singleton] at hz
  unfold Dpq at hdz ⊢
  rcases hz with rfl | rfl <;> revert hdz <;>
    simp only [Nat.testBit_and, Nat.testBit_or] <;>
    cases a.testBit pq.1 <;> cases a.testBit pq.2 <;>
    cases b.testBit pq.1 <;> cases b.testBit pq.2 <;> simp

theorem bop_O (pq : ℕ × ℕ) (a b z : ℕ) (hz : z ∈ bop a b)
    (hdz : z.testBit pq.1 = true ∧ z.testBit pq.2 = false) :
    (a.testBit pq.1 = true ∧ a.testBit pq.2 = false) ∨
      (b.testBit pq.1 = true ∧ b.testBit pq.2 = false) := by
  simp only [bop, Finset.mem_insert, Finset.mem_singleton] at hz
  rcases hz with rfl | rfl <;> revert hdz <;>
    simp only [Nat.testBit_and, Nat.testBit_or] <;>
    cases a.testBit pq.1 <;> cases a.testBit pq.2 <;>
    cases b.testBit pq.1 <;> cases b.testBit pq.2 <;> simp

theorem sep_of_live (hD : ∀ pq ∈ prs, Dpq pq goal)
    (hM : ∀ pq ∈ prs, mask.testBit pq.1 = mask.testBit pq.2)
    {k : ℕ} {ws : List ℕ} (h : live bop (uopN mask nt) goal k ws.toFinset) :
    sepOK prs ws = true := by
  simp only [sepOK, List.all_eq_true, List.any_eq_true, bne_iff_ne]
  intro pq hpq
  obtain ⟨w, hw, hd⟩ := live_separates (Dpq pq) (hD pq hpq) (bop_D pq)
    (by
      intro a z hz hdz
      unfold uopN at hz
      split at hz
      · simp only [Finset.mem_singleton] at hz
        subst hz
        unfold Dpq at hdz ⊢
        have hm := hM pq hpq
        revert hdz
        simp only [Nat.testBit_xor, hm]
        cases mask.testBit pq.2 <;> cases a.testBit pq.1 <;> cases a.testBit pq.2 <;> simp
      · simp at hz) h
  exact ⟨w, List.mem_toFinset.mp hw, hd⟩

theorem mon_of_live (hO : ∀ pq ∈ prs, goal.testBit pq.1 = true ∧ goal.testBit pq.2 = false)
    {k : ℕ} {ws : List ℕ} (hn : ws.Nodup) (h : live bop (uopN mask nt) goal k ws.toFinset)
    (hc : nt = false ∨ ws.length = k + 1) : monOK prs ws = true := by
  simp only [monOK, List.all_eq_true, List.any_eq_true, Bool.and_eq_true, Bool.not_eq_true']
  intro pq hpq
  rcases hc with hnt | hc
  · obtain ⟨w, hw, hd⟩ := live_separates (fun w => w.testBit pq.1 = true ∧ w.testBit pq.2 = false)
      (hO pq hpq) (bop_O pq) (by intro a z hz; simp [uopN, hnt] at hz) h
    exact ⟨w, List.mem_toFinset.mp hw, hd⟩
  · obtain ⟨w, hw, hd⟩ := live_tight (fun w => w.testBit pq.1 = true ∧ w.testBit pq.2 = false)
      (hO pq hpq) (bop_O pq) h (by rw [List.toFinset_card_of_nodup hn, hc])
    exact ⟨w, List.mem_toFinset.mp hw, hd⟩

theorem chk_of_live (hD : ∀ pq ∈ prsOf N J, Dpq pq goal)
    (hM : ∀ pq ∈ prsOf N J, mask.testBit pq.1 = mask.testBit pq.2)
    (hO : ∀ pq ∈ prsOf N J, goal.testBit pq.1 = true ∧ goal.testBit pq.2 = false)
    {k : ℕ} {ws : List ℕ} (hn : ws.Nodup)
    (h : live bop (uopN mask nt) goal (k + 1) ws.toFinset) : chk N J nt k ws = true := by
  have hcard := live_card h
  rw [List.toFinset_card_of_nodup hn] at hcard
  have hsep := sepF_of N J (sep_of_live goal mask (prsOf N J) nt hD hM h)
  simp only [chk, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, bne_iff_ne]
  refine ⟨⟨hcard, hsep⟩, ?_⟩
  by_cases hnt : nt = true
  · by_cases hl : ws.length = k + 2
    · exact Or.inr (monF_of N J (mon_of_live goal mask (prsOf N J) nt hO hn h (Or.inr hl)))
    · exact Or.inl ⟨hnt, hl⟩
  · exact Or.inr (monF_of N J (mon_of_live goal mask (prsOf N J) nt hO hn h
      (Or.inl (by simpa using hnt))))

theorem LS_complete (hD : ∀ pq ∈ prsOf N J, Dpq pq goal)
    (hM : ∀ pq ∈ prsOf N J, mask.testBit pq.1 = mask.testBit pq.2)
    (hO : ∀ pq ∈ prsOf N J, goal.testBit pq.1 = true ∧ goal.testBit pq.2 = false) :
    ∀ k (ws : List ℕ), ws.Nodup → live bop (uopN mask nt) goal k ws.toFinset →
      LS goal mask N J nt k ws = true := by
  intro k
  induction k with
  | zero =>
    intro ws hn h
    simp [LS, singleton_list hn h]
  | succ k ih =>
    intro ws hn h
    have hchk := chk_of_live goal mask N J nt hD hM hO hn h
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩ |
        ⟨a, ha, z, hz, hout, needed, hs, tail⟩
    · exact LS_mono goal mask N J nt k ws (ih ws hn skip)
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have hzc : ws.contains z = false := by
        simpa using fun hh => hout (List.mem_toFinset.mpr hh)
      have go {a b : ℕ} (perm : ws.Perm (a :: b :: r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ bop a b) :
          [a &&& b, a ||| b].any (fun z =>
            !ws.contains z && (keepChoices a b r).any (fun kept => LS goal mask N J nt k (z :: kept)))
            = true := by
        obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn hset
        have hznew : z ∉ kept := by
          intro hu
          apply hout
          rw [hset]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
            (hfin ▸ (List.mem_toFinset.mpr hu)))
        have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
        have hl : live bop (uopN mask nt) goal k (z :: kept).toFinset := by
          simpa [hfin] using tail
        have hrec := ih _ hnd hl
        simp only [List.any_eq_true, Bool.and_eq_true, Bool.not_eq_true']
        refine ⟨z, ?_, hzc, kept, hk, hrec⟩
        simp only [bop, Finset.mem_insert, Finset.mem_singleton] at hop
        rcases hop with rfl | rfl <;> simp
      simp only [LS, Bool.or_eq_true, Bool.and_eq_true]
      right
      refine ⟨hchk, Or.inl ?_⟩
      simp only [List.any_eq_true]
      rcases hm with direct | swap
      · exact ⟨(a, b, r), direct, by simpa using go hp hs hz⟩
      · exact ⟨(b, a, r), swap, by
          simpa using go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm])
            (bop_comm a b ▸ hz)⟩
    · obtain ⟨r, hm, hp⟩ := pick_one (List.mem_toFinset.mp ha)
      by_cases hnt : nt = true
      · simp only [uopN, hnt, if_true, Finset.mem_singleton] at hz
        subst hz
        have hzc : ws.contains (mask ^^^ a) = false := by
          simpa using fun hh => hout (List.mem_toFinset.mpr hh)
        obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept1 hp hn hs
        have hznew : (mask ^^^ a) ∉ kept := by
          intro hu
          apply hout
          rw [hs]
          exact Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu))
        have hnd : ((mask ^^^ a) :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
        have hl : live bop (uopN mask nt) goal k ((mask ^^^ a) :: kept).toFinset := by
          simpa [hfin] using tail
        have hrec := ih _ hnd hl
        simp only [LS, Bool.or_eq_true, Bool.and_eq_true]
        right
        refine ⟨hchk, Or.inr ⟨hnt, ?_⟩⟩
        simp only [List.any_eq_true, Bool.and_eq_true, Bool.not_eq_true']
        exact ⟨(a, r), hm, hzc, kept, hk, hrec⟩
      · simp [uopN, hnt] at hz

def kidsN (ws : List ℕ) : List (List ℕ) :=
  (pairs ws).flatMap (fun t => [t.1 &&& t.2.1, t.1 ||| t.2.1].flatMap (fun z =>
      if ws.contains z then [] else (keepChoices t.1 t.2.1 t.2.2).map (fun kept => z :: kept))) ++
  (if nt then (singles ws).flatMap (fun t =>
      if ws.contains (mask ^^^ t.1) then [] else
        [t.2, t.1 :: t.2].map (fun kept => (mask ^^^ t.1) :: kept)) else [])

def expand (k : ℕ) (L : List (List ℕ)) : List (List ℕ) :=
  L.flatMap (fun ws => if chk N J nt k ws then kidsN mask nt ws else [])

theorem LS_split {k : ℕ} {ws : List ℕ} (h : LS goal mask N J nt (k + 1) ws = true) :
    ws = [goal] ∨ ∃ c ∈ kidsN mask nt ws, chk N J nt k ws = true ∧ LS goal mask N J nt k c = true := by
  rw [LS] at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, List.any_eq_true, beq_iff_eq,
    Bool.not_eq_true'] at h
  rcases h with h | ⟨hc, ⟨t, ht, z, hz, hzc, kept, hk, hr⟩ | ⟨hnt, t, ht, hzc, kept, hk, hr⟩⟩
  · exact Or.inl h
  · right
    refine ⟨z :: kept, ?_, hc, hr⟩
    unfold kidsN
    apply List.mem_append_left
    rw [List.mem_flatMap]
    refine ⟨t, ht, ?_⟩
    rw [List.mem_flatMap]
    refine ⟨z, hz, ?_⟩
    rw [hzc]
    exact List.mem_map.mpr ⟨kept, hk, rfl⟩
  · right
    refine ⟨(mask ^^^ t.1) :: kept, ?_, hc, hr⟩
    unfold kidsN
    apply List.mem_append_right
    rw [hnt, if_pos rfl, List.mem_flatMap]
    refine ⟨t, ht, ?_⟩
    rw [hzc]
    exact List.mem_map.mpr ⟨kept, hk, rfl⟩

theorem split_all (k : ℕ) (L : List (List ℕ)) (h1 : L.all (fun ws => !(ws == [goal])) = true)
    (h2 : (expand mask N J nt k L).all (fun c => !LS goal mask N J nt k c) = true) :
    L.all (fun ws => !LS goal mask N J nt (k + 1) ws) = true := by
  rw [List.all_eq_true]
  intro ws hws
  cases e : LS goal mask N J nt (k + 1) ws
  · rfl
  · exfalso
    rcases LS_split goal mask N J nt e with hg | ⟨c, hc, hck, hl⟩
    · have := List.all_eq_true.mp h1 ws hws
      simp [hg] at this
    · have hmem : c ∈ expand mask N J nt k L := by
        unfold expand
        rw [List.mem_flatMap]
        exact ⟨ws, hws, by rw [hck, if_pos rfl]; exact hc⟩
      have := List.all_eq_true.mp h2 c hmem
      simp [hl] at this

end Search

section Circ

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def beh (W : List (List Bool)) (i : ℕ) : ℕ := enc (W.map fun w => w.getD i false)

theorem getD_map_row (W : List (List Bool)) (i r : ℕ) :
    (W.map fun w => w.getD i false).getD r false = (W.getD r []).getD i false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases W[r]? <;> simp

theorem beh_testBit (W : List (List Bool)) (i r : ℕ) :
    (beh W i).testBit r = (W.getD r []).getD i false := by
  rw [beh, testBit_enc, getD_map_row]

theorem row_of_lt {W : List (List Bool)} {r : ℕ} (h : r < W.length) :
    W.getD r [] ∈ W := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]
  exact List.getElem_mem h

theorem row_of_ge {W : List (List Bool)} {r : ℕ} (h : W.length ≤ r) : W.getD r [] = [] := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem getD_step_ne {w : List Bool} {g : Gate} {i : ℕ} (hi : i ≠ w.length) :
    (step w g).getD i false = w.getD i false := by
  simp only [step, List.getD_eq_getElem?_getD]
  rcases Nat.lt_or_gt_of_ne hi with h | h
  · rw [List.getElem?_append_left h]
  · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

theorem getD_step_eq {w : List Bool} {g : Gate} :
    (step w g).getD w.length false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  simp [step, List.getD_eq_getElem?_getD]

theorem mapstep_row (W : List (List Bool)) (g : Gate) (r : ℕ) :
    (W.map (fun w => step w g)).getD r [] =
      if r < W.length then step (W.getD r []) g else [] := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  by_cases h : r < W.length
  · simp [h, List.getElem?_eq_getElem h]
  · simp [h, List.getElem?_eq_none (Nat.le_of_not_lt h)]

theorem beh_old {W : List (List Bool)} {L : ℕ} (hl : ∀ w ∈ W, w.length = L) (g : Gate) {i : ℕ}
    (hi : i ≠ L) : beh (W.map (fun w => step w g)) i = beh W i := by
  apply Nat.eq_of_testBit_eq
  intro r
  rw [beh_testBit, beh_testBit, mapstep_row]
  by_cases h : r < W.length
  · simp only [h, ↓reduceIte]
    rw [getD_step_ne (by rw [hl _ (row_of_lt h)]; exact hi)]
  · simp only [h, ↓reduceIte]
    rw [row_of_ge (Nat.le_of_not_lt h)]

theorem beh_beyond {W : List (List Bool)} {L : ℕ} (hl : ∀ w ∈ W, w.length = L) {i : ℕ}
    (hi : L ≤ i) : beh W i = 0 := by
  apply Nat.eq_of_testBit_eq
  intro r
  rw [beh_testBit, Nat.zero_testBit]
  by_cases h : r < W.length
  · have h2 : (W.getD r []).length ≤ i := by rw [hl _ (row_of_lt h)]; exact hi
    exact List.getD_eq_default _ _ h2
  · rw [row_of_ge (Nat.le_of_not_lt h)]
    rfl

def okGate (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem beh_new {W : List (List Bool)} {L N : ℕ} (hl : ∀ w ∈ W, w.length = L)
    (hN : W.length = N) (g : Gate) (z : ℕ)
    (hz : ∀ r, (r < N → z.testBit r =
        g.op.eval (g.inputs.map fun i => (W.getD r []).getD i false)) ∧
      (N ≤ r → z.testBit r = false)) :
    beh (W.map (fun w => step w g)) L = z := by
  apply Nat.eq_of_testBit_eq
  intro r
  rw [beh_testBit, mapstep_row]
  by_cases h : r < W.length
  · simp only [h, ↓reduceIte]
    have hm := row_of_lt h
    have := getD_step_eq (w := W.getD r []) (g := g)
    rw [hl _ hm] at this
    rw [this, (hz r).1 (hN ▸ h)]
  · simp only [h, ↓reduceIte]
    rw [(hz r).2 (by omega)]
    rfl

theorem gate_step {W : List (List Bool)} {L N : ℕ} (hl : ∀ w ∈ W, w.length = L)
    (hN : W.length = N) (av : Finset ℕ) (hmask : maskN N ∈ av) (hinv : ∀ i, beh W i ∈ av)
    (g : Gate) (hg : okGate g) :
    ∃ z, (z ∈ av ∨ (∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ z ∈ bop a b) ∨
        (g.op = GateOp.not ∧ ∃ a ∈ av, z ∈ uop (maskN N) a)) ∧
      beh (W.map (fun w => step w g)) L = z := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  simp only at hlen
  have hbeyond := beh_beyond hl (le_refl L)
  have hi : ∀ i r, N ≤ r → (beh W i).testBit r = false := by
    intro i r hr
    rw [beh_testBit, row_of_ge (by omega)]
    rfl
  have hmk : ∀ r, N ≤ r → (maskN N).testBit r = false := by
    intro r hr
    rw [maskN_testBit]
    simp; omega
  have hmk' : ∀ r, r < N → (maskN N).testBit r = true := by
    intro r hr
    rw [maskN_testBit]
    simp; omega
  match inputs, hlen with
  | [], _ =>
    rcases hop with rfl | rfl | rfl
    · refine ⟨maskN N, Or.inl hmask, beh_new hl hN _ _ ?_⟩
      intro r
      exact ⟨fun hr => by simp [hmk' r hr, GateOp.eval], fun hr => hmk r hr⟩
    · refine ⟨0, Or.inl (hbeyond ▸ hinv L), beh_new hl hN _ _ ?_⟩
      intro r
      exact ⟨fun _ => by simp [GateOp.eval], fun _ => by simp⟩
    · refine ⟨maskN N, Or.inl hmask, beh_new hl hN _ _ ?_⟩
      intro r
      exact ⟨fun hr => by simp [hmk' r hr, GateOp.eval], fun hr => hmk r hr⟩
  | [i], _ =>
    rcases hop with rfl | rfl | rfl
    · refine ⟨beh W i, Or.inl (hinv i), beh_new hl hN _ _ ?_⟩
      intro r
      exact ⟨fun _ => by simp [beh_testBit, GateOp.eval], fun hr => hi i r hr⟩
    · refine ⟨beh W i, Or.inl (hinv i), beh_new hl hN _ _ ?_⟩
      intro r
      exact ⟨fun _ => by simp [beh_testBit, GateOp.eval], fun hr => hi i r hr⟩
    · refine ⟨maskN N ^^^ beh W i, Or.inr (Or.inr ⟨rfl, beh W i, hinv i, by simp [uop]⟩),
        beh_new hl hN _ _ ?_⟩
      intro r
      exact ⟨fun hr => by simp [Nat.testBit_xor, hmk' r hr, beh_testBit, GateOp.eval],
        fun hr => by simp [Nat.testBit_xor, hmk r hr, hi i r hr]⟩
  | [i, j], _ =>
    rcases hop with rfl | rfl | rfl
    · refine ⟨beh W i &&& beh W j, ?_, beh_new hl hN _ _ ?_⟩
      · by_cases e : beh W i = beh W j
        · left; rw [e, Nat.and_self]; exact hinv j
        · right; left; exact ⟨_, hinv i, _, hinv j, e, by simp [bop]⟩
      · intro r
        exact ⟨fun _ => by simp [Nat.testBit_and, beh_testBit, GateOp.eval],
          fun hr => by simp [Nat.testBit_and, hi i r hr]⟩
    · refine ⟨beh W i ||| beh W j, ?_, beh_new hl hN _ _ ?_⟩
      · by_cases e : beh W i = beh W j
        · left; rw [e, Nat.or_self]; exact hinv j
        · right; left; exact ⟨_, hinv i, _, hinv j, e, by simp [bop]⟩
      · intro r
        exact ⟨fun _ => by simp [Nat.testBit_or, beh_testBit, GateOp.eval],
          fun hr => by simp [Nat.testBit_or, hi i r hr, hi j r hr]⟩
    · refine ⟨maskN N ^^^ beh W i, Or.inr (Or.inr ⟨rfl, beh W i, hinv i, by simp [uop]⟩),
        beh_new hl hN _ _ ?_⟩
      intro r
      exact ⟨fun hr => by simp [Nat.testBit_xor, hmk' r hr, beh_testBit, GateOp.eval],
        fun hr => by simp [Nat.testBit_xor, hmk r hr, hi i r hr]⟩
  | _ :: _ :: _ :: _, h => simp at h

def stepAll (gs : List Gate) (W : List (List Bool)) : List (List Bool) :=
  gs.foldl (fun W g => W.map (fun w => step w g)) W

theorem stepAll_eq (gs : List Gate) :
    ∀ W, stepAll gs W = W.map (fun w => gs.foldl step w) := by
  induction gs with
  | nil => intro W; simp [stepAll]
  | cons g gs ih =>
    intro W
    show stepAll gs (W.map (fun w => step w g)) = _
    rw [ih, List.map_map]
    rfl

def okN (nt : Bool) (g : Gate) : Prop := okGate g ∧ (nt = false → g.op ≠ GateOp.not)

theorem to_buildN (nt : Bool) (N goal : ℕ) (gs : List Gate) (hg : ∀ g ∈ gs, okN nt g) :
    ∀ (L : ℕ) (W : List (List Bool)) (av : Finset ℕ), (∀ w ∈ W, w.length = L) → W.length = N →
      maskN N ∈ av → (∀ i, beh W i ∈ av) → ∀ o, beh (stepAll gs W) o = goal →
      build bop (uopN (maskN N) nt) goal gs.length av := by
  induction gs with
  | nil =>
    intro L W av _ _ _ hinv o ho
    exact ho ▸ hinv o
  | cons g gs ih =>
    intro L W av hl hN hm hinv o ho
    obtain ⟨z, hz, hbz⟩ := gate_step hl hN av hm hinv g (hg g (by simp)).1
    have hl' : ∀ w ∈ W.map (fun w => step w g), w.length = L + 1 := by
      intro w hw
      obtain ⟨w0, hw0, rfl⟩ := List.mem_map.mp hw
      simp [step, hl w0 hw0]
    have hN' : (W.map (fun w => step w g)).length = N := by simp [hN]
    have hinv' : ∀ i, beh (W.map (fun w => step w g)) i ∈ insert z av := by
      intro i
      by_cases hi : i = L
      · subst hi; rw [hbz]; exact Finset.mem_insert_self _ _
      · rw [beh_old hl g hi]; exact Finset.mem_insert_of_mem (hinv i)
    have hrec := ih (fun g hg' => hg g (List.mem_cons_of_mem _ hg')) (L + 1) _ (insert z av)
      hl' hN' (Finset.mem_insert_of_mem hm) hinv' o ho
    rw [List.length_cons]
    rcases hz with hz | ⟨a, ha, b, hb, hab, hz⟩ | ⟨hop, a, ha, hz⟩
    · rw [Finset.insert_eq_of_mem hz] at hrec; exact Or.inl hrec
    · exact Or.inr (Or.inl ⟨a, ha, b, hb, hab, z, hz, hrec⟩)
    · by_cases hnt : nt = true
      · refine Or.inr (Or.inr ⟨a, ha, z, ?_, hrec⟩)
        simp only [uop, Finset.mem_singleton] at hz
        simp [uopN, hnt, hz]
      · exact absurd hop ((hg g (by simp)).2 (by simpa using hnt))

def rowsOf (n m : ℕ) (ex : List (Fin n × Fin m)) : List (List Bool) :=
  ((List.finRange n).flatMap fun u => (List.finRange m).map fun v => oneEach u v) ++
    ex.map (fun p => oneEach p.1 p.2)

def goalOf {n m : ℕ} (A : Fin n → Fin m → Bool) (ex : List (Fin n × Fin m)) : List Bool :=
  ((List.finRange n).flatMap fun u => (List.finRange m).map fun v => A u v) ++
    ex.map (fun p => A p.1 p.2)

theorem rows_len (n m : ℕ) (ex : List (Fin n × Fin m)) :
    ∀ w ∈ rowsOf n m ex, w.length = n + m := by
  intro w hw
  simp only [rowsOf, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_finRange,
    true_and] at hw
  rcases hw with ⟨u, v, rfl⟩ | ⟨p, _, rfl⟩ <;> simp [oneEach]

theorem core (X : List (List Bool)) (L : ℕ) (hX : ∀ x ∈ X, x.length = L) (tl : List Bool)
    (nt : Bool) (K Nb J Nt goal mask : ℕ) (init : List ℕ)
    (hN : X.length = Nt) (hgoal : enc tl = goal) (hmask : maskN Nt = mask)
    (hinit : ((List.range L).all (fun i => init.contains (beh X i)) &&
      init.contains 0 && init.contains mask) = true)
    (hnd : init.Nodup)
    (hprs : (List.range J).all (fun j => (goal.testBit (Nb + j) && !goal.testBit (Nb + J + j)) &&
      (mask.testBit (Nb + j) == mask.testBit (Nb + J + j))) = true)
    (hsearch : init.sublists.all (fun l => !LS goal mask Nb J nt K l) = true)
    (C : Circuit) (hF : ∀ g ∈ C.gates, okN nt g) (hs : C.size ≤ K)
    (hev : X.map (fun x => C.eval x) = tl) : False := by
  simp only [Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem, List.mem_range] at hinit
  obtain ⟨⟨hinp, h0⟩, hm⟩ := hinit
  have hinv : ∀ i, beh X i ∈ init.toFinset := by
    intro i
    rw [List.mem_toFinset]
    by_cases h : i < L
    · exact hinp i h
    · rw [beh_beyond hX (Nat.le_of_not_lt h)]; exact h0
  have hfin : beh (stepAll C.gates X) C.output = goal := by
    rw [← hgoal, ← hev, beh, stepAll_eq, List.map_map]
    rfl
  have hb := to_buildN nt Nt goal C.gates hF L X init.toFinset hX hN
    (by rw [hmask]; exact List.mem_toFinset.mpr hm) hinv C.output hfin
  rw [hmask] at hb
  have hb' := build_mono hb K hs
  obtain ⟨S, hS, hlive⟩ := compress hb'
  have hall : ∀ pq ∈ prsOf Nb J, (goal.testBit pq.1 = true ∧ goal.testBit pq.2 = false) ∧
      mask.testBit pq.1 = mask.testBit pq.2 := by
    intro pq hpq
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hpq
    have := List.all_eq_true.mp hprs j hj
    simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at this
    exact this
  have hO : ∀ pq ∈ prsOf Nb J, goal.testBit pq.1 = true ∧ goal.testBit pq.2 = false :=
    fun pq hpq => (hall pq hpq).1
  have hD : ∀ pq ∈ prsOf Nb J, Dpq pq goal := by
    intro pq hpq
    have := hO pq hpq
    unfold Dpq
    rw [this.1, this.2]
    simp
  have hM : ∀ pq ∈ prsOf Nb J, mask.testBit pq.1 = mask.testBit pq.2 :=
    fun pq hpq => (hall pq hpq).2
  let l := init.filter (fun x => decide (x ∈ S))
  have hl_sub : l ∈ init.sublists := List.mem_sublists.mpr List.filter_sublist
  have hl_nd : l.Nodup := hnd.filter _
  have hl_fs : l.toFinset = S := by
    ext x
    simp only [l, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨List.mem_toFinset.mp (hS h), h⟩⟩
  have hc := LS_complete goal mask Nb J nt hD hM hO K l hl_nd (hl_fs ▸ hlive)
  have hf := List.all_eq_true.mp hsearch l hl_sub
  rw [hc] at hf
  exact Bool.noConfusion hf

theorem rows_eval {n m : ℕ} (A : Fin n → Fin m → Bool) (ex : List (Fin n × Fin m)) (C : Circuit)
    (hr : Represents A C) : (rowsOf n m ex).map (fun x => C.eval x) = goalOf A ex := by
  simp only [rowsOf, goalOf, List.map_append, List.map_flatMap, List.map_map]
  congr 1
  · congr 1
    funext u
    apply List.map_congr_left
    intro v _
    exact hr u v
  · apply List.map_congr_left
    intro p _
    exact hr p.1 p.2

theorem refuteM {n m : ℕ} (A : Fin n → Fin m → Bool) (K Nb J Nt goal mask : ℕ) (init : List ℕ)
    (ex : List (Fin n × Fin m))
    (hN : (rowsOf n m ex).length = Nt) (hgoal : enc (goalOf A ex) = goal) (hmask : maskN Nt = mask)
    (hinit : ((List.range (n + m)).all (fun i => init.contains (beh (rowsOf n m ex) i)) &&
      init.contains 0 && init.contains mask) = true)
    (hnd : init.Nodup)
    (hprs : (List.range J).all (fun j => (goal.testBit (Nb + j) && !goal.testBit (Nb + J + j)) &&
      (mask.testBit (Nb + j) == mask.testBit (Nb + J + j))) = true)
    (hsearch : init.sublists.all (fun l => !LS goal mask Nb J false K l) = true) :
    ¬ PEqualNP.Represents.RepSizeAtMost A K := by
  rintro ⟨C, hC, hs, hr⟩
  refine core (rowsOf n m ex) (n + m) (rows_len n m ex) (goalOf A ex) false K Nb J Nt goal mask
    init hN hgoal hmask hinit hnd hprs hsearch C ?_ hs (rows_eval A ex C hr)
  intro g hg
  obtain ⟨hop, hl⟩ := hC g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  refine ⟨⟨by rcases hop with h | h <;> simp [h], hl⟩, fun _ => ?_⟩
  rcases hop with h | h <;> rw [h] <;> simp

theorem refuteF {n m : ℕ} (A : Fin n → Fin m → Bool) (K Nb J Nt goal mask : ℕ) (init : List ℕ)
    (ex : List (Fin n × Fin m))
    (hN : (rowsOf n m ex).length = Nt) (hgoal : enc (goalOf A ex) = goal) (hmask : maskN Nt = mask)
    (hinit : ((List.range (n + m)).all (fun i => init.contains (beh (rowsOf n m ex) i)) &&
      init.contains 0 && init.contains mask) = true)
    (hnd : init.Nodup)
    (hprs : (List.range J).all (fun j => (goal.testBit (Nb + j) && !goal.testBit (Nb + J + j)) &&
      (mask.testBit (Nb + j) == mask.testBit (Nb + J + j))) = true)
    (hsearch : init.sublists.all (fun l => !LS goal mask Nb J true K l) = true) :
    ¬ ∃ C : Circuit, FanInTwo C ∧ C.size ≤ K ∧ Represents A C := by
  rintro ⟨C, hC, hs, hr⟩
  exact core (rowsOf n m ex) (n + m) (rows_len n m ex) (goalOf A ex) true K Nb J Nt goal mask
    init hN hgoal hmask hinit hnd hprs hsearch C (fun g hg => ⟨hC g hg, by simp⟩) hs
    (rows_eval A ex C hr)

def twoRow (p : Fin 6 × Fin 6) : List Bool := List.ofFn fun k : Fin 6 => decide (k = p.1 ∨ k = p.2)

def twoGoal (M : ℕ) (p : Fin 6 × Fin 6) : Bool :=
  M.testBit (6 * min p.1.val p.2.val + max p.1.val p.2.val)

theorem refuteT (M K Nb J Nt goal mask : ℕ) (init : List ℕ) (ex : List (Fin 6 × Fin 6))
    (hN : (ex.map twoRow).length = Nt) (hgoal : enc (ex.map (twoGoal M)) = goal)
    (hmask : maskN Nt = mask)
    (hinit : ((List.range 6).all (fun i => init.contains (beh (ex.map twoRow) i)) &&
      init.contains 0 && init.contains mask) = true)
    (hnd : init.Nodup)
    (hprs : (List.range J).all (fun j => (goal.testBit (Nb + j) && !goal.testBit (Nb + J + j)) &&
      (mask.testBit (Nb + j) == mask.testBit (Nb + J + j))) = true)
    (hsearch : init.sublists.all (fun l => !LS goal mask Nb J true K l) = true) :
    ¬ ∃ C : Circuit, FanInTwo C ∧ C.size ≤ K ∧ ∀ i j : Fin 6,
      C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
        M.testBit (6 * min i.val j.val + max i.val j.val) := by
  rintro ⟨C, hC, hs, hr⟩
  refine core (ex.map twoRow) 6 ?_ (ex.map (twoGoal M)) true K Nb J Nt goal mask
    init hN hgoal hmask hinit hnd hprs hsearch C (fun g hg => ⟨hC g hg, by simp⟩) hs ?_
  · intro x hx
    obtain ⟨p, _, rfl⟩ := List.mem_map.mp hx
    simp [twoRow]
  · rw [List.map_map]
    apply List.map_congr_left
    intro p _
    exact hr p.1 p.2

end Circ

def G : ℕ := 618970019642690137447465113
def MK : ℕ := 182687704666362864775460604089535377456991567871
def I : List ℕ := [9756650461692823381407865994663388684222527, 168650672266404519068933922849041954086324162, 2678897455339086649055657019185201210233747588, 20360735706344109136505303160101888829637759240, 74975677376482907904633990729057094109651345936, 149956929981801068851200202381240811799216538656, 0, 182687704666362864775460604089535377456991567871]
def E : List (Fin 6 × Fin 6) := [(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 2), (2, 3), (2, 4), (2, 5), (3, 3), (3, 4), (3, 5), (4, 4), (4, 5), (5, 5), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 3), (0, 3), (0, 3), (0, 3), (0, 3), (0, 3), (0, 3), (0, 3), (0, 3), (0, 3), (0, 3), (0, 3), (0, 3), (0, 3), (0, 3), (0, 3), (0, 3), (0, 4), (0, 4), (0, 4), (0, 4), (0, 4), (0, 4), (0, 4), (0, 4), (0, 4), (0, 4), (0, 4), (0, 4), (0, 4), (0, 4), (0, 4), (0, 4), (0, 4), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (0, 1), (0, 2), (0, 5), (1, 1), (1, 3), (1, 4), (1, 5), (2, 2), (2, 3), (2, 4), (2, 5), (3, 3), (3, 4), (3, 5), (4, 4), (4, 5), (5, 5), (0, 1), (0, 2), (0, 5), (1, 1), (1, 3), (1, 4), (1, 5), (2, 2), (2, 3), (2, 4), (2, 5), (3, 3), (3, 4), (3, 5), (4, 4), (4, 5), (5, 5), (0, 1), (0, 2), (0, 5), (1, 1), (1, 3), (1, 4), (1, 5), (2, 2), (2, 3), (2, 4), (2, 5), (3, 3), (3, 4), (3, 5), (4, 4), (4, 5), (5, 5), (0, 1), (0, 2), (0, 5), (1, 1), (1, 3), (1, 4), (1, 5), (2, 2), (2, 3), (2, 4), (2, 5), (3, 3), (3, 4), (3, 5), (4, 4), (4, 5), (5, 5)]
def R0 : List (List ℕ) := I.sublists

set_option maxRecDepth 100000 in
theorem T0 : (R0.drop 0).all (fun c => !LS G MK 21 68 true 5 c) = true := by
  decide +kernel

theorem S0 : R0.all (fun c => !LS G MK 21 68 true 5 c) = true := by
  have h := T0
  rwa [List.drop_zero] at h

end PEqualNP.Outside.L_meta_25662

theorem PEqualNP.Outside.L_meta_25662 : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 5 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (281 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) :=
  PEqualNP.Outside.L_meta_25662.refuteT 281 5 21 68 157 PEqualNP.Outside.L_meta_25662.G PEqualNP.Outside.L_meta_25662.MK PEqualNP.Outside.L_meta_25662.I PEqualNP.Outside.L_meta_25662.E
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) PEqualNP.Outside.L_meta_25662.S0
