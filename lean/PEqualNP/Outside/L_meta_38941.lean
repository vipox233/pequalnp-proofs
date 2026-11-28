import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_38941

section Live

variable {α : Type} [DecidableEq α]

def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k + 1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)

def live (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k + 1, s => live ops goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest)

theorem compress {ops : α → α → Finset α} {goal : α} {k : ℕ} {available : Finset α}
    (h : build ops goal k available) : ∃ s ⊆ available, live ops goal k s := by
  induction k generalizing available with
  | zero =>
    exact ⟨{goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · obtain ⟨s, hs, hrun⟩ := ih skip
      exact ⟨s, hs, Or.inl hrun⟩
    · obtain ⟨t, ht, hrun⟩ := ih tail
      by_cases sub : t ⊆ available
      · exact ⟨t, sub, Or.inl hrun⟩
      · have hzmem : z ∈ t := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : z ∉ available := by
          intro hh
          exact sub ((Finset.insert_eq_of_mem hh) ▸ ht)
        let rest := t.erase z
        have hrest : rest ⊆ available := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (ht hu'.2)).resolve_left hu'.1
        let s := insert a (insert b rest)
        have hs : s ⊆ available := Finset.insert_subset ha (Finset.insert_subset hb hrest)
        refine ⟨s, hs, Or.inr ⟨a, by simp [s], b, by simp [s], hab, z, hz,
          fun h => hzout (hs h), rest, rfl, ?_⟩⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun

theorem live_card {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal k s) : s.card ≤ k + 1 := by
  induction k generalizing s with
  | zero => change s = {goal} at h; simp [h]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact (ih skip).trans (by omega)
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a (insert b rest)
      have h₂ := Finset.card_insert_le b rest
      omega

theorem live_separates {ops : α → α → Finset α} {goal : α} (D : α → Prop)
    (hd : D goal) (hops : ∀ a b, ∀ z ∈ ops a b, D z → D a ∨ D b)
    {k : ℕ} {s : Finset α} (h : live ops goal k s) : ∃ w ∈ s, D w := by
  induction k generalizing s with
  | zero => change s = {goal} at h; exact ⟨goal, by simp [h], hd⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact ih skip
    · obtain ⟨w, hw, hD⟩ := ih tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rcases hops a b w hz hD with h | h
        · exact ⟨a, ha, h⟩
        · exact ⟨b, hb, h⟩
      · exact ⟨w, by simp [hw], hD⟩

theorem first_live {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal (k + 1) s) :
    s = {goal} ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | step
    · rcases ih skip with done | ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, tail⟩
      · exact .inl done
      · exact .inr ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, Or.inl tail⟩
    · exact .inr step

end Live

abbrev W := BitVec 256

def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def sep (x : W) : BitVec 128 := ((x >>> 128) ^^^ x).setWidth 128
def cuts (ws : List W) : BitVec 128 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (-1 : BitVec 128) ++ (0 : BitVec 128)
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

abbrev basicOps (a b : W) : Finset W := (ops a b).toFinset

def differs (i : Fin 128) (w : W) : Prop :=
  w.getLsbD (128+i.val) ≠ w.getLsbD i.val

theorem ops_differs (i : Fin 128) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha,hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : 128+i.val < 256 := by omega
  have hi' : i.val < 256 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

theorem cuts_spec (ws : List W) (i : Fin 128) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have bx (p q : Bool) : Bool.xor p q = true ↔ p ≠ q := by cases p <;> cases q <;> decide
    simp [sep, i.isLt, differs, Nat.add_comm, bx]

theorem cuts_full {g : W} (hg : g = goal ∨ g = ~~~goal) {k : ℕ} {ws : List W}
    (h : live basicOps g k ws.toFinset) : cuts ws = -1 := by
  have hd : ∀ i, differs i g := by rcases hg with rfl | rfl <;> unfold differs <;> decide +kernel
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (differs ⟨j, hj⟩) (hd ⟨j,hj⟩) (ops_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 128)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

theorem ops_swap (a b : W) : basicOps a b = basicOps b a := by
  ext z
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  rw [BitVec.and_comm a b, BitVec.or_comm a b]
  tauto

def keepChoices (a b : W) (r : List W) : List (List W) := [r, a :: r, b :: r, a :: b :: r]

theorem recover_kept {ws r : List W} {a b : W} {needed : Finset W}
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

theorem singleton_list {goal : W} {ws : List W} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

def insertW (x : W) : List W → List W
  | [] => [x]
  | y :: ys => if x.toNat ≤ y.toNat then x :: y :: ys else y :: insertW x ys

def canon : List W → List W
  | [] => []
  | x :: xs => insertW x (canon xs)

theorem insertW_perm (x : W) : ∀ l : List W, (insertW x l).Perm (x :: l)
  | [] => List.Perm.refl _
  | y :: ys => by
    unfold insertW
    split
    · exact List.Perm.refl _
    · exact ((insertW_perm x ys).cons y).trans (List.Perm.swap _ _ _)

theorem canon_perm : ∀ l : List W, (canon l).Perm l
  | [] => List.Perm.refl _
  | x :: xs => (insertW_perm x (canon xs)).trans ((canon_perm xs).cons x)

def dispatch (extra : ℕ) (next : ℕ → List W → Bool) (a b : W) (r : List W) : Bool :=
  let base := cuts r
  (ops a b).any fun w =>
    let v := sep w ||| base
    ((v == -1) && next extra (w :: r)) ||
    ((extra != 0) && (((v ||| sep a == -1) && next (extra - 1) (w :: a :: r)) ||
                       ((v ||| sep b == -1) && next (extra - 1) (w :: b :: r)))) ||
    ((extra ≥ 2) && (v ||| sep a ||| sep b == -1) && next (extra - 2) (w :: a :: b :: r))

def optimized : ℕ → ℕ → List W → Bool
  | 0, _, ws => (ws == [goal] || ws == [~~~goal])
  | k + 1, extra, ws => (ws == [goal] || ws == [~~~goal]) ||
    (pairs ws).any (fun (a, b, r) => dispatch extra (fun e l => optimized k e (canon l)) a b r)

theorem dispatch_complete {k extra : ℕ} {a b z : W} {r kept : List W}
    (next : ℕ → List W → Bool)
    (hz : z ∈ basicOps a b) (hk : kept ∈ keepChoices a b r)
    (he : extra + r.length = k) (hn : kept.length ≤ k)
    (hc : cuts (z :: kept) = -1) (ht : next (k - kept.length) (z :: kept) = true) :
    dispatch extra next a b r = true := by
  apply List.any_eq_true.mpr
  refine ⟨z, List.mem_toFinset.mp hz, ?_⟩
  simp [keepChoices] at hk
  rcases hk with rfl | rfl | rfl | rfl <;>
    simp only [cuts, List.foldr_cons] at hc ⊢ <;>
    (try simp only [List.length_cons] at *) <;>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne]
  · left; left; exact ⟨hc, by convert ht using 2; omega⟩
  · left; right; exact ⟨by omega, .inl ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · left; right; exact ⟨by omega, .inr ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · right; exact ⟨⟨by omega, by convert hc using 1; ac_rfl⟩, by convert ht using 2; omega⟩

theorem optimized_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (ws : List W) (extra : ℕ) (hn : ws.Nodup)
    (room : extra + ws.length = n + 1) (h : live basicOps g n ws.toFinset) :
    optimized n extra ws = true := by
  induction n generalizing ws extra with
  | zero => rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn h]
  | succ k ih =>
    rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
    · rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn done]
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have go {a b : W} (perm : ws.Perm (a :: b :: r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
          dispatch extra (fun e l => optimized k e (canon l)) a b r = true := by
        obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn hset
        have hznew : z ∉ kept := by
          intro hu
          apply hout
          rw [hset]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
        have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
        have hl : live basicOps g k (z :: kept).toFinset := by
          simpa [hfin] using tail
        have hc := live_card hl
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        have hcn : (canon (z :: kept)).Perm (z :: kept) := canon_perm _
        apply dispatch_complete (k := k) (extra := extra) (fun e l => optimized k e (canon l)) hop hk (by omega) (by omega) (cuts_full hg hl)
        refine ih _ _ (hcn.nodup_iff.mpr hnd) ?_ (by rw [List.toFinset_eq_of_perm _ _ hcn]; exact hl)
        rw [hcn.length_eq]; simp; omega
      simp only [optimized, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a, b, r), direct, go hp hs hz⟩
      · exact ⟨(b, a, r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩

def search (n : ℕ) (inputs : List W) : Bool :=
  inputs.sublists.any fun ws =>
    decide (ws.length ≤ n+1) && (cuts ws == -1) && optimized n (n+1-ws.length) (canon ws)

theorem search_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (inputs : List W)
    (hn : inputs.Nodup) (h : build basicOps g n inputs.toFinset) : search n inputs = true := by
  classical
  obtain ⟨s,hs,hl⟩ := compress h
  let ws := inputs.filter (· ∈ s)
  have eq : ws.toFinset = s := by
    ext w
    simp only [ws, List.mem_toFinset, List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hs hw)
  have hnd : ws.Nodup := hn.filter _
  have hl' : live basicOps g n ws.toFinset := eq.symm ▸ hl
  have sz := live_card hl'
  rw [List.toFinset_card_of_nodup hnd] at sz
  have hcn : (canon ws).Perm ws := canon_perm ws
  have hopt : optimized n (n+1-ws.length) (canon ws) = true :=
    optimized_complete hg n (canon ws) _ (hcn.nodup_iff.mpr hnd) (by rw [hcn.length_eq]; omega) (by rw [List.toFinset_eq_of_perm _ _ hcn]; exact hl')
  exact List.any_eq_true.mpr ⟨ws,List.mem_sublists.mpr (List.filter_sublist ..),
    by simp [sz, cuts_full hg hl', hopt]⟩

def kidsOf (extra : ℕ) (a b : W) (r : List W) (w : W) : List (ℕ × List W) :=
  let v := sep w ||| cuts r
  (if v == -1 then [(extra, canon (w :: r))] else []) ++
  (if extra != 0 && (v ||| sep a == -1) then [(extra - 1, canon (w :: a :: r))] else []) ++
  (if extra != 0 && (v ||| sep b == -1) then [(extra - 1, canon (w :: b :: r))] else []) ++
  (if extra ≥ 2 && (v ||| sep a ||| sep b == -1) then [(extra - 2, canon (w :: a :: b :: r))] else [])

def children (c : ℕ × List W) : List (ℕ × List W) :=
  (pairs c.2).flatMap fun p => (ops p.1 p.2.1).flatMap fun w => kidsOf c.1 p.1 p.2.1 p.2.2 w

def goalFree (ws : List W) : Bool := !(ws == [goal] || ws == [~~~goal])

theorem dispatch_false {extra k : ℕ} {a b : W} {r : List W}
    (h : ∀ w ∈ ops a b, ∀ c ∈ kidsOf extra a b r w, optimized k c.1 c.2 = false) :
    dispatch extra (fun e l => optimized k e (canon l)) a b r = false := by
  unfold dispatch
  rw [List.any_eq_false]
  intro w hw hcon
  have h1 := h w hw
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne] at hcon
  rcases hcon with (⟨hv, hn⟩ | ⟨hx, (⟨hv, hn⟩ | ⟨hv, hn⟩)⟩) | ⟨⟨hx, hv⟩, hn⟩
  · have := h1 (extra, canon (w :: r)) (by simp [kidsOf, hv])
    simp_all
  · have := h1 (extra - 1, canon (w :: a :: r)) (by simp [kidsOf, hv, hx])
    simp_all
  · have := h1 (extra - 1, canon (w :: b :: r)) (by simp [kidsOf, hv, hx])
    simp_all
  · have := h1 (extra - 2, canon (w :: a :: b :: r)) (by simp [kidsOf, hv, hx])
    simp_all

theorem opt_false {k e : ℕ} {ws : List W} (hg : goalFree ws = true)
    (h : ∀ c ∈ children (e, ws), optimized k c.1 c.2 = false) :
    optimized (k + 1) e ws = false := by
  unfold optimized
  rw [Bool.or_eq_false_iff]
  refine ⟨by simpa [goalFree] using hg, ?_⟩
  rw [List.any_eq_false]
  rintro ⟨a, b, r⟩ hx hcon
  have key := dispatch_false (extra := e) (k := k) (a := a) (b := b) (r := r)
    (fun w hw c hc => h c (List.mem_flatMap.mpr ⟨(a, b, r), hx, List.mem_flatMap.mpr ⟨w, hw, hc⟩⟩))
  simp_all

def FalseAt (k : ℕ) (L : List (ℕ × List W)) : Prop := ∀ c ∈ L, optimized k c.1 c.2 = false

theorem falseAt_expand {k : ℕ} {L : List (ℕ × List W)}
    (hg : ∀ c ∈ L, goalFree c.2 = true) (h : FalseAt k (L.flatMap children)) : FalseAt (k + 1) L := by
  intro c hc
  exact opt_false (hg c hc) (fun c' hc' => h c' (List.mem_flatMap.mpr ⟨c, hc, hc'⟩))

def expandN : ℕ → List (ℕ × List W) → List (ℕ × List W)
  | 0, L => L
  | d + 1, L => expandN d (L.flatMap children)

def allGoalFree : ℕ → List (ℕ × List W) → Bool
  | 0, _ => true
  | d + 1, L => L.all (fun c => goalFree c.2) && allGoalFree d (L.flatMap children)

theorem falseAt_expandN : ∀ (d : ℕ) {j : ℕ} {L : List (ℕ × List W)},
    allGoalFree d L = true → FalseAt j (expandN d L) → FalseAt (j + d) L
  | 0, _, _, _, h => h
  | d + 1, j, L, hg, h => by
    simp only [allGoalFree, Bool.and_eq_true, List.all_eq_true] at hg
    exact falseAt_expand hg.1 (falseAt_expandN d hg.2 h)

def level0 (n : ℕ) (inputs : List W) : List (ℕ × List W) :=
  (inputs.sublists.filter (fun ws => decide (ws.length ≤ n + 1) && (cuts ws == -1))).map
    (fun ws => (n + 1 - ws.length, canon ws))

theorem search_of_false {n : ℕ} {inputs : List W} (h : FalseAt n (level0 n inputs)) :
    search n inputs = false := by
  unfold search
  rw [List.any_eq_false]
  intro ws hws hcon
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hcon
  obtain ⟨⟨hl, hc⟩, ho⟩ := hcon
  have hmem : (n + 1 - ws.length, canon ws) ∈ level0 n inputs := by
    simp only [level0, List.mem_map, List.mem_filter]
    exact ⟨ws, ⟨hws, by simp [hl, hc]⟩, rfl⟩
  have := h _ hmem
  simp_all

theorem search_false_of_chunks {n d j : ℕ} {inputs : List W} (hj : j + d = n)
    (hg : allGoalFree d (level0 n inputs) = true)
    (hl : FalseAt j (expandN d (level0 n inputs))) : search n inputs = false := by
  subst hj
  exact search_of_false (falseAt_expandN d hg hl)

def chunkOK (j : ℕ) (L : List (ℕ × List W)) : Bool := L.all fun c => !optimized j c.1 c.2

theorem falseAt_of_chunkOK {j : ℕ} {L : List (ℕ × List W)} (h : chunkOK j L = true) : FalseAt j L := by
  intro c hc
  have := List.all_eq_true.mp h c hc
  simpa using this

def hashW (acc : ℕ) (w : W) : ℕ := (acc * 31 + w.toNat) % 1000003

def hashS (nb : ℕ) (c : ℕ × List W) : ℕ := (c.2.foldl hashW c.1) % nb

def inB (bk : List (List (ℕ × List W))) (c : ℕ × List W) : Bool :=
  (bk.getD (hashS bk.length c) []).any fun x => decide (x = c)

theorem inB_mem {bk : List (List (ℕ × List W))} {c : ℕ × List W} (h : inB bk c = true) :
    c ∈ bk.flatten := by
  unfold inB at h
  rw [List.any_eq_true] at h
  obtain ⟨x, hx, hxc⟩ := h
  have hxc' : x = c := of_decide_eq_true hxc
  subst hxc'
  rw [List.mem_flatten]
  by_cases hi : hashS bk.length x < bk.length
  · exact ⟨bk.getD (hashS bk.length x) [], by simp [List.getD_eq_getElem?_getD, hi], hx⟩
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (not_lt.mp hi)] at hx

def windowsF (j : ℕ) (L : List (List (ℕ × List W))) (a : ℕ) : List ℕ → Bool
  | [] => (L.drop a).isEmpty
  | s :: rest => chunkOK j ((L.drop a).take s).flatten && windowsF j L (a + s) rest

theorem falseAt_of_windowsF {j : ℕ} {L : List (List (ℕ × List W))} :
    ∀ (sizes : List ℕ) (a : ℕ), windowsF j L a sizes = true → FalseAt j (L.drop a).flatten
  | [], a, h => by
    intro c hc
    simp only [windowsF, List.isEmpty_iff] at h
    rw [h] at hc
    simp at hc
  | s :: rest, a, h => by
    simp only [windowsF, Bool.and_eq_true] at h
    have h1 := falseAt_of_chunkOK h.1
    have h2 := falseAt_of_windowsF rest (a + s) h.2
    intro c hc
    have split : L.drop a = (L.drop a).take s ++ L.drop (a + s) := by
      rw [← List.drop_drop, List.take_append_drop]
    rw [split, List.flatten_append] at hc
    rcases List.mem_append.mp hc with hc | hc
    · exact h1 c hc
    · exact h2 c hc

theorem windowsF_cons {j : ℕ} {L : List (List (ℕ × List W))} {a s : ℕ} {rest : List ℕ}
    (h1 : chunkOK j ((L.drop a).take s).flatten = true)
    (h2 : windowsF j L (a + s) rest = true) : windowsF j L a (s :: rest) = true := by
  simp [windowsF, h1, h2]

theorem windowsF_nil {j : ℕ} {L : List (List (ℕ × List W))} {a : ℕ} (h : (L.drop a).isEmpty = true) :
    windowsF j L a [] = true := h

theorem dispatch_mono {extra : ℕ} {n1 n2 : ℕ → List W → Bool} (a b : W) (r : List W)
    (h : ∀ e l, n2 e l = true → n1 e l = true) :
    dispatch extra n2 a b r = true → dispatch extra n1 a b r = true := by
  unfold dispatch
  simp only [List.any_eq_true]
  rintro ⟨w, hw, hx⟩
  refine ⟨w, hw, ?_⟩
  simp only [Bool.or_eq_true, Bool.and_eq_true] at hx ⊢
  rcases hx with (⟨hv, hn⟩ | ⟨hx1, (⟨hv, hn⟩ | ⟨hv, hn⟩)⟩) | ⟨⟨hx1, hv⟩, hn⟩
  · exact Or.inl (Or.inl ⟨hv, h _ _ hn⟩)
  · exact Or.inl (Or.inr ⟨hx1, Or.inl ⟨hv, h _ _ hn⟩⟩)
  · exact Or.inl (Or.inr ⟨hx1, Or.inr ⟨hv, h _ _ hn⟩⟩)
  · exact Or.inr ⟨⟨hx1, hv⟩, h _ _ hn⟩

def optB (S : ℕ × List W → Bool) : ℕ → ℕ → List W → Bool
  | 0, e, ws => S (e, ws)
  | k + 1, e, ws => (ws == [goal] || ws == [~~~goal]) ||
    (pairs ws).any (fun (a, b, r) => dispatch e (fun e' l => optB S k e' (canon l)) a b r)

theorem optB_sound (S : ℕ × List W → Bool) (J : ℕ)
    (hS : ∀ c, S c = false → optimized J c.1 c.2 = false) :
    ∀ (k e : ℕ) (ws : List W), optB S k e ws = false → optimized (J + k) e ws = false
  | 0, e, ws, h => hS (e, ws) h
  | k + 1, e, ws, h => by
    have ih := optB_sound S J hS k
    unfold optB at h
    rw [Bool.or_eq_false_iff] at h
    show optimized ((J + k) + 1) e ws = false
    unfold optimized
    rw [Bool.or_eq_false_iff]
    refine ⟨h.1, ?_⟩
    have h2 := h.2
    rw [List.any_eq_false] at h2 ⊢
    rintro ⟨a, b, r⟩ hp hcon
    apply h2 (a, b, r) hp
    refine dispatch_mono a b r ?_ hcon
    intro e' l hl
    by_contra hne
    have hf : optB S k e' (canon l) = false := by simpa using hne
    have := ih e' (canon l) hf
    simp_all

def chunkB (S : ℕ × List W → Bool) (d : ℕ) (L : List (ℕ × List W)) : Bool :=
  L.all fun c => !optB S d c.1 c.2

def windowsG (f : List (ℕ × List W) → Bool) (L : List (ℕ × List W)) (a : ℕ) : List ℕ → Bool
  | [] => (L.drop a).isEmpty
  | s :: rest => f ((L.drop a).take s) && windowsG f L (a + s) rest

theorem windowsG_sound {f : List (ℕ × List W) → Bool} {P : ℕ × List W → Prop}
    (hf : ∀ X, f X = true → ∀ c ∈ X, P c) {L : List (ℕ × List W)} :
    ∀ (sizes : List ℕ) (a : ℕ), windowsG f L a sizes = true → ∀ c ∈ L.drop a, P c
  | [], a, h => by
    intro c hc
    simp only [windowsG, List.isEmpty_iff] at h
    rw [h] at hc
    simp at hc
  | s :: rest, a, h => by
    simp only [windowsG, Bool.and_eq_true] at h
    have h1 := hf _ h.1
    have h2 := windowsG_sound hf rest (a + s) h.2
    intro c hc
    have split : L.drop a = (L.drop a).take s ++ L.drop (a + s) := by
      rw [← List.drop_drop, List.take_append_drop]
    rw [split] at hc
    rcases List.mem_append.mp hc with hc | hc
    · exact h1 c hc
    · exact h2 c hc

theorem windowsG_cons {f : List (ℕ × List W) → Bool} {L : List (ℕ × List W)} {a s : ℕ} {rest : List ℕ}
    (h1 : f ((L.drop a).take s) = true) (h2 : windowsG f L (a + s) rest = true) :
    windowsG f L a (s :: rest) = true := by
  simp [windowsG, h1, h2]

theorem windowsG_nil {f : List (ℕ × List W) → Bool} {L : List (ℕ × List W)} {a : ℕ}
    (h : (L.drop a).isEmpty = true) : windowsG f L a [] = true := h

theorem search_false_B {n dp J d : ℕ} {inputs : List W} {bk : List (List (ℕ × List W))} {sa sb : List ℕ}
    (hj : J + d + dp = n)
    (hg : allGoalFree dp (level0 n inputs) = true)
    (hB : windowsF J bk 0 sb = true)
    (hA : windowsG (chunkB (fun c => !inB bk c) d) (expandN dp (level0 n inputs)) 0 sa = true) :
    search n inputs = false := by
  have hBF : FalseAt J bk.flatten := by
    have := falseAt_of_windowsF sb 0 hB
    simpa using this
  have hS : ∀ c, (fun c => !inB bk c) c = false → optimized J c.1 c.2 = false := by
    intro c hc
    have hin : inB bk c = true := by simpa using hc
    exact hBF c (inB_mem hin)
  have hP : ∀ c ∈ (expandN dp (level0 n inputs)).drop 0, optB (fun c => !inB bk c) d c.1 c.2 = false := by
    refine windowsG_sound (P := fun c => optB (fun c => !inB bk c) d c.1 c.2 = false) ?_ sa 0 hA
    intro X hX c hc
    have := List.all_eq_true.mp hX c hc
    simpa using this
  have hF : FalseAt (J + d) (expandN dp (level0 n inputs)) := by
    intro c hc
    exact optB_sound _ J hS d c.1 c.2 (hP c (by simpa using hc))
  exact search_false_of_chunks (j := J + d) (d := dp) hj hg hF

theorem getD_mem_or_nil {α : Type} (l : List (List α)) (i : ℕ) :
    l.getD i [] ∈ l ∨ l.getD i [] = [] := by
  by_cases hi : i < l.length
  · left
    simp [List.getD_eq_getElem?_getD, hi]
  · right
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (not_lt.mp hi)]

def inB2 (g nb : ℕ) (bk2 : List (List (List (ℕ × List W)))) (c : ℕ × List W) : Bool :=
  ((bk2.getD (hashS nb c / g) []).getD (hashS nb c % g) []).any fun x => decide (x = c)

theorem inB2_mem {g nb : ℕ} {bk2 : List (List (List (ℕ × List W)))} {c : ℕ × List W}
    (h : inB2 g nb bk2 c = true) : c ∈ bk2.flatten.flatten := by
  unfold inB2 at h
  rw [List.any_eq_true] at h
  obtain ⟨x, hx, hxc⟩ := h
  have hxc' : x = c := of_decide_eq_true hxc
  subst hxc'
  have hG := getD_mem_or_nil bk2 (hashS nb x / g)
  have hB := getD_mem_or_nil (bk2.getD (hashS nb x / g) []) (hashS nb x % g)
  rw [List.mem_flatten]
  rcases hB with hB | hB
  · rcases hG with hG | hG
    · exact ⟨_, List.mem_flatten.mpr ⟨_, hG, hB⟩, hx⟩
    · rw [hG] at hB
      simp at hB
  · rw [hB] at hx
    simp at hx

theorem search_false_B2 {n dp J d g nb : ℕ} {inputs : List W} {bk2 : List (List (List (ℕ × List W)))} {sa sb : List ℕ}
    (hj : J + d + dp = n)
    (hg : allGoalFree dp (level0 n inputs) = true)
    (hB : windowsF J bk2.flatten 0 sb = true)
    (hA : windowsG (chunkB (fun c => !inB2 g nb bk2 c) d) (expandN dp (level0 n inputs)) 0 sa = true) :
    search n inputs = false := by
  have hBF : FalseAt J bk2.flatten.flatten := by
    have := falseAt_of_windowsF sb 0 hB
    simpa using this
  have hS : ∀ c, (fun c => !inB2 g nb bk2 c) c = false → optimized J c.1 c.2 = false := by
    intro c hc
    have hin : inB2 g nb bk2 c = true := by simpa using hc
    exact hBF c (inB2_mem hin)
  have hP : ∀ c ∈ (expandN dp (level0 n inputs)).drop 0, optB (fun c => !inB2 g nb bk2 c) d c.1 c.2 = false := by
    refine windowsG_sound (P := fun c => optB (fun c => !inB2 g nb bk2 c) d c.1 c.2 = false) ?_ sa 0 hA
    intro X hX c hc
    have := List.all_eq_true.mp hX c hc
    simpa using this
  have hF : FalseAt (J + d) (expandN dp (level0 n inputs)) := by
    intro c hc
    exact optB_sound _ J hS d c.1 c.2 (hP c (by simpa using hc))
  exact search_false_of_chunks (j := J + d) (d := dp) hj hg hF

theorem search_false_C2 {n dp J d g1 nb1 g2 nb2 : ℕ} {inputs : List W}
    {bkA bkB : List (List (List (ℕ × List W)))} {sa sb sc : List ℕ}
    (hj : J + 1 + d + dp = n)
    (hg : allGoalFree dp (level0 n inputs) = true)
    (hC : windowsF J bkB.flatten 0 sc = true)
    (hB : windowsG (chunkB (fun c => !inB2 g2 nb2 bkB c) 1) bkA.flatten.flatten 0 sb = true)
    (hA : windowsG (chunkB (fun c => !inB2 g1 nb1 bkA c) d) (expandN dp (level0 n inputs)) 0 sa = true) :
    search n inputs = false := by
  have hCF : FalseAt J bkB.flatten.flatten := by
    have := falseAt_of_windowsF sc 0 hC
    simpa using this
  have hS2 : ∀ c, (fun c => !inB2 g2 nb2 bkB c) c = false → optimized J c.1 c.2 = false := by
    intro c hc
    have hin : inB2 g2 nb2 bkB c = true := by simpa using hc
    exact hCF c (inB2_mem hin)
  have hP2 : ∀ c ∈ bkA.flatten.flatten, optimized (J + 1) c.1 c.2 = false := by
    have h1 : ∀ c ∈ (bkA.flatten.flatten).drop 0, optB (fun c => !inB2 g2 nb2 bkB c) 1 c.1 c.2 = false := by
      refine windowsG_sound (P := fun c => optB (fun c => !inB2 g2 nb2 bkB c) 1 c.1 c.2 = false) ?_ sb 0 hB
      intro X hX c hc
      have := List.all_eq_true.mp hX c hc
      simpa using this
    intro c hc
    exact optB_sound _ J hS2 1 c.1 c.2 (h1 c (by simpa using hc))
  have hS1 : ∀ c, (fun c => !inB2 g1 nb1 bkA c) c = false → optimized (J + 1) c.1 c.2 = false := by
    intro c hc
    have hin : inB2 g1 nb1 bkA c = true := by simpa using hc
    exact hP2 c (inB2_mem hin)
  have hP : ∀ c ∈ (expandN dp (level0 n inputs)).drop 0, optB (fun c => !inB2 g1 nb1 bkA c) d c.1 c.2 = false := by
    refine windowsG_sound (P := fun c => optB (fun c => !inB2 g1 nb1 bkA c) d c.1 c.2 = false) ?_ sa 0 hA
    intro X hX c hc
    have := List.all_eq_true.mp hX c hc
    simpa using this
  have hF : FalseAt (J + 1 + d) (expandN dp (level0 n inputs)) := by
    intro c hc
    exact optB_sound _ (J + 1) hS1 d c.1 c.2 (hP c (by simpa using hc))
  exact search_false_of_chunks (j := J + 1 + d) (d := dp) hj hg hF

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def holds (av : Finset W) (z : W) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ ∃ a ∈ av, z = a ∨ z = ~~~a

theorem holds_insert {av : Finset W} {z a : W} (h : holds av z) : holds (insert a av) z := by
  rcases h with h|h|⟨u,hu,he⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨u,Finset.mem_insert_of_mem hu,he⟩)

theorem holds_not {av : Finset W} {z : W} (h : holds av z) : holds av (~~~z) := by
  rcases h with rfl|rfl|⟨a,ha,he⟩
  · exact .inr (.inl rfl)
  · exact .inl BitVec.not_not
  · rcases he with he|he <;> rw [he]
    · exact .inr (.inr ⟨a, ha, .inr rfl⟩)
    · exact .inr (.inr ⟨a, ha, .inl BitVec.not_not⟩)

def reachable (av : Finset W) (z : W) : Prop :=
  holds av z ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ w ∈ basicOps a b, holds (insert w av) z

theorem reachable_not {av : Finset W} {z : W} (h : reachable av z) : reachable av (~~~z) := by
  rcases h with h|⟨a,ha,b,hb,ne,w,hop,hw⟩
  · exact .inl (holds_not h)
  · exact .inr ⟨a,ha,b,hb,ne,w,hop,holds_not hw⟩

set_option maxRecDepth 5000 in
theorem and_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x &&& y) := by
  have const : holds av (0 : W) := .inl rfl
  have oldx := hx
  rcases hx with rfl|rfl|⟨a,ha,ea⟩
  · rw [show (0 : W) &&& y = 0 from BitVec.zero_and]; exact .inl const
  · change reachable av (BitVec.allOnes 256 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 256)
    rw [BitVec.and_allOnes]; exact .inl oldx
  by_cases h : a = b
  · subst b
    rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb] <;>
      simp only [BitVec.and_self, BitVec.and_not_self, BitVec.not_and_self] <;>
      first | exact .inl const | exact .inl (.inr (.inr ⟨a,ha,.inl rfl⟩)) |
        exact .inl (.inr (.inr ⟨a,ha,.inr rfl⟩))
  have add (w : W) (hw : w ∈ basicOps a b) (z : W) (hz : z = w ∨ z = ~~~w) :
      reachable av z :=
    .inr ⟨a,ha,b,hb,h,w,hw,.inr (.inr ⟨w,Finset.mem_insert_self ..,hz⟩)⟩
  rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb]
  · exact add _ (by simp [basicOps,ops] : a &&& b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : a &&& ~~~b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : b &&& ~~~a ∈ basicOps a b) _ (.inl (BitVec.and_comm ..))
  · exact add _ (by simp [basicOps,ops] : a ||| b ∈ basicOps a b) _ (.inr BitVec.not_or.symm)

theorem or_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x ||| y) := by
  simpa only [BitVec.not_and, BitVec.not_not] using reachable_not (and_reach (holds_not hx) (holds_not hy))

private def bit (k : Fin 256) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 256) :
    (w.map (bit k)).getD i false = bit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit]

def legal (g : Gate) : Prop := (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

def action (w : List W) (g : Gate) : W := match g.op with
  | .not => ~~~(g.inputs.head?.map (fun i => w.getD i 0)).getD 0
  | .and => (g.inputs.map fun i => w.getD i 0).foldr (· &&& ·) (~~~0)
  | .or => (g.inputs.map fun i => w.getD i 0).foldr (· ||| ·) 0
  | _ => 0

set_option maxRecDepth 5000 in
theorem action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 256) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (0#256)[k.val] = false; simp
  all_goals rcases hop with rfl|rfl|rfl <;>
    simp only [step, List.map_cons,List.map_nil,read_bit,List.map_append] <;>
    simp only [action, GateOp.eval, List.foldr_cons,List.foldr_nil,List.head?_cons,List.head?_nil,
      List.headD_cons,List.headD_nil,Option.map_some,Option.map_none,Option.getD_some,Option.getD_none,
      List.all_cons,List.all_nil,List.any_cons,List.any_nil,List.map_cons,List.map_nil,id_eq,
      Bool.and_true,Bool.or_false, bit,BitVec.getElem_and,BitVec.getElem_or,BitVec.getElem_not,
      bit0,Bool.not_false]

def isBinary (g : Gate) : Bool := match g.op with
  | .not => false
  | _ => true
def binaryCost (gs : List Gate) := (gs.filter isBinary).length

theorem available_read {av : Finset W} {w : List W} (hw : ∀ u ∈ w, holds av u) (i : ℕ) :
    holds av (w.getD i 0) := by
  by_cases h : i < w.length
  · exact hw _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt h)]
    exact .inl rfl

set_option maxRecDepth 5000 in
theorem gate_reach (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (g : Gate) (hg : legal g) :
    if isBinary g then reachable av (action w g) else holds av (action w g) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals rcases hop with rfl|rfl|rfl <;> simp only [isBinary,Bool.false_eq_true,ite_false,ite_true,
    action,List.head?_nil,List.head?_cons,List.map_nil,List.map_cons,List.foldr_nil,List.foldr_cons,
    Option.map_none,Option.map_some,Option.getD_none,Option.getD_some,
    show ∀ x : W, x ||| (0 : W) = x from fun x => BitVec.or_zero,
    show ∀ x : W, x &&& ~~~0 = x from fun x => BitVec.and_allOnes]
  all_goals first
    | exact .inl (.inl rfl)
    | exact .inl (.inr (.inl rfl))
    | exact .inr (.inl rfl)
    | exact .inl (available_read hw _)
    | exact holds_not (available_read hw _)
    | exact and_reach (available_read hw _) (available_read hw _)
    | exact or_reach (available_read hw _) (available_read hw _)

set_option maxRecDepth 4000 in
theorem compile (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (he : ∀ k, (gs.foldl step (w.map (bit k))).getD out false = bit k (~~~goal)) :
    ∃ t, (t = goal ∨ t = ~~~goal) ∧ build basicOps t (binaryCost gs) av := by
  induction gs generalizing w av with
  | nil =>
    have hv : w.getD out 0 = ~~~goal := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit, bit] using he ⟨i,hi⟩
    have h := hv ▸ available_read hw out
    rcases h with zero|ones|⟨t,ht,eq|eq⟩
    · exact False.elim ((by decide : ~~~goal ≠ 0) zero)
    · exact False.elim ((by decide : ~~~goal ≠ ~~~0) ones)
    · exact ⟨t, .inr eq.symm, ht⟩
    · exact ⟨t, .inl (by simpa only [BitVec.not_not] using congrArg (fun w : W => ~~~w) eq.symm), ht⟩
  | cons g gs ih =>
    let z := action w g
    have stepOK := action_spec w g (hg g (by simp))
    have nextEval : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false = bit k (~~~goal) := by
      intro k; simpa only [List.foldl_cons, stepOK] using he k
    have tail := ih (fun t ht => hg t (by simp [ht])) (w ++ [z])
    have cont (A : Finset W) (hold : ∀ u ∈ w, holds A u) (new : holds A z) :=
      tail A (by
        intro u hu
        rcases List.mem_append.mp hu with hu|hu
        · exact hold u hu
        · exact (List.mem_singleton.mp hu) ▸ new) nextEval
    have stepClass := gate_reach w av hw g (hg g (by simp))
    cases neg : isBinary g
    · simp only [neg,Bool.false_eq_true,ite_false] at stepClass
      simpa [binaryCost,neg] using cont av hw stepClass
    · simp only [neg,ite_true] at stepClass
      have len : binaryCost (g::gs) = binaryCost gs+1 := by simp [binaryCost,neg]
      rw [len]
      rcases stepClass with existing|⟨a,ha,b,hb,ne,new,op,rep⟩
      · obtain ⟨t,ht,run⟩ := cont av hw existing
        exact ⟨t,ht,Or.inl run⟩
      · obtain ⟨t,ht,run⟩ := cont (insert new av) (fun u hu => holds_insert (hw u hu)) rep
        exact ⟨t,ht,Or.inr ⟨a,ha,b,hb,ne,new,op,run⟩⟩

def target (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (4276809440 * 2 ^ 32 + 4276789408) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

theorem bound_from_search (inputs : List W) (width : inputs.length = 6)
    (nd : inputs.Nodup) (reject : search 8 inputs = false)
    (sample : ∀ k : Fin 256,
      target (fun i => (inputs.getD i.val 0)[k.val]) = (~~~goal)[k.val])
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = target x) :
    8 < binaryCost gs := by
  by_contra! low
  have init : ∀ u ∈ inputs, holds inputs.toFinset u := by
    intro u hu
    exact .inr (.inr ⟨u, List.mem_toFinset.mpr hu, .inl rfl⟩)
  have evaluate (k : Fin 256) :
      (gs.foldl step (inputs.map (bit k))).getD o false = bit k (~~~goal) := by
    let x (i : Fin 6) : Bool := bit k (inputs.getD i.val 0)
    have same : List.ofFn x = inputs.map (bit k) := by
      apply List.ext_getElem
      · simp [width]
      · intro i hi hj
        have hlt : i < inputs.length := by simpa using hj
        simp only [List.getElem_ofFn, List.getElem_map, x, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hlt, Option.getD_some]
    change Circuit.eval ⟨gs,o⟩ (inputs.map (bit k)) = bit k (~~~goal)
    rw [← same, he]
    exact sample k
  obtain ⟨t, ht, run⟩ := compile gs o hg inputs inputs.toFinset init evaluate
  have lift {a b : ℕ} (h : a ≤ b) (hr : build basicOps t a inputs.toFinset) :
      build basicOps t b inputs.toFinset := by
    induction h with
    | refl => exact hr
    | step _ ih => exact Or.inl ih
  exact Bool.noConfusion (reject.symm.trans (search_complete ht 8 inputs nd (lift low run)))

def rows : List W :=
  [(0x0001461c21082aac#64 ++ 0x200028c384210555#64 ++ 0xb827ce3c6118ffff#64 ++ 0xd704f9c78c231fff#64 : BitVec 256),
   (0x084b16c591636666#64 ++ 0x410962d8b22c6ccc#64 ++ 0xe8db37c791e76667#64 ++ 0xbd1b66f8f23ceccc#64 : BitVec 256),
   (0x03143802d6058550#64 ++ 0x806287005ac0b0aa#64 ++ 0xdf1c3807fe0787ff#64 ++ 0x7be38700ffc0f0ff#64 : BitVec 256),
   (0x15a03b681bb80787#64 ++ 0x02b4076d037700f0#64 ++ 0xf7e03ff81ff80786#64 ++ 0xfefc07ff03ff00f0#64 : BitVec 256),
   (0x06fe80000cd6d000#64 ++ 0x00dfd000019ada00#64 ++ 0x9fffc0001ffff805#64 ++ 0xf3fff80003ffff00#64 : BitVec 256),
   (0x27ffedb760000000#64 ++ 0x04fffdb6ec000000#64 ++ 0xe7ffffffe0000003#64 ++ 0xfcfffffffc000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [2, 3]⟩, ⟨.or, [0, 6]⟩, ⟨.and, [7, 4]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [1, 9]⟩, ⟨.or, [0, 10]⟩, ⟨.and, [3, 9]⟩, ⟨.or, [2, 12]⟩, ⟨.and, [11, 13]⟩, ⟨.or, [14, 8]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0000000000000000 0x0000000000000000 0x98040804600087ff 0x530081008c0010ff

def z1 : W := mkw 0x0001461c21082aac 0x200028c384210555 0xb827ce3c6118ffff 0xd704f9c78c231fff

def z2 : W := mkw 0x03157e1ef70daffc 0xa062afc3dee1b5ff 0xff3ffe3fff1fffff 0xffe7ffc7ffe3ffff

def z3 : W := mkw 0x06fe80000cd6d000 0x00dfd000019ada00 0x9fffc0001ffff805 0xf3fff80003ffff00

def z4 : W := mkw 0x084b16c591636666 0x410962d8b22c6ccc 0xe8db37c791e76667 0xbd1b66f8f23ceccc

def z5 : W := mkw 0x15a03b681bb80787 0x02b4076d037700f0 0xf7e03ff81ff80786 0xfefc07ff03ff00f0

def z6 : W := mkw 0x27ffedb760000000 0x04fffdb6ec000000 0xe7ffffffe0000003 0xfcfffffffc000000

def z7 : W := mkw 0x03143802d6058550 0x806287005ac0b0aa 0xdf1c3807fe0787ff 0x7be38700ffc0f0ff

def z8 : W := mkw 0x15a03b681bb80787 0x02b4076d037700f0 0x67c03ff81ee00782 0x2cf807ff03dc00f0

def z9 : W := mkw 0x06ffc61c2ddefaac 0x20dff8c385bbdf55 0xbfffce3c7fffffff 0xf7fff9c78fffffff

def z10 : W := mkw 0x084a10c190634442 0x41094218320c6888 0x40d831c390e70000 0x281b0638721ce000

def z11 : W := mkw 0x21016db760000000 0x04202db6ec000000 0x60003fffe0000002 0x0c0007fffc000000

def z12 : W := mkw 0x0001441420002828 0x2000288284000505 0x0807c0046000f879 0x0100f8008c001f0f

def z13 : W := mkw 0x084a12c191634646 0x41094258322c68c8 0xe0d837c391e70606 0xbc1b06f8723ce0c0

def z14 : W := mkw 0x17b43b6a5fbc8797 0x82f6876d4bf790f2 0xf7e43ff87ff8879e 0xfefc87ff0fff10f3

def z15 : W := mkw 0x0001461c21082aac 0x200028c384210555 0x2023c63801187800 0x840478c700230f00

def z16 : W := mkw 0x03143802d6058550 0x806287005ac0b0aa 0x471830039e070000 0x28e3060073c0e000

def z17 : W := mkw 0x0000020801080284 0x0000004100210050 0xb0200e3801180786 0xd60401c7002300f0

def z18 : W := mkw 0x084b56ddb16b6eee 0x61096adbb62d6ddd 0xf8fffffff1ffffff 0xff1ffffffe3fffff

def z19 : W := mkw 0x214b6db760000000 0x04296db6ec000000 0xe0db3fffe0000003 0xbc1b67fffc000000

def z20 : W := mkw 0x004b048500424000 0x00096090a0084800 0xe8db37c791e76007 0xbd1b66f8f23cec00

def z21 : W := mkw 0x27ffedb76cd6d000 0x04fffdb6ed9ada00 0xfffffffffffff807 0xffffffffffffff00

def z22 : W := mkw 0x05a0292008900000 0x00b4052401120000 0xf7e03ff81ff80006 0xfefc07ff03ff0000

def z23 : W := mkw 0x0001441c200828a8 0x2000288384010515 0x1827c83c6018f9f9 0x4304f9078c031f3f

def z24 : W := mkw 0x15a03b681bb80787 0x02b4076d037700f0 0x67e037f81ff80000 0xacfc06ff03ff0000

def z25 : W := mkw 0x084a10c190634442 0x41094218320c6888 0xc8db31c391e76005 0xb91b6638723cec00

def z26 : W := mkw 0x37ffffffffbd87d7 0x86fffffffff7b0fa 0xffffffffffff87ff 0xfffffffffffff0ff

def z27 : W := mkw 0x004a000000424000 0x0009400000084800 0x88db000011e76005 0xb11b6000023cec00

def z28 : W := mkw 0x27b5edb760000000 0x04f6bdb6ec000000 0x6724ffffe0000002 0x4ce49ffffc000000

def z29 : W := mkw 0x0001461c21082aac 0x200028c384210555 0xa8030e3c610067ff 0x950061c78c200cff

def z30 : W := mkw 0x15a02b680bb80387 0x02b4056d01770070 0x37e00ff80ff80180 0xc6fc01ff01ff0030

def z31 : W := mkw 0x04a0012000000000 0x0094002400000000 0x20e007f800000000 0x841c00ff00000000

def z32 : W := mkw 0x225fc4976446d000 0x044bf892ec88da00 0x081fc007e007f801 0x0103f800fc00ff00

def z33 : W := mkw 0x0000000000000000 0x0000000000000000 0x9827c0000118f805 0xd304f80000231f00

def z34 : W := mkw 0x27b5ed3660000000 0x04f6bda6cc000000 0xa727ce3c60000003 0xd4e4f9c78c000000

def z35 : W := mkw 0x0b5e38c3d667c552 0xc16bc7187accf8aa 0x47d831c39ee70000 0x28fb063873dce000

def z36 : W := mkw 0x021400000cd6d000 0x00428000019ada00 0x9f1c00001ffff805 0x73e3800003ffff00

def z37 : W := mkw 0x01003802d2010550 0x802007005a4020aa 0xc8183807f00707ff 0x39030700fe00e0ff

def z38 : W := mkw 0x004b048500000000 0x00096090a0000000 0xe0db37c780000003 0xbc1b66f8f0000000

def z39 : W := mkw 0x27b4e93260000000 0x04f69d264c000000 0x0724c83860000000 0x40e499070c000000

def z40 : W := mkw 0x05a0292000000000 0x00b4052400000000 0xe7e03ff800000002 0xfcfc07ff00000000

def z41 : W := mkw 0x37ffffff7bb80787 0x06ffffffef7700f0 0xf7fffffffff80787 0xfeffffffffff00f0

def z42 : W := mkw 0x0001441420002828 0x2000288284000505 0xa827ce3c6000f87b 0xd504f9c78c001f0f

def z43 : W := mkw 0x06fe80000cd6d000 0x00dfd000019ada00 0x07d800001ee70000 0x20fb000003dce000

def z44 : W := mkw 0x0314280246048110 0x8062850048c09022 0x170408006e008198 0x42e081000dc01033

def z45 : W := mkw 0x15a039601ab00503 0x02b4072c035600a0 0x47c031c01ee00000 0x28f8063803dc0000

def z46 : W := mkw 0x15a17f7c3bb82faf 0x22b42fef877705f5 0xffe7fffc7ff8ffff 0xfffcffff8fff1fff

def z47 : W := mkw 0x080116c591212666 0x410022d8b22424cc 0xe81837c790070667 0x3d0306f8f200e0cc

def z48 : W := mkw 0x04ea800008d25000 0x009d5000011a4a00 0x00e3c00001f87800 0x801c7800003f0f00

def z49 : W := mkw 0x27ffedb768d25000 0x04fffdb6ed1a4a00 0xe7ffffffe1f87803 0xfcfffffffc3f0f00

def z50 : W := mkw 0x0314380016048500 0x0062870002c090a0 0xdf1c38001e078787 0x7be3870003c0f0f0

def z51 : W := mkw 0x27b4e9326c949000 0x04f69d264d929200 0x1724c8386e189800 0x42e499070dc31300

def z52 : W := mkw 0x0800124091636666 0x41000248122c6ccc 0x0800000011e76664 0x01000000023ceccc

def z53 : W := mkw 0x004a000000424000 0x0009400000084800 0x98ffc00011fff805 0xf31ff800023fff00

def z54 : W := mkw 0x000000000cd6d000 0x00000000019ada00 0x180000001ffff804 0x0300000003ffff00

def z55 : W := mkw 0x05a0292000000000 0x00b4052400000000 0x47c031c000000000 0x28f8063800000000

def z56 : W := mkw 0x26ffc5b52cd6d000 0x04dff8b6a59ada00 0xbfffc7f81ffff805 0xf7fff8ff03ffff00

def z57 : W := mkw 0x04a0000008900000 0x0094000001120000 0x97e000001ff80004 0xf2fc000003ff0000

def z58 : W := mkw 0x27ffedb768900000 0x04fffdb6ed120000 0xf7fffffffff80007 0xfeffffffffff0000

def z59 : W := mkw 0x025e80000446d000 0x004bd0000088da00 0x081fc0000007f801 0x0103f8000000ff00

def z60 : W := mkw 0x084b16c591212666 0x410962d8b22424cc 0xe0db37c780000663 0xbc1b66f8f00000cc

def z61 : W := mkw 0x210029a340000000 0x0420053468000000 0x400031c380000000 0x0800063870000000

def z62 : W := mkw 0x31017fff73280787 0x06202fffee6500f0 0x60003fffe0000782 0x0c0007fffc0000f0

def z63 : W := mkw 0x03143802d6058550 0x806287005ac0b0aa 0xdf1c30039e078005 0x7be3860073c0f000

def z64 : W := mkw 0x27ffedb760000000 0x04fffdb6ec000000 0x47dff1c7e0000001 0x28fbfe38fc000000

def z65 : W := mkw 0x1ceb17ed99fb66e7 0x439d62fdb33f6cdc 0xe8fb37ff91ff6667 0xbd1f66fff23feccc

def z66 : W := mkw 0x084b16c591636666 0x410962d8b22c6ccc 0x081b000791e76665 0x01036000f23ceccc

def z67 : W := mkw 0x225fc49760000000 0x044bf892ec000000 0x001fc007e0000001 0x0003f800fc000000

def z68 : W := mkw 0x01003802d2010550 0x802007005a4020aa 0x40003807e00007fa 0x08000700fc0000ff

def z69 : W := mkw 0x03143802d6058550 0x806287005ac0b0aa 0x571c3803fe078198 0x6ae387007fc0f033

def z70 : W := mkw 0x2ffffffff16b6eee 0x65fffffffe2d6ddd 0xfffffffff1ffffff 0xfffffffffe3fffff

def z71 : W := mkw 0x05a0392012000500 0x00b40724024000a0 0xf7e03ff81e000786 0xfefc07ff03c000f0

def z72 : W := mkw 0x0b5f7edff76feffe 0xe16befdbfeedfdff 0xffffffffffffffff 0xffffffffffffffff

def z73 : W := mkw 0x27ffefbf61082aac 0x24fffdf7ec210555 0xe7ffffffe00007fb 0xfcfffffffc0000ff

def z74 : W := mkw 0x004b449520000000 0x00096892a4000000 0xe0ffffffe0000003 0xfc1ffffffc000000

def z75 : W := mkw 0x084b46dd216a6aae 0x610968dba42d4d55 0x20e3c7f801f87800 0x841c78ff003f0f00

def z76 : W := mkw 0x025e80000446d000 0x004bd0000088da00 0x983fc000011ff805 0xd307f8000023ff00

def z77 : W := mkw 0x0000100090010440 0x0000020012002088 0xc818300790070667 0x39030600f200e0cc

def z78 : W := mkw 0x0100280240000000 0x0020050048000000 0x40003807e0000002 0x08000700fc000000

def z79 : W := mkw 0x35a17fff7bb80787 0x06b42fffef7700f0 0xf7e03ffffff80786 0xfefc07ffffff00f0

def z80 : W := mkw 0x27b4e93260000000 0x04f69d264c000000 0xe7e4fff860000002 0xfcfc9fff0c000000

def z81 : W := mkw 0x27b4f932f6058550 0x84f69f265ec0b0aa 0xdf3cf83ffe0787ff 0x7be79f07ffc0f0ff

def z82 : W := mkw 0x0214000004048000 0x0042800000809000 0x9f3fc0001f1ff805 0xf3e7f80003e3ff00

def z83 : W := mkw 0x07feb802ded7d550 0x80ffd7005bdafaaa 0x47d830039ee70000 0x28fb060073dce000

def z84 : W := mkw 0x080106c501202226 0x410020d8a0240444 0x200007c000000000 0x040000f800000000

def z85 : W := mkw 0x14a0036809b80287 0x0294006d01370050 0xb7e007f81ff80004 0xf6fc00ff03ff0000

def z86 : W := mkw 0x204bc49520000000 0x04097892a4000000 0x0003c00000000000 0x0000780000000000

def z87 : W := mkw 0x0314280246048110 0x8062850048c09022 0x9f1c08007e07819d 0x73e381000fc0f033

def z88 : W := mkw 0x08001248916b6eee 0x61000249122d6ddd 0x1800000011fffffc 0x03000000023fffff

def z89 : W := mkw 0x084a00c100624002 0x41094018200c4800 0x00c001c000e00000 0x00180038001c0000

def z90 : W := mkw 0x0000000004048000 0x0000000000809000 0x180000001e078004 0x0300000003c0f000

def z91 : W := mkw 0x0214800004049000 0x0042900000809200 0x0004c00000009800 0x0000980000001300

def z92 : W := mkw 0x15a029280a980181 0x02b4052501530030 0xf7e03ff80e180182 0xfefc07ff01c30030

def z93 : W := mkw 0x05eb2da500000000 0x00bd65b4a0000000 0xe7fb3fff80000003 0xfcff67fff0000000

def z94 : W := mkw 0x0000000000000000 0x0000000000000000 0xc018300780000003 0x38030600f0000000

def z95 : W := mkw 0x294b7ff7f1636666 0x45296ffefe2c6ccc 0xe8db3ffff1e76667 0xbd1b67fffe3ceccc

def z96 : W := mkw 0x0effd6ddbdfffeee 0x61dffadbb7bfffdd 0xffffffffffffffff 0xffffffffffffffff

def z97 : W := mkw 0x27ffefbf61082aac 0x24fffdf7ec210555 0xffffffffe118ffff 0xfffffffffc231fff

def z98 : W := mkw 0x0b5f3ec7d767e776 0xc16be7d8faecfcee 0xffdf3fc7ffe7e7ff 0xfffbe7f8fffcfcff

def z99 : W := mkw 0x0001441420000000 0x0000288284000000 0xa027ce3c60000003 0xd404f9c78c000000

def z100 : W := mkw 0x0000000000000000 0x0000000000000000 0x9827c8046118ffff 0xd304f9008c231fff

def z101 : W := mkw 0x27ffedb766048110 0x84fffdb6ecc09022 0xf7ffffffee00819b 0xfefffffffdc01033

def z102 : W := mkw 0x084b16c59767e776 0xc10962d8b2ecfcee 0xf8db37c79fe7e7ff 0xbf1b66f8f3fcfcff

def z103 : W := mkw 0x11003b6813280787 0x0220076d026500f0 0x60003ff800000782 0x0c0007ff000000f0

def z104 : W := mkw 0x0000000000000000 0x0000000000000000 0x0804000460008079 0x010080008c00100f

def z105 : W := mkw 0x0000100090010440 0x0000020012002088 0xd81c3807f00787ff 0x7b038700fe00f0ff

def z106 : W := mkw 0x01017e1c33082fac 0x20202fc3866105f5 0xff27fe3c7f18ffff 0xffe4ffc78fe31fff

def z107 : W := mkw 0x084b16c591636666 0x410962d8b22c6ccc 0xf8df3fc7f1e7e7ff 0xff1be7f8fe3cfcff

def z108 : W := mkw 0x27ffedb760000000 0x04fffdb6ec000000 0xffffffffe118f807 0xfffffffffc231f00

def z109 : W := mkw 0x27ffffbff70daffc 0xa4fffff7fee1b5ff 0xffffffffff1fffff 0xffffffffffe3ffff

def z110 : W := mkw 0x03143802d6058550 0x806287005ac0b0aa 0xdf3ff807ff1fffff 0xfbe7ff00ffe3ffff

def z111 : W := mkw 0x004a008100000000 0x0009401020000000 0x40d831c380000000 0x281b063870000000

def z112 : W := mkw 0x0214000004048000 0x0042800000809000 0x9f1c00001e078005 0x73e3800003c0f000

def z113 : W := mkw 0x14a0012808980081 0x0294002501130010 0x0020003800180000 0x0004000700030000

def z114 : W := mkw 0x080010c190210442 0x4100021832042088 0x400031c380000000 0x0800063870000000

def z115 : W := mkw 0x06b4c0182c9c9888 0x20d6980305939311 0x1724c8386e189998 0x42e499070dc31333

def z116 : W := mkw 0x0314280240000000 0x0062850048000000 0xc71c3807e0000003 0x78e38700fc000000

def z117 : W := mkw 0x0000020801080284 0x0000004100210050 0x2020063801180000 0x840400c700230000

def z118 : W := mkw 0x0314280246048110 0x8062850048c09022 0x9f0408046e0087ff 0x53e081008dc010ff

def z119 : W := mkw 0x0100380092010540 0x00200700124020a8 0xdf1838079e0707e7 0x7be30700f3c0e0fc

def z120 : W := mkw 0x15a03b681bb80787 0x02b4076d037700f0 0xffe43ffc7ff887ff 0xfffc87ff8fff10ff

def z121 : W := mkw 0x004a000000424000 0x0009400000084800 0x00d8000010e70000 0x201b0000021ce000

def z122 : W := mkw 0x004b048500000000 0x00096090a0000000 0x20c307c000000000 0x841860f800000000

def z123 : W := mkw 0x11003b681bb80787 0x0220076d037700f0 0x70003ff81ff80786 0x0e0007ff03ff00f0

def z124 : W := mkw 0x0000401820080888 0x2000080304010111 0x1024c83860189998 0x420499070c031333

def z125 : W := mkw 0x15a03b6adbb907d7 0x82b4076d5b7720fa 0xf7e03ffffff807fe 0xfefc07ffffff00ff

def z126 : W := mkw 0x0000100010000400 0x0000020002000080 0xc000300010000606 0x38000600020000c0

def z127 : W := mkw 0x0001441420000000 0x0000288284000000 0x2023c63800000000 0x840478c700000000

def z128 : W := mkw 0x17febb681bb80787 0x02ffd76d037700f0 0xf7fffff81ff80787 0xfeffffff03ff00f0

def z129 : W := mkw 0x0801565cb16b6eee 0x61002acb962d6ddd 0xb827ce3c71ffffff 0xd704f9c78e3fffff

def z130 : W := mkw 0x0efe92409df7f666 0x41dfd24813befecc 0x9fffc0001ffffe65 0xf3fff80003ffffcc

def z131 : W := mkw 0x27fee9326cd6d000 0x04ffdd264d9ada00 0x9fffc8387ffff805 0xf3fff9070fffff00

def z132 : W := mkw 0x15a17f7c3bb82faf 0x22b42fef877705f5 0xf7e03ffc7ff807fe 0xfefc07ff8fff00ff

def z133 : W := mkw 0x080116c591212666 0x410022d8b22424cc 0x600037c780000662 0x0c0006f8f00000cc

def z134 : W := mkw 0x27ffedb760002828 0x24fffdb6ec000505 0xefffffffe000f87b 0xfdfffffffc001f0f

def z135 : W := mkw 0x0001461c21082aac 0x200028c384210555 0x3027ce386118f998 0xc604f9c70c231f33

def z136 : W := mkw 0x225fc49760002828 0x244bf892ec000505 0x081fc007e000f879 0x0103f800fc001f0f

def z137 : W := mkw 0x0214000000000000 0x0042800000000000 0x871c000000000001 0x70e3800000000000

def z138 : W := mkw 0x01003802d6058550 0x802007005ac0b0aa 0x58003807fe0787fe 0x0b000700ffc0f0ff

def z139 : W := mkw 0x02154416e405a878 0xa042a882dc80b50f 0x081fc007e007f879 0x0103f800fc00ff0f

def z140 : W := mkw 0x0001461c21082aac 0x200028c384210555 0x20000e3c600007fa 0x040001c78c0000ff

def z141 : W := mkw 0x25ebedb760000000 0x04bd7db6ec000000 0x60e3ffffe0000002 0x8c1c7ffffc000000

def z142 : W := mkw 0x0314280240000000 0x0062850048000000 0xdf1c3807e00087ff 0x7be38700fc0010ff

def z143 : W := mkw 0x004a800000425000 0x0009500000084a00 0x0003c00000007800 0x0000780000000f00

def z144 : W := mkw 0x0001561cb1092eec 0x20002ac3962125dd 0xf83ffe3ff11fffff 0xff07ffc7fe23ffff

def z145 : W := mkw 0x11003b6ad32907d7 0x8220076d5a6520fa 0x60003fffe00007fa 0x0c0007fffc0000ff

def z146 : W := mkw 0x15a029280a980181 0x02b4052501530030 0x172008380e180180 0x42e4010701c30030

def z147 : W := mkw 0x17b43b6adfbd87d7 0x82f6876d5bf7b0fa 0xfffc3fffffff87ff 0xffff87fffffff0ff

def z148 : W := mkw 0x080012409df7f666 0x4100024813befecc 0x180000001ffffe64 0x0300000003ffffcc

def z149 : W := mkw 0x06fe800000000000 0x00dfd00000000000 0x87ffc00000000001 0xf0fff80000000000

def z150 : W := mkw 0x07feb802ded7d550 0x80ffd7005bdafaaa 0xdffff807ffffffff 0xfbffff00ffffffff

def z151 : W := mkw 0x025e80000446d000 0x004bd0000088da00 0x0018000000070000 0x000300000000e000

def z152 : W := mkw 0x0eff96c59df7f666 0x41dff2d8b3befecc 0xfffff7c79ffffe67 0xfffffef8f3ffffcc

def z153 : W := mkw 0x1dea3be99bfb47c7 0x43bd477d337f68f8 0xf7f83ffb9fff0786 0xfeff07ff73ffe0f0

def z154 : W := mkw 0x06b5c61c2d9cbaac 0x20d6b8c385b39755 0xbf27ce3c6f18ffff 0xd7e4f9c78de31fff

def z155 : W := mkw 0x0001461c21082aac 0x200028c384210555 0xb0200e3c611807fe 0xd60401c78c2300ff

def z156 : W := mkw 0x0214000004048000 0x0042800000809000 0x071800001e070000 0x20e3000003c0e000

def z157 : W := mkw 0x0215461ee50daafc 0xa042a8c3dca1b55f 0xb83fce3fe11fffff 0xd707f9c7fc23ffff

def z158 : W := mkw 0x0000000000000000 0x0000000000000000 0x8800000400000667 0x11000000800000cc

def z159 : W := mkw 0x084b56ddb16b6eee 0x61096adbb62d6ddd 0xe8fbf7ff91ff7e67 0xbd1f7efff23fefcc

def z160 : W := mkw 0x15a03b681bb80787 0x02b4076d037700f0 0xffe7fff81ff8ff87 0xfffcffff03ff1ff0

def z161 : W := mkw 0x27feb9a3d6058550 0x84ffd7347ac0b0aa 0xdfdc39c7fe0787ff 0x7bfb8738ffc0f0ff

def z162 : W := mkw 0x0100380012000500 0x00200700024000a0 0xd70038001e000786 0x7ae0070003c000f0

def z163 : W := mkw 0x0b5f3c87d647e570 0xc16be790fac8fcae 0xdf1f3807fe07e7ff 0x7be3e700ffc0fcff

def z164 : W := mkw 0x084b048580436060 0x41096090b0086c0c 0xe8db37c780076063 0xbd1b66f8f000ec0c

def z165 : W := mkw 0x0000020801082aac 0x2000004100210555 0x180000000118fffc 0x0300000000231fff

def z166 : W := mkw 0x0a5f16c7d567e676 0xc14be2d8faacfcce 0xe8df37c7f1e7e67f 0xbd1be6f8fe3cfccf

def z167 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z168 : W := mkw 0x084b048580436060 0x41096090b0086c0c 0x081b000780076061 0x01036000f000ec0c

def z169 : W := mkw 0x0eff96c59df7f666 0x41dff2d8b3befecc 0xefdb37c79fe76667 0xbdfb66f8f3fceccc

def z170 : W := mkw 0x06fe80000cd6d000 0x00dfd000019ada00 0x8fdb00001fe76005 0xb1fb600003fcec00

def z171 : W := mkw 0x03143802d6058550 0x806287005ac0b0aa 0x5f1830039e0787fc 0x2be3060073c0f0ff

def z172 : W := mkw 0x0fffbec7dff7f776 0xc1fff7d8fbfefeee 0xffffffc7ffffffff 0xfffffff8ffffffff

def z173 : W := mkw 0x27ffedb7e4058050 0x84fffdb6fc80b00a 0xefffffffe007807b 0xfdfffffffc00f00f

def z174 : W := mkw 0x0ceb86c509f27226 0x419d70d8a13e4e44 0x20e3c7c001f87800 0x841c78f8003f0f00

def z175 : W := mkw 0x04a0000008900000 0x0094000001120000 0x172000000e180000 0x42e4000001c30000

def z176 : W := mkw 0x17b4392ade9d85d1 0x82f687255bd3b0ba 0xdf3c383ffe1f87ff 0x7be78707ffc3f0ff

def z177 : W := mkw 0x15a03b601bb00707 0x02b4076c037600e0 0xe7c037c01fe00606 0xbcf806f803fc00c0

def z178 : W := mkw 0x06b480000c949000 0x00d6900001929200 0x1724c0000e189800 0x42e4980001c31300

def z179 : W := mkw 0x0001060401002224 0x000020c080200444 0xa803060401006667 0x950060c080200ccc

def z180 : W := mkw 0x100012481bb80787 0x02000249037700f0 0x100000001ff80784 0x0200000003ff00f0

def z181 : W := mkw 0x27fea9a340000000 0x04ffd53468000000 0x47d831c380000000 0x28fb063870000000

def z182 : W := mkw 0x16fe83680dfed287 0x02dfd06d01bfda50 0xbfffc7f81ffff805 0xf7fff8ff03ffff00

def z183 : W := mkw 0x27ffedb760000000 0x04fffdb6ec000000 0x67fbf7fb80000000 0xacff7eff70000000

def z184 : W := mkw 0x04ea800000000000 0x009d500000000000 0x00e3c00000000000 0x801c780000000000

def z185 : W := mkw 0x07b4292240000000 0x00f6852448000000 0xe7fc3fffe0000003 0xfcff87fffc000000

def z186 : W := mkw 0x084b16c591636666 0x410962d8b22c6ccc 0x60d837c790e70662 0x2c1b06f8f21ce0cc

def z187 : W := mkw 0x06fe80000cd6d000 0x00dfd000019ada00 0x17fcc0001eff9800 0x62ff980003dff300

def z188 : W := mkw 0x06fec0182cded888 0x20dfd803059bdb11 0x9fffc8387ffff99d 0xf3fff9070fffff33

def z189 : W := mkw 0x0000000000000000 0x0000000000000000 0x8818000010070005 0x310300000200e000

def z190 : W := mkw 0x0ceb16c599f36666 0x419d62d8b33e6ccc 0xfffb37c79fff6667 0xffff66f8f3ffeccc

def z191 : W := mkw 0x1ceb07ed09fa62a7 0x439d60fda13f4c54 0x20e307f801f86000 0x841c60ff003f0c00

def z192 : W := mkw 0x05a03b6011200606 0x00b4076c022400c0 0xe7e03ff811e00606 0xfcfc07ff023c00c0

def z193 : W := mkw 0x07feb802ded7d550 0x80ffd7005bdafaaa 0xdffff0039ffff805 0xfbfffe0073ffff00

def z194 : W := mkw 0x14a0036809b80287 0x0294006d01370050 0xb0e00ff801f80786 0xd61c01ff003f00f0

def z195 : W := mkw 0x084a008180434040 0x4109401030086808 0x0018000380070000 0x000300007000e000

def z196 : W := mkw 0x0800124091636666 0x41000248122c6ccc 0xc818300791e76667 0x39030600f23ceccc

def z197 : W := mkw 0x2001449760000000 0x04002892ec000000 0x00000007e0000000 0x00000000fc000000

def z198 : W := mkw 0x0000020801082aac 0x2000004100210555 0x9827c0000118fffd 0xd304f80000231fff

def z199 : W := mkw 0x0000000000000000 0x0000000000000000 0x180000000118f804 0x0300000000231f00

def z200 : W := mkw 0x0001040400000000 0x0000208080000000 0xa003060400000003 0x940060c080000000

def z201 : W := mkw 0x0000000800080080 0x0000000100010010 0x1020083800180180 0x4204010700030030

def z202 : W := mkw 0x2ffffdf7f0634442 0x45ffffbefe0c6888 0xe7fffffff0e70003 0xfcfffffffe1ce000

def z203 : W := mkw 0x27b4e93266048110 0x84f69d264cc09022 0x1724c8386e008198 0x42e499070dc01033

def z204 : W := mkw 0x0001565c31282eae 0x20002acb862505d5 0xf8e7fffc71f8ffff 0xff1cffff8e3f1fff

def z205 : W := mkw 0x1deb3fed9bfb67e7 0x43bd67fdb37f6cfc 0xfffb3fff9fff67e7 0xffff67fff3ffecfc

def z206 : W := mkw 0x15a03b681bb82faf 0x22b4076d037705f5 0xffe03ff81ff8fffe 0xfffc07ff03ff1fff

def z207 : W := mkw 0x05a038001a900500 0x00b40700035200a0 0xd7e038001ff80786 0xfafc070003ff00f0

def z208 : W := mkw 0x15a03b689bb907c7 0x02b4076d137720f8 0xfff83fff9fff07e7 0xffff07fff3ffe0fc

def z209 : W := mkw 0x24ebc5b520000000 0x049d78b6a4000000 0xe0fbf7ff80000003 0xbc1f7efff0000000

def z210 : W := mkw 0x15a03b681bb80787 0x02b4076d037700f0 0x77203ff80e180782 0x4ee407ff01c300f0

def z211 : W := mkw 0x194b3fed936b67e7 0x432967fdb26d6cfc 0xe8db3fff91e767e7 0xbd1b67fff23cecfc

def z212 : W := mkw 0x0000124011200606 0x00000248022400c0 0xe0c037c011e00606 0xbc1806f8023c00c0

def z213 : W := mkw 0x27fea9a34cd6d000 0x04ffd534699ada00 0xdffff1c39ffff805 0xfbfffe3873ffff00

def z214 : W := mkw 0x0100292000000000 0x0020052400000000 0x60003ff800000002 0x0c0007ff00000000

def z215 : W := mkw 0x225fc49760000000 0x044bf892ec000000 0xe0dff7c7e0000003 0xbc1bfef8fc000000

def z216 : W := mkw 0x080156ddb1292eee 0x61002adbb62525dd 0x60003fffe00007fa 0x0c0007fffc0000ff

def z217 : W := mkw 0x0000000000000000 0x0000000000000000 0xa0200e3800000002 0xd40401c700000000

def z218 : W := mkw 0x27fffdb7f6058550 0x84ffffb6fec0b0aa 0xfffffffffe0787ff 0xffffffffffc0f0ff

def z219 : W := mkw 0x03143802d6058550 0x806287005ac0b0aa 0x481c3807e00787fb 0x09038700fc00f0ff

def z220 : W := mkw 0x37ffffff7ffed787 0x06ffffffefffdaf0 0xffffffffffffff87 0xfffffffffffffff0

def z221 : W := mkw 0x07feb802d6058550 0x80ffd7005ac0b0aa 0xdffff807fe0787ff 0xfbffff00ffc0f0ff

def z222 : W := mkw 0x0001060c010822a4 0x000020c180210454 0xb8230e3c011867e7 0xd70461c780230cfc

def z223 : W := mkw 0x37ffedbf6a980181 0x06fffdb7ed530030 0xf7ffffffee180183 0xfefffffffdc30030

def z224 : W := mkw 0x0800024001626226 0x41000048002c4c44 0x0000000001e06000 0x00000000003c0c00

def z225 : W := mkw 0x0000100096058550 0x8000020012c0b0aa 0x180000001e0787fc 0x0300000003c0f0ff

def z226 : W := mkw 0x0000100096058550 0x8000020012c0b0aa 0xd81830079e0787ff 0x3b030600f3c0f0ff

def z227 : W := mkw 0x084b16c591636666 0x410962d8b22c6ccc 0xf8fff7c791fffe67 0xff1ffef8f23fffcc

def z228 : W := mkw 0x0eff86c50df6f226 0x41dff0d8a1bede44 0xbfffc7c01ffff805 0xf7fff8f803ffff00

def z229 : W := mkw 0x06fe8002ccd7d050 0x80dfd000599afa0a 0x9fffc007fffff87d 0xf3fff800ffffff0f

def z230 : W := mkw 0x27ffefbf61080284 0x04fffdf7ec210050 0xf7ffffffe1180787 0xfefffffffc2300f0

def z231 : W := mkw 0x1deb3fe59bf36767 0x43bd67fcb37e6cec 0xefdb37c79fe76667 0xbdfb66f8f3fceccc

def z232 : W := mkw 0x00000002c0010050 0x800000005800200a 0x00000007e0000078 0x00000000fc00000f

def z233 : W := mkw 0x14a0036809b80287 0x0294006d01370050 0x20e007f801f80000 0x841c00ff003f0000

def z234 : W := mkw 0x0214000004048000 0x0042800000809000 0x170400000e008000 0x42e0800001c01000

def z235 : W := mkw 0x0000000000000000 0x0000000000000000 0x8027c00000000001 0xd004f80000000000

def z236 : W := mkw 0x03157e1ef70daffc 0xa062afc3dee1b5ff 0xff1c3e3ffe0787ff 0x7fe387c7ffc0f0ff

def z237 : W := mkw 0x35ebfffd3bb80787 0x06bd7fffa77700f0 0xf7e3fff81ff80786 0xfefc7fff03ff00f0

def z238 : W := mkw 0x084b16c591636666 0x410962d8b22c6ccc 0x681b37c780076663 0x0d0366f8f000eccc

def z239 : W := mkw 0x03156e1e61082aac 0x2062adc3cc210555 0xff3ffe3fe118ffff 0xffe7ffc7fc231fff

def z240 : W := mkw 0x14a012481bb80787 0x02940249037700f0 0x97e000001ff80784 0xf2fc000003ff00f0

def z241 : W := mkw 0x0001461c21082aac 0x200028c384210555 0x2827c63c6118f879 0x8504f8c78c231f0f

def z242 : W := mkw 0x06fe80000cd6d000 0x00dfd000019ada00 0x1f3fc0000e1ff801 0x43e7f80001c3ff00

def z243 : W := mkw 0x000010009ed7d550 0x8000020013dafaaa 0x180000001ffffffc 0x0300000003ffffff

def z244 : W := mkw 0x06fe80000cd6d000 0x00dfd000019ada00 0x08ffc00001fff801 0x811ff800003fff00

def z245 : W := mkw 0x17b43b6a5bb80787 0x02f6876d4b7700f0 0xf7fc3ffffff80787 0xfeff87ffffff00f0

def z246 : W := mkw 0x0000100096058550 0x8000020012c0b0aa 0x000000001e070000 0x0000000003c0e000

def z247 : W := mkw 0x15a03b689fbd87d7 0x82b4076d13f7b0fa 0xffe03ff81fff87fe 0xfffc07ff03fff0ff

def z248 : W := mkw 0x0000020801082aac 0x2000004100210555 0x00000000000007f8 0x00000000000000ff

def z249 : W := mkw 0x15a039681ab80583 0x02b4072d035700b0 0x57e039f81ef80180 0x6afc073f03df0030

def z250 : W := mkw 0x17b4a9280e9c9181 0x02f6952501d39230 0x1724c8380e189980 0x42e4990701c31330

def z251 : W := mkw 0x27ffedb760000000 0x04fffdb6ec000000 0x67d83fffe0000002 0x2cfb07fffc000000

def z252 : W := mkw 0x0000020001000204 0x0000004000200040 0xa000060001000606 0x940000c0002000c0

def z253 : W := mkw 0x084a12c191636666 0x41094258322c6ccc 0x48d831c391e76664 0x291b0638723ceccc

def z254 : W := mkw 0x15a039601ab00503 0x02b4072c035600a0 0xe7e03ff81ee00002 0xfcfc07ff03dc0000

def z255 : W := mkw 0x02140002c4058050 0x804280005880b00a 0x081c0007e0078079 0x01038000fc00f00f

def z256 : W := mkw 0x0314280240000000 0x0062850048000000 0x0704080060000000 0x40e081000c000000

def z257 : W := mkw 0x17feb9601ef6d503 0x02ffd72c03dedaa0 0x47d831c01ee70000 0x28fb063803dce000

def z258 : W := mkw 0x2ffffff7f1636666 0x45fffffefe2c6ccc 0xeffffffff1e76667 0xfdfffffffe3ceccc

def z259 : W := mkw 0x225fc69f61082aac 0x244bf8d3ec210555 0xb83fce3fe118ffff 0xd707f9c7fc231fff

def z260 : W := mkw 0x0000000000000000 0x0000000000000000 0x1004080060008198 0x420081000c001033

def z261 : W := mkw 0x0000100092010550 0x80000200124020aa 0x00000000000007f8 0x00000000000000ff

def z262 : W := mkw 0x15a029200a900101 0x02b4052401520020 0x070000000e000000 0x00e0000001c00000

def z263 : W := mkw 0x004b148590010440 0x00096290b2002088 0xe8db37c790070667 0xbd1b66f8f200e0cc

def z264 : W := mkw 0x084a124091636666 0x41094248122c6ccc 0x88db000011e76665 0xb11b6000023ceccc

def z265 : W := mkw 0x004b048500000000 0x00096090a0000000 0x001b000780000001 0x00036000f0000000

def z266 : W := mkw 0x000000000cd6d000 0x00000000019ada00 0x000000001ee70000 0x0000000003dce000

def z267 : W := mkw 0x0001060401002224 0x000020c080200444 0xb8070e046100e7ff 0xd700e1c08c201cff

def z268 : W := mkw 0x24ebc5b520000000 0x049d78b6a4000000 0x20e3c7f800000000 0x841c78ff00000000

def z269 : W := mkw 0x15a02b6809b80287 0x02b4056d01370050 0xe7e03ff801f80002 0xfcfc07ff003f0000

def z270 : W := mkw 0x0000401820080888 0x2000080304010111 0x9827c8386118f99d 0xd304f9070c231f33

def z271 : W := mkw 0x0000401820080888 0x2000080304010111 0x0020c03800181800 0x0004180700030300

def z272 : W := mkw 0x06b480000c949000 0x00d6900001929200 0x9f27c0000f18f805 0xd3e4f80001e31f00

def z273 : W := mkw 0x0000124091210646 0x00000248122420c8 0xe8d837c791e70667 0xbd1b06f8f23ce0cc

def z274 : W := mkw 0x24ebc7bd21082aac 0x249d78f7a4210555 0x20e3c7f801187800 0x841c78ff00230f00

def z275 : W := mkw 0x0000000000000000 0x0000000000000000 0x970000001e000004 0x72e0000003c00000

def z276 : W := mkw 0x01003a4013200706 0x00200748026400e0 0xf7c03fc01fe00786 0xfef807f803fc00f0

def z277 : W := mkw 0x0001048500000000 0x00002090a0000000 0x600037c780000002 0x0c0006f8f0000000

def z278 : W := mkw 0x100012481bb80787 0x02000249037700f0 0xf0c037c01ff80786 0xbe1806f803ff00f0

def z279 : W := mkw 0x084b56d5b1636666 0x41096adab62c6ccc 0xe8fffffff1e76667 0xfd1ffffffe3ceccc

def z280 : W := mkw 0x15eabb681bfa5787 0x02bd576d037f4af0 0xf7e3fff81ff87f86 0xfefc7fff03ff0ff0

def z281 : W := mkw 0x0001461c21082aac 0x200028c384210555 0xa823c63c01187e67 0x950478c780230fcc

def z282 : W := mkw 0x07feb8001ed6d500 0x00ffd70003dadaa0 0xdffff8001fffff87 0xfbffff0003fffff0

def z283 : W := mkw 0x180012489bfb67e7 0x43000249137f6cfc 0x180000001fff67e4 0x0300000003ffecfc

def z284 : W := mkw 0x23156db760000000 0x0462adb6ec000000 0xe71c3fffe0000003 0x7ce387fffc000000

def z285 : W := mkw 0x0deb3fe591636666 0x41bd67fcb22c6ccc 0xeffb3fff91e76667 0xfdff67fff23ceccc

def z286 : W := mkw 0x17b57f7effbdafff 0xa2f6afefdff7b5ff 0xffffffffffffffff 0xffffffffffffffff

def z287 : W := mkw 0x06ffc41420000000 0x00dff88284000000 0xa7ffce3c60000003 0xf4fff9c78c000000

def z288 : W := mkw 0x27ffedb764048000 0x04fffdb6ec809000 0xfffffffffe078007 0xffffffffffc0f000

def z289 : W := mkw 0x02141002d4058450 0x804282005a80b08a 0xc81c3007f007867f 0x39038600fe00f0cf

def z290 : W := mkw 0x27ffedb76cd6d000 0x04fffdb6ed9ada00 0xe7fffffffee70003 0xfcffffffffdce000

def z291 : W := mkw 0x0b143a42d767e776 0xc16287485aecfcee 0xdf1c3807ffe7e7ff 0x7be38700fffcfcff

def z292 : W := mkw 0x0800124091636666 0x41000248122c6ccc 0xe8c037c011e76666 0xbd1806f8023ceccc

def z293 : W := mkw 0x06fe80000cd6d000 0x00dfd000019ada00 0x87ffc0001ee70001 0xf0fff80003dce000

def z294 : W := mkw 0x0001441420000000 0x0000288284000000 0xb827ce3c6118f807 0xd704f9c78c231f00

def z295 : W := mkw 0x084b56ddb16b6eee 0x61096adbb62d6ddd 0xe8db3ffff1e767ff 0xbd1b67fffe3cecff

def z296 : W := mkw 0x06fe800008d25000 0x00dfd000011a4a00 0x87ffc00001f87801 0xf0fff800003f0f00

def z297 : W := mkw 0x06ffc61c21082aac 0x20dff8c384210555 0xbfffce3c6118ffff 0xf7fff9c78c231fff

def z298 : W := mkw 0x06fe80000cd6d000 0x00dfd000019ada00 0x9fffc8047fffffff 0xf3fff9008fffffff

def z299 : W := mkw 0x21016db760000000 0x04202db6ec000000 0xe027ffffe0000003 0xdc04fffffc000000

def z300 : W := mkw 0x06fe82080dded284 0x00dfd04101bbda50 0xbfffce381fffff87 0xf7fff9c703fffff0

def z301 : W := mkw 0x025e80000446d000 0x004bd0000088da00 0x9f1fc0001e07f805 0x73e3f80003c0ff00

def z302 : W := mkw 0x17febb681ffed787 0x02ffd76d03ffdaf0 0xfffffff81fffff87 0xffffffff03fffff0

def z303 : W := mkw 0x03143802d6058550 0x806287005ac0b0aa 0x47183807fe0707fa 0x28e30700ffc0e0ff

def z304 : W := mkw 0x084b56d5b1636e6e 0x61096adab62c6dcd 0xe8dff7c7f1e7fe7f 0xbd1bfef8fe3cffcf

def z305 : W := mkw 0x0000000000000000 0x0000000000000000 0x9000080000000786 0x52000100000000f0

def z306 : W := mkw 0x27ffada740000000 0x04fff5b4e8000000 0xe7db37c780000003 0xbcfb66f8f0000000

def z307 : W := mkw 0x27ffedb76446d000 0x04fffdb6ec88da00 0xefffffffe007f803 0xfdfffffffc00ff00

def z308 : W := mkw 0x025e80000446d000 0x004bd0000088da00 0x88dfc00011e7f805 0xb11bf800023cff00

def z309 : W := mkw 0x0801048580012060 0x41002090b000240c 0x0000000780000060 0x00000000f000000c

def z310 : W := mkw 0x06ffc4142cd6f828 0x20dff882859adf05 0x9fffc0047ffff87d 0xf3fff8008fffff0f

def z311 : W := mkw 0x0001461c21082aac 0x200028c384210555 0x38000e3c6118fffe 0x070001c78c231fff

def z312 : W := mkw 0x084b06c501626226 0x410960d8a02c4c44 0x20c307c001e06000 0x841860f8003c0c00

def z313 : W := mkw 0x0efe90c19cf7d442 0x41dfd218339efa88 0x47d831c39ee70000 0x28fb063873dce000

def z314 : W := mkw 0x0214100096058550 0x8042820012c0b0aa 0x9f1c00001e0787fd 0x73e3800003c0f0ff

def z315 : W := mkw 0x0b5e38c3d667c552 0xc16bc7187accf8aa 0xdfdc39c7fee787ff 0x7bfb8738ffdcf0ff

def z316 : W := mkw 0x04ea80000cd6d000 0x009d5000019ada00 0x18e3c0001ffff804 0x831c780003ffff00

def z317 : W := mkw 0x27ffedb760424000 0x04fffdb6ec084800 0xeffffffff1e76007 0xfdfffffffe3cec00

def z318 : W := mkw 0x1001565c3bb82faf 0x22002acb877705f5 0xb827ce3c7ff8ffff 0xd704f9c78fff1fff

def z319 : W := mkw 0x0100380096058550 0x8020070012c0b0aa 0xdf0038001e0787fe 0x7be0070003c0f0ff

def z320 : W := mkw 0x06fe80000cd6d000 0x00dfd000019ada00 0x07fbc0001fff7800 0xa0ff780003ffef00

def z321 : W := mkw 0x084b16c591636666 0x410962d8b22c6ccc 0x60db37c391e76000 0xac1b66f8723cec00

def z322 : W := mkw 0x0000104010200402 0x0000020802040080 0x40c031c010e00000 0x28180638021c0000

def z323 : W := mkw 0x17feb9601ef6d503 0x02ffd72c03dedaa0 0xdffff1c01ffff805 0xfbfffe3803ffff00

def z324 : W := mkw 0x37feb9e35ab00503 0x06ffd73c6b5600a0 0x47d831c39ee00000 0x28fb063873dc0000

def z325 : W := mkw 0x0000401020000808 0x2000080204000101 0x0004c00060009818 0x000098000c001303

def z326 : W := mkw 0x225e808340000000 0x044bd01068000000 0x0018000380000000 0x0003000070000000

def z327 : W := mkw 0x06fe82080ddefaac 0x20dfd04101bbdf55 0x9fffc0001ffffffd 0xf3fff80003ffffff

def z328 : W := mkw 0x14ea836809fa5287 0x029d506d013f4a50 0x20e3c7f801f87800 0x841c78ff003f0f00

def z329 : W := mkw 0x0001461c21082aac 0x200028c384210555 0x1807c0046118fffd 0x0300f8008c231fff

def z330 : W := mkw 0x07fffe1effdffffc 0xa0ffffc3dffbffff 0xfffffe3fffffffff 0xffffffc7ffffffff

def z331 : W := mkw 0x17b43b681fbc8787 0x02f6876d03f790f0 0xfffc3ff81fff8787 0xffff87ff03fff0f0

def z332 : W := mkw 0x2cebd7f5b1636666 0x459d7afeb62c6ccc 0xe8fbf7ff91e76667 0xbd1f7efff23ceccc

def z333 : W := mkw 0x0001441420002828 0x2000288284000505 0x0000000460000078 0x000000008c00000f

def z334 : W := mkw 0x0001164411202626 0x000022c8822404c4 0xe8c337c411e06667 0xbd1866f8823c0ccc

def z335 : W := mkw 0x084b46dd216a6aae 0x610968dba42d4d55 0xb8e7cffc61f8ffff 0xd71cf9ff8c3f1fff

def z336 : W := mkw 0x0efe90c19cf7d442 0x41dfd218339efa88 0xdffff1c39ffff805 0xfbfffe3873ffff00

def z337 : W := mkw 0x0214100094058440 0x004282001280b088 0xdf1c30079e078667 0x7be38600f3c0f0cc

def z338 : W := mkw 0x37ffffff73280787 0x06ffffffee6500f0 0xe7ffffffe0000783 0xfcfffffffc0000f0

def z339 : W := mkw 0x0001461c21082aac 0x200028c384210555 0xa027ce3c600007fb 0xd404f9c78c0000ff

def z340 : W := mkw 0x0001461421002a2c 0x200028c284200545 0xa807c6046100fe7f 0x9500f8c08c201fcf

def z341 : W := mkw 0x0000421821082aac 0x2000084304210555 0x1824c8386118fffc 0x430499070c231fff

def z342 : W := mkw 0x03156c1660000000 0x0062ad82cc000000 0xe73ffe3fe0000003 0xfce7ffc7fc000000

def z343 : W := mkw 0x0100380012000500 0x00200700024000a0 0x470030001e000000 0x28e0060003c00000

def z344 : W := mkw 0x01017e1ef3092ffc 0xa0202fc3de6125ff 0xf827fe3fe118ffff 0xdf04ffc7fc231fff

def z345 : W := mkw 0x27fea9a34cd6d000 0x04ffd534699ada00 0x47d831c39ee70000 0x28fb063873dce000

def z346 : W := mkw 0x03143a42d7258756 0x806287485ae4b0ea 0xffdc3fc7ffe787ff 0xfffb87f8fffcf0ff

def z347 : W := mkw 0x01003a0813080784 0x00200741026100f0 0xf7203e381f180786 0xfee407c703e300f0

def z348 : W := mkw 0x01003802d2010550 0x802007005a4020aa 0xd8043807e00087ff 0x5b008700fc0010ff

def z349 : W := mkw 0x0000000008d25000 0x00000000011a4a00 0x0000000001f87800 0x00000000003f0f00

def z350 : W := mkw 0x084b06c581636266 0x410960d8b02c6c4c 0x28db07c781e76061 0x851b60f8f03cec0c

def z351 : W := mkw 0x084b06c501626226 0x410960d8a02c4c44 0xe0db37c781e06003 0xbc1b66f8f03c0c00

def z352 : W := mkw 0x15a03b681bb80787 0x02b4076d037700f0 0x57c031c01ff80784 0x2af8063803ff00f0

def z353 : W := mkw 0x0801164491636666 0x410022c8922c6ccc 0xa803060411e76667 0x950060c0823ceccc

def z354 : W := mkw 0x094b3ec7d3636776 0xc12967d8fa6c6cee 0xe8db3fc7f1e767ff 0xbd1b67f8fe3cecff

def z355 : W := mkw 0x17b4292a4e9c8191 0x82f6852549d39032 0x172408386e188198 0x42e481070dc31033

def z356 : W := mkw 0x080156ddb1292eee 0x61002adbb62525dd 0xf827ffffe118ffff 0xdf04fffffc231fff

def z357 : W := mkw 0x184b16cd9bfb67e7 0x430962d9b37f6cfc 0xf8db37c79fff67e7 0xbf1b66f8f3ffecfc

def z358 : W := mkw 0x17b43962deb58553 0x82f6872c5bd6b0aa 0x47d831c39ee70000 0x28fb063873dce000

def z359 : W := mkw 0x03143802d0010440 0x006287005a002088 0xcf1c3807f0070667 0x79e38700fe00e0cc

def z360 : W := mkw 0x0000000000000000 0x0000000000000000 0x0807c0000000f801 0x0100f80000001f00

def z361 : W := mkw 0x37fffdf77ab00503 0x06ffffbeef5600a0 0xe7fffffffee00003 0xfcffffffffdc0000

def z362 : W := mkw 0x05a02b2801080284 0x00b4056500210050 0xf7e03ff801180786 0xfefc07ff002300f0

def z363 : W := mkw 0x035f2c8740000000 0x006be590e8000000 0xe7df3fc7e0000003 0xfcfbe7f8fc000000

def z364 : W := mkw 0x05a0292000000000 0x00b4052400000000 0x0720083800000000 0x40e4010700000000

def z365 : W := mkw 0x035e3802d647c550 0x806bc7005ac8f8aa 0xdfdf3807ffe7e7ff 0xfbfbe700fffcfcff

def z366 : W := mkw 0x07fea9200cd6d000 0x00ffd524019ada00 0xfffffff81ffff807 0xffffffff03ffff00

def z367 : W := mkw 0x084b16cd916b66e6 0x410962d9b22d6cdc 0xf8fb3fff91ff67e7 0xff1f67fff23fecfc

def z368 : W := mkw 0x15a069382a980989 0x22b40d2705530131 0x1724c8386e189998 0x42e499070dc31333

def z369 : W := mkw 0x17febb6adfffd7d7 0x82ffd76d5bfffafa 0xffffffffffffffff 0xffffffffffffffff

def z370 : W := mkw 0x04a0800008901000 0x0094100001120200 0x0020c00000181800 0x0004180000030300

def z371 : W := mkw 0x07fea92000000000 0x00ffd52400000000 0xe7fffff800000003 0xfcffffff00000000

def z372 : W := mkw 0x04ea800008d25000 0x009d5000011a4a00 0x97e3c0001ff87804 0xf2fc780003ff0f00

def z373 : W := mkw 0x27fffff771200606 0x04fffffeee2400c0 0xe7fffffff1e00607 0xfcfffffffe3c00c0

def z374 : W := mkw 0x0314380252000500 0x006287004a4000a0 0xd71c3807fe000787 0x7ae38700ffc000f0

def z375 : W := mkw 0x17ffff7c3ffeffaf 0x22ffffef87ffdff5 0xfffffffc7fffffff 0xffffffff8fffffff

def z376 : W := mkw 0x0214000244048010 0x8042800048809002 0x0004000060008018 0x000080000c001003

def z377 : W := mkw 0x03142802c4058050 0x806285005880b00a 0xcf1c3807e007807b 0x79e38700fc00f00f

def z378 : W := mkw 0x03143802d6058550 0x806287005ac0b0aa 0xc71c3807fe070003 0x78e38700ffc0e000

def z379 : W := mkw 0x06b4800000000000 0x00d6900000000000 0x0724c00000000000 0x40e4980000000000

def z380 : W := mkw 0x02140002c4058050 0x804280005880b00a 0x0018000380070000 0x000300007000e000

def z381 : W := mkw 0x15a07b783bb80f8f 0x22b40f6f077701f1 0xf7e4fff87ff89f9e 0xfefc9fff0fff13f3

def z382 : W := mkw 0x0000020801082aac 0x2000004100210555 0x980408046118ffff 0x530081008c231fff

def z383 : W := mkw 0x1deb3fed1bfa67a7 0x43bd67fda37f4cf4 0xf7e33ff81ff86786 0xfefc67ff03ff0cf0

def z384 : W := mkw 0x21016fbf61082aac 0x24202df7ec210555 0x60003fffe00007fa 0x0c0007fffc0000ff

def z385 : W := mkw 0x084b14c590634442 0x41096298b20c6888 0xe0db37c790e70003 0xbc1b66f8f21ce000

def z386 : W := mkw 0x14a013681bb80787 0x0294026d037700f0 0x30e007f81ff80784 0x861c00ff03ff00f0

def z387 : W := mkw 0x0314280246048110 0x8062850048c09022 0xd71c3807ee00819b 0x7ae38700fdc01033

def z388 : W := mkw 0x004a100090434440 0x0009420012086888 0xc8db300791e76667 0xb91b6600f23ceccc

def z389 : W := mkw 0x0001441420002828 0x2000288284000505 0x9807c8046000ffff 0x5300f9008c001fff

def z390 : W := mkw 0x27ffedb760000000 0x04fffdb6ec000000 0x073fc83fe0000001 0x40e7f907fc000000

def z391 : W := mkw 0x15a17f7c3bb82faf 0x22b42fef877705f5 0xf7e3fff81ff87f86 0xfefc7fff03ff0ff0

def z392 : W := mkw 0x25ebedb520000000 0x04bd7db6a4000000 0xe7e3fff800000002 0xfcfc7fff00000000

def z393 : W := mkw 0x27ffedb760000000 0x04fffdb6ec000000 0xffffffffe00087ff 0xfffffffffc0010ff

def z394 : W := mkw 0x01017e1ef3092ffc 0xa0202fc3de6125ff 0x60003e3fe00007fa 0x0c0007c7fc0000ff

def z395 : W := mkw 0x084b06c501626226 0x410960d8a02c4c44 0xa8c307c401e06667 0x951860f8803c0ccc

def z396 : W := mkw 0x084b16c511626626 0x410962d8a22c4cc4 0xe0c337c011e06606 0xbc1866f8023c0cc0

def z397 : W := mkw 0x084b16c591636666 0x410962d8b22c6ccc 0x28c307c011e76664 0x851860f8023ceccc

def z398 : W := mkw 0x04ea000008d24000 0x009d4000011a4800 0x9ffb00001fff6005 0xf3ff600003ffec00

def z399 : W := mkw 0x235ffc97f6058550 0x846bff92fec0b0aa 0xdf1ff807fe0787ff 0x7be3ff00ffc0f0ff

def z400 : W := mkw 0x16fe92481ffed787 0x02dfd24903ffdaf0 0x9fffc0001fffff85 0xf3fff80003fffff0

def z401 : W := mkw 0x27fee9b360000000 0x04ffdd366c000000 0x47fcf9fbe0000000 0x68ff9f3f7c000000

def z402 : W := mkw 0x0001461c21082aac 0x200028c384210555 0xb023ce3801187f86 0xd60479c700230ff0

def z403 : W := mkw 0x3ffffffffbfb67e7 0x47ffffffff7f6cfc 0xffffffffffff67e7 0xffffffffffffecfc

def z404 : W := mkw 0x0001461c21082aac 0x200028c384210555 0x2000063800000000 0x040000c700000000

def z405 : W := mkw 0x04a0000008900000 0x0094000001120000 0x07c000001ee00000 0x20f8000003dc0000

def z406 : W := mkw 0x15a02b280b980385 0x02b4056501730070 0xb7200e380f180786 0xd6e401c701e300f0

def z407 : W := mkw 0x025e8002c447d050 0x804bd0005888fa0a 0x081fc007e007f879 0x0103f800fc00ff0f

def z408 : W := mkw 0x21017db7f2010550 0x84202fb6fe4020aa 0x60003fffe00007fa 0x0c0007fffc0000ff

def z409 : W := mkw 0x0800124091212666 0x41000248122424cc 0x0000000000000660 0x00000000000000cc

def z410 : W := mkw 0x2a5fc497e0436060 0x454bf892fc086c0c 0x081fc007e0076061 0x0103f800fc00ec0c

def z411 : W := mkw 0x0000020801082aac 0x2000004100210555 0xb8200e380118fffe 0xd70401c700231fff

def z412 : W := mkw 0x0000024001200206 0x0000004800240040 0x20c007c001e00000 0x841800f8003c0000

def z413 : W := mkw 0x15a03b6813280787 0x02b4076d026500f0 0xe7e03ff800000782 0xfcfc07ff000000f0

def z414 : W := mkw 0x27fea9a340000000 0x04ffd53468000000 0xe7f83ffb80000002 0xfcff07ff70000000

def z415 : W := mkw 0x11003a481bb80787 0x02200749037700f0 0xd70038001ff80786 0x7ae0070003ff00f0

def z416 : W := mkw 0x06fe800008900000 0x00dfd00001120000 0x97ffc0001ff80005 0xf2fff80003ff0000

def z417 : W := mkw 0x27fffdb7fed7d550 0x84ffffb6ffdafaaa 0xffffffffffffffff 0xffffffffffffffff

def z418 : W := mkw 0x26ffc49760000000 0x04dff892ec000000 0x87ffc007e0000001 0xf0fff800fc000000

def z419 : W := mkw 0x200145b520000000 0x040028b6a4000000 0x200007f800000000 0x040000ff00000000

def z420 : W := mkw 0x26ffc5b760000000 0x04dff8b6ec000000 0x20ffc7ffe0000001 0x841ff8fffc000000

def z421 : W := mkw 0x1da13fed9bb927e7 0x43b427fdb37724fc 0xf7e03fff9ff807e6 0xfefc07fff3ff00fc

def z422 : W := mkw 0x2ffffff7fdf7f666 0x45fffffeffbefecc 0xfffffffffffffe67 0xffffffffffffffcc

def z423 : W := mkw 0x03143a0ad70daffc 0xa06287415ae1b5ff 0xdf1c3807ff1fffff 0x7be38700ffe3ffff

def z424 : W := mkw 0x06fe90009cd7d440 0x00dfd200139afa88 0xdffff0079ffffe67 0xfbfffe00f3ffffcc

def z425 : W := mkw 0x0000020801080284 0x0000004100210050 0x1000000001180784 0x02000000002300f0

def z426 : W := mkw 0x06b480000c949000 0x00d6900001929200 0x9f3cc0001e1f9805 0x73e7980003c3f300

def z427 : W := mkw 0x27ffedb76c949000 0x04fffdb6ed929200 0xf7ffffffee189803 0xfefffffffdc31300

def z428 : W := mkw 0x004a00000cd6d000 0x00094000019ada00 0x98db00001ffff805 0xb31b600003ffff00

def z429 : W := mkw 0x025e80000cd6d000 0x004bd000019ada00 0x181fc0001ffff805 0x0303f80003ffff00

def z430 : W := mkw 0x04ea800008d25000 0x009d5000011a4a00 0x00c0000000e00000 0x00180000001c0000

def z431 : W := mkw 0x084b16cd916b6eee 0x610962d9b22d6ddd 0xf8db37c791ffffff 0xbf1b66f8f23fffff

def z432 : W := mkw 0x0001441420000000 0x0000288284000000 0x20000e3c60000002 0x040001c78c000000

def z433 : W := mkw 0x17fea9280eded181 0x02ffd52501dbda30 0x9fffc8381ffff985 0xf3fff90703ffff30

def z434 : W := mkw 0x0000000000000000 0x0000000000000000 0x1024c00000189800 0x4204980000031300

def z435 : W := mkw 0x084b14c590636462 0x41096298b20c6c8c 0x48db31c790e76061 0x291b6638f21cec0c

def z436 : W := mkw 0x24ebc5b528d25000 0x049d78b6a51a4a00 0x20e3c7f801f87800 0x841c78ff003f0f00

def z437 : W := mkw 0x06fe92401df6d606 0x00dfd24803bedac0 0xfffff7c01ffffe07 0xfffffef803ffffc0

def z438 : W := mkw 0x0a5f0487c447e070 0xc14be090f888fc0e 0x081f0007e007e079 0x0103e000fc00fc0f

def z439 : W := mkw 0x1fffbfed9ffff7e7 0x43fff7fdb3fffefc 0xffffffff9fffffe7 0xfffffffff3fffffc

def z440 : W := mkw 0x15a029280a980181 0x02b4052501530030 0x97e008381ff80184 0xf2fc010703ff0030

def z441 : W := mkw 0x17b43b6adfbd87d7 0x82f6876d5bf7b0fa 0xf7f83ffb9fff0786 0xfeff07ff73ffe0f0

def z442 : W := mkw 0x15a03b681ffed787 0x02b4076d03ffdaf0 0xffe03ff81fffff86 0xfffc07ff03fffff0

def z443 : W := mkw 0x03143802d6058550 0x806287005ac0b0aa 0xcf1830079e070667 0x39e30600f3c0e0cc

def z444 : W := mkw 0x0001060401002224 0x000020c080200444 0xb827c6040118fe67 0xd704f8c080231fcc

def z445 : W := mkw 0x0000000000000000 0x0000000000000000 0x18000000000087fc 0x03000000000010ff

def z446 : W := mkw 0x06fe80000cd6d000 0x00dfd000019ada00 0x0fdfc0001ee7f801 0x21fbf80003dcff00

def z447 : W := mkw 0x100012481bb80787 0x02000249037700f0 0xb0200e381ff80786 0xd60401c703ff00f0

def z448 : W := mkw 0x21016fbf61082aac 0x24202df7ec210555 0xf827ffffe118ffff 0xdf04fffffc231fff

def z449 : W := mkw 0x1da03b689bfb67e7 0x43b4076d137f6cfc 0xffe03ff81fff67e6 0xfffc07ff03ffecfc

def z450 : W := mkw 0x27ffefb761002224 0x04fffdf6ec200444 0xefffffffe1006667 0xfdfffffffc200ccc

def z451 : W := mkw 0x03157c16f605ad78 0xa062af82dec0b5af 0xdf1ff807fe07ffff 0x7be3ff00ffc0ffff

def z452 : W := mkw 0x27fffdb7f0010440 0x04ffffb6fe002088 0xeffffffff0070667 0xfdfffffffe00e0cc

def z453 : W := mkw 0x0001461c21082aac 0x200028c384210555 0x2807ce3c6000fffb 0x0500f9c78c001fff

def z454 : W := mkw 0x03142802c6058150 0x8062850058c0b02a 0x1f1c0807ee0781f9 0x43e38100fdc0f03f

def z455 : W := mkw 0x1fff3fefdfffe7f7 0xc3ffe7fdfbfffcfe 0xffff3fffffffe7ff 0xffffe7fffffffcff

def z456 : W := mkw 0x25a16db760000000 0x04b42db6ec000000 0xe7e03fffe0000002 0xfcfc07fffc000000

def z457 : W := mkw 0x004a000000424000 0x0009400000084800 0x00c3000001e06000 0x80186000003c0c00

def z458 : W := mkw 0x07fea8024cd6d000 0x00ffd500499ada00 0xdffff807fffff807 0xfbffff00ffffff00

def z459 : W := mkw 0x2100693260000000 0x04200d264c000000 0x0000083860000000 0x000001070c000000

def z460 : W := mkw 0x06ffc4142cd6d000 0x00dff882859ada00 0xbfffce3c7ffff807 0xf7fff9c78fffff00

def z461 : W := mkw 0x27b4e93a60080888 0x24f69d274c010111 0x1724c83860189998 0x42e499070c031333

def z462 : W := mkw 0x07fea80240000000 0x00ffd50048000000 0xc7fff807e0000003 0xf8ffff00fc000000

def z463 : W := mkw 0x0314280246048110 0x8062850048c09022 0x070000000e000000 0x00e0000001c00000

def z464 : W := mkw 0x06fe80000cd6d000 0x00dfd000019ada00 0x97f800001fff0004 0xf2ff000003ffe000

def z465 : W := mkw 0x225fc49760000000 0x044bf892ec000000 0xa03fce3fe0000003 0xd407f9c7fc000000

def z466 : W := mkw 0x004b16c511200606 0x000962d8a22400c0 0xe0db37c791e00607 0xbc1b66f8f23c00c0

def z467 : W := mkw 0x0000000000000000 0x0000000000000000 0x0023c00001187800 0x8004780000230f00

def z468 : W := mkw 0x004a000000000000 0x0009400000000000 0x80db000000000001 0xb01b600000000000

def z469 : W := mkw 0x025e800000000000 0x004bd00000000000 0x001fc00000000001 0x0003f80000000000

def z470 : W := mkw 0x06b480000cd6d000 0x00d69000019ada00 0x1f24c0001ffff804 0x43e4980003ffff00

def z471 : W := mkw 0x100010401ab00503 0x02000208035600a0 0x000000001ee00000 0x0000000003dc0000

def z472 : W := mkw 0x05a16f3c21082aac 0x20b42de784210555 0xffe7fffc6118ffff 0xfffcffff8c231fff

def z473 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000804600007fa 0x000001008c0000ff

def z474 : W := mkw 0x0800104090634442 0x41000208120c6888 0x0000000010e70000 0x00000000021ce000

def z475 : W := mkw 0x04a0000008900000 0x0094000001120000 0x9fe7c0001ff8f805 0xf3fcf80003ff1f00

def z476 : W := mkw 0x080012409767e776 0xc100024812ecfcee 0x180000001fe7e7fc 0x0300000003fcfcff

def z477 : W := mkw 0x15a16f3c2b982bad 0x22b42de785730575 0xbf27ce3c6f18ffff 0xd7e4f9c78de31fff

def z478 : W := mkw 0x06ffc61c2ddefaac 0x20dff8c385bbdf55 0xbfffc6381ffff805 0xf7fff8c703ffff00

def z479 : W := mkw 0x06fe80000cd6d000 0x00dfd000019ada00 0x9fdc00001ee78005 0x73fb800003dcf000

def z480 : W := mkw 0x1000124813280787 0x02000249026500f0 0x0000000000000780 0x00000000000000f0

def z481 : W := mkw 0x11017f7c33282faf 0x22202fef866505f5 0x60003ffc600007fa 0x0c0007ff8c0000ff

def z482 : W := mkw 0x15eb3fed1bb80787 0x02bd67fda37700f0 0xf7fb3fff9ff80787 0xfeff67fff3ff00f0

def z483 : W := mkw 0x084b469da14b6aec 0x610968d3b4296d5d 0xb83fce3fe11fffff 0xd707f9c7fc23ffff

def z484 : W := mkw 0x29017ff7f1212666 0x45202ffefe2424cc 0x60003fffe0000662 0x0c0007fffc0000cc

def z485 : W := mkw 0x0001461c21080284 0x000028c384210050 0xb027ce3c61180787 0xd604f9c78c2300f0

def z486 : W := mkw 0x06fe800000000000 0x00dfd00000000000 0x07d8000000000000 0x20fb000000000000

def z487 : W := mkw 0x06fe80000c949000 0x00dfd00001929200 0x97ffc0000e189801 0xf2fff80001c31300

def z488 : W := mkw 0x0000000000424000 0x0000000000084800 0x0800000011e76004 0x01000000023cec00

def z489 : W := mkw 0x15a03b681bb80787 0x02b4076d037700f0 0x172008381ff80784 0x42e4010703ff00f0

def z490 : W := mkw 0x0000020801080284 0x0000004100210050 0xb8240e3c611887ff 0xd70481c78c2310ff

def z491 : W := mkw 0x17febb681ffed787 0x02ffd76d03ffdaf0 0xf7f83ff81fff0786 0xfeff07ff03ffe0f0

def z492 : W := mkw 0x03153e06d705a774 0x8062a7c0dae0b4ee 0xff1f3e07ff07e7ff 0xffe3e7c0ffe0fcff

def z493 : W := mkw 0x11017f7c33282faf 0x22202fef866505f5 0xf827fffc6118ffff 0xdf04ffff8c231fff

def z494 : W := mkw 0x100000080a980181 0x0200000101530030 0x100000000e180180 0x0200000001c30030

def z495 : W := mkw 0x01003802d2010550 0x802007005a4020aa 0x4000300380000000 0x0800060070000000

def z496 : W := mkw 0x0214000004048000 0x0042800000809000 0x9f1c08047e0787ff 0x73e381008fc0f0ff

def z497 : W := mkw 0x03143802ded7d550 0x806287005bdafaaa 0xdf1c3807ffffffff 0x7be38700ffffffff

def z498 : W := mkw 0x15a039601ab00503 0x02b4072c035600a0 0xd7e031c01ff80004 0xfafc063803ff0000

def z499 : W := mkw 0x080116c591212666 0x410022d8b22424cc 0xe80337c781006667 0x9d0066f8f0200ccc

def z500 : W := mkw 0x0314781af60d8dd8 0xa0628f035ec1b1bb 0xdf3cf83ffe1f9fff 0x7be79f07ffc3f3ff

def z501 : W := mkw 0x0001441420000000 0x0000288284000000 0xb827ce3c600087ff 0xd704f9c78c0010ff

def z502 : W := mkw 0x004a000000424000 0x0009400000084800 0x081b000000076001 0x010360000000ec00

def z503 : W := mkw 0x0000000008900000 0x0000000001120000 0x100000001ff80004 0x0200000003ff0000

def z504 : W := mkw 0x0314380256048510 0x806287004ac090a2 0xd70438007e00879e 0x7ae087000fc010f3

def z505 : W := mkw 0x15ea3b681bfa4787 0x02bd476d037f48f0 0xfffb3ff81fff6787 0xffff67ff03ffecf0

def z506 : W := mkw 0x080116c591212666 0x410022d8b22424cc 0xe0c037c791e00666 0xbc1806f8f23c00cc

def z507 : W := mkw 0x02140002c4058050 0x804280005880b00a 0x9f1c0007fe07807d 0x73e38000ffc0f00f

def z508 : W := mkw 0x0314280244048000 0x0062850048809000 0xdf1c3807fe078007 0x7be38700ffc0f000

def z509 : W := mkw 0x03143802d6058550 0x806287005ac0b0aa 0xd71838039e070786 0x7ae3070073c0e0f0

def z510 : W := mkw 0x0001461c21082aac 0x200028c384210555 0x3024ce3c60189ffa 0x460499c78c0313ff

def z511 : W := mkw 0x27ffefbf6ddefaac 0x24fffdf7edbbdf55 0xffffffffffffffff 0xffffffffffffffff

def z512 : W := mkw 0x100012481bb82faf 0x22000249037705f5 0x180000001ff8fffc 0x0300000003ff1fff

def z513 : W := mkw 0x0001461c21082aac 0x200028c384210555 0x3823c6380118fffc 0x870478c700231fff

def z514 : W := mkw 0x0000000000000000 0x0000000000000000 0xe0c037c000000002 0xbc1806f800000000

def z515 : W := mkw 0x0000100090010440 0x0000020012002088 0x4018300390070000 0x280306007200e000

def z516 : W := mkw 0x004b060401426224 0x000960c080284c44 0xa8db060411e76667 0xb51b60c0823ceccc

def z517 : W := mkw 0x37febbeb5bb80787 0x06ffd77d6b7700f0 0xf7f83ffb9ff80786 0xfeff07ff73ff00f0

def z518 : W := mkw 0x11003b6813280787 0x0220076d026500f0 0xe0c03ff811e00786 0xbc1807ff023c00f0

def z519 : W := mkw 0x084b16c59df7f666 0x410962d8b3befecc 0xf8db37c79ffffe67 0xbf1b66f8f3ffffcc

def z520 : W := mkw 0x0a5f96c59567f666 0x414bf2d8b2acfecc 0xe8dff7c791e7fe67 0xbd1bfef8f23cffcc

def z521 : W := mkw 0x0314280240000000 0x0062850048000000 0x4718300380000000 0x28e3060070000000

def z522 : W := mkw 0x084b4495a0436868 0x61096892b4086d0d 0x081fc007e007f879 0x0103f800fc00ff0f

def z523 : W := mkw 0x0000124011200606 0x00000248022400c0 0x600037c000000602 0x0c0006f8000000c0

def z524 : W := mkw 0x2ffeb9e3d0634442 0x45ffd73c7a0c6888 0x47d831c390e70000 0x28fb0638721ce000

def z525 : W := mkw 0x0001160491012664 0x000022c0922024cc 0xe81b360791076667 0xbd0366c0f220eccc

def z526 : W := mkw 0x0001040400002020 0x0000208080000404 0x0803000400006061 0x0100600080000c0c

def z527 : W := mkw 0x235fedb760000000 0x046bfdb6ec000000 0x601fffffe0000003 0x0c03fffffc000000

def z528 : W := mkw 0x04a000000cd6d000 0x00940000019ada00 0x9fe000001ffff804 0xf3fc000003ffff00

def z529 : W := mkw 0x1deb7ffdbbfb6fef 0x63bd6fffb77f6dfd 0xffffffffffffffff 0xffffffffffffffff

def z530 : W := mkw 0x004b461c214a6aac 0x200968c384294d55 0xb8ffce3c71ffffff 0xf71ff9c78e3fffff

def z531 : W := mkw 0x0001461c2ddefaac 0x200028c385bbdf55 0xb827ce3c7fffffff 0xd704f9c78fffffff

def z532 : W := mkw 0x084a10c190634442 0x41094218320c6888 0xc8d831c790e70667 0x391b0638f21ce0cc

def z533 : W := mkw 0x04ea800008d25000 0x009d5000011a4a00 0x88fbc00011ff7805 0xb11f7800023fef00

def z534 : W := mkw 0x06fe90009ed7d550 0x80dfd20013dafaaa 0x9fffc0001ffffffd 0xf3fff80003ffffff

def z535 : W := mkw 0x06ff848500000000 0x00dff090a0000000 0xe7fff7c780000003 0xfcfffef8f0000000

def z536 : W := mkw 0x0000020801080284 0x0000004100210050 0x20000e3800000782 0x040001c7000000f0

def z537 : W := mkw 0x02141002d6058550 0x804282005ac0b0aa 0x181c0007fe0787fd 0x03038000ffc0f0ff

def z538 : W := mkw 0x0000000080010040 0x0000000010002008 0x0818000780070061 0x01030000f000e00c

def z539 : W := mkw 0x24ebc7bd21082aac 0x249d78f7a4210555 0xb8e7cffc6118ffff 0xd71cf9ff8c231fff

def z540 : W := mkw 0x01003802d2010550 0x802007005a4020aa 0xd7003807fe0007fe 0x7ae00700ffc000ff

def z541 : W := mkw 0x06fe800000424000 0x00dfd00000084800 0x8fffc00011e76005 0xf1fff800023cec00

def z542 : W := mkw 0x06fe80000cd6d000 0x00dfd000019ada00 0x17e7c0000ff8f800 0xc2fcf80001ff1f00

def z543 : W := mkw 0x07b43802de958550 0x80f687005bd2b0aa 0xdffc3807ffff87ff 0xfbff8700fffff0ff

def z544 : W := mkw 0x04ebc61c29da7aac 0x209d78c3853b4f55 0x20e3c63801f87800 0x841c78c7003f0f00

def z545 : W := mkw 0x0000000800080888 0x2000000100010111 0x1000000000189998 0x0200000000031333

def z546 : W := mkw 0x24a0c13020000000 0x0494182604000000 0x0020c03800000000 0x0004180700000000

def z547 : W := mkw 0x2fffeff761626226 0x45fffdfeec2c4c44 0xe7ffffffe1e06003 0xfcfffffffc3c0c00

def z548 : W := mkw 0x2214c01260000000 0x044298024c000000 0x0004c00060000000 0x000098000c000000

def z549 : W := mkw 0x14a1477c29b82aaf 0x229428ef85370555 0x20e3c7f801f87800 0x841c78ff003f0f00

def z550 : W := mkw 0x0001060c01082aac 0x200020c180210555 0xb80306040118ffff 0x970060c080231fff

def z551 : W := mkw 0x0001461c21082aac 0x200028c384210555 0x2023ce3c61187ffa 0x840479c78c230fff

def z552 : W := mkw 0x0ceb96c599f37666 0x419d72d8b33e6ecc 0xe8fbf7c791ff7e67 0xbd1f7ef8f23fefcc

def z553 : W := mkw 0x025e00000446c000 0x004bc0000088d800 0x9fdf00001fe7e005 0xf3fbe00003fcfc00

def z554 : W := mkw 0x04a1461c29982aac 0x209428c385330555 0xbfe7ce3c7ff8ffff 0xf7fcf9c78fff1fff

def z555 : W := mkw 0x06ff86040dd6f224 0x00dff0c081bade44 0xbfffc6041ffffe67 0xf7fff8c083ffffcc

def z556 : W := mkw 0x05a16d3420000000 0x00b42da684000000 0xe7e7fffc60000003 0xfcfcffff8c000000

def z557 : W := mkw 0x0000020001002224 0x0000004000200444 0x0800000001006664 0x0100000000200ccc

def z558 : W := mkw 0x0000100090010440 0x0000020012002088 0x0800000010070664 0x010000000200e0cc

def z559 : W := mkw 0x27ffedb760000000 0x04fffdb6ec000000 0x27e7cff860000000 0xc4fcf9ff0c000000

def z560 : W := mkw 0x03143a0ad70d87d4 0x806287415ae1b0fa 0xff3c3e3fff1f87ff 0xffe787c7ffe3f0ff

def z561 : W := mkw 0x27b5ef3e61082aac 0x24f6bde7cc210555 0xbf27ce3c6118ffff 0xd7e4f9c78c231fff

def z562 : W := mkw 0x100012489fbd87d7 0x8200024913f7b0fa 0x180000001fff87fc 0x0300000003fff0ff

def z563 : W := mkw 0x07fea8024ed6d110 0x80ffd50049dada22 0x9fffc8007ffff99d 0xf3fff9000fffff33

def z564 : W := mkw 0x1100292802080181 0x0220052500410030 0x0000083800000180 0x0000010700000030

def z565 : W := mkw 0x0b153ec7d725a776 0xc162a7d8fae4b4ee 0xff1c3fc7fe0787ff 0x7fe387f8ffc0f0ff

def z566 : W := mkw 0x37ffffff7bb82faf 0x26ffffffef7705f5 0xfffffffffff8ffff 0xffffffffffff1fff

def z567 : W := mkw 0x27feb9a3d6058550 0x84ffd7347ac0b0aa 0x47d831c39e070000 0x28fb063873c0e000

def z568 : W := mkw 0x0a5f84858447f060 0x414bf090b088fe0c 0x081fc0078007f861 0x0103f800f000ff0c

def z569 : W := mkw 0x0000100096058550 0x8000020012c0b0aa 0x980408047e0787ff 0x530081008fc0f0ff

def z570 : W := mkw 0x15a039281a980581 0x02b40725035300b0 0xd72038381e180786 0x7ae4070703c300f0

def z571 : W := mkw 0x03143802d6058550 0x806287005ac0b0aa 0x1f0408007e0787fc 0x43e081000fc0f0ff

def z572 : W := mkw 0x27fffdb7f6058550 0x84ffffb6fec0b0aa 0xe7fffffffe070003 0xfcffffffffc0e000

def z573 : W := mkw 0x14a0136819b80687 0x0294026d033700d0 0xe0e037f811f80606 0xbc1c06ff023f00c0

def z574 : W := mkw 0x0001060401002224 0x000020c080200444 0x2003060001006000 0x840060c000200c00

def z575 : W := mkw 0x2cebc7f521626226 0x459d78fea42c4c44 0x20e3c7f801e06000 0x841c78ff003c0c00

def z576 : W := mkw 0x26ffc4976cd6d000 0x04dff892ed9ada00 0x9fffc007fffff805 0xf3fff800ffffff00

def z577 : W := mkw 0x03143802d2010550 0x806287005a4020aa 0xc71c3807e00007fb 0x78e38700fc0000ff

def z578 : W := mkw 0x0314681a660c8998 0xa0628d034cc19133 0x1724c8386e189998 0x42e499070dc31333

def z579 : W := mkw 0x00001208970daffc 0xa000024112e1b5ff 0x180000001f1ffffc 0x0300000003e3ffff

def z580 : W := mkw 0x000000000cd6d000 0x00000000019ada00 0x9827c0001ffff805 0xd304f80003ffff00

def z581 : W := mkw 0x03157c16f6058550 0x8062af82dec0b0aa 0xff3ffe3ffe0787ff 0xffe7ffc7ffc0f0ff

def z582 : W := mkw 0x27b4e93260000000 0x04f69d264c000000 0xc73cf83fe0000003 0x78e79f07fc000000

def z583 : W := mkw 0x0eff84858cd7f060 0x41dff090b19afe0c 0x9fffc0079ffff865 0xf3fff800f3ffff0c

def z584 : W := mkw 0x06fe80000cd6d000 0x00dfd000019ada00 0x1fd800001ffff804 0x23fb000003ffff00

def z585 : W := mkw 0x04a0000000000000 0x0094000000000000 0x87e0000000000000 0xf0fc000000000000

def z586 : W := mkw 0x26ffc5b520000000 0x04dff8b6a4000000 0xa7ffc7f800000001 0xf4fff8ff00000000

def z587 : W := mkw 0x07b4b802de959550 0x80f697005bd2b2aa 0xdf3cf807fe1f9fff 0x7be79f00ffc3f3ff

def z588 : W := mkw 0x24ea81a100000000 0x049d503420000000 0x00c001c000000000 0x0018003800000000

def z589 : W := mkw 0x0000401820080888 0x2000080304010111 0x9824c83c60189fff 0x530499078c0313ff

def z590 : W := mkw 0x000002080ddefaac 0x2000004101bbdf55 0x180000001ffffffc 0x0300000003ffffff

def z591 : W := mkw 0x04a0020809980284 0x0094004101330050 0xb7e00e381ff80786 0xf6fc01c703ff00f0

def z592 : W := mkw 0x0000124811280686 0x00000249022500d0 0xf0e03ff811f80786 0xfe1c07ff023f00f0

def z593 : W := mkw 0x080116c591636666 0x410022d8b22c6ccc 0x680037c791e76666 0x0d0006f8f23ceccc

def z594 : W := mkw 0x17b43962deb58553 0x82f6872c5bd6b0aa 0xdfdc39c7fee787ff 0x7bfb8738ffdcf0ff

def z595 : W := mkw 0x084b16c591636666 0x410962d8b22c6ccc 0x60c337c781e06662 0x8c1866f8f03c0ccc

def z596 : W := mkw 0x07b4a8024e949110 0x80f6950049d29222 0x1724c8006e189998 0x42e499000dc31333

def z597 : W := mkw 0x03156e1e670cabbc 0xa062adc3cce19577 0xbf27ce3c6f18ffff 0xd7e4f9c78de31fff

def z598 : W := mkw 0x004b068501002224 0x000960d0a0200444 0xe8db37c781006667 0xbd1b66f8f0200ccc

def z599 : W := mkw 0x0000000084058050 0x800000001080b00a 0x0800000000078078 0x010000000000f00f

def z600 : W := mkw 0x035f3c87d6058550 0x806be790fac0b0aa 0xffdf3fc7fe0787ff 0xfffbe7f8ffc0f0ff

def z601 : W := mkw 0x11003b6813280787 0x0220076d026500f0 0xf0203ff801180786 0xde0407ff002300f0

def z602 : W := mkw 0x06b480000c949000 0x00d6900001929200 0x070000000e000000 0x00e0000001c00000

def z603 : W := mkw 0x27ffedbf60080888 0x24fffdb7ec010111 0xf7ffffffe018999b 0xfefffffffc031333

def z604 : W := mkw 0x000000000446d000 0x000000000088da00 0x080000000007f800 0x010000000000ff00

def z605 : W := mkw 0x0001441420000000 0x0000288284000000 0x0007c00460000001 0x0000f8008c000000

def z606 : W := mkw 0x2fffbfe7d1636666 0x45fff7fcfa2c6ccc 0xefdb37c791e76667 0xbdfb66f8f23ceccc

def z607 : W := mkw 0x094b3ec593636766 0x412967d8b26c6cec 0xffdb3fc79fe767e7 0xfffb67f8f3fcecfc

def z608 : W := mkw 0x0001441c20080888 0x2000288384010111 0xb027ce3c6018999b 0xd604f9c78c031333

def z609 : W := mkw 0x07b43922d6058550 0x80f687245ac0b0aa 0xfffc3ffffe0787ff 0xffff87ffffc0f0ff

def z610 : W := mkw 0x1000024809b80287 0x0200004901370050 0x0000000001f80000 0x00000000003f0000

def z611 : W := mkw 0x13143a4adfbd87d7 0x826287495bf7b0fa 0xdf1c3807ffff87ff 0x7be38700fffff0ff

def z612 : W := mkw 0x0000000000000000 0x0000000000000000 0x9804000000008005 0x5300800000001000

def z613 : W := mkw 0x27b4a92240000000 0x04f6952448000000 0x0700000000000000 0x00e0000000000000

def z614 : W := mkw 0x0000401020000000 0x0000080204000000 0x0024c83860000000 0x400499070c000000

def z615 : W := mkw 0x0214000004048000 0x0042800000809000 0x081c000000078001 0x010380000000f000

def z616 : W := mkw 0x000000000c949000 0x0000000001929200 0x100000000e189800 0x0200000001c31300

def z617 : W := mkw 0x004b469d21082aac 0x200968d3a4210555 0xf8ffffffe118ffff 0xff1ffffffc231fff

def z618 : W := mkw 0x11003b6813280787 0x0220076d026500f0 0xf7003ff81e000786 0x7ee007ff03c000f0

def z619 : W := mkw 0x2fffedb7e0436060 0x45fffdb6fc086c0c 0xefffffffe0076063 0xfdfffffffc00ec0c

def z620 : W := mkw 0x0100280000000000 0x0020050000000000 0xc700380000000002 0x78e0070000000000

def z621 : W := mkw 0x37ffefff69b80287 0x06fffdffed370050 0xe7ffffffe1f80003 0xfcfffffffc3f0000

def z622 : W := mkw 0x06fe80000446d000 0x00dfd0000088da00 0x8fffc0000007f801 0xf1fff8000000ff00

def z623 : W := mkw 0x0100380012000500 0x00200700024000a0 0xdf0438047e0087ff 0x7be087008fc010ff

def z624 : W := mkw 0x084b148590436460 0x41096290b2086c8c 0xc81b300790076667 0x39036600f200eccc

def z625 : W := mkw 0x03143802d6058550 0x806287005ac0b0aa 0x57043807ee0087fa 0x4ae08700fdc010ff

def z626 : W := mkw 0x0001461421002224 0x000028c284200444 0xa827ce3c61006667 0xd504f9c78c200ccc

def z627 : W := mkw 0x27fee93260000000 0x04ffdd264c000000 0x87ffc83860000001 0xf0fff9070c000000

def z628 : W := mkw 0x0001561cb70daffc 0xa0002ac396e1b5ff 0xb827ce3c7f1fffff 0xd704f9c78fe3ffff

def z629 : W := mkw 0x23157db7f6058550 0x8462afb6fec0b0aa 0xff1c3ffffe0787ff 0x7fe387ffffc0f0ff

def z630 : W := mkw 0x37b4e93a6a980181 0x06f69d274d530030 0x1724c8386e180180 0x42e499070dc30030

def z631 : W := mkw 0x2a5fd6d7f1636666 0x454bfadafe2c6ccc 0xe8dff7c7f1e76667 0xbd1bfef8fe3ceccc

def z632 : W := mkw 0x27fea9a340000000 0x04ffd53468000000 0xc7dc39c7e0000003 0x78fb8738fc000000

def z633 : W := mkw 0x0a5f16c59567e666 0x414be2d8b2acfccc 0xffdf37c79fe7e667 0xfffbe6f8f3fcfccc

def z634 : W := mkw 0x0001441420002828 0x2000288284000505 0x9827c0046118f87d 0xd304f8008c231f0f

def z635 : W := mkw 0x084b048500426020 0x41096090a0084c04 0x0003000000006000 0x0000600000000c00

def z636 : W := mkw 0x025fc4142446f828 0x204bf8828488df05 0x081fc0046007f879 0x0103f8008c00ff0f

def z637 : W := mkw 0x07feb802ded7d550 0x80ffd7005bdafaaa 0xdfdc3807fee787ff 0x7bfb8700ffdcf0ff

def z638 : W := mkw 0x1100396012200503 0x0220072c024400a0 0x400031c000000000 0x0800063800000000

def z639 : W := mkw 0x100012481ffed787 0x0200024903ffdaf0 0x180000001fffff84 0x0300000003fffff0

def z640 : W := mkw 0x025fc61c254efaac 0x204bf8c384a9df55 0xb83fce3c611fffff 0xd707f9c78c23ffff

def z641 : W := mkw 0x0000421821080a8c 0x2000084304210151 0xb024ce3861189f9e 0xd60499c70c2313f3

def z642 : W := mkw 0x0b5f3ec7d767e776 0xc16be7d8faecfcee 0xefdb37c79fe76667 0xbdfb66f8f3fceccc

def z643 : W := mkw 0x0215461c250caaac 0x2042a8c384a19555 0xbf3fce3c7f1fffff 0xf7e7f9c78fe3ffff

def z644 : W := mkw 0x235fec9760000000 0x046bfd92ec000000 0xc71ff807e0000003 0x78e3ff00fc000000

def z645 : W := mkw 0x0100380012000500 0x00200700024000a0 0x4000380000000782 0x08000700000000f0

def z646 : W := mkw 0x15a039601ab00503 0x02b4072c035600a0 0xd7c039c01ee00786 0x7af8073803dc00f0

def z647 : W := mkw 0x04ea800008d25000 0x009d5000011a4a00 0x98e7c00001f8f805 0xd31cf800003f1f00

def z648 : W := mkw 0x0b5f3ec7d1636666 0x416be7d8fa2c6ccc 0xefdf3fc7f1e76667 0xfdfbe7f8fe3ceccc

def z649 : W := mkw 0x34ebc7fd29b80287 0x069d78ffa5370050 0x20e3c7f801f80000 0x841c78ff003f0000

def z650 : W := mkw 0x0000000000000000 0x0000000000000000 0x8004080460000003 0x500081008c000000

def z651 : W := mkw 0x0000100090010440 0x0000020012002088 0x4000300780000662 0x08000600f00000cc

def z652 : W := mkw 0x27ffefbf61082aac 0x24fffdf7ec210555 0xe7ffffffe1187803 0xfcfffffffc230f00

def z653 : W := mkw 0x27fffdb7f2010550 0x84ffffb6fe4020aa 0xe7ffffffe00007fb 0xfcfffffffc0000ff

def z654 : W := mkw 0x035eb802d647d550 0x806bd7005ac8faaa 0xdf1ff807fe07ffff 0x7be3ff00ffc0ffff

def z655 : W := mkw 0x0000000000000000 0x0000000000000000 0x8803000001006005 0x9100600000200c00

def z656 : W := mkw 0x02140002c4058050 0x804280005880b00a 0x981c0807e00787ff 0x53038100fc00f0ff

def z657 : W := mkw 0x0100280242000110 0x8020050048400022 0x0000080060000198 0x000001000c000033

def z658 : W := mkw 0x0000020801082aac 0x2000004100210555 0x0000000001187800 0x0000000000230f00

def z659 : W := mkw 0x04a0000008900000 0x0094000001120000 0x00e0000001f80000 0x801c0000003f0000

def z660 : W := mkw 0x2ffffff7f767e776 0xc5fffffefeecfcee 0xffffffffffe7e7ff 0xfffffffffffcfcff

def z661 : W := mkw 0x2ffffff7f1212666 0x45fffffefe2424cc 0xe7ffffffe0000663 0xfcfffffffc0000cc

def z662 : W := mkw 0x27fea9a340000000 0x04ffd53468000000 0xc7fff1c380000001 0xf8fffe3870000000

def z663 : W := mkw 0x0001441420002828 0x2000288284000505 0x0003c00000007800 0x0000780000000f00

def z664 : W := mkw 0x0eff96c591636666 0x41dff2d8b22c6ccc 0xeffff7c791e76667 0xfdfffef8f23ceccc

def z665 : W := mkw 0x1000036801280287 0x0200006d00250050 0x200007f800000000 0x040000ff00000000

def z666 : W := mkw 0x0214000240000000 0x0042800048000000 0x001c0007e0000001 0x00038000fc000000

def z667 : W := mkw 0x0000000000000000 0x0000000000000000 0x80c0000011e00004 0xb0180000023c0000

def z668 : W := mkw 0x13143b6ad72d87d7 0x8262876d5ae5b0fa 0xff1c3ffffe0787ff 0x7fe387ffffc0f0ff

def z669 : W := mkw 0x0000020801080284 0x0000004100210050 0xb827ce380118ff87 0xd704f9c700231ff0

def z670 : W := mkw 0x0000000000002828 0x2000000000000505 0x080000000000f878 0x0100000000001f0f

def z671 : W := mkw 0x225fc497e4058050 0x844bf892fc80b00a 0x081fc007e0078079 0x0103f800fc00f00f

def z672 : W := mkw 0x19013fed932927e7 0x432027fdb26524fc 0x60003fff800007e2 0x0c0007fff00000fc

def z673 : W := mkw 0x03143802d6058550 0x806287005ac0b0aa 0x4f1c3007fe078079 0x29e38600ffc0f00f

def z674 : W := mkw 0x0000124011200606 0x00000248022400c0 0x0000000011e00604 0x00000000023c00c0

def z675 : W := mkw 0x06ff84850cd6d000 0x00dff090a19ada00 0xfffff7c79ffff807 0xfffffef8f3ffff00

def z676 : W := mkw 0x04a0124019b00606 0x00940248033600c0 0xf7e037c01ff80606 0xfefc06f803ff00c0

def z677 : W := mkw 0x0000100012000500 0x00000200024000a0 0x100000001e000784 0x0200000003c000f0

def z678 : W := mkw 0x004a124011624606 0x00094248022c48c0 0xe8db37c011e76607 0xbd1b66f8023cecc0

def z679 : W := mkw 0x15a17f7c3bb80787 0x02b42fef877700f0 0xf7e7fffc7ff80787 0xfefcffff8fff00f0

def z680 : W := mkw 0x0001461c21082aac 0x200028c384210555 0xb827c6380118f805 0xd704f8c700231f00

def z681 : W := mkw 0x09013ec7d3212776 0xc12027d8fa6424ee 0x60003fc7e00007fa 0x0c0007f8fc0000ff

def z682 : W := mkw 0x0001461c21082aac 0x200028c384210555 0xb8040e3c600087ff 0x570081c78c0010ff

def z683 : W := mkw 0x0100280002000100 0x0020050000400020 0x170008000e000180 0x42e0010001c00030

def z684 : W := mkw 0x06b480000c949000 0x00d6900001929200 0x97e4c0001ff89804 0xf2fc980003ff1300

def z685 : W := mkw 0x15a13f6c1bb827a7 0x02b427ed837704f4 0xffe33ffc1ff867e7 0xfffc67ff83ff0cfc

def z686 : W := mkw 0x084b068581436264 0x410960d0b0286c4c 0xa81b060781076667 0x950360c0f020eccc

def z687 : W := mkw 0x14a0016008b00003 0x0294002c01160000 0x00c001c000e00000 0x00180038001c0000

def z688 : W := mkw 0x37b4fb7a7bb80787 0x06f69f6f4f7700f0 0xf7e4fff87ff80786 0xfefc9fff0fff00f0

def z689 : W := mkw 0x0800000080436060 0x4100000010086c0c 0x0800000000076060 0x010000000000ec0c

def z690 : W := mkw 0x17b4bb681fbc9787 0x02f6976d03f792f0 0xf7e4fff81ff89f86 0xfefc9fff03ff13f0

def z691 : W := mkw 0x06b400000c948000 0x00d6800001929000 0x9ffc00001fff8005 0xf3ff800003fff000

def z692 : W := mkw 0x14a1477c29b82aaf 0x229428ef85370555 0xb8e7cffc61f8ffff 0xd71cf9ff8c3f1fff

def z693 : W := mkw 0x084b048580436060 0x41096090b0086c0c 0x88db000791e76065 0xb11b6000f23cec0c

def z694 : W := mkw 0x06fe800004048000 0x00dfd00000809000 0x9fffc0001e078005 0xf3fff80003c0f000

def z695 : W := mkw 0x24ebc5b520000000 0x049d78b6a4000000 0xa0e7cffc60000003 0xd41cf9ff8c000000

def z696 : W := mkw 0x0000000000000000 0x0000000000000000 0x9020000001180004 0xd204000000230000

def z697 : W := mkw 0x06fe800000000000 0x00dfd00000000000 0x9fffc0000118f805 0xf3fff80000231f00

def z698 : W := mkw 0x0001060401002224 0x000020c080200444 0x2000060400000662 0x040000c0800000cc

def z699 : W := mkw 0x15a03b681bb80787 0x02b4076d037700f0 0x60e03ff801f80782 0x8c1c07ff003f00f0

def z700 : W := mkw 0x084b06c501626226 0x410960d8a02c4c44 0xa8db07c011e76005 0xb51b60f8023cec00

def z701 : W := mkw 0x04ebc61c29da7aac 0x209d78c3853b4f55 0xb8e7ce3c61f8ffff 0xd71cf9c78c3f1fff

def z702 : W := mkw 0x0001461c21082aac 0x200028c384210555 0xa027ce3c61187803 0xd404f9c78c230f00

def z703 : W := mkw 0x0000401820080888 0x2000080304010111 0x0000083860000198 0x000001070c000033

def z704 : W := mkw 0x0000000006048110 0x8000000000c09022 0x100000000e008198 0x0200000001c01033

def z705 : W := mkw 0x27fffdb772000500 0x04ffffb6ee4000a0 0xf7fffffffe000787 0xfeffffffffc000f0

def z706 : W := mkw 0x1dea39e19af34543 0x43bd473c335e68a8 0x47d831c39ee70000 0x28fb063873dce000

def z707 : W := mkw 0x004b449520424000 0x00096892a4084800 0xf8fffffff1fff807 0xff1ffffffe3fff00

def z708 : W := mkw 0x0001469d21082aac 0x200028d3a4210555 0xf827ffffe118ffff 0xdf04fffffc231fff

def z709 : W := mkw 0x084b16c591636666 0x410962d8b22c6ccc 0xf8db37c791e7e7ff 0xbf1b66f8f23cfcff

def z710 : W := mkw 0x214b6db760000000 0x04296db6ec000000 0x60d83fffe0000002 0x2c1b07fffc000000

def z711 : W := mkw 0x084b16c591636666 0x410962d8b22c6ccc 0xf8db3fc791e767e7 0xff1b67f8f23cecfc

def z712 : W := mkw 0x084b14c590634442 0x41096298b20c6888 0xe8db37c791e76007 0xbd1b66f8f23cec00

def z713 : W := mkw 0x27ffedb760000000 0x04fffdb6ec000000 0xe7ffffffe1187803 0xfcfffffffc230f00

def z714 : W := mkw 0x0001449520000000 0x00002892a4000000 0x60003fffe0000002 0x0c0007fffc000000

def z715 : W := mkw 0x084b56ddb16b6eee 0x61096adbb62d6ddd 0xe8fff7fff1fffe7f 0xbd1ffefffe3fffcf

def z716 : W := mkw 0x03157e1ef70daffc 0xa062afc3dee1b5ff 0x673bf63b9f1f7800 0xace77ec773e3ef00

def z717 : W := mkw 0x084b16c591636666 0x410962d8b22c6ccc 0xe8fff7c791e76667 0xfd1ffef8f23ceccc

def z718 : W := mkw 0x27ffedb766048110 0x84fffdb6ecc09022 0xe7ffffffee000003 0xfcfffffffdc00000

def z719 : W := mkw 0x084a10c190634442 0x41094218320c6888 0x48d831c390e70664 0x291b0638721ce0cc

def z720 : W := mkw 0x214b6db760424000 0x04296db6ec084800 0xe8db3ffff1e76007 0xbd1b67fffe3cec00

def z721 : W := mkw 0x0800124891292eee 0x61000249122525dd 0x180000000118fffc 0x0300000000231fff

def z722 : W := mkw 0x135ebb68176ed787 0x026bd76d02eddaf0 0x681ffff80007ff83 0x0d03ffff0000fff0

def z723 : W := mkw 0x27ffedb760002828 0x24fffdb6ec000505 0xffffffffe118f87f 0xfffffffffc231f0f

def z724 : W := mkw 0x08001248916b6eee 0x61000249122d6ddd 0x0800000011e767fc 0x01000000023cecff

def z725 : W := mkw 0x084b16c591636666 0x410962d8b22c6ccc 0xe8df3fc7f1e76667 0xfd1be7f8fe3ceccc

def z726 : W := mkw 0x084a1248916b6eee 0x61094249122d6ddd 0x98ffc00011fffffd 0xf31ff800023fffff

def z727 : W := mkw 0x084b56d5b1636666 0x41096adab62c6ccc 0xf8fffffff1fffe67 0xff1ffffffe3fffcc

def z728 : W := mkw 0x03143802d6058550 0x806287005ac0b0aa 0xdf3c3807ff1f87ff 0xfbe78700ffe3f0ff

def z729 : W := mkw 0x084a10c190634442 0x41094218320c6888 0x40db31c391e76000 0xa81b6638723cec00

def z730 : W := mkw 0x37b4e93a6e9c9181 0x06f69d274dd39230 0x1724c8386e189980 0x42e499070dc31330

def z731 : W := mkw 0x05a03b6019b00606 0x00b4076c033600c0 0xf7e03ff81ff80606 0xfefc07ff03ff00c0

def z732 : W := mkw 0x27ffedb764048000 0x04fffdb6ec809000 0xe7fffffffe070003 0xfcffffffffc0e000

def z733 : W := mkw 0x15a03b689bb907c7 0x02b4076d137720f8 0xfffc3fffffff87ff 0xffff87fffffff0ff

def z734 : W := mkw 0x004b16c591210646 0x000962d8b22420c8 0xe8db37c791e70667 0xbd1b66f8f23ce0cc

def z735 : W := mkw 0x24ebc7bd29da7aac 0x249d78f7a53b4f55 0x20e3c7f801f87800 0x841c78ff003f0f00

def z736 : W := mkw 0x27b4e93a6c9c9888 0x24f69d274d939311 0x1724c8386e189998 0x42e499070dc31333

def z737 : W := mkw 0x07b4292240000000 0x00f6852448000000 0xe7f83ffb80000002 0xfcff07ff70000000

def z738 : W := mkw 0x27feabab41082aac 0x24ffd57568210555 0x5fd831c38118fffc 0x2bfb063870231fff

def z739 : W := mkw 0x0b5f2ec74766e336 0xc16be5d8e8ecdc66 0x37c70fc06fe0e198 0xc6f8e1f80dfc1c33

def z740 : W := mkw 0x0eb596c59db5b666 0x41d6b2d8b3b6b6cc 0x7724f7c78e189e62 0x4ee49ef8f1c313cc

def z741 : W := mkw 0x184b16cd936b67e7 0x430962d9b26d6cfc 0xe8db37c791e767e7 0xbd1b66f8f23cecfc

def z742 : W := mkw 0x1deb2dad8adb61e1 0x43bd65b5b15b6c3c 0x1f3b083f8e1f61e1 0x43e76107f1c3ec3c

def z743 : W := mkw 0x03142802c6058150 0x8062850058c0b02a 0x9f1c0807ee0787ff 0x53e38100fdc0f0ff

def z744 : W := mkw 0x06b480000cd6d000 0x00d69000019ada00 0x9f27c0001ffff805 0xd3e4f80003ffff00

def z745 : W := mkw 0x15a03b681bb82faf 0x22b4076d037705f5 0xf7e03ff81ff87f86 0xfefc07ff03ff0ff0

def z746 : W := mkw 0x15a03b6adbb907d7 0x82b4076d5b7720fa 0xffe43ffffff887ff 0xfffc87ffffff10ff

def z747 : W := mkw 0x15a03b689bb907c7 0x02b4076d137720f8 0xffe03ff81fff07e6 0xfffc07ff03ffe0fc

def z748 : W := mkw 0x06fe80024cd6d000 0x00dfd000499ada00 0x9fffc007fffff805 0xf3fff800ffffff00

def z749 : W := mkw 0x06ffc61c2ddefaac 0x20dff8c385bbdf55 0x27d80e3c7ee707fa 0x24fb01c78fdce0ff

def z750 : W := mkw 0x27ffedb76c949000 0x04fffdb6ed929200 0xe7ffffffee000003 0xfcfffffffdc00000

def z751 : W := mkw 0x084b56ddb16b6eee 0x61096adbb62d6ddd 0xf8fff7ff91fffe67 0xff1ffefff23fffcc

def z752 : W := mkw 0x27fee9b360000000 0x04ffdd366c000000 0xe7fcfffbe0000002 0xfcff9fff7c000000

def z753 : W := mkw 0x2fffedb760426020 0x45fffdb6ec084c04 0xe7ffffffe0006003 0xfcfffffffc000c00

def z754 : W := mkw 0x084a10c190634442 0x41094218320c6888 0xc0d831c391e70004 0xb81b0638723ce000

def z755 : W := mkw 0x06fe80000cd6d000 0x00dfd000019ada00 0x8ffbc0001fff7805 0xb1ff780003ffef00

def z756 : W := mkw 0x225fc4976446f828 0x244bf892ec88df05 0x081fc007e007f879 0x0103f800fc00ff0f

def z757 : W := mkw 0x27ffedb76446f828 0x24fffdb6ec88df05 0xefffffffe007f87b 0xfdfffffffc00ff0f

def z758 : W := mkw 0x07b429224c948000 0x00f6852449929000 0xfffc3fffffff8007 0xffff87fffffff000

def z759 : W := mkw 0x214b6db760000000 0x04296db6ec000000 0x601b3fffe0000003 0x0c0367fffc000000

def z760 : W := mkw 0x06ffc49520000000 0x00dff892a4000000 0xe7ffffffe0000003 0xfcfffffffc000000

def z761 : W := mkw 0x15a03b681bb80787 0x02b4076d037700f0 0x77e03ff80ff80782 0xcefc07ff01ff00f0

def z762 : W := mkw 0x27ffedb760000000 0x04fffdb6ec000000 0x67fff7ffe0000001 0xacfffefffc000000

def z763 : W := mkw 0x08001248916b66e6 0x41000249122d6cdc 0x1800000011ff67e4 0x03000000023fecfc

def z764 : W := mkw 0x27ffedb760424000 0x04fffdb6ec084800 0xefffffffe0076003 0xfdfffffffc00ec00

def z765 : W := mkw 0x084a12c191636666 0x41094258322c6ccc 0xc8db31c391e76665 0xb91b6638723ceccc

def z766 : W := mkw 0x0efe92489dfffeee 0x61dfd24913bfffdd 0x9fffc0001ffffffd 0xf3fff80003ffffff

def z767 : W := mkw 0x27b5edb760000000 0x04f6bdb6ec000000 0x67003fffe0000002 0x0ce007fffc000000

def z768 : W := mkw 0x05a039201a900500 0x00b40724035200a0 0xf7e03ff81ff80786 0xfefc07ff03ff00f0

def z769 : W := mkw 0x100012489bb907c7 0x02000249137720f8 0x180000001fff07e4 0x0300000003ffe0fc

def z770 : W := mkw 0x0001461c21082aac 0x200028c384210555 0xb8e7ce3c71f8ffff 0xf71cf9c78e3f1fff

def z771 : W := mkw 0x27ffedb76c948000 0x04fffdb6ed929000 0xffffffffffff8007 0xfffffffffffff000

def z772 : W := mkw 0x025e80000cd6d000 0x004bd000019ada00 0x9f1fc0001ffff805 0x73e3f80003ffff00

def z773 : W := mkw 0x084b16cd916b6eee 0x610962d9b22d6ddd 0xf8fff7c791ffffff 0xff1ffef8f23fffff

def z774 : W := mkw 0x0800124891292eee 0x61000249122525dd 0x00000000000007f8 0x00000000000000ff

def z775 : W := mkw 0x27b5edb76c949000 0x04f6bdb6ed929200 0x7724ffffee189802 0x4ee49ffffdc31300

def z776 : W := mkw 0x27ffedb760000000 0x04fffdb6ec000000 0xffffffffe0008007 0xfffffffffc001000

def z777 : W := mkw 0x07ff2da740000000 0x00ffe5b4e8000000 0xe7ff3fffe0000003 0xfcffe7fffc000000

def z778 : W := mkw 0x27ffedb760000000 0x04fffdb6ec000000 0xe7fffffff1e00007 0xfcfffffffe3c0000

def z779 : W := mkw 0x004b148590434440 0x00096290b2086888 0xe8db37c791e76667 0xbd1b66f8f23ceccc

def z780 : W := mkw 0x180012489bfb47c7 0x43000249137f68f8 0x100000001fff0784 0x0200000003ffe0f0

def z781 : W := mkw 0x27ffedb760002828 0x24fffdb6ec000505 0xffffffffe000ffff 0xfffffffffc001fff

def z782 : W := mkw 0x084b16cd916b6eee 0x610962d9b22d6ddd 0xf8df3fc7f1ffffff 0xff1be7f8fe3fffff

def z783 : W := mkw 0x0001164491212666 0x000022c8922424cc 0xe8db37c791e76667 0xbd1b66f8f23ceccc

def z784 : W := mkw 0x23156db760000000 0x0462adb6ec000000 0x67043fffe0000002 0x4ce087fffc000000

def z785 : W := mkw 0x27ffedb760000000 0x04fffdb6ec000000 0x60ffffffe0000003 0x8c1ffffffc000000

def z786 : W := mkw 0x084a10c190634442 0x41094218320c6888 0x48d831c790e70061 0x291b0638f21ce00c

def z787 : W := mkw 0x035f6c9760000000 0x006bed92ec000000 0xe7ffffffe0000003 0xfcfffffffc000000

def z788 : W := mkw 0x27ffedb76cd6d000 0x04fffdb6ed9ada00 0xefffffffe1fff803 0xfdfffffffc3fff00

def z789 : W := mkw 0x03143802d6058550 0x806287005ac0b0aa 0xdfdc3807ffe787ff 0xfbfb8700fffcf0ff

def z790 : W := mkw 0x14a013681bb80787 0x0294026d037700f0 0xb7e007f81ff80784 0xf6fc00ff03ff00f0

def z791 : W := mkw 0x21016db760000000 0x04202db6ec000000 0x600037fb80000000 0x0c0006ff70000000

def z792 : W := mkw 0x15a03b681bb80787 0x02b4076d037700f0 0xf7e037f81ff80004 0xfefc06ff03ff0000

def z793 : W := mkw 0x214b6db760000000 0x04296db6ec000000 0xe0ffffffe0000003 0xfc1ffffffc000000

def z794 : W := mkw 0x27ffedb76cd6d000 0x04fffdb6ed9ada00 0xf7ffffffeff8f803 0xfefffffffdff1f00

def z795 : W := mkw 0x2fb4fb72f1636666 0x45f69f6e5e2c6ccc 0x0f24c83871e76664 0x41e499070e3ceccc

def z796 : W := mkw 0x325fd6df7bb80787 0x064bfadbef7700f0 0x101fc007fff80785 0x0203f800ffff00f0

def z797 : W := mkw 0x004b16c511624606 0x000962d8a22c48c0 0xe8db37c791e76607 0xbd1b66f8f23cecc0

def z798 : W := mkw 0x03143922d6058550 0x806287245ac0b0aa 0xff1c3ffffe0787ff 0x7fe387ffffc0f0ff

def z799 : W := mkw 0x05eb2da508d24000 0x00bd65b4a11a4800 0xfffb3fff9fff6007 0xffff67fff3ffec00

def z800 : W := mkw 0x23156db760000000 0x0462adb6ec000000 0x601c3fffe0000003 0x0c0387fffc000000

def z801 : W := mkw 0x25a16db760000000 0x04b42db6ec000000 0x67203fffe0000002 0x4ce407fffc000000

def z802 : W := mkw 0x06fe80000cd6d000 0x00dfd000019ada00 0x9fffc0001ffffffd 0xf3fff80003ffffff

def z803 : W := mkw 0x25ebedb760000000 0x04bd7db6ec000000 0xe7e3ffffe0000002 0xfcfc7ffffc000000

def z804 : W := mkw 0x05a0292000000000 0x00b4052400000000 0xe7f83fff80000003 0xfcff07fff0000000

def z805 : W := mkw 0x235fedb760000000 0x046bfdb6ec000000 0xe0dfffffe0000003 0xbc1bfffffc000000

def z806 : W := mkw 0x07ffada50cd6d000 0x00fff5b4a19ada00 0xffffffff9ffff807 0xfffffffff3ffff00

def z807 : W := mkw 0x06fe80000cd6d000 0x00dfd000019ada00 0x9fffc8047ffff807 0xf3fff9008fffff00

def z808 : W := mkw 0x084b54d5b0634442 0x41096a9ab60c6888 0xe0fffffff0e70003 0xfc1ffffffe1ce000

def z809 : W := mkw 0x004a008100424000 0x0009401020084800 0xc8db31c391e76005 0xb91b6638723cec00

def z810 : W := mkw 0x084b16c591636666 0x410962d8b22c6ccc 0x60d837c390e70000 0x2c1b06f8721ce000

def z811 : W := mkw 0x2a5fc497e447f060 0x454bf892fc88fe0c 0x081fc007e007f861 0x0103f800fc00ff0c

def z812 : W := mkw 0x084a10c190634442 0x41094218320c6888 0xc0d831c390e70606 0x381b0638721ce0c0

def z813 : W := mkw 0x084a12c191636666 0x41094258322c6ccc 0x40d831c391e76000 0x281b0638723cec00

def z814 : W := mkw 0x084b16cd916b6eee 0x610962d9b22d6ddd 0xe8db37c791e767ff 0xbd1b66f8f23cecff

def z815 : W := mkw 0x27b4e9326c949000 0x04f69d264d929200 0x0724c8386e000000 0x40e499070dc00000

def z816 : W := mkw 0x235fedb760000000 0x046bfdb6ec000000 0x60183fffe0000002 0x0c0307fffc000000

def z817 : W := mkw 0x27b56db760000000 0x04f6adb6ec000000 0xe7fc3fffe0000003 0xfcff87fffc000000

def z818 : W := mkw 0x0001461c21082aac 0x200028c384210555 0xf83ffe3fe118ffff 0xff07ffc7fc231fff

def z819 : W := mkw 0x180012489bfb6fef 0x63000249137f6dfd 0x180000001ffffffc 0x0300000003ffffff

def z820 : W := mkw 0x05eb6db520000000 0x00bd6db6a4000000 0xe7ffffffe0000003 0xfcfffffffc000000

def z821 : W := mkw 0x27ffedb76e949110 0x84fffdb6edd29222 0xf7ffffffee18999b 0xfefffffffdc31333

def z822 : W := mkw 0x100012489bb907d7 0x82000249137720fa 0x100000001ff807fc 0x0200000003ff00ff

def z823 : W := mkw 0x25a029a340000000 0x04b4053468000000 0xe7e03ffb80000002 0xfcfc07ff70000000

def z824 : W := mkw 0x0cebc6dd29fa7aae 0x619d78dba53f4f55 0x20e3c7f801f87800 0x841c78ff003f0f00

def z825 : W := mkw 0x05a02b2809980284 0x00b4056501330050 0xf7e03ff81ff80786 0xfefc07ff03ff00f0

def z826 : W := mkw 0x21016db76cd6d000 0x04202db6ed9ada00 0x78003ffffffff806 0x0f0007ffffffff00

def z827 : W := mkw 0x02141002d6058550 0x804282005ac0b0aa 0x9f1c0007fe0787fd 0x73e38000ffc0f0ff

def z828 : W := mkw 0x25ebedb760000000 0x04bd7db6ec000000 0xe0fbffffe0000003 0xbc1f7ffffc000000

def z829 : W := mkw 0x19017ffdb3292fef 0x63202fffb66525fd 0x60003fffe00007fa 0x0c0007fffc0000ff

def z830 : W := mkw 0x15a02b680bb80387 0x02b4056d01770070 0xf7e03ff80ff80182 0xfefc07ff01ff0030

def z831 : W := mkw 0x24ebc5b520000000 0x049d78b6a4000000 0x60e3f7ff80000002 0x8c1c7efff0000000

def z832 : W := mkw 0x084b16c591636666 0x410962d8b22c6ccc 0x68d837c791e76666 0x2d1b06f8f23ceccc

def z833 : W := mkw 0x2a5fc497e447e070 0xc54bf892fc88fc0e 0x081fc007e007e079 0x0103f800fc00fc0f

def z834 : W := mkw 0x01003802d2010550 0x802007005a4020aa 0xdf183807fe0707ff 0x7be30700ffc0e0ff

def z835 : W := mkw 0x084b56ddb16b6eee 0x61096adbb62d6ddd 0xe8dffffff1e7ffff 0xbd1bfffffe3cffff

def z836 : W := mkw 0x0000421821082aac 0x2000084304210555 0x9827c8386118fffd 0xd304f9070c231fff

def z837 : W := mkw 0x27ffedb760000000 0x04fffdb6ec000000 0xe7ffffffe00007fb 0xfcfffffffc0000ff

def z838 : W := mkw 0x27ffedb760000000 0x04fffdb6ec000000 0xe7fbfffb80000002 0xfcff7fff70000000

def z839 : W := mkw 0x15a03b681bb80787 0x02b4076d037700f0 0xfff83ff81fff0787 0xffff07ff03ffe0f0

def z840 : W := mkw 0x084b56ddb16b6eee 0x61096adbb62d6ddd 0x60fbf7fb91ff7800 0xac1f7eff723fef00

def z841 : W := mkw 0x06b400000c948000 0x00d6800001929000 0x9fffc0001ffff805 0xf3fff80003ffff00

def z842 : W := mkw 0x1ceb47fd29fa6aaf 0x639d68ffa53f4d55 0x20e3c7f801f87800 0x841c78ff003f0f00

def z843 : W := mkw 0x05eab802dad35550 0x80bd57005b5a6aaa 0x40e3f807e1f87ffa 0x881c7f00fc3f0fff

def z844 : W := mkw 0x06fe80000cd6d000 0x00dfd000019ada00 0x1fe7c0001ffff804 0xc3fcf80003ffff00

def z845 : W := mkw 0x06fe80024cd6d010 0x80dfd000499ada02 0x9fffc0007ffff81d 0xf3fff8000fffff03

def z846 : W := mkw 0x084a12c191634646 0x41094258322c68c8 0x40d831c391e70604 0x281b0638723ce0c0

def z847 : W := mkw 0x0214100094058440 0x004282001280b088 0xdf1c3807fe0787ff 0x7be38700ffc0f0ff

def z848 : W := mkw 0x06fe80000cd6d000 0x00dfd000019ada00 0x87ffc0001fff7801 0xf0fff80003ffef00

def z849 : W := mkw 0x02140002c4058050 0x804280005880b00a 0x9f1c0807fe0787ff 0x73e38100ffc0f0ff

def z850 : W := mkw 0x0001461c21082aac 0x200028c384210555 0x3027ce3c6118fffa 0xc604f9c78c231fff

def z851 : W := mkw 0x27ffedb760000000 0x04fffdb6ec000000 0xf7ffffffe0189803 0xfefffffffc031300

def z852 : W := mkw 0x27ffedb768900000 0x04fffdb6ed120000 0xe7fffffffee00003 0xfcffffffffdc0000

def z853 : W := mkw 0x27ffedb76446d000 0x04fffdb6ec88da00 0xe7ffffffe0070003 0xfcfffffffc00e000

def z854 : W := mkw 0x27b5edb760000000 0x04f6bdb6ec000000 0xe7e4ffffe0000002 0xfcfc9ffffc000000

def z855 : W := mkw 0x180012489ffff7e7 0x4300024913fffefc 0x180000001fffffe4 0x0300000003fffffc

def z856 : W := mkw 0x004b048500424000 0x00096090a0084800 0xe0db37c790e70003 0xbc1b66f8f21ce000

def z857 : W := mkw 0x15a17d743ab02d2b 0x22b42fae875605a5 0x4fc7f1c47ee0f879 0x29f8fe388fdc1f0f

def z858 : W := mkw 0x200145b520000000 0x040028b6a4000000 0x600037ff80000002 0x0c0006fff0000000

def z859 : W := mkw 0x214b6db760000000 0x04296db6ec000000 0x60c33fffe0000002 0x8c1867fffc000000

def z860 : W := mkw 0x27ffedb76cd6d000 0x04fffdb6ed9ada00 0xefffffffffe76007 0xfdfffffffffcec00

def z861 : W := mkw 0x17b4a92a4e9c9191 0x82f6952549d39232 0x1724c8386e189998 0x42e499070dc31333

def z862 : W := mkw 0x084b14c590636462 0x41096298b20c6c8c 0x40d831c790e70060 0x281b0638f21ce00c

def z863 : W := mkw 0x27ffedb760000000 0x04fffdb6ec000000 0xefffffffe000f803 0xfdfffffffc001f00

def z864 : W := mkw 0x27ffedb766048110 0x84fffdb6ecc09022 0xfffffffffe07819f 0xffffffffffc0f033

def z865 : W := mkw 0x27b5ef3e6d9cbaac 0x24f6bde7cdb39755 0xbf27ce3c6f18ffff 0xd7e4f9c78de31fff

def z866 : W := mkw 0x27ffedb760000000 0x04fffdb6ec000000 0xf7ffffffe0000787 0xfefffffffc0000f0

def z867 : W := mkw 0x27b5ed366c949000 0x04f6bda6cd929200 0xbf27ce3c6f18f807 0xd7e4f9c78de31f00

def z868 : W := mkw 0x27ffedb76cd6d000 0x04fffdb6ed9ada00 0xe7ffffffffff7803 0xfcffffffffffef00

def z869 : W := mkw 0x084b16c591636666 0x410962d8b22c6ccc 0xe8d837c790e70667 0x3d1b06f8f21ce0cc

def z870 : W := mkw 0x084a12c191636666 0x41094258322c6ccc 0xc8d831c791e76667 0x391b0638f23ceccc

def z871 : W := mkw 0x25ebedb768d25000 0x04bd7db6ed1a4a00 0x60e3ffffe1f87802 0x8c1c7ffffc3f0f00

def z872 : W := mkw 0x084a10c190634442 0x41094218320c6888 0xc0d831c790e70003 0x381b0638f21ce000

def z873 : W := mkw 0x21016db760000000 0x04202db6ec000000 0xe0043fffe0000003 0x5c0087fffc000000

def z874 : W := mkw 0x03143802d6058550 0x806287005ac0b0aa 0xc71c3807fe0707fb 0x78e38700ffc0e0ff

def z875 : W := mkw 0x15a039681ab80583 0x02b4072d035700b0 0xf7e03ff81ef80182 0xfefc07ff03df0030

def z876 : W := mkw 0x0000401820080888 0x2000080304010111 0x9827c83c6118ffff 0xd304f9078c231fff

def z877 : W := mkw 0x0001461c21082aac 0x200028c384210555 0x3827ce3c6018fffb 0x4704f9c78c031fff

def z878 : W := mkw 0x084a10c190636462 0x41094218320c6c8c 0x48d831c390e76060 0x291b0638721cec0c

def z879 : W := mkw 0x06fe80000cd6d000 0x00dfd000019ada00 0xfffff7c01ffff807 0xfffffef803ffff00

def z880 : W := mkw 0x084b16c593636766 0x410962d8b26c6cec 0xf8db37c79fe767e7 0xbf1b66f8f3fcecfc

def z881 : W := mkw 0x1cea12489bfb67e7 0x439d4249137f6cfc 0x9ffb00001fff67e5 0xf3ff600003ffecfc

def z882 : W := mkw 0x10001248972d87d7 0x8200024912e5b0fa 0x180000001e0787fc 0x0300000003c0f0ff

def z883 : W := mkw 0x27ffedb760424000 0x04fffdb6ec084800 0xe7fffffff0e70003 0xfcfffffffe1ce000

def z884 : W := mkw 0x15a03b681bb80787 0x02b4076d037700f0 0x37e00ff81ff80784 0xc6fc01ff03ff00f0

def z885 : W := mkw 0x15a03b681bb80787 0x02b4076d037700f0 0xf7e43ff87ff8879e 0xfefc87ff0fff10f3

def z886 : W := mkw 0x084b16c591636666 0x410962d8b22c6ccc 0xe8fbf7c791ff7e67 0xbd1f7ef8f23fefcc

def z887 : W := mkw 0x03143802d6058550 0x806287005ac0b0aa 0x5f1c3007fe0787fd 0x2be38600ffc0f0ff

def z888 : W := mkw 0x0100292240000000 0x0020052448000000 0x60003fffe0000002 0x0c0007fffc000000

def z889 : W := mkw 0x07ffada500000000 0x00fff5b4a0000000 0xe7ffffff80000003 0xfcfffffff0000000

def z890 : W := mkw 0x084b16cd916b66e6 0x410962d9b22d6cdc 0xf8ffffff91ffffe7 0xff1ffffff23ffffc

def z891 : W := mkw 0x15a03b681bb80787 0x02b4076d037700f0 0xffe03ff81ff887fe 0xfffc07ff03ff10ff

def z892 : W := mkw 0x084b56ddb16b6eee 0x61096adbb62d6ddd 0xe8db37ff91e76667 0xbd1b66fff23ceccc

def z893 : W := mkw 0x084b16c591636666 0x410962d8b22c6ccc 0xe8df37c7f1e7e67f 0xbd1be6f8fe3cfccf

def z894 : W := mkw 0x084b16c593636776 0xc10962d8b26c6cee 0xe8db37c791e767ff 0xbd1b66f8f23cecff

def z895 : W := mkw 0x084b96c591637666 0x410972d8b22c6ecc 0xe8dbf7c791e77e67 0xbd1b7ef8f23cefcc

def z896 : W := mkw 0x14a0036809b80287 0x0294006d01370050 0x37e007f80ff80000 0xc6fc00ff01ff0000

def z897 : W := mkw 0x06fe80000cd6d000 0x00dfd000019ada00 0x1ffbc0001ffff804 0xa3ff780003ffff00

def z898 : W := mkw 0x15a03b681bb82faf 0x22b4076d037705f5 0xffe7fff81ff8ffff 0xfffcffff03ff1fff

def z899 : W := mkw 0x27ffedb760000000 0x04fffdb6ec000000 0x67fbffffe0000002 0xacff7ffffc000000

def z900 : W := mkw 0x225fc4976446d000 0x044bf892ec88da00 0x001fc007e0070001 0x0003f800fc00e000

def z901 : W := mkw 0x004a008100424000 0x0009401020084800 0x40d831c390e70000 0x281b0638721ce000

def z902 : W := mkw 0x004b048500000000 0x00096090a0000000 0xe0fb3fff80000003 0xfc1f67fff0000000

def z903 : W := mkw 0x284bd6d5b1636666 0x45097adab62c6ccc 0xe8dbf7c791e76667 0xbd1b7ef8f23ceccc

def z904 : W := mkw 0x0001461c21082aac 0x200028c384210555 0xbf27ce3c7f18ffff 0xf7e4f9c78fe31fff

def z905 : W := mkw 0x27ffedb760000000 0x04fffdb6ec000000 0xf7fffffffe000007 0xfeffffffffc00000

def z906 : W := mkw 0x25a16db760000000 0x04b42db6ec000000 0x60e03fffe0000002 0x8c1c07fffc000000

def z907 : W := mkw 0x084b56d5b1636e6e 0x61096adab62c6dcd 0xe8fffffff1e7fe7f 0xfd1ffffffe3cffcf

def z908 : W := mkw 0x0001441420000000 0x0000288284000000 0xb827ce3c6118ffff 0xd704f9c78c231fff

def z909 : W := mkw 0x03143802d6058550 0x806287005ac0b0aa 0xdf3ff807fe0787ff 0xfbe7ff00ffc0f0ff

def z910 : W := mkw 0x27ffedb760000000 0x04fffdb6ec000000 0xefffffffe000807b 0xfdfffffffc00100f

def z911 : W := mkw 0x27ffedb764048000 0x04fffdb6ec809000 0xffffffffff1ff807 0xffffffffffe3ff00

def z912 : W := mkw 0x17feb962def7d553 0x82ffd72c5bdefaaa 0x47d831c39ee70000 0x28fb063873dce000

def z913 : W := mkw 0x27b4a9224c949000 0x04f6952449929200 0x070000000e000000 0x00e0000001c00000

def z914 : W := mkw 0x27ffedb76cd6d000 0x04fffdb6ed9ada00 0xffffffffee1ff803 0xfffffffffdc3ff00

def z915 : W := mkw 0x23156db760000000 0x0462adb6ec000000 0x67183fffe0000002 0x2ce307fffc000000

def z916 : W := mkw 0x004b449520000000 0x00096892a4000000 0xe0db3fffe0000003 0xbc1b67fffc000000

def z917 : W := mkw 0x27b5edb760000000 0x04f6bdb6ec000000 0xe73cffffe0000003 0x7ce79ffffc000000

def z918 : W := mkw 0x27ffedb760425000 0x04fffdb6ec084a00 0xe7ffffffe0007803 0xfcfffffffc000f00

def z919 : W := mkw 0x27b4e9326e949110 0x84f69d264dd29222 0x1724c8386e189998 0x42e499070dc31333

def z920 : W := mkw 0x084b16c591636666 0x410962d8b22c6ccc 0xf8df37c791e7e667 0xff1be6f8f23cfccc

def z921 : W := mkw 0x27ffedb768d24000 0x04fffdb6ed1a4800 0xffffffffffff6007 0xffffffffffffec00

def z922 : W := mkw 0x06fe80000cd6d000 0x00dfd000019ada00 0x9fffc8007ffff99d 0xf3fff9000fffff33

def z923 : W := mkw 0x235fedb760000000 0x046bfdb6ec000000 0xe03fffffe0000003 0xdc07fffffc000000

def z924 : W := mkw 0x16fe92489fffd7d7 0x82dfd24913fffafa 0x9fffc0001ffffffd 0xf3fff80003ffffff

def z925 : W := mkw 0x15a03b681bb82faf 0x22b4076d037705f5 0xffe43ffc7ff8ffff 0xfffc87ff8fff1fff

def z926 : W := mkw 0x05a0292008900000 0x00b4052401120000 0xe7e03ff81ee00002 0xfcfc07ff03dc0000

def z927 : W := mkw 0x27ffedb764049000 0x04fffdb6ec809200 0xe7ffffffe0009803 0xfcfffffffc001300

def z928 : W := mkw 0x26ffc5b52cd6d000 0x04dff8b6a59ada00 0xfffff7ff9ffff807 0xfffffefff3ffff00

def z929 : W := mkw 0x37b4e93a6e9c8191 0x86f69d274dd39032 0x1724c8386e188198 0x42e499070dc31033

def z930 : W := mkw 0x084b16c591636666 0x410962d8b22c6ccc 0x60db37c791e76662 0xac1b66f8f23ceccc

def z931 : W := mkw 0x004b449520000000 0x00096892a4000000 0xe0fbf7ff80000003 0xbc1f7efff0000000

def z932 : W := mkw 0x15a03b681bb80787 0x02b4076d037700f0 0x67c037f81ee00000 0x2cf806ff03dc0000

def z933 : W := mkw 0x084b06c501626226 0x410960d8a02c4c44 0xe8db37c791e76007 0xbd1b66f8f23cec00

def z934 : W := mkw 0x27ffedb760000000 0x04fffdb6ec000000 0xe7dc3fffe0000003 0x7cfb87fffc000000

def z935 : W := mkw 0x21016db762000110 0x84202db6ec400022 0x60003fffe000019a 0x0c0007fffc000033

def z936 : W := mkw 0x084a10c190634442 0x41094218320c6888 0x48db31c390e76001 0x291b6638721cec00

def z937 : W := mkw 0x27ffedb768d25000 0x04fffdb6ed1a4a00 0xe7ffffffe0e00003 0xfcfffffffc1c0000

def z938 : W := mkw 0x084a50d9b06b4cca 0x61094a1b360d6999 0x50fcf9fbf0ff9998 0x6a1f9f3f7e1ff333

def z939 : W := mkw 0x21016db760000000 0x04202db6ec000000 0x6007ffffe0000003 0x0c00fffffc000000

def z940 : W := mkw 0x0000104090210442 0x0000020812042088 0xc8d831c790e70667 0x391b0638f21ce0cc

def z941 : W := mkw 0x18001248932927e7 0x43000249126524fc 0x00000000000007e0 0x00000000000000fc

def z942 : W := mkw 0x27b4e93260000000 0x04f69d264c000000 0xe7fcffffe0000003 0xfcff9ffffc000000

def z943 : W := mkw 0x0314280244048000 0x0062850048809000 0xdf1c3807fe0787ff 0x7be38700ffc0f0ff

def z944 : W := mkw 0x27b4a9224c949000 0x04f6952449929200 0x1724c0000e189800 0x42e4980001c31300

def z945 : W := mkw 0x27ffedb768d25000 0x04fffdb6ed1a4a00 0xffffffffe1f8f807 0xfffffffffc3f1f00

def z946 : W := mkw 0x27ffedb760000808 0x24fffdb6ec000101 0xe7ffffffe000981b 0xfcfffffffc001303

def z947 : W := mkw 0x15a02b6809b80287 0x02b4056d01370050 0xf7e03ff81ff80006 0xfefc07ff03ff0000

def z948 : W := mkw 0x084b56d5b1636666 0x41096adab62c6ccc 0xe8db3ffff1e76667 0xbd1b67fffe3ceccc

def z949 : W := mkw 0x15a02b680bb80387 0x02b4056d01770070 0xb7e00ff81ff80184 0xf6fc01ff03ff0030

def z950 : W := mkw 0x100012489fbdafff 0xa200024913f7b5ff 0x180000001ffffffc 0x0300000003ffffff

def z951 : W := mkw 0x25ebedb760000000 0x04bd7db6ec000000 0x60e3f7fb80000000 0x8c1c7eff70000000

def z952 : W := mkw 0x25a16db760000000 0x04b42db6ec000000 0xe7e7ffffe0000003 0xfcfcfffffc000000

def z953 : W := mkw 0x214bedb760000000 0x04297db6ec000000 0x6003ffffe0000002 0x0c007ffffc000000

def z954 : W := mkw 0x24ebd5b5b6058550 0x849d7ab6b6c0b0aa 0x38e3c7f81e0787fc 0x871c78ff03c0f0ff

def z955 : W := mkw 0x09017edff3292ffe 0xe1202fdbfe6525ff 0x60003fffe00007fa 0x0c0007fffc0000ff

def z956 : W := mkw 0x0001461c21082aac 0x200028c384210555 0xb83fce3c711fffff 0xf707f9c78e23ffff

def z957 : W := mkw 0x15a029280a980181 0x02b4052501530030 0xf7e03ff81ff80186 0xfefc07ff03ff0030

def z958 : W := mkw 0x03143802d6058550 0x806287005ac0b0aa 0xff3c3e3ffe0787ff 0xffe787c7ffc0f0ff

def z959 : W := mkw 0x15a03b689bb907d7 0x82b4076d137720fa 0xf7e03ff81ff807fe 0xfefc07ff03ff00ff

def z960 : W := mkw 0x07fea9224cd6d000 0x00ffd524499ada00 0xfffffffffffff807 0xffffffffffffff00

def z961 : W := mkw 0x084b16c591636666 0x410962d8b22c6ccc 0xe8db37c391e76005 0xbd1b66f8723cec00

def z962 : W := mkw 0x06fe80000cd6d000 0x00dfd000019ada00 0x9fffc8001fffff87 0xf3fff90003fffff0

def z963 : W := mkw 0x0000104090210442 0x0000020812042088 0x40d831c390e70000 0x281b0638721ce000

def z964 : W := mkw 0x27ffedb76cd6d000 0x04fffdb6ed9ada00 0xfffffffffee78007 0xffffffffffdcf000

def z965 : W := mkw 0x05a12da500000000 0x00b425b4a0000000 0xe7e03fff80000002 0xfcfc07fff0000000

def z966 : W := mkw 0x084b16c591636666 0x410962d8b22c6ccc 0xe0db37c790e70663 0xbc1b66f8f21ce0cc

def z967 : W := mkw 0x24ebc5b520000000 0x049d78b6a4000000 0xe0ffffffe0000003 0xfc1ffffffc000000

def z968 : W := mkw 0x210029a340000000 0x0420053468000000 0x60003ffb80000002 0x0c0007ff70000000

def z969 : W := mkw 0x004a124091634646 0x00094248122c68c8 0xe8db37c791e76667 0xbd1b66f8f23ceccc

def z970 : W := mkw 0x27ffedb76cd6d000 0x04fffdb6ed9ada00 0x67d83ffffee70002 0x2cfb07ffffdce000

def z971 : W := mkw 0x15a03b601bb00707 0x02b4076c037600e0 0xe7e03ff81fe00606 0xfcfc07ff03fc00c0

def z972 : W := mkw 0x27ffedb76c949000 0x04fffdb6ed929200 0xffffffffef18f807 0xfffffffffde31f00

def z973 : W := mkw 0x05a03b6013200706 0x00b4076c026400e0 0xf7e03ff81fe00786 0xfefc07ff03fc00f0

def z974 : W := mkw 0x15a03b689bb907c7 0x02b4076d137720f8 0xf7e03fff9ff807e6 0xfefc07fff3ff00fc

def z975 : W := mkw 0x084a12c191636666 0x41094258322c6ccc 0x40d831c390e70660 0x281b0638721ce0cc

def z976 : W := mkw 0x06fe80000cd6d000 0x00dfd000019ada00 0x1f3fc0001ffff805 0x43e7f80003ffff00

def z977 : W := mkw 0x084a10c190634442 0x41094218320c6888 0xe0d837c390e70002 0xbc1b06f8721ce000

def z978 : W := mkw 0x06fe80000cd6d000 0x00dfd000019ada00 0x17ffc0001ffff800 0xe2fff80003ffff00

def z979 : W := mkw 0x27ffedb76446d000 0x04fffdb6ec88da00 0xeffffffff1e7f807 0xfdfffffffe3cff00

def z980 : W := mkw 0x17b4693a6e9c8999 0xa2f68d274dd39133 0x1724c8386e189998 0x42e499070dc31333

def z981 : W := mkw 0x084b56ddb16b6eee 0x61096adbb62d6ddd 0xe8fbfffff1ff7fff 0xbd1f7ffffe3fefff

def z982 : W := mkw 0x21016db760000000 0x04202db6ec000000 0xe7003fffe0000002 0x7ce007fffc000000

def z983 : W := mkw 0x084b56d5b1636e6e 0x61096adab62c6dcd 0xf8dfffc7f1e7ffff 0xff1bfff8fe3cffff

def z984 : W := mkw 0x084b56ddb16b6eee 0x61096adbb62d6ddd 0xe8fffffff1e767ff 0xfd1ffffffe3cecff

def z985 : W := mkw 0x0100380092010540 0x00200700124020a8 0xdf1c3807fe0787ff 0x7be38700ffc0f0ff

def z986 : W := mkw 0x07b56d3660000000 0x00f6ada6cc000000 0xe7ffffffe0000003 0xfcfffffffc000000

def z987 : W := mkw 0x21016db760000000 0x04202db6ec000000 0xf827ffffe118f807 0xdf04fffffc231f00

def z988 : W := mkw 0x0a5fc495a447f868 0x614bf892b488ff0d 0x081fc007e007f879 0x0103f800fc00ff0f

def z989 : W := mkw 0x2315edb760000000 0x0462bdb6ec000000 0x6004ffffe0000002 0x0c009ffffc000000

def z990 : W := mkw 0x084b56ddb16b6eee 0x61096adbb62d6ddd 0x60d83ffff0e707fa 0x2c1b07fffe1ce0ff

def z991 : W := mkw 0x21016db760002828 0x24202db6ec000505 0x60003fffe000007a 0x0c0007fffc00000f

def z992 : W := mkw 0x084b16c591636e6e 0x610962d8b22c6dcd 0xe8db37c791e7fe7f 0xbd1b66f8f23cffcf

def z993 : W := mkw 0x15a03b681bb80f8f 0x22b4076d037701f1 0xf7e03ff81ff89f9e 0xfefc07ff03ff13f3

def z994 : W := mkw 0x27ffedb76cd6d000 0x04fffdb6ed9ada00 0xf7ffffffffff0007 0xfeffffffffffe000

def z995 : W := mkw 0x084a12c191634646 0x41094258322c68c8 0x60d837c391e70000 0xac1b06f8723ce000

def z996 : W := mkw 0x084b16cd916b66e6 0x410962d9b22d6cdc 0xf8db37c791ff67e7 0xbf1b66f8f23fecfc

def z997 : W := mkw 0x27ffedb760000000 0x04fffdb6ec000000 0xffffffffe118ffff 0xfffffffffc231fff

def z998 : W := mkw 0x21016db760000000 0x04202db6ec000000 0xe0183fffe0000003 0x3c0307fffc000000

def z999 : W := mkw 0x04eb05a500000000 0x009d60b4a0000000 0xe0fb37ff80000003 0xbc1f66fff0000000

def z1000 : W := mkw 0x084b14c590636462 0x41096298b20c6c8c 0xc8db31c791e76065 0xb91b6638f23cec0c

def z1001 : W := mkw 0x01003a4813280786 0x00200749026500f0 0xf7e03ff81ff80786 0xfefc07ff03ff00f0

def z1002 : W := mkw 0x04a0124819b80686 0x00940249033700d0 0xf7e03ff81ff80786 0xfefc07ff03ff00f0

def z1003 : W := mkw 0x084b14c590636462 0x41096298b20c6c8c 0x40db31c390e76000 0x281b6638721cec00

def z1004 : W := mkw 0x27ffedb760424000 0x04fffdb6ec084800 0xfffffffff1fff807 0xfffffffffe3fff00

def z1005 : W := mkw 0x27ffedb766048110 0x84fffdb6ecc09022 0xffffffffee0087ff 0xfffffffffdc010ff

def z1006 : W := mkw 0x15a039601ab00503 0x02b4072c035600a0 0x67c03ff81ee00002 0x2cf807ff03dc0000

def z1007 : W := mkw 0x27ffedb76cd6d000 0x04fffdb6ed9ada00 0xffffffffffffffff 0xffffffffffffffff

def z1008 : W := mkw 0x0001461c21082aac 0x200028c384210555 0x2827ce3c6118fffb 0x8504f9c78c231fff

def z1009 : W := mkw 0x27ffedb760000000 0x04fffdb6ec000000 0xf7ffffffe000819b 0xfefffffffc001033

def z1010 : W := mkw 0x15a03b681bb80787 0x02b4076d037700f0 0xf7e4fff81ff89f86 0xfefc9fff03ff13f0

def z1011 : W := mkw 0x27ffedb768900000 0x04fffdb6ed120000 0xfffffffffff8f807 0xffffffffffff1f00

def z1012 : W := mkw 0x27ffedb76446d000 0x04fffdb6ec88da00 0xffffffffe11ff807 0xfffffffffc23ff00

def z1013 : W := mkw 0x080146dd21282aae 0x610028dba4250555 0xb827cffc6118ffff 0xd704f9ff8c231fff

def z1014 : W := mkw 0x25a1edb760000000 0x04b43db6ec000000 0x6020ffffe0000002 0x0c041ffffc000000

def z1015 : W := mkw 0x27ffedb760000000 0x04fffdb6ec000000 0x67dfffffe0000003 0x2cfbfffffc000000

def z1016 : W := mkw 0x084b16c591636666 0x410962d8b22c6ccc 0xf8ffffc7f1ffffff 0xff1ffff8fe3fffff

def z1017 : W := mkw 0x16b4036acdbd82d7 0x82d6806d59b7b05a 0x28fc07ffe1ff8079 0x851f80fffc3ff00f

def z1018 : W := mkw 0x225fc4952446d000 0x044bf892a488da00 0x081fc0000007f801 0x0103f8000000ff00

def z1019 : W := mkw 0x03143802d6058550 0x806287005ac0b0aa 0x5f183807fe0787fe 0x2be30700ffc0f0ff

def z1020 : W := mkw 0x084b56d5b1636e6e 0x61096adab62c6dcd 0xe8db37c7f1e7667f 0xbd1b66f8fe3ceccf

def z1021 : W := mkw 0x0000124091210646 0x00000248122420c8 0xe0d837c391e70606 0xbc1b06f8723ce0c0

def z1022 : W := mkw 0x27ffedb764048000 0x04fffdb6ec809000 0xfffffffffe0787ff 0xffffffffffc0f0ff

def z1023 : W := mkw 0x0a5f4497e447e878 0xe14be892fc88fd0f 0x081fc007e007f879 0x0103f800fc00ff0f

def z1024 : W := mkw 0x21016db760000000 0x04202db6ec000000 0x6024ffffe0000002 0x4c049ffffc000000

def z1025 : W := mkw 0x21016db760002828 0x24202db6ec000505 0x6807ffffe000f87b 0x0d00fffffc001f0f

def z1026 : W := mkw 0x27fea9a34cd6d000 0x04ffd534699ada00 0xf7f83ffb9fff0006 0xfeff07ff73ffe000

def z1027 : W := mkw 0x27ffedb768901000 0x04fffdb6ed120200 0xe7ffffffe0181803 0xfcfffffffc030300

def z1028 : W := mkw 0x27ffedb76ed6d110 0x84fffdb6eddada22 0xfffffffffffff99f 0xffffffffffffff33

def z1029 : W := mkw 0x225fc497e447d050 0x844bf892fc88fa0a 0x081fc007e007f879 0x0103f800fc00ff0f

def z1030 : W := mkw 0x1efe92489ffff7e7 0x43dfd24913fffefc 0x9fffc0001fffffe5 0xf3fff80003fffffc

def z1031 : W := mkw 0x27ffedb76cd6d000 0x04fffdb6ed9ada00 0xf7fffffffeff9803 0xfeffffffffdff300

def z1032 : W := mkw 0x1da03b689bb927e7 0x43b4076d137724fc 0xf7e03ff81ff807e6 0xfefc07ff03ff00fc

def z1033 : W := mkw 0x15a03b681bb80787 0x02b4076d037700f0 0xf7e03ffc7ff807fe 0xfefc07ff8fff00ff

def z1034 : W := mkw 0x180012489fffe7f7 0xc300024913fffcfe 0x180000001fffe7fc 0x0300000003fffcff

def z1035 : W := mkw 0x04ea80000cd6d000 0x009d5000019ada00 0x9fe3c0001ffff804 0xf3fc780003ffff00

def z1036 : W := mkw 0x08001248916b6eee 0x61000249122d6ddd 0x0800000011ff7e64 0x01000000023fefcc

def z1037 : W := mkw 0x27fea9a340000000 0x04ffd53468000000 0x67d83ffb80000002 0x2cfb07ff70000000

def z1038 : W := mkw 0x084b048580436060 0x41096090b0086c0c 0xe8db37c791e76067 0xbd1b66f8f23cec0c

def z1039 : W := mkw 0x27ffedb76cd6d000 0x04fffdb6ed9ada00 0xeffffffffee7f803 0xfdffffffffdcff00

def z1040 : W := mkw 0x27b5edb760000000 0x04f6bdb6ec000000 0xe727ffffe0000003 0xdce4fffffc000000

def z1041 : W := mkw 0x06fe80000cd6d000 0x00dfd000019ada00 0x97fbc0001fff7804 0xf2ff780003ffef00

def z1042 : W := mkw 0x084b54d5b0636c6a 0x61096a9ab60c6d8d 0x48dff1c7f0e7f879 0x291bfe38fe1cff0f

def z1043 : W := mkw 0x00001248912906c6 0x00000249122520d8 0xf8fc3ffff1ff87ff 0xff1f87fffe3ff0ff

def z1044 : W := mkw 0x07fea92240000000 0x00ffd52448000000 0xe7ffffffe0000003 0xfcfffffffc000000

def z1045 : W := mkw 0x05a0292240000000 0x00b4052448000000 0xe7e03fffe0000002 0xfcfc07fffc000000

def z1046 : W := mkw 0x0800124091636666 0x41000248122c6ccc 0xe8d837c791e76667 0xbd1b06f8f23ceccc

def z1047 : W := mkw 0x13143962d6258553 0x8262872c5ac4b0aa 0xdf1c39c7fe0787ff 0x7be38738ffc0f0ff

def z1048 : W := mkw 0x11003b6813280787 0x0220076d026500f0 0xf7c03ff81fe00786 0xfef807ff03fc00f0

def z1049 : W := mkw 0x15a03b681bb82faf 0x22b4076d037705f5 0xf7e03ff81ff807fe 0xfefc07ff03ff00ff

def z1050 : W := mkw 0x084a12c191634646 0x41094258322c68c8 0xe8d837c791e70667 0xbd1b06f8f23ce0cc

def z1051 : W := mkw 0x03143802d6058550 0x806287005ac0b0aa 0xdf1c3807ff1fffff 0x7be38700ffe3ffff

def z1052 : W := mkw 0x15a03b681bb80787 0x02b4076d037700f0 0xf7f83fff9ff80787 0xfeff07fff3ff00f0

def z1053 : W := mkw 0x084a12c191634646 0x41094258322c68c8 0x60d837c390e70602 0x2c1b06f8721ce0c0

def z1054 : W := mkw 0x27ffedb760000000 0x04fffdb6ec000000 0x67fffffbe0000000 0xecffffff7c000000

def z1055 : W := mkw 0x03143802d6058550 0x806287005ac0b0aa 0xdf3cf807fe1f9fff 0x7be79f00ffc3f3ff

def z1056 : W := mkw 0x27fea9a34cd6d000 0x04ffd534699ada00 0xfffffffb9ffff807 0xffffffff73ffff00

def z1057 : W := mkw 0x27ffedb76cd6d000 0x04fffdb6ed9ada00 0xfffff7fb9ffff805 0xfffffeff73ffff00

def z1058 : W := mkw 0x084b14c590636462 0x41096298b20c6c8c 0xc8db31c790e76667 0x391b6638f21ceccc

def z1059 : W := mkw 0x0314292240000000 0x0062852448000000 0xe71c3fffe0000003 0x7ce387fffc000000

def z1060 : W := mkw 0x025e00000446c000 0x004bc0000088d800 0x9fffc0001ffff805 0xf3fff80003ffff00

def z1061 : W := mkw 0x15a03b681bb80787 0x02b4076d037700f0 0xf7e3fff81ff87f86 0xfefc7fff03ff0ff0

def z1062 : W := mkw 0x27ffedb760000000 0x04fffdb6ec000000 0xeffffffff0070007 0xfdfffffffe00e000

def z1063 : W := mkw 0x004b469d214a6aac 0x200968d3a4294d55 0xf8fffffff1ffffff 0xff1ffffffe3fffff

def z1064 : W := mkw 0x03143802d6058550 0x806287005ac0b0aa 0xdf1f3807ff07e7ff 0xfbe3e700ffe0fcff

def z1065 : W := mkw 0x06fe80810cd6d000 0x00dfd010219ada00 0xdffff1c39ffff805 0xfbfffe3873ffff00

def z1066 : W := mkw 0x15a02b680bb80387 0x02b4056d01770070 0x27e007f80ff80000 0x84fc00ff01ff0000

def z1067 : W := mkw 0x15a039601ab00503 0x02b4072c035600a0 0x67e037f81ee00000 0xacfc06ff03dc0000

def z1068 : W := mkw 0x27feb9a3ded7d550 0x84ffd7347bdafaaa 0x47d831c39ee70000 0x28fb063873dce000

def z1069 : W := mkw 0x15a03b681bb80787 0x02b4076d037700f0 0xf7e43ffc7ff80787 0xfefc87ff8fff00f0

def z1070 : W := mkw 0x27ffedb764048000 0x04fffdb6ec809000 0xf7ffffffee008003 0xfefffffffdc01000

def z1071 : W := mkw 0x084b56ddb16b66e6 0x41096adbb62d6cdc 0xf8fffffff1ff67e7 0xff1ffffffe3fecfc

def z1072 : W := mkw 0x084b16c591636666 0x410962d8b22c6ccc 0xf8fb37c791ff6667 0xff1f66f8f23feccc

def z1073 : W := mkw 0x15a03b681bb80787 0x02b4076d037700f0 0xe7c03ff81fe00786 0xbcf807ff03fc00f0

def z1074 : W := mkw 0x084b16c591636666 0x410962d8b22c6ccc 0x48db31c791e76665 0x291b6638f23ceccc

def z1075 : W := mkw 0x27ffedb76cd6f828 0x24fffdb6ed9adf05 0xfffffffffffff87f 0xffffffffffffff0f

def z1076 : W := mkw 0x0001465c21282aae 0x200028cb84250555 0xb8e7cffc61f8ffff 0xd71cf9ff8c3f1fff

def z1077 : W := mkw 0x15a03b6a5bb80787 0x02b4076d4b7700f0 0xf7e03ffffff80786 0xfefc07ffffff00f0

def z1078 : W := mkw 0x084b14c590634442 0x41096298b20c6888 0x40db31c790e70001 0x281b6638f21ce000

def z1079 : W := mkw 0x04a000000cd6d000 0x00940000019ada00 0x9fe7c0001ffff805 0xf3fcf80003ffff00

def z1080 : W := mkw 0x15a03b681bb80787 0x02b4076d037700f0 0x67e03ff81ff80782 0xacfc07ff03ff00f0

def z1081 : W := mkw 0x084b16cd916b66e6 0x410962d9b22d6cdc 0xe8fb37ff91ff6667 0xbd1f66fff23feccc

def z1082 : W := mkw 0x084b16c591636666 0x410962d8b22c6ccc 0xf8db37c791fffe67 0xbf1b66f8f23fffcc

def z1083 : W := mkw 0x27ffedb760002020 0x04fffdb6ec000404 0xefffffffe0006063 0xfdfffffffc000c0c

def z1084 : W := mkw 0x26ffc5b760000000 0x04dff8b6ec000000 0xe0fff7ffe0000003 0xbc1ffefffc000000

def z1085 : W := mkw 0x21016db760000000 0x04202db6ec000000 0xe0c03fffe0000002 0xbc1807fffc000000

def z1086 : W := mkw 0x27ffedb76c949000 0x04fffdb6ed929200 0xf7fffffffff89807 0xfeffffffffff1300

def z1087 : W := mkw 0x004b068501426224 0x000960d0a0284c44 0xe8db37c791e76667 0xbd1b66f8f23ceccc

def z1088 : W := mkw 0x084a10c190634442 0x41094218320c6888 0x48d831c391e76004 0x291b0638723cec00

def z1089 : W := mkw 0x25ebedb520000000 0x04bd7db6a4000000 0xe7fbffff80000003 0xfcff7ffff0000000

def z1090 : W := mkw 0x0001565cb1292eee 0x20002acb962525dd 0xf8fffffff1ffffff 0xff1ffffffe3fffff

def z1091 : W := mkw 0x17b56f3e6f9cabbd 0xa2f6ade7cdf39577 0xbf27ce3c6f18ffff 0xd7e4f9c78de31fff

def z1092 : W := mkw 0x15a03b681bb80787 0x02b4076d037700f0 0xffe43ff81ff88787 0xfffc87ff03ff10f0

def z1093 : W := mkw 0x11017f7ef3292fff 0xa2202fefde6525ff 0x60003fffe00007fa 0x0c0007fffc0000ff

def z1094 : W := mkw 0x084a10c190634442 0x41094218320c6888 0x40d831c790e70662 0x281b0638f21ce0cc

def z1095 : W := mkw 0x0314b802d6059550 0x806297005ac0b2aa 0xdf1cf807fe079fff 0x7be39f00ffc0f3ff

def z1096 : W := mkw 0x26fe81a10cd6d000 0x04dfd034219ada00 0x9fffc1c01ffff805 0xf3fff83803ffff00

def z1097 : W := mkw 0x27ffedb760000000 0x04fffdb6ec000000 0x67fcffffe0000002 0x6cff9ffffc000000

def z1098 : W := mkw 0x27ffedb760424000 0x04fffdb6ec084800 0xe7ffffffe1e06003 0xfcfffffffc3c0c00

def z1099 : W := mkw 0x084b14c590634442 0x41096298b20c6888 0x60d837c790e70002 0x2c1b06f8f21ce000

def z1100 : W := mkw 0x27ffedb76446d000 0x04fffdb6ec88da00 0xfffffffffe07f807 0xffffffffffc0ff00

def z1101 : W := mkw 0x15a03b6adbb907d7 0x82b4076d5b7720fa 0xfff83fffffff07ff 0xffff07ffffffe0ff

def z1102 : W := mkw 0x15a03b681bb80787 0x02b4076d037700f0 0xffe03ff81ff8ff86 0xfffc07ff03ff1ff0

def z1103 : W := mkw 0x084b16c591636666 0x410962d8b22c6ccc 0xe0d837c791e70666 0xbc1b06f8f23ce0cc

def z1104 : W := mkw 0x24ebc5b520000000 0x049d78b6a4000000 0x60fbf7fb80000000 0xac1f7eff70000000

def z1105 : W := mkw 0x06fe80000cd6d000 0x00dfd000019ada00 0xdffff0079ffff807 0xfbfffe00f3ffff00

def z1106 : W := mkw 0x06fe81200cd6d000 0x00dfd024019ada00 0xbfffc7f81ffff805 0xf7fff8ff03ffff00

def z1107 : W := mkw 0x15a03b681bb80787 0x02b4076d037700f0 0x77c03ff81ff80786 0x2ef807ff03ff00f0

def z1108 : W := mkw 0x084a10c190634442 0x41094218320c6888 0xc8d831c390e70005 0x391b0638721ce000

def z1109 : W := mkw 0x27ffedb760002828 0x24fffdb6ec000505 0xe7ffffffe0007803 0xfcfffffffc000f00

def z1110 : W := mkw 0x27ffedb764048010 0x84fffdb6ec809002 0xe7ffffffe000801b 0xfcfffffffc001003

def z1111 : W := mkw 0x084a12c9916b46c6 0x41094259322d68d8 0xf0f83ffb91ff0786 0xfe1f07ff723fe0f0

def z1112 : W := mkw 0x26fe80834cd6d000 0x04dfd010699ada00 0x9fffc0039ffff805 0xf3fff80073ffff00

def z1113 : W := mkw 0x084b56d5b1636666 0x41096adab62c6ccc 0xe8fbf7ff91e76667 0xbd1f7efff23ceccc

def z1114 : W := mkw 0x21016db760000000 0x04202db6ec000000 0xe0033fffe0000003 0x9c0067fffc000000

def z1115 : W := mkw 0x04a0012008900000 0x0094002401120000 0xb7e007f81ff80004 0xf6fc00ff03ff0000

def z1116 : W := mkw 0x14a0136819b80687 0x0294026d033700d0 0xf7e037f81ff80606 0xfefc06ff03ff00c0

def z1117 : W := mkw 0x080012489dfffeee 0x6100024913bfffdd 0x180000001ffffffc 0x0300000003ffffff

def z1118 : W := mkw 0x04ea800008d25000 0x009d5000011a4a00 0x9ffbc0001fff7805 0xf3ff780003ffef00

def z1119 : W := mkw 0x084a12c191636666 0x41094258322c6ccc 0xe8d837c391e76666 0xbd1b06f8723ceccc

def z1120 : W := mkw 0x15a03b681bb80787 0x02b4076d037700f0 0x77e03ff81ff80180 0xeefc07ff03ff0030

def z1121 : W := mkw 0x21016db760000000 0x04202db6ec000000 0xf8043fffe00087ff 0x5f0087fffc0010ff

def z1122 : W := mkw 0x15a03b681bb80787 0x02b4076d037700f0 0xe7e03ff81ee00782 0xfcfc07ff03dc00f0

def z1123 : W := mkw 0x37ffedb76a900101 0x06fffdb6ed520020 0xe7ffffffee000003 0xfcfffffffdc00000

def z1124 : W := mkw 0x27fea9a340000000 0x04ffd53468000000 0xe7fc3fffe0000003 0xfcff87fffc000000

def z1125 : W := mkw 0x08001248976feffe 0xe100024912edfdff 0x180000001ffffffc 0x0300000003ffffff

def z1126 : W := mkw 0x084b16c591636666 0x410962d8b22c6ccc 0xe8db3fc7f1e767ff 0xbd1b67f8fe3cecff

def z1127 : W := mkw 0x17b429224e948111 0x82f6852449d29022 0x070000000e000000 0x00e0000001c00000

def z1128 : W := mkw 0x05ea29a100000000 0x00bd453420000000 0xe7f83ffb80000002 0xfcff07ff70000000

def z1129 : W := mkw 0x18001248936b67e7 0x43000249126d6cfc 0x0800000011e767e4 0x01000000023cecfc

def z1130 : W := mkw 0x10001248932907d7 0x82000249126520fa 0x00000000000007f8 0x00000000000000ff

def z1131 : W := mkw 0x27ffedb760000000 0x04fffdb6ec000000 0xe7fbf7ff80000003 0xbcff7efff0000000

def z1132 : W := mkw 0x084b56ddb16b6eee 0x61096adbb62d6ddd 0xf8fbf7ff91ffffff 0xbf1f7efff23fffff

def z1133 : W := mkw 0x03143802d6058550 0x806287005ac0b0aa 0x5f1c3807ee0787fb 0x4be38700fdc0f0ff

def z1134 : W := mkw 0x0001449520000000 0x00002892a4000000 0xe027ffffe0000003 0xdc04fffffc000000

def z1135 : W := mkw 0x084b56ddb16b6eee 0x61096adbb62d6ddd 0xf8fbffff91ff7fe7 0xff1f7ffff23feffc

def z1136 : W := mkw 0x084a10c190634442 0x41094218320c6888 0xd8dc39c7f0e787ff 0x7b1b8738fe1cf0ff

def z1137 : W := mkw 0x15a03b681bb80787 0x02b4076d037700f0 0xf7c03ff81ee00786 0x7ef807ff03dc00f0

def z1138 : W := mkw 0x084a10c190634442 0x41094218320c6888 0xd8fff1c391fff805 0xfb1ffe38723fff00

def z1139 : W := mkw 0x084b56ddb16b6eee 0x61096adbb62d6ddd 0xf8df3ffff1e7e7ff 0xff1be7fffe3cfcff

def z1140 : W := mkw 0x084b56ddb16b6eee 0x61096adbb62d6ddd 0xf8db3ffff1ffffff 0xbf1b67fffe3fffff

def z1141 : W := mkw 0x27ffedb76cd6d000 0x04fffdb6ed9ada00 0x67fbf7fb9fff7800 0xacff7eff73ffef00

def z1142 : W := mkw 0x27ffedb760002828 0x24fffdb6ec000505 0xe7ffffffe000007b 0xfcfffffffc00000f

def z1143 : W := mkw 0x084b16c591636666 0x410962d8b22c6ccc 0xffdb37c79fe76667 0xfffb66f8f3fceccc

def z1144 : W := mkw 0x15a03b681bb80787 0x02b4076d037700f0 0x77e03ff81ef80782 0x6efc07ff03df00f0

def z1145 : W := mkw 0x15a03b681bb80787 0x02b4076d037700f0 0x77e037f81ff80784 0xaefc06ff03ff00f0

def z1146 : W := mkw 0x15a03b689bb907c7 0x02b4076d137720f8 0xf7f83ffb9fff0786 0xfeff07ff73ffe0f0

def z1147 : W := mkw 0x084b56ddb16b6eee 0x61096adbb62d6ddd 0xe8fffffff1ff7e67 0xfd1ffffffe3fefcc

def z1148 : W := mkw 0x084b16c591634646 0x410962d8b22c68c8 0xe0db37c791e70607 0xbc1b66f8f23ce0c0

def z1149 : W := mkw 0x084b16cd916b66e6 0x410962d9b22d6cdc 0xe8db3fff91e767e7 0xbd1b67fff23cecfc

def z1150 : W := mkw 0x23156db766048110 0x8462adb6ecc09022 0x77043fffee00819a 0x4ee087fffdc01033

def z1151 : W := mkw 0x0001441c200828a8 0x2000288384010515 0x9827c83c6018ffff 0x5304f9078c031fff

def z1152 : W := mkw 0x15a03b681bb80787 0x02b4076d037700f0 0xe7e037f81ff80606 0xbcfc06ff03ff00c0

def z1153 : W := mkw 0x084b16c591636666 0x410962d8b22c6ccc 0x68db37c391e76664 0xad1b66f8723ceccc

def z1154 : W := mkw 0x25ebedb760000000 0x04bd7db6ec000000 0x60c03fffe0000002 0x0c1807fffc000000

def z1155 : W := mkw 0x23156db760000000 0x0462adb6ec000000 0xe73fffffe0000003 0xfce7fffffc000000

def z1156 : W := mkw 0x15a03b6adbb907d7 0x82b4076d5b7720fa 0xf7e03ffb9ff80786 0xfefc07ff73ff00f0

def z1157 : W := mkw 0x26ffc5b520000000 0x04dff8b6a4000000 0xe7fff7ff80000003 0xfcfffefff0000000

def z1158 : W := mkw 0x084b14c590634442 0x41096298b20c6888 0x60db37c390e70000 0xac1b66f8721ce000

def z1159 : W := mkw 0x15a02b680bb80387 0x02b4056d01770070 0xb7e00ff80ff80786 0xd6fc01ff01ff00f0

def z1160 : W := mkw 0x084b16c591636666 0x410962d8b22c6ccc 0xe8dff7c791e7fe67 0xbd1bfef8f23cffcc

def z1161 : W := mkw 0x06fe80000cd6d000 0x00dfd000019ada00 0xbfffce381ffff807 0xf7fff9c703ffff00

def z1162 : W := mkw 0x03143802d6058550 0x806287005ac0b0aa 0xd7183807fe0707fe 0x7ae30700ffc0e0ff

def z1163 : W := mkw 0x225fc49760000000 0x044bf892ec000000 0xe0ffffffe0000003 0xfc1ffffffc000000

def z1164 : W := mkw 0x27ffedb760000000 0x04fffdb6ec000000 0xe7db3fffe0000003 0xbcfb67fffc000000

def z1165 : W := mkw 0x0001461c21082aac 0x200028c384210555 0x1827c83c6118fffd 0x4304f9078c231fff

def z1166 : W := mkw 0x06fe80000cd6d000 0x00dfd000019ada00 0x1fdfc0001ffff805 0x23fbf80003ffff00

def z1167 : W := mkw 0x084a12c9916b6eee 0x61094259322d6ddd 0x58d831c391fffffc 0x2b1b0638723fffff

def z1168 : W := mkw 0x27ffedb760000000 0x04fffdb6ec000000 0x67d837fb80000000 0x2cfb06ff70000000

def z1169 : W := mkw 0x27ffedb768900000 0x04fffdb6ed120000 0xe7ffffffe1f80003 0xfcfffffffc3f0000

def z1170 : W := mkw 0x15a03b681bb80787 0x02b4076d037700f0 0xf7e7fff81ff80787 0xfefcffff03ff00f0

def z1171 : W := mkw 0x084a12c191634646 0x41094258322c68c8 0xe8db37c391e76607 0xbd1b66f8723cecc0

def z1172 : W := mkw 0x21016db760000000 0x04202db6ec000000 0xe0203fffe0000002 0xdc0407fffc000000

def z1173 : W := mkw 0x084b16cd916b66e6 0x410962d9b22d6cdc 0xf8ff3ffff1ffe7ff 0xff1fe7fffe3ffcff

def z1174 : W := mkw 0x235f6db760000000 0x046bedb6ec000000 0xe7df3fffe0000003 0xfcfbe7fffc000000

def z1175 : W := mkw 0x27ffedb76c949000 0x04fffdb6ed929200 0xfffffffffe1f9807 0xffffffffffc3f300

def z1176 : W := mkw 0x27ffedb760000000 0x04fffdb6ec000000 0xefffffffe0000667 0xfdfffffffc0000cc

def z1177 : W := mkw 0x14a0036809b80287 0x0294006d01370050 0x27e007f81ff80000 0xa4fc00ff03ff0000

def z1178 : W := mkw 0x084b56d5b1636666 0x41096adab62c6ccc 0xe8dff7c7f1e76667 0xbd1bfef8fe3ceccc

def z1179 : W := mkw 0x15a039601ab00503 0x02b4072c035600a0 0xf7e03ff81ff80006 0xfefc07ff03ff0000

def z1180 : W := mkw 0x27ffada740000000 0x04fff5b4e8000000 0xe7fb3fff80000003 0xfcff67fff0000000

def z1181 : W := mkw 0x03143842d6258552 0x806287085ac4b0aa 0xdfdc39c7fee787ff 0x7bfb8738ffdcf0ff

def z1182 : W := mkw 0x084b14c590636462 0x41096298b20c6c8c 0xe8db37c790e76063 0xbd1b66f8f21cec0c

def z1183 : W := mkw 0x27ffedb760000000 0x04fffdb6ec000000 0x67e7ffffe0000002 0xccfcfffffc000000

def z1184 : W := mkw 0x03143802d6058550 0x806287005ac0b0aa 0xdf1ff807fe07ffff 0x7be3ff00ffc0ffff

def z1185 : W := mkw 0x084b16c591636666 0x410962d8b22c6ccc 0x68db37c781e76663 0x8d1b66f8f03ceccc

def z1186 : W := mkw 0x084a10c190634442 0x41094218320c6888 0xc0db31c390e70001 0xb81b6638721ce000

def z1187 : W := mkw 0x04ea000008d24000 0x009d4000011a4800 0x9fffc0001ffff805 0xf3fff80003ffff00

def z1188 : W := mkw 0x15a0bb681bb81787 0x02b4176d037702f0 0xf7e0fff81ff81f86 0xfefc1fff03ff03f0

def z1189 : W := mkw 0x25eb6db760000000 0x04bd6db6ec000000 0xe7fb3fffe0000003 0xfcff67fffc000000

def z1190 : W := mkw 0x27ffedb764048000 0x04fffdb6ec809000 0xefffffffe0078003 0xfdfffffffc00f000

def z1191 : W := mkw 0x27ffedb768d25000 0x04fffdb6ed1a4a00 0xeffffffff1ff7807 0xfdfffffffe3fef00

def z1192 : W := mkw 0x15a03b681bb80787 0x02b4076d037700f0 0xffe03ffc1ff807e7 0xfffc07ff83ff00fc

def z1193 : W := mkw 0x03143802d6058550 0x806287005ac0b0aa 0xcf183807fe0707ff 0x39e30700ffc0e0ff

def z1194 : W := mkw 0x17b42b2a4f9c8395 0x82f6856549f39072 0xbf240e3c6f1887ff 0xd7e481c78de310ff

def z1195 : W := mkw 0x27ffedb762000100 0x04fffdb6ec400020 0xf7ffffffee000183 0xfefffffffdc00030

def z1196 : W := mkw 0x27ffedb768d25000 0x04fffdb6ed1a4a00 0xf7fffffffff87807 0xfeffffffffff0f00

def z1197 : W := mkw 0x15a03b681bb80787 0x02b4076d037700f0 0xffe7fffc7ff8ffff 0xfffcffff8fff1fff

def z1198 : W := mkw 0x03143802d6058550 0x806287005ac0b0aa 0x1f1c0807fe0787fd 0x43e38100ffc0f0ff

def z1199 : W := mkw 0x084b06c581636266 0x410960d8b02c6c4c 0xe8db37c781e76063 0xbd1b66f8f03cec0c

def z1200 : W := mkw 0x084b16c591636666 0x410962d8b22c6ccc 0x68db37c791e76061 0xad1b66f8f23cec0c

def z1201 : W := mkw 0x084b14c590634442 0x41096298b20c6888 0xe8db37c790e70667 0xbd1b66f8f21ce0cc

def z1202 : W := mkw 0x0000020801080284 0x0000004100210050 0xb827ce3c6118ffff 0xd704f9c78c231fff

def z1203 : W := mkw 0x1800124899fb66e7 0x43000249133f6cdc 0x0800000011ff6664 0x01000000023feccc

def z1204 : W := mkw 0x235fedb76446d000 0x046bfdb6ec88da00 0x681fffffe007f803 0x0d03fffffc00ff00

def z1205 : W := mkw 0x01012da500000000 0x002025b4a0000000 0x60003fff80000002 0x0c0007fff0000000

def z1206 : W := mkw 0x084a10c190634442 0x41094218320c6888 0xc8db31c791e76667 0xb91b6638f23ceccc

def z1207 : W := mkw 0x27fea9a340000000 0x04ffd53468000000 0x67f837fb80000000 0xacff06ff70000000

def z1208 : W := mkw 0x084b56d5b1636666 0x41096adab62c6ccc 0xf8fffffff1e7e7ff 0xff1ffffffe3cfcff

def z1209 : W := mkw 0x15a03b6a5bb80797 0x82b4076d4b7700f2 0xf7e03ff87ff8079e 0xfefc07ff0fff00f3

def z1210 : W := mkw 0x0001461c21082aac 0x200028c384210555 0x3827ce386118fffc 0xc704f9c70c231fff

def z1211 : W := mkw 0x23156db764048000 0x0462adb6ec809000 0xff1c3ffffe078007 0x7fe387ffffc0f000

def z1212 : W := mkw 0x180012489bb927e7 0x43000249137724fc 0x100000001ff807e4 0x0200000003ff00fc

def z1213 : W := mkw 0x084b56ddb16b6eee 0x61096adbb62d6ddd 0xf8dff7c7f1ffffff 0xbf1bfef8fe3fffff

def z1214 : W := mkw 0x100012489fbd87d7 0x8200024913f7b0fa 0x100000001fff0784 0x0200000003ffe0f0

def z1215 : W := mkw 0x03143802d6058550 0x806287005ac0b0aa 0x571c3807fe0787fa 0x6ae38700ffc0f0ff

def z1216 : W := mkw 0x15a03b681bb827a7 0x02b4076d037704f4 0xffe03ff81ff867e6 0xfffc07ff03ff0cfc

def z1217 : W := mkw 0x014b2da500000000 0x002965b4a0000000 0xe0db3fff80000003 0xbc1b67fff0000000

def z1218 : W := mkw 0x03143802d6058550 0x806287005ac0b0aa 0xffdc3fc7fe0787ff 0xfffb87f8ffc0f0ff

def z1219 : W := mkw 0x06fe80000cd6d000 0x00dfd000019ada00 0x9fffc0047ffff87d 0xf3fff8008fffff0f

def z1220 : W := mkw 0x21016db760000000 0x04202db6ec000000 0x60003fffe00007fa 0x0c0007fffc0000ff

def z1221 : W := mkw 0x084b16c591636666 0x410962d8b22c6ccc 0xe8fb3fff91e76667 0xfd1f67fff23ceccc

def z1222 : W := mkw 0x021400000cd6d000 0x00428000019ada00 0x9f3fc0001ffff805 0xf3e7f80003ffff00

def z1223 : W := mkw 0x27ffedb760000000 0x04fffdb6ec000000 0xf7ffffffe1180007 0xfefffffffc230000

def z1224 : W := mkw 0x084b16c591636666 0x410962d8b22c6ccc 0xe0db37c391e76606 0xbc1b66f8723cecc0

def z1225 : W := mkw 0x084b16cd916b6eee 0x610962d9b22d6ddd 0xe8db37c791ff7e67 0xbd1b66f8f23fefcc

def z1226 : W := mkw 0x204b45b520000000 0x040968b6a4000000 0xe0db37ff80000003 0xbc1b66fff0000000

def z1227 : W := mkw 0x16b412489fbd87d7 0x82d6824913f7b0fa 0x9ffc00001fff87fd 0xf3ff800003fff0ff

def z1228 : W := mkw 0x27ffedb760000000 0x04fffdb6ec000000 0xefffffffe1006007 0xfdfffffffc200c00

def z1229 : W := mkw 0x27ffedb760000000 0x04fffdb6ec000000 0xe7f83fffe0000002 0xfcff07fffc000000

def z1230 : W := mkw 0x21016db760000000 0x04202db6ec000000 0x6023ffffe0000002 0x8c047ffffc000000

def z1231 : W := mkw 0x27ffedb76446c000 0x04fffdb6ec88d800 0xffffffffffe7e007 0xfffffffffffcfc00

def z1232 : W := mkw 0x0001461c21082aac 0x200028c384210555 0xf8e7fffc6118ffff 0xff1cffff8c231fff

def z1233 : W := mkw 0x06ffc4952cd6d000 0x00dff892a59ada00 0xfffffffffffff807 0xffffffffffffff00

def z1234 : W := mkw 0x27ffedb762000110 0x84fffdb6ec400022 0xe7ffffffe000019b 0xfcfffffffc000033

def z1235 : W := mkw 0x14a0036809b80287 0x0294006d01370050 0xb7e00ff81ff80786 0xf6fc01ff03ff00f0

def z1236 : W := mkw 0x25a16db760000000 0x04b42db6ec000000 0x67c03fffe0000002 0x2cf807fffc000000

def z1237 : W := mkw 0x17b4292a4e9c8191 0x82f6852549d39032 0x172008380e180180 0x42e4010701c30030

def z1238 : W := mkw 0x084b16c591636666 0x410962d8b22c6ccc 0x68db37c790e76663 0x2d1b66f8f21ceccc

def z1239 : W := mkw 0x24ebc5b528d25000 0x049d78b6a51a4a00 0xe8fbf7ff91ff7807 0xbd1f7efff23fef00

def z1240 : W := mkw 0x27ffedb760000000 0x04fffdb6ec000000 0x673fffffe0000003 0x4ce7fffffc000000

def z1241 : W := mkw 0x06fe80000cd6d000 0x00dfd000019ada00 0x9fffc0041ffffe67 0xf3fff80083ffffcc

def z1242 : W := mkw 0x03143802d6058550 0x806287005ac0b0aa 0x4f1c3807fe0787fb 0x29e38700ffc0f0ff

def z1243 : W := mkw 0x25ebedb760000000 0x04bd7db6ec000000 0xe0e7ffffe0000003 0xdc1cfffffc000000

def z1244 : W := mkw 0x17b429224e948111 0x82f6852449d29022 0x170408006e008198 0x42e081000dc01033

def z1245 : W := mkw 0x06fe80000cd6d000 0x00dfd000019ada00 0x0fffc0001ffff801 0xa1fff80003ffff00

def z1246 : W := mkw 0x15a03b681bb80787 0x02b4076d037700f0 0xe7e03ff81ff80002 0xfcfc07ff03ff0000

def z1247 : W := mkw 0x15a03b681bb80787 0x02b4076d037700f0 0xffe33ff81ff86787 0xfffc67ff03ff0cf0

def z1248 : W := mkw 0x084b16cd916b6eee 0x610962d9b22d6ddd 0xf8fb3fff91ffffff 0xff1f67fff23fffff

def z1249 : W := mkw 0x15a039601ab00503 0x02b4072c035600a0 0xf7e03ff81ee00786 0xfefc07ff03dc00f0

def z1250 : W := mkw 0x084b56d5b1636e6e 0x61096adab62c6dcd 0xe8dbf7c791e77e67 0xbd1b7ef8f23cefcc

def z1251 : W := mkw 0x27fea9a340000000 0x04ffd53468000000 0xe7fffffb80000003 0xfcffffff70000000

def z1252 : W := mkw 0x080116c591212666 0x410022d8b22424cc 0xe8d837c791e70667 0xbd1b06f8f23ce0cc

def z1253 : W := mkw 0x27ffedb760000000 0x04fffdb6ec000000 0xe7fff7fb80000001 0xfcfffeff70000000

def z1254 : W := mkw 0x235fedb760000000 0x046bfdb6ec000000 0xe71fffffe0000003 0x7ce3fffffc000000

def z1255 : W := mkw 0x084b16c591636666 0x410962d8b22c6ccc 0xe0db37c791e76003 0xbc1b66f8f23cec00

def z1256 : W := mkw 0x084b56ddb16b6eee 0x61096adbb62d6ddd 0xf8fb3ffff1ff67ff 0xff1f67fffe3fecff

def z1257 : W := mkw 0x100012489fffd7d7 0x8200024913fffafa 0x180000001ffffffc 0x0300000003ffffff

def z1258 : W := mkw 0x27ffedb768900000 0x04fffdb6ed120000 0xf7ffffffee180003 0xfefffffffdc30000

def z1259 : W := mkw 0x25a16db768900000 0x04b42db6ed120000 0xf7e03ffffff80006 0xfefc07ffffff0000

def z1260 : W := mkw 0x084b56d5b1636e6e 0x61096adab62c6dcd 0xf8fff7c7f1fffe7f 0xff1ffef8fe3fffcf

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z8,z5,z6]),(0,[z1,z7,z3,z9,z4,z5,z6]),(1,[z1,z7,z3,z10,z5,z11]),(0,[z12,z1,z7,z3,z13,z5,z6]),(0,[z1,z7,z3,z4,z5,z14,z6])],[(0,[z15,z16,z7,z3,z4,z5,z6]),(0,[z17,z1,z7,z3,z18,z5,z6]),(0,[z1,z7,z3,z4,z5,z19,z6]),(1,[z1,z20,z7,z3,z5,z21]),(0,[z1,z7,z22,z3,z4,z5,z21]),(0,[z23,z1,z7,z3,z4,z5,z6])],[(1,[z1,z7,z3,z4,z24,z6]),(0,[z1,z7,z3,z25,z4,z5,z6]),(0,[z1,z7,z3,z10,z5,z6,z21]),(0,[z1,z7,z3,z4,z5,z6,z26]),(0,[z1,z27,z7,z3,z4,z5,z28]),(0,[z29,z1,z7,z3,z4,z5,z6])],[(1,[z1,z7,z3,z4,z30,z6]),(0,[z1,z7,z31,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z32,z21])],[(1,[z33,z7,z9,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z34,z6]),(0,[z1,z7,z3,z4,z35,z5,z6]),(0,[z1,z36,z7,z3,z4,z5,z6]),(0,[z1,z37,z7,z3,z4,z5,z6]),(0,[z1,z38,z7,z3,z4,z5,z39]),(0,[z1,z7,z40,z3,z4,z5,z41]),(0,[z42,z1,z7,z3,z4,z5,z6])],[(0,[z1,z7,z43,z3,z4,z5,z21]),(1,[z1,z7,z3,z18,z5,z11]),(0,[z1,z44,z7,z3,z10,z5,z6]),(0,[z7,z3,z4,z45,z5,z46,z6]),(0,[z1,z7,z3,z47,z4,z5,z6]),(0,[z1,z7,z48,z3,z4,z5,z49]),(0,[z1,z50,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z5,z51,z6,z21]),(0,[z1,z7,z40,z3,z52,z4,z5])],[(0,[z1,z53,z7,z3,z18,z5,z6]),(0,[z54,z1,z7,z3,z18,z5,z6]),(0,[z1,z7,z55,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z56,z6]),(0,[z1,z7,z57,z3,z4,z5,z58]),(0,[z1,z59,z7,z3,z4,z5,z21]),(0,[z1,z7,z3,z60,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z61,z11]),(0,[z1,z7,z3,z4,z5,z6,z62])],[(0,[z1,z63,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z64,z6]),(0,[z1,z7,z3,z4,z5,z65,z6]),(0,[z1,z7,z3,z66,z4,z5,z6]),(0,[z1,z7,z40,z3,z4,z5,z67])]],
   [[(0,[z1,z68,z2,z3,z4,z5,z6]),(0,[z1,z69,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z70]),(0,[z1,z7,z71,z3,z4,z5,z6])],[(0,[z1,z7,z3,z4,z72,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z73]),(0,[z1,z74,z7,z3,z18,z5,z6]),(0,[z1,z7,z3,z4,z75,z5,z6]),(0,[z1,z76,z7,z3,z4,z5,z6]),(0,[z77,z1,z7,z3,z4,z5,z21]),(0,[z1,z78,z7,z3,z4,z5,z11]),(0,[z1,z7,z3,z4,z5,z6,z79]),(0,[z1,z7,z3,z4,z5,z80,z6]),(0,[z1,z7,z3,z4,z5,z81,z6])],[(0,[z1,z82,z7,z3,z4,z5,z6]),(0,[z1,z44,z7,z3,z18,z5,z6]),(0,[z1,z7,z3,z83,z4,z5,z6]),(0,[z1,z7,z3,z84,z4,z5,z6]),(0,[z1,z68,z7,z3,z4,z85,z6]),(0,[z1,z7,z3,z4,z5,z86,z6]),(0,[z1,z87,z7,z3,z4,z5,z6])],[(0,[z1,z7,z3,z88,z4,z18,z5]),(0,[z1,z7,z3,z89,z10,z5,z6]),(0,[z90,z1,z7,z3,z4,z5,z6]),(0,[z1,z91,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z92,z5,z6])],[(0,[z1,z7,z3,z10,z5,z6,z41]),(0,[z1,z7,z93,z3,z4,z5,z6])],[(0,[z94,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z39,z21]),(0,[z1,z7,z3,z4,z5,z11,z95])],[(0,[z1,z7,z3,z4,z96,z5,z6]),(0,[z1,z7,z3,z18,z5,z6,z97]),(0,[z1,z7,z3,z18,z98,z5,z6]),(1,[z99,z7,z3,z4,z5,z97]),(0,[z100,z1,z7,z3,z4,z5,z6]),(1,[z1,z7,z3,z4,z5,z101]),(0,[z1,z7,z3,z4,z102,z5,z6]),(1,[z1,z59,z7,z4,z103,z6]),(0,[z1,z7,z3,z4,z5,z11,z39])],[(0,[z0,z1,z7,z3,z4,z5,z6]),(0,[z104,z1,z7,z3,z4,z5,z6]),(0,[z105,z1,z7,z3,z18,z5,z6]),(0,[z1,z106,z7,z3,z4,z5,z6])]],
   [[(0,[z1,z7,z3,z4,z107,z5,z6]),(0,[z33,z1,z7,z3,z4,z5,z108]),(0,[z1,z38,z7,z3,z4,z5,z11])],[(0,[z0,z7,z2,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z109]),(0,[z33,z1,z110,z3,z4,z5,z6]),(0,[z1,z111,z7,z3,z4,z5,z6]),(0,[z17,z12,z7,z3,z4,z5,z6]),(0,[z1,z112,z7,z3,z4,z5,z11]),(0,[z1,z7,z3,z4,z113,z5,z6]),(1,[z1,z7,z4,z5,z11,z21])],[(0,[z1,z7,z3,z114,z4,z5,z6])],[(0,[z1,z7,z115,z3,z4,z5,z6]),(1,[z1,z7,z3,z25,z5,z6]),(0,[z7,z3,z10,z4,z18,z5,z6]),(0,[z77,z1,z7,z3,z4,z30,z6]),(0,[z1,z116,z7,z3,z4,z5,z21])],[(0,[z117,z1,z7,z3,z4,z5,z6]),(0,[z1,z118,z7,z3,z4,z5,z6]),(0,[z17,z1,z7,z3,z4,z5,z6]),(0,[z1,z119,z7,z3,z4,z5,z6])],[(0,[z0,z1,z7,z3,z4,z120,z6]),(0,[z1,z121,z7,z3,z10,z5,z6]),(0,[z1,z122,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z123,z5,z6]),(0,[z1,z7,z3,z52,z4,z5,z39])],[(1,[z1,z7,z3,z88,z4,z5]),(0,[z124,z1,z7,z3,z10,z5,z6]),(0,[z1,z7,z3,z4,z5,z125,z6]),(0,[z126,z1,z7,z3,z4,z5,z6])],[(0,[z127,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z128,z6]),(0,[z1,z7,z3,z129,z4,z5,z6]),(0,[z1,z7,z3,z4,z130,z5,z6]),(0,[z1,z7,z3,z4,z5,z131,z6])]],
   [[(0,[z1,z16,z7,z3,z4,z5,z21]),(0,[z1,z7,z3,z4,z5,z132,z6]),(0,[z1,z7,z3,z133,z10,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z134]),(0,[z135,z1,z7,z3,z4,z5,z6])],[(0,[z1,z1,z7,z3,z10,z5,z6]),(0,[z1,z7,z3,z4,z5,z136,z6]),(0,[z1,z137,z7,z3,z4,z5,z6]),(0,[z1,z138,z7,z3,z4,z5,z6]),(0,[z54,z1,z7,z3,z4,z5,z6])],[(0,[z99,z1,z7,z3,z4,z5,z11]),(0,[z1,z20,z7,z3,z4,z5,z21]),(0,[z1,z7,z3,z4,z32,z6,z21]),(0,[z1,z7,z3,z4,z5,z11,z11]),(0,[z1,z38,z7,z40,z3,z4,z5])],[(0,[z1,z139,z7,z3,z4,z5,z6]),(0,[z140,z1,z7,z3,z25,z5,z6]),(0,[z1,z7,z3,z4,z5,z141,z6])],[(0,[z1,z74,z7,z3,z4,z5,z6]),(0,[z1,z142,z7,z3,z4,z5,z6]),(0,[z1,z143,z7,z3,z4,z5,z6]),(0,[z1,z144,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z145,z5,z6]),(0,[z1,z7,z3,z4,z146,z147,z6]),(0,[z1,z7,z3,z148,z4,z5,z6]),(0,[z1,z7,z149,z3,z4,z5,z11])],[(0,[z1,z16,z3,z150,z4,z5,z6]),(0,[z1,z151,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z10,z152,z5,z6]),(0,[z1,z7,z3,z4,z5,z153,z6]),(0,[z1,z7,z154,z3,z4,z5,z6]),(0,[z155,z1,z7,z3,z4,z5,z6])],[(0,[z15,z1,z7,z3,z4,z5,z11]),(0,[z1,z156,z7,z3,z4,z5,z6]),(0,[z1,z157,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z21,z41])],[(0,[z158,z1,z7,z3,z4,z5,z6]),(1,[z1,z7,z3,z159,z5,z6]),(0,[z33,z1,z7,z3,z4,z160,z6]),(0,[z1,z7,z3,z4,z5,z161,z6]),(0,[z1,z162,z7,z3,z4,z5,z11]),(0,[z1,z7,z3,z4,z163,z5,z6]),(0,[z1,z7,z3,z164,z4,z5,z6])]],
   [[(0,[z1,z7,z2,z3,z18,z5,z6]),(0,[z140,z1,z7,z3,z4,z5,z11]),(0,[z1,z7,z3,z4,z5,z46,z11]),(0,[z165,z99,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z166,z5,z6]),(0,[z167,z1,z7,z3,z4,z5,z21]),(0,[z1,z7,z3,z168,z4,z5,z21])],[(0,[z1,z7,z3,z4,z169,z5,z6]),(0,[z1,z7,z170,z3,z4,z5,z6]),(0,[z1,z171,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z172,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z173]),(0,[z1,z7,z3,z4,z174,z5,z6]),(0,[z1,z7,z175,z3,z4,z5,z6]),(0,[z1,z7,z3,z52,z4,z5,z11]),(0,[z1,z7,z3,z4,z5,z176,z6])],[(0,[z105,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z177,z5,z6]),(0,[z1,z7,z178,z3,z133,z5,z6]),(0,[z1,z7,z178,z3,z4,z5,z21])],[(0,[z179,z1,z7,z3,z4,z5,z21]),(0,[z1,z7,z3,z4,z180,z5,z181]),(0,[z1,z7,z3,z4,z5,z182,z6])],[(0,[z1,z7,z3,z4,z5,z183,z6]),(1,[z1,z7,z3,z10,z5,z21]),(0,[z1,z7,z184,z3,z4,z5,z6]),(0,[z1,z7,z3,z185,z4,z5,z6]),(0,[z1,z27,z7,z3,z4,z5,z11]),(0,[z1,z59,z7,z3,z4,z67,z6])],[(0,[z15,z1,z7,z3,z159,z5,z6]),(1,[z1,z7,z3,z186,z5,z6]),(0,[z1,z7,z187,z3,z4,z5,z6]),(0,[z1,z7,z3,z188,z4,z5,z6]),(0,[z189,z1,z7,z3,z4,z5,z6]),(0,[z1,z59,z7,z57,z4,z5,z6]),(0,[z1,z7,z3,z4,z190,z5,z6]),(0,[z1,z7,z3,z4,z5,z191,z6]),(0,[z1,z7,z192,z3,z4,z5,z6])],[(0,[z1,z7,z3,z193,z4,z5,z6]),(0,[z1,z7,z3,z4,z194,z5,z6]),(0,[z1,z7,z3,z195,z4,z5,z6]),(0,[z1,z7,z3,z196,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z197,z6]),(0,[z198,z1,z7,z3,z4,z5,z11])],[(0,[z199,z1,z7,z3,z4,z5,z6]),(0,[z200,z1,z7,z3,z4,z5,z6]),(0,[z201,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z10,z5,z6,z202]),(0,[z1,z7,z3,z4,z5,z203,z6]),(0,[z1,z204,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z205,z6])]],
   [[(0,[z179,z7,z3,z4,z18,z5,z6]),(1,[z1,z7,z3,z4,z206,z6]),(0,[z1,z7,z207,z3,z4,z5,z6]),(1,[z1,z7,z3,z4,z208,z6]),(0,[z1,z7,z3,z4,z5,z209,z6]),(0,[z1,z7,z3,z4,z210,z5,z6]),(0,[z1,z7,z3,z4,z5,z211,z6])],[(0,[z212,z1,z7,z3,z18,z5,z6]),(0,[z165,z1,z7,z3,z4,z5,z97]),(0,[z1,z7,z3,z4,z5,z213,z6]),(0,[z1,z68,z7,z48,z4,z5,z6]),(0,[z1,z214,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z215,z6])],[(0,[z1,z7,z3,z216,z18,z5,z6]),(0,[z217,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z218]),(0,[z1,z7,z178,z3,z5,z39,z6]),(0,[z1,z219,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z220]),(0,[z1,z7,z3,z221,z4,z5,z6]),(0,[z222,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z223])],[(0,[z1,z7,z3,z9,z10,z5,z6]),(0,[z1,z7,z3,z10,z45,z5,z6]),(0,[z12,z7,z3,z4,z45,z5,z6]),(0,[z1,z7,z3,z224,z4,z5,z6]),(0,[z225,z1,z7,z3,z4,z180,z5]),(0,[z226,z1,z7,z3,z4,z5,z6])],[(1,[z1,z7,z3,z227,z5,z6]),(0,[z1,z7,z3,z18,z5,z46,z6]),(0,[z1,z7,z3,z4,z228,z5,z6]),(0,[z1,z7,z3,z229,z4,z5,z6])],[(0,[z1,z7,z3,z4,z5,z6,z230]),(0,[z1,z7,z3,z4,z5,z231,z6]),(0,[z232,z1,z7,z3,z4,z5,z6]),(0,[z1,z162,z7,z3,z4,z233,z6]),(0,[z1,z7,z3,z4,z5,z67,z21])],[(0,[z1,z234,z7,z3,z4,z5,z6]),(0,[z1,z7,z48,z3,z4,z5,z11])],[(0,[z235,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z236,z3,z4,z5,z6]),(0,[z12,z1,z7,z3,z4,z46,z6]),(0,[z1,z7,z40,z3,z4,z46,z6]),(0,[z1,z7,z3,z4,z5,z6,z237]),(0,[z1,z7,z3,z238,z4,z5,z6])]],
   [[(0,[z1,z7,z3,z186,z4,z5,z6]),(0,[z1,z162,z3,z4,z5,z147,z6]),(1,[z1,z7,z3,z185,z4,z5]),(0,[z1,z7,z239,z3,z4,z5,z6]),(1,[z1,z116,z3,z4,z5,z218]),(0,[z1,z7,z3,z4,z240,z5,z11])],[(0,[z241,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z242,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z180,z5,z6])],[(0,[z243,z1,z7,z3,z4,z5,z6])],[(0,[z1,z7,z2,z3,z4,z5,z6]),(0,[z1,z7,z244,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z147,z11]),(0,[z1,z7,z3,z4,z5,z245,z6]),(0,[z1,z20,z7,z3,z5,z6,z21])],[(0,[z246,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z247,z6]),(1,[z1,z7,z3,z5,z51,z21]),(0,[z1,z38,z7,z3,z4,z5,z21])],[(0,[z248,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z249,z5,z6]),(0,[z1,z112,z7,z3,z4,z5,z21]),(0,[z1,z7,z57,z3,z4,z5,z11]),(0,[z1,z7,z3,z4,z5,z250,z6]),(1,[z1,z7,z22,z3,z4,z6])],[(1,[z1,z7,z3,z4,z5,z251]),(0,[z252,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z168,z18,z5,z6]),(0,[z1,z7,z3,z10,z5,z181,z6]),(0,[z1,z7,z3,z253,z4,z5,z6]),(1,[z1,z7,z3,z4,z254,z6]),(0,[z1,z255,z7,z3,z4,z5,z11])],[(0,[z1,z256,z7,z3,z4,z5,z6]),(0,[z1,z44,z7,z3,z4,z5,z209]),(0,[z1,z7,z3,z4,z5,z6,z58]),(0,[z1,z7,z3,z4,z5,z257,z6]),(0,[z1,z7,z3,z4,z5,z6,z258]),(0,[z1,z7,z3,z4,z5,z259,z6])]],
   [[(0,[z33,z1,z7,z9,z4,z5,z6]),(0,[z1,z7,z3,z18,z5,z39,z6]),(0,[z77,z1,z7,z3,z4,z208,z6]),(0,[z212,z1,z7,z3,z4,z146,z6])],[(0,[z260,z1,z7,z3,z4,z5,z6]),(0,[z261,z1,z7,z3,z4,z5,z21])],[(0,[z0,z1,z7,z3,z4,z5,z183]),(0,[z0,z1,z7,z3,z10,z5,z6]),(0,[z1,z7,z3,z18,z262,z5,z6]),(0,[z1,z7,z3,z4,z18,z5,z11]),(0,[z1,z112,z3,z150,z4,z5,z6]),(0,[z1,z263,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z264,z4,z5,z11]),(0,[z1,z265,z7,z3,z4,z5,z6])],[(0,[z266,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z10,z5,z147,z6])],[(0,[z1,z7,z3,z4,z5,z160,z6]),(0,[z1,z7,z3,z4,z5,z6,z108]),(0,[z1,z111,z7,z3,z10,z5,z6]),(0,[z267,z1,z7,z3,z4,z5,z6]),(0,[z212,z1,z7,z3,z4,z5,z6])],[(0,[z1,z7,z3,z216,z4,z5,z6]),(0,[z1,z7,z3,z114,z10,z5,z6]),(0,[z1,z7,z3,z4,z5,z268,z97]),(0,[z1,z7,z3,z4,z5,z6,z49]),(0,[z1,z7,z3,z4,z269,z5,z6]),(0,[z270,z1,z7,z3,z4,z5,z6])],[(0,[z271,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z272,z3,z4,z5,z6]),(0,[z99,z1,z7,z3,z4,z5,z21]),(0,[z273,z1,z7,z3,z5,z147,z6]),(0,[z1,z7,z3,z4,z5,z11,z21])],[(0,[z17,z1,z7,z3,z10,z5,z6]),(0,[z1,z118,z7,z3,z10,z5,z6]),(0,[z1,z7,z3,z4,z5,z274,z6]),(0,[z275,z1,z7,z3,z4,z5,z6]),(0,[z1,z276,z7,z3,z4,z5,z6]),(0,[z277,z1,z7,z3,z4,z5,z11]),(0,[z1,z7,z3,z4,z278,z5,z6])]],
   [[(1,[z1,z7,z3,z279,z5,z6]),(0,[z1,z7,z3,z4,z5,z280,z6]),(0,[z1,z7,z149,z3,z4,z5,z21])],[(0,[z281,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z282,z4,z5,z6]),(1,[z1,z7,z3,z4,z5,z283])],[(0,[z0,z1,z7,z3,z107,z5,z6]),(0,[z1,z7,z3,z10,z18,z5,z6]),(0,[z1,z7,z3,z4,z5,z284,z6]),(0,[z1,z7,z3,z4,z285,z5,z6])],[(0,[z1,z7,z3,z4,z5,z286,z6]),(0,[z1,z7,z3,z287,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z288]),(1,[z1,z112,z150,z4,z5,z6]),(0,[z1,z162,z7,z3,z4,z5,z21]),(0,[z1,z7,z57,z3,z4,z233,z6]),(0,[z1,z7,z133,z4,z152,z5,z6]),(0,[z1,z289,z7,z3,z4,z5,z6])],[(0,[z140,z1,z7,z3,z4,z5,z21]),(0,[z1,z7,z3,z4,z5,z6,z290]),(0,[z54,z1,z7,z3,z10,z5,z6]),(0,[z1,z7,z3,z4,z5,z46,z21]),(1,[z12,z7,z3,z4,z45,z6]),(0,[z1,z68,z7,z3,z4,z5,z11]),(0,[z1,z255,z7,z3,z4,z233,z6]),(0,[z1,z7,z3,z4,z291,z5,z6]),(0,[z1,z7,z3,z292,z4,z5,z6])],[(0,[z1,z7,z293,z3,z4,z5,z6]),(1,[z77,z1,z3,z98,z5,z6]),(0,[z294,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z52,z4,z5,z21]),(0,[z1,z7,z3,z3,z4,z5,z11])],[(0,[z1,z7,z110,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z295,z5,z6]),(0,[z1,z68,z7,z3,z4,z125,z6]),(0,[z1,z7,z296,z3,z4,z5,z6]),(0,[z1,z7,z3,z297,z4,z5,z6])],[(0,[z1,z7,z3,z298,z4,z5,z6]),(1,[z1,z7,z3,z4,z5,z299]),(0,[z1,z7,z3,z300,z4,z5,z6]),(0,[z1,z7,z3,z4,z45,z5,z21]),(0,[z1,z301,z7,z3,z4,z5,z6]),(0,[z1,z7,z4,z103,z5,z302,z6])]],
   [[(1,[z1,z303,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z304,z5,z6]),(0,[z12,z1,z7,z3,z4,z45,z6]),(0,[z1,z7,z40,z3,z4,z45,z6]),(0,[z1,z27,z7,z3,z133,z5,z6]),(0,[z1,z27,z7,z3,z4,z5,z21]),(0,[z1,z7,z3,z4,z5,z11,z41])],[(0,[z305,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z75,z18,z5,z6]),(0,[z1,z7,z3,z4,z5,z306,z6]),(0,[z99,z1,z7,z3,z52,z4,z5]),(0,[z1,z7,z3,z4,z5,z6,z307]),(0,[z1,z7,z3,z168,z4,z5,z6]),(0,[z1,z308,z7,z3,z4,z5,z6])],[(0,[z33,z1,z7,z3,z4,z8,z6]),(0,[z1,z38,z7,z3,z18,z5,z6]),(1,[z1,z162,z3,z4,z147,z6]),(0,[z1,z7,z3,z309,z4,z5,z6])],[(0,[z1,z7,z3,z310,z4,z5,z6]),(0,[z1,z7,z3,z150,z4,z5,z11]),(0,[z311,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z11,z67])],[(1,[z179,z7,z3,z18,z5,z6]),(1,[z165,z7,z3,z4,z5,z181]),(0,[z1,z44,z7,z3,z98,z5,z6]),(0,[z1,z44,z7,z3,z312,z5,z6]),(0,[z225,z1,z3,z4,z5,z268,z6]),(0,[z1,z7,z3,z4,z313,z5,z6]),(1,[z1,z7,z178,z133,z5,z6]),(0,[z1,z314,z7,z3,z4,z5,z11])],[(0,[z1,z7,z3,z4,z315,z5,z6]),(0,[z1,z7,z316,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z317]),(0,[z1,z7,z3,z52,z5,z39,z6])],[(0,[z1,z7,z3,z4,z318,z5,z6]),(0,[z1,z319,z7,z3,z4,z5,z6])],[(1,[z1,z7,z320,z4,z5,z6]),(1,[z1,z7,z3,z321,z5,z6]),(0,[z322,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z323,z6]),(0,[z1,z7,z3,z4,z5,z6,z97]),(0,[z1,z7,z3,z4,z98,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z324])]],
   [[(1,[z1,z74,z7,z3,z18,z5]),(0,[z325,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z326,z6]),(0,[z1,z7,z3,z327,z4,z5,z6]),(0,[z1,z27,z7,z3,z5,z39,z6]),(0,[z1,z7,z3,z4,z328,z5,z6]),(0,[z329,z1,z7,z3,z4,z5,z6])],[(0,[z0,z15,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z330,z4,z5,z6]),(0,[z1,z7,z3,z195,z10,z5,z6]),(0,[z1,z7,z3,z4,z5,z331,z6]),(0,[z1,z7,z3,z4,z5,z6,z332])],[(0,[z333,z1,z7,z3,z4,z5,z6]),(1,[z1,z7,z3,z18,z5,z6]),(0,[z124,z7,z3,z10,z4,z5,z6]),(0,[z1,z7,z3,z10,z5,z153,z6]),(0,[z334,z1,z7,z3,z4,z5,z6]),(0,[z1,z48,z3,z150,z4,z5,z6]),(0,[z1,z7,z48,z3,z4,z5,z21]),(0,[z1,z7,z3,z4,z335,z5,z6]),(0,[z1,z7,z3,z312,z4,z5,z11]),(0,[z212,z1,z7,z3,z168,z5,z6])],[(0,[z1,z7,z43,z3,z4,z5,z299]),(0,[z12,z1,z7,z3,z18,z5,z6]),(0,[z1,z7,z40,z3,z18,z5,z6]),(0,[z1,z7,z3,z4,z336,z5,z6]),(0,[z1,z337,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z338]),(0,[z1,z7,z22,z3,z4,z6,z21]),(0,[z339,z1,z7,z3,z4,z5,z6]),(0,[z340,z1,z7,z3,z4,z5,z6]),(0,[z341,z1,z7,z3,z4,z5,z6])],[(0,[z1,z7,z342,z3,z4,z5,z6]),(0,[z1,z343,z7,z3,z4,z5,z6]),(0,[z225,z1,z7,z3,z18,z5,z6]),(0,[z1,z74,z7,z3,z4,z18,z5]),(0,[z1,z344,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z345,z6])],[(0,[z1,z7,z3,z10,z4,z5,z6])],[(0,[z1,z7,z178,z3,z152,z5,z6]),(0,[z1,z7,z346,z3,z4,z5,z6]),(0,[z1,z7,z40,z3,z4,z6,z41])],[(0,[z1,z7,z3,z321,z4,z5,z6]),(0,[z1,z347,z7,z3,z4,z5,z6]),(0,[z1,z348,z7,z3,z4,z5,z6]),(0,[z349,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z350,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z147,z21]),(0,[z1,z7,z3,z351,z4,z5,z6])]],
   [[(0,[z15,z1,z7,z3,z18,z5,z6]),(0,[z1,z7,z3,z18,z5,z67,z6]),(0,[z1,z7,z3,z10,z103,z5,z6]),(0,[z1,z7,z3,z4,z352,z5,z6]),(0,[z1,z7,z3,z353,z4,z5,z6]),(0,[z1,z7,z40,z3,z4,z5,z181]),(0,[z273,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z152,z5,z11])],[(1,[z0,z2,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z354,z5,z6]),(0,[z1,z7,z3,z5,z355,z147,z6]),(0,[z1,z7,z3,z356,z4,z5,z6]),(0,[z1,z7,z57,z3,z4,z5,z21]),(0,[z1,z7,z3,z4,z5,z6,z95])],[(0,[z165,z1,z38,z7,z3,z4,z5]),(0,[z1,z255,z7,z3,z4,z5,z21]),(0,[z1,z7,z3,z4,z5,z357,z6])],[(0,[z1,z7,z3,z185,z4,z5,z147])],[(0,[z15,z1,z16,z3,z4,z5,z6]),(0,[z1,z7,z3,z10,z5,z268,z6]),(0,[z1,z7,z3,z4,z5,z358,z6]),(0,[z1,z359,z7,z3,z4,z5,z6]),(1,[z1,z7,z40,z3,z4,z41])],[(0,[z360,z1,z7,z3,z4,z5,z6]),(1,[z140,z7,z43,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z361]),(0,[z1,z7,z362,z3,z4,z5,z6]),(0,[z1,z7,z363,z3,z4,z5,z6]),(0,[z1,z7,z3,z133,z4,z5,z11]),(0,[z1,z7,z3,z4,z5,z302,z11]),(0,[z1,z7,z364,z3,z4,z5,z6]),(0,[z1,z38,z7,z3,z4,z5,z6])],[(0,[z1,z7,z2,z3,z10,z5,z6]),(0,[z1,z7,z43,z3,z18,z5,z6]),(0,[z1,z7,z3,z4,z18,z5,z21]),(0,[z1,z112,z7,z3,z4,z5,z6]),(0,[z1,z7,z365,z3,z4,z5,z6]),(0,[z1,z7,z3,z366,z4,z5,z6])],[(0,[z1,z59,z7,z3,z18,z5,z6]),(0,[z1,z7,z3,z4,z367,z5,z6]),(0,[z1,z7,z3,z4,z5,z368,z6]),(0,[z1,z7,z3,z4,z5,z369,z6]),(0,[z1,z7,z370,z3,z4,z5,z6]),(0,[z1,z7,z3,z371,z4,z5,z6])]],
   [[(0,[z1,z7,z372,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z373]),(0,[z1,z374,z7,z3,z4,z5,z6])],[(0,[z1,z7,z3,z4,z227,z5,z6]),(0,[z1,z7,z3,z4,z5,z375,z6]),(0,[z1,z376,z7,z3,z4,z5,z6]),(1,[z1,z7,z57,z4,z302,z6]),(0,[z1,z7,z149,z4,z5,z6,z21]),(0,[z1,z377,z7,z3,z4,z5,z6])],[(0,[z77,z1,z7,z3,z18,z5,z6]),(0,[z1,z378,z7,z3,z4,z5,z6]),(0,[z1,z7,z379,z3,z4,z5,z6])],[(0,[z1,z380,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z381,z6]),(0,[z382,z1,z7,z3,z4,z5,z6])],[(0,[z165,z1,z7,z3,z4,z5,z21]),(0,[z1,z112,z7,z150,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z383,z6]),(0,[z1,z38,z7,z3,z4,z180,z5])],[(1,[z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z10,z5,z302,z6]),(0,[z1,z7,z3,z4,z45,z67,z6]),(0,[z1,z7,z3,z4,z5,z384,z6]),(1,[z1,z7,z3,z385,z5,z6]),(0,[z1,z7,z3,z4,z386,z5,z6]),(0,[z1,z387,z7,z3,z4,z5,z6])],[(0,[z12,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z45,z5,z11]),(0,[z1,z388,z7,z3,z4,z5,z6]),(0,[z77,z212,z1,z7,z3,z5,z6]),(0,[z389,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z390,z6]),(0,[z1,z7,z40,z3,z4,z5,z6])],[(0,[z1,z7,z3,z4,z5,z391,z6]),(0,[z212,z1,z7,z3,z10,z5,z6]),(0,[z1,z7,z3,z4,z5,z206,z6]),(0,[z1,z7,z3,z4,z5,z208,z6]),(0,[z1,z162,z255,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z392,z6]),(0,[z225,z1,z7,z3,z4,z5,z6])]],
   [[(0,[z1,z7,z3,z4,z5,z6,z393]),(0,[z1,z394,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z395,z4,z5,z6]),(0,[z1,z68,z7,z3,z4,z5,z21]),(0,[z1,z7,z3,z396,z4,z5,z6]),(0,[z1,z7,z3,z397,z4,z5,z6]),(0,[z1,z7,z398,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z399,z6])],[(0,[z1,z7,z3,z18,z5,z11,z6]),(0,[z1,z7,z272,z3,z10,z5,z6]),(0,[z1,z7,z3,z3,z4,z5,z21]),(0,[z1,z7,z3,z168,z146,z5,z6]),(0,[z1,z7,z3,z4,z5,z400,z6])],[(0,[z1,z7,z3,z4,z46,z67,z6])],[(0,[z15,z1,z7,z3,z4,z5,z6]),(1,[z1,z7,z3,z4,z120,z6]),(0,[z1,z7,z3,z4,z5,z401,z6]),(0,[z1,z7,z3,z10,z168,z5,z6]),(0,[z402,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z403])],[(0,[z404,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z405,z3,z4,z5,z6]),(0,[z1,z116,z7,z3,z18,z5,z6]),(0,[z1,z7,z3,z4,z406,z5,z6]),(0,[z1,z407,z7,z3,z4,z5,z6]),(0,[z1,z162,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z408,z6])],[(0,[z1,z7,z3,z4,z5,z46,z6]),(0,[z1,z7,z4,z5,z11,z6,z21]),(1,[z1,z20,z7,z3,z5,z6]),(0,[z1,z7,z22,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z146,z5,z11])],[(0,[z1,z7,z3,z4,z233,z5,z11]),(0,[z1,z7,z3,z409,z4,z5,z21]),(1,[z54,z1,z7,z4,z5,z11]),(0,[z1,z7,z3,z4,z5,z6,z410]),(0,[z411,z1,z7,z3,z4,z5,z6])],[(0,[z1,z7,z57,z3,z18,z5,z6]),(0,[z165,z1,z7,z3,z52,z4,z5]),(0,[z1,z7,z3,z150,z4,z5,z21]),(0,[z412,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z32,z6]),(0,[z1,z7,z3,z4,z413,z5,z6])]],
   [[(0,[z1,z7,z3,z9,z4,z5,z11]),(1,[z1,z7,z3,z4,z5,z414]),(0,[z1,z7,z3,z4,z415,z5,z6]),(0,[z1,z7,z416,z3,z4,z5,z6])],[(0,[z1,z16,z7,z3,z18,z5,z6]),(0,[z1,z7,z43,z3,z4,z5,z6]),(0,[z12,z1,z7,z3,z4,z5,z414]),(0,[z1,z7,z3,z4,z5,z6,z417]),(0,[z1,z7,z3,z4,z5,z21,z218]),(0,[z1,z7,z3,z4,z5,z21,z220])],[(0,[z1,z7,z3,z18,z45,z5,z6]),(0,[z212,z1,z44,z7,z3,z5,z6]),(0,[z1,z59,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z418,z6])],[(0,[z1,z7,z3,z4,z5,z419,z6]),(0,[z1,z7,z3,z4,z5,z420,z6]),(0,[z1,z7,z3,z4,z5,z421,z6])],[(0,[z225,z1,z7,z3,z4,z5,z268]),(0,[z1,z7,z3,z4,z5,z6,z422])],[(0,[z1,z7,z320,z3,z4,z5,z6]),(0,[z1,z7,z3,z10,z146,z5,z6]),(0,[z1,z7,z423,z3,z4,z5,z6]),(0,[z77,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z424,z4,z5,z6]),(0,[z1,z7,z3,z52,z4,z180,z5])],[(0,[z1,z7,z3,z10,z233,z5,z6]),(0,[z425,z1,z7,z3,z4,z5,z6]),(1,[z17,z7,z3,z4,z46,z6]),(0,[z1,z7,z426,z3,z4,z5,z6]),(0,[z1,z7,z3,z312,z4,z5,z21]),(0,[z1,z7,z3,z4,z5,z6,z427]),(0,[z1,z428,z7,z3,z4,z5,z6]),(0,[z1,z429,z7,z3,z4,z5,z6])],[(0,[z1,z7,z430,z3,z4,z5,z6]),(0,[z1,z7,z43,z150,z4,z5,z6]),(1,[z1,z7,z3,z431,z5,z6]),(0,[z1,z7,z57,z3,z4,z67,z6]),(0,[z432,z1,z7,z3,z4,z5,z11]),(0,[z1,z7,z3,z4,z5,z433,z6])]],
   [[(0,[z434,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z435,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z436,z21]),(0,[z1,z7,z3,z437,z4,z5,z6]),(1,[z1,z7,z93,z3,z4,z5])],[(0,[z167,z1,z7,z3,z18,z5,z6]),(0,[z1,z7,z3,z4,z438,z5,z6]),(0,[z1,z7,z3,z4,z5,z439,z6]),(0,[z1,z7,z3,z4,z440,z5,z6]),(0,[z1,z7,z3,z4,z5,z39,z6])],[(0,[z1,z7,z3,z4,z5,z441,z6]),(0,[z322,z1,z7,z3,z10,z5,z6]),(0,[z1,z7,z3,z4,z5,z442,z6])],[(0,[z1,z7,z178,z3,z18,z5,z6]),(0,[z1,z7,z3,z4,z262,z5,z6]),(0,[z1,z443,z7,z3,z4,z5,z6]),(0,[z444,z1,z7,z3,z4,z5,z6])],[(0,[z445,z1,z7,z3,z4,z5,z6]),(0,[z179,z1,z7,z3,z18,z5,z6]),(0,[z1,z7,z3,z10,z5,z34,z6]),(0,[z1,z7,z446,z3,z4,z5,z6]),(0,[z1,z27,z7,z3,z152,z5,z6]),(0,[z1,z27,z38,z7,z3,z5,z6]),(0,[z1,z7,z3,z4,z152,z5,z21])],[(0,[z33,z1,z7,z3,z4,z5,z11]),(0,[z1,z7,z3,z4,z447,z5,z6]),(0,[z1,z7,z3,z4,z5,z448,z6]),(0,[z1,z38,z7,z3,z52,z5,z6]),(0,[z1,z7,z3,z4,z5,z449,z6]),(0,[z1,z7,z3,z4,z67,z6,z41])],[(0,[z1,z7,z3,z4,z5,z6,z450]),(1,[z225,z1,z3,z4,z5,z268]),(0,[z1,z7,z3,z4,z5,z21,z258])],[(0,[z0,z1,z7,z3,z4,z5,z11]),(0,[z124,z1,z7,z3,z4,z5,z21]),(0,[z1,z7,z451,z3,z4,z5,z6]),(1,[z1,z7,z3,z4,z5,z209]),(0,[z1,z116,z7,z3,z4,z5,z6])]],
   [[(0,[z1,z7,z3,z10,z10,z5,z6])],[(0,[z0,z1,z7,z298,z4,z5,z6]),(0,[z0,z1,z7,z3,z4,z5,z393]),(0,[z1,z7,z3,z4,z5,z6,z452]),(0,[z1,z7,z3,z4,z147,z205,z6]),(0,[z1,z7,z3,z4,z233,z205,z6]),(0,[z1,z7,z3,z133,z4,z5,z21]),(0,[z453,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z302,z21])],[(0,[z1,z68,z16,z3,z4,z5,z6]),(0,[z1,z7,z3,z18,z5,z147,z6]),(0,[z77,z1,z3,z4,z98,z5,z6]),(0,[z1,z7,z57,z3,z4,z5,z6]),(0,[z1,z454,z7,z3,z4,z5,z6])],[(0,[z165,z1,z7,z3,z4,z5,z11]),(0,[z1,z7,z3,z4,z5,z455,z6]),(0,[z1,z44,z7,z3,z4,z5,z101]),(0,[z1,z7,z3,z4,z5,z456,z6])],[(0,[z1,z16,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z10,z98,z5,z6]),(0,[z17,z1,z7,z3,z4,z5,z11]),(0,[z1,z457,z7,z3,z4,z5,z6]),(1,[z1,z7,z3,z5,z355,z6]),(0,[z1,z7,z3,z458,z4,z5,z6]),(0,[z1,z27,z7,z4,z152,z5,z6]),(0,[z1,z7,z3,z4,z5,z459,z6])],[(0,[z1,z7,z3,z150,z18,z5,z6]),(0,[z1,z7,z3,z460,z4,z5,z6]),(0,[z99,z1,z7,z3,z279,z5,z6]),(0,[z1,z7,z3,z4,z5,z461,z6]),(0,[z1,z7,z3,z462,z4,z5,z6])],[(0,[z1,z463,z7,z3,z18,z5,z6]),(0,[z1,z116,z7,z3,z4,z180,z5]),(0,[z1,z20,z7,z3,z4,z5,z6]),(0,[z212,z1,z7,z3,z5,z205,z6])],[(0,[z1,z7,z464,z3,z4,z5,z6]),(1,[z1,z7,z3,z4,z5,z134])]],
   [[(0,[z1,z38,z7,z3,z10,z5,z6]),(0,[z12,z1,z7,z3,z4,z5,z134]),(0,[z1,z7,z3,z4,z5,z465,z6]),(0,[z1,z59,z7,z40,z3,z4,z6]),(0,[z1,z7,z3,z168,z4,z146,z6])],[(0,[z1,z7,z3,z18,z18,z5,z6]),(0,[z54,z1,z7,z3,z4,z5,z11])],[(0,[z33,z1,z7,z3,z186,z5,z6]),(0,[z1,z7,z3,z4,z180,z5,z97]),(0,[z1,z7,z3,z4,z5,z6,z21]),(0,[z1,z466,z7,z3,z4,z5,z6])],[(0,[z467,z1,z7,z3,z4,z5,z6]),(0,[z7,z3,z4,z5,z181,z6,z97]),(0,[z1,z162,z7,z3,z4,z147,z6]),(0,[z1,z468,z7,z3,z4,z5,z6]),(0,[z1,z469,z7,z3,z4,z5,z6]),(0,[z1,z7,z470,z3,z4,z5,z6])],[(0,[z167,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z18,z5,z6,z21]),(0,[z1,z7,z3,z4,z471,z5,z6]),(0,[z1,z3,z4,z233,z5,z147,z6]),(0,[z1,z116,z7,z3,z4,z5,z268]),(0,[z1,z7,z472,z3,z4,z5,z6])],[(0,[z473,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z474,z4,z5,z6]),(0,[z1,z7,z475,z3,z4,z5,z6]),(0,[z1,z7,z3,z476,z4,z5,z6]),(0,[z1,z44,z7,z3,z4,z5,z11]),(0,[z1,z7,z3,z146,z5,z205,z6]),(0,[z1,z7,z3,z4,z5,z477,z6])],[(0,[z1,z7,z3,z478,z4,z5,z6]),(0,[z1,z7,z479,z3,z4,z5,z6]),(0,[z1,z112,z7,z3,z18,z5,z6]),(0,[z1,z7,z178,z3,z4,z5,z6])],[(0,[z179,z1,z7,z3,z4,z5,z6])]],
   [[(1,[z1,z7,z3,z10,z5,z6]),(1,[z1,z7,z3,z253,z5,z6]),(0,[z1,z7,z3,z4,z480,z5,z21])],[(0,[z33,z1,z7,z3,z227,z5,z6]),(0,[z12,z1,z7,z3,z10,z5,z6]),(0,[z1,z7,z40,z3,z10,z5,z6]),(0,[z1,z7,z3,z4,z481,z5,z6]),(0,[z1,z59,z7,z3,z4,z147,z6]),(0,[z1,z38,z7,z3,z4,z5,z218]),(0,[z1,z7,z3,z4,z146,z5,z21]),(0,[z1,z7,z3,z4,z5,z482,z6])],[(0,[z1,z7,z3,z3,z4,z5,z6]),(0,[z225,z1,z7,z3,z10,z5,z6]),(0,[z1,z7,z3,z4,z233,z5,z21]),(0,[z1,z7,z3,z4,z483,z5,z6])],[(0,[z17,z7,z3,z4,z5,z46,z6]),(0,[z165,z1,z7,z3,z4,z206,z6]),(0,[z1,z68,z48,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z103,z5,z11]),(0,[z1,z7,z3,z4,z5,z6,z484])],[(0,[z1,z7,z3,z9,z4,z5,z21]),(0,[z140,z1,z7,z43,z4,z5,z6]),(0,[z1,z7,z3,z4,z46,z147,z6]),(0,[z485,z1,z7,z3,z4,z5,z6])],[(0,[z1,z7,z486,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z181,z21]),(0,[z77,z1,z7,z3,z146,z5,z6]),(0,[z1,z7,z487,z3,z4,z5,z6])],[(0,[z15,z1,z7,z3,z10,z5,z6]),(0,[z1,z7,z3,z4,z5,z61,z6]),(0,[z1,z7,z3,z18,z5,z6,z41]),(0,[z17,z1,z7,z3,z367,z5,z6]),(0,[z1,z7,z3,z4,z5,z21,z97]),(0,[z77,z1,z44,z3,z4,z5,z6]),(0,[z488,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z197,z11]),(0,[z1,z7,z3,z4,z489,z5,z6])],[(0,[z1,z7,z3,z4,z159,z5,z6]),(0,[z99,z1,z7,z3,z18,z5,z6]),(1,[z1,z74,z7,z3,z4,z5]),(0,[z1,z162,z7,z3,z10,z5,z6]),(0,[z490,z1,z7,z3,z4,z5,z6])]],
   [[(1,[z1,z7,z3,z107,z5,z6]),(1,[z15,z16,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z491,z6]),(0,[z1,z7,z492,z3,z4,z5,z6]),(0,[z1,z7,z3,z150,z4,z5,z6]),(0,[z1,z7,z3,z4,z493,z5,z6]),(0,[z1,z7,z3,z4,z494,z5,z6])],[(0,[z1,z495,z7,z3,z4,z5,z6]),(0,[z1,z463,z7,z3,z4,z5,z6]),(0,[z1,z496,z7,z3,z4,z5,z6]),(0,[z1,z7,z149,z3,z18,z5,z6]),(0,[z1,z78,z7,z3,z4,z5,z6]),(0,[z1,z7,z497,z3,z4,z5,z6]),(0,[z1,z214,z7,z3,z4,z5,z11]),(0,[z1,z314,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z67,z6])],[(0,[z1,z7,z3,z4,z498,z5,z6]),(0,[z1,z7,z3,z499,z4,z5,z6]),(0,[z1,z7,z500,z3,z4,z5,z6]),(0,[z501,z1,z7,z3,z4,z5,z6]),(0,[z1,z502,z7,z3,z4,z5,z6]),(1,[z1,z27,z7,z152,z5,z6]),(0,[z503,z1,z7,z3,z4,z5,z6]),(0,[z1,z504,z7,z3,z4,z5,z6])],[(0,[z33,z1,z7,z3,z4,z5,z251]),(1,[z1,z7,z3,z4,z85,z6]),(0,[z225,z1,z7,z3,z4,z5,z218]),(0,[z1,z7,z3,z4,z5,z505,z6]),(0,[z1,z7,z3,z506,z4,z5,z6]),(0,[z1,z507,z7,z3,z4,z5,z6]),(0,[z1,z508,z7,z3,z4,z5,z21])],[(0,[z1,z7,z43,z3,z10,z5,z6]),(0,[z1,z162,z7,z3,z18,z5,z6]),(0,[z1,z509,z7,z3,z4,z5,z6]),(0,[z99,z1,z7,z3,z4,z5,z181]),(0,[z1,z7,z3,z4,z5,z11,z181]),(0,[z510,z1,z7,z3,z4,z5,z6])],[(0,[z1,z7,z3,z4,z5,z6,z511]),(0,[z140,z1,z7,z3,z18,z5,z6]),(0,[z1,z59,z7,z3,z10,z5,z6])],[(0,[z1,z7,z3,z52,z18,z5,z6]),(0,[z124,z1,z7,z3,z4,z5,z11]),(0,[z1,z7,z3,z4,z512,z5,z6]),(0,[z513,z1,z7,z3,z4,z5,z6]),(0,[z514,z1,z7,z3,z4,z5,z6]),(0,[z1,z38,z7,z3,z4,z5,z258])],[(0,[z15,z1,z2,z3,z4,z5,z6]),(0,[z515,z1,z7,z3,z4,z5,z6]),(0,[z1,z516,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z18,z103,z5,z6]),(0,[z1,z7,z3,z10,z5,z205,z6]),(0,[z1,z7,z3,z4,z5,z6,z517]),(0,[z1,z7,z3,z4,z5,z6,z101]),(0,[z1,z7,z3,z4,z5,z28,z6]),(0,[z1,z7,z3,z4,z518,z5,z6]),(0,[z1,z7,z3,z4,z519,z5,z6])]],
   [[(0,[z77,z1,z7,z3,z10,z5,z6]),(0,[z165,z7,z3,z4,z5,z181,z6]),(0,[z1,z7,z3,z4,z520,z5,z6]),(1,[z1,z7,z3,z5,z51,z6])],[(0,[z1,z521,z7,z3,z4,z5,z6]),(0,[z33,z1,z7,z3,z4,z5,z21]),(0,[z1,z27,z7,z3,z18,z5,z6]),(0,[z1,z7,z3,z4,z522,z5,z6]),(0,[z165,z1,z7,z3,z4,z254,z6]),(0,[z1,z7,z57,z3,z4,z147,z6]),(0,[z523,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z180,z5,z11]),(0,[z1,z7,z3,z4,z5,z6,z524])],[(0,[z525,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z48,z43,z4,z5,z6]),(0,[z526,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z10,z5,z6,z218]),(0,[z1,z7,z3,z4,z5,z11,z448])],[(0,[z0,z1,z7,z3,z4,z5,z21]),(0,[z1,z7,z2,z3,z4,z5,z11]),(0,[z1,z38,z7,z178,z3,z5,z6]),(1,[z1,z7,z3,z4,z5,z527])],[(0,[z1,z7,z3,z4,z5,z5,z6]),(0,[z1,z7,z528,z3,z4,z5,z6])],[(0,[z1,z7,z3,z18,z5,z529,z6]),(0,[z1,z7,z3,z522,z18,z5,z6]),(0,[z17,z1,z7,z3,z435,z5,z6]),(0,[z261,z1,z7,z3,z4,z5,z6]),(0,[z1,z530,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z152,z5,z6]),(0,[z1,z531,z7,z3,z4,z5,z6])],[(1,[z1,z7,z3,z532,z5,z6]),(0,[z1,z7,z533,z3,z4,z5,z6]),(0,[z1,z7,z3,z534,z4,z5,z6]),(0,[z1,z7,z3,z535,z4,z5,z6]),(0,[z1,z7,z178,z133,z4,z5,z6]),(1,[z1,z7,z3,z4,z5,z58])],[(0,[z536,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z18,z152,z5,z6]),(0,[z1,z537,z7,z3,z4,z5,z6])]],
   [[(0,[z17,z1,z7,z3,z4,z5,z21]),(0,[z538,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z539,z6]),(0,[z1,z7,z3,z4,z5,z11,z258])],[(0,[z1,z7,z3,z10,z180,z5,z6]),(0,[z1,z7,z3,z4,z103,z46,z6]),(0,[z1,z540,z7,z3,z4,z5,z6]),(0,[z1,z7,z541,z3,z4,z5,z6]),(1,[z1,z7,z3,z4,z180,z67])],[(0,[z1,z116,z7,z3,z10,z5,z6]),(0,[z99,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z542,z3,z4,z5,z6]),(0,[z1,z116,z3,z4,z5,z6,z218]),(0,[z1,z7,z3,z543,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z11,z6])],[(1,[z1,z7,z3,z4,z5,z108]),(0,[z1,z7,z544,z3,z4,z5,z6]),(0,[z1,z7,z48,z3,z18,z5,z6]),(0,[z545,z1,z7,z3,z4,z5,z6]),(0,[z1,z112,z7,z3,z4,z5,z288]),(0,[z1,z7,z3,z4,z5,z546,z6])],[(0,[z0,z1,z7,z3,z4,z24,z6]),(0,[z15,z1,z7,z3,z532,z5,z6]),(1,[z1,z110,z3,z4,z5,z6]),(0,[z1,z7,z3,z18,z5,z302,z6]),(0,[z1,z68,z112,z3,z4,z5,z6]),(1,[z1,z7,z3,z4,z5,z49]),(0,[z1,z7,z3,z4,z5,z6,z547]),(0,[z1,z7,z149,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z51,z21]),(0,[z212,z1,z7,z3,z4,z5,z11]),(0,[z1,z7,z3,z4,z5,z548,z6])],[(0,[z33,z1,z303,z3,z4,z5,z6]),(0,[z1,z7,z57,z3,z10,z5,z6]),(0,[z1,z38,z7,z3,z4,z5,z268]),(0,[z54,z1,z7,z3,z4,z5,z21]),(0,[z1,z7,z3,z5,z39,z6,z258])],[(0,[z33,z1,z7,z43,z4,z5,z6]),(0,[z1,z7,z3,z4,z549,z5,z6]),(0,[z550,z1,z7,z3,z4,z5,z6])],[(0,[z1,z16,z7,z3,z10,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z202]),(0,[z1,z7,z3,z10,z5,z6,z258]),(0,[z551,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z552,z5,z6]),(1,[z1,z7,z3,z4,z5,z284]),(0,[z1,z553,z7,z3,z4,z5,z6]),(0,[z1,z7,z554,z3,z4,z5,z6]),(0,[z1,z7,z3,z52,z4,z5,z258])]],
   [[(0,[z140,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z555,z4,z5,z6]),(0,[z1,z7,z556,z3,z4,z5,z6]),(0,[z1,z7,z178,z3,z4,z5,z19])],[(0,[z557,z1,z7,z3,z4,z5,z6]),(0,[z558,z1,z7,z3,z4,z5,z6]),(0,[z1,z44,z7,z3,z4,z5,z21]),(0,[z1,z7,z3,z52,z4,z5,z6]),(1,[z1,z38,z7,z3,z5,z258])],[(1,[z1,z7,z3,z4,z5,z288]),(0,[z1,z7,z3,z4,z5,z559,z6])],[(1,[z1,z7,z3,z4,z5,z290]),(0,[z1,z255,z7,z3,z18,z5,z6]),(0,[z1,z7,z560,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z45,z5,z6]),(0,[z1,z116,z7,z3,z4,z5,z218]),(1,[z1,z7,z3,z4,z5,z28]),(0,[z1,z7,z3,z4,z5,z561,z6])],[(0,[z1,z3,z312,z4,z98,z5,z6]),(0,[z1,z7,z3,z4,z562,z5,z6]),(0,[z1,z27,z7,z3,z4,z5,z6])],[(0,[z1,z7,z3,z563,z4,z5,z6]),(0,[z1,z7,z3,z4,z564,z5,z6]),(0,[z1,z7,z3,z4,z565,z5,z6])],[(0,[z0,z1,z7,z320,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z566]),(0,[z1,z7,z3,z4,z5,z567,z6]),(0,[z1,z7,z3,z4,z568,z5,z6]),(0,[z198,z1,z7,z3,z4,z5,z6])],[(0,[z33,z1,z7,z3,z18,z5,z6]),(0,[z167,z1,z7,z3,z10,z5,z6]),(0,[z569,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z570,z5,z6]),(0,[z1,z7,z3,z4,z5,z11,z268]),(0,[z1,z7,z3,z4,z103,z5,z21]),(0,[z1,z571,z7,z3,z4,z5,z6]),(0,[z1,z38,z7,z3,z5,z6,z258])]],
   [[(0,[z1,z7,z3,z4,z5,z6,z572]),(0,[z1,z7,z3,z474,z10,z5,z6]),(0,[z1,z7,z3,z4,z279,z5,z6]),(0,[z1,z7,z3,z4,z573,z5,z6]),(1,[z1,z7,z3,z4,z5,z307])],[(0,[z574,z1,z7,z3,z4,z5,z6]),(1,[z7,z3,z10,z18,z5,z6]),(0,[z1,z7,z178,z3,z10,z5,z6]),(1,[z1,z7,z3,z4,z562,z5]),(0,[z1,z7,z3,z4,z5,z6,z575]),(0,[z1,z7,z3,z4,z5,z576,z6])],[(1,[z1,z7,z3,z4,z160,z6]),(0,[z1,z7,z9,z150,z4,z5,z6]),(0,[z179,z1,z7,z3,z10,z5,z6]),(0,[z1,z7,z3,z13,z4,z5,z6]),(0,[z1,z577,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z283,z205]),(1,[z1,z7,z3,z168,z146,z6])],[(0,[z1,z7,z578,z3,z4,z5,z6]),(0,[z579,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z268,z21]),(0,[z1,z59,z7,z3,z4,z302,z6])],[(0,[z1,z7,z3,z18,z146,z5,z6]),(0,[z580,z1,z7,z3,z4,z5,z6]),(1,[z1,z7,z3,z4,z5,z317])],[(0,[z0,z1,z16,z3,z4,z5,z6]),(0,[z165,z1,z7,z3,z18,z5,z6]),(0,[z1,z7,z3,z18,z233,z5,z6]),(0,[z1,z7,z581,z3,z4,z5,z6]),(0,[z1,z44,z3,z312,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z582,z6]),(0,[z1,z7,z3,z4,z5,z11,z79]),(0,[z1,z7,z3,z4,z583,z5,z6])],[(0,[z1,z7,z3,z4,z46,z302,z6]),(0,[z1,z7,z584,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z181,z6]),(0,[z1,z7,z48,z3,z4,z5,z6]),(0,[z1,z7,z3,z52,z4,z5,z268]),(0,[z1,z7,z585,z3,z4,z5,z6])],[(0,[z1,z7,z3,z4,z24,z5,z6]),(0,[z16,z7,z2,z3,z4,z5,z6]),(0,[z1,z303,z7,z3,z4,z5,z6]),(0,[z1,z7,z43,z3,z4,z5,z290]),(0,[z1,z7,z40,z3,z4,z5,z97]),(0,[z1,z7,z3,z4,z5,z586,z6]),(0,[z1,z7,z3,z4,z98,z5,z11]),(0,[z212,z1,z7,z3,z4,z205,z6])]],
   [[(0,[z1,z7,z3,z18,z5,z181,z6]),(0,[z1,z7,z3,z88,z18,z5,z6]),(0,[z99,z1,z7,z3,z4,z5,z97]),(0,[z1,z7,z3,z4,z5,z11,z97]),(0,[z1,z7,z3,z587,z4,z5,z6]),(0,[z1,z7,z57,z3,z4,z5,z527]),(0,[z1,z59,z7,z4,z103,z5,z6]),(0,[z1,z7,z3,z4,z240,z5,z6])],[(0,[z1,z7,z3,z4,z5,z588,z6]),(0,[z1,z68,z7,z3,z18,z5,z6]),(0,[z589,z1,z7,z3,z4,z5,z6])],[(0,[z590,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z103,z45,z6]),(0,[z165,z1,z7,z3,z4,z5,z181])],[(0,[z1,z7,z591,z3,z4,z5,z6]),(0,[z1,z7,z3,z150,z10,z5,z6]),(0,[z1,z7,z3,z4,z5,z147,z6])],[(0,[z432,z1,z7,z3,z4,z5,z6]),(0,[z592,z1,z7,z3,z18,z5,z6]),(0,[z1,z27,z7,z178,z4,z5,z6]),(0,[z1,z7,z3,z593,z4,z5,z6]),(1,[z1,z7,z3,z4,z32,z21]),(0,[z1,z508,z7,z3,z4,z5,z6])],[(0,[z7,z43,z3,z9,z4,z5,z6]),(0,[z1,z7,z3,z10,z315,z5,z6]),(0,[z1,z7,z3,z10,z4,z5,z11]),(0,[z1,z7,z3,z4,z5,z594,z6]),(0,[z1,z7,z3,z595,z4,z5,z6]),(0,[z1,z7,z3,z596,z4,z5,z6]),(0,[z1,z7,z48,z3,z4,z5,z284]),(0,[z1,z7,z597,z3,z4,z5,z6]),(0,[z1,z255,z3,z4,z233,z5,z6]),(0,[z1,z59,z7,z3,z4,z5,z307]),(0,[z1,z7,z3,z4,z180,z5,z21])],[(0,[z1,z598,z7,z3,z4,z5,z6]),(0,[z1,z255,z7,z3,z4,z5,z6]),(0,[z599,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z600,z3,z4,z5,z6]),(0,[z1,z7,z40,z3,z4,z180,z6])],[(0,[z1,z7,z2,z3,z4,z5,z21]),(0,[z1,z7,z3,z4,z601,z5,z6]),(0,[z1,z7,z602,z3,z18,z5,z6]),(0,[z1,z7,z3,z18,z5,z6,z70]),(0,[z1,z7,z3,z4,z5,z6,z603]),(0,[z1,z7,z3,z10,z5,z6,z97]),(0,[z1,z7,z3,z10,z312,z5,z6]),(0,[z1,z7,z3,z4,z233,z46,z6]),(0,[z1,z112,z7,z3,z4,z5,z141])]],
   [[(0,[z1,z7,z3,z18,z72,z5,z6]),(0,[z99,z7,z3,z4,z5,z6,z97]),(0,[z1,z27,z7,z3,z4,z5,z317]),(0,[z604,z1,z7,z3,z4,z5,z6])],[(0,[z605,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z606]),(0,[z1,z7,z3,z4,z607,z5,z6]),(0,[z248,z1,z7,z3,z4,z5,z21]),(1,[z1,z7,z22,z3,z4,z21]),(0,[z608,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z609,z4,z5,z6])],[(0,[z33,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z18,z5,z6]),(0,[z515,z1,z7,z3,z10,z5,z6]),(0,[z1,z7,z3,z4,z610,z5,z6]),(1,[z1,z7,z3,z4,z5,z19]),(0,[z1,z7,z3,z264,z4,z5,z6]),(0,[z1,z7,z3,z4,z611,z5,z6])],[(0,[z612,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z10,z336,z5,z6]),(0,[z1,z7,z178,z3,z4,z5,z427]),(0,[z1,z7,z57,z3,z4,z302,z6])],[(0,[z1,z7,z3,z4,z5,z613,z6]),(0,[z614,z1,z7,z3,z4,z5,z6]),(0,[z1,z112,z7,z3,z10,z5,z6]),(0,[z1,z615,z7,z3,z4,z5,z6]),(0,[z616,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z168,z4,z205,z6]),(0,[z1,z617,z7,z3,z4,z5,z6])],[(0,[z1,z7,z3,z18,z96,z5,z6]),(0,[z1,z7,z3,z4,z618,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z619])],[(1,[z1,z7,z3,z295,z5,z6]),(0,[z1,z7,z3,z4,z5,z299,z6]),(0,[z1,z7,z3,z18,z5,z613,z6]),(0,[z1,z7,z3,z10,z5,z67,z6]),(1,[z1,z7,z3,z4,z5,z141]),(0,[z1,z620,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z621]),(0,[z1,z7,z622,z3,z4,z5,z6])],[(1,[z1,z7,z3,z88,z18,z5]),(0,[z1,z7,z3,z312,z18,z5,z6]),(0,[z1,z623,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z624,z4,z5,z6]),(0,[z1,z625,z7,z3,z4,z5,z6]),(0,[z277,z1,z7,z3,z4,z5,z6]),(0,[z626,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z180,z5,z41])]],
   [[(1,[z1,z7,z3,z304,z5,z6]),(0,[z165,z1,z7,z3,z4,z5,z6]),(0,[z165,z1,z7,z3,z385,z5,z6]),(0,[z1,z7,z3,z4,z5,z627,z6]),(0,[z212,z1,z7,z3,z4,z5,z21])],[(0,[z12,z1,z7,z3,z304,z5,z6]),(0,[z1,z628,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z21,z21]),(0,[z1,z7,z3,z4,z5,z629,z6]),(0,[z1,z7,z3,z4,z5,z6,z630])],[(0,[z1,z7,z3,z4,z5,z251,z6]),(0,[z1,z7,z3,z4,z45,z147,z6]),(0,[z1,z7,z3,z4,z180,z5,z67]),(0,[z1,z7,z3,z4,z5,z6,z631])],[(1,[z1,z7,z3,z4,z5,z183]),(0,[z1,z7,z3,z4,z5,z632,z6]),(0,[z1,z7,z3,z88,z4,z5,z6]),(0,[z1,z7,z3,z4,z633,z5,z6]),(0,[z634,z1,z7,z3,z4,z5,z6])],[(0,[z1,z68,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z635,z4,z5,z6])],[(0,[z1,z636,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z637,z4,z5,z6]),(0,[z99,z1,z7,z3,z10,z5,z6]),(0,[z99,z1,z7,z3,z253,z5,z6]),(1,[z1,z7,z3,z4,z5,z11]),(0,[z1,z7,z3,z4,z5,z51,z6])],[(0,[z1,z7,z3,z4,z638,z5,z6]),(0,[z140,z1,z7,z3,z295,z5,z6]),(0,[z1,z53,z7,z3,z4,z5,z6]),(0,[z12,z1,z7,z3,z4,z5,z11]),(0,[z1,z7,z3,z4,z5,z268,z181]),(0,[z1,z7,z40,z3,z4,z5,z11])],[(1,[z1,z7,z298,z4,z5,z6]),(1,[z1,z7,z3,z4,z5,z393]),(0,[z592,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z149,z3,z10,z5,z6]),(1,[z1,z7,z3,z4,z125,z6]),(0,[z225,z1,z7,z3,z4,z5,z11]),(0,[z54,z1,z7,z149,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z41])]],
   [[(0,[z1,z2,z3,z150,z4,z5,z6]),(0,[z124,z1,z7,z3,z18,z5,z6]),(0,[z1,z7,z3,z4,z639,z5,z6]),(0,[z1,z640,z7,z3,z4,z5,z6]),(0,[z641,z1,z7,z3,z4,z5,z6])],[(0,[z1,z7,z3,z4,z642,z5,z6]),(0,[z1,z7,z3,z4,z5,z97,z218]),(0,[z1,z643,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z644,z6]),(0,[z294,z1,z7,z3,z4,z5,z21]),(1,[z212,z1,z7,z3,z205,z6])],[(0,[z1,z7,z602,z3,z4,z5,z6]),(0,[z1,z7,z3,z133,z18,z5,z6]),(0,[z1,z68,z7,z150,z4,z5,z6]),(0,[z1,z645,z7,z3,z4,z5,z6]),(0,[z1,z44,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z409,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z527,z6]),(1,[z1,z7,z3,z4,z5,z456]),(0,[z1,z7,z3,z4,z5,z205,z11])],[(0,[z1,z7,z3,z532,z4,z5,z6]),(0,[z1,z7,z3,z4,z646,z5,z6]),(0,[z1,z7,z647,z3,z4,z5,z6]),(0,[z140,z1,z7,z9,z4,z5,z6]),(0,[z140,z1,z7,z3,z10,z5,z6]),(0,[z1,z1,z7,z3,z18,z5,z6]),(1,[z124,z7,z3,z10,z5,z6]),(0,[z1,z7,z3,z4,z648,z5,z6]),(0,[z1,z7,z57,z40,z3,z4,z6]),(0,[z1,z7,z3,z4,z5,z6,z649])],[(0,[z650,z1,z7,z3,z4,z5,z6]),(0,[z33,z7,z3,z9,z4,z5,z6]),(0,[z1,z7,z3,z52,z10,z5,z6]),(0,[z651,z1,z7,z3,z4,z5,z6])],[(0,[z1,z7,z3,z4,z5,z6,z652]),(0,[z1,z7,z3,z4,z4,z5,z6]),(0,[z17,z1,z7,z3,z4,z46,z6]),(0,[z1,z7,z3,z4,z5,z6,z653]),(0,[z1,z7,z57,z4,z5,z302,z6]),(0,[z1,z7,z654,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z283,z6])],[(0,[z33,z140,z7,z3,z4,z5,z6]),(0,[z655,z1,z7,z3,z4,z5,z6]),(0,[z1,z656,z7,z3,z4,z5,z6]),(1,[z1,z255,z3,z4,z233,z6]),(0,[z1,z7,z3,z4,z5,z11,z218])],[(0,[z1,z7,z3,z10,z5,z11,z6]),(0,[z1,z27,z7,z3,z10,z5,z6]),(0,[z1,z657,z7,z3,z4,z5,z6])]],
   [[(0,[z1,z7,z3,z89,z4,z5,z6]),(0,[z658,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z233,z45,z6]),(0,[z1,z7,z659,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z660]),(0,[z1,z7,z3,z4,z5,z6,z661]),(0,[z1,z7,z3,z4,z103,z5,z6])],[(0,[z1,z7,z43,z3,z4,z5,z11]),(0,[z225,z1,z7,z40,z3,z4,z5])],[(0,[z1,z7,z3,z4,z5,z662,z6]),(0,[z165,z1,z7,z3,z431,z5,z6]),(0,[z1,z7,z3,z312,z4,z5,z6]),(0,[z1,z59,z7,z3,z4,z5,z11])],[(0,[z663,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z98,z5,z21]),(0,[z1,z7,z3,z4,z664,z5,z6]),(0,[z1,z7,z3,z4,z5,z419,z11]),(0,[z1,z7,z3,z4,z180,z67,z6])],[(0,[z1,z7,z3,z10,z406,z5,z6]),(0,[z1,z7,z3,z4,z665,z5,z6]),(0,[z1,z666,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z268,z6]),(0,[z667,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z668,z5,z6]),(0,[z1,z7,z3,z4,z5,z21,z511]),(0,[z1,z7,z3,z4,z5,z436,z6])],[(1,[z1,z7,z3,z4,z8,z6]),(0,[z124,z179,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z10,z5,z46,z6]),(0,[z77,z1,z7,z3,z4,z5,z11]),(0,[z1,z255,z7,z3,z4,z147,z6]),(0,[z1,z7,z3,z52,z4,z5,z218]),(1,[z1,z7,z3,z4,z5,z427]),(0,[z669,z1,z7,z3,z4,z5,z6]),(0,[z1,z59,z7,z3,z4,z103,z6]),(0,[z1,z7,z3,z4,z5,z11,z629])],[(0,[z1,z7,z3,z18,z5,z268,z6]),(1,[z1,z7,z3,z18,z5,z21]),(0,[z1,z7,z3,z18,z5,z205,z6]),(0,[z1,z7,z3,z4,z5,z529,z6]),(0,[z670,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z671,z6]),(0,[z1,z7,z3,z4,z5,z672,z6])],[(0,[z1,z673,z7,z3,z4,z5,z6]),(1,[z1,z7,z3,z367,z5,z6]),(0,[z77,z1,z7,z3,z312,z5,z6]),(0,[z77,z1,z7,z3,z98,z5,z6]),(0,[z1,z59,z7,z3,z4,z5,z456]),(0,[z674,z1,z7,z3,z4,z5,z6])]],
   [[(0,[z1,z7,z3,z4,z5,z345,z21]),(0,[z1,z7,z3,z675,z4,z5,z6])],[(0,[z1,z7,z48,z9,z4,z5,z6]),(0,[z1,z7,z3,z18,z5,z6,z218]),(0,[z1,z7,z48,z3,z10,z5,z6]),(0,[z1,z7,z3,z10,z4,z5,z21]),(0,[z1,z7,z676,z3,z4,z5,z6]),(0,[z1,z7,z93,z3,z4,z5,z205]),(1,[z1,z7,z3,z52,z5,z39])],[(0,[z1,z121,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z30,z5,z6]),(0,[z677,z1,z7,z3,z4,z5,z6]),(0,[z1,z678,z7,z3,z4,z5,z6])],[(0,[z124,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z85,z5,z6]),(0,[z1,z7,z3,z4,z562,z5,z147])],[],[(0,[z1,z7,z3,z4,z5,z120,z6]),(0,[z1,z7,z3,z9,z18,z5,z6]),(0,[z1,z7,z3,z4,z5,z679,z6]),(0,[z680,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z681,z5,z6]),(0,[z1,z7,z3,z133,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z302,z6]),(1,[z1,z7,z3,z4,z32,z6])],[(0,[z1,z1,z7,z3,z4,z5,z6]),(0,[z54,z1,z7,z4,z5,z11,z6])],[(0,[z1,z7,z3,z4,z431,z5,z6]),(0,[z682,z1,z7,z3,z4,z5,z6]),(0,[z1,z683,z7,z3,z4,z5,z6]),(0,[z1,z116,z7,z3,z4,z5,z11]),(0,[z1,z7,z684,z3,z4,z5,z6])]],
   [[(0,[z140,z7,z43,z3,z4,z5,z6]),(0,[z1,z7,z3,z18,z180,z5,z6]),(0,[z1,z7,z3,z4,z5,z414,z6]),(0,[z1,z59,z7,z3,z4,z233,z6])],[(0,[z1,z7,z3,z4,z5,z685,z6]),(0,[z1,z255,z7,z3,z10,z5,z6]),(0,[z1,z7,z3,z10,z5,z39,z6]),(0,[z1,z7,z3,z686,z4,z5,z6]),(0,[z99,z1,z38,z7,z3,z4,z5]),(0,[z1,z3,z4,z5,z268,z6,z218])],[(0,[z1,z7,z3,z4,z687,z5,z6]),(0,[z1,z7,z3,z4,z5,z181,z218]),(0,[z1,z7,z3,z4,z5,z6,z688])],[(0,[z1,z7,z3,z689,z4,z5,z6])],[(0,[z1,z16,z7,z3,z4,z5,z11]),(0,[z1,z7,z3,z4,z5,z459,z11])],[(0,[z33,z1,z7,z3,z10,z5,z6]),(0,[z1,z7,z57,z3,z4,z103,z6])],[(0,[z1,z7,z3,z18,z5,z6,z258]),(1,[z1,z7,z3,z435,z5,z6]),(0,[z17,z1,z7,z3,z4,z45,z6]),(0,[z1,z7,z3,z4,z5,z6,z6]),(0,[z1,z112,z7,z48,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z690,z6])],[(0,[z1,z7,z691,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z692,z5,z6]),(0,[z1,z7,z3,z693,z4,z5,z6])]],
   [[(1,[z1,z44,z3,z312,z5,z6]),(0,[z1,z7,z694,z3,z4,z5,z6])],[(0,[z0,z1,z7,z3,z321,z5,z6]),(0,[z1,z7,z3,z4,z5,z695,z6]),(0,[z696,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z697,z3,z4,z5,z6]),(0,[z1,z116,z7,z40,z3,z4,z5]),(1,[z1,z7,z3,z4,z5,z21])],[(0,[z698,z1,z7,z3,z4,z5,z6]),(0,[z12,z1,z7,z3,z4,z5,z21]),(0,[z1,z7,z3,z4,z699,z5,z6]),(0,[z1,z7,z3,z700,z4,z5,z6]),(0,[z1,z44,z7,z3,z146,z5,z6]),(0,[z1,z7,z3,z4,z233,z146,z6]),(1,[z1,z7,z149,z4,z5,z21]),(0,[z1,z7,z40,z3,z4,z5,z21])],[(0,[z165,z1,z7,z3,z10,z5,z6]),(0,[z225,z1,z7,z3,z4,z5,z21]),(0,[z1,z7,z3,z4,z5,z21,z417])],[(0,[z0,z1,z7,z3,z18,z5,z6]),(0,[z1,z7,z3,z4,z45,z302,z6]),(0,[z1,z7,z3,z385,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z355,z6]),(0,[z1,z7,z3,z4,z480,z5,z6]),(0,[z167,z1,z7,z3,z4,z5,z11]),(0,[z1,z7,z3,z168,z4,z5,z11])],[(0,[z1,z7,z701,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z146,z5,z6])],[(0,[z1,z7,z3,z4,z233,z5,z6]),(1,[z273,z1,z7,z3,z5,z6]),(0,[z225,z1,z116,z3,z4,z5,z6]),(0,[z702,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z178,z3,z4,z5,z11]),(0,[z1,z7,z3,z4,z5,z205,z21]),(0,[z1,z7,z3,z4,z5,z21,z422])],[(0,[z1,z7,z7,z3,z4,z5,z6]),(0,[z15,z1,z7,z3,z4,z5,z21]),(0,[z703,z1,z7,z3,z4,z5,z6]),(0,[z179,z1,z7,z3,z4,z5,z11]),(0,[z1,z68,z7,z3,z10,z5,z6]),(1,[z1,z7,z3,z13,z5,z6]),(0,[z1,z7,z3,z4,z254,z5,z6]),(0,[z704,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z705]),(0,[z1,z7,z3,z4,z5,z706,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z1,z7,z3,z4,z120,z183]),(0,[z1,z110,z3,z4,z5,z11]),(0,[z1,z707,z7,z3,z5,z21]),(0,[z77,z1,z3,z98,z5,z21]),(0,[z708,z7,z3,z4,z5,z11]),(0,[z212,z1,z7,z3,z205,z6])],[(0,[z1,z7,z3,z709,z5,z6]),(0,[z1,z7,z3,z18,z32,z6]),(0,[z1,z7,z3,z4,z5,z710])],[(0,[z1,z7,z3,z711,z5,z6]),(0,[z1,z7,z3,z4,z120,z11]),(0,[z634,z7,z3,z4,z45,z6]),(0,[z1,z7,z3,z712,z5,z21])],[(0,[z1,z7,z3,z159,z5,z6]),(0,[z1,z7,z3,z4,z5,z713]),(0,[z1,z303,z3,z4,z5,z21]),(0,[z714,z1,z7,z3,z4,z5]),(0,[z1,z7,z424,z4,z5,z21]),(0,[z1,z7,z3,z715,z5,z6])],[(0,[z1,z7,z298,z4,z120,z6]),(0,[z1,z7,z3,z4,z120,z393]),(0,[z16,z716,z3,z4,z5,z6]),(0,[z1,z7,z3,z717,z5,z6]),(0,[z1,z7,z3,z5,z51,z427]),(0,[z1,z20,z7,z3,z5,z11]),(0,[z1,z7,z4,z5,z21,z62])],[(0,[z1,z7,z3,z4,z5,z718]),(0,[z1,z7,z3,z10,z5,z290]),(0,[z1,z7,z3,z13,z5,z134]),(0,[z12,z7,z3,z13,z45,z6]),(0,[z1,z162,z3,z4,z147,z21]),(0,[z1,z7,z3,z719,z5,z6]),(0,[z1,z7,z3,z4,z5,z720]),(0,[z1,z7,z3,z721,z4,z5]),(0,[z1,z7,z3,z4,z722,z6]),(0,[z1,z7,z3,z4,z5,z723])],[(0,[z1,z7,z3,z724,z295,z5]),(0,[z1,z20,z7,z22,z3,z21]),(0,[z1,z7,z22,z3,z51,z21])],[(0,[z1,z7,z3,z725,z5,z6]),(0,[z1,z7,z3,z18,z5,z251]),(0,[z179,z7,z3,z18,z5,z21]),(0,[z1,z7,z3,z726,z4,z5]),(0,[z1,z7,z4,z722,z5,z6]),(0,[z1,z7,z3,z727,z5,z21])]],
   [[(0,[z1,z728,z3,z4,z5,z6]),(0,[z1,z7,z272,z10,z5,z21]),(0,[z1,z7,z3,z729,z5,z6]),(0,[z1,z7,z542,z4,z5,z21]),(0,[z273,z1,z162,z3,z147,z6]),(0,[z1,z7,z3,z5,z6,z730])],[(0,[z1,z7,z3,z186,z5,z6]),(0,[z1,z7,z3,z522,z146,z6]),(0,[z1,z7,z149,z10,z5,z21]),(0,[z1,z7,z40,z3,z4,z361]),(0,[z273,z1,z7,z3,z185,z5]),(0,[z1,z7,z731,z3,z4,z6]),(0,[z1,z20,z7,z149,z5,z21])],[(0,[z1,z7,z3,z321,z5,z21]),(0,[z1,z7,z3,z4,z5,z732]),(0,[z1,z156,z150,z4,z5,z6]),(0,[z1,z7,z3,z4,z733,z6]),(0,[z1,z7,z3,z10,z5,z307]),(0,[z77,z1,z3,z98,z30,z6]),(0,[z1,z734,z7,z3,z5,z6]),(0,[z1,z3,z4,z5,z735,z21]),(0,[z1,z7,z3,z5,z736,z21])],[(0,[z1,z7,z3,z737,z4,z5]),(0,[z1,z7,z3,z10,z562,z5]),(0,[z7,z3,z4,z5,z738,z6]),(0,[z1,z7,z22,z3,z4,z181]),(0,[z1,z3,z4,z739,z5,z6]),(0,[z1,z7,z740,z152,z5,z6]),(0,[z1,z7,z3,z5,z741,z6]),(0,[z1,z7,z3,z4,z742,z6])],[(0,[z1,z7,z3,z10,z160,z6]),(0,[z1,z743,z3,z10,z5,z6]),(0,[z1,z7,z744,z4,z5,z6]),(0,[z1,z7,z3,z4,z206,z6]),(0,[z1,z7,z3,z385,z206,z6]),(0,[z1,z7,z3,z4,z208,z6])],[(0,[z1,z7,z3,z4,z745,z6]),(0,[z1,z7,z3,z4,z746,z6]),(0,[z1,z7,z3,z18,z5,z21]),(0,[z1,z38,z7,z3,z5,z202]),(0,[z17,z7,z3,z4,z46,z11]),(0,[z198,z7,z3,z4,z5,z61])],[(0,[z33,z303,z9,z4,z5,z6]),(0,[z1,z74,z7,z3,z5,z70]),(0,[z1,z7,z3,z367,z5,z6]),(0,[z1,z7,z3,z431,z5,z11]),(0,[z382,z7,z3,z4,z5,z181]),(0,[z1,z7,z3,z4,z747,z6]),(0,[z1,z7,z748,z4,z5,z6])],[(0,[z1,z7,z3,z4,z8,z108]),(0,[z33,z7,z749,z4,z5,z6]),(0,[z1,z53,z74,z7,z3,z5]),(0,[z1,z7,z3,z18,z5,z750]),(0,[z1,z7,z3,z522,z262,z6]),(0,[z1,z7,z3,z751,z5,z6]),(0,[z1,z20,z7,z3,z5,z417]),(0,[z1,z7,z675,z4,z5,z11])]],
   [[(0,[z1,z7,z3,z227,z5,z6]),(0,[z1,z110,z3,z4,z8,z6]),(0,[z1,z7,z3,z4,z5,z752]),(0,[z7,z3,z18,z5,z561,z6]),(0,[z99,z7,z3,z279,z5,z97]),(0,[z1,z3,z312,z739,z5,z6]),(0,[z1,z7,z3,z4,z5,z753]),(0,[z1,z7,z3,z754,z5,z6]),(0,[z1,z7,z3,z52,z5,z39])],[(0,[z1,z7,z755,z4,z5,z6]),(0,[z7,z3,z18,z692,z5,z6]),(0,[z1,z7,z3,z4,z756,z21])],[(0,[z1,z7,z3,z4,z5,z757]),(0,[z1,z7,z40,z3,z10,z41]),(0,[z1,z7,z3,z758,z4,z5]),(0,[z1,z27,z7,z740,z5,z6]),(0,[z1,z27,z7,z152,z5,z21]),(0,[z1,z20,z7,z3,z5,z422]),(0,[z1,z7,z3,z4,z5,z759])],[(0,[z1,z7,z3,z321,z24,z6]),(0,[z1,z7,z3,z760,z4,z5]),(0,[z1,z7,z3,z4,z761,z6])],[(0,[z1,z7,z3,z4,z5,z762]),(0,[z0,z2,z3,z4,z5,z21]),(0,[z1,z112,z150,z18,z5,z6]),(0,[z29,z7,z3,z18,z5,z6]),(0,[z1,z7,z3,z763,z4,z5]),(0,[z1,z7,z3,z185,z4,z5]),(0,[z1,z116,z3,z4,z5,z218]),(0,[z1,z7,z3,z4,z5,z764]),(0,[z1,z7,z3,z4,z32,z6]),(0,[z1,z7,z3,z32,z51,z6])],[(0,[z1,z7,z3,z765,z5,z6]),(0,[z1,z7,z3,z18,z766,z5]),(0,[z1,z7,z3,z4,z5,z767]),(0,[z1,z7,z768,z3,z4,z6]),(0,[z1,z7,z3,z4,z769,z5]),(0,[z770,z7,z3,z4,z5,z6])],[(0,[z1,z7,z3,z18,z24,z6]),(0,[z1,z7,z10,z336,z5,z21]),(0,[z1,z7,z3,z4,z5,z771]),(0,[z1,z772,z7,z4,z5,z6]),(0,[z1,z7,z3,z773,z5,z6])],[(0,[z1,z7,z3,z18,z30,z6]),(0,[z1,z7,z3,z774,z4,z5]),(0,[z1,z7,z3,z4,z5,z775])]],
   [[(0,[z1,z7,z3,z4,z5,z776]),(0,[z33,z7,z9,z18,z5,z6]),(0,[z1,z7,z3,z777,z4,z5]),(0,[z1,z7,z3,z4,z5,z778]),(0,[z1,z779,z7,z3,z5,z21]),(0,[z1,z7,z3,z5,z51,z21])],[(0,[z7,z3,z18,z5,z706,z6]),(0,[z1,z7,z3,z4,z5,z780]),(0,[z641,z7,z3,z10,z5,z6]),(0,[z1,z7,z3,z4,z5,z781]),(0,[z1,z7,z3,z782,z5,z6]),(0,[z1,z7,z22,z3,z4,z6]),(0,[z1,z7,z149,z5,z51,z21])],[(0,[z783,z1,z7,z3,z5,z6]),(0,[z1,z7,z3,z4,z5,z251]),(0,[z1,z7,z3,z385,z254,z6]),(0,[z1,z7,z3,z4,z5,z784])],[(0,[z1,z7,z3,z4,z5,z785]),(0,[z1,z7,z3,z5,z355,z11]),(0,[z1,z7,z3,z786,z5,z6])],[(0,[z1,z7,z787,z3,z4,z5]),(0,[z222,z7,z3,z18,z5,z6]),(0,[z1,z7,z3,z4,z5,z788]),(0,[z1,z789,z3,z4,z5,z6]),(0,[z1,z20,z7,z3,z32,z6]),(0,[z432,z7,z3,z4,z5,z448]),(0,[z1,z7,z3,z4,z790,z11])],[(0,[z1,z7,z298,z4,z5,z791]),(0,[z1,z7,z3,z4,z792,z6]),(0,[z1,z7,z320,z321,z5,z6]),(0,[z0,z2,z3,z4,z24,z6]),(0,[z1,z7,z3,z435,z5,z6]),(0,[z74,z7,z3,z10,z18,z5]),(0,[z1,z7,z3,z18,z5,z793]),(0,[z99,z7,z3,z10,z5,z97]),(0,[z1,z59,z7,z10,z103,z6]),(0,[z1,z7,z3,z10,z5,z101]),(0,[z1,z7,z3,z4,z46,z414]),(0,[z1,z7,z3,z4,z5,z794]),(1,[z1,z7,z3,z5,z795]),(0,[z1,z7,z3,z4,z6,z796])],[(0,[z1,z82,z7,z4,z5,z21]),(0,[z1,z7,z3,z532,z5,z21]),(0,[z7,z43,z749,z4,z5,z6]),(0,[z1,z7,z475,z4,z302,z6]),(0,[z1,z7,z3,z431,z206,z6]),(0,[z1,z797,z7,z3,z5,z6]),(0,[z1,z798,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z240,z197])],[(0,[z17,z7,z3,z367,z46,z6]),(0,[z1,z7,z799,z3,z4,z5])]],
   [[(0,[z1,z7,z3,z4,z5,z21]),(0,[z1,z7,z320,z18,z5,z6])],[(0,[z643,z7,z3,z18,z5,z6]),(0,[z273,z1,z7,z3,z146,z6]),(0,[z1,z7,z3,z168,z742,z6])],[(0,[z1,z7,z3,z4,z5,z750]),(0,[z99,z7,z3,z18,z5,z97]),(0,[z1,z7,z3,z18,z5,z101]),(0,[z1,z7,z3,z88,z5,z39]),(0,[z7,z3,z356,z10,z5,z6]),(0,[z1,z38,z7,z3,z431,z5]),(0,[z1,z7,z3,z4,z5,z800]),(0,[z1,z7,z3,z4,z5,z801])],[(0,[z1,z7,z802,z4,z5,z6]),(0,[z1,z68,z647,z4,z5,z6]),(0,[z100,z7,z9,z4,z5,z6]),(0,[z140,z7,z43,z4,z5,z299]),(0,[z1,z7,z3,z4,z5,z803]),(0,[z1,z7,z804,z3,z4,z5]),(0,[z1,z7,z3,z4,z5,z805]),(0,[z1,z7,z3,z806,z4,z5])],[(0,[z1,z7,z807,z4,z5,z6]),(0,[z1,z110,z3,z4,z5,z21]),(0,[z1,z7,z3,z808,z5,z6]),(1,[z7,z3,z4,z5,z738]),(0,[z99,z1,z20,z7,z3,z5]),(0,[z1,z7,z40,z3,z4,z796])],[(0,[z7,z3,z10,z335,z5,z6]),(0,[z1,z809,z7,z3,z5,z6]),(0,[z1,z7,z3,z810,z5,z6]),(0,[z1,z7,z3,z4,z21,z811])],[(0,[z1,z7,z3,z4,z120,z21]),(0,[z198,z7,z3,z18,z5,z6]),(0,[z1,z7,z3,z812,z5,z6]),(0,[z1,z7,z3,z813,z5,z6]),(0,[z1,z7,z3,z814,z5,z21])],[(0,[z0,z2,z320,z4,z5,z6]),(0,[z1,z7,z3,z4,z160,z108]),(0,[z1,z7,z3,z5,z815,z6]),(0,[z1,z7,z3,z10,z5,z11]),(0,[z1,z7,z3,z4,z5,z816]),(0,[z1,z7,z3,z253,z5,z11]),(0,[z1,z112,z150,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z817]),(0,[z818,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z180,z449])]],
   [[(0,[z1,z7,z3,z18,z5,z819]),(0,[z1,z7,z820,z3,z4,z5]),(0,[z1,z7,z3,z4,z766,z5]),(0,[z341,z7,z3,z10,z5,z6]),(0,[z1,z7,z3,z4,z5,z821]),(0,[z1,z7,z3,z4,z822,z5]),(0,[z1,z20,z7,z3,z5,z21])],[(0,[z1,z7,z3,z4,z24,z6]),(0,[z1,z7,z298,z10,z5,z6]),(0,[z1,z7,z3,z10,z5,z393]),(0,[z1,z7,z3,z4,z5,z823]),(0,[z1,z3,z18,z824,z5,z6]),(0,[z1,z7,z825,z3,z4,z21]),(0,[z54,z1,z7,z4,z5,z826]),(0,[z1,z827,z3,z4,z5,z11])],[(0,[z1,z7,z602,z216,z5,z6]),(0,[z1,z7,z3,z4,z30,z6])],[(0,[z33,z7,z9,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z299]),(0,[z530,z7,z3,z10,z5,z6]),(0,[z1,z7,z3,z185,z4,z46]),(0,[z198,z7,z3,z4,z5,z181]),(0,[z1,z7,z3,z4,z5,z828]),(0,[z1,z7,z3,z146,z742,z6])],[(0,[z100,z2,z3,z4,z5,z6]),(0,[z1,z7,z4,z5,z829,z6]),(0,[z1,z7,z3,z10,z5,z710]),(0,[z1,z27,z7,z336,z5,z6])],[(0,[z1,z7,z3,z4,z830,z6]),(0,[z1,z7,z3,z739,z5,z6]),(0,[z1,z7,z3,z4,z5,z831]),(0,[z1,z508,z3,z4,z5,z417])],[(0,[z0,z716,z3,z4,z5,z6]),(0,[z1,z7,z3,z832,z5,z6]),(0,[z33,z7,z9,z4,z5,z108]),(0,[z140,z7,z43,z18,z5,z6]),(0,[z1,z7,z18,z5,z829,z6]),(0,[z1,z7,z3,z4,z6,z833]),(0,[z1,z834,z3,z4,z5,z6]),(0,[z1,z7,z3,z835,z5,z6]),(0,[z836,z7,z3,z4,z5,z11])],[(0,[z1,z7,z3,z4,z5,z837]),(0,[z1,z7,z3,z107,z5,z11]),(0,[z1,z7,z3,z4,z5,z838]),(0,[z15,z16,z3,z4,z5,z11]),(0,[z33,z110,z9,z4,z5,z6]),(0,[z1,z7,z3,z4,z839,z6]),(0,[z77,z1,z3,z98,z208,z6]),(0,[z1,z20,z7,z22,z3,z6]),(0,[z1,z7,z22,z3,z51,z6])]],
   [[(0,[z1,z7,z3,z840,z5,z6]),(0,[z1,z7,z841,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z793]),(0,[z1,z3,z4,z5,z842,z6]),(0,[z165,z7,z3,z4,z5,z181]),(0,[z165,z7,z3,z385,z5,z181]),(0,[z1,z843,z3,z4,z5,z6]),(0,[z1,z7,z844,z4,z5,z6]),(0,[z1,z7,z845,z4,z5,z6]),(0,[z1,z7,z178,z133,z5,z6]),(0,[z1,z7,z3,z5,z795,z258]),(0,[z1,z7,z3,z846,z5,z6])],[(0,[z1,z7,z298,z107,z5,z6]),(0,[z1,z7,z3,z107,z5,z393]),(0,[z7,z3,z10,z18,z5,z21]),(0,[z1,z847,z3,z18,z5,z6]),(0,[z17,z7,z3,z4,z46,z21]),(0,[z1,z7,z3,z4,z5,z795])],[(0,[z1,z2,z298,z4,z5,z6]),(0,[z1,z7,z848,z4,z5,z6]),(0,[z1,z849,z3,z4,z5,z6]),(0,[z1,z7,z57,z18,z302,z6]),(0,[z1,z53,z7,z152,z5,z6]),(0,[z626,z7,z3,z18,z5,z6]),(0,[z1,z7,z3,z431,z5,z21]),(0,[z850,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z85,z11])],[(0,[z1,z7,z320,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z851]),(0,[z1,z7,z3,z5,z736,z6]),(0,[z1,z7,z3,z4,z5,z852]),(0,[z1,z7,z3,z4,z5,z853]),(0,[z12,z7,z3,z4,z45,z414]),(0,[z1,z7,z3,z4,z5,z854]),(0,[z1,z7,z4,z740,z5,z6]),(0,[z1,z7,z3,z4,z5,z855])],[(0,[z1,z856,z7,z3,z5,z6]),(0,[z411,z7,z3,z4,z46,z6]),(0,[z12,z7,z3,z4,z857,z6]),(0,[z1,z7,z3,z4,z5,z858]),(0,[z1,z7,z534,z4,z5,z21])],[(0,[z1,z7,z3,z4,z5,z859]),(0,[z1,z20,z7,z3,z5,z51])],[(0,[z1,z7,z3,z4,z5,z860]),(0,[z1,z7,z3,z4,z45,z414]),(0,[z1,z843,z150,z4,z5,z6]),(0,[z1,z7,z3,z5,z861,z6]),(0,[z1,z7,z3,z862,z5,z6])],[(0,[z1,z7,z3,z10,z206,z6]),(0,[z1,z7,z744,z10,z5,z6]),(0,[z1,z7,z3,z10,z208,z6]),(0,[z1,z7,z3,z52,z431,z5]),(0,[z1,z7,z528,z4,z5,z11])]],
   [[(0,[z1,z7,z3,z4,z5,z863]),(0,[z1,z7,z3,z4,z5,z864]),(0,[z1,z7,z3,z5,z865,z21]),(0,[z1,z38,z7,z3,z5,z51])],[(0,[z1,z7,z320,z4,z120,z6]),(0,[z1,z7,z57,z3,z185,z4])],[(0,[z1,z7,z3,z4,z5,z866]),(0,[z7,z554,z3,z18,z5,z6]),(0,[z1,z7,z3,z5,z867,z21])],[(0,[z1,z7,z320,z4,z5,z868]),(0,[z1,z7,z3,z869,z5,z6]),(0,[z1,z7,z3,z4,z5,z819]),(0,[z1,z59,z7,z4,z722,z6])],[(0,[z1,z7,z3,z870,z5,z6]),(0,[z1,z7,z3,z18,z208,z6]),(0,[z17,z7,z3,z4,z857,z6]),(0,[z1,z7,z3,z4,z5,z871]),(0,[z1,z7,z3,z872,z5,z6]),(0,[z1,z7,z3,z5,z39,z317]),(0,[z1,z7,z4,z5,z826,z21]),(0,[z1,z38,z7,z3,z5,z795])],[(0,[z1,z7,z3,z4,z5,z873]),(0,[z1,z7,z3,z532,z5,z11]),(0,[z1,z874,z3,z4,z5,z6])],[(0,[z1,z7,z3,z4,z875,z6]),(0,[z876,z7,z3,z4,z5,z6]),(0,[z877,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z878,z5,z6])],[(0,[z7,z3,z749,z4,z5,z6]),(0,[z1,z116,z3,z10,z5,z218]),(0,[z1,z7,z3,z10,z32,z6]),(0,[z1,z7,z3,z5,z355,z21]),(0,[z1,z7,z879,z4,z5,z6])]],
   [[(0,[z212,z1,z7,z3,z208,z6]),(0,[z1,z7,z3,z880,z5,z6]),(0,[z1,z7,z3,z4,z5,z881]),(0,[z1,z7,z40,z3,z4,z41])],[(0,[z140,z7,z43,z4,z5,z6]),(0,[z1,z7,z3,z18,z5,z414]),(0,[z1,z74,z7,z3,z52,z5]),(0,[z329,z7,z3,z4,z45,z6]),(0,[z1,z7,z3,z4,z882,z5])],[(0,[z165,z7,z3,z431,z5,z181])],[(0,[z1,z7,z133,z740,z5,z6]),(0,[z1,z7,z3,z4,z11,z32])],[(0,[z1,z847,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z883]),(0,[z1,z116,z3,z18,z5,z218]),(0,[z1,z7,z3,z10,z5,z780]),(0,[z165,z7,z3,z4,z254,z181])],[(0,[z1,z7,z3,z10,z5,z251]),(0,[z1,z7,z3,z18,z5,z767]),(0,[z1,z7,z57,z4,z302,z6]),(0,[z1,z59,z7,z4,z103,z307])],[(0,[z1,z7,z3,z295,z5,z21]),(0,[z1,z7,z3,z4,z884,z6]),(1,[z1,z7,z4,z5,z826])],[(0,[z1,z7,z3,z4,z885,z6]),(0,[z1,z7,z3,z886,z5,z6]),(0,[z17,z7,z3,z18,z46,z6]),(0,[z1,z887,z3,z4,z5,z6]),(0,[z1,z888,z7,z3,z4,z5]),(0,[z1,z7,z3,z889,z4,z5]),(0,[z1,z7,z3,z890,z5,z6])]],
   [[(0,[z1,z7,z3,z4,z891,z6]),(0,[z1,z7,z3,z892,z5,z6])],[(0,[z1,z7,z3,z893,z5,z6]),(0,[z1,z7,z3,z385,z5,z6]),(0,[z1,z7,z3,z88,z431,z5]),(0,[z1,z7,z3,z894,z5,z6]),(0,[z1,z7,z3,z895,z5,z6]),(0,[z1,z7,z3,z4,z896,z6]),(0,[z1,z7,z487,z4,z5,z21])],[(0,[z1,z7,z897,z4,z5,z6]),(0,[z1,z7,z3,z18,z254,z6]),(0,[z12,z7,z3,z4,z45,z134]),(0,[z1,z7,z3,z4,z898,z6]),(0,[z1,z7,z3,z5,z6,z795])],[(0,[z1,z7,z3,z4,z5,z899]),(0,[z1,z7,z3,z4,z900,z290]),(0,[z1,z7,z3,z10,z5,z21]),(0,[z1,z76,z7,z4,z103,z6]),(0,[z1,z7,z3,z253,z5,z21]),(0,[z1,z7,z40,z3,z4,z517]),(0,[z1,z314,z3,z4,z5,z268])],[(0,[z329,z7,z3,z18,z5,z6]),(0,[z1,z901,z7,z3,z5,z21]),(0,[z1,z902,z7,z3,z367,z5]),(0,[z1,z44,z3,z312,z5,z11]),(0,[z1,z7,z3,z5,z6,z903])],[(0,[z1,z74,z7,z3,z88,z5]),(0,[z580,z1,z7,z4,z5,z11]),(0,[z904,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z905]),(0,[z1,z7,z3,z4,z5,z906]),(0,[z1,z7,z22,z3,z4,z220]),(0,[z1,z7,z3,z52,z5,z51]),(0,[z1,z7,z3,z907,z5,z6])],[(0,[z608,z7,z3,z10,z5,z6]),(0,[z1,z44,z3,z739,z5,z6]),(0,[z1,z7,z149,z4,z5,z826]),(0,[z908,z7,z3,z4,z5,z21]),(0,[z1,z7,z4,z5,z11,z131])],[(0,[z1,z7,z3,z186,z5,z108]),(0,[z1,z909,z3,z4,z5,z6]),(0,[z1,z7,z3,z814,z5,z6]),(0,[z1,z7,z3,z4,z254,z181]),(0,[z1,z7,z3,z5,z21,z730])]],
   [[(0,[z1,z7,z3,z4,z5,z910]),(0,[z1,z7,z3,z4,z5,z911]),(0,[z1,z110,z3,z186,z5,z6]),(0,[z7,z3,z10,z18,z5,z11]),(0,[z7,z597,z3,z18,z5,z6]),(0,[z1,z7,z3,z4,z512,z67]),(0,[z7,z3,z4,z5,z912,z6]),(0,[z1,z7,z4,z722,z302,z6]),(0,[z1,z7,z22,z3,z4,z32])],[(0,[z1,z7,z3,z4,z5,z868]),(0,[z1,z7,z3,z4,z160,z11]),(0,[z1,z7,z3,z5,z913,z21]),(0,[z1,z7,z3,z763,z367,z5]),(0,[z329,z7,z3,z4,z5,z181]),(0,[z1,z20,z7,z3,z5,z6]),(0,[z1,z7,z3,z168,z146,z11]),(0,[z1,z7,z3,z4,z5,z914]),(0,[z1,z7,z3,z52,z5,z795])],[(0,[z1,z7,z3,z4,z5,z915]),(0,[z1,z916,z7,z3,z295,z5]),(0,[z7,z3,z83,z18,z5,z6]),(0,[z1,z112,z150,z10,z5,z6]),(0,[z617,z7,z3,z10,z5,z6]),(0,[z1,z902,z7,z3,z4,z5]),(0,[z1,z428,z7,z4,z5,z11])],[(0,[z1,z7,z3,z107,z5,z21]),(0,[z716,z2,z3,z4,z5,z6]),(0,[z15,z16,z3,z4,z5,z21]),(0,[z1,z7,z3,z4,z5,z917]),(0,[z1,z7,z3,z4,z5,z918]),(0,[z1,z7,z4,z103,z722,z6])],[(0,[z1,z7,z3,z10,z24,z6]),(0,[z1,z7,z3,z4,z24,z183]),(0,[z1,z7,z3,z4,z5,z414]),(0,[z1,z7,z3,z5,z919,z6]),(0,[z1,z3,z739,z98,z5,z6])],[(0,[z1,z7,z3,z920,z5,z6]),(0,[z1,z7,z3,z18,z5,z283]),(0,[z1,z7,z3,z10,z30,z6]),(0,[z1,z7,z416,z4,z5,z21]),(0,[z1,z7,z3,z4,z5,z921])],[(0,[z1,z7,z922,z4,z5,z6]),(0,[z1,z7,z3,z227,z5,z108]),(0,[z33,z7,z9,z10,z5,z6]),(0,[z1,z7,z3,z4,z5,z923]),(0,[z1,z7,z3,z4,z85,z21]),(0,[z1,z7,z3,z4,z5,z924]),(0,[z1,z7,z3,z4,z925,z6])],[(0,[z1,z110,z3,z227,z5,z6]),(0,[z1,z7,z926,z3,z4,z6]),(0,[z1,z7,z3,z4,z5,z927])]],
   [[(0,[z1,z7,z3,z18,z5,z134]),(0,[z12,z7,z3,z18,z45,z6]),(0,[z1,z53,z7,z96,z5,z6]),(0,[z1,z7,z93,z3,z18,z5]),(0,[z1,z7,z3,z4,z5,z928]),(0,[z1,z7,z3,z5,z6,z929]),(0,[z1,z7,z3,z624,z146,z6]),(0,[z1,z20,z7,z3,z180,z5])],[(0,[z1,z7,z4,z5,z11,z213]),(0,[z1,z7,z22,z3,z4,z345])],[(0,[z1,z7,z3,z930,z5,z6]),(0,[z1,z931,z7,z3,z159,z5]),(0,[z17,z7,z3,z4,z46,z6]),(0,[z1,z7,z3,z4,z932,z6]),(0,[z1,z116,z7,z22,z3,z4]),(0,[z1,z7,z22,z3,z4,z58]),(0,[z1,z7,z3,z933,z5,z21])],[(0,[z1,z394,z7,z4,z5,z21]),(0,[z1,z7,z3,z4,z5,z934]),(0,[z1,z7,z3,z18,z5,z299]),(0,[z1,z7,z3,z431,z5,z6]),(0,[z165,z7,z3,z10,z5,z181]),(0,[z1,z7,z3,z4,z5,z935]),(0,[z1,z7,z3,z936,z5,z6])],[(0,[z1,z7,z3,z107,z24,z6]),(0,[z1,z7,z3,z4,z5,z937]),(0,[z1,z303,z3,z18,z5,z6]),(0,[z7,z749,z9,z4,z5,z6]),(0,[z1,z496,z150,z4,z5,z6]),(0,[z7,z3,z938,z18,z5,z6]),(0,[z1,z7,z3,z195,z406,z6]),(0,[z1,z7,z3,z4,z5,z939]),(0,[z940,z1,z7,z3,z5,z6]),(0,[z1,z7,z3,z4,z5,z941])],[(0,[z1,z7,z3,z4,z8,z21]),(0,[z23,z7,z3,z10,z5,z6]),(0,[z1,z7,z3,z4,z254,z6]),(0,[z1,z7,z3,z4,z5,z942]),(0,[z1,z943,z3,z4,z5,z21])],[(0,[z1,z7,z320,z10,z5,z6]),(0,[z1,z7,z3,z186,z160,z6]),(0,[z1,z162,z3,z18,z147,z6]),(0,[z1,z7,z3,z5,z944,z6]),(0,[z1,z68,z48,z4,z5,z21]),(0,[z1,z116,z3,z4,z5,z629])],[(0,[z1,z7,z3,z4,z5,z945]),(0,[z1,z7,z3,z4,z5,z946]),(0,[z1,z7,z3,z4,z947,z6]),(0,[z1,z7,z3,z948,z5,z11])]],
   [[(0,[z165,z7,z3,z18,z5,z181]),(0,[z99,z7,z3,z253,z5,z97]),(0,[z1,z7,z3,z4,z949,z6]),(0,[z77,z1,z346,z3,z5,z6])],[(0,[z1,z7,z3,z4,z950,z5]),(0,[z1,z110,z3,z4,z5,z251]),(0,[z1,z7,z3,z4,z5,z951]),(0,[z1,z7,z3,z4,z5,z952]),(0,[z7,z3,z18,z35,z5,z6]),(0,[z1,z7,z3,z4,z5,z953]),(1,[z1,z3,z4,z5,z954]),(0,[z1,z7,z5,z11,z51,z21]),(0,[z1,z7,z3,z5,z865,z6])],[(0,[z1,z7,z18,z955,z5,z6]),(0,[z1,z7,z40,z3,z4,z566]),(0,[z956,z7,z3,z4,z5,z6]),(0,[z1,z7,z22,z4,z11,z21]),(0,[z1,z7,z4,z130,z5,z21]),(0,[z1,z7,z3,z4,z957,z21]),(0,[z1,z7,z3,z264,z5,z39])],[],[(0,[z1,z958,z3,z4,z5,z6]),(0,[z7,z3,z4,z5,z738,z97]),(0,[z7,z3,z4,z5,z181,z738]),(0,[z1,z7,z3,z4,z959,z6]),(0,[z1,z59,z7,z4,z145,z6]),(0,[z1,z7,z3,z960,z4,z5]),(0,[z1,z116,z3,z4,z5,z954])],[(0,[z1,z7,z3,z961,z5,z6]),(0,[z1,z7,z962,z4,z5,z6]),(0,[z1,z7,z3,z227,z160,z6]),(0,[z1,z7,z3,z295,z5,z11]),(0,[z963,z1,z7,z3,z5,z6]),(0,[z7,z3,z10,z483,z5,z6]),(0,[z273,z1,z7,z3,z205,z6]),(0,[z1,z7,z3,z5,z39,z427]),(0,[z1,z7,z4,z5,z11,z826])],[(0,[z1,z7,z320,z107,z5,z6]),(0,[z1,z7,z3,z4,z5,z964]),(0,[z7,z3,z18,z313,z5,z6]),(0,[z1,z7,z22,z3,z18,z21]),(0,[z1,z7,z697,z4,z5,z21]),(0,[z1,z7,z965,z3,z4,z5]),(0,[z1,z7,z149,z4,z32,z21])],[(0,[z1,z7,z3,z966,z5,z6]),(0,[z1,z7,z3,z25,z5,z11]),(0,[z105,z1,z3,z72,z5,z6]),(0,[z1,z7,z3,z18,z5,z967]),(0,[z1,z7,z3,z279,z5,z6]),(0,[z1,z7,z3,z4,z5,z968]),(0,[z1,z7,z3,z304,z5,z11]),(0,[z1,z969,z7,z3,z5,z6]),(0,[z1,z7,z3,z4,z32,z307]),(0,[z1,z59,z7,z4,z103,z456])]],
   [[(0,[z33,z7,z9,z4,z8,z6]),(0,[z1,z7,z3,z4,z5,z970]),(0,[z592,z1,z7,z3,z529,z6]),(0,[z1,z7,z3,z4,z971,z6]),(0,[z1,z7,z3,z4,z5,z972]),(0,[z1,z7,z584,z4,z5,z11]),(0,[z1,z7,z973,z3,z4,z6]),(0,[z1,z219,z3,z4,z233,z6]),(0,[z1,z7,z3,z4,z5,z283])],[(0,[z1,z7,z475,z4,z5,z21]),(0,[z294,z7,z3,z4,z5,z97]),(0,[z1,z7,z3,z4,z974,z6]),(0,[z1,z7,z3,z975,z5,z21]),(0,[z1,z7,z976,z4,z5,z6])],[(0,[z0,z2,z3,z321,z5,z6]),(0,[z1,z3,z4,z824,z5,z6]),(0,[z77,z1,z3,z315,z5,z6]),(0,[z1,z7,z3,z977,z5,z6])],[(0,[z1,z7,z978,z4,z5,z6]),(0,[z1,z74,z7,z3,z279,z5]),(0,[z12,z7,z3,z4,z45,z6]),(0,[z1,z7,z3,z4,z5,z134]),(0,[z1,z7,z3,z4,z5,z979])],[(0,[z1,z7,z298,z4,z5,z183]),(0,[z1,z7,z3,z5,z980,z6]),(0,[z140,z7,z43,z10,z5,z6]),(0,[z1,z707,z7,z3,z5,z6]),(0,[z77,z1,z3,z98,z5,z6])],[(0,[z0,z2,z3,z18,z5,z6]),(0,[z1,z7,z10,z5,z11,z21]),(0,[z1,z7,z3,z474,z5,z34]),(0,[z1,z7,z3,z981,z5,z6]),(0,[z1,z7,z3,z4,z5,z982]),(0,[z1,z7,z3,z983,z5,z6]),(0,[z1,z7,z3,z984,z5,z6])],[(0,[z1,z7,z298,z4,z5,z11]),(0,[z1,z716,z3,z4,z5,z6]),(0,[z1,z82,z150,z4,z5,z6]),(0,[z1,z7,z3,z712,z5,z6]),(0,[z1,z985,z3,z18,z5,z6]),(0,[z1,z7,z3,z4,z125,z11]),(0,[z1,z7,z4,z5,z182,z21]),(0,[z1,z571,z3,z4,z5,z268]),(0,[z1,z7,z3,z4,z180,z796])],[(0,[z1,z303,z3,z4,z5,z6]),(0,[z1,z7,z3,z986,z4,z5]),(0,[z1,z7,z3,z4,z160,z251]),(0,[z7,z3,z938,z4,z5,z6]),(0,[z1,z7,z3,z10,z5,z883]),(0,[z1,z7,z3,z431,z254,z6]),(0,[z1,z7,z3,z146,z208,z6]),(0,[z1,z7,z694,z4,z5,z21]),(0,[z1,z7,z3,z4,z480,z32])]],
   [[(0,[z1,z7,z298,z4,z5,z393]),(0,[z1,z7,z57,z10,z302,z6]),(0,[z1,z44,z3,z312,z5,z21]),(0,[z1,z7,z3,z562,z5,z355]),(0,[z212,z1,z7,z3,z205,z11])],[(0,[z1,z7,z3,z4,z5,z987]),(0,[z179,z74,z7,z3,z18,z5]),(0,[z1,z7,z3,z18,z988,z6]),(0,[z1,z7,z3,z88,z5,z613]),(0,[z1,z7,z93,z3,z10,z5]),(0,[z1,z162,z3,z4,z147,z6]),(0,[z1,z7,z3,z4,z5,z989])],[(0,[z1,z303,z3,z4,z5,z108]),(0,[z1,z7,z3,z990,z5,z6]),(0,[z124,z7,z3,z10,z5,z11]),(0,[z1,z7,z3,z4,z5,z991]),(0,[z1,z7,z3,z992,z5,z6]),(0,[z1,z7,z22,z3,z4,z97]),(0,[z1,z7,z242,z4,z5,z21])],[(0,[z179,z7,z3,z18,z5,z6]),(0,[z515,z1,z3,z315,z5,z6]),(0,[z1,z7,z3,z4,z254,z97]),(0,[z1,z20,z7,z22,z3,z4]),(0,[z1,z7,z3,z727,z5,z6])],[(0,[z1,z110,z43,z4,z5,z6]),(0,[z1,z7,z3,z18,z5,z527]),(0,[z1,z7,z3,z4,z993,z6]),(0,[z1,z7,z3,z4,z5,z994]),(0,[z1,z112,z150,z4,z5,z288]),(0,[z1,z7,z3,z995,z5,z6]),(0,[z1,z7,z57,z366,z4,z6])],[(0,[z1,z7,z3,z4,z160,z21]),(0,[z1,z7,z3,z5,z815,z290]),(1,[z1,z707,z7,z3,z5]),(0,[z1,z7,z3,z996,z5,z6]),(0,[z1,z7,z3,z4,z5,z997]),(0,[z1,z7,z3,z4,z5,z998]),(0,[z1,z255,z3,z4,z233,z11]),(0,[z1,z7,z999,z3,z4,z5]),(0,[z1,z7,z3,z168,z146,z21])],[(0,[z1,z7,z3,z321,z5,z6]),(0,[z1,z3,z4,z5,z735,z6]),(0,[z1,z7,z3,z1000,z5,z6]),(0,[z1,z1001,z7,z3,z18,z6]),(0,[z1,z7,z1002,z3,z18,z6]),(0,[z1,z7,z3,z1003,z5,z6]),(0,[z1,z289,z3,z4,z233,z6]),(0,[z1,z827,z3,z4,z5,z6]),(0,[z1,z7,z3,z409,z5,z51]),(0,[z1,z38,z7,z22,z3,z4])],[(0,[z1,z74,z7,z3,z18,z5]),(0,[z1,z7,z3,z18,z5,z1004]),(0,[z1,z7,z3,z4,z5,z1005]),(0,[z1,z7,z229,z4,z5,z21]),(0,[z1,z7,z3,z4,z1006,z6])]],
   [[(0,[z1,z7,z298,z4,z5,z1007]),(0,[z7,z239,z3,z18,z5,z6]),(0,[z1008,z7,z3,z4,z5,z6])],[(0,[z1,z7,z3,z18,z5,z6]),(0,[z1,z7,z3,z4,z5,z1009]),(0,[z15,z16,z3,z159,z5,z6]),(0,[z1,z7,z3,z4,z1010,z6]),(0,[z1,z7,z3,z186,z5,z11]),(0,[z1,z7,z3,z4,z5,z1011]),(0,[z1,z7,z3,z4,z5,z1012]),(0,[z7,z3,z1013,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z1014]),(0,[z1,z162,z3,z4,z562,z147]),(0,[z1,z59,z7,z3,z185,z4]),(0,[z273,z1,z7,z3,z562,z5])],[(0,[z1,z7,z3,z4,z5,z967]),(0,[z1,z7,z3,z4,z5,z1015]),(0,[z1,z7,z3,z5,z913,z6]),(0,[z1,z7,z3,z1016,z5,z6]),(1,[z1,z3,z4,z1017,z6]),(0,[z1,z7,z3,z4,z1018,z6]),(0,[z1,z27,z7,z675,z5,z6])],[(0,[z1,z1019,z3,z4,z5,z6]),(0,[z1,z7,z3,z1020,z5,z6]),(0,[z1,z7,z57,z4,z182,z6]),(0,[z1,z7,z3,z4,z180,z247]),(0,[z1,z214,z7,z3,z4,z79])],[(0,[z1,z7,z3,z321,z120,z6]),(0,[z1021,z1,z7,z3,z5,z6]),(0,[z1,z7,z3,z4,z8,z11]),(0,[z1,z7,z3,z4,z5,z1022]),(0,[z1,z121,z7,z336,z5,z6]),(0,[z1,z7,z3,z4,z206,z11])],[(0,[z1,z7,z3,z4,z1023,z6]),(0,[z1,z110,z3,z18,z5,z6]),(0,[z1,z7,z3,z4,z756,z6]),(0,[z1,z916,z7,z3,z4,z5]),(0,[z135,z7,z3,z10,z5,z6])],[(0,[z1,z7,z3,z4,z5,z1024]),(0,[z1,z7,z3,z367,z5,z11]),(0,[z1,z7,z3,z4,z5,z1025]),(0,[z1,z3,z4,z1017,z147,z6]),(0,[z1,z27,z7,z152,z5,z6])],[(0,[z1,z7,z3,z18,z120,z6]),(0,[z7,z716,z3,z4,z5,z6]),(0,[z1,z7,z3,z10,z5,z414]),(0,[z1,z7,z22,z3,z10,z21]),(0,[z1,z7,z3,z4,z5,z1026]),(0,[z1,z7,z3,z4,z85,z6]),(0,[z1,z7,z3,z4,z5,z1027]),(0,[z1,z7,z3,z4,z5,z1028]),(0,[z1,z7,z3,z4,z67,z58])]],
   [[(0,[z0,z2,z3,z4,z5,z6]),(0,[z1,z7,z3,z227,z5,z11]),(0,[z33,z7,z9,z4,z160,z6]),(0,[z1,z7,z3,z18,z5,z284]),(0,[z1,z74,z7,z3,z5,z258]),(0,[z1,z38,z7,z3,z279,z5]),(0,[z1,z7,z3,z4,z1029,z21]),(0,[z1,z7,z3,z4,z5,z1030])],[(0,[z1,z7,z3,z4,z5,z1031]),(0,[z1,z985,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z1032,z21])],[(0,[z54,z1,z7,z18,z5,z11])],[(0,[z1,z7,z3,z4,z1033,z6]),(0,[z389,z7,z3,z4,z45,z6]),(0,[z569,z1,z3,z4,z5,z268]),(0,[z1,z7,z3,z4,z5,z1034]),(0,[z1,z7,z57,z4,z302,z527])],[(0,[z1,z7,z3,z4,z988,z6]),(1,[z7,z3,z4,z857,z6]),(0,[z1,z779,z7,z3,z5,z6]),(0,[z1,z7,z1035,z4,z5,z6]),(0,[z1,z7,z3,z5,z51,z6]),(0,[z1,z7,z3,z264,z5,z459])],[(0,[z1,z7,z3,z1036,z4,z5]),(0,[z17,z7,z3,z10,z46,z6]),(0,[z1,z44,z3,z312,z5,z101]),(0,[z1,z20,z7,z3,z5,z218]),(0,[z1,z7,z3,z4,z5,z1037]),(0,[z1,z7,z3,z1038,z5,z21]),(0,[z1,z7,z3,z765,z5,z11])],[(0,[z0,z2,z3,z4,z120,z6]),(0,[z1,z7,z3,z4,z5,z1039]),(0,[z1,z7,z57,z4,z302,z58]),(0,[z1,z7,z3,z773,z5,z11]),(0,[z1,z7,z3,z742,z205,z6])],[(0,[z1,z7,z3,z4,z5,z1040]),(0,[z1,z7,z3,z4,z5,z527])]],
   [[(0,[z1,z7,z1041,z4,z5,z6]),(0,[z1,z7,z3,z1042,z5,z6]),(0,[z1043,z1,z7,z3,z5,z6]),(0,[z1,z7,z3,z10,z254,z6]),(0,[z1,z7,z3,z1044,z4,z5]),(0,[z1,z7,z1045,z3,z4,z5]),(0,[z1,z7,z3,z1046,z5,z6])],[(0,[z1,z7,z3,z186,z8,z6]),(0,[z1,z3,z4,z1047,z5,z6]),(0,[z270,z7,z3,z10,z5,z6]),(0,[z165,z7,z3,z4,z5,z738]),(0,[z1,z7,z3,z4,z1048,z6]),(0,[z1,z7,z3,z4,z1049,z21]),(0,[z1,z7,z22,z3,z4,z11])],[(0,[z1,z7,z3,z532,z5,z6]),(0,[z1,z7,z3,z1050,z5,z6]),(0,[z1,z1051,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z1004]),(0,[z1,z7,z3,z4,z1052,z6]),(0,[z1,z7,z3,z1053,z5,z6]),(0,[z261,z1,z7,z22,z3,z4])],[(0,[z1,z7,z3,z4,z5,z1054]),(0,[z1,z1055,z3,z4,z5,z6]),(0,[z1,z7,z3,z25,z5,z21]),(0,[z1,z7,z272,z114,z5,z6]),(0,[z1,z7,z3,z304,z5,z21]),(0,[z1,z7,z3,z4,z5,z1056]),(0,[z1,z3,z4,z5,z1017,z6])],[(0,[z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z1057]),(0,[z1,z7,z3,z1058,z5,z6]),(0,[z1,z7,z3,z4,z822,z125]),(0,[z1,z1059,z7,z3,z4,z5])],[(0,[z1,z7,z3,z18,z5,z317]),(0,[z340,z7,z3,z18,z5,z6]),(0,[z1,z7,z3,z435,z5,z11]),(0,[z248,z7,z3,z4,z5,z345]),(0,[z1,z7,z3,z4,z180,z67])],[(0,[z1,z1060,z7,z18,z5,z6]),(0,[z389,z7,z3,z18,z5,z6])],[(0,[z1,z7,z3,z4,z1061,z6]),(0,[z1,z7,z3,z4,z5,z108]),(0,[z140,z7,z43,z4,z5,z290]),(0,[z1,z7,z3,z4,z5,z1062]),(0,[z1,z7,z296,z4,z5,z21]),(0,[z1,z1063,z7,z3,z5,z21])]],
   [[(0,[z1,z110,z3,z4,z5,z6]),(0,[z1,z7,z3,z227,z8,z6]),(0,[z1,z74,z7,z3,z10,z5]),(0,[z1,z118,z3,z312,z5,z6]),(0,[z1,z643,z150,z4,z5,z6]),(0,[z1,z112,z150,z4,z5,z141]),(0,[z1,z36,z7,z4,z5,z11]),(0,[z708,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z826])],[(0,[z1,z1064,z3,z4,z5,z6]),(0,[z1,z111,z7,z3,z5,z202]),(0,[z1,z7,z1065,z4,z5,z6]),(0,[z1,z7,z3,z4,z67,z307]),(0,[z1,z7,z4,z5,z21,z484])],[(0,[z1,z7,z3,z4,z120,z6]),(0,[z1,z7,z298,z4,z5,z21]),(0,[z1,z7,z3,z18,z1066,z6]),(0,[z225,z1,z3,z18,z5,z268]),(0,[z1,z7,z300,z4,z5,z21]),(0,[z1,z7,z3,z4,z125,z21]),(0,[z1,z7,z3,z4,z1067,z6]),(0,[z7,z3,z4,z5,z1068,z21]),(0,[z1,z7,z3,z975,z5,z6]),(0,[z1,z20,z7,z3,z5,z258])],[(0,[z1,z7,z3,z4,z1069,z6]),(0,[z1,z7,z3,z18,z5,z209]),(0,[z1,z7,z3,z10,z5,z972]),(0,[z1,z7,z3,z10,z5,z283]),(0,[z1,z7,z3,z4,z5,z284]),(0,[z1,z7,z3,z4,z5,z1070]),(0,[z212,z1,z7,z3,z283,z205]),(0,[z1,z7,z3,z1071,z5,z6])],[(0,[z1,z7,z3,z1072,z5,z6]),(0,[z1,z7,z3,z4,z5,z738]),(0,[z1,z59,z7,z4,z576,z6]),(0,[z212,z1,z7,z3,z205,z21])],[(0,[z1,z7,z3,z4,z1073,z6]),(0,[z1,z7,z825,z3,z4,z6]),(0,[z1,z7,z3,z18,z32,z21]),(0,[z1,z7,z3,z52,z279,z5]),(0,[z273,z1,z7,z3,z5,z11]),(0,[z1,z116,z3,z609,z4,z5]),(0,[z1,z7,z178,z133,z5,z19]),(0,[z54,z1,z7,z4,z5,z11]),(0,[z248,z1,z20,z7,z3,z5]),(0,[z1,z314,z3,z4,z5,z419]),(0,[z1,z38,z7,z3,z5,z258])],[(0,[z198,z7,z3,z18,z5,z11]),(0,[z1,z44,z3,z75,z5,z6]),(0,[z124,z7,z3,z10,z5,z21]),(0,[z1,z7,z3,z10,z5,z134]),(0,[z1,z7,z3,z1074,z5,z6]),(0,[z1,z7,z3,z4,z5,z1075]),(0,[z1,z7,z3,z13,z5,z11]),(0,[z1,z7,z3,z4,z5,z288]),(0,[z1076,z7,z3,z4,z5,z6]),(0,[z1,z7,z40,z3,z4,z32]),(0,[z1,z7,z3,z4,z1077,z11]),(0,[z1,z7,z3,z1078,z5,z6])],[(0,[z1,z7,z1079,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z28])]],
   [[(0,[z1,z7,z3,z4,z1080,z6]),(0,[z1,z7,z3,z1081,z5,z6]),(0,[z1,z7,z3,z1082,z5,z6]),(0,[z1,z7,z3,z4,z5,z1083]),(0,[z1,z7,z293,z4,z5,z21]),(0,[z1,z7,z3,z4,z5,z1084]),(0,[z1,z7,z3,z4,z5,z1085]),(0,[z1,z7,z3,z4,z5,z1086])],[(0,[z1,z7,z3,z4,z24,z11]),(0,[z1,z7,z3,z10,z5,z299]),(0,[z1,z7,z178,z216,z5,z6]),(0,[z1,z255,z3,z4,z233,z21]),(0,[z1,z1087,z7,z3,z5,z21]),(0,[z1,z7,z3,z1088,z5,z6])],[(0,[z1,z303,z3,z10,z5,z6]),(0,[z1,z7,z3,z4,z8,z251]),(0,[z1,z7,z446,z4,z5,z21]),(0,[z1,z7,z3,z4,z30,z11]),(0,[z1,z7,z3,z4,z5,z1089]),(0,[z1,z1090,z7,z3,z5,z6]),(0,[z1,z7,z3,z5,z1091,z6])],[(0,[z1,z7,z3,z4,z1092,z6]),(0,[z1,z7,z298,z4,z24,z6]),(0,[z1,z7,z3,z4,z24,z393]),(0,[z1,z7,z4,z1093,z5,z6]),(0,[z1,z7,z749,z4,z5,z6]),(0,[z33,z7,z9,z4,z5,z11]),(0,[z513,z7,z3,z18,z5,z6]),(0,[z1,z7,z3,z18,z5,z19]),(0,[z1,z7,z327,z4,z5,z21]),(0,[z1,z7,z3,z1094,z5,z6]),(0,[z1,z1095,z3,z4,z5,z6]),(0,[z294,z1,z20,z7,z3,z5]),(0,[z1,z7,z4,z5,z11,z576])],[(0,[z1,z7,z4,z5,z1096,z6]),(0,[z1,z7,z3,z4,z5,z1097]),(0,[z1,z162,z3,z10,z147,z6]),(0,[z322,z1,z7,z3,z153,z6]),(0,[z1,z38,z7,z3,z4,z254]),(0,[z1,z119,z3,z4,z147,z6])],[(0,[z1,z7,z3,z186,z5,z21]),(0,[z7,z3,z10,z18,z5,z6]),(0,[z7,z3,z129,z10,z5,z6]),(0,[z1,z7,z3,z4,z5,z1098]),(0,[z1,z7,z731,z3,z4,z21])],[(0,[z179,z7,z3,z938,z5,z6]),(0,[z1,z27,z74,z7,z3,z5]),(0,[z1,z7,z4,z336,z5,z21]),(1,[z1,z7,z740,z5,z6]),(0,[z1,z7,z3,z1099,z5,z11]),(0,[z1,z7,z3,z168,z146,z6])],[(0,[z453,z7,z3,z18,z5,z6]),(0,[z165,z7,z3,z129,z4,z5]),(0,[z1,z7,z93,z3,z4,z5])]],
   [[(0,[z1,z7,z3,z4,z206,z21]),(0,[z1,z7,z3,z4,z5,z1100]),(0,[z1,z7,z3,z4,z5,z317]),(0,[z1,z7,z178,z133,z5,z11])],[(0,[z1,z7,z320,z4,z5,z183]),(0,[z1,z1060,z7,z4,z5,z6]),(0,[z1,z74,z7,z178,z3,z5]),(0,[z1,z20,z7,z3,z5,z268]),(0,[z1,z7,z3,z4,z1101,z6]),(0,[z1,z20,z7,z40,z3,z5])],[(0,[z144,z7,z3,z10,z5,z6]),(0,[z1,z7,z3,z10,z5,z1005]),(0,[z1,z7,z3,z367,z5,z21])],[(0,[z1,z7,z320,z4,z5,z11]),(0,[z1,z7,z4,z955,z5,z6]),(0,[z1,z7,z3,z4,z1102,z6]),(0,[z1,z508,z3,z4,z5,z218])],[(0,[z1,z7,z3,z18,z5,z183]),(0,[z1,z7,z3,z227,z5,z21]),(0,[z1,z7,z3,z938,z5,z6]),(0,[z1,z707,z7,z3,z18,z5])],[(0,[z1,z7,z320,z4,z5,z393]),(0,[z1,z7,z3,z1103,z5,z6]),(0,[z1,z7,z3,z4,z1066,z6]),(0,[z1,z38,z7,z3,z88,z5]),(0,[z1,z7,z3,z4,z5,z1104]),(0,[z273,z1,z7,z3,z208,z6]),(0,[z1,z7,z1105,z4,z5,z6]),(0,[z1,z7,z1106,z4,z5,z6]),(0,[z225,z1,z3,z4,z5,z268]),(0,[z1,z59,z7,z4,z103,z11]),(0,[z277,z1,z7,z3,z5,z95])],[(0,[z1,z7,z3,z4,z1107,z6]),(0,[z1,z7,z3,z5,z867,z6]),(0,[z1,z7,z3,z1108,z5,z6]),(0,[z1,z7,z3,z4,z5,z209])],[(0,[z1,z7,z3,z4,z5,z1109]),(0,[z1,z7,z3,z4,z5,z1110]),(0,[z261,z1,z3,z4,z5,z436])]],
   [[(0,[z33,z7,z9,z186,z5,z6]),(0,[z1,z7,z3,z1111,z5,z6]),(0,[z1,z7,z3,z18,z125,z6]),(0,[z7,z154,z3,z18,z5,z6]),(0,[z7,z3,z4,z857,z46,z6]),(0,[z1,z7,z4,z5,z1112,z6]),(0,[z1,z656,z3,z4,z233,z6]),(0,[z1,z20,z7,z3,z5,z317]),(0,[z1,z7,z4,z5,z826,z6]),(0,[z1,z7,z3,z4,z32,z21]),(0,[z1,z7,z3,z32,z51,z21]),(0,[z1,z7,z40,z3,z4,z482])],[(0,[z1,z7,z3,z1113,z5,z6]),(0,[z1,z7,z3,z4,z5,z1114]),(0,[z592,z1,z7,z3,z205,z6]),(0,[z1,z7,z1045,z3,z4,z125]),(0,[z1,z7,z1115,z3,z4,z6]),(0,[z1,z7,z622,z4,z5,z21]),(0,[z1,z7,z3,z4,z240,z67])],[(0,[z140,z7,z43,z295,z5,z6]),(0,[z7,z3,z4,z5,z857,z6])],[(0,[z1,z7,z3,z4,z5,z791]),(0,[z0,z2,z3,z4,z5,z183]),(0,[z0,z2,z3,z10,z5,z6]),(0,[z1,z7,z3,z18,z5,z456]),(0,[z1,z7,z3,z4,z1116,z6]),(0,[z1,z7,z3,z5,z355,z6]),(0,[z1,z38,z7,z3,z5,z317])],[(0,[z1,z16,z298,z4,z5,z6]),(0,[z15,z16,z3,z18,z5,z6]),(0,[z1,z303,z3,z4,z8,z6]),(0,[z1,z7,z3,z948,z5,z6]),(0,[z1,z7,z3,z1117,z18,z5]),(0,[z124,z7,z3,z938,z5,z6]),(0,[z1,z7,z460,z4,z5,z11]),(0,[z1,z7,z3,z4,z790,z6]),(0,[z1,z7,z1118,z4,z5,z6])],[(0,[z1,z7,z3,z18,z1023,z6]),(0,[z204,z7,z3,z10,z5,z6]),(0,[z1,z7,z3,z1119,z5,z6]),(0,[z1,z7,z22,z3,z4,z21])],[(0,[z1,z7,z3,z4,z1120,z6]),(0,[z1,z44,z3,z5,z176,z6]),(0,[z1,z7,z40,z3,z4,z245]),(0,[z1,z7,z3,z4,z5,z19])],[(0,[z1,z7,z3,z4,z5,z1121]),(0,[z33,z7,z9,z227,z5,z6]),(0,[z1,z7,z3,z4,z1122,z6]),(0,[z140,z7,z749,z4,z5,z6]),(0,[z1,z7,z3,z18,z85,z6]),(0,[z1,z7,z3,z18,z5,z1123]),(0,[z669,z7,z3,z4,z46,z6]),(0,[z1,z7,z3,z4,z180,z136]),(0,[z1,z38,z7,z3,z5,z332])]],
   [[(0,[z1,z7,z3,z52,z5,z34]),(0,[z1,z7,z178,z133,z5,z427]),(0,[z1,z20,z7,z3,z32,z21])],[(0,[z1,z7,z3,z4,z5,z1124]),(0,[z140,z7,z43,z4,z5,z11]),(0,[z1,z7,z3,z435,z5,z21]),(0,[z1,z7,z3,z52,z4,z254])],[(0,[z1,z7,z3,z295,z5,z6]),(0,[z1,z7,z3,z1125,z18,z5]),(0,[z1,z7,z3,z10,z5,z1040]),(0,[z1,z7,z3,z10,z5,z527]),(0,[z1,z7,z3,z4,z5,z141]),(0,[z1,z3,z4,z5,z268,z954]),(0,[z1,z797,z7,z3,z5,z21])],[(0,[z1,z7,z3,z1126,z5,z6]),(0,[z0,z2,z3,z107,z5,z6]),(0,[z1,z7,z3,z88,z18,z5]),(0,[z1,z7,z3,z5,z1127,z6]),(0,[z1,z7,z1128,z3,z10,z5]),(0,[z212,z1,z7,z3,z153,z6]),(0,[z1,z7,z3,z4,z5,z1129])],[(0,[z1,z7,z18,z5,z11,z21]),(0,[z1,z7,z3,z304,z5,z6]),(0,[z1,z7,z4,z5,z400,z21])],[(0,[z1,z301,z7,z4,z5,z21]),(0,[z1,z7,z541,z4,z5,z21]),(0,[z1,z7,z40,z3,z4,z79])],[(0,[z1,z7,z3,z1125,z4,z5]),(0,[z1,z7,z3,z159,z5,z11]),(0,[z1,z7,z3,z18,z8,z6]),(0,[z1,z7,z3,z18,z5,z427])],[(0,[z1,z7,z3,z4,z5,z183]),(0,[z1,z7,z3,z10,z5,z6]),(0,[z1,z7,z3,z253,z5,z6]),(0,[z1,z7,z3,z4,z1130,z5]),(0,[z294,z7,z3,z4,z5,z511])]],
   [[(0,[z1,z7,z3,z4,z5,z1131]),(0,[z1,z901,z7,z3,z5,z6]),(0,[z1,z7,z3,z10,z180,z67]),(0,[z1,z7,z57,z4,z722,z6])],[(0,[z33,z7,z9,z4,z5,z251]),(0,[z7,z3,z4,z45,z857,z6]),(0,[z273,z1,z7,z3,z5,z21]),(0,[z1,z7,z3,z52,z5,z203])],[(0,[z1,z7,z3,z18,z5,z58]),(0,[z550,z7,z3,z18,z5,z6]),(0,[z1,z7,z3,z13,z5,z21]),(0,[z908,z7,z3,z4,z5,z6]),(0,[z1,z7,z22,z3,z4,z67])],[(1,[z716,z3,z4,z5,z6]),(0,[z1,z7,z3,z1036,z159,z5]),(0,[z1,z110,z3,z10,z5,z6]),(0,[z1,z7,z3,z4,z125,z6]),(0,[z1,z7,z3,z1132,z5,z6]),(0,[z225,z1,z3,z4,z611,z5]),(0,[z1,z1133,z3,z4,z5,z6]),(0,[z1134,z1,z7,z3,z4,z5]),(1,[z1,z7,z4,z722,z6])],[(0,[z714,z1,z7,z3,z18,z5]),(0,[z1,z7,z1065,z10,z5,z6]),(0,[z1,z7,z3,z1135,z5,z6])],[(0,[z1,z7,z3,z10,z120,z6]),(0,[z1,z7,z3,z4,z24,z21]),(0,[z1,z7,z3,z1136,z5,z6]),(0,[z1,z1001,z7,z3,z4,z6]),(0,[z1,z7,z3,z4,z1137,z6]),(0,[z15,z16,z3,z532,z5,z6]),(0,[z1,z7,z1002,z3,z4,z6]),(0,[z1,z7,z3,z18,z180,z67]),(0,[z490,z7,z3,z4,z46,z6]),(0,[z1,z142,z3,z4,z5,z218]),(0,[z1,z3,z4,z5,z954,z6])],[(0,[z1,z7,z3,z1138,z5,z6]),(0,[z1,z74,z7,z3,z4,z5]),(0,[z1,z7,z3,z10,z5,z284]),(0,[z1,z7,z3,z1139,z5,z6]),(0,[z1,z7,z3,z4,z30,z21]),(0,[z836,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z456]),(0,[z1,z7,z3,z1140,z5,z6]),(0,[z1,z7,z4,z11,z32,z21])],[(0,[z1,z7,z3,z107,z5,z6]),(0,[z15,z16,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z1141]),(0,[z1,z7,z3,z18,z5,z108]),(0,[z33,z7,z9,z4,z5,z21]),(0,[z1,z7,z3,z4,z5,z1142]),(0,[z124,z7,z3,z10,z5,z6]),(0,[z1,z7,z3,z304,z5,z414]),(0,[z1,z7,z3,z1143,z5,z6]),(0,[z1,z112,z843,z4,z5,z6]),(0,[z1,z7,z3,z4,z208,z11]),(0,[z1,z20,z7,z5,z11,z21])]],
   [[(0,[z1,z7,z3,z4,z1144,z6]),(0,[z1,z7,z3,z18,z5,z49]),(0,[z1,z7,z3,z726,z18,z5]),(0,[z54,z1,z7,z10,z5,z11]),(0,[z1,z7,z22,z3,z4,z511]),(0,[z1,z7,z3,z4,z67,z796])],[(0,[z1,z7,z3,z4,z1145,z6]),(0,[z1,z7,z3,z4,z1146,z6]),(0,[z1,z7,z3,z10,z5,z288]),(0,[z165,z7,z3,z4,z5,z345]),(1,[z1,z3,z739,z5,z6]),(0,[z1,z7,z372,z4,z5,z21]),(0,[z1,z7,z3,z1147,z5,z6])],[(0,[z1,z1087,z7,z3,z5,z6]),(0,[z1,z7,z3,z4,z5,z1123]),(0,[z1,z7,z3,z10,z5,z28]),(0,[z1,z7,z3,z168,z406,z6]),(0,[z1,z7,z3,z1148,z5,z6]),(0,[z1,z255,z3,z4,z233,z6])],[(0,[z1,z7,z3,z4,z5,z1007]),(0,[z1,z7,z3,z1149,z5,z6]),(0,[z1,z7,z3,z4,z5,z1150]),(0,[z1151,z7,z3,z4,z5,z6]),(0,[z1,z7,z437,z4,z5,z21])],[(0,[z1,z7,z3,z4,z1152,z6]),(0,[z1,z7,z3,z1153,z5,z6]),(0,[z1,z7,z3,z4,z5,z1154]),(0,[z1,z7,z3,z4,z5,z1155]),(0,[z1,z7,z3,z4,z1156,z6]),(0,[z1,z303,z3,z4,z160,z6]),(0,[z682,z7,z43,z4,z5,z6]),(0,[z1,z7,z3,z185,z4,z45]),(0,[z1,z7,z3,z4,z5,z1157]),(0,[z1,z7,z3,z1158,z5,z6]),(0,[z1,z7,z178,z133,z5,z21])],[(0,[z1,z7,z3,z107,z120,z6]),(0,[z1,z7,z3,z4,z1159,z6]),(0,[z1,z7,z3,z1160,z5,z6]),(0,[z1,z856,z7,z3,z5,z290]),(0,[z1,z7,z1161,z4,z5,z6]),(0,[z1,z7,z3,z146,z14,z6])],[(0,[z1,z1162,z3,z4,z5,z6]),(0,[z1,z7,z3,z18,z5,z288]),(0,[z1,z7,z3,z18,z5,z1163]),(0,[z1,z7,z3,z933,z5,z6]),(1,[z1,z20,z7,z22,z3])],[(0,[z1,z7,z320,z4,z5,z21]),(0,[z1,z7,z3,z4,z5,z1164]),(0,[z1,z7,z3,z18,z5,z290]),(0,[z1,z7,z3,z18,z5,z28]),(0,[z1165,z7,z3,z4,z5,z6])]],
   [[(0,[z7,z3,z10,z938,z5,z6]),(0,[z1,z7,z1166,z4,z5,z6]),(0,[z1,z7,z366,z4,z5,z11])],[(0,[z1,z7,z3,z4,z8,z6]),(0,[z1,z943,z3,z4,z5,z6]),(0,[z1,z7,z3,z1167,z5,z6]),(0,[z165,z1,z20,z7,z3,z5]),(0,[z1,z7,z3,z4,z5,z1168]),(0,[z1,z7,z3,z4,z5,z1169]),(0,[z1,z387,z3,z4,z5,z218]),(0,[z1,z7,z3,z4,z5,z427]),(0,[z1,z59,z7,z4,z103,z21])],[(0,[z1,z7,z3,z4,z1170,z6]),(0,[z1,z7,z3,z1171,z5,z6])],[(0,[z1,z7,z149,z18,z5,z21]),(0,[z1,z7,z3,z10,z5,z317]),(0,[z1,z7,z3,z4,z5,z1172]),(0,[z1,z7,z3,z1173,z5,z6]),(0,[z1,z7,z3,z4,z5,z796])],[(0,[z1,z7,z3,z88,z10,z5]),(0,[z1,z7,z3,z760,z18,z5]),(0,[z1,z7,z3,z18,z5,z307]),(0,[z42,z7,z3,z4,z5,z97]),(0,[z1,z7,z3,z4,z5,z1174]),(0,[z1,z7,z3,z4,z5,z1175]),(0,[z1,z27,z7,z152,z5,z28])],[(0,[z1,z7,z3,z185,z18,z5]),(0,[z1,z7,z3,z18,z562,z5]),(0,[z1,z7,z3,z4,z254,z11]),(0,[z1,z7,z3,z4,z5,z954]),(0,[z1,z7,z3,z4,z5,z58]),(0,[z1,z7,z3,z5,z39,z795])],[(0,[z1,z7,z3,z4,z5,z1176]),(0,[z1,z7,z3,z18,z160,z6]),(0,[z1,z7,z3,z4,z1177,z6]),(0,[z1,z7,z3,z1178,z5,z6]),(0,[z1,z7,z3,z4,z957,z6]),(0,[z1,z7,z3,z4,z1179,z21])],[(0,[z225,z1,z7,z22,z3,z4])]],
   [[(0,[z1,z7,z320,z4,z24,z6]),(0,[z1,z7,z3,z774,z18,z5]),(0,[z1,z7,z3,z4,z5,z1180]),(0,[z1,z7,z3,z10,z5,z1104]),(0,[z225,z1,z3,z10,z5,z268]),(0,[z1,z1181,z3,z4,z5,z6]),(0,[z1,z7,z3,z1182,z5,z6]),(0,[z1,z7,z3,z4,z5,z1183])],[(0,[z1,z1184,z3,z4,z5,z6]),(0,[z1,z118,z3,z89,z5,z6]),(0,[z1,z7,z3,z10,z5,z209]),(0,[z1,z7,z22,z149,z4,z21]),(0,[z1,z798,z3,z4,z5,z11])],[(0,[z1,z7,z22,z3,z18,z6]),(0,[z501,z7,z3,z4,z5,z97]),(0,[z1,z7,z3,z1185,z5,z6]),(0,[z1,z7,z3,z1186,z5,z6]),(0,[z1,z7,z3,z5,z742,z6]),(1,[z1,z7,z3,z4,z796])],[(0,[z1,z7,z3,z10,z32,z21]),(0,[z1,z7,z3,z4,z5,z49])],[(0,[z7,z3,z88,z10,z18,z5]),(0,[z1,z7,z1187,z18,z5,z6]),(0,[z7,z472,z3,z18,z5,z6]),(0,[z99,z7,z3,z4,z5,z448]),(0,[z1,z7,z3,z4,z1188,z6]),(0,[z1,z162,z3,z355,z147,z6]),(0,[z1,z7,z3,z4,z5,z1189]),(0,[z1,z38,z7,z3,z5,z427])],[(0,[z140,z7,z43,z4,z5,z21]),(0,[z1,z7,z787,z3,z18,z5]),(0,[z1,z7,z3,z4,z5,z1190]),(0,[z1,z27,z7,z152,z5,z317]),(0,[z212,z1,z7,z93,z3,z205])],[(0,[z1,z110,z3,z4,z5,z108]),(0,[z1,z7,z3,z304,z5,z134]),(0,[z12,z7,z3,z304,z45,z6]),(0,[z1,z7,z3,z4,z5,z1191]),(0,[z1,z7,z178,z5,z131,z6]),(0,[z1,z20,z7,z22,z3,z5]),(0,[z1,z78,z3,z4,z5,z629])],[(0,[z1,z7,z3,z4,z1192,z6]),(0,[z1,z1193,z3,z4,z5,z6]),(0,[z1,z7,z3,z5,z1194,z6]),(0,[z1,z7,z3,z279,z5,z11]),(0,[z1,z7,z3,z4,z5,z1195]),(0,[z1,z7,z3,z4,z5,z1196])]],
   [[(0,[z444,z7,z3,z18,z5,z6]),(0,[z1,z7,z3,z4,z1197,z6]),(0,[z1,z1198,z3,z4,z5,z6])],[(0,[z1,z7,z3,z4,z5,z1163]),(0,[z1,z7,z3,z10,z5,z19]),(0,[z1,z7,z3,z1199,z5,z6]),(0,[z225,z1,z3,z4,z5,z954]),(0,[z1,z7,z57,z4,z302,z21])],[(0,[z1,z7,z3,z1200,z5,z6]),(0,[z1,z7,z3,z159,z5,z21]),(0,[z1,z7,z3,z1201,z5,z6]),(0,[z1,z7,z3,z4,z5,z290]),(0,[z1,z7,z3,z186,z5,z251]),(0,[z1,z74,z7,z602,z3,z5]),(0,[z7,z3,z18,z5,z448,z6]),(0,[z1,z112,z150,z4,z5,z11]),(0,[z1202,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z1203]),(0,[z1,z7,z3,z4,z5,z1204]),(0,[z1,z1205,z7,z3,z4,z5])],[(0,[z1,z7,z3,z1206,z5,z6]),(0,[z12,z7,z3,z4,z45,z11]),(0,[z1,z7,z3,z4,z769,z208])],[(0,[z1,z7,z4,z481,z5,z21]),(0,[z1,z44,z3,z312,z5,z6]),(0,[z77,z1,z3,z98,z5,z11]),(0,[z1,z7,z3,z4,z5,z1207]),(0,[z1,z7,z3,z1208,z5,z6]),(0,[z1,z7,z4,z5,z11,z56])],[(0,[z1,z7,z3,z10,z5,z141]),(0,[z1,z7,z272,z133,z5,z6]),(0,[z1,z7,z272,z4,z5,z21]),(0,[z1,z623,z3,z4,z147,z6]),(0,[z1,z7,z3,z385,z5,z21]),(0,[z1,z7,z3,z894,z5,z21])],[(0,[z1,z7,z3,z4,z1209,z6]),(0,[z77,z1,z3,z739,z5,z6]),(0,[z1,z7,z3,z4,z6,z811]),(0,[z1,z7,z149,z4,z5,z21])],[(0,[z1,z303,z3,z4,z5,z11]),(0,[z1,z59,z7,z18,z103,z6]),(0,[z1210,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z307])]],
   [[(0,[z1,z7,z3,z4,z5,z1211]),(0,[z1,z7,z3,z4,z562,z5]),(0,[z1,z7,z3,z4,z5,z1212]),(0,[z1,z7,z22,z3,z52,z4]),(0,[z1,z7,z3,z4,z180,z32]),(0,[z1,z7,z3,z1213,z5,z6])],[(0,[z1,z931,z7,z3,z4,z5]),(0,[z1,z7,z3,z4,z1214,z5]),(0,[z1,z7,z3,z4,z160,z6]),(0,[z1,z1215,z3,z4,z5,z6]),(0,[z1,z7,z3,z227,z5,z251]),(0,[z1,z7,z3,z4,z1216,z6]),(0,[z1,z7,z820,z3,z18,z5]),(0,[z1,z743,z3,z4,z5,z6]),(0,[z1,z7,z1128,z3,z4,z5]),(0,[z1,z162,z3,z4,z147,z11]),(0,[z1,z255,z3,z4,z1017,z6]),(0,[z1,z1217,z7,z3,z4,z5]),(0,[z1,z1218,z3,z4,z5,z6]),(0,[z1,z7,z3,z52,z5,z357])],[(0,[z1,z7,z1219,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z1220]),(0,[z1,z7,z3,z10,z5,z183]),(0,[z1,z7,z3,z18,z5,z141]),(0,[z1,z7,z3,z1221,z5,z6]),(0,[z273,z1,z7,z3,z5,z6]),(0,[z1,z7,z316,z4,z5,z11]),(0,[z1,z7,z3,z5,z741,z21])],[(0,[z1,z1222,z7,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z1223]),(0,[z1,z7,z3,z13,z5,z6]),(0,[z179,z7,z3,z18,z5,z11]),(0,[z1,z7,z3,z4,z1077,z6]),(0,[z1,z7,z3,z4,z208,z21]),(0,[z1,z7,z40,z3,z4,z58]),(0,[z1,z7,z470,z4,z5,z11]),(0,[z1,z38,z7,z3,z285,z5])],[(0,[z1,z7,z320,z4,z5,z873]),(0,[z1,z7,z3,z321,z5,z183]),(0,[z99,z7,z3,z4,z5,z738])],[(0,[z1,z7,z3,z1224,z5,z6]),(0,[z1,z110,z3,z4,z160,z6]),(0,[z100,z7,z3,z18,z5,z6]),(0,[z1,z7,z3,z185,z5,z355]),(0,[z1,z3,z4,z233,z1017,z6])],[(0,[z1,z7,z3,z321,z5,z11]),(0,[z1,z7,z3,z1225,z5,z6]),(0,[z1,z7,z3,z10,z125,z6]),(0,[z1,z7,z3,z185,z10,z5]),(0,[z1,z7,z3,z4,z5,z1226]),(0,[z1,z7,z3,z4,z1017,z6])],[(0,[z1,z348,z48,z4,z5,z6]),(0,[z1,z7,z1187,z4,z5,z6]),(0,[z1,z7,z843,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z1227]),(0,[z1,z20,z7,z3,z480,z5]),(0,[z1,z7,z3,z4,z1006,z11])]],
   [[(0,[z1,z7,z298,z321,z5,z6]),(0,[z1,z7,z3,z321,z5,z393]),(0,[z1,z7,z3,z4,z5,z1228]),(1,[z7,z749,z4,z5,z6]),(0,[z1,z7,z926,z3,z4,z290]),(0,[z1,z7,z3,z740,z5,z6]),(0,[z1,z7,z3,z5,z919,z21]),(0,[z1,z20,z7,z3,z5,z436])],[(0,[z1,z7,z3,z4,z5,z1229]),(0,[z1,z7,z3,z18,z5,z11]),(0,[z1,z7,z3,z10,z5,z456]),(0,[z1,z7,z804,z3,z4,z208]),(0,[z1,z508,z7,z22,z3,z4])],[(0,[z1,z7,z3,z107,z5,z183]),(0,[z1,z7,z3,z4,z5,z1230]),(0,[z15,z16,z3,z10,z5,z6]),(0,[z7,z3,z18,z5,z477,z6]),(0,[z99,z617,z7,z3,z4,z5]),(0,[z1,z7,z3,z4,z5,z1231]),(0,[z1232,z7,z3,z4,z5,z6])],[(0,[z1,z7,z298,z18,z5,z6]),(0,[z1,z7,z3,z18,z5,z393]),(0,[z1,z7,z3,z1233,z18,z5]),(0,[z1,z707,z7,z3,z4,z5]),(0,[z1,z7,z22,z3,z10,z6]),(0,[z17,z7,z3,z435,z46,z6]),(0,[z1,z7,z3,z4,z5,z1234]),(0,[z1,z7,z3,z1099,z5,z6]),(0,[z1,z7,z3,z4,z796,z41])],[(0,[z1,z303,z3,z186,z5,z6]),(0,[z1,z7,z3,z10,z1146,z6]),(0,[z1,z7,z3,z4,z1029,z6]),(0,[z225,z1,z3,z4,z5,z436]),(0,[z1,z7,z768,z3,z4,z21])],[(0,[z1,z7,z3,z10,z85,z6]),(0,[z1,z255,z3,z10,z233,z6]),(0,[z510,z7,z3,z10,z5,z6]),(0,[z1,z7,z3,z4,z1032,z6])],[(0,[z1,z7,z3,z4,z1235,z6]),(0,[z1,z7,z3,z724,z4,z5]),(0,[z1,z7,z3,z13,z5,z414]),(0,[z1,z7,z458,z4,z5,z11]),(0,[z1,z27,z7,z152,z5,z11])],[(0,[z140,z7,z43,z25,z5,z6]),(0,[z1,z3,z18,z5,z842,z6]),(0,[z1,z7,z3,z1233,z4,z5]),(0,[z1,z7,z3,z4,z5,z1236]),(0,[z1,z162,z3,z4,z1017,z6])]],
   [[(0,[z0,z2,z3,z4,z5,z11]),(0,[z1,z7,z3,z5,z1237,z6]),(0,[z1,z7,z3,z1238,z5,z6]),(0,[z179,z7,z3,z88,z18,z5]),(0,[z105,z1,z3,z98,z5,z6]),(0,[z1,z7,z3,z10,z1159,z6]),(0,[z1,z7,z3,z4,z5,z1239]),(0,[z1,z162,z3,z185,z4,z147]),(0,[z1,z7,z3,z4,z5,z1240])],[(0,[z1,z7,z1241,z4,z5,z6]),(1,[z7,z3,z938,z5,z6]),(0,[z1,z7,z3,z4,z254,z21]),(0,[z1,z3,z4,z5,z954,z218]),(0,[z1,z7,z3,z1038,z5,z6])],[(0,[z0,z2,z298,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z393]),(0,[z1,z1242,z3,z4,z5,z6]),(0,[z1,z7,z3,z18,z5,z718]),(0,[z1,z255,z3,z18,z233,z6]),(0,[z99,z7,z3,z4,z5,z97]),(0,[z1,z7,z3,z4,z5,z101]),(0,[z1,z59,z7,z4,z103,z6])],[(0,[z15,z716,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z1243]),(0,[z1,z303,z3,z227,z5,z6]),(0,[z1,z7,z3,z1117,z4,z5]),(0,[z1,z7,z3,z5,z1244,z6]),(0,[z1,z7,z4,z5,z384,z21]),(0,[z165,z7,z3,z4,z206,z181]),(0,[z1,z540,z3,z4,z147,z6]),(0,[z1,z7,z3,z4,z947,z21])],[(0,[z1,z7,z1245,z4,z5,z6]),(0,[z1,z7,z3,z4,z1246,z6]),(0,[z1,z7,z3,z4,z1247,z6]),(0,[z1,z7,z3,z10,z8,z6]),(0,[z1,z7,z3,z10,z5,z427]),(0,[z1,z7,z3,z4,z857,z6]),(0,[z1,z7,z3,z1248,z5,z6])],[(0,[z1,z7,z3,z4,z1249,z6]),(0,[z1,z7,z3,z4,z1049,z6]),(0,[z281,z7,z3,z18,z5,z6]),(0,[z1,z7,z40,z3,z4,z307]),(0,[z1,z7,z4,z5,z11,z21]),(0,[z1,z7,z22,z3,z409,z4])],[(0,[z551,z7,z3,z18,z5,z6]),(0,[z1,z44,z3,z312,z5,z209]),(0,[z1,z429,z7,z4,z5,z11])],[(0,[z1,z7,z3,z1250,z5,z6]),(0,[z1,z7,z3,z25,z5,z6]),(0,[z1,z7,z3,z4,z5,z1251]),(0,[z1,z7,z3,z4,z1179,z6]),(0,[z1,z7,z3,z18,z733,z6]),(0,[z267,z7,z3,z18,z5,z6]),(0,[z1,z7,z3,z1252,z5,z6]),(1,[z1,z7,z3,z742,z6])]],
   [[(0,[z1,z7,z3,z4,z5,z1253]),(0,[z1,z463,z3,z75,z5,z6]),(0,[z1,z7,z3,z10,z5,z58]),(0,[z1,z7,z3,z4,z5,z1254]),(0,[z1,z7,z178,z740,z5,z6]),(0,[z1,z7,z57,z4,z302,z11]),(0,[z1,z7,z3,z4,z959,z21]),(0,[z1,z20,z7,z3,z5,z39])],[(0,[z1,z7,z3,z18,z206,z6]),(0,[z1,z7,z40,z3,z18,z41]),(0,[z589,z7,z3,z10,z5,z6])],[(0,[z1,z7,z3,z88,z4,z5]),(0,[z1,z7,z4,z5,z408,z21]),(0,[z1,z7,z3,z5,z11,z51]),(0,[z1,z7,z22,z3,z4,z41]),(0,[z1,z38,z7,z3,z5,z95])],[(0,[z1,z7,z3,z1255,z5,z6]),(0,[z1,z1181,z3,z10,z5,z6]),(0,[z1,z7,z3,z279,z5,z21]),(0,[z1,z1063,z7,z3,z5,z6]),(0,[z1,z7,z40,z3,z4,z324])],[(0,[z1,z7,z3,z4,z5,z11]),(0,[z1,z7,z3,z385,z5,z11]),(0,[z212,z1,z7,z3,z742,z6])],[(0,[z1,z303,z3,z4,z5,z251]),(0,[z1,z7,z3,z10,z5,z108]),(0,[z1,z7,z3,z4,z900,z6]),(0,[z1,z7,z3,z1256,z5,z6]),(0,[z1,z7,z3,z4,z898,z11])],[(0,[z1,z7,z298,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z393]),(0,[z1,z110,z9,z4,z5,z6]),(0,[z7,z3,z18,z5,z6,z524]),(0,[z1,z7,z3,z10,z5,z49]),(0,[z1,z112,z150,z4,z5,z21]),(0,[z1,z7,z3,z4,z1257,z5]),(0,[z7,z3,z4,z5,z1068,z6]),(0,[z1,z7,z3,z4,z5,z1258])],[(0,[z680,z16,z3,z4,z5,z6]),(0,[z7,z3,z18,z5,z11,z448]),(0,[z12,z7,z3,z4,z45,z21]),(0,[z1,z7,z3,z4,z5,z1259]),(0,[z1,z7,z3,z1260,z5,z6])]]]

def SA : ℕ × List W → Bool := fun c => !inB2 8 256 bkA c

def SB : ℕ × List W → Bool := fun c => !inB2 8 256 bkB c

def parents : List (ℕ × List W) := expandN 0 (level0 8 rows)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem gf : allGoalFree 0 (level0 8 rows) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pa0 : chunkB SA 2 ((parents.drop 0).take 1) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem paend : ((parents.drop 1)).isEmpty = true := by
  decide +kernel

theorem windowsA : windowsG (chunkB SA 2) parents 0 [1] = true :=
  windowsG_cons pa0 (windowsG_nil paend)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 509) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 509).take 517) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1026).take 341) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1367)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [509, 517, 341] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 92).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 92).take 87).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 179).take 77).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [92, 87, 77] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_nil pcend)))

theorem reject : search 8 rows = false :=
  search_false_C2 (dp := 0) (J := 5) (d := 2) (g1 := 8) (nb1 := 256) (g2 := 8) (nb2 := 256) (by norm_num) gf windowsC windowsB windowsA

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem witness_ok : ∀ x : Fin 6 → Bool, Circuit.eval witness (List.ofFn x) = target x := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sample_ok : ∀ k : Fin 256, target (fun i => (rows.getD i.val 0)[k.val]) = (~~~goal)[k.val] := by
  decide +kernel

theorem solve (s : ℕ) (hs : HasCircuitSize 6 target s) :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = target x := by
  obtain ⟨C, fits, size, computes⟩ := hs
  by_cases hasNot : ∃ g ∈ C.gates, g.op = GateOp.not
  · obtain ⟨g, mem, op⟩ := hasNot
    have short : binaryCost C.gates < C.size :=
      (List.length_filter_lt_length_iff_exists (p := isBinary)).mpr
        ⟨g, mem, by simp [isBinary, op]⟩
    have bound := bound_from_search rows rfl (by decide) reject sample_ok C.gates C.output fits computes
    refine ⟨witness, by simp [Monotone2, witness], ?_, witness_ok⟩
    change 10 ≤ s
    omega
  · refine ⟨C, ?_, size, computes⟩
    intro g mem
    obtain ⟨op, cap⟩ := fits g mem
    change g.op = .and ∨ g.op = .or ∨ g.op = .not at op
    exact ⟨op.elim Or.inl (fun h => h.elim Or.inr (fun eq => (hasNot ⟨g, mem, eq⟩).elim)), cap⟩

end PEqualNP.Outside.L_meta_38941

theorem PEqualNP.Outside.L_meta_38941 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809440 * 2 ^ 32 + 4276789408) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809440 * 2 ^ 32 + 4276789408) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_38941.solve