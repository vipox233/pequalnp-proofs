import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_39219

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
  Nat.testBit (4277071598 * 2 ^ 32 + 4276152480) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x8008822221c216a2#64 ++ 0x84004411110e10b5#64 ++ 0x4059a66623c63ffb#64 ++ 0xfa02cd33311e31ff#64 : BitVec 256),
   (0x000a08a82c58cb83#64 ++ 0x080050454162c65c#64 ++ 0xf8ae59b83c79cf97#64 ++ 0xf7c572cdc1e3ce7c#64 : BitVec 256),
   (0x033061c0c02d6154#64 ++ 0x5019830e06016b0a#64 ++ 0xe73061c1c07ff1ff#64 ++ 0x6f39830e0e03ff8f#64 : BitVec 256),
   (0x0dc07e015681bc08#64 ++ 0x606e03f00ab40de0#64 ++ 0xcfc07e01ff81fe1e#64 ++ 0xde7e03f00ffc0ff0#64 : BitVec 256),
   (0x16ff8001bb76000f#64 ++ 0x80b7fc000ddbb000#64 ++ 0xd7ff8001fffe000e#64 ++ 0x3ebffc000ffff000#64 : BitVec 256),
   (0x07f5755400000010#64 ++ 0x003fabaaa0000000#64 ++ 0xfffffffe00000001#64 ++ 0xfffffffff0000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.or, [0, 4]⟩, ⟨.or, [1, 4]⟩, ⟨.and, [3, 8]⟩, ⟨.and, [2, 9]⟩, ⟨.or, [2, 9]⟩, ⟨.and, [11, 7]⟩, ⟨.or, [12, 5]⟩, ⟨.and, [6, 13]⟩, ⟨.or, [14, 10]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x000a08a82c58cb83 0x080050454162c65c 0xf8ae59b83c79cf97 0xf7c572cdc1e3ce7c

def z1 : W := mkw 0x023a0000a8740007 0x0011d0000543a000 0xd7be0001fc7e000e 0x3ebdf0000fe3f000

def z2 : W := mkw 0x033061c0c02d6154 0x5019830e06016b0a 0xe73061c1c07ff1ff 0x6f39830e0e03ff8f

def z3 : W := mkw 0x07f5755400000010 0x003fabaaa0000000 0xfffffffe00000001 0xfffffffff0000000

def z4 : W := mkw 0x0dc07e015681bc08 0x606e03f00ab40de0 0xcfc07e01ff81fe1e 0xde7e03f00ffc0ff0

def z5 : W := mkw 0x16ff8001bb76000f 0x80b7fc000ddbb000 0xd7ff8001fffe000e 0x3ebffc000ffff000

def z6 : W := mkw 0x8008822221c216a2 0x84004411110e10b5 0x4059a66623c63ffb 0xfa02cd33311e31ff

def z7 : W := mkw 0x033069e8c42debd4 0x5819834f46216f5e 0xef3079f9c07fffff 0xef7983cfce03ffff

def z8 : W := mkw 0x0100600040012000 0x4008030002000900 0xc7006001c001f01e 0x4e3803000e000f80

def z9 : W := mkw 0x0ff57f555681bc18 0x607fabfaaab40de0 0xffffffffff81fe1f 0xfffffffffffc0ff0

def z10 : W := mkw 0x0230000080240004 0x0011800004012000 0x87200001c0380004 0x043900000e01c000

def z11 : W := mkw 0x04c0000112000008 0x0026000008900000 0xc7c00001ff80000e 0x1e3e00000ffc0000

def z12 : W := mkw 0x96ff8223bbf616af 0x84b7fc111ddfb0b5 0xd7ffa667fffe3fff 0xfebffd333ffff1ff

def z13 : W := mkw 0x80088022214202a2 0x84004401110a1015 0x4059806623c601eb 0x3a02cc03311e300f

def z14 : W := mkw 0x123f8000a9760007 0x8091fc00054bb000 0x507f800023fe000a 0x3a83fc00011ff000

def z15 : W := mkw 0x0100600040012000 0x4008030002000900 0x07002001c0003008 0x083801000e000180

def z16 : W := mkw 0x0000000000000000 0x0000000000000000 0xf8ae59b800000001 0xf7c572cdc0000000

def z17 : W := mkw 0x0dc07e015681bc08 0x606e03f00ab40de0 0x07402601ff81fe1e 0x083a01300ffc0ff0

def z18 : W := mkw 0x17f5f5559326001c 0x80bfafaaac993000 0x0751a647c3860008 0x083a8d323e1c3000

def z19 : W := mkw 0x0cc00a015681bc08 0x606600500ab40de0 0xc7c00001ff81fe1e 0x1e3e00000ffc0ff0

def z20 : W := mkw 0x0008800021420002 0x80004400010a1000 0x4059a04023c631fb 0x7a02cd02011e318f

def z21 : W := mkw 0x033061c0c02d6154 0x5019830e06016b0a 0xe779e7e7c07ff1ff 0xff3bcf3f3e03ff8f

def z22 : W := mkw 0x000208880c18c901 0x080010444060c648 0xf8a659983c39ce16 0xd7c532ccc1e1ce70

def z23 : W := mkw 0x010061c040096150 0x5008030e02004b0a 0xe02061c00079f1f7 0x6701030e0003cf8f

def z24 : W := mkw 0x0ff07f415681bc18 0x607f83fa0ab40de0 0xeff07fc1ff81fe1f 0xff7f83fe0ffc0ff0

def z25 : W := mkw 0x06f5155400000010 0x0037a8aaa0000000 0x38ff9ffe00000001 0xb1c7fcfff0000000

def z26 : W := mkw 0x0000020000801400 0x00000010000400a0 0x0000000023803e1a 0x00000000011c01f0

def z27 : W := mkw 0x16f700019a34000d 0x00b7b8000cd1a000 0x97a60001dc380004 0x04bd30000ee1c000

def z28 : W := mkw 0x16ff88a9bf7ecb8f 0x88b7fc454dfbf65c 0xffffd9b9ffffcf9f 0xfffffecdcffffe7c

def z29 : W := mkw 0x96ff8203bbf6142f 0x84b7fc101ddfb0a1 0xd7ffa647fffe306e 0x3ebffd323ffff183

def z30 : W := mkw 0x07f575d4c02d6154 0x503fabaea6016b0a 0xffffffffc07ff1ff 0xfffffffffe03ff8f

def z31 : W := mkw 0x17fff555bb76001f 0x80bfffaaaddbb000 0xfffffffffffe000f 0xfffffffffffff000

def z32 : W := mkw 0x14cf88a93f5acb8b 0x88a67c4549fad65c 0xf8efd9b83ff9cf97 0xf7c77ecdc1ffce7c

def z33 : W := mkw 0x0000020000801400 0x00000010000400a0 0x4059a66623803e1b 0xfa02cd33311c01f0

def z34 : W := mkw 0x8dc8fe2377c3beaa 0xe46e47f11bbe1df5 0xcfc07e01ffc7fffe 0xde7e03f00ffe3fff

def z35 : W := mkw 0x033061c0c02d6154 0x5019830e06016b0a 0x271061c1c007f1f9 0x4938830e0e003f8f

def z36 : W := mkw 0x16ff9415bb76000f 0x80b7fca0addbb000 0xdfff9e3ffffe000e 0xbefffcf1fffff000

def z37 : W := mkw 0x16ff8001bb76000f 0x80b7fc000ddbb000 0xd7ffa041fffe31ff 0x7ebffd020ffff18f

def z38 : W := mkw 0x0100755400000010 0x000803aaa0000000 0x28007ffe00000001 0xc14003fff0000000

def z39 : W := mkw 0x09007e004481bc00 0x604803f002240de0 0x08007e000001fe10 0xc04003f000000ff0

def z40 : W := mkw 0x000808a82448cb82 0x080040454122465c 0x680859b82041cf93 0xf34042cdc1020e7c

def z41 : W := mkw 0x0000000000000000 0x0000000000000000 0xc00040000001c016 0x4600020000000e00

def z42 : W := mkw 0x8008822221c216a2 0x84004411110e10b5 0x0051a64623c63ffa 0x08028d32311e31ff

def z43 : W := mkw 0x000a000028500003 0x0000500001428000 0xd0ae00003c780006 0x3685700001e3c000

def z44 : W := mkw 0x07f575d4802c4154 0x103fabaea401620a 0xfffffffe007e01e1 0xfffffffff003f00f

def z45 : W := mkw 0x000a08a82c58cb83 0x080050454162c65c 0xf8be79f83c7fffff 0xffc5f3cfc1e3ffff

def z46 : W := mkw 0x07f57554c0252054 0x503fabaaa6012902 0xffffffffc0063069 0xfffffffffe003183

def z47 : W := mkw 0x023001c0802c4154 0x1011800e0401620a 0x203001c0007e01e1 0x2101800e0003f00f

def z48 : W := mkw 0x0000080004008800 0x0000004000200440 0xc88058003c01ce16 0xd64402c001e00e70

def z49 : W := mkw 0x0dca7ea97ed9ff8b 0x686e53f54bf6cffc 0xffee7fb9fff9ff9f 0xffff73fdcfffcffc

def z50 : W := mkw 0x000a08a82c58cb83 0x080050454162c65c 0xe02041803c79cf97 0x6701020c01e3ce7c

def z51 : W := mkw 0x0000000000000000 0x0000000000000000 0x40102040004631fb 0x6a0081020002318f

def z52 : W := mkw 0x8338e3e2e1ef77f6 0xd419c71f170f7bbf 0xe779e7e7e3ffffff 0xff3bcf3f3f1fffff

def z53 : W := mkw 0x06f5015400000010 0x0037a80aa0000000 0xf7ff81fe00000001 0x3fbffc0ff0000000

def z54 : W := mkw 0x94cf82233bd216ab 0x84a67c1119de90b5 0x10cf86263f800e00 0x90867c3131fc0070

def z55 : W := mkw 0x8338e362e1e736f6 0xd419c71b170f39b7 0x4759a667e3c63ffb 0xfa3acd333f1e31ff

def z56 : W := mkw 0x080a0aa97ed9ff8b 0x684050554bf6cffc 0x00000001fff9ff9e 0x000000000fffcffc

def z57 : W := mkw 0x8008822221c216a2 0x84004411110e10b5 0x0049862623800e00 0x90024c31311c0070

def z58 : W := mkw 0x0000000000000000 0x0000000000000000 0x4059a66600000001 0xfa02cd3330000000

def z59 : W := mkw 0x000a08a82c58cb83 0x080050454162c65c 0xf8fffffe3c79cf97 0xffc7fffff1e3ce7c

def z60 : W := mkw 0x0dc07e015681bc08 0x606e03f00ab40de0 0x08c07e003f81fe10 0xd04603f001fc0ff0

def z61 : W := mkw 0x000a008028584103 0x000050040142c208 0xf0ae41803c79c197 0x7785720c01e3ce0c

def z62 : W := mkw 0x033561d4c02d6154 0x5019ab0ea6016b0a 0xf73fe1ffc07ff1ff 0x6fb9ff0ffe03ff8f

def z63 : W := mkw 0x133fe1c0e97f6157 0xd099ff0e074bfb0a 0xf73fe1c1c07ff1ff 0x6fb9ff0e0e03ff8f

def z64 : W := mkw 0x03306140c0252054 0x5019830a06012902 0xc7106041c007f07e 0x4e3883020e003f83

def z65 : W := mkw 0x07f575d440096150 0x503fabaea2004b0a 0xfffffffe0001f1f1 0xfffffffff0000f8f

def z66 : W := mkw 0x06ff08a82c58cb83 0x0837f8454162c65c 0xffffd9b83c79cf97 0xfffffecdc1e3ce7c

def z67 : W := mkw 0x8908fe2265c3bea2 0xe44847f1132e1df5 0x4859fe6623c7fffb 0xfa42cff3311e3fff

def z68 : W := mkw 0x8008822221c216a2 0x84004411110e10b5 0xf8fffffe23c63ffb 0xffc7fffff11e31ff

def z69 : W := mkw 0x800a8aaa2ddadfa3 0x8c005455516ed6fd 0xf8fffffe3fffffff 0xffc7fffff1ffffff

def z70 : W := mkw 0x00000080c02d6144 0x5000000406016b0a 0x00000001c07ff1fe 0x000000000e03ff8f

def z71 : W := mkw 0x04c5141400000000 0x002628a0a0000000 0x18cf9e3e00000000 0x90c67cf1f0000000

def z72 : W := mkw 0x033061c0c02d6154 0x5019830e06016b0a 0xa7204181c039c004 0x0539020c0e01ce00

def z73 : W := mkw 0x09007fc04489fd50 0x704803fe02244fea 0x28007fc00001fff1 0xc14003fe00000fff

def z74 : W := mkw 0x80000222008016a0 0x04000011100400b5 0x4040266623803ffb 0xda020133311c01ff

def z75 : W := mkw 0x0230000080240004 0x0011800004012000 0xc7300001c07e000e 0x2e3980000e03f000

def z76 : W := mkw 0x17ffe1c1fb7f615f 0xd0bfff0e0fdbfb0a 0xf7ffe1c1fffff1ff 0x7fbfff0e0fffff8f

def z77 : W := mkw 0x16ff8000a9760007 0x80b7fc00054bb000 0xd7ff8000007e0000 0x3ebffc000003f000

def z78 : W := mkw 0x16ff8001bb76000f 0x80b7fc000ddbb000 0xd7ffa667fffe000f 0xfebffd333ffff000

def z79 : W := mkw 0x000a00a828584383 0x080050054142c21c 0xf0ae01b83c780187 0x3785700dc1e3c00c

def z80 : W := mkw 0x96ff8023bb7602af 0x84b7fc011ddbb015 0xd7ff8067fffe01ef 0x3ebffc033ffff00f

def z81 : W := mkw 0x0dc87e2176c1be8a 0x606e43f10bb60df4 0xcfc87e21ffc1ff9f 0xfe7e43f10ffe0ffc

def z82 : W := mkw 0x010061c0c02d6154 0x5008030e06016b0a 0x200061c1c07ff1ff 0x4100030e0e03ff8f

def z83 : W := mkw 0x1ffffe01fff7bc0f 0xe0fffff00fffbde0 0xdffffe01fffffe1e 0xfefffff00ffffff0

def z84 : W := mkw 0x16f580019326000c 0x80b7ac000c993000 0x07518001c3860008 0x083a8c000e1c3000

def z85 : W := mkw 0x14cf80013b52000b 0x80a67c0009da9000 0x10cf80003f800000 0x10867c0001fc0000

def z86 : W := mkw 0x87fffffe2ddadfb3 0x8c3ffffff16ed6fd 0xfffffffe3fffffff 0xfffffffff1ffffff

def z87 : W := mkw 0x0002008808184101 0x080010044040c208 0x3026019800380000 0x0181300cc001c000

def z88 : W := mkw 0x94cf82233bd216ab 0x84a67c1119de90b5 0x50dfa6663fc63ffb 0xfa86fd3331fe31ff

def z89 : W := mkw 0x80088022214202a2 0x84004401110a1015 0x00198066004601e1 0x2000cc033002300f

def z90 : W := mkw 0x000a08a82c58cb83 0x080050454162c65c 0x000000003c79cf96 0x0000000001e3ce7c

def z91 : W := mkw 0x07f5755400000010 0x003fabaaa0000000 0x0751a64600000000 0x083a8d3230000000

def z92 : W := mkw 0x100a8001bb76000f 0x808054000ddbb000 0xd0ae0001fffe000e 0x368570000ffff000

def z93 : W := mkw 0x80088a2225c29ea2 0x84004451112e14f5 0xc8d9fe663fc7ffff 0xfe46cff331fe3fff

def z94 : W := mkw 0x05c0740000000000 0x002e03a000000000 0xcfc07e0000000000 0xde7e03f000000000

def z95 : W := mkw 0x08000a015681bc08 0x604000500ab40de0 0x00000001ff81fe1e 0x000000000ffc0ff0

def z96 : W := mkw 0x000a08002c508803 0x0000504001628440 0xd8ae58003c79ce16 0xf6c572c001e3ce70

def z97 : W := mkw 0x06f5000000000000 0x0037a80000000000 0xffffd9b800000001 0xfffffecdc0000000

def z98 : W := mkw 0x033269c8cc3de955 0x5819934e4661ef4a 0xffb679d9dc7ff1ff 0x6ffdb3cecee3ff8f

def z99 : W := mkw 0x033a69e82c58cb93 0x0819d34f4162c65c 0xffbe79f83c79cf97 0xfffdf3cfc1e3ce7c

def z100 : W := mkw 0x0cc01e0116809c08 0x206600f008b404e0 0x08c01e003f800e00 0x904600f001fc0070

def z101 : W := mkw 0x8dc8fe2377c3beaa 0xe46e47f11bbe1df5 0xcfd9fe67ffc7ffff 0xfe7ecff33ffe3fff

def z102 : W := mkw 0x96ff8223bbf616af 0x84b7fc111ddfb0b5 0xd7ff8627fffe0e0e 0xbebffc313ffff070

def z103 : W := mkw 0x97fff777bbf616bf 0x84bfffbbbddfb0b5 0xfffffffffffe3fff 0xfffffffffffff1ff

def z104 : W := mkw 0x0dc07e015681bc08 0x606e03f00ab40de0 0xcfd9fe67ff81fe1f 0xfe7ecff33ffc0ff0

def z105 : W := mkw 0x0000020000801400 0x00000010000400a0 0x0000260000003e10 0xc0000130000001f0

def z106 : W := mkw 0x0235015400000010 0x0011a80aa0000000 0x707fa7fe00000001 0xfb83fd3ff0000000

def z107 : W := mkw 0x033061c0c02d6154 0x5019830e06016b0a 0xa72061c1c039f1f5 0x4539030e0e01cf8f

def z108 : W := mkw 0x0ff07f41d6a5bc5c 0x707f83fa0eb52de2 0xcfd07e41ff87fe7e 0xde7e83f20ffc3ff3

def z109 : W := mkw 0x000a00a828584383 0x080050054142c21c 0x302e01b800780181 0x2181700dc003c00c

def z110 : W := mkw 0x0dc0760152813408 0x606e03b00a9409a0 0x07402601c3803008 0x083a01300e1c0180

def z111 : W := mkw 0x800a8aaa2ddadfa3 0x8c005455516ed6fd 0xf8ae59b83fffffff 0xf7c572cdc1ffffff

def z112 : W := mkw 0x04ca08a93e58cb8b 0x0826504549f2c65c 0xffee59b9fff9cf9f 0xffff72cdcfffce7c

def z113 : W := mkw 0x100a8001bb76000f 0x808054000ddbb000 0x00000001fffe000e 0x000000000ffff000

def z114 : W := mkw 0x0008820021c21402 0x80004410010e10a0 0x4059a60023c63e1a 0xfa02cd30011e31f0

def z115 : W := mkw 0x033061c0c02d6154 0x5019830e06016b0a 0xe7206181c039f01e 0x4f39030c0e01cf80

def z116 : W := mkw 0x16f700019a34000d 0x00b7b8000cd1a000 0xd7e60001ffb8000e 0x1ebf30000ffdc000

def z117 : W := mkw 0x8000820201821420 0x84000410100c10a1 0x0051a64603863068 0x08028d32301c3183

def z118 : W := mkw 0x0330614000000010 0x0019830a00000000 0xe73061c000000001 0x6f39830e00000000

def z119 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000000004631fa 0x000000000002318f

def z120 : W := mkw 0x05c5755400000010 0x002e2baaa0000000 0x38cffffe00000001 0xd1c67ffff0000000

def z121 : W := mkw 0x0dc07e015681bc08 0x606e03f00ab40de0 0x8f807e01dc01fe14 0xc47c03f00ee00ff0

def z122 : W := mkw 0x000208880c18c901 0x080010444060c648 0xb8a659981c39c004 0x05c532ccc0e1ce00

def z123 : W := mkw 0x06ff000028500003 0x0037f80001428000 0xd7ff80003c780006 0x3ebffc0001e3c000

def z124 : W := mkw 0x0000141400000000 0x000000a0a0000000 0x08001e3e00000000 0x804000f1f0000000

def z125 : W := mkw 0x0dc8fe0177c3bc0a 0xe06e47f00bbe1de0 0xcfd9fe01ffc7fe1e 0xfe7ecff00ffe3ff0

def z126 : W := mkw 0x80008222018216a0 0x84000411100c10b5 0x0051a66603863ff9 0xc8028d33301c31ff

def z127 : W := mkw 0x00000080c02d6144 0x5000000406016b0a 0x00000001c039c004 0x000000000e01ce00

def z128 : W := mkw 0x0dc57e155681bc08 0x606e2bf0aab40de0 0xdfcffe3fff81fe1e 0xdefe7ff1fffc0ff0

def z129 : W := mkw 0x07f5755400000010 0x003fabaaa0000000 0xbfa6599800000000 0x05fd32ccc0000000

def z130 : W := mkw 0x8008822221c216a2 0x84004411110e10b5 0x0000000023c63ffa 0x00000000011e31ff

def z131 : W := mkw 0x033063c0c0ad7554 0x5019831e06056baa 0xe77067c1e3ffffff 0xff3b833e0f1fffff

def z132 : W := mkw 0x0000000000000000 0x0000000000000000 0xc08000003c000006 0x1604000001e00000

def z133 : W := mkw 0x16ff8021bb76028f 0x80b7fc010ddbb014 0xd7ff8021fffe0f9f 0xfebffc010ffff07c

def z134 : W := mkw 0x00000a0004809c00 0x00000050002404e0 0xc8c07e003f81fe1e 0xde4603f001fc0ff0

def z135 : W := mkw 0x07f5755400000010 0x003fabaaa0000000 0xbfefdfbe00000000 0x95ff7efdf0000000

def z136 : W := mkw 0x000a00a828584383 0x080050054142c21c 0xf8ae59b800780181 0xf7c572cdc003c00c

def z137 : W := mkw 0x88088a2377c3beaa 0xe44044511bbe1df5 0x4059a667ffc7ffff 0xfa02cd333ffe3fff

def z138 : W := mkw 0x100f800029520003 0x80807c00014a9000 0x100f800000000000 0x00807c0000000000

def z139 : W := mkw 0x010061c040096150 0x5008030e02004b0a 0x200061c00001f1f1 0x4100030e00000f8f

def z140 : W := mkw 0x1235800081260004 0x8091ac0004093000 0x0011800000060000 0x00008c0000003000

def z141 : W := mkw 0x000a800029520003 0x80005400014a9000 0xd0ff80003ffe000e 0x3e87fc0001fff000

def z142 : W := mkw 0x07f5755480240014 0x003fabaaa4012000 0xffffffffc07e000f 0xfffffffffe03f000

def z143 : W := mkw 0x0000000000000000 0x0000000000000000 0x404000002380000a 0x1a020000011c0000

def z144 : W := mkw 0x010075d440096150 0x500803aea2004b0a 0x28007ffe0001f1f1 0xc14003fff0000f8f

def z145 : W := mkw 0x8008822221c216a2 0x84004411110e10b5 0x4010204023c63ffb 0x6a008102011e31ff

def z146 : W := mkw 0x0000000000000000 0x0000000000000000 0x00100040004601e1 0x200080020002300f

def z147 : W := mkw 0x05c0760000801400 0x002e03b0000400a0 0xcfc07e0023803e1a 0xde7e03f0011c01f0

def z148 : W := mkw 0x96f5820393a6142c 0x84b7ac101c9d30a1 0x0751a647c3863068 0x083a8d323e1c3183

def z149 : W := mkw 0x0000000000000000 0x0000000000000000 0x302e01b800000001 0x2181700dc0000000

def z150 : W := mkw 0x0000000000000000 0x0000000000000000 0x0051a64600000000 0x08028d3230000000

def z151 : W := mkw 0x16ff8001bb76000f 0x80b7fc000ddbb000 0xffffd9b9fffe000f 0xfffffecdcffff000

def z152 : W := mkw 0x08000a0116809c08 0x2040005008b404e0 0x000000003f800e00 0x0000000001fc0070

def z153 : W := mkw 0x07f575d400084110 0x003fabaea0004208 0xfffffffe0079c197 0xfffffffff003ce0c

def z154 : W := mkw 0x04c0000112000008 0x0026000008900000 0x00c000003f800000 0x1006000001fc0000

def z155 : W := mkw 0x000a08282c508a83 0x0800504141628454 0x188e18383c000e00 0x90c470c1c1e00070

def z156 : W := mkw 0x03306140c0252054 0x5019830a06012902 0x07102041c0063068 0x083881020e003183

def z157 : W := mkw 0x123f8000a9760007 0x8091fc00054bb000 0x103f8000007e0000 0x2081fc000003f000

def z158 : W := mkw 0x000008a80408cb80 0x080000454020465c 0x280059b80001cf91 0xc14002cdc0000e7c

def z159 : W := mkw 0x07f5755440012010 0x403fabaaa2000900 0xffffffffc001f01f 0xfffffffffe000f80

def z160 : W := mkw 0x800882a2e1ef77e6 0xd4004415170f7bbf 0x00000001e3fffffe 0x000000000f1fffff

def z161 : W := mkw 0x0dc07f555681bc18 0x606e03faaab40de0 0xefc07fffff81fe1f 0xdf7e03fffffc0ff0

def z162 : W := mkw 0x023f01fc28584393 0x0811f80fe142c21c 0x303f81fe00780181 0x2181fc0ff003c00c

def z163 : W := mkw 0x17f5e1c1d32f615c 0xd0bfaf0e0e997b0a 0xe771e1c1c3fff1ff 0x6f3b8f0e0e1fff8f

def z164 : W := mkw 0x123f8000a9760007 0x8091fc00054bb000 0xd73f8001c07e000e 0x2eb9fc000e03f000

def z165 : W := mkw 0x0dc07c015601a808 0x606e03e00ab00d40 0x8f805801dc01c004 0x047c02c00ee00e00

def z166 : W := mkw 0x123f80a8a97e4387 0x8891fc05454bf21c 0x303f81b8007e0181 0x2181fc0dc003f00c

def z167 : W := mkw 0x07f77ddc0c18c911 0x083fbbeee060c648 0xfffffffe1c39c005 0xfffffffff0e1ce00

def z168 : W := mkw 0x000a08282c508a83 0x0800504141628454 0x588e18383c400f93 0xf2c470c1c1e2007c

def z169 : W := mkw 0x17fff554a9760017 0x80bfffaaa54bb000 0xfffffffe007e0001 0xfffffffff003f000

def z170 : W := mkw 0x80000222008016a0 0x04000011100400b5 0x0000266600003ff1 0xc0000133300001ff

def z171 : W := mkw 0x000208080c108801 0x0800104040608440 0x188618181c000000 0x00c430c0c0e00000

def z172 : W := mkw 0x0230000000000000 0x0011800000000000 0xc730000000000000 0x2e39800000000000

def z173 : W := mkw 0x05c0600152012008 0x402e03000a900900 0xc7c06001ff81f01e 0x5e3e03000ffc0f80

def z174 : W := mkw 0x0dc07fc15689fd58 0x706e03fe0ab44fea 0xefc07fc1ff81ffff 0xdf7e03fe0ffc0fff

def z175 : W := mkw 0x05ca7ca82c58cb83 0x082e53e54162c65c 0xffee7fb83c79cf97 0xffff73fdc1e3ce7c

def z176 : W := mkw 0x1fffff55fff7bc1f 0xe0fffffaafffbde0 0xfffffffffffffe1f 0xfffffffffffffff0

def z177 : W := mkw 0x16ff8829bf768a8f 0x88b7fc414dfbb454 0xdfff9839fffe0e0e 0xbefffcc1cffff070

def z178 : W := mkw 0x87fdf7f6e1ef77f6 0xd43fefbfb70f7bbf 0xffffffffe3ffffff 0xffffffffff1fffff

def z179 : W := mkw 0x000008a80408cb80 0x080000454020465c 0xe88059b83c01cf97 0xd74402cdc1e00e7c

def z180 : W := mkw 0x0cc01e0116809c08 0x206600f008b404e0 0xc8c05e003f81ce16 0xd64602f001fc0e70

def z181 : W := mkw 0x07ff755428500013 0x003ffbaaa1428000 0xfffffffe3c780007 0xfffffffff1e3c000

def z182 : W := mkw 0x1ff5f601d3a7340c 0xe0ffafb00e9d39a0 0x0751a601c3863008 0x083a8d300e1c3180

def z183 : W := mkw 0x000a0aa82cd8df83 0x080050554166c6fc 0xf8ee7fb83ff9ff9f 0xffc773fdc1ffcffc

def z184 : W := mkw 0x0008002020400282 0x0000400101020014 0x4008002020400f93 0xf20040010102007c

def z185 : W := mkw 0x0330614040012010 0x4019830a02000900 0xe73061c1c001f01f 0x6f39830e0e000f80

def z186 : W := mkw 0x07ff7dfc2c58cb93 0x083ffbefe162c65c 0xfffffffe3c79cf97 0xfffffffff1e3ce7c

def z187 : W := mkw 0x000a000028500003 0x0000500001428000 0x000000003c780006 0x0000000001e3c000

def z188 : W := mkw 0x16ff8001bb76000f 0x80b7fc000ddbb000 0x07518001fffe000e 0x083a8c000ffff000

def z189 : W := mkw 0x033061c0c02d6154 0x5019830e06016b0a 0xffbe79f9c07ff1ff 0xfffdf3cfce03ff8f

def z190 : W := mkw 0x06fd800021420002 0x8037ec00010a1000 0xd7ff800023c6000a 0x3ebffc00011e3000

def z191 : W := mkw 0x0000000000000000 0x0000000000000000 0x0049862600000000 0x90024c3130000000

def z192 : W := mkw 0x09007e015681bc08 0x604803f00ab40de0 0x08007e01ff81fe1e 0xc04003f00ffc0ff0

def z193 : W := mkw 0x000a002028500283 0x0000500101428014 0xd0ae00203c780f97 0xf685700101e3c07c

def z194 : W := mkw 0x0000008000084100 0x0000000400004208 0xe02041800079c197 0x6701020c0003ce0c

def z195 : W := mkw 0x033a69e8ec7debd7 0x5819d34f4763ef5e 0xffbe79f9fc7fffff 0xfffdf3cfcfe3ffff

def z196 : W := mkw 0x0230014080240054 0x1011800a04012002 0x0010004000060060 0x0000800200003003

def z197 : W := mkw 0x07f57554c0252054 0x503fabaaa6012902 0x0751a647c0063068 0x083a8d323e003183

def z198 : W := mkw 0x0235015400000010 0x0011a80aa0000000 0x303f81fe00000001 0x2181fc0ff0000000

def z199 : W := mkw 0x923f8022a97602a7 0x8491fc01154bb015 0x103f8066007e01e1 0x2081fc033003f00f

def z200 : W := mkw 0x05c0740000000000 0x002e03a000000000 0xffee7fb800000001 0xffff73fdc0000000

def z201 : W := mkw 0x16f780019b36000d 0x80b7bc000cd9b000 0x97f78001dfbe000c 0x0cbfbc000efdf000

def z202 : W := mkw 0x16ff8155bb76001f 0x80b7fc0aaddbb000 0xf7ff81fffffe000f 0x3fbffc0ffffff000

def z203 : W := mkw 0x16ff88a9bf7ecb8f 0x88b7fc454dfbf65c 0xd7ff8001ffffcf9e 0x3ebffc000ffffe7c

def z204 : W := mkw 0x08000a81d6adfd4c 0x704000540eb56fea 0x00000001fffffffe 0x000000000fffffff

def z205 : W := mkw 0x0000000000000000 0x0000000000000000 0x4040260000000000 0xda02013000000000

def z206 : W := mkw 0x033061c0c02d6154 0x5019830e06016b0a 0x07102041c07ff1fe 0x083881020e03ff8f

def z207 : W := mkw 0x000008a80408cb80 0x080000454020465c 0x000000000001cf90 0x0000000000000e7c

def z208 : W := mkw 0x04c0140000000000 0x002600a000000000 0x08c01e0000000000 0x904600f000000000

def z209 : W := mkw 0x0100600040012000 0x4008030002000900 0x87004001c001c004 0x043802000e000e00

def z210 : W := mkw 0x0ff57f555681bc18 0x607fabfaaab40de0 0xffe67f99ff81fe1e 0xdfff33fccffc0ff0

def z211 : W := mkw 0x07f061c1d22d615c 0x503f830e0e916b0a 0xe7f061c1fffff1ff 0x7f3f830e0fffff8f

def z212 : W := mkw 0x03306000c0252004 0x4019830006012900 0xc7306001c07ff01e 0x6e3983000e03ff80

def z213 : W := mkw 0x17ffe9e9ff7febdf 0xd8bfff4f4ffbff5e 0xfffff9f9ffffffff 0xffffffcfcfffffff

def z214 : W := mkw 0x800a82aa29da57a3 0x8c005415514ed2bd 0x707fa7fe23fe3ffb 0xfb83fd3ff11ff1ff

def z215 : W := mkw 0x8108e22261c336a2 0xc4084711130e19b5 0xc759e667e3c7ffff 0xfe3acf333f1e3fff

def z216 : W := mkw 0x02388000a1660006 0x8011c400050b3000 0xc7798001e3fe000e 0x3e3bcc000f1ff000

def z217 : W := mkw 0x8000820201821420 0x84000410100c10a1 0x0000000003863068 0x00000000001c3183

def z218 : W := mkw 0x87fdf576214202b2 0x843fefabb10a1015 0xfffffffe004601e1 0xfffffffff002300f

def z219 : W := mkw 0x0000020000801400 0x00000010000400a0 0x4040260023803e1a 0xda020130011c01f0

def z220 : W := mkw 0x023001c0802c4154 0x1011800e0401620a 0xe03041c0007fc1f7 0x6701820e0003fe0f

def z221 : W := mkw 0x05c0740040012000 0x402e03a002000900 0xcfc07e01c001f01e 0xde7e03f00e000f80

def z222 : W := mkw 0x8338e3e2e1ef77f6 0xd419c71f170f7bbf 0xe73061c1e3ffffff 0x6f39830e0f1fffff

def z223 : W := mkw 0x0330614000000010 0x0019830a00000000 0xe73061c0004631fb 0x6f39830e0002318f

def z224 : W := mkw 0x010061c040096150 0x5008030e02004b0a 0x601061c00047f1fb 0x6b00830e00023f8f

def z225 : W := mkw 0x06f5000080240004 0x0037a80004012000 0xd7ff8001c07e000e 0x3ebffc000e03f000

def z226 : W := mkw 0x000a08282c508a83 0x0800504141628454 0xf8ae59b83c000e01 0xf7c572cdc1e00070

def z227 : W := mkw 0x14c700011a100009 0x00a6380008d08000 0x108600001c000000 0x0084300000e00000

def z228 : W := mkw 0x0dc07e015681bc08 0x606e03f00ab40de0 0x8fc05e01ff81ce04 0x947e02f00ffc0e70

def z229 : W := mkw 0x8008822221c216a2 0x84004411110e10b5 0x0019806623c63ffb 0x2000cc03311e31ff

def z230 : W := mkw 0x000a08882c58c903 0x080050444162c648 0xf8ae59983c79c006 0x37c572ccc1e3ce00

def z231 : W := mkw 0x96fd8223b3e616ae 0x84b7ec111d9f30b5 0x4759a667e3c63ffb 0xfa3acd333f1e31ff

def z232 : W := mkw 0x04c5141400000000 0x002628a0a0000000 0x1886181800000000 0x00c430c0c0000000

def z233 : W := mkw 0x133ae1c1fb7f615f 0xd099d70e0fdbfb0a 0xe73061c1fffff1ff 0x6f39830e0fffff8f

def z234 : W := mkw 0x033061c040096150 0x5019830e02004b0a 0xe73061c00001f1f1 0x6f39830e00000f8f

def z235 : W := mkw 0x000001c000084150 0x1000000e0000420a 0x200001c0000001e1 0x0100000e0000000f

def z236 : W := mkw 0x87fdf77621c216b2 0x843fefbbb10e10b5 0xfffffffe23c63ffb 0xfffffffff11e31ff

def z237 : W := mkw 0x0100620040813400 0x40080310020409a0 0xc7406601e381fe1e 0xde3a03300f1c0ff0

def z238 : W := mkw 0x033a69e8ec7debd7 0x5819d34f4763ef5e 0xffae59b9fc79cf97 0xf7fd72cdcfe3ce7c

def z239 : W := mkw 0x06f5000000000000 0x0037a80000000000 0xd7ff800000000000 0x3ebffc0000000000

def z240 : W := mkw 0x0100614040012050 0x5008030a02000902 0x0000204000003060 0x0000010200000183

def z241 : W := mkw 0x0dc07e004481bc00 0x606e03f002240de0 0xcfc07e000001fe10 0xde7e03f000000ff0

def z242 : W := mkw 0x0000000000000000 0x0000000000000000 0xc7000001c000000e 0x0e3800000e000000

def z243 : W := mkw 0x0000015400000010 0x0000000aa0000000 0x200001fe00000001 0x0100000ff0000000

def z244 : W := mkw 0x07f5755512000018 0x003fabaaa8900000 0xffffffffff80000f 0xfffffffffffc0000

def z245 : W := mkw 0x16fd8001b366000e 0x80b7ec000d9b3000 0x47598001e3c6000a 0x3a3acc000f1e3000

def z246 : W := mkw 0x08001e0004809c00 0x204000f0002404e0 0x08001e0000000e00 0x804000f000000070

def z247 : W := mkw 0x16f700019a34000d 0x00b7b8000cd1a000 0xd7b60001dc7e000e 0x2ebdb0000ee3f000

def z248 : W := mkw 0x100a8001bb76000f 0x808054000ddbb000 0x40598001fffe000e 0x3a02cc000ffff000

def z249 : W := mkw 0x0dc07e015681bc08 0x606e03f00ab40de0 0xffee7fb9ff81fe1f 0xffff73fdcffc0ff0

def z250 : W := mkw 0x09006a015681bc08 0x604803500ab40de0 0xc7006001ff81fe1e 0x4e3803000ffc0ff0

def z251 : W := mkw 0x0cc01e0116809c08 0x206600f008b404e0 0xcfc01e01ff800e0e 0x9e7e00f00ffc0070

def z252 : W := mkw 0x04c5141400000000 0x002628a0a0000000 0x0041860600000000 0x00020c3030000000

def z253 : W := mkw 0x0ff07fc1d6adfd5c 0x707f83fe0eb56fea 0xefe07f81ffb9fe1e 0xdf7f03fc0ffdcff0

def z254 : W := mkw 0x07f075c0c02d6154 0x503f83ae06016b0a 0xeff07fc1c07ff1ff 0xff7f83fe0e03ff8f

def z255 : W := mkw 0x023001c0802c4154 0x1011800e0401620a 0xe73001c1c07e01ef 0x2f39800e0e03f00f

def z256 : W := mkw 0x033a61e8e87d63d7 0x5819d30f4743eb1e 0xf73e61f9c07ff1ff 0x6fb9f30fce03ff8f

def z257 : W := mkw 0x0005001400000000 0x00002800a0000000 0x100f803e00000000 0x00807c01f0000000

def z258 : W := mkw 0x0000000000000000 0x0000000000000000 0x00002040000031f1 0x400001020000018f

def z259 : W := mkw 0x023a01e8a87c43d7 0x1811d00f4543e21e 0x303e01f8007e01e1 0x2181f00fc003f00f

def z260 : W := mkw 0x07f5755400000010 0x003fabaaa0000000 0xbfbfd9fe00000001 0x25fdfecff0000000

def z261 : W := mkw 0x87f57776008016b0 0x043fabbbb00400b5 0xfffffffe00003ff1 0xfffffffff00001ff

def z262 : W := mkw 0x16ff0001ba74000f 0x00b7f8000dd3a000 0xd7ae0001fc780006 0x36bd70000fe3c000

def z263 : W := mkw 0x9ffffe23fff7beaf 0xe4fffff11fffbdf5 0xdffffe67ffffffff 0xfefffff33fffffff

def z264 : W := mkw 0x0230000080240004 0x0011800004012000 0xc7302041c07e31ff 0x6e3981020e03f18f

def z265 : W := mkw 0x090a7ea86cd9ff83 0x684853f54366cffc 0xf8ae7fb83c79ff97 0xf7c573fdc1e3cffc

def z266 : W := mkw 0x04c0080116008808 0x0026004008b00440 0xcfc05801ff81ce1e 0xde7e02c00ffc0e70

def z267 : W := mkw 0x0ff07fc1d6adfd5c 0x707f83fe0eb56fea 0xeff07fc1ffffffff 0xff7f83fe0fffffff

def z268 : W := mkw 0x0dc07e015681bc08 0x606e03f00ab40de0 0xcfd07e41ffc7ffff 0xfe7e83f20ffe3fff

def z269 : W := mkw 0x84cd963621c216a2 0x84266cb1b10e10b5 0x18cf9e3e23800e00 0x90c67cf1f11c0070

def z270 : W := mkw 0x8000020200801420 0x04000010100400a1 0x0000264600003060 0x0000013230000183

def z271 : W := mkw 0x0235015400000010 0x0011a80aa0000000 0xf8bfd9fe00000001 0xf7c5fecff0000000

def z272 : W := mkw 0x00000080c02d6144 0x5000000406016b0a 0x40102041c07ff1ff 0x6a0081020e03ff8f

def z273 : W := mkw 0x07f5755400000010 0x003fabaaa0000000 0x1fdfbe7e00000000 0x98fefdf3f0000000

def z274 : W := mkw 0x17f761c1da3d615d 0x50bfbb0e0ed1eb0a 0xb7a64181dc39c004 0x05bd320c0ee1ce00

def z275 : W := mkw 0x07f5755400000010 0x003fabaaa0000000 0xffffd99800000000 0x3ffffeccc0000000

def z276 : W := mkw 0x100a80013b52000b 0x8080540009da9000 0x000000003f800000 0x0000000001fc0000

def z277 : W := mkw 0x0330755400000010 0x001983aaa0000000 0xef307ffe00000001 0xef7983fff0000000

def z278 : W := mkw 0x04c880013342000a 0x80264400099a1000 0xc7d98001ffc6000e 0x3e3ecc000ffe3000

def z279 : W := mkw 0x03306140c0252054 0x5019830a06012902 0xe73061c1c0063069 0x6f39830e0e003183

def z280 : W := mkw 0x800a822229d216a3 0x84005411114e90b5 0xd0ffa6663ffe3fff 0xfe87fd3331fff1ff

def z281 : W := mkw 0x16ff8001bb76000f 0x80b7fc000ddbb000 0x97ef8001ffb80004 0x14bf7c000ffdc000

def z282 : W := mkw 0x04c0000000000000 0x0026000000000000 0xc7c0000000000000 0x1e3e000000000000

def z283 : W := mkw 0x000a08a8ec7debc7 0x580050454763ef5e 0xf8ae59b9fc7fffff 0xf7c572cdcfe3ffff

def z284 : W := mkw 0x0dc07c015601a808 0x606e03e00ab00d40 0xcf807801dc01f01e 0x4e7c03c00ee00f80

def z285 : W := mkw 0x100080019326000c 0x808004000c993000 0x00000001c3860008 0x000000000e1c3000

def z286 : W := mkw 0x07f575d4c02d6154 0x503fabaea6016b0a 0xe771e7c7c07ff1ff 0x6f3b8f3e3e03ff8f

def z287 : W := mkw 0x0235015400000010 0x0011a80aa0000000 0x0011804600000000 0x00008c0230000000

def z288 : W := mkw 0x0008002020400282 0x0000400101020014 0x0008002000400181 0x200040010002000c

def z289 : W := mkw 0x033861e0e06d63d6 0x5019c30f07036b1e 0xe73861e1e07fffff 0xff39c30f0f03ffff

def z290 : W := mkw 0x0cc0160112801408 0x206600b0089400a0 0x0040060003800000 0x00020030001c0000

def z291 : W := mkw 0x000a002828500283 0x0800500141428014 0x100e003800000000 0x00807001c0000000

def z292 : W := mkw 0x8ff8ffe3f7effffe 0xf47fc7ff1fbf7fff 0xeff9ffe7ffffffff 0xff7fcfff3fffffff

def z293 : W := mkw 0x0000000000000000 0x0000000000000000 0x0010204000063068 0x0800810200003183

def z294 : W := mkw 0x17fff555bb76001f 0x80bfffaaaddbb000 0xd7ffa647fffe000e 0x3ebffd323ffff000

def z295 : W := mkw 0x07f5755400000010 0x003fabaaa0000000 0x377fa7fe00000001 0x29bbfd3ff0000000

def z296 : W := mkw 0x84cd963621c216a2 0x84266cb1b10e10b5 0x58dfbe7e23c63ffb 0xfac6fdf3f11e31ff

def z297 : W := mkw 0x01006080c02d6144 0x5008030406016b0a 0xc7006001c07ff1fe 0x4e3803000e03ff8f

def z298 : W := mkw 0x09007e004481bc00 0x604803f002240de0 0x48407e002381fe1a 0xda4203f0011c0ff0

def z299 : W := mkw 0x123a8001bb76000f 0x8091d4000ddbb000 0xc7300001fffe000e 0x2e3980000ffff000

def z300 : W := mkw 0x14ca8001bb76000f 0x80a654000ddbb000 0xc7c00001fffe000e 0x1e3e00000ffff000

def z301 : W := mkw 0x05c0755400000010 0x002e03aaa0000000 0xefc07ffe00000001 0xdf7e03fff0000000

def z302 : W := mkw 0x0000008000084100 0x0000000400004208 0x2020018000780181 0x2101000c0003c00c

def z303 : W := mkw 0x07f77ddc0c18c911 0x083fbbeee060c648 0xbfa659981c39c004 0x05fd32ccc0e1ce00

def z304 : W := mkw 0x8008822221c216a2 0x84004411110e10b5 0x4008002023c63ffb 0xf2004001011e31ff

def z305 : W := mkw 0x17fff5d5fb7f615f 0xd0bfffaeafdbfb0a 0xfffffffffffff1ff 0xffffffffffffff8f

def z306 : W := mkw 0x000a00a828584383 0x080050054142c21c 0x702e01b820780f93 0xf381700dc103c07c

def z307 : W := mkw 0x000a08a8ec7debc7 0x580050454763ef5e 0x00000001fc7ffffe 0x000000000fe3ffff

def z308 : W := mkw 0x06f5000112000008 0x0037a80008900000 0xd7ff8001ff80000e 0x3ebffc000ffc0000

def z309 : W := mkw 0x80088022214202a2 0x84004401110a1015 0x00000000004601e0 0x000000000002300f

def z310 : W := mkw 0x080a0aa97ed9ff8b 0x684050554bf6cffc 0xf8ae59b9fff9ff9f 0xf7c572cdcfffcffc

def z311 : W := mkw 0x88088a2377c3beaa 0xe44044511bbe1df5 0x00000001ffc7fffe 0x000000000ffe3fff

def z312 : W := mkw 0x0008800021420002 0x80004400010a1000 0x4059800023c6000a 0x3a02cc00011e3000

def z313 : W := mkw 0x05c07c0004008800 0x002e03e000200440 0xcfc07e003c01ce16 0xde7e03f001e00e70

def z314 : W := mkw 0x800a8aaa2ddadfa3 0x8c005455516ed6fd 0x000000003ffffffe 0x0000000001ffffff

def z315 : W := mkw 0x123f81c0a97e4157 0x9091fc0e054bf20a 0x303f81c0007e01e1 0x2181fc0e0003f00f

def z316 : W := mkw 0x07f5755400000010 0x003fabaaa0000000 0xfffffffe004631fb 0xfffffffff002318f

def z317 : W := mkw 0x8ffdff7777c3beba 0xe47feffbbbbe1df5 0xffffffffffc7ffff 0xfffffffffffe3fff

def z318 : W := mkw 0x1eff8a01fff7bc0f 0xe0f7fc500fffbde0 0xd7ff8001fffffe1e 0x3ebffc000ffffff0

def z319 : W := mkw 0x07f5755400000010 0x003fabaaa0000000 0x0700000000000000 0x0038000000000000

def z320 : W := mkw 0x000a08282c508a83 0x0800504141628454 0xd8ae18383c780e06 0xb6c570c1c1e3c070

def z321 : W := mkw 0x87fdf77621c216b2 0x843fefbbb10e10b5 0xfffffffe23800e01 0xfffffffff11c0070

def z322 : W := mkw 0x000a08a82c58cb83 0x080050454162c65c 0xb8a659983c79cf96 0x05c532ccc1e3ce7c

def z323 : W := mkw 0x033061c0c02d6154 0x5019830e06016b0a 0xa7204181c07ff1fe 0x0539020c0e03ff8f

def z324 : W := mkw 0x800a88aa2d5acba3 0x8c005445516ad65d 0xf8bfd9fe3c7fcff7 0xf7c5fecff1e3fe7f

def z325 : W := mkw 0x0000000000000000 0x0000000000000000 0x4059a666004631fb 0xfa02cd333002318f

def z326 : W := mkw 0x800a8aaa2ddadfa3 0x8c005455516ed6fd 0xf8efdfbe3ff9cf97 0xf7c77efdf1ffce7c

def z327 : W := mkw 0x8000820201821420 0x84000410100c10a1 0x4059a66603863069 0xfa02cd33301c3183

def z328 : W := mkw 0x16ff8001bb76000f 0x80b7fc000ddbb000 0x10ff80003ffe0000 0x3087fc0001fff000

def z329 : W := mkw 0x17f775559a34001d 0x00bfbbaaacd1a000 0xbfa65999dc380004 0x05fd32cccee1c000

def z330 : W := mkw 0x000208a80c18cb81 0x080010454060c65c 0xb8a659b81c39cf95 0xc5c532cdc0e1ce7c

def z331 : W := mkw 0x0000000000000000 0x0000000000000000 0xe020418000000001 0x6701020c00000000

def z332 : W := mkw 0x000a08282c508a83 0x0800504141628454 0x000000003c000e00 0x0000000001e00070

def z333 : W := mkw 0x0008002020400282 0x0000400101020014 0x0000000020400f92 0x000000000102007c

def z334 : W := mkw 0x80000222008016a0 0x04000011100400b5 0x0000062600000e00 0x8000003130000070

def z335 : W := mkw 0x09007e004481bc00 0x604803f002240de0 0xcf007e01c001fe1e 0xce7803f00e000ff0

def z336 : W := mkw 0x0000000000000000 0x0000000000000000 0x4000000020000e12 0xd200000001000070

def z337 : W := mkw 0x000a08a82c58cb83 0x080050454162c65c 0xb8ae59b83c39ce04 0x95c572cdc1e1ce70

def z338 : W := mkw 0x000a000028500003 0x0000500001428000 0x108e00003c000000 0x1084700001e00000

def z339 : W := mkw 0x04cf1c3c2c508a83 0x082678e1e1628454 0x18cf9e3e3c000e00 0x90c67cf1f1e00070

def z340 : W := mkw 0x0008002020400282 0x0000400101020014 0x4059a66620400f93 0xfa02cd333102007c

def z341 : W := mkw 0x0dc27e895e99fd09 0x686e13f44af4cfe8 0xffe67f99ffb9fe1e 0xdfff33fccffdcff0

def z342 : W := mkw 0x0100614000000010 0x0008030a00000000 0x200061c000000001 0x4100030e00000000

def z343 : W := mkw 0x80000222008016a0 0x04000011100400b5 0x4059a66600003ff1 0xfa02cd33300001ff

def z344 : W := mkw 0x0008002020400282 0x0000400101020014 0x0008002020000e00 0x9000400101000070

def z345 : W := mkw 0x0cc01e015681bc08 0x606600f00ab40de0 0x08c01e01ff81fe1e 0x904600f00ffc0ff0

def z346 : W := mkw 0x8008822221c216a2 0x84004411110e10b5 0x0000266623c63ffb 0xc0000133311e31ff

def z347 : W := mkw 0x000a08a82c58cb83 0x080050454162c65c 0xd0ae00003c79cf96 0x3685700001e3ce7c

def z348 : W := mkw 0x87f5f75601821430 0x843fafbab00c10a1 0x0751a64603863068 0x083a8d32301c3183

def z349 : W := mkw 0x033069c0c42de954 0x5019834e06216f4a 0xefb079c1fc7fffff 0xff7d83ce0fe3ffff

def z350 : W := mkw 0x1ff77c01de35a80d 0x60ffbbe00ef1ad40 0x9fa65801dc39c004 0x04fd32c00ee1ce00

def z351 : W := mkw 0x09007ea84489ff80 0x684803f542244ffc 0x28007fb80001ff91 0xc14003fdc0000ffc

def z352 : W := mkw 0x8008822221c216a2 0x84004411110e10b5 0x4059800023c63ffa 0x3a02cc00011e31ff

def z353 : W := mkw 0x0330614000000010 0x0019830a00000000 0xe779e7e600000001 0xff3bcf3f30000000

def z354 : W := mkw 0x0000080004008800 0x0000004000200440 0xf8ae59b83c01ce17 0xf7c572cdc1e00e70

def z355 : W := mkw 0x0000000000000000 0x0000000000000000 0xc880580000000000 0xd64402c000000000

def z356 : W := mkw 0x033a69e8ec7debd7 0x5819d34f4763ef5e 0xe73061c1fc7fffff 0x6f39830e0fe3ffff

def z357 : W := mkw 0x000a08a82c58cb83 0x080050454162c65c 0x388e59b83c01cf91 0xd1c472cdc1e00e7c

def z358 : W := mkw 0x033075d4c02d6154 0x501983aea6016b0a 0xef307fffc07ff1ff 0xef7983fffe03ff8f

def z359 : W := mkw 0x14cf80013b52000b 0x80a67c0009da9000 0xd0ef80003ff80006 0x36877c0001ffc000

def z360 : W := mkw 0x0000020000801400 0x00000010000400a0 0x0040060023800e00 0x90020030011c0070

def z361 : W := mkw 0x96ff8223bbf616af 0x84b7fc111ddfb0b5 0xd7ff8001fffe3ffe 0x3ebffc000ffff1ff

def z362 : W := mkw 0x16ff8081bb7e410f 0x80b7fc040ddbf208 0xf7ffc181ffffc19f 0x7fbffe0c0ffffe0c

def z363 : W := mkw 0x09007c004401a800 0x604803e002200d40 0x080058000001c000 0x004002c000000e00

def z364 : W := mkw 0x0dc07c015601a808 0x606e03e00ab00d40 0xcfc05801ff81c00e 0x1e7e02c00ffc0e00

def z365 : W := mkw 0x8000820201821420 0x84000410100c10a1 0x0041860603800000 0x00020c30301c0000

def z366 : W := mkw 0x0dc0760152813408 0x606e03b00a9409a0 0xc7406601c381f01e 0x4e3a03300e1c0f80

def z367 : W := mkw 0x1eff9e01bff69c0f 0xa0f7fcf00dffb4e0 0xdfff9e01fffe0e0e 0xbefffcf00ffff070

def z368 : W := mkw 0x14cf8001bb76000f 0x80a67c000ddbb000 0x10cf8001fffe000e 0x10867c000ffff000

def z369 : W := mkw 0x0100755400000010 0x000803aaa0000000 0x6859fffe00000001 0xfb42cffff0000000

def z370 : W := mkw 0x07f5755400000010 0x003fabaaa0000000 0xd7ffa64600000000 0x3ebffd3230000000

def z371 : W := mkw 0x1dcafe01fff7bc0f 0xe0ee57f00fffbde0 0xcfc07e01fffffe1e 0xde7e03f00ffffff0

def z372 : W := mkw 0x8cc89e2337c29eaa 0xa46644f119be14f5 0x08c99e263f800e00 0x90464cf131fc0070

def z373 : W := mkw 0x033061c0c02d6154 0x5019830e06016b0a 0x273021c1c07e31e9 0x2939810e0e03f18f

def z374 : W := mkw 0x16ff80013b52000b 0x80b7fc0009da9000 0xd7ff80003f800000 0x3ebffc0001fc0000

def z375 : W := mkw 0x0ff07dc1d62de95c 0x707f83ee0eb16f4a 0xefb079c1dc7ff1ff 0x6f7d83ce0ee3ff8f

def z376 : W := mkw 0x09007f544481bc10 0x604803faa2240de0 0x28007ffe0001fe11 0xc14003fff0000ff0

def z377 : W := mkw 0x123f88a8ad7ecb87 0x8891fc45456bf65c 0xf8bfd9b83c7fcf97 0xf7c5fecdc1e3fe7c

def z378 : W := mkw 0x07f5755400000010 0x003fabaaa0000000 0xbff7ffde00000000 0x0dffbffef0000000

def z379 : W := mkw 0x80088022214202a2 0x84004401110a1015 0x0009802600000000 0x00004c0130000000

def z380 : W := mkw 0x08000a004481bc00 0x6040005002240de0 0x000000000001fe10 0x0000000000000ff0

def z381 : W := mkw 0x000a88a82d5acb83 0x88005445416ad65c 0xf8ffd9b83fffcf9f 0xffc7fecdc1fffe7c

def z382 : W := mkw 0x8008820221c21422 0x84004410110e10a1 0x4059a64623c6306a 0x3a02cd32311e3183

def z383 : W := mkw 0x0000000040012000 0x4000000002000900 0x00000001c001f01e 0x000000000e000f80

def z384 : W := mkw 0x16ff8001bb76000f 0x80b7fc000ddbb000 0x17df8001ff860008 0x18befc000ffc3000

def z385 : W := mkw 0x00000000c0252044 0x5000000006012902 0x00000001c0063068 0x000000000e003183

def z386 : W := mkw 0x0dc0760152813408 0x606e03b00a9409a0 0xcfc07e01c3803008 0xde7e03f00e1c0180

def z387 : W := mkw 0x1ffff601fbf7340f 0xe0ffffb00fdfb9a0 0xd7ffa601fffe300e 0x3ebffd300ffff180

def z388 : W := mkw 0x0ff57f5516809c18 0x207fabfaa8b404e0 0xfffffffe3f800e01 0xfffffffff1fc0070

def z389 : W := mkw 0x03306140c0252054 0x5019830a06012902 0xc7302041c07e306e 0x2e3981020e03f183

def z390 : W := mkw 0x800a8a2a2dd29ea3 0x8c005451516e94f5 0x18cf9e3e3f800e00 0x90c67cf1f1fc0070

def z391 : W := mkw 0x16ff8889bf7ec90f 0x88b7fc444dfbf648 0xffffd999ffffc00e 0x3ffffecccffffe00

def z392 : W := mkw 0x17ffe1c1fb7f615f 0xd0bfff0e0fdbfb0a 0xf7ffc181ffffc00e 0x3fbffe0c0ffffe00

def z393 : W := mkw 0x17f761c1da3d615d 0x50bfbb0e0ed1eb0a 0xf7b661c1dc7ff1ff 0x6fbdb30e0ee3ff8f

def z394 : W := mkw 0x07fd757420400292 0x003febaba1020014 0xfffffffe20400f93 0xfffffffff102007c

def z395 : W := mkw 0x023001c0802c4154 0x1011800e0401620a 0x2020018000380000 0x0101000c0001c000

def z396 : W := mkw 0x17f5e141d327205c 0xd0bfaf0a0e993902 0x0751a041c3863068 0x083a8d020e1c3183

def z397 : W := mkw 0x07f5614000000010 0x003fab0a00000000 0xf7ffe1c000000001 0x7fbfff0e00000000

def z398 : W := mkw 0x17fff5553b52001b 0x80bfffaaa9da9000 0xfffffffe3f800001 0xfffffffff1fc0000

def z399 : W := mkw 0x823881e2a16e43f6 0x9411c40f150b721f 0x203981e6007e01e1 0x2101cc0f3003f00f

def z400 : W := mkw 0x0330614000000010 0x0019830a00000000 0xffbe79f800000001 0xfffdf3cfc0000000

def z401 : W := mkw 0x1fffffc1fffffd5f 0xf0fffffe0fffffea 0xffffffc1ffffffff 0xfffffffe0fffffff

def z402 : W := mkw 0x8cc89e2337c29eaa 0xa46644f119be14f5 0x48d9be663fc63ffb 0xfa46cdf331fe31ff

def z403 : W := mkw 0x0dc07c015601a808 0x606e03e00ab00d40 0xcfc07e01dc01c004 0xde7e03f00ee00e00

def z404 : W := mkw 0x07ff7d7c2c508a93 0x083ffbebe1628454 0xfffffffe3c000e01 0xfffffffff1e00070

def z405 : W := mkw 0x06f5000000000000 0x0037a80000000000 0x0751800000000000 0x083a8c0000000000

def z406 : W := mkw 0x80088022214202a2 0x84004401110a1015 0x4059a666004601e1 0xfa02cd333002300f

def z407 : W := mkw 0x07f5740000000000 0x003faba000000000 0xdffffe0000000000 0xfefffff000000000

def z408 : W := mkw 0x87fdf77621c216b2 0x843fefbbb10e10b5 0x4759a66623c63ffb 0xfa3acd33311e31ff

def z409 : W := mkw 0x8dc0f60353833428 0xe46e07b01a9c19a1 0x0751a647c3863068 0x083a8d323e1c3183

def z410 : W := mkw 0x0dca7e017ed1bc0b 0x606e53f00bf68de0 0xdfee7e01fff9fe1e 0xfeff73f00fffcff0

def z411 : W := mkw 0x0ff07e01d6a5bc0c 0x607f83f00eb52de0 0xcff07e01fffffe1e 0xfe7f83f00ffffff0

def z412 : W := mkw 0x100200019a34000d 0x008010000cd1a000 0x00000001dc380004 0x000000000ee1c000

def z413 : W := mkw 0x16ff8001bb76000f 0x80b7fc000ddbb000 0x97bf8001dc7e0004 0x24bdfc000ee3f000

def z414 : W := mkw 0x0000000000000000 0x0000000000000000 0xc020000000780006 0x260100000003c000

def z415 : W := mkw 0x0330614000000010 0x0019830a00000000 0x0710204000000000 0x0838810200000000

def z416 : W := mkw 0x800a0aaa2cd8dfa3 0x0c0050555166c6fd 0xf8ae7ffe3c79fff7 0xf7c573fff1e3cfff

def z417 : W := mkw 0x0000000000000000 0x0000000000000000 0x0019806600000001 0x2000cc0330000000

def z418 : W := mkw 0x16ff81c1bb7e415f 0x90b7fc0e0ddbf20a 0xf7ff81c1fffe01ef 0x3fbffc0e0ffff00f

def z419 : W := mkw 0x000a08a82c58cb83 0x080050454162c65c 0x302e01b83c79cf97 0x2181700dc1e3ce7c

def z420 : W := mkw 0x823d8176214202b2 0x8411ec0bb10a1015 0x303f81fe004601e1 0x2181fc0ff002300f

def z421 : W := mkw 0x1237000088340005 0x0091b8000441a000 0x1026000000380000 0x008130000001c000

def z422 : W := mkw 0x000a00a828584383 0x080050054142c21c 0x0000000000780180 0x000000000003c00c

def z423 : W := mkw 0x0ff5775552813418 0x607fabbaaa9409a0 0xffffffffc3803009 0xfffffffffe1c0180

def z424 : W := mkw 0x04c0000112000008 0x0026000008900000 0x07400001c3800008 0x083a00000e1c0000

def z425 : W := mkw 0x14cf80013b52000b 0x80a67c0009da9000 0xd7cf8001ff80000e 0x1ebe7c000ffc0000

def z426 : W := mkw 0x17f775559a34001d 0x00bfbbaaacd1a000 0xffffffffdc380005 0xfffffffffee1c000

def z427 : W := mkw 0x96ff8aabbffedfaf 0x8cb7fc555dfff6fd 0xffffffffffffffff 0xffffffffffffffff

def z428 : W := mkw 0x16ff8081fb7f614f 0xd0b7fc040fdbfb0a 0xd7ff8001fffff1fe 0x3ebffc000fffff8f

def z429 : W := mkw 0x06f000019224000c 0x003780000c912000 0xc7f00001fffe000e 0x3e3f80000ffff000

def z430 : W := mkw 0x05c0740000000000 0x002e03a000000000 0x8f80580000000000 0x047c02c000000000

def z431 : W := mkw 0x0000000112000008 0x0000000008900000 0x00000001ff80000e 0x000000000ffc0000

def z432 : W := mkw 0x0ff5775552813418 0x607fabbaaa9409a0 0x0751a647c3803008 0x083a8d323e1c0180

def z433 : W := mkw 0x0000000000000000 0x0000000000000000 0x280059b800000001 0xc14002cdc0000000

def z434 : W := mkw 0x033061c000084110 0x0019830e00004208 0xe73061c00079c197 0x6f39830e0003ce0c

def z435 : W := mkw 0x000208880c18c901 0x080010444060c648 0xf8a659981c79c197 0x67c532ccc0e3ce0c

def z436 : W := mkw 0x100a8081fb7f614f 0xd08054040fdbfb0a 0x00000001fffff1fe 0x000000000fffff8f

def z437 : W := mkw 0x923f8222a9f616a7 0x8491fc11154fb0b5 0x507fa66623fe3ffb 0xfa83fd33311ff1ff

def z438 : W := mkw 0x04c0020112801408 0x00260010089400a0 0xc7c02601ff803e1e 0xde3e01300ffc01f0

def z439 : W := mkw 0x07ff7dfcec7debd7 0x583ffbefe763ef5e 0xfffffffffc7fffff 0xffffffffffe3ffff

def z440 : W := mkw 0x0230014000000010 0x0011800a00000000 0x203001c000000001 0x2101800e00000000

def z441 : W := mkw 0x17fff555bb76001f 0x80bfffaaaddbb000 0xffffd999fffe000e 0x3ffffecccffff000

def z442 : W := mkw 0x0cca1e293ed09e8b 0x286650f149f684f4 0x18ce1e383f800e00 0x90c670f1c1fc0070

def z443 : W := mkw 0x0000000000000000 0x0000000000000000 0xf8fffffe00000001 0xffc7fffff0000000

def z444 : W := mkw 0x8008822221c216a2 0x84004411110e10b5 0x4059862623c60e0a 0xba02cc31311e3070

def z445 : W := mkw 0x000008a80408cb80 0x080000454020465c 0xe82059b80079cf97 0xe74102cdc003ce7c

def z446 : W := mkw 0x0000000000000000 0x0000000000000000 0x4000000000400193 0x620000000002000c

def z447 : W := mkw 0x010068004401a800 0x4008034002200d40 0xcf807801fc01fe1e 0xde7c03c00fe00ff0

def z448 : W := mkw 0x033061c0c02d6154 0x5019830e06016b0a 0xa73061c1c03ff06c 0x0d39830e0e01ff83

def z449 : W := mkw 0x000a08a82c58cb83 0x080050454162c65c 0xb8ae59b81c79c185 0x25c572cdc0e3ce0c

def z450 : W := mkw 0x800a8aaa2ddadfa3 0x8c005455516ed6fd 0x4059a6663fffffff 0xfa02cd3331ffffff

def z451 : W := mkw 0x000a08a82c58cb83 0x080050454162c65c 0x188e18383c79cf96 0x90c470c1c1e3ce7c

def z452 : W := mkw 0x0000008000084100 0x0000000400004208 0xf8ae59b80079c197 0xf7c572cdc003ce0c

def z453 : W := mkw 0x02300080c02d6144 0x5011800406016b0a 0xc7300001c07ff1fe 0x2e3980000e03ff8f

def z454 : W := mkw 0x000208880c18c901 0x080010444060c648 0xf8ae59b81c39c005 0xf7c572cdc0e1ce00

def z455 : W := mkw 0x0000080004008800 0x0000004000200440 0x000000003c01ce16 0x0000000001e00e70

def z456 : W := mkw 0x01007dfc0408cb90 0x080803efe020465c 0x28007ffe0001cf91 0xc14003fff0000e7c

def z457 : W := mkw 0x80088aaa25cadfa2 0x8c004455512e56fd 0x6859fffe23c7fffb 0xfb42cffff11e3fff

def z458 : W := mkw 0x06f5000000000000 0x0037a80000000000 0x97a6000000000000 0x04bd300000000000

def z459 : W := mkw 0x900a8223bbf616af 0x848054111ddfb0b5 0x4059a667fffe3fff 0xfa02cd333ffff1ff

def z460 : W := mkw 0x8008822221c216a2 0x84004411110e10b5 0x4040260023c63ffa 0xda020130011e31ff

def z461 : W := mkw 0x0000008000084100 0x0000000400004208 0x200041800001c191 0x4100020c00000e0c

def z462 : W := mkw 0x0008002020400282 0x0000400101020014 0x4018206020463ffb 0xfa00c103010231ff

def z463 : W := mkw 0x04c5141400000000 0x002628a0a0000000 0xf8efdfbe00000001 0xf7c77efdf0000000

def z464 : W := mkw 0x0000000000000000 0x0000000000000000 0x4008002000000001 0xf200400100000000

def z465 : W := mkw 0x85c8f62221c216a2 0x842e47b1110e10b5 0xcfd9fe6623c63ffb 0xfe7ecff3311e31ff

def z466 : W := mkw 0x07f575d4c02d6154 0x503fabaea6016b0a 0xffb679d9c07ff1ff 0x6ffdb3cece03ff8f

def z467 : W := mkw 0x16ff8201bbf6140f 0x80b7fc100ddfb0a0 0xd7ffa601fffe3e1e 0xfebffd300ffff1f0

def z468 : W := mkw 0x1ffffc01ff77a80f 0xe0ffffe00ffbbd40 0xdfffd801ffffc00e 0x3efffec00ffffe00

def z469 : W := mkw 0x023a08a8ac7ccb87 0x0811d0454563e65c 0xffbe59b9fc7fcf9f 0xfffdf2cdcfe3fe7c

def z470 : W := mkw 0x04ca00013a50000b 0x0026500009d28000 0xd7ee0001fff8000e 0x3ebf70000fffc000

def z471 : W := mkw 0x0230000080240004 0x0011800004012000 0x00300000007e0000 0x200180000003f000

def z472 : W := mkw 0x0cc51e1516809c08 0x206628f0a8b404e0 0x18cf9e3e3f800e00 0x90c67cf1f1fc0070

def z473 : W := mkw 0x0008800021420002 0x80004400010a1000 0x0019800000460000 0x2000cc0000023000

def z474 : W := mkw 0x0000000080240004 0x0000000004012000 0x00000001c07e000e 0x000000000e03f000

def z475 : W := mkw 0x05c0740000000000 0x002e03a000000000 0x0740260000000000 0x083a013000000000

def z476 : W := mkw 0x823883e2a1ee57f6 0x9411c41f150f72bf 0x6079a7e623fe3ffb 0xfb03cd3f311ff1ff

def z477 : W := mkw 0x180a8a01fff7bc0f 0xe0c054500fffbde0 0x00000001fffffe1e 0x000000000ffffff0

def z478 : W := mkw 0x0000008040096140 0x5000000402004b0a 0x000000000001f1f0 0x0000000000000f8f

def z479 : W := mkw 0x0008082024408a82 0x0000404101220454 0xc88858203c41cf97 0xf64442c101e20e7c

def z480 : W := mkw 0x833aebeaedfffff7 0xdc19d75f576fffff 0xffffffffffffffff 0xffffffffffffffff

def z481 : W := mkw 0x0000080004008800 0x0000004000200440 0x888058001c01c004 0x044402c000e00e00

def z482 : W := mkw 0x000a08282c508a83 0x0800504141628454 0xd88e58383c01ce16 0xd6c472c1c1e00e70

def z483 : W := mkw 0x0235015400000010 0x0011a80aa0000000 0x3026019800000000 0x0181300cc0000000

def z484 : W := mkw 0x0dca7e297ed1be8b 0x686e53f14bf68df4 0xdfce7e39ff81fe1e 0xdefe73f1cffc0ff0

def z485 : W := mkw 0x8dc8f62373c336aa 0xe46e47b11b9e19b5 0x4759a667e3c63ffb 0xfa3acd333f1e31ff

def z486 : W := mkw 0x0b306bc1d6adfd5c 0x7059835e0eb56fea 0xe73061c1ffffffff 0x6f39830e0fffffff

def z487 : W := mkw 0x0dc07c015601a808 0x606e03e00ab00d40 0xcf805801fc01ce16 0xd67c02c00fe00e70

def z488 : W := mkw 0x000008800408c900 0x0000004400204648 0xe8a059803c79cf97 0xf74502cc01e3ce7c

def z489 : W := mkw 0x0000020000801400 0x00000010000400a0 0x4050264023c63ffb 0xfa028132011e31ff

def z490 : W := mkw 0x86fd822221c216a2 0x8437ec11110e10b5 0xd7ffa66623c63ffb 0xfebffd33311e31ff

def z491 : W := mkw 0x0330614080240014 0x0019830a04012000 0xe73061c1c07e000f 0x6f39830e0e03f000

def z492 : W := mkw 0x010061c040096150 0x5008030e02004b0a 0xe70061c1c001f1ff 0x4f38030e0e000f8f

def z493 : W := mkw 0x16ff8001bb76000f 0x80b7fc000ddbb000 0x177f8001c3fe0008 0x28bbfc000e1ff000

def z494 : W := mkw 0x04c5141400000000 0x002628a0a0000000 0x58dfbe7e00000001 0xfac6fdf3f0000000

def z495 : W := mkw 0x010a7dfc2c58cb93 0x080853efe162c65c 0xf8ae7ffe3c79cf97 0xf7c573fff1e3ce7c

def z496 : W := mkw 0x0900760040813400 0x604803b0020409a0 0x0000260000003000 0x0000013000000180

def z497 : W := mkw 0x0ff57d555601a818 0x607fabeaaab00d40 0xbfa65999dc01c004 0x05fd32cccee00e00

def z498 : W := mkw 0x81007776008016b0 0x040803bbb00400b5 0x28007ffe00003ff1 0xc14003fff00001ff

def z499 : W := mkw 0x033061c0c02d6154 0x5019830e06016b0a 0xe73061c1c039c005 0x6f39830e0e01ce00

def z500 : W := mkw 0x1ff77e01deb5bc0d 0x60ffbbf00ef5ade0 0xdfe67e01ffb9fe1e 0xdeff33f00ffdcff0

def z501 : W := mkw 0x07f5755400000010 0x003fabaaa0000000 0xcfd1fe4600000000 0xde7e8ff230000000

def z502 : W := mkw 0x0dc0760152813408 0x606e03b00a9409a0 0xc7c02601ff80300e 0x1e3e01300ffc0180

def z503 : W := mkw 0x100a8000a9760007 0x80805400054bb000 0x00000000007e0000 0x000000000003f000

def z504 : W := mkw 0x84c8822333c216aa 0x84264411199e10b5 0xc7d9a667ffc63fff 0xfe3ecd333ffe31ff

def z505 : W := mkw 0x0dc07e81d6adfd4c 0x706e03f40eb56fea 0xcfc07e01fffffffe 0xde7e03f00fffffff

def z506 : W := mkw 0x010a68a86c59eb83 0x480853454362cf5c 0xffae79b9fc79ff9f 0xfffd73cdcfe3cffc

def z507 : W := mkw 0x0dc07e015681bc08 0x606e03f00ab40de0 0x8f805801ff81fe1e 0x047c02c00ffc0ff0

def z508 : W := mkw 0x0dc07e015681bc08 0x606e03f00ab40de0 0x8fc07e01df81f00c 0x0c7e03f00efc0f80

def z509 : W := mkw 0x0ff57d555601a818 0x607fabeaaab00d40 0xffffffffdc01c005 0xfffffffffee00e00

def z510 : W := mkw 0x0335615400000010 0x0019ab0aa0000000 0xf73fe1fe00000001 0x6fb9ff0ff0000000

def z511 : W := mkw 0x033a61c0e87d6157 0x5019d30e0743eb0a 0xf7be61c1fc7ff1ff 0x7fbdf30e0fe3ff8f

def z512 : W := mkw 0x100a88a9bf7ecb8f 0x888054454dfbf65c 0xf8ae59b9ffffcf9f 0xf7c572cdcffffe7c

def z513 : W := mkw 0x03306140c0252054 0x5019830a06012902 0x07000001c0000000 0x003800000e000000

def z514 : W := mkw 0x16f700019a34000d 0x00b7b8000cd1a000 0xd7ff8001dc380004 0x3ebffc000ee1c000

def z515 : W := mkw 0x0dc0760152813408 0x606e03b00a9409a0 0x47402601e3803e1a 0xda3a01300f1c01f0

def z516 : W := mkw 0x07ff7dfc2c58cb93 0x083ffbefe162c65c 0xffae59b83c79cf97 0xf7fd72cdc1e3ce7c

def z517 : W := mkw 0x033061c0c02d6154 0x5019830e06016b0a 0x203061c0007ff1f1 0x6101830e0003ff8f

def z518 : W := mkw 0x8008822221c216a2 0x84004411110e10b5 0x0000000023800e00 0x00000000011c0070

def z519 : W := mkw 0x0dc07e015681bc08 0x606e03f00ab40de0 0x0f407e01c381fe18 0xc87a03f00e1c0ff0

def z520 : W := mkw 0x100a88a9bf7ecb8f 0x888054454dfbf65c 0x00000001ffffcf9e 0x000000000ffffe7c

def z521 : W := mkw 0x8008022220c016a2 0x04004011110600b5 0x4008266620403ff3 0xf2004133310201ff

def z522 : W := mkw 0x010061c040096150 0x5008030e02004b0a 0x200041800001c000 0x0100020c00000e00

def z523 : W := mkw 0x80000aaa0488dfa0 0x0c000055502446fd 0x28007ffe0001fff1 0xc14003fff0000fff

def z524 : W := mkw 0x87f5f75601821430 0x843fafbab00c10a1 0xfffffffe03863069 0xfffffffff01c3183

def z525 : W := mkw 0x07f5755400000010 0x003fabaaa0000000 0xffae59b800000001 0xf7fd72cdc0000000

def z526 : W := mkw 0x8008822221c216a2 0x84004411110e10b5 0x0049862623c63ffa 0x90024c31311e31ff

def z527 : W := mkw 0x8338e1e2e16f63f6 0xd419c70f170b7b1f 0xe739e1e7c07ff1ff 0x6f39cf0f3e03ff8f

def z528 : W := mkw 0x16ff8801bf76880f 0x80b7fc400dfbb440 0xdfffd801ffffce1e 0xfefffec00ffffe70

def z529 : W := mkw 0x033061c0802c4154 0x1019830e0401620a 0xe73061c0007e01e1 0x6f39830e0003f00f

def z530 : W := mkw 0x033061c0c02d6154 0x5019830e06016b0a 0xe7204181c079c197 0x6739020c0e03ce0c

def z531 : W := mkw 0x14cf80013b52000b 0x80a67c0009da9000 0x50df80003fc6000a 0x3a86fc0001fe3000

def z532 : W := mkw 0x0800020152813408 0x604000100a9409a0 0x00000001c3803008 0x000000000e1c0180

def z533 : W := mkw 0x17f5f5559326001c 0x80bfafaaac993000 0xffffffffc3860009 0xfffffffffe1c3000

def z534 : W := mkw 0x17ffe141bb76001f 0x80bfff0a0ddbb000 0xf7ffe1c1fffe000f 0x7fbfff0e0ffff000

def z535 : W := mkw 0x0ff07dc1d62de95c 0x707f83ee0eb16f4a 0xafa05981dc39c004 0x057d02cc0ee1ce00

def z536 : W := mkw 0x0100740000000000 0x000803a000000000 0x08007e0000000000 0xc04003f000000000

def z537 : W := mkw 0x8008822221c216a2 0x84004411110e10b5 0x4049a62623803e1a 0xda024d31311c01f0

def z538 : W := mkw 0x123f8001bb76000f 0x8091fc000ddbb000 0x103f8001fffe000e 0x2081fc000ffff000

def z539 : W := mkw 0x0000002000000280 0x0000000100000014 0x0000002000000f91 0xc00000010000007c

def z540 : W := mkw 0x0100755400000010 0x000803aaa0000000 0x2800599800000000 0x014002ccc0000000

def z541 : W := mkw 0x0008800021420002 0x80004400010a1000 0x0000000023c6000a 0x00000000011e3000

def z542 : W := mkw 0x17fffdfdbf7ecb9f 0x88bfffefedfbf65c 0xffffffffffffcf9f 0xfffffffffffffe7c

def z543 : W := mkw 0x17ffe001fb77200f 0xc0bfff000fdbb900 0xd7ffe001fffff01e 0x7ebfff000fffff80

def z544 : W := mkw 0x080008015601a808 0x604000400ab00d40 0x00000001dc01c004 0x000000000ee00e00

def z545 : W := mkw 0x0000008000084100 0x0000000400004208 0x000000000079c196 0x000000000003ce0c

def z546 : W := mkw 0x0008802021420282 0x80004401010a1014 0x4059802023c60f9b 0xfa02cc01011e307c

def z547 : W := mkw 0x810063e2408977f0 0x5408031f12044bbf 0x200067e60001fff1 0xc100033f30000fff

def z548 : W := mkw 0x123f8154a9760017 0x8091fc0aa54bb000 0x303f81fe007e0001 0x2181fc0ff003f000

def z549 : W := mkw 0x0000800001020000 0x8000040000081000 0x0051800003860008 0x08028c00001c3000

def z550 : W := mkw 0x0ff57fd5d6adfd5c 0x707fabfeaeb56fea 0xffffffffffffffff 0xffffffffffffffff

def z551 : W := mkw 0x00000080802c4144 0x100000040401620a 0x00000000007e01e0 0x000000000003f00f

def z552 : W := mkw 0x8008822221c216a2 0x84004411110e10b5 0x0019a66600463ff1 0xe000cd33300231ff

def z553 : W := mkw 0x0000000000000000 0x0000000000000000 0x4059800000000000 0x3a02cc0000000000

def z554 : W := mkw 0x0100600040012000 0x4008030002000900 0xc7106041c047f1ff 0x6e3883020e023f8f

def z555 : W := mkw 0x16f580019326000c 0x80b7ac000c993000 0xd7ff8001c3860008 0x3ebffc000e1c3000

def z556 : W := mkw 0x07f57dfc0408cb90 0x083fabefe020465c 0xfffffffe0001cf91 0xfffffffff0000e7c

def z557 : W := mkw 0x0b307fc0c4adfd54 0x705983fe06256fea 0xef307fc1c07fffff 0xef7983fe0e03ffff

def z558 : W := mkw 0x07f5775400801410 0x003fabbaa00400a0 0xfffffffe23803e1b 0xfffffffff11c01f0

def z559 : W := mkw 0x09007e004481bc00 0x604803f002240de0 0xc8807e003c01fe16 0xd64403f001e00ff0

def z560 : W := mkw 0x16ff8001bb76000f 0x80b7fc000ddbb000 0x97a60001fffe000e 0x04bd30000ffff000

def z561 : W := mkw 0x8000800201020020 0x8400040010081001 0x0011804600060060 0x00008c0230003003

def z562 : W := mkw 0x000a000028500003 0x0000500001428000 0xf8ae59b83c780007 0xf7c572cdc1e3c000

def z563 : W := mkw 0x07f57d5404008810 0x003fabeaa0200440 0xfffffffe3c01ce17 0xfffffffff1e00e70

def z564 : W := mkw 0x800882a221ca57a2 0x84004415110e52bd 0xe079e7e623ffffff 0xff03cf3f311fffff

def z565 : W := mkw 0x023001c0802c4154 0x1011800e0401620a 0x603021c0007e31fb 0x6b01810e0003f18f

def z566 : W := mkw 0x07f5755400000010 0x003fabaaa0000000 0x4759a66600000001 0xfa3acd3330000000

def z567 : W := mkw 0x000008880408c900 0x0800004440204648 0x280059980001c000 0x014002ccc0000e00

def z568 : W := mkw 0x0000000000000000 0x0000000000000000 0x400020000000301a 0x4a00010000000180

def z569 : W := mkw 0x0ff07741d2a5345c 0x707f83ba0e9529a2 0x07502641c3863068 0x083a81320e1c3183

def z570 : W := mkw 0x833063e2c0ad77f4 0x5419831f16056bbf 0xe73067e7c07fffff 0xef39833f3e03ffff

def z571 : W := mkw 0x0100608040096100 0x4008030402004b08 0xe7206181c079f19f 0x6f39030c0e03cf8c

def z572 : W := mkw 0x16f500019224000c 0x00b7a8000c912000 0x07000001c0000000 0x003800000e000000

def z573 : W := mkw 0x07f5755400000010 0x003fabaaa0000000 0x2f51fffe00000001 0xc97a8ffff0000000

def z574 : W := mkw 0x000008a80408cb80 0x080000454020465c 0xf8ae59b80001cf91 0xf7c572cdc0000e7c

def z575 : W := mkw 0x800a8a2a2dd29ea3 0x8c005451516e94f5 0x58dfbe7e3fc63ffb 0xfac6fdf3f1fe31ff

def z576 : W := mkw 0x0dc0740152012008 0x606e03a00a900900 0x07000001c0000000 0x003800000e000000

def z577 : W := mkw 0x06f5141400000000 0x0037a8a0a0000000 0xdfff9e3e00000000 0xbefffcf1f0000000

def z578 : W := mkw 0x000a000028500003 0x0000500001428000 0x102e000000780000 0x208170000003c000

def z579 : W := mkw 0x0000000000000000 0x0000000000000000 0x4010204000000001 0x6a00810200000000

def z580 : W := mkw 0x000800a020484382 0x000040050102421c 0xe02841a02079cf97 0xf701420d0103ce7c

def z581 : W := mkw 0x0335755400000010 0x0019abaaa0000000 0x383ffffe00000001 0xe1c1fffff0000000

def z582 : W := mkw 0x0000008000084100 0x0000000400004208 0xa02041800039c004 0x0501020c0001ce00

def z583 : W := mkw 0x0dca7ca97e59eb8b 0x686e53e54bf2cf5c 0xffae59b9fc79cf97 0xf7fd72cdcfe3ce7c

def z584 : W := mkw 0x08000a015681bc08 0x604000500ab40de0 0xc8805801ff81fe1e 0xd64402c00ffc0ff0

def z585 : W := mkw 0x16f580019326000c 0x80b7ac000c993000 0xc7d18001ff86000e 0x1e3e8c000ffc3000

def z586 : W := mkw 0x0ff077c1d2ad755c 0x707f83be0e956baa 0xe77067c1c3fff1ff 0x6f3b833e0e1fff8f

def z587 : W := mkw 0x17ffe141fb77205f 0xd0bfff0a0fdbb902 0xd7ffa041fffe306e 0x3ebffd020ffff183

def z588 : W := mkw 0x1dcffe017fd3bc0b 0xe0ee7ff00bfe9de0 0xdfcffe01ff81fe1e 0xdefe7ff00ffc0ff0

def z589 : W := mkw 0x900a8223bbf616af 0x848054111ddfb0b5 0x00000001fffe3ffe 0x000000000ffff1ff

def z590 : W := mkw 0x04cf1cbc2c58cb83 0x082678e5e162c65c 0xf8efdfbe3c79cf97 0xf7c77efdf1e3ce7c

def z591 : W := mkw 0x07f575d4c02d6154 0x503fabaea6016b0a 0xffffffffc039c005 0xfffffffffe01ce00

def z592 : W := mkw 0x17fff401bb76000f 0x80bfffa00ddbb000 0xdffffe01fffe000e 0xfefffff00ffff000

def z593 : W := mkw 0x0dca7ea97ed9ff8b 0x686e53f54bf6cffc 0xcfc07e01fff9ff9e 0xde7e03f00fffcffc

def z594 : W := mkw 0x8330e3c2c1af7574 0xd419871e160d7bab 0xe771e7c7c3fff1ff 0x6f3b8f3e3e1fff8f

def z595 : W := mkw 0x04c5000000000000 0x0026280000000000 0x10cf800000000000 0x10867c0000000000

def z596 : W := mkw 0x8008822221c216a2 0x84004411110e10b5 0x0059866623c60fe1 0xb002cc33311e307f

def z597 : W := mkw 0x0cc01e0116809c08 0x206600f008b404e0 0x48c03e003f803e1a 0xda4601f001fc01f0

def z598 : W := mkw 0x0008022020c01682 0x00004011010600b4 0x4048262023c03f9b 0xfa024131011e01fc

def z599 : W := mkw 0x000a08a82c58cb83 0x080050454162c65c 0xc88058003c79cf96 0xd64402c001e3ce7c

def z600 : W := mkw 0x80000022000002a0 0x0400000110000015 0x00000066000001e1 0x000000033000000f

def z601 : W := mkw 0x0000020000801400 0x00000010000400a0 0x0040260003803008 0x08020130001c0180

def z602 : W := mkw 0x0008800021420002 0x80004400010a1000 0x0049800023800000 0x10024c00011c0000

def z603 : W := mkw 0x80000222008016a0 0x04000011100400b5 0x4010266600463ffb 0xea008133300231ff

def z604 : W := mkw 0x023a09e8ac7ccbd7 0x1811d04f4563e65e 0xf8be59f83c7fcff7 0xf7c5f2cfc1e3fe7f

def z605 : W := mkw 0x010069e84409ebd0 0x5808034f42204f5e 0x280079f80001fff1 0xc14003cfc0000fff

def z606 : W := mkw 0x0dc27c895e19e909 0x686e13e44af0cf48 0xbfa65999dc39c004 0x05fd32cccee1ce00

def z607 : W := mkw 0x800a80aa295a43a3 0x8c005405514ad21d 0x303f81fe007e01e1 0x2181fc0ff003f00f

def z608 : W := mkw 0x000a08a82c58cb83 0x080050454162c65c 0x382e59b80079cf91 0xe1c172cdc003ce7c

def z609 : W := mkw 0x89007e224481bea0 0x644803f112240df5 0x08007e660001fff1 0xc04003f330000fff

def z610 : W := mkw 0x0dc07e815689fd08 0x606e03f40ab44fe8 0xefe07f81fff9ff9f 0xff7f03fc0fffcffc

def z611 : W := mkw 0x8008822221c216a2 0x84004411110e10b5 0x4049862623c00f93 0xf2024c31311e007c

def z612 : W := mkw 0x023501d4802c4154 0x1011a80ea401620a 0x303f81fe007e01e1 0x2181fc0ff003f00f

def z613 : W := mkw 0x8008822221c216a2 0x84004411110e10b5 0x4059a66623800e01 0xfa02cd33311c0070

def z614 : W := mkw 0x0ffa7fe9fefdffdf 0x787fd3ff4ff7effe 0xfffe7ff9ffffffff 0xfffff3ffcfffffff

def z615 : W := mkw 0x8008822221c216a2 0x84004411110e10b5 0x0059a66603c631e9 0x2802cd33301e318f

def z616 : W := mkw 0x1ff5fe01d7a7bc0c 0xe0ffaff00ebd3de0 0xcfd1fe01ff87fe1e 0xde7e8ff00ffc3ff0

def z617 : W := mkw 0x8108f77621c216b2 0x840847bbb10e10b5 0x6859fffe23c63ffb 0xfb42cffff11e31ff

def z618 : W := mkw 0x07f5755400000010 0x003fabaaa0000000 0xbfa67ffe00000001 0xc5fd33fff0000000

def z619 : W := mkw 0x82388222a1e616a6 0x8411c411150f30b5 0xc779a667e3fe3fff 0xfe3bcd333f1ff1ff

def z620 : W := mkw 0x16ff08a9be7ccb8f 0x08b7f8454df3e65c 0xffae59b9fc79cf97 0xf7fd72cdcfe3ce7c

def z621 : W := mkw 0x0ff57f555681bc18 0x607fabfaaab40de0 0xcfd1fe47ff81fe1e 0xde7e8ff23ffc0ff0

def z622 : W := mkw 0x000000a800084380 0x080000054000421c 0x200001b800000181 0x0100000dc000000c

def z623 : W := mkw 0x08000a015681bc08 0x604000500ab40de0 0x40402601ff81fe1e 0xda0201300ffc0ff0

def z624 : W := mkw 0x1ffffea9ffffff8f 0xe8fffff54ffffffc 0xffffffb9ffffff9f 0xfffffffdcffffffc

def z625 : W := mkw 0x80088022214202a2 0x84004401110a1015 0x4019806620460ff3 0xf200cc033102307f

def z626 : W := mkw 0x07f0754000000010 0x003f83aa00000000 0xeff07fc000000001 0xff7f83fe00000000

def z627 : W := mkw 0x00000080c02d6144 0x5000000406016b0a 0xe0204181c07ff1ff 0x6701020c0e03ff8f

def z628 : W := mkw 0x07f561c0c02d6154 0x503fab0e06016b0a 0xf7ffe1c1c07ff1ff 0x7fbfff0e0e03ff8f

def z629 : W := mkw 0x0dc07e015681bc08 0x606e03f00ab40de0 0x0fc03e01ff803e08 0x987e01f00ffc01f0

def z630 : W := mkw 0x0000080004008800 0x0000004000200440 0x080058000001ce10 0xc04002c000000e70

def z631 : W := mkw 0x07ff75fc28584393 0x083ffbafe142c21c 0xfffffffe00780181 0xfffffffff003c00c

def z632 : W := mkw 0x123f8000a9760007 0x8091fc00054bb000 0xd0bf80003c7e0006 0x3685fc0001e3f000

def z633 : W := mkw 0x0000000000000000 0x0000000000000000 0x401000000046000a 0x2a00800000023000

def z634 : W := mkw 0x010a69e86c59ebd3 0x5808534f4362cf5e 0xf8ae79f83c79fff7 0xf7c573cfc1e3cfff

def z635 : W := mkw 0x07f5755400000010 0x003fabaaa0000000 0xffe67f9800000000 0xdfff33fcc0000000

def z636 : W := mkw 0x8000820201821420 0x84000410100c10a1 0x4051a64603c631fb 0x6a028d32301e318f

def z637 : W := mkw 0x0fff7ffd7ed9ff9b 0x687ffbffebf6cffc 0xfffffffffff9ff9f 0xffffffffffffcffc

def z638 : W := mkw 0x16f708899e3cc90d 0x08b7b8444cf1e648 0xbfa65999dc39c004 0x05fd32cccee1ce00

def z639 : W := mkw 0x8338e36221c216b2 0x8419c71b110e10b5 0xe779e7e623c63ffb 0xff3bcf3f311e31ff

def z640 : W := mkw 0x05c0740112000008 0x002e03a008900000 0xcfc07e01ff80000e 0xde7e03f00ffc0000

def z641 : W := mkw 0x823d837621c216b2 0x8411ec1bb10e10b5 0x707fa7fe23c63ffb 0xfb83fd3ff11e31ff

def z642 : W := mkw 0x0000082804008a80 0x0800004140200454 0x0800183800000e00 0x804000c1c0000070

def z643 : W := mkw 0x1ccf9e013fd29c0b 0xa0e67cf009fe94e0 0x18cf9e003f800e00 0x90c67cf001fc0070

def z644 : W := mkw 0x16ff80a9bb7e438f 0x88b7fc054ddbf21c 0xf7ff81b9fffe018f 0x3fbffc0dcffff00c

def z645 : W := mkw 0x0dc07e0116809c08 0x206e03f008b404e0 0xcfc07e003f800e00 0xde7e03f001fc0070

def z646 : W := mkw 0x97ffe3e3fbff77ff 0xd4bfff1f1fdffbbf 0xf7ffe7e7ffffffff 0xffbfff3f3fffffff

def z647 : W := mkw 0x0000000000000000 0x0000000000000000 0x188e183800000000 0x90c470c1c0000000

def z648 : W := mkw 0x800882a2e1ef77e6 0xd4004415170f7bbf 0x4059a667e3ffffff 0xfa02cd333f1fffff

def z649 : W := mkw 0x07f5755400000010 0x003fabaaa0000000 0xffb679d800000001 0x6ffdb3cec0000000

def z650 : W := mkw 0x8dc8fe2377c3beaa 0xe46e47f11bbe1df5 0xcfc9fe27ff81fe1e 0xde7e4ff13ffc0ff0

def z651 : W := mkw 0x14cf94153b52000b 0x80a67ca0a9da9000 0x18cf9e3e3f800000 0x90c67cf1f1fc0000

def z652 : W := mkw 0x033061c0c02d6154 0x5019830e06016b0a 0xa73041c1c07fc1e5 0x2539820e0e03fe0f

def z653 : W := mkw 0x0338e1c0e16f6156 0xd019c70e070b7b0a 0xe779e1c1e3fff1ff 0x7f3bcf0e0f1fff8f

def z654 : W := mkw 0x000a08a82c58cb83 0x080050454162c65c 0x38ae19b83c780f81 0xb1c570cdc1e3c07c

def z655 : W := mkw 0x80088022214202a2 0x84004401110a1015 0x4019a066004631fb 0x6a00cd033002318f

def z656 : W := mkw 0x033269c8cc3de955 0x5819934e4661ef4a 0xbfa65999dc39c004 0x05fd32cccee1ce00

def z657 : W := mkw 0x0002000008100001 0x0000100000408000 0x90a600001c380004 0x0485300000e1c000

def z658 : W := mkw 0x033061c0c02d6154 0x5019830e06016b0a 0xe7304181c07fc00e 0x2f39820c0e03fe00

def z659 : W := mkw 0x8dcafeab7fdbffab 0xec6e57f55bfedffd 0xffffffffffffffff 0xffffffffffffffff

def z660 : W := mkw 0x0cc01c0116008808 0x206600e008b00440 0x088018001c000000 0x004400c000e00000

def z661 : W := mkw 0x14c5800113020008 0x80a62c0008981000 0x0041800003800000 0x00020c00001c0000

def z662 : W := mkw 0x8330e342c1a73474 0xd419871a160d39a3 0x0751a647c3863068 0x083a8d323e1c3183

def z663 : W := mkw 0x07f5755400000010 0x003fabaaa0000000 0xe771e7c600000001 0x6f3b8f3e30000000

def z664 : W := mkw 0x07fdf55421420012 0x803fefaaa10a1000 0xfffffffe23c6000b 0xfffffffff11e3000

def z665 : W := mkw 0x8108e3e261cb77f2 0xd408471f130e5bbf 0x6059e7e623c7fffb 0xfb02cf3f311e3fff

def z666 : W := mkw 0x0230000080240004 0x0011800004012000 0x07100001c0060008 0x083880000e003000

def z667 : W := mkw 0x0dc07ea95689ff88 0x686e03f54ab44ffc 0xefc07fb9ff81ff9f 0xdf7e03fdcffc0ffc

def z668 : W := mkw 0x03306140c0252054 0x5019830a06012902 0x47102041c04631fb 0x6a3881020e02318f

def z669 : W := mkw 0x0330614000000010 0x0019830a00000000 0xa720418000000000 0x0539020c00000000

def z670 : W := mkw 0x05c0740000000000 0x002e03a000000000 0xcfd9fe6600000001 0xfe7ecff330000000

def z671 : W := mkw 0x000a08a82c58cb83 0x080050454162c65c 0x280059b83c79cf97 0xc14002cdc1e3ce7c

def z672 : W := mkw 0x8008822221c216a2 0x84004411110e10b5 0x0059a66623863e68 0x9802cd33311c31f3

def z673 : W := mkw 0x16f580019326000c 0x80b7ac000c993000 0xc7718001c3fe000e 0x2e3b8c000e1ff000

def z674 : W := mkw 0x0100600040012000 0x4008030002000900 0x000060000001f010 0x4000030000000f80

def z675 : W := mkw 0x05c5741400000000 0x002e2ba0a0000000 0xdfcffe3e00000000 0xdefe7ff1f0000000

def z676 : W := mkw 0x0cca1ea93ed8df8b 0x286650f549f6c6fc 0xf8ee5fb83ff9cf97 0xf7c772fdc1ffce7c

def z677 : W := mkw 0x0235000000000000 0x0011a80000000000 0x103f800000000000 0x2081fc0000000000

def z678 : W := mkw 0x0008002020400282 0x0000400101020014 0xf8ae59b820400f93 0xf7c572cdc102007c

def z679 : W := mkw 0x0000080004008800 0x0000004000200440 0x088018003c000e00 0x904400c001e00070

def z680 : W := mkw 0x0000000000000000 0x0000000000000000 0xb8a6599800000000 0x05c532ccc0000000

def z681 : W := mkw 0x023f09fc2c58cb93 0x0811f84fe162c65c 0xf8bfd9fe3c79cf97 0xf7c5fecff1e3ce7c

def z682 : W := mkw 0x0100755400000010 0x000803aaa0000000 0xf8ae7ffe00000001 0xf7c573fff0000000

def z683 : W := mkw 0x8008822221c216a2 0x84004411110e10b5 0x0049a66623803ff1 0xd0024d33311c01ff

def z684 : W := mkw 0x80000222008016a0 0x04000011100400b5 0x0000000000003ff0 0x00000000000001ff

def z685 : W := mkw 0x04c0000112000008 0x0026000008900000 0x87800001dc000004 0x043c00000ee00000

def z686 : W := mkw 0x02300080802c4104 0x0011800404016208 0xe7304181c07fc19f 0x6f39820c0e03fe0c

def z687 : W := mkw 0x023001c0c02d6154 0x5011800e06016b0a 0x203001c1c07ff1ff 0x2101800e0e03ff8f

def z688 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000266600000001 0xc000013330000000

def z689 : W := mkw 0x06f5000000000000 0x0037a80000000000 0xd7ffa66600000001 0xfebffd3330000000

def z690 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z691 : W := mkw 0x0008000020400002 0x0000400001020000 0x4008000020400002 0x3200400001020000

def z692 : W := mkw 0x14cf88293f528a8b 0x88a67c4149fa9454 0x18cf98383f800e00 0x90c67cc1c1fc0070

def z693 : W := mkw 0x8dc0fe035783bc28 0xe46e07f01abc1de1 0xcfd1fe47ff87fe7e 0xde7e8ff23ffc3ff3

def z694 : W := mkw 0x0100600000000000 0x0008030000000000 0xc700600000000000 0x4e38030000000000

def z695 : W := mkw 0x000a00a828584383 0x080050054142c21c 0xf02e41b80079c197 0x6781720dc003ce0c

def z696 : W := mkw 0x0ff57e015681bc08 0x607fabf00ab40de0 0xdffffe01ff81fe1e 0xfefffff00ffc0ff0

def z697 : W := mkw 0x000a08a82c58cb83 0x080050454162c65c 0x400800203c79cf97 0xf200400101e3ce7c

def z698 : W := mkw 0x000208880c18c901 0x080010444060c648 0x000000001c39c004 0x0000000000e1ce00

def z699 : W := mkw 0x8000820201821420 0x84000410100c10a1 0x4051a64623863e7a 0xda028d32311c31f3

def z700 : W := mkw 0x0000008000084100 0x0000000400004208 0xe03061c0007ff1ff 0x6f01830e0003ff8f

def z701 : W := mkw 0x0008800021420002 0x80004400010a1000 0x4059a66623c6000b 0xfa02cd33311e3000

def z702 : W := mkw 0x8dc07e235681bea8 0x646e03f11ab40df5 0xcfc07e67ff81ffff 0xde7e03f33ffc0fff

def z703 : W := mkw 0x0100755400000010 0x000803aaa0000000 0x0000264600000000 0x0000013230000000

def z704 : W := mkw 0x0ff57f544481bc10 0x607fabfaa2240de0 0xfffffffe0001fe11 0xfffffffff0000ff0

def z705 : W := mkw 0x0000000000000000 0x0000000000000000 0xd0ae000000000000 0x3685700000000000

def z706 : W := mkw 0x07f575d4c02d6154 0x503fabaea6016b0a 0xbfa65999c039c004 0x05fd32ccce01ce00

def z707 : W := mkw 0x8000820201821420 0x84000410100c10a1 0x4051a64623c63ffb 0xfa028d32311e31ff

def z708 : W := mkw 0x16ff8001bb76000f 0x80b7fc000ddbb000 0x47598001fffe000e 0x3a3acc000ffff000

def z709 : W := mkw 0x16ff8001bb76000f 0x80b7fc000ddbb000 0x97ef8001fffe000e 0x14bf7c000ffff000

def z710 : W := mkw 0x0dc57e155681bc08 0x606e2bf0aab40de0 0xffefffbfff81fe1f 0xffff7ffdfffc0ff0

def z711 : W := mkw 0x07f575559224001c 0x003fabaaac912000 0xfffffffffffe000f 0xfffffffffffff000

def z712 : W := mkw 0x16ff8155bb76001f 0x80b7fc0aaddbb000 0xffffd9fffffe000f 0xfffffecffffff000

def z713 : W := mkw 0x80028a8a0d9add21 0x8c001454506cd6e9 0xb8f7ffde1fbff06c 0x0dc7bffef0fdff83

def z714 : W := mkw 0x07ff7dfc2c58cb93 0x083ffbefe162c65c 0x0751a6463c79cf96 0x083a8d3231e3ce7c

def z715 : W := mkw 0x07f5755400000010 0x003fabaaa0000000 0xfffffffe20000e13 0xfffffffff1000070

def z716 : W := mkw 0x16f780019b36000d 0x80b7bc000cd9b000 0xd7ff8001dfbe000c 0x3ebffc000efdf000

def z717 : W := mkw 0x17f575559224001c 0x00bfabaaac912000 0xffffffffc0000001 0xfffffffffe000000

def z718 : W := mkw 0x05c5755400000010 0x002e2baaa0000000 0xffcffffe00000001 0xdffe7ffff0000000

def z719 : W := mkw 0x033075c0c02d6154 0x501983ae06016b0a 0xef307fc1c07ff1ff 0xef7983fe0e03ff8f

def z720 : W := mkw 0x033061c0c02d6154 0x5019830e06016b0a 0x271061c1c07ff1ff 0x4938830e0e03ff8f

def z721 : W := mkw 0x07f5755440012010 0x403fabaaa2000900 0xffffffffc0003009 0xfffffffffe000180

def z722 : W := mkw 0x0000020000801400 0x00000010000400a0 0x4059a66623c63ffb 0xfa02cd33311e31ff

def z723 : W := mkw 0x0330614000000010 0x0019830a00000000 0xfffffffe00000001 0xfffffffff0000000

def z724 : W := mkw 0x0dc07e015681bc08 0x606e03f00ab40de0 0x8fc05e01ff81fe1e 0x947e02f00ffc0ff0

def z725 : W := mkw 0x000a08a82c58cb83 0x080050454162c65c 0xb8a659983c39ce04 0x05c532ccc1e1ce70

def z726 : W := mkw 0x06fa0001ba74000f 0x0037d0000dd3a000 0xd7fe0001fffe000e 0x3ebff0000ffff000

def z727 : W := mkw 0x0dc07e015681bc08 0x606e03f00ab40de0 0xefc07fb9ff81fe1f 0xdf7e03fdcffc0ff0

def z728 : W := mkw 0x16f588a9972ecb8c 0x88b7ac454cb9765c 0x2f51d9b9c387cf99 0xc97a8ecdce1c3e7c

def z729 : W := mkw 0x15cfe1c17b5b615b 0xd0ae7f0e0bdadb0a 0x30cfe1c03f81f1f1 0x51867f0e01fc0f8f

def z730 : W := mkw 0x07f5755400000010 0x003fabaaa0000000 0xfffffffe3c000007 0xfffffffff1e00000

def z731 : W := mkw 0x07f5755440012010 0x403fabaaa2000900 0xffffffffc047f1ff 0xfffffffffe023f8f

def z732 : W := mkw 0x0dc07e015681bc08 0x606e03f00ab40de0 0x8fc07e01ff81fe0c 0x9c7e03f00ffc0ff0

def z733 : W := mkw 0x033a6968ec75aad7 0x5819d34b4763ad56 0x1f9e3879fc063e68 0x98fcf1c3cfe031f3

def z734 : W := mkw 0x0dc07e015681bc08 0x606e03f00ab40de0 0xdfee7e01ff81fe1e 0xfeff73f00ffc0ff0

def z735 : W := mkw 0x8008822221c216a2 0x84004411110e10b5 0x4059a64623c63ffa 0x3a02cd32311e31ff

def z736 : W := mkw 0x8cca9e2b3fd29eab 0xac6654f159fe94f5 0x18cf9e3e3f800e00 0x90c67cf1f1fc0070

def z737 : W := mkw 0x800a822229d216a3 0x84005411114e90b5 0x507fa66623fe3ffb 0xfa83fd33311ff1ff

def z738 : W := mkw 0x04c51494c02d6144 0x502628a4a6016b0a 0x18cf9e3fc07ff1fe 0x90c67cf1fe03ff8f

def z739 : W := mkw 0x0a350b555681bc18 0x6051a85aaab40de0 0x303f81ffff81fe1f 0x2181fc0ffffc0ff0

def z740 : W := mkw 0x8dc8fc237743aaaa 0xe46e47e11bba1d55 0x8f99d867dc47c1e5 0x247ccec33ee23e0f

def z741 : W := mkw 0x16ff9415bb76000f 0x80b7fca0addbb000 0xffffdfbffffe000f 0xfffffefdfffff000

def z742 : W := mkw 0x06f5155400000010 0x0037a8aaa0000000 0x38ef9fbe00000000 0x91c77cfdf0000000

def z743 : W := mkw 0x16ff8001bb76000f 0x80b7fc000ddbb000 0xf7ff81b9fffe000f 0x3fbffc0dcffff000

def z744 : W := mkw 0x04ca00013a50000b 0x0026500009d28000 0xc7c00001fff8000e 0x1e3e00000fffc000

def z745 : W := mkw 0x0dc07e015681bc08 0x606e03f00ab40de0 0xcfc07e01ff81ce04 0xde7e03f00ffc0e70

def z746 : W := mkw 0x00000080c02d6144 0x5000000406016b0a 0xc7000001c07ff1fe 0x0e3800000e03ff8f

def z747 : W := mkw 0x01006080c02d6144 0x5008030406016b0a 0x87004001c07ff1fe 0x043802000e03ff8f

def z748 : W := mkw 0x0dc07f415681bc58 0x706e03fa0ab40de2 0xcfc07e41ff81fe7e 0xde7e03f20ffc0ff3

def z749 : W := mkw 0x16ff8001bb76000f 0x80b7fc000ddbb000 0x97a60001ffb80004 0x04bd30000ffdc000

def z750 : W := mkw 0x04c000019224000c 0x002600000c912000 0xc7c00001fffe000e 0x1e3e00000ffff000

def z751 : W := mkw 0x8338e3e2e1ef77f6 0xd419c71f170f7bbf 0xa769c7a7e3b9ce04 0x953b4e3d3f1dce70

def z752 : W := mkw 0x033075d4c02d6154 0x501983aea6016b0a 0xef3079d9c07ff1ff 0x6f7983cece03ff8f

def z753 : W := mkw 0x09006a015681bc08 0x604803500ab40de0 0x07002001ff81fe1e 0x083801000ffc0ff0

def z754 : W := mkw 0x0ef01fc196acdd5c 0x307780fe0cb566ea 0x28f01fc03ffe0fe1 0xb14780fe01fff07f

def z755 : W := mkw 0x023a8000a9760007 0x8011d400054bb000 0xd7ff8001fffe000e 0x3ebffc000ffff000

def z756 : W := mkw 0x0cc01e015681bc08 0x606600f00ab40de0 0xcfc01e01ff81fe1e 0x9e7e00f00ffc0ff0

def z757 : W := mkw 0x0dc57e015681bc08 0x606e2bf00ab40de0 0xdfcffe01ff81fe1e 0xdefe7ff00ffc0ff0

def z758 : W := mkw 0x8008822221c216a2 0x84004411110e10b5 0xc0d9a6663fc63fff 0xfe06cd3331fe31ff

def z759 : W := mkw 0x1b3ffe00edf7bc07 0xe0d9fff0076fbde0 0x183ffe00007ffe10 0xe0c1fff00003fff0

def z760 : W := mkw 0x16ff8001bb76000f 0x80b7fc000ddbb000 0xdfff9839fffe000e 0xbefffcc1cffff000

def z761 : W := mkw 0x8008822221c216a2 0x84004411110e10b5 0x707fa7fe23c63ffb 0xfb83fd3ff11e31ff

def z762 : W := mkw 0x16ff9555bb76001f 0x80b7fcaaaddbb000 0xffff9ffffffe000f 0xbffffcfffffff000

def z763 : W := mkw 0x01006080c02d6144 0x5008030406016b0a 0xc7106041c07ff1ff 0x6e3883020e03ff8f

def z764 : W := mkw 0x96f702239ab416ad 0x04b7b8111cd5a0b5 0x97a62667dc383ff5 0xc4bd31333ee1c1ff

def z765 : W := mkw 0x0dc07e015681bc08 0x606e03f00ab40de0 0xffffffffff81fe1f 0xfffffffffffc0ff0

def z766 : W := mkw 0x900a8aabbffedfaf 0x8c8054555dfff6fd 0x00000001fffffffe 0x000000000fffffff

def z767 : W := mkw 0x000a08a82c58cb83 0x080050454162c65c 0xf8a659983c79cf97 0x67c532ccc1e3ce7c

def z768 : W := mkw 0x123a8001bb76000f 0x8091d4000ddbb000 0x87200001fffe000e 0x043900000ffff000

def z769 : W := mkw 0x0dc07e015681bc08 0x606e03f00ab40de0 0xefe07f81ff81fe1f 0xff7f03fc0ffc0ff0

def z770 : W := mkw 0x05c5755400000010 0x002e2baaa0000000 0xf8effffe00000001 0xf7c77ffff0000000

def z771 : W := mkw 0x16ff8021bb76028f 0x80b7fc010ddbb014 0xd7ff8001fffe0f9e 0x3ebffc000ffff07c

def z772 : W := mkw 0x06f5155400000010 0x0037a8aaa0000000 0x78ffbffe00000001 0xfbc7fdfff0000000

def z773 : W := mkw 0x0335755400000010 0x0019abaaa0000000 0xf8bffffe00000001 0xf7c5fffff0000000

def z774 : W := mkw 0x0dc07f415681bc18 0x606e03fa0ab40de0 0xefc07fc1ff81fe1f 0xdf7e03fe0ffc0ff0

def z775 : W := mkw 0x0dc07e015681bc08 0x606e03f00ab40de0 0xcfc9fe27ff81fe1e 0xde7e4ff13ffc0ff0

def z776 : W := mkw 0x033061c0c02d6154 0x5019830e06016b0a 0xc7106041c07ff1fe 0x4e3883020e03ff8f

def z777 : W := mkw 0x16ff8001bb76000f 0x80b7fc000ddbb000 0xd7ff8041fffe01ef 0x3ebffc020ffff00f

def z778 : W := mkw 0x16ff8001bb76000f 0x80b7fc000ddbb000 0xf7ffc181fffe000f 0x7fbffe0c0ffff000

def z779 : W := mkw 0x16f780019b36000d 0x80b7bc000cd9b000 0x97e78001dfb80004 0x04bf3c000efdc000

def z780 : W := mkw 0x8008822221c216a2 0x84004411110e10b5 0x4051a64623c63ffa 0xda028d32311e31ff

def z781 : W := mkw 0x16ff8021bb76028f 0x80b7fc010ddbb014 0xd7ff8021fffe018f 0x3ebffc010ffff00c

def z782 : W := mkw 0x000a08a82c58cb83 0x080050454162c65c 0xb8ae59b83c79cf96 0x95c572cdc1e3ce7c

def z783 : W := mkw 0x0dc07e015681bc08 0x606e03f00ab40de0 0x0fc07e01ff81fe18 0xd87e03f00ffc0ff0

def z784 : W := mkw 0x110af555bb76001f 0x808857aaaddbb000 0x28007ffffffe000f 0xc14003fffffff000

def z785 : W := mkw 0x14cf80013b52000b 0x80a67c0009da9000 0xd7ef8001fff8000e 0x3ebf7c000fffc000

def z786 : W := mkw 0x16ff8001bb76000f 0x80b7fc000ddbb000 0xd7ffa667fffe31ff 0xfebffd333ffff18f

def z787 : W := mkw 0x000a08a82c58cb83 0x080050454162c65c 0xf8be59b83c7fcf9f 0xffc5f2cdc1e3fe7c

def z788 : W := mkw 0x000a08a82c58cb83 0x080050454162c65c 0xf8be79f83c79cf97 0xffc5f3cfc1e3ce7c

def z789 : W := mkw 0x0dc07e015681bc08 0x606e03f00ab40de0 0x8f805801ff81ce04 0x047c02c00ffc0e70

def z790 : W := mkw 0x800a822229d216a3 0x84005411114e90b5 0x4059a6663ffe3fff 0xfa02cd3331fff1ff

def z791 : W := mkw 0x16ff8001bb76000f 0x80b7fc000ddbb000 0xd7ff8001fffe019f 0x7ebffc000ffff00c

def z792 : W := mkw 0x16ff8001bb76000f 0x80b7fc000ddbb000 0xdfffd801fffe000e 0xfefffec00ffff000

def z793 : W := mkw 0x0dc07e015681bc08 0x606e03f00ab40de0 0x8f807e01ff81fe1e 0xc47c03f00ffc0ff0

def z794 : W := mkw 0x16ff8141bb76001f 0x80b7fc0a0ddbb000 0xf7ff81c1fffe000f 0x3fbffc0e0ffff000

def z795 : W := mkw 0x87fdf77621c216b2 0x843fefbbb10e10b5 0xbfa6599823c63ffa 0x05fd32ccc11e31ff

def z796 : W := mkw 0x06f000019224000c 0x003780000c912000 0xc7e00001ffb8000e 0x1e3f00000ffdc000

def z797 : W := mkw 0x16ff8141bb76005f 0x90b7fc0a0ddbb002 0xd7ff8041fffe006e 0x3ebffc020ffff003

def z798 : W := mkw 0x033061c0c02d6154 0x5019830e06016b0a 0x273061c1c07ff1f9 0x6939830e0e03ff8f

def z799 : W := mkw 0x04c5155400000010 0x002628aaa0000000 0x38cf9ffe00000001 0x91c67cfff0000000

def z800 : W := mkw 0x0dc07e015681bc08 0x606e03f00ab40de0 0xc7c02601ff81fe1e 0x1e3e01300ffc0ff0

def z801 : W := mkw 0x0dc07e015681bc08 0x606e03f00ab40de0 0x07000001ff81fe1e 0x003800000ffc0ff0

def z802 : W := mkw 0x000208880c18c901 0x080010444060c648 0xf8a659983c79cf97 0xf7c532ccc1e3ce7c

def z803 : W := mkw 0x0dc07e015681bc08 0x606e03f00ab40de0 0xcfd07e01ffc7fe1e 0xfe7e83f00ffe3ff0

def z804 : W := mkw 0x16f580019326000c 0x80b7ac000c993000 0xc7f18001fffe000e 0x3e3f8c000ffff000

def z805 : W := mkw 0x07f5755512000018 0x003fabaaa8900000 0xfffffffe3f800001 0xfffffffff1fc0000

def z806 : W := mkw 0x123a8001bb76000f 0x8091d4000ddbb000 0xc7798001fffe000e 0x3e3bcc000ffff000

def z807 : W := mkw 0x000a88a82d5acb83 0x88005445416ad65c 0xf8fff9f83fffffff 0xffc7ffcfc1ffffff

def z808 : W := mkw 0x07f5755400000010 0x003fabaaa0000000 0xffffdfbe00000000 0xbffffefdf0000000

def z809 : W := mkw 0x96ff8023bb7602af 0x84b7fc011ddbb015 0xd7ffa667fffe01ef 0xfebffd333ffff00f

def z810 : W := mkw 0x09007ea84489ff80 0x684803f542244ffc 0x08007e000001ff90 0xc04003f000000ffc

def z811 : W := mkw 0x923f81e2a97e43f7 0x9491fc0f154bf21f 0x303f81e6007e01e1 0x2181fc0f3003f00f

def z812 : W := mkw 0x800a88aa2d5acba3 0x8c005445516ad65d 0xf8ffd9fe3fffcfff 0xffc7fecff1fffe7f

def z813 : W := mkw 0x07f5755400000010 0x003fabaaa0000000 0xfffffffe0001c017 0xfffffffff0000e00

def z814 : W := mkw 0x16ff8001bb76000f 0x80b7fc000ddbb000 0xd7ff8627fffe000e 0xbebffc313ffff000

def z815 : W := mkw 0x01006080c02d6144 0x5008030406016b0a 0xe7206181c07ff1ff 0x6f39030c0e03ff8f

def z816 : W := mkw 0x8008822221c216a2 0x84004411110e10b5 0xe079e7e623c63ffb 0xff03cf3f311e31ff

def z817 : W := mkw 0x0dc07c015601a808 0x606e03e00ab00d40 0xcfc05801ff81ce1e 0xde7e02c00ffc0e70

def z818 : W := mkw 0x06f5000000000000 0x0037a80000000000 0xfffffffe00000001 0xfffffffff0000000

def z819 : W := mkw 0x16ff8001bb76000f 0x80b7fc000ddbb000 0x97bf8001fffe000e 0x24bdfc000ffff000

def z820 : W := mkw 0x0dc07e015681bc08 0x606e03f00ab40de0 0xdfce7e39ff81fe1e 0xdefe73f1cffc0ff0

def z821 : W := mkw 0x800a822a29d216a3 0x8c005411514e90b5 0x505fa67e23c63ffb 0xfa82fd33f11e31ff

def z822 : W := mkw 0x02300080802c4104 0x0011800404016208 0xe73061c1c07ff1ff 0x6f39830e0e03ff8f

def z823 : W := mkw 0x01006080c02d6144 0x5008030406016b0a 0x07002001c07ff1fe 0x083801000e03ff8f

def z824 : W := mkw 0x0000000000000000 0x0000000000000000 0xf8efdfbe00000001 0xf7c77efdf0000000

def z825 : W := mkw 0x033061c0c02d6154 0x5019830e06016b0a 0xe7206181c07ff1fe 0x4f39030c0e03ff8f

def z826 : W := mkw 0x05c0620152813408 0x402e03100a9409a0 0xc7c06601ff81fe1e 0xde3e03300ffc0ff0

def z827 : W := mkw 0x81006bea4489fff0 0x5c08035f52244fff 0x28007ffe0001fff1 0xc14003fff0000fff

def z828 : W := mkw 0x000a08a82c58cb83 0x080050454162c65c 0xffae59b9fc79cf9f 0xfffd72cdcfe3ce7c

def z829 : W := mkw 0x16ff8001bb76000f 0x80b7fc000ddbb000 0xd7ff8067fffe000f 0x3ebffc033ffff000

def z830 : W := mkw 0x0100755400000010 0x000803aaa0000000 0xf8fffffe00000001 0xffc7fffff0000000

def z831 : W := mkw 0x800a88aa2d5acba3 0x8c005445516ad65d 0xf8afd9be3c79cf97 0xf7c57ecdf1e3ce7c

def z832 : W := mkw 0x0235155400000010 0x0011a8aaa0000000 0x383f9ffe00000001 0xa1c1fcfff0000000

def z833 : W := mkw 0x000a88a82d5acb83 0x88005445416ad65c 0xf8efd9b83ff9cf97 0xf7c77ecdc1ffce7c

def z834 : W := mkw 0x0cc00a015681bc08 0x606600500ab40de0 0xc7c02601ff81fe1e 0xde3e01300ffc0ff0

def z835 : W := mkw 0x123f81e8a97e43d7 0x9891fc0f454bf21e 0x303f81f8007e01e1 0x2181fc0fc003f00f

def z836 : W := mkw 0x0dc57f555681bc18 0x606e2bfaaab40de0 0xffcfffffff81fe1f 0xdffe7ffffffc0ff0

def z837 : W := mkw 0x07f5755400000010 0x003fabaaa0000000 0x38fffffe00000001 0xf1c7fffff0000000

def z838 : W := mkw 0x04c5141400000000 0x002628a0a0000000 0x38cfdfbe00000001 0xd1c67efdf0000000

def z839 : W := mkw 0x80008222018216a0 0x84000411100c10b5 0x4051a66603c63ffb 0xea028d33301e31ff

def z840 : W := mkw 0x0dc07e015681bc08 0x606e03f00ab40de0 0xffe67f99ff81fe1e 0xdfff33fccffc0ff0

def z841 : W := mkw 0x16ff9401bb76000f 0x80b7fca00ddbb000 0xdfff9e01fffe000e 0xbefffcf00ffff000

def z842 : W := mkw 0x0dc07e015681bc08 0x606e03f00ab40de0 0xcfc07e67ff81fe1f 0xde7e03f33ffc0ff0

def z843 : W := mkw 0x14c200019a34000d 0x00a610000cd1a000 0xc7c00001ffb8000e 0x1e3e00000ffdc000

def z844 : W := mkw 0x000208a80c18cb81 0x080010454060c65c 0xb8a659b81c39ce04 0x85c532cdc0e1ce70

def z845 : W := mkw 0x16ff8001bb76000f 0x80b7fc000ddbb000 0x97f78001fffe000e 0x0cbfbc000ffff000

def z846 : W := mkw 0x16ff8001bb76000f 0x80b7fc000ddbb000 0xd7ae0001fffe000e 0x36bd70000ffff000

def z847 : W := mkw 0x000a08a82c58cb83 0x080050454162c65c 0x38ae59b83c79cf91 0xf1c572cdc1e3ce7c

def z848 : W := mkw 0x000a08a82c58cb83 0x080050454162c65c 0xf8bfd9fe3c79cf97 0xf7c5fecff1e3ce7c

def z849 : W := mkw 0x033061c0c02d6154 0x5019830e06016b0a 0xe7b061c1fc7ff1ff 0x7f3d830e0fe3ff8f

def z850 : W := mkw 0x96ff8003bb76002f 0x84b7fc001ddbb001 0xd7ff8047fffe006e 0x3ebffc023ffff003

def z851 : W := mkw 0x0dc07e015681bc08 0x606e03f00ab40de0 0x8fc07e01ff81fe14 0xd47e03f00ffc0ff0

def z852 : W := mkw 0x14ca8001bb76000f 0x80a654000ddbb000 0xd7ee0001fffe000e 0x3ebf70000ffff000

def z853 : W := mkw 0x05c0740000000000 0x002e03a000000000 0xfffffffe00000001 0xfffffffff0000000

def z854 : W := mkw 0x000a08a82c58cb83 0x080050454162c65c 0xb8ae59b81c79cf95 0xe5c572cdc0e3ce7c

def z855 : W := mkw 0x000208a80c18cb81 0x080010454060c65c 0xf8ae59b81c39cf95 0xf7c572cdc0e1ce7c

def z856 : W := mkw 0x0dc07e015681bc08 0x606e03f00ab40de0 0xcfc05e01ff81ce16 0xd67e02f00ffc0e70

def z857 : W := mkw 0x033561d4c02d6154 0x5019ab0ea6016b0a 0xe731e1c7c07ff1ff 0x6f398f0e3e03ff8f

def z858 : W := mkw 0x0dc07e015681bc08 0x606e03f00ab40de0 0xcfc05801ff81fe1e 0x1e7e02c00ffc0ff0

def z859 : W := mkw 0x033061c0c02d6154 0x5019830e06016b0a 0xa73061c1c07ff1ed 0x2d39830e0e03ff8f

def z860 : W := mkw 0x89007eaa4489ffa0 0x6c4803f552244ffd 0x28007ffe0001fff1 0xc14003fff0000fff

def z861 : W := mkw 0x033061c0c02d6154 0x5019830e06016b0a 0xa73061c1c07ff1f5 0x6539830e0e03ff8f

def z862 : W := mkw 0x09007e804489fd40 0x704803f402244fea 0x08007e000001fff0 0xc04003f000000fff

def z863 : W := mkw 0x800a822229d216a3 0x84005411114e90b5 0x50dfa6663fc63ffb 0xfa86fd3331fe31ff

def z864 : W := mkw 0x16ff8001bb76000f 0x80b7fc000ddbb000 0x17df8001fffe000e 0x18befc000ffff000

def z865 : W := mkw 0x96ff8023bb7602af 0x84b7fc011ddbb015 0xd7ffa067fffe31ff 0x7ebffd033ffff18f

def z866 : W := mkw 0x0dc07e015681bc08 0x606e03f00ab40de0 0xcfd07e41ff87fe7e 0xde7e83f20ffc3ff3

def z867 : W := mkw 0x880a8aab7fdbffab 0xec4054555bfedffd 0x00000001fffffffe 0x000000000fffffff

def z868 : W := mkw 0x16ff8001bb76000f 0x80b7fc000ddbb000 0xd7e60001fffe000e 0x1ebf30000ffff000

def z869 : W := mkw 0x0cc00a015681bc08 0x606600500ab40de0 0x87800001ff81fe1e 0x043c00000ffc0ff0

def z870 : W := mkw 0x16ff8001bb76000f 0x80b7fc000ddbb000 0x17ff8001fffe0008 0x38bffc000ffff000

def z871 : W := mkw 0x16ff8001bb76000f 0x80b7fc000ddbb000 0xd7ef8001ffb8000e 0x1ebf7c000ffdc000

def z872 : W := mkw 0x14ca8001bb76000f 0x80a654000ddbb000 0x87800001fffe000e 0x043c00000ffff000

def z873 : W := mkw 0x16ff8001bb76000f 0x80b7fc000ddbb000 0xd7ffc001ffffc01e 0x7ebffe000ffffe00

def z874 : W := mkw 0x0335755400000010 0x0019abaaa0000000 0xff3ffffe00000001 0xeff9fffff0000000

def z875 : W := mkw 0x0dc07f555681bc18 0x606e03faaab40de0 0xffee7fffff81fe1f 0xffff73fffffc0ff0

def z876 : W := mkw 0x8008822221c216a2 0x84004411110e10b5 0x0059a66623c63ff1 0xf002cd33311e31ff

def z877 : W := mkw 0x16f700019a34000d 0x00b7b8000cd1a000 0x97e60001ffb80004 0x14bf30000ffdc000

def z878 : W := mkw 0x08000a015681bc08 0x604000500ab40de0 0xc7000001ff81fe1e 0x0e3800000ffc0ff0

def z879 : W := mkw 0x0dc07e015681bc08 0x606e03f00ab40de0 0x47402601ff81fe1e 0xda3a01300ffc0ff0

def z880 : W := mkw 0x07f5755480240014 0x003fabaaa4012000 0xffffffffc0060009 0xfffffffffe003000

def z881 : W := mkw 0x07f57554c0252054 0x503fabaaa6012902 0xffffffffc0000001 0xfffffffffe000000

def z882 : W := mkw 0x09007e804489fd00 0x604803f402244fe8 0x28007f800001ff91 0xc14003fc00000ffc

def z883 : W := mkw 0x80008222018216a0 0x84000411100c10b5 0x4051a66623863ffb 0xda028d33311c31ff

def z884 : W := mkw 0x80008222018216a0 0x84000411100c10b5 0x0051a64603863ff8 0x08028d32301c31ff

def z885 : W := mkw 0x033061c0c02d6154 0x5019830e06016b0a 0xe73067e7c07ff1ff 0xef39833f3e03ff8f

def z886 : W := mkw 0x05c07c0116008808 0x002e03e008b00440 0xcfc07e01ff81ce1e 0xde7e03f00ffc0e70

def z887 : W := mkw 0x04c0080116008808 0x0026004008b00440 0xc7c00001ff81ce1e 0x1e3e00000ffc0e70

def z888 : W := mkw 0x0235015400000010 0x0011a80aa0000000 0xf8fffffe00000001 0xffc7fffff0000000

def z889 : W := mkw 0x0cc00a015681bc08 0x606600500ab40de0 0xcfc05801ff81fe1e 0xde7e02c00ffc0ff0

def z890 : W := mkw 0x033061c0c02d6154 0x5019830e06016b0a 0xa73041c1c07ff1ff 0x2539820e0e03ff8f

def z891 : W := mkw 0x800a822229d216a3 0x84005411114e90b5 0xf8fffffe3ffe3fff 0xffc7fffff1fff1ff

def z892 : W := mkw 0x033061c0c02d6154 0x5019830e06016b0a 0xe7304181c07ff1fe 0x2f39820c0e03ff8f

def z893 : W := mkw 0x000a08a82c58cb83 0x080050454162c65c 0xf8ae79b83c79ff9f 0xffc573cdc1e3cffc

def z894 : W := mkw 0x033061c0c02d6154 0x5019830e06016b0a 0xe77067c1c07ff1ff 0xff3b833e0e03ff8f

def z895 : W := mkw 0x07f5755400000010 0x003fabaaa0000000 0xbfeffffe00000001 0xd5ff7ffff0000000

def z896 : W := mkw 0x0100608040096100 0x4008030402004b08 0xe73061c1c07ff1ff 0x6f39830e0e03ff8f

def z897 : W := mkw 0x033575d4c02d6154 0x5019abaea6016b0a 0xff3fffffc07ff1ff 0xeff9fffffe03ff8f

def z898 : W := mkw 0x04ca80013b52000b 0x8026540009da9000 0xd7ff8001fffe000e 0x3ebffc000ffff000

def z899 : W := mkw 0x07f57554c0252054 0x503fabaaa6012902 0xffffffffc007f07f 0xfffffffffe003f83

def z900 : W := mkw 0x07f5755400000010 0x003fabaaa0000000 0x3fdffffe00000001 0xd9fefffff0000000

def z901 : W := mkw 0x16ff8001bb76000f 0x80b7fc000ddbb000 0xd7ffa041fffe306e 0x3ebffd020ffff183

def z902 : W := mkw 0x16ff8001bb76000f 0x80b7fc000ddbb000 0xd7ff8001ffb80004 0x3ebffc000ffdc000

def z903 : W := mkw 0x16ff8021bb76028f 0x80b7fc010ddbb014 0xd7ffa061fffe3fff 0xfebffd030ffff1ff

def z904 : W := mkw 0x0dc07e015681bc08 0x606e03f00ab40de0 0xc7406601ff81fe1e 0x4e3a03300ffc0ff0

def z905 : W := mkw 0x000a88a82d5acb83 0x88005445416ad65c 0xf8ae59b83fffcf9f 0xf7c572cdc1fffe7c

def z906 : W := mkw 0x03306000c0252004 0x4019830006012900 0xc7306041c07ff1ff 0x6e3983020e03ff8f

def z907 : W := mkw 0x07f5755400000010 0x003fabaaa0000000 0xbffffffe00000001 0x2dfffffff0000000

def z908 : W := mkw 0x0105755400000010 0x00082baaa0000000 0x380ffffe00000001 0xc1c07ffff0000000

def z909 : W := mkw 0x07f5755480240014 0x003fabaaa4012000 0xffffffffc0380005 0xfffffffffe01c000

def z910 : W := mkw 0x80008222018216a0 0x84000411100c10b5 0x4059a66603863ff9 0xfa02cd33301c31ff

def z911 : W := mkw 0x16ff8001bb76000f 0x80b7fc000ddbb000 0xd7ffa647fffe000e 0x3ebffd323ffff000

def z912 : W := mkw 0x07f5755400000010 0x003fabaaa0000000 0xffffffffc000000f 0xfffffffffe000000

def z913 : W := mkw 0x033061c0c02d6154 0x5019830e06016b0a 0xffb679d9c07ff1ff 0x6ffdb3cece03ff8f

def z914 : W := mkw 0x033075d4c02d6154 0x501983aea6016b0a 0xef79ffffc07ff1ff 0xff7bcffffe03ff8f

def z915 : W := mkw 0x16ff8021bb76028f 0x80b7fc010ddbb014 0xd7ffa667fffe0f9f 0xfebffd333ffff07c

def z916 : W := mkw 0x000a08a82c58cb83 0x080050454162c65c 0xf8ae59b83c7fffff 0xf7c572cdc1e3ffff

def z917 : W := mkw 0x16fa8001bb76000f 0x80b7d4000ddbb000 0xc7f00001fffe000e 0x3e3f80000ffff000

def z918 : W := mkw 0x033061d4c02d6154 0x5019830ea6016b0a 0xe73061ffc07ff1ff 0x6f39830ffe03ff8f

def z919 : W := mkw 0x000a08a82c58cb83 0x080050454162c65c 0xf8ae59b83c39ce05 0xf7c572cdc1e1ce70

def z920 : W := mkw 0x0dc07e015681bc08 0x606e03f00ab40de0 0xcf807801ff81fe1e 0x4e7c03c00ffc0ff0

def z921 : W := mkw 0x04c0000112000008 0x0026000008900000 0xc7e00001fff8000e 0x3e3f00000fffc000

def z922 : W := mkw 0x000a08a82c58cb83 0x080050454162c65c 0xf8ae79f83c79fff7 0xf7c573cfc1e3cfff

def z923 : W := mkw 0x16ff8001bb76000f 0x80b7fc000ddbb000 0xd7ffa001fffe301e 0x7ebffd000ffff180

def z924 : W := mkw 0x000a08a82c58cb83 0x080050454162c65c 0xf8be59f83c7fcff7 0xf7c5f2cfc1e3fe7f

def z925 : W := mkw 0x033061c0c02d6154 0x5019830e06016b0a 0xe771e7c7c07ff1ff 0x6f3b8f3e3e03ff8f

def z926 : W := mkw 0x0dc07e015681bc08 0x606e03f00ab40de0 0xcfc07e01ffc7fffe 0xde7e03f00ffe3fff

def z927 : W := mkw 0x0dc07e015681bc08 0x606e03f00ab40de0 0xcfd9fe01ff81fe1e 0xfe7ecff00ffc0ff0

def z928 : W := mkw 0x000a88a82d5acb83 0x88005445416ad65c 0xf8fffffe3fffcf9f 0xffc7fffff1fffe7c

def z929 : W := mkw 0x9ccf9e233fd29eab 0xa4e67cf119fe94f5 0x18cf9e263f800e00 0x90c67cf131fc0070

def z930 : W := mkw 0x000208880c18c901 0x080010444060c648 0xb8a659981c39ce14 0xc5c532ccc0e1ce70

def z931 : W := mkw 0x16f700019a34000d 0x00b7b8000cd1a000 0x97e60001dfb8000c 0x0cbf30000efdc000

def z932 : W := mkw 0x07f5755440012050 0x503fabaaa2000902 0xfffffffe00003061 0xfffffffff0000183

def z933 : W := mkw 0x07f5755400000010 0x003fabaaa0000000 0xfffffffe00063069 0xfffffffff0003183

def z934 : W := mkw 0x16ff8155bb76001f 0x80b7fc0aaddbb000 0xf7ff8199fffe000e 0x3fbffc0ccffff000

def z935 : W := mkw 0x033061c0c02d6154 0x5019830e06016b0a 0xef3079f9c07ff1ff 0xef7983cfce03ff8f

def z936 : W := mkw 0x8008822221c216a2 0x84004411110e10b5 0xc759a667e3c63fff 0xfe3acd333f1e31ff

def z937 : W := mkw 0x023001c0c02d6154 0x5011800e06016b0a 0xe73001c1c07ff1ff 0x2f39800e0e03ff8f

def z938 : W := mkw 0x07f5755552012018 0x403fabaaaa900900 0xffffffffff81f01f 0xfffffffffffc0f80

def z939 : W := mkw 0x16ff8021bb76028f 0x80b7fc010ddbb014 0xd7ff8021fffe0e0e 0xbebffc010ffff070

def z940 : W := mkw 0x16ff8001bb76000f 0x80b7fc000ddbb000 0xd7ef8001fff80006 0x36bf7c000fffc000

def z941 : W := mkw 0x07f5755400000010 0x003fabaaa0000000 0x3f7ffffe00000001 0xe9fbfffff0000000

def z942 : W := mkw 0x0ff57755d2a5345c 0x707fabbaae9529a2 0x0751a647c3863068 0x083a8d323e1c3183

def z943 : W := mkw 0x823a81eaa97e43f7 0x9c11d40f554bf21f 0x303f81fe007e01e1 0x2181fc0ff003f00f

def z944 : W := mkw 0x033061c0c02d6154 0x5019830e06016b0a 0xefb079c1c07ff1ff 0xff7d83ce0e03ff8f

def z945 : W := mkw 0x09007ffc4489ff90 0x684803ffe2244ffc 0x28007ffe0001ff91 0xc14003fff0000ffc

def z946 : W := mkw 0x07f5755440012010 0x403fabaaa2000900 0xffffffffc001c005 0xfffffffffe000e00

def z947 : W := mkw 0x07f5755480240014 0x003fabaaa4012000 0xfffffffe007e0001 0xfffffffff003f000

def z948 : W := mkw 0x800a8aaa2ddadfa3 0x8c005455516ed6fd 0x000000003ff9cf96 0x0000000001ffce7c

def z949 : W := mkw 0x07f5755400000010 0x003fabaaa0000000 0xfffffffe0046000b 0xfffffffff0023000

def z950 : W := mkw 0x07f5755440012010 0x403fabaaa2000900 0xfffffffe0001f011 0xfffffffff0000f80

def z951 : W := mkw 0x000a08a82c58cb83 0x080050454162c65c 0xf8a659983c79cf96 0xd7c532ccc1e3ce7c

def z952 : W := mkw 0x09006bc04489fd50 0x7048035e02244fea 0x200061c00001fff1 0x4100030e00000fff

def z953 : W := mkw 0x16ff8001bb76000f 0x80b7fc000ddbb000 0xd7ff8001fffe0e1e 0xfebffc000ffff070

def z954 : W := mkw 0x05c5741400000000 0x002e2ba0a0000000 0xffefffbe00000001 0xffff7ffdf0000000

def z955 : W := mkw 0x033061c0c02d6154 0x5019830e06016b0a 0xffffffffc07ff1ff 0xfffffffffe03ff8f

def z956 : W := mkw 0x923f80aaa97e43a7 0x8c91fc05554bf21d 0x303f81fe007e01e1 0x2181fc0ff003f00f

def z957 : W := mkw 0x033061c0c02d6154 0x5019830e06016b0a 0x273021c1c07ff1ff 0x2939810e0e03ff8f

def z958 : W := mkw 0x033061c0c02d6154 0x5019830e06016b0a 0xe73861e1c07ff1ff 0xff39c30f0e03ff8f

def z959 : W := mkw 0x16ff8001bb76000f 0x80b7fc000ddbb000 0xd7ff8021fffe000f 0xfebffc010ffff000

def z960 : W := mkw 0x123f80a8a97e4387 0x8891fc05454bf21c 0x103f8000007e0180 0x2081fc000003f00c

def z961 : W := mkw 0x033075d4c02d6154 0x501983aea6016b0a 0xffbe7fffc07ff1ff 0xfffdf3fffe03ff8f

def z962 : W := mkw 0x000a08a82c58cb83 0x080050454162c65c 0xf8efdfbe3c79cf97 0xf7c77efdf1e3ce7c

def z963 : W := mkw 0x16ff8155bb76001f 0x80b7fc0aaddbb000 0xf7ffa7fffffe000f 0xffbffd3ffffff000

def z964 : W := mkw 0x033061c0c02d6154 0x5019830e06016b0a 0x07000001c07ff1fe 0x003800000e03ff8f

def z965 : W := mkw 0x0dc07e015681bc08 0x606e03f00ab40de0 0xcfd9fe67ffc7ffff 0xfe7ecff33ffe3fff

def z966 : W := mkw 0x16ff8015bb76000f 0x80b7fc00addbb000 0xd7ff803ffffe000e 0x3ebffc01fffff000

def z967 : W := mkw 0x000208880c18c901 0x080010444060c648 0xf8ae59b83c39ce17 0xf7c572cdc1e1ce70

def z968 : W := mkw 0x06f5155400000010 0x0037a8aaa0000000 0xffff9ffe00000001 0xbffffcfff0000000

def z969 : W := mkw 0x07f5755400000010 0x003fabaaa0000000 0xfffffffe00780007 0xfffffffff003c000

def z970 : W := mkw 0x123a8001bb76000f 0x8091d4000ddbb000 0x07100001fffe000e 0x083880000ffff000

def z971 : W := mkw 0x09007e015681bc08 0x604803f00ab40de0 0xcf007e01ff81fe1e 0xce7803f00ffc0ff0

def z972 : W := mkw 0x0dca76a97ad9778b 0x686e53b54bd6cbbc 0x376e27b9c3f83189 0x29bb713dce1fc18c

def z973 : W := mkw 0x023000019224000c 0x001180000c912000 0xc7300001fffe000e 0x2e3980000ffff000

def z974 : W := mkw 0x000a08a82c58cb83 0x080050454162c65c 0xb8ae59b83c39cf95 0xd5c572cdc1e1ce7c

def z975 : W := mkw 0x07f5755512000018 0x003fabaaa8900000 0xffffffffc3800009 0xfffffffffe1c0000

def z976 : W := mkw 0x8008822221c216a2 0x84004411110e10b5 0x0059a66623c63fe9 0xb802cd33311e31ff

def z977 : W := mkw 0x04c5141400000000 0x002628a0a0000000 0xb8efdfbe00000000 0x95c77efdf0000000

def z978 : W := mkw 0x14cf8001bb76000f 0x80a67c000ddbb000 0xd7cf8001fffe000e 0x1ebe7c000ffff000

def z979 : W := mkw 0x123f8001bb76000f 0x8091fc000ddbb000 0xd73f8001fffe000e 0x2eb9fc000ffff000

def z980 : W := mkw 0x000a08a82c58cb83 0x080050454162c65c 0xf8ae59983c79cf96 0x37c572ccc1e3ce7c

def z981 : W := mkw 0x04c200011a100009 0x0026100008d08000 0xd7e60001ffb8000e 0x1ebf30000ffdc000

def z982 : W := mkw 0x09006a015681bc08 0x604803500ab40de0 0xc7406601ff81fe1e 0xde3a03300ffc0ff0

def z983 : W := mkw 0x000208a80c18cb81 0x080010454060c65c 0xf8a659b81c79cf97 0xe7c532cdc0e3ce7c

def z984 : W := mkw 0x1ff5f755d3a7341c 0xe0ffafbaae9d39a0 0x0751a647c3863008 0x083a8d323e1c3180

def z985 : W := mkw 0x033561c0c02d6154 0x5019ab0e06016b0a 0xf73fe1c1c07ff1ff 0x6fb9ff0e0e03ff8f

def z986 : W := mkw 0x16f780019b36000d 0x80b7bc000cd9b000 0xd7f78001ffbe000e 0x1ebfbc000ffdf000

def z987 : W := mkw 0x16ff8001bb76000f 0x80b7fc000ddbb000 0x97ff8001ffbe000c 0x1cbffc000ffdf000

def z988 : W := mkw 0x16ff9415bb76000f 0x80b7fca0addbb000 0xdfff9819fffe000e 0x3efffcc0cffff000

def z989 : W := mkw 0x033061c0c02d6154 0x5019830e06016b0a 0xe739e1e7c07ff1ff 0x6f39cf0f3e03ff8f

def z990 : W := mkw 0x000a08a82c58cb83 0x080050454162c65c 0xb8a659b83c79cf97 0xc5c532cdc1e3ce7c

def z991 : W := mkw 0x0dc07e015681bc08 0x606e03f00ab40de0 0xcfd07e41ff81fe1f 0xfe7e83f20ffc0ff0

def z992 : W := mkw 0x09007fd44489fd50 0x704803fea2244fea 0x28007ffe0001fff1 0xc14003fff0000fff

def z993 : W := mkw 0x000a08a82c58cb83 0x080050454162c65c 0xf8ae59b83c39ce16 0xd7c572cdc1e1ce70

def z994 : W := mkw 0x04c5141400000000 0x002628a0a0000000 0xf8fffffe00000001 0xffc7fffff0000000

def z995 : W := mkw 0x800a88aa2d5acba3 0x8c005445516ad65d 0xf8fffffe3c7fcff7 0xffc7fffff1e3fe7f

def z996 : W := mkw 0x033061c0c02d6154 0x5019830e06016b0a 0xe779e1c1c07ff1ff 0x7f3bcf0e0e03ff8f

def z997 : W := mkw 0x07f5755400000010 0x003fabaaa0000000 0xbfbffffe00000001 0xe5fdfffff0000000

def z998 : W := mkw 0x05c068015601a808 0x402e03400ab00d40 0xcfc07801ff81fe1e 0xde7e03c00ffc0ff0

def z999 : W := mkw 0x8008822221c216a2 0x84004411110e10b5 0x58dfbe7e23c63ffb 0xfac6fdf3f11e31ff

def z1000 : W := mkw 0x06f5141400000000 0x0037a8a0a0000000 0xffffdfbe00000001 0xfffffefdf0000000

def z1001 : W := mkw 0x16ff8001bb76000f 0x80b7fc000ddbb000 0xffffd999fffe000e 0x3ffffecccffff000

def z1002 : W := mkw 0x010061c0c02d6154 0x5008030e06016b0a 0xe70061c1c07ff1ff 0x4f38030e0e03ff8f

def z1003 : W := mkw 0x800a08aa2c58cba3 0x0c0050455162c65d 0xf8ae59fe3c79cff7 0xf7c572cff1e3ce7f

def z1004 : W := mkw 0x0dc07e015681bc08 0x606e03f00ab40de0 0x0fc03e01ff81fe1e 0x987e01f00ffc0ff0

def z1005 : W := mkw 0x033061c0c02d6154 0x5019830e06016b0a 0xc7302041c07ff1fe 0x2e3981020e03ff8f

def z1006 : W := mkw 0x000a08a82c58cb83 0x080050454162c65c 0xb8ae59b83c79cf85 0xb5c572cdc1e3ce7c

def z1007 : W := mkw 0x07f5755400000010 0x003fabaaa0000000 0xfffffffe000031f1 0xfffffffff000018f

def z1008 : W := mkw 0x03306080c02d6144 0x5019830406016b0a 0xc7306001c07ff1fe 0x6e3983000e03ff8f

def z1009 : W := mkw 0x16ff8021bb76028f 0x80b7fc010ddbb014 0xffffd9b9fffe0f9f 0xfffffecdcffff07c

def z1010 : W := mkw 0x16ff8155bb76001f 0x80b7fc0aaddbb000 0xd7ff8047fffe000e 0x3ebffc023ffff000

def z1011 : W := mkw 0x000a08a82c58cb83 0x080050454162c65c 0xf8ee7fb83c79cf97 0xffc773fdc1e3ce7c

def z1012 : W := mkw 0x0dc07f555681bc18 0x606e03faaab40de0 0xefc07f99ff81fe1e 0xdf7e03fccffc0ff0

def z1013 : W := mkw 0x07f5755400000010 0x003fabaaa0000000 0xfffffffe00400193 0xfffffffff002000c

def z1014 : W := mkw 0x09006a015681bc08 0x604803500ab40de0 0x87004001ff81fe1e 0x043802000ffc0ff0

def z1015 : W := mkw 0x033561d4c02d6154 0x5019ab0ea6016b0a 0xf73661d9c07ff1ff 0x6fb9b30ece03ff8f

def z1016 : W := mkw 0x0dc57e155681bc08 0x606e2bf0aab40de0 0xcfc1fe07ff81fe1e 0xde7e0ff03ffc0ff0

def z1017 : W := mkw 0x14ca8001bb76000f 0x80a654000ddbb000 0xc7d98001fffe000e 0x3e3ecc000ffff000

def z1018 : W := mkw 0x8008822221c216a2 0x84004411110e10b5 0x0059a66623863ff9 0xd802cd33311c31ff

def z1019 : W := mkw 0x96ff8023bb7602af 0x84b7fc011ddbb015 0xd7ff8027fffe000e 0x3ebffc013ffff000

def z1020 : W := mkw 0x16ff9415bb76000f 0x80b7fca0addbb000 0xdfffbe7ffffe000f 0xfefffdf3fffff000

def z1021 : W := mkw 0x000a08a82c58cb83 0x080050454162c65c 0xb8ae59b83c79cf97 0x25c572cdc1e3ce7c

def z1022 : W := mkw 0x033061c0c02d6154 0x5019830e06016b0a 0xe73061c1e07fffff 0xff39830e0f03ffff

def z1023 : W := mkw 0x09007e884489fd00 0x684803f442244fe8 0x28007f980001fe10 0xc14003fcc0000ff0

def z1024 : W := mkw 0x07f5755400000010 0x003fabaaa0000000 0xfffffffe0000301b 0xfffffffff0000180

def z1025 : W := mkw 0x0ff5755552012018 0x607fabaaaa900900 0xffffffffc0000001 0xfffffffffe000000

def z1026 : W := mkw 0x100a8001bb76000f 0x808054000ddbb000 0xc7000001fffe000e 0x0e3800000ffff000

def z1027 : W := mkw 0x96ff8023bb7602af 0x84b7fc011ddbb015 0xd7ff8067fffe0fff 0xfebffc033ffff07f

def z1028 : W := mkw 0x8008822221c216a2 0x84004411110e10b5 0x0059a66623c63ffb 0x2802cd33311e31ff

def z1029 : W := mkw 0x07f5755400000010 0x003fabaaa0000000 0xbfffdffe00000001 0xb5fffefff0000000

def z1030 : W := mkw 0x07f5755400000010 0x003fabaaa0000000 0xfffffffe004601e1 0xfffffffff002300f

def z1031 : W := mkw 0x0dc07e015681bc08 0x606e03f00ab40de0 0x8fc07e01ff81fe1e 0x0c7e03f00ffc0ff0

def z1032 : W := mkw 0x04c5141400000000 0x002628a0a0000000 0x38ef9fbe00000001 0xb1c77cfdf0000000

def z1033 : W := mkw 0x16ff8001bb76000f 0x80b7fc000ddbb000 0xfffffffffffe000f 0xfffffffffffff000

def z1034 : W := mkw 0x000a08a82c58cb83 0x080050454162c65c 0xf8ae59b83c79ce06 0xb7c572cdc1e3ce70

def z1035 : W := mkw 0x000a08a82c58cb83 0x080050454162c65c 0xf8ae7ffe3c79cf97 0xf7c573fff1e3ce7c

def z1036 : W := mkw 0x07f5755400000010 0x003fabaaa0000000 0xbffffffe00000000 0x9dfffffff0000000

def z1037 : W := mkw 0x033061c0c02d6154 0x5019830e06016b0a 0xe77061c1e3fff1ff 0x7f3b830e0f1fff8f

def z1038 : W := mkw 0x02300080c02d6144 0x5011800406016b0a 0x87200001c07ff1fe 0x043900000e03ff8f

def z1039 : W := mkw 0x16ff8001bb76000f 0x80b7fc000ddbb000 0xc7d18001fffe000e 0x1e3e8c000ffff000

def z1040 : W := mkw 0x0dc07e015681bc08 0x606e03f00ab40de0 0xcf805801ff81fe1e 0xd67c02c00ffc0ff0

def z1041 : W := mkw 0x16ff8001bb76000f 0x80b7fc000ddbb000 0xd7ffa601fffe000e 0xfebffd300ffff000

def z1042 : W := mkw 0x16ff9415bb76000f 0x80b7fca0addbb000 0xd7ff8607fffe000e 0x3ebffc303ffff000

def z1043 : W := mkw 0x033061c0c02d6154 0x5019830e06016b0a 0xa73061c1c07ff1fe 0x0d39830e0e03ff8f

def z1044 : W := mkw 0x0dc06a015681bc08 0x606e03500ab40de0 0xc7c06001ff81fe1e 0x5e3e03000ffc0ff0

def z1045 : W := mkw 0x8008822221c216a2 0x84004411110e10b5 0x0059a66623c63ffa 0x9802cd33311e31ff

def z1046 : W := mkw 0x033061c0c02d6154 0x5019830e06016b0a 0xf73e61f9c07ff1ff 0x6fb9f30fce03ff8f

def z1047 : W := mkw 0x0dc07e015681bc08 0x606e03f00ab40de0 0xcfe07e01fff9fe1e 0xfe7f03f00fffcff0

def z1048 : W := mkw 0x02300080c02d6144 0x5011800406016b0a 0xe7304181c07ff1ff 0x6f39820c0e03ff8f

def z1049 : W := mkw 0x94cf8a2b3fd29eab 0x8ca67c5159fe94f5 0x18cf9e3e3f800e00 0x90c67cf1f1fc0070

def z1050 : W := mkw 0x000a08a82c58cb83 0x080050454162c65c 0xf8fffffe3c7fffff 0xffc7fffff1e3ffff

def z1051 : W := mkw 0x033061c0c02d6154 0x5019830e06016b0a 0xf7be61c1c07ff1ff 0x7fbdf30e0e03ff8f

def z1052 : W := mkw 0x0dc07e015681bc08 0x606e03f00ab40de0 0xcfc07e01ffc1ff9f 0xfe7e03f00ffe0ffc

def z1053 : W := mkw 0x02300080c02d6144 0x5011800406016b0a 0xc7302041c07ff1ff 0x6e3981020e03ff8f

def z1054 : W := mkw 0x02300080c02d6144 0x5011800406016b0a 0x07100001c07ff1fe 0x083880000e03ff8f

def z1055 : W := mkw 0x07f5755400000010 0x003fabaaa0000000 0xfffffffe2380000b 0xfffffffff11c0000

def z1056 : W := mkw 0x16ff8001bb76000f 0x80b7fc000ddbb000 0x177f8001fffe000e 0x28bbfc000ffff000

def z1057 : W := mkw 0x07f57554c0252054 0x503fabaaa6012902 0xffffffffc07e306f 0xfffffffffe03f183

def z1058 : W := mkw 0x16ff8001bb76000f 0x80b7fc000ddbb000 0xd7ffa041fffe000f 0x7ebffd020ffff000

def z1059 : W := mkw 0x09007fc04489fd50 0x704803fe02244fea 0x28007f800001fe10 0xc14003fc00000ff0

def z1060 : W := mkw 0x000a88a82d5acb83 0x88005445416ad65c 0xf8bfd9b83c7fcf97 0xf7c5fecdc1e3fe7c

def z1061 : W := mkw 0x0dc07f555681bc18 0x606e03faaab40de0 0xefd9ffffff81fe1f 0xff7ecffffffc0ff0

def z1062 : W := mkw 0x8008822221c216a2 0x84004411110e10b5 0xc8d9fe6623c63ffb 0xfe46cff3311e31ff

def z1063 : W := mkw 0x16ff8001bb76000f 0x80b7fc000ddbb000 0x97ff8001fffe0004 0x34bffc000ffff000

def z1064 : W := mkw 0x8008822221c216a2 0x84004411110e10b5 0xc059e66623c7ffff 0xfe02cf33311e3fff

def z1065 : W := mkw 0x0dc07e015681bc08 0x606e03f00ab40de0 0xcfc05e01ff81ce0e 0x9e7e02f00ffc0e70

def z1066 : W := mkw 0x000a08002c508803 0x0000504001628440 0xf8ae59b83c79ce17 0xf7c572cdc1e3ce70

def z1067 : W := mkw 0x16f700019a34000d 0x00b7b8000cd1a000 0x97a60001ffb8000e 0x04bd30000ffdc000

def z1068 : W := mkw 0x16ff8001bb76000f 0x80b7fc000ddbb000 0xd7ff8001fffe31fe 0x3ebffc000ffff18f

def z1069 : W := mkw 0x033561d4c02d6154 0x5019ab0ea6016b0a 0xf77fe7ffc07ff1ff 0xffbbff3ffe03ff8f

def z1070 : W := mkw 0x8008822221c216a2 0x84004411110e10b5 0xc079a66623fe3fff 0xfe03cd33311ff1ff

def z1071 : W := mkw 0x8008822221c216a2 0x84004411110e10b5 0x0051a66623c63ffb 0xc8028d33311e31ff

def z1072 : W := mkw 0x0dc07e015681bc08 0x606e03f00ab40de0 0xcfc87e21ff81fe1f 0xfe7e43f10ffc0ff0

def z1073 : W := mkw 0x05c5755400000010 0x002e2baaa0000000 0x38cfdfbe00000000 0x91c67efdf0000000

def z1074 : W := mkw 0x16ff8029bb76028f 0x88b7fc014ddbb014 0xd7ff8039fffe000e 0x3ebffc01cffff000

def z1075 : W := mkw 0x0dc57e155681bc08 0x606e2bf0aab40de0 0xdfc67e19ff81fe1e 0xdefe33f0cffc0ff0

def z1076 : W := mkw 0x07f57554c0252014 0x403fabaaa6012900 0xffffffffc07ff01f 0xfffffffffe03ff80

def z1077 : W := mkw 0x0cc00a015681bc08 0x606600500ab40de0 0x07400001ff81fe1e 0x083a00000ffc0ff0

def z1078 : W := mkw 0x8dc07e035681bc28 0x646e03f01ab40de1 0xcfc07e47ff81fe7e 0xde7e03f23ffc0ff3

def z1079 : W := mkw 0x000008800408c900 0x0000004400204648 0xf8ae59b83c79cf97 0xf7c572cdc1e3ce7c

def z1080 : W := mkw 0x8008822221c216a2 0x84004411110e10b5 0x4051a64623c63ffb 0x6a028d32311e31ff

def z1081 : W := mkw 0x07f5755480240054 0x103fabaaa4012002 0xfffffffe00060061 0xfffffffff0003003

def z1082 : W := mkw 0x0cc01e0116809c08 0x206600f008b404e0 0xcfc05e01ff81ce1e 0xde7e02f00ffc0e70

def z1083 : W := mkw 0x0ff57dd5d62de95c 0x707fabeeaeb16f4a 0xbfa65999dc39c004 0x05fd32cccee1ce00

def z1084 : W := mkw 0x0dc07e155681bc08 0x606e03f0aab40de0 0xcfc07e3fff81fe1e 0xde7e03f1fffc0ff0

def z1085 : W := mkw 0x16ff8001bb76000f 0x80b7fc000ddbb000 0xd7b60001fffe000e 0x2ebdb0000ffff000

def z1086 : W := mkw 0x000208880c18c901 0x080010444060c648 0xb8a659983c39ce04 0x95c532ccc1e1ce70

def z1087 : W := mkw 0x96ff8177bb7602bf 0x84b7fc0bbddbb015 0xf7ff81fffffe01ef 0x3fbffc0ffffff00f

def z1088 : W := mkw 0x07f5755512000018 0x003fabaaa8900000 0xffffffffdc000005 0xfffffffffee00000

def z1089 : W := mkw 0x123a8001bb76000f 0x8091d4000ddbb000 0xd7be0001fffe000e 0x3ebdf0000ffff000

def z1090 : W := mkw 0x07f5755400000010 0x003fabaaa0000000 0xffefdfbe00000001 0xf7ff7efdf0000000

def z1091 : W := mkw 0x16f780019b36000d 0x80b7bc000cd9b000 0x07518001dfbe000c 0x083a8c000efdf000

def z1092 : W := mkw 0x123f81fca97e4397 0x8891fc0fe54bf21c 0x303f81fe007e0181 0x2181fc0ff003f00c

def z1093 : W := mkw 0x16ff0001ba74000f 0x00b7f8000dd3a000 0xd7ee0001fff8000e 0x3ebf70000fffc000

def z1094 : W := mkw 0x05c5755400000010 0x002e2baaa0000000 0x78dffffe00000001 0xfbc6fffff0000000

def z1095 : W := mkw 0x8008822221c216a2 0x84004411110e10b5 0x0059a66603c63ff9 0xe802cd33301e31ff

def z1096 : W := mkw 0x07f5755400000010 0x003fabaaa0000000 0xffefffbe00000000 0xdfff7ffdf0000000

def z1097 : W := mkw 0x07f5755400000010 0x003fabaaa0000000 0x3fffbffe00000001 0xb9fffdfff0000000

def z1098 : W := mkw 0x033061c0c02d6154 0x5019830e06016b0a 0xe7204181c07ff1ff 0x6739020c0e03ff8f

def z1099 : W := mkw 0x000a08a82c58cb83 0x080050454162c65c 0xf8ee59b83ff9cf9f 0xffc772cdc1ffce7c

def z1100 : W := mkw 0x16ff8001bb76000f 0x80b7fc000ddbb000 0x07000001fffe000e 0x003800000ffff000

def z1101 : W := mkw 0x16f700019a34000d 0x00b7b8000cd1a000 0xd7f60001fffe000e 0x3ebfb0000ffff000

def z1102 : W := mkw 0x000208880c18c901 0x080010444060c648 0xb8a659983c39ce16 0x05c532ccc1e1ce70

def z1103 : W := mkw 0x000208a80c18cb81 0x080010454060c65c 0xb8a659981c39cf94 0x05c532ccc0e1ce7c

def z1104 : W := mkw 0x800a8aaaedffffe7 0xdc005455576fffff 0x00000001fffffffe 0x000000000fffffff

def z1105 : W := mkw 0x16f700019a34000d 0x00b7b8000cd1a000 0xd7ff8001ffb8000e 0x3ebffc000ffdc000

def z1106 : W := mkw 0x09006a015681bc08 0x604803500ab40de0 0xcf807801ff81fe1e 0xde7c03c00ffc0ff0

def z1107 : W := mkw 0x04c00a0116809c08 0x0026005008b404e0 0xcfc07e01ff81fe1e 0xde7e03f00ffc0ff0

def z1108 : W := mkw 0x07f57554c0252054 0x503fabaaa6012902 0xffffffffc04631fb 0xfffffffffe02318f

def z1109 : W := mkw 0x000208a80c18cb81 0x080010454060c65c 0xf8a659b83c39cf97 0xd7c532cdc1e1ce7c

def z1110 : W := mkw 0x01006a004481bc00 0x4008035002240de0 0xcfc07e01ff81fe1e 0xde7e03f00ffc0ff0

def z1111 : W := mkw 0x16f780019b36000d 0x80b7bc000cd9b000 0x97a60001dfbe000c 0x04bd30000efdf000

def z1112 : W := mkw 0x14ca8001bb76000f 0x80a654000ddbb000 0x07400001fffe000e 0x083a00000ffff000

def z1113 : W := mkw 0x09007fe84489ffd0 0x784803ff42244ffe 0x28007ff80001fff1 0xc14003ffc0000fff

def z1114 : W := mkw 0x16f780019b36000d 0x80b7bc000cd9b000 0xd7f78001dffe000e 0x2ebfbc000efff000

def z1115 : W := mkw 0x8008822221c216a2 0x84004411110e10b5 0x6859fffe23c63ffb 0xfb42cffff11e31ff

def z1116 : W := mkw 0x0dc07e015681bc08 0x606e03f00ab40de0 0x0f407e01ff81fe1e 0xc87a03f00ffc0ff0

def z1117 : W := mkw 0x06ff00013a50000b 0x0037f80009d28000 0xd7ff8001fff8000e 0x3ebffc000fffc000

def z1118 : W := mkw 0x16ff8001bb76000f 0x80b7fc000ddbb000 0x97ff8001dffe000c 0x2cbffc000efff000

def z1119 : W := mkw 0x0dc57e155681bc08 0x606e2bf0aab40de0 0xdfdffe7fff81fe1f 0xfefefff3fffc0ff0

def z1120 : W := mkw 0x033561d4c02d6154 0x5019ab0ea6016b0a 0xffbff9ffc07ff1ff 0xfffdffcffe03ff8f

def z1121 : W := mkw 0x96ff8023bb7602af 0x84b7fc011ddbb015 0xd7ff8001fffe01ee 0x3ebffc000ffff00f

def z1122 : W := mkw 0x06f500019224000c 0x0037a8000c912000 0xd7ff8001fffe000e 0x3ebffc000ffff000

def z1123 : W := mkw 0x0dc07e015681bc08 0x606e03f00ab40de0 0xcfc07e41ff81ffff 0xde7e03f20ffc0fff

def z1124 : W := mkw 0x16ff8001bb76000f 0x80b7fc000ddbb000 0xc7718001fffe000e 0x2e3b8c000ffff000

def z1125 : W := mkw 0x033061c0c02d6154 0x5019830e06016b0a 0x47102041c07ff1ff 0x6a3881020e03ff8f

def z1126 : W := mkw 0x0dc07f555681bc18 0x606e03faaab40de0 0xcfc07e47ff81fe1e 0xde7e03f23ffc0ff0

def z1127 : W := mkw 0x000a08882c58c903 0x080050444162c648 0xf8ae59983c79ce16 0xf7c572ccc1e3ce70

def z1128 : W := mkw 0x0dc07e015681bc08 0x606e03f00ab40de0 0xcfd1fe47ff81fe1e 0xde7e8ff23ffc0ff0

def z1129 : W := mkw 0x800a88aa2d5acba3 0x8c005445516ad65d 0xf8bff9fe3c7fffff 0xffc5ffcff1e3ffff

def z1130 : W := mkw 0x800a88aa2d5acba3 0x8c005445516ad65d 0xf8ae59b83c7fcff7 0xf7c572cdc1e3fe7f

def z1131 : W := mkw 0x033075d4c02d6154 0x501983aea6016b0a 0xe73067c7c07ff1ff 0x6f39833e3e03ff8f

def z1132 : W := mkw 0x07f5755480240014 0x003fabaaa4012000 0xffffffffc07e31ff 0xfffffffffe03f18f

def z1133 : W := mkw 0x06f5155400000010 0x0037a8aaa0000000 0xf8ffdffe00000001 0xf7c7fefff0000000

def z1134 : W := mkw 0x0335755400000010 0x0019abaaa0000000 0x787ffffe00000001 0xfbc3fffff0000000

def z1135 : W := mkw 0x89007fe24489fff0 0x744803ff12244fff 0x28007fe60001fff1 0xc14003ff30000fff

def z1136 : W := mkw 0x06f88001b366000e 0x8037c4000d9b3000 0xc7f98001fffe000e 0x3e3fcc000ffff000

def z1137 : W := mkw 0x000a08a82c58cb83 0x080050454162c65c 0xf8ffd9b83c79cf97 0xffc7fecdc1e3ce7c

def z1138 : W := mkw 0x033061c0c02d6154 0x5019830e06016b0a 0xa72061c1c07ff1ff 0x4539030e0e03ff8f

def z1139 : W := mkw 0x8008822221c216a2 0x84004411110e10b5 0xd0ffa66623c63ffb 0xfe87fd33311e31ff

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z0,z2,z7,z3,z4,z5,z6]),(0,[z0,z8,z2,z3,z9,z5,z6]),(0,[z0,z10,z2,z3,z4,z5,z6]),(0,[z0,z2,z11,z3,z4,z6,z12]),(0,[z0,z2,z3,z4,z5,z13,z6]),(0,[z0,z2,z3,z4,z14,z5,z6])],[(0,[z0,z15,z2,z3,z4,z5,z6]),(0,[z16,z0,z2,z3,z17,z5,z6]),(0,[z0,z2,z3,z4,z5,z18,z6]),(1,[z0,z2,z3,z19,z5,z6])],[(0,[z20,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z21,z3,z4,z5,z6]),(1,[z22,z2,z3,z4,z5,z6])],[(0,[z0,z23,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z24,z5,z6]),(1,[z0,z2,z25,z4,z5,z6]),(0,[z26,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z27,z28,z6]),(0,[z0,z2,z3,z4,z5,z6,z29]),(0,[z0,z2,z30,z4,z5,z31,z6]),(0,[z0,z2,z3,z4,z32,z5,z6])],[(0,[z33,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z34])],[(0,[z0,z35,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z36,z6]),(0,[z0,z2,z3,z4,z5,z37,z6]),(0,[z0,z38,z2,z3,z19,z5,z6]),(0,[z0,z2,z3,z39,z4,z27,z6]),(0,[z40,z0,z2,z3,z4,z5,z6])],[(0,[z41,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z5,z42]),(0,[z43,z0,z2,z3,z39,z4,z6]),(0,[z0,z2,z3,z44,z4,z5,z6]),(1,[z45,z2,z3,z4,z5,z6])]],
   [[(1,[z0,z2,z46,z4,z5,z6]),(0,[z0,z47,z2,z3,z4,z5,z6])],[(0,[z48,z0,z2,z3,z49,z5,z6]),(0,[z50,z0,z2,z3,z4,z5,z6]),(1,[z51,z0,z3,z4,z5,z52]),(0,[z0,z2,z53,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z54])],[(0,[z0,z2,z3,z4,z5,z6,z55]),(0,[z0,z2,z3,z56,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z57,z6]),(0,[z58,z59,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z60,z4,z5,z6]),(0,[z61,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z62,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z63,z5,z6])],[(0,[z0,z64,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z65,z4,z5,z6]),(0,[z0,z2,z66,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z67])],[(0,[z16,z0,z2,z3,z4,z5,z68])],[(1,[z0,z2,z3,z4,z5,z68]),(0,[z0,z2,z3,z4,z5,z6,z69]),(0,[z70,z0,z2,z71,z4,z5,z6]),(0,[z70,z0,z72,z3,z4,z5,z6]),(0,[z0,z2,z3,z73,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z74,z6])]],
   [[(0,[z0,z72,z3,z30,z4,z5,z6]),(0,[z0,z75,z3,z4,z5,z76,z6]),(0,[z0,z72,z2,z3,z4,z5,z57]),(0,[z0,z2,z3,z4,z77,z5,z6]),(0,[z58,z0,z2,z3,z4,z78,z6]),(0,[z79,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z6,z80])],[(0,[z0,z2,z3,z4,z81,z5,z6]),(0,[z0,z82,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z83,z6])],[(0,[z2,z3,z4,z84,z5,z28,z6]),(0,[z0,z2,z3,z4,z85,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z86]),(0,[z87,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z88]),(0,[z0,z2,z3,z4,z89,z6,z80])],[(0,[z90,z0,z2,z91,z4,z5,z6]),(0,[z0,z2,z3,z4,z92,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z93]),(0,[z0,z2,z94,z3,z95,z5,z6]),(0,[z96,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z97,z3,z4,z5,z6]),(0,[z0,z2,z98,z3,z4,z5,z6]),(0,[z0,z2,z99,z3,z4,z5,z6]),(0,[z0,z2,z3,z100,z5,z6,z101]),(0,[z0,z2,z3,z4,z5,z6,z102]),(0,[z0,z2,z3,z4,z5,z6,z103]),(0,[z58,z0,z2,z3,z104,z5,z6]),(0,[z105,z0,z2,z3,z4,z5,z6]),(0,[z0,z106,z2,z3,z4,z5,z6]),(0,[z0,z107,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z108,z5,z6]),(0,[z109,z2,z3,z110,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z111]),(0,[z0,z2,z112,z3,z4,z5,z6]),(1,[z0,z2,z11,z3,z83,z6])],[(0,[z0,z38,z2,z3,z4,z113,z6]),(0,[z114,z0,z2,z3,z4,z5,z6]),(0,[z0,z115,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z116,z89,z6])]],
   [[(0,[z0,z2,z3,z4,z5,z117,z6]),(0,[z70,z0,z118,z3,z4,z5,z6]),(0,[z119,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z120,z3,z4,z5,z6]),(0,[z0,z2,z3,z121,z4,z5,z6])],[(0,[z58,z90,z0,z2,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z5,z6]),(0,[z122,z2,z3,z4,z5,z117,z6])],[(0,[z0,z2,z123,z3,z4,z5,z6]),(0,[z48,z2,z3,z4,z5,z6,z69]),(0,[z124,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z125,z5,z6])],[(0,[z0,z2,z3,z4,z5,z126,z6]),(0,[z127,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z128,z5,z6]),(0,[z0,z8,z2,z25,z4,z5,z6]),(0,[z51,z45,z2,z3,z4,z5,z6]),(0,[z0,z2,z129,z3,z4,z5,z130]),(0,[z0,z2,z131,z3,z4,z5,z6])],[(0,[z90,z2,z91,z3,z4,z5,z6]),(0,[z132,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z133,z6]),(0,[z134,z0,z2,z3,z4,z5,z6]),(0,[z0,z47,z2,z3,z9,z5,z6]),(0,[z51,z0,z2,z135,z4,z5,z6]),(0,[z136,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z137]),(0,[z0,z38,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z138,z5,z6]),(0,[z0,z139,z2,z3,z4,z85,z6])],[(0,[z0,z2,z3,z4,z140,z5,z6]),(0,[z122,z2,z3,z110,z4,z5,z6]),(0,[z0,z2,z3,z95,z110,z5,z6]),(0,[z0,z141,z2,z3,z4,z5,z6]),(1,[z0,z2,z142,z4,z5,z6]),(0,[z143,z0,z2,z3,z4,z5,z6])],[(0,[z0,z144,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z145,z6]),(0,[z146,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z147,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z148])]],
   [[(0,[z149,z0,z2,z3,z4,z5,z6]),(0,[z150,z0,z2,z3,z4,z5,z6])],[(0,[z16,z0,z2,z3,z4,z151,z6]),(0,[z0,z2,z3,z4,z84,z31,z6]),(0,[z0,z2,z3,z152,z4,z5,z6])],[(0,[z0,z2,z3,z153,z4,z5,z6]),(1,[z0,z2,z3,z4,z151,z6]),(0,[z0,z2,z154,z3,z4,z5,z6])],[(0,[z155,z0,z156,z3,z4,z5,z6]),(0,[z16,z0,z2,z71,z4,z5,z6]),(0,[z109,z0,z2,z3,z157,z5,z6]),(0,[z158,z2,z3,z4,z84,z5,z6]),(1,[z0,z2,z159,z4,z5,z6]),(1,[z0,z139,z3,z4,z85,z6]),(0,[z0,z2,z3,z4,z5,z6,z160]),(1,[z0,z2,z3,z161,z5,z6])],[(0,[z0,z162,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z163,z6]),(0,[z0,z2,z3,z4,z164,z5,z6]),(0,[z0,z2,z3,z165,z9,z5,z6])],[(0,[z0,z2,z3,z4,z166,z5,z6]),(0,[z0,z2,z3,z167,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z76,z6]),(0,[z168,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z169,z6]),(0,[z0,z2,z3,z4,z27,z5,z170])],[(0,[z171,z0,z2,z3,z4,z5,z6]),(0,[z0,z172,z2,z3,z4,z5,z6]),(0,[z0,z2,z173,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z174,z5,z6]),(0,[z0,z2,z175,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z176,z6])],[(0,[z0,z2,z3,z4,z5,z177,z6]),(1,[z0,z2,z3,z4,z5,z126]),(0,[z0,z2,z3,z4,z84,z27,z6]),(0,[z0,z2,z3,z4,z5,z6,z178]),(0,[z0,z2,z3,z4,z27,z31,z6]),(0,[z179,z0,z2,z3,z4,z5,z6])]],
   [[(0,[z0,z2,z3,z180,z4,z5,z6]),(0,[z0,z2,z3,z181,z4,z5,z6]),(0,[z158,z0,z2,z3,z4,z28,z6]),(0,[z0,z38,z2,z3,z161,z5,z6]),(0,[z0,z2,z3,z4,z5,z182,z6]),(0,[z0,z183,z2,z3,z4,z5,z6])],[(0,[z90,z0,z2,z4,z5,z130,z6]),(1,[z184,z2,z3,z4,z5,z69]),(0,[z0,z45,z2,z3,z4,z5,z6]),(0,[z0,z185,z2,z3,z4,z5,z6])],[(0,[z2,z3,z186,z4,z5,z6,z69]),(0,[z187,z0,z2,z3,z4,z5,z6])],[(0,[z16,z0,z2,z3,z4,z188,z6]),(0,[z0,z38,z2,z30,z4,z5,z6]),(0,[z0,z8,z47,z3,z4,z5,z6]),(0,[z51,z0,z2,z3,z4,z5,z6])],[(1,[z0,z189,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z117,z6,z69]),(0,[z0,z2,z3,z4,z5,z78,z6]),(0,[z0,z2,z190,z3,z4,z5,z6])],[(0,[z158,z43,z2,z3,z4,z5,z6]),(0,[z191,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z11,z3,z95,z5,z6]),(0,[z0,z2,z3,z192,z4,z5,z6]),(0,[z58,z0,z2,z129,z4,z5,z6]),(0,[z0,z2,z3,z39,z4,z83,z6]),(0,[z193,z0,z2,z3,z4,z5,z6])],[(0,[z194,z2,z195,z3,z4,z5,z6]),(0,[z0,z196,z2,z3,z4,z5,z6]),(0,[z43,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z197,z4,z5,z6]),(0,[z0,z198,z2,z3,z9,z5,z6]),(0,[z0,z2,z11,z3,z4,z31,z6]),(0,[z0,z2,z3,z4,z5,z6,z199])],[(0,[z0,z2,z200,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z201,z5,z6]),(0,[z70,z0,z71,z3,z4,z5,z6]),(0,[z0,z198,z2,z3,z4,z202,z6])]],
   [[(0,[z0,z2,z3,z4,z5,z203,z6]),(0,[z0,z2,z3,z204,z4,z5,z6]),(0,[z205,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z110,z9,z5,z6]),(0,[z0,z2,z3,z4,z5,z170,z117]),(0,[z0,z139,z2,z3,z4,z31,z6]),(0,[z0,z72,z2,z3,z4,z5,z52])],[(0,[z0,z206,z2,z3,z4,z5,z6]),(0,[z207,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z208,z3,z4,z5,z6]),(0,[z0,z209,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z210,z5,z6]),(0,[z0,z2,z211,z3,z4,z5,z6]),(0,[z0,z212,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z213,z6]),(0,[z0,z2,z3,z4,z5,z6,z214]),(0,[z0,z2,z3,z4,z5,z6,z215]),(0,[z0,z216,z2,z3,z4,z5,z6]),(1,[z0,z21,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z217,z6]),(0,[z0,z2,z11,z3,z4,z27,z6]),(0,[z0,z2,z3,z4,z5,z6,z218])],[(0,[z155,z156,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z39,z4,z5,z6]),(1,[z219,z0,z2,z3,z5,z101]),(0,[z0,z2,z3,z4,z5,z6,z101])],[(0,[z0,z2,z3,z4,z5,z42,z6]),(0,[z90,z2,z3,z4,z5,z6,z69]),(0,[z0,z2,z3,z4,z4,z5,z6]),(0,[z0,z220,z2,z3,z4,z5,z6]),(0,[z0,z2,z221,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z222])],[(0,[z0,z2,z3,z4,z28,z31,z6]),(0,[z0,z223,z2,z3,z4,z5,z6]),(0,[z219,z0,z2,z3,z5,z6,z101]),(0,[z0,z224,z2,z3,z4,z5,z6])]],
   [[(0,[z0,z118,z2,z3,z4,z5,z6]),(0,[z0,z2,z225,z3,z4,z5,z6]),(0,[z226,z0,z2,z3,z4,z5,z6]),(0,[z0,z47,z3,z100,z4,z5,z6]),(0,[z0,z139,z2,z11,z3,z4,z6]),(0,[z58,z0,z2,z3,z4,z5,z130]),(0,[z219,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z227,z5,z6]),(0,[z0,z2,z3,z228,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z229,z6]),(0,[z230,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z231]),(0,[z0,z2,z232,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z233,z5,z6]),(0,[z0,z234,z2,z3,z4,z5,z6])],[(0,[z235,z0,z2,z3,z4,z5,z6]),(1,[z0,z62,z3,z4,z5,z6]),(0,[z58,z0,z2,z3,z4,z5,z236])],[(0,[z0,z2,z3,z4,z49,z5,z6]),(0,[z0,z237,z2,z3,z4,z5,z6]),(0,[z0,z2,z238,z3,z4,z5,z6]),(0,[z0,z2,z239,z3,z4,z113,z6])],[(0,[z0,z240,z2,z3,z4,z5,z6]),(0,[z0,z2,z189,z3,z4,z5,z6]),(0,[z0,z2,z3,z241,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z89,z6])],[(0,[z242,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z135,z3,z4,z5,z6]),(0,[z243,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z129,z4,z5,z130]),(0,[z0,z2,z3,z244,z4,z5,z6])]],
   [[(0,[z0,z2,z3,z4,z245,z5,z6]),(0,[z0,z2,z3,z246,z4,z5,z6]),(0,[z0,z2,z3,z4,z247,z5,z6]),(0,[z0,z198,z2,z94,z4,z5,z6]),(0,[z0,z2,z3,z4,z248,z5,z6])],[(1,[z0,z2,z3,z249,z5,z6]),(0,[z0,z75,z3,z30,z4,z5,z6]),(0,[z0,z2,z3,z250,z4,z5,z6]),(0,[z0,z2,z3,z251,z4,z5,z6])],[(0,[z0,z2,z252,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z253,z5,z6]),(0,[z0,z2,z254,z3,z4,z5,z6]),(0,[z0,z255,z2,z3,z4,z5,z6])],[(0,[z16,z0,z2,z91,z4,z5,z6]),(0,[z0,z2,z256,z3,z4,z5,z6]),(0,[z257,z0,z2,z3,z4,z5,z6]),(0,[z258,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z228,z5,z6])],[(0,[z0,z259,z2,z3,z4,z5,z6]),(0,[z0,z2,z260,z3,z4,z5,z6])],[(1,[z0,z2,z3,z17,z5,z6]),(0,[z48,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z71,z3,z250,z5,z6]),(0,[z0,z75,z2,z3,z4,z85,z6]),(0,[z0,z2,z3,z4,z5,z6,z261])],[(0,[z0,z2,z3,z4,z262,z5,z6]),(0,[z0,z59,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z263]),(0,[z0,z264,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z3,z4,z5,z6]),(0,[z0,z118,z2,z30,z4,z5,z6]),(0,[z0,z2,z3,z265,z4,z5,z6])]],
   [[(0,[z0,z2,z266,z3,z4,z5,z6]),(1,[z0,z8,z3,z267,z5,z6]),(1,[z0,z2,z3,z268,z5,z6])],[(0,[z48,z2,z3,z4,z49,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z269])],[(0,[z0,z2,z3,z4,z5,z270,z6]),(0,[z0,z2,z3,z4,z9,z5,z6])],[(0,[z0,z271,z2,z3,z4,z5,z6]),(0,[z272,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z273,z3,z4,z5,z6]),(0,[z48,z0,z2,z11,z3,z5,z6]),(0,[z0,z2,z3,z4,z28,z6,z12]),(0,[z0,z2,z3,z4,z5,z69,z12]),(0,[z0,z2,z3,z4,z5,z274,z6]),(0,[z0,z2,z275,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z276,z5,z6]),(0,[z0,z2,z277,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z170,z6])],[(0,[z0,z156,z3,z30,z4,z5,z6]),(0,[z0,z2,z3,z4,z104,z5,z6]),(0,[z0,z2,z278,z3,z4,z5,z6])],[(0,[z0,z279,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z5,z280]),(1,[z0,z2,z3,z4,z281,z6]),(0,[z0,z2,z282,z3,z4,z5,z6])]],
   [[(0,[z156,z2,z195,z3,z4,z5,z6]),(1,[z122,z2,z3,z4,z5,z117]),(0,[z0,z283,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z52]),(0,[z0,z2,z3,z284,z4,z5,z6])],[(0,[z0,z2,z3,z4,z285,z5,z6]),(0,[z0,z2,z3,z286,z4,z5,z6]),(0,[z0,z287,z2,z3,z4,z5,z6]),(0,[z288,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z289,z3,z4,z5,z6]),(0,[z0,z2,z71,z4,z5,z6,z236])],[(0,[z0,z2,z3,z290,z4,z5,z6]),(0,[z291,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z117,z12]),(0,[z0,z2,z3,z4,z5,z6,z292]),(0,[z0,z2,z3,z9,z5,z6,z101]),(0,[z0,z2,z3,z4,z5,z130,z6])],[(0,[z293,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z294,z6]),(0,[z0,z2,z295,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z117,z130]),(0,[z0,z2,z3,z4,z5,z6,z296]),(0,[z0,z297,z198,z3,z4,z5,z6]),(0,[z0,z2,z3,z165,z4,z5,z6]),(0,[z0,z2,z3,z298,z4,z5,z6])],[(0,[z0,z2,z3,z4,z299,z5,z6]),(0,[z0,z2,z3,z4,z300,z5,z6]),(0,[z0,z2,z301,z3,z4,z5,z6])],[(0,[z302,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z303,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z304,z6]),(0,[z0,z2,z3,z4,z5,z305,z6]),(0,[z306,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z80])],[(0,[z0,z307,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z84,z5,z6]),(0,[z0,z2,z3,z4,z113,z28,z6]),(0,[z0,z2,z3,z30,z4,z5,z6]),(0,[z0,z2,z308,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z309,z6])],[(1,[z194,z195,z3,z4,z5,z6]),(0,[z0,z47,z2,z3,z100,z5,z6]),(0,[z0,z2,z3,z310,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z311]),(0,[z312,z0,z2,z3,z4,z6,z12])]],
   [[(0,[z0,z2,z313,z3,z4,z5,z6])],[(0,[z194,z155,z2,z3,z4,z5,z6]),(1,[z0,z2,z4,z5,z6,z314]),(0,[z0,z75,z2,z3,z4,z31,z6])],[(0,[z0,z2,z3,z186,z4,z5,z6]),(0,[z0,z2,z3,z4,z315,z5,z6])],[(0,[z122,z2,z3,z186,z4,z5,z6]),(0,[z158,z122,z2,z3,z4,z5,z6]),(1,[z0,z2,z316,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z317]),(0,[z0,z2,z3,z4,z5,z318,z6]),(0,[z0,z2,z11,z244,z4,z5,z6]),(0,[z0,z2,z3,z165,z5,z89,z6])],[(0,[z0,z2,z319,z3,z4,z5,z6]),(0,[z320,z0,z2,z3,z4,z5,z6]),(0,[z51,z0,z2,z3,z268,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z321]),(0,[z322,z0,z2,z3,z4,z5,z6]),(0,[z58,z0,z21,z3,z4,z5,z6]),(0,[z0,z323,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z89,z6,z324]),(0,[z0,z2,z3,z4,z27,z5,z6])],[(0,[z325,z0,z2,z3,z4,z5,z6]),(0,[z0,z72,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z326]),(0,[z0,z198,z2,z3,z4,z5,z6]),(1,[z0,z2,z239,z4,z31,z6])],[(0,[z0,z2,z3,z4,z5,z327,z6])],[(1,[z155,z156,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z328,z5,z6]),(0,[z0,z38,z198,z2,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z329,z6]),(1,[z330,z2,z3,z4,z5,z6])]],
   [[(0,[z331,z0,z2,z3,z4,z5,z6]),(0,[z332,z0,z2,z3,z4,z5,z6]),(0,[z333,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z110,z4,z5,z6]),(0,[z0,z75,z2,z11,z3,z4,z6]),(0,[z0,z2,z3,z4,z5,z334,z6]),(0,[z0,z2,z3,z335,z4,z5,z6])],[(0,[z194,z0,z2,z3,z4,z5,z6]),(0,[z90,z0,z2,z3,z4,z5,z6]),(0,[z336,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z30,z4,z5,z6,z236]),(0,[z337,z0,z2,z3,z4,z5,z6])],[(0,[z338,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z339,z3,z4,z5,z6]),(0,[z340,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z341,z5,z6]),(0,[z0,z2,z129,z3,z4,z5,z236])],[(0,[z0,z342,z2,z3,z4,z5,z6]),(0,[z0,z2,z11,z3,z4,z5,z6])],[(0,[z0,z3,z30,z4,z85,z5,z6]),(0,[z0,z2,z3,z4,z5,z343,z6])],[(0,[z344,z0,z2,z3,z4,z5,z6]),(0,[z155,z2,z3,z4,z5,z6,z69]),(0,[z0,z2,z3,z345,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z346,z6]),(0,[z347,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z348])],[(0,[z0,z2,z349,z3,z4,z5,z6]),(0,[z0,z139,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z350,z6]),(1,[z312,z0,z2,z3,z4,z12])],[(0,[z0,z2,z3,z4,z5,z151,z6]),(0,[z0,z2,z3,z4,z268,z5,z6]),(1,[z0,z2,z3,z4,z116,z6])]],
   [[(1,[z0,z2,z3,z351,z4,z6]),(0,[z0,z3,z30,z100,z4,z5,z6]),(1,[z322,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z352,z6])],[(0,[z0,z353,z2,z3,z4,z5,z6]),(0,[z354,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z157,z5,z6])],[(0,[z355,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z356,z3,z4,z5,z6])],[(0,[z0,z198,z2,z30,z4,z5,z6]),(0,[z0,z8,z2,z3,z267,z5,z6]),(0,[z0,z2,z3,z4,z85,z6,z12])],[(0,[z357,z0,z2,z3,z4,z5,z6]),(0,[z0,z75,z2,z120,z4,z5,z6]),(0,[z0,z2,z358,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z359,z5,z6]),(0,[z2,z3,z4,z5,z28,z6,z69]),(1,[z0,z2,z3,z4,z27,z170])],[(1,[z0,z2,z3,z4,z188,z6]),(0,[z70,z0,z8,z3,z4,z5,z6]),(0,[z360,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z95,z5,z6,z101]),(0,[z0,z2,z3,z4,z5,z6,z361]),(1,[z2,z3,z4,z5,z6,z324])]],
   [[(0,[z0,z2,z3,z4,z5,z362,z6]),(0,[z90,z0,z2,z30,z4,z5,z6]),(0,[z0,z2,z3,z95,z4,z5,z6]),(0,[z0,z2,z3,z363,z4,z5,z6])],[(0,[z158,z0,z2,z3,z4,z84,z6]),(0,[z0,z2,z3,z364,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z365,z6]),(0,[z0,z2,z3,z366,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z367,z6])],[(0,[z48,z109,z2,z3,z4,z5,z6]),(1,[z158,z2,z3,z4,z84,z6]),(1,[z0,z2,z3,z4,z201,z6]),(0,[z0,z2,z3,z4,z368,z5,z6]),(0,[z0,z2,z3,z4,z267,z5,z6]),(0,[z0,z2,z3,z39,z4,z113,z6]),(0,[z0,z369,z2,z3,z4,z5,z6])],[(0,[z90,z0,z2,z186,z4,z5,z6]),(0,[z0,z2,z370,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z371,z6]),(0,[z0,z2,z3,z4,z5,z6,z372])],[(0,[z0,z373,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z374,z5,z6])],[(0,[z0,z2,z3,z4,z375,z5,z6])],[(0,[z0,z2,z3,z95,z49,z5,z6]),(0,[z0,z2,z11,z3,z9,z5,z6]),(0,[z0,z2,z3,z376,z4,z5,z6]),(0,[z0,z2,z3,z4,z377,z5,z6])]],
   [[(0,[z0,z2,z378,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z379,z6]),(0,[z0,z2,z3,z4,z281,z5,z6]),(0,[z0,z2,z3,z380,z4,z5,z6]),(0,[z312,z381,z2,z3,z4,z5,z6])],[(0,[z48,z0,z2,z3,z157,z5,z6]),(0,[z0,z2,z3,z4,z5,z382,z6]),(0,[z383,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z19,z4,z5,z6])],[(0,[z0,z2,z3,z4,z384,z5,z6]),(0,[z385,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z386,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z387,z6]),(0,[z0,z2,z3,z4,z388,z5,z6])],[(0,[z0,z2,z3,z46,z4,z5,z6]),(0,[z0,z389,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z390]),(0,[z0,z2,z3,z4,z5,z391,z6]),(0,[z70,z0,z2,z3,z4,z5,z6]),(1,[z0,z75,z3,z4,z76,z6]),(0,[z0,z2,z3,z4,z5,z392,z6]),(0,[z0,z2,z3,z4,z5,z393,z6])],[(0,[z0,z2,z3,z394,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z6]),(0,[z0,z395,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z396,z6])],[(0,[z0,z2,z3,z4,z128,z5,z6]),(0,[z0,z2,z397,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z398,z6]),(0,[z0,z2,z3,z4,z5,z6,z399]),(0,[z0,z198,z2,z3,z4,z300,z6])],[(0,[z0,z400,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z28,z6]),(0,[z0,z8,z2,z159,z4,z5,z6]),(0,[z0,z8,z2,z3,z100,z5,z6]),(0,[z0,z2,z3,z4,z5,z401,z6]),(0,[z0,z2,z3,z4,z5,z6,z402]),(1,[z337,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z403,z4,z5,z6])],[(0,[z0,z2,z3,z404,z4,z5,z6]),(1,[z16,z2,z186,z4,z5,z6]),(0,[z0,z2,z405,z3,z4,z5,z6]),(0,[z122,z2,z3,z4,z5,z28,z6]),(1,[z0,z2,z3,z250,z5,z6])]],
   [[(1,[z0,z118,z30,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z406,z6]),(0,[z0,z2,z407,z3,z4,z5,z6])],[(0,[z194,z0,z195,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z408]),(0,[z43,z0,z2,z3,z4,z5,z126]),(0,[z0,z2,z11,z3,z5,z83,z6]),(0,[z0,z2,z3,z4,z5,z6,z409])],[(0,[z0,z2,z3,z4,z410,z5,z6]),(0,[z0,z139,z2,z3,z39,z4,z6]),(0,[z0,z198,z62,z3,z4,z5,z6]),(1,[z0,z297,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z411,z5,z6]),(0,[z0,z38,z2,z4,z113,z5,z6]),(0,[z0,z2,z3,z4,z412,z5,z6]),(1,[z58,z0,z2,z4,z5,z236]),(0,[z0,z2,z3,z4,z413,z5,z6]),(0,[z312,z0,z2,z3,z4,z5,z170])],[(0,[z414,z0,z2,z3,z4,z5,z6]),(0,[z0,z415,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z39,z157,z6]),(0,[z330,z312,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z416])],[(0,[z2,z91,z3,z186,z4,z5,z6]),(0,[z417,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z161,z5,z6])],[(0,[z0,z2,z3,z4,z5,z418,z6]),(0,[z419,z0,z2,z3,z4,z5,z6]),(0,[z0,z198,z2,z95,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z420]),(0,[z0,z2,z3,z4,z421,z5,z6])],[(0,[z422,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z423,z5,z6]),(0,[z0,z2,z71,z3,z4,z36,z6]),(0,[z0,z2,z3,z9,z157,z5,z6])]],
   [[(0,[z2,z3,z110,z4,z49,z5,z6]),(0,[z0,z47,z2,z3,z267,z5,z6]),(0,[z0,z2,z3,z100,z165,z5,z6]),(0,[z0,z2,z3,z4,z170,z6,z12])],[(0,[z0,z2,z424,z3,z4,z5,z6]),(0,[z122,z0,z2,z3,z4,z5,z69]),(0,[z0,z2,z3,z73,z4,z267,z6]),(0,[z0,z2,z3,z4,z425,z5,z6]),(0,[z0,z2,z3,z4,z5,z426,z6])],[(0,[z0,z2,z3,z4,z5,z6,z427]),(0,[z70,z0,z2,z30,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z428,z6]),(0,[z0,z2,z429,z3,z4,z5,z6]),(0,[z0,z2,z430,z3,z4,z5,z6]),(0,[z431,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z432,z5,z6]),(0,[z312,z0,z2,z3,z4,z27,z6])],[(0,[z433,z0,z2,z3,z4,z5,z6]),(0,[z0,z434,z2,z3,z4,z5,z6]),(0,[z184,z0,z2,z3,z4,z5,z69]),(0,[z435,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z436,z5,z6]),(0,[z0,z2,z94,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z437]),(0,[z0,z2,z438,z3,z4,z5,z6])],[(0,[z0,z2,z3,z439,z4,z5,z6]),(0,[z0,z440,z2,z3,z4,z5,z6]),(0,[z0,z75,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z113,z6,z12]),(0,[z0,z2,z3,z4,z5,z441,z6])],[(0,[z0,z2,z3,z442,z4,z5,z6]),(1,[z443,z0,z2,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z444,z6]),(0,[z445,z0,z2,z3,z4,z5,z6])]],
   [[(0,[z155,z0,z2,z3,z4,z5,z6]),(0,[z446,z0,z2,z3,z4,z5,z6]),(0,[z0,z447,z2,z3,z4,z5,z6]),(0,[z16,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z266,z3,z5,z28,z6]),(0,[z0,z448,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z165,z267,z5,z6]),(0,[z0,z2,z94,z4,z9,z5,z6]),(0,[z449,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z450]),(0,[z451,z0,z2,z3,z4,z5,z6]),(0,[z452,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z267,z5,z6,z101]),(0,[z0,z2,z3,z142,z4,z5,z6]),(0,[z0,z3,z4,z85,z5,z76,z6]),(0,[z0,z453,z2,z3,z4,z5,z6]),(0,[z58,z322,z2,z3,z4,z5,z6]),(0,[z454,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z324])],[(0,[z455,z0,z2,z3,z4,z5,z6]),(1,[z381,z2,z3,z4,z5,z6])],[(0,[z0,z456,z2,z3,z4,z5,z6]),(0,[z43,z0,z2,z3,z4,z28,z6]),(0,[z0,z2,z3,z4,z5,z6,z457]),(0,[z0,z2,z458,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z459])],[(0,[z0,z2,z3,z4,z5,z69,z236]),(0,[z0,z2,z3,z4,z5,z460,z6]),(0,[z0,z2,z3,z39,z4,z157,z6])],[(0,[z461,z0,z2,z3,z4,z5,z6]),(0,[z462,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z463,z3,z4,z5,z6]),(0,[z16,z0,z206,z3,z4,z5,z6]),(0,[z464,z0,z2,z3,z4,z5,z6]),(0,[z158,z0,z2,z11,z3,z4,z6]),(0,[z51,z0,z3,z4,z5,z6,z52]),(0,[z0,z2,z3,z4,z5,z6,z465]),(0,[z0,z2,z3,z466,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z467,z6]),(0,[z0,z2,z3,z4,z5,z468,z6])],[(0,[z16,z90,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z159,z4,z5,z6]),(0,[z0,z469,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z27,z5,z12])],[(1,[z0,z2,z470,z3,z4,z6]),(0,[z0,z471,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z472,z4,z5,z6]),(0,[z473,z0,z2,z3,z4,z5,z6])]],
   [[(0,[z158,z2,z3,z4,z5,z6,z69]),(0,[z474,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z475,z3,z4,z5,z6]),(0,[z184,z0,z2,z3,z4,z201,z6]),(0,[z0,z2,z3,z4,z5,z6,z476]),(1,[z0,z453,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z477,z6])],[(0,[z48,z122,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z117,z236]),(0,[z0,z2,z71,z3,z4,z5,z6]),(0,[z51,z0,z2,z3,z228,z5,z6])],[(0,[z70,z0,z195,z3,z4,z5,z6]),(0,[z16,z0,z2,z4,z5,z130,z6]),(0,[z478,z0,z2,z3,z4,z5,z6]),(0,[z479,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z480]),(0,[z481,z0,z2,z3,z4,z5,z6]),(0,[z2,z3,z110,z4,z5,z6,z69]),(0,[z158,z0,z2,z3,z39,z4,z6]),(0,[z482,z0,z2,z3,z4,z5,z6]),(0,[z0,z483,z2,z3,z4,z5,z6]),(0,[z0,z2,z239,z4,z5,z31,z6])],[(0,[z0,z2,z3,z4,z484,z5,z6]),(0,[z0,z2,z3,z351,z4,z49,z6]),(0,[z109,z0,z2,z3,z110,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z485]),(0,[z0,z2,z71,z4,z9,z5,z6]),(1,[z0,z2,z3,z73,z4,z6]),(0,[z0,z2,z3,z4,z76,z6,z12]),(0,[z0,z2,z3,z486,z4,z5,z6])],[(0,[z2,z195,z3,z4,z5,z6,z69]),(1,[z0,z358,z3,z4,z5,z6]),(0,[z0,z38,z453,z3,z4,z5,z6]),(0,[z0,z2,z11,z3,z4,z83,z6])],[(0,[z16,z0,z2,z30,z4,z5,z6]),(0,[z0,z2,z3,z4,z113,z84,z6]),(0,[z0,z2,z3,z487,z4,z5,z6]),(0,[z0,z8,z3,z30,z4,z5,z6]),(0,[z488,z0,z2,z3,z4,z5,z6]),(0,[z489,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z490])]],
   [[(0,[z0,z491,z2,z3,z4,z5,z6]),(0,[z0,z492,z2,z3,z4,z5,z6]),(0,[z22,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z130,z69]),(0,[z0,z71,z3,z30,z4,z5,z6]),(0,[z0,z2,z94,z3,z9,z5,z6]),(0,[z0,z2,z3,z4,z5,z31,z6]),(0,[z0,z2,z11,z3,z4,z113,z6])],[(0,[z0,z2,z3,z4,z493,z5,z6]),(0,[z0,z3,z30,z4,z5,z6,z52]),(0,[z0,z2,z494,z3,z4,z5,z6]),(0,[z0,z495,z2,z3,z4,z5,z6])],[(0,[z0,z2,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z249,z5,z6]),(1,[z43,z2,z3,z4,z28,z6])],[(0,[z0,z2,z3,z496,z4,z5,z6]),(0,[z0,z139,z2,z3,z4,z113,z6]),(0,[z0,z2,z3,z4,z497,z5,z6]),(0,[z0,z2,z3,z95,z157,z5,z6]),(0,[z0,z38,z2,z3,z4,z31,z6]),(0,[z0,z2,z3,z4,z5,z6,z498]),(0,[z0,z499,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z500,z6])],[(0,[z0,z2,z501,z3,z4,z5,z6]),(0,[z0,z2,z3,z502,z4,z5,z6]),(0,[z0,z2,z3,z4,z503,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z504]),(0,[z22,z2,z3,z4,z5,z89,z6])],[(0,[z0,z2,z3,z4,z505,z5,z6]),(0,[z0,z506,z2,z3,z4,z5,z6]),(0,[z51,z0,z2,z3,z4,z281,z6]),(1,[z0,z2,z3,z4,z202,z6]),(1,[z0,z2,z3,z507,z5,z6])],[(0,[z0,z2,z3,z508,z4,z5,z6]),(0,[z70,z0,z3,z4,z85,z5,z6]),(0,[z0,z2,z3,z4,z509,z5,z6])]],
   [[(0,[z0,z118,z3,z30,z4,z5,z6]),(0,[z0,z2,z510,z3,z4,z5,z6])],[(0,[z0,z2,z511,z3,z4,z5,z6]),(0,[z43,z0,z2,z3,z4,z5,z280]),(0,[z0,z297,z2,z3,z4,z5,z6])],[(0,[z0,z75,z2,z3,z39,z4,z6]),(0,[z0,z2,z3,z4,z512,z5,z6]),(0,[z219,z0,z2,z3,z165,z5,z6])],[(0,[z0,z513,z2,z3,z4,z5,z6]),(0,[z58,z16,z0,z2,z4,z5,z6]),(0,[z70,z0,z3,z100,z4,z5,z6]),(0,[z0,z2,z3,z4,z27,z76,z6]),(0,[z0,z2,z3,z4,z514,z5,z6])],[(0,[z109,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z515,z4,z5,z6]),(0,[z0,z2,z3,z516,z4,z5,z6]),(0,[z0,z517,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z39,z157,z5,z6])],[(0,[z0,z2,z30,z4,z9,z5,z6]),(0,[z0,z2,z3,z4,z5,z518,z6])],[(0,[z0,z2,z3,z519,z4,z5,z6]),(0,[z0,z2,z3,z4,z520,z5,z6]),(0,[z0,z2,z3,z4,z5,z521,z6]),(0,[z0,z522,z2,z3,z4,z5,z6])],[(1,[z0,z2,z463,z4,z5,z6]),(1,[z0,z2,z266,z3,z5,z6]),(0,[z0,z2,z3,z4,z5,z523,z6]),(0,[z0,z2,z3,z4,z5,z6,z524]),(0,[z0,z2,z525,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z526,z6]),(0,[z0,z38,z2,z71,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z527])]],
   [[(0,[z155,z0,z195,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z528,z6]),(0,[z0,z2,z470,z3,z4,z49,z6])],[(0,[z0,z2,z91,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z57,z6,z52])],[(0,[z51,z0,z2,z316,z4,z5,z6]),(0,[z0,z529,z2,z3,z4,z5,z6])],[(0,[z109,z0,z2,z3,z49,z5,z6]),(0,[z0,z530,z2,z3,z4,z5,z6]),(1,[z0,z2,z120,z4,z5,z6]),(0,[z0,z2,z3,z4,z531,z5,z6]),(0,[z0,z2,z3,z5,z89,z6,z101])],[(0,[z0,z2,z3,z532,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z533,z6]),(0,[z0,z2,z3,z4,z5,z534,z6]),(0,[z0,z2,z3,z4,z535,z5,z6]),(0,[z0,z536,z2,z3,z4,z5,z6]),(0,[z58,z0,z2,z4,z5,z6,z236]),(0,[z0,z381,z2,z3,z4,z5,z6])],[(0,[z0,z139,z2,z3,z4,z76,z6])],[(0,[z0,z2,z3,z4,z5,z6,z68]),(0,[z43,z2,z3,z4,z5,z28,z6]),(0,[z0,z8,z2,z3,z95,z5,z6]),(0,[z0,z2,z3,z4,z5,z537,z6]),(0,[z0,z2,z3,z4,z538,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z12])],[(0,[z539,z0,z2,z3,z4,z5,z6]),(0,[z0,z198,z2,z4,z5,z31,z6]),(0,[z0,z540,z2,z3,z4,z5,z6]),(0,[z541,z0,z2,z3,z4,z5,z6])]],
   [[(0,[z0,z2,z3,z4,z5,z542,z6]),(0,[z0,z2,z3,z4,z5,z543,z6]),(0,[z0,z2,z3,z544,z4,z5,z6])],[(0,[z545,z0,z2,z3,z4,z5,z6]),(0,[z0,z156,z2,z463,z4,z5,z6]),(0,[z546,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z547]),(0,[z0,z2,z3,z4,z548,z5,z6])],[(0,[z549,z0,z2,z3,z4,z5,z6]),(0,[z122,z184,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z550,z5,z6]),(0,[z551,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z71,z3,z4,z299,z6]),(0,[z0,z2,z3,z4,z5,z552,z6]),(0,[z312,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z95,z4,z9,z5,z6]),(0,[z553,z0,z2,z3,z4,z5,z6]),(0,[z0,z554,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z555,z5,z6]),(0,[z0,z2,z3,z556,z4,z5,z6]),(0,[z0,z2,z3,z557,z4,z5,z6]),(0,[z0,z2,z3,z558,z4,z5,z6])],[(0,[z43,z0,z2,z11,z3,z4,z6]),(0,[z0,z2,z3,z559,z4,z5,z6]),(0,[z0,z2,z3,z39,z4,z31,z6]),(1,[z0,z2,z3,z4,z560,z6])],[(0,[z0,z2,z3,z4,z5,z561,z6]),(0,[z0,z139,z75,z3,z4,z5,z6]),(0,[z51,z0,z72,z3,z4,z5,z6])],[(0,[z443,z0,z2,z4,z5,z6,z69]),(0,[z562,z0,z2,z3,z4,z5,z6])]],
   [[(0,[z0,z2,z3,z563,z4,z5,z6])],[(1,[z0,z2,z3,z4,z36,z6]),(1,[z0,z2,z3,z4,z37,z6])],[(0,[z0,z2,z3,z4,z5,z6,z564]),(0,[z0,z2,z429,z3,z4,z267,z6]),(0,[z0,z2,z3,z4,z113,z27,z6]),(0,[z0,z2,z11,z3,z4,z157,z6]),(0,[z0,z565,z2,z3,z4,z5,z6])],[(0,[z0,z2,z195,z3,z4,z5,z6]),(0,[z16,z0,z2,z3,z4,z5,z42]),(0,[z158,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z166,z5,z6]),(0,[z0,z2,z566,z3,z4,z5,z6])],[(0,[z122,z2,z195,z3,z4,z5,z6]),(0,[z567,z0,z2,z3,z4,z5,z6]),(0,[z568,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z569,z5,z6]),(0,[z0,z72,z3,z4,z5,z57,z6])],[(1,[z48,z2,z3,z49,z5,z6]),(1,[z0,z2,z135,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z570])],[(0,[z0,z571,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z572,z5,z6])],[(0,[z0,z2,z573,z3,z4,z5,z6]),(0,[z574,z0,z2,z3,z4,z5,z6])]],
   [[(0,[z0,z2,z3,z4,z5,z6,z575]),(0,[z0,z2,z3,z507,z4,z5,z6])],[(0,[z0,z2,z3,z576,z4,z5,z6]),(0,[z0,z3,z100,z4,z267,z5,z6]),(0,[z0,z2,z577,z3,z4,z5,z6]),(0,[z0,z2,z3,z165,z4,z5,z101])],[(0,[z578,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z71,z129,z4,z5,z6]),(0,[z0,z2,z239,z3,z4,z31,z6]),(0,[z0,z2,z3,z4,z560,z5,z6])],[(0,[z70,z0,z156,z3,z4,z5,z6]),(0,[z0,z118,z2,z71,z4,z5,z6]),(0,[z579,z0,z2,z3,z4,z5,z6]),(0,[z580,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z94,z9,z5,z6]),(1,[z0,z2,z581,z4,z5,z6])],[(0,[z582,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z314]),(0,[z0,z75,z2,z3,z4,z113,z6]),(1,[z0,z323,z3,z4,z5,z6]),(1,[z0,z2,z244,z4,z5,z6]),(0,[z0,z2,z3,z4,z583,z5,z6])],[(0,[z0,z2,z3,z584,z4,z5,z6]),(0,[z0,z2,z3,z4,z585,z5,z6]),(0,[z0,z2,z3,z4,z586,z5,z6])],[(0,[z0,z2,z3,z4,z5,z587,z6]),(0,[z0,z2,z3,z351,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z588,z6]),(0,[z0,z2,z3,z316,z4,z5,z6]),(0,[z0,z2,z581,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z589])],[(0,[z0,z156,z2,z46,z4,z5,z6]),(0,[z184,z2,z3,z4,z5,z6,z69]),(0,[z0,z2,z590,z3,z4,z5,z6]),(0,[z0,z2,z3,z591,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z592,z6]),(0,[z58,z0,z2,z3,z507,z5,z6])]],
   [[(0,[z0,z2,z3,z4,z593,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z594]),(0,[z0,z2,z595,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z596,z6]),(0,[z0,z2,z3,z597,z4,z5,z6]),(0,[z0,z2,z3,z157,z5,z83,z6])],[(0,[z598,z0,z2,z3,z4,z5,z6]),(0,[z599,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z600,z6])],[(0,[z601,z0,z2,z3,z4,z5,z6]),(0,[z0,z47,z2,z3,z95,z5,z6]),(0,[z602,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z603,z6]),(0,[z0,z2,z3,z39,z4,z6,z12])],[(0,[z70,z0,z75,z3,z4,z5,z6]),(0,[z0,z2,z3,z100,z4,z5,z6]),(0,[z0,z604,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z27,z170,z6])],[(1,[z0,z2,z3,z4,z5,z6]),(0,[z0,z605,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z49,z9,z5,z6]),(0,[z0,z2,z3,z4,z606,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z607])],[(0,[z0,z139,z3,z4,z85,z5,z6]),(0,[z51,z337,z2,z3,z4,z5,z6]),(0,[z51,z0,z2,z3,z4,z37,z6]),(0,[z608,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z609])],[(0,[z0,z2,z3,z4,z610,z5,z6]),(0,[z0,z2,z3,z4,z5,z611,z6]),(0,[z0,z2,z3,z166,z5,z28,z6])],[(1,[z0,z2,z3,z4,z133,z6]),(0,[z0,z612,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z613,z6])]],
   [[(0,[z0,z75,z2,z142,z4,z5,z6]),(0,[z0,z2,z3,z4,z31,z6,z12])],[(1,[z0,z206,z3,z4,z5,z6]),(0,[z0,z2,z3,z17,z4,z5,z6]),(0,[z219,z0,z2,z3,z4,z5,z89])],[(0,[z0,z2,z3,z4,z614,z5,z6]),(0,[z0,z38,z2,z239,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z615,z6]),(0,[z0,z2,z3,z4,z5,z616,z6]),(0,[z122,z0,z2,z3,z4,z5,z117]),(0,[z0,z2,z3,z4,z5,z6,z617]),(0,[z0,z2,z618,z3,z4,z5,z6])],[(0,[z43,z0,z2,z3,z4,z84,z6]),(0,[z0,z2,z3,z4,z5,z6,z619]),(0,[z0,z38,z2,z4,z9,z5,z6]),(0,[z0,z2,z3,z4,z620,z5,z6])],[(0,[z0,z2,z3,z4,z621,z5,z6]),(0,[z622,z0,z2,z3,z4,z5,z6]),(0,[z0,z75,z2,z3,z4,z76,z6])],[(0,[z0,z156,z2,z3,z4,z5,z6]),(0,[z184,z0,z2,z3,z4,z5,z117]),(0,[z51,z0,z2,z3,z4,z5,z57]),(0,[z0,z2,z3,z623,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z624,z6]),(0,[z0,z2,z3,z4,z5,z625,z6]),(0,[z0,z2,z3,z4,z5,z170,z69]),(0,[z0,z2,z626,z3,z4,z5,z6])]],
   [[(0,[z627,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z628,z3,z4,z5,z6]),(0,[z0,z2,z129,z3,z4,z5,z6])],[(0,[z0,z2,z3,z629,z4,z5,z6]),(0,[z630,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z470,z3,z4,z5,z6]),(0,[z0,z2,z3,z631,z4,z5,z6]),(0,[z0,z2,z3,z4,z632,z5,z6]),(0,[z0,z2,z71,z3,z128,z5,z6]),(1,[z0,z198,z2,z95,z5,z6]),(1,[z59,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z95,z165,z5,z6])],[(0,[z633,z0,z2,z3,z4,z5,z6]),(0,[z0,z634,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z85,z27,z6]),(1,[z0,z38,z2,z4,z113,z6]),(0,[z0,z2,z635,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z636,z6]),(0,[z0,z2,z3,z4,z637,z5,z6]),(0,[z0,z2,z3,z4,z638,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z639]),(0,[z0,z198,z2,z3,z95,z5,z6]),(0,[z0,z2,z640,z3,z4,z5,z6])],[(0,[z70,z0,z3,z4,z5,z6,z52]),(0,[z0,z2,z3,z4,z5,z6,z641])],[(0,[z642,z0,z2,z3,z4,z5,z6]),(0,[z16,z0,z2,z186,z4,z5,z6]),(1,[z0,z2,z429,z3,z4,z6]),(0,[z0,z2,z4,z9,z5,z31,z6]),(0,[z0,z38,z358,z3,z4,z5,z6]),(0,[z58,z0,z2,z3,z4,z560,z6]),(0,[z0,z2,z3,z4,z5,z643,z6])],[(0,[z0,z2,z3,z4,z5,z644,z6]),(0,[z0,z2,z3,z645,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z646]),(1,[z0,z2,z3,z4,z78,z6]),(1,[z0,z2,z3,z165,z5,z89])]],
   [[(0,[z647,z0,z2,z3,z4,z5,z6]),(0,[z16,z0,z189,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z648]),(0,[z0,z2,z649,z3,z4,z5,z6]),(0,[z0,z2,z4,z113,z5,z31,z6])],[(0,[z0,z2,z3,z4,z5,z6,z650]),(0,[z0,z2,z3,z4,z651,z5,z6]),(0,[z0,z652,z2,z3,z4,z5,z6]),(0,[z0,z2,z653,z3,z4,z5,z6])],[(0,[z654,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z655,z6])],[(0,[z0,z2,z656,z3,z4,z5,z6]),(0,[z657,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z202,z6]),(0,[z0,z2,z129,z4,z5,z130,z6]),(0,[z0,z658,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z659]),(0,[z0,z8,z2,z3,z4,z5,z6]),(0,[z0,z2,z25,z3,z4,z5,z6]),(1,[z0,z2,z3,z104,z5,z6]),(0,[z0,z2,z4,z5,z130,z6,z236]),(0,[z0,z2,z581,z11,z4,z5,z6])],[(1,[z70,z0,z71,z4,z5,z6]),(0,[z0,z2,z3,z660,z4,z5,z6])],[(0,[z0,z2,z3,z4,z661,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z662])],[(0,[z0,z2,z663,z3,z4,z5,z6]),(0,[z122,z155,z2,z3,z4,z5,z6]),(0,[z0,z2,z129,z30,z4,z5,z6]),(0,[z0,z2,z3,z664,z4,z5,z6])]],
   [[(0,[z0,z198,z2,z71,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z665])],[(0,[z0,z666,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z667,z5,z6]),(0,[z0,z668,z2,z3,z4,z5,z6]),(0,[z0,z669,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z113,z5,z6]),(0,[z219,z0,z2,z3,z4,z5,z101]),(0,[z0,z2,z670,z3,z4,z5,z6])],[(0,[z671,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z116,z5,z6])],[(0,[z0,z2,z3,z4,z5,z672,z6]),(0,[z0,z195,z3,z30,z4,z5,z6]),(0,[z48,z0,z2,z3,z110,z5,z6]),(0,[z0,z2,z3,z4,z84,z6,z12])],[(0,[z194,z0,z156,z3,z4,z5,z6]),(0,[z16,z2,z3,z186,z4,z5,z6]),(0,[z90,z0,z2,z71,z4,z5,z6]),(1,[z0,z2,z3,z4,z299,z6]),(0,[z0,z2,z71,z4,z5,z31,z6]),(1,[z0,z2,z3,z4,z300,z6]),(0,[z0,z2,z3,z165,z4,z5,z89]),(0,[z312,z0,z2,z3,z4,z5,z12])],[(0,[z0,z2,z3,z4,z673,z5,z6]),(0,[z0,z674,z2,z3,z4,z5,z6]),(0,[z0,z2,z675,z3,z4,z5,z6]),(0,[z0,z2,z3,z676,z4,z5,z6]),(0,[z0,z677,z2,z3,z4,z5,z6]),(0,[z58,z0,z323,z3,z4,z5,z6]),(0,[z678,z0,z2,z3,z4,z5,z6])],[(0,[z0,z0,z2,z3,z4,z5,z6]),(0,[z679,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z188,z5,z6]),(0,[z680,z0,z2,z3,z4,z5,z6]),(0,[z109,z0,z2,z11,z3,z5,z6]),(0,[z0,z681,z2,z3,z4,z5,z6]),(0,[z330,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z280]),(0,[z0,z682,z2,z3,z4,z5,z6]),(0,[z122,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z683,z6]),(0,[z0,z2,z3,z4,z5,z684,z6]),(0,[z0,z2,z11,z3,z39,z5,z6])]],
   [[(0,[z443,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z685,z3,z4,z5,z6])],[(0,[z0,z686,z2,z3,z4,z5,z6]),(0,[z0,z687,z2,z3,z4,z5,z6])],[(0,[z184,z0,z2,z3,z4,z5,z6]),(0,[z688,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z689,z3,z4,z5,z6])],[(0,[z690,z0,z2,z3,z4,z5,z6]),(0,[z691,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z692,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z693]),(0,[z0,z694,z2,z3,z4,z5,z6]),(0,[z695,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z696,z5,z6]),(0,[z697,z0,z2,z3,z4,z5,z6])],[(0,[z698,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z699,z6]),(0,[z700,z0,z2,z3,z4,z5,z6]),(0,[z701,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z702])],[(0,[z16,z0,z2,z3,z249,z5,z6]),(0,[z122,z90,z2,z3,z4,z5,z6]),(0,[z0,z703,z2,z3,z4,z5,z6]),(0,[z184,z0,z2,z3,z4,z133,z6]),(0,[z58,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z4,z5,z6,z314,z69]),(0,[z0,z2,z3,z4,z5,z6,z236]),(0,[z0,z2,z3,z4,z704,z5,z6])],[(0,[z705,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z706,z4,z5,z6]),(0,[z0,z8,z3,z4,z267,z5,z6]),(0,[z51,z0,z2,z3,z4,z5,z52]),(0,[z0,z2,z239,z3,z4,z5,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z2,z3,z4,z5,z707]),(0,[z0,z2,z3,z4,z708,z6]),(0,[z0,z2,z3,z4,z709,z6]),(0,[z59,z323,z3,z4,z5,z6]),(0,[z0,z21,z3,z4,z560,z6])],[(0,[z0,z2,z463,z710,z5,z6]),(0,[z70,z0,z71,z4,z36,z6]),(0,[z0,z2,z429,z711,z4,z6])],[(0,[z0,z2,z3,z4,z712,z6]),(0,[z2,z3,z4,z5,z713,z69]),(0,[z0,z75,z3,z4,z436,z6])],[(0,[z0,z2,z3,z249,z188,z6]),(0,[z2,z714,z186,z4,z5,z6]),(0,[z0,z2,z715,z4,z5,z6]),(0,[z0,z2,z11,z3,z410,z6])],[(0,[z0,z2,z3,z4,z716,z6]),(0,[z0,z2,z4,z5,z717,z6])],[(0,[z0,z2,z11,z3,z4,z280]),(0,[z0,z2,z718,z4,z5,z6]),(0,[z0,z719,z3,z4,z5,z6])],[(0,[z0,z353,z30,z4,z5,z6]),(0,[z0,z2,z581,z9,z5,z6]),(0,[z0,z323,z3,z4,z78,z6])],[(0,[z0,z2,z3,z17,z188,z6]),(0,[z0,z720,z3,z4,z5,z6]),(0,[z0,z139,z3,z4,z85,z6]),(0,[z0,z2,z3,z161,z5,z6])]],
   [[(0,[z59,z2,z3,z4,z5,z6]),(0,[z0,z198,z2,z95,z5,z6])],[],[(0,[z0,z2,z721,z4,z5,z6])],[(0,[z443,z59,z2,z4,z5,z6]),(0,[z722,z0,z2,z3,z4,z5]),(0,[z0,z106,z2,z95,z5,z6])],[(0,[z0,z723,z2,z4,z5,z6]),(0,[z0,z2,z3,z724,z5,z6])],[(0,[z725,z2,z3,z4,z5,z6]),(0,[z0,z2,z429,z3,z4,z6])],[(0,[z0,z2,z726,z3,z4,z6]),(0,[z0,z2,z3,z727,z5,z6]),(0,[z0,z2,z3,z4,z728,z6]),(0,[z546,z2,z3,z4,z5,z69]),(0,[z0,z3,z4,z729,z5,z6]),(0,[z0,z2,z3,z4,z78,z6]),(0,[z0,z2,z3,z165,z5,z89])],[(0,[z0,z206,z30,z4,z5,z6]),(0,[z0,z2,z730,z4,z5,z6]),(0,[z43,z2,z112,z3,z4,z6]),(0,[z40,z2,z3,z4,z84,z6]),(0,[z0,z510,z30,z4,z5,z6]),(0,[z0,z2,z11,z3,z176,z6]),(0,[z0,z2,z731,z4,z5,z6])]],
   [[(0,[z0,z2,z3,z732,z5,z6]),(0,[z156,z733,z3,z4,z5,z6]),(0,[z0,z453,z71,z4,z5,z6]),(0,[z0,z2,z11,z3,z411,z6]),(0,[z330,z312,z2,z3,z4,z12])],[(1,[z733,z3,z4,z5,z6]),(0,[z48,z0,z2,z470,z3,z6]),(0,[z48,z2,z3,z341,z5,z6]),(0,[z0,z2,z129,z4,z5,z145])],[(0,[z0,z2,z3,z734,z5,z6]),(0,[z0,z2,z3,z4,z5,z735]),(0,[z2,z3,z714,z4,z5,z6]),(0,[z109,z0,z2,z470,z3,z6]),(0,[z0,z3,z4,z5,z6,z736]),(0,[z0,z2,z3,z4,z5,z737]),(0,[z657,z2,z3,z4,z28,z6]),(0,[z0,z738,z3,z4,z5,z6]),(0,[z0,z8,z30,z9,z5,z6]),(0,[z0,z2,z739,z9,z5,z6]),(0,[z0,z2,z581,z4,z300,z6]),(0,[z0,z2,z689,z4,z31,z6]),(0,[z0,z2,z3,z4,z5,z740])],[(0,[z0,z2,z3,z4,z741,z6]),(0,[z0,z2,z3,z4,z27,z343]),(0,[z0,z2,z742,z4,z5,z6]),(0,[z381,z2,z3,z4,z6,z12])],[(0,[z0,z2,z3,z4,z743,z6]),(0,[z0,z2,z744,z3,z4,z6]),(0,[z70,z0,z71,z4,z5,z6]),(0,[z337,z2,z3,z228,z5,z6])],[(0,[z0,z72,z316,z4,z5,z6])],[(0,[z16,z2,z714,z4,z5,z6]),(0,[z0,z3,z30,z250,z5,z6]),(0,[z0,z2,z3,z745,z5,z6]),(0,[z0,z75,z3,z4,z729,z6]),(0,[z0,z38,z2,z161,z113,z6]),(0,[z746,z0,z3,z4,z5,z6]),(0,[z0,z747,z3,z4,z5,z6])],[(0,[z0,z2,z3,z748,z5,z6]),(0,[z0,z21,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z749,z6]),(0,[z0,z2,z750,z3,z4,z6]),(0,[z0,z2,z3,z5,z740,z101])]],
   [[(0,[z2,z733,z3,z4,z5,z6]),(0,[z549,z0,z2,z3,z4,z12]),(0,[z0,z3,z4,z5,z6,z751]),(0,[z0,z752,z3,z4,z5,z6])],[(0,[z0,z2,z3,z753,z5,z6]),(0,[z0,z2,z3,z268,z37,z6]),(0,[z0,z3,z4,z5,z751,z52])],[(0,[z0,z3,z4,z754,z5,z6])],[(0,[z0,z755,z2,z3,z4,z6]),(0,[z0,z2,z266,z3,z31,z6]),(0,[z0,z2,z3,z4,z299,z6]),(0,[z0,z2,z3,z756,z5,z6]),(0,[z0,z2,z3,z757,z5,z6]),(0,[z0,z2,z3,z4,z300,z6]),(0,[z59,z2,z3,z4,z78,z6])],[(0,[z0,z2,z3,z4,z5,z758]),(0,[z0,z2,z3,z759,z83,z6]),(0,[z0,z2,z3,z4,z13,z12])],[(0,[z43,z2,z3,z4,z28,z126]),(0,[z70,z0,z120,z4,z5,z6]),(0,[z0,z2,z135,z268,z5,z6]),(0,[z33,z0,z2,z3,z5,z101])],[(0,[z0,z2,z3,z4,z760,z6]),(0,[z0,z2,z3,z4,z5,z761]),(0,[z0,z2,z3,z4,z762,z6]),(0,[z0,z2,z142,z39,z4,z6]),(0,[z0,z763,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z6,z764])],[(0,[z443,z0,z2,z765,z5,z6]),(0,[z0,z2,z120,z4,z31,z6])]],
   [[(0,[z443,z90,z2,z4,z5,z6]),(0,[z0,z2,z4,z5,z6,z766]),(0,[z0,z62,z3,z4,z5,z6]),(0,[z767,z2,z3,z4,z5,z6]),(0,[z337,z2,z3,z4,z281,z6]),(0,[z0,z2,z3,z4,z768,z6]),(0,[z59,z2,z3,z104,z5,z6])],[(0,[z0,z738,z30,z4,z5,z6]),(0,[z51,z0,z135,z4,z5,z52])],[(0,[z0,z2,z3,z769,z5,z6]),(0,[z0,z2,z770,z4,z5,z6]),(0,[z0,z2,z3,z4,z771,z6]),(0,[z0,z2,z772,z4,z5,z6])],[(0,[z0,z2,z773,z4,z5,z6]),(0,[z0,z2,z3,z774,z5,z6]),(0,[z70,z0,z738,z4,z5,z6]),(0,[z70,z0,z494,z4,z5,z6]),(0,[z0,z2,z3,z775,z5,z6]),(0,[z0,z2,z3,z19,z113,z6]),(0,[z0,z2,z129,z4,z5,z130])],[(0,[z0,z776,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z777,z6])],[(0,[z0,z2,z3,z4,z778,z6]),(0,[z0,z2,z3,z4,z779,z6]),(0,[z0,z2,z3,z710,z5,z6]),(0,[z0,z2,z3,z4,z5,z780]),(0,[z0,z2,z3,z4,z781,z6]),(0,[z0,z2,z3,z104,z78,z6])],[(0,[z16,z0,z21,z4,z5,z6]),(0,[z782,z2,z3,z4,z5,z6])]],
   [[(0,[z0,z2,z3,z783,z5,z6]),(0,[z0,z198,z2,z95,z300,z6]),(0,[z0,z2,z4,z113,z784,z6]),(0,[z58,z0,z21,z4,z5,z236]),(0,[z0,z2,z3,z165,z89,z80])],[(0,[z0,z2,z3,z4,z785,z6]),(0,[z0,z2,z3,z17,z5,z6]),(0,[z22,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z786,z6]),(0,[z787,z2,z3,z4,z5,z6])],[(0,[z0,z206,z3,z249,z5,z6])],[(0,[z122,z2,z266,z3,z5,z6]),(0,[z2,z3,z4,z84,z728,z6]),(0,[z788,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z789,z5,z6]),(1,[z0,z2,z3,z4,z764])],[(0,[z0,z8,z3,z267,z5,z6]),(0,[z0,z2,z3,z268,z5,z6]),(0,[z337,z2,z316,z4,z5,z6]),(0,[z0,z2,z316,z4,z37,z6]),(0,[z0,z21,z3,z507,z5,z6]),(0,[z2,z3,z4,z116,z6,z324])],[(0,[z0,z2,z470,z3,z9,z6])],[(0,[z0,z206,z3,z17,z5,z6]),(0,[z0,z2,z3,z4,z5,z713]),(0,[z0,z2,z11,z142,z4,z6])],[(0,[z0,z2,z3,z4,z5,z790]),(0,[z0,z2,z3,z128,z36,z6]),(0,[z0,z2,z3,z9,z300,z6]),(0,[z0,z21,z3,z104,z5,z6])]],
   [[(0,[z0,z2,z3,z4,z791,z6]),(0,[z0,z2,z3,z4,z792,z6]),(0,[z0,z2,z266,z3,z6,z12]),(0,[z51,z0,z3,z4,z5,z52]),(0,[z0,z297,z3,z95,z5,z6]),(0,[z0,z2,z3,z793,z5,z6])],[(0,[z0,z2,z3,z4,z794,z6]),(1,[z0,z2,z4,z5,z795])],[(0,[z0,z2,z796,z3,z4,z6]),(0,[z2,z3,z165,z5,z89,z324])],[(0,[z0,z2,z3,z4,z797,z6]),(0,[z0,z798,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z625,z69]),(0,[z0,z2,z3,z4,z281,z6]),(0,[z0,z75,z211,z3,z4,z6]),(0,[z0,z369,z2,z4,z113,z6])],[(0,[z122,z2,z3,z4,z5,z117]),(0,[z184,z2,z3,z4,z5,z713]),(0,[z70,z0,z71,z4,z299,z6]),(0,[z0,z2,z301,z9,z5,z6]),(0,[z0,z198,z358,z4,z5,z6]),(0,[z0,z2,z799,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z68]),(0,[z0,z2,z3,z800,z5,z6]),(0,[z43,z2,z3,z4,z728,z6]),(0,[z0,z2,z3,z801,z5,z6]),(0,[z0,z141,z2,z3,z4,z12]),(0,[z802,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z803,z5,z6]),(0,[z0,z62,z3,z4,z202,z6]),(0,[z322,z2,z3,z4,z560,z6]),(0,[z0,z2,z3,z5,z759,z6])],[(0,[z0,z2,z3,z4,z804,z6]),(0,[z0,z2,z805,z4,z5,z6])],[(0,[z0,z2,z463,z753,z5,z6]),(0,[z0,z2,z3,z4,z806,z6]),(0,[z0,z139,z3,z4,z651,z6])]],
   [[(0,[z807,z2,z3,z4,z5,z6]),(0,[z0,z2,z808,z4,z5,z6]),(0,[z0,z2,z3,z4,z6,z809]),(0,[z0,z2,z581,z11,z83,z6])],[(0,[z0,z2,z3,z4,z151,z42]),(0,[z0,z2,z3,z810,z4,z6]),(0,[z0,z2,z3,z5,z6,z811])],[(0,[z0,z206,z3,z4,z5,z68]),(0,[z0,z118,z738,z4,z5,z6]),(1,[z0,z2,z3,z759,z6]),(0,[z2,z3,z4,z5,z6,z812])],[(0,[z194,z195,z3,z4,z5,z6]),(0,[z0,z2,z813,z4,z5,z6]),(0,[z90,z2,z3,z4,z5,z68])],[(0,[z0,z120,z30,z4,z5,z6]),(0,[z0,z2,z3,z4,z814,z6]),(0,[z22,z2,z3,z165,z5,z89])],[(0,[z0,z815,z3,z4,z5,z6]),(0,[z0,z2,z11,z3,z83,z6]),(1,[z0,z2,z3,z5,z740])],[(0,[z0,z2,z3,z4,z5,z816]),(0,[z16,z2,z590,z4,z5,z6]),(1,[z2,z3,z4,z28,z280]),(0,[z0,z2,z3,z817,z5,z6]),(0,[z0,z75,z120,z4,z76,z6])],[(0,[z0,z2,z818,z4,z5,z6]),(0,[z0,z2,z3,z4,z819,z6]),(0,[z381,z2,z3,z4,z5,z170])]],
   [[(0,[z0,z2,z4,z5,z130,z68])],[(0,[z0,z2,z3,z820,z5,z6]),(0,[z0,z2,z3,z4,z5,z821]),(0,[z0,z822,z3,z4,z5,z6]),(0,[z184,z2,z4,z5,z314,z69]),(0,[z0,z2,z221,z9,z5,z6]),(0,[z0,z2,z3,z39,z174,z6])],[(0,[z0,z823,z3,z4,z5,z6])],[(0,[z0,z189,z3,z4,z5,z42]),(0,[z330,z2,z3,z4,z5,z6]),(0,[z158,z2,z3,z265,z4,z6]),(0,[z824,z0,z2,z4,z5,z6]),(0,[z0,z825,z3,z4,z5,z6]),(0,[z59,z2,z3,z4,z5,z130])],[(0,[z0,z2,z30,z4,z5,z68]),(0,[z122,z2,z3,z4,z5,z327]),(0,[z0,z2,z826,z3,z5,z6]),(0,[z322,z323,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z6,z827]),(0,[z43,z2,z3,z4,z28,z280]),(0,[z141,z2,z3,z4,z28,z6]),(0,[z0,z2,z525,z4,z5,z130]),(0,[z0,z2,z142,z4,z5,z6]),(0,[z828,z2,z3,z4,z5,z6]),(0,[z20,z0,z2,z3,z4,z12]),(0,[z0,z2,z3,z4,z829,z6])],[(0,[z0,z830,z2,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z831]),(0,[z0,z2,z11,z244,z83,z6])],[(0,[z0,z682,z2,z4,z113,z6]),(0,[z59,z2,z3,z4,z5,z236]),(0,[z381,z2,z3,z4,z27,z6])]],
   [[(0,[z0,z832,z2,z4,z5,z6]),(0,[z833,z2,z3,z4,z5,z6]),(0,[z0,z453,z3,z4,z31,z6]),(0,[z0,z2,z3,z834,z5,z6])],[(0,[z0,z2,z3,z835,z5,z6]),(0,[z0,z2,z3,z4,z151,z6]),(0,[z0,z2,z120,z836,z5,z6])],[(0,[z48,z2,z112,z3,z5,z6]),(0,[z0,z2,z159,z4,z5,z6]),(0,[z0,z2,z837,z4,z5,z6])],[(0,[z0,z2,z838,z4,z5,z6]),(0,[z0,z2,z3,z4,z764,z12])],[(0,[z0,z2,z3,z4,z5,z839]),(0,[z322,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z840,z5,z6]),(0,[z0,z2,z3,z4,z841,z6]),(0,[z0,z2,z3,z842,z5,z6]),(0,[z0,z2,z3,z4,z843,z6])],[(0,[z0,z2,z3,z4,z133,z69]),(0,[z0,z2,z25,z4,z762,z6]),(0,[z844,z2,z3,z4,z5,z6]),(0,[z0,z38,z62,z4,z5,z6])],[(0,[z0,z206,z3,z4,z151,z6]),(0,[z0,z2,z3,z4,z845,z6]),(0,[z0,z2,z3,z4,z846,z6]),(0,[z0,z2,z3,z4,z5,z126]),(0,[z847,z2,z3,z4,z5,z6]),(0,[z848,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z39,z4,z280]),(0,[z2,z3,z4,z28,z6,z280]),(0,[z0,z2,z4,z784,z31,z6])]],
   [[(0,[z0,z206,z71,z4,z5,z6]),(0,[z0,z849,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z6,z850]),(0,[z184,z2,z3,z4,z5,z69]),(0,[z2,z3,z4,z5,z117,z713]),(0,[z0,z185,z30,z4,z5,z6]),(0,[z58,z0,z2,z4,z560,z236]),(0,[z746,z0,z581,z4,z5,z6])],[(0,[z0,z71,z738,z4,z5,z6]),(0,[z0,z2,z3,z851,z5,z6])],[(0,[z0,z2,z3,z4,z852,z6]),(0,[z0,z2,z853,z4,z5,z6]),(1,[z0,z2,z739,z5,z6]),(0,[z0,z2,z3,z4,z759,z6]),(0,[z0,z2,z3,z4,z27,z170])],[(0,[z0,z189,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z324]),(0,[z122,z2,z3,z4,z133,z6]),(0,[z184,z2,z3,z4,z133,z69]),(0,[z0,z25,z30,z4,z5,z6]),(0,[z854,z2,z3,z4,z5,z6])],[(0,[z0,z2,z670,z9,z5,z6]),(0,[z855,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z856,z5,z6]),(0,[z0,z857,z3,z4,z5,z6]),(0,[z0,z2,z3,z858,z5,z6])],[(0,[z2,z3,z4,z728,z28,z6]),(0,[z0,z139,z3,z4,z729,z6]),(0,[z312,z0,z2,z3,z4,z764])],[(0,[z0,z859,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z6,z860]),(0,[z0,z2,z3,z228,z37,z6])]],
   [[(0,[z0,z2,z3,z249,z5,z42]),(0,[z0,z2,z30,z4,z151,z6]),(0,[z58,z0,z323,z4,z5,z236]),(0,[z0,z861,z3,z4,z5,z6])],[(0,[z0,z2,z30,z161,z5,z6]),(0,[z0,z2,z3,z862,z4,z6]),(0,[z0,z2,z11,z3,z759,z6])],[(0,[z0,z2,z3,z4,z5,z863]),(0,[z0,z224,z3,z4,z85,z6])],[(0,[z0,z2,z3,z4,z864,z6]),(0,[z90,z2,z4,z5,z130,z69]),(0,[z70,z0,z71,z128,z5,z6]),(0,[z272,z0,z71,z4,z5,z6]),(0,[z0,z8,z25,z267,z5,z6]),(0,[z0,z2,z3,z4,z6,z865]),(0,[z0,z2,z135,z228,z5,z6])],[(0,[z70,z0,z463,z4,z5,z6]),(0,[z0,z2,z3,z866,z5,z6]),(0,[z0,z2,z3,z17,z5,z42]),(0,[z0,z2,z4,z5,z6,z867]),(0,[z0,z30,z4,z5,z6,z639]),(0,[z0,z453,z120,z4,z5,z6]),(0,[z219,z0,z2,z3,z5,z101]),(0,[z2,z3,z4,z6,z324,z80])],[(0,[z733,z195,z3,z4,z5,z6]),(0,[z340,z2,z3,z4,z5,z69]),(0,[z0,z3,z4,z729,z76,z6]),(0,[z0,z2,z3,z4,z868,z6]),(0,[z0,z2,z11,z3,z371,z6]),(0,[z0,z2,z3,z5,z89,z740]),(0,[z0,z2,z3,z869,z5,z6])],[(0,[z0,z2,z3,z4,z870,z6])],[(0,[z0,z8,z3,z505,z5,z6]),(0,[z0,z2,z3,z4,z871,z6]),(0,[z0,z75,z3,z4,z76,z6]),(0,[z45,z2,z3,z268,z5,z6]),(0,[z0,z2,z3,z4,z872,z6])]],
   [[(0,[z0,z2,z3,z4,z873,z6]),(0,[z0,z2,z71,z4,z202,z6]),(0,[z0,z2,z874,z4,z5,z6])],[(0,[z155,z156,z463,z4,z5,z6]),(0,[z0,z2,z3,z875,z5,z6]),(0,[z0,z2,z3,z4,z5,z876]),(0,[z51,z0,z3,z268,z5,z52]),(0,[z322,z2,z3,z507,z5,z6]),(0,[z0,z2,z3,z39,z6,z199])],[(0,[z58,z0,z2,z4,z5,z68]),(0,[z43,z2,z266,z3,z28,z6]),(0,[z325,z0,z3,z4,z5,z52]),(0,[z0,z2,z3,z128,z299,z6]),(0,[z0,z2,z3,z4,z877,z6]),(0,[z0,z2,z120,z878,z5,z6])],[(0,[z155,z733,z3,z4,z5,z6]),(0,[z16,z2,z186,z4,z5,z6]),(0,[z0,z2,z3,z879,z5,z6]),(0,[z0,z2,z3,z250,z5,z6]),(0,[z0,z565,z3,z100,z5,z6]),(0,[z0,z139,z3,z557,z4,z6])],[(0,[z0,z2,z880,z4,z5,z6]),(0,[z0,z2,z881,z4,z5,z6]),(0,[z158,z0,z2,z266,z3,z6]),(0,[z0,z2,z266,z3,z27,z6]),(0,[z0,z2,z3,z765,z5,z6]),(0,[z322,z2,z3,z104,z5,z6])],[(0,[z0,z2,z3,z882,z4,z6]),(0,[z0,z2,z3,z4,z5,z883]),(0,[z0,z2,z3,z4,z5,z884]),(0,[z0,z885,z3,z4,z5,z6]),(0,[z0,z2,z4,z5,z795,z236]),(0,[z22,z2,z3,z4,z6,z80])],[(0,[z0,z297,z3,z4,z5,z6]),(0,[z45,z2,z3,z4,z281,z6])],[(0,[z0,z2,z886,z3,z5,z6]),(0,[z0,z2,z887,z3,z5,z6]),(0,[z0,z888,z2,z4,z5,z6]),(0,[z158,z2,z3,z4,z5,z280]),(0,[z0,z2,z135,z4,z281,z6]),(0,[z59,z21,z3,z4,z5,z6]),(0,[z58,z0,z2,z4,z5,z236])]],
   [[(0,[z0,z2,z3,z249,z5,z6]),(0,[z16,z206,z186,z4,z5,z6]),(0,[z0,z2,z3,z889,z5,z6]),(0,[z0,z8,z3,z73,z267,z6]),(0,[z51,z0,z3,z4,z281,z52]),(0,[z0,z890,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z891])],[(0,[z0,z2,z3,z228,z5,z6]),(0,[z0,z2,z3,z836,z5,z6]),(0,[z0,z297,z198,z95,z5,z6]),(0,[z0,z892,z3,z4,z5,z6]),(0,[z0,z381,z2,z3,z4,z12])],[(0,[z0,z733,z3,z4,z5,z6]),(0,[z893,z2,z3,z4,z5,z6]),(0,[z0,z894,z3,z4,z5,z6]),(0,[z0,z198,z2,z19,z5,z6])],[(0,[z0,z2,z895,z4,z5,z6])],[(0,[z0,z896,z3,z4,z5,z6]),(0,[z0,z2,z3,z19,z31,z6]),(0,[z0,z21,z3,z4,z78,z6]),(0,[z0,z897,z3,z4,z5,z6])],[(0,[z700,z195,z3,z4,z5,z6]),(0,[z122,z2,z3,z4,z5,z615]),(0,[z0,z2,z898,z3,z4,z6]),(0,[z0,z198,z2,z4,z36,z6])],[(0,[z0,z2,z899,z4,z5,z6])]],
   [[(0,[z0,z2,z900,z4,z5,z6]),(0,[z0,z2,z3,z4,z901,z6]),(0,[z443,z2,z186,z4,z5,z6]),(0,[z2,z3,z4,z5,z133,z69]),(0,[z2,z3,z4,z5,z713,z6])],[(1,[z2,z3,z4,z728,z6]),(0,[z0,z277,z30,z4,z5,z6]),(0,[z0,z2,z3,z4,z902,z6])],[(0,[z45,z2,z316,z4,z5,z6])],[(0,[z0,z2,z3,z4,z903,z6]),(0,[z0,z2,z3,z904,z5,z6]),(0,[z0,z8,z3,z550,z5,z6]),(0,[z0,z2,z675,z9,z5,z6]),(0,[z905,z2,z3,z4,z5,z6]),(0,[z0,z906,z3,z4,z5,z6])],[(0,[z0,z2,z907,z4,z5,z6]),(0,[z0,z908,z2,z4,z5,z6]),(0,[z0,z2,z909,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z910]),(0,[z0,z2,z3,z4,z911,z6]),(0,[z574,z2,z3,z4,z84,z6]),(0,[z0,z2,z912,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z795])],[(0,[z0,z2,z3,z4,z5,z280])],[(0,[z155,z156,z46,z4,z5,z6]),(0,[z0,z2,z30,z249,z5,z6]),(0,[z0,z913,z3,z4,z5,z6]),(0,[z0,z914,z3,z4,z5,z6])]],
   [[(0,[z0,z2,z3,z4,z915,z6]),(0,[z916,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z917,z6]),(0,[z0,z918,z3,z4,z5,z6])],[(0,[z919,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z920,z5,z6]),(0,[z0,z264,z3,z4,z76,z6]),(0,[z0,z2,z94,z739,z5,z6]),(0,[z0,z2,z581,z95,z5,z6])],[(0,[z0,z2,z921,z3,z4,z6]),(0,[z0,z2,z577,z4,z31,z6]),(0,[z922,z2,z3,z4,z5,z6]),(0,[z0,z297,z3,z9,z5,z6]),(0,[z0,z2,z581,z4,z31,z6])],[(0,[z0,z2,z470,z3,z4,z6]),(0,[z0,z8,z159,z267,z5,z6]),(0,[z0,z2,z3,z4,z923,z6]),(0,[z0,z8,z3,z754,z5,z6]),(0,[z924,z2,z3,z4,z5,z6]),(0,[z0,z297,z3,z4,z202,z6])],[(0,[z70,z0,z71,z250,z5,z6]),(0,[z0,z554,z3,z267,z5,z6]),(0,[z0,z2,z308,z4,z31,z6]),(0,[z58,z0,z2,z507,z5,z236])],[(0,[z0,z453,z3,z4,z5,z6]),(1,[z0,z2,z4,z784,z6]),(0,[z0,z2,z3,z39,z548,z6])],[(0,[z0,z925,z3,z4,z5,z6])],[(0,[z0,z2,z3,z926,z5,z6]),(0,[z0,z75,z3,z4,z233,z6]),(0,[z0,z2,z3,z927,z5,z6]),(0,[z0,z2,z239,z4,z784,z6]),(0,[z58,z0,z2,z104,z5,z236])]],
   [[(0,[z0,z2,z4,z5,z6,z314]),(0,[z546,z0,z2,z3,z4,z12]),(0,[z0,z2,z711,z4,z5,z6]),(0,[z928,z2,z3,z4,z5,z6]),(0,[z0,z2,z4,z5,z130,z795]),(0,[z0,z3,z4,z5,z6,z929])],[(0,[z930,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z931,z6]),(0,[z0,z2,z316,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z751]),(0,[z0,z2,z11,z3,z477,z6])],[(0,[z462,z2,z3,z4,z5,z69]),(0,[z0,z2,z932,z4,z5,z6]),(0,[z0,z2,z933,z4,z5,z6]),(0,[z0,z2,z3,z4,z151,z68]),(0,[z0,z2,z3,z250,z299,z6]),(0,[z0,z2,z3,z878,z5,z6]),(0,[z0,z62,z3,z4,z300,z6]),(0,[z0,z2,z3,z4,z934,z6])],[(0,[z0,z935,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z936]),(0,[z0,z937,z3,z4,z5,z6]),(0,[z0,z2,z239,z4,z31,z6])],[(0,[z0,z2,z938,z4,z5,z6]),(0,[z0,z358,z4,z9,z5,z6])],[(0,[z155,z156,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z939,z6]),(0,[z0,z2,z3,z4,z188,z42]),(0,[z0,z2,z3,z157,z759,z6])],[(0,[z0,z2,z3,z4,z940,z6]),(0,[z0,z2,z941,z4,z5,z6]),(0,[z2,z3,z4,z942,z5,z6]),(0,[z0,z2,z3,z754,z5,z6]),(0,[z0,z2,z11,z3,z318,z6])]],
   [[(0,[z0,z2,z3,z5,z6,z943]),(0,[z0,z944,z3,z4,z5,z6]),(0,[z0,z2,z3,z945,z4,z6]),(0,[z0,z2,z946,z4,z5,z6]),(0,[z0,z2,z947,z4,z5,z6]),(0,[z0,z2,z4,z5,z6,z948])],[(0,[z0,z2,z949,z4,z5,z6]),(0,[z0,z198,z62,z95,z5,z6])],[(0,[z0,z21,z129,z4,z5,z6])],[(0,[z0,z2,z3,z4,z27,z552])],[(0,[z0,z453,z30,z4,z5,z6]),(0,[z51,z337,z3,z4,z5,z52]),(0,[z0,z2,z3,z4,z27,z764])],[(0,[z0,z189,z3,z4,z5,z68]),(0,[z0,z2,z950,z4,z5,z6]),(0,[z951,z2,z3,z4,z5,z6]),(0,[z312,z0,z2,z3,z4,z12])],[(0,[z0,z2,z3,z952,z4,z6]),(0,[z0,z2,z3,z4,z116,z6])],[(0,[z0,z2,z3,z351,z4,z6]),(0,[z0,z75,z3,z4,z305,z6])]],
   [[(0,[z0,z2,z3,z4,z953,z6]),(0,[z0,z2,z4,z299,z31,z6]),(0,[z0,z2,z4,z300,z31,z6]),(0,[z0,z2,z244,z4,z6,z12])],[],[(0,[z0,z2,z954,z4,z5,z6]),(0,[z443,z0,z955,z4,z5,z6]),(0,[z0,z2,z25,z250,z5,z6]),(0,[z337,z2,z3,z4,z37,z6]),(0,[z0,z38,z2,z4,z784,z6])],[(0,[z0,z2,z266,z3,z5,z6]),(0,[z0,z2,z3,z5,z6,z956]),(0,[z0,z2,z3,z250,z36,z6])],[(0,[z0,z957,z3,z4,z5,z6]),(0,[z0,z958,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z959,z6]),(0,[z0,z2,z3,z960,z5,z6]),(0,[z0,z961,z3,z4,z5,z6])],[(0,[z962,z2,z3,z4,z5,z6]),(0,[z0,z297,z25,z4,z5,z6])],[(0,[z0,z2,z3,z4,z188,z6]),(0,[z16,z2,z186,z4,z5,z42]),(0,[z337,z2,z135,z4,z5,z6]),(0,[z0,z2,z135,z4,z37,z6]),(0,[z0,z2,z3,z739,z5,z6]),(0,[z0,z2,z3,z4,z963,z6])],[(0,[z443,z0,z964,z4,z5,z6]),(0,[z0,z2,z120,z4,z5,z6]),(0,[z0,z2,z3,z965,z5,z6]),(0,[z0,z2,z3,z4,z966,z6]),(0,[z0,z908,z2,z429,z4,z6]),(0,[z967,z2,z3,z4,z5,z6])]],
   [[(0,[z0,z279,z30,z4,z5,z6]),(0,[z539,z2,z3,z4,z5,z69]),(0,[z0,z2,z968,z4,z5,z6]),(0,[z58,z322,z2,z4,z5,z236])],[(0,[z0,z2,z969,z4,z5,z6]),(0,[z0,z2,z463,z4,z970,z6]),(0,[z2,z3,z186,z4,z5,z68]),(0,[z0,z2,z3,z971,z5,z6]),(0,[z0,z323,z3,z4,z560,z6])],[(0,[z48,z2,z3,z972,z5,z6]),(0,[z158,z2,z3,z4,z84,z6]),(0,[z0,z2,z3,z4,z201,z6]),(0,[z0,z2,z71,z161,z5,z6]),(0,[z0,z973,z2,z3,z4,z6]),(0,[z0,z581,z897,z4,z5,z6])],[(0,[z0,z206,z3,z4,z188,z6]),(0,[z974,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z5,z6,z740])],[(0,[z0,z2,z975,z4,z5,z6])],[(0,[z0,z2,z738,z4,z5,z6]),(0,[z0,z491,z30,z4,z5,z6]),(0,[z45,z2,z3,z228,z5,z6])],[(0,[z0,z2,z3,z4,z5,z976]),(0,[z0,z2,z977,z4,z5,z6]),(0,[z0,z2,z3,z4,z978,z6]),(0,[z0,z2,z3,z4,z979,z6]),(1,[z0,z3,z4,z729,z6])],[(0,[z0,z2,z3,z4,z133,z117]),(0,[z0,z669,z30,z4,z5,z6]),(0,[z51,z0,z3,z228,z5,z52])]],
   [[(0,[z0,z2,z470,z3,z95,z6]),(0,[z454,z2,z3,z4,z5,z117]),(0,[z980,z2,z3,z4,z5,z6])],[(0,[z0,z189,z3,z4,z151,z6]),(0,[z70,z0,z3,z4,z299,z6]),(0,[z0,z2,z3,z4,z560,z6]),(0,[z0,z2,z3,z165,z116,z89])],[(0,[z0,z2,z3,z249,z5,z68]),(0,[z0,z2,z3,z39,z667,z6]),(0,[z0,z2,z981,z3,z4,z6]),(0,[z0,z2,z3,z982,z5,z6]),(0,[z0,z2,z3,z95,z300,z6]),(0,[z322,z2,z3,z4,z78,z6]),(0,[z58,z0,z2,z4,z5,z795])],[(0,[z983,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z984,z6]),(0,[z0,z985,z3,z4,z5,z6]),(0,[z0,z2,z3,z165,z5,z406]),(0,[z0,z2,z3,z39,z759,z6])],[(0,[z2,z3,z4,z28,z69,z12])],[(0,[z337,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z37,z6]),(0,[z0,z2,z129,z4,z5,z795])],[(0,[z0,z2,z3,z17,z5,z68]),(0,[z0,z2,z3,z4,z986,z6]),(0,[z562,z2,z3,z4,z28,z6])],[(0,[z0,z2,z3,z4,z987,z6]),(0,[z193,z2,z3,z4,z5,z69]),(0,[z0,z118,z30,z4,z5,z6]),(0,[z0,z2,z3,z4,z988,z6]),(0,[z0,z2,z3,z268,z281,z6]),(0,[z0,z989,z3,z4,z5,z6]),(0,[z990,z2,z3,z4,z5,z6])]],
   [[(0,[z0,z2,z3,z991,z5,z6]),(0,[z0,z2,z3,z992,z4,z6])],[(0,[z230,z2,z3,z4,z5,z117]),(0,[z325,z0,z2,z4,z5,z236]),(0,[z0,z75,z142,z4,z76,z6]),(0,[z0,z75,z2,z244,z4,z6])],[(0,[z0,z453,z3,z19,z5,z6]),(0,[z0,z2,z4,z5,z6,z795])],[(0,[z322,z21,z3,z4,z5,z6]),(0,[z0,z2,z3,z39,z157,z6])],[(0,[z993,z2,z3,z4,z5,z6])],[(0,[z0,z2,z994,z4,z5,z6]),(0,[z2,z3,z4,z972,z5,z6]),(0,[z2,z3,z4,z5,z6,z995]),(0,[z0,z996,z3,z4,z5,z6])],[(0,[z2,z3,z4,z728,z5,z6]),(0,[z0,z2,z997,z4,z5,z6])],[(0,[z0,z2,z998,z3,z5,z6]),(0,[z0,z2,z3,z4,z5,z999]),(0,[z0,z2,z1000,z4,z5,z6]),(0,[z90,z59,z2,z4,z5,z6]),(0,[z0,z2,z94,z9,z5,z6]),(0,[z701,z0,z2,z3,z4,z12]),(0,[z0,z358,z3,z19,z5,z6])]],
   [[(0,[z0,z2,z3,z4,z1001,z6]),(0,[z0,z2,z3,z972,z5,z6]),(1,[z2,z3,z4,z133,z69]),(0,[z0,z323,z3,z4,z5,z6]),(0,[z70,z0,z25,z4,z5,z6]),(0,[z0,z1002,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z1003]),(0,[z381,z2,z3,z4,z5,z12])],[(0,[z0,z2,z3,z1004,z5,z6]),(0,[z0,z1005,z3,z4,z5,z6]),(0,[z0,z2,z25,z95,z5,z6]),(0,[z1006,z2,z3,z4,z5,z6]),(0,[z0,z8,z429,z3,z267,z6]),(0,[z0,z2,z1007,z4,z5,z6]),(0,[z0,z1008,z3,z4,z5,z6])],[],[(0,[z2,z3,z972,z49,z5,z6]),(0,[z0,z2,z3,z4,z262,z170]),(0,[z0,z2,z316,z268,z5,z6]),(0,[z0,z2,z3,z4,z1009,z6])],[(0,[z0,z2,z3,z4,z1010,z6])],[(0,[z1011,z2,z3,z4,z5,z6]),(0,[z0,z2,z11,z9,z31,z6])],[(0,[z0,z2,z3,z249,z151,z6]),(0,[z443,z0,z2,z4,z5,z6]),(0,[z51,z45,z3,z4,z5,z52]),(0,[z0,z2,z3,z1012,z5,z6]),(0,[z0,z2,z3,z507,z560,z6])],[(0,[z0,z2,z1013,z4,z5,z6]),(0,[z0,z2,z120,z4,z299,z6]),(0,[z51,z0,z316,z4,z5,z52]),(0,[z0,z2,z3,z1014,z5,z6]),(0,[z0,z2,z3,z376,z157,z6]),(0,[z0,z1015,z3,z4,z5,z6])]],
   [[(0,[z158,z2,z3,z4,z245,z6]),(0,[z0,z297,z30,z4,z5,z6])],[(0,[z0,z2,z3,z1016,z5,z6]),(0,[z0,z271,z2,z95,z5,z6]),(0,[z43,z2,z3,z166,z28,z6]),(0,[z381,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z1017,z6]),(0,[z0,z2,z3,z104,z560,z6])],[(0,[z0,z2,z3,z4,z5,z1018]),(0,[z0,z2,z3,z17,z151,z6]),(0,[z0,z2,z3,z4,z6,z1019]),(0,[z0,z2,z3,z4,z1020,z6]),(0,[z1021,z2,z3,z4,z5,z6])],[(0,[z0,z1022,z3,z4,z5,z6]),(0,[z622,z0,z2,z11,z3,z6]),(0,[z2,z3,z4,z5,z28,z280]),(0,[z0,z2,z3,z4,z133,z6]),(0,[z0,z453,z3,z4,z113,z6]),(0,[z0,z2,z3,z4,z5,z764])],[(0,[z0,z2,z3,z1023,z4,z6]),(0,[z22,z2,z3,z4,z116,z6])],[(0,[z0,z206,z3,z4,z5,z6]),(0,[z193,z2,z3,z4,z28,z6]),(0,[z0,z2,z1024,z4,z5,z6]),(0,[z0,z62,z4,z5,z31,z6]),(0,[z0,z38,z358,z4,z113,z6]),(0,[z58,z0,z2,z4,z78,z236])],[(0,[z0,z2,z3,z4,z970,z6]),(0,[z0,z2,z4,z1025,z5,z6]),(0,[z0,z2,z3,z4,z1026,z6]),(0,[z0,z2,z3,z4,z729,z6]),(0,[z0,z38,z453,z4,z113,z6])],[(0,[z0,z2,z3,z4,z6,z1027]),(0,[z0,z2,z95,z739,z5,z6])]],
   [[(0,[z0,z189,z3,z249,z5,z6]),(0,[z0,z2,z3,z4,z5,z1028]),(0,[z48,z2,z3,z351,z49,z6]),(1,[z0,z738,z4,z5,z6]),(0,[z0,z2,z1029,z4,z5,z6]),(0,[z0,z2,z1030,z4,z5,z6])],[(0,[z0,z2,z3,z1031,z5,z6]),(0,[z0,z2,z714,z4,z5,z6]),(0,[z0,z2,z1032,z4,z5,z6]),(0,[z443,z0,z2,z4,z1033,z6]),(0,[z0,z2,z3,z4,z784,z6])],[(0,[z1034,z2,z3,z4,z5,z6]),(0,[z1035,z2,z3,z4,z5,z6])],[(0,[z0,z2,z1036,z4,z5,z6]),(0,[z0,z2,z3,z4,z1033,z6]),(0,[z0,z1037,z3,z4,z5,z6]),(0,[z0,z1038,z3,z4,z5,z6])],[(0,[z452,z195,z3,z4,z5,z6]),(0,[z0,z189,z3,z17,z5,z6]),(0,[z0,z2,z3,z4,z1039,z6]),(0,[z0,z2,z3,z1040,z5,z6]),(0,[z0,z75,z3,z4,z428,z6]),(0,[z0,z3,z754,z267,z5,z6]),(0,[z0,z2,z3,z73,z4,z6]),(0,[z0,z2,z3,z4,z1041,z6]),(0,[z0,z2,z244,z4,z27,z6])],[(0,[z0,z2,z3,z4,z1042,z6]),(0,[z0,z1043,z3,z4,z5,z6]),(0,[z0,z358,z3,z4,z5,z6]),(0,[z0,z2,z3,z1044,z5,z6]),(0,[z0,z323,z3,z507,z5,z6])],[(0,[z0,z2,z3,z4,z5,z1045]),(0,[z0,z1046,z3,z4,z5,z6]),(0,[z122,z2,z3,z4,z5,z713]),(0,[z0,z2,z250,z9,z5,z6]),(0,[z0,z2,z53,z4,z31,z6])],[(0,[z0,z2,z3,z1047,z5,z6]),(0,[z0,z1048,z3,z4,z5,z6]),(0,[z0,z38,z2,z4,z113,z6]),(0,[z0,z2,z4,z784,z5,z6]),(0,[z0,z2,z3,z165,z5,z740])]],
   [[(0,[z0,z2,z71,z4,z5,z68]),(0,[z0,z3,z4,z5,z6,z1049]),(0,[z1050,z2,z3,z4,z5,z6]),(0,[z0,z323,z3,z104,z5,z6])],[(0,[z0,z223,z30,z4,z5,z6]),(0,[z0,z297,z3,z4,z300,z6])],[(0,[z0,z1051,z3,z4,z5,z6]),(0,[z43,z2,z3,z4,z28,z6]),(0,[z443,z184,z2,z4,z5,z69]),(0,[z0,z316,z4,z5,z6,z52])],[(0,[z0,z2,z3,z1052,z5,z6]),(0,[z0,z1053,z3,z4,z5,z6])],[(0,[z0,z1054,z3,z4,z5,z6]),(0,[z0,z2,z3,z165,z5,z655]),(0,[z0,z453,z3,z161,z5,z6]),(0,[z0,z2,z1055,z4,z5,z6])],[(0,[z0,z2,z3,z4,z1056,z6]),(0,[z0,z2,z1057,z4,z5,z6]),(0,[z0,z2,z3,z4,z1058,z6]),(0,[z0,z2,z3,z1059,z4,z6]),(0,[z0,z2,z3,z4,z202,z6]),(0,[z0,z2,z3,z507,z5,z6]),(1,[z381,z2,z3,z4,z12])],[(0,[z194,z733,z3,z4,z5,z6]),(0,[z0,z3,z30,z4,z299,z6]),(0,[z0,z2,z225,z4,z31,z6]),(0,[z0,z21,z4,z5,z6,z236]),(0,[z1060,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z1061,z5,z6])],[(0,[z0,z2,z3,z4,z5,z1062]),(0,[z0,z2,z3,z4,z1063,z6])]],
   [[(0,[z0,z2,z3,z4,z5,z1064]),(0,[z122,z2,z3,z4,z5,z636]),(0,[z16,z2,z186,z249,z5,z6]),(0,[z0,z2,z3,z4,z188,z68]),(0,[z90,z2,z4,z5,z6,z111]),(0,[z2,z3,z394,z4,z5,z69]),(0,[z0,z38,z2,z128,z5,z6]),(0,[z0,z2,z3,z104,z5,z6]),(0,[z96,z0,z2,z11,z3,z6]),(0,[z0,z2,z11,z3,z500,z6])],[(0,[z0,z2,z266,z3,z113,z6]),(0,[z0,z144,z3,z4,z85,z6]),(0,[z0,z2,z3,z1065,z5,z6]),(0,[z1066,z2,z3,z4,z5,z6]),(0,[z0,z358,z3,z161,z5,z6])],[(0,[z0,z2,z3,z4,z1067,z6])],[(0,[z0,z2,z3,z4,z1068,z6]),(0,[z0,z1069,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z1070]),(0,[z16,z2,z186,z17,z5,z6]),(0,[z0,z2,z3,z4,z5,z1071]),(0,[z0,z2,z3,z1072,z5,z6]),(1,[z2,z3,z4,z5,z713]),(0,[z0,z2,z1073,z4,z5,z6])],[(0,[z0,z2,z120,z4,z113,z6])],[(0,[z0,z2,z463,z4,z5,z6]),(0,[z0,z955,z3,z4,z5,z6]),(0,[z0,z2,z128,z5,z31,z6]),(0,[z337,z2,z3,z268,z5,z6])],[(0,[z0,z2,z3,z4,z1074,z6]),(0,[z0,z2,z3,z1075,z5,z6]),(0,[z0,z8,z3,z486,z5,z6]),(0,[z0,z2,z1076,z4,z5,z6])]],
   [[(0,[z0,z2,z4,z5,z130,z450]),(0,[z90,z0,z21,z4,z5,z6]),(0,[z45,z2,z3,z4,z37,z6])],[(0,[z0,z2,z3,z1077,z5,z6]),(0,[z0,z198,z2,z739,z5,z6])],[(0,[z0,z2,z3,z5,z6,z1078]),(0,[z1079,z2,z3,z4,z5,z6]),(0,[z51,z0,z3,z4,z37,z52]),(0,[z0,z198,z2,z95,z202,z6]),(0,[z59,z2,z3,z507,z5,z6])],[(0,[z0,z206,z463,z4,z5,z6]),(0,[z0,z2,z3,z4,z28,z280])],[(0,[z0,z2,z71,z4,z151,z6]),(0,[z0,z2,z11,z3,z528,z6]),(0,[z0,z2,z30,z4,z202,z6]),(0,[z45,z2,z135,z4,z5,z6]),(0,[z0,z2,z581,z19,z5,z6])],[(0,[z0,z2,z3,z4,z5,z1080]),(0,[z0,z2,z1081,z4,z5,z6]),(0,[z0,z2,z3,z1082,z5,z6]),(0,[z43,z0,z2,z266,z3,z6]),(0,[z0,z2,z3,z4,z1083,z5])],[(0,[z2,z3,z4,z133,z6,z69]),(0,[z678,z2,z3,z4,z5,z69])],[(0,[z0,z2,z3,z1084,z5,z6]),(0,[z0,z2,z3,z4,z1085,z6]),(0,[z1086,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z6,z1087]),(0,[z0,z2,z1088,z4,z5,z6])]],
   [[(0,[z0,z2,z3,z4,z1089,z6]),(0,[z16,z2,z186,z4,z5,z68]),(0,[z0,z2,z3,z507,z78,z6])],[(0,[z0,z2,z1090,z4,z5,z6]),(0,[z0,z2,z3,z4,z84,z280]),(0,[z122,z2,z3,z4,z5,z382])],[(0,[z0,z2,z200,z9,z5,z6]),(0,[z2,z266,z3,z5,z6,z69]),(0,[z0,z2,z3,z4,z1091,z6])],[(0,[z0,z2,z3,z1092,z5,z6]),(0,[z0,z2,z3,z4,z1093,z6]),(0,[z0,z2,z1094,z4,z5,z6]),(0,[z51,z0,z3,z4,z5,z751])],[(0,[z333,z2,z3,z4,z5,z69]),(0,[z0,z2,z3,z4,z5,z1095]),(0,[z0,z2,z1096,z4,z5,z6])],[(0,[z0,z2,z3,z228,z281,z6]),(0,[z0,z2,z3,z19,z5,z6])],[(0,[z0,z2,z1097,z4,z5,z6]),(0,[z0,z1098,z3,z4,z5,z6]),(0,[z0,z8,z3,z204,z5,z6]),(0,[z1099,z2,z3,z4,z5,z6])],[(0,[z155,z668,z3,z4,z5,z6]),(0,[z443,z0,z2,z4,z1100,z6]),(0,[z0,z2,z25,z4,z5,z6]),(0,[z0,z2,z3,z4,z1101,z6])]],
   [[(0,[z0,z2,z3,z4,z36,z6]),(0,[z489,z0,z2,z3,z5,z101]),(0,[z1102,z2,z3,z4,z5,z6]),(0,[z1103,z2,z3,z4,z5,z6])],[(0,[z0,z2,z4,z5,z6,z1104]),(0,[z0,z2,z3,z4,z1100,z6]),(0,[z70,z0,z3,z250,z5,z6]),(0,[z0,z198,z2,z250,z5,z6]),(0,[z0,z139,z2,z244,z4,z6]),(0,[z0,z2,z3,z4,z1105,z6])],[(0,[z0,z2,z3,z166,z5,z6]),(0,[z0,z75,z30,z4,z31,z6]),(0,[z0,z3,z4,z85,z729,z6]),(0,[z0,z2,z640,z9,z5,z6])],[(0,[z45,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z1106,z5,z6]),(0,[z0,z2,z3,z4,z5,z42]),(0,[z0,z2,z1107,z3,z5,z6]),(0,[z0,z964,z3,z4,z5,z6]),(0,[z0,z2,z1108,z4,z5,z6]),(0,[z0,z2,z4,z9,z36,z6]),(0,[z1109,z2,z3,z4,z5,z6])],[(0,[z0,z2,z46,z4,z5,z6]),(0,[z0,z1110,z2,z3,z5,z6]),(0,[z48,z2,z3,z49,z5,z6]),(0,[z0,z2,z135,z4,z5,z6]),(0,[z0,z38,z2,z4,z299,z6]),(0,[z0,z38,z2,z4,z300,z6])],[(0,[z0,z2,z3,z4,z1111,z6]),(0,[z0,z2,z3,z4,z1112,z6]),(0,[z0,z2,z25,z4,z1026,z6]),(0,[z0,z2,z581,z4,z113,z6])],[(0,[z0,z2,z3,z1113,z4,z6]),(0,[z0,z2,z3,z4,z1114,z6]),(0,[z0,z2,z463,z4,z741,z6]),(0,[z0,z189,z3,z4,z188,z6]),(0,[z0,z2,z3,z4,z5,z1115])],[(0,[z0,z2,z3,z1116,z5,z6]),(0,[z0,z2,z1117,z3,z4,z6]),(0,[z0,z2,z3,z4,z1118,z6]),(0,[z48,z2,z470,z3,z49,z6]),(0,[z184,z2,z3,z4,z201,z69]),(0,[z0,z2,z3,z1119,z5,z6]),(0,[z0,z2,z3,z4,z170,z764])]],
   [[(0,[z0,z206,z3,z4,z5,z42]),(0,[z443,z0,z2,z4,z5,z68]),(0,[z0,z1120,z3,z4,z5,z6]),(0,[z443,z0,z2,z801,z5,z6])],[(0,[z443,z0,z2,z4,z5,z130]),(0,[z0,z2,z316,z228,z5,z6]),(0,[z0,z2,z3,z4,z6,z1121]),(0,[z59,z2,z3,z4,z560,z6])],[(0,[z0,z2,z1122,z3,z4,z6]),(0,[z0,z2,z3,z1123,z5,z6]),(0,[z0,z2,z581,z4,z5,z6])],[(0,[z0,z2,z3,z4,z1124,z6]),(0,[z0,z1125,z3,z4,z5,z6]),(0,[z0,z2,z244,z4,z5,z6])],[(0,[z16,z2,z186,z4,z151,z6]),(0,[z0,z2,z3,z1126,z5,z6]),(0,[z0,z38,z2,z19,z113,z6]),(0,[z0,z2,z3,z4,z6,z80])],[(0,[z443,z0,z2,z4,z5,z236])],[(0,[z0,z2,z97,z4,z31,z6]),(0,[z1127,z2,z3,z4,z5,z6])],[(0,[z226,z156,z3,z4,z5,z6]),(0,[z0,z2,z3,z1128,z5,z6]),(0,[z2,z3,z4,z5,z6,z1129])]],
   [[(0,[z354,z2,z3,z49,z5,z6]),(0,[z2,z3,z4,z5,z6,z1130]),(0,[z312,z381,z2,z3,z4,z12])],[(0,[z0,z1131,z3,z4,z5,z6]),(0,[z0,z297,z71,z4,z5,z6])],[],[(0,[z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z71,z249,z5,z6]),(0,[z0,z2,z25,z9,z5,z6]),(0,[z0,z2,z1132,z4,z5,z6])],[(0,[z0,z463,z30,z4,z5,z6]),(0,[z0,z2,z1133,z4,z5,z6]),(0,[z0,z2,z1134,z4,z5,z6])],[(0,[z0,z2,z3,z157,z644,z6]),(0,[z0,z2,z3,z4,z6,z1135]),(0,[z0,z2,z316,z4,z281,z6]),(0,[z219,z0,z2,z3,z5,z740])],[(0,[z16,z189,z186,z4,z5,z6]),(0,[z16,z2,z186,z4,z188,z6]),(0,[z16,z59,z2,z4,z5,z6]),(0,[z0,z2,z1136,z3,z4,z6]),(0,[z0,z2,z3,z4,z27,z603]),(0,[z0,z2,z739,z4,z5,z6]),(0,[z0,z2,z19,z9,z5,z6]),(0,[z1137,z2,z3,z4,z5,z6]),(0,[z0,z1138,z3,z4,z5,z6])],[(0,[z0,z400,z30,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z1139]),(0,[z158,z2,z3,z4,z728,z6]),(0,[z0,z2,z3,z4,z27,z521]),(0,[z0,z2,z3,z128,z5,z6]),(0,[z58,z59,z2,z4,z5,z236])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 548) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 548).take 541) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1089).take 13) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1102)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [548, 541, 13] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 133).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 133).take 123).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [133, 123] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_nil pcend))

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

end PEqualNP.Outside.L_meta_39219

theorem PEqualNP.Outside.L_meta_39219 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277071598 * 2 ^ 32 + 4276152480) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277071598 * 2 ^ 32 + 4276152480) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_39219.solve