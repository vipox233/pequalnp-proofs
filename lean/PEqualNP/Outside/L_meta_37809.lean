import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_37809

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
  Nat.testBit (4277074602 * 2 ^ 32 + 4243126272) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x004040aac886e634#64 ++ 0x2004040aac886e63#64 ++ 0x60c8c3ffc88fe67f#64 ++ 0xd60c8c3ffc88fe67#64 : BitVec 256),
   (0x1113326603b17851#64 ++ 0x41113326603b1785#64 ++ 0xb33732660ff1f87f#64 ++ 0xbb33732660ff1f87#64 : BitVec 256),
   (0x0438147810da2a81#64 ++ 0x80438147810da2a8#64 ++ 0xec383c7870fe3f8d#64 ++ 0x7ec383c7870fe3f8#64 : BitVec 256),
   (0x0bc02b806d001566#64 ++ 0x00bc02b806d00156#64 ++ 0xcfc03f807f003ffc#64 ++ 0xfcfc03f807f003ff#64 : BitVec 256),
   (0x2eedc0007e6d8008#64 ++ 0x02eedc0007e6d800#64 ++ 0xbfffc0007fffc00b#64 ++ 0xfbfffc0007fffc00#64 : BitVec 256),
   (0x4fbebf5500000000#64 ++ 0x04fbebf550000000#64 ++ 0x5fffffff80000007#64 ++ 0xf5fffffff8000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [0, 1]⟩, ⟨.or, [6, 2]⟩, ⟨.and, [1, 4]⟩, ⟨.or, [0, 8]⟩, ⟨.or, [8, 7]⟩, ⟨.and, [7, 4]⟩, ⟨.or, [11, 5]⟩, ⟨.and, [9, 12]⟩, ⟨.and, [10, 3]⟩, ⟨.or, [13, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x004040aac886e634 0x2004040aac886e63 0x60c8c3ffc88fe67f 0xd60c8c3ffc88fe67

def z1 : W := mkw 0x0438147810da2a81 0x80438147810da2a8 0xec383c7870fe3f8d 0x7ec383c7870fe3f8

def z2 : W := mkw 0x0bc02b806d001566 0x00bc02b806d00156 0xcfc03f807f003ffc 0xfcfc03f807f003ff

def z3 : W := mkw 0x1113326603b17851 0x41113326603b1785 0xb33732660ff1f87f 0xbb33732660ff1f87

def z4 : W := mkw 0x2eedc0007e6d8008 0x02eedc0007e6d800 0xbfffc0007fffc00b 0xfbfffc0007fffc00

def z5 : W := mkw 0x4fbebf5500000000 0x04fbebf550000000 0x5fffffff80000007 0xf5fffffff8000000

def z6 : W := mkw 0x4ffebffd7dda3fe7 0x84ffebffd7dda3fe 0xfffffffffffe3fff 0xffffffffffffe3ff

def z7 : W := mkw 0x1102220601005050 0x4110222060100505 0x0000020600000070 0x0000002060000007

def z8 : W := mkw 0x04684498d84e86a4 0xa04684498d84e86a 0x4cc8cd99f00e0780 0x44cc8cd99f00e078

def z9 : W := mkw 0x0bc02b806d001566 0x00bc02b806d00156 0xcfc03d8077001f80 0x6cfc03d8077001f8

def z10 : W := mkw 0x0000002200806010 0x0000000220080601 0x200002660881e07f 0x9200002660881e07

def z11 : W := mkw 0x2eecc0007c4c8008 0x02eecc0007c4c800 0x0cc8c000700e0000 0x40cc8c000700e000

def z12 : W := mkw 0x004040aac886e634 0x2004040aac886e63 0x20000000488fe678 0x020000000488fe67

def z13 : W := mkw 0x4ffeffffc886e634 0x24ffeffffc886e63 0x7fffffffc88fe67f 0xf7fffffffc88fe67

def z14 : W := mkw 0x2eecc4187c4e8288 0x82eecc4187c4e828 0x4cc8cc18700e0780 0x44cc8cc18700e078

def z15 : W := mkw 0x0ee80d987c4a07a6 0x80ee80d987c4a07a 0x4cc80d98700e0780 0x44cc80d98700e078

def z16 : W := mkw 0x047854fad8deeeb5 0xa047854fad8deeeb 0x60f8c3ffc8ffe67f 0xd60f8c3ffc8ffe67

def z17 : W := mkw 0x1103220603215050 0x4110322060321505 0x130702060f01c072 0x8130702060f01c07

def z18 : W := mkw 0x2a85800026210008 0x02a8580002621000 0x1307000007000000 0x0130700000700000

def z19 : W := mkw 0x5fbebf7701907851 0x45fbebf770190785 0x5fffffff80003877 0xf5fffffff8000387

def z20 : W := mkw 0x004040aac886e634 0x2004040aac886e63 0x20000266488fe67f 0x920000266488fe67

def z21 : W := mkw 0x0000002810da2a81 0x80000002810da2a8 0xa000000070fe3f88 0x0a000000070fe3f8

def z22 : W := mkw 0x0438145010580881 0x8043814501058088 0x8c303c0030701980 0x28c303c003070198

def z23 : W := mkw 0x4faeab0500000000 0x04faeab050000000 0x1fffc38780000003 0xf1fffc3878000000

def z24 : W := mkw 0x053a367c10da2a81 0x8053a367c10da2a8 0xff3f3e7e70fe3f8f 0xfff3f3e7e70fe3f8

def z25 : W := mkw 0x1013106602b16811 0x41013106602b1681 0x3037026608f1e07f 0x93037026608f1e07

def z26 : W := mkw 0x0001000002210000 0x0000100000221000 0xb33700000ff1c00b 0xbb33700000ff1c00

def z27 : W := mkw 0x0040400048048000 0x0004040004804800 0x20c8c000488fc00b 0xd20c8c000488fc00

def z28 : W := mkw 0x242dc000126d8008 0x0242dc000126d800 0x303fc00000ffc003 0x0303fc00000ffc00

def z29 : W := mkw 0x2ead800036690008 0x02ead80003669000 0x9f37000037700000 0x29f3700003770000

def z30 : W := mkw 0x0000000000000000 0x0000000000000000 0x40c8c3ff80000007 0xd40c8c3ff8000000

def z31 : W := mkw 0x4ffebfd56d001566 0x04ffebfd56d00156 0xdfffffffff003fff 0xfdfffffffff003ff

def z32 : W := mkw 0x0bc02b8048000424 0x00bc02b804800042 0x4fc03f804800267c 0xf4fc03f804800267

def z33 : W := mkw 0x2bc5eb806f25956e 0x02bc5eb806f25956 0x13c7c3800f01c072 0x813c7c3800f01c07

def z34 : W := mkw 0x0000002810da2a81 0x80000002810da2a8 0xec003c0070fe3f8c 0x7ec003c0070fe3f8

def z35 : W := mkw 0x443e945500000000 0x0443e94550000000 0x103fc07f80000003 0x0103fc07f8000000

def z36 : W := mkw 0x0438145000000000 0x0043814500000000 0x4c383c7800000005 0x74c383c780000000

def z37 : W := mkw 0x4fbebf7d10da2a81 0x84fbebf7d10da2a8 0xfffffffff0fe3f8f 0xffffffffff0fe3f8

def z38 : W := mkw 0x0428000010480000 0x0042800001048000 0xec383c0070fe3f8d 0x7ec383c0070fe3f8

def z39 : W := mkw 0x2fedeb807f6d956e 0x02fedeb807f6d956 0xffffff807fffffff 0xfffffff807ffffff

def z40 : W := mkw 0x0fb83f7835da3bc3 0x80fb83f7835da3bc 0xef383c7877fe3f8d 0x7ef383c7877fe3f8

def z41 : W := mkw 0x1113326603b17851 0x41113326603b1785 0xb33730000ff1f878 0x2b33730000ff1f87

def z42 : W := mkw 0x004040aad8deeeb5 0xa004040aad8deeeb 0xe0c8c3fff8ffffff 0xde0c8c3fff8fffff

def z43 : W := mkw 0x243dd47812ffaa89 0x8243dd47812ffaa8 0xfc3ffc7870ffff8f 0x7fc3ffc7870ffff8

def z44 : W := mkw 0x553fb67703b17851 0x4553fb67703b1785 0xb33ff27f8ff1f87f 0xbb33ff27f8ff1f87

def z45 : W := mkw 0x4b86ab0500000000 0x04b86ab050000000 0x53cfc3ff80000007 0xd53cfc3ff8000000

def z46 : W := mkw 0x00404088c8068624 0x200404088c806862 0x40c8c199c00e0600 0x440c8c199c00e060

def z47 : W := mkw 0x0478547858deaa81 0x80478547858deaa8 0xecf8fc7878ffff8f 0xfecf8fc7878ffff8

def z48 : W := mkw 0x0bc02b806d001566 0x00bc02b806d00156 0xcfc8ffffff003fff 0xfcfc8ffffff003ff

def z49 : W := mkw 0x2fede2007f6d9048 0x02fede2007f6d904 0xbffff2007ffff87f 0xfbffff2007ffff87

def z50 : W := mkw 0x111332ee83b37e75 0x6111332ee83b37e7 0xf33733ff8ff1fe7f 0xbf33733ff8ff1fe7

def z51 : W := mkw 0x115332e66fb17d77 0x4115332e66fb17d7 0xb33732667ff1ffff 0xbb33732667ff1fff

def z52 : W := mkw 0x0000002800822200 0x0000000280082220 0xec083c78708e3f8d 0x7ec083c78708e3f8

def z53 : W := mkw 0x1113326603b17851 0x41113326603b1785 0x3037326600f1f877 0x03037326600f1f87

def z54 : W := mkw 0x115372eecbb7fe75 0x6115372eecbb7fe7 0xf3fff3ffcffffe7f 0xff3fff3ffcffffe7

def z55 : W := mkw 0x153b367e13fb7ad1 0xc153b367e13fb7ad 0xff3f3e7e7fffffff 0xfff3f3e7e7ffffff

def z56 : W := mkw 0x104140aacbb7fe75 0x6104140aacbb7fe7 0xe0c8c3ffcffffe7f 0xde0c8c3ffcffffe7

def z57 : W := mkw 0x2efdd4507e7d8889 0x82efdd4507e7d888 0xbffffc007fffd98b 0xfbffffc007fffd98

def z58 : W := mkw 0x0010145000100881 0x8001014500010088 0x00003c0000001980 0x000003c000000198

def z59 : W := mkw 0x2eedc088fe6f862c 0x22eedc088fe6f862 0xffffc199ffffc60b 0xfffffc199ffffc60

def z60 : W := mkw 0x4b86ab0500000000 0x04b86ab050000000 0x13c7c38780000002 0x813c7c3878000000

def z61 : W := mkw 0x2eedc0007e6d8008 0x02eedc0007e6d800 0x33ffc0000fffc003 0x833ffc0000fffc00

def z62 : W := mkw 0x0040008048000424 0x0004000804800042 0x40c003804800267c 0xd40c003804800267

def z63 : W := mkw 0x2eadc000366d8008 0x02eadc000366d800 0xbf3fc00037ffc003 0x2bf3fc00037ffc00

def z64 : W := mkw 0x1001002203b17851 0x41001002203b1785 0xa00000000ff1f878 0x0a00000000ff1f87

def z65 : W := mkw 0x0000002000802000 0x0000000200080200 0x200000600080200d 0x1200000600080200

def z66 : W := mkw 0x4fbeff7f8086e210 0x24fbeff7f8086e21 0x7fffffff808fc007 0xf7fffffff808fc00

def z67 : W := mkw 0x1113324403311841 0x4111332440331184 0x9337300007701800 0x2933730000770180

def z68 : W := mkw 0x0010147800922a81 0x80010147800922a8 0x40003c7800003f84 0x040003c7800003f8

def z69 : W := mkw 0x1113367e03b37ad1 0xc1113367e03b37ad 0xf3373e7e0ff1ffff 0xbf3373e7e0ff1fff

def z70 : W := mkw 0x2efdd4507e6d8008 0x02efdd4507e6d800 0xfffffc787fffc00f 0xffffffc787fffc00

def z71 : W := mkw 0x004000806c000526 0x0004000806c00052 0x0000000070000780 0x0000000007000078

def z72 : W := mkw 0x1b933b6603b17851 0x41b933b6603b1785 0xfff73fe60ff1f87f 0xffff73fe60ff1f87

def z73 : W := mkw 0x1bd37beeefb7ff77 0x61bd37beeefb7ff7 0xffffffffffffffff 0xffffffffffffffff

def z74 : W := mkw 0x4fbebf7d10da2a81 0x84fbebf7d10da2a8 0x7fffffff80fe0007 0xf7fffffff80fe000

def z75 : W := mkw 0x1112326601907851 0x4111232660190785 0xa030326600f0387d 0x3a030326600f0387

def z76 : W := mkw 0x4eac8d1100000000 0x04eac8d110000000 0x4cc8cd9980000000 0x44cc8cd998000000

def z77 : W := mkw 0x6eedcd117e6d8008 0x06eedcd117e6d800 0xffffcd99ffffc00b 0xfffffcd99ffffc00

def z78 : W := mkw 0x204140007e6d8008 0x0204140007e6d800 0xa00000007fffc008 0x0a00000007fffc00

def z79 : W := mkw 0x204140aafeefe63c 0x2204140aafeefe63 0xe0c8c3ffffffe67f 0xde0c8c3ffffffe67

def z80 : W := mkw 0x0a80000024000000 0x00a8000002400000 0x8f00000037000000 0x28f0000003700000

def z81 : W := mkw 0x3ffff2eefffffe7d 0x63ffff2eefffffe7 0xfffff3fffffffe7f 0xffffff3fffffffe7

def z82 : W := mkw 0x0112324400000000 0x0011232440000000 0x1337326600000007 0xb133732660000000

def z83 : W := mkw 0x5fbfbf7703b17851 0x45fbfbf7703b1785 0xffffffff8ff1f87f 0xfffffffff8ff1f87

def z84 : W := mkw 0x0040400048048000 0x0004040004804800 0x00c0c0000801c002 0x800c0c0000801c00

def z85 : W := mkw 0x0bc02b806d001566 0x00bc02b806d00156 0x43c003804f00267c 0xd43c003804f00267

def z86 : W := mkw 0x246dc0005a6d8008 0x0246dc0005a6d800 0x30ffc00048ffc00b 0xd30ffc00048ffc00

def z87 : W := mkw 0x0000000000000000 0x0000000000000000 0xcc003c0070003f8c 0x7cc003c0070003f8

def z88 : W := mkw 0x1113326603b17851 0x41113326603b1785 0x333702660ff1c073 0x8333702660ff1c07

def z89 : W := mkw 0x1001000203215050 0x4100100020321505 0x000000000f01c070 0x0000000000f01c07

def z90 : W := mkw 0x0ef81df87cda2fa7 0x80ef81df87cda2fa 0xecf83df870fe3f8d 0x7ecf83df870fe3f8

def z91 : W := mkw 0x6fffff557e6d8008 0x06fffff557e6d800 0xffffffffffffc00f 0xfffffffffffffc00

def z92 : W := mkw 0x2eedc0aafeefe63c 0x22eedc0aafeefe63 0xffffc3ffffffe67f 0xfffffc3ffffffe67

def z93 : W := mkw 0x004000806d001566 0x0004000806d00156 0x800000007f003ff8 0x0800000007f003ff

def z94 : W := mkw 0x0b802b0025001142 0x00b802b002500114 0x8f003c0037001980 0x28f003c003700198

def z95 : W := mkw 0x0bc02b806d001566 0x00bc02b806d00156 0x83c003807f003ff8 0x883c003807f003ff

def z96 : W := mkw 0x1013106602b16811 0x41013106602b1681 0x3037006600f1c003 0x03037006600f1c00

def z97 : W := mkw 0x004040aac886e634 0x2004040aac886e63 0x40c8c3ffc00e2674 0x440c8c3ffc00e267

def z98 : W := mkw 0x6ffeff557c4c8008 0x06ffeff557c4c800 0x5ffffffff00e0007 0xf5ffffffff00e000

def z99 : W := mkw 0x20014000126d8008 0x020014000126d800 0x2000000000ffc000 0x02000000000ffc00

def z100 : W := mkw 0x0438147810da2a81 0x80438147810da2a8 0xac303c0070fe3f88 0x2ac303c0070fe3f8

def z101 : W := mkw 0x004040a2c884e434 0x2004040a2c884e43 0x20c0c3e78881e07f 0x920c0c3e78881e07

def z102 : W := mkw 0x0eac800000000000 0x00eac80000000000 0x1fffc00000000003 0xf1fffc0000000000

def z103 : W := mkw 0x0100222201807050 0x0010022220180705 0xa30032660f81f87f 0xba30032660f81f87

def z104 : W := mkw 0x3fefe2067f6dd058 0x43fefe2067f6dd05 0xbfffc2067fffc07b 0xfbfffc2067fffc07

def z105 : W := mkw 0x0428000010480000 0x0042800001048000 0xac38000070fe0009 0x7ac38000070fe000

def z106 : W := mkw 0x014062aac986f674 0x2014062aac986f67 0xe3c8f3ffcf8ffe7f 0xfe3c8f3ffcf8ffe7

def z107 : W := mkw 0x0000402a8086e210 0x20000402a8086e21 0x2008c27f888fe07f 0x92008c27f888fe07

def z108 : W := mkw 0x0001000002210000 0x0000100000221000 0xa00000000ff1c008 0x0a00000000ff1c00

def z109 : W := mkw 0x004040224884e010 0x0004040224884e01 0x20c8c266488fe07f 0xd20c8c266488fe07

def z110 : W := mkw 0x4fbebf5510580881 0x84fbebf551058088 0xdfffffffb0701987 0xfdfffffffb070198

def z111 : W := mkw 0x4eeccd99c8068624 0x24eeccd99c806862 0x4cc8cd99c00e0600 0x44cc8cd99c00e060

def z112 : W := mkw 0x2ebd945036790889 0x82ebd94503679088 0x9f373c0037701980 0x29f373c003770198

def z113 : W := mkw 0x047814f858da2ea5 0x8047814f858da2ea 0xecf83ff878fe3ffd 0xfecf83ff878fe3ff

def z114 : W := mkw 0x00404082c804c434 0x200404082c804c43 0x00c0c3878801c072 0x800c0c3878801c07

def z115 : W := mkw 0x047854fad8deeeb5 0xa047854fad8deeeb 0xecf8fffff8ffffff 0xfecf8fffff8fffff

def z116 : W := mkw 0x4fbebf5500000000 0x04fbebf550000000 0x1f373c0000000000 0x21f373c000000000

def z117 : W := mkw 0x0bc02b806d001566 0x00bc02b806d00156 0x43c03f800f003ff4 0x843c03f800f003ff

def z118 : W := mkw 0x2eedc0287effaa89 0x82eedc0287effaa8 0xbfffc0007fffff8b 0xfbfffc0007fffff8

def z119 : W := mkw 0x000000aa80826634 0x2000000aa8082663 0x600003ff8881e67f 0x9600003ff8881e67

def z120 : W := mkw 0x04684000584c8000 0x004684000584c800 0xacf8c00078ffc00b 0xfacf8c00078ffc00

def z121 : W := mkw 0x4bc6eb87c804c434 0x24bc6eb87c804c43 0x13c7c3878801c072 0x813c7c3878801c07

def z122 : W := mkw 0x0000002a00826210 0x00000002a0082621 0x6008027e488fe67f 0xd6008027e488fe67

def z123 : W := mkw 0x00404088c8068624 0x200404088c806862 0x40c8c399c80e267c 0xd40c8c399c80e267

def z124 : W := mkw 0x01002b8001001566 0x001002b800100156 0x40003f8000003ff4 0x040003f8000003ff

def z125 : W := mkw 0x2eadc000126d8008 0x02eadc000126d800 0x3fffc00000ffc003 0xf3fffc00000ffc00

def z126 : W := mkw 0x4fbebf5500000000 0x04fbebf550000000 0x4cc8ffff80000004 0x44cc8ffff8000000

def z127 : W := mkw 0x0bd23bc46d001566 0x00bd23bc46d00156 0xdff73fe67f003fff 0xfdff73fe67f003ff

def z128 : W := mkw 0x2fedeb007e6d8008 0x02fedeb007e6d800 0xffffff807fffc00f 0xfffffff807fffc00

def z129 : W := mkw 0x2eecc0aafccee63c 0x22eecc0aafccee63 0x6cc8c3fff88fe67f 0xd6cc8c3fff88fe67

def z130 : W := mkw 0x0000002a80826210 0x20000002a8082621 0x0000007f80000000 0x00000007f8000000

def z131 : W := mkw 0x0000000000000000 0x0000000000000000 0x400003ff80000004 0x0400003ff8000000

def z132 : W := mkw 0x0bc02b806d001566 0x00bc02b806d00156 0x03c003800f000070 0x803c003800f00007

def z133 : W := mkw 0x0ff83ff87dda3fe7 0x80ff83ff87dda3fe 0xeff83ff87ffe3ffd 0xfeff83ff87ffe3ff

def z134 : W := mkw 0x0100220001001040 0x0010022000100104 0x830032000f00387c 0xb830032000f00387

def z135 : W := mkw 0x05383ff811da3fe7 0x805383ff811da3fe 0xec383ff870fe3ffd 0x7ec383ff870fe3ff

def z136 : W := mkw 0x643fd455126d8008 0x0643fd455126d800 0x303fc07f80ffc003 0x0303fc07f80ffc00

def z137 : W := mkw 0x1001002203b17851 0x41001002203b1785 0xb33700000ff1f87b 0xbb33700000ff1f87

def z138 : W := mkw 0x004140004a258000 0x0004140004a25800 0xb3ffc0004fffc00b 0xfb3ffc0004fffc00

def z139 : W := mkw 0x0010104000000000 0x0001010400000000 0x0030306000000005 0x3003030600000000

def z140 : W := mkw 0x4eac8d19104a0280 0x84eac8d19104a028 0x4cc8cd99f00e0780 0x44cc8cd99f00e078

def z141 : W := mkw 0x1bd33be66fb17d77 0x41bd33be66fb17d7 0xfff73fe67ff1ffff 0xffff73fe67ff1fff

def z142 : W := mkw 0x0000402a8086e210 0x20000402a8086e21 0x2008c07f808fc003 0x02008c07f808fc00

def z143 : W := mkw 0x0100220001001040 0x0010022000100104 0x8300300007001800 0x2830030000700180

def z144 : W := mkw 0x047854fac886e634 0x2047854fac886e63 0x6cf8ffffc88fe67f 0xf6cf8ffffc88fe67

def z145 : W := mkw 0x1011106203b17851 0x41011106203b1785 0xa03030600ff1f87d 0x3a03030600ff1f87

def z146 : W := mkw 0x0113324402210000 0x0011332440221000 0xb33732660ff1c00f 0xbb33732660ff1c00

def z147 : W := mkw 0x0000002800822200 0x0000000280082220 0x20000000408e2608 0x020000000408e260

def z148 : W := mkw 0x2ac5c0006e258008 0x02ac5c0006e25800 0x13c7c0000f01c002 0x813c7c0000f01c00

def z149 : W := mkw 0x1113324603315851 0x4111332460331585 0x933732060f71d872 0xa933732060f71d87

def z150 : W := mkw 0x2eecc088fc4e862c 0x22eecc088fc4e862 0x4cc8c199f00e0600 0x44cc8c199f00e060

def z151 : W := mkw 0x4eeccdbbc886e634 0x24eeccdbbc886e63 0x6cc8cfffc88fe67f 0xd6cc8cfffc88fe67

def z152 : W := mkw 0x0438145010580881 0x8043814501058088 0xcc303c0070703f8c 0x7cc303c0070703f8

def z153 : W := mkw 0x443e945500000000 0x0443e94550000000 0x50ffc3ff80000007 0xd50ffc3ff8000000

def z154 : W := mkw 0x2eedc0007e6d8008 0x02eedc0007e6d800 0xbf3700007fffc008 0x2bf3700007fffc00

def z155 : W := mkw 0x0000002800822200 0x0000000280082220 0x60c8c3ffc08e260f 0xd60c8c3ffc08e260

def z156 : W := mkw 0x1112367e01927ad1 0xc1112367e01927ad 0x40003e7e00003ff4 0x040003e7e00003ff

def z157 : W := mkw 0x0000000000000000 0x0000000000000000 0x1337000000000003 0xb133700000000000

def z158 : W := mkw 0x0040000048000000 0x0004000004800000 0x00c0000048000008 0xd00c000004800000

def z159 : W := mkw 0x2fedeb007f6d914a 0x02fedeb007f6d914 0xbffffc007fffd98b 0xfbffffc007fffd98

def z160 : W := mkw 0x1113326603b17851 0x41113326603b1785 0xf3fff3ff8ff1f87f 0xff3fff3ff8ff1f87

def z161 : W := mkw 0x01002b8001001566 0x001002b800100156 0xcc003f8070003ffc 0x7cc003f8070003ff

def z162 : W := mkw 0x5fffffffcbb7fe75 0x65fffffffcbb7fe7 0xffffffffcffffe7f 0xfffffffffcffffe7

def z163 : W := mkw 0x00404088c8068624 0x200404088c806862 0x00000000400e0600 0x000000000400e060

def z164 : W := mkw 0x004000a87dda3fe7 0x8004000a87dda3fe 0xa00000007ffe3ff8 0x0a00000007ffe3ff

def z165 : W := mkw 0x11133be603b17d77 0x411133be603b17d7 0xf3373fe60ff1ffff 0xbf3373fe60ff1fff

def z166 : W := mkw 0x2ead800036690008 0x02ead80003669000 0xbf3f000077fe0009 0x7bf3f000077fe000

def z167 : W := mkw 0x0438147010d82881 0x80438147010d8288 0xac303c6030f0398d 0x3ac303c6030f0398

def z168 : W := mkw 0x000000aa80826634 0x2000000aa8082663 0x400003ff80002674 0x0400003ff8000267

def z169 : W := mkw 0x1112326601907851 0x4111232660190785 0x0000326600003874 0x0000032660000387

def z170 : W := mkw 0x5b87ab0703215050 0x45b87ab070321505 0x13c7c3878f01c072 0x813c7c3878f01c07

def z171 : W := mkw 0x00404088c8068624 0x200404088c806862 0x40c8c3ffc00e0607 0xd40c8c3ffc00e060

def z172 : W := mkw 0x1113726e83b7fa51 0x61113726e83b7fa5 0xb33ff27f8ffff87f 0xbb33ff27f8ffff87

def z173 : W := mkw 0x0001002202a16010 0x00001002202a1601 0xb33702660ff1e07f 0xbb33702660ff1e07

def z174 : W := mkw 0x3fbfb26637f97859 0x43fbfb26637f9785 0xbf3732663ff1f87f 0xbbf3732663ff1f87

def z175 : W := mkw 0x0bc02b806d001566 0x00bc02b806d00156 0x83c033800f00387c 0xb83c033800f00387

def z176 : W := mkw 0x246dc0007e6d8008 0x0246dc0007e6d800 0xb03fc0007fffc00b 0x0b03fc0007fffc00

def z177 : W := mkw 0x0000000000000000 0x0000000000000000 0x4008007800000005 0x5400800780000000

def z178 : W := mkw 0x0000002200806010 0x0000000220080601 0x200000000881e078 0x0200000000881e07

def z179 : W := mkw 0x0000002800922a81 0x80000002800922a8 0x0000000000003f80 0x00000000000003f8

def z180 : W := mkw 0x4ebc9d7910da2a81 0x84ebc9d7910da2a8 0xecf8fdf9f0fe3f8d 0x7ecf8fdf9f0fe3f8

def z181 : W := mkw 0x3ffff2667ffdf859 0x43ffff2667ffdf85 0xbffff2667ffff87f 0xfbffff2667ffff87

def z182 : W := mkw 0x0000000000000000 0x0000000000000000 0x8c00000070000008 0x78c0000007000000

def z183 : W := mkw 0x453ebf5500000000 0x0453ebf550000000 0x503fffff80000007 0x0503fffff8000000

def z184 : W := mkw 0x0112324400000000 0x0011232440000000 0x0000326600000004 0x0000032660000000

def z185 : W := mkw 0x0428002810ca2200 0x00428002810ca220 0xec38007870fe260d 0x7ec38007870fe260

def z186 : W := mkw 0x04280418104a0280 0x804280418104a028 0x4c080c18700e0780 0x44c080c18700e078

def z187 : W := mkw 0x1103220603215050 0x4110322060321505 0xb33702060ff1c07b 0xbb33702060ff1c07

def z188 : W := mkw 0x4ebe9d5500000000 0x04ebe9d550000000 0x5cffcdff80000003 0x45cffcdff8000000

def z189 : W := mkw 0x5fbfbf7702b16811 0x45fbfbf7702b1681 0x7fffffff80f1c007 0xf7fffffff80f1c00

def z190 : W := mkw 0x047814f87dda3fe7 0x8047814f87dda3fe 0xec383c787ffe3ffd 0x7ec383c787ffe3ff

def z191 : W := mkw 0x153b367c13fb3ac1 0xc153b367c13fb3ac 0xff3f3c7877fe3f8d 0x7ff3f3c7877fe3f8

def z192 : W := mkw 0x0438147810da2a81 0x80438147810da2a8 0xcc303c7830703f84 0x2cc303c7830703f8

def z193 : W := mkw 0x153b3654137918c1 0xc153b3654137918c 0x9f373c0037701980 0x29f373c003770198

def z194 : W := mkw 0x00404082c804c434 0x200404082c804c43 0x000000000801c070 0x0000000000801c07

def z195 : W := mkw 0x1013104402310801 0x4101310440231080 0x1037000000700000 0x0103700000070000

def z196 : W := mkw 0x4fbebfff80826634 0x24fbebfff8082663 0x5fffffff80002677 0xf5fffffff8000267

def z197 : W := mkw 0x51123f7701907851 0x451123f770190785 0x40003fff80003874 0x040003fff8000387

def z198 : W := mkw 0x2eedc0007e6d8008 0x02eedc0007e6d800 0xfffffc007fffff8f 0xffffffc007fffff8

def z199 : W := mkw 0x2efdd4787effaa89 0x82efdd4787effaa8 0xfffffc787fffff8f 0xffffffc787fffff8

def z200 : W := mkw 0x0438147810da2a81 0x80438147810da2a8 0xa038007870fe3f89 0x0a038007870fe3f8

def z201 : W := mkw 0x004040aac886e634 0x2004040aac886e63 0x20c8c3ff888fc073 0x820c8c3ff888fc07

def z202 : W := mkw 0x0ebc945000000000 0x00ebc94500000000 0x5ffffc7800000007 0xf5ffffc780000000

def z203 : W := mkw 0x4fecaf916d001566 0x04fecaf916d00156 0xcfc8ff99ff003ffc 0xfcfc8ff99ff003ff

def z204 : W := mkw 0x2eedc0807e6d842c 0x02eedc0807e6d842 0xffffc3807fffe67f 0xfffffc3807fffe67

def z205 : W := mkw 0x004000a848822624 0x0004000a84882262 0x60c803f8488e267d 0xd60c803f8488e267

def z206 : W := mkw 0x2005c00002258008 0x02005c0000225800 0x1007c0000001c002 0x01007c0000001c00

def z207 : W := mkw 0x4ffebfd56d001566 0x04ffebfd56d00156 0x5fffffff8f000077 0xf5fffffff8f00007

def z208 : W := mkw 0x005050eac896ee35 0x2005050eac896ee3 0xe0f8f3ffc8fffe7f 0xfe0f8f3ffc8fffe7

def z209 : W := mkw 0x01002baa81827776 0x201002baa8182777 0x40003fff80003ff4 0x040003fff80003ff

def z210 : W := mkw 0x4ffeffddc8068624 0x24ffeffddc806862 0x5fffffffc00e0607 0xf5fffffffc00e060

def z211 : W := mkw 0x1103220603215050 0x4110322060321505 0x930732060f01f87e 0xb930732060f01f87

def z212 : W := mkw 0x0000002200806010 0x0000000220080601 0x0000026600002074 0x0000002660000207

def z213 : W := mkw 0x2eedc0007e6d8008 0x02eedc0007e6d800 0xffffc3ffffffc00f 0xfffffc3ffffffc00

def z214 : W := mkw 0x4fbebf5500000000 0x04fbebf550000000 0xdffffffff0003f8f 0xfdffffffff0003f8

def z215 : W := mkw 0x0438145000000000 0x0043814500000000 0x0038007800000001 0x0003800780000000

def z216 : W := mkw 0x0bc06baaed86f776 0x20bc06baaed86f77 0xefc8ffffff8fffff 0xfefc8ffffff8ffff

def z217 : W := mkw 0x443ed47f8086e210 0x2443ed47f8086e21 0x303fc07f808fc003 0x0303fc07f808fc00

def z218 : W := mkw 0x1113324403311841 0x4111332440331184 0xb33730000ff1d80b 0xbb33730000ff1d80

def z219 : W := mkw 0x0a84800000000000 0x00a8480000000000 0x13c7c00000000002 0x813c7c0000000000

def z220 : W := mkw 0x0040008048000424 0x0004000804800042 0xccc03f8078003ffc 0xfccc03f8078003ff

def z221 : W := mkw 0x0100220001001040 0x0010022000100104 0xcf003e007f003ffc 0xfcf003e007f003ff

def z222 : W := mkw 0x0ac000006c000000 0x00ac000006c00000 0x0cc0000070000000 0x40cc000007000000

def z223 : W := mkw 0x1012106600906811 0x4101210660090681 0x0000006600000000 0x0000000660000000

def z224 : W := mkw 0x0000400880068200 0x2000040088006820 0x0008c019800e0000 0x00008c019800e000

def z225 : W := mkw 0x04280418104a0280 0x804280418104a028 0xcc083c18700e3f8c 0x7cc083c18700e3f8

def z226 : W := mkw 0x0010147800922a81 0x80010147800922a8 0xcc003c7870003f8c 0x7cc003c7870003f8

def z227 : W := mkw 0x443e947d10da2a81 0x8443e947d10da2a8 0xfc3ffc7ff0fe3f8f 0x7fc3ffc7ff0fe3f8

def z228 : W := mkw 0x0438145000000000 0x0043814500000000 0x4cf8ffff80000007 0xf4cf8ffff8000000

def z229 : W := mkw 0x4fbebf7500902801 0x04fbebf750090280 0xffffffff80f0380f 0xfffffffff80f0380

def z230 : W := mkw 0x41123f7d00922a81 0x841123f7d00922a8 0x40003fff80003f84 0x040003fff80003f8

def z231 : W := mkw 0x447ed4ffc886e634 0x2447ed4ffc886e63 0x70ffc3ffc88fe67f 0xd70ffc3ffc88fe67

def z232 : W := mkw 0x1113326603b17851 0x41113326603b1785 0xa00032660ff1f87c 0x0a00032660ff1f87

def z233 : W := mkw 0x04381458105a0a81 0x804381458105a0a8 0xcc383c18707e1f80 0x6cc383c18707e1f8

def z234 : W := mkw 0x0110326001903841 0x0011032600190384 0xa33032600ff0387d 0xba33032600ff0387

def z235 : W := mkw 0x0a80000000000000 0x00a8000000000000 0x0fc0000000000000 0xf0fc000000000000

def z236 : W := mkw 0x2eedc0807f6d956e 0x02eedc0807f6d956 0xbfffc0007ffffffb 0xfbfffc0007ffffff

def z237 : W := mkw 0x0438147810da2a81 0x80438147810da2a8 0x2038007800fe0001 0x02038007800fe000

def z238 : W := mkw 0x1013106603b17851 0x41013106603b1785 0xb03700660ff1f87b 0x0b03700660ff1f87

def z239 : W := mkw 0x0000000800020200 0x0000000080002020 0x40080018400e0600 0x440080018400e060

def z240 : W := mkw 0x4fbebf5500000000 0x04fbebf550000000 0x1f3ffc7f80000003 0x21f3ffc7f8000000

def z241 : W := mkw 0x2eedc0007e6d8008 0x02eedc0007e6d800 0xacc8c0007fffc008 0x4acc8c0007fffc00

def z242 : W := mkw 0x1113326e03b37a51 0x41113326e03b37a5 0xf33f327e4ffffe7f 0xff33f327e4ffffe7

def z243 : W := mkw 0x4ffeffffed86f776 0x24ffeffffed86f77 0xffffffffff8fffff 0xfffffffffff8ffff

def z244 : W := mkw 0x0bc02b006d001142 0x00bc02b006d00114 0x8fc03c007f001988 0xf8fc03c007f00198

def z245 : W := mkw 0x0ac009806c000526 0x00ac009806c00052 0xccc03d8070003f8c 0x7ccc03d8070003f8

def z246 : W := mkw 0x3bd7f2666fb5f859 0x43bd7f2666fb5f85 0xb3f7f2660ff1f87f 0xbb3f7f2660ff1f87

def z247 : W := mkw 0x0000000000000000 0x0000000000000000 0x200000000881c00b 0x9200000000881c00

def z248 : W := mkw 0x2bc5eb806f25956e 0x02bc5eb806f25956 0xdfc7ff807f01fffe 0xfdfc7ff807f01fff

def z249 : W := mkw 0x1113326603b17851 0x41113326603b1785 0xff373e667ff1ffff 0xfff373e667ff1fff

def z250 : W := mkw 0x00404082c804c434 0x200404082c804c43 0x40c0c387c801e67e 0xd40c0c387c801e67

def z251 : W := mkw 0x0000000000000000 0x0000000000000000 0xa030000000f00009 0x3a030000000f0000

def z252 : W := mkw 0x143b147e12fb6a91 0xc143b147e12fb6a9 0xfc3f3c7e70ffff8f 0x7fc3f3c7e70ffff8

def z253 : W := mkw 0x0428043810ca2280 0x80428043810ca228 0x6c080c78708e278d 0x56c080c78708e278

def z254 : W := mkw 0x4eac8d1100000000 0x04eac8d110000000 0x5fffcd9980000003 0xf5fffcd998000000

def z255 : W := mkw 0x41123f5500000000 0x041123f550000000 0x40003fff80000004 0x040003fff8000000

def z256 : W := mkw 0x0bd03be06d903d67 0x00bd03be06d903d6 0xeff03fe07ff03ffd 0xfeff03fe07ff03ff

def z257 : W := mkw 0x204140287effaa89 0x8204140287effaa8 0xa00000007fffff88 0x0a00000007fffff8

def z258 : W := mkw 0x0ac000006c000000 0x00ac000006c00000 0x8fc000007f000008 0xf8fc000007f00000

def z259 : W := mkw 0x7fffff777ffdf859 0x47fffff777ffdf85 0xfffffffffffff87f 0xffffffffffffff87

def z260 : W := mkw 0x0000002800822200 0x0000000280082220 0x60080078408e260d 0x560080078408e260

def z261 : W := mkw 0x0fecab806d001566 0x00fecab806d00156 0xdfffff807f003fff 0xfdfffff807f003ff

def z262 : W := mkw 0x0bc06b82ed04d576 0x20bc06b82ed04d57 0xcfc0ff87ff01fffe 0xfcfc0ff87ff01fff

def z263 : W := mkw 0x0000000010580881 0x8000000001058088 0x8000000030701980 0x0800000003070198

def z264 : W := mkw 0x005054fac896eeb5 0xa005054fac896eeb 0x60c8ffffc88fffff 0xd60c8ffffc88ffff

def z265 : W := mkw 0x2ac5c0aaeea7e63c 0x22ac5c0aaeea7e63 0x73cfc3ffcf8fe67f 0xd73cfc3ffcf8fe67

def z266 : W := mkw 0x0b802b0000000000 0x00b802b000000000 0x4fc03f8000000004 0xf4fc03f800000000

def z267 : W := mkw 0x004040aac886e634 0x2004040aac886e63 0x60c8c199c88fe678 0x460c8c199c88fe67

def z268 : W := mkw 0x0ac04988ec068726 0x20ac04988ec06872 0x4cc8cd99f00e0780 0x44cc8cd99f00e078

def z269 : W := mkw 0x0112326600806010 0x0011232660080601 0x333732660881e07f 0xb333732660881e07

def z270 : W := mkw 0x1113326602b16811 0x41113326602b1681 0x3337326600f1c007 0xb3337326600f1c00

def z271 : W := mkw 0x015272eec886e634 0x2015272eec886e63 0x73fff3ffc88fe67f 0xf73fff3ffc88fe67

def z272 : W := mkw 0x0ff83fd07d581de7 0x80ff83fd07d581de 0xcff03f807f703ffc 0xfcff03f807f703ff

def z273 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000026600000007 0x9000002660000000

def z274 : W := mkw 0x0010147810da2a81 0x80010147810da2a8 0xe0003c7870fe3f8c 0x0e0003c7870fe3f8

def z275 : W := mkw 0x004040aaed86f776 0x2004040aaed86f77 0xa00000007f8ffff8 0x0a00000007f8ffff

def z276 : W := mkw 0x4fbebf5500000000 0x04fbebf550000000 0x1f373e6600000007 0xb1f373e660000000

def z277 : W := mkw 0x4fbebf5500000000 0x04fbebf550000000 0x5f373fff80000004 0x25f373fff8000000

def z278 : W := mkw 0x2eecc9807c4c852e 0x02eecc9807c4c852 0x4cc8cd80700e0780 0x44cc8cd80700e078

def z279 : W := mkw 0x0428043810da2a81 0x80428043810da2a8 0xec080c1870fe3f88 0x4ec080c1870fe3f8

def z280 : W := mkw 0x4fbebf5500000000 0x04fbebf550000000 0x1ff7ff8780000002 0xa1ff7ff878000000

def z281 : W := mkw 0x0010106000902801 0x0001010600090280 0xa030306000f0380d 0x3a030306000f0380

def z282 : W := mkw 0x2efdd0607efda809 0x02efdd0607efda80 0xbffff0607ffff80f 0xfbffff0607ffff80

def z283 : W := mkw 0x0010147800922a81 0x80010147800922a8 0xe0303c7800f03f8d 0x3e0303c7800f03f8

def z284 : W := mkw 0x0428000010480000 0x0042800001048000 0x8c30000030700000 0x28c3000003070000

def z285 : W := mkw 0x053a365400000000 0x0053a36540000000 0x5f3f3e7e00000007 0xf5f3f3e7e0000000

def z286 : W := mkw 0x004000806d001566 0x0004000806d00156 0xcc003c007f003ffc 0x7cc003c007f003ff

def z287 : W := mkw 0x2eedc9807e6d852e 0x02eedc9807e6d852 0xffffcd807fffc78b 0xfffffcd807fffc78

def z288 : W := mkw 0x0000002800822200 0x0000000280082220 0x20080078008e0001 0x020080078008e000

def z289 : W := mkw 0x0010106800922a01 0x00010106800922a0 0xe038307840fe3e0d 0x7e038307840fe3e0

def z290 : W := mkw 0x0100220001001040 0x0010022000100104 0x0000320000003874 0x0000032000000387

def z291 : W := mkw 0x0438147810da2a81 0x80438147810da2a8 0xecf8fffff0fe3f8f 0xfecf8fffff0fe3f8

def z292 : W := mkw 0x204140007e6d8008 0x0204140007e6d800 0xa0c8c0007fffc00b 0xda0c8c0007fffc00

def z293 : W := mkw 0x0112324400000000 0x0011232440000000 0x1337300000000000 0x2133730000000000

def z294 : W := mkw 0x4fbebf5500000000 0x04fbebf550000000 0x13ffc3ff80000003 0x813ffc3ff8000000

def z295 : W := mkw 0x3ffffbe67ffdfd7f 0x43ffffbe67ffdfd7 0xffffffe67fffffff 0xfffffffe67ffffff

def z296 : W := mkw 0x4fbebf5525001142 0x04fbebf552500114 0xdfffffffb7001987 0xfdfffffffb700198

def z297 : W := mkw 0x105350eecab7ee35 0x6105350eecab7ee3 0x70ffc3ffc8ffe67f 0xd70ffc3ffc8ffe67

def z298 : W := mkw 0x4ffebfd56d001566 0x04ffebfd56d00156 0xdff73f807f003ffc 0xfdff73f807f003ff

def z299 : W := mkw 0x0000000001001040 0x0000000000100104 0x800000000f003878 0x0800000000f00387

def z300 : W := mkw 0x0000000000000000 0x0000000000000000 0x8c003c0030001980 0x28c003c003000198

def z301 : W := mkw 0x0eecc00048048000 0x00eecc0004804800 0x3fffc000488fc00b 0xf3fffc000488fc00

def z302 : W := mkw 0x2ffdfff87fffbfef 0x82ffdfff87fffbfe 0xfffffff87fffffff 0xffffffff87ffffff

def z303 : W := mkw 0x042c800000000000 0x0042c80000000000 0x103fc00000000003 0x0103fc0000000000

def z304 : W := mkw 0x0fb83f7810da2a81 0x80fb83f7810da2a8 0xeff83ff870fe3f8d 0xfeff83ff870fe3f8

def z305 : W := mkw 0x242dc000126d8008 0x0242dc000126d800 0xbc3fc00070ffc00b 0x7bc3fc00070ffc00

def z306 : W := mkw 0x153b367603b17851 0x4153b367603b1785 0xff3f3e7e0ff1f87f 0xfff3f3e7e0ff1f87

def z307 : W := mkw 0x242dc000126d8008 0x0242dc000126d800 0xb33fc0000fffc00b 0xbb33fc0000fffc00

def z308 : W := mkw 0x004000a248806434 0x0004000a24880643 0x60c003e64881e67f 0xd60c003e64881e67

def z309 : W := mkw 0x0b923b4400000000 0x00b923b440000000 0x5ff73fe600000007 0xf5ff73fe60000000

def z310 : W := mkw 0x0ac009806c000526 0x00ac009806c00052 0x4cc00d8070000780 0x44cc00d807000078

def z311 : W := mkw 0x4fbebf5510480000 0x04fbebf551048000 0xfffffffff0fe000f 0xffffffffff0fe000

def z312 : W := mkw 0x353ff26613fdf859 0x4353ff26613fdf85 0xb33ff2660ffff87f 0xbb33ff2660ffff87

def z313 : W := mkw 0x0ac009806c000526 0x00ac009806c00052 0xcfc00d807f000788 0xfcfc00d807f00078

def z314 : W := mkw 0x1000002201907851 0x4100000220190785 0x0000000000003870 0x0000000000000387

def z315 : W := mkw 0x4bd23fd56d001566 0x04bd23fd56d00156 0xcfc03fffff003ffc 0xfcfc03fffff003ff

def z316 : W := mkw 0x0bc02ba86d823766 0x00bc02ba86d82376 0xefc83ff87f8e3ffd 0xfefc83ff87f8e3ff

def z317 : W := mkw 0x0000002810da2a81 0x80000002810da2a8 0x2000000000fe0000 0x02000000000fe000

def z318 : W := mkw 0x3effd0667efde819 0x43effd0667efde81 0xbfffc0667fffc00b 0xfbfffc0667fffc00

def z319 : W := mkw 0x204140007e6d8008 0x0204140007e6d800 0xb33700007fffc00b 0xbb33700007fffc00

def z320 : W := mkw 0x0428002810da2a81 0x80428002810da2a8 0xac38000070fe3f89 0x7ac38000070fe3f8

def z321 : W := mkw 0x0bc02b806d001566 0x00bc02b806d00156 0x8f003c007f003ff8 0x28f003c007f003ff

def z322 : W := mkw 0x1101222203b17851 0x41101222203b1785 0xa30032000ff1f87c 0xba30032000ff1f87

def z323 : W := mkw 0x004040aad8deeeb5 0xa004040aad8deeeb 0xa000000078fffff8 0x0a000000078fffff

def z324 : W := mkw 0x242dc02a92efe218 0x2242dc02a92efe21 0x303fc07f80ffc003 0x0303fc07f80ffc00

def z325 : W := mkw 0x41123fd501001566 0x041123fd50100156 0x40003fff80003ff4 0x040003fff80003ff

def z326 : W := mkw 0x00404088c8068624 0x200404088c806862 0x60c8c199c88fc60b 0xd60c8c199c88fc60

def z327 : W := mkw 0x2efdd4787effaa89 0x82efdd4787effaa8 0xbfffc0787fffc00b 0xfbfffc0787fffc00

def z328 : W := mkw 0x1113324603215050 0x4111332460321505 0x133732660f01c077 0xb133732660f01c07

def z329 : W := mkw 0x4bc6ebafc886e634 0x24bc6ebafc886e63 0x73cfc3ffc88fe67f 0xd73cfc3ffc88fe67

def z330 : W := mkw 0x5fffbff76fb17d77 0x45fffbff76fb17d7 0xfffffffffff1ffff 0xffffffffffff1fff

def z331 : W := mkw 0x3fbfb24437791849 0x43fbfb2443779184 0x9f37300037701800 0x29f3730003770180

def z332 : W := mkw 0x343fd06612fde819 0x4343fd06612fde81 0x303fc06600ffc003 0x0303fc06600ffc00

def z333 : W := mkw 0x000040028004c010 0x2000040028004c01 0x0000c0078001c002 0x00000c0078001c00

def z334 : W := mkw 0x0a80090024000102 0x00a8009002400010 0x0c000c0030000180 0x00c000c003000018

def z335 : W := mkw 0x0a80090000000000 0x00a8009000000000 0x4cc00d8000000000 0x44cc00d800000000

def z336 : W := mkw 0x2eecc0007c4c8008 0x02eecc0007c4c800 0x2cc8c000788fc00b 0xd2cc8c000788fc00

def z337 : W := mkw 0x0eac800000000000 0x00eac80000000000 0x1f37000000000000 0x21f3700000000000

def z338 : W := mkw 0x2bc16b807f6d956e 0x02bc16b807f6d956 0xefc03f807ffffffc 0xfefc03f807ffffff

def z339 : W := mkw 0x2fedebaaffeff77e 0x22fedebaaffeff77 0xffffffffffffffff 0xffffffffffffffff

def z340 : W := mkw 0x111232ee81927e75 0x6111232ee81927e7 0x400033ff80003e74 0x0400033ff80003e7

def z341 : W := mkw 0x0fe82f987d4a17e6 0x80fe82f987d4a17e 0xcfc83f987f0e3ffc 0xfcfc83f987f0e3ff

def z342 : W := mkw 0x0112324401001040 0x0011232440100104 0x933732660f00387f 0xb933732660f00387

def z343 : W := mkw 0x0438147810da2a81 0x80438147810da2a8 0x6c383c7800fe0005 0x76c383c7800fe000

def z344 : W := mkw 0x0438147810da2a81 0x80438147810da2a8 0x4c083c78700e3f84 0x44c083c78700e3f8

def z345 : W := mkw 0x143b147e12fb6a91 0xc143b147e12fb6a9 0x303f007e00ffc003 0x0303f007e00ffc00

def z346 : W := mkw 0x51133f7703b17851 0x451133f7703b1785 0xf3373fff8ff1f87f 0xbf3373fff8ff1f87

def z347 : W := mkw 0x0428041010480080 0x8042804101048008 0x0c000c0030000180 0x00c000c003000018

def z348 : W := mkw 0x6fffff557e6d8008 0x06fffff557e6d800 0xbffffc007fffc00b 0xfbffffc007fffc00

def z349 : W := mkw 0x0000000000000000 0x0000000000000000 0x40003c0000003f84 0x040003c0000003f8

def z350 : W := mkw 0x4012145500000000 0x0401214550000000 0x0000007f80000000 0x00000007f8000000

def z351 : W := mkw 0x0bc022006d001040 0x00bc022006d00104 0x8fc032007f00387c 0xf8fc032007f00387

def z352 : W := mkw 0x443e947d10da2a81 0x8443e947d10da2a8 0x303fc07f80fe0003 0x0303fc07f80fe000

def z353 : W := mkw 0x0000000200004010 0x0000000020000401 0x000002060801c072 0x8000002060801c07

def z354 : W := mkw 0x204140807f6d956e 0x0204140807f6d956 0xa00000007ffffff8 0x0a00000007ffffff

def z355 : W := mkw 0x4fbfbf5502210000 0x04fbfbf550221000 0xffffffff8ff1c00f 0xfffffffff8ff1c00

def z356 : W := mkw 0x004040aac886e634 0x2004040aac886e63 0x20c0c387c88fe67a 0x820c0c387c88fe67

def z357 : W := mkw 0x004040aac886e634 0x2004040aac886e63 0x60c00380488fe67c 0xd60c00380488fe67

def z358 : W := mkw 0x0ee800007c480000 0x00ee800007c48000 0xaff800007ffe0009 0xfaff800007ffe000

def z359 : W := mkw 0x0010106000902801 0x0001010600090280 0x0000306000003804 0x0000030600000380

def z360 : W := mkw 0x315372667ffdf859 0x4315372667ffdf85 0xb33732667ffff87f 0xbb33732667ffff87

def z361 : W := mkw 0x4ffebfd56c000526 0x04ffebfd56c00052 0x5ffffffff0000787 0xf5ffffffff000078

def z362 : W := mkw 0x0000002200806010 0x0000000220080601 0x60c8c3ff8881e07f 0xd60c8c3ff8881e07

def z363 : W := mkw 0x1bd33bc46f311d67 0x41bd33bc46f311d6 0xdff73f807f703ffc 0xfdff73f807f703ff

def z364 : W := mkw 0x01103ff801923fe7 0x801103ff801923fe 0x40003ff800003ff4 0x040003ff800003ff

def z365 : W := mkw 0x0429000012690000 0x0042900001269000 0xbf3f00007fffc00b 0xfbf3f00007fffc00

def z366 : W := mkw 0x4bc6ab856d001566 0x04bc6ab856d00156 0xdfc7ff87ff003ffe 0xfdfc7ff87ff003ff

def z367 : W := mkw 0x000040aa8086e634 0x2000040aa8086e63 0x6008c3ff808fe677 0x06008c3ff808fe67

def z368 : W := mkw 0x0438147800822200 0x0043814780082220 0x6c383c78408e260d 0x76c383c78408e260

def z369 : W := mkw 0x0eac800000000000 0x00eac80000000000 0x5fffc3ff80000007 0xf5fffc3ff8000000

def z370 : W := mkw 0x2ac140007e6d8008 0x02ac140007e6d800 0xafc000007fffc008 0xfafc000007fffc00

def z371 : W := mkw 0x4eac8d1100000000 0x04eac8d110000000 0x0c000c0000000000 0x00c000c000000000

def z372 : W := mkw 0x0b802b0025001142 0x00b802b002500114 0xcfc03f8037001984 0xfcfc03f803700198

def z373 : W := mkw 0x0ff83fd06d001566 0x00ff83fd06d00156 0xcff83ff87f003ffd 0xfcff83ff87f003ff

def z374 : W := mkw 0x00404082c804c434 0x200404082c804c43 0x40c8c3ff8801c077 0xd40c8c3ff8801c07

def z375 : W := mkw 0x104140aacbb7fe75 0x6104140aacbb7fe7 0xa00000004ffffe78 0x0a00000004ffffe7

def z376 : W := mkw 0x6ffffffffeefe63c 0x26ffffffffeefe63 0xffffffffffffe67f 0xfffffffffffffe67

def z377 : W := mkw 0x204140aafeefe63c 0x2204140aafeefe63 0xa00000007fffe678 0x0a00000007fffe67

def z378 : W := mkw 0x41022b0500000000 0x041022b050000000 0x0000038780000000 0x0000003878000000

def z379 : W := mkw 0x3bc7e2066f25d058 0x43bc7e2066f25d05 0x13c7c2060f01c072 0x813c7c2060f01c07

def z380 : W := mkw 0x157b76fedbfffef5 0xe157b76fedbfffef 0xffffffffffffffff 0xffffffffffffffff

def z381 : W := mkw 0x0438145010580881 0x8043814501058088 0xcc383c7830701985 0x7cc383c783070198

def z382 : W := mkw 0x0bc02ba87dda3fe7 0x80bc02ba87dda3fe 0xefc03f807ffe3ffc 0xfefc03f807ffe3ff

def z383 : W := mkw 0x0438147810da2a81 0x80438147810da2a8 0x60383c7800fe3f85 0x060383c7800fe3f8

def z384 : W := mkw 0x0040408048048424 0x0004040804804842 0x60c8c380488fe67f 0xd60c8c380488fe67

def z385 : W := mkw 0x004040aac886e634 0x2004040aac886e63 0x20c8c000488fe67b 0xd20c8c000488fe67

def z386 : W := mkw 0x0000000000000000 0x0000000000000000 0x4c000c0070000780 0x44c000c007000078

def z387 : W := mkw 0x0eac800010480000 0x00eac80001048000 0xbfffc00070fe000b 0xfbfffc00070fe000

def z388 : W := mkw 0x115372e6cbb5fc75 0x6115372e6cbb5fc7 0xb3f7f3e78ff1f87f 0xbb3f7f3e78ff1f87

def z389 : W := mkw 0x00404080c8048424 0x200404080c804842 0x00c0c18180000000 0x000c0c1818000000

def z390 : W := mkw 0x0000002200806010 0x0000000220080601 0x200000660081c003 0x0200000660081c00

def z391 : W := mkw 0x0100220001001040 0x0010022000100104 0x030002000f000070 0x8030002000f00007

def z392 : W := mkw 0x01002b0000000000 0x001002b000000000 0x40003f8000000004 0x040003f800000000

def z393 : W := mkw 0x0040400048048000 0x0004040004804800 0x00c8c000400e0000 0x400c8c000400e000

def z394 : W := mkw 0x004040284886a200 0x0004040284886a20 0x60c8c078488fe60f 0xd60c8c078488fe60

def z395 : W := mkw 0x1103222603b17851 0x41103222603b1785 0xb30702060ff1f87a 0x8b30702060ff1f87

def z396 : W := mkw 0x453eb65500000000 0x0453eb6550000000 0x133ff27f80000007 0xb133ff27f8000000

def z397 : W := mkw 0x04280418104a0280 0x804280418104a028 0xec380c1870fe0789 0x7ec380c1870fe078

def z398 : W := mkw 0x247954787effaa89 0x8247954787effaa8 0xec383c787fffff8d 0x7ec383c787fffff8

def z399 : W := mkw 0x4fbebf7700806010 0x04fbebf770080601 0x7fffffff8881e07f 0xf7fffffff8881e07

def z400 : W := mkw 0x0000041800020280 0x8000004180002028 0x40000c1800000780 0x040000c180000078

def z401 : W := mkw 0x1bc32b866f215576 0x41bc32b866f21557 0xdfc73f867f01fffe 0xfdfc73f867f01fff

def z402 : W := mkw 0x0010145000000000 0x0001014500000000 0x40003c7800000004 0x040003c780000000

def z403 : W := mkw 0x0010106200906811 0x0001010620090681 0xa030326608f1f87f 0xba030326608f1f87

def z404 : W := mkw 0x2eedc0007e6d8008 0x02eedc0007e6d800 0x9fffc000777e0000 0x69fffc000777e000

def z405 : W := mkw 0x6eeccd117c4c8008 0x06eeccd117c4c800 0x4cc8cd99f00e0000 0x44cc8cd99f00e000

def z406 : W := mkw 0x242d800012690008 0x0242d80001269000 0x1037000000700000 0x0103700000070000

def z407 : W := mkw 0x1013106602b16811 0x41013106602b1681 0xb33700660ff1c00b 0xbb33700660ff1c00

def z408 : W := mkw 0x0040008048000424 0x0004000804800042 0x40c0018040000600 0x440c001804000060

def z409 : W := mkw 0x0000008880020624 0x2000000888002062 0x4000019980000600 0x0400001998000060

def z410 : W := mkw 0x0bc06b806d049566 0x00bc06b806d04956 0xefc8ff807f8fffff 0xfefc8ff807f8ffff

def z411 : W := mkw 0x4ffeff5548048000 0x04ffeff554804800 0x7fffffffc88fc00f 0xf7fffffffc88fc00

def z412 : W := mkw 0x004040aac886e634 0x2004040aac886e63 0xecc8fffff88fffff 0xfecc8fffff88ffff

def z413 : W := mkw 0x2ac5c0006e258008 0x02ac5c0006e25800 0xb3f7c0000ff1c00b 0xbb3f7c0000ff1c00

def z414 : W := mkw 0x1b933b6627b17953 0x41b933b6627b1795 0xbf373e663ff1f9ff 0xbbf373e663ff1f9f

def z415 : W := mkw 0x0b802b0000000000 0x00b802b000000000 0x03c0038000000000 0x803c003800000000

def z416 : W := mkw 0x0438147800922a81 0x80438147800922a8 0x4c383c7800003f85 0x74c383c7800003f8

def z417 : W := mkw 0x0040008048000424 0x0004000804800042 0x00c0038008000070 0x800c003800800007

def z418 : W := mkw 0x4fbebf5501001040 0x04fbebf550100104 0xdfffffff8f00387f 0xfdfffffff8f00387

def z419 : W := mkw 0x4ffeffd7c804c434 0x24ffeffd7c804c43 0x5fffffff8801c077 0xf5fffffff8801c07

def z420 : W := mkw 0x0ac000806c000424 0x00ac000806c00042 0xcfc003807f00267c 0xfcfc003807f00267

def z421 : W := mkw 0x0010147800922a81 0x80010147800922a8 0x0000007800000000 0x0000000780000000

def z422 : W := mkw 0x243dd47812ffaa89 0x8243dd47812ffaa8 0x303fc07800ffc003 0x0303fc07800ffc00

def z423 : W := mkw 0x1113326603b17851 0x41113326603b1785 0xb337306607f1d803 0x2b337306607f1d80

def z424 : W := mkw 0x1001002a13fb7ad1 0xc1001002a13fb7ad 0xa00000007ffffff8 0x0a00000007ffffff

def z425 : W := mkw 0x000000aa80826634 0x2000000aa8082663 0x600803ffc08e267d 0x5600803ffc08e267

def z426 : W := mkw 0x0428000010480000 0x0042800001048000 0x0c080000700e0000 0x40c080000700e000

def z427 : W := mkw 0x5b97bb6703b17851 0x45b97bb6703b1785 0xb3f7f3e78ff1f87f 0xbb3f7f3e78ff1f87

def z428 : W := mkw 0x047854fad8deeeb5 0xa047854fad8deeeb 0xec383c7878fffffd 0x7ec383c7878fffff

def z429 : W := mkw 0x0000000000000000 0x0000000000000000 0x4c003c0000000004 0x74c003c000000000

def z430 : W := mkw 0x2ffff2447e6d8008 0x02ffff2447e6d800 0xbffff2667fffc00f 0xfbffff2667fffc00

def z431 : W := mkw 0x2ead800036690008 0x02ead80003669000 0x9fffc00037700003 0xf9fffc0003770000

def z432 : W := mkw 0x0040408ac806c634 0x20040408ac806c63 0x40c8c39fc80fc672 0xc40c8c39fc80fc67

def z433 : W := mkw 0x0eecc0aac886e634 0x20eecc0aac886e63 0x7fffc3ffc88fe67f 0xf7fffc3ffc88fe67

def z434 : W := mkw 0x0438547a90deea91 0xa0438547a90deea9 0x2038c07f80ffc003 0x02038c07f80ffc00

def z435 : W := mkw 0x104100a26fb17d77 0x4104100a26fb17d7 0xa00000007ff1fff8 0x0a00000007ff1fff

def z436 : W := mkw 0x0101220003211040 0x0010122000321104 0xb33732000ff1f87f 0xbb33732000ff1f87

def z437 : W := mkw 0x4fbebfd501001566 0x04fbebfd50100156 0x5fffffff80003ff7 0xf5fffffff80003ff

def z438 : W := mkw 0x0bc06b82ed04d576 0x20bc06b82ed04d57 0x03c0c3878f01c072 0x803c0c3878f01c07

def z439 : W := mkw 0x0438106010d82801 0x00438106010d8280 0xac38306070fe380d 0x7ac38306070fe380

def z440 : W := mkw 0x4b96bf5500000000 0x04b96bf550000000 0x53c7ffff80000006 0x853c7ffff8000000

def z441 : W := mkw 0x2efdd4fafeffeebd 0xa2efdd4fafeffeeb 0xffffffffffffffff 0xffffffffffffffff

def z442 : W := mkw 0x443e945500000000 0x0443e94550000000 0x1037000000000000 0x0103700000000000

def z443 : W := mkw 0x2ac5c082ee25c43c 0x22ac5c082ee25c43 0x13c7c3878f01c072 0x813c7c3878f01c07

def z444 : W := mkw 0x0bc06baac886e634 0x20bc06baac886e63 0x6fc8ffffc88fe67f 0xf6fc8ffffc88fe67

def z445 : W := mkw 0x004140aacaa7e634 0x2004140aacaa7e63 0xf3ffc3ffcfffe67f 0xff3ffc3ffcfffe67

def z446 : W := mkw 0x0010106000902801 0x0001010600090280 0xec303c6070f03f8d 0x7ec303c6070f03f8

def z447 : W := mkw 0x0001000002210000 0x0000100000221000 0x3037000000f1c003 0x03037000000f1c00

def z448 : W := mkw 0x004040aac886e634 0x2004040aac886e63 0x600003ffc88fe67c 0x0600003ffc88fe67

def z449 : W := mkw 0x1bd33be66fb17d77 0x41bd33be66fb17d7 0xb3f733e60ff1f87f 0xbb3f733e60ff1f87

def z450 : W := mkw 0x2ac5c0006e258008 0x02ac5c0006e25800 0x33cfc0004f8fc00b 0xd33cfc0004f8fc00

def z451 : W := mkw 0x0b802b0025001142 0x00b802b002500114 0x8f003e003f0039fc 0xb8f003e003f0039f

def z452 : W := mkw 0x41123f5500000000 0x041123f550000000 0x00003c0000000000 0x000003c000000000

def z453 : W := mkw 0x0b802b0001001040 0x00b802b000100104 0xcfc03f800f00387c 0xfcfc03f800f00387

def z454 : W := mkw 0x4ffeffffd8deeeb5 0xa4ffeffffd8deeeb 0xfffffffff8ffffff 0xffffffffff8fffff

def z455 : W := mkw 0x115332e64bb17c75 0x4115332e64bb17c7 0xf3f733e64ff1fe7f 0xff3f733e64ff1fe7

def z456 : W := mkw 0x0000002000902801 0x0000000200090280 0xa000000000f03808 0x0a000000000f0380

def z457 : W := mkw 0x0439147812fb2a81 0x80439147812fb2a8 0xff3f3c787fffff8f 0xfff3f3c787fffff8

def z458 : W := mkw 0x4fbebf5500000000 0x04fbebf550000000 0x5f3f3c7800000005 0x75f3f3c780000000

def z459 : W := mkw 0x0b802b8025001566 0x00b802b802500156 0xcf003f8037003ff4 0x2cf003f8037003ff

def z460 : W := mkw 0x01002b8001001566 0x001002b800100156 0x0000038000000070 0x0000003800000007

def z461 : W := mkw 0x0100220000000000 0x0010022000000000 0x0300320000000004 0xb030032000000000

def z462 : W := mkw 0x2ac5c0006e258008 0x02ac5c0006e25800 0x9fc7c0007f01c00a 0xf9fc7c0007f01c00

def z463 : W := mkw 0x0ac000006c000000 0x00ac000006c00000 0x03c000000f000000 0x803c000000f00000

def z464 : W := mkw 0x4fbebf7d00922a81 0x84fbebf7d00922a8 0x5fffffff80003f87 0xf5fffffff80003f8

def z465 : W := mkw 0x04381458104a0280 0x804381458104a028 0x4c383c78700e0785 0x74c383c78700e078

def z466 : W := mkw 0x0438145000000000 0x0043814500000000 0x0c303c0000000000 0x20c303c000000000

def z467 : W := mkw 0x2ead800036690008 0x02ead80003669000 0xbf3700003ff1c00b 0xbbf3700003ff1c00

def z468 : W := mkw 0x0000000000000000 0x0000000000000000 0x40c8c19980000000 0x440c8c1998000000

def z469 : W := mkw 0x0428041000000000 0x0042804100000000 0x4c080c1800000000 0x44c080c180000000

def z470 : W := mkw 0x00000008104a0280 0x800000008104a028 0x00000000700e0780 0x000000000700e078

def z471 : W := mkw 0x304140227ffdf859 0x4304140227ffdf85 0xa00000007ffff878 0x0a00000007ffff87

def z472 : W := mkw 0x1113324403311841 0x4111332440331184 0x933732000f70387c 0xb933732000f70387

def z473 : W := mkw 0x6fffff7d7effaa89 0x86fffff7d7effaa8 0xffffffffffffff8f 0xfffffffffffffff8

def z474 : W := mkw 0x0bc02b806d001566 0x00bc02b806d00156 0x4fc00f807f0007f0 0xc4fc00f807f0007f

def z475 : W := mkw 0x4fbebf5525001142 0x04fbebf552500114 0x9f373c0037001980 0x29f373c003700198

def z476 : W := mkw 0x0000400000048000 0x0000040000004800 0x2008c000008fc003 0x02008c000008fc00

def z477 : W := mkw 0x1113326603b17851 0x41113326603b1785 0x130732660f01f876 0x8130732660f01f87

def z478 : W := mkw 0x242cc000104c8008 0x0242cc000104c800 0x0008c000000e0000 0x00008c000000e000

def z479 : W := mkw 0x0438147000902801 0x0043814700090280 0xec383c7800f0380d 0x7ec383c7800f0380

def z480 : W := mkw 0x0b802b0025001142 0x00b802b002500114 0x0300000007000000 0x0030000000700000

def z481 : W := mkw 0x0000008000000424 0x0000000800000042 0x4000038000002674 0x0400003800000267

def z482 : W := mkw 0x000000aa80826634 0x2000000aa8082663 0x0000000000002670 0x0000000000000267

def z483 : W := mkw 0x453a3f5500000000 0x0453a3f550000000 0x4c383fff80000005 0x74c383fff8000000

def z484 : W := mkw 0x0000098000000526 0x0000009800000052 0x40000d8000000780 0x040000d800000078

def z485 : W := mkw 0x0012104400000000 0x0001210440000000 0x1037006600000003 0x0103700660000000

def z486 : W := mkw 0x004040aac886e634 0x2004040aac886e63 0x60c8c1ffc08fc603 0x460c8c1ffc08fc60

def z487 : W := mkw 0x004040aac886e634 0x2004040aac886e63 0x2008c07fc88fe67b 0x02008c07fc88fe67

def z488 : W := mkw 0x004000806d001566 0x0004000806d00156 0x000000000f000070 0x0000000000f00007

def z489 : W := mkw 0x6fbfff55126d8008 0x06fbfff55126d800 0x7fffffff80ffc007 0xf7fffffff80ffc00

def z490 : W := mkw 0x204040007c4c8008 0x0204040007c4c800 0x00000000700e0000 0x000000000700e000

def z491 : W := mkw 0x000000aa80826634 0x2000000aa8082663 0x40c8c3ff80002677 0xd40c8c3ff8000267

def z492 : W := mkw 0x0ef814787cda2a81 0x80ef814787cda2a8 0xeff83c787ffe3f8d 0xfeff83c787ffe3f8

def z493 : W := mkw 0x4eec8d916c000526 0x04eec8d916c00052 0x4cc8cd99f0000780 0x44cc8cd99f000078

def z494 : W := mkw 0x0000002800822200 0x0000000280082220 0x4000007800002604 0x0400000780000260

def z495 : W := mkw 0x1112326601907851 0x4111232660190785 0x830032660f00387c 0xb830032660f00387

def z496 : W := mkw 0x01402b8049001566 0x001402b804900156 0x40c03f8048003ffc 0xd40c03f8048003ff

def z497 : W := mkw 0x41123f5500000000 0x041123f550000000 0x40c8ffff80000007 0xd40c8ffff8000000

def z498 : W := mkw 0x4b96bb4500000000 0x04b96bb450000000 0x13f7f3e780000007 0xb13f7f3e78000000

def z499 : W := mkw 0x0438147810da2a81 0x80438147810da2a8 0xac383c7830fe1981 0x2ac383c7830fe198

def z500 : W := mkw 0x2eecc0007c4c8008 0x02eecc0007c4c800 0x1fffc000700e0003 0xf1fffc000700e000

def z501 : W := mkw 0x0010104000100801 0x0001010400010080 0x8030300000701800 0x2803030000070180

def z502 : W := mkw 0x442c841100000000 0x0442c84110000000 0x0008c01980000000 0x00008c0198000000

def z503 : W := mkw 0x0428000000000000 0x0042800000000000 0x0c38000000000001 0x70c3800000000000

def z504 : W := mkw 0x4ffebfd548000424 0x04ffebfd54800042 0x5fffffffc800267f 0xf5fffffffc800267

def z505 : W := mkw 0x114362aecba7f674 0x6114362aecba7f67 0x73cfc3ffcf8fe67f 0xd73cfc3ffcf8fe67

def z506 : W := mkw 0x0438147810da2a81 0x80438147810da2a8 0x6c380c7870fe0781 0x46c380c7870fe078

def z507 : W := mkw 0x2eedc0007e6d8008 0x02eedc0007e6d800 0x9ff7c0003f71c002 0xa9ff7c0003f71c00

def z508 : W := mkw 0x4ebc9d5100000000 0x04ebc9d510000000 0x4cf8fdf980000005 0x74cf8fdf98000000

def z509 : W := mkw 0x0ac040aaec86e634 0x20ac040aaec86e63 0xefc8c3ffff8fe67f 0xfefc8c3ffff8fe67

def z510 : W := mkw 0x0000000000000000 0x0000000000000000 0x830000000f000008 0xb830000000f00000

def z511 : W := mkw 0x0010106810da2a81 0x80010106810da2a8 0xa030306070fe3f8d 0x3a030306070fe3f8

def z512 : W := mkw 0x0438145010480000 0x0043814501048000 0xec383c7870fe000d 0x7ec383c7870fe000

def z513 : W := mkw 0x204140006e258008 0x0204140006e25800 0x000000000f01c000 0x0000000000f01c00

def z514 : W := mkw 0x0438147810da2a81 0x80438147810da2a8 0xa038307800fe380d 0x3a038307800fe380

def z515 : W := mkw 0x2feceb807d4c956e 0x02feceb807d4c956 0xcfc8ff807f0e3ffc 0xfcfc8ff807f0e3ff

def z516 : W := mkw 0x0438147a10da6a91 0x80438147a10da6a9 0xec383e7e78ffffff 0xfec383e7e78fffff

def z517 : W := mkw 0x2eedc0aafeefe63c 0x22eedc0aafeefe63 0xbfffc0007fffe67b 0xfbfffc0007fffe67

def z518 : W := mkw 0x0000000000000000 0x0000000000000000 0x20080000408e0009 0x520080000408e000

def z519 : W := mkw 0x1112326601907851 0x4111232660190785 0x1337326600003877 0xb133732660000387

def z520 : W := mkw 0x2eedc02afeefe218 0x22eedc02afeefe21 0xbfffc07fffffc00b 0xfbfffc07fffffc00

def z521 : W := mkw 0x046844bad8cee6b4 0xa046844bad8cee6b 0x6cc8cffff88fe7ff 0xd6cc8cffff88fe7f

def z522 : W := mkw 0x4ebe945500000000 0x04ebe94550000000 0x1fffc07f80000003 0xf1fffc07f8000000

def z523 : W := mkw 0x543f947702b16811 0x4543f947702b1681 0x303fc07f80f1c003 0x0303fc07f80f1c00

def z524 : W := mkw 0x2eedc0006e258008 0x02eedc0006e25800 0x1fffc0000f01c003 0xf1fffc0000f01c00

def z525 : W := mkw 0x4b86ab0500000000 0x04b86ab050000000 0x1307000000000000 0x0130700000000000

def z526 : W := mkw 0x115372664bb5f851 0x4115372664bb5f85 0xb3fff2664ffff87f 0xfb3fff2664ffff87

def z527 : W := mkw 0x4faeaf1500000000 0x04faeaf150000000 0x5fcfcf9f80000002 0xc5fcfcf9f8000000

def z528 : W := mkw 0x00404082c804c434 0x200404082c804c43 0x20c8c387c88fc07b 0xd20c8c387c88fc07

def z529 : W := mkw 0x0000000000000000 0x0000000000000000 0x00c0c38780000002 0x800c0c3878000000

def z530 : W := mkw 0x0000002810da2a81 0x80000002810da2a8 0xe008007870fe3f8d 0x5e008007870fe3f8

def z531 : W := mkw 0x1001002203b17851 0x41001002203b1785 0xa00002660ff1f87f 0x9a00002660ff1f87

def z532 : W := mkw 0x0538367811da3ac1 0x80538367811da3ac 0xef383e787ffe3ffd 0xfef383e787ffe3ff

def z533 : W := mkw 0x2fadab003769114a 0x02fadab003769114 0x9f373c0037701980 0x29f373c003770198

def z534 : W := mkw 0x0040400048048000 0x0004040004804800 0x20000000488fc008 0x020000000488fc00

def z535 : W := mkw 0x5fbfbf7f13fb7ad1 0xc5fbfbf7f13fb7ad 0xffffffffffffffff 0xffffffffffffffff

def z536 : W := mkw 0x443e945500000000 0x0443e94550000000 0x5c3ffc7f80000007 0x75c3ffc7f8000000

def z537 : W := mkw 0x0facab0000000000 0x00facab000000000 0x5fffff8000000007 0xf5fffff800000000

def z538 : W := mkw 0x0010147800922a81 0x80010147800922a8 0x60083c78408e3f8d 0x560083c78408e3f8

def z539 : W := mkw 0x4facaf1100000000 0x04facaf110000000 0x4fc8ff9980000004 0xf4fc8ff998000000

def z540 : W := mkw 0x1103222603a17050 0x41103222603a1705 0x330702660f81e07f 0x9330702660f81e07

def z541 : W := mkw 0x0bc02b806d001566 0x00bc02b806d00156 0x4cc03f8070003ff4 0x44cc03f8070003ff

def z542 : W := mkw 0x2ac4c0006c048008 0x02ac4c0006c04800 0x00c0c00000000000 0x000c0c0000000000

def z543 : W := mkw 0x5fbfbf5503311841 0x45fbfbf550331184 0x9f373c0007701800 0x29f373c000770180

def z544 : W := mkw 0x0b802b8001001566 0x00b802b800100156 0x4fc03f8000003ff4 0xf4fc03f8000003ff

def z545 : W := mkw 0x4b923f5500000000 0x04b923f550000000 0x4fc03fff80000004 0xf4fc03fff8000000

def z546 : W := mkw 0x0bc06b88ed069766 0x20bc06b88ed06976 0xcfc8ff99ff0e3ffc 0xfcfc8ff99ff0e3ff

def z547 : W := mkw 0x1112326601907851 0x4111232660190785 0x200032660881f87f 0x9200032660881f87

def z548 : W := mkw 0x0040008048000424 0x0004000804800042 0x0000000048002678 0x0000000004800267

def z549 : W := mkw 0x0000000000000000 0x0000000000000000 0x00c8c00000000003 0xd00c8c0000000000

def z550 : W := mkw 0x004000806d001566 0x0004000806d00156 0xc0c003807f003ffc 0xdc0c003807f003ff

def z551 : W := mkw 0x6bc7eb056e258008 0x06bc7eb056e25800 0x13c7c3878f01c002 0x813c7c3878f01c00

def z552 : W := mkw 0x2001000036690008 0x0200100003669000 0x8000000037700000 0x0800000003770000

def z553 : W := mkw 0x1b933b4427311943 0x41b933b442731194 0x9f373c0037701980 0x29f373c003770198

def z554 : W := mkw 0x1bd23be66d907d77 0x41bd23be66d907d7 0xcfc03fe67f003ffc 0xfcfc03fe67f003ff

def z555 : W := mkw 0x4fbebf5d104a0280 0x84fbebf5d104a028 0x5ffffffff00e0787 0xf5ffffffff00e078

def z556 : W := mkw 0x0040008048000424 0x0004000804800042 0x40c8c3ffc800267f 0xd40c8c3ffc800267

def z557 : W := mkw 0x115372eecbb7fe75 0x6115372eecbb7fe7 0xb33732664ffffe7f 0xbb33732664ffffe7

def z558 : W := mkw 0x0fb83f50355819c3 0x80fb83f50355819c 0x8f303c0037701980 0x28f303c003770198

def z559 : W := mkw 0x153b326613f97851 0x4153b326613f9785 0xbf3f32667ffff87f 0xfbf3f32667ffff87

def z560 : W := mkw 0x0000008001001566 0x0000000800100156 0x0000000000003ff0 0x00000000000003ff

def z561 : W := mkw 0x4eac8d1100000000 0x04eac8d110000000 0x4cc8cfff80000007 0xd4cc8cfff8000000

def z562 : W := mkw 0x0fe82b807d481566 0x00fe82b807d48156 0xeff83f807ffe3ffd 0xfeff83f807ffe3ff

def z563 : W := mkw 0x0011106002b12801 0x00011106002b1280 0xb33730600ff1f80f 0xbb33730600ff1f80

def z564 : W := mkw 0x0b802b0000000000 0x00b802b000000000 0xcfc03f8070003f8c 0xfcfc03f8070003f8

def z565 : W := mkw 0x0438145000000000 0x0043814500000000 0xcc383c7870003f8d 0x7cc383c7870003f8

def z566 : W := mkw 0x2eedc082fe6dc43c 0x22eedc082fe6dc43 0xbfffc387ffffc07b 0xfbfffc387ffffc07

def z567 : W := mkw 0x0bc02baaed827776 0x20bc02baaed82777 0xcfc03fffff003ffc 0xfcfc03fffff003ff

def z568 : W := mkw 0x0000000000000000 0x0000000000000000 0x8000000070003f88 0x08000000070003f8

def z569 : W := mkw 0x0bc06baaed86f776 0x20bc06baaed86f77 0x63c8c3ffcf8fe67f 0xd63c8c3ffcf8fe67

def z570 : W := mkw 0x4a84890100000000 0x04a8489010000000 0x00c0c18180000000 0x000c0c1818000000

def z571 : W := mkw 0x246dc0aadaefe63c 0x2246dc0aadaefe63 0x70ffc3ffc8ffe67f 0xd70ffc3ffc8ffe67

def z572 : W := mkw 0x6effd4557e6d8008 0x06effd4557e6d800 0xbfffc07fffffc00b 0xfbfffc07fffffc00

def z573 : W := mkw 0x2ac5c0007e6d8008 0x02ac5c0007e6d800 0xb3c7c0007fffc00a 0x8b3c7c0007fffc00

def z574 : W := mkw 0x153a367e11da7ad1 0xc153a367e11da7ad 0xec383e7e70fe3ffd 0x7ec383e7e70fe3ff

def z575 : W := mkw 0x6fffff556e258008 0x06fffff556e25800 0x5fffffff8f01c007 0xf5fffffff8f01c00

def z576 : W := mkw 0x0ac000806d001566 0x00ac000806d00156 0x8fc000007f003ff8 0xf8fc000007f003ff

def z577 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z578 : W := mkw 0x6fbfbf5536690008 0x06fbfbf553669000 0x9f373c0037700000 0x29f373c003770000

def z579 : W := mkw 0x0438547a90deea91 0xa0438547a90deea9 0xec38fc7ff0ffff8f 0x7ec38fc7ff0ffff8

def z580 : W := mkw 0x1ffb3ffe7ffb7ff7 0xc1ffb3ffe7ffb7ff 0xffff3ffe7fffffff 0xfffff3ffe7ffffff

def z581 : W := mkw 0x0000402a8086e210 0x20000402a8086e21 0x6008c07fc08fe60f 0x56008c07fc08fe60

def z582 : W := mkw 0x0102220400000000 0x0010222040000000 0x1307020600000002 0x8130702060000000

def z583 : W := mkw 0x6fffffd57f6d956e 0x06fffffd57f6d956 0xffffffffffffffff 0xffffffffffffffff

def z584 : W := mkw 0x0000402a8086e210 0x20000402a8086e21 0x20000000008fc000 0x020000000008fc00

def z585 : W := mkw 0x0b802b0000000000 0x00b802b000000000 0x0f003c0000000000 0x20f003c000000000

def z586 : W := mkw 0x3ffff2447f7d9849 0x43ffff2447f7d984 0xbffff0007fffd80b 0xfbffff0007fffd80

def z587 : W := mkw 0x41123fff80826634 0x241123fff8082663 0x40003fff80002674 0x040003fff8000267

def z588 : W := mkw 0x1003000602214010 0x4100300060221401 0x100700060001c002 0x0100700060001c00

def z589 : W := mkw 0x1013506e82b7ea11 0x61013506e82b7ea1 0x303fc07f80ffc003 0x0303fc07f80ffc00

def z590 : W := mkw 0x1113326e13fb7ad1 0xc1113326e13fb7ad 0xb33732667fffffff 0xbb33732667ffffff

def z591 : W := mkw 0x246940007e6d8008 0x0246940007e6d800 0xac3800007fffc009 0x7ac3800007fffc00

def z592 : W := mkw 0x0000402a8086e210 0x20000402a8086e21 0x60c8c3ff808fc007 0xd60c8c3ff808fc00

def z593 : W := mkw 0x2eac800034480008 0x02eac80003448000 0x0c00000030000000 0x00c0000003000000

def z594 : W := mkw 0x2ebd947836fb2a89 0x82ebd947836fb2a8 0xff3f3c7877fe3f8d 0x7ff3f3c7877fe3f8

def z595 : W := mkw 0x0112326400902801 0x0011232640090280 0xb337326600f0380f 0xbb337326600f0380

def z596 : W := mkw 0x01406baac986f776 0x201406baac986f77 0x60c8ffffc88fffff 0xd60c8ffffc88ffff

def z597 : W := mkw 0x0438145010580881 0x8043814501058088 0x0030000000700000 0x0003000000070000

def z598 : W := mkw 0x2eedc4187e6f8288 0x82eedc4187e6f828 0xffffcc187fffc78b 0xfffffcc187fffc78

def z599 : W := mkw 0x41123f5500000000 0x041123f550000000 0x53373fff80000007 0xb53373fff8000000

def z600 : W := mkw 0x0000008280004434 0x2000000828000443 0x0000038780000070 0x0000003878000007

def z601 : W := mkw 0x11123be601907d77 0x411123be601907d7 0x40003fe600003ff4 0x040003fe600003ff

def z602 : W := mkw 0x115272eec996fe75 0x6115272eec996fe7 0x60c8f3ffc88ffe7f 0xd60c8f3ffc88ffe7

def z603 : W := mkw 0x2eedc0287eefa208 0x02eedc0287eefa20 0xffffc0787fffe60f 0xfffffc0787fffe60

def z604 : W := mkw 0x0000000000000000 0x0000000000000000 0x800030000000380c 0x3800030000000380

def z605 : W := mkw 0x2eedc0227eede018 0x02eedc0227eede01 0xbfffc2667fffe07f 0xfbfffc2667fffe07

def z606 : W := mkw 0x0ac009806c000526 0x00ac009806c00052 0x4cc00f80780027fc 0xd4cc00f80780027f

def z607 : W := mkw 0x4006800500000000 0x0400680050000000 0x1007c00780000002 0x01007c0078000000

def z608 : W := mkw 0x2fedeb807f6d956e 0x02fedeb807f6d956 0xbfffc3807fffc07b 0xfbfffc3807fffc07

def z609 : W := mkw 0x6fefeb057e6d8008 0x06fefeb057e6d800 0xbfffc387ffffc00b 0xfbfffc387ffffc00

def z610 : W := mkw 0x4fbebf5500000000 0x04fbebf550000000 0x5ffffd9980000000 0x65ffffd998000000

def z611 : W := mkw 0x4fbebf5500000000 0x04fbebf550000000 0x1ffffc0000000003 0xf1ffffc000000000

def z612 : W := mkw 0x3ffff67e7ffffad9 0xc3ffff67e7ffffad 0xfffffe7e7fffffff 0xffffffe7e7ffffff

def z613 : W := mkw 0x0ac000006c000000 0x00ac000006c00000 0xcfc03c007f003f8c 0xfcfc03c007f003f8

def z614 : W := mkw 0x0eac800000000000 0x00eac80000000000 0x0cc8c00000000000 0x40cc8c0000000000

def z615 : W := mkw 0x01402b806d001566 0x001402b806d00156 0xc0003f807f003ffc 0x0c0003f807f003ff

def z616 : W := mkw 0x453a3f7d10da2a81 0x8453a3f7d10da2a8 0xec383ffff0fe3f8d 0x7ec383ffff0fe3f8

def z617 : W := mkw 0x0438145010580881 0x8043814501058088 0xac383c0070fe1989 0x7ac383c0070fe198

def z618 : W := mkw 0x0010106000902801 0x0001010600090280 0x2030006000f00001 0x02030006000f0000

def z619 : W := mkw 0x4fbebf7d10da2a81 0x84fbebf7d10da2a8 0xff3f3c7870fe3f8d 0x7ff3f3c7870fe3f8

def z620 : W := mkw 0x0438147810da2a81 0x80438147810da2a8 0xac38007870fe0009 0x7ac38007870fe000

def z621 : W := mkw 0x01002b8001001566 0x001002b800100156 0xc3003f800f003ffc 0xbc3003f800f003ff

def z622 : W := mkw 0x0bc12b806f211566 0x00bc12b806f21156 0xfff73f807ff1ffff 0xffff73f807ff1fff

def z623 : W := mkw 0x0ead800002210000 0x00ead80000221000 0xbfffc0000ff1c00b 0xfbfffc0000ff1c00

def z624 : W := mkw 0x3eedc0227ffdf859 0x43eedc0227ffdf85 0xbfffc0007ffff87b 0xfbfffc0007ffff87

def z625 : W := mkw 0x01002b0001001142 0x001002b000100114 0x00003c0000001980 0x000003c000000198

def z626 : W := mkw 0x0428000010480000 0x0042800001048000 0x2038000000fe0001 0x02038000000fe000

def z627 : W := mkw 0x0b802b0025001142 0x00b802b002500114 0xcf003c0077003f8c 0x7cf003c0077003f8

def z628 : W := mkw 0x043814fa90da6eb5 0xa043814fa90da6eb 0xec383ffff0fe3ffd 0x7ec383ffff0fe3ff

def z629 : W := mkw 0x0ac040006c048000 0x00ac040006c04800 0xafc8c0007f8fc00b 0xfafc8c0007f8fc00

def z630 : W := mkw 0x2eed80007e690008 0x02eed80007e69000 0x9ff700007f700008 0xf9ff700007f70000

def z631 : W := mkw 0x1013106602b16811 0x41013106602b1681 0xb037306600f1f80f 0x3b037306600f1f80

def z632 : W := mkw 0x004040aac886e634 0x2004040aac886e63 0x60080078488fe67d 0x560080078488fe67

def z633 : W := mkw 0x4ffebf556c000000 0x04ffebf556c00000 0xdfffffffff00000f 0xfdfffffffff00000

def z634 : W := mkw 0x004000006c000000 0x0004000006c00000 0x800000007f000008 0x0800000007f00000

def z635 : W := mkw 0x0bd03ff86d923fe7 0x80bd03ff86d923fe 0xcfc03ff87f003ffc 0xfcfc03ff87f003ff

def z636 : W := mkw 0x001014fa80926eb5 0xa001014fa80926eb 0x40003fff80003ff4 0x040003fff80003ff

def z637 : W := mkw 0x0bc06baaed86f776 0x20bc06baaed86f77 0xefc03f807f8ffffc 0xfefc03f807f8ffff

def z638 : W := mkw 0x046840aad8cee634 0x2046840aad8cee63 0xecf8c3fff8ffe67f 0xfecf8c3fff8ffe67

def z639 : W := mkw 0x0000000025001142 0x0000000002500114 0x8000000037001980 0x0800000003700198

def z640 : W := mkw 0x0bc02ba26d807576 0x00bc02ba26d80757 0xefc03fe67f81ffff 0xfefc03fe67f81fff

def z641 : W := mkw 0x0140228049001464 0x0014022804900146 0xc3c033804f003e7c 0xfc3c033804f003e7

def z642 : W := mkw 0x1001000003311841 0x4100100000331184 0x8000000007701800 0x0800000000770180

def z643 : W := mkw 0x1113326603b17851 0x41113326603b1785 0x9337326607703874 0x2933732660770387

def z644 : W := mkw 0x0fb83f5000000000 0x00fb83f500000000 0x4ff83ff800000005 0xf4ff83ff80000000

def z645 : W := mkw 0x1bc12ba26fb17d77 0x41bc12ba26fb17d7 0xefc03f807ff1fffc 0xfefc03f807ff1fff

def z646 : W := mkw 0x0000000000000000 0x0000000000000000 0x0008c07f80000003 0x00008c07f8000000

def z647 : W := mkw 0x0bc02b806c000526 0x00bc02b806c00052 0x4fc03f8070000784 0xf4fc03f807000078

def z648 : W := mkw 0x4fbebf5500000000 0x04fbebf550000000 0x5ff73f8000000004 0xf5ff73f800000000

def z649 : W := mkw 0x2eecc0007c4c8008 0x02eecc0007c4c800 0xacf8c00070fe0009 0x7acf8c00070fe000

def z650 : W := mkw 0x0fbeb24400000000 0x00fbeb2440000000 0x1ffff26600000007 0xf1ffff2660000000

def z651 : W := mkw 0x004040aac886e634 0x2004040aac886e63 0x40c0c3ff8801e676 0x840c0c3ff8801e67

def z652 : W := mkw 0x11436286cb25d474 0x611436286cb25d47 0x13c7c3878f01c072 0x813c7c3878f01c07

def z653 : W := mkw 0x004040a8c886a624 0x2004040a8c886a62 0x60c8c1f9c08e260d 0x560c8c1f9c08e260

def z654 : W := mkw 0x2eedc0007e6d8008 0x02eedc0007e6d800 0x3cffc00070ffc003 0x43cffc00070ffc00

def z655 : W := mkw 0x1103220403211040 0x4110322040321104 0x1307000007000000 0x0130700000700000

def z656 : W := mkw 0x4fbebf5510580881 0x84fbebf551058088 0x9f373c0030701980 0x29f373c003070198

def z657 : W := mkw 0x4fbebf7d00822200 0x04fbebf7d0082220 0x7fffffffc08e260f 0xf7fffffffc08e260

def z658 : W := mkw 0x153b367e13fb7ad1 0xc153b367e13fb7ad 0xb33f327e0ffff87f 0xbb33f327e0ffff87

def z659 : W := mkw 0x04280418104a0280 0x804280418104a028 0x00080018000e0000 0x000080018000e000

def z660 : W := mkw 0x1fbfb26603b17851 0x41fbfb26603b1785 0xbffff2660ff1f87f 0xfbffff2660ff1f87

def z661 : W := mkw 0x0bc02b806d001566 0x00bc02b806d00156 0x8fc003807f000078 0xf8fc003807f00007

def z662 : W := mkw 0x0ebc947810da2a81 0x80ebc947810da2a8 0xfffffc7870fe3f8f 0xffffffc7870fe3f8

def z663 : W := mkw 0x0ff87ffafddefff7 0xa0ff87ffafddefff 0xeff8ffffffffffff 0xfeff8fffffffffff

def z664 : W := mkw 0x153b367613f978d1 0xc153b367613f978d 0xbf373e663ff1f9ff 0xbbf373e663ff1f9f

def z665 : W := mkw 0x5fbfbf5503311841 0x45fbfbf550331184 0xdfffffff87701807 0xfdfffffff8770180

def z666 : W := mkw 0x5fbfbf5703215050 0x45fbfbf570321505 0x5fffffff8f01c077 0xf5fffffff8f01c07

def z667 : W := mkw 0x1bd332666fb17851 0x41bd332666fb1785 0xbff732667ff1f87f 0xfbff732667ff1f87

def z668 : W := mkw 0x0eec80006c000000 0x00eec80006c00000 0x9fffc0007f00000b 0xf9fffc0007f00000

def z669 : W := mkw 0x1439147a13fb7ad1 0xc1439147a13fb7ad 0xec383c787ffffffd 0x7ec383c787ffffff

def z670 : W := mkw 0x0112324400000000 0x0011232440000000 0x53fff3ff80000007 0xf53fff3ff8000000

def z671 : W := mkw 0x047854f8d8deaea5 0xa047854f8d8deaea 0xecf8fdf9f0fe3f8d 0x7ecf8fdf9f0fe3f8

def z672 : W := mkw 0x4b86ab0500000000 0x04b86ab050000000 0x5fc7ff8780000006 0xf5fc7ff878000000

def z673 : W := mkw 0x5fbfbf7703b17851 0x45fbfbf7703b1785 0xbf373e660ff1f87f 0xbbf373e660ff1f87

def z674 : W := mkw 0x014022806d001566 0x0014022806d00156 0x830032007f003ffc 0xb830032007f003ff

def z675 : W := mkw 0x1112324401101841 0x4111232440110184 0x0000300000001800 0x0000030000000180

def z676 : W := mkw 0x0ac009806d001566 0x00ac009806d00156 0xccc00d807f003ff8 0x4ccc00d807f003ff

def z677 : W := mkw 0x1113324403311841 0x4111332440331184 0x9337326607701807 0xb933732660770180

def z678 : W := mkw 0x0bc02b806d001566 0x00bc02b806d00156 0x4fc03f800f000074 0xf4fc03f800f00007

def z679 : W := mkw 0x004040aaed86f776 0x2004040aaed86f77 0xe0c8c3ffff8fffff 0xde0c8c3ffff8ffff

def z680 : W := mkw 0x0bc02b806d001566 0x00bc02b806d00156 0x8fc03f803f0019f0 0xa8fc03f803f0019f

def z681 : W := mkw 0x0438147810da2a81 0x80438147810da2a8 0x6038007840fe260d 0x56038007840fe260

def z682 : W := mkw 0x0001000002210000 0x0000100000221000 0x130700000f01c002 0x8130700000f01c00

def z683 : W := mkw 0x0b802b0000000000 0x00b802b000000000 0x4fc8ffff80000007 0xf4fc8ffff8000000

def z684 : W := mkw 0x0000000000000000 0x0000000000000000 0x400000004000260c 0x5400000004000260

def z685 : W := mkw 0x0001000002210000 0x0000100000221000 0x9337000007700000 0x2933700000770000

def z686 : W := mkw 0x2eecc0007c4c8008 0x02eecc0007c4c800 0x8fc8c0007f0e0008 0xf8fc8c0007f0e000

def z687 : W := mkw 0x0bc02b006c000000 0x00bc02b006c00000 0xcfc03f807f00000c 0xfcfc03f807f00000

def z688 : W := mkw 0x1113326403b13841 0x41113326403b1384 0xb337306007f0380d 0x3b337306007f0380

def z689 : W := mkw 0x6fbfbf5536690008 0x06fbfbf553669000 0xdfffffffb7700007 0xfdfffffffb770000

def z690 : W := mkw 0x1001002202b16811 0x41001002202b1681 0x2000000000f1c000 0x02000000000f1c00

def z691 : W := mkw 0x0000000000000000 0x0000000000000000 0x000002000800207c 0x9000002000800207

def z692 : W := mkw 0x0000000000000000 0x0000000000000000 0x40c0038000000004 0xd40c003800000000

def z693 : W := mkw 0x0ac009806c000526 0x00ac009806c00052 0x00c0018000000000 0x000c001800000000

def z694 : W := mkw 0x2eedc0007e6d8008 0x02eedc0007e6d800 0x1fcfc0007f0fc002 0xc1fcfc0007f0fc00

def z695 : W := mkw 0x0000000010480000 0x0000000001048000 0xa000000070fe0008 0x0a000000070fe000

def z696 : W := mkw 0x0ac049aaec86e736 0x20ac049aaec86e73 0x6cc8cffff88fe7ff 0xd6cc8cffff88fe7f

def z697 : W := mkw 0x0040402ac886e210 0x20040402ac886e21 0x20c8c07fc88fc00b 0xd20c8c07fc88fc00

def z698 : W := mkw 0x4bc6ab856d001566 0x04bc6ab856d00156 0x13c7c3878f000072 0x813c7c3878f00007

def z699 : W := mkw 0x40000d1100000000 0x040000d110000000 0x40000d9980000000 0x040000d998000000

def z700 : W := mkw 0x2efcd4787cdeaa89 0x82efcd4787cdeaa8 0xecf8fc7870fe3f8d 0x7ecf8fc7870fe3f8

def z701 : W := mkw 0x0040400048048000 0x0004040004804800 0x60c8c3ffc88fc00f 0xd60c8c3ffc88fc00

def z702 : W := mkw 0x41527fffc886e634 0x241527fffc886e63 0x60c8ffffc88fe67f 0xd60c8ffffc88fe67

def z703 : W := mkw 0x2fedab807f69156e 0x02fedab807f69156 0xdff73f807f703ffc 0xfdff73f807f703ff

def z704 : W := mkw 0x1bc32b866f215576 0x41bc32b866f21557 0x13c703860f01c072 0x813c703860f01c07

def z705 : W := mkw 0x0ac100006e210000 0x00ac100006e21000 0xbff700007ff1c00b 0xfbff700007ff1c00

def z706 : W := mkw 0x004000aac8826634 0x2004000aac882663 0x40c003ffc800267c 0xd40c003ffc800267

def z707 : W := mkw 0x4fbebf5525001142 0x04fbebf552500114 0x5fffffff87000007 0xf5fffffff8700000

def z708 : W := mkw 0x115372cccb379e65 0x6115372cccb379e6 0xd3fff199c77e1e00 0x6d3fff199c77e1e0

def z709 : W := mkw 0x242dc000126d8008 0x0242dc000126d800 0xbf3fc0007fffc00b 0xfbf3fc0007fffc00

def z710 : W := mkw 0x152b261e136b52d0 0xc152b261e136b52d 0x5f0f0e1e7f0fc7f2 0xc5f0f0e1e7f0fc7f

def z711 : W := mkw 0x0ead800012690000 0x00ead80001269000 0xbfffc0007fffc00b 0xfbfffc0007fffc00

def z712 : W := mkw 0x1113367e03b37ad1 0xc1113367e03b37ad 0xff373e7e7ff1ffff 0xfff373e7e7ff1fff

def z713 : W := mkw 0x004000806d001566 0x0004000806d00156 0xccc03f807f003ffc 0xfccc03f807f003ff

def z714 : W := mkw 0x0b802b8025001566 0x00b802b802500156 0xcf003f803f003ffc 0xbcf003f803f003ff

def z715 : W := mkw 0x0b923b4400000000 0x00b923b440000000 0x5fffffff80000007 0xf5fffffff8000000

def z716 : W := mkw 0x1113326603b17851 0x41113326603b1785 0xb33702660ff1c07b 0xbb33702660ff1c07

def z717 : W := mkw 0x4fbebf5500000000 0x04fbebf550000000 0x5cffffff80000007 0x45cffffff8000000

def z718 : W := mkw 0x3ffef2667ddcf859 0x43ffef2667ddcf85 0x0cc8f266700e3874 0x40cc8f266700e387

def z719 : W := mkw 0x0438147810da2a81 0x80438147810da2a8 0x6c383c7870fe3f85 0x46c383c7870fe3f8

def z720 : W := mkw 0x1ad319e66eb16d37 0x41ad319e66eb16d3 0x7cf70de670f1c783 0x47cf70de670f1c78

def z721 : W := mkw 0x1113326603b17851 0x41113326603b1785 0xb33f32664ffff87f 0xfb33f32664ffff87

def z722 : W := mkw 0x0ebc945000000000 0x00ebc94500000000 0x5fffffff80000007 0xf5fffffff8000000

def z723 : W := mkw 0x1113326603b17851 0x41113326603b1785 0xb3f7f3e78ff1f87f 0xbb3f7f3e78ff1f87

def z724 : W := mkw 0x0ff83ff87dda3fe7 0x80ff83ff87dda3fe 0x23f803f80ffe0071 0x823f803f80ffe007

def z725 : W := mkw 0x0bc022006d001040 0x00bc022006d00104 0xcfc03e007f003ffc 0xfcfc03e007f003ff

def z726 : W := mkw 0x61537f557e6d8008 0x061537f557e6d800 0xe0003fffffffc00c 0x0e0003fffffffc00

def z727 : W := mkw 0x2eedc9807e6d852e 0x02eedc9807e6d852 0xffffcf807fffe7ff 0xfffffcf807fffe7f

def z728 : W := mkw 0x4b86ab0500000000 0x04b86ab050000000 0x53c7c3ff80000006 0x853c7c3ff8000000

def z729 : W := mkw 0x7fbfbf5537791849 0x47fbfbf553779184 0x9f373c0037701800 0x29f373c003770180

def z730 : W := mkw 0x1113326603b17851 0x41113326603b1785 0xb33732060ff1f87a 0xab33732060ff1f87

def z731 : W := mkw 0x1113326603b17851 0x41113326603b1785 0xb33732667ff1ffff 0xbb33732667ff1fff

def z732 : W := mkw 0x0438147810da2a81 0x80438147810da2a8 0xec303c0070fe3f8c 0x7ec303c0070fe3f8

def z733 : W := mkw 0x51133f7703b17851 0x451133f7703b1785 0xb3373e660ff1f87f 0xbb3373e660ff1f87

def z734 : W := mkw 0x2eedc0007e6d8008 0x02eedc0007e6d800 0xbffff0007ffff80f 0xfbffff0007ffff80

def z735 : W := mkw 0x5fbfbf55137918c1 0xc5fbfbf55137918c 0x9f373c0037701980 0x29f373c003770198

def z736 : W := mkw 0x004040aac886e634 0x2004040aac886e63 0x60c8c3ffc08fe677 0x460c8c3ffc08fe67

def z737 : W := mkw 0x1112326e01927ad1 0xc1112326e01927ad 0x0000326600003ff4 0x00000326600003ff

def z738 : W := mkw 0x2eadc000366d8008 0x02eadc000366d800 0xbf3fc00077ffc00b 0x7bf3fc00077ffc00

def z739 : W := mkw 0x1113326603b17851 0x41113326603b1785 0xbf3732667ff1f87f 0xfbf3732667ff1f87

def z740 : W := mkw 0x4bc22b856d001566 0x04bc22b856d00156 0xcfc03f87ff003ffc 0xfcfc03f87ff003ff

def z741 : W := mkw 0x5ead8d3303b17851 0x45ead8d3303b1785 0xecc8cd998ff1f878 0x4ecc8cd998ff1f87

def z742 : W := mkw 0x2eedc0007e6d8008 0x02eedc0007e6d800 0xffffc0787fffc00f 0xfffffc0787fffc00

def z743 : W := mkw 0x2eecc498fc4e86ac 0xa2eecc498fc4e86a 0x4cc8cd99f00e0780 0x44cc8cd99f00e078

def z744 : W := mkw 0x1113326603b17851 0x41113326603b1785 0xf33f327e0ff1f87f 0xff33f327e0ff1f87

def z745 : W := mkw 0x0bc02b806d001566 0x00bc02b806d00156 0xefc03f807f81ffff 0xfefc03f807f81fff

def z746 : W := mkw 0x246940007e6d8008 0x0246940007e6d800 0xbf3f00007fffc00b 0xfbf3f00007fffc00

def z747 : W := mkw 0x4fbebf5510480000 0x04fbebf551048000 0xfffffffff0fe3f8f 0xffffffffff0fe3f8

def z748 : W := mkw 0x0438147a90da6a91 0xa0438147a90da6a9 0xec383c7ff0fe3f8d 0x7ec383c7ff0fe3f8

def z749 : W := mkw 0x2eedc0007e6d8008 0x02eedc0007e6d800 0xffffc3807fffc00f 0xfffffc3807fffc00

def z750 : W := mkw 0x4fbebf5524000102 0x04fbebf552400010 0x5fffffffb0000187 0xf5fffffffb000018

def z751 : W := mkw 0x4fbebf5525001142 0x04fbebf552500114 0xdfffffffbf0039ff 0xfdfffffffbf0039f

def z752 : W := mkw 0x204140aadaefe63c 0x2204140aadaefe63 0x2000000048ffe678 0x02000000048ffe67

def z753 : W := mkw 0x104140aacab7ee35 0x6104140aacab7ee3 0x2000000048ffe678 0x02000000048ffe67

def z754 : W := mkw 0x4b96bf5500000000 0x04b96bf550000000 0x13c7c3ff80000002 0x813c7c3ff8000000

def z755 : W := mkw 0x2eedc0007e6d8008 0x02eedc0007e6d800 0xb3ffc0007fffc00b 0x8b3ffc0007fffc00

def z756 : W := mkw 0x1113326603b17851 0x41113326603b1785 0x933732660f71f876 0xa933732660f71f87

def z757 : W := mkw 0x4ffeffffc886e634 0x24ffeffffc886e63 0x3f373c00488fe678 0x23f373c00488fe67

def z758 : W := mkw 0x1013106603b17851 0x41013106603b1785 0xb33700660ff1f87b 0xbb33700660ff1f87

def z759 : W := mkw 0x0bc02b806d001566 0x00bc02b806d00156 0xefc83f807f8e3ffd 0xfefc83f807f8e3ff

def z760 : W := mkw 0x242dc000126d8008 0x0242dc000126d800 0x333fc0000fffc003 0x8333fc0000fffc00

def z761 : W := mkw 0x242dc000126d8008 0x0242dc000126d800 0xb33fc00007ffc003 0x2b33fc00007ffc00

def z762 : W := mkw 0x004040aac886e634 0x2004040aac886e63 0x20c8c3ffc88fe67b 0x820c8c3ffc88fe67

def z763 : W := mkw 0x1103220603215050 0x4110322060321505 0xb33732060ff1f87f 0xbb33732060ff1f87

def z764 : W := mkw 0x2eecc080fc4c842c 0x22eecc080fc4c842 0x0cc8c181f00e0000 0x40cc8c181f00e000

def z765 : W := mkw 0x2eadc000366d8008 0x02eadc000366d800 0xbfffc00037ffc003 0xfbfffc00037ffc00

def z766 : W := mkw 0x4b86ab2d10da2a81 0x84b86ab2d10da2a8 0xb3c7c387f0fe3f8a 0x8b3c7c387f0fe3f8

def z767 : W := mkw 0x0012104400000000 0x0001210440000000 0x50ffc3ff80000007 0xd50ffc3ff8000000

def z768 : W := mkw 0x2eedc0007e6d8008 0x02eedc0007e6d800 0xbff7c0007fffc00a 0xabff7c0007fffc00

def z769 : W := mkw 0x0bc02b806d001566 0x00bc02b806d00156 0xcfc03d807f003ff8 0x6cfc03d807f003ff

def z770 : W := mkw 0x004040aac886e634 0x2004040aac886e63 0x6cc8ffffc88fe67f 0xf6cc8ffffc88fe67

def z771 : W := mkw 0x004040aaec86e634 0x2004040aaec86e63 0xe0c8c3ffff8fe67f 0xde0c8c3ffff8fe67

def z772 : W := mkw 0x4fbebf5500000000 0x04fbebf550000000 0x1fffffff80000003 0xa1fffffff8000000

def z773 : W := mkw 0x0001000002210000 0x0000100000221000 0xb33f00004fffc00b 0xfb33f00004fffc00

def z774 : W := mkw 0x2eedc080fe6d842c 0x22eedc080fe6d842 0xbfffc181ffffc00b 0xfbfffc181ffffc00

def z775 : W := mkw 0x453ebf5500000000 0x0453ebf550000000 0x50ffffff80000007 0xd50ffffff8000000

def z776 : W := mkw 0x1113326603b17851 0x41113326603b1785 0x333732660ff1f877 0x8333732660ff1f87

def z777 : W := mkw 0x0113326602a16010 0x00113326602a1601 0xb33732660ff1e07f 0xbb33732660ff1e07

def z778 : W := mkw 0x1113367603b178d1 0xc1113367603b178d 0xb3373e660ff1f9ff 0xbb3373e660ff1f9f

def z779 : W := mkw 0x2eedc0007e6d8008 0x02eedc0007e6d800 0xbfffc07fffffc00b 0xfbfffc07fffffc00

def z780 : W := mkw 0x0101222203a17050 0x00101222203a1705 0xb33732660ff1f87f 0xbb33732660ff1f87

def z781 : W := mkw 0x004040aac886e634 0x2004040aac886e63 0x6cc8cffff88fe7ff 0xd6cc8cffff88fe7f

def z782 : W := mkw 0x1011106203b17851 0x41011106203b1785 0xb33730600ff1f87f 0xbb33730600ff1f87

def z783 : W := mkw 0x6fbfbf553769114a 0x06fbfbf553769114 0x9f373c0037701980 0x29f373c003770198

def z784 : W := mkw 0x2eedc0007e6d8008 0x02eedc0007e6d800 0xbfffc0003fffc003 0xabfffc0003fffc00

def z785 : W := mkw 0x0facab0000000000 0x00facab000000000 0x5fffffff80000007 0xf5fffffff8000000

def z786 : W := mkw 0x4b96bf5500000000 0x04b96bf550000000 0x53f7ffff80000007 0xb53f7ffff8000000

def z787 : W := mkw 0x0bc02b806d001566 0x00bc02b806d00156 0xcfc8ff99ff003ffc 0xfcfc8ff99ff003ff

def z788 : W := mkw 0x004040aac886e634 0x2004040aac886e63 0xecc8c3fff88fe67f 0xfecc8c3fff88fe67

def z789 : W := mkw 0x4b96bb4500000000 0x04b96bb450000000 0x53fff3ff80000007 0xf53fff3ff8000000

def z790 : W := mkw 0x0438147810da2a81 0x80438147810da2a8 0xec303c7870fe3f8c 0x2ec303c7870fe3f8

def z791 : W := mkw 0x2eadc000366d8008 0x02eadc000366d800 0x333fc00007ffc003 0x0333fc00007ffc00

def z792 : W := mkw 0x2ad5d4786eb7aa89 0x82ad5d4786eb7aa8 0x53c7fc780f01ff86 0x853c7fc780f01ff8

def z793 : W := mkw 0x2eedc0007e6d8008 0x02eedc0007e6d800 0xbfffc387ffffc00b 0xfbfffc387ffffc00

def z794 : W := mkw 0x0438147a10da6a91 0x80438147a10da6a9 0xec383c7e70ffff8f 0x7ec383c7e70ffff8

def z795 : W := mkw 0x2eadc000126d8008 0x02eadc000126d800 0xbfffc0000fffc00b 0xfbfffc0000fffc00

def z796 : W := mkw 0x2eadc000366d8008 0x02eadc000366d800 0xbf37000037ffc000 0x2bf37000037ffc00

def z797 : W := mkw 0x04381458105a0a81 0x804381458105a0a8 0x8c303c00707e1f80 0x28c303c00707e1f8

def z798 : W := mkw 0x004040aac886e634 0x2004040aac886e63 0x40c8c3ffc80fe676 0xc40c8c3ffc80fe67

def z799 : W := mkw 0x2eecc0807c4c852e 0x02eecc0807c4c852 0x0cc8c000700e0780 0x40cc8c000700e078

def z800 : W := mkw 0x047854d2d85cccb5 0xa047854d2d85cccb 0x8cf0ff87b871d9f2 0xa8cf0ff87b871d9f

def z801 : W := mkw 0x1113367e03b37ad1 0xc1113367e03b37ad 0xb337327e0ff1f87f 0xbb337327e0ff1f87

def z802 : W := mkw 0x246dc0007e6d8008 0x0246dc0007e6d800 0xb33fc0007fffc00b 0xbb33fc0007fffc00

def z803 : W := mkw 0x1113326603b17851 0x41113326603b1785 0x333702660ff1e07f 0x9333702660ff1e07

def z804 : W := mkw 0x1113326603b17851 0x41113326603b1785 0xb33732000ff1f87c 0xbb33732000ff1f87

def z805 : W := mkw 0x0438147810da2a81 0x80438147810da2a8 0xec383c7878ffff8f 0xfec383c7878ffff8

def z806 : W := mkw 0x252deb80136d956e 0x0252deb80136d956 0x703fff8000fffff7 0x0703fff8000fffff

def z807 : W := mkw 0x2eeccd987c4e87ae 0x82eeccd987c4e87a 0x4cc8cd98700e0780 0x44cc8cd98700e078

def z808 : W := mkw 0x4fbebf5500000000 0x04fbebf550000000 0x13fff3ff80000007 0xb13fff3ff8000000

def z809 : W := mkw 0x1113324603215050 0x4111332460321505 0xb33732660ff1c07f 0xbb33732660ff1c07

def z810 : W := mkw 0x11123ffe01927ff7 0xc11123ffe01927ff 0x40003ffe00003ff4 0x040003ffe00003ff

def z811 : W := mkw 0x004040aac886e634 0x2004040aac886e63 0xe3c8c3ffcf8fe67f 0xfe3c8c3ffcf8fe67

def z812 : W := mkw 0x4fbebf5500000000 0x04fbebf550000000 0x7fffffff8881c00f 0xf7fffffff8881c00

def z813 : W := mkw 0x1112326e01927a51 0x41112326e01927a5 0x4000327e00003e74 0x04000327e00003e7

def z814 : W := mkw 0x0001000012690000 0x0000100001269000 0xb33700007fffc00b 0xbb33700007fffc00

def z815 : W := mkw 0x4fbebf5501001040 0x04fbebf550100104 0x5fffffff80003877 0xf5fffffff8000387

def z816 : W := mkw 0x1113324603315851 0x4111332460331585 0x133702060f71c072 0x8133702060f71c07

def z817 : W := mkw 0x6eedcd117e6d8008 0x06eedcd117e6d800 0xbfffcc007fffc00b 0xfbfffcc007fffc00

def z818 : W := mkw 0x01002b8001001566 0x001002b800100156 0xcf003f807f003ffc 0xfcf003f807f003ff

def z819 : W := mkw 0x0438145010480000 0x0043814501048000 0xec383c7870fe3f8d 0x7ec383c7870fe3f8

def z820 : W := mkw 0x0001000002210000 0x0000100000221000 0xb33702000ff1e07f 0xbb33702000ff1e07

def z821 : W := mkw 0x2ead80aab6eb663c 0x22ead80aab6eb663 0xdf3703ffb7702674 0x2df3703ffb770267

def z822 : W := mkw 0x2ac140007e6d8008 0x02ac140007e6d800 0xbff700007fffc00b 0xfbff700007fffc00

def z823 : W := mkw 0x0438147810da2a81 0x80438147810da2a8 0xec383c1870fe3f88 0x6ec383c1870fe3f8

def z824 : W := mkw 0x143b547e92ffea91 0xe143b547e92ffea9 0x303fc07f80ffc003 0x0303fc07f80ffc00

def z825 : W := mkw 0x1439147a12fb6a91 0xc1439147a12fb6a9 0x2038007800ffc001 0x02038007800ffc00

def z826 : W := mkw 0x2eedc0007e6d8008 0x02eedc0007e6d800 0xbfffc2007fffe07f 0xfbfffc2007fffe07

def z827 : W := mkw 0x0b802b0001001040 0x00b802b000100104 0xcfc03f807f003ffc 0xfcfc03f807f003ff

def z828 : W := mkw 0x0000000001001040 0x0000000000100104 0xcc003c007f003ffc 0x7cc003c007f003ff

def z829 : W := mkw 0x4fbebf5510580881 0x84fbebf551058088 0xdffffffff0703f8f 0xfdffffffff0703f8

def z830 : W := mkw 0x443e945500000000 0x0443e94550000000 0x50ffc1ff80000003 0x450ffc1ff8000000

def z831 : W := mkw 0x447e94d56d001566 0x0447e94d56d00156 0x903fc07fff003ffb 0x0903fc07fff003ff

def z832 : W := mkw 0x0000002810da2a81 0x80000002810da2a8 0xec083c7870fe3f8d 0x7ec083c7870fe3f8

def z833 : W := mkw 0x51133f7703b17851 0x451133f7703b1785 0xf3ffffff8ff1f87f 0xff3ffffff8ff1f87

def z834 : W := mkw 0x2eecc9807c4c852e 0x02eecc9807c4c852 0x0cc8c180700e0000 0x40cc8c180700e000

def z835 : W := mkw 0x4b86ab0500000000 0x04b86ab050000000 0x5fcfffff80000007 0xf5fcfffff8000000

def z836 : W := mkw 0x2eedc0007e6d8008 0x02eedc0007e6d800 0xbfffc0007fffc008 0x6bfffc0007fffc00

def z837 : W := mkw 0x4bc4ab816d001566 0x04bc4ab816d00156 0xcfc0ff81ff003ffc 0xfcfc0ff81ff003ff

def z838 : W := mkw 0x4fbebf5501001040 0x04fbebf550100104 0xdfffffff87001807 0xfdfffffff8700180

def z839 : W := mkw 0x4ebe945500000000 0x04ebe94550000000 0x5fffc3ff80000007 0xf5fffc3ff8000000

def z840 : W := mkw 0x51123f7f01927ad1 0xc51123f7f01927ad 0x40003fff80003ff4 0x040003fff80003ff

def z841 : W := mkw 0x4fbebf5500000000 0x04fbebf550000000 0x5fffffff8800207f 0xf5fffffff8800207

def z842 : W := mkw 0x1113326603b17851 0x41113326603b1785 0xf3f733e60ff1f87f 0xff3f733e60ff1f87

def z843 : W := mkw 0x443e947d10da2a81 0x8443e947d10da2a8 0xfc3f3c7870fe3f8d 0x7fc3f3c7870fe3f8

def z844 : W := mkw 0x4fbebf5500000000 0x04fbebf550000000 0x1fffc3ff80000003 0xf1fffc3ff8000000

def z845 : W := mkw 0x0001000003211040 0x0000100000321104 0xb33700000ff1f87b 0xbb33700000ff1f87

def z846 : W := mkw 0x4fbebf5510580881 0x84fbebf551058088 0x5fffffff80700007 0xf5fffffff8070000

def z847 : W := mkw 0x51123fff81927e75 0x651123fff81927e7 0x40003fff80003e74 0x040003fff80003e7

def z848 : W := mkw 0x104140aaefb7ff77 0x6104140aaefb7ff7 0xa00000007ffffff8 0x0a00000007ffffff

def z849 : W := mkw 0x1113326603b17851 0x41113326603b1785 0xb33730000ff1f87b 0xbb33730000ff1f87

def z850 : W := mkw 0x2eedc0807e6d842c 0x02eedc0807e6d842 0xffffff807fffffff 0xfffffff807ffffff

def z851 : W := mkw 0x4fbebf5500000000 0x04fbebf550000000 0xdfffffff8000380f 0xfdfffffff8000380

def z852 : W := mkw 0x4fbebf5500000000 0x04fbebf550000000 0x5fcfffff80000006 0xc5fcfffff8000000

def z853 : W := mkw 0x0bc22b846d001566 0x00bc22b846d00156 0xdfc73f867f003ffe 0xfdfc73f867f003ff

def z854 : W := mkw 0x4fbebf5500100881 0x84fbebf550010088 0x5fffffff80001987 0xf5fffffff8000198

def z855 : W := mkw 0x0438145010580881 0x8043814501058088 0xec383c0070fe3f8d 0x7ec383c0070fe3f8

def z856 : W := mkw 0x2eedc0007e6d8008 0x02eedc0007e6d800 0x3fffc0007fffc003 0xc3fffc0007fffc00

def z857 : W := mkw 0x1103222603a17050 0x41103222603a1705 0xb33702660ff1e07f 0xbb33702660ff1e07

def z858 : W := mkw 0x111236fe81927ef5 0xe111236fe81927ef 0x40003fff80003ff4 0x040003fff80003ff

def z859 : W := mkw 0x0bc06b806d049566 0x00bc06b806d04956 0xcfc0ff807f01fffe 0xfcfc0ff807f01fff

def z860 : W := mkw 0x0438147810da2a81 0x80438147810da2a8 0xecf8fdf9f0fe3f8d 0x7ecf8fdf9f0fe3f8

def z861 : W := mkw 0x2eecc088fc4e862c 0x22eecc088fc4e862 0x0cc8c000700e0600 0x40cc8c000700e060

def z862 : W := mkw 0x0ee900007e690000 0x00ee900007e69000 0xbfff00007fffc00b 0xfbfff00007fffc00

def z863 : W := mkw 0x1113326e83b37a51 0x61113326e83b37a5 0xb337327f8ff1f87f 0xbb337327f8ff1f87

def z864 : W := mkw 0x1113367603b17851 0x41113367603b1785 0xf3373e7e0ff1f87f 0xbf3373e7e0ff1f87

def z865 : W := mkw 0x6eedcd917e6d852e 0x06eedcd917e6d852 0xffffcd99ffffc78b 0xfffffcd99ffffc78

def z866 : W := mkw 0x0b802b0025001142 0x00b802b002500114 0xcf003e007f003ffc 0xfcf003e007f003ff

def z867 : W := mkw 0x4fbebf5500000000 0x04fbebf550000000 0xdfffffff8f00000f 0xfdfffffff8f00000

def z868 : W := mkw 0x0438147a10da6a91 0x80438147a10da6a9 0xecf8fffff8ffffff 0xfecf8fffff8fffff

def z869 : W := mkw 0x6eedcd117e6d8008 0x06eedcd117e6d800 0xffffcfffffffc00f 0xfffffcfffffffc00

def z870 : W := mkw 0x0ac000806d001566 0x00ac000806d00156 0xcfc03c007f003ffc 0xfcfc03c007f003ff

def z871 : W := mkw 0x4fbebf5500000000 0x04fbebf550000000 0xdffffffff000000f 0xfdffffffff000000

def z872 : W := mkw 0x5113367703b17851 0x45113367703b1785 0xb337327f8ff1f87f 0xbb337327f8ff1f87

def z873 : W := mkw 0x0040408ac806c634 0x20040408ac806c63 0x40c8c3ffc80fc677 0xd40c8c3ffc80fc67

def z874 : W := mkw 0x0bc02b806d001566 0x00bc02b806d00156 0xccc03f807f003ffc 0x4ccc03f807f003ff

def z875 : W := mkw 0x0b802b8025001566 0x00b802b802500156 0xcf003f8077003ffc 0x7cf003f8077003ff

def z876 : W := mkw 0x2eecc988fc4e872e 0x22eecc988fc4e872 0x4cc8cd99f00e0780 0x44cc8cd99f00e078

def z877 : W := mkw 0x3bc7eb866f25d57e 0x43bc7eb866f25d57 0x13c7c3860f01c072 0x813c7c3860f01c07

def z878 : W := mkw 0x4b86ab0500000000 0x04b86ab050000000 0x13cfc3ff80000003 0x813cfc3ff8000000

def z879 : W := mkw 0x1103220603215050 0x4110322060321505 0x933702060f71c072 0xa933702060f71c07

def z880 : W := mkw 0x0000002a00826210 0x00000002a0082621 0x60c8c3ffc88fe67f 0xd60c8c3ffc88fe67

def z881 : W := mkw 0x2ac5c0007e6d8008 0x02ac5c0007e6d800 0xb3f7c0007fffc00b 0xbb3f7c0007fffc00

def z882 : W := mkw 0x0010147810da2a81 0x80010147810da2a8 0xec003c7870fe3f8c 0x7ec003c7870fe3f8

def z883 : W := mkw 0x4fbebf5510480000 0x04fbebf551048000 0xdfffffffb0700007 0xfdfffffffb070000

def z884 : W := mkw 0x0eedc0004a258000 0x00eedc0004a25800 0xbfffc0004fffc00b 0xfbfffc0004fffc00

def z885 : W := mkw 0x0bc06b806d049566 0x00bc06b806d04956 0xcfc8ff807f0e3ffc 0xfcfc8ff807f0e3ff

def z886 : W := mkw 0x4fbebf5500000000 0x04fbebf550000000 0x53ffffff80000007 0x853ffffff8000000

def z887 : W := mkw 0x2bc4eb806d04956e 0x02bc4eb806d04956 0xcfc0ff807f003ffc 0xfcfc0ff807f003ff

def z888 : W := mkw 0x0bc02b806d001566 0x00bc02b806d00156 0xcfc03f803f003ff4 0xacfc03f803f003ff

def z889 : W := mkw 0x0438147810da2a81 0x80438147810da2a8 0xff3f3c7870fe3f8f 0xfff3f3c7870fe3f8

def z890 : W := mkw 0x2eedc9007e6d810a 0x02eedc9007e6d810 0xbfffcc007fffc18b 0xfbfffcc007fffc18

def z891 : W := mkw 0x0438106010d82801 0x00438106010d8280 0xec383c6070fe3f8d 0x7ec383c6070fe3f8

def z892 : W := mkw 0x0011106202b16811 0x00011106202b1681 0xb33732660ff1f87f 0xbb33732660ff1f87

def z893 : W := mkw 0x004000806d001566 0x0004000806d00156 0x8c003c007f003ff8 0x28c003c007f003ff

def z894 : W := mkw 0x1113326603b17851 0x41113326603b1785 0xb33732660ff1f87c 0x2b33732660ff1f87

def z895 : W := mkw 0x4fbebf5500000000 0x04fbebf550000000 0xdfffffffb0001987 0xfdfffffffb000198

def z896 : W := mkw 0x4faeab0500000000 0x04faeab050000000 0x5fffc3ff80000007 0xf5fffc3ff8000000

def z897 : W := mkw 0x2eedc0807e6d842c 0x02eedc0807e6d842 0xbfffc0007fffe67b 0xfbfffc0007fffe67

def z898 : W := mkw 0x51133f7f03b37ad1 0xc51133f7f03b37ad 0xf3373fff8ff1ffff 0xbf3373fff8ff1fff

def z899 : W := mkw 0x2eedc0807e6d852e 0x02eedc0807e6d852 0xbfffc0007fffc78b 0xfbfffc0007fffc78

def z900 : W := mkw 0x1103220603215050 0x4110322060321505 0x333702060ff1c073 0x8333702060ff1c07

def z901 : W := mkw 0x2eecc0807c4c842c 0x02eecc0807c4c842 0x4cc8c180700e0600 0x44cc8c180700e060

def z902 : W := mkw 0x1113324403311841 0x4111332440331184 0xb33732000ff1f87f 0xbb33732000ff1f87

def z903 : W := mkw 0x1113326603b17851 0x41113326603b1785 0xf33733ff8ff1f87f 0xbf33733ff8ff1f87

def z904 : W := mkw 0x004040aac886e634 0x2004040aac886e63 0x60c8c3ff888fc077 0xd60c8c3ff888fc07

def z905 : W := mkw 0x4b96bf5500000000 0x04b96bf550000000 0x53cfffff80000007 0xd53cfffff8000000

def z906 : W := mkw 0x4fbebf5500000000 0x04fbebf550000000 0x5fffffffc000260f 0xf5fffffffc000260

def z907 : W := mkw 0x1001000203215050 0x4100100020321505 0xb33700000ff1c07b 0xbb33700000ff1c07

def z908 : W := mkw 0x0bc02b806d001566 0x00bc02b806d00156 0xcfc03fe67f003fff 0xfcfc03fe67f003ff

def z909 : W := mkw 0x1113326e03b37ad1 0xc1113326e03b37ad 0xb33732660ff1ffff 0xbb33732660ff1fff

def z910 : W := mkw 0x2bc5eb82ef25d57e 0x22bc5eb82ef25d57 0x13c7c3878f01c072 0x813c7c3878f01c07

def z911 : W := mkw 0x0438147810da2a81 0x80438147810da2a8 0xec383ffff0fe3f8d 0x7ec383ffff0fe3f8

def z912 : W := mkw 0x104140aadbfffef5 0xe104140aadbfffef 0xa00000007ffffff8 0x0a00000007ffffff

def z913 : W := mkw 0x143a147e10da6a91 0xc143a147e10da6a9 0xec383c7e70fe3f8d 0x7ec383c7e70fe3f8

def z914 : W := mkw 0x4fbebf5500000000 0x04fbebf550000000 0x5fffcfff80000003 0xc5fffcfff8000000

def z915 : W := mkw 0x004040224884e010 0x0004040224884e01 0x60c8c3ffc88fe07f 0xd60c8c3ffc88fe07

def z916 : W := mkw 0x11133b6603b17953 0x411133b6603b1795 0xb3373e660ff1f9ff 0xbb3373e660ff1f9f

def z917 : W := mkw 0x4fbebf5510480000 0x04fbebf551048000 0x5ffffffff00e0007 0xf5ffffffff00e000

def z918 : W := mkw 0x0b802b8025001566 0x00b802b802500156 0x8f003c0037003ff0 0x28f003c0037003ff

def z919 : W := mkw 0x4fbebf5500000000 0x04fbebf550000000 0x5fffffff80003f87 0xf5fffffff80003f8

def z920 : W := mkw 0x0001400002258000 0x0000140000225800 0xb33fc0000fffc00b 0xbb33fc0000fffc00

def z921 : W := mkw 0x0010106800922a01 0x00010106800922a0 0xec383c7870fe3f8d 0x7ec383c7870fe3f8

def z922 : W := mkw 0x0000002810da2a81 0x80000002810da2a8 0xac003c0070fe3f88 0x2ac003c0070fe3f8

def z923 : W := mkw 0x1113326603b17851 0x41113326603b1785 0x333732660ff1c077 0xb333732660ff1c07

def z924 : W := mkw 0x0438147810da2a81 0x80438147810da2a8 0xcc383c78707e3f84 0x6cc383c78707e3f8

def z925 : W := mkw 0x2eedc0007e6d8008 0x02eedc0007e6d800 0xffffcc007fffc78b 0xfffffcc007fffc78

def z926 : W := mkw 0x0000000000000000 0x0000000000000000 0x53ffc3ff80000007 0xf53ffc3ff8000000

def z927 : W := mkw 0x4bc6ab856d001566 0x04bc6ab856d00156 0xdfcfffffff003fff 0xfdfcfffffff003ff

def z928 : W := mkw 0x4fbebf5524000000 0x04fbebf552400000 0xdfffffffb7000007 0xfdfffffffb700000

def z929 : W := mkw 0x0bc06b80ed049566 0x20bc06b80ed04956 0xcfc0ff81ff003ffc 0xfcfc0ff81ff003ff

def z930 : W := mkw 0x04381458105a0a81 0x804381458105a0a8 0xcc383c18707e3f8c 0x7cc383c18707e3f8

def z931 : W := mkw 0x4fbebf5500000000 0x04fbebf550000000 0x5ffffffff0000787 0xf5ffffffff000078

def z932 : W := mkw 0x4fbebf5501001040 0x04fbebf550100104 0xdfffffffff003fff 0xfdfffffffff003ff

def z933 : W := mkw 0x51133b6703b17851 0x451133b6703b1785 0xb33733e78ff1f87f 0xbb33733e78ff1f87

def z934 : W := mkw 0x4ebe9d5500000000 0x04ebe9d550000000 0x5fffcdff80000003 0xf5fffcdff8000000

def z935 : W := mkw 0x4fbebf5500000000 0x04fbebf550000000 0x53ffc3ff80000007 0xd53ffc3ff8000000

def z936 : W := mkw 0x0bc06b806d049566 0x00bc06b806d04956 0xefc8ffffff8fffff 0xfefc8ffffff8ffff

def z937 : W := mkw 0x4fbebf5501001040 0x04fbebf550100104 0x5fffffff8f000077 0xf5fffffff8f00007

def z938 : W := mkw 0x2eedc9807e6d852e 0x02eedc9807e6d852 0xfffffd807fffff8f 0xffffffd807fffff8

def z939 : W := mkw 0x0438147810da2a81 0x80438147810da2a8 0xef383c787ffe3f8d 0xfef383c787ffe3f8

def z940 : W := mkw 0x443a147d10da2a81 0x8443a147d10da2a8 0xec383c7ff0fe3f8d 0x7ec383c7ff0fe3f8

def z941 : W := mkw 0x0438147810da2a81 0x80438147810da2a8 0xec38fc7ff0fe3f8f 0x7ec38fc7ff0fe3f8

def z942 : W := mkw 0x104140aacba7f674 0x6104140aacba7f67 0x200000004f8fe678 0x0200000004f8fe67

def z943 : W := mkw 0x543f947f12fb6a91 0xc543f947f12fb6a9 0x303fc07f80ffc003 0x0303fc07f80ffc00

def z944 : W := mkw 0x4ebe9d5500000000 0x04ebe9d550000000 0x5cffcfff80000007 0xd5cffcfff8000000

def z945 : W := mkw 0x41123f5500000000 0x041123f550000000 0x53ffffff80000007 0xf53ffffff8000000

def z946 : W := mkw 0x2eedc0007e6d8008 0x02eedc0007e6d800 0xffffc199ffffc00b 0xfffffc199ffffc00

def z947 : W := mkw 0x0429000012690000 0x0042900001269000 0xb33f00000fffc00b 0xbb33f00000fffc00

def z948 : W := mkw 0x1113326e03b37a51 0x41113326e03b37a5 0xb33732664ffffe7f 0xbb33732664ffffe7

def z949 : W := mkw 0x1113326e03b37a51 0x41113326e03b37a5 0xff3f3e7e7fffffff 0xfff3f3e7e7ffffff

def z950 : W := mkw 0x0bc02b806d001566 0x00bc02b806d00156 0x8fc03c007f003ff8 0xf8fc03c007f003ff

def z951 : W := mkw 0x6eedc4117e6d8008 0x06eedc4117e6d800 0xbfffc019ffffc00b 0xfbfffc019ffffc00

def z952 : W := mkw 0x1013106602b16811 0x41013106602b1681 0xb33702660ff1e07f 0xbb33702660ff1e07

def z953 : W := mkw 0x2eedc0007e6d8008 0x02eedc0007e6d800 0xbfffc00077ffc003 0x6bfffc00077ffc00

def z954 : W := mkw 0x1001002203b17851 0x41001002203b1785 0xb33700000ff1f878 0x2b33700000ff1f87

def z955 : W := mkw 0x1113326603b17851 0x41113326603b1785 0xf3373e660ff1ffff 0xbf3373e660ff1fff

def z956 : W := mkw 0x0b806b2aa586f352 0x20b806b2aa586f35 0xaf08fc7fb78fd983 0x2af08fc7fb78fd98

def z957 : W := mkw 0x204140aafeffeebd 0xa204140aafeffeeb 0xa00000007ffffff8 0x0a00000007ffffff

def z958 : W := mkw 0x0438147810da2a81 0x80438147810da2a8 0xac303c6070fe3f8d 0x3ac303c6070fe3f8

def z959 : W := mkw 0x0000000010480000 0x0000000001048000 0xec003c0070fe3f8c 0x7ec003c0070fe3f8

def z960 : W := mkw 0x2eedc0007e6d8008 0x02eedc0007e6d800 0xffffc0007fffe60f 0xfffffc0007fffe60

def z961 : W := mkw 0x2eedc0007e6d8008 0x02eedc0007e6d800 0xbfffc0007fffff8b 0xfbfffc0007fffff8

def z962 : W := mkw 0x0bc02b806d001566 0x00bc02b806d00156 0xcf003c007f003ffc 0x7cf003c007f003ff

def z963 : W := mkw 0x453eb65500000000 0x0453eb6550000000 0x53fff3ff80000007 0xf53fff3ff8000000

def z964 : W := mkw 0x111232ee81927e75 0x6111232ee81927e7 0x0000326600003e74 0x00000326600003e7

def z965 : W := mkw 0x1113326603b17851 0x41113326603b1785 0xff373e660ff1f87f 0xfff373e660ff1f87

def z966 : W := mkw 0x0140228049001464 0x0014022804900146 0xcfc03f807f003ffc 0xfcfc03f807f003ff

def z967 : W := mkw 0x004040aac886e634 0x2004040aac886e63 0x60c8c3ffc88fe67c 0x460c8c3ffc88fe67

def z968 : W := mkw 0x0438147810da2a81 0x80438147810da2a8 0xec083c7870fe3f8c 0x4ec083c7870fe3f8

def z969 : W := mkw 0x443e947d10da2a81 0x8443e947d10da2a8 0xfcfffffff0fe3f8f 0xffcfffffff0fe3f8

def z970 : W := mkw 0x4ebe9d5500000000 0x04ebe9d550000000 0x10ffc1ff80000003 0x010ffc1ff8000000

def z971 : W := mkw 0x0010106810da2a81 0x80010106810da2a8 0xec303c6070fe3f8d 0x7ec303c6070fe3f8

def z972 : W := mkw 0x2eadc000366d8008 0x02eadc000366d800 0xbf3fc0003fffc00b 0xbbf3fc0003fffc00

def z973 : W := mkw 0x2eedc0007e6d8008 0x02eedc0007e6d800 0xbf3700007fffc00b 0xbbf3700007fffc00

def z974 : W := mkw 0x1113326e03b37a51 0x41113326e03b37a5 0xf337327e0ff1fe7f 0xbf337327e0ff1fe7

def z975 : W := mkw 0x2eedc0807e6d842c 0x02eedc0807e6d842 0xbfffc3807fffc07b 0xfbfffc3807fffc07

def z976 : W := mkw 0x04280418104a0280 0x804280418104a028 0xec383c1870fe3f8d 0x7ec383c1870fe3f8

def z977 : W := mkw 0x046940005a6d8000 0x0046940005a6d800 0xbfffc0007fffc00b 0xfbfffc0007fffc00

def z978 : W := mkw 0x11123bee81927f77 0x611123bee81927f7 0x40003fff80003ff4 0x040003fff80003ff

def z979 : W := mkw 0x00404082c804c434 0x200404082c804c43 0x60c8c3ffc88fc07f 0xd60c8c3ffc88fc07

def z980 : W := mkw 0x1113326603b17851 0x41113326603b1785 0xb33702660ff1f87b 0x8b33702660ff1f87

def z981 : W := mkw 0x004040aac886e634 0x2004040aac886e63 0x60c8c3ffc88fc673 0xc60c8c3ffc88fc67

def z982 : W := mkw 0x2eedc0007e6d8008 0x02eedc0007e6d800 0xb3ffc0000fffc00b 0xbb3ffc0000fffc00

def z983 : W := mkw 0x01402b806d001566 0x001402b806d00156 0xcc003f807f003ffc 0x7cc003f807f003ff

def z984 : W := mkw 0x0438147a10da6a91 0x80438147a10da6a9 0xec383e7e70fe3ffd 0x7ec383e7e70fe3ff

def z985 : W := mkw 0x0438147810da2a81 0x80438147810da2a8 0xec383c7870fe1f81 0x6ec383c7870fe1f8

def z986 : W := mkw 0x4eac8d1100000000 0x04eac8d110000000 0x5fffcfff80000007 0xf5fffcfff8000000

def z987 : W := mkw 0x0bc02b806d001566 0x00bc02b806d00156 0xcfc8ff807f003fff 0xfcfc8ff807f003ff

def z988 : W := mkw 0x1113326603b17851 0x41113326603b1785 0xb3fff2660ff1f87f 0xfb3fff2660ff1f87

def z989 : W := mkw 0x0bc02b806d001566 0x00bc02b806d00156 0x8f003e007f003ffc 0xb8f003e007f003ff

def z990 : W := mkw 0x204140aaffeff77e 0x2204140aaffeff77 0xa00000007ffffff8 0x0a00000007ffffff

def z991 : W := mkw 0x04381458105a0a81 0x804381458105a0a8 0xec383c1870fe1f89 0x7ec383c1870fe1f8

def z992 : W := mkw 0x2eedc0007e6d8008 0x02eedc0007e6d800 0xbfffc2667fffc00f 0xfbfffc2667fffc00

def z993 : W := mkw 0x0438147810da2a81 0x80438147810da2a8 0xac383c0070fe3f89 0x7ac383c0070fe3f8

def z994 : W := mkw 0x004040aac886e634 0x2004040aac886e63 0x60c8ffffc88fffff 0xd60c8ffffc88ffff

def z995 : W := mkw 0x0438147810da2a81 0x80438147810da2a8 0xec383e7878fe3ffd 0xfec383e7878fe3ff

def z996 : W := mkw 0x014022806d001566 0x0014022806d00156 0xcf003e007f003ffc 0xfcf003e007f003ff

def z997 : W := mkw 0x11133b6603b17851 0x411133b6603b1785 0xf3373fe60ff1f87f 0xbf3373fe60ff1f87

def z998 : W := mkw 0x4fbebf5500000000 0x04fbebf550000000 0x5ffffdff80000003 0x65ffffdff8000000

def z999 : W := mkw 0x0428002810ca2200 0x00428002810ca220 0xec383c7870fe3f8d 0x7ec383c7870fe3f8

def z1000 : W := mkw 0x004040aac886e634 0x2004040aac886e63 0x60c8c3ff888fe677 0x860c8c3ff888fe67

def z1001 : W := mkw 0x0102220400000000 0x0010222040000000 0x53cfc3ff80000007 0xd53cfc3ff8000000

def z1002 : W := mkw 0x2bc16b806f25956e 0x02bc16b806f25956 0x03c003800f01c070 0x803c003800f01c07

def z1003 : W := mkw 0x204140aaeea7e63c 0x2204140aaeea7e63 0x200000004f8fe678 0x0200000004f8fe67

def z1004 : W := mkw 0x0040408048048424 0x0004040804804842 0x60c8c3ffc88fe67f 0xd60c8c3ffc88fe67

def z1005 : W := mkw 0x0438147810da2a81 0x80438147810da2a8 0xecf83ff870fe3f8d 0xfecf83ff870fe3f8

def z1006 : W := mkw 0x004140004a258000 0x0004140004a25800 0xb33700004fffc00b 0xbb33700004fffc00

def z1007 : W := mkw 0x443e945500000000 0x0443e94550000000 0x10ffc3ff80000003 0x810ffc3ff8000000

def z1008 : W := mkw 0x4fbebf5500000000 0x04fbebf550000000 0x5fffffff80000004 0x65fffffff8000000

def z1009 : W := mkw 0x6eedc9017e6d8008 0x06eedc9017e6d800 0xbfffc181ffffc00b 0xfbfffc181ffffc00

def z1010 : W := mkw 0x004040aac896ee35 0x2004040aac896ee3 0xe0c8c3ffc8fffe7f 0xde0c8c3ffc8fffe7

def z1011 : W := mkw 0x343fd47e12ffea99 0xc343fd47e12ffea9 0x303fc07e00ffc003 0x0303fc07e00ffc00

def z1012 : W := mkw 0x043a147c10da2a81 0x8043a147c10da2a8 0xfc3f3c7e70fe3f8f 0x7fc3f3c7e70fe3f8

def z1013 : W := mkw 0x5fbebf5501101841 0x45fbebf550110184 0x5fffffff80001807 0xf5fffffff8000180

def z1014 : W := mkw 0x004040aac886e634 0x2004040aac886e63 0xe0f8c3ffc8ffe67f 0xfe0f8c3ffc8ffe67

def z1015 : W := mkw 0x1001002203b17851 0x41001002203b1785 0xb33702660ff1f87f 0xbb33702660ff1f87

def z1016 : W := mkw 0x246dc0005a6d8008 0x0246dc0005a6d800 0xb3ffc0004fffc00b 0xfb3ffc0004fffc00

def z1017 : W := mkw 0x1113326603b17851 0x41113326603b1785 0xb33730660ff1f87b 0x2b33730660ff1f87

def z1018 : W := mkw 0x0bc02b806d001566 0x00bc02b806d00156 0xcfc03f8077003ff4 0x6cfc03f8077003ff

def z1019 : W := mkw 0x6bc7eb856f25956e 0x06bc7eb856f25956 0x13c7c3878f01c072 0x813c7c3878f01c07

def z1020 : W := mkw 0x0428002810da2a81 0x80428002810da2a8 0xec383c0070fe3f8d 0x7ec383c0070fe3f8

def z1021 : W := mkw 0x0b802b8025001566 0x00b802b802500156 0xcfc03f8037003ff4 0xfcfc03f8037003ff

def z1022 : W := mkw 0x4fbebf5510580881 0x84fbebf551058088 0xfffffffff0fe198f 0xffffffffff0fe198

def z1023 : W := mkw 0x1113326e03b37a51 0x41113326e03b37a5 0xb33f327e0ffff87f 0xbb33f327e0ffff87

def z1024 : W := mkw 0x443c947910da2a81 0x8443c947910da2a8 0xec38fc79f0fe3f8d 0x7ec38fc79f0fe3f8

def z1025 : W := mkw 0x0bc02b806d001566 0x00bc02b806d00156 0xcfc83ff87f003ffd 0xfcfc83ff87f003ff

def z1026 : W := mkw 0x2ead800036690008 0x02ead80003669000 0xbf3f00007fffc00b 0xfbf3f00007fffc00

def z1027 : W := mkw 0x0bc06b806d049566 0x00bc06b806d04956 0xefc03f807f8ffffc 0xfefc03f807f8ffff

def z1028 : W := mkw 0x20014000126d8008 0x020014000126d800 0xb33700000fffc00b 0xbb33700000fffc00

def z1029 : W := mkw 0x2eedc0007e6d8008 0x02eedc0007e6d800 0xbf3f00007fffc009 0x7bf3f00007fffc00

def z1030 : W := mkw 0x1113326603b17851 0x41113326603b1785 0xbf373e663ff1f9ff 0xbbf373e663ff1f9f

def z1031 : W := mkw 0x1113326603b17851 0x41113326603b1785 0xb33ff27f8ff1f87f 0xbb33ff27f8ff1f87

def z1032 : W := mkw 0x1113324603315851 0x4111332460331585 0xb33732060ff1d87b 0xbb33732060ff1d87

def z1033 : W := mkw 0x6fbebf5534480008 0x06fbebf553448000 0x5fffffffb0000007 0xf5fffffffb000000

def z1034 : W := mkw 0x4fbebf5500000000 0x04fbebf550000000 0x5ff7ffff80000006 0xa5ff7ffff8000000

def z1035 : W := mkw 0x4ebe9d5500000000 0x04ebe9d550000000 0x5cfffdff80000007 0x75cfffdff8000000

def z1036 : W := mkw 0x1113326e03b37a51 0x41113326e03b37a5 0xf3fff3ffcffffe7f 0xff3fff3ffcffffe7

def z1037 : W := mkw 0x2eedc0807e6d842c 0x02eedc0807e6d842 0xffffc3ffffffe67f 0xfffffc3ffffffe67

def z1038 : W := mkw 0x4fbebf5510480080 0x84fbebf551048008 0x5fffffffb0000187 0xf5fffffffb000018

def z1039 : W := mkw 0x1112367e01927ad1 0xc1112367e01927ad 0x0000327e00003874 0x00000327e0000387

def z1040 : W := mkw 0x0101220003211040 0x0010122000321104 0xb33702000ff1c07b 0xbb33702000ff1c07

def z1041 : W := mkw 0x0a84800000000000 0x00a8480000000000 0x53cfc3ff80000007 0xd53cfc3ff8000000

def z1042 : W := mkw 0x0bc4ab806d001566 0x00bc4ab806d00156 0xdfc7ff807f003ffe 0xfdfc7ff807f003ff

def z1043 : W := mkw 0x0000402a8086e210 0x20000402a8086e21 0x60c8c3ff888fe07f 0xd60c8c3ff888fe07

def z1044 : W := mkw 0x0113324403211040 0x0011332440321104 0xb33732660ff1f87f 0xbb33732660ff1f87

def z1045 : W := mkw 0x4bc6ab856d001566 0x04bc6ab856d00156 0xdfc73f807f003ffc 0xfdfc73f807f003ff

def z1046 : W := mkw 0x2eedc0007e6d8008 0x02eedc0007e6d800 0x33ffc0004fffc00b 0xd33ffc0004fffc00

def z1047 : W := mkw 0x1bc36b86ef25d576 0x61bc36b86ef25d57 0x13c7c3878f01c072 0x813c7c3878f01c07

def z1048 : W := mkw 0x0438147810da2a81 0x80438147810da2a8 0xac383c7870fe3f89 0x2ac383c7870fe3f8

def z1049 : W := mkw 0x2eedc0007e6d8008 0x02eedc0007e6d800 0xbff700007fffc008 0xfbff700007fffc00

def z1050 : W := mkw 0x204140007e6d8008 0x0204140007e6d800 0xb3ffc0007fffc00b 0xfb3ffc0007fffc00

def z1051 : W := mkw 0x0bc02b806d001566 0x00bc02b806d00156 0xeff03f807ff03ffd 0xfeff03f807ff03ff

def z1052 : W := mkw 0x042c800000000000 0x0042c80000000000 0x50ffc3ff80000007 0xd50ffc3ff8000000

def z1053 : W := mkw 0x0bc02b806d001566 0x00bc02b806d00156 0xcfc0ff87ff003ffe 0xfcfc0ff87ff003ff

def z1054 : W := mkw 0x0438147810da2a81 0x80438147810da2a8 0xecf8fc7870fe3f8f 0xfecf8fc7870fe3f8

def z1055 : W := mkw 0x4fbebf55355819c3 0x84fbebf55355819c 0xdfffffffb7701987 0xfdfffffffb770198

def z1056 : W := mkw 0x2eedc0007e6d8008 0x02eedc0007e6d800 0xbf3fc0007fffc00b 0x2bf3fc0007fffc00

def z1057 : W := mkw 0x0428043810da2a81 0x80428043810da2a8 0xec083c1870fe3f8c 0x7ec083c1870fe3f8

def z1058 : W := mkw 0x4fbebf5500000000 0x04fbebf550000000 0xffffffff80f0000f 0xfffffffff80f0000

def z1059 : W := mkw 0x004040aac886e634 0x2004040aac886e63 0x20c8c3ffc88fc07b 0xd20c8c3ffc88fc07

def z1060 : W := mkw 0x4b96bf5500000000 0x04b96bf550000000 0x5fc7ffff80000006 0xf5fc7ffff8000000

def z1061 : W := mkw 0x043c947810da2a81 0x8043c947810da2a8 0xfc3ffc7870fe3f8f 0x7fc3ffc7870fe3f8

def z1062 : W := mkw 0x2eedc9807e6d852e 0x02eedc9807e6d852 0xbfffc1807fffc00b 0xfbfffc1807fffc00

def z1063 : W := mkw 0x0bc02b806d001566 0x00bc02b806d00156 0xdff73f807f003fff 0xfdff73f807f003ff

def z1064 : W := mkw 0x1113326603b17851 0x41113326603b1785 0xf33732664ff1fe7f 0xff33732664ff1fe7

def z1065 : W := mkw 0x304140aafffffe7d 0x6304140aafffffe7 0xa00000007ffffe78 0x0a00000007ffffe7

def z1066 : W := mkw 0x0111326003b13841 0x00111326003b1384 0xb33732600ff1f87f 0xbb33732600ff1f87

def z1067 : W := mkw 0x1113324603315851 0x4111332460331585 0x933732660f71d877 0xb933732660f71d87

def z1068 : W := mkw 0x2ac5c0006e258008 0x02ac5c0006e25800 0xb3ffc0004fffc00b 0xfb3ffc0004fffc00

def z1069 : W := mkw 0x053a365400000000 0x0053a36540000000 0x5fffffff80000007 0xf5fffffff8000000

def z1070 : W := mkw 0x4006800500000000 0x0400680050000000 0x50cfc3ff80000007 0xd50cfc3ff8000000

def z1071 : W := mkw 0x4fbebf5501001142 0x04fbebf550100114 0x5fffffff80001987 0xf5fffffff8000198

def z1072 : W := mkw 0x204140007e6d8008 0x0204140007e6d800 0xb33700007fffc008 0x2b33700007fffc00

def z1073 : W := mkw 0x004040aac886e634 0x2004040aac886e63 0x20c8c3ff888fe07f 0x920c8c3ff888fe07

def z1074 : W := mkw 0x2eedc0007e6d8008 0x02eedc0007e6d800 0x3fffc0000fffc003 0xf3fffc0000fffc00

def z1075 : W := mkw 0x243dd47a92ffea99 0xa243dd47a92ffea9 0x303fc07f80ffc003 0x0303fc07f80ffc00

def z1076 : W := mkw 0x1103222603b17851 0x41103222603b1785 0xb33702060ff1f87b 0xbb33702060ff1f87

def z1077 : W := mkw 0x4fbebf5500100801 0x04fbebf550010080 0xdfffffff80701807 0xfdfffffff8070180

def z1078 : W := mkw 0x004040aac886e634 0x2004040aac886e63 0x73ffc3ffc88fe67f 0xf73ffc3ffc88fe67

def z1079 : W := mkw 0x443e945500000000 0x0443e94550000000 0x5cffffff80000007 0xf5cffffff8000000

def z1080 : W := mkw 0x4faeaf1500000000 0x04faeaf150000000 0x5fcfcfff80000007 0xd5fcfcfff8000000

def z1081 : W := mkw 0x04381458105a0a81 0x804381458105a0a8 0xcc383c78707e1f85 0x7cc383c78707e1f8

def z1082 : W := mkw 0x4fbebf5500000000 0x04fbebf550000000 0x7fffffffc08e000f 0xf7fffffffc08e000

def z1083 : W := mkw 0x1113326603b17851 0x41113326603b1785 0xb33730600ff1f87d 0x3b33730600ff1f87

def z1084 : W := mkw 0x004040aac896eeb5 0xa004040aac896eeb 0x60c8c3ffc88fffff 0xd60c8c3ffc88ffff

def z1085 : W := mkw 0x0001000202214010 0x0000100020221401 0xb33702060ff1c07b 0xbb33702060ff1c07

def z1086 : W := mkw 0x0ac140006e258000 0x00ac140006e25800 0xbfffc0007fffc00b 0xfbfffc0007fffc00

def z1087 : W := mkw 0x0bc02b806d001566 0x00bc02b806d00156 0x8fc03f807f003ff8 0xa8fc03f807f003ff

def z1088 : W := mkw 0x2eedc0007e6d8008 0x02eedc0007e6d800 0xbffffc007fffd98b 0xfbffffc007fffd98

def z1089 : W := mkw 0x2eedc4107e6d8088 0x82eedc4107e6d808 0xbfffcc007fffc18b 0xfbfffcc007fffc18

def z1090 : W := mkw 0x0438147a10da6a91 0x80438147a10da6a9 0xec383c7878fffffd 0x7ec383c7878fffff

def z1091 : W := mkw 0x2eedc0007e6d8008 0x02eedc0007e6d800 0xfffffc007fffc00f 0xffffffc007fffc00

def z1092 : W := mkw 0x0438147810da2a81 0x80438147810da2a8 0xec383e7e70fe3f8f 0xfec383e7e70fe3f8

def z1093 : W := mkw 0x0bc02b806d001566 0x00bc02b806d00156 0xcfc03fffff003ffc 0xfcfc03fffff003ff

def z1094 : W := mkw 0x1113367e03b37ad1 0xc1113367e03b37ad 0xf33f3e7e4fffffff 0xff33f3e7e4ffffff

def z1095 : W := mkw 0x1113326603b17851 0x41113326603b1785 0xb33732660ff1d873 0xab33732660ff1d87

def z1096 : W := mkw 0x4fbebf5510480000 0x04fbebf551048000 0x7fffffff80fe0007 0xf7fffffff80fe000

def z1097 : W := mkw 0x2eedc9007e6d8008 0x02eedc9007e6d800 0xffffcd807fffc00b 0xfffffcd807fffc00

def z1098 : W := mkw 0x6eeccd917c4c852e 0x06eeccd917c4c852 0x4cc8cd99f00e0780 0x44cc8cd99f00e078

def z1099 : W := mkw 0x1101222203b17851 0x41101222203b1785 0xb33732000ff1f87f 0xbb33732000ff1f87

def z1100 : W := mkw 0x1112326e81927a51 0x61112326e81927a5 0x0000327f80003874 0x00000327f8000387

def z1101 : W := mkw 0x004040aac886e634 0x2004040aac886e63 0xe0c8f3ffc88ffe7f 0xfe0c8f3ffc88ffe7

def z1102 : W := mkw 0x1113324603315851 0x4111332460331585 0x933732060f71f87e 0xb933732060f71f87

def z1103 : W := mkw 0x4fbebf5525001142 0x04fbebf552500114 0xdffffffff7003f8f 0xfdffffffff7003f8

def z1104 : W := mkw 0x0bc02b806d001566 0x00bc02b806d00156 0x4fc03f807f003ff4 0xc4fc03f807f003ff

def z1105 : W := mkw 0x000040aa8086e634 0x2000040aa8086e63 0x60c8c3ff808fe677 0xd60c8c3ff808fe67

def z1106 : W := mkw 0x004140aacaa7e634 0x2004140aacaa7e63 0xa00000004fffe678 0x0a00000004fffe67

def z1107 : W := mkw 0x0ac000806c000424 0x00ac000806c00042 0xcfc03f807f003ffc 0xfcfc03f807f003ff

def z1108 : W := mkw 0x0fbeb24400000000 0x00fbeb2440000000 0x5ffff3ff80000007 0xf5ffff3ff8000000

def z1109 : W := mkw 0x6eeccd99fc4e862c 0x26eeccd99fc4e862 0x4cc8cd99f00e0600 0x44cc8cd99f00e060

def z1110 : W := mkw 0x2eedc0807e6d842c 0x02eedc0807e6d842 0xffffc1807fffc60b 0xfffffc1807fffc60

def z1111 : W := mkw 0x004040aaec86e736 0x2004040aaec86e73 0x60c8c3fff88fe7ff 0xd60c8c3fff88fe7f

def z1112 : W := mkw 0x1113324603315851 0x4111332460331585 0x933730000f71d870 0x2933730000f71d87

def z1113 : W := mkw 0x0bc02b806d001566 0x00bc02b806d00156 0xcf003f807f003ffc 0x2cf003f807f003ff

def z1114 : W := mkw 0x0001002202a16010 0x00001002202a1601 0xb33700000ff1e07b 0xbb33700000ff1e07

def z1115 : W := mkw 0x004040aac886e634 0x2004040aac886e63 0xe0c8c3fff88fffff 0xde0c8c3fff88ffff

def z1116 : W := mkw 0x2eedc4107e6d8008 0x02eedc4107e6d800 0xffffcc187fffc00b 0xfffffcc187fffc00

def z1117 : W := mkw 0x0ac009806d001566 0x00ac009806d00156 0xccc03d807f003ffc 0x7ccc03d807f003ff

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z0,z1,z2,z7,z3,z4,z5])],[(0,[z0,z1,z8,z2,z3,z4,z5]),(0,[z0,z1,z9,z2,z3,z4,z5]),(0,[z10,z0,z1,z2,z11,z4,z5]),(0,[z12,z0,z1,z2,z3,z4,z13]),(0,[z0,z1,z2,z3,z14,z4,z5])],[(0,[z0,z1,z2,z15,z3,z4,z5]),(0,[z0,z1,z16,z2,z3,z4,z5]),(0,[z0,z1,z2,z17,z11,z4,z5])],[(0,[z0,z1,z2,z3,z18,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z19]),(0,[z20,z0,z1,z2,z3,z4,z5])],[(0,[z21,z0,z22,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z23,z5]),(0,[z0,z1,z24,z2,z3,z4,z5])],[(0,[z0,z1,z2,z2,z3,z4,z5]),(0,[z0,z1,z2,z25,z3,z4,z5]),(0,[z26,z27,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z28,z29,z5]),(0,[z30,z0,z1,z2,z3,z4,z31]),(0,[z0,z1,z32,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z33,z4,z5]),(0,[z34,z0,z2,z3,z4,z35,z5])],[(0,[z0,z36,z1,z2,z3,z4,z37]),(0,[z0,z38,z2,z3,z4,z39,z5])],[(0,[z0,z1,z2,z40,z3,z4,z5]),(1,[z0,z1,z2,z41,z4,z5]),(0,[z12,z0,z1,z2,z3,z4,z35])]],
   [[(0,[z0,z42,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z43,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z44])],[(0,[z0,z1,z2,z3,z4,z45,z5]),(0,[z26,z46,z0,z1,z2,z4,z5]),(0,[z0,z1,z47,z2,z3,z4,z5]),(0,[z0,z1,z2,z48,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z37]),(0,[z0,z1,z2,z3,z4,z49,z5])],[(0,[z0,z1,z2,z3,z50,z4,z5]),(0,[z0,z1,z2,z3,z51,z4,z5])],[(0,[z52,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z53,z3,z4,z5])],[(0,[z0,z1,z2,z54,z55,z4,z5]),(0,[z0,z1,z2,z56,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z57,z5]),(0,[z58,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z59,z5]),(0,[z30,z0,z1,z2,z3,z4,z60]),(1,[z0,z1,z2,z3,z61,z5]),(0,[z0,z36,z2,z3,z4,z5,z37]),(0,[z0,z1,z3,z28,z4,z39,z5])],[(0,[z62,z0,z1,z2,z3,z63,z5]),(0,[z30,z0,z1,z2,z64,z3,z4]),(0,[z26,z0,z1,z2,z64,z4,z5])],[(0,[z65,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z66]),(0,[z46,z1,z2,z67,z3,z4,z5]),(0,[z68,z0,z1,z2,z69,z4,z5]),(0,[z0,z1,z2,z3,z4,z70,z5]),(0,[z71,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z72,z4,z5])]],
   [[(0,[z0,z22,z1,z2,z3,z4,z45]),(0,[z0,z1,z2,z3,z73,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z74]),(0,[z0,z1,z2,z75,z3,z4,z5]),(0,[z0,z1,z2,z3,z76,z5,z77]),(0,[z0,z1,z2,z3,z78,z4,z5]),(0,[z0,z1,z2,z3,z79,z4,z5])],[(0,[z0,z1,z80,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z81,z5]),(0,[z12,z0,z82,z1,z2,z3,z4]),(1,[z0,z82,z1,z2,z4,z83])],[(0,[z84,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z85,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z86,z4,z5]),(0,[z87,z0,z1,z2,z88,z4,z5]),(0,[z0,z1,z2,z89,z3,z4,z5]),(0,[z0,z1,z2,z90,z3,z4,z5]),(0,[z0,z1,z2,z3,z11,z4,z5]),(0,[z0,z1,z2,z3,z78,z4,z91])],[(0,[z0,z1,z2,z3,z4,z92,z5])],[(0,[z93,z0,z1,z94,z3,z4,z5]),(0,[z0,z1,z95,z2,z3,z4,z5]),(0,[z0,z1,z2,z96,z3,z4,z5]),(0,[z97,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z98])],[(0,[z30,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z99,z4,z5]),(0,[z34,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z64,z4,z76,z5])],[(0,[z30,z0,z100,z2,z3,z4,z5]),(0,[z101,z0,z1,z2,z3,z4,z5]),(1,[z0,z38,z2,z3,z4,z5]),(0,[z0,z1,z2,z102,z3,z4,z5])],[(0,[z0,z103,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z104,z5]),(0,[z0,z105,z1,z2,z3,z4,z5]),(0,[z0,z106,z1,z2,z3,z4,z5]),(0,[z107,z0,z1,z2,z3,z4,z5]),(0,[z108,z0,z1,z2,z3,z4,z5]),(0,[z109,z0,z1,z2,z3,z4,z5]),(0,[z0,z82,z1,z2,z64,z4,z5])]],
   [[(0,[z0,z22,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z110]),(0,[z0,z1,z2,z3,z4,z111,z5]),(0,[z0,z1,z2,z3,z112,z4,z5])],[(0,[z0,z1,z113,z2,z3,z4,z5])],[(0,[z114,z0,z1,z2,z3,z4,z5]),(0,[z114,z0,z115,z2,z3,z4,z5]),(1,[z12,z1,z2,z3,z4,z116]),(0,[z0,z1,z117,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z118,z5])],[(0,[z93,z0,z1,z2,z3,z4,z35]),(0,[z119,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z120,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z121,z5]),(0,[z122,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z60,z5]),(0,[z123,z0,z1,z2,z3,z4,z5]),(0,[z0,z124,z1,z3,z28,z4,z5]),(0,[z0,z1,z2,z3,z125,z4,z5]),(0,[z0,z1,z2,z3,z4,z126,z5])],[(0,[z0,z1,z2,z127,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z128,z5]),(0,[z0,z1,z2,z3,z129,z4,z5])],[(0,[z130,z0,z1,z2,z3,z4,z5]),(0,[z131,z0,z1,z2,z3,z4,z5]),(0,[z0,z132,z2,z133,z3,z4,z5]),(0,[z0,z134,z1,z2,z11,z4,z5]),(0,[z0,z1,z135,z2,z3,z4,z5])]],
   [[(0,[z0,z1,z2,z3,z4,z5,z136]),(1,[z0,z1,z2,z137,z4,z5])],[(1,[z0,z138,z1,z2,z3,z5]),(0,[z139,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z140,z5]),(0,[z0,z134,z1,z3,z141,z4,z5]),(0,[z0,z1,z2,z4,z76,z5,z83])],[(0,[z142,z0,z1,z94,z3,z4,z5]),(0,[z0,z143,z1,z2,z3,z4,z5]),(0,[z0,z1,z144,z2,z3,z4,z5]),(0,[z0,z1,z2,z145,z3,z4,z5]),(0,[z26,z0,z1,z2,z3,z39,z5]),(0,[z0,z146,z1,z2,z3,z4,z5])],[(0,[z147,z0,z1,z2,z3,z4,z5]),(0,[z0,z132,z2,z3,z148,z4,z5]),(0,[z0,z1,z2,z3,z4,z76,z5])],[(0,[z0,z1,z2,z149,z3,z4,z5]),(0,[z0,z1,z2,z150,z4,z92,z5]),(0,[z0,z1,z2,z3,z4,z151,z5])],[(0,[z0,z152,z1,z2,z3,z4,z5]),(0,[z0,z1,z94,z2,z3,z4,z153]),(0,[z30,z0,z1,z2,z3,z154,z5]),(0,[z0,z105,z132,z2,z3,z4,z5]),(0,[z155,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z156,z3,z55,z5]),(0,[z157,z0,z1,z2,z3,z4,z5])],[(1,[z0,z1,z2,z3,z4,z45]),(0,[z158,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z159,z5]),(1,[z0,z1,z2,z160,z4,z5]),(0,[z0,z161,z1,z2,z3,z4,z5])]],
   [[(0,[z0,z124,z1,z94,z3,z4,z5]),(0,[z10,z1,z2,z3,z54,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z162]),(0,[z163,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z64,z3,z4,z5])],[(0,[z87,z0,z1,z133,z3,z4,z5]),(0,[z164,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z165,z4,z5])],[(0,[z0,z1,z2,z3,z166,z4,z5]),(0,[z0,z167,z1,z2,z3,z4,z5]),(0,[z168,z0,z1,z2,z3,z92,z5]),(0,[z0,z1,z2,z169,z3,z39,z5]),(0,[z26,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z170]),(0,[z171,z0,z1,z2,z3,z4,z5])],[(0,[z62,z0,z1,z94,z3,z4,z5])],[(0,[z0,z1,z2,z3,z172,z4,z5]),(0,[z173,z0,z1,z2,z4,z92,z5]),(0,[z0,z1,z2,z3,z4,z174,z5]),(0,[z0,z1,z2,z41,z3,z4,z5]),(0,[z0,z1,z175,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z176,z4,z5])],[(0,[z177,z0,z1,z2,z3,z4,z5]),(0,[z178,z0,z1,z2,z3,z4,z5]),(0,[z179,z0,z1,z2,z3,z4,z5]),(0,[z26,z0,z1,z2,z3,z28,z5]),(0,[z0,z1,z2,z3,z4,z180,z5])],[(0,[z26,z0,z1,z2,z3,z181,z5])],[(0,[z182,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z183,z5]),(0,[z0,z38,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z31]),(0,[z0,z184,z1,z2,z3,z4,z5])]],
   [[(0,[z0,z185,z1,z2,z3,z4,z5]),(1,[z0,z100,z2,z3,z4,z5]),(0,[z0,z186,z1,z2,z55,z4,z5]),(1,[z0,z1,z2,z187,z4,z5]),(0,[z0,z134,z1,z2,z3,z4,z188]),(0,[z0,z1,z2,z3,z4,z5,z189]),(0,[z0,z1,z190,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z83])],[(0,[z46,z0,z1,z2,z67,z4,z5]),(0,[z0,z1,z2,z3,z191,z4,z5]),(0,[z0,z192,z1,z2,z3,z4,z5]),(0,[z27,z0,z1,z2,z3,z92,z5]),(0,[z0,z1,z2,z3,z193,z4,z5])],[(0,[z194,z0,z1,z2,z3,z4,z5]),(1,[z114,z22,z2,z3,z4,z5]),(0,[z0,z1,z2,z169,z3,z4,z5])],[(0,[z0,z1,z2,z195,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z196]),(0,[z68,z0,z105,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z197])],[(0,[z0,z186,z115,z2,z3,z4,z5]),(0,[z87,z0,z1,z2,z3,z198,z5]),(0,[z0,z1,z2,z3,z199,z39,z5]),(0,[z0,z36,z1,z2,z3,z4,z60]),(0,[z0,z200,z1,z2,z3,z4,z5])],[(0,[z87,z201,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z202,z3,z4,z5]),(0,[z0,z1,z2,z169,z3,z28,z5]),(0,[z0,z1,z2,z3,z4,z5,z203])],[(0,[z0,z1,z2,z3,z4,z204,z5]),(1,[z0,z1,z2,z88,z4,z5]),(0,[z205,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z206,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z207]),(0,[z0,z208,z1,z2,z3,z4,z5]),(0,[z0,z105,z1,z2,z3,z148,z5]),(0,[z0,z1,z2,z169,z3,z181,z5])],[(0,[z0,z209,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z17,z54,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z210]),(0,[z12,z0,z1,z2,z3,z78,z4]),(0,[z0,z1,z2,z211,z3,z4,z5])]],
   [[(0,[z212,z0,z1,z2,z3,z4,z5]),(0,[z0,z138,z1,z2,z3,z54,z5]),(0,[z0,z1,z2,z3,z4,z213,z5]),(0,[z0,z1,z2,z3,z4,z5,z214]),(0,[z0,z215,z1,z2,z3,z4,z5])],[(0,[z114,z1,z2,z216,z3,z4,z5]),(1,[z46,z1,z2,z67,z4,z5]),(0,[z0,z1,z2,z3,z4,z217,z5]),(0,[z87,z0,z2,z133,z3,z4,z5])],[(0,[z93,z0,z1,z216,z3,z4,z5]),(0,[z0,z1,z2,z218,z3,z4,z5]),(0,[z0,z1,z219,z2,z3,z4,z5])],[(0,[z220,z0,z1,z2,z3,z4,z5]),(0,[z27,z1,z2,z3,z4,z92,z5]),(1,[z0,z221,z1,z3,z4,z5]),(0,[z0,z1,z222,z2,z3,z4,z5]),(0,[z0,z1,z2,z223,z3,z4,z5])],[(0,[z224,z0,z1,z2,z3,z4,z5]),(0,[z0,z36,z1,z2,z3,z4,z5]),(0,[z0,z225,z1,z2,z3,z4,z5]),(0,[z226,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z227,z5])],[(0,[z0,z228,z1,z2,z3,z4,z5]),(0,[z87,z0,z2,z3,z148,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z229]),(0,[z0,z1,z2,z3,z4,z230,z5]),(0,[z0,z1,z2,z3,z4,z231,z5])],[(0,[z0,z1,z2,z232,z3,z4,z5])],[(1,[z0,z233,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z5]),(0,[z0,z234,z1,z2,z3,z4,z5]),(0,[z68,z0,z1,z2,z3,z148,z5]),(0,[z0,z1,z235,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z236,z5])]],
   [[(0,[z87,z0,z237,z2,z3,z4,z5]),(0,[z0,z1,z2,z238,z3,z4,z5])],[(0,[z239,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z240,z5]),(0,[z0,z1,z2,z3,z241,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z91])],[(0,[z0,z1,z2,z3,z242,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z243]),(0,[z0,z1,z244,z2,z3,z4,z5]),(0,[z0,z1,z245,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z246,z5])],[(0,[z247,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z248,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z77])],[(0,[z0,z1,z2,z3,z29,z4,z5]),(0,[z168,z0,z1,z2,z169,z3,z5]),(0,[z0,z1,z2,z3,z249,z4,z5]),(0,[z250,z0,z1,z2,z3,z4,z5])],[(0,[z46,z0,z1,z2,z11,z4,z5]),(0,[z251,z0,z1,z2,z3,z4,z5]),(0,[z26,z68,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z252,z4,z5]),(1,[z0,z1,z2,z169,z11,z5])],[(0,[z0,z253,z1,z2,z3,z4,z5]),(1,[z0,z134,z1,z141,z4,z5]),(0,[z0,z1,z2,z3,z4,z254,z5]),(0,[z0,z1,z2,z102,z3,z4,z255])],[(0,[z0,z1,z2,z3,z54,z4,z5]),(0,[z0,z1,z2,z256,z3,z4,z5]),(0,[z0,z1,z2,z3,z257,z4,z5]),(0,[z0,z1,z2,z187,z3,z4,z5]),(1,[z0,z1,z258,z3,z39,z5])]],
   [[(0,[z142,z0,z1,z216,z3,z4,z5]),(0,[z87,z21,z0,z2,z3,z4,z5]),(1,[z0,z36,z2,z3,z4,z37]),(0,[z0,z1,z258,z3,z4,z39,z5]),(0,[z0,z1,z2,z3,z4,z5,z259])],[(0,[z260,z0,z1,z2,z242,z4,z5])],[(1,[z0,z1,z2,z3,z63,z5]),(0,[z0,z237,z1,z133,z3,z4,z5]),(0,[z0,z1,z2,z261,z3,z4,z5])],[(0,[z0,z1,z2,z262,z3,z4,z5]),(0,[z263,z0,z1,z2,z3,z4,z5]),(0,[z27,z0,z1,z2,z169,z3,z5])],[(0,[z0,z264,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z265,z4,z5]),(0,[z93,z0,z1,z266,z3,z4,z5]),(0,[z267,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z268,z2,z3,z4,z5]),(0,[z0,z269,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z270,z3,z4,z5]),(0,[z0,z271,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z272,z3,z4,z5]),(1,[z0,z1,z2,z3,z204,z5]),(0,[z0,z124,z1,z216,z3,z4,z5]),(0,[z273,z0,z1,z2,z3,z4,z5]),(0,[z30,z0,z1,z2,z3,z4,z13]),(0,[z274,z0,z1,z2,z3,z4,z5])],[(0,[z0,z275,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z276,z5]),(0,[z0,z1,z2,z3,z4,z277,z5]),(0,[z0,z1,z2,z3,z78,z92,z5]),(0,[z12,z0,z1,z2,z3,z4,z37]),(0,[z0,z1,z2,z3,z4,z60,z31]),(0,[z0,z1,z2,z278,z4,z39,z5])]],
   [[(0,[z0,z100,z1,z2,z3,z4,z5]),(0,[z30,z0,z1,z2,z160,z4,z5]),(1,[z0,z1,z2,z3,z213,z5]),(0,[z87,z0,z1,z2,z249,z4,z5]),(0,[z0,z1,z2,z11,z4,z5,z83]),(0,[z0,z279,z1,z2,z3,z4,z5])],[(0,[z62,z0,z1,z216,z3,z4,z5]),(0,[z168,z27,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z280,z5]),(0,[z281,z0,z1,z2,z17,z4,z5]),(0,[z0,z1,z2,z3,z4,z282,z5]),(0,[z0,z1,z2,z3,z4,z35,z76]),(0,[z283,z0,z1,z2,z3,z4,z5])],[(0,[z0,z284,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z96,z55,z4,z5]),(0,[z0,z1,z285,z2,z3,z4,z5]),(0,[z286,z0,z1,z2,z3,z4,z5]),(1,[z0,z1,z2,z3,z4,z188]),(0,[z0,z124,z1,z258,z3,z4,z5])],[(0,[z30,z0,z1,z2,z3,z4,z35]),(0,[z0,z1,z2,z3,z4,z287,z5])],[(0,[z62,z0,z1,z2,z3,z204,z5]),(0,[z0,z1,z2,z3,z4,z199,z5])],[(0,[z288,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z94,z3,z4,z39,z5]),(0,[z289,z0,z1,z2,z3,z4,z5]),(0,[z0,z290,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z76,z31])],[(1,[z0,z291,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z292,z4,z5])]],
   [[(0,[z142,z1,z115,z2,z3,z4,z5]),(0,[z0,z293,z1,z2,z3,z4,z5]),(0,[z87,z0,z1,z2,z3,z4,z294]),(0,[z0,z1,z2,z3,z4,z295,z5]),(0,[z0,z2,z3,z4,z35,z227,z5])],[(0,[z0,z1,z94,z2,z3,z4,z296]),(0,[z12,z0,z1,z2,z3,z4,z116]),(0,[z0,z1,z2,z297,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z5,z298]),(0,[z299,z0,z1,z2,z3,z4,z5])],[(0,[z300,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z301,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z302,z5]),(0,[z0,z303,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z102,z3,z4,z91])],[(1,[z62,z1,z216,z3,z4,z5]),(0,[z0,z1,z2,z304,z3,z4,z5]),(0,[z0,z1,z2,z64,z3,z4,z83])],[(0,[z0,z1,z2,z3,z305,z4,z5]),(0,[z0,z1,z2,z3,z306,z4,z5]),(0,[z0,z1,z2,z3,z307,z4,z5])],[(0,[z0,z1,z2,z67,z4,z5,z83]),(0,[z0,z186,z1,z2,z17,z4,z5]),(0,[z308,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z309,z2,z3,z4,z5]),(1,[z0,z1,z310,z96,z4,z5])],[(1,[z0,z1,z2,z3,z4,z311]),(0,[z0,z1,z2,z3,z4,z312,z5]),(0,[z0,z1,z313,z2,z3,z4,z5]),(0,[z0,z1,z2,z314,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z315,z5])]],
   [[(0,[z260,z114,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z316,z3,z4,z5]),(1,[z142,z1,z94,z3,z4,z5]),(0,[z0,z1,z2,z3,z150,z4,z5]),(0,[z0,z1,z291,z2,z3,z4,z5]),(0,[z317,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z318,z5]),(0,[z0,z1,z2,z3,z319,z4,z5]),(0,[z0,z320,z1,z2,z3,z4,z5])],[(0,[z0,z1,z321,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z60,z91]),(0,[z0,z1,z2,z322,z3,z4,z5])],[(0,[z0,z323,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z324,z4,z5]),(0,[z0,z1,z2,z3,z4,z325,z5]),(0,[z326,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z327,z5]),(0,[z0,z1,z2,z328,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z329,z5]),(0,[z0,z1,z2,z3,z4,z5,z330]),(0,[z0,z1,z2,z3,z4,z331,z5]),(0,[z0,z1,z2,z3,z4,z332,z5])],[(0,[z333,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z334,z2,z3,z4,z5]),(0,[z0,z1,z2,z55,z11,z4,z5]),(0,[z68,z0,z1,z2,z187,z4,z5]),(0,[z0,z134,z1,z310,z3,z4,z5]),(0,[z0,z1,z335,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z336,z4,z5]),(0,[z168,z1,z2,z3,z29,z4,z5]),(0,[z0,z1,z2,z337,z3,z4,z5]),(0,[z0,z1,z2,z3,z338,z4,z5])],[(0,[z0,z1,z2,z3,z4,z339,z5]),(0,[z0,z1,z2,z340,z3,z54,z5]),(0,[z0,z1,z2,z340,z3,z4,z5]),(0,[z0,z134,z237,z1,z3,z4,z5]),(0,[z0,z1,z2,z3,z255,z5,z91])],[(0,[z0,z1,z2,z341,z3,z4,z5]),(0,[z0,z342,z1,z2,z3,z4,z5]),(0,[z0,z343,z1,z2,z3,z4,z5]),(0,[z0,z344,z1,z2,z3,z4,z5]),(0,[z0,z82,z1,z2,z3,z4,z83])]],
   [[(0,[z114,z22,z1,z2,z3,z4,z5]),(1,[z0,z1,z3,z345,z4,z5]),(0,[z0,z1,z2,z3,z69,z4,z5]),(0,[z21,z0,z1,z2,z3,z4,z37]),(0,[z26,z0,z1,z2,z169,z4,z5]),(1,[z0,z1,z2,z4,z5,z346])],[(0,[z0,z347,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z348]),(0,[z349,z0,z1,z2,z3,z4,z5]),(0,[z21,z0,z132,z2,z3,z4,z5]),(0,[z0,z1,z2,z17,z3,z4,z5]),(0,[z26,z0,z1,z2,z55,z4,z5]),(1,[z0,z186,z2,z17,z4,z5])],[(0,[z0,z1,z2,z3,z4,z294,z5]),(0,[z286,z0,z1,z3,z4,z60,z5]),(0,[z0,z1,z2,z3,z4,z350,z5]),(0,[z0,z1,z351,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z352,z5])],[(0,[z353,z0,z1,z2,z3,z4,z5]),(1,[z0,z1,z2,z3,z287,z5]),(0,[z0,z1,z2,z3,z354,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z355])],[(0,[z356,z0,z1,z2,z3,z4,z5])],[],[(0,[z30,z12,z1,z2,z3,z4,z5]),(0,[z0,z1,z310,z2,z11,z4,z5]),(0,[z357,z0,z1,z2,z3,z4,z5])]],
   [[(0,[z0,z1,z2,z358,z3,z4,z5]),(0,[z359,z0,z1,z2,z3,z4,z5]),(1,[z34,z0,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z360,z5])],[(0,[z0,z237,z132,z2,z3,z4,z5]),(0,[z0,z1,z96,z3,z141,z4,z5])],[(0,[z0,z1,z2,z156,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z361]),(0,[z362,z0,z1,z2,z3,z4,z5])],[(1,[z0,z1,z2,z3,z4,z296]),(0,[z10,z46,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z363,z4,z5]),(0,[z0,z364,z1,z2,z3,z4,z5]),(0,[z0,z365,z1,z2,z3,z55,z5]),(1,[z0,z1,z3,z4,z366,z5]),(1,[z0,z1,z2,z3,z307,z5]),(0,[z367,z0,z1,z2,z3,z4,z5])],[(0,[z0,z368,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z28,z4,z5])],[(0,[z0,z1,z2,z369,z3,z4,z5]),(0,[z0,z1,z2,z3,z370,z4,z5])],[(0,[z0,z1,z2,z3,z4,z371,z5]),(0,[z0,z1,z372,z2,z3,z4,z5]),(0,[z0,z1,z2,z373,z3,z4,z5]),(0,[z0,z1,z266,z2,z3,z4,z5]),(0,[z0,z82,z1,z2,z3,z4,z5])],[(1,[z0,z1,z2,z156,z3,z5]),(0,[z0,z105,z2,z3,z4,z199,z5]),(0,[z374,z0,z1,z2,z3,z4,z5]),(1,[z0,z124,z1,z3,z28,z5])]],
   [[(1,[z0,z1,z2,z375,z3,z4]),(0,[z0,z1,z2,z3,z4,z5,z376]),(0,[z0,z1,z2,z3,z4,z5,z13])],[(0,[z0,z1,z2,z3,z3,z4,z5]),(0,[z10,z0,z1,z2,z54,z4,z5]),(1,[z0,z1,z2,z3,z377,z4]),(0,[z30,z0,z1,z2,z3,z213,z5]),(0,[z93,z0,z237,z1,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z378,z5]),(0,[z68,z0,z1,z2,z169,z3,z5]),(0,[z0,z1,z258,z2,z3,z39,z5]),(0,[z93,z0,z1,z3,z4,z35,z5]),(0,[z0,z1,z2,z3,z4,z379,z5])],[(0,[z0,z1,z2,z3,z380,z4,z5]),(0,[z46,z0,z1,z2,z54,z4,z5]),(0,[z0,z381,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z382,z3,z4,z5]),(0,[z0,z383,z1,z2,z3,z4,z5]),(0,[z384,z0,z1,z2,z3,z4,z5]),(0,[z385,z0,z1,z2,z3,z4,z5])],[(0,[z168,z0,z1,z2,z3,z29,z5]),(0,[z386,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z387,z3,z4,z5])],[(0,[z10,z26,z0,z1,z2,z4,z5]),(0,[z12,z0,z1,z2,z3,z4,z60])],[(0,[z0,z1,z2,z3,z388,z4,z5]),(0,[z389,z0,z1,z2,z3,z4,z5]),(0,[z390,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z369,z3,z4,z92]),(0,[z87,z0,z1,z2,z3,z4,z214]),(0,[z0,z391,z1,z2,z3,z4,z5]),(0,[z0,z392,z1,z2,z3,z4,z5])],[(0,[z393,z0,z1,z2,z3,z4,z5]),(0,[z0,z132,z2,z3,z4,z5,z37]),(0,[z394,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z395,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z396,z5]),(0,[z0,z1,z2,z3,z278,z4,z5]),(0,[z0,z397,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z398,z4,z5])]],
   [[(0,[z260,z0,z1,z2,z3,z4,z5]),(0,[z260,z0,z115,z2,z3,z4,z5]),(0,[z114,z0,z22,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z399]),(0,[z30,z0,z291,z2,z3,z4,z5]),(0,[z0,z221,z1,z3,z55,z4,z5]),(0,[z400,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z401,z4,z5]),(1,[z0,z105,z2,z3,z199,z5]),(0,[z402,z0,z1,z2,z3,z4,z5])],[(0,[z403,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z404,z4,z5]),(0,[z0,z1,z2,z96,z17,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z405]),(0,[z0,z1,z2,z4,z255,z5,z346])],[(0,[z0,z1,z2,z3,z406,z4,z5]),(1,[z0,z1,z2,z3,z4,z153]),(0,[z0,z1,z2,z407,z3,z4,z5])],[(0,[z408,z0,z1,z2,z3,z4,z5]),(0,[z409,z0,z1,z2,z3,z4,z5]),(0,[z27,z0,z1,z2,z3,z29,z5]),(0,[z0,z1,z2,z3,z4,z198,z5])],[(0,[z0,z1,z2,z54,z4,z5,z83]),(1,[z0,z1,z410,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z411]),(0,[z87,z412,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z413,z4,z5]),(1,[z0,z1,z2,z3,z319,z5])],[(0,[z0,z1,z2,z3,z414,z4,z5]),(0,[z0,z1,z2,z3,z92,z39,z5]),(1,[z173,z0,z1,z2,z4,z5]),(0,[z12,z0,z1,z2,z3,z4,z5]),(0,[z87,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z415,z2,z3,z4,z5]),(0,[z0,z416,z1,z2,z3,z4,z5])],[(0,[z417,z0,z1,z2,z3,z4,z5]),(0,[z0,z134,z1,z2,z3,z4,z5]),(0,[z0,z134,z1,z2,z3,z4,z418]),(0,[z0,z1,z3,z4,z35,z5,z31])],[(0,[z0,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z419]),(0,[z0,z1,z420,z2,z3,z4,z5]),(0,[z12,z0,z1,z2,z102,z3,z4]),(0,[z421,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z422,z4,z5])]],
   [[(0,[z0,z1,z2,z423,z3,z4,z5]),(0,[z0,z1,z2,z424,z3,z4,z5]),(0,[z425,z0,z1,z2,z3,z4,z5]),(0,[z26,z0,z1,z2,z3,z11,z5])],[(0,[z0,z426,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z427]),(0,[z26,z0,z1,z2,z4,z181,z5])],[(0,[z27,z0,z1,z410,z3,z4,z5]),(0,[z0,z1,z428,z2,z3,z4,z5]),(0,[z429,z0,z1,z2,z3,z4,z5]),(0,[z0,z105,z1,z2,z3,z4,z311]),(0,[z0,z1,z2,z3,z4,z430,z5])],[(0,[z0,z1,z2,z3,z431,z4,z5]),(0,[z432,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z433,z3,z4,z5])],[(0,[z260,z0,z1,z2,z149,z4,z5]),(0,[z0,z1,z434,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z366,z5]),(0,[z0,z1,z2,z435,z3,z4,z5]),(0,[z0,z436,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z437])],[(0,[z0,z1,z2,z438,z3,z4,z5]),(0,[z0,z1,z2,z3,z154,z4,z5]),(0,[z0,z439,z1,z2,z3,z4,z5])],[(1,[z0,z1,z2,z3,z4,z440])],[(0,[z0,z1,z2,z3,z4,z441,z5]),(0,[z0,z1,z94,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z442,z5]),(0,[z0,z1,z2,z3,z443,z4,z5]),(0,[z0,z1,z2,z444,z3,z4,z5]),(1,[z0,z1,z266,z3,z4,z31]),(0,[z0,z445,z1,z2,z3,z4,z5])]],
   [[(0,[z0,z1,z2,z17,z141,z4,z5]),(1,[z0,z436,z1,z2,z4,z5]),(0,[z0,z1,z2,z169,z3,z11,z5])],[(0,[z0,z2,z3,z148,z4,z199,z5]),(0,[z446,z0,z1,z2,z3,z4,z5]),(0,[z447,z0,z1,z2,z3,z4,z5]),(0,[z448,z0,z1,z2,z3,z4,z5])],[(0,[z173,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z449,z4,z5])],[(0,[z0,z1,z2,z3,z450,z4,z5]),(0,[z0,z1,z451,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z452,z5]),(0,[z0,z1,z2,z3,z28,z148,z5]),(0,[z26,z0,z134,z1,z2,z4,z5]),(0,[z0,z1,z453,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z5,z454]),(0,[z0,z1,z2,z3,z455,z4,z5]),(0,[z87,z0,z1,z96,z3,z4,z5]),(0,[z456,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z457,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z458,z5]),(0,[z0,z1,z459,z2,z3,z4,z5]),(0,[z0,z460,z1,z2,z3,z4,z5]),(0,[z68,z0,z2,z3,z148,z4,z5]),(0,[z0,z461,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z181,z5]),(0,[z0,z1,z2,z64,z3,z4,z76])],[(0,[z0,z1,z216,z3,z4,z5,z31]),(0,[z0,z1,z2,z3,z462,z4,z5]),(0,[z0,z1,z463,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z464]),(0,[z21,z0,z1,z2,z3,z4,z60]),(0,[z0,z465,z1,z2,z3,z4,z5])],[(0,[z0,z466,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z467,z4,z5]),(0,[z468,z0,z1,z2,z3,z4,z5]),(0,[z0,z469,z1,z2,z3,z4,z5]),(0,[z470,z0,z1,z2,z3,z4,z5]),(0,[z26,z0,z1,z2,z17,z4,z5]),(0,[z0,z1,z2,z3,z4,z471,z5])]],
   [[(0,[z0,z22,z2,z3,z55,z4,z5]),(0,[z0,z1,z2,z472,z3,z4,z5]),(0,[z87,z0,z105,z2,z3,z4,z5]),(0,[z0,z105,z1,z2,z3,z199,z5]),(0,[z0,z1,z2,z3,z4,z5,z473])],[(0,[z87,z0,z2,z3,z4,z5,z37]),(0,[z0,z1,z474,z2,z3,z4,z5]),(0,[z0,z1,z310,z2,z3,z287,z5]),(0,[z93,z0,z1,z2,z3,z4,z5])],[(0,[z0,z186,z22,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z440,z5]),(0,[z0,z1,z2,z3,z4,z5,z475])],[(0,[z476,z0,z1,z2,z3,z4,z5]),(1,[z0,z1,z2,z3,z198,z5]),(0,[z0,z1,z2,z477,z3,z4,z5]),(0,[z0,z1,z2,z3,z478,z4,z5]),(0,[z0,z479,z1,z2,z3,z4,z5])],[(0,[z0,z1,z480,z2,z3,z4,z5]),(0,[z481,z0,z1,z2,z3,z4,z5]),(0,[z482,z0,z1,z2,z3,z4,z5]),(1,[z201,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z483,z5]),(0,[z484,z0,z1,z2,z3,z4,z5]),(0,[z485,z0,z1,z2,z3,z4,z5]),(0,[z0,z436,z1,z2,z4,z39,z5])],[(1,[z0,z1,z321,z3,z4,z5]),(0,[z486,z0,z1,z2,z3,z4,z5]),(0,[z487,z0,z1,z2,z3,z4,z5])],[(0,[z21,z0,z115,z2,z3,z4,z5]),(0,[z488,z0,z1,z2,z3,z4,z5]),(0,[z21,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z489]),(0,[z0,z1,z2,z3,z490,z4,z5]),(1,[z0,z1,z2,z3,z5,z77]),(0,[z491,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z492,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z493,z5])]],
   [[(0,[z494,z0,z1,z2,z3,z4,z5]),(0,[z0,z233,z1,z2,z3,z4,z5]),(0,[z201,z0,z1,z2,z3,z4,z5]),(0,[z0,z134,z1,z2,z96,z4,z5]),(0,[z0,z1,z2,z3,z141,z4,z5]),(0,[z0,z1,z310,z2,z3,z307,z5]),(0,[z0,z1,z2,z495,z3,z4,z5]),(0,[z0,z1,z266,z3,z4,z5,z31]),(0,[z0,z82,z1,z2,z3,z4,z76])],[(0,[z0,z1,z2,z3,z78,z29,z5]),(0,[z30,z0,z82,z1,z2,z3,z4]),(0,[z68,z0,z1,z2,z3,z199,z5])],[],[],[(0,[z0,z496,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z497,z5]),(0,[z0,z1,z2,z3,z4,z498,z5]),(0,[z0,z1,z3,z4,z60,z366,z5])],[(0,[z0,z499,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z148,z39,z5]),(0,[z0,z1,z2,z3,z4,z188,z5]),(0,[z0,z124,z1,z2,z3,z39,z5]),(0,[z0,z1,z2,z3,z500,z4,z5])],[(0,[z501,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z216,z3,z4,z5]),(0,[z12,z1,z2,z3,z4,z116,z5]),(0,[z0,z237,z1,z2,z3,z4,z5]),(0,[z87,z0,z1,z2,z3,z61,z5]),(0,[z0,z1,z2,z3,z4,z502,z5]),(0,[z0,z1,z2,z137,z3,z4,z5])],[(0,[z0,z1,z2,z67,z3,z4,z5]),(0,[z0,z503,z1,z2,z3,z4,z5]),(1,[z21,z0,z2,z3,z4,z60])]],
   [[(0,[z0,z1,z2,z3,z4,z5,z504]),(0,[z168,z0,z1,z2,z3,z4,z5]),(0,[z281,z0,z2,z3,z55,z4,z5]),(0,[z0,z186,z2,z17,z3,z4,z5]),(0,[z0,z1,z2,z3,z505,z4,z5])],[(0,[z0,z1,z2,z133,z3,z4,z5]),(0,[z0,z1,z266,z2,z3,z4,z31])],[(0,[z0,z506,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z507,z4,z5]),(0,[z10,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z88,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z508,z5]),(0,[z0,z1,z509,z2,z3,z4,z5])],[(0,[z510,z0,z1,z2,z3,z4,z5]),(0,[z511,z0,z1,z2,z3,z4,z5]),(0,[z0,z512,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z64,z67,z4,z5]),(0,[z0,z1,z2,z3,z377,z4,z5]),(1,[z0,z1,z48,z3,z4,z5]),(0,[z0,z1,z2,z3,z148,z4,z5]),(0,[z0,z1,z2,z3,z513,z4,z5]),(0,[z0,z134,z1,z2,z141,z4,z5]),(0,[z0,z1,z310,z2,z96,z4,z5]),(0,[z0,z124,z1,z2,z3,z4,z5])],[(0,[z0,z514,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z515,z5])],[(0,[z10,z0,z516,z2,z3,z4,z5]),(0,[z27,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z517,z5]),(0,[z87,z0,z1,z3,z4,z5,z31]),(0,[z0,z1,z2,z3,z4,z35,z37])]],
   [[(0,[z518,z0,z1,z2,z3,z4,z5]),(0,[z62,z0,z1,z2,z3,z4,z5]),(0,[z0,z124,z1,z2,z3,z28,z5]),(0,[z0,z1,z2,z519,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z520,z5]),(0,[z0,z1,z2,z3,z29,z5,z91]),(0,[z0,z1,z2,z3,z4,z37,z31])],[(0,[z0,z1,z521,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z311]),(0,[z0,z1,z2,z3,z4,z522,z5]),(0,[z0,z1,z2,z3,z4,z5,z523])],[(0,[z0,z1,z2,z3,z28,z92,z5]),(0,[z26,z0,z105,z1,z2,z3,z5]),(0,[z0,z105,z1,z2,z169,z3,z5])],[(0,[z0,z1,z2,z3,z160,z4,z5]),(0,[z0,z1,z2,z3,z524,z4,z5])],[(1,[z0,z1,z2,z242,z4,z5]),(0,[z0,z1,z2,z3,z4,z525,z5]),(0,[z0,z237,z1,z96,z3,z4,z5]),(0,[z0,z1,z3,z345,z55,z4,z5]),(0,[z0,z1,z2,z11,z4,z181,z5])],[(0,[z22,z1,z115,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z526,z4,z5]),(0,[z0,z1,z2,z3,z377,z4,z92])],[(1,[z0,z1,z2,z249,z4,z5]),(0,[z0,z1,z2,z3,z4,z527,z5]),(0,[z528,z0,z1,z2,z3,z4,z5]),(1,[z93,z0,z1,z3,z4,z35])]],
   [[(0,[z529,z0,z1,z2,z3,z4,z5]),(0,[z12,z0,z1,z2,z3,z4,z31]),(0,[z530,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z531,z3,z4,z5]),(0,[z0,z1,z2,z3,z55,z4,z5]),(0,[z0,z1,z532,z2,z3,z4,z5]),(0,[z26,z0,z1,z310,z2,z4,z5]),(0,[z0,z1,z2,z3,z4,z533,z5])],[(0,[z142,z62,z1,z2,z3,z4,z5]),(0,[z534,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z535]),(0,[z0,z105,z1,z2,z3,z4,z440]),(1,[z0,z2,z3,z33,z4,z5])],[(1,[z10,z1,z2,z54,z4,z5]),(0,[z1,z2,z3,z29,z4,z92,z5]),(0,[z0,z1,z2,z3,z4,z536,z5]),(0,[z0,z1,z2,z537,z3,z4,z5])],[],[],[(0,[z538,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z539,z5])],[(0,[z0,z1,z2,z540,z3,z4,z5])],[(1,[z0,z1,z2,z3,z4,z294]),(0,[z0,z365,z1,z2,z3,z4,z5]),(0,[z0,z1,z541,z2,z3,z4,z5])]],
   [[(0,[z0,z1,z132,z2,z3,z4,z5])],[(0,[z12,z0,z1,z2,z64,z3,z4]),(0,[z0,z1,z2,z3,z4,z255,z37]),(0,[z0,z1,z2,z64,z11,z4,z5])],[(0,[z0,z1,z2,z3,z542,z4,z5]),(1,[z26,z0,z1,z2,z181,z5])],[(0,[z30,z1,z2,z3,z4,z5,z13]),(0,[z0,z1,z2,z3,z4,z37,z91]),(0,[z0,z1,z2,z3,z4,z5,z543]),(0,[z0,z1,z544,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z345,z4,z5]),(0,[z0,z1,z258,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z545,z5])],[(1,[z0,z1,z2,z3,z4,z110]),(0,[z0,z1,z2,z546,z3,z4,z5]),(0,[z0,z1,z2,z547,z3,z4,z5]),(0,[z21,z0,z2,z3,z4,z60,z5])],[(0,[z548,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z296]),(0,[z549,z0,z1,z2,z3,z4,z5]),(0,[z30,z0,z1,z321,z3,z4,z5]),(0,[z550,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z102,z3,z5,z91]),(0,[z0,z1,z2,z3,z4,z5,z551])],[(1,[z0,z1,z2,z369,z3,z4]),(0,[z0,z1,z2,z3,z552,z4,z5]),(0,[z30,z0,z1,z2,z3,z78,z4]),(0,[z87,z0,z1,z132,z3,z4,z5]),(0,[z0,z1,z2,z3,z553,z4,z5]),(0,[z0,z1,z258,z2,z3,z28,z5]),(0,[z0,z1,z2,z3,z554,z4,z5])]],
   [[(0,[z0,z1,z2,z3,z4,z5,z555]),(0,[z556,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z557,z4,z5]),(0,[z0,z412,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z558,z3,z4,z5]),(0,[z0,z1,z2,z3,z559,z4,z5]),(0,[z560,z0,z1,z2,z3,z4,z5])],[(0,[z142,z114,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z561,z5]),(0,[z0,z1,z2,z562,z3,z4,z5]),(0,[z563,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z564,z2,z3,z4,z5]),(0,[z0,z565,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z566,z5]),(0,[z0,z1,z2,z567,z3,z4,z5]),(0,[z568,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z569,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z570,z5]),(0,[z0,z1,z2,z3,z571,z4,z5]),(0,[z0,z1,z2,z3,z4,z31,z83]),(0,[z0,z1,z2,z3,z4,z5,z572]),(0,[z0,z1,z2,z169,z11,z4,z5])],[(0,[z1,z2,z67,z3,z54,z4,z5]),(0,[z0,z1,z2,z3,z4,z39,z5]),(0,[z93,z0,z1,z2,z3,z4,z31])],[(0,[z0,z221,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z573,z4,z5]),(0,[z0,z1,z2,z3,z574,z4,z5])],[(0,[z87,z93,z0,z1,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z575]),(0,[z0,z1,z2,z102,z3,z78,z5]),(0,[z0,z1,z576,z2,z3,z4,z5])],[(0,[z62,z1,z2,z216,z3,z4,z5]),(0,[z0,z2,z3,z33,z4,z39,z5])]],
   [[(0,[z577,z0,z1,z2,z3,z4,z5]),(0,[z0,z115,z2,z3,z55,z4,z5]),(0,[z0,z237,z1,z3,z4,z5,z31]),(0,[z0,z2,z17,z3,z55,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z578])],[(0,[z0,z1,z579,z2,z3,z4,z5]),(1,[z0,z1,z459,z3,z4,z5]),(0,[z0,z1,z2,z3,z580,z4,z5]),(0,[z581,z0,z1,z2,z3,z4,z5]),(1,[z0,z365,z1,z2,z3,z5]),(0,[z0,z582,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z583])],[(0,[z584,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z585,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z586,z5]),(0,[z0,z1,z2,z3,z4,z587,z5]),(0,[z0,z1,z2,z588,z3,z4,z5])],[(1,[z0,z1,z2,z150,z4,z5])],[(1,[z260,z115,z2,z3,z4,z5]),(0,[z0,z1,z2,z589,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z4,z5]),(1,[z27,z1,z2,z3,z92,z5]),(0,[z30,z0,z1,z2,z102,z3,z4]),(0,[z0,z1,z2,z3,z590,z4,z5]),(0,[z0,z1,z2,z3,z591,z4,z5]),(0,[z592,z0,z1,z2,z3,z4,z5])],[(0,[z1,z94,z2,z216,z3,z4,z5]),(0,[z0,z1,z2,z3,z593,z4,z5]),(0,[z0,z1,z2,z3,z594,z4,z5]),(0,[z0,z595,z1,z2,z3,z4,z5]),(0,[z0,z596,z1,z2,z3,z4,z5])],[(0,[z0,z597,z1,z2,z3,z4,z5]),(1,[z0,z1,z2,z340,z3,z5]),(0,[z30,z0,z1,z48,z3,z4,z5]),(1,[z30,z1,z2,z3,z4,z13]),(0,[z0,z1,z310,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z35,z83])],[(0,[z27,z0,z1,z459,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z598,z5]),(0,[z0,z1,z2,z3,z4,z599,z5])]],
   [[(0,[z600,z0,z1,z2,z3,z4,z5]),(0,[z168,z26,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z601,z3,z4,z5]),(0,[z0,z1,z2,z3,z602,z4,z5])],[(0,[z0,z1,z2,z3,z4,z603,z5]),(0,[z604,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z605,z5]),(0,[z0,z1,z606,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z607,z5]),(0,[z0,z1,z2,z3,z4,z608,z5]),(0,[z0,z1,z2,z3,z4,z5,z609]),(0,[z26,z0,z1,z2,z3,z5,z91])],[(0,[z0,z1,z2,z3,z4,z610,z5]),(0,[z0,z1,z2,z3,z4,z611,z5]),(0,[z0,z1,z2,z3,z4,z612,z5]),(0,[z0,z1,z613,z2,z3,z4,z5]),(1,[z0,z1,z2,z69,z4,z5]),(0,[z0,z1,z2,z614,z3,z4,z5]),(0,[z0,z615,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z616,z5])],[(0,[z0,z617,z1,z2,z3,z4,z5]),(0,[z618,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z5,z619]),(0,[z68,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z35,z60]),(0,[z0,z620,z1,z2,z3,z4,z5]),(0,[z0,z621,z1,z2,z3,z4,z5])],[(0,[z0,z115,z2,z3,z4,z5,z37]),(0,[z1,z2,z3,z4,z116,z5,z13]),(0,[z0,z1,z2,z622,z3,z4,z5])],[(1,[z168,z1,z2,z3,z29,z5]),(0,[z30,z0,z1,z2,z3,z4,z37]),(0,[z0,z1,z2,z623,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z624,z5])]],
   [[(0,[z0,z625,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z410,z3,z4,z5]),(0,[z0,z626,z1,z2,z3,z4,z5])],[(0,[z0,z1,z627,z2,z3,z4,z5]),(0,[z0,z1,z628,z2,z3,z4,z5]),(0,[z281,z0,z1,z2,z55,z4,z5]),(0,[z26,z0,z1,z2,z4,z5,z83]),(0,[z0,z1,z2,z137,z4,z255,z5])],[(0,[z0,z1,z629,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z630,z4,z5]),(0,[z0,z1,z2,z631,z3,z4,z5]),(0,[z632,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z633]),(0,[z26,z0,z1,z2,z3,z78,z5]),(0,[z0,z1,z2,z169,z3,z5,z91])],[(0,[z0,z1,z2,z3,z4,z153,z5]),(0,[z634,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z635,z3,z4,z5])],[(0,[z636,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z637,z3,z4,z5]),(1,[z0,z1,z2,z3,z4,z214]),(0,[z281,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z638,z2,z3,z4,z5]),(0,[z0,z1,z310,z96,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z35,z5])],[(0,[z260,z0,z22,z2,z3,z4,z5]),(0,[z639,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z640,z3,z4,z5]),(0,[z0,z641,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z67,z55,z4,z5]),(0,[z0,z1,z2,z642,z3,z4,z5]),(0,[z0,z1,z2,z643,z3,z4,z5]),(0,[z0,z1,z2,z644,z3,z4,z5]),(0,[z0,z2,z3,z4,z60,z5,z37])],[(0,[z0,z1,z2,z3,z645,z4,z5])]],
   [[(0,[z646,z0,z1,z2,z3,z4,z5]),(0,[z0,z237,z1,z132,z3,z4,z5]),(0,[z0,z1,z647,z2,z3,z4,z5])],[(0,[z0,z22,z2,z3,z4,z5,z37]),(0,[z0,z1,z2,z3,z4,z648,z5]),(0,[z30,z0,z1,z2,z3,z4,z116]),(1,[z87,z0,z133,z3,z4,z5]),(1,[z0,z237,z132,z3,z4,z5]),(0,[z0,z1,z2,z3,z649,z4,z5]),(0,[z0,z1,z2,z650,z3,z4,z5])],[(0,[z142,z0,z1,z2,z3,z4,z5]),(0,[z651,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z169,z3,z78,z5]),(0,[z0,z82,z1,z2,z4,z5,z83])],[(0,[z0,z1,z2,z3,z652,z4,z5]),(0,[z0,z1,z2,z3,z4,z116,z5]),(1,[z412,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z61,z4,z5]),(0,[z653,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z654,z4,z5])],[(1,[z0,z1,z2,z3,z4,z5]),(0,[z1,z115,z2,z216,z3,z4,z5]),(0,[z0,z1,z2,z655,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z656]),(1,[z0,z1,z2,z3,z4,z418])],[(0,[z0,z1,z2,z3,z4,z5,z657]),(0,[z10,z0,z1,z2,z67,z4,z5]),(0,[z30,z0,z1,z2,z41,z4,z5]),(0,[z0,z1,z2,z3,z658,z4,z5]),(0,[z0,z659,z1,z2,z3,z4,z5]),(0,[z21,z0,z36,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z660,z4,z5])],[(0,[z260,z1,z115,z2,z3,z4,z5]),(0,[z0,z1,z2,z17,z67,z4,z5]),(0,[z0,z1,z661,z2,z3,z4,z5]),(0,[z0,z1,z2,z662,z3,z4,z5])],[(0,[z0,z1,z2,z663,z3,z4,z5]),(0,[z0,z1,z2,z3,z664,z4,z5]),(0,[z46,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z665]),(0,[z0,z1,z2,z3,z4,z5,z666]),(0,[z0,z1,z2,z3,z4,z255,z60])]],
   [[(0,[z0,z1,z216,z3,z4,z39,z5]),(1,[z0,z516,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z667,z4,z5]),(0,[z0,z1,z2,z668,z3,z4,z5]),(1,[z0,z2,z3,z4,z227,z5]),(0,[z0,z1,z2,z3,z669,z4,z5]),(0,[z0,z1,z2,z3,z78,z255,z5])],[(0,[z0,z22,z1,z2,z3,z4,z110]),(1,[z0,z670,z1,z2,z3,z4]),(0,[z0,z1,z671,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z672,z5]),(0,[z0,z186,z1,z2,z3,z4,z5])],[(0,[z142,z1,z94,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z673]),(0,[z0,z1,z2,z55,z141,z4,z5]),(1,[z0,z1,z2,z278,z4,z5]),(0,[z0,z674,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z319,z76,z5])],[(0,[z0,z1,z2,z3,z63,z4,z5]),(0,[z0,z1,z2,z675,z3,z4,z5]),(1,[z68,z0,z2,z3,z148,z5]),(0,[z0,z1,z676,z2,z3,z4,z5])],[(0,[z0,z1,z2,z677,z3,z4,z5]),(0,[z0,z1,z678,z2,z3,z4,z5])],[(0,[z0,z1,z1,z2,z3,z4,z5]),(0,[z0,z1,z115,z2,z3,z4,z5]),(0,[z0,z138,z1,z2,z3,z4,z5]),(0,[z281,z0,z186,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z28,z199,z5]),(0,[z0,z679,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z346])],[(0,[z0,z1,z680,z2,z3,z4,z5]),(0,[z0,z681,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z64,z54,z4,z5]),(0,[z0,z1,z2,z375,z3,z54,z4]),(1,[z281,z0,z2,z55,z4,z5]),(1,[z286,z0,z1,z3,z4,z5]),(1,[z0,z1,z2,z102,z3,z91])],[(0,[z0,z1,z2,z3,z4,z255,z5])]],
   [[(1,[z0,z1,z2,z149,z4,z5]),(0,[z0,z670,z1,z2,z3,z54,z4]),(0,[z682,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z266,z2,z3,z4,z35])],[(0,[z0,z1,z683,z2,z3,z4,z5]),(0,[z0,z1,z516,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z29,z39,z5])],[(0,[z684,z0,z1,z2,z3,z4,z5]),(0,[z685,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z92,z5,z91]),(1,[z0,z1,z2,z64,z4,z76])],[(0,[z87,z0,z134,z1,z3,z4,z5]),(0,[z0,z1,z2,z3,z686,z4,z5]),(0,[z0,z1,z687,z2,z3,z4,z5])],[(0,[z0,z1,z2,z688,z3,z4,z5]),(0,[z0,z1,z94,z3,z4,z5,z31]),(0,[z0,z1,z2,z375,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z689]),(1,[z0,z1,z2,z3,z154,z5]),(0,[z0,z1,z2,z3,z4,z5,z418]),(0,[z0,z1,z2,z690,z3,z4,z5])],[(0,[z691,z0,z1,z2,z3,z4,z5]),(0,[z692,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z693,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z694,z4,z5]),(0,[z0,z1,z310,z2,z141,z4,z5]),(0,[z0,z1,z2,z3,z78,z4,z255])],[(0,[z10,z0,z233,z2,z3,z4,z5]),(0,[z0,z670,z1,z2,z3,z4,z5]),(0,[z695,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z696,z2,z3,z4,z5]),(0,[z697,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z698,z5]),(0,[z0,z1,z2,z3,z4,z699,z5]),(0,[z0,z1,z2,z3,z4,z700,z5]),(0,[z701,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z702,z5])],[(0,[z0,z1,z2,z3,z4,z703,z5]),(0,[z0,z1,z2,z3,z704,z4,z5]),(0,[z0,z1,z705,z2,z3,z4,z5]),(0,[z706,z0,z1,z2,z3,z4,z5])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z707]),(0,[z1,z2,z67,z708,z4,z5]),(0,[z0,z1,z2,z3,z709,z5]),(0,[z0,z2,z3,z710,z4,z5]),(0,[z0,z1,z2,z711,z3,z5])],[(0,[z0,z1,z2,z64,z557,z4]),(0,[z0,z1,z2,z712,z4,z5])],[(0,[z713,z0,z1,z3,z4,z5]),(0,[z0,z1,z714,z3,z4,z5]),(0,[z0,z1,z2,z69,z4,z5]),(0,[z21,z0,z3,z4,z60,z366])],[(0,[z0,z1,z715,z2,z3,z4]),(0,[z87,z412,z133,z3,z4,z5])],[(0,[z0,z1,z2,z716,z4,z5]),(0,[z0,z1,z2,z3,z4,z717]),(0,[z26,z0,z1,z2,z718,z5])],[(0,[z0,z719,z2,z3,z4,z5]),(1,[z0,z1,z720,z4,z5]),(0,[z0,z1,z310,z96,z287,z5])],[(0,[z0,z1,z2,z721,z4,z5]),(0,[z0,z1,z629,z3,z39,z5]),(0,[z168,z1,z2,z3,z29,z5])],[(0,[z260,z115,z2,z149,z4,z5]),(0,[z0,z1,z2,z722,z3,z4]),(0,[z0,z1,z2,z3,z61,z294])]],
   [[(0,[z0,z1,z2,z723,z4,z5]),(0,[z0,z670,z1,z2,z160,z4])],[(0,[z87,z0,z133,z3,z4,z214]),(0,[z0,z2,z724,z3,z4,z5]),(0,[z0,z1,z725,z3,z4,z5])],[(0,[z173,z0,z1,z2,z369,z4]),(0,[z0,z1,z2,z102,z3,z726])],[(0,[z0,z1,z2,z3,z4,z45]),(0,[z412,z1,z2,z3,z4,z214]),(0,[z87,z0,z1,z3,z4,z418]),(0,[z26,z109,z0,z1,z2,z5])],[(0,[z0,z1,z2,z3,z727,z5]),(0,[z0,z1,z2,z3,z4,z728]),(0,[z0,z100,z2,z3,z4,z60]),(0,[z0,z1,z2,z3,z4,z214]),(0,[z0,z1,z2,z88,z198,z5]),(0,[z0,z1,z310,z96,z307,z5]),(0,[z1,z2,z3,z4,z5,z729])],[(0,[z0,z1,z2,z730,z4,z5]),(0,[z30,z1,z2,z3,z154,z13]),(0,[z201,z1,z2,z88,z4,z5]),(0,[z0,z1,z2,z731,z4,z5]),(0,[z286,z0,z1,z3,z4,z31])],[(0,[z0,z732,z2,z3,z4,z5]),(0,[z142,z1,z94,z3,z4,z296]),(0,[z0,z1,z2,z4,z5,z733]),(0,[z0,z496,z1,z3,z28,z5]),(0,[z0,z1,z2,z3,z734,z5]),(0,[z1,z2,z3,z4,z5,z735])],[(0,[z0,z1,z2,z64,z4,z561]),(0,[z0,z1,z48,z160,z4,z5]),(0,[z0,z2,z3,z4,z294,z37]),(0,[z87,z0,z724,z3,z4,z5]),(0,[z736,z1,z2,z3,z4,z5])]],
   [[],[(0,[z556,z1,z216,z3,z4,z5]),(0,[z0,z1,z2,z737,z3,z5])],[(0,[z412,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z738,z5]),(0,[z1,z2,z708,z54,z4,z5]),(0,[z0,z1,z2,z739,z4,z5]),(0,[z0,z1,z3,z4,z740,z5]),(0,[z0,z134,z1,z622,z4,z5]),(0,[z0,z342,z1,z2,z4,z83]),(0,[z0,z1,z2,z64,z4,z741])],[(0,[z0,z1,z2,z3,z742,z5]),(0,[z0,z1,z2,z743,z4,z5])],[(0,[z0,z100,z2,z3,z4,z5])],[(0,[z27,z1,z2,z3,z377,z92]),(0,[z68,z0,z2,z3,z574,z5]),(1,[z0,z1,z2,z4,z741])],[(0,[z0,z1,z2,z744,z4,z5]),(0,[z0,z1,z216,z3,z204,z5]),(0,[z0,z1,z745,z3,z4,z5]),(0,[z26,z0,z1,z2,z5,z259])],[(0,[z0,z516,z2,z3,z4,z5]),(0,[z0,z2,z3,z4,z227,z5]),(0,[z0,z1,z2,z3,z746,z5])]],
   [[(0,[z0,z670,z1,z2,z3,z4]),(0,[z0,z512,z2,z3,z4,z37])],[(0,[z592,z1,z94,z3,z4,z5]),(0,[z173,z0,z1,z2,z5,z91]),(0,[z12,z1,z2,z56,z3,z4]),(0,[z0,z38,z2,z3,z4,z747]),(1,[z0,z1,z2,z718,z5])],[(0,[z0,z748,z2,z3,z4,z5]),(0,[z12,z1,z2,z3,z4,z656]),(0,[z0,z105,z2,z3,z199,z311]),(0,[z26,z0,z1,z2,z49,z5])],[(0,[z0,z1,z2,z3,z749,z5]),(0,[z0,z1,z2,z3,z4,z750]),(0,[z10,z0,z138,z1,z2,z5]),(0,[z0,z1,z2,z3,z4,z751]),(0,[z68,z0,z2,z187,z148,z5]),(0,[z0,z1,z2,z4,z76,z741])],[(0,[z0,z132,z3,z248,z4,z5]),(0,[z0,z1,z2,z3,z752,z4])],[(0,[z142,z1,z94,z3,z4,z153]),(0,[z46,z1,z2,z67,z4,z5]),(0,[z286,z0,z1,z3,z4,z5]),(0,[z0,z1,z2,z753,z3,z4]),(0,[z0,z38,z2,z3,z4,z754])],[(0,[z0,z670,z1,z2,z340,z3]),(0,[z30,z1,z2,z3,z213,z13]),(0,[z0,z1,z2,z3,z755,z5]),(0,[z0,z1,z156,z3,z345,z5])],[(0,[z168,z173,z0,z1,z2,z5]),(0,[z0,z221,z1,z3,z4,z5]),(0,[z0,z1,z2,z64,z4,z126])]],
   [[(0,[z0,z1,z2,z756,z4,z5]),(0,[z0,z1,z2,z3,z4,z757]),(0,[z0,z1,z2,z758,z4,z5])],[(0,[z0,z1,z759,z3,z4,z5]),(0,[z173,z0,z1,z2,z78,z5]),(0,[z87,z164,z0,z3,z4,z5]),(0,[z446,z0,z2,z55,z4,z5]),(0,[z0,z1,z2,z3,z760,z5]),(0,[z0,z1,z720,z141,z4,z5]),(0,[z26,z0,z38,z2,z3,z5]),(0,[z0,z1,z2,z64,z4,z76])],[(0,[z173,z27,z1,z2,z92,z5])],[(0,[z10,z1,z2,z708,z4,z5]),(0,[z0,z1,z2,z708,z4,z5]),(0,[z0,z1,z2,z3,z761,z5]),(0,[z762,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z763,z4,z5])],[(0,[z0,z1,z2,z764,z4,z5]),(0,[z0,z1,z2,z3,z765,z5]),(0,[z0,z100,z2,z3,z154,z5]),(0,[z0,z36,z2,z3,z4,z766])],[(0,[z767,z0,z1,z2,z3,z4])],[(0,[z0,z1,z2,z3,z768,z5]),(0,[z412,z2,z3,z4,z5,z37])],[(0,[z0,z1,z769,z3,z4,z5]),(0,[z770,z1,z2,z3,z4,z5]),(0,[z771,z1,z2,z3,z4,z5])]],
   [[(0,[z0,z1,z321,z3,z213,z5]),(0,[z26,z0,z1,z2,z104,z5])],[(0,[z0,z1,z2,z3,z4,z772]),(0,[z773,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z774,z5]),(0,[z0,z1,z2,z3,z4,z775]),(0,[z0,z1,z2,z776,z4,z5])],[(0,[z384,z1,z216,z3,z4,z5])],[(0,[z0,z777,z1,z2,z4,z5]),(0,[z0,z436,z2,z33,z4,z5])],[(0,[z0,z1,z2,z778,z4,z5]),(0,[z0,z1,z2,z3,z779,z5]),(0,[z0,z36,z2,z3,z4,z37])],[(0,[z0,z780,z1,z2,z4,z5]),(0,[z10,z138,z1,z2,z54,z5]),(0,[z0,z221,z1,z249,z4,z5]),(0,[z781,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z61,z214])],[(0,[z0,z1,z2,z3,z63,z5]),(0,[z0,z1,z2,z782,z4,z5]),(0,[z1,z2,z3,z4,z5,z783])],[(0,[z0,z1,z2,z3,z784,z5]),(0,[z0,z1,z2,z785,z3,z4]),(0,[z0,z291,z321,z3,z4,z5]),(0,[z0,z100,z2,z41,z4,z5]),(0,[z93,z0,z1,z3,z4,z294]),(0,[z0,z1,z2,z3,z4,z786])]],
   [[(0,[z0,z1,z787,z3,z4,z5]),(0,[z0,z1,z2,z88,z4,z294]),(0,[z788,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z789]),(0,[z87,z0,z133,z3,z61,z5])],[(0,[z114,z22,z2,z3,z4,z110]),(0,[z0,z790,z2,z3,z4,z5]),(0,[z34,z93,z0,z3,z4,z5]),(0,[z0,z1,z2,z3,z718,z5])],[(0,[z0,z1,z2,z3,z791,z5]),(1,[z1,z2,z3,z4,z757]),(0,[z412,z1,z2,z3,z61,z5]),(0,[z0,z2,z3,z792,z4,z5])],[(0,[z0,z1,z2,z3,z793,z5]),(0,[z0,z794,z2,z3,z4,z5]),(0,[z10,z233,z2,z54,z4,z5]),(0,[z0,z138,z670,z1,z2,z3]),(0,[z0,z1,z2,z3,z213,z5]),(0,[z0,z1,z2,z3,z61,z5]),(0,[z0,z1,z2,z3,z795,z5]),(0,[z0,z1,z2,z3,z796,z5]),(0,[z0,z797,z2,z3,z4,z5])],[(0,[z798,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z799,z4,z5])],[(0,[z800,z115,z2,z3,z4,z5]),(1,[z1,z2,z708,z4,z5]),(0,[z0,z1,z2,z801,z4,z5]),(0,[z0,z1,z2,z3,z802,z5])],[(0,[z0,z1,z2,z803,z4,z5])]],
   [[(0,[z0,z1,z2,z804,z4,z5]),(0,[z0,z1,z48,z3,z213,z5]),(0,[z30,z1,z2,z160,z4,z13]),(0,[z0,z1,z2,z3,z726,z91])],[(0,[z0,z805,z2,z3,z4,z5]),(0,[z173,z0,z1,z2,z377,z4])],[(0,[z0,z1,z3,z28,z806,z5]),(0,[z0,z674,z1,z3,z4,z35])],[(0,[z0,z291,z2,z3,z4,z5]),(0,[z697,z1,z94,z3,z4,z5]),(0,[z171,z1,z2,z67,z4,z5])],[(0,[z0,z138,z1,z2,z17,z5]),(0,[z0,z1,z410,z3,z29,z5]),(0,[z412,z1,z3,z4,z5,z31]),(0,[z0,z1,z2,z807,z4,z5])],[(0,[z0,z1,z2,z3,z4,z808]),(0,[z0,z38,z2,z3,z4,z5]),(0,[z0,z1,z2,z387,z3,z91])],[(0,[z0,z1,z2,z160,z4,z31]),(0,[z0,z1,z2,z809,z4,z5]),(0,[z26,z0,z1,z2,z360,z5])],[(0,[z0,z291,z48,z3,z4,z5]),(0,[z0,z1,z2,z810,z3,z5]),(0,[z811,z1,z2,z3,z4,z5])]],
   [[(0,[z62,z1,z216,z3,z4,z5]),(0,[z0,z124,z1,z3,z86,z5]),(0,[z0,z1,z2,z3,z4,z812])],[(0,[z10,z1,z2,z375,z54,z4]),(0,[z12,z1,z2,z3,z4,z116]),(0,[z1,z2,z3,z4,z116,z757])],[(0,[z0,z22,z2,z242,z4,z5]),(0,[z0,z1,z2,z813,z3,z5]),(0,[z30,z1,z2,z433,z3,z4]),(0,[z814,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z4,z815]),(0,[z0,z1,z3,z720,z4,z5])],[(0,[z0,z1,z2,z816,z4,z5]),(0,[z0,z1,z2,z3,z4,z311]),(0,[z0,z2,z3,z4,z766,z37]),(0,[z0,z38,z2,z278,z4,z5])],[(0,[z0,z1,z2,z3,z5,z817]),(0,[z0,z132,z3,z4,z352,z5]),(0,[z0,z818,z1,z3,z4,z5]),(0,[z0,z134,z1,z720,z4,z5]),(0,[z0,z819,z2,z3,z4,z5])],[(0,[z820,z0,z1,z2,z4,z5]),(0,[z168,z1,z2,z3,z821,z5]),(0,[z0,z1,z2,z3,z822,z5]),(0,[z0,z1,z2,z3,z4,z726])],[(0,[z0,z823,z2,z3,z4,z5]),(0,[z0,z138,z1,z2,z5,z83]),(0,[z1,z2,z3,z821,z4,z5]),(0,[z0,z1,z321,z3,z4,z35]),(0,[z0,z221,z1,z141,z4,z5]),(0,[z26,z0,z1,z2,z69,z5])],[(0,[z0,z1,z3,z824,z4,z5]),(0,[z0,z1,z410,z169,z3,z5]),(0,[z281,z0,z2,z710,z4,z5]),(0,[z0,z1,z2,z137,z4,z5])]],
   [[(0,[z0,z138,z1,z2,z3,z5]),(0,[z0,z1,z3,z825,z4,z5])],[(0,[z0,z1,z2,z3,z826,z5]),(0,[z0,z1,z827,z3,z4,z5]),(0,[z0,z105,z2,z3,z199,z440]),(0,[z828,z0,z1,z3,z4,z5])],[(0,[z0,z1,z2,z4,z718,z5]),(0,[z0,z1,z2,z64,z76,z77])],[(0,[z0,z1,z2,z3,z4,z829]),(0,[z0,z1,z2,z3,z4,z830]),(0,[z281,z0,z345,z55,z4,z5]),(0,[z0,z1,z3,z4,z831,z5])],[(0,[z832,z0,z2,z3,z4,z5]),(0,[z0,z1,z2,z4,z5,z833]),(0,[z0,z82,z1,z2,z160,z4]),(0,[z0,z1,z2,z4,z5,z346]),(0,[z0,z1,z2,z64,z319,z5])],[(0,[z0,z1,z2,z834,z4,z5]),(0,[z0,z186,z2,z17,z4,z5])],[(0,[z0,z1,z2,z3,z4,z835]),(0,[z0,z1,z2,z3,z836,z5]),(0,[z0,z1,z2,z160,z4,z5]),(0,[z12,z1,z2,z3,z79,z4]),(0,[z0,z1,z3,z4,z837,z5])],[(0,[z0,z100,z2,z3,z4,z45]),(0,[z0,z1,z2,z3,z4,z838]),(0,[z0,z100,z2,z160,z4,z5]),(0,[z0,z1,z2,z41,z213,z5]),(0,[z93,z412,z1,z3,z4,z5])]],
   [[(0,[z0,z1,z2,z3,z4,z839]),(0,[z30,z1,z2,z3,z4,z231]),(0,[z0,z1,z2,z3,z5,z840])],[(0,[z0,z1,z2,z3,z4,z841]),(0,[z0,z1,z2,z842,z4,z5]),(0,[z0,z2,z3,z4,z843,z5]),(0,[z0,z1,z2,z3,z4,z844]),(0,[z0,z132,z2,z3,z4,z311]),(0,[z0,z208,z2,z55,z4,z5]),(0,[z226,z0,z2,z3,z148,z5]),(0,[z845,z0,z1,z2,z4,z5])],[(0,[z0,z1,z2,z3,z4,z846]),(0,[z0,z1,z2,z3,z5,z847])],[(0,[z0,z1,z2,z848,z3,z4]),(0,[z0,z1,z80,z3,z39,z5]),(0,[z0,z1,z2,z849,z4,z5]),(0,[z0,z1,z96,z658,z4,z5]),(0,[z0,z1,z245,z96,z4,z5]),(0,[z26,z0,z1,z2,z559,z5])],[(0,[z0,z134,z1,z249,z4,z5]),(0,[z0,z258,z3,z33,z39,z5])],[(0,[z0,z1,z2,z3,z850,z5]),(0,[z0,z1,z2,z3,z4,z851])],[(0,[z0,z291,z2,z41,z4,z5]),(0,[z0,z1,z2,z88,z4,z214]),(0,[z0,z1,z2,z3,z4,z852]),(0,[z0,z1,z853,z3,z4,z5]),(0,[z0,z1,z2,z319,z5,z83])],[(0,[z0,z1,z2,z3,z4,z854]),(0,[z0,z855,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z856,z5]),(0,[z0,z1,z3,z4,z366,z5]),(0,[z0,z1,z2,z187,z4,z5])]],
   [[(0,[z0,z1,z2,z857,z4,z5]),(0,[z87,z0,z190,z3,z4,z5]),(0,[z68,z0,z2,z3,z792,z5])],[(0,[z114,z22,z2,z3,z4,z5]),(0,[z0,z1,z2,z858,z3,z5]),(0,[z114,z800,z2,z3,z4,z5]),(0,[z0,z516,z2,z67,z4,z5])],[(0,[z0,z1,z859,z3,z4,z5]),(0,[z0,z1,z321,z3,z4,z153]),(0,[z0,z860,z2,z3,z4,z5]),(0,[z87,z0,z133,z88,z4,z5]),(0,[z26,z0,z221,z1,z4,z5]),(0,[z21,z286,z0,z3,z4,z60])],[(0,[z0,z1,z2,z861,z4,z5]),(0,[z0,z1,z2,z862,z3,z5]),(0,[z0,z1,z2,z156,z3,z5]),(0,[z0,z1,z2,z156,z11,z5]),(0,[z0,z344,z2,z17,z4,z5])],[(0,[z0,z1,z2,z863,z4,z5]),(0,[z0,z1,z2,z375,z3,z4]),(0,[z409,z26,z0,z1,z2,z5]),(0,[z412,z1,z2,z88,z4,z5]),(0,[z0,z38,z2,z3,z148,z5]),(0,[z286,z0,z1,z3,z4,z35])],[(0,[z1,z2,z3,z29,z821,z5]),(0,[z0,z1,z2,z88,z4,z5]),(0,[z0,z1,z2,z864,z4,z5]),(0,[z0,z1,z2,z3,z5,z865])],[(0,[z0,z1,z866,z3,z4,z5]),(0,[z0,z1,z2,z160,z154,z5]),(0,[z281,z0,z365,z2,z55,z5]),(0,[z0,z1,z2,z3,z4,z867]),(0,[z0,z868,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z5,z869]),(0,[z0,z2,z3,z4,z536,z37]),(0,[z0,z1,z870,z3,z4,z5])]],
   [[(0,[z0,z1,z2,z3,z4,z871]),(0,[z0,z1,z2,z4,z5,z872])],[(0,[z260,z800,z2,z3,z4,z5]),(0,[z173,z0,z1,z2,z39,z5]),(0,[z873,z1,z2,z3,z4,z5]),(0,[z26,z0,z1,z2,z156,z5]),(0,[z34,z0,z2,z3,z4,z37]),(0,[z0,z1,z874,z3,z4,z5])],[(0,[z0,z1,z875,z3,z4,z5]),(0,[z0,z1,z2,z876,z4,z5]),(0,[z26,z0,z516,z2,z4,z5]),(0,[z21,z286,z0,z3,z4,z5]),(0,[z0,z1,z2,z4,z599,z83]),(0,[z0,z82,z1,z2,z4,z741])],[(0,[z27,z1,z2,z369,z3,z92]),(0,[z12,z0,z1,z3,z4,z366]),(0,[z0,z2,z3,z4,z877,z5])],[(0,[z0,z1,z2,z3,z4,z878]),(0,[z0,z1,z2,z879,z4,z5]),(0,[z880,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z881,z5]),(0,[z882,z0,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z883]),(0,[z0,z1,z2,z884,z3,z5]),(0,[z0,z1,z885,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z886]),(0,[z0,z1,z3,z887,z4,z5]),(0,[z26,z0,z1,z2,z287,z5]),(0,[z0,z1,z541,z3,z28,z5]),(0,[z0,z1,z3,z4,z35,z831]),(0,[z26,z0,z1,z2,z471,z5])],[(0,[z0,z233,z2,z3,z4,z5]),(0,[z0,z1,z888,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z153]),(0,[z0,z889,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z890,z5]),(0,[z87,z0,z3,z4,z5,z6]),(0,[z0,z891,z2,z3,z4,z5])]],
   [[(0,[z892,z0,z1,z2,z4,z5]),(0,[z893,z0,z1,z3,z4,z45]),(0,[z0,z1,z2,z894,z4,z5]),(0,[z30,z291,z2,z3,z4,z13]),(0,[z0,z1,z3,z4,z294,z31])],[(0,[z122,z1,z2,z54,z4,z5]),(0,[z362,z1,z2,z54,z4,z5]),(0,[z26,z0,z1,z2,z526,z5]),(0,[z0,z1,z2,z11,z4,z418]),(0,[z0,z1,z310,z720,z4,z5])],[(0,[z142,z1,z627,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z895]),(0,[z0,z1,z2,z3,z4,z896]),(0,[z34,z0,z2,z3,z4,z294])],[(0,[z0,z2,z3,z148,z792,z5])],[(0,[z0,z1,z2,z169,z11,z5])],[(0,[z0,z1,z2,z3,z897,z5]),(0,[z0,z516,z2,z11,z4,z5]),(0,[z0,z237,z1,z3,z4,z418]),(0,[z0,z1,z2,z4,z5,z898]),(0,[z0,z134,z1,z141,z4,z5]),(0,[z0,z134,z1,z141,z4,z418]),(0,[z0,z1,z2,z3,z899,z5]),(0,[z0,z1,z2,z900,z4,z5])],[(0,[z773,z0,z1,z2,z242,z5]),(0,[z0,z1,z2,z901,z4,z5]),(0,[z0,z1,z2,z902,z4,z5]),(0,[z0,z291,z2,z3,z4,z31]),(0,[z0,z1,z258,z3,z39,z5])],[(0,[z0,z138,z1,z2,z64,z5]),(0,[z0,z1,z2,z903,z4,z5]),(0,[z0,z1,z2,z3,z213,z60])]],
   [[(0,[z893,z0,z1,z3,z4,z5]),(0,[z904,z1,z2,z3,z4,z5]),(0,[z26,z0,z1,z2,z312,z5]),(0,[z0,z1,z2,z169,z718,z5])],[(0,[z0,z1,z2,z3,z4,z905]),(0,[z0,z237,z724,z3,z4,z5]),(0,[z0,z1,z258,z3,z806,z5]),(0,[z0,z1,z2,z3,z4,z741])],[(0,[z0,z1,z2,z3,z4,z906]),(0,[z653,z1,z2,z67,z4,z5]),(0,[z201,z1,z2,z3,z198,z5]),(0,[z0,z1,z2,z3,z4,z440]),(0,[z0,z1,z2,z907,z4,z5])],[],[(0,[z0,z1,z908,z3,z4,z5]),(0,[z0,z436,z1,z2,z4,z5]),(0,[z0,z1,z258,z278,z39,z5])],[(0,[z0,z1,z2,z3,z204,z5]),(0,[z0,z1,z2,z909,z4,z5])],[(0,[z0,z2,z3,z910,z4,z5]),(0,[z0,z911,z2,z3,z4,z5])],[(0,[z0,z1,z2,z912,z3,z4]),(0,[z0,z1,z683,z3,z4,z31]),(0,[z0,z2,z3,z913,z4,z5])]],
   [[(0,[z0,z100,z2,z3,z213,z5])],[(0,[z0,z800,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z914]),(0,[z0,z2,z3,z4,z766,z5]),(0,[z0,z1,z509,z3,z39,z5]),(1,[z0,z1,z3,z4,z831]),(0,[z915,z1,z2,z3,z4,z5])],[(0,[z12,z1,z2,z3,z4,z757]),(0,[z0,z2,z3,z148,z198,z5]),(0,[z0,z1,z2,z3,z4,z188])],[(0,[z0,z1,z2,z916,z4,z5]),(0,[z0,z1,z2,z3,z4,z917]),(0,[z0,z1,z2,z4,z741,z83]),(0,[z0,z1,z918,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z919]),(0,[z0,z1,z2,z710,z4,z5])],[(0,[z920,z0,z1,z2,z3,z5])],[(0,[z0,z1,z2,z88,z61,z5]),(0,[z0,z1,z3,z4,z831,z31])],[(0,[z0,z105,z457,z2,z3,z5])]],
   [[(0,[z201,z1,z2,z3,z4,z5]),(0,[z921,z0,z2,z3,z4,z5]),(0,[z922,z0,z2,z3,z4,z153]),(0,[z46,z1,z2,z129,z4,z5]),(0,[z0,z565,z2,z3,z4,z37])],[],[(0,[z220,z1,z216,z3,z4,z5]),(0,[z0,z1,z2,z923,z4,z5]),(0,[z0,z1,z2,z3,z5,z77])],[],[(0,[z0,z186,z2,z540,z4,z5]),(0,[z0,z924,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z925,z5]),(0,[z0,z237,z3,z4,z698,z5]),(0,[z0,z1,z2,z322,z4,z76]),(0,[z926,z0,z1,z2,z3,z4])],[(0,[z0,z1,z3,z4,z45,z927]),(0,[z0,z1,z2,z3,z4,z928]),(0,[z1,z2,z3,z821,z92,z5]),(0,[z283,z0,z2,z55,z4,z5]),(0,[z0,z1,z310,z96,z4,z5]),(0,[z0,z1,z2,z3,z4,z831])],[(0,[z0,z1,z929,z3,z4,z5])],[(0,[z0,z1,z2,z813,z242,z5]),(0,[z142,z1,z94,z3,z4,z5]),(0,[z0,z930,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z931]),(0,[z0,z1,z2,z3,z4,z932]),(0,[z0,z1,z2,z3,z254,z91])]],
   [[(0,[z0,z365,z1,z3,z345,z5]),(0,[z0,z1,z2,z11,z718,z5])],[(0,[z0,z1,z2,z4,z5,z933]),(0,[z0,z1,z2,z3,z4,z934])],[(0,[z0,z1,z372,z3,z4,z31])],[],[(1,[z800,z2,z3,z4,z5]),(0,[z27,z1,z2,z3,z821,z5]),(0,[z0,z186,z2,z710,z4,z5])],[(0,[z0,z1,z2,z3,z4,z935]),(0,[z0,z1,z2,z160,z4,z35]),(0,[z0,z1,z2,z249,z198,z5]),(0,[z0,z1,z936,z3,z4,z5])],[(0,[z0,z291,z2,z3,z154,z5]),(0,[z201,z1,z2,z249,z4,z5]),(0,[z0,z1,z2,z3,z4,z937]),(1,[z0,z2,z710,z4,z5]),(0,[z0,z1,z2,z3,z938,z5]),(0,[z0,z939,z2,z3,z4,z5])],[(0,[z0,z1,z3,z345,z4,z5]),(0,[z34,z0,z2,z3,z4,z60]),(0,[z0,z2,z3,z4,z940,z5])]],
   [[(0,[z93,z0,z3,z4,z35,z227])],[(0,[z0,z941,z2,z3,z4,z5]),(0,[z0,z1,z2,z942,z3,z4])],[(0,[z0,z1,z3,z4,z5,z943])],[(0,[z27,z1,z410,z3,z92,z5]),(0,[z0,z1,z2,z3,z287,z5])],[(0,[z114,z22,z2,z3,z4,z45])],[(0,[z0,z1,z2,z3,z4,z944]),(0,[z0,z1,z2,z3,z4,z945]),(0,[z0,z1,z2,z3,z946,z5]),(0,[z1,z2,z3,z4,z5,z757]),(0,[z0,z1,z2,z3,z198,z294]),(0,[z0,z947,z1,z2,z3,z5]),(0,[z0,z436,z38,z2,z4,z5])],[(0,[z0,z1,z2,z948,z4,z5]),(0,[z0,z1,z2,z949,z4,z5]),(0,[z0,z1,z950,z3,z4,z5]),(0,[z168,z1,z2,z3,z602,z5]),(0,[z201,z1,z2,z3,z4,z294]),(0,[z0,z1,z2,z3,z5,z951]),(0,[z0,z124,z1,z3,z806,z5])],[(0,[z0,z228,z2,z3,z4,z37]),(0,[z34,z0,z2,z3,z4,z5])]],
   [[(0,[z21,z0,z2,z3,z4,z766]),(0,[z0,z38,z258,z3,z39,z5])],[(0,[z0,z1,z2,z952,z4,z5]),(0,[z0,z1,z2,z278,z287,z5])],[(0,[z0,z1,z2,z3,z4,z296]),(0,[z0,z1,z2,z3,z307,z5])],[(0,[z93,z0,z1,z3,z4,z35])],[(0,[z0,z1,z2,z3,z953,z5]),(0,[z0,z1,z2,z954,z4,z5]),(0,[z0,z1,z2,z955,z4,z5])],[(0,[z1,z956,z216,z3,z4,z5]),(0,[z0,z1,z2,z3,z78,z213])],[(0,[z0,z1,z2,z3,z957,z4]),(0,[z62,z1,z216,z3,z63,z5]),(0,[z10,z1,z2,z54,z4,z5]),(0,[z0,z138,z1,z2,z55,z5]),(0,[z0,z958,z2,z3,z4,z5]),(0,[z0,z1,z48,z3,z4,z37]),(0,[z0,z124,z1,z3,z28,z5]),(0,[z959,z0,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z960,z5]),(0,[z701,z1,z2,z3,z92,z5]),(0,[z0,z291,z2,z3,z213,z5]),(0,[z0,z1,z2,z3,z961,z5]),(0,[z87,z0,z382,z3,z4,z5])]],
   [[(0,[z0,z1,z2,z3,z377,z4]),(0,[z0,z1,z310,z4,z515,z5])],[(0,[z0,z1,z962,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z963]),(0,[z0,z1,z2,z964,z3,z5]),(0,[z0,z1,z2,z965,z4,z5]),(0,[z0,z1,z2,z156,z69,z5])],[(0,[z0,z516,z2,z54,z4,z5]),(0,[z0,z1,z2,z11,z59,z5]),(0,[z12,z0,z2,z3,z4,z227]),(0,[z26,z0,z1,z2,z4,z418])],[(0,[z0,z966,z1,z3,z4,z5]),(0,[z967,z1,z2,z3,z4,z5]),(0,[z0,z968,z2,z3,z4,z5])],[(0,[z1,z800,z2,z3,z4,z5]),(0,[z0,z2,z3,z4,z153,z969]),(0,[z0,z1,z2,z3,z4,z970]),(0,[z971,z0,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z972,z5]),(0,[z289,z0,z2,z55,z4,z5]),(0,[z0,z1,z2,z375,z340,z3]),(0,[z0,z1,z2,z3,z973,z5])],[(0,[z0,z1,z2,z974,z4,z5]),(0,[z0,z1,z2,z3,z975,z5]),(0,[z0,z976,z2,z3,z4,z5]),(0,[z26,z0,z1,z2,z181,z5])],[(0,[z0,z105,z2,z3,z199,z5])]],
   [[(0,[z0,z1,z977,z2,z3,z5]),(0,[z0,z1,z2,z978,z3,z5]),(0,[z26,z0,z1,z2,z605,z5]),(0,[z979,z1,z2,z3,z4,z5])],[(0,[z21,z0,z2,z3,z4,z294])],[(0,[z0,z221,z1,z156,z3,z5])],[(0,[z114,z152,z2,z3,z4,z5]),(0,[z0,z1,z410,z3,z4,z5]),(0,[z0,z1,z2,z369,z3,z4]),(0,[z0,z1,z2,z980,z4,z5]),(0,[z0,z1,z2,z3,z319,z5])],[(0,[z173,z0,z1,z2,z4,z5])],[(0,[z981,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z982,z5]),(0,[z0,z983,z1,z3,z4,z5]),(0,[z26,z0,z1,z2,z624,z5])],[(0,[z0,z2,z3,z4,z45,z37]),(0,[z101,z22,z2,z3,z4,z5]),(0,[z0,z984,z2,z3,z4,z5]),(0,[z30,z1,z321,z3,z4,z13])],[(0,[z0,z985,z2,z3,z4,z5]),(0,[z93,z0,z1,z3,z4,z153]),(0,[z0,z1,z2,z3,z4,z986]),(0,[z0,z1,z987,z3,z4,z5]),(0,[z0,z1,z2,z988,z4,z5]),(0,[z173,z0,z1,z2,z28,z5])]],
   [[(0,[z0,z1,z989,z3,z4,z5]),(0,[z0,z1,z2,z3,z5,z726])],[(0,[z0,z1,z2,z3,z990,z4]),(0,[z0,z670,z1,z2,z4,z83]),(0,[z0,z1,z2,z249,z4,z294])],[(0,[z0,z991,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z992,z5]),(0,[z0,z993,z2,z3,z4,z5]),(0,[z0,z1,z2,z160,z213,z5]),(0,[z994,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z169,z69,z5])],[(0,[z0,z995,z2,z3,z4,z5]),(0,[z10,z445,z1,z2,z4,z5]),(0,[z0,z1,z2,z3,z792,z5])],[(0,[z0,z996,z1,z3,z4,z5]),(0,[z0,z2,z3,z792,z199,z5]),(0,[z0,z1,z2,z997,z4,z5]),(0,[z34,z93,z0,z3,z4,z35]),(0,[z0,z1,z2,z137,z5,z91])],[(0,[z0,z1,z2,z3,z4,z998])],[(0,[z0,z999,z2,z3,z4,z5]),(0,[z30,z0,z2,z3,z4,z227]),(0,[z1000,z1,z2,z3,z4,z5]),(0,[z0,z1,z724,z3,z4,z5]),(0,[z26,z0,z1,z2,z3,z311]),(0,[z0,z1,z564,z3,z4,z31]),(0,[z0,z1,z266,z3,z4,z31])],[(0,[z0,z1001,z1,z2,z3,z4]),(0,[z0,z2,z3,z1002,z4,z5])]],
   [[(0,[z0,z2,z3,z4,z969,z5]),(0,[z27,z1,z2,z3,z92,z5]),(0,[z0,z221,z1,z11,z4,z5])],[(0,[z0,z291,z2,z160,z4,z5]),(0,[z0,z1,z2,z3,z78,z517]),(0,[z0,z225,z2,z17,z4,z5]),(0,[z0,z1,z2,z3,z1003,z4]),(0,[z0,z1,z2,z64,z319,z76])],[(0,[z27,z445,z1,z2,z3,z5]),(0,[z30,z0,z1,z3,z4,z366])],[(0,[z62,z1,z956,z3,z4,z5]),(0,[z0,z1,z2,z3,z198,z214]),(0,[z1004,z1,z2,z3,z4,z5])],[(0,[z201,z1,z2,z3,z4,z214])],[(0,[z403,z0,z2,z55,z4,z5]),(0,[z0,z1005,z2,z3,z4,z5]),(0,[z0,z291,z2,z3,z4,z35]),(0,[z0,z1006,z1,z2,z3,z5])],[(0,[z30,z1,z48,z3,z4,z13]),(0,[z87,z201,z133,z3,z4,z5]),(0,[z0,z38,z2,z3,z199,z5]),(0,[z0,z1,z613,z3,z39,z5])],[(0,[z0,z1,z2,z3,z4,z1007]),(0,[z0,z1,z2,z3,z4,z1008]),(0,[z87,z0,z133,z3,z198,z5]),(0,[z281,z0,z2,z156,z55,z5]),(0,[z0,z1,z2,z3,z5,z1009]),(1,[z0,z1,z3,z806,z5]),(0,[z0,z436,z1,z258,z39,z5])]],
   [[(0,[z1010,z1,z2,z3,z4,z5]),(0,[z0,z1,z3,z4,z1011,z5])],[(0,[z412,z1,z2,z3,z198,z5]),(0,[z34,z0,z3,z4,z5,z31])],[(0,[z0,z1,z2,z3,z198,z5]),(0,[z0,z1012,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z1013]),(0,[z1014,z1,z2,z3,z4,z5]),(0,[z26,z0,z1,z2,z278,z5])],[(0,[z260,z115,z2,z242,z4,z5]),(0,[z0,z1,z321,z3,z4,z5]),(0,[z0,z1,z2,z1015,z4,z5]),(0,[z0,z132,z724,z3,z4,z5])],[(0,[z0,z1,z2,z3,z1016,z5]),(0,[z491,z1,z2,z3,z29,z5]),(0,[z0,z100,z321,z3,z4,z5]),(1,[z0,z2,z3,z792,z5]),(0,[z0,z1,z2,z718,z181,z5])],[(0,[z0,z1,z2,z1017,z4,z5]),(0,[z0,z1,z1018,z3,z4,z5]),(0,[z0,z1,z2,z369,z3,z213]),(0,[z0,z105,z2,z3,z792,z5]),(0,[z68,z0,z2,z69,z148,z5])],[(0,[z22,z800,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z757,z13])]],
   [[(0,[z501,z0,z2,z55,z4,z5]),(0,[z384,z1,z2,z3,z92,z5]),(0,[z12,z1,z2,z3,z4,z475]),(1,[z0,z724,z3,z4,z5]),(0,[z0,z2,z3,z4,z5,z1019]),(0,[z0,z1,z2,z11,z5,z197])],[(0,[z21,z412,z2,z3,z4,z5]),(0,[z0,z1020,z2,z3,z4,z5])],[(0,[z0,z1,z1021,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z1022])],[(0,[z0,z1,z2,z1023,z4,z5]),(0,[z0,z237,z3,z252,z4,z5]),(0,[z0,z2,z3,z4,z1024,z5]),(0,[z0,z1,z2,z3,z806,z5])],[(0,[z0,z1,z1025,z3,z4,z5]),(0,[z0,z1,z2,z3,z1026,z5]),(0,[z0,z1,z1027,z3,z4,z5]),(0,[z0,z1,z48,z3,z4,z60]),(0,[z0,z161,z1,z3,z28,z5]),(0,[z0,z1,z2,z3,z1028,z5])],[(0,[z0,z1,z2,z3,z1029,z5]),(0,[z0,z1,z2,z1030,z4,z5]),(0,[z0,z1,z2,z1031,z4,z5]),(0,[z0,z138,z1,z2,z375,z3]),(0,[z87,z0,z133,z3,z4,z5]),(0,[z0,z237,z132,z3,z4,z5])],[(0,[z21,z0,z2,z3,z4,z45]),(0,[z21,z0,z2,z3,z4,z60]),(0,[z0,z1,z2,z720,z4,z5]),(0,[z93,z0,z1,z3,z4,z831])],[(0,[z0,z1,z2,z1032,z4,z5])]],
   [[(0,[z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z901,z204,z5]),(0,[z0,z1,z2,z3,z4,z1033]),(0,[z0,z1,z2,z3,z4,z418])],[(0,[z0,z1,z2,z3,z4,z1034]),(0,[z30,z1,z2,z3,z4,z757]),(0,[z0,z2,z3,z148,z608,z5]),(0,[z0,z1,z2,z3,z4,z1035]),(0,[z0,z1,z2,z1036,z4,z5]),(0,[z0,z1,z313,z3,z39,z5]),(0,[z0,z1,z2,z3,z1037,z5])],[(0,[z0,z1,z2,z3,z4,z1038]),(0,[z1,z2,z3,z708,z4,z5]),(0,[z0,z1,z2,z1039,z3,z5])],[(0,[z0,z1040,z1,z2,z4,z5]),(0,[z0,z1,z1041,z2,z3,z4]),(0,[z0,z1,z1042,z3,z4,z5]),(0,[z1043,z1,z2,z3,z4,z5]),(0,[z0,z1044,z1,z2,z4,z5])],[(0,[z0,z1,z3,z4,z1045,z5]),(0,[z0,z1,z48,z3,z4,z5]),(0,[z0,z1,z321,z3,z154,z5]),(0,[z0,z134,z1,z141,z4,z188])],[(0,[z0,z1,z2,z3,z1046,z5]),(0,[z0,z2,z3,z1047,z4,z5]),(0,[z0,z100,z48,z3,z4,z5]),(0,[z30,z1,z2,z41,z4,z13]),(0,[z0,z105,z2,z3,z198,z5]),(0,[z87,z0,z3,z4,z37,z31]),(0,[z0,z2,z710,z55,z4,z5]),(0,[z0,z1,z2,z3,z4,z766])],[(0,[z0,z1048,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z1049,z5]),(0,[z0,z1,z2,z3,z1050,z5]),(0,[z173,z27,z0,z1,z2,z5]),(0,[z0,z221,z1,z3,z4,z932]),(0,[z0,z1,z2,z278,z4,z5])],[(0,[z0,z1,z2,z249,z4,z214]),(0,[z0,z1,z1051,z3,z4,z5]),(0,[z68,z0,z2,z3,z148,z5]),(0,[z0,z1052,z1,z2,z3,z4])]],
   [[(0,[z0,z1,z1053,z3,z4,z5]),(0,[z0,z1054,z2,z3,z4,z5]),(0,[z0,z1,z420,z3,z39,z5]),(0,[z0,z1,z2,z377,z150,z4]),(0,[z0,z724,z133,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z1055]),(0,[z0,z38,z2,z169,z3,z5])],[(0,[z0,z1,z2,z3,z1056,z5]),(0,[z281,z0,z2,z55,z4,z5]),(0,[z0,z1057,z2,z3,z4,z5]),(0,[z0,z1,z2,z102,z3,z91])],[(0,[z0,z1,z2,z369,z3,z78]),(0,[z87,z0,z133,z249,z4,z5]),(0,[z0,z1,z2,z3,z4,z1058]),(0,[z0,z2,z33,z278,z4,z5])],[(0,[z0,z1,z2,z242,z4,z5]),(0,[z0,z1,z2,z149,z4,z5]),(0,[z0,z115,z2,z242,z4,z5])],[(0,[z412,z1,z2,z249,z4,z5]),(0,[z1059,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z1060]),(0,[z0,z1,z96,z720,z4,z5])],[(0,[z122,z115,z2,z3,z4,z5]),(0,[z0,z100,z2,z3,z4,z37]),(0,[z0,z1,z2,z249,z4,z5]),(0,[z0,z1061,z2,z3,z4,z5])],[(0,[z0,z1,z321,z41,z4,z5]),(0,[z87,z0,z2,z3,z4,z311]),(0,[z0,z1,z2,z3,z1062,z5]),(0,[z0,z1,z2,z169,z3,z311]),(0,[z0,z1,z1063,z3,z4,z5])]],
   [[(0,[z27,z1,z459,z3,z92,z5]),(0,[z0,z1,z2,z3,z154,z5]),(0,[z0,z2,z3,z33,z4,z5])],[(0,[z0,z1,z2,z1064,z4,z5]),(0,[z0,z1,z3,z4,z153,z31]),(0,[z0,z1,z2,z3,z4,z1065]),(0,[z0,z1066,z1,z2,z4,z5])],[(0,[z0,z1,z2,z1067,z4,z5]),(0,[z0,z1,z2,z3,z1068,z5]),(0,[z10,z1,z2,z340,z54,z5]),(0,[z27,z1,z2,z150,z92,z5]),(0,[z0,z1,z453,z3,z4,z31])],[(0,[z46,z0,z138,z1,z2,z5]),(0,[z0,z1,z2,z3,z821,z5]),(0,[z87,z0,z133,z3,z4,z294]),(0,[z0,z320,z2,z3,z4,z60])],[(0,[z0,z1,z1069,z2,z3,z4]),(0,[z0,z1,z2,z369,z150,z4]),(0,[z0,z1,z48,z3,z154,z5]),(0,[z201,z1,z2,z3,z61,z5]),(0,[z0,z1,z2,z3,z4,z1070]),(0,[z0,z1,z3,z806,z39,z5])],[(0,[z62,z1,z216,z3,z204,z5]),(0,[z142,z1,z956,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z1071]),(0,[z10,z516,z2,z54,z4,z5]),(0,[z412,z1,z2,z3,z4,z294]),(0,[z87,z0,z532,z3,z4,z5])],[(0,[z0,z1,z2,z3,z1072,z5]),(0,[z0,z1,z2,z3,z4,z294]),(0,[z1073,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z1074,z5])],[(0,[z0,z1,z3,z4,z927,z5]),(1,[z0,z2,z3,z4,z766])]],
   [[(0,[z0,z1,z3,z1075,z4,z5]),(0,[z0,z1,z2,z169,z50,z5])],[(0,[z0,z221,z365,z1,z3,z5]),(0,[z0,z1,z2,z1076,z4,z5]),(0,[z0,z1,z2,z11,z287,z5])],[(0,[z0,z1,z2,z3,z4,z1077]),(0,[z820,z0,z1,z2,z204,z5]),(0,[z922,z0,z2,z3,z4,z5]),(0,[z0,z1,z410,z3,z92,z5]),(0,[z1078,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z41,z4,z5]),(0,[z46,z1,z2,z708,z4,z5])],[(0,[z0,z1,z2,z3,z4,z110]),(0,[z0,z1,z2,z3,z4,z1079]),(0,[z0,z1,z956,z3,z4,z5]),(0,[z0,z38,z2,z3,z198,z5]),(0,[z0,z1,z3,z806,z4,z5]),(0,[z0,z1,z2,z169,z278,z5])],[(0,[z0,z1,z2,z3,z4,z1080]),(0,[z0,z1,z2,z102,z3,z213]),(0,[z0,z1,z96,z249,z4,z5])],[(0,[z87,z0,z562,z3,z4,z5])],[(0,[z0,z1,z48,z41,z4,z5]),(0,[z0,z1,z3,z4,z672,z31]),(0,[z0,z1,z2,z3,z4,z747])]],
   [[(0,[z0,z1,z94,z3,z204,z5]),(0,[z0,z1081,z2,z3,z4,z5]),(0,[z286,z0,z1,z3,z4,z294]),(0,[z0,z2,z17,z710,z4,z5])],[(0,[z0,z1,z2,z3,z4,z1082]),(0,[z0,z1,z2,z1083,z4,z5]),(0,[z1084,z1,z2,z3,z4,z5])],[(0,[z1085,z0,z1,z2,z4,z5]),(0,[z0,z1,z1086,z2,z3,z5]),(0,[z26,z0,z1,z410,z3,z5]),(0,[z281,z0,z221,z55,z4,z5])],[(0,[z0,z1,z1087,z3,z4,z5]),(0,[z0,z1,z2,z3,z1088,z5]),(0,[z0,z1,z2,z3,z1089,z5]),(0,[z0,z1090,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z1091,z5]),(0,[z0,z221,z1,z3,z4,z970]),(0,[z0,z1,z2,z3,z4,z754])],[(0,[z1,z94,z956,z3,z4,z5]),(0,[z0,z1092,z2,z3,z4,z5]),(0,[z0,z1,z2,z4,z5,z741])],[(0,[z0,z1,z1093,z3,z4,z5]),(0,[z0,z1,z2,z1094,z4,z5]),(0,[z30,z1,z2,z3,z4,z329]),(0,[z0,z1,z266,z3,z4,z831]),(0,[z0,z82,z1,z2,z4,z83])],[(0,[z0,z1,z2,z1095,z4,z5]),(1,[z1,z2,z3,z821,z5]),(0,[z0,z1,z2,z369,z3,z91]),(0,[z0,z1,z2,z3,z4,z1096]),(0,[z0,z221,z1,z96,z4,z5]),(0,[z0,z1,z2,z3,z1097,z5]),(0,[z0,z1,z2,z4,z5,z1098])],[(0,[z0,z1,z321,z3,z4,z31]),(0,[z0,z1,z2,z1099,z4,z5])]],
   [[(0,[z0,z1,z459,z3,z4,z5]),(0,[z0,z1,z2,z1100,z3,z5]),(0,[z1101,z1,z2,z3,z4,z5]),(0,[z0,z365,z1,z2,z3,z5])],[(0,[z0,z1,z2,z1102,z4,z5]),(0,[z0,z1,z2,z3,z4,z1103]),(0,[z30,z271,z1,z2,z3,z4]),(0,[z0,z1,z1104,z3,z4,z5]),(0,[z1105,z1,z2,z3,z4,z5]),(0,[z0,z1106,z1,z2,z3,z4])],[(0,[z52,z115,z2,z3,z4,z5]),(0,[z0,z1,z1107,z3,z4,z5]),(0,[z0,z1,z2,z150,z4,z5]),(0,[z0,z1,z2,z1108,z3,z4]),(0,[z0,z253,z2,z17,z4,z5])],[(0,[z260,z115,z2,z3,z4,z5]),(0,[z0,z1,z2,z4,z5,z1109]),(0,[z0,z1,z2,z41,z154,z5])],[(0,[z155,z115,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z1110,z5]),(0,[z1,z956,z2,z3,z4,z5]),(0,[z0,z670,z1,z2,z64,z4]),(0,[z0,z1,z2,z64,z160,z4]),(0,[z286,z0,z3,z4,z5,z37]),(0,[z0,z2,z3,z4,z60,z766]),(0,[z1111,z1,z2,z3,z4,z5])],[(0,[z10,z670,z1,z2,z54,z4]),(0,[z0,z1,z2,z340,z3,z5]),(0,[z706,z1,z2,z3,z29,z5]),(0,[z30,z1,z2,z3,z4,z13]),(0,[z0,z1,z2,z1112,z4,z5])],[(0,[z374,z22,z2,z3,z4,z5]),(0,[z0,z1,z1113,z3,z4,z5]),(0,[z30,z100,z2,z3,z4,z13]),(0,[z0,z1,z2,z3,z213,z37]),(0,[z1114,z0,z1,z2,z4,z5]),(0,[z1115,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z169,z5,z405])],[(1,[z1,z956,z3,z4,z5]),(0,[z0,z1,z321,z160,z4,z5]),(0,[z0,z381,z2,z3,z4,z37]),(0,[z0,z1,z2,z249,z61,z5]),(0,[z0,z1,z2,z3,z1116,z5]),(0,[z0,z1,z1117,z3,z4,z5]),(0,[z0,z1,z2,z137,z78,z5])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 545) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 545).take 549) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1094).take 3) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1097)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [545, 549, 3] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 158).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 158).take 98).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [158, 98] = true :=
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

end PEqualNP.Outside.L_meta_37809

theorem PEqualNP.Outside.L_meta_37809 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277074602 * 2 ^ 32 + 4243126272) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277074602 * 2 ^ 32 + 4243126272) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_37809.solve