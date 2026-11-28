import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_37651

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
  Nat.testBit (4276813544 * 2 ^ 32 + 4276791976) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x0400100850002128#64 ++ 0x808002010a000425#64 ++ 0xfa04f018f011ffff#64 ++ 0xff409e031e023fff#64 : BitVec 256),
   (0xf809486328669494#64 ++ 0x1f01290c650cd292#64 ++ 0x779b48e738ee949e#64 ++ 0xeef3691ce71dd293#64 : BitVec 256),
   (0x50228b058b0b18c1#64 ++ 0x0a045160b1616318#64 ++ 0xee638f07cf0f18e5#64 ++ 0xddcc71e0f9e1e31c#64 : BitVec 256),
   (0x60540db00db01e00#64 ++ 0x2c0a81b601b603c0#64 ++ 0xdffc0ff80ff01f03#64 ++ 0xbbff81ff01fe03e0#64 : BitVec 256),
   (0x807fe00006ddc006#64 ++ 0x300ffc0000dbb800#64 ++ 0x3f7ff0000fffe007#64 ++ 0x87effe0001fffc00#64 : BitVec 256),
   (0x00fff6def0000007#64 ++ 0xc01ffedbde000000#64 ++ 0xfefffffff0000000#64 ++ 0x7fdffffffe000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 5]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [0, 7]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [9, 3]⟩, ⟨.or, [8, 10]⟩, ⟨.or, [9, 3]⟩, ⟨.and, [12, 6]⟩, ⟨.or, [13, 4]⟩, ⟨.and, [11, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0400100850002128 0x808002010a000425 0x8804b018c0116b61 0x1100960318022d6c

def z1 : W := mkw 0x0400100850002128 0x808002010a000425 0xfa04f018f011ffff 0xff409e031e023fff

def z2 : W := mkw 0x50228b058b0b18c1 0x0a045160b1616318 0xee638f07cf0f18e5 0xddcc71e0f9e1e31c

def z3 : W := mkw 0x60540db00db01e00 0x2c0a81b601b603c0 0xdffc0ff80ff01f03 0xbbff81ff01fe03e0

def z4 : W := mkw 0x807fe00006ddc006 0x300ffc0000dbb800 0x3f7ff0000fffe007 0x87effe0001fffc00

def z5 : W := mkw 0x80fff6def6ddc007 0xf01ffedbdedbb800 0xffffffffffffe007 0xfffffffffffffc00

def z6 : W := mkw 0xf809486328669494 0x1f01290c650cd292 0x779b48e738ee949e 0xeef3691ce71dd293

def z7 : W := mkw 0x00fff6def6994007 0xe01ffedbded32800 0xfefffffff7116001 0x7fdffffffee22c00

def z8 : W := mkw 0x10228205820b00c1 0x02045040b0416018 0x20038007c00f00e4 0x44007000f801e01c

def z9 : W := mkw 0x008016def0000001 0xc01002dbde000000 0xc0800ffff0000000 0x781001fffe000000

def z10 : W := mkw 0x50228b058b0b18c1 0x0a045160b1616318 0x04630f070f0e0000 0x008c61e0e1e1c000

def z11 : W := mkw 0x00fff6def0000007 0xc01ffedbde000000 0xfefffffff0000000 0x7fdffffffe000000

def z12 : W := mkw 0x54229b0ddb0b39e9 0x8a845361bb61673d 0xfe67ff1fff1fffff 0xffccffe3ffe3ffff

def z13 : W := mkw 0xd07feb058fdfd8c7 0x3a0ffd60b1fbfb18 0xff7fff07cffff8e7 0xdfefffe0f9ffff1c

def z14 : W := mkw 0x0000000000000000 0x0000000000000000 0x3a04f0000011e007 0x87409e0000023c00

def z15 : W := mkw 0x60540db00db01e00 0x2c0a81b601b603c0 0xfffcfff80ff1ff07 0xbfff9fff01fe3fe0

def z16 : W := mkw 0xf8094df329669e94 0x1f0129be652cd3d2 0xf79b4fff38ee9f9e 0xfef369ffe71dd3f3

def z17 : W := mkw 0x500009010b0b18c0 0x0a00012021616318 0xea008000cf0f18e5 0xdd40100019e1e31c

def z18 : W := mkw 0xfc0948632866b5bc 0x1f81290c650cd6b7 0x779b48e738ffffff 0xeef3691ce71fffff

def z19 : W := mkw 0xe07fedb00ffdde06 0x3c0ffdb601ffbbc0 0xfffffff80fffff07 0xbfffffff01ffffe0

def z20 : W := mkw 0x0022820480000001 0x0004504090000000 0x04630f0700000000 0x008c61e0e0000000

def z21 : W := mkw 0x00ffe6d6a0000007 0x401ffcdad4000000 0x04fb0fe700000000 0x009f61fce0000000

def z22 : W := mkw 0x0054049000000000 0x000a809200000000 0xdefc0ff800000000 0x3bdf81ff00000000

def z23 : W := mkw 0x500009010b0b18c0 0x0a00012021616318 0x000000000f0f18e5 0x8000000001e1e31c

def z24 : W := mkw 0x8000000006ddc000 0x3000000000dbb800 0x010000000fffe007 0x8020000001fffc00

def z25 : W := mkw 0x70768fb58fbb1ec1 0x2e0ed1f6b1f763d8 0xeffb8fe7cfef18e5 0xddff71fcf9fde31c

def z26 : W := mkw 0x00fff6def0000007 0xc01ffedbde000000 0xfefffffff000949e 0xffdffffffe001293

def z27 : W := mkw 0x00fff4da70000006 0xc01ffe9b4e000000 0x3efff0f830000000 0x27dffe1f06000000

def z28 : W := mkw 0x04fff6def000212f 0xc09ffedbde000425 0xfefffffff011ffff 0xffdffffffe023fff

def z29 : W := mkw 0x205404b004b00600 0x240a8096009600c0 0x119c00f800f00702 0x2233801f001e00e0

def z30 : W := mkw 0x0009404220000004 0x0001280844000000 0x769b48e730000000 0x6ed3691ce6000000

def z31 : W := mkw 0xf8fffefff8669497 0xdf1fffdfff0cd292 0xfffffffff8ee949e 0xffffffffff1dd293

def z32 : W := mkw 0x807fe00006ddc006 0x300ffc0000dbb800 0x257bf0000fefe004 0x04af7e0001fdfc00

def z33 : W := mkw 0x0054149850000000 0x800a82930a000000 0xfefcfff8f0000000 0x7fdf9fff1e000000

def z34 : W := mkw 0x7800086328221490 0x0f00010c65044292 0x008008e700000000 0x0010011ce0000000

def z35 : W := mkw 0x00dd76def0000007 0xc01baedbde000000 0xd09c7ffff0000000 0x7a138ffffe000000

def z36 : W := mkw 0xa809406220648414 0x1501280c440c9082 0x119840e030e0841a 0x2233081c061c1083

def z37 : W := mkw 0xf82bcb67ab6f9cd5 0x1f05796cf56df39a 0xfffbcfe7ffef9cff 0xffff79fcfffdf39f

def z38 : W := mkw 0x20dd74fa74b00606 0xe41bae9f4e9600c0 0x119c70f830f00702 0x22338e1f061e00e0

def z39 : W := mkw 0x807fe20486ddc007 0x300ffc4090dbb800 0xff7fff07cfffe007 0xdfefffe0f9fffc00

def z40 : W := mkw 0x00ffe6d6a0000007 0x401ffcdad4000000 0x3effffe700000000 0x07dffffce0000000

def z41 : W := mkw 0x00fff7def5900a07 0xe01ffefbdeb20140 0xfefffffff7100b01 0x7fdffffffee20160

def z42 : W := mkw 0x600009200db01e00 0x2c00012401b603c0 0x010000000ff01f03 0x8020000001fe03e0

def z43 : W := mkw 0x10000001020b00c0 0x0200000020416018 0x00000000000f00e4 0x000000000001e01c

def z44 : W := mkw 0x807fe49006ddc006 0x300ffc9200dbb800 0xfffffff80fffe007 0xbfffffff01fffc00

def z45 : W := mkw 0x0000000000000000 0x0000000000000000 0xda04001800101f03 0xbb408003000203e0

def z46 : W := mkw 0x50228b058b0b18c1 0x0a045160b1616318 0xfe678f1fcf1f1fe7 0xffccf1e3f9e3e3fc

def z47 : W := mkw 0x00d416def0000001 0xc01a82dbde000000 0xdefc0ffff0000000 0x7bdf81fffe000000

def z48 : W := mkw 0x802be000024dc006 0x10057c000049b800 0x2003f000000fe004 0x04007e000001fc00

def z49 : W := mkw 0x00f6b69cd0000003 0xc01ed6d39a000000 0x8864b718c0000000 0x110c96e318000000

def z50 : W := mkw 0x00dd64d220000006 0x401bac9a44000000 0x009800e000000000 0x0013001c00000000

def z51 : W := mkw 0xf87fe8632effd496 0x3f0ffd0c65dffa92 0x7ffff8e73ffff49f 0xefffff1ce7fffe93

def z52 : W := mkw 0x60540db00db01e00 0x2c0a81b601b603c0 0x05f80fe00fe00000 0x00bf01fc01fc0000

def z53 : W := mkw 0x00ffe6d6a0000007 0x401ffcdad4000000 0xeefb8fe7c0000000 0x5ddf71fcf8000000

def z54 : W := mkw 0x0400100850002128 0x808002010a000425 0x100470183010e71a 0x22008e0306021ce3

def z55 : W := mkw 0x50228b058b0b18c1 0x0a045160b1616318 0xfe67ff07cf1ff8e7 0xdfccffe0f9e3ff1c

def z56 : W := mkw 0x00dd74da70000006 0xc01bae9b4e000000 0xdefc7ff830000000 0x3bdf8fff06000000

def z57 : W := mkw 0x002bc246a0000005 0x00057848d4000000 0xfefbcfe7f0000000 0x7fdf79fcfe000000

def z58 : W := mkw 0x0000100850000000 0x800002010a000000 0xfa04f018f0000000 0x7f409e031e000000

def z59 : W := mkw 0xf800082108669490 0x1f000104210cd292 0x0100000008ee0000 0x00200000011dc000

def z60 : W := mkw 0x00dd74da70000006 0xc01bae9b4e000000 0x109c70f830000000 0x22138e1f06000000

def z61 : W := mkw 0x502289010b0b18c0 0x0a04512021616318 0x2e6380000f0f18e5 0x85cc700001e1e31c

def z62 : W := mkw 0x0000000000000000 0x0000000000000000 0xea008000c00118e5 0xdd4010001800231c

def z63 : W := mkw 0x0022800002090000 0x0004500000412000 0x2e6380000f0f0005 0x85cc700001e1e000

def z64 : W := mkw 0x847ff00856dde12e 0xb08ffe010adbbc25 0xbf7ff018cfffeb67 0x97effe0319fffd6c

def z65 : W := mkw 0xb809406320668494 0x1701280c640cd092 0x319b40e730ee849e 0x6633681ce61dd093

def z66 : W := mkw 0x0022830483090841 0x0004506090612108 0x88608700c7010861 0x110c10e018e0210c

def z67 : W := mkw 0xf800082108669490 0x1f000104210cd292 0x0100000008ee949e 0x80200000011dd293

def z68 : W := mkw 0x0076a00006994002 0x200ed40000d32800 0x0864b00007116001 0x010c960000e22c00

def z69 : W := mkw 0xf8895efff8669495 0xdf112bdfff0cd292 0xf79b4ffff8ee949e 0xfef369ffff1dd293

def z70 : W := mkw 0x0009504a70000004 0x80012a094e000000 0xfe9ff8fff0000000 0x7fd3ff1ffe000000

def z71 : W := mkw 0x0054049000000000 0x000a809200000000 0x04f80fe000000000 0x009f01fc00000000

def z72 : W := mkw 0x007fe00000000006 0x000ffc0000000000 0x3e7ff00000000000 0x07cffe0000000000

def z73 : W := mkw 0x7800086328221490 0x0f00010c65044292 0x408008e730001498 0x6810011ce6000293

def z74 : W := mkw 0x805d400004d48004 0x300ba800009a9000 0x3f7f40000ffe8007 0x87efe80001ffd000

def z75 : W := mkw 0x0000000000000000 0x0000000000000000 0xfa04f000c011f8e7 0xdf409e0018023f1c

def z76 : W := mkw 0x8000000006ddc000 0x3000000000dbb800 0x010000000fee0000 0x0020000001fdc000

def z77 : W := mkw 0x600009200db01e00 0x2c00012401b603c0 0xcf600f000ff01f03 0x99ec01e001fe03e0

def z78 : W := mkw 0x0000049000000000 0x0000009200000000 0xc0800ff800000000 0x381001ff00000000

def z79 : W := mkw 0x50228b058b0b18c1 0x0a045160b1616318 0xfe63cf07ff0f9cff 0xffcc79e0ffe1f39f

def z80 : W := mkw 0xd009480108469084 0x1a0129002108d210 0x771b480708ee9086 0xcee36900e11dd210

def z81 : W := mkw 0x6000092009201c00 0x0c00012401240380 0xdff80fe00fe01c03 0xbbff01fc01fc0380

def z82 : W := mkw 0xf800082108669490 0x1f000104210cd292 0x7300400038ee949e 0xee600800071dd293

def z83 : W := mkw 0xf82bca67a8669495 0x1f05794cf50cd292 0xfffbcfe7f8ee949e 0xffff79fcff1dd293

def z84 : W := mkw 0x60fffffefdb01e07 0xec1fffffdfb603c0 0xfffffffffff01f03 0xfffffffffffe03e0

def z85 : W := mkw 0x502bcb47ab0b18c5 0x0a057968f5616318 0xfefbcfe7ff0f18e5 0xffdf79fcffe1e31c

def z86 : W := mkw 0xf85d4df32df69e94 0x3f0ba9be65bed3d2 0xffff4fff3ffe9f9f 0xffffe9ffe7ffd3f3

def z87 : W := mkw 0x0022820482090001 0x0004504090412000 0xee638f07cf0f0005 0xddcc71e0f9e1e000

def z88 : W := mkw 0x8076a00006ddc002 0x300ed40000dbb800 0x0964b0000fffe007 0x812c960001fffc00

def z89 : W := mkw 0x04fff6def000212f 0xc09ffedbde000425 0xfefffffff0116b61 0x7fdffffffe022d6c

def z90 : W := mkw 0x205405b005b00e00 0x240a80b600b601c0 0x99fc07f807f00f03 0x333f80ff00fe01e0

def z91 : W := mkw 0x5000080108021080 0x0a00010021004210 0x66030807080e1084 0xccc06100e101c210

def z92 : W := mkw 0xa85d606224f4c416 0x350bac0c449e9882 0x119c70e030f0e41a 0x22338e1c061e1c83

def z93 : W := mkw 0xf8fffefffeffd497 0xff1fffdfffdffa92 0xfffffffffffff49f 0xfffffffffffffe93

def z94 : W := mkw 0x805d600004d4c006 0x300bac00009a9800 0x111c700000f0e002 0x02238e00001e1c00

def z95 : W := mkw 0x0400100850002128 0x808002010a000425 0xc0000018f0001ff8 0x780000031e0003ff

def z96 : W := mkw 0x807fe00006ddc006 0x300ffc0000dbb800 0x057b00000fee0000 0x00af600001fdc000

def z97 : W := mkw 0x8009400000448004 0x1001280000089000 0x20034000000e8004 0x040068000001d000

def z98 : W := mkw 0x60541db85db01e00 0xac0a83b70bb603c0 0xfffcfff8fff01f03 0xffff9fff1ffe03e0

def z99 : W := mkw 0xf8dd7cfb78669496 0xdf1baf9f6f0cd292 0x779f78ff38ee949e 0xeef3ef1fe71dd293

def z100 : W := mkw 0x0000004220000000 0x0000000844000000 0x408008e730000000 0x6810011ce6000000

def z101 : W := mkw 0x50228b058b0b18c1 0x0a045160b1616318 0x88608700cf0f18e5 0x910c10e019e1e31c

def z102 : W := mkw 0x64541db85db03f28 0xac8a83b70bb607e5 0xfffcfff8fff1ffff 0xffff9fff1ffe3fff

def z103 : W := mkw 0x04fff6def000212f 0xc09ffedbde000425 0xfefffffff001e0fc 0x7fdffffffe003c1f

def z104 : W := mkw 0x80fff6def6ddc007 0xf01ffedbdedbb800 0xffffffffffee0000 0x7ffffffffffdc000

def z105 : W := mkw 0x0009404220000004 0x0001280844000000 0x049b08e700000000 0x0093611ce0000000

def z106 : W := mkw 0xfc09586b7866b5bc 0x9f812b0d6f0cd6b7 0xff9ff8fff8ffffff 0xfff3ff1fff1fffff

def z107 : W := mkw 0x0000000000000000 0x0000000000000000 0x569808e000000000 0x2ad3011c00000000

def z108 : W := mkw 0x00fff6def0000007 0xc01ffedbde000000 0x24fbffe7f0000000 0x449f7ffcfe000000

def z109 : W := mkw 0x8009400000448004 0x1001280000089000 0x371b400008ee8006 0x86e36800011dd000

def z110 : W := mkw 0x00ffe6d6a0000007 0x401ffcdad4000000 0x76fb4fe730000000 0x6edf69fce6000000

def z111 : W := mkw 0x0022820480000001 0x0004504090000000 0xee638f07c0000000 0x5dcc71e0f8000000

def z112 : W := mkw 0x0000000000000000 0x0000000000000000 0x0804b00000116001 0x0100960000022c00

def z113 : W := mkw 0x0054000004900000 0x200a800000920000 0x1f7c00000ff00003 0x83ef800001fe0000

def z114 : W := mkw 0x6000082008201400 0x0c00010401040280 0x408008e000001400 0x2810011c00000280

def z115 : W := mkw 0xa800002000648410 0x15000004000c9082 0x0100000000e0841a 0x00200000001c1083

def z116 : W := mkw 0xf87fe86328669496 0x1f0ffd0c650cd292 0x7ffff8e738ee949e 0xefffff1ce71dd293

def z117 : W := mkw 0x60540cb008201400 0x0c0a819601040280 0xdffc0ff808e01402 0xbbff81ff011c0280

def z118 : W := mkw 0x847ff00856dde12e 0xb08ffe010adbbc25 0xff7ff018ffffffff 0xffeffe031fffffff

def z119 : W := mkw 0x0000000000000000 0x0000000000000000 0x7a04f0003011f49f 0xef409e0006023e93

def z120 : W := mkw 0x0400000000002128 0x0080000000000425 0x0000000000001ff8 0x00000000000003ff

def z121 : W := mkw 0x8009404220448004 0x1001280844089000 0x779b48e738ee8006 0xeef3691ce71dd000

def z122 : W := mkw 0x0080124ef0000001 0xc0100249de000000 0x00000007f0000000 0x40000000fe000000

def z123 : W := mkw 0x0000000000000000 0x0000000000000000 0x7200400030000000 0x6e40080006000000

def z124 : W := mkw 0x048016def0002129 0xc09002dbde000425 0xc0800ffff0001ff8 0x781001fffe0003ff

def z125 : W := mkw 0x008006d6a0000001 0x401000dad4000000 0x00800fe700000000 0x001001fce0000000

def z126 : W := mkw 0x54228b058b0b39e9 0x0a845160b161673d 0xee638f07cf1fffff 0xddcc71e0f9e3ffff

def z127 : W := mkw 0x70768fb58fbb1ec1 0x2e0ed1f6b1f763d8 0xffff8fffcfff1fe7 0xfffff1fff9ffe3fc

def z128 : W := mkw 0x0000100850000000 0x800002010a000000 0xfa04f018f011e007 0xff409e031e023c00

def z129 : W := mkw 0x8000000006ddc000 0x3000000000dbb800 0x3b04f0000fffe007 0x87609e0001fffc00

def z130 : W := mkw 0x60540db00db01e00 0x2c0a81b601b603c0 0xc5f80ff80fe01f00 0x38bf01ff01fc03e0

def z131 : W := mkw 0x807fe00006ddc006 0x300ffc0000dbb800 0x0d7fb0000fff6001 0x01aff60001ffec00

def z132 : W := mkw 0x0400100850002128 0x808002010a000425 0x9804f018f011ef7b 0x33009e031e023def

def z133 : W := mkw 0x9809404320468094 0x130128086408d012 0x20034007300e809c 0x44006800e601d013

def z134 : W := mkw 0x0054059005900a00 0x200a80b200b20140 0x8864071807100b01 0x110c80e300e20160

def z135 : W := mkw 0xf8ffeef7a8669497 0x5f1ffddef50cd292 0x05fb0fe708ee0000 0x00bf61fce11dc000

def z136 : W := mkw 0xf809486328669494 0x1f01290c650cd292 0x7f9ff8e738fff49f 0xeff3ff1ce71ffe93

def z137 : W := mkw 0x5000080108021080 0x0a00010021004210 0x04030807080e0000 0x00806100e101c000

def z138 : W := mkw 0x7000082108221480 0x0e00010421044290 0x779b08e708ee1486 0xeef3611ce11dc290

def z139 : W := mkw 0x50ffffdff90218c7 0xca1ffffbff204318 0xfefffffff00018e0 0x7fdffffffe00031c

def z140 : W := mkw 0x70228b258fbb1ec1 0x2e045164b1f763d8 0xef638f07cfff1fe7 0xddec71e0f9ffe3fc

def z141 : W := mkw 0x04fff6def000212f 0xc09ffedbde000425 0xfefffffff010e71a 0x7fdffffffe021ce3

def z142 : W := mkw 0xe47ffdb85ffdff2e 0xbc8fffb70bffbfe5 0xfffffff8ffffffff 0xffffffff1fffffff

def z143 : W := mkw 0x60540db00db01e00 0x2c0a81b601b603c0 0xd19c0ff800f01f02 0x3a3381ff001e03e0

def z144 : W := mkw 0xf87fe8632effd496 0x3f0ffd0c65dffa92 0x05fb08e70fee0000 0x00bf611ce1fdc000

def z145 : W := mkw 0x80ffe6d6a6ddc007 0x701ffcdad4dbb800 0x3fffffe70fffe007 0x87fffffce1fffc00

def z146 : W := mkw 0x0000000000000000 0x0000000000000000 0x2a00800000010005 0x8540100000002000

def z147 : W := mkw 0xc07fe9000fddd806 0x380ffd2001fbbb00 0xff7fff000ffff807 0x9fefffe001ffff00

def z148 : W := mkw 0x2000002000200400 0x0400000400040080 0x119800e000e00402 0x2233001c001c0080

def z149 : W := mkw 0xfcfffefff866b5bf 0xdf9fffdfff0cd6b7 0xfffffffff8ffffff 0xffffffffff1fffff

def z150 : W := mkw 0x0000010005900a00 0x2000002000b20140 0x0000000007100b01 0x0000000000e20160

def z151 : W := mkw 0x0400100850002128 0x808002010a000425 0xf2004018f0009ffe 0xfe4008031e0013ff

def z152 : W := mkw 0x0000000002090000 0x0000000000412000 0x000000000f0f0005 0x8000000001e1e000

def z153 : W := mkw 0x04fff6def000212f 0xc09ffedbde000425 0xfefffffff0001ff8 0x7fdffffffe0003ff

def z154 : W := mkw 0x00a296def0000001 0xc01452dbde000000 0xeee38ffff0000000 0x7ddc71fffe000000

def z155 : W := mkw 0x8000000004d4c000 0x30000000009a9800 0x0100000000f0e002 0x00200000001e1c00

def z156 : W := mkw 0xf809486328669494 0x1f01290c650cd292 0x579b08e708ee1402 0xaaf3611ce11dc280

def z157 : W := mkw 0x0400100850002128 0x808002010a000425 0xe000f018f001fffc 0x7c001e031e003fff

def z158 : W := mkw 0xe05d4db00df49e04 0x3c0ba9b601be93c0 0xffff4ff80ffe9f07 0xbfffe9ff01ffd3e0

def z159 : W := mkw 0x84fff6def6dde12f 0xf09ffedbdedbbc25 0xffffffffffffffff 0xffffffffffffffff

def z160 : W := mkw 0x00fff6def2090007 0xc01ffedbde412000 0xfeffffffff0f0005 0xffdfffffffe1e000

def z161 : W := mkw 0x0000100850000000 0x800002010a000000 0x2000f000f0000000 0x44001e001e000000

def z162 : W := mkw 0xf809486328669494 0x1f01290c650cd292 0x059b08e708ee0000 0x00b3611ce11dc000

def z163 : W := mkw 0x70540db10db21e80 0x2e0a81b621b643d0 0xffff0fff0ffe1f87 0xffffe1ffe1ffc3f0

def z164 : W := mkw 0x50000b05890218c1 0x0a000160b1204318 0xc0000f07c00018e0 0x580001e0f800031c

def z165 : W := mkw 0x60540db00db01e00 0x2c0a81b601b603c0 0xc8e40ff807101f01 0x391c81ff00e203e0

def z166 : W := mkw 0x0054000000000000 0x000a800000000000 0x1e7c000000000000 0x03cf800000000000

def z167 : W := mkw 0x0400000000002128 0x0080000000000425 0x3a04f0000011ffff 0x87409e0000023fff

def z168 : W := mkw 0x8400100856dde128 0xb08002010adbbc25 0xfb04f018ffffffff 0xff609e031fffffff

def z169 : W := mkw 0x0000000000000000 0x0000000000000000 0x720040003000949e 0xee40080006001293

def z170 : W := mkw 0x54001809580231a8 0x8a8003012b004635 0xfe07f81ff81fffff 0xffc0ff03ff03ffff

def z171 : W := mkw 0x60000db009201e00 0x0c0001b6012403c0 0xc0800ff800001f00 0x381001ff000003e0

def z172 : W := mkw 0x0000000000000000 0x0000000000000000 0xea008000c0000000 0x5d40100018000000

def z173 : W := mkw 0x6000082008201400 0x0c00010401040280 0x579808e008e01402 0xaaf3011c011c0280

def z174 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000000000118e5 0x800000000000231c

def z175 : W := mkw 0x847fe00006dde12e 0x308ffc0000dbbc25 0x3f7ff0000fffffff 0x87effe0001ffffff

def z176 : W := mkw 0x50ffffdffb0b18c7 0xca1ffffbff616318 0xfeffffffff0f18e5 0xffdfffffffe1e31c

def z177 : W := mkw 0x0089704a70000006 0xc0112e094e000000 0x0000700030000000 0x00000e0006000000

def z178 : W := mkw 0xe07fe9200ffdde06 0x3c0ffd2401ffbbc0 0x3f7ff0000fffff07 0x87effe0001ffffe0

def z179 : W := mkw 0x807fe00006ddc006 0x300ffc0000dbb800 0xff7ff000cffff8e7 0xdfeffe0019ffff1c

def z180 : W := mkw 0x807fe00006ddc006 0x300ffc0000dbb800 0xff7ff0180fffff07 0xbfeffe0301ffffe0

def z181 : W := mkw 0x0400100850002128 0x808002010a000425 0xea00f000f001f8fd 0xdd401e001e003f1f

def z182 : W := mkw 0xe85d4df22df49e14 0x3d0ba9be45be93c2 0xdffc4ff83ff09f1b 0xbbff89ff07fe13e3

def z183 : W := mkw 0x0400100850002128 0x808002010a000425 0x80000018c0000b60 0x100000031800016c

def z184 : W := mkw 0x98fff6dff0468097 0xd31ffedbfe08d012 0xfefffffff00e809c 0x7fdffffffe01d013

def z185 : W := mkw 0x00fff6def0000007 0xc01ffedbde000000 0xfefffffff0101f03 0xffdffffffe0203e0

def z186 : W := mkw 0xe05d6db00df4de06 0x3c0badb601be9bc0 0xdffc7ff80ff0ff03 0xbbff8fff01fe1fe0

def z187 : W := mkw 0x9809404320468094 0x130128086408d012 0x371b400738ee809e 0xc6e36800e71dd013

def z188 : W := mkw 0x70228b258b2b1cc1 0x0e045164b1656398 0xfffb8fe7cfef1ce7 0xffff71fcf9fde39c

def z189 : W := mkw 0xf80949632b6f9cd4 0x1f01292c656df39a 0x779b48e73fef9cff 0xeef3691ce7fdf39f

def z190 : W := mkw 0x507feb058b0b18c7 0x0a0ffd60b1616318 0xfe7fff07cf0f18e5 0xdfcfffe0f9e1e31c

def z191 : W := mkw 0xf800086328669490 0x1f00010c650cd292 0x418008e738ee949e 0xe830011ce71dd293

def z192 : W := mkw 0x74769fbddfbb3fe9 0xae8ed3f7bbf767fd 0xffffffffffffffff 0xffffffffffffffff

def z193 : W := mkw 0x0000000000000000 0x0000000000000000 0xfa048018c0111fe7 0xff409003180223fc

def z194 : W := mkw 0x64001db859203f28 0x8c8003b70b2407e5 0xfa84fff8f011ffff 0xff509fff1e023fff

def z195 : W := mkw 0x00f6b6def0000003 0xc01ed6dbde000000 0xc8e4bffff0000000 0x791c97fffe000000

def z196 : W := mkw 0xf8ffeef7a8669497 0x5f1ffddef50cd292 0x77fb4fe738ee949e 0xeeff69fce71dd293

def z197 : W := mkw 0x00abf24ef0000007 0xc0157e49de000000 0x2003f007f0000000 0x44007e00fe000000

def z198 : W := mkw 0x60540db009201e00 0x0c0a81b6012403c0 0xdefc0ff800001f00 0x3bdf81ff000003e0

def z199 : W := mkw 0x4000090009001800 0x0800012001200300 0x04600f000f000000 0x008c01e001e00000

def z200 : W := mkw 0x0022800002090000 0x0004500000412000 0x20038000000f0004 0x040070000001e000

def z201 : W := mkw 0xf809486328669494 0x1f01290c650cd292 0x2103400738ee949e 0xc4206800e71dd293

def z202 : W := mkw 0x0400100850002128 0x808002010a000425 0xfa04f018f001e0fc 0x7f409e031e003c1f

def z203 : W := mkw 0xac09506a7064a53c 0x95812a0d4e0c94a7 0xfb9cf0f8f0f1ffff 0xff739e1f1e1e3fff

def z204 : W := mkw 0x5000080108021080 0x0a00010021004210 0x00000000080e1084 0x800000000101c210

def z205 : W := mkw 0xd0228b058fdfd8c1 0x3a045160b1fbfb18 0xef638f07cffff8e7 0xddec71e0f9ffff1c

def z206 : W := mkw 0x607fedb00db01e06 0x2c0ffdb601b603c0 0xfffffff80ff01f03 0xbfffffff01fe03e0

def z207 : W := mkw 0x0000000000000000 0x0000000000000000 0xc0000000c00018e0 0x580000001800031c

def z208 : W := mkw 0x0000000000000000 0x0000000000000000 0x200040003000809c 0x4400080006001013

def z209 : W := mkw 0x80fff6def24dc007 0xd01ffedbde49b800 0xfefffffff00fe004 0x7fdffffffe01fc00

def z210 : W := mkw 0xf809486328669494 0x1f01290c650cd292 0xff9bc8e7f8ef9cff 0xfff3791cff1df39f

def z211 : W := mkw 0xd02bcb058b4f98c5 0x1a057960b169f318 0xff7bcf07cfef98e7 0xdfef79e0f9fdf31c

def z212 : W := mkw 0x0400100850002128 0x808002010a000425 0x2000f000f001e0fc 0x44001e001e003c1f

def z213 : W := mkw 0xe07fedb00ffdde06 0x3c0ffdb601ffbbc0 0x3fffffe00fffe007 0x87fffffc01fffc00

def z214 : W := mkw 0x20fff6fef4b00607 0xe41ffedfde9600c0 0xfffffffff0f00702 0x7ffffffffe1e00e0

def z215 : W := mkw 0x0400100850002128 0x808002010a000425 0xd0047018f010fffa 0x7a008e031e021fff

def z216 : W := mkw 0x78000df329221e90 0x0f0001be652443d2 0xc0800fff30001f98 0x781001ffe60003f3

def z217 : W := mkw 0xf809486328669494 0x1f01290c650cd292 0xff9f48ff38fe9f9f 0xfff3e91fe71fd3f3

def z218 : W := mkw 0x008016def0000001 0xc01002dbde000000 0xfa84fffff0000000 0x7f509ffffe000000

def z219 : W := mkw 0x04f6b69cd000212b 0xc09ed6d39a000425 0x8864b718c0116b61 0x110c96e318022d6c

def z220 : W := mkw 0x60540db00db01e00 0x2c0a81b601b603c0 0x1ffc0fe00ff00003 0x83ff81fc01fe0000

def z221 : W := mkw 0x005d44d220000004 0x000ba89a44000000 0xfeff4fff30000000 0x7fdfe9ffe6000000

def z222 : W := mkw 0x0000000000000000 0x0000000000000000 0x100040003000841a 0x2200080006001083

def z223 : W := mkw 0x50ffffdffb0b18c7 0xca1ffffbff616318 0xfeffffffff0e0000 0x7fdfffffffe1c000

def z224 : W := mkw 0x0054000004900000 0x200a800000920000 0x057800000fe00000 0x00af000001fc0000

def z225 : W := mkw 0x405409000d901800 0x280a812001b20300 0xdf7c0f000ff01803 0x9bef81e001fe0300

def z226 : W := mkw 0x80fff6def4d4c007 0xf01ffedbde9a9800 0xfffffffff0f0e002 0x7ffffffffe1e1c00

def z227 : W := mkw 0x7809486328221494 0x0f01290c65044292 0x769b48e730001498 0x6ed3691ce6000293

def z228 : W := mkw 0x007fe00006994006 0x200ffc0000d32800 0x3e7ff00007116001 0x07cffe0000e22c00

def z229 : W := mkw 0x54001b0dd90239e9 0x8a800361bb20473d 0xc0000f1ff0001ff8 0x780001e3fe0003ff

def z230 : W := mkw 0x0022820480000001 0x0004504090000000 0x88608700c0000000 0x110c10e018000000

def z231 : W := mkw 0xf85d4cf328669494 0x1f0ba99e650cd292 0xffff4fff38ee949e 0xffffe9ffe71dd293

def z232 : W := mkw 0x807fe04226ddc006 0x300ffc0844dbb800 0x7ffff8e73fffe007 0xefffff1ce7fffc00

def z233 : W := mkw 0x0054000004900000 0x200a800000920000 0x111c000000f00002 0x02238000001e0000

def z234 : W := mkw 0x200004b000200600 0x04000096000400c0 0x008000f800000700 0x2010001f000000e0

def z235 : W := mkw 0x0400100850002128 0x808002010a000425 0xba04f018c011eb67 0x97409e0318023d6c

def z236 : W := mkw 0x54ffffdffb0b39ef 0xca9ffffbff61673d 0xfeffffffff1fffff 0xffdfffffffe3ffff

def z237 : W := mkw 0x0009404220000004 0x0001280844000000 0x109840e030000000 0x2213081c06000000

def z238 : W := mkw 0x60540db00db01e00 0x2c0a81b601b603c0 0xfffc8ff8cff11fe7 0xffff91ff19fe23fc

def z239 : W := mkw 0x807fe00006ddc006 0x300ffc0000dbb800 0x157f70000ffee002 0x02afee0001ffdc00

def z240 : W := mkw 0x0000000000000000 0x0000000000000000 0x4000000030001498 0x6800000006000293

def z241 : W := mkw 0x0076869480000001 0x000ed0d290000000 0xfeff8fffc0000000 0x7fdff1fff8000000

def z242 : W := mkw 0xd809484328469094 0x1b0129086508d212 0x66034807380e909c 0xccc06900e701d213

def z243 : W := mkw 0xf85d4df32df69e94 0x3f0ba9be65bed3d2 0x05fb0fe70fee0000 0x00bf61fce1fdc000

def z244 : W := mkw 0x50fffedff8021087 0xca1fffdbff004210 0xfefffffff80e1084 0xffdfffffff01c210

def z245 : W := mkw 0xf80009210df69e90 0x3f00012421bed3d2 0x010000000ffe9f9f 0x8020000001ffd3f3

def z246 : W := mkw 0x0476b0085699612a 0xa08ed6010ad32c25 0xfa64f018f711ffff 0xff4c9e031ee23fff

def z247 : W := mkw 0x007fe00004900006 0x200ffc0000920000 0x3f7ff0000ff00003 0x87effe0001fe0000

def z248 : W := mkw 0xf80009210b6f9cd0 0x1f000124216df39a 0x010000000fef9cff 0x8020000001fdf39f

def z249 : W := mkw 0x60fffefef8201407 0xcc1fffdfdf040280 0xfffffffff8e01402 0xffffffffff1c0280

def z250 : W := mkw 0x0454159855902b28 0xa08a82b30ab20565 0xfa64f718f711ffff 0xff4c9ee31ee23fff

def z251 : W := mkw 0x50a29fdffb0b18c1 0xca1453fbff616318 0xeee38fffff0f18e5 0xfddc71ffffe1e31c

def z252 : W := mkw 0xf809486328669494 0x1f01290c650cd292 0x159b48e738ee841a 0x22b3691ce71dd083

def z253 : W := mkw 0x0400000000002128 0x0080000000000425 0x000000000011ffff 0x8000000000023fff

def z254 : W := mkw 0xfc5d5dfb7df6bfbc 0xbf8babbf6fbed7f7 0xffffffffffffffff 0xffffffffffffffff

def z255 : W := mkw 0x50228b058b0b18c1 0x0a045160b1616318 0xc4630f07cf0e18e0 0x588c61e0f9e1c31c

def z256 : W := mkw 0x50000b05890218c1 0x0a000160b1204318 0xce600f07cf0018e1 0xd9cc01e0f9e0031c

def z257 : W := mkw 0x700009210fbb1ec0 0x2e00012421f763d8 0x010000000fff1fe7 0x8020000001ffe3fc

def z258 : W := mkw 0x6000092009201e00 0x0c000124012403c0 0x0000000000001f00 0x00000000000003e0

def z259 : W := mkw 0x8009400006ddc004 0x3001280000dbb800 0x371b40000fffe007 0x86e3680001fffc00

def z260 : W := mkw 0xf809486328669494 0x1f01290c650cd292 0x679b08e708ee1084 0xccf3611ce11dc210

def z261 : W := mkw 0xe07fedb00ffdde06 0x3c0ffdb601ffbbc0 0x05fb0fe00fee0000 0x00bf61fc01fdc000

def z262 : W := mkw 0x9809404320468094 0x130128086408d012 0x72034007300e949e 0xee406800e601d293

def z263 : W := mkw 0x00fff6def4900007 0xe01ffedbde920000 0xfffffffffff00003 0xfffffffffffe0000

def z264 : W := mkw 0xf80948632effd494 0x3f01290c65dffa92 0x779b48e73ffff49f 0xeef3691ce7fffe93

def z265 : W := mkw 0x0400100850002128 0x808002010a000425 0x00000000f00000f8 0x400000001e00001f

def z266 : W := mkw 0x007fe20480000007 0x000ffc4090000000 0xfe7fff07c0000000 0x5fcfffe0f8000000

def z267 : W := mkw 0x10228305830b08c1 0x02045060b0616118 0xa8638707c70f08e5 0x550c70e0f8e1e11c

def z268 : W := mkw 0x0022820480000001 0x0004504090000000 0xee638f07c00118e5 0xddcc71e0f800231c

def z269 : W := mkw 0xf8540db10df69e90 0x3f0a81b621bed3d2 0xdffc0ff80ffe9f9f 0xbbff81ff01ffd3f3

def z270 : W := mkw 0x00abf24ef0000007 0xc0157e49de000000 0xee63ff07f0000000 0x5dcc7fe0fe000000

def z271 : W := mkw 0x60768fb48fb91e41 0x2c0ed1f691f723c8 0xdffc8ff8cff11f63 0xbbff91ff19fe23ec

def z272 : W := mkw 0x007fe00000000006 0x000ffc0000000000 0x3e7ff0000011e007 0x87cffe0000023c00

def z273 : W := mkw 0x0400100850002128 0x808002010a000425 0x2000f000f011ffff 0xc4001e001e023fff

def z274 : W := mkw 0x6000082008201400 0x0c00010401040280 0x059808e008e00000 0x00b3011c011c0000

def z275 : W := mkw 0x807fe00006ddc006 0x300ffc0000dbb800 0x311ff00000ffe006 0x0623fe00001ffc00

def z276 : W := mkw 0x600009200db01e00 0x2c00012401b603c0 0x010000000fe00000 0x0020000001fc0000

def z277 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z278 : W := mkw 0x50228b058b0b18c1 0x0a045160b1616318 0x24638f07cf0f00e4 0x448c71e0f9e1e01c

def z279 : W := mkw 0x0076a59007994a02 0x200ed4b200f32940 0x8864b71807116b01 0x110c96e300e22d60

def z280 : W := mkw 0x0009400000000004 0x0001280000000000 0x361b400000000000 0x06c3680000000000

def z281 : W := mkw 0x00f6b69cd6994003 0xe01ed6d39ad32800 0x8864b718c7116001 0x110c96e318e22c00

def z282 : W := mkw 0xf82bcb67ab6f9cd5 0x1f05796cf56df39a 0x77fb4fe73fee949e 0xeeff69fce7fdd293

def z283 : W := mkw 0x0400100850002128 0x808002010a000425 0xea008018f0011ffd 0xfd4010031e0023ff

def z284 : W := mkw 0x600009200db01e00 0x2c00012401b603c0 0xdb0400180ff01f03 0xbb60800301fe03e0

def z285 : W := mkw 0xf8fffffffb6f9cd7 0xdf1fffffff6df39a 0xffffffffffef9cff 0xfffffffffffdf39f

def z286 : W := mkw 0x10000205800200c1 0x02000040b0004018 0x00000007c00000e0 0x40000000f800001c

def z287 : W := mkw 0x00fff6def0000007 0xc01ffedbde000000 0xfefffffff00118e5 0xffdffffffe00231c

def z288 : W := mkw 0x64541db85db03f28 0xac8a83b70bb607e5 0xdffc7ff83ff0ff1b 0xbbff8fff07fe1fe3

def z289 : W := mkw 0x10228205820b00c1 0x02045040b0416018 0x00030007000e0000 0x00006000e001c000

def z290 : W := mkw 0x0400100850002128 0x808002010a000425 0x3004f018f011e7fe 0x66009e031e023cff

def z291 : W := mkw 0xf87fcff7afff9ed5 0x3f0ff9fef5fff3da 0xffffcfffffff9fff 0xfffff9fffffff3ff

def z292 : W := mkw 0x987fe04326dfc096 0x330ffc0864dbf812 0x3f7ff0073fffe09f 0xc7effe00e7fffc13

def z293 : W := mkw 0x982be043224fc096 0x13057c086449f812 0x2003f007300fe09c 0x44007e00e601fc13

def z294 : W := mkw 0x60fffffefdb01e07 0xec1fffffdfb603c0 0xffffffffffe00000 0x7ffffffffffc0000

def z295 : W := mkw 0x50228b058b0b18c1 0x0a045160b1616318 0xc8608f07c70118e1 0x590c11e0f8e0231c

def z296 : W := mkw 0xe0fffffefffdde07 0xfc1fffffdfffbbc0 0xffffffffffffff07 0xffffffffffffffe0

def z297 : W := mkw 0x807fe00006ddc006 0x300ffc0000dbb800 0x1f7f00000ffe0003 0x83efe00001ffc000

def z298 : W := mkw 0x4000090009001800 0x0800012001200300 0xce600f000f001801 0x99cc01e001e00300

def z299 : W := mkw 0x00fff6def0000007 0xc01ffedbde000000 0x309ff0fff0000000 0x6613fe1ffe000000

def z300 : W := mkw 0x0022830483090841 0x0004506090612108 0xae638700cf0f0865 0x95cc70e019e1e10c

def z301 : W := mkw 0x60ffeff6adb01e07 0x6c1ffdfed5b603c0 0xdfff0fff0ff01f03 0xbbffe1ffe1fe03e0

def z302 : W := mkw 0x60540db00db01e00 0x2c0a81b601b603c0 0x05f80fe00ff01f03 0x80bf01fc01fe03e0

def z303 : W := mkw 0x60540db00db01e00 0x2c0a81b601b603c0 0xcff80fe00fe01801 0x99ff01fc01fc0300

def z304 : W := mkw 0x0076a00006994002 0x200ed40000d32800 0x3a64f0000711e007 0x874c9e0000e23c00

def z305 : W := mkw 0xf07fefb58fffdec7 0x3e0ffdf6b1fffbd8 0xffffffffcfffffe7 0xfffffffff9fffffc

def z306 : W := mkw 0x0000100850000000 0x800002010a000000 0xc0000018f0000000 0x780000031e000000

def z307 : W := mkw 0xa809406220648414 0x1501280c440c9082 0x019800e000e00000 0x0033001c001c0000

def z308 : W := mkw 0x40540d900d901a00 0x280a81b201b20340 0xce640f180f101b01 0x99cc81e301e20360

def z309 : W := mkw 0x0400100850002128 0x808002010a000425 0x3a04f000f011e0ff 0xc7409e001e023c1f

def z310 : W := mkw 0x78fffefff8221497 0xcf1fffdfff044292 0xfefffffff0001498 0x7fdffffffe000293

def z311 : W := mkw 0x540019095b0b39e8 0x8a8003212b61673d 0xfa04f018ff1fffff 0xff409e031fe3ffff

def z312 : W := mkw 0x0409504a7000212c 0x80812a094e000425 0xfe9ff8fff011ffff 0xffd3ff1ffe023fff

def z313 : W := mkw 0x60540db00db01e00 0x2c0a81b601b603c0 0x15fc0ff80ff00702 0x22bf81ff01fe00e0

def z314 : W := mkw 0x50000b05890218c1 0x0a000160b1204318 0xea008f07c00118e5 0xdd4011e0f800231c

def z315 : W := mkw 0xa8dd74fa70648416 0xd51bae9f4e0c9082 0x119c70f830e0841a 0x22338e1f061c1083

def z316 : W := mkw 0x64541db85db03f28 0xac8a83b70bb607e5 0xdffcbff8cff17f63 0xbbff97ff19fe2fec

def z317 : W := mkw 0x0000000000000000 0x0000000000000000 0xfa04f0180011ff07 0xbf409e0300023fe0

def z318 : W := mkw 0x0454149850002128 0x808a82930a000425 0xfefcfff8f011ffff 0xffdf9fff1e023fff

def z319 : W := mkw 0x9800000100468090 0x130000002008d012 0x00000000000e809c 0x000000000001d013

def z320 : W := mkw 0xfc09586b7866b5bc 0x9f812b0d6f0cd6b7 0x779bf8e7f8eff4fe 0xeef37f1cff1dfe9f

def z321 : W := mkw 0x60540db00db01e00 0x2c0a81b601b603c0 0x8dfc0ff80ff00b01 0x11bf81ff01fe0160

def z322 : W := mkw 0x807fe00006ddc006 0x300ffc0000dbb800 0x2867f000071fe005 0x050cfe0000e3fc00

def z323 : W := mkw 0x5000090109021880 0x0a00012021204310 0xee630f070f0e1885 0xddcc61e0e1e1c310

def z324 : W := mkw 0x60dd7dfa7db01e06 0xec1bafbf4fb603c0 0xdffc7ff83ff01f03 0xbbff8fff07fe03e0

def z325 : W := mkw 0x0054059005900a00 0x200a80b200b20140 0xda64071807101f03 0xbb4c80e300e203e0

def z326 : W := mkw 0xf87fedf32fffde96 0x3f0ffdbe65fffbd2 0xffffffff3fffff9f 0xffffffffe7fffff3

def z327 : W := mkw 0x0000059001000a00 0x000000b200200140 0x8000071800000b00 0x100000e300000160

def z328 : W := mkw 0x807fe000024dc006 0x100ffc000049b800 0x3e7ff000000fe004 0x07cffe000001fc00

def z329 : W := mkw 0x0000000000000000 0x0000000000000000 0x100470000010e002 0x02008e0000021c00

def z330 : W := mkw 0x00ffe6d6a0000007 0x401ffcdad4000000 0xdeff0fff00000000 0x3bdfe1ffe0000000

def z331 : W := mkw 0x60000db009201e00 0x0c0001b6012403c0 0x00800fe000000000 0x001001fc00000000

def z332 : W := mkw 0x0080169cd0000001 0xc01002d39a000000 0x80000718c0000000 0x100000e318000000

def z333 : W := mkw 0x807fe00006ddc006 0x300ffc0000dbb800 0x2f7b80000fef0005 0x85ef700001fde000

def z334 : W := mkw 0xf85d4cf32cf69694 0x3f0ba99e659ed2d2 0x779f48ff38fe979e 0xeef3e91fe71fd2f3

def z335 : W := mkw 0x8009400000448004 0x1001280000089000 0x3f1ff00008ffe007 0x87e3fe00011ffc00

def z336 : W := mkw 0x0400100850002128 0x808002010a000425 0xda040018f0101ffb 0xfb4080031e0203ff

def z337 : W := mkw 0x540009010b0b39e8 0x0a8001202161673d 0x000000000f1fffff 0x8000000001e3ffff

def z338 : W := mkw 0xf809486328669494 0x1f01290c650cd292 0x519848e730e0949a 0x6a33091ce61c1293

def z339 : W := mkw 0x805d600004d4c006 0x300bac00009a9800 0x0118000000e00000 0x00230000001c0000

def z340 : W := mkw 0x0400100850002128 0x808002010a000425 0xc804b018f0117ff9 0x790096031e022fff

def z341 : W := mkw 0x640019285db03f28 0xac8003250bb607e5 0xfb04f018fff1ffff 0xff609e031ffe3fff

def z342 : W := mkw 0x0054049000000000 0x000a809200000000 0xdefc0ff800101f03 0xbbdf81ff000203e0

def z343 : W := mkw 0xd82bcb47ab4f98d5 0x1b057968f569f31a 0xee63cf07ff0f98fd 0xddcc79e0ffe1f31f

def z344 : W := mkw 0x0000000000000000 0x0000000000000000 0x3a04f00000000000 0x07409e0000000000

def z345 : W := mkw 0x0400100850002128 0x808002010a000425 0x0000001830000718 0x20000003060000e3

def z346 : W := mkw 0x00fff6def0000007 0xc01ffedbde000000 0xfefffffff011e007 0xffdffffffe023c00

def z347 : W := mkw 0x0000000000000000 0x0000000000000000 0x3200400000008006 0x8640080000001000

def z348 : W := mkw 0x7800086328221490 0x0f00010c65044292 0x728048e73000949e 0xee50091ce6001293

def z349 : W := mkw 0x1000000100020080 0x0200000020004010 0x20030007000e0084 0x44006000e001c010

def z350 : W := mkw 0x00fff6def0000007 0xc01ffedbde000000 0x14ff7fff30000000 0x229fefffe6000000

def z351 : W := mkw 0xd02beb058b4fd8c7 0x1a057d60b169fb18 0xee63ff07cf0ff8e5 0xddcc7fe0f9e1ff1c

def z352 : W := mkw 0x60d41ffefdb01e01 0xec1a83ffdfb603c0 0xdffc0ffffff01f03 0xfbff81fffffe03e0

def z353 : W := mkw 0x0076879487990a41 0x200ed0f290f32148 0x88648718c7110b61 0x110c90e318e2216c

def z354 : W := mkw 0x007fe00002090006 0x000ffc0000412000 0x3e7ff0000f0f0005 0x87cffe0001e1e000

def z355 : W := mkw 0x0400000000002128 0x0080000000000425 0xea008000c011ffff 0xdd40100018023fff

def z356 : W := mkw 0xd0ffffdfffdfd8c7 0xfa1ffffbfffbfb18 0xfffffffffffff8e7 0xffffffffffffff1c

def z357 : W := mkw 0x0000000000000000 0x0000000000000000 0x6200000000001084 0xcc40000000000210

def z358 : W := mkw 0x0000000000000000 0x0000000000000000 0x20008000c00100e4 0x440010001800201c

def z359 : W := mkw 0x805d600006ddc006 0x300bac0000dbb800 0x111c70000fffe007 0x82238e0001fffc00

def z360 : W := mkw 0x0000020480000001 0x0000004090000000 0xc0000f07c0000000 0x580001e0f8000000

def z361 : W := mkw 0x805d600004d4c006 0x300bac00009a9800 0x371f700008fee006 0x86e3ee00011fdc00

def z362 : W := mkw 0x0054049000000000 0x000a809200000000 0x8864071800000000 0x110c80e300000000

def z363 : W := mkw 0x60f6bfbcddb01e03 0xec1ed7f79bb603c0 0xdffcbff8cff01f03 0xbbff97ff19fe03e0

def z364 : W := mkw 0x00f6b69cd0000003 0xc01ed6d39a000000 0xdefcbff8c0000000 0x3bdf97ff18000000

def z365 : W := mkw 0x50000b05890218c1 0x0a000160b1204318 0xe6030f07c80e18e4 0xdcc061e0f901c31c

def z366 : W := mkw 0x0000000000000000 0x0000000000000000 0x5200000000001402 0xaa40000000000280

def z367 : W := mkw 0x0000010003090840 0x0000002000612108 0x0000000007010861 0x0000000000e0210c

def z368 : W := mkw 0x008014da70000000 0xc010029b4e000000 0x008000f830000000 0x2010001f06000000

def z369 : W := mkw 0x0400000000002128 0x0080000000000425 0x720040003011ffff 0xee40080006023fff

def z370 : W := mkw 0xd07feb058fdfd8c7 0x3a0ffd60b1fbfb18 0x3f7fff070fffe007 0x87efffe0e1fffc00

def z371 : W := mkw 0xf82bc8632a6f9494 0x1f05790c654df292 0x7ffbc8e73fef949f 0xefff791ce7fdf293

def z372 : W := mkw 0x54001b0dd90239e9 0x8a800361bb20473d 0xfa04ff1ff011ffff 0xff409fe3fe023fff

def z373 : W := mkw 0x5000080108021080 0x0a00010021004210 0x4000080700001080 0x48000100e0000210

def z374 : W := mkw 0x00f6b69cd0000003 0xc01ed6d39a000000 0xfa64f718f0000000 0x7f4c9ee31e000000

def z375 : W := mkw 0x04dd74da7000212e 0xc09bae9b4e000425 0xfa9cf0f8f011ffff 0xff539e1f1e023fff

def z376 : W := mkw 0xf82be8632a6fd496 0x1f057d0c654dfa92 0x779bf8e738eff49e 0xeef37f1ce71dfe93

def z377 : W := mkw 0x50228b05890218c1 0x0a045160b1204318 0xee638f07c00018e0 0x5dcc71e0f800031c

def z378 : W := mkw 0x0022830483090841 0x0004506090612108 0xea608700c70118e5 0xdd4c10e018e0231c

def z379 : W := mkw 0x0400100850002128 0x808002010a000425 0x3a04f0183011e71f 0xa7409e0306023ce3

def z380 : W := mkw 0x0054049004900000 0x200a809200920000 0xdffc0ff80ff00003 0xbbff81ff01fe0000

def z381 : W := mkw 0x605d4df22db01e04 0x2c0ba9be45b603c0 0xffff4fff3ff01f03 0xffffe9ffe7fe03e0

def z382 : W := mkw 0x80ffe6d6a6ddc007 0x701ffcdad4dbb800 0x05fb0fe70fee0000 0x00bf61fce1fdc000

def z383 : W := mkw 0x40ffffdef9001807 0xc81ffffbdf200300 0xfeffffffff001801 0xffdfffffffe00300

def z384 : W := mkw 0x245414b854b02728 0xa48a82970a9604e5 0xfb9cf0f8f0f1ffff 0xff739e1f1e1e3fff

def z385 : W := mkw 0x802bc000024d8004 0x100578000049b000 0x3f7bc0000fef8007 0x87ef780001fdf000

def z386 : W := mkw 0x50ffefd7ab0b18c7 0x4a1ffdfaf5616318 0xeefb8fe7cf0f18e5 0xdddf71fcf9e1e31c

def z387 : W := mkw 0x80fff24ef6ddc007 0xf01ffe49dedbb800 0x3f7ff007ffffe007 0xc7effe00fffffc00

def z388 : W := mkw 0x00f6b79cd5900a03 0xe01ed6f39ab20140 0x8864b718c7100b01 0x110c96e318e20160

def z389 : W := mkw 0xf809482108669494 0x1f012904210cd292 0x371b400008ee949e 0x86e36800011dd293

def z390 : W := mkw 0x54229b0ddb0b39e9 0x8a845361bb61673d 0xee63ff07ff0ff8fd 0xddcc7fe0ffe1ff1f

def z391 : W := mkw 0x00abf24ef0000007 0xc0157e49de000000 0xfa07f01ff0000000 0x7f40fe03fe000000

def z392 : W := mkw 0x64fffffefdb03f2f 0xec9fffffdfb607e5 0xfffffffffff1ffff 0xfffffffffffe3fff

def z393 : W := mkw 0x00f6a69480000003 0x401ed4d290000000 0x0060070000000000 0x000c00e000000000

def z394 : W := mkw 0x0400000000002128 0x0080000000000425 0x0000000000116b61 0x0000000000022d6c

def z395 : W := mkw 0x0076a00006994002 0x200ed40000d32800 0x0060000007000000 0x000c000000e00000

def z396 : W := mkw 0x907fe20586dfc0c7 0x320ffc40b0dbf818 0x3f7ff007cfffe0e7 0xc7effe00f9fffc1c

def z397 : W := mkw 0x0422900852092128 0x808452010a412425 0xfe67f018ff1fffff 0xffccfe031fe3ffff

def z398 : W := mkw 0x8009400000448004 0x1001280000089000 0x1118400000e08002 0x02230800001c1000

def z399 : W := mkw 0x50228b058b0b18c1 0x0a045160b1616318 0xe0038f07c00f18e4 0x5c0071e0f801e31c

def z400 : W := mkw 0x008956def0000005 0xc0112adbde000000 0xf69b4ffff0000000 0x7ed369fffe000000

def z401 : W := mkw 0x0000000000000000 0x0000000000000000 0x1004001800100702 0x22008003000200e0

def z402 : W := mkw 0x04abf24ef000212f 0xc0957e49de000425 0x2003f007f001e0fc 0x44007e00fe003c1f

def z403 : W := mkw 0x00abf6def0000007 0xc0157edbde000000 0xe083fffff0000000 0x7c107ffffe000000

def z404 : W := mkw 0x0000000000000000 0x0000000000000000 0xc000001800001f00 0x38000003000003e0

def z405 : W := mkw 0x00f6b79cd3090843 0xc01ed6f39a612108 0x8864b718c7010861 0x110c96e318e0210c

def z406 : W := mkw 0x8400000006dde128 0x3080000000dbbc25 0x010000000fffffff 0x8020000001ffffff

def z407 : W := mkw 0xe00009200ffdde00 0x3c00012401ffbbc0 0x010000000fffff07 0x8020000001ffffe0

def z408 : W := mkw 0x80fff6def0448007 0xd01ffedbde089000 0xfffffffff8ee8006 0xffffffffff1dd000

def z409 : W := mkw 0x0400000000002128 0x0080000000000425 0x000000000010e71a 0x0000000000021ce3

def z410 : W := mkw 0x10228205820b00c1 0x02045040b0416018 0xee638f07c00f00e4 0x5dcc71e0f801e01c

def z411 : W := mkw 0x0076a00006994002 0x200ed40000d32800 0x2e67b0000f1f6005 0x85ccf60001e3ec00

def z412 : W := mkw 0x00abe246a0000007 0x40157c48d4000000 0x0003000700000000 0x00006000e0000000

def z413 : W := mkw 0xf85d4df32df69e94 0x3f0ba9be65bed3d2 0xdfff0fff0ffe1f03 0xbbffe1ffe1ffc3e0

def z414 : W := mkw 0x0400100850002128 0x808002010a000425 0xea04b018c0117be5 0xdd40960318022f7c

def z415 : W := mkw 0x7c00186b782235b8 0x8f80030d6f0446b7 0xfa84f8fff011ffff 0xff509f1ffe023fff

def z416 : W := mkw 0x0000000000000000 0x0000000000000000 0x6603080700000000 0x4cc06100e0000000

def z417 : W := mkw 0x60000db00db01e00 0x2c0001b601b603c0 0xc1800ff80ff01f03 0xb83001ff01fe03e0

def z418 : W := mkw 0x80fff69cd6ddc007 0xf01ffed39adbb800 0xbf7ff718cfffe007 0x97effee319fffc00

def z419 : W := mkw 0xfc0018295866b5b8 0x9f8003052b0cd6b7 0xfb04f018f8ffffff 0xff609e031f1fffff

def z420 : W := mkw 0xf8228b258b6f9cd1 0x1f045164b16df39a 0xef638f07cfef9cff 0xddec71e0f9fdf39f

def z421 : W := mkw 0x00dd74da70000006 0xc01bae9b4e000000 0xfa9cf0f8f0000000 0x7f539e1f1e000000

def z422 : W := mkw 0x00fff6def0000007 0xc01ffedbde000000 0x8cffbfffc0000000 0x119ff7fff8000000

def z423 : W := mkw 0x807fe00006ddc006 0x300ffc0000dbb800 0x377b40000fee8006 0x86ef680001fdd000

def z424 : W := mkw 0x007fe00000000006 0x000ffc0000000000 0x047b000000000000 0x008f600000000000

def z425 : W := mkw 0x8054000006ddc000 0x300a800000dbb800 0x1f7c00000fffe007 0x83ef800001fffc00

def z426 : W := mkw 0x78801efff8221491 0xcf1003dfff044292 0xc0800ffff0001498 0x781001fffe000293

def z427 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000101f03 0x80000000000203e0

def z428 : W := mkw 0x00fff6def0000007 0xc01ffedbde000000 0xc4fb0ffff0000000 0x789f61fffe000000

def z429 : W := mkw 0xf809496329669c94 0x1f01292c652cd392 0xfffb4fe73fee9c9f 0xffff69fce7fdd393

def z430 : W := mkw 0x60fffffef9201e07 0xcc1fffffdf2403c0 0xfefffffff0001f00 0x7fdffffffe0003e0

def z431 : W := mkw 0x60768fb48db01e01 0x2c0ed1f691b603c0 0xffff8fffcff01f03 0xfffff1fff9fe03e0

def z432 : W := mkw 0xa85d44f224f48614 0x350ba89e449e90c2 0x119c40f830f0871a 0x2233881f061e10e3

def z433 : W := mkw 0x0422920cd0002129 0x808452419a000425 0xfe67ff1ff011ffff 0xffccffe3fe023fff

def z434 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000000000949e 0x8000000000001293

def z435 : W := mkw 0x80000000024dc000 0x100000000049b800 0x00000000000fe004 0x000000000001fc00

def z436 : W := mkw 0x6000082008201400 0x0c00010401040280 0x779848e038e0949e 0xeef3091c071c1293

def z437 : W := mkw 0x2000002004b00600 0x24000004009600c0 0x0100000000f00702 0x00200000001e00e0

def z438 : W := mkw 0x802be00006ddc006 0x30057c0000dbb800 0x2103f0000fffe007 0x84207e0001fffc00

def z439 : W := mkw 0x0400100850002128 0x808002010a000425 0x000070003000e018 0x00000e0006001c03

def z440 : W := mkw 0xa05d64b004f4c606 0x340bac96009e98c0 0x119c70f800f0e702 0x22338e1f001e1ce0

def z441 : W := mkw 0x50ffefd7ab0b18c7 0x4a1ffdfaf5616318 0x04fb0fe70f0e0000 0x009f61fce1e1c000

def z442 : W := mkw 0xa809406220648414 0x1501280c440c9082 0x779b48e730e0841a 0x6ef3691ce61c1083

def z443 : W := mkw 0x7800086328221490 0x0f00010c65044292 0x668308e7380e149c 0xecd0611ce701c293

def z444 : W := mkw 0x802be000024dc006 0x10057c000049b800 0x371bf00008efe006 0x86e37e00011dfc00

def z445 : W := mkw 0x00a2b20cd0000003 0xc01456419a000000 0x0000b000c0000000 0x0000160018000000

def z446 : W := mkw 0x0022830483090841 0x0004506090612108 0xee638f07c7010861 0x5dcc71e0f8e0210c

def z447 : W := mkw 0x847ff00856dde12e 0xb08ffe010adbbc25 0x3f7ff000ffffe0ff 0xc7effe001ffffc1f

def z448 : W := mkw 0xac09506a7064a53c 0x95812a0d4e0c94a7 0x119c70f830f0e71a 0x22338e1f061e1ce3

def z449 : W := mkw 0xf809586b78669494 0x9f012b0d6f0cd292 0xff9ff8fff8ee949e 0xfff3ff1fff1dd293

def z450 : W := mkw 0x0400100850002128 0x808002010a000425 0x720470183010f79e 0xee408e0306021ef3

def z451 : W := mkw 0xe07fedb00ffdde06 0x3c0ffdb601ffbbc0 0xdfff0ff80ffe1f03 0xbbffe1ff01ffc3e0

def z452 : W := mkw 0x50228b058b0b18c1 0x0a045160b1616318 0x66630f070f0e1084 0xcccc61e0e1e1c210

def z453 : W := mkw 0xf809486328669494 0x1f01290c650cd292 0x259b48e738ee809c 0x44b3691ce71dd013

def z454 : W := mkw 0x0000000000000000 0x0000000000000000 0x26030000080e0004 0x84c060000101c000

def z455 : W := mkw 0x50229b0ddb0b18c1 0x8a045361bb616318 0xfe67ff1fff0f18e5 0xffccffe3ffe1e31c

def z456 : W := mkw 0x0009404220000004 0x0001280844000000 0x769b48e73000949e 0xeed3691ce6001293

def z457 : W := mkw 0x50000b058b0b18c1 0x0a000160b1616318 0xc0000f07cf0f18e5 0xd80001e0f9e1e31c

def z458 : W := mkw 0x0422930cd3092969 0x808452619a61252d 0x8864b718c7116b61 0x110c96e318e22d6c

def z459 : W := mkw 0x500009010b0b18c0 0x0a00012021616318 0x000000000f0e0000 0x0000000001e1c000

def z460 : W := mkw 0x60ffeff6adb01e07 0x6c1ffdfed5b603c0 0x05fb0fe70fe00000 0x00bf61fce1fc0000

def z461 : W := mkw 0xa809406220648414 0x1501280c440c9082 0x739840e030e0949e 0xee73081c061c1293

def z462 : W := mkw 0x60540db00db01e00 0x2c0a81b601b603c0 0x119c00f80ff01f03 0xa233801f01fe03e0

def z463 : W := mkw 0xd07fe9010fdfd8c6 0x3a0ffd2021fbfb18 0x3f7ff0000ffff8e7 0x87effe0001ffff1c

def z464 : W := mkw 0x0000000000000000 0x0000000000000000 0x2000f0000001e004 0x04001e0000003c00

def z465 : W := mkw 0x7800082108221490 0x0f00010421044292 0x0000000000001498 0x0000000000000293

def z466 : W := mkw 0x00fff6def0000007 0xc01ffedbde000000 0x98fcf7f8f0000000 0x331f9eff1e000000

def z467 : W := mkw 0x50000901090218c0 0x0a00012021204318 0x00000000000018e0 0x000000000000031c

def z468 : W := mkw 0x0054059005900a00 0x200a80b200b20140 0x0060070007000000 0x000c00e000e00000

def z469 : W := mkw 0x50228b058b0b18c1 0x0a045160b1616318 0x04630f070f0f18e5 0x808c61e0e1e1e31c

def z470 : W := mkw 0x8809404220448014 0x1101280844089002 0x0000400030008018 0x0000080006001003

def z471 : W := mkw 0x0400100850002128 0x808002010a000425 0x0004301800106300 0x0000860300020c60

def z472 : W := mkw 0x0022800002090000 0x0004500000412000 0x0860800007010001 0x010c100000e02000

def z473 : W := mkw 0xa07fe4b006fdc606 0x340ffc9600dfb8c0 0x3ffff0f80fffe707 0xa7fffe1f01fffce0

def z474 : W := mkw 0x4000090009001800 0x0800012001200300 0xde640f180f101f03 0xbbcc81e301e203e0

def z475 : W := mkw 0x70540fb58db21ec1 0x2e0a81f6b1b643d8 0xdffc0fffcff01fe3 0xfbff81fff9fe03fc

def z476 : W := mkw 0x0076a00000000002 0x000ed40000000000 0x0864b00000000000 0x010c960000000000

def z477 : W := mkw 0x70228fb58b2b1ec1 0x0e0451f6b16563d8 0xeee38fffcf0f1fe5 0xfddc71fff9e1e3fc

def z478 : W := mkw 0x50228b058b0b18c1 0x0a045160b1616318 0x20038007cf0f18e5 0xc4007000f9e1e31c

def z479 : W := mkw 0x807fe00000448006 0x100ffc0000089000 0x3f7ff00008ee8006 0x87effe00011dd000

def z480 : W := mkw 0x007fe49000000006 0x000ffc9200000000 0xfefffff800000000 0x3fdfffff00000000

def z481 : W := mkw 0x40228b048b091841 0x0804516091612308 0xce608f00cf011861 0x99cc11e019e0230c

def z482 : W := mkw 0x847ff00856dde12e 0xb08ffe010adbbc25 0x3f7ff0183fffe71f 0xa7effe0307fffce3

def z483 : W := mkw 0xfc09586b7866b5bc 0x9f812b0d6f0cd6b7 0x779f78ff38fef79e 0xeef3ef1fe71fdef3

def z484 : W := mkw 0x50000b05890218c1 0x0a000160b1204318 0x00000f0700000000 0x000001e0e0000000

def z485 : W := mkw 0x802be000024dc006 0x10057c000049b800 0x00030000000e0000 0x000060000001c000

def z486 : W := mkw 0x60540db00db01e00 0x2c0a81b601b603c0 0xfffc4ff83ff09f9f 0xffff89ff07fe13f3

def z487 : W := mkw 0x04abf24ef000212f 0xc0957e49de000425 0xfa07f01ff011ffff 0xff40fe03fe023fff

def z488 : W := mkw 0x0454159855902b28 0xa08a82b30ab20565 0x8864b718c7116b61 0x110c96e318e22d6c

def z489 : W := mkw 0x70000fb589221ec1 0x0e0001f6b12443d8 0xc0800fffc0001fe0 0x781001fff80003fc

def z490 : W := mkw 0xd00009010fdfd8c0 0x3a00012021fbfb18 0x010000000ffff8e7 0x8020000001ffff1c

def z491 : W := mkw 0xd47ffb0ddfdff9ef 0xba8fff61bbfbff3d 0xff7fff1fffffffff 0xffefffe3ffffffff

def z492 : W := mkw 0x5000080108021080 0x0a00010021004210 0xee038807c80f18e5 0xddc07100f901e31c

def z493 : W := mkw 0x0400100850002128 0x808002010a000425 0xda0470183010ff1b 0xbb408e0306021fe3

def z494 : W := mkw 0x10228205820b00c1 0x02045040b0416018 0x2e638007cf0f00e5 0xc5cc7000f9e1e01c

def z495 : W := mkw 0x00fff69cd0000007 0xc01ffed39a000000 0xbe7ff718c0000000 0x17cffee318000000

def z496 : W := mkw 0x0000100850000000 0x800002010a000000 0xfa04f018f00118e5 0xff409e031e00231c

def z497 : W := mkw 0x640009200db03f28 0x2c80012401b607e5 0x010000000ff1ffff 0x8020000001fe3fff

def z498 : W := mkw 0x50801fdff90218c1 0xca1003fbff204318 0xc0800ffff00018e0 0x781001fffe00031c

def z499 : W := mkw 0x0400100850002128 0x808002010a000425 0x8804b018c011ffff 0x9100960318023fff

def z500 : W := mkw 0x0054049004900200 0x200a809200920040 0x0004001800100300 0x0000800300020060

def z501 : W := mkw 0x605409200db01e00 0x2c0a812401b603c0 0x1f7c00000ff01f03 0x83ef800001fe03e0

def z502 : W := mkw 0x50f6bf9ddb0b18c3 0xca1ed7f3bb616318 0xee67bf1fcf0f18e5 0xddccf7e3f9e1e31c

def z503 : W := mkw 0xf809486328669494 0x1f01290c650cd292 0x459b08e738ee1498 0x68b3611ce71dc293

def z504 : W := mkw 0x0022a00002094002 0x0004540000412800 0x0000b00000016000 0x0000160000002c00

def z505 : W := mkw 0x80dd74da74d4c006 0xf01bae9b4e9a9800 0x119c70f830f0e002 0x22338e1f061e1c00

def z506 : W := mkw 0x4000090009001800 0x0800012001200300 0xc0000f0000001800 0x180001e000000300

def z507 : W := mkw 0xf87fe8632effd496 0x3f0ffd0c65dffa92 0x3ffff8e70fffe007 0x87ffff1ce1fffc00

def z508 : W := mkw 0x0400100850002128 0x808002010a000425 0xfa04f018f0001ff8 0x7f409e031e0003ff

def z509 : W := mkw 0xfc0008210866b5b8 0x1f800104210cd6b7 0x0100000008ffffff 0x80200000011fffff

def z510 : W := mkw 0x2800006220200410 0x0500000c44040082 0x008000e030000418 0x2010001c06000083

def z511 : W := mkw 0x6076adb00fb95e02 0x2c0ed5b601f72bc0 0xdffcbff80ff17f03 0xbbff97ff01fe2fe0

def z512 : W := mkw 0x0009404220000004 0x0001280844000000 0x2003400730000000 0x44006800e6000000

def z513 : W := mkw 0x50228a0588021081 0x0a045140b1004210 0xee638f07c80e1084 0xddcc71e0f901c210

def z514 : W := mkw 0xf87fe8632effd496 0x3f0ffd0c65dffa92 0x77fb48e73fee949e 0xeeff691ce7fdd293

def z515 : W := mkw 0x00abf24ef0000007 0xc0157e49de000000 0x769bf8e7f0000000 0x6ed37f1cfe000000

def z516 : W := mkw 0x0400100850002128 0x808002010a000425 0x100470183011ffff 0xa2008e0306023fff

def z517 : W := mkw 0x9c09504b7046a1bc 0x93812a096e08d437 0x2003f007f00fe0fc 0x44007e00fe01fc1f

def z518 : W := mkw 0x600009200db01e00 0x2c00012401b603c0 0x579808e00ff01f03 0xaaf3011c01fe03e0

def z519 : W := mkw 0xf82bca67aa6f94d5 0x1f05794cf54df29a 0x779bc8e7f8ef94fe 0xeef3791cff1df29f

def z520 : W := mkw 0x807fe30487ddc847 0x300ffc6090fbb908 0xbf7ff700cfffe867 0x97effee019fffd0c

def z521 : W := mkw 0x60801ffef9201e01 0xcc1003ffdf2403c0 0xc0800ffff0001f00 0x781001fffe0003e0

def z522 : W := mkw 0x64541db85db03f28 0xac8a83b70bb607e5 0xdffc0ff8fff01ffb 0xfbff81ff1ffe03ff

def z523 : W := mkw 0xd07feb058fdfd8c7 0x3a0ffd60b1fbfb18 0xef7b8f07cfef18e5 0xddef71e0f9fde31c

def z524 : W := mkw 0x0400000000002128 0x0080000000000425 0x000000000001e0fc 0x0000000000003c1f

def z525 : W := mkw 0x402289000b091800 0x0804512001612300 0xee638f000f0f1805 0x9dcc71e001e1e300

def z526 : W := mkw 0x60540cb00cb01600 0x2c0a8196019602c0 0x579c08f808f01702 0xaaf3811f011e02e0

def z527 : W := mkw 0x048016def0002129 0xc09002dbde000425 0xfa84fffff011ffff 0xff509ffffe023fff

def z528 : W := mkw 0x0000000000000000 0x0000000000000000 0x88008000c0010861 0x110010001800210c

def z529 : W := mkw 0xf85d48632cf69494 0x3f0ba90c659ed292 0x7fff48e73ffe949f 0xefffe91ce7ffd293

def z530 : W := mkw 0x40540d9009001800 0x080a81b201200300 0xdefc0ff80f001801 0xbbdf81ff01e00300

def z531 : W := mkw 0x80fff4da76ddc006 0xf01ffe9b4edbb800 0x3ffff0f83fffe007 0xa7fffe1f07fffc00

def z532 : W := mkw 0x98abf24ff0468097 0xd3157e49fe08d012 0x2003f007f00e809c 0x44007e00fe01d013

def z533 : W := mkw 0x64001db859203f28 0x8c8003b70b2407e5 0xc0800ff8f0001ff8 0x781001ff1e0003ff

def z534 : W := mkw 0xf85d68632cf6d496 0x3f0bad0c659eda92 0x779f78e738fef49e 0xeef3ef1ce71fde93

def z535 : W := mkw 0x04dd74da7000212e 0xc09bae9b4e000425 0x109c70f83010e71a 0x22138e1f06021ce3

def z536 : W := mkw 0x007fe04220000006 0x000ffc0844000000 0x7efff8e730000000 0x6fdfff1ce6000000

def z537 : W := mkw 0x0022800002090000 0x0004500000412000 0xee638000cf0f18e5 0xddcc700019e1e31c

def z538 : W := mkw 0x807fe00006ddc006 0x300ffc0000dbb800 0x057b00000fffe007 0x80af600001fffc00

def z539 : W := mkw 0x64540db00db03f28 0x2c8a81b601b607e5 0xdffc0ff80ff1ffff 0xbbff81ff01fe3fff

def z540 : W := mkw 0x00d4349850000002 0xc01a86930a000000 0x0004301800000000 0x0000860300000000

def z541 : W := mkw 0xf800082108669490 0x1f000104210cd292 0x579808e008ee949e 0xaaf3011c011dd293

def z542 : W := mkw 0x002be00000000006 0x00057c0000000000 0x2003f00000000000 0x04007e0000000000

def z543 : W := mkw 0x205404b004b00600 0x240a8096009600c0 0xdffc0ff800f00702 0x3bff81ff001e00e0

def z544 : W := mkw 0x80abf24ef24dc007 0xd0157e49de49b800 0x2003f007f00fe004 0x44007e00fe01fc00

def z545 : W := mkw 0x982bc247a24f80d5 0x13057848f449f01a 0x2003c007f00f80fc 0x44007800fe01f01f

def z546 : W := mkw 0x00fff24ef0000007 0xc01ffe49de000000 0x3e7ff007f0000000 0x47cffe00fe000000

def z547 : W := mkw 0x0400100850002128 0x808002010a000425 0xa804f018f011ebfd 0x55009e031e023d7f

def z548 : W := mkw 0x78228b67ab2b1cd1 0x0f04516cf565639a 0xeee38fe7ff0f1cfd 0xfddc71fcffe1e39f

def z549 : W := mkw 0x50768f958b0b18c1 0x0a0ed1f2b1616318 0xfeff8fffcf0f18e5 0xffdff1fff9e1e31c

def z550 : W := mkw 0x0022830483090841 0x0004506090612108 0x0060070007000000 0x000c00e000e00000

def z551 : W := mkw 0x1800004320020090 0x0300000864004012 0x0000000730000098 0x40000000e6000013

def z552 : W := mkw 0x50768f958f9b1ac1 0x2a0ed1f2b1f36358 0xee678f1fcf1f1be5 0xddccf1e3f9e3e37c

def z553 : W := mkw 0x807fe00004d4c006 0x300ffc00009a9800 0x3f7ff00000f0e002 0x07effe00001e1c00

def z554 : W := mkw 0x50abfb4ffb0b18c7 0xca157f69ff616318 0xee63ff07ff0f18e5 0xddcc7fe0ffe1e31c

def z555 : W := mkw 0x807fe00006ddc006 0x300ffc0000dbb800 0x197cf00007f1e003 0x032f9e0000fe3c00

def z556 : W := mkw 0x50228b058b0b18c1 0x0a045160b1616318 0xee638f07cf0e0000 0x5dcc71e0f9e1c000

def z557 : W := mkw 0x902be205824fc0c7 0x12057c40b049f818 0x2003f007c00fe0e4 0x44007e00f801fc1c

def z558 : W := mkw 0x845d700854d4e12e 0xb08bae010a9a9c25 0xfb1cf018f0f1ffff 0xff639e031e1e3fff

def z559 : W := mkw 0x0000000000000000 0x0000000000000000 0xce600f0000000000 0x19cc01e000000000

def z560 : W := mkw 0xf80949632df69e94 0x3f01292c65bed3d2 0x779b48e73ffe9f9f 0xeef3691ce7ffd3f3

def z561 : W := mkw 0x0076800006990000 0x200ed00000d32000 0x3f7f80000fff0007 0x87eff00001ffe000

def z562 : W := mkw 0x0022820482090041 0x0004504090412008 0x00008000c0010060 0x000010001800200c

def z563 : W := mkw 0x0000000004900000 0x2000000000920000 0x010000000ff00003 0x8020000001fe0000

def z564 : W := mkw 0x70768fb58fbb1ec1 0x2e0ed1f6b1f763d8 0x05fb0fe70fee0000 0x00bf61fce1fdc000

def z565 : W := mkw 0x502288010a0b1080 0x0a04510021416210 0x6e6388070f0f1085 0xcdcc7100e1e1e210

def z566 : W := mkw 0x60540db00db01e00 0x2c0a81b601b603c0 0x57f80fe00fe01402 0xaaff01fc01fc0280

def z567 : W := mkw 0xd07feb058fdfd8c7 0x3a0ffd60b1fbfb18 0x057b0f070fee0000 0x00af61e0e1fdc000

def z568 : W := mkw 0x1422920dd20b21e9 0x82845241ba41643d 0x2003f007f00fe0fc 0x44007e00fe01fc1f

def z569 : W := mkw 0x10fff6dff20b00c7 0xc21ffedbfe416018 0xfefffffff00f00e4 0x7fdffffffe01e01c

def z570 : W := mkw 0x50228b058b0b18c1 0x0a045160b1616318 0x8c638f07cf0f0861 0x118c71e0f9e1e10c

def z571 : W := mkw 0xf82bcb67ab6f9cd5 0x1f05796cf56df39a 0xeffb8fe7cfef18e5 0xddff71fcf9fde31c

def z572 : W := mkw 0xf85d4df32df69e94 0x3f0ba9be65bed3d2 0x77fb4fe73fee949e 0xeeff69fce7fdd293

def z573 : W := mkw 0x4000090009001800 0x0800012001200300 0x000000000f001801 0x8000000001e00300

def z574 : W := mkw 0x8000000000448000 0x1000000000089000 0x0100000008ee8006 0x80200000011dd000

def z575 : W := mkw 0x6000082008201400 0x0c00010401040280 0xdf9c08f808f01f03 0xbbf3811f011e03e0

def z576 : W := mkw 0x0054059005900a00 0x200a80b200b20140 0xdefc0ff807100b01 0x3bdf81ff00e20160

def z577 : W := mkw 0x840950085044a12c 0x90812a010a089425 0xff1ff018f8ffffff 0xffe3fe031f1fffff

def z578 : W := mkw 0x0400000000002128 0x0080000000000425 0xda0400180011ffff 0xbb40800300023fff

def z579 : W := mkw 0x9809404320468094 0x130128086408d012 0x769b48e7300e809c 0x6ed3691ce601d013

def z580 : W := mkw 0x5076ab058f9b58c3 0x2a0ed560b1f36b18 0xee67bf07cf1f78e5 0xddccf7e0f9e3ef1c

def z581 : W := mkw 0x500009010b0b18c0 0x0a00012021616318 0x660308070f0f18e5 0xccc06100e1e1e31c

def z582 : W := mkw 0x0400100850002128 0x808002010a000425 0x7200f000f001f4fe 0xee401e001e003e9f

def z583 : W := mkw 0x0076a30487994843 0x200ed46090f32908 0x8864b700c7116861 0x110c96e018e22d0c

def z584 : W := mkw 0xe07fe8200efdd406 0x3c0ffd0401dfba80 0x7ffff8e00ffff407 0xafffff1c01fffe80

def z585 : W := mkw 0x0054049000000000 0x000a809200000000 0x109c00f800000000 0x2213801f00000000

def z586 : W := mkw 0xf809486328669494 0x1f01290c650cd292 0x608348e7300e949c 0x6c10691ce601d293

def z587 : W := mkw 0xf800082108669490 0x1f000104210cd292 0x6703080708ee949e 0xcce06100e11dd293

def z588 : W := mkw 0x5000080108021080 0x0a00010021004210 0x76034807380e949e 0xeec06900e701d293

def z589 : W := mkw 0x60000db009201e00 0x0c0001b6012403c0 0xd7980ff808e01f02 0xbaf301ff011c03e0

def z590 : W := mkw 0x10228205820b00c1 0x02045040b0416018 0xea038007c00f18e5 0xdd407000f801e31c

def z591 : W := mkw 0x6400182858203528 0x8c8003050b0406a5 0xff9cf8f8f8f1ffff 0xfff39f1f1f1e3fff

def z592 : W := mkw 0x9809404320468094 0x130128086408d012 0x00030007000e0000 0x00006000e001c000

def z593 : W := mkw 0xf82bcb67ab6f9cd5 0x1f05796cf56df39a 0x05fb0fe70fee0000 0x00bf61fce1fdc000

def z594 : W := mkw 0xf87fe8210effd496 0x3f0ffd0421dffa92 0x3f7ff0000ffff49f 0x87effe0001fffe93

def z595 : W := mkw 0x842bf008524de12e 0x90857e010a49bc25 0x2003f000f00fe0fc 0x44007e001e01fc1f

def z596 : W := mkw 0x845d700854d4e12e 0xb08bae010a9a9c25 0x111c701830f0e71a 0x22238e03061e1ce3

def z597 : W := mkw 0x50228a058a0b10c1 0x0a045140b1416218 0x66038807c80f10e4 0xccc07100f901e21c

def z598 : W := mkw 0xfc2bdb6ffb6fbdfd 0x9f857b6dff6df7bf 0xffffffffffffffff 0xffffffffffffffff

def z599 : W := mkw 0x0400100850002128 0x808002010a000425 0x0000b000c0016060 0x0000160018002c0c

def z600 : W := mkw 0x842bf008524de12e 0x90857e010a49bc25 0xfa07f018f01fffff 0xff40fe031e03ffff

def z601 : W := mkw 0x10abf24ff20b00c7 0xc2157e49fe416018 0x2003f007f00f00e4 0x44007e00fe01e01c

def z602 : W := mkw 0x00f6b69cd0000003 0xc01ed6d39a000000 0xee67bf1fc0000000 0x5dccf7e3f8000000

def z603 : W := mkw 0x60000db009201e00 0x0c0001b6012403c0 0xcee00ff80f001f01 0xb9dc01ff01e003e0

def z604 : W := mkw 0x00dd74da70000006 0xc01bae9b4e000000 0x769f78ff30000000 0x6ed3ef1fe6000000

def z605 : W := mkw 0xf809486328669494 0x1f01290c650cd292 0x059b08e708ee949e 0x80b3611ce11dd293

def z606 : W := mkw 0xfc09586b7866b5bc 0x9f812b0d6f0cd6b7 0xf79b48fff8ee9ffe 0xfef3691fff1dd3ff

def z607 : W := mkw 0x60000db009201e00 0x0c0001b6012403c0 0xda840ff800101f03 0xbb5081ff000203e0

def z608 : W := mkw 0x0000030481000841 0x0000006090200108 0x80000700c0000860 0x100000e01800010c

def z609 : W := mkw 0x0054000004900000 0x200a800000920000 0x3f7cf0000ff1e007 0x87ef9e0001fe3c00

def z610 : W := mkw 0x802be000024dc006 0x10057c000049b800 0x3a07f000001fe007 0x8740fe000003fc00

def z611 : W := mkw 0x205404b004b00600 0x240a8096009600c0 0x1ffc00f80ff00703 0xa3ff801f01fe00e0

def z612 : W := mkw 0xf8094b67a9669cd5 0x1f01296cf52cd39a 0xf79b4fe7f8ee9cfe 0xfef369fcff1dd39f

def z613 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000000011e007 0x8000000000023c00

def z614 : W := mkw 0xf8fffffffdf69e97 0xff1fffffffbed3d2 0xfffffffffffe9f9f 0xffffffffffffd3f3

def z615 : W := mkw 0x0022800002090000 0x0004500000412000 0x3e67f0000f1fe007 0x87ccfe0001e3fc00

def z616 : W := mkw 0x54229b0ddb0b39e9 0x8a845361bb61673d 0xee67bf1fcf1f7be5 0xddccf7e3f9e3ef7c

def z617 : W := mkw 0x805d600004d4c006 0x300bac00009a9800 0x1f7c70000ff0e003 0x83ef8e0001fe1c00

def z618 : W := mkw 0x5009484328021084 0x0a01290865004210 0x769b48e7380e1084 0xeed3691ce701c210

def z619 : W := mkw 0x802be000024dc006 0x10057c000049b800 0x2e63f0000f0fe005 0x85cc7e0001e1fc00

def z620 : W := mkw 0x60768db00fb91e00 0x2c0ed1b601f723c0 0xffff8ff80fff1f07 0xbffff1ff01ffe3e0

def z621 : W := mkw 0x0454100854902128 0xa08a82010a920425 0xff7cf018fff1ffff 0xffef9e031ffe3fff

def z622 : W := mkw 0x807ff00856ddc006 0xb00ffe010adbb800 0xff7ff018ffffe007 0xffeffe031ffffc00

def z623 : W := mkw 0xf809486328669494 0x1f01290c650cd292 0x119840e038ee949e 0xa233081c071dd293

def z624 : W := mkw 0x0476b0085699612a 0xa08ed6010ad32c25 0x8864b018c7116b61 0x110c960318e22d6c

def z625 : W := mkw 0x8009400000448004 0x1001280000089000 0x051b000008ee0000 0x00a36000011dc000

def z626 : W := mkw 0x807fe00006ddc006 0x300ffc0000dbb800 0x7f7ff0003ffff49f 0xefeffe0007fffe93

def z627 : W := mkw 0x800960000044c006 0x10012c0000089800 0x000070000000e000 0x00000e0000001c00

def z628 : W := mkw 0x8022800006ddc000 0x3004500000dbb800 0x2f6380000fffe007 0x85ec700001fffc00

def z629 : W := mkw 0x04f6b69cd000212b 0xc09ed6d39a000425 0xfa64f718f011ffff 0xff4c9ee31e023fff

def z630 : W := mkw 0x805d600004d4c006 0x300bac00009a9800 0x3b1cf00000f1e007 0x87639e00001e3c00

def z631 : W := mkw 0x54229b0ddb0b39e9 0x8a845361bb61673d 0xee638f1fff0f1ffd 0xfdcc71e3ffe1e3ff

def z632 : W := mkw 0x1422920dd20b21e9 0x82845241ba41643d 0xfa07f01ff01fffff 0xff40fe03fe03ffff

def z633 : W := mkw 0x0400100850002128 0x808002010a000425 0xc0000018f011ffff 0xf80000031e023fff

def z634 : W := mkw 0xa87fe06226fdc416 0x350ffc0c44dfb882 0x3ffff0e03fffe41f 0xa7fffe1c07fffc83

def z635 : W := mkw 0xf80008210effd490 0x3f00010421dffa92 0x010000000ffff49f 0x8020000001fffe93

def z636 : W := mkw 0x205404b004b00600 0x240a8096009600c0 0x019800e000e00000 0x0033001c001c0000

def z637 : W := mkw 0xfc7ff86b7efff5be 0xbf8fff0d6fdffeb7 0xfffff8ffffffffff 0xffffff1fffffffff

def z638 : W := mkw 0x0054059005900a00 0x200a80b200b20140 0x9f7c07180ff00b03 0x93ef80e301fe0160

def z639 : W := mkw 0x0000100850000000 0x800002010a000000 0x1004701830000000 0x22008e0306000000

def z640 : W := mkw 0x0400100850002128 0x808002010a000425 0xda04b018c0117f63 0xbb40960318022fec

def z641 : W := mkw 0xf87feb67afffdcd7 0x3f0ffd6cf5fffb9a 0xffffffe7fffffcff 0xfffffffcffffff9f

def z642 : W := mkw 0x7800086328221490 0x0f00010c65044292 0x579808e738e0149a 0xeaf3011ce71c0293

def z643 : W := mkw 0x0076a00006994002 0x200ed40000d32800 0x1f7cb0000ff16003 0x83ef960001fe2c00

def z644 : W := mkw 0x005d600000000006 0x000bac0000000000 0x101c700000000000 0x02038e0000000000

def z645 : W := mkw 0x50228b058b0b18c1 0x0a045160b1616318 0x2e638f070f0f0005 0x85cc71e0e1e1e000

def z646 : W := mkw 0xe009482008649404 0x1c012904010c9280 0x779b48e008ee9406 0xaef3691c011dd280

def z647 : W := mkw 0x0000000000000000 0x0000000000000000 0xda04001800000000 0x3b40800300000000

def z648 : W := mkw 0x807fe00006ddc006 0x300ffc0000dbb800 0x3f7ff0000fee0000 0x07effe0001fdc000

def z649 : W := mkw 0x00fff7def3090847 0xc01ffefbde612108 0xfefffffff7010861 0x7fdffffffee0210c

def z650 : W := mkw 0x6000082008201400 0x0c00010401040280 0x0100000008e01402 0x80200000011c0280

def z651 : W := mkw 0x9c09504b7046a1bc 0x93812a096e08d437 0xfa07f01ff01fffff 0xff40fe03fe03ffff

def z652 : W := mkw 0x0000000000000000 0x0000000000000000 0x0e6000000f000001 0x81cc000001e00000

def z653 : W := mkw 0x70540db10fbb1ec0 0x2e0a81b621f763d8 0xdffc0ff80fff1fe7 0xbbff81ff01ffe3fc

def z654 : W := mkw 0x40228b0489001801 0x0804516091200300 0xee638f07cf001801 0xddcc71e0f9e00300

def z655 : W := mkw 0xf8abfa6ff8669497 0xdf157f4dff0cd292 0x779bf8e7f8ee949e 0xeef37f1cff1dd293

def z656 : W := mkw 0x4000090009001800 0x0800012001200300 0xee608f00cf0118e5 0xddcc11e019e0231c

def z657 : W := mkw 0xe809486228649414 0x1d01290c450c9282 0x579848e038e0941a 0xaaf3091c071c1283

def z658 : W := mkw 0x0000000000000000 0x0000000000000000 0x1a04000000100003 0x8340800000020000

def z659 : W := mkw 0x0000010001000800 0x0000002000200100 0x8860070007000801 0x110c00e000e00100

def z660 : W := mkw 0x0422930cd3092969 0x808452619a61252d 0xfa64f718f711ffff 0xff4c9ee31ee23fff

def z661 : W := mkw 0x78540df32db21e90 0x2f0a81be65b643d2 0xdffc0fff3ff01f9b 0xfbff81ffe7fe03f3

def z662 : W := mkw 0x007ff00850000006 0x800ffe010a000000 0xfe7ff018f0000000 0x7fcffe031e000000

def z663 : W := mkw 0xd07fe8010edfd086 0x3a0ffd0021dbfa10 0x7f7ff8070ffff087 0xcfefff00e1fffe10

def z664 : W := mkw 0x0000100850000000 0x800002010a000000 0xfa04f018f0101f03 0xff409e031e0203e0

def z665 : W := mkw 0x0000000000000000 0x0000000000000000 0xca00000000001801 0x9940000000000300

def z666 : W := mkw 0xa8fff6fef0648417 0xd51ffedfde0c9082 0xfffffffff0e0841a 0x7ffffffffe1c1083

def z667 : W := mkw 0x0054000004900000 0x200a800000920000 0x0864000007100001 0x010c800000e20000

def z668 : W := mkw 0x047ff0085000212e 0x808ffe010a000425 0xfe7ff018f011ffff 0xffcffe031e023fff

def z669 : W := mkw 0x807fe59007ddca06 0x300ffcb200fbb940 0xbf7ff7180fffeb07 0x97effee301fffd60

def z670 : W := mkw 0x70768fb58fbb1ec1 0x2e0ed1f6b1f763d8 0xdfff0fff0ffe1f03 0xbbffe1ffe1ffc3e0

def z671 : W := mkw 0x0000000000000000 0x0000000000000000 0xfa00c000f0019cff 0xff4018001e00339f

def z672 : W := mkw 0x0000100850000000 0x800002010a000000 0x8804b018c0000000 0x1100960318000000

def z673 : W := mkw 0x8009400000448004 0x1001280000089000 0x771b400038ee949e 0xeee36800071dd293

def z674 : W := mkw 0x0000100850000000 0x800002010a000000 0xfa04f018f000949e 0xff409e031e001293

def z675 : W := mkw 0x00fff6def0000007 0xc01ffedbde000000 0xa867f71ff0000000 0x550cfee3fe000000

def z676 : W := mkw 0x0000000000000000 0x0000000000000000 0x1718000008e00002 0x82e30000011c0000

def z677 : W := mkw 0x4000080008001000 0x0800010001000200 0x4600080008001000 0x88c0010001000200

def z678 : W := mkw 0x70ffffffffbb1ec7 0xee1ffffffff763d8 0xffffffffffff1fe7 0xffffffffffffe3fc

def z679 : W := mkw 0x0022800000000000 0x0004500000000000 0x2e63800000000000 0x05cc700000000000

def z680 : W := mkw 0x6009486228201404 0x0c01290c45040280 0x779b48e738e01402 0xeef3691ce71c0280

def z681 : W := mkw 0xe0540db00ffdde00 0x3c0a81b601ffbbc0 0xdffc0ff80fffff07 0xbbff81ff01ffffe0

def z682 : W := mkw 0x245414b854b02728 0xa48a82970a9604e5 0x119c70f830f0e71a 0x22338e1f061e1ce3

def z683 : W := mkw 0x605408200cb01400 0x2c0a810401960280 0x5ffc08e00ff01403 0xabff811c01fe0280

def z684 : W := mkw 0x0000000006994000 0x2000000000d32800 0x0000000007116001 0x0000000000e22c00

def z685 : W := mkw 0x60540db00db01e00 0x2c0a81b601b603c0 0x896407180ff01f03 0x912c80e301fe03e0

def z686 : W := mkw 0x0022800002090000 0x0004500000412000 0x046300000f0e0000 0x008c600001e1c000

def z687 : W := mkw 0xf809486328669494 0x1f01290c650cd292 0x379b48e708ee8006 0x86f3691ce11dd000

def z688 : W := mkw 0xf8fffefff8669497 0xdf1fffdfff0cd292 0xfffffffff8ee0000 0x7fffffffff1dc000

def z689 : W := mkw 0x50768b058f9b18c1 0x2a0ed160b1f36318 0xff7f8f07cfff18e7 0xdfeff1e0f9ffe31c

def z690 : W := mkw 0x0000000000000000 0x0000000000000000 0x8804001800100b01 0x1100800300020160

def z691 : W := mkw 0x7c00186b782235b8 0x8f80030d6f0446b7 0xc08008fff0001ff8 0x7810011ffe0003ff

def z692 : W := mkw 0x0400100850002128 0x808002010a000425 0xfa04f018f0116b61 0x7f409e031e022d6c

def z693 : W := mkw 0x0054200004904002 0x200a840000920800 0x0004300000106000 0x0000860000020c00

def z694 : W := mkw 0x78000b67a9221cd1 0x0f00016cf524439a 0xc0800fe7f0001cf8 0x781001fcfe00039f

def z695 : W := mkw 0x0000000000000000 0x0000000000000000 0xfa04401830109f9f 0xff408803060213f3

def z696 : W := mkw 0x0022820480000001 0x0004504090000000 0x20038007c0000000 0x44007000f8000000

def z697 : W := mkw 0x0022920cd0000001 0x800452419a000000 0xfe67ff1ff0000000 0x7fccffe3fe000000

def z698 : W := mkw 0x500009010b0b18c0 0x0a00012021616318 0xce600f000f0f18e5 0x99cc01e001e1e31c

def z699 : W := mkw 0x50228b058b0b18c1 0x0a045160b1616318 0xce630f070f0e1801 0x99cc61e0e1e1c300

def z700 : W := mkw 0x0400100850002128 0x808002010a000425 0xfa04f018f010e71a 0x7f409e031e021ce3

def z701 : W := mkw 0x60540db00db01e00 0x2c0a81b601b603c0 0xdffc0ff80fe00000 0x3bff81ff01fc0000

def z702 : W := mkw 0xf809486328669494 0x1f01290c650cd292 0x779b48e738ee0000 0x6ef3691ce71dc000

def z703 : W := mkw 0x205404b004b00600 0x240a8096009600c0 0xdb9c00f800f01f03 0xbb73801f001e03e0

def z704 : W := mkw 0x0054000004900000 0x200a800000920000 0xdf7c00180ff01f03 0xbbef800301fe03e0

def z705 : W := mkw 0x4400190859003928 0x888003210b200725 0xfe64ff18ff11ffff 0xffcc9fe31fe23fff

def z706 : W := mkw 0xa809406220648414 0x1501280c440c9082 0x379b40e038ee841e 0xa6f3681c071dd083

def z707 : W := mkw 0x9809404320468094 0x130128086408d012 0x779b48e738ee809e 0xeef3691ce71dd013

def z708 : W := mkw 0x80fff6def6ddc007 0xf01ffedbdedbb800 0xffffffffffef0005 0xfffffffffffde000

def z709 : W := mkw 0x802bc000024d8004 0x100578000049b000 0x3f7ff0000fffe007 0x87effe0001fffc00

def z710 : W := mkw 0x00fff6def4904007 0xe01ffedbde920800 0xfefffffff0106000 0x7fdffffffe020c00

def z711 : W := mkw 0x0076969cd0000001 0x800ed2d39a000000 0xfefffffff0000000 0x7fdffffffe000000

def z712 : W := mkw 0x00a286d6a0000001 0x401450dad4000000 0xeee38fe7c0000000 0x5ddc71fcf8000000

def z713 : W := mkw 0x04fff6def000212f 0xc09ffedbde000425 0xfefffffff0117be5 0xffdffffffe022f7c

def z714 : W := mkw 0x50dd7ddb7b0b18c6 0xca1bafbb6f616318 0x109c70f83f0f18e5 0xa2138e1f07e1e31c

def z715 : W := mkw 0xf809496329669c94 0x1f01292c652cd392 0x77fb4fe73fee949e 0xeeff69fce7fdd293

def z716 : W := mkw 0x805d600006ddc006 0x300bac0000dbb800 0x371f70000fffe007 0x86e3ee0001fffc00

def z717 : W := mkw 0x847ff00856dde12e 0xb08ffe010adbbc25 0xc57b0018ffee1ff8 0x78af60031ffdc3ff

def z718 : W := mkw 0x04fff6def209212f 0xc09ffedbde412425 0xfeffffffff1fffff 0xffdfffffffe3ffff

def z719 : W := mkw 0x84fff6def044a12f 0xd09ffedbde089425 0xfffffffff8ffffff 0xffffffffff1fffff

def z720 : W := mkw 0x008976def0000007 0xc0112edbde000000 0xc0807ffff0000000 0x78100ffffe000000

def z721 : W := mkw 0x00fff6def0000007 0xc01ffedbde000000 0xfefffffff0019cff 0xffdffffffe00339f

def z722 : W := mkw 0x60540db00db01e00 0x2c0a81b601b603c0 0xfffc0ff80ff01f87 0xffff81ff01fe03f0

def z723 : W := mkw 0xfc09586b7866b5bc 0x9f812b0d6f0cd6b7 0x8d9fb8ffc8ff6b61 0x11b3f71ff91fed6c

def z724 : W := mkw 0x00f6a69486994003 0x601ed4d290d32800 0x0864b70007116001 0x010c96e000e22c00

def z725 : W := mkw 0x9c2bd24ff24fa1fd 0x93857a49fe49f43f 0x2003f007f00fe0fc 0x44007e00fe01fc1f

def z726 : W := mkw 0x0400100850002128 0x808002010a000425 0xfe07f81ff011ffff 0xffc0ff03fe023fff

def z727 : W := mkw 0x807fe00006ddc006 0x300ffc0000dbb800 0x057f30000ffe6000 0x00afe60001ffcc00

def z728 : W := mkw 0x00dd56def0000005 0xc01baadbde000000 0xfeff4ffff0000000 0x7fdfe9fffe000000

def z729 : W := mkw 0xf809486328669494 0x1f01290c650cd292 0x579b48e738ee941a 0xaaf3691ce71dd283

def z730 : W := mkw 0x60540db00db01e00 0x2c0a81b601b603c0 0xdffc0ff80ff00b01 0x3bff81ff01fe0160

def z731 : W := mkw 0x807fe00006ddc006 0x300ffc0000dbb800 0xff7ff018cfffffe7 0xffeffe0319fffffc

def z732 : W := mkw 0x0400100850002128 0x808002010a000425 0xfe9cf8f8f011ffff 0xffd39f1f1e023fff

def z733 : W := mkw 0x7800092109221e90 0x0f000124212443d2 0x0000000000001f98 0x00000000000003f3

def z734 : W := mkw 0x80fff6def6ddc007 0xf01ffedbdedbb800 0xfffffffffffee002 0x7fffffffffffdc00

def z735 : W := mkw 0x04fff6def000212f 0xc09ffedbde000425 0xfefffffff0016060 0x7fdffffffe002c0c

def z736 : W := mkw 0x80fff6def6ddc007 0xf01ffedbdedbb800 0xffffffffffff6001 0x7fffffffffffec00

def z737 : W := mkw 0x70228b258b2b1cc1 0x0e045164b1656398 0xfffbcfe7ffef9cff 0xffff79fcfffdf39f

def z738 : W := mkw 0x00fff6def0000007 0xc01ffedbde000000 0x04fb0fff30000000 0x209f61ffe6000000

def z739 : W := mkw 0x54229b0ddb0b39e9 0x8a845361bb61673d 0x14677f1f3f1ee71a 0x228cefe3e7e3dce3

def z740 : W := mkw 0x80fff6def24dc007 0xd01ffedbde49b800 0xfefffffff01fe007 0xffdffffffe03fc00

def z741 : W := mkw 0xf809486328669494 0x1f01290c650cd292 0xff9ff8ff38ffff9f 0xfff3ff1fe71ffff3

def z742 : W := mkw 0x80ffe6d6a0448007 0x501ffcdad4089000 0x37fb4fe708ee8006 0x86ff69fce11dd000

def z743 : W := mkw 0x64541db85db03f28 0xac8a83b70bb607e5 0x25f8ffe0ffe1e0fc 0x44bf1ffc1ffc3c1f

def z744 : W := mkw 0x60540db00db01e00 0x2c0a81b601b603c0 0xfffcfff8cff1ffe7 0xffff9fff19fe3ffc

def z745 : W := mkw 0x00fff6def0000007 0xc01ffedbde000000 0x04ff3fff00000000 0x009fe7ffe0000000

def z746 : W := mkw 0x70540db10db21ec0 0x2e0a81b621b643d8 0xdffc0ff80ff01fe3 0xbbff81ff01fe03fc

def z747 : W := mkw 0x807fe00006ddc006 0x300ffc0000dbb800 0x1f7fb0000fff6003 0x83eff60001ffec00

def z748 : W := mkw 0x8000000006ddc000 0x3000000000dbb800 0x0904b0000fffe007 0x8120960001fffc00

def z749 : W := mkw 0x80ffe246a6ddc007 0x701ffc48d4dbb800 0x3f7ff0070fffe007 0x87effe00e1fffc00

def z750 : W := mkw 0x005d44d220000004 0x000ba89a44000000 0xdeff0fff00000000 0x3bdfe1ffe0000000

def z751 : W := mkw 0x887fe04226ddc016 0x310ffc0844dbb802 0x3f7ff0003fffe01f 0x87effe0007fffc03

def z752 : W := mkw 0x50228b058b0b18c1 0x0a045160b1616318 0x8c638f07cf0f18e5 0x918c71e0f9e1e31c

def z753 : W := mkw 0x78228b258b2b1cd1 0x0f045164b165639a 0xee638f07cf0f1cfd 0xddcc71e0f9e1e39f

def z754 : W := mkw 0x807fe00006ddc006 0x300ffc0000dbb800 0x2f7bf0000fefe005 0x85ef7e0001fdfc00

def z755 : W := mkw 0x50000901090218c0 0x0a00012021204318 0xc0000000c00018e0 0x580000001800031c

def z756 : W := mkw 0x008016def0000001 0xc01002dbde000000 0xda840ffff0101f03 0xfb5081fffe0203e0

def z757 : W := mkw 0x80fff6def6ddc007 0xf01ffedbdedbb800 0x3fffffff3fffe007 0xa7ffffffe7fffc00

def z758 : W := mkw 0x0400100850002128 0x808002010a000425 0x9804f018f011ffff 0xb3009e031e023fff

def z759 : W := mkw 0xf80009210fff9ed0 0x3f00012421fff3da 0x010000000fff9fff 0x8020000001fff3ff

def z760 : W := mkw 0x50228b058b0b18c1 0x0a045160b1616318 0xee638f1fcf0f1fe5 0xfdcc71e3f9e1e3fc

def z761 : W := mkw 0x8022a00006ddc002 0x3004540000dbb800 0x0100b0000fffe007 0x8020160001fffc00

def z762 : W := mkw 0x008016def0000001 0xc01002dbde000000 0x00800fff30000000 0x201001ffe6000000

def z763 : W := mkw 0x80ffe4d226ddc006 0x701ffc9a44dbb800 0x3ffff0e00fffe007 0x87fffe1c01fffc00

def z764 : W := mkw 0x807fe00006ddc006 0x300ffc0000dbb800 0x257bf0000fffe007 0x84af7e0001fffc00

def z765 : W := mkw 0x00fff6def0000007 0xc01ffedbde000000 0xfefffffff80e0004 0xffdfffffff01c000

def z766 : W := mkw 0x00ffe6d6a0000007 0x401ffcdad4000000 0x24fb4fe730000000 0x449f69fce6000000

def z767 : W := mkw 0x10228305830b08c1 0x02045060b0616118 0xee638f07c70f08e5 0x5dcc71e0f8e1e11c

def z768 : W := mkw 0x80fff6def0448007 0xd01ffedbde089000 0xfffffffff0e08002 0x7ffffffffe1c1000

def z769 : W := mkw 0xf809486328669494 0x1f01290c650cd292 0xff9b48e738ee9c9f 0xfff3691ce71dd393

def z770 : W := mkw 0x80fff6def6ddc007 0xf01ffedbdedbb800 0xfffffffffffff49f 0xfffffffffffffe93

def z771 : W := mkw 0x0022830483090841 0x0004506090612108 0xee638f07cf0f0865 0xddcc71e0f9e1e10c

def z772 : W := mkw 0x04f6b69cd699612b 0xe09ed6d39ad32c25 0x8864b718c7116b61 0x110c96e318e22d6c

def z773 : W := mkw 0x00fff6def0000007 0xc01ffedbde000000 0xfefffffff0008006 0xffdffffffe001000

def z774 : W := mkw 0x78540db10db21e90 0x2f0a81b621b643d2 0xdffc0ff80ff01f9b 0xbbff81ff01fe03f3

def z775 : W := mkw 0x80ffe6d6a6ddc007 0x701ffcdad4dbb800 0x7fffffe73fffe007 0xeffffffce7fffc00

def z776 : W := mkw 0x04a296def0002129 0xc09452dbde000425 0xfee7fffff011ffff 0xffdcfffffe023fff

def z777 : W := mkw 0x8054200006ddc002 0x300a840000dbb800 0x010430000fffe007 0x8020860001fffc00

def z778 : W := mkw 0x8076a00006ddc002 0x300ed40000dbb800 0x0964b0000fff6001 0x012c960001ffec00

def z779 : W := mkw 0x307686b586bb06c1 0x260ed0d6b0d760d8 0x319f80ffc0ff07e6 0x6633f01ff81fe0fc

def z780 : W := mkw 0x740009210fbb3fe8 0x2e80012421f767fd 0x010000000fffffff 0x8020000001ffffff

def z781 : W := mkw 0x00fff6def0000007 0xc01ffedbde000000 0x9cfffffff0000000 0x339ffffffe000000

def z782 : W := mkw 0x00fff6def0000007 0xc01ffedbde000000 0xeefb8ffff0000000 0x7ddf71fffe000000

def z783 : W := mkw 0x70540db10db21e80 0x2e0a81b621b643d0 0xdfff0fff0ffe1f03 0xbbffe1ffe1ffc3e0

def z784 : W := mkw 0x0009404220000004 0x0001280844000000 0xfefb4fe730000000 0x7fdf69fce6000000

def z785 : W := mkw 0x0054049004900000 0x200a809200920000 0xdffc0ff80ff01f03 0xbbff81ff01fe03e0

def z786 : W := mkw 0x00fff6def0000007 0xc01ffedbde000000 0xfeffffffff000001 0xffdfffffffe00000

def z787 : W := mkw 0x807fe4d226ddc006 0x300ffc9a44dbb800 0xffffffff3fffe007 0xffffffffe7fffc00

def z788 : W := mkw 0x00fff6def0000007 0xc01ffedbde000000 0xfefffffff0001498 0x7fdffffffe000293

def z789 : W := mkw 0x008946d6a0000005 0x401128dad4000000 0x049b0fe700000000 0x009361fce0000000

def z790 : W := mkw 0xa809406220648414 0x1501280c440c9082 0x779b48e738ee841e 0xeef3691ce71dd083

def z791 : W := mkw 0x00ffe6d6a0000007 0x401ffcdad4000000 0x8cff0fff00000000 0x119fe1ffe0000000

def z792 : W := mkw 0x807fe00006ddc006 0x300ffc0000dbb800 0x377f70000ffee006 0x86efee0001ffdc00

def z793 : W := mkw 0x00fff6def0000007 0xc01ffedbde000000 0xeeffbfffc0000000 0x5ddff7fff8000000

def z794 : W := mkw 0x60540db00db01e00 0x2c0a81b601b603c0 0xd7f80ff80fe01f02 0xbaff01ff01fc03e0

def z795 : W := mkw 0xa82bc366a36d8c55 0x1505786cd46db18a 0x99f8c7e0f7e18c7b 0x333f18fc1efc318f

def z796 : W := mkw 0x807fe00006ddc006 0x300ffc0000dbb800 0x2967f0000fffe007 0x852cfe0001fffc00

def z797 : W := mkw 0x80ffe69486ddc007 0x701ffcd290dbb800 0x3f7ff7000fffe007 0x87effee001fffc00

def z798 : W := mkw 0x802be00006ddc006 0x30057c0000dbb800 0x371bf0000fffe007 0x86e37e0001fffc00

def z799 : W := mkw 0x0076869486990001 0x200ed0d290d32000 0xffff8fffcfff0007 0xfffff1fff9ffe000

def z800 : W := mkw 0x04fff6def000212f 0xc09ffedbde000425 0xfefffffff0011ffd 0xffdffffffe0023ff

def z801 : W := mkw 0x00fff6def0000007 0xc01ffedbde000000 0x3effffff30000000 0x27dfffffe6000000

def z802 : W := mkw 0x7c001dfb79223fb8 0x8f8003bf6f2447f7 0xc0800ffff0001ff8 0x781001fffe0003ff

def z803 : W := mkw 0x0022869480000001 0x000450d290000000 0xeee38fffc0000000 0x7ddc71fff8000000

def z804 : W := mkw 0x00ffe6d6a6994007 0x601ffcdad4d32800 0x0cffbfe707116001 0x019ff7fce0e22c00

def z805 : W := mkw 0x00a296def2090001 0xc01452dbde412000 0xeee38fffff0f0005 0xfddc71ffffe1e000

def z806 : W := mkw 0x00f6b6def0000003 0xc01ed6dbde000000 0x88e4bfffc0000000 0x111c97fff8000000

def z807 : W := mkw 0x805d600006ddc006 0x300bac0000dbb800 0x1f7c70000fffe007 0x83ef8e0001fffc00

def z808 : W := mkw 0x80ffe6d6a6ddc007 0x701ffcdad4dbb800 0xffffffe7cfffe007 0xdffffffcf9fffc00

def z809 : W := mkw 0x60540db00db01e00 0x2c0a81b601b603c0 0x57fc0ff80ff01702 0xaaff81ff01fe02e0

def z810 : W := mkw 0xf809486328669494 0x1f01290c650cd292 0x359b48e738ee849e 0x66b3691ce71dd093

def z811 : W := mkw 0x048016def0002129 0xc09002dbde000425 0xe080fffff001e0fc 0x7c101ffffe003c1f

def z812 : W := mkw 0x60540db00db01e00 0x2c0a81b601b603c0 0xdffc8ff8cff11f63 0xbbff91ff19fe23ec

def z813 : W := mkw 0x008016def0000001 0xc01002dbde000000 0xe080fffff0000000 0x7c101ffffe000000

def z814 : W := mkw 0x60542db00db05e02 0x2c0a85b601b60bc0 0xdffc3ff80ff07f03 0xbbff87ff01fe0fe0

def z815 : W := mkw 0x84fff6def6dde12f 0xf09ffedbdedbbc25 0xffffffffffffe0ff 0xfffffffffffffc1f

def z816 : W := mkw 0xf809486328669494 0x1f01290c650cd292 0x679b48e738ee909c 0xccf3691ce71dd213

def z817 : W := mkw 0x80fff6def4d48007 0xf01ffedbde9a9000 0xfffffffffffe8007 0xffffffffffffd000

def z818 : W := mkw 0xf809496329669cd4 0x1f01292c652cd39a 0x779b48e738ee9cfe 0xeef3691ce71dd39f

def z819 : W := mkw 0x7000082108221480 0x0e00010421044290 0x779b48e738ee949e 0xeef3691ce71dd293

def z820 : W := mkw 0x5000090109021880 0x0a00012021204310 0xee638f07cf0f18e5 0xddcc71e0f9e1e31c

def z821 : W := mkw 0x00fff6def4900007 0xe01ffedbde920000 0xffffffffffe00000 0x7ffffffffffc0000

def z822 : W := mkw 0x60540db00db01e00 0x2c0a81b601b603c0 0xd9fc0ff807f01f03 0x3b3f81ff00fe03e0

def z823 : W := mkw 0x807fe49006ddc006 0x300ffc9200dbb800 0x3ffff0f80fffe007 0xa7fffe1f01fffc00

def z824 : W := mkw 0xf80009210df69e90 0x3f00012421bed3d2 0xfb0440183ffe9f9f 0xff60880307ffd3f3

def z825 : W := mkw 0x807fe00006ddc006 0x300ffc0000dbb800 0x3f7ff0000fff6001 0x07effe0001ffec00

def z826 : W := mkw 0x00abd6def0000005 0xc0157adbde000000 0xfefbcffff0000000 0x7fdf79fffe000000

def z827 : W := mkw 0xfc0019295b6fbdf8 0x9f8003252b6df7bf 0xfb04f018ffffffff 0xff609e031fffffff

def z828 : W := mkw 0x807fe00006ddc006 0x300ffc0000dbb800 0x3f7ff0000ffff49f 0x87effe0001fffe93

def z829 : W := mkw 0xf85d49210df69e94 0x3f0ba92421bed3d2 0x3f7f40000ffe9f9f 0x87efe80001ffd3f3

def z830 : W := mkw 0x807fe00006ddc006 0x300ffc0000dbb800 0xff7ff000cfffe007 0xdfeffe0019fffc00

def z831 : W := mkw 0xf8f6bebdd8669493 0xdf1ed7d7bb0cd292 0x8964b718c8ee949e 0x912c96e3191dd293

def z832 : W := mkw 0x00fff6def0000007 0xc01ffedbde000000 0xeefbffe7f0000000 0x5ddf7ffcfe000000

def z833 : W := mkw 0x008016def0000001 0xc01002dbde000000 0xf2804ffff0000000 0x7e5009fffe000000

def z834 : W := mkw 0x00ffe6d6a0000007 0x401ffcdad4000000 0x7effffe730000000 0x6fdffffce6000000

def z835 : W := mkw 0x0476969cd0002129 0x808ed2d39a000425 0xfefffffff011ffff 0xffdffffffe023fff

def z836 : W := mkw 0xf809486328669494 0x1f01290c650cd292 0xff9fc8fff8ff9fff 0xfff3f91fff1ff3ff

def z837 : W := mkw 0x802be00006ddc006 0x30057c0000dbb800 0x3b07f0000fffe007 0x8760fe0001fffc00

def z838 : W := mkw 0x50228b058b0b18c1 0x0a045160b1616318 0xee638f07cf0f0861 0x5dcc71e0f9e1e10c

def z839 : W := mkw 0x807fe00006ddc006 0x300ffc0000dbb800 0x7ffff8e00fffe007 0xafffff1c01fffc00

def z840 : W := mkw 0x008016def0000001 0xc01002dbde000000 0xc884bffff0000000 0x791097fffe000000

def z841 : W := mkw 0x80fff6def6ddc007 0xf01ffedbdedbb800 0xffffffffffefe004 0x7ffffffffffdfc00

def z842 : W := mkw 0x10228305830b08c1 0x02045060b0616118 0x20638707c70f00e4 0x440c70e0f8e1e01c

def z843 : W := mkw 0x04fff6def000212f 0xc09ffedbde000425 0x8cffbfffc0116b61 0x119ff7fff8022d6c

def z844 : W := mkw 0x0022820482090001 0x0004504090412000 0xee638f07cf0f18e5 0xddcc71e0f9e1e31c

def z845 : W := mkw 0x50228b058b0b18c1 0x0a045160b1616318 0xff7b8f07cfef18e7 0xdfef71e0f9fde31c

def z846 : W := mkw 0xf82bc9210b6f9cd4 0x1f057924216df39a 0x3f7bc0000fef9cff 0x87ef780001fdf39f

def z847 : W := mkw 0x048016def0002129 0xc09002dbde000425 0xc0800ffff0000b60 0x781001fffe00016c

def z848 : W := mkw 0x84fff6def4d4e12f 0xf09ffedbde9a9c25 0xfffffffff0f1ffff 0xfffffffffe1e3fff

def z849 : W := mkw 0x008016def0000001 0xc01002dbde000000 0xea808ffff0000000 0x7d5011fffe000000

def z850 : W := mkw 0x205405b005b00e00 0x240a80b600b601c0 0x9ffc07f80ff00f03 0xb3ff80ff01fe01e0

def z851 : W := mkw 0x50228b058b0b18c1 0x0a045160b1616318 0xfe638f07cf0f1ce7 0xffcc71e0f9e1e39c

def z852 : W := mkw 0x04fff6def000212f 0xc09ffedbde000425 0xfefffffff001f4fe 0xffdffffffe003e9f

def z853 : W := mkw 0x04dd76def000212f 0xc09baedbde000425 0xfa9cfffff011ffff 0xff539ffffe023fff

def z854 : W := mkw 0x00ffe6d6a0000007 0x401ffcdad4000000 0xdeff0fff00101f03 0xbbdfe1ffe00203e0

def z855 : W := mkw 0x60abfb6efdb01e07 0xec157f6ddfb603c0 0x2103f007fff01f03 0xc4207e00fffe03e0

def z856 : W := mkw 0xf809486328669494 0x1f01290c650cd292 0xf79b48ff38ee9f9e 0xfef3691fe71dd3f3

def z857 : W := mkw 0x00fff6def0000007 0xc01ffedbde000000 0xfefffffff011f49f 0xffdffffffe023e93

def z858 : W := mkw 0x8076a00006ddc002 0x300ed40000dbb800 0x3b64f0000fffe007 0x876c9e0001fffc00

def z859 : W := mkw 0x807fe00006ddc006 0x300ffc0000dbb800 0xff7ff0000ffff807 0x9feffe0001ffff00

def z860 : W := mkw 0x00dd76def0000007 0xc01baedbde000000 0xf69f7ffff0000000 0x7ed3effffe000000

def z861 : W := mkw 0xf80009210fffde90 0x3f00012421fffbd2 0x010000000fffff9f 0x8020000001fffff3

def z862 : W := mkw 0x8009404220448004 0x1001280844089000 0x779b48e738ee949e 0xeef3691ce71dd293

def z863 : W := mkw 0x7800092109221cd0 0x0f0001242124439a 0x0000000000001cf8 0x000000000000039f

def z864 : W := mkw 0x042bd24ef000212d 0x80857a49de000425 0xfefffffff011ffff 0xffdffffffe023fff

def z865 : W := mkw 0x00fff6def0000007 0xc01ffedbde000000 0x3effffe7f0000000 0x47dffffcfe000000

def z866 : W := mkw 0x7800086328221490 0x0f00010c65044292 0x779b08e738ee149e 0xeef3611ce71dc293

def z867 : W := mkw 0x00f6b69cd0000003 0xc01ed6d39a000000 0xfeffbfffc0000000 0x7fdff7fff8000000

def z868 : W := mkw 0x60540db00db01e00 0x2c0a81b601b603c0 0x8dfc0ff80ff01f03 0x91bf81ff01fe03e0

def z869 : W := mkw 0x807fe00006ddc006 0x300ffc0000dbb800 0x057bb0000fef6000 0x00af760001fdec00

def z870 : W := mkw 0x80fff6def6ddc007 0xf01ffedbdedbb800 0x3fffffe7ffffe007 0xc7fffffcfffffc00

def z871 : W := mkw 0x00fff6def0000007 0xc01ffedbde000000 0xfefffffff001e004 0x7fdffffffe003c00

def z872 : W := mkw 0xd05d6b058dd6d8c7 0x3a0bad60b1badb18 0xd11c7f07c0f0f8e2 0x5a238fe0f81e1f1c

def z873 : W := mkw 0x00a296def0000001 0xc01452dbde000000 0xfee7fffff0000000 0x7fdcfffffe000000

def z874 : W := mkw 0x00fff6def0000007 0xc01ffedbde000000 0xfefffffff0109f9f 0xffdffffffe0213f3

def z875 : W := mkw 0x00ffe6d6a0000007 0x401ffcdad4000000 0x44fb0fe730000000 0x689f61fce6000000

def z876 : W := mkw 0x8076a00006ddc002 0x300ed40000dbb800 0x2f67b0000fffe007 0x85ecf60001fffc00

def z877 : W := mkw 0x807fe69486ddc007 0x300ffcd290dbb800 0xffffffffcfffe007 0xfffffffff9fffc00

def z878 : W := mkw 0x04f6b6def000212b 0xc09ed6dbde000425 0xc8e4bffff0117ff9 0x791c97fffe022fff

def z879 : W := mkw 0x50228b058b0b18c1 0x0a045160b1616318 0x04630f07cf0e00e0 0x408c61e0f9e1c01c

def z880 : W := mkw 0x50228b058b0b18c1 0x0a045160b1616318 0xfe63cf07ff0f18e5 0xffcc79e0ffe1e31c

def z881 : W := mkw 0xf809496329669c94 0x1f01292c652cd392 0xf79b4fe738ee9c9e 0xfef369fce71dd393

def z882 : W := mkw 0x80fff6def4d4c007 0xf01ffedbde9a9800 0xfffffffff0e00000 0x7ffffffffe1c0000

def z883 : W := mkw 0xf809486328669494 0x1f01290c650cd292 0x7f9f48e738fe949f 0xeff3e91ce71fd293

def z884 : W := mkw 0x00fff6def4900007 0xe01ffedbde920000 0xfffffffffff1e007 0xfffffffffffe3c00

def z885 : W := mkw 0x048016def0002129 0xc09002dbde000425 0xd0847ffff010e71a 0x7a108ffffe021ce3

def z886 : W := mkw 0x8009600006ddc006 0x30012c0000dbb800 0x010070000fffe007 0x80200e0001fffc00

def z887 : W := mkw 0x04ffe6d6a000212f 0x409ffcdad4000425 0x04fb0fe70011ffff 0x809f61fce0023fff

def z888 : W := mkw 0x00abf6def0000007 0xc0157edbde000000 0xfa87fffff0000000 0x7f50fffffe000000

def z889 : W := mkw 0x00d406d6a0000001 0x401a80dad4000000 0xdefc0fff00000000 0x3bdf81ffe0000000

def z890 : W := mkw 0x00fff6def0000007 0xc01ffedbde000000 0xfefffffff0111fe7 0xffdffffffe0223fc

def z891 : W := mkw 0x80ffe6d6a24dc007 0x501ffcdad449b800 0x24fbffe7000fe004 0x049f7ffce001fc00

def z892 : W := mkw 0x10228305830b08c1 0x02045060b0616118 0x88638707c70f0861 0x110c70e0f8e1e10c

def z893 : W := mkw 0x805d400004d48004 0x300ba800009a9000 0x3f7ff0000fffe007 0x87effe0001fffc00

def z894 : W := mkw 0x04fff6def000212f 0xc09ffedbde000425 0xfefffffff0101ffb 0xffdffffffe0203ff

def z895 : W := mkw 0xf809486328669494 0x1f01290c650cd292 0x779b48e738ef9cff 0xeef3691ce71df39f

def z896 : W := mkw 0xfc0009210b6fbdf8 0x1f800124216df7bf 0x010000000fffffff 0x8020000001ffffff

def z897 : W := mkw 0x00abf24ef0000007 0xc0157e49de000000 0xfefbffe7f0000000 0x7fdf7ffcfe000000

def z898 : W := mkw 0xf809486328669494 0x1f01290c650cd292 0xff9ff8e7f8fffcff 0xfff3ff1cff1fff9f

def z899 : W := mkw 0x008016def0000001 0xc01002dbde000000 0xd6980ffff0000000 0x7ad301fffe000000

def z900 : W := mkw 0x807fe20486ddc007 0x300ffc4090dbb800 0xbf7ff700cfffe007 0x97effee019fffc00

def z901 : W := mkw 0x807fe00006ddc006 0x300ffc0000dbb800 0x2f7fb0000fff6005 0x85eff60001ffec00

def z902 : W := mkw 0x8000000006ddc000 0x3000000000dbb800 0x2100f0000fffe007 0x84201e0001fffc00

def z903 : W := mkw 0x807fe246a6ddc007 0x300ffc48d4dbb800 0xffffffe7ffffe007 0xfffffffcfffffc00

def z904 : W := mkw 0x00fff6def0000007 0xc01ffedbde000000 0x04fb0fe7f0000000 0x409f61fcfe000000

def z905 : W := mkw 0x00f6b6def6994003 0xe01ed6dbded32800 0xc8e4bffff7116001 0x791c97fffee22c00

def z906 : W := mkw 0xf809486328669494 0x1f01290c650cd292 0x059b08e738ee0418 0x20b3611ce71dc083

def z907 : W := mkw 0x80ffe6d6a4d4c007 0x701ffcdad49a9800 0x05fb0fe700e00000 0x00bf61fce01c0000

def z908 : W := mkw 0x807fe00006ddc006 0x300ffc0000dbb800 0x3f7ff000cfffe0e7 0xc7effe0019fffc1c

def z909 : W := mkw 0x008016def0000001 0xc01002dbde000000 0xc0800ffff0001f00 0x781001fffe0003e0

def z910 : W := mkw 0x807fe00006ddc006 0x300ffc0000dbb800 0x3f7ff0003fffe41f 0xa7effe0007fffc83

def z911 : W := mkw 0x70540db10db21e80 0x2e0a81b621b643d0 0xdffc0fff0ff01f83 0xfbff81ffe1fe03f0

def z912 : W := mkw 0x00a296def0000001 0xc01452dbde000000 0xc4e30ffff0000000 0x789c61fffe000000

def z913 : W := mkw 0x60540db00db01e00 0x2c0a81b601b603c0 0xdffc4ff83ff09f1b 0xbbff89ff07fe13e3

def z914 : W := mkw 0xf80009210b6f9cd0 0x1f000124216df39a 0x010000000fef18e5 0x8020000001fde31c

def z915 : W := mkw 0x00a296def0000001 0xc01452dbde000000 0xe0838ffff0000000 0x7c1071fffe000000

def z916 : W := mkw 0x008016def0000001 0xc01002dbde000000 0xfa84fffff011e007 0xff509ffffe023c00

def z917 : W := mkw 0xf800092109669cd0 0x1f000124212cd39a 0x0100000008ee9cfe 0x80200000011dd39f

def z918 : W := mkw 0x50228b058b0b18c1 0x0a045160b1616318 0xc4630f07cf0f18e5 0xd88c61e0f9e1e31c

def z919 : W := mkw 0x00ffe6d6a2090007 0x401ffcdad4412000 0x04fb0fe70f0e0000 0x009f61fce1e1c000

def z920 : W := mkw 0x88fff6def0448017 0xd11ffedbde089002 0xfefffffff0008018 0x7fdffffffe001003

def z921 : W := mkw 0x00fff6def0000007 0xc01ffedbde000000 0xfefffffff0001801 0xffdffffffe000300

def z922 : W := mkw 0x00fff6def0000007 0xc01ffedbde000000 0xfefffffff000841a 0x7fdffffffe001083

def z923 : W := mkw 0x0400100850002128 0x808002010a000425 0xe804f018f011fffd 0x7d009e031e023fff

def z924 : W := mkw 0x00abf6def0000007 0xc0157edbde000000 0xc0830ffff0000000 0x781061fffe000000

def z925 : W := mkw 0x80fff6def0448007 0xd01ffedbde089000 0xfffffffff8ffe007 0xffffffffff1ffc00

def z926 : W := mkw 0xf809486328669494 0x1f01290c650cd292 0x379b48e738ee841e 0xa6f3691ce71dd083

def z927 : W := mkw 0x008016def0000001 0xc01002dbde000000 0xda840ffff0000000 0x7b5081fffe000000

def z928 : W := mkw 0x008016def0000001 0xc01002dbde000000 0xea808ffff00118e5 0xfd5011fffe00231c

def z929 : W := mkw 0xf809486328669494 0x1f01290c650cd292 0x7f9bc8e738ef949f 0xeff3791ce71df293

def z930 : W := mkw 0x007fc6d6a0000005 0x000ff8dad4000000 0xfeffcffff0000000 0x7fdff9fffe000000

def z931 : W := mkw 0x807fe49006ddc206 0x300ffc9200dbb840 0x3f7ff0180fffe307 0x87effe0301fffc60

def z932 : W := mkw 0x700009210db21ec0 0x2e00012421b643d8 0x010000000ff01fe3 0x8020000001fe03fc

def z933 : W := mkw 0x802be00006ddc006 0x30057c0000dbb800 0x2103f0000fefe004 0x04207e0001fdfc00

def z934 : W := mkw 0x60540db00db01e00 0x2c0a81b601b603c0 0xfffc4ff80ff09f07 0xbfff89ff01fe13e0

def z935 : W := mkw 0x005404d220000000 0x000a809a44000000 0xdefc0fff30000000 0x7bdf81ffe6000000

def z936 : W := mkw 0x807fe00006ddc006 0x300ffc0000dbb800 0x377bf0000fefe006 0x86ef7e0001fdfc00

def z937 : W := mkw 0x00f6b6def0000003 0xc01ed6dbde000000 0xeee7bffff0000000 0x7ddcf7fffe000000

def z938 : W := mkw 0xfc0019295df6bfb8 0xbf8003252bbed7f7 0xfb04f018ffffffff 0xff609e031fffffff

def z939 : W := mkw 0x80dd76def4d4c007 0xf01baedbde9a9800 0xd19c7ffff0f0e002 0x7a338ffffe1e1c00

def z940 : W := mkw 0x50228b058b0b18c1 0x0a045160b1616318 0x2e638f07cf0f00e5 0xc5cc71e0f9e1e01c

def z941 : W := mkw 0x80fff6def4d4c007 0xf01ffedbde9a9800 0xfffffffffff0e003 0xfffffffffffe1c00

def z942 : W := mkw 0x50228b058b0b18c1 0x0a045160b1616318 0xcc638f07cf0f18e1 0x598c71e0f9e1e31c

def z943 : W := mkw 0x60540db00db01e00 0x2c0a81b601b603c0 0xdffc0ff80ff09f9f 0xbbff81ff01fe13f3

def z944 : W := mkw 0x04fff6def000212f 0xc09ffedbde000425 0x24fbffe7f001e0fc 0x449f7ffcfe003c1f

def z945 : W := mkw 0x807fe04226ddc006 0x300ffc0844dbb800 0x3f7ff0073fffe007 0xc7effe00e7fffc00

def z946 : W := mkw 0x00fff6def0000007 0xc01ffedbde000000 0x76fbffe7f0000000 0x6edf7ffcfe000000

def z947 : W := mkw 0x005d44d220000004 0x000ba89a44000000 0x04fb0fe700000000 0x009f61fce0000000

def z948 : W := mkw 0x50228b058b0b18c1 0x0a045160b1616318 0xe6630f07cf0e18e4 0xdccc61e0f9e1c31c

def z949 : W := mkw 0x0076800006990000 0x200ed00000d32000 0x3f7ff0000fffe007 0x87effe0001fffc00

def z950 : W := mkw 0x00ffe6d6a0000007 0x401ffcdad4000000 0xfeffffff00000000 0x3fdfffffe0000000

def z951 : W := mkw 0x700009210fbb1ec0 0x2e00012421f763d8 0x010000000fef18e5 0x8020000001fde31c

def z952 : W := mkw 0x700009210b2b1cc0 0x0e00012421656398 0x010000000fef1ce7 0x8020000001fde39c

def z953 : W := mkw 0x008956def0000005 0xc0112adbde000000 0xe0834ffff0000000 0x7c1069fffe000000

def z954 : W := mkw 0x00ffe6d6a6994007 0x601ffcdad4d32800 0x04fb0fe707000000 0x009f61fce0e00000

def z955 : W := mkw 0x008016def0000001 0xc01002dbde000000 0x00800fe7f0000000 0x401001fcfe000000

def z956 : W := mkw 0x00ffe6d6a0000007 0x401ffcdad4000000 0x14ff7fe700000000 0x029feffce0000000

def z957 : W := mkw 0x00fff6def0000007 0xc01ffedbde000000 0xd8fcfffff0000000 0x7b1f9ffffe000000

def z958 : W := mkw 0xf8ffeef7aeffd497 0x7f1ffddef5dffa92 0x7fffffe73ffff49f 0xeffffffce7fffe93

def z959 : W := mkw 0x00abf6def0000007 0xc0157edbde000000 0xf69bfffff0000000 0x7ed37ffffe000000

def z960 : W := mkw 0x80abf6def24dc007 0xd0157edbde49b800 0xe083fffff00fe004 0x7c107ffffe01fc00

def z961 : W := mkw 0xf809486328669494 0x1f01290c650cd292 0x779f48ff38fe979e 0xeef3e91fe71fd2f3

def z962 : W := mkw 0x780009210db21e90 0x2f00012421b643d2 0x010000000ff01f9b 0x8020000001fe03f3

def z963 : W := mkw 0x808016def6ddc001 0xf01002dbdedbb800 0xc1800fffffffe007 0xf83001fffffffc00

def z964 : W := mkw 0x002bc246a0000005 0x00057848d4000000 0x76fb4fe730000000 0x6edf69fce6000000

def z965 : W := mkw 0x807fe49006ddc006 0x300ffc9200dbb800 0x3fffffe00fffe007 0x87fffffc01fffc00

def z966 : W := mkw 0x50228b058b0b18c1 0x0a045160b1616318 0xee67bf07cf1f78e5 0xddccf7e0f9e3ef1c

def z967 : W := mkw 0x8009404220448004 0x1001280844089000 0x379b48e708ee8006 0x86f3691ce11dd000

def z968 : W := mkw 0x80fff6def6ddc007 0xf01ffedbdedbb800 0x8dffbfffcfff6001 0x11bff7fff9ffec00

def z969 : W := mkw 0x50228b058b0b18c1 0x0a045160b1616318 0x66638f07cf0f10e4 0xcccc71e0f9e1e21c

def z970 : W := mkw 0x60540db00db01e00 0x2c0a81b601b603c0 0xdffcbff80ff17f03 0xbbff97ff01fe2fe0

def z971 : W := mkw 0x60540db00db01e00 0x2c0a81b601b603c0 0xdffc0ff80ff11fe7 0xbbff81ff01fe23fc

def z972 : W := mkw 0x00fff6def0000007 0xc01ffedbde000000 0xfefffffff0100702 0x7fdffffffe0200e0

def z973 : W := mkw 0x00fff6def0000007 0xc01ffedbde000000 0xbeffffffc0000000 0x17dffffff8000000

def z974 : W := mkw 0x807fe49006ddc006 0x300ffc9200dbb800 0xfffffff80fffff07 0xbfffffff01ffffe0

def z975 : W := mkw 0x04d416def0002129 0xc09a82dbde000425 0xdefc0ffff0101ffb 0xfbdf81fffe0203ff

def z976 : W := mkw 0x80ffe6d6a6ddc007 0x701ffcdad4dbb800 0x05fb0fe70fffe007 0x80bf61fce1fffc00

def z977 : W := mkw 0x205405b005b00e00 0x240a80b600b601c0 0xdffc0ff807f00f03 0x3bff81ff00fe01e0

def z978 : W := mkw 0x70228b258b2b1ec1 0x0e045164b16563d8 0xee638f07cf0f1fe5 0xddcc71e0f9e1e3fc

def z979 : W := mkw 0x04fff6def000212f 0xc09ffedbde000425 0xfefffffff00000f8 0x7fdffffffe00001f

def z980 : W := mkw 0x00fff6def2090007 0xc01ffedbde412000 0xfefffffff7010001 0x7fdffffffee02000

def z981 : W := mkw 0x007fe246a0000007 0x000ffc48d4000000 0xfeffffe7f0000000 0x7fdffffcfe000000

def z982 : W := mkw 0x80fff6def6ddc007 0xf01ffedbdedbb800 0xfefffffff71fe005 0x7fdffffffee3fc00

def z983 : W := mkw 0xf809486328669494 0x1f01290c650cd292 0x659b48e738ee949c 0x6cb3691ce71dd293

def z984 : W := mkw 0x00ffe6d6a0000007 0x401ffcdad4000000 0xc4fb0fff00000000 0x389f61ffe0000000

def z985 : W := mkw 0x80fff6def6ddc007 0xf01ffedbdedbb800 0x25fbffe7ffefe004 0x44bf7ffcfffdfc00

def z986 : W := mkw 0xf809486328669494 0x1f01290c650cd292 0x779b48e738ee1498 0x6ef3691ce71dc293

def z987 : W := mkw 0x60540db00db01e00 0x2c0a81b601b603c0 0x9ffc0ff80ff00b03 0x93ff81ff01fe0160

def z988 : W := mkw 0x04fff6def000212f 0xc09ffedbde000425 0xfefffffff011e0ff 0xffdffffffe023c1f

def z989 : W := mkw 0xfc0009210df6bfb8 0x3f80012421bed7f7 0x010000000fffffff 0x8020000001ffffff

def z990 : W := mkw 0x50228b058b0b18c1 0x0a045160b1616318 0xee63ff07cf0ff8e5 0xddcc7fe0f9e1ff1c

def z991 : W := mkw 0x7876a8632ebb5492 0x2f0ed50c65d76a92 0x48e4b8e737117499 0x691c971ce6e22e93

def z992 : W := mkw 0x50228b058b0b18c1 0x0a045160b1616318 0xfe67ff07ff1ffcff 0xffccffe0ffe3ff9f

def z993 : W := mkw 0x007fe4d220000006 0x000ffc9a44000000 0xfeffffff30000000 0x7fdfffffe6000000

def z994 : W := mkw 0x04dd76def000212f 0xc09baedbde000425 0xd09c7ffff010fffa 0x7a138ffffe021fff

def z995 : W := mkw 0x60540db00db01e00 0x2c0a81b601b603c0 0xdffc0ff8cff01fe3 0xfbff81ff19fe03fc

def z996 : W := mkw 0x04fff6def000212f 0xc09ffedbde000425 0xfefffffff0106300 0x7fdffffffe020c60

def z997 : W := mkw 0xb809406320668494 0x1701280c640cd092 0x739b40e730ee949e 0xee73681ce61dd293

def z998 : W := mkw 0x0054059005900a00 0x200a80b200b20140 0xdffc0ff80ff00b03 0xbbff81ff01fe0160

def z999 : W := mkw 0xf809486328669494 0x1f01290c650cd292 0x259b48e738ee949e 0xc4b3691ce71dd293

def z1000 : W := mkw 0x50228b058b0b18c1 0x0a045160b1616318 0xee638f07cf1f1fe7 0xddcc71e0f9e3e3fc

def z1001 : W := mkw 0x00ffe6d6a0000007 0x401ffcdad4000000 0xfeffffe7c0000000 0x5fdffffcf8000000

def z1002 : W := mkw 0x008956def0000005 0xc0112adbde000000 0xfe9ffffff0000000 0x7fd3fffffe000000

def z1003 : W := mkw 0x80ffe6d6a4d4c007 0x701ffcdad49a9800 0x15ff7fe700f0e002 0x02bfeffce01e1c00

def z1004 : W := mkw 0x60540db00db01e00 0x2c0a81b601b603c0 0x9dfc0ff80ff00f03 0x33bf81ff01fe01e0

def z1005 : W := mkw 0x008016def0000001 0xc01002dbde000000 0xcee00ffff0000000 0x79dc01fffe000000

def z1006 : W := mkw 0x00fff6def0000007 0xc01ffedbde000000 0x84fb0fffc0000000 0x109f61fff8000000

def z1007 : W := mkw 0x0076a00006994002 0x200ed40000d32800 0x3f7fb0000fff6007 0x87eff60001ffec00

def z1008 : W := mkw 0x00ffe6d6a0000007 0x401ffcdad4000000 0x14ff0fff00000000 0x229fe1ffe0000000

def z1009 : W := mkw 0x7c001b6ff9223df9 0x8f80036dff2447bf 0xc0800ffff0001ff8 0x781001fffe0003ff

def z1010 : W := mkw 0xf800092109669c90 0x1f000124212cd392 0x010000000fee9c9f 0x8020000001fdd393

def z1011 : W := mkw 0x8009400006ddc004 0x3001280000dbb800 0x3f1ff0000fffe007 0x87e3fe0001fffc00

def z1012 : W := mkw 0x50228b058b0b18c1 0x0a045160b1616318 0xce638f07cf0f1861 0x99cc71e0f9e1e30c

def z1013 : W := mkw 0xf809486328669494 0x1f01290c650cd292 0x779f78e738fef49e 0xeef3ef1ce71fde93

def z1014 : W := mkw 0x00fff6def2094007 0xc01ffedbde412800 0xfefffffff0016000 0x7fdffffffe002c00

def z1015 : W := mkw 0x807fe04226ddc006 0x300ffc0844dbb800 0x3ffff8e70fffe007 0x87ffff1ce1fffc00

def z1016 : W := mkw 0xf80009210df69e90 0x3f00012421bed3d2 0x010000000ffe1f03 0x8020000001ffc3e0

def z1017 : W := mkw 0x60000db009201e00 0x0c0001b6012403c0 0xdff80ff80fe01f03 0xbbff01ff01fc03e0

def z1018 : W := mkw 0x807fe00006ddc006 0x300ffc0000dbb800 0x3f7ff0000ffff8e7 0x87effe0001ffff1c

def z1019 : W := mkw 0xf809486328669494 0x1f01290c650cd292 0x719b48e730ee949e 0x6e33691ce61dd293

def z1020 : W := mkw 0xf809486328669494 0x1f01290c650cd292 0xff9f48ff38ee949e 0xfff3e91fe71dd293

def z1021 : W := mkw 0x60540db00db01e00 0x2c0a81b601b603c0 0xdffc0ff80fe01f00 0x3bff81ff01fc03e0

def z1022 : W := mkw 0x807fe00006ddc006 0x300ffc0000dbb800 0x3f7ff0180fffe707 0xa7effe0301fffce0

def z1023 : W := mkw 0x00fff6def2090007 0xc01ffedbde412000 0xfeffffffff0f18e5 0xffdfffffffe1e31c

def z1024 : W := mkw 0xe02bedb00b6dde06 0x1c057db6016dbbc0 0xe083fff8000fff04 0x3c107fff0001ffe0

def z1025 : W := mkw 0x60540db00db01e00 0x2c0a81b601b603c0 0x85f80ff80fe00b00 0x10bf01ff01fc0160

def z1026 : W := mkw 0xf809486328669494 0x1f01290c650cd292 0x779b48e738ee841a 0x6ef3691ce71dd083

def z1027 : W := mkw 0x00fff6def6994007 0xe01ffedbded32800 0xfffffffffff16003 0xfffffffffffe2c00

def z1028 : W := mkw 0x00fff6def0000007 0xc01ffedbde000000 0xfefffffff000809c 0x7fdffffffe001013

def z1029 : W := mkw 0x0476979cd7992b69 0xa08ed2f39af3256d 0x8864b718c7116b61 0x110c96e318e22d6c

def z1030 : W := mkw 0xf809486328669494 0x1f01290c650cd292 0xff9bc8e7f8ee949e 0xfff3791cff1dd293

def z1031 : W := mkw 0x80fff6def6ddc007 0xf01ffedbdedbb800 0xbfffffffcfffe007 0x97fffffff9fffc00

def z1032 : W := mkw 0x008956def0000005 0xc0112adbde000000 0xc49b0ffff0000000 0x789361fffe000000

def z1033 : W := mkw 0x00ffe6d6a0000007 0x401ffcdad4000000 0xc4fb0fe7c0000000 0x589f61fcf8000000

def z1034 : W := mkw 0x04fff6def000212f 0xc09ffedbde000425 0xfefffffff011e7fe 0x7fdffffffe023cff

def z1035 : W := mkw 0xf809486328669494 0x1f01290c650cd292 0x459b08e738ee949e 0xe8b3611ce71dd293

def z1036 : W := mkw 0x80fff6def6ddc007 0xf01ffedbdedbb800 0xfffffffff0ffe006 0x7ffffffffe1ffc00

def z1037 : W := mkw 0x04fff6def000212f 0xc09ffedbde000425 0xfefffffff001f8fd 0xffdffffffe003f1f

def z1038 : W := mkw 0x00ffe6d6a0000007 0x401ffcdad4000000 0x14fb4fe730000000 0x229f69fce6000000

def z1039 : W := mkw 0x00fff6def0000007 0xc01ffedbde000000 0xfefffffff00100e4 0x7fdffffffe00201c

def z1040 : W := mkw 0xf809486328669494 0x1f01290c650cd292 0x579b08e738ee149a 0xeaf3611ce71dc293

def z1041 : W := mkw 0x008016def0000001 0xc01002dbde000000 0xc0800ffff0001498 0x781001fffe000293

def z1042 : W := mkw 0x50228b058b0b18c1 0x0a045160b1616318 0xee638f07cf1ff8e7 0xddcc71e0f9e3ff1c

def z1043 : W := mkw 0x205405b005b00e00 0x240a80b600b601c0 0x11fc07f807f00702 0x223f80ff00fe00e0

def z1044 : W := mkw 0x00ffe6d6a0000007 0x401ffcdad4000000 0x66fb0fe700000000 0x4cdf61fce0000000

def z1045 : W := mkw 0x7800082108221490 0x0f00010421044292 0x4000000030001498 0x6800000006000293

def z1046 : W := mkw 0x84fff6def6dde12f 0xf09ffedbdedbbc25 0xffffffffffffe71f 0xfffffffffffffce3

def z1047 : W := mkw 0xf809486328669494 0x1f01290c650cd292 0xfffb4fe738ee949e 0xffff69fce71dd293

def z1048 : W := mkw 0x70540db10db21e80 0x2e0a81b621b643d0 0xffff4fff3ffe9f9f 0xffffe9ffe7ffd3f3

def z1049 : W := mkw 0xf809486328669494 0x1f01290c650cd292 0x779bf8e738eff49e 0xeef37f1ce71dfe93

def z1050 : W := mkw 0x0400100850002128 0x808002010a000425 0xf004f018f011fffe 0x7e009e031e023fff

def z1051 : W := mkw 0x00fff6def2090007 0xc01ffedbde412000 0xfefffffff00f0004 0x7fdffffffe01e000

def z1052 : W := mkw 0x00f6a6d6a0000003 0x401ed4dad4000000 0x00e00fe700000000 0x001c01fce0000000

def z1053 : W := mkw 0x807fe49006ddc006 0x300ffc9200dbb800 0xbf7ff7180fffe007 0x97effee301fffc00

def z1054 : W := mkw 0x70540db10db21e80 0x2e0a81b621b643d0 0xdffc0ff80ffe1f87 0xbbff81ff01ffc3f0

def z1055 : W := mkw 0x00ffe6d6a0000007 0x401ffcdad4000000 0xfeff8fffc0000000 0x7fdff1fff8000000

def z1056 : W := mkw 0x60540db00db01e00 0x2c0a81b601b603c0 0xc5f80ff80ff01f03 0xb8bf01ff01fe03e0

def z1057 : W := mkw 0x00fff6def6990007 0xe01ffedbded32000 0xffffffffffff0007 0xffffffffffffe000

def z1058 : W := mkw 0x70540db10db21e80 0x2e0a81b621b643d0 0xffff8fffcfff1fe7 0xfffff1fff9ffe3fc

def z1059 : W := mkw 0x807fe20486ddc007 0x300ffc4090dbb800 0xff7fff07cffff8e7 0xdfefffe0f9ffff1c

def z1060 : W := mkw 0x00abf6def0000007 0xc0157edbde000000 0xeee3fffff0000000 0x7ddc7ffffe000000

def z1061 : W := mkw 0x00ffe6d6a0000007 0x401ffcdad4000000 0xeefb8fe7c00118e5 0xdddf71fcf800231c

def z1062 : W := mkw 0x807fe00006ddc006 0x300ffc0000dbb800 0xff7fff000fffe007 0x9fefffe001fffc00

def z1063 : W := mkw 0x60540db00db01e00 0x2c0a81b601b603c0 0x99fc07f80ff01f03 0xb33f80ff01fe03e0

def z1064 : W := mkw 0x808956def0448005 0xd0112adbde089000 0xf79b4ffff8ee8006 0xfef369ffff1dd000

def z1065 : W := mkw 0x00fff6def0000007 0xc01ffedbde000000 0xdeffbfffc0000000 0x3bdff7fff8000000

def z1066 : W := mkw 0x00d406d6a0000001 0x401a80dad4000000 0x04f80fe700000000 0x009f01fce0000000

def z1067 : W := mkw 0x50228b058b0b18c1 0x0a045160b1616318 0xee638f07cf0e18e0 0x5dcc71e0f9e1c31c

def z1068 : W := mkw 0x80ffe6d6a6ddc007 0x701ffcdad4dbb800 0xffffffff0fffe007 0xbfffffffe1fffc00

def z1069 : W := mkw 0x00abf6def0000007 0xc0157edbde000000 0x2083ffe7f0000000 0x44107ffcfe000000

def z1070 : W := mkw 0x985d45d325d68a94 0x330ba8ba64bad152 0xa867471f371e8b9d 0x550ce8e3e6e3d173

def z1071 : W := mkw 0x80ffe6d6a6ddc007 0x701ffcdad4dbb800 0xeffb8fe7cfef0005 0xddff71fcf9fde000

def z1072 : W := mkw 0x04fff6def000212f 0xc09ffedbde000425 0xfefffffff0000718 0x7fdffffffe0000e3

def z1073 : W := mkw 0x048016def0002129 0xc09002dbde000425 0xc0800ffff011ffff 0xf81001fffe023fff

def z1074 : W := mkw 0x0400100850002128 0x808002010a000425 0x3004f018f011ffff 0xe6009e031e023fff

def z1075 : W := mkw 0x807fe00006ddc006 0x300ffc0000dbb800 0x1d7ff0000fffe003 0x03affe0001fffc00

def z1076 : W := mkw 0x00dd66d6a0000007 0x401bacdad4000000 0x00980fe700000000 0x001301fce0000000

def z1077 : W := mkw 0x008006d6a0000001 0x401000dad4000000 0x40800fe730000000 0x681001fce6000000

def z1078 : W := mkw 0x740019295fbb3fe8 0xae8003252bf767fd 0xfb04f018ffffffff 0xff609e031fffffff

def z1079 : W := mkw 0x007fe69480000007 0x000ffcd290000000 0xfeffffffc0000000 0x7fdffffff8000000

def z1080 : W := mkw 0x50228b058b0b18c1 0x0a045160b1616318 0xee638f07cf0f00e4 0x5dcc71e0f9e1e01c

def z1081 : W := mkw 0x00ffe6d6a0000007 0x401ffcdad4000000 0xfefbcfe7f0000000 0x7fdf79fcfe000000

def z1082 : W := mkw 0x04fff6def000212f 0xc09ffedbde000425 0xfefffffff001fffc 0x7fdffffffe003fff

def z1083 : W := mkw 0x0076869480000001 0x000ed0d290000000 0xdeff0fff00000000 0x3bdfe1ffe0000000

def z1084 : W := mkw 0x80fff6def6ddc007 0xf01ffedbdedbb800 0xfffffffffffff8e7 0xffffffffffffff1c

def z1085 : W := mkw 0xf809486328669494 0x1f01290c650cd292 0xf79b48e7f8ee9cfe 0xfef3691cff1dd39f

def z1086 : W := mkw 0x70228b258b2b1cc1 0x0e045164b1656398 0xeffb8fe7cfef18e5 0xddff71fcf9fde31c

def z1087 : W := mkw 0xf07fe9210fffdec6 0x3e0ffd2421fffbd8 0x3f7ff0000fffffe7 0x87effe0001fffffc

def z1088 : W := mkw 0x707689210fbb1ec0 0x2e0ed12421f763d8 0x3f7f80000fff1fe7 0x87eff00001ffe3fc

def z1089 : W := mkw 0x00ffe6d6a0000007 0x401ffcdad4000000 0xcefb0fe700000000 0x19df61fce0000000

def z1090 : W := mkw 0x04f6b6def000212b 0xc09ed6dbde000425 0xfae4fffff011ffff 0xff5c9ffffe023fff

def z1091 : W := mkw 0x70228b258b2b1cc1 0x0e045164b1656398 0xeee38fe7cf0f1ce5 0xfddc71fcf9e1e39c

def z1092 : W := mkw 0x84fff6def4d4e12f 0xf09ffedbde9a9c25 0xfffffffff0f0e71a 0x7ffffffffe1e1ce3

def z1093 : W := mkw 0xb809406320668494 0x1701280c640cd092 0x779b48e730ee849e 0x6ef3691ce61dd093

def z1094 : W := mkw 0x807fe20486ddc007 0x300ffc4090dbb800 0x3f7ff007cfffe007 0xc7effe00f9fffc00

def z1095 : W := mkw 0x0054069480000001 0x000a80d290000000 0xdefc0fffc0000000 0x7bdf81fff8000000

def z1096 : W := mkw 0x00000246a0000001 0x00000048d4000000 0xc0800fe7f0000000 0x781001fcfe000000

def z1097 : W := mkw 0x8054000006ddc000 0x300a800000dbb800 0x3f7cf0000fffe007 0x87ef9e0001fffc00

def z1098 : W := mkw 0x00ffe6d6a2090007 0x401ffcdad4412000 0x2efb8fe70f0f0005 0x85df71fce1e1e000

def z1099 : W := mkw 0x805d44d224d48004 0x300ba89a449a9000 0xffff4fff3ffe8007 0xffffe9ffe7ffd000

def z1100 : W := mkw 0x60540db00db01e00 0x2c0a81b601b603c0 0xffff0fff0ff01f03 0xffffe1ffe1fe03e0

def z1101 : W := mkw 0x70228b258b2b1cc1 0x0e045164b1656398 0xef638f07cfef1ce7 0xddec71e0f9fde39c

def z1102 : W := mkw 0xf800092109669e90 0x1f000124212cd3d2 0x0100000008ee9f9e 0x80200000011dd3f3

def z1103 : W := mkw 0x00ffe6d6a0000007 0x401ffcdad4000000 0x24fbffe700000000 0x049f7ffce0000000

def z1104 : W := mkw 0x60540db00db01e00 0x2c0a81b601b603c0 0x1ffc0ff80ff00703 0xa3ff81ff01fe00e0

def z1105 : W := mkw 0x80fff6def4d4c007 0xf01ffedbde9a9800 0xfffffffff0f1e007 0xfffffffffe1e3c00

def z1106 : W := mkw 0x000004d220000000 0x0000009a44000000 0xc0800fff30000000 0x781001ffe6000000

def z1107 : W := mkw 0x60540db00db01e00 0x2c0a81b601b603c0 0x05fc0ff80ff00300 0x00bf81ff01fe0060

def z1108 : W := mkw 0x50228b058b0b18c1 0x0a045160b1616318 0xa8638707cf0f18e5 0xd50c70e0f9e1e31c

def z1109 : W := mkw 0xf809486328669494 0x1f01290c650cd292 0x779bc8e7f8ef94fe 0xeef3791cff1df29f

def z1110 : W := mkw 0x005d54da70000004 0x800baa9b4e000000 0xfefffffff0000000 0x7fdffffffe000000

def z1111 : W := mkw 0x60540db00db01e00 0x2c0a81b601b603c0 0xfffcfff80ff01f03 0xbfff9fff01fe03e0

def z1112 : W := mkw 0x00fff6def6994007 0xe01ffedbded32800 0xfefffffff7000000 0x7fdffffffee00000

def z1113 : W := mkw 0x807fe00006ddc006 0x300ffc0000dbb800 0x0d7fb0000fffe007 0x81aff60001fffc00

def z1114 : W := mkw 0x807fe00006ddc006 0x300ffc0000dbb800 0x311ff0000fffe007 0x8623fe0001fffc00

def z1115 : W := mkw 0x205404b004b00600 0x240a8096009600c0 0xdffc0ff80ff00703 0xbbff81ff01fe00e0

def z1116 : W := mkw 0x80fff6def24dc007 0xd01ffedbde49b800 0xfefffffff00e0000 0x7fdffffffe01c000

def z1117 : W := mkw 0xf80009210df69e90 0x3f00012421bed3d2 0x010000000fee0000 0x0020000001fdc000

def z1118 : W := mkw 0x807fe20486ddc007 0x300ffc4090dbb800 0x3f7fff070fffe007 0x87efffe0e1fffc00

def z1119 : W := mkw 0xf80009210b6f9cd0 0x1f000124216df39a 0xfb00c000ffef9cff 0xff6018001ffdf39f

def z1120 : W := mkw 0x74001fbdd9223fe9 0x8e8003f7bb2447fd 0xc0800ffff0001ff8 0x781001fffe0003ff

def z1121 : W := mkw 0x00ffe6d6a0000007 0x401ffcdad4000000 0x0cffbfe700000000 0x019ff7fce0000000

def z1122 : W := mkw 0x807fe00006ddc006 0x300ffc0000dbb800 0x7f7ff0000ffff087 0xcfeffe0001fffe10

def z1123 : W := mkw 0xf80009210df69e90 0x3f00012421bed3d2 0x010000000fee949e 0x8020000001fdd293

def z1124 : W := mkw 0xf809496329669e94 0x1f01292c652cd3d2 0x779b48e738ee9f9e 0xeef3691ce71dd3f3

def z1125 : W := mkw 0x805d600006ddc006 0x300bac0000dbb800 0x3b1cf0000fffe007 0x87639e0001fffc00

def z1126 : W := mkw 0x50228b058b0b18c1 0x0a045160b1616318 0xfe67ff1fcf1fffe7 0xffccffe3f9e3fffc

def z1127 : W := mkw 0x700009210b2b1ec0 0x0e000124216563d8 0x000000000f0f1fe5 0x8000000001e1e3fc

def z1128 : W := mkw 0x50000b05890218c1 0x0a000160b1204318 0xee630f07cf0e18e5 0xddcc61e0f9e1c31c

def z1129 : W := mkw 0x60540db00db01e00 0x2c0a81b601b603c0 0x15fc0ff80ff01f03 0xa2bf81ff01fe03e0

def z1130 : W := mkw 0x00fff6def2090007 0xc01ffedbde412000 0xfeffffffff1fe007 0xffdfffffffe3fc00

def z1131 : W := mkw 0xf80009210b6f9cd0 0x1f000124216df39a 0x010000000fee0000 0x0020000001fdc000

def z1132 : W := mkw 0x802bc246a24d8005 0x10057848d449b000 0xfffbcfe7ffef8007 0xffff79fcfffdf000

def z1133 : W := mkw 0x805d600006ddc006 0x300bac0000dbb800 0x111c70000ffee002 0x02238e0001ffdc00

def z1134 : W := mkw 0xe0ffeff6affdde07 0x7c1ffdfed5ffbbc0 0xffffffff0fffff07 0xbfffffffe1ffffe0

def z1135 : W := mkw 0xf80009210b6f9cd0 0x1f000124216df39a 0x010000000fee949e 0x8020000001fdd293

def z1136 : W := mkw 0x80fff6def6ddc007 0xf01ffedbdedbb800 0xffffffffffee8006 0xfffffffffffdd000

def z1137 : W := mkw 0x60540db00db01e00 0x2c0a81b601b603c0 0x05f80ff80fe00700 0x20bf01ff01fc00e0

def z1138 : W := mkw 0x60540db00db01e00 0x2c0a81b601b603c0 0xfffccff8fff19fff 0xffff99ff1ffe33ff

def z1139 : W := mkw 0xf809496329669c94 0x1f01292c652cd392 0xffff4fff3ffe9f9f 0xffffe9ffe7ffd3f3

def z1140 : W := mkw 0x00fff6def0000007 0xc01ffedbde000000 0xd4ff7ffff0000000 0x7a9feffffe000000

def z1141 : W := mkw 0x04fff6def000212f 0xc09ffedbde000425 0xfefffffff011e71f 0xffdffffffe023ce3

def z1142 : W := mkw 0x00ffe6d6a0000007 0x401ffcdad4000000 0x76fb4fe73000949e 0xeedf69fce6001293

def z1143 : W := mkw 0x50228b058b0b18c1 0x0a045160b1616318 0xee638f07cf0f9cff 0xddcc71e0f9e1f39f

def z1144 : W := mkw 0x807fe00006ddc006 0x300ffc0000dbb800 0xbf7ff0180fffeb07 0x97effe0301fffd60

def z1145 : W := mkw 0x04fff6def000212f 0xc09ffedbde000425 0x14ff7fff3010e71a 0x229fefffe6021ce3

def z1146 : W := mkw 0x008006d6a0000001 0x401000dad4000000 0xc0800fff00000000 0x381001ffe0000000

def z1147 : W := mkw 0x04abf6def000212f 0xc0957edbde000425 0xfa87fffff011ffff 0xff50fffffe023fff

def z1148 : W := mkw 0x00fff6def0000007 0xc01ffedbde000000 0x76ff7fff30000000 0x6edfefffe6000000

def z1149 : W := mkw 0x048956def000212d 0xc0912adbde000425 0xfe9ffffff011ffff 0xffd3fffffe023fff

def z1150 : W := mkw 0xf809486328669494 0x1f01290c650cd292 0x059b48e738ee8018 0x00b3691ce71dd003

def z1151 : W := mkw 0x8076a00006ddc002 0x300ed40000dbb800 0x1f7cb0000fffe007 0x83ef960001fffc00

def z1152 : W := mkw 0x00fff6def4900207 0xe01ffedbde920040 0xfefffffff0100300 0x7fdffffffe020060

def z1153 : W := mkw 0x10228205820b00c1 0x02045040b0416018 0xee638f07cf0f00e5 0xddcc71e0f9e1e01c

def z1154 : W := mkw 0x84dd74da74d4e12e 0xf09bae9b4e9a9c25 0x119c70f830f0e71a 0x22338e1f061e1ce3

def z1155 : W := mkw 0x008016def0000001 0xc01002dbde000000 0xf2804ffff000949e 0xfe5009fffe001293

def z1156 : W := mkw 0x700009210fbb1ec0 0x2e00012421f763d8 0x010000000ffe1f03 0x8020000001ffc3e0

def z1157 : W := mkw 0x00fff6def6994007 0xe01ffedbded32800 0xfefffffff711e007 0xffdffffffee23c00

def z1158 : W := mkw 0x0400100850002128 0x808002010a000425 0xd804f018f011fffb 0x7b009e031e023fff

def z1159 : W := mkw 0x04fff6def000212f 0xc09ffedbde000425 0xfefffffff010f79e 0xffdffffffe021ef3

def z1160 : W := mkw 0x80fff6def6ddc007 0xf01ffedbdedbb800 0xc5fb0fffffee0000 0x78bf61fffffdc000

def z1161 : W := mkw 0x80fff6def6ddc007 0xf01ffedbdedbb800 0xffffffffffffff07 0xffffffffffffffe0

def z1162 : W := mkw 0x04d416def0002129 0xc09a82dbde000425 0xfefcfffff011ffff 0xffdf9ffffe023fff

def z1163 : W := mkw 0xf809496329669c94 0x1f01292c652cd392 0x779b48e73fee9c9f 0xeef3691ce7fdd393

def z1164 : W := mkw 0x00fff6def2090007 0xc01ffedbde412000 0xfeffffffff0e0000 0x7fdfffffffe1c000

def z1165 : W := mkw 0x50228b058b0b18c1 0x0a045160b1616318 0xfe678f1fcf0f18e5 0xffccf1e3f9e1e31c

def z1166 : W := mkw 0x50228b058b0b18c1 0x0a045160b1616318 0xee63cf07ff0f98fd 0xddcc79e0ffe1f31f

def z1167 : W := mkw 0x00ffe6d6a0000007 0x401ffcdad4000000 0x36fb4fe700000000 0x06df69fce0000000

def z1168 : W := mkw 0x008016def0000001 0xc01002dbde000000 0x80800fffc0000000 0x101001fff8000000

def z1169 : W := mkw 0x04fff6def490212f 0xe09ffedbde920425 0xfffffffffff1ffff 0xfffffffffffe3fff

def z1170 : W := mkw 0x84fff6def24de12f 0xd09ffedbde49bc25 0xfefffffff01fffff 0xffdffffffe03ffff

def z1171 : W := mkw 0xf00009210fffdec0 0x3e00012421fffbd8 0x010000000fffffe7 0x8020000001fffffc

def z1172 : W := mkw 0x6000092009201e00 0x0c000124012403c0 0xc000001800001f00 0x38000003000003e0

def z1173 : W := mkw 0x00d416def0000001 0xc01a82dbde000000 0xd09c0ffff0000000 0x7a1381fffe000000

def z1174 : W := mkw 0x00ffe6d6a0000007 0x401ffcdad4000000 0x3effffe70011e007 0x87dffffce0023c00

def z1175 : W := mkw 0x802be00006ddc006 0x30057c0000dbb800 0x2f63f0000fffe007 0x85ec7e0001fffc00

def z1176 : W := mkw 0x807fe00006ddc006 0x300ffc0000dbb800 0x2d7ff0000fffe005 0x05affe0001fffc00

def z1177 : W := mkw 0x807fe00006ddc006 0x300ffc0000dbb800 0x7f7ff0003fffe007 0xefeffe0007fffc00

def z1178 : W := mkw 0x0022820480000001 0x0004504090000000 0xfefb8fe7c0000000 0x7fdf71fcf8000000

def z1179 : W := mkw 0x700009210db21e80 0x2e00012421b643d0 0x010000000ffe1f87 0x8020000001ffc3f0

def z1180 : W := mkw 0x807fe00006ddc006 0x300ffc0000dbb800 0x197cf0000fffe007 0x832f9e0001fffc00

def z1181 : W := mkw 0x00fff6def0000007 0xc01ffedbde000000 0xfefffffff0100003 0xffdffffffe020000

def z1182 : W := mkw 0x10228305830b08c1 0x02045060b0616118 0xea638707c70f18e5 0xdd4c70e0f8e1e31c

def z1183 : W := mkw 0x00ffe6d6a0000007 0x401ffcdad4000000 0x1eff0fe700000000 0x03dfe1fce0000000

def z1184 : W := mkw 0x8000000006ddc000 0x3000000000dbb800 0x110470000fffe007 0x82208e0001fffc00

def z1185 : W := mkw 0x60540db00db01e00 0x2c0a81b601b603c0 0xdffc7ff80ff0ff03 0xbbff8fff01fe1fe0

def z1186 : W := mkw 0x84fff6def6dde12f 0xf09ffedbdedbbc25 0xffffffffffffeb67 0xfffffffffffffd6c

def z1187 : W := mkw 0x04fff6def000212f 0xc09ffedbde000425 0xfefffffff0000b60 0x7fdffffffe00016c

def z1188 : W := mkw 0x0400100850002128 0x808002010a000425 0xfe64ff18f011ffff 0xffcc9fe31e023fff

def z1189 : W := mkw 0x84abf24ef24de12f 0xd0957e49de49bc25 0x2003f007f00fe0fc 0x44007e00fe01fc1f

def z1190 : W := mkw 0x008946d6a0000005 0x401128dad4000000 0x769b4fe730000000 0x6ed369fce6000000

def z1191 : W := mkw 0x802be000024dc006 0x10057c000049b800 0x3f7bf0000fefe007 0x87ef7e0001fdfc00

def z1192 : W := mkw 0x00f6b6def0000003 0xc01ed6dbde000000 0xdefcbffff0000000 0x7bdf97fffe000000

def z1193 : W := mkw 0x04fff6def000212f 0xc09ffedbde000425 0xfefffffff011eb67 0xffdffffffe023d6c

def z1194 : W := mkw 0x00ffe6d6a4900007 0x601ffcdad4920000 0x1fff0fe70ff00003 0x83ffe1fce1fe0000

def z1195 : W := mkw 0x008006d6a0000001 0x401000dad4000000 0xc0800fe7c0000000 0x581001fcf8000000

def z1196 : W := mkw 0x807fe04226ddc006 0x300ffc0844dbb800 0x3ffff0e03fffe007 0xa7fffe1c07fffc00

def z1197 : W := mkw 0x807fe00006ddc006 0x300ffc0000dbb800 0x1f7f70000ffee003 0x83efee0001ffdc00

def z1198 : W := mkw 0x00ffe6d6a0000007 0x401ffcdad4000000 0x24fb8fe7c0000000 0x449f71fcf8000000

def z1199 : W := mkw 0x00fff6def2090047 0xc01ffedbde412008 0xfefffffff0010060 0x7fdffffffe00200c

def z1200 : W := mkw 0x04fff6def000212f 0xc09ffedbde000425 0xfefffffff011ef7b 0x7fdffffffe023def

def z1201 : W := mkw 0x807fe00006ddc006 0x300ffc0000dbb800 0x3f7ff0000fffff07 0x87effe0001ffffe0

def z1202 : W := mkw 0x00fff6def0000007 0xc01ffedbde000000 0xdeff7fff30000000 0x3bdfefffe6000000

def z1203 : W := mkw 0x00f6b6def0000003 0xc01ed6dbde000000 0xfae4fffff0000000 0x7f5c9ffffe000000

def z1204 : W := mkw 0x80fff6def0448007 0xd01ffedbde089000 0xfefffffff00e8004 0x7fdffffffe01d000

def z1205 : W := mkw 0x00fff6def4900007 0xe01ffedbde920000 0xfffffffff0f00002 0x7ffffffffe1e0000

def z1206 : W := mkw 0x80fff6def6ddc007 0xf01ffedbdedbb800 0xfffffffff7f1e003 0x7ffffffffefe3c00

def z1207 : W := mkw 0x002bc246a0000005 0x00057848d4000000 0xfefbcfe7f0019cff 0xffdf79fcfe00339f

def z1208 : W := mkw 0x04fff6def699612f 0xe09ffedbded32c25 0xfefffffff7116b61 0x7fdffffffee22d6c

def z1209 : W := mkw 0x00fff6def0000007 0xc01ffedbde000000 0x04fbbfe7c0000000 0x009f77fcf8000000

def z1210 : W := mkw 0x0400100850002128 0x808002010a000425 0xfe64f018ff11ffff 0xffcc9e031fe23fff

def z1211 : W := mkw 0x700009210fbb1ec0 0x2e00012421f763d8 0xfb048018cfff1fe7 0xff60900319ffe3fc

def z1212 : W := mkw 0x50228b058b0b18c1 0x0a045160b1616318 0xce630f07cf0e18e1 0xd9cc61e0f9e1c31c

def z1213 : W := mkw 0x8022800006ddc000 0x3004500000dbb800 0x3f67f0000fffe007 0x87ecfe0001fffc00

def z1214 : W := mkw 0xb809406320668494 0x1701280c640cd092 0x119b40e730ee841a 0x2233681ce61dd083

def z1215 : W := mkw 0x80ffe6d6a24dc007 0x501ffcdad449b800 0x04fb0fe7000e0000 0x009f61fce001c000

def z1216 : W := mkw 0x205405b005b00e00 0x240a80b600b601c0 0x89fc07f807f00b01 0x113f80ff00fe0160

def z1217 : W := mkw 0x04fff6def000212f 0xc09ffedbde000425 0xfefffffff010fffa 0x7fdffffffe021fff

def z1218 : W := mkw 0x50228b058b0b18c1 0x0a045160b1616318 0xe8638f07c70f18e5 0x5d0c71e0f8e1e31c

def z1219 : W := mkw 0x00fff6def0000007 0xc01ffedbde000000 0xfefffffff011f8e7 0xffdffffffe023f1c

def z1220 : W := mkw 0x805d600004d4c006 0x300bac00009a9800 0x3f7f70000ffee007 0x87efee0001ffdc00

def z1221 : W := mkw 0x002bc246a0000005 0x00057848d4000000 0x04fb0fe700000000 0x009f61fce0000000

def z1222 : W := mkw 0x60540db00db01e00 0x2c0a81b601b603c0 0xcdfc0ff80ff01f01 0x39bf81ff01fe03e0

def z1223 : W := mkw 0x00dd76def0000007 0xc01baedbde000000 0xdefc7ffff0000000 0x7bdf8ffffe000000

def z1224 : W := mkw 0x0076869480000001 0x000ed0d290000000 0x04fb0fe700000000 0x009f61fce0000000

def z1225 : W := mkw 0x807fe00006ddc006 0x300ffc0000dbb800 0x3f7ff0000ffee002 0x07effe0001ffdc00

def z1226 : W := mkw 0x00fff6def0000007 0xc01ffedbde000000 0xf09ffffff0000000 0x7e13fffffe000000

def z1227 : W := mkw 0x60540db00db01e00 0x2c0a81b601b603c0 0xffff0ff80ffe1f07 0xbfffe1ff01ffc3e0

def z1228 : W := mkw 0x807fe00006ddc006 0x300ffc0000dbb800 0x3f7ff0000fefe004 0x07effe0001fdfc00

def z1229 : W := mkw 0x00fff6def0000007 0xc01ffedbde000000 0xfefffffff0010861 0x7fdffffffe00210c

def z1230 : W := mkw 0x00fff6def0000007 0xc01ffedbde000000 0xacfffffff0000000 0x559ffffffe000000

def z1231 : W := mkw 0x00f6b6def0000003 0xc01ed6dbde000000 0xc0e00ffff0000000 0x781c01fffe000000

def z1232 : W := mkw 0x00fff6def6994007 0xe01ffedbded32800 0xfeffffffff1f6005 0xffdfffffffe3ec00

def z1233 : W := mkw 0xf809486328669494 0x1f01290c650cd292 0x159b48e738ee949e 0xa2b3691ce71dd293

def z1234 : W := mkw 0x700009210fbb1ec0 0x2e00012421f763d8 0x010000000fee0000 0x0020000001fdc000

def z1235 : W := mkw 0x807fe00006ddc006 0x300ffc0000dbb800 0x7f7ff8070fffe007 0xcfefff00e1fffc00

def z1236 : W := mkw 0x807fe20486ddc047 0x300ffc4090dbb808 0x3f7ff000cfffe067 0x87effe0019fffc0c

def z1237 : W := mkw 0xf80009210fffdcd0 0x3f00012421fffb9a 0x010000000ffffcff 0x8020000001ffff9f

def z1238 : W := mkw 0x00fff6def0000007 0xc01ffedbde000000 0xe8e7fffff0000000 0x7d1cfffffe000000

def z1239 : W := mkw 0x807fe04226ddc006 0x300ffc0844dbb800 0x7ffff8e73ffff49f 0xefffff1ce7fffe93

def z1240 : W := mkw 0x807fe00006ddc006 0x300ffc0000dbb800 0xff7ff0183fffff9f 0xffeffe0307fffff3

def z1241 : W := mkw 0x00d416def0000001 0xc01a82dbde000000 0xc4f80ffff0000000 0x789f01fffe000000

def z1242 : W := mkw 0x10228305830b08c1 0x02045060b0616118 0xae638707cf0f08e5 0xd5cc70e0f9e1e11c

def z1243 : W := mkw 0x80fff6def24dc007 0xd01ffedbde49b800 0xfeffffffff0fe005 0xffdfffffffe1fc00

def z1244 : W := mkw 0x0054049000000000 0x000a809200000000 0xfeff0fff00000000 0x7fdfe1ffe0000000

def z1245 : W := mkw 0x00ffe6d6a0000007 0x401ffcdad4000000 0x8cfb8fe7c0000000 0x119f71fcf8000000

def z1246 : W := mkw 0x00fff6def0000007 0xc01ffedbde000000 0xfefffffff0116001 0x7fdffffffe022c00

def z1247 : W := mkw 0x00ffe6d6a0000007 0x401ffcdad4000000 0x56fb0fe700000000 0x2adf61fce0000000

def z1248 : W := mkw 0x00fff6def0000007 0xc01ffedbde000000 0xfefffffff0001402 0xffdffffffe000280

def z1249 : W := mkw 0x04fff6def000212f 0xc09ffedbde000425 0xfefffffff010ff1b 0xffdffffffe021fe3

def z1250 : W := mkw 0x005d44d220000004 0x000ba89a44000000 0xfeff4fff30109f9f 0xffdfe9ffe60213f3

def z1251 : W := mkw 0x780009210b2b1cd0 0x0f0001242165639a 0x000000000f0f1cfd 0x8000000001e1e39f

def z1252 : W := mkw 0x60540db00db01e00 0x2c0a81b601b603c0 0xfffc8ff80ff11f07 0xbfff91ff01fe23e0

def z1253 : W := mkw 0x00fff6def0000007 0xc01ffedbde000000 0xfefffffff00018e0 0x7fdffffffe00031c

def z1254 : W := mkw 0x00dd76def0000007 0xc01baedbde000000 0xc0980ffff0000000 0x781301fffe000000

def z1255 : W := mkw 0x00ffe6d6a0000007 0x401ffcdad4000000 0x2efb8fe700000000 0x05df71fce0000000

def z1256 : W := mkw 0x50228b058b0b18c1 0x0a045160b1616318 0x24638f07cf0f18e5 0xc48c71e0f9e1e31c

def z1257 : W := mkw 0x60540db00db01e00 0x2c0a81b601b603c0 0xfffcfff83ff1ff9f 0xffff9fff07fe3ff3

def z1258 : W := mkw 0xac5d54fa74f4a73c 0xb58baa9f4e9e94e7 0x119c70f830f0e71a 0x22338e1f061e1ce3

def z1259 : W := mkw 0x04fff6def000212f 0xc09ffedbde000425 0xfefffffff011ebfd 0x7fdffffffe023d7f

def z1260 : W := mkw 0x048016def0002129 0xc09002dbde000425 0xc884bffff0116b61 0x791097fffe022d6c

def z1261 : W := mkw 0x00fff6def0000007 0xc01ffedbde000000 0xfefffffff0100b01 0x7fdffffffe020160

def z1262 : W := mkw 0x00dd76def0000007 0xc01baedbde000000 0x109c7fff30000000 0x22138fffe6000000

def z1263 : W := mkw 0xf809486328669494 0x1f01290c650cd292 0x779b48e738fff49f 0xeef3691ce71ffe93

def z1264 : W := mkw 0x0000069480000001 0x000000d290000000 0xc0800fffc0000000 0x781001fff8000000

def z1265 : W := mkw 0x002bc246a0000005 0x00057848d4000000 0xeefb8fe7c0000000 0x5ddf71fcf8000000

def z1266 : W := mkw 0x00d416def0000001 0xc01a82dbde000000 0xc8e40ffff0000000 0x791c81fffe000000

def z1267 : W := mkw 0x0076869480000001 0x000ed0d290000000 0xeefb8fe7c0000000 0x5ddf71fcf8000000

def z1268 : W := mkw 0x70228b258b2b1cc1 0x0e045164b1656398 0xffff8fffcfff1fe7 0xfffff1fff9ffe3fc

def z1269 : W := mkw 0x008016def0000001 0xc01002dbde000000 0xe6830ffff0000000 0x7cd061fffe000000

def z1270 : W := mkw 0x60540db00db01e00 0x2c0a81b601b603c0 0xfffc8ff8cff01f03 0xffff91ff19fe03e0

def z1271 : W := mkw 0x00ffe6d6a0000007 0x401ffcdad4000000 0xfeff4fff30000000 0x7fdfe9ffe6000000

def z1272 : W := mkw 0x048016def0002129 0xc09002dbde000425 0xc0800ffff00000f8 0x781001fffe00001f

def z1273 : W := mkw 0x04fff6def000212f 0xc09ffedbde000425 0xfefffffff0009ffe 0xffdffffffe0013ff

def z1274 : W := mkw 0x00d416def4900001 0xe01a82dbde920000 0xdffc0ffffff00003 0xfbff81fffffe0000

def z1275 : W := mkw 0x04a296def0002129 0xc09452dbde000425 0xeee38ffff0011ffd 0xfddc71fffe0023ff

def z1276 : W := mkw 0x0054049004900000 0x200a809200920000 0x1ffc0fe00ff00003 0x83ff81fc01fe0000

def z1277 : W := mkw 0xb809406320668494 0x1701280c640cd092 0x219b40e730ee809c 0x4433681ce61dd013

def z1278 : W := mkw 0x84fff6def24de12f 0xd09ffedbde49bc25 0xfefffffff00fe0fc 0x7fdffffffe01fc1f

def z1279 : W := mkw 0x80dd64d224d4c006 0x701bac9a449a9800 0x119c70e000f0e002 0x02338e1c001e1c00

def z1280 : W := mkw 0x50228b058b0b18c1 0x0a045160b1616318 0xee638f07ff0f1cfd 0xfdcc71e0ffe1e39f

def z1281 : W := mkw 0x008956def0000005 0xc0112adbde000000 0xd0984ffff0000000 0x7a1309fffe000000

def z1282 : W := mkw 0x80ffe6d6a6ddc007 0x701ffcdad4dbb800 0xdfff0fff0ffe0003 0xbbffe1ffe1ffc000

def z1283 : W := mkw 0x00d436def0000003 0xc01a86dbde000000 0xc0843ffff0000000 0x781087fffe000000

def z1284 : W := mkw 0x50228b058b0b18c1 0x0a045160b1616318 0x84630f07cf0e0860 0x108c61e0f9e1c10c

def z1285 : W := mkw 0x807fe00006ddc006 0x300ffc0000dbb800 0x157f70000fffe007 0x82afee0001fffc00

def z1286 : W := mkw 0xf809486328669494 0x1f01290c650cd292 0x319b40e738ee949e 0xe633681ce71dd293

def z1287 : W := mkw 0xf809486328669494 0x1f01290c650cd292 0x7f9ff8e738ee949e 0xeff3ff1ce71dd293

def z1288 : W := mkw 0x807fe00006ddc006 0x300ffc0000dbb800 0xbf7ff000cfffe867 0x97effe0019fffd0c

def z1289 : W := mkw 0x60540db00db01e00 0x2c0a81b601b603c0 0xcffc0ff80ff01b01 0x99ff81ff01fe0360

def z1290 : W := mkw 0x50228b058b0b18c1 0x0a045160b1616318 0xee678f1fcf1f1be5 0xddccf1e3f9e3e37c

def z1291 : W := mkw 0x807fe00006ddc006 0x300ffc0000dbb800 0x057b70000feee000 0x00af6e0001fddc00

def z1292 : W := mkw 0x80fff6def6ddc007 0xf01ffedbdedbb800 0x15ff7fff3ffee002 0x22bfefffe7ffdc00

def z1293 : W := mkw 0xf809496329669c94 0x1f01292c652cd392 0xfffbcfe7ffef9cff 0xffff79fcfffdf39f

def z1294 : W := mkw 0x04fff6def699612f 0xe09ffedbded32c25 0xfefffffff711ffff 0xffdffffffee23fff

def z1295 : W := mkw 0x00fff6def0000007 0xc01ffedbde000000 0xe4fbfffff0000000 0x7c9f7ffffe000000

def z1296 : W := mkw 0x80fff6def044c007 0xd01ffedbde089800 0xfefffffff000e000 0x7fdffffffe001c00

def z1297 : W := mkw 0xf87fe9210fffde96 0x3f0ffd2421fffbd2 0x3f7ff0000fffff9f 0x87effe0001fffff3

def z1298 : W := mkw 0x80fff6def24dc007 0xd01ffedbde49b800 0xfffffffff8efe006 0xffffffffff1dfc00

def z1299 : W := mkw 0x04abf6def000212f 0xc0957edbde000425 0xe083fffff001fffc 0x7c107ffffe003fff

def z1300 : W := mkw 0x00fff6def0000007 0xc01ffedbde000000 0xfffffffff8e00002 0xffffffffff1c0000

def z1301 : W := mkw 0x80ffe6d6a6ddc007 0x701ffcdad4dbb800 0x77fb4fe73fee8006 0xeeff69fce7fdd000

def z1302 : W := mkw 0x00d416def0000001 0xc01a82dbde000000 0xfefcfffff0000000 0x7fdf9ffffe000000

def z1303 : W := mkw 0x807fe00006ddc006 0x300ffc0000dbb800 0xff7ff000fffffcff 0xffeffe001fffff9f

def z1304 : W := mkw 0x50228b058b0b18c1 0x0a045160b1616318 0x04638f07cf0f0060 0x008c71e0f9e1e00c

def z1305 : W := mkw 0x00dd76def0000007 0xc01baedbde000000 0xfa9cfffff0000000 0x7f539ffffe000000

def z1306 : W := mkw 0x00ffe6d6a4900007 0x601ffcdad4920000 0x05fb0fe70fe00000 0x00bf61fce1fc0000

def z1307 : W := mkw 0x0076869480000001 0x000ed0d290000000 0xfeff8fffc0111fe7 0xffdff1fff80223fc

def z1308 : W := mkw 0xf809486328669494 0x1f01290c650cd292 0x679b08e738ee149c 0xecf3611ce71dc293

def z1309 : W := mkw 0xf809486328669494 0x1f01290c650cd292 0x7ffb48e73fee949f 0xefff691ce7fdd293

def z1310 : W := mkw 0x00094246a0000005 0x00012848d4000000 0xf69b4fe7f0000000 0x7ed369fcfe000000

def z1311 : W := mkw 0x50228b058b0b18c1 0x0a045160b1616318 0xfe67cf1fff1f9fff 0xffccf9e3ffe3f3ff

def z1312 : W := mkw 0x005d44d220000004 0x000ba89a44000000 0x76fb4fe730000000 0x6edf69fce6000000

def z1313 : W := mkw 0x00fff6def0000007 0xc01ffedbde000000 0xccffbffff0000000 0x799ff7fffe000000

def z1314 : W := mkw 0xf80968632866d496 0x1f012d0c650cda92 0x779b78e738eef49e 0xeef36f1ce71dde93

def z1315 : W := mkw 0x50228b058b0b18c1 0x0a045160b1616318 0xfe67ff07cf0f18e5 0xdfccffe0f9e1e31c

def z1316 : W := mkw 0x04fff6def000212f 0xc09ffedbde000425 0xfefffffff0117ff9 0x7fdffffffe022fff

def z1317 : W := mkw 0x807fe00006ddc006 0x300ffc0000dbb800 0xff7ff0180fffe007 0xbfeffe0301fffc00

def z1318 : W := mkw 0x008016def0000001 0xc01002dbde000000 0xd0847ffff0000000 0x7a108ffffe000000

def z1319 : W := mkw 0x00fff6def0000007 0xc01ffedbde000000 0x34fffffff0000000 0x669ffffffe000000

def z1320 : W := mkw 0x807fe00006ddc006 0x300ffc0000dbb800 0x357ff0000fffe006 0x06affe0001fffc00

def z1321 : W := mkw 0x00fff6def0000007 0xc01ffedbde000000 0xfefffffff0010005 0xffdffffffe002000

def z1322 : W := mkw 0xf809486328669494 0x1f01290c650cd292 0x559b48e738ee949a 0x6ab3691ce71dd293

def z1323 : W := mkw 0x000944d220000004 0x0001289a44000000 0xf69b4fff30000000 0x7ed369ffe6000000

def z1324 : W := mkw 0x60540db00db01e00 0x2c0a81b601b603c0 0xcff80ff80fe01f01 0xb9ff01ff01fc03e0

def z1325 : W := mkw 0x0400100850002128 0x808002010a000425 0xff1cf018f8f1ffff 0xffe39e031f1e3fff

def z1326 : W := mkw 0xf809486328669494 0x1f01290c650cd292 0x779b48e738ee809c 0x6ef3691ce71dd013

def z1327 : W := mkw 0xf809486328669494 0x1f01290c650cd292 0x059b08e738ee0098 0x40b3611ce71dc013

def z1328 : W := mkw 0x04fff6def000212f 0xc09ffedbde000425 0xfefffffff0117f63 0xffdffffffe022fec

def z1329 : W := mkw 0x60540db00db01e00 0x2c0a81b601b603c0 0xdffc0ff80ff1ff07 0xbbff81ff01fe3fe0

def z1330 : W := mkw 0x04fff6def000212f 0xc09ffedbde000425 0xfefffffff000e018 0x7fdffffffe001c03

def z1331 : W := mkw 0x04fff6def000212f 0xc09ffedbde000425 0xc4fb0ffff0001ff8 0x789f61fffe0003ff

def z1332 : W := mkw 0x60540db00db01e00 0x2c0a81b601b603c0 0xdffc0ff80ff00702 0x3bff81ff01fe00e0

def z1333 : W := mkw 0x00fff6def0000007 0xc01ffedbde000000 0xfefffffff0001f00 0x7fdffffffe0003e0

def z1334 : W := mkw 0x50228b058b0b18c1 0x0a045160b1616318 0xae638f07cf0f0865 0x95cc71e0f9e1e10c

def z1335 : W := mkw 0xd0ffefd7afdfd8c7 0x7a1ffdfaf5fbfb18 0xffffffe7cffff8e7 0xdffffffcf9ffff1c

def z1336 : W := mkw 0xf809486328669494 0x1f01290c650cd292 0x379b48e738ee809e 0xc6f3691ce71dd013

def z1337 : W := mkw 0x80fff6def0448007 0xd01ffedbde089000 0xfffffffff8ee0000 0x7fffffffff1dc000

def z1338 : W := mkw 0x5022ab058b0b58c3 0x0a045560b1616b18 0xee63bf07cf0f78e5 0xddcc77e0f9e1ef1c

def z1339 : W := mkw 0x80abe246a24dc007 0x50157c48d449b800 0x2003f007000fe004 0x04007e00e001fc00

def z1340 : W := mkw 0x00fff6def4900007 0xe01ffedbde920000 0xfffffffffff01f03 0xfffffffffffe03e0

def z1341 : W := mkw 0x80fff6def0448007 0xd01ffedbde089000 0xfffffffff8ee949e 0xffffffffff1dd293

def z1342 : W := mkw 0x00fff6def0000007 0xc01ffedbde000000 0xfefffffff0001084 0xffdffffffe000210

def z1343 : W := mkw 0x00a286d6a0000001 0x401450dad4000000 0x04e30fe700000000 0x009c61fce0000000

def z1344 : W := mkw 0x00a296def0000001 0xc01452dbde000000 0xc8e08ffff0000000 0x791c11fffe000000

def z1345 : W := mkw 0x205405b005b00e00 0x240a80b600b601c0 0xdbfc07f807f01f03 0xbb7f80ff00fe03e0

def z1346 : W := mkw 0x80ffe6d6a0448007 0x501ffcdad4089000 0x05fb0fe708ee0000 0x00bf61fce11dc000

def z1347 : W := mkw 0x00abe6d6a0000007 0x40157cdad4000000 0x00830fe700000000 0x001061fce0000000

def z1348 : W := mkw 0x00fff6def0000007 0xc01ffedbde000000 0x04fb7fe730000000 0x009f6ffce6000000

def z1349 : W := mkw 0x60540db00db01e00 0x2c0a81b601b603c0 0xd5fc0ff80ff01f02 0x3abf81ff01fe03e0

def z1350 : W := mkw 0x048016def0002129 0xc09002dbde000425 0xc0800ffff0000718 0x781001fffe0000e3

def z1351 : W := mkw 0x00fff6def4900007 0xe01ffedbde920000 0xfefffffff7100001 0x7fdffffffee20000

def z1352 : W := mkw 0x50228b058b0b18c1 0x0a045160b1616318 0xac638f07cf0f08e5 0x558c71e0f9e1e11c

def z1353 : W := mkw 0x50228b058b0b18c1 0x0a045160b1616318 0xfefb8fe7cf0f18e5 0xffdf71fcf9e1e31c

def z1354 : W := mkw 0x50228b058b0b18c1 0x0a045160b1616318 0xfe678f07cf1f18e7 0xdfccf1e0f9e3e31c

def z1355 : W := mkw 0x00fff6def0000007 0xc01ffedbde000000 0xf6fb4ffff0000000 0x7edf69fffe000000

def z1356 : W := mkw 0x045d54da7000212c 0x808baa9b4e000425 0xfefffffff011ffff 0xffdffffffe023fff

def z1357 : W := mkw 0x807fe00006ddc006 0x300ffc0000dbb800 0x7f7ff0000ffff407 0xafeffe0001fffe80

def z1358 : W := mkw 0xb809406320668494 0x1701280c640cd092 0x379b40e738ee849e 0xe6f3681ce71dd093

def z1359 : W := mkw 0x00a2b6def0000003 0xc01456dbde000000 0xc080bffff0000000 0x781017fffe000000

def z1360 : W := mkw 0x60540db00db01e00 0x2c0a81b601b603c0 0xfffc4ff83ff01f03 0xffff89ff07fe03e0

def z1361 : W := mkw 0x00f696def0000001 0xc01ed2dbde000000 0xfeff8ffff0000000 0x7fdff1fffe000000

def z1362 : W := mkw 0x0400100850002128 0x808002010a000425 0xa804f018f011ffff 0xd5009e031e023fff

def z1363 : W := mkw 0x00fff6def0000007 0xc01ffedbde000000 0xfefffffff010e002 0x7fdffffffe021c00

def z1364 : W := mkw 0x00228246a0000001 0x00045048d4000000 0xeee38fe7f0000000 0x7ddc71fcfe000000

def z1365 : W := mkw 0x7000092109221ec0 0x0e000124212443d8 0x0000000000001fe0 0x00000000000003fc

def z1366 : W := mkw 0x008016def0000001 0xc01002dbde000000 0xc0800ffff00018e0 0x781001fffe00031c

def z1367 : W := mkw 0x807fe00006ddc006 0x300ffc0000dbb800 0x3f7ff0003fffe09f 0xc7effe0007fffc13

def z1368 : W := mkw 0x00dd74da70000006 0xc01bae9b4e000000 0xfeff7fff30000000 0x7fdfefffe6000000

def z1369 : W := mkw 0x0022820482090001 0x0004504090412000 0x2e638f070f0f0005 0x85cc71e0e1e1e000

def z1370 : W := mkw 0x00fff6def0000007 0xc01ffedbde000000 0xdeff0ffff0000000 0x7bdfe1fffe000000

def z1371 : W := mkw 0x048956def000212d 0xc0912adbde000425 0xf69b4ffff0009ffe 0xfed369fffe0013ff

def z1372 : W := mkw 0x50228b058b0b18c1 0x0a045160b1616318 0xfe63cf07cf0f98e7 0xdfcc79e0f9e1f31c

def z1373 : W := mkw 0x0400100850002128 0x808002010a000425 0xfe07f018f81fffff 0xffc0fe031f03ffff

def z1374 : W := mkw 0x00fff6def0000007 0xc01ffedbde000000 0xfefffffff011ff07 0xffdffffffe023fe0

def z1375 : W := mkw 0xf809486328669494 0x1f01290c650cd292 0x779b48e738fe9f9f 0xeef3691ce71fd3f3

def z1376 : W := mkw 0x6000092009201c00 0x0c00012401240380 0xdffc0ff80ff01f03 0xbbff81ff01fe03e0

def z1377 : W := mkw 0x60540db00db01e00 0x2c0a81b601b603c0 0xdffc0ff83ff01f9b 0xfbff81ff07fe03f3

def z1378 : W := mkw 0x80fff6def24d8007 0xd01ffedbde49b000 0xffffffffffef8007 0xfffffffffffdf000

def z1379 : W := mkw 0x002bd24ef0000005 0x80057a49de000000 0xfefffffff0000000 0x7fdffffffe000000

def z1380 : W := mkw 0x50228b058b0b18c1 0x0a045160b1616318 0xe4638f07cf0f18e4 0x5c8c71e0f9e1e31c

def z1381 : W := mkw 0x80fff6def6ddc007 0xf01ffedbdedbb800 0xfffffffffffe0003 0xffffffffffffc000

def z1382 : W := mkw 0xf87fe9210fffdcd6 0x3f0ffd2421fffb9a 0x3f7ff0000ffffcff 0x87effe0001ffff9f

def z1383 : W := mkw 0x80fff6def4d4c007 0xf01ffedbde9a9800 0xfffffffff8fee006 0xffffffffff1fdc00

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(1,[z7,z1,z2,z3,z4,z6])],[(0,[z1,z8,z2,z3,z4,z5,z6]),(0,[z9,z1,z10,z2,z3,z4,z6]),(0,[z11,z1,z12,z3,z4,z13,z6]),(0,[z14,z11,z1,z2,z15,z4,z6]),(0,[z11,z1,z2,z3,z4,z6,z16])],[(0,[z11,z1,z17,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z4,z6,z18]),(1,[z1,z2,z3,z5,z19,z6]),(0,[z11,z1,z2,z3,z4,z6,z6])],[(0,[z20,z21,z1,z2,z3,z4,z6]),(0,[z22,z1,z23,z2,z3,z4,z6]),(0,[z9,z11,z1,z2,z3,z24,z6]),(0,[z11,z1,z2,z3,z25,z4,z6]),(0,[z11,z26,z1,z2,z3,z4,z6]),(0,[z27,z11,z1,z2,z3,z4,z6])],[(0,[z1,z28,z23,z2,z3,z4,z6]),(0,[z9,z1,z29,z2,z3,z4,z6]),(0,[z30,z11,z1,z2,z3,z4,z31]),(0,[z11,z1,z2,z3,z32,z4,z6]),(0,[z33,z11,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z34,z4,z6]),(1,[z35,z1,z2,z3,z4,z6]),(0,[z11,z1,z3,z4,z36,z6,z37])],[(0,[z11,z1,z38,z2,z3,z4,z6])],[(1,[z11,z1,z2,z3,z39,z6]),(1,[z40,z1,z2,z3,z4,z6]),(0,[z11,z41,z1,z2,z3,z4,z6])],[(0,[z1,z28,z2,z42,z3,z4,z6]),(0,[z11,z1,z43,z2,z3,z4,z6]),(0,[z22,z11,z1,z2,z3,z44,z6]),(0,[z45,z11,z1,z46,z3,z4,z6]),(0,[z47,z1,z2,z3,z48,z4,z6])]],
   [[(0,[z49,z1,z28,z2,z3,z4,z6]),(0,[z50,z11,z1,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z5,z6,z51]),(0,[z9,z1,z2,z52,z3,z4,z6]),(0,[z53,z54,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z55,z3,z4,z6]),(0,[z56,z11,z1,z2,z3,z4,z6]),(1,[z57,z1,z2,z3,z4,z6])],[(1,[z58,z28,z2,z3,z4,z6]),(0,[z1,z28,z2,z3,z4,z59,z6]),(0,[z60,z1,z28,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z5,z36,z6]),(0,[z9,z1,z61,z2,z3,z4,z6]),(0,[z62,z11,z54,z2,z3,z4,z6]),(0,[z63,z11,z1,z2,z3,z13,z6])],[(0,[z11,z1,z2,z3,z4,z64,z6]),(0,[z11,z1,z8,z2,z3,z4,z6]),(1,[z11,z1,z2,z3,z4,z65])],[(0,[z66,z21,z1,z2,z3,z4,z6]),(0,[z22,z1,z2,z3,z4,z67,z6]),(1,[z68,z1,z2,z3,z5,z6]),(0,[z14,z9,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z4,z6,z69]),(0,[z70,z11,z1,z2,z3,z4,z6])],[(0,[z1,z28,z2,z3,z4,z67,z6]),(0,[z71,z21,z1,z2,z3,z4,z6]),(0,[z72,z11,z1,z2,z3,z4,z6]),(0,[z9,z1,z2,z3,z73,z4,z6]),(0,[z11,z1,z2,z3,z74,z4,z6])],[(0,[z45,z21,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z4,z5,z6]),(0,[z75,z11,z1,z2,z3,z4,z6])],[(0,[z11,z1,z2,z3,z76,z4,z6]),(0,[z11,z1,z2,z77,z3,z4,z6]),(0,[z78,z11,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z79,z3,z4,z6]),(0,[z11,z1,z2,z3,z4,z80,z6]),(0,[z11,z1,z2,z81,z3,z4,z6])],[(0,[z11,z1,z2,z3,z4,z82,z6]),(0,[z11,z1,z2,z3,z4,z6,z83]),(0,[z22,z9,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z84,z4,z6]),(0,[z11,z1,z2,z85,z3,z4,z6]),(0,[z35,z11,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z4,z37,z86])]],
   [[(0,[z87,z1,z2,z3,z4,z5,z6]),(0,[z30,z11,z1,z2,z3,z88,z6]),(0,[z0,z1,z89,z2,z3,z4,z6]),(0,[z11,z1,z90,z91,z2,z4,z6]),(0,[z11,z1,z2,z3,z4,z92,z6])],[(0,[z58,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z93]),(0,[z11,z1,z2,z3,z94,z5,z6]),(1,[z11,z95,z2,z3,z96,z6]),(0,[z11,z1,z2,z3,z97,z4,z6])],[(0,[z11,z1,z2,z3,z98,z4,z6]),(0,[z11,z1,z2,z3,z4,z6,z99]),(0,[z11,z1,z2,z3,z48,z5,z6]),(0,[z100,z9,z1,z2,z3,z4,z6]),(0,[z11,z1,z101,z2,z3,z4,z6]),(0,[z45,z11,z2,z3,z102,z4,z6]),(1,[z1,z103,z2,z3,z4,z6]),(0,[z1,z2,z3,z96,z4,z104,z6])],[(0,[z105,z21,z1,z2,z3,z4,z6]),(0,[z21,z1,z2,z3,z4,z6,z106]),(0,[z107,z11,z1,z2,z3,z4,z6]),(1,[z14,z1,z2,z3,z5,z6]),(0,[z45,z108,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z109,z6,z51])],[(0,[z21,z1,z10,z2,z3,z4,z6]),(0,[z45,z11,z1,z2,z102,z4,z6]),(0,[z110,z11,z1,z2,z3,z4,z6])],[(0,[z1,z28,z2,z12,z3,z4,z6]),(0,[z111,z1,z28,z2,z3,z4,z6]),(0,[z9,z1,z2,z3,z4,z36,z6]),(0,[z11,z1,z2,z3,z24,z13,z6]),(0,[z112,z11,z1,z2,z3,z4,z6]),(0,[z113,z11,z1,z2,z4,z19,z6]),(0,[z11,z1,z2,z114,z3,z4,z6])],[(0,[z11,z1,z2,z3,z4,z115,z6]),(0,[z11,z1,z2,z3,z4,z6,z116]),(0,[z11,z1,z2,z117,z3,z4,z6]),(0,[z11,z1,z2,z3,z4,z118,z6]),(0,[z119,z11,z1,z2,z3,z4,z6])],[(0,[z11,z120,z1,z2,z3,z4,z6]),(0,[z1,z2,z3,z121,z4,z5,z6]),(0,[z122,z9,z1,z2,z3,z4,z6]),(1,[z11,z1,z46,z3,z4,z6])]],
   [[(0,[z123,z11,z1,z2,z3,z4,z6]),(0,[z11,z1,z124,z2,z3,z4,z6]),(0,[z125,z11,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z126,z3,z4,z6])],[(0,[z1,z124,z28,z2,z3,z4,z6]),(0,[z1,z28,z2,z3,z127,z4,z6]),(0,[z128,z1,z2,z3,z4,z5,z6])],[(0,[z21,z11,z1,z2,z3,z129,z6]),(0,[z11,z1,z2,z130,z3,z4,z6]),(0,[z11,z1,z2,z3,z94,z118,z6]),(0,[z11,z1,z2,z3,z131,z4,z6]),(0,[z11,z132,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z4,z133,z6,z86])],[(0,[z1,z28,z2,z3,z4,z133,z6]),(0,[z1,z28,z2,z3,z109,z4,z6]),(0,[z60,z11,z1,z23,z3,z4,z6]),(0,[z134,z9,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z4,z6,z135]),(0,[z14,z11,z1,z2,z3,z4,z136]),(0,[z11,z1,z2,z3,z48,z118,z6])],[(0,[z49,z11,z1,z2,z3,z4,z6]),(0,[z11,z1,z137,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z138,z4,z6]),(0,[z11,z1,z2,z139,z3,z4,z6]),(0,[z11,z1,z91,z2,z3,z4,z6]),(1,[z11,z1,z90,z2,z4,z6])],[(1,[z21,z1,z2,z3,z4,z6]),(0,[z1,z28,z2,z3,z4,z13,z6]),(0,[z21,z1,z2,z3,z129,z4,z6]),(0,[z60,z11,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z140,z4,z6]),(0,[z11,z1,z141,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z4,z142,z6]),(0,[z11,z1,z2,z143,z3,z4,z6]),(0,[z11,z1,z3,z94,z4,z13,z6]),(0,[z11,z1,z2,z3,z4,z6,z144])],[(0,[z11,z1,z2,z3,z4,z145,z6]),(0,[z63,z1,z2,z3,z4,z5,z6]),(0,[z146,z11,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z4,z104,z6]),(0,[z11,z1,z2,z3,z4,z147,z6]),(0,[z11,z1,z148,z2,z3,z4,z6])],[(0,[z11,z1,z2,z3,z4,z6,z149]),(0,[z150,z11,z1,z2,z3,z4,z6]),(0,[z1,z2,z3,z102,z4,z5,z6]),(0,[z11,z1,z2,z3,z4,z6,z31]),(0,[z108,z11,z1,z2,z3,z4,z6]),(0,[z11,z151,z1,z2,z3,z4,z6])]],
   [[(0,[z152,z11,z1,z2,z3,z4,z6]),(0,[z9,z49,z1,z2,z3,z4,z6]),(0,[z11,z1,z153,z2,z3,z4,z6]),(0,[z154,z11,z1,z2,z3,z4,z6])],[(0,[z11,z1,z2,z3,z155,z4,z6]),(0,[z11,z1,z2,z3,z4,z156,z6]),(0,[z11,z157,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z4,z158,z6])],[(0,[z1,z2,z3,z4,z118,z159,z6]),(1,[z160,z1,z2,z3,z4,z6])],[(0,[z161,z11,z1,z2,z3,z4,z6]),(0,[z1,z2,z42,z3,z4,z5,z6]),(0,[z53,z11,z1,z2,z3,z4,z6])],[(0,[z11,z1,z28,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z4,z133,z162]),(0,[z11,z1,z2,z3,z163,z4,z6])],[(0,[z1,z28,z164,z2,z3,z4,z6]),(0,[z1,z2,z42,z3,z84,z4,z6]),(0,[z66,z11,z1,z8,z3,z4,z6]),(0,[z11,z1,z2,z165,z3,z4,z6])],[(0,[z166,z11,z1,z2,z3,z4,z6]),(0,[z11,z167,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z4,z168,z6]),(0,[z169,z11,z0,z2,z3,z4,z6]),(0,[z11,z1,z8,z29,z2,z4,z6]),(0,[z11,z1,z2,z170,z3,z4,z6]),(0,[z11,z1,z2,z171,z3,z4,z6]),(0,[z11,z1,z2,z171,z3,z48,z6])],[(0,[z172,z11,z1,z2,z3,z4,z6]),(0,[z1,z28,z2,z173,z3,z4,z6]),(0,[z21,z11,z28,z2,z3,z4,z6]),(0,[z174,z11,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z4,z175,z6]),(0,[z111,z11,z1,z23,z3,z4,z6]),(0,[z9,z1,z2,z176,z3,z4,z6]),(0,[z177,z11,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z4,z178,z6]),(0,[z9,z1,z2,z3,z96,z4,z6]),(1,[z11,z1,z2,z3,z179,z6]),(0,[z45,z11,z1,z2,z3,z180,z6]),(0,[z11,z181,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z4,z182,z6])]],
   [[(0,[z58,z1,z28,z2,z3,z4,z6]),(1,[z1,z2,z3,z5,z13,z6]),(0,[z11,z1,z2,z3,z4,z179,z6]),(0,[z11,z1,z2,z3,z4,z133,z106])],[(0,[z62,z9,z1,z2,z3,z4,z6]),(0,[z11,z183,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z4,z184,z6])],[(0,[z11,z1,z10,z3,z127,z4,z6]),(0,[z45,z185,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z4,z186,z6]),(0,[z11,z1,z2,z3,z4,z187,z6]),(0,[z11,z1,z173,z3,z188,z4,z6])],[(0,[z11,z1,z2,z3,z4,z6,z189]),(0,[z11,z1,z2,z190,z3,z4,z6]),(0,[z11,z1,z2,z3,z4,z191,z6]),(0,[z11,z1,z2,z3,z192,z4,z6]),(0,[z11,z1,z2,z52,z127,z4,z6]),(0,[z193,z11,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z194,z4,z6]),(0,[z195,z1,z2,z3,z109,z4,z6])],[(0,[z21,z1,z2,z3,z4,z6,z196]),(0,[z197,z1,z2,z3,z4,z5,z6]),(0,[z11,z1,z2,z198,z3,z4,z6]),(0,[z11,z1,z199,z2,z3,z4,z6]),(0,[z200,z11,z1,z2,z3,z4,z6]),(0,[z66,z11,z1,z3,z4,z36,z6])],[(0,[z11,z1,z2,z3,z4,z201,z6])],[(0,[z11,z202,z1,z2,z3,z4,z6]),(0,[z11,z1,z10,z3,z4,z13,z6]),(0,[z11,z1,z2,z3,z4,z203,z6])],[(0,[z11,z1,z204,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z4,z205,z6])]],
   [[(0,[z11,z1,z2,z3,z206,z4,z6]),(0,[z1,z10,z2,z3,z4,z5,z6]),(0,[z207,z11,z1,z2,z3,z4,z6]),(0,[z208,z11,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z4,z209,z6])],[(0,[z72,z11,z1,z2,z3,z5,z6]),(0,[z62,z11,z1,z2,z3,z4,z210]),(0,[z11,z1,z2,z3,z4,z211,z6])],[(0,[z11,z2,z52,z3,z102,z4,z6]),(0,[z11,z212,z2,z52,z3,z4,z6]),(0,[z11,z1,z2,z3,z4,z213,z6]),(0,[z11,z1,z214,z2,z3,z4,z6]),(0,[z11,z215,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z216,z4,z6])],[(0,[z21,z1,z2,z3,z127,z4,z6]),(0,[z30,z111,z1,z2,z3,z4,z6]),(0,[z66,z11,z1,z10,z3,z4,z6]),(0,[z11,z1,z2,z3,z4,z6,z217]),(1,[z218,z1,z2,z3,z4,z6])],[(0,[z11,z1,z219,z2,z3,z4,z6]),(1,[z11,z1,z2,z3,z32,z6]),(0,[z11,z1,z2,z220,z3,z4,z6]),(0,[z221,z1,z2,z3,z4,z6,z86])],[(0,[z63,z1,z28,z2,z3,z4,z6]),(0,[z21,z1,z2,z3,z4,z133,z6]),(0,[z21,z1,z2,z3,z109,z4,z6]),(0,[z68,z21,z1,z2,z3,z4,z6]),(0,[z63,z11,z1,z3,z4,z13,z6]),(1,[z11,z1,z164,z3,z94,z6]),(1,[z11,z1,z3,z188,z4,z6])],[(0,[z111,z22,z1,z2,z3,z4,z6]),(0,[z222,z11,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z223,z3,z4,z6]),(0,[z224,z11,z1,z2,z3,z4,z6]),(1,[z169,z11,z2,z3,z4,z106]),(0,[z11,z1,z225,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z4,z226,z6])],[(0,[z1,z2,z3,z4,z5,z6,z106]),(0,[z11,z1,z2,z3,z227,z4,z6]),(0,[z228,z11,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z229,z3,z4,z6]),(1,[z11,z1,z2,z3,z180,z6])]],
   [[(0,[z11,z11,z1,z2,z3,z4,z6]),(0,[z230,z11,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z4,z6,z231]),(0,[z212,z1,z2,z3,z4,z5,z6]),(0,[z66,z9,z1,z2,z3,z4,z6]),(1,[z11,z1,z2,z3,z232,z6]),(0,[z30,z11,z1,z2,z3,z232,z6]),(0,[z233,z11,z1,z2,z3,z4,z6]),(0,[z11,z1,z234,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z4,z6,z37]),(1,[z195,z1,z2,z3,z4,z6]),(0,[z11,z235,z1,z2,z3,z4,z6])],[(0,[z1,z28,z2,z236,z3,z4,z6]),(0,[z237,z11,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z4,z232,z6]),(0,[z49,z11,z1,z2,z3,z4,z31]),(0,[z62,z11,z1,z2,z238,z4,z6]),(1,[z11,z1,z2,z3,z239,z6]),(0,[z240,z11,z1,z2,z3,z4,z6]),(1,[z241,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z4,z242,z6]),(0,[z11,z1,z2,z3,z4,z6,z243])],[(0,[z1,z219,z28,z2,z3,z4,z6]),(0,[z21,z1,z2,z176,z3,z4,z6]),(0,[z14,z1,z2,z3,z4,z5,z6]),(0,[z45,z9,z1,z2,z3,z4,z6]),(0,[z63,z11,z1,z2,z3,z94,z6]),(0,[z11,z1,z2,z244,z3,z4,z6]),(0,[z1,z2,z3,z4,z245,z6,z86]),(0,[z11,z1,z246,z2,z3,z4,z6])],[(0,[z247,z11,z1,z2,z3,z4,z6]),(0,[z87,z11,z1,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z248,z6,z37]),(0,[z11,z1,z2,z3,z249,z4,z6]),(0,[z11,z1,z250,z2,z3,z4,z6])],[(0,[z58,z11,z1,z2,z3,z4,z6]),(0,[z21,z212,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z251,z3,z4,z6]),(0,[z62,z11,z1,z2,z3,z4,z252]),(0,[z11,z1,z2,z3,z94,z96,z6])],[(0,[z11,z253,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z239,z4,z6]),(0,[z11,z1,z2,z3,z4,z6,z254]),(0,[z14,z11,z1,z255,z3,z4,z6]),(0,[z11,z1,z2,z3,z48,z96,z6]),(0,[z11,z1,z256,z2,z3,z4,z6])],[(0,[z22,z1,z2,z3,z4,z5,z6]),(1,[z14,z11,z2,z3,z118,z6]),(1,[z1,z2,z3,z257,z4,z6]),(0,[z11,z1,z2,z127,z4,z6,z86])],[(0,[z1,z28,z2,z3,z4,z162,z6]),(0,[z1,z28,z2,z3,z4,z5,z6]),(0,[z11,z1,z2,z258,z3,z4,z6]),(0,[z11,z1,z2,z3,z259,z4,z6]),(0,[z11,z1,z2,z3,z4,z260,z6]),(0,[z11,z1,z2,z3,z4,z261,z6])]],
   [[(0,[z21,z21,z1,z2,z3,z4,z6]),(0,[z197,z11,z1,z2,z42,z4,z6]),(0,[z11,z1,z2,z3,z4,z262,z6]),(1,[z11,z1,z2,z15,z4,z6]),(0,[z11,z1,z2,z3,z4,z36,z86]),(0,[z11,z263,z1,z2,z3,z4,z6])],[(0,[z113,z1,z28,z2,z3,z4,z6]),(0,[z21,z1,z2,z173,z3,z4,z6]),(1,[z22,z1,z2,z84,z4,z6]),(0,[z11,z1,z2,z3,z4,z6,z264]),(1,[z53,z1,z2,z3,z4,z6]),(0,[z11,z265,z1,z2,z3,z4,z6]),(0,[z266,z11,z1,z2,z3,z4,z6]),(0,[z11,z1,z267,z2,z3,z4,z6])],[(0,[z268,z11,z1,z2,z3,z4,z6]),(1,[z11,z1,z2,z3,z44,z6]),(0,[z11,z1,z2,z3,z4,z6,z269]),(0,[z11,z1,z10,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z102,z4,z6]),(0,[z270,z11,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z271,z4,z6])],[(0,[z272,z1,z28,z2,z3,z4,z6]),(0,[z11,z273,z1,z2,z3,z4,z6]),(0,[z9,z1,z2,z3,z4,z6,z106]),(0,[z11,z1,z2,z274,z3,z4,z6]),(0,[z11,z1,z2,z3,z275,z4,z6]),(0,[z11,z1,z8,z3,z4,z6,z37])],[(0,[z1,z28,z2,z276,z3,z4,z6]),(0,[z277,z21,z1,z2,z3,z4,z6]),(0,[z21,z95,z1,z2,z3,z4,z6]),(0,[z128,z11,z1,z2,z3,z4,z6])],[(0,[z169,z21,z1,z2,z3,z4,z6]),(0,[z11,z1,z278,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z96,z19,z6]),(0,[z11,z1,z29,z2,z3,z4,z6]),(0,[z279,z11,z1,z2,z3,z4,z6])],[(0,[z280,z11,z1,z2,z3,z4,z6]),(1,[z95,z1,z2,z3,z5,z6]),(0,[z11,z1,z2,z3,z24,z94,z6])],[(0,[z281,z11,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z4,z6,z282]),(0,[z11,z283,z1,z2,z3,z4,z6])]],
   [[(0,[z11,z1,z2,z284,z3,z4,z6]),(0,[z111,z11,z1,z2,z3,z39,z6]),(0,[z11,z1,z2,z3,z4,z6,z285]),(1,[z110,z1,z2,z3,z4,z6]),(0,[z241,z1,z2,z3,z127,z4,z6]),(0,[z11,z1,z286,z2,z3,z4,z6])],[(0,[z54,z1,z2,z3,z4,z5,z6]),(0,[z62,z287,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z288,z4,z6]),(0,[z11,z1,z2,z52,z3,z4,z6]),(0,[z11,z1,z2,z3,z118,z6,z51]),(0,[z63,z11,z1,z2,z3,z4,z6]),(1,[z11,z1,z2,z163,z4,z6])],[(0,[z11,z1,z2,z3,z4,z39,z6]),(1,[z9,z1,z2,z3,z4,z6]),(0,[z134,z1,z2,z3,z4,z5,z6]),(0,[z11,z1,z2,z3,z121,z4,z6]),(0,[z11,z1,z61,z2,z3,z4,z6]),(0,[z11,z1,z289,z2,z3,z4,z6]),(0,[z169,z11,z1,z2,z3,z4,z162]),(0,[z11,z290,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z4,z6,z291]),(0,[z11,z1,z2,z3,z4,z292,z6]),(0,[z11,z1,z2,z3,z4,z293,z6])],[(0,[z11,z1,z2,z3,z294,z4,z6]),(0,[z11,z1,z295,z2,z3,z4,z6])],[(0,[z11,z1,z2,z3,z4,z159,z6]),(2,[z1,z2,z3,z145,z6]),(0,[z11,z1,z2,z3,z4,z296,z6]),(0,[z1,z2,z3,z94,z4,z5,z6]),(0,[z11,z1,z2,z3,z297,z4,z6]),(0,[z11,z1,z2,z52,z4,z19,z6]),(0,[z11,z0,z1,z2,z3,z4,z162]),(0,[z11,z1,z298,z2,z3,z4,z65])],[(0,[z299,z11,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z188,z4,z6]),(0,[z11,z1,z2,z3,z73,z4,z6]),(0,[z300,z11,z1,z2,z3,z4,z6])],[(0,[z21,z1,z2,z3,z301,z4,z6]),(0,[z9,z1,z23,z2,z3,z4,z6]),(0,[z11,z1,z12,z3,z4,z6,z37]),(0,[z169,z11,z1,z2,z3,z4,z106])],[(0,[z11,z1,z2,z302,z3,z4,z6]),(0,[z11,z1,z2,z303,z3,z4,z6]),(0,[z304,z11,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z4,z305,z6])]],
   [[(0,[z306,z9,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z4,z307,z6]),(0,[z11,z0,z1,z2,z3,z4,z106]),(0,[z11,z1,z308,z2,z3,z4,z6]),(0,[z11,z309,z1,z2,z3,z4,z6]),(1,[z11,z1,z267,z3,z4,z6]),(0,[z11,z1,z2,z3,z310,z4,z6])],[(0,[z1,z28,z2,z3,z4,z6,z149]),(0,[z11,z1,z2,z311,z3,z4,z6]),(0,[z9,z1,z2,z42,z3,z4,z6]),(0,[z11,z1,z312,z2,z3,z4,z6]),(1,[z11,z1,z2,z313,z4,z6]),(0,[z11,z1,z164,z10,z3,z4,z6]),(0,[z11,z1,z29,z2,z52,z4,z6]),(0,[z11,z1,z314,z2,z3,z4,z6]),(0,[z11,z1,z2,z171,z48,z4,z6]),(0,[z11,z7,z1,z2,z3,z4,z6])],[(0,[z22,z11,z1,z2,z42,z4,z6]),(0,[z11,z1,z2,z3,z4,z315,z6]),(0,[z11,z1,z2,z3,z316,z4,z6]),(0,[z11,z1,z91,z2,z3,z4,z37]),(0,[z317,z11,z1,z2,z3,z4,z6]),(0,[z47,z11,z1,z2,z3,z4,z6])],[(0,[z21,z1,z1,z2,z3,z4,z6]),(1,[z21,z1,z2,z3,z145,z6]),(0,[z60,z21,z1,z2,z3,z4,z6]),(0,[z11,z1,z318,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z4,z319,z6]),(0,[z1,z2,z3,z48,z4,z5,z6]),(0,[z11,z1,z2,z3,z5,z19,z6]),(0,[z30,z49,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z4,z6,z320]),(0,[z11,z1,z2,z321,z3,z4,z6]),(0,[z11,z1,z2,z3,z322,z4,z6]),(0,[z11,z1,z323,z2,z3,z4,z6])],[(0,[z21,z1,z2,z3,z4,z19,z6]),(0,[z11,z1,z2,z3,z324,z4,z6]),(0,[z325,z11,z1,z2,z3,z4,z6]),(0,[z57,z11,z1,z2,z3,z4,z6]),(0,[z57,z1,z2,z3,z4,z6,z37]),(0,[z11,z1,z2,z3,z4,z6,z326]),(0,[z327,z11,z1,z2,z3,z4,z6])],[(0,[z11,z1,z2,z3,z328,z4,z6]),(0,[z11,z1,z2,z3,z24,z4,z6]),(0,[z11,z1,z2,z3,z24,z48,z6]),(0,[z329,z11,z1,z2,z3,z4,z6]),(1,[z45,z11,z2,z102,z4,z6]),(0,[z330,z212,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z331,z3,z4,z6]),(0,[z11,z1,z91,z3,z4,z6,z37]),(0,[z113,z11,z1,z2,z3,z4,z6]),(0,[z113,z11,z1,z2,z3,z48,z6]),(0,[z11,z1,z2,z3,z4,z6,z51])],[(0,[z332,z11,z1,z2,z3,z4,z6]),(0,[z9,z1,z2,z3,z4,z67,z6]),(0,[z11,z1,z2,z3,z333,z4,z6]),(0,[z11,z1,z2,z3,z4,z36,z6])],[(0,[z272,z11,z1,z2,z3,z4,z6]),(0,[z197,z11,z1,z2,z3,z4,z6]),(0,[z134,z11,z1,z2,z127,z4,z6]),(0,[z11,z1,z2,z3,z4,z6,z334])]],
   [[(0,[z1,z28,z2,z171,z3,z4,z6]),(0,[z62,z1,z2,z3,z4,z5,z6]),(0,[z11,z1,z2,z3,z335,z4,z6]),(0,[z11,z336,z1,z2,z3,z4,z6])],[(0,[z21,z1,z2,z3,z4,z162,z6]),(0,[z111,z1,z2,z176,z3,z4,z6]),(0,[z11,z1,z2,z337,z3,z4,z6]),(0,[z40,z11,z1,z2,z3,z4,z6]),(0,[z11,z95,z2,z3,z96,z4,z6]),(0,[z11,z1,z2,z3,z4,z338,z6])],[(0,[z0,z1,z28,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z339,z4,z6]),(1,[z11,z1,z2,z3,z4,z136]),(0,[z113,z11,z1,z2,z171,z4,z6]),(0,[z11,z340,z1,z2,z3,z4,z6])],[(0,[z1,z1,z28,z2,z3,z4,z6]),(0,[z1,z28,z298,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z341,z4,z6]),(0,[z72,z11,z1,z2,z3,z24,z6])],[(0,[z342,z11,z1,z2,z3,z4,z6]),(0,[z1,z2,z176,z3,z4,z5,z6]),(0,[z11,z1,z2,z3,z4,z343,z6])],[(0,[z344,z11,z1,z2,z3,z4,z6]),(0,[z21,z0,z1,z2,z3,z4,z6]),(0,[z11,z345,z1,z2,z3,z4,z6]),(0,[z11,z1,z91,z2,z3,z4,z36]),(0,[z113,z263,z1,z2,z3,z4,z6])],[(1,[z72,z1,z2,z3,z5,z6]),(0,[z11,z1,z2,z3,z4,z6,z93]),(0,[z11,z346,z1,z2,z3,z4,z6]),(0,[z11,z1,z255,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z15,z4,z6]),(0,[z347,z11,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z348,z4,z6]),(0,[z11,z1,z349,z2,z3,z4,z6])],[(0,[z111,z21,z1,z2,z3,z4,z6]),(0,[z62,z350,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z4,z351,z6]),(0,[z134,z11,z1,z2,z3,z4,z86])]],
   [[(0,[z30,z21,z1,z2,z3,z4,z6]),(0,[z9,z1,z2,z3,z352,z4,z6]),(0,[z353,z11,z1,z2,z3,z4,z6]),(0,[z11,z1,z8,z29,z3,z4,z6]),(0,[z66,z11,z1,z91,z3,z4,z6]),(1,[z113,z11,z1,z2,z19,z6])],[(0,[z1,z28,z2,z3,z94,z4,z6]),(0,[z1,z28,z2,z3,z4,z6,z86]),(0,[z21,z1,z23,z2,z3,z4,z6]),(0,[z354,z11,z1,z2,z3,z4,z6]),(0,[z11,z355,z1,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z5,z356,z6]),(0,[z1,z2,z3,z73,z4,z5,z6]),(0,[z357,z11,z1,z2,z3,z4,z6])],[(0,[z1,z28,z2,z3,z48,z4,z6]),(0,[z68,z9,z1,z2,z3,z4,z6]),(0,[z358,z11,z1,z2,z3,z4,z6])],[(0,[z11,z1,z2,z3,z359,z4,z6]),(0,[z360,z9,z1,z2,z3,z4,z6]),(0,[z9,z1,z2,z3,z127,z4,z6]),(0,[z11,z1,z2,z171,z102,z4,z6]),(0,[z11,z1,z103,z2,z3,z4,z6]),(1,[z63,z11,z1,z3,z13,z6]),(0,[z11,z1,z2,z3,z361,z4,z6])],[(0,[z21,z1,z2,z42,z3,z4,z6]),(0,[z1,z23,z2,z176,z3,z4,z6]),(0,[z362,z11,z1,z2,z3,z4,z6]),(0,[z1,z2,z3,z127,z4,z5,z6]),(0,[z11,z1,z2,z3,z363,z4,z6]),(0,[z364,z11,z1,z2,z3,z4,z6]),(0,[z11,z1,z365,z2,z3,z4,z6])],[(0,[z9,z1,z2,z3,z4,z133,z6]),(0,[z9,z1,z2,z3,z109,z4,z6]),(0,[z14,z11,z1,z2,z3,z4,z6])],[(1,[z108,z1,z2,z3,z4,z6])],[(0,[z95,z1,z2,z3,z4,z5,z6]),(0,[z66,z1,z2,z3,z4,z5,z6]),(0,[z9,z1,z2,z3,z4,z13,z6]),(0,[z62,z11,z1,z12,z3,z4,z6]),(0,[z366,z11,z1,z2,z3,z4,z6])]],
   [[(0,[z367,z11,z1,z2,z3,z4,z6]),(0,[z368,z9,z1,z2,z3,z4,z6]),(0,[z11,z369,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z4,z370,z6]),(0,[z11,z1,z8,z10,z3,z4,z6]),(0,[z11,z1,z2,z3,z96,z4,z6]),(0,[z11,z1,z2,z3,z4,z6,z371]),(0,[z11,z1,z2,z372,z3,z4,z6]),(0,[z11,z1,z373,z2,z3,z4,z6])],[(0,[z21,z54,z1,z2,z3,z4,z6]),(0,[z21,z1,z2,z3,z4,z67,z6]),(0,[z45,z1,z2,z3,z4,z5,z6]),(0,[z374,z11,z1,z2,z3,z4,z6])],[(0,[z1,z28,z2,z3,z4,z6,z37]),(0,[z11,z1,z375,z2,z3,z4,z6]),(1,[z287,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z4,z6,z376])],[(0,[z11,z1,z2,z3,z4,z356,z6]),(0,[z11,z1,z377,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z96,z13,z6]),(0,[z378,z11,z1,z2,z3,z4,z6])],[(1,[z11,z1,z2,z3,z359,z6]),(0,[z9,z212,z1,z2,z3,z4,z6]),(0,[z100,z11,z1,z2,z3,z4,z6]),(0,[z11,z379,z1,z2,z3,z4,z6])],[(0,[z380,z1,z2,z3,z4,z5,z6]),(0,[z11,z1,z2,z3,z381,z4,z6]),(0,[z134,z11,z1,z2,z173,z4,z6])],[(0,[z11,z1,z2,z3,z4,z382,z6]),(0,[z14,z11,z1,z55,z3,z4,z6]),(0,[z11,z1,z383,z2,z3,z4,z6]),(0,[z11,z1,z384,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z385,z4,z6])],[(0,[z62,z1,z28,z2,z3,z4,z6]),(0,[z21,z1,z2,z386,z3,z4,z6]),(0,[z11,z1,z2,z3,z4,z387,z6]),(1,[z9,z1,z2,z3,z5,z6]),(0,[z9,z1,z164,z2,z3,z4,z6]),(1,[z26,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z4,z65,z6]),(0,[z11,z1,z29,z2,z4,z6,z86]),(0,[z11,z1,z2,z3,z4,z245,z6])]],
   [[(1,[z21,z1,z2,z3,z129,z6]),(0,[z9,z21,z1,z2,z3,z4,z6]),(0,[z388,z11,z1,z2,z3,z4,z6]),(0,[z9,z1,z2,z3,z4,z389,z6]),(0,[z11,z1,z2,z390,z3,z4,z6]),(0,[z391,z11,z1,z2,z3,z4,z6])],[(0,[z268,z1,z28,z2,z3,z4,z6]),(0,[z1,z28,z2,z3,z392,z4,z6]),(0,[z393,z21,z1,z2,z3,z4,z6]),(0,[z122,z11,z1,z2,z3,z4,z6]),(0,[z277,z9,z1,z2,z3,z4,z6]),(0,[z9,z1,z2,z173,z3,z4,z6])],[(0,[z21,z1,z2,z12,z3,z4,z6]),(0,[z11,z394,z1,z2,z3,z4,z6]),(0,[z169,z9,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z46,z3,z4,z6]),(0,[z395,z11,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z4,z396,z6]),(0,[z11,z1,z397,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z398,z4,z6]),(0,[z11,z1,z399,z2,z3,z4,z6]),(0,[z400,z11,z1,z2,z3,z4,z6])],[(0,[z401,z11,z1,z2,z3,z4,z6]),(0,[z45,z11,z212,z2,z3,z4,z6]),(0,[z11,z1,z2,z52,z4,z6,z86]),(0,[z11,z160,z1,z2,z3,z4,z6])],[(0,[z1,z28,z2,z3,z102,z4,z6]),(0,[z11,z1,z402,z2,z3,z4,z6]),(0,[z60,z1,z23,z2,z3,z4,z6]),(0,[z9,z95,z1,z2,z3,z4,z6]),(1,[z403,z1,z2,z3,z4,z6])],[(0,[z404,z11,z1,z2,z3,z4,z6]),(0,[z1,z2,z3,z94,z4,z226,z6]),(0,[z134,z11,z1,z2,z3,z4,z6])],[(0,[z405,z11,z1,z2,z3,z4,z6]),(0,[z11,z212,z1,z2,z52,z4,z6]),(0,[z11,z1,z2,z3,z4,z406,z6]),(0,[z11,z1,z2,z3,z4,z407,z6]),(0,[z1,z2,z3,z48,z4,z209,z6]),(1,[z1,z2,z3,z4,z408,z6])],[(0,[z11,z409,z1,z2,z3,z4,z6]),(0,[z11,z1,z410,z2,z3,z4,z6]),(1,[z11,z1,z298,z127,z4,z6]),(0,[z411,z11,z1,z2,z3,z4,z6])]],
   [[(0,[z412,z21,z1,z2,z3,z4,z6]),(1,[z197,z1,z2,z42,z4,z6]),(0,[z1,z2,z3,z4,z5,z19,z6]),(0,[z1,z2,z171,z3,z4,z5,z6]),(0,[z11,z1,z2,z3,z238,z4,z6]),(1,[z11,z1,z2,z3,z131,z6]),(0,[z11,z1,z2,z3,z4,z6,z413]),(0,[z11,z414,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z415,z4,z6])],[(0,[z416,z11,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z417,z3,z4,z6]),(1,[z1,z2,z3,z4,z5,z6]),(0,[z11,z1,z2,z3,z5,z13,z6]),(0,[z11,z1,z2,z3,z4,z418,z6]),(0,[z11,z1,z2,z3,z4,z6,z419]),(0,[z11,z1,z2,z3,z4,z6,z420]),(0,[z421,z11,z1,z2,z3,z4,z6]),(1,[z422,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z423,z4,z6])],[(0,[z21,z1,z2,z3,z4,z13,z6]),(0,[z424,z11,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z425,z4,z6]),(0,[z11,z1,z2,z3,z426,z4,z6]),(0,[z95,z1,z153,z2,z3,z4,z6]),(0,[z66,z11,z1,z3,z127,z4,z6])],[(0,[z21,z1,z2,z3,z4,z6,z86]),(0,[z427,z11,z1,z2,z3,z4,z6]),(0,[z49,z1,z2,z3,z4,z67,z6]),(0,[z11,z54,z1,z10,z3,z4,z6]),(0,[z11,z1,z10,z3,z4,z6,z37]),(0,[z11,z1,z2,z3,z4,z180,z6])],[(0,[z21,z1,z2,z3,z48,z4,z6]),(0,[z14,z428,z1,z2,z3,z4,z6]),(1,[z11,z1,z255,z3,z4,z6]),(1,[z11,z1,z2,z3,z4,z429]),(0,[z11,z1,z90,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z430,z4,z6])],[(0,[z11,z1,z2,z3,z431,z4,z6]),(0,[z1,z2,z3,z4,z5,z162,z6]),(1,[z185,z1,z2,z3,z4,z6]),(1,[z11,z1,z2,z321,z4,z6]),(0,[z11,z1,z2,z3,z4,z432,z6])],[(0,[z1,z28,z2,z3,z4,z159,z6]),(0,[z11,z1,z433,z2,z3,z4,z6]),(1,[z1,z2,z3,z48,z5,z6])],[(0,[z1,z28,z8,z2,z3,z4,z6]),(0,[z434,z11,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z435,z4,z6]),(0,[z11,z1,z2,z3,z24,z6,z51]),(0,[z11,z1,z2,z436,z3,z4,z6])]],
   [[(0,[z45,z1,z28,z2,z3,z4,z6]),(0,[z11,z1,z437,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z438,z4,z6]),(1,[z350,z1,z2,z3,z4,z6]),(0,[z11,z439,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z4,z440,z6]),(0,[z221,z11,z1,z2,z3,z4,z6])],[(0,[z50,z21,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z441,z3,z4,z6]),(0,[z30,z1,z23,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z4,z442,z6]),(0,[z1,z29,z2,z3,z4,z5,z6]),(0,[z134,z11,z1,z2,z52,z4,z6]),(0,[z14,z11,z1,z2,z130,z4,z6]),(0,[z11,z1,z2,z3,z443,z4,z6])],[(0,[z21,z1,z164,z2,z3,z4,z6]),(0,[z14,z11,z95,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z444,z4,z6])],[(0,[z1,z28,z2,z3,z76,z4,z6]),(0,[z111,z1,z2,z42,z3,z4,z6]),(0,[z22,z1,z2,z3,z84,z4,z6]),(0,[z445,z11,z1,z2,z3,z4,z6]),(0,[z30,z11,z1,z2,z3,z4,z67]),(0,[z446,z11,z1,z2,z3,z4,z6]),(0,[z62,z11,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z4,z447,z6]),(0,[z11,z1,z2,z3,z4,z448,z6])],[(0,[z11,z1,z2,z3,z4,z6,z449]),(0,[z1,z28,z2,z3,z84,z4,z6]),(0,[z30,z1,z2,z42,z3,z4,z6]),(0,[z9,z1,z2,z3,z4,z19,z6]),(0,[z11,z1,z2,z3,z4,z6,z106]),(0,[z63,z160,z1,z2,z3,z4,z6]),(0,[z11,z450,z1,z2,z3,z4,z6])],[(0,[z72,z21,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z4,z451,z6]),(0,[z11,z1,z452,z2,z3,z4,z6])],[(0,[z197,z1,z28,z2,z3,z4,z6]),(0,[z60,z11,z1,z176,z3,z4,z6]),(0,[z11,z1,z2,z3,z4,z44,z6]),(0,[z45,z11,z1,z2,z3,z4,z453]),(0,[z454,z11,z1,z2,z3,z4,z6]),(1,[z11,z1,z2,z173,z4,z86]),(0,[z68,z11,z1,z2,z3,z73,z4])],[(0,[z11,z1,z2,z455,z3,z4,z6]),(0,[z456,z1,z28,z2,z3,z4,z6]),(0,[z1,z28,z2,z3,z4,z6,z51]),(0,[z1,z28,z2,z3,z24,z4,z6]),(0,[z11,z1,z457,z2,z3,z4,z6]),(0,[z11,z1,z458,z2,z3,z4,z6])]],
   [[(0,[z11,z1,z459,z2,z3,z4,z6]),(0,[z111,z1,z2,z3,z4,z67,z6]),(0,[z11,z1,z2,z3,z460,z4,z6]),(0,[z120,z1,z2,z3,z4,z5,z6]),(1,[z11,z54,z10,z3,z4,z6]),(0,[z11,z1,z2,z3,z4,z461,z6]),(0,[z1,z2,z3,z257,z127,z4,z6])],[(0,[z11,z1,z2,z462,z3,z4,z6]),(0,[z11,z1,z2,z3,z4,z463,z6]),(0,[z22,z11,z1,z2,z3,z438,z6]),(0,[z9,z1,z2,z3,z4,z162,z6]),(1,[z1,z141,z2,z3,z4,z6]),(0,[z464,z11,z1,z2,z3,z4,z6]),(0,[z218,z11,z1,z2,z3,z4,z6]),(1,[z1,z89,z2,z3,z4,z6])],[(0,[z20,z11,z1,z2,z3,z4,z6]),(0,[z1,z2,z3,z465,z4,z5,z6]),(0,[z14,z11,z1,z2,z3,z5,z6]),(0,[z466,z11,z1,z2,z3,z4,z6])],[(0,[z1,z28,z2,z3,z4,z118,z6]),(0,[z342,z1,z28,z2,z3,z4,z6]),(0,[z113,z21,z1,z2,z3,z4,z6]),(0,[z1,z467,z2,z3,z4,z5,z6]),(0,[z468,z11,z1,z2,z3,z4,z6]),(0,[z14,z346,z1,z2,z3,z4,z6])],[(0,[z11,z1,z469,z2,z3,z4,z6]),(0,[z111,z9,z1,z2,z3,z4,z6]),(1,[z62,z11,z12,z3,z4,z6]),(1,[z1,z153,z2,z3,z4,z6]),(0,[z169,z11,z2,z3,z4,z6,z106])],[(0,[z1,z2,z3,z4,z5,z67,z6]),(0,[z9,z0,z1,z2,z3,z4,z6]),(0,[z30,z9,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z4,z252,z6]),(0,[z11,z1,z2,z3,z4,z470,z6])],[(0,[z11,z1,z2,z3,z129,z4,z6]),(0,[z1,z23,z2,z42,z3,z4,z6]),(0,[z11,z471,z1,z2,z3,z4,z6]),(0,[z45,z11,z1,z278,z3,z4,z6]),(0,[z472,z11,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z4,z248,z6])],[(0,[z11,z1,z23,z2,z3,z4,z6]),(0,[z11,z1,z2,z102,z4,z19,z6]),(1,[z11,z212,z2,z52,z4,z6]),(0,[z11,z1,z2,z3,z257,z4,z6]),(0,[z11,z1,z2,z3,z4,z473,z6])]],
   [[(0,[z1,z2,z3,z84,z4,z5,z6]),(0,[z11,z1,z474,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z475,z4,z6])],[(0,[z1,z28,z91,z2,z3,z4,z6]),(0,[z125,z21,z1,z2,z3,z4,z6]),(0,[z476,z11,z1,z2,z3,z4,z6]),(0,[z68,z1,z2,z3,z4,z5,z6]),(0,[z134,z11,z1,z29,z2,z4,z6]),(0,[z11,z1,z2,z3,z477,z4,z6])],[(0,[z212,z1,z28,z2,z3,z4,z6]),(0,[z111,z11,z1,z176,z3,z4,z6]),(0,[z11,z1,z478,z2,z3,z4,z6]),(0,[z11,z1,z2,z42,z3,z4,z6]),(1,[z1,z2,z3,z5,z6,z51]),(0,[z11,z1,z2,z3,z479,z4,z6]),(0,[z480,z11,z1,z2,z3,z4,z6]),(0,[z11,z1,z481,z2,z3,z4,z6])],[(0,[z71,z11,z1,z2,z3,z4,z6]),(0,[z1,z23,z2,z3,z4,z67,z6]),(0,[z11,z1,z2,z3,z4,z482,z6]),(0,[z11,z1,z2,z3,z4,z6,z483]),(0,[z14,z11,z1,z2,z3,z118,z6])],[(0,[z14,z1,z28,z2,z3,z4,z6]),(0,[z1,z28,z2,z3,z4,z6,z31]),(0,[z11,z1,z164,z12,z3,z4,z6]),(0,[z11,z1,z484,z2,z3,z4,z6]),(0,[z45,z11,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z485,z4,z6]),(1,[z11,z1,z2,z486,z4,z6])],[(0,[z49,z21,z1,z2,z3,z4,z6]),(0,[z11,z1,z487,z2,z3,z4,z6]),(1,[z11,z1,z2,z3,z4,z210]),(0,[z11,z1,z488,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z489,z4,z6]),(0,[z11,z1,z2,z3,z4,z490,z6])],[(0,[z11,z1,z2,z3,z4,z491,z6]),(0,[z11,z1,z492,z2,z3,z4,z6])],[(0,[z22,z197,z1,z2,z3,z4,z6]),(0,[z11,z95,z1,z2,z3,z5,z6]),(0,[z169,z26,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z4,z6,z429]),(0,[z11,z493,z1,z2,z3,z4,z6]),(0,[z11,z1,z494,z2,z3,z4,z6]),(0,[z495,z11,z1,z2,z3,z4,z6])]],
   [[(0,[z22,z1,z28,z2,z3,z4,z6]),(0,[z496,z11,z1,z2,z3,z4,z6]),(0,[z380,z11,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z497,z4,z6]),(1,[z68,z11,z1,z2,z3,z73])],[(0,[z1,z28,z28,z2,z3,z4,z6]),(0,[z21,z1,z8,z2,z3,z4,z6]),(0,[z11,z1,z2,z498,z3,z4,z6]),(0,[z9,z54,z1,z2,z3,z4,z6]),(1,[z9,z1,z2,z3,z24,z6]),(0,[z11,z499,z1,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z67,z6,z31]),(0,[z500,z11,z1,z2,z3,z4,z6])],[(0,[z105,z11,z1,z2,z3,z4,z6]),(0,[z9,z1,z2,z501,z3,z4,z6])],[(0,[z456,z11,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z502,z3,z4,z6]),(0,[z11,z54,z10,z2,z3,z4,z6]),(0,[z14,z11,z1,z2,z3,z4,z503]),(0,[z504,z11,z1,z2,z3,z4,z6])],[(0,[z58,z11,z28,z2,z3,z4,z6]),(0,[z21,z1,z2,z3,z4,z5,z6]),(1,[z111,z1,z176,z3,z4,z6]),(0,[z1,z2,z3,z4,z5,z133,z6]),(0,[z11,z1,z2,z3,z4,z505,z6]),(0,[z54,z1,z141,z2,z3,z4,z6]),(0,[z11,z1,z506,z2,z3,z4,z6]),(0,[z11,z1,z2,z173,z3,z4,z86]),(0,[z134,z11,z1,z2,z4,z133,z6]),(0,[z68,z11,z1,z2,z3,z109,z6])],[(0,[z11,z1,z2,z3,z4,z6,z196]),(0,[z9,z9,z1,z2,z3,z4,z6]),(1,[z11,z1,z2,z238,z4,z6]),(0,[z11,z1,z2,z3,z4,z6,z507])],[(0,[z21,z1,z2,z3,z4,z82,z6]),(0,[z21,z1,z2,z3,z84,z4,z6]),(0,[z1,z2,z3,z4,z5,z13,z6]),(0,[z68,z11,z1,z2,z3,z5,z6]),(0,[z11,z508,z1,z2,z3,z4,z6]),(1,[z11,z1,z278,z3,z4,z6]),(1,[z330,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z4,z6,z509]),(0,[z11,z1,z510,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z511,z4,z6])],[(0,[z58,z9,z1,z2,z3,z4,z6]),(0,[z512,z11,z1,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z5,z6,z86]),(0,[z11,z1,z513,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z4,z6,z514]),(0,[z515,z11,z1,z2,z3,z4,z6])]],
   [[(0,[z11,z516,z1,z2,z3,z4,z6]),(0,[z277,z1,z2,z3,z4,z5,z6]),(1,[z11,z1,z2,z3,z4,z252]),(0,[z45,z11,z1,z2,z52,z4,z6]),(0,[z169,z11,z1,z2,z3,z131,z6]),(0,[z11,z1,z2,z3,z4,z517,z6])],[(0,[z169,z1,z2,z3,z4,z5,z6]),(0,[z11,z1,z2,z3,z352,z4,z6]),(0,[z11,z1,z2,z518,z3,z4,z6]),(0,[z169,z422,z1,z2,z3,z4,z6])],[(0,[z9,z1,z2,z12,z3,z4,z6]),(0,[z9,z1,z2,z171,z3,z4,z6]),(0,[z62,z11,z2,z12,z3,z4,z6]),(1,[z1,z2,z3,z4,z226,z6])],[(0,[z54,z1,z28,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z4,z6,z519])],[(1,[z11,z1,z2,z3,z4,z6]),(0,[z134,z1,z28,z2,z3,z4,z6]),(0,[z197,z11,z1,z2,z84,z4,z6]),(0,[z11,z1,z2,z3,z4,z51,z106]),(0,[z11,z1,z2,z3,z127,z4,z6]),(0,[z11,z1,z2,z3,z4,z133,z36])],[(0,[z21,z1,z2,z3,z4,z118,z6]),(0,[z9,z1,z298,z2,z3,z4,z6]),(0,[z169,z11,z1,z2,z321,z4,z6]),(0,[z11,z1,z2,z3,z4,z520,z6])],[(0,[z11,z1,z2,z3,z521,z4,z6]),(0,[z428,z11,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z522,z4,z6]),(0,[z11,z1,z2,z3,z4,z523,z6]),(0,[z63,z11,z1,z164,z3,z4,z6]),(0,[z11,z1,z2,z3,z4,z133,z6]),(0,[z11,z1,z2,z3,z109,z4,z6])],[(0,[z11,z524,z1,z2,z3,z4,z6]),(0,[z9,z1,z2,z3,z4,z4,z6]),(0,[z11,z1,z2,z3,z4,z37,z106])]],
   [[(0,[z68,z1,z28,z2,z3,z4,z6]),(1,[z11,z1,z91,z3,z4,z37]),(0,[z11,z1,z525,z2,z3,z4,z6])],[(0,[z63,z35,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z526,z3,z4,z6])],[(0,[z306,z11,z1,z2,z3,z4,z6]),(1,[z1,z527,z2,z3,z4,z6]),(0,[z528,z11,z1,z2,z3,z4,z6]),(0,[z110,z0,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z4,z6,z529])],[(0,[z11,z1,z2,z176,z3,z4,z6]),(0,[z11,z1,z530,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z4,z531,z6]),(0,[z9,z1,z2,z3,z94,z4,z6]),(0,[z9,z1,z2,z3,z4,z6,z86]),(0,[z11,z1,z2,z3,z4,z532,z6]),(0,[z11,z1,z2,z3,z4,z453,z6]),(0,[z11,z1,z2,z3,z533,z4,z6])],[(1,[z125,z1,z2,z3,z4,z6]),(0,[z22,z11,z1,z2,z3,z4,z6]),(0,[z9,z1,z2,z3,z48,z4,z6]),(1,[z49,z1,z2,z3,z4,z67]),(0,[z11,z1,z2,z3,z4,z6,z534]),(1,[z263,z1,z2,z3,z4,z6])],[(0,[z11,z1,z535,z2,z3,z4,z6]),(0,[z21,z1,z2,z3,z4,z145,z6]),(0,[z11,z212,z1,z2,z3,z4,z6]),(1,[z11,z1,z55,z3,z4,z6]),(0,[z134,z11,z1,z2,z3,z4,z133]),(0,[z536,z11,z1,z2,z3,z4,z6])],[(0,[z21,z1,z2,z3,z4,z6,z31]),(0,[z111,z11,z1,z2,z3,z359,z6]),(0,[z537,z11,z1,z2,z3,z4,z6])],[(0,[z11,z1,z2,z3,z538,z4,z6]),(0,[z11,z1,z2,z3,z539,z4,z6]),(0,[z540,z11,z1,z2,z3,z4,z6]),(0,[z60,z1,z2,z3,z4,z5,z6]),(0,[z11,z1,z2,z3,z4,z541,z6]),(0,[z1,z2,z3,z24,z4,z5,z6])]],
   [[(0,[z11,z1,z164,z2,z3,z4,z6])],[(0,[z542,z11,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z4,z389,z6]),(0,[z11,z1,z2,z102,z127,z4,z6])],[(0,[z11,z1,z543,z2,z3,z4,z6]),(0,[z72,z9,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z4,z544,z6]),(0,[z11,z1,z2,z3,z486,z4,z6]),(0,[z11,z1,z2,z3,z4,z545,z6]),(0,[z546,z11,z1,z2,z3,z4,z6]),(0,[z11,z547,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z173,z3,z4,z6]),(0,[z11,z1,z2,z3,z548,z4,z6])],[(0,[z21,z1,z28,z2,z3,z4,z6]),(0,[z11,z1,z2,z549,z3,z4,z6]),(0,[z550,z11,z1,z2,z3,z4,z6]),(0,[z11,z1,z164,z2,z3,z13,z6]),(0,[z11,z1,z551,z2,z3,z4,z6]),(0,[z11,z1,z2,z552,z3,z4,z6])],[(0,[z11,z1,z2,z3,z553,z4,z6]),(0,[z11,z1,z2,z554,z3,z4,z6]),(0,[z78,z9,z1,z2,z3,z4,z6]),(0,[z14,z11,z1,z2,z3,z24,z6]),(0,[z11,z1,z2,z3,z4,z162,z86]),(0,[z11,z1,z2,z3,z555,z4,z6])],[(0,[z58,z21,z1,z2,z3,z4,z6]),(0,[z21,z1,z2,z171,z3,z4,z6]),(0,[z11,z1,z556,z2,z3,z4,z6]),(0,[z11,z95,z1,z2,z3,z4,z6]),(0,[z14,z11,z1,z2,z3,z96,z6]),(0,[z11,z1,z2,z3,z4,z557,z6]),(0,[z11,z1,z2,z3,z4,z558,z6])],[(0,[z559,z11,z1,z2,z3,z4,z6]),(0,[z22,z11,z1,z2,z84,z4,z6]),(0,[z11,z1,z2,z3,z4,z6,z560]),(0,[z1,z2,z3,z4,z382,z5,z6]),(0,[z11,z1,z2,z102,z4,z6,z86]),(0,[z561,z11,z1,z2,z3,z4,z6]),(0,[z562,z11,z1,z2,z3,z4,z6])],[(0,[z277,z1,z28,z2,z3,z4,z6]),(0,[z1,z28,z10,z2,z3,z4,z6]),(0,[z563,z11,z1,z2,z3,z4,z6]),(0,[z14,z11,z2,z3,z4,z118,z6]),(0,[z11,z1,z2,z3,z564,z4,z6]),(0,[z11,z1,z565,z2,z3,z4,z6])]],
   [[(0,[z169,z1,z28,z2,z3,z4,z6]),(1,[z1,z2,z3,z4,z159,z6]),(0,[z21,z1,z298,z2,z3,z4,z6]),(0,[z21,z11,z253,z2,z3,z4,z6]),(0,[z113,z9,z1,z2,z3,z4,z6]),(0,[z49,z11,z1,z2,z3,z4,z67]),(0,[z11,z1,z2,z3,z4,z6,z136]),(0,[z11,z1,z2,z566,z3,z4,z6]),(0,[z11,z1,z8,z298,z3,z4,z6]),(0,[z11,z1,z2,z3,z4,z567,z6])],[(0,[z332,z9,z1,z2,z3,z4,z6]),(0,[z66,z11,z1,z12,z3,z4,z6]),(0,[z11,z1,z568,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z118,z19,z6]),(0,[z218,z1,z2,z3,z96,z4,z6]),(0,[z11,z1,z569,z2,z3,z4,z6]),(1,[z11,z1,z8,z29,z4,z6])],[(0,[z1,z28,z29,z2,z3,z4,z6]),(0,[z9,z1,z527,z2,z3,z4,z6]),(0,[z11,z1,z12,z3,z127,z4,z6]),(1,[z11,z1,z570,z3,z4,z6]),(0,[z11,z1,z2,z3,z4,z6,z571]),(0,[z11,z1,z2,z3,z73,z6,z51])],[(0,[z111,z1,z2,z3,z4,z5,z6]),(0,[z11,z1,z2,z3,z4,z6,z572]),(1,[z428,z1,z2,z3,z4,z6])],[(0,[z11,z1,z573,z2,z3,z4,z6]),(0,[z30,z1,z2,z3,z4,z5,z6]),(0,[z11,z1,z2,z3,z574,z4,z6]),(0,[z11,z1,z2,z313,z3,z4,z6]),(0,[z11,z1,z570,z2,z3,z4,z6]),(0,[z169,z11,z1,z2,z486,z4,z6]),(0,[z11,z1,z2,z575,z3,z4,z6]),(0,[z68,z11,z1,z2,z3,z4,z6])],[(0,[z360,z11,z1,z2,z3,z4,z6]),(0,[z576,z11,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z4,z162,z37]),(1,[z47,z1,z2,z3,z4,z6]),(0,[z195,z11,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z4,z577,z6])],[(0,[z1,z28,z2,z52,z3,z4,z6]),(0,[z21,z1,z2,z3,z94,z4,z6]),(0,[z11,z578,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z4,z579,z6]),(0,[z1,z2,z3,z96,z4,z5,z6]),(0,[z125,z9,z1,z2,z3,z4,z6]),(0,[z9,z1,z2,z3,z102,z4,z6]),(0,[z11,z54,z1,z12,z3,z4,z6]),(0,[z11,z1,z298,z2,z3,z4,z429]),(0,[z11,z1,z2,z580,z3,z4,z6])],[(0,[z11,z1,z2,z3,z301,z4,z6]),(0,[z11,z1,z581,z2,z3,z4,z6]),(1,[z11,z0,z2,z3,z4,z162]),(0,[z11,z582,z1,z2,z3,z4,z6])]],
   [[(1,[z21,z28,z2,z3,z4,z6]),(1,[z1,z2,z3,z94,z5,z6]),(0,[z1,z2,z3,z4,z5,z5,z6]),(1,[z11,z1,z2,z130,z4,z6]),(0,[z583,z11,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z171,z3,z19,z6]),(0,[z11,z1,z2,z3,z4,z584,z6])],[(0,[z95,z1,z28,z2,z3,z4,z6]),(0,[z66,z1,z28,z2,z3,z4,z6]),(0,[z585,z11,z1,z2,z3,z4,z6]),(0,[z11,z95,z1,z2,z3,z24,z6]),(0,[z11,z1,z91,z2,z163,z4,z6]),(0,[z11,z1,z2,z3,z4,z586,z6])],[(0,[z1,z535,z28,z2,z3,z4,z6]),(0,[z1,z28,z2,z3,z73,z4,z6]),(0,[z63,z21,z1,z2,z3,z4,z6]),(0,[z368,z11,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z4,z587,z6]),(0,[z11,z1,z2,z3,z3,z4,z6]),(0,[z11,z1,z588,z2,z3,z4,z6]),(0,[z11,z95,z1,z2,z3,z96,z6]),(0,[z11,z1,z2,z3,z4,z86,z106])],[(0,[z62,z11,z1,z2,z3,z179,z6]),(0,[z11,z1,z2,z48,z4,z19,z6]),(0,[z11,z1,z2,z589,z3,z4,z6])],[(0,[z11,z1,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z236,z3,z4,z6]),(1,[z11,z1,z2,z3,z438,z6]),(0,[z11,z1,z590,z2,z3,z4,z6]),(1,[z66,z11,z1,z3,z4,z36]),(0,[z11,z1,z2,z3,z591,z4,z6])],[(0,[z45,z11,z1,z2,z3,z4,z217]),(0,[z11,z1,z29,z2,z102,z4,z6]),(0,[z11,z1,z2,z3,z4,z592,z6]),(0,[z11,z1,z3,z127,z4,z6,z37]),(0,[z11,z1,z2,z3,z4,z6,z593]),(0,[z11,z1,z2,z3,z4,z19,z6])],[(0,[z1,z23,z2,z3,z4,z5,z6]),(0,[z11,z1,z2,z3,z4,z6,z594]),(0,[z11,z1,z2,z3,z4,z595,z6])],[(0,[z21,z11,z1,z2,z3,z4,z6]),(1,[z1,z124,z2,z3,z4,z6]),(0,[z21,z1,z2,z3,z4,z6,z37]),(0,[z11,z1,z2,z3,z4,z596,z6]),(0,[z11,z1,z2,z3,z4,z408,z6])]],
   [[(0,[z68,z11,z1,z2,z3,z24,z6]),(0,[z11,z1,z298,z2,z127,z4,z6]),(0,[z66,z11,z1,z2,z3,z4,z37]),(0,[z11,z1,z597,z2,z3,z4,z6])],[(0,[z1,z2,z3,z4,z5,z118,z6]),(0,[z1,z298,z2,z3,z4,z5,z6]),(0,[z9,z1,z8,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z4,z6,z598]),(0,[z11,z599,z1,z2,z3,z4,z6]),(0,[z68,z11,z1,z2,z3,z96,z6]),(0,[z11,z1,z2,z3,z4,z600,z6])],[(0,[z11,z1,z601,z2,z3,z4,z6]),(0,[z9,z1,z2,z3,z4,z6,z69]),(1,[z346,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z4,z162,z6]),(0,[z602,z11,z1,z2,z3,z4,z6])],[(0,[z277,z11,z1,z2,z3,z4,z6]),(0,[z1,z28,z2,z3,z4,z36,z6]),(0,[z11,z1,z2,z3,z73,z4,z162]),(0,[z11,z1,z2,z603,z3,z4,z6]),(0,[z604,z11,z1,z2,z3,z4,z6])],[(0,[z21,z253,z1,z2,z3,z4,z6]),(0,[z9,z1,z2,z3,z4,z5,z6]),(0,[z169,z11,z1,z2,z3,z4,z6]),(0,[z68,z11,z1,z2,z3,z4,z51])],[(0,[z11,z1,z2,z3,z4,z605,z6]),(1,[z1,z2,z3,z4,z145,z6]),(1,[z11,z1,z2,z3,z88,z6]),(1,[z1,z2,z3,z4,z104,z6])],[(0,[z9,z1,z2,z3,z84,z4,z6]),(0,[z1,z2,z258,z3,z4,z5,z6]),(0,[z30,z1,z2,z3,z4,z6,z31]),(0,[z11,z185,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z4,z6,z606]),(0,[z11,z1,z2,z607,z3,z4,z6]),(0,[z11,z0,z1,z2,z3,z4,z6]),(0,[z11,z1,z298,z3,z127,z4,z6]),(0,[z68,z400,z1,z2,z3,z4,z6])],[(0,[z11,z1,z2,z276,z3,z4,z6]),(0,[z11,z10,z2,z12,z3,z4,z6]),(0,[z11,z1,z2,z3,z73,z4,z106]),(0,[z608,z11,z1,z2,z3,z4,z6])]],
   [[(0,[z197,z21,z1,z2,z3,z4,z6]),(0,[z609,z11,z1,z2,z3,z4,z6]),(1,[z221,z1,z2,z3,z4,z6])],[(0,[z21,z1,z2,z3,z102,z4,z6]),(0,[z9,z1,z2,z3,z4,z6,z51]),(0,[z9,z1,z2,z3,z24,z4,z6]),(0,[z212,z1,z103,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z610,z4,z6])],[(0,[z1,z2,z3,z4,z5,z6,z31]),(0,[z11,z1,z611,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z4,z6,z612])],[(1,[z1,z28,z2,z3,z4,z6]),(0,[z30,z1,z28,z2,z3,z4,z6]),(0,[z253,z1,z2,z3,z4,z5,z6]),(0,[z613,z11,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z4,z6,z614]),(0,[z1,z2,z3,z4,z544,z5,z6]),(1,[z30,z1,z2,z3,z4,z31]),(0,[z615,z11,z1,z2,z3,z4,z6]),(0,[z11,z2,z3,z96,z4,z118,z6]),(0,[z66,z11,z1,z2,z3,z4,z36])],[(0,[z21,z1,z17,z2,z3,z4,z6]),(0,[z21,z1,z29,z2,z3,z4,z6]),(1,[z60,z1,z23,z3,z4,z6]),(0,[z11,z1,z2,z616,z3,z4,z6]),(0,[z11,z0,z2,z3,z4,z162,z6]),(0,[z11,z1,z2,z3,z4,z36,z162]),(0,[z11,z1,z2,z3,z617,z4,z6]),(0,[z154,z1,z2,z3,z94,z4,z6])],[(0,[z111,z60,z1,z2,z3,z4,z6]),(0,[z11,z1,z618,z2,z3,z4,z6]),(0,[z9,z1,z2,z3,z4,z118,z6]),(0,[z62,z11,z1,z2,z3,z239,z6]),(1,[z11,z1,z2,z3,z4,z217]),(0,[z11,z1,z2,z3,z96,z6,z51]),(0,[z11,z1,z2,z3,z619,z4,z6]),(0,[z66,z11,z1,z2,z3,z4,z6]),(0,[z68,z7,z1,z2,z3,z4,z6])],[(0,[z11,z1,z2,z3,z4,z503,z6]),(0,[z40,z95,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z620,z4,z6]),(0,[z11,z1,z621,z2,z3,z4,z6])],[(0,[z11,z1,z2,z3,z4,z622,z6]),(0,[z11,z1,z2,z3,z4,z59,z6]),(0,[z21,z1,z2,z284,z3,z4,z6]),(0,[z11,z1,z2,z3,z4,z623,z6]),(0,[z11,z1,z624,z2,z3,z4,z6]),(1,[z11,z1,z2,z3,z109,z51])]],
   [[(0,[z21,z1,z2,z52,z3,z4,z6]),(0,[z11,z1,z2,z3,z625,z4,z6]),(0,[z169,z11,z1,z2,z3,z626,z6]),(0,[z11,z1,z2,z3,z4,z36,z106])],[(0,[z1,z91,z2,z3,z4,z5,z6]),(0,[z281,z1,z2,z3,z4,z5,z6]),(0,[z9,z11,z1,z2,z3,z5,z6]),(1,[z11,z1,z2,z3,z4,z453]),(0,[z11,z1,z2,z3,z627,z4,z6])],[(1,[z11,z1,z2,z3,z145,z6]),(0,[z11,z1,z2,z3,z628,z4,z6]),(1,[z1,z2,z3,z4,z382,z6]),(0,[z11,z1,z2,z3,z4,z67,z6]),(0,[z11,z1,z629,z2,z3,z4,z6]),(0,[z11,z54,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z630,z4,z6]),(1,[z11,z1,z2,z3,z4,z503]),(0,[z11,z1,z2,z631,z3,z4,z6]),(0,[z11,z1,z89,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z4,z162,z51]),(0,[z11,z1,z632,z2,z3,z4,z6])],[(0,[z11,z633,z1,z2,z3,z4,z6]),(0,[z9,z1,z91,z2,z3,z4,z6]),(0,[z11,z1,z2,z501,z3,z4,z6]),(0,[z169,z11,z1,z79,z3,z4,z6]),(1,[z1,z2,z3,z4,z245,z6])],[(0,[z21,z1,z2,z3,z73,z4,z6]),(0,[z350,z11,z1,z2,z3,z4,z6]),(0,[z241,z11,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z4,z133,z37]),(0,[z11,z1,z2,z3,z4,z634,z6]),(0,[z11,z1,z2,z173,z4,z6,z86])],[(0,[z1,z28,z2,z3,z96,z4,z6]),(0,[z1,z28,z2,z176,z3,z4,z6]),(0,[z403,z11,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z4,z635,z6])],[(0,[z14,z21,z1,z2,z3,z4,z6]),(0,[z9,z1,z2,z3,z4,z6,z31]),(0,[z11,z1,z636,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z4,z6,z637]),(0,[z638,z11,z1,z2,z3,z4,z6])],[(0,[z11,z1,z2,z3,z118,z13,z6]),(1,[z1,z2,z3,z4,z209,z6])]],
   [[(0,[z639,z11,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z386,z3,z4,z6]),(0,[z330,z11,z1,z2,z3,z4,z6]),(0,[z11,z1,z164,z3,z94,z4,z6]),(0,[z11,z640,z1,z2,z3,z4,z6])],[(0,[z72,z1,z2,z3,z4,z5,z6]),(0,[z62,z11,z1,z10,z3,z4,z6]),(0,[z45,z11,z1,z2,z3,z32,z6])],[(0,[z22,z21,z1,z2,z3,z4,z6]),(0,[z9,z197,z1,z2,z3,z4,z6]),(0,[z169,z11,z1,z570,z3,z4,z6]),(0,[z11,z1,z2,z3,z4,z6,z641]),(0,[z113,z403,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z642,z4,z6]),(0,[z643,z11,z1,z2,z3,z4,z6])],[(0,[z9,z1,z28,z2,z3,z4,z6]),(0,[z644,z11,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z5,z6,z51]),(0,[z11,z1,z2,z12,z3,z4,z6]),(0,[z11,z95,z1,z2,z3,z118,z6]),(0,[z11,z1,z645,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z4,z646,z6])],[(0,[z647,z11,z1,z2,z3,z4,z6]),(0,[z21,z1,z2,z3,z4,z6,z51]),(0,[z21,z1,z2,z3,z24,z4,z6]),(0,[z11,z1,z2,z3,z648,z4,z6]),(0,[z11,z1,z164,z2,z3,z94,z6]),(0,[z11,z649,z1,z2,z3,z4,z6])],[(0,[z21,z1,z2,z3,z4,z36,z6]),(0,[z9,z167,z1,z2,z3,z4,z6])],[(0,[z111,z11,z1,z2,z3,z4,z6]),(0,[z9,z60,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z650,z3,z4,z6]),(0,[z11,z1,z298,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z4,z651,z6])],[(0,[z113,z1,z2,z3,z4,z5,z6]),(0,[z30,z11,z1,z2,z3,z4,z6])]],
   [[(0,[z11,z1,z2,z3,z4,z4,z6]),(0,[z652,z11,z1,z2,z3,z4,z6])],[(0,[z11,z1,z2,z3,z653,z4,z6]),(0,[z11,z1,z654,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z4,z6,z655]),(0,[z11,z1,z656,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z4,z657,z6])],[(0,[z58,z11,z253,z2,z3,z4,z6]),(0,[z253,z1,z28,z2,z3,z4,z6]),(0,[z658,z11,z1,z2,z3,z4,z6]),(0,[z11,z212,z1,z2,z102,z4,z6]),(0,[z68,z11,z1,z2,z3,z118,z6]),(0,[z659,z11,z1,z2,z3,z4,z6]),(0,[z11,z1,z29,z3,z127,z4,z6]),(1,[z154,z1,z2,z3,z4,z6]),(0,[z11,z1,z660,z2,z3,z4,z6]),(0,[z11,z1,z2,z173,z3,z4,z133]),(0,[z11,z1,z2,z3,z661,z4,z6])],[(0,[z1,z2,z3,z4,z5,z6,z37]),(0,[z662,z11,z1,z2,z3,z4,z6]),(0,[z422,z11,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z4,z13,z6]),(0,[z11,z1,z2,z3,z4,z663,z6])],[(0,[z664,z11,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z465,z4,z6]),(0,[z665,z11,z1,z2,z3,z4,z6]),(0,[z11,z1,z8,z2,z127,z4,z6]),(0,[z11,z1,z2,z3,z94,z4,z6]),(0,[z11,z1,z2,z3,z4,z666,z6]),(0,[z667,z11,z1,z2,z3,z4,z6]),(1,[z11,z1,z2,z171,z48,z6]),(0,[z11,z1,z2,z3,z4,z6,z86])],[(0,[z11,z1,z668,z2,z3,z4,z6]),(0,[z1,z2,z12,z3,z4,z5,z6]),(0,[z62,z11,z1,z2,z313,z4,z6]),(0,[z11,z1,z2,z3,z48,z4,z6]),(0,[z11,z1,z2,z3,z4,z669,z6])],[(0,[z1,z402,z28,z2,z3,z4,z6]),(0,[z21,z1,z91,z2,z3,z4,z6]),(0,[z134,z21,z1,z2,z3,z4,z6]),(0,[z11,z1,z8,z12,z3,z4,z6]),(0,[z11,z1,z2,z3,z670,z4,z6]),(0,[z671,z11,z1,z2,z3,z4,z6])],[(0,[z672,z11,z1,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z4,z5,z6]),(0,[z63,z9,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z24,z19,z6]),(0,[z11,z1,z2,z171,z52,z4,z6]),(0,[z11,z1,z2,z3,z673,z4,z6]),(0,[z113,z11,z1,z2,z3,z19,z6])]],
   [[(0,[z1,z2,z42,z3,z4,z67,z6]),(0,[z674,z11,z1,z2,z3,z4,z6]),(0,[z675,z11,z1,z2,z3,z4,z6])],[(0,[z1,z2,z52,z3,z4,z5,z6]),(0,[z49,z1,z2,z3,z4,z5,z6]),(0,[z676,z11,z1,z2,z3,z4,z6])],[(0,[z11,z1,z677,z2,z3,z4,z6])],[(0,[z424,z21,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z678,z4,z6]),(0,[z11,z1,z2,z3,z4,z6,z210]),(1,[z11,z1,z2,z3,z626,z6])],[(0,[z679,z11,z1,z2,z3,z4,z6]),(0,[z30,z22,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z680,z3,z4,z6]),(0,[z197,z1,z2,z42,z3,z4,z6]),(0,[z11,z1,z2,z3,z4,z681,z6]),(0,[z11,z1,z682,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z4,z626,z6]),(0,[z11,z1,z267,z173,z3,z4,z6]),(0,[z11,z1,z2,z683,z3,z4,z6])],[(0,[z134,z11,z1,z2,z102,z4,z6])],[(0,[z684,z11,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z685,z3,z4,z6]),(0,[z686,z11,z1,z2,z3,z4,z6]),(0,[z125,z1,z2,z3,z4,z118,z6]),(0,[z11,z1,z2,z3,z4,z687,z6]),(1,[z11,z1,z79,z3,z4,z6]),(0,[z11,z1,z2,z3,z4,z6,z688]),(0,[z11,z1,z2,z689,z3,z4,z6])],[(0,[z1,z28,z2,z3,z4,z19,z6]),(0,[z21,z1,z2,z3,z96,z4,z6]),(1,[z11,z1,z2,z3,z129,z6]),(0,[z9,z11,z1,z2,z3,z4,z6]),(0,[z1,z2,z173,z3,z4,z5,z6]),(0,[z9,z1,z2,z3,z4,z6,z37])]],
   [[(0,[z72,z1,z28,z2,z3,z4,z6]),(0,[z393,z11,z1,z2,z3,z4,z6]),(0,[z690,z11,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z691,z4,z6])],[(0,[z1,z28,z2,z3,z4,z6,z106]),(0,[z11,z692,z1,z2,z3,z4,z6]),(0,[z693,z11,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z694,z4,z6]),(0,[z695,z11,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z109,z4,z51]),(1,[z400,z1,z2,z3,z4,z6])],[(1,[z1,z2,z3,z4,z248,z6]),(0,[z1,z2,z3,z109,z4,z408,z6]),(0,[z11,z1,z2,z3,z73,z109,z4])],[(0,[z696,z11,z1,z2,z3,z4,z6]),(0,[z11,z1,z467,z2,z3,z4,z6]),(0,[z9,z1,z2,z251,z3,z4,z6]),(0,[z11,z1,z527,z2,z3,z4,z6]),(0,[z697,z11,z1,z2,z3,z4,z6]),(0,[z11,z2,z3,z4,z162,z6,z106])],[(0,[z11,z1,z2,z3,z392,z4,z6]),(0,[z62,z21,z1,z2,z3,z4,z6]),(0,[z9,z253,z1,z2,z3,z4,z6]),(0,[z11,z1,z698,z2,z3,z4,z6]),(0,[z1,z164,z2,z3,z4,z5,z6]),(0,[z11,z1,z699,z2,z3,z4,z6]),(0,[z11,z1,z29,z298,z2,z4,z6]),(0,[z68,z11,z1,z2,z3,z73,z6])],[(0,[z1,z28,z459,z2,z3,z4,z6]),(0,[z21,z11,z1,z2,z3,z145,z6]),(0,[z1,z2,z3,z109,z4,z5,z6])],[(0,[z11,z700,z1,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z505,z5,z6]),(0,[z11,z1,z2,z3,z88,z4,z6]),(0,[z11,z287,z1,z2,z3,z4,z6])],[(0,[z412,z11,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z701,z3,z4,z6]),(0,[z11,z1,z2,z3,z4,z702,z6]),(0,[z11,z1,z2,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z5,z159,z6]),(0,[z1,z2,z3,z4,z5,z296,z6]),(0,[z11,z1,z703,z2,z3,z4,z6]),(0,[z704,z11,z1,z2,z3,z4,z6]),(0,[z11,z1,z705,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z4,z706,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z11,z1,z2,z3,z4,z707]),(0,[z1,z2,z3,z4,z708,z6]),(0,[z11,z1,z90,z2,z4,z6])],[(0,[z11,z1,z2,z3,z145,z6]),(0,[z1,z2,z3,z4,z382,z6]),(0,[z1,z2,z3,z5,z6,z507]),(0,[z87,z1,z3,z4,z356,z6]),(0,[z11,z1,z2,z3,z709,z6]),(0,[z710,z1,z2,z3,z4,z6])],[(0,[z1,z23,z3,z4,z505,z6]),(0,[z1,z2,z3,z4,z245,z6]),(0,[z1,z2,z3,z382,z13,z6])],[(0,[z1,z79,z3,z4,z5,z6]),(0,[z711,z1,z2,z3,z4,z6]),(0,[z712,z1,z2,z3,z4,z6]),(0,[z1,z713,z2,z3,z4,z6]),(0,[z11,z1,z3,z188,z4,z86])],[(0,[z1,z28,z2,z3,z32,z6]),(0,[z111,z1,z714,z3,z4,z6]),(0,[z9,z1,z2,z3,z180,z6])],[(0,[z1,z2,z3,z94,z382,z6]),(0,[z62,z11,z12,z3,z239,z6]),(0,[z11,z1,z2,z3,z4,z715]),(0,[z11,z1,z3,z127,z4,z429]),(0,[z11,z1,z90,z91,z4,z37])],[(0,[z1,z28,z2,z3,z626,z6]),(0,[z253,z1,z2,z3,z145,z6]),(0,[z11,z1,z2,z3,z716,z6]),(0,[z1,z2,z3,z48,z382,z6]),(0,[z11,z1,z2,z3,z717,z6])],[(0,[z28,z2,z3,z4,z6,z419]),(0,[z1,z718,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z719,z6]),(0,[z1,z46,z3,z4,z5,z6]),(0,[z1,z2,z3,z479,z5,z6]),(0,[z11,z1,z2,z3,z179,z252]),(0,[z720,z1,z2,z3,z4,z6]),(0,[z721,z1,z2,z3,z4,z6])],[(0,[z30,z1,z2,z3,z232,z31]),(0,[z11,z1,z2,z722,z4,z6])],[(0,[z125,z1,z2,z3,z145,z6]),(0,[z1,z2,z3,z520,z5,z6]),(0,[z11,z2,z3,z4,z6,z723]),(0,[z160,z1,z2,z3,z13,z6])],[(0,[z1,z28,z2,z3,z129,z6]),(0,[z724,z1,z2,z3,z145,z6]),(0,[z125,z527,z2,z3,z4,z6]),(0,[z21,z1,z55,z3,z4,z6]),(0,[z11,z1,z2,z4,z725,z6]),(0,[z11,z1,z2,z3,z673,z51])],[(0,[z1,z124,z2,z3,z76,z6]),(0,[z1,z10,z2,z3,z145,z6]),(0,[z1,z2,z3,z102,z145,z6]),(0,[z21,z369,z2,z3,z4,z6]),(0,[z11,z726,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z727,z6]),(0,[z728,z1,z2,z3,z4,z6])],[(0,[z412,z1,z2,z284,z4,z6]),(0,[z62,z12,z3,z4,z5,z6]),(0,[z1,z2,z3,z5,z13,z6]),(0,[z11,z1,z2,z3,z4,z729]),(0,[z66,z11,z1,z163,z4,z6])],[(0,[z132,z28,z2,z3,z4,z6]),(0,[z11,z1,z2,z730,z4,z6]),(0,[z1,z2,z3,z328,z5,z6]),(0,[z11,z379,z10,z3,z4,z6]),(0,[z346,z1,z2,z130,z4,z6]),(0,[z11,z1,z2,z3,z731,z6])],[(0,[z1,z29,z2,z3,z145,z6]),(0,[z1,z2,z498,z3,z5,z6]),(0,[z11,z732,z2,z3,z4,z6]),(0,[z1,z2,z3,z733,z4,z6]),(0,[z1,z2,z3,z4,z734,z6]),(0,[z1,z735,z2,z3,z4,z6]),(0,[z1,z2,z3,z131,z736,z6])],[(0,[z1,z124,z2,z3,z159,z6]),(0,[z1,z23,z714,z3,z4,z6]),(0,[z60,z1,z61,z3,z4,z6]),(0,[z45,z11,z2,z102,z180,z6]),(0,[z11,z1,z3,z737,z4,z6]),(0,[z738,z1,z2,z3,z4,z6])]],
   [[(0,[z212,z2,z52,z4,z5,z6]),(0,[z1,z2,z3,z5,z6,z534])],[(0,[z1,z2,z284,z3,z145,z6]),(0,[z62,z11,z739,z3,z4,z6]),(0,[z1,z2,z3,z4,z740,z6]),(0,[z11,z1,z2,z3,z4,z741])],[(0,[z1,z2,z52,z3,z145,z6]),(0,[z1,z2,z3,z4,z742,z6]),(0,[z542,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z121,z5,z51]),(0,[z11,z2,z3,z743,z4,z6]),(0,[z11,z1,z2,z744,z4,z6])],[(0,[z128,z28,z2,z3,z4,z6]),(0,[z14,z21,z2,z3,z118,z6]),(0,[z14,z1,z2,z130,z5,z6]),(0,[z11,z1,z2,z171,z48,z6])],[(0,[z344,z1,z2,z3,z5,z6]),(0,[z14,z95,z2,z3,z5,z6]),(0,[z745,z1,z2,z3,z4,z6])],[(0,[z21,z487,z2,z3,z4,z6]),(0,[z11,z1,z2,z746,z4,z6]),(0,[z1,z2,z42,z4,z544,z6])],[(0,[z11,z1,z2,z238,z239,z6]),(0,[z11,z1,z2,z3,z747,z6]),(0,[z263,z1,z2,z3,z48,z6]),(0,[z11,z1,z267,z173,z4,z86])],[(0,[z63,z1,z2,z3,z145,z6]),(0,[z21,z1,z570,z3,z4,z6]),(0,[z110,z1,z2,z3,z748,z6])],[(0,[z21,z1,z2,z3,z749,z6]),(0,[z11,z1,z2,z3,z32,z6]),(0,[z750,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z751,z6])],[(0,[z11,z1,z752,z3,z4,z6]),(0,[z1,z28,z2,z3,z39,z6]),(0,[z9,z212,z2,z52,z4,z6]),(0,[z11,z1,z2,z3,z239,z252])],[],[(0,[z113,z1,z28,z2,z19,z6]),(0,[z1,z2,z3,z145,z6,z106]),(0,[z1,z2,z3,z522,z5,z6])],[(0,[z21,z0,z2,z3,z4,z162]),(0,[z60,z1,z2,z3,z39,z6]),(0,[z1,z2,z3,z44,z67,z6]),(0,[z1,z2,z3,z5,z6,z136]),(0,[z1,z3,z753,z4,z5,z6]),(0,[z11,z1,z2,z3,z754,z6])],[(0,[z9,z1,z2,z3,z622,z6]),(0,[z1,z755,z2,z3,z145,z6]),(0,[z756,z1,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z757,z6]),(0,[z62,z11,z12,z313,z4,z6])],[(0,[z11,z1,z2,z3,z129,z6]),(0,[z11,z758,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z759,z6]),(0,[z63,z160,z1,z3,z13,z6])],[(0,[z643,z1,z2,z3,z5,z6]),(0,[z9,z1,z2,z3,z4,z210]),(0,[z11,z1,z760,z3,z4,z6]),(0,[z134,z11,z1,z188,z4,z6])]],
   [[(0,[z1,z2,z3,z533,z5,z6]),(0,[z11,z1,z2,z3,z761,z6])],[(0,[z202,z28,z2,z3,z4,z6]),(0,[z21,z1,z2,z3,z438,z6]),(0,[z1,z2,z3,z4,z67,z560]),(0,[z762,z1,z2,z3,z179,z6])],[(0,[z11,z1,z2,z3,z763,z6]),(0,[z1,z2,z3,z257,z4,z6]),(0,[z1,z12,z3,z5,z13,z6]),(0,[z14,z11,z2,z3,z118,z6]),(0,[z95,z2,z3,z96,z104,z6])],[(0,[z11,z1,z2,z3,z764,z6]),(0,[z11,z95,z2,z3,z717,z6]),(0,[z765,z1,z2,z3,z4,z6]),(0,[z766,z1,z2,z3,z4,z6])],[(0,[z11,z1,z767,z3,z4,z6]),(0,[z1,z2,z3,z4,z768,z6])],[(0,[z22,z1,z2,z84,z4,z6])],[(0,[z11,z1,z2,z3,z4,z769])],[(0,[z111,z1,z85,z3,z4,z6]),(0,[z9,z1,z2,z3,z4,z136])],[(0,[z21,z54,z10,z3,z4,z6]),(0,[z1,z2,z3,z626,z770,z6])],[(0,[z20,z1,z2,z3,z145,z6]),(0,[z22,z1,z2,z3,z232,z6]),(0,[z771,z1,z3,z4,z5,z6])],[(0,[z1,z28,z46,z3,z4,z6]),(0,[z45,z21,z2,z102,z4,z6]),(0,[z49,z1,z2,z3,z145,z6]),(0,[z122,z1,z2,z3,z44,z6]),(0,[z95,z1,z2,z3,z5,z6]),(0,[z1,z772,z2,z3,z4,z5]),(0,[z11,z2,z3,z4,z717,z6])],[],[(0,[z773,z1,z2,z3,z4,z6])],[(0,[z11,z1,z2,z3,z39,z6]),(0,[z380,z1,z2,z84,z4,z6]),(0,[z14,z1,z2,z3,z5,z503]),(0,[z11,z1,z377,z3,z94,z6]),(0,[z11,z1,z55,z15,z4,z6]),(0,[z11,z1,z2,z163,z4,z6])],[(0,[z11,z1,z2,z774,z4,z6])],[(0,[z110,z1,z2,z3,z775,z6]),(0,[z1,z776,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z777,z6])]],
   [[(0,[z11,z1,z2,z3,z778,z6]),(0,[z45,z2,z102,z4,z5,z6]),(0,[z75,z11,z12,z3,z4,z6]),(0,[z169,z11,z570,z3,z4,z106]),(0,[z11,z1,z779,z3,z4,z6])],[(0,[z1,z2,z321,z4,z5,z6]),(0,[z11,z1,z2,z313,z4,z252]),(0,[z11,z1,z91,z163,z4,z37])],[(0,[z169,z1,z2,z3,z145,z6]),(0,[z68,z1,z2,z3,z5,z6]),(0,[z9,z1,z91,z3,z4,z37]),(0,[z1,z2,z3,z780,z4,z6])],[(0,[z781,z1,z2,z3,z4,z6]),(0,[z782,z1,z2,z3,z4,z6]),(0,[z11,z1,z8,z703,z4,z6]),(0,[z11,z1,z2,z783,z4,z6]),(0,[z784,z1,z2,z3,z4,z429])],[(0,[z700,z28,z2,z3,z4,z6]),(0,[z21,z1,z2,z486,z4,z6]),(0,[z785,z1,z2,z4,z5,z6]),(0,[z786,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z787,z6])],[(0,[z30,z1,z2,z3,z4,z196]),(0,[z788,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z321,z131,z6])],[(0,[z21,z1,z2,z3,z4,z453]),(0,[z789,z1,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z5,z790]),(0,[z1,z3,z188,z4,z5,z6]),(0,[z791,z1,z2,z3,z4,z6])],[(0,[z11,z1,z2,z3,z792,z6]),(0,[z11,z1,z2,z575,z4,z86])],[(0,[z793,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z794,z4,z6]),(0,[z11,z1,z3,z4,z795,z37])],[(0,[z9,z1,z2,z3,z359,z6]),(0,[z11,z1,z2,z3,z796,z6])],[(0,[z1,z219,z2,z3,z4,z59]),(0,[z11,z1,z2,z3,z797,z6]),(0,[z11,z1,z2,z3,z798,z6]),(0,[z799,z1,z2,z3,z4,z6]),(0,[z1,z2,z3,z444,z5,z6]),(0,[z1,z800,z2,z3,z4,z6])],[(0,[z128,z2,z3,z4,z159,z6]),(0,[z801,z1,z2,z3,z4,z6])],[(0,[z277,z1,z2,z3,z145,z6]),(0,[z1,z2,z714,z3,z4,z6]),(0,[z11,z1,z2,z3,z802,z6]),(0,[z803,z1,z2,z3,z4,z6])],[(0,[z804,z1,z2,z3,z4,z6]),(0,[z805,z1,z2,z3,z94,z6]),(0,[z45,z185,z2,z102,z4,z6]),(0,[z806,z1,z2,z3,z4,z6])],[(0,[z21,z1,z278,z3,z4,z6]),(0,[z11,z1,z2,z3,z807,z6]),(0,[z11,z1,z46,z3,z4,z6]),(0,[z14,z11,z2,z130,z118,z6])],[(0,[z0,z28,z2,z3,z4,z162])]],
   [[(0,[z1,z23,z3,z140,z4,z6])],[(0,[z11,z1,z2,z3,z808,z6])],[(0,[z1,z2,z3,z669,z5,z6]),(0,[z11,z1,z2,z809,z4,z6])],[(0,[z68,z1,z2,z3,z145,z6]),(0,[z9,z1,z8,z29,z4,z6]),(0,[z11,z1,z2,z3,z4,z810]),(0,[z14,z428,z2,z3,z118,z6])],[(0,[z78,z1,z2,z352,z4,z6]),(0,[z1,z811,z2,z3,z4,z6]),(0,[z11,z1,z2,z812,z4,z6]),(0,[z813,z1,z2,z3,z4,z6]),(0,[z169,z422,z2,z3,z4,z106]),(0,[z11,z1,z2,z814,z4,z6])],[(0,[z1,z2,z3,z4,z815,z6]),(0,[z9,z1,z2,z3,z131,z6]),(0,[z11,z1,z2,z3,z4,z816]),(0,[z11,z1,z3,z4,z795,z6]),(0,[z1,z2,z3,z4,z817,z6])],[(0,[z268,z1,z176,z3,z4,z6]),(0,[z1,z2,z3,z5,z6,z641]),(0,[z1,z2,z3,z4,z5,z818]),(0,[z11,z1,z2,z3,z819,z4]),(0,[z11,z1,z820,z3,z4,z6]),(0,[z821,z1,z2,z3,z4,z6])],[(0,[z1,z28,z298,z127,z4,z6]),(0,[z287,z1,z2,z238,z4,z6])],[(0,[z11,z1,z2,z822,z4,z6])],[(0,[z11,z1,z2,z3,z823,z6]),(0,[z9,z1,z255,z3,z4,z6])],[(0,[z108,z1,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z824,z6]),(0,[z11,z1,z2,z3,z825,z6]),(0,[z287,z1,z2,z3,z4,z252])],[(0,[z14,z1,z2,z3,z145,z6])],[(0,[z1,z28,z2,z3,z4,z429]),(0,[z1,z2,z42,z653,z4,z6]),(0,[z805,z1,z2,z3,z4,z6]),(0,[z53,z54,z10,z3,z4,z6]),(0,[z826,z1,z2,z3,z4,z6]),(1,[z11,z1,z163,z4,z37]),(0,[z1,z2,z3,z4,z6,z827])],[(0,[z111,z1,z2,z3,z145,z6]),(0,[z11,z1,z2,z3,z828,z6]),(0,[z1,z2,z3,z4,z6,z829]),(0,[z169,z11,z2,z486,z4,z106])],[(0,[z11,z1,z2,z3,z830,z6]),(0,[z1,z2,z3,z4,z5,z210]),(0,[z1,z2,z3,z4,z6,z831]),(0,[z832,z1,z2,z3,z4,z6]),(0,[z833,z1,z2,z3,z131,z6])],[(0,[z1,z2,z3,z44,z5,z6]),(0,[z834,z1,z2,z3,z4,z6]),(0,[z1,z835,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z4,z836])]],
   [[(0,[z1,z2,z3,z159,z19,z6]),(0,[z11,z1,z2,z3,z837,z6]),(0,[z11,z1,z838,z3,z4,z6]),(0,[z633,z1,z2,z3,z5,z6]),(0,[z11,z1,z2,z3,z180,z453])],[(0,[z2,z3,z4,z382,z159,z6]),(0,[z11,z1,z2,z3,z839,z6]),(0,[z840,z1,z2,z3,z4,z6]),(0,[z11,z1,z3,z188,z4,z133])],[(0,[z28,z2,z441,z3,z4,z6]),(0,[z21,z578,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z841,z6]),(0,[z11,z1,z2,z15,z118,z6]),(0,[z378,z11,z1,z3,z4,z36])],[(0,[z1,z714,z176,z3,z4,z6]),(0,[z9,z1,z2,z3,z5,z6]),(0,[z66,z1,z3,z4,z5,z36]),(0,[z30,z1,z2,z3,z4,z831]),(0,[z185,z1,z2,z3,z4,z453]),(0,[z11,z1,z842,z3,z4,z6])],[(0,[z1,z843,z2,z3,z4,z6]),(0,[z844,z1,z28,z3,z4,z6]),(0,[z111,z1,z251,z3,z4,z6]),(0,[z197,z1,z2,z3,z44,z6]),(0,[z11,z1,z845,z3,z4,z6])],[(0,[z169,z9,z2,z3,z4,z106]),(0,[z1,z2,z3,z4,z6,z846]),(0,[z11,z1,z2,z3,z626,z162]),(0,[z1,z847,z2,z3,z4,z6])],[(0,[z1,z2,z3,z4,z5,z136]),(0,[z11,z1,z3,z4,z36,z795])],[(0,[z1,z2,z3,z4,z848,z6]),(0,[z9,z1,z2,z3,z88,z6]),(0,[z849,z1,z2,z3,z239,z6]),(0,[z40,z95,z2,z3,z96,z6]),(0,[z11,z1,z850,z2,z4,z6])],[(0,[z1,z23,z2,z3,z145,z6]),(0,[z403,z1,z2,z3,z4,z6]),(0,[z11,z1,z278,z3,z180,z6]),(0,[z11,z1,z851,z3,z4,z6]),(0,[z14,z11,z2,z3,z118,z503]),(0,[z11,z1,z79,z3,z4,z162]),(0,[z1,z852,z2,z3,z4,z6])],[(0,[z1,z2,z3,z352,z5,z6]),(0,[z11,z1,z2,z3,z626,z106]),(0,[z1,z853,z2,z3,z4,z6])],[(0,[z218,z1,z2,z3,z4,z6]),(0,[z1,z90,z2,z4,z5,z6])],[(0,[z854,z1,z2,z3,z4,z6]),(0,[z1,z2,z42,z3,z145,z6]),(0,[z1,z2,z42,z855,z4,z6]),(0,[z185,z1,z278,z3,z4,z6]),(0,[z11,z1,z2,z3,z4,z856]),(0,[z11,z1,z298,z127,z4,z6]),(0,[z857,z1,z2,z3,z4,z6])],[(0,[z1,z28,z2,z163,z4,z6]),(0,[z1,z2,z3,z145,z19,z6]),(0,[z11,z1,z2,z3,z858,z6]),(0,[z11,z1,z2,z3,z859,z6]),(0,[z11,z1,z79,z3,z4,z106]),(0,[z860,z1,z2,z3,z4,z6])],[(0,[z1,z570,z3,z4,z5,z6]),(0,[z350,z1,z2,z238,z4,z6]),(0,[z1,z2,z3,z4,z861,z6])],[(0,[z1,z2,z3,z862,z4,z159]),(0,[z1,z2,z3,z521,z5,z6]),(0,[z2,z3,z4,z382,z118,z6]),(0,[z1,z2,z3,z863,z4,z6]),(0,[z1,z864,z2,z3,z4,z6]),(0,[z11,z1,z2,z81,z4,z86])],[(0,[z1,z28,z2,z3,z778,z6]),(0,[z154,z1,z164,z3,z94,z6])]],
   [[(0,[z350,z1,z2,z3,z4,z252]),(0,[z865,z1,z2,z3,z4,z6]),(0,[z695,z11,z2,z102,z4,z6]),(0,[z11,z1,z2,z3,z4,z429]),(0,[z11,z1,z2,z3,z866,z4]),(0,[z867,z1,z2,z3,z4,z6])],[(0,[z62,z21,z12,z3,z4,z6]),(0,[z9,z1,z2,z3,z109,z51]),(0,[z62,z11,z12,z3,z4,z210]),(0,[z11,z1,z2,z321,z4,z6])],[(0,[z11,z1,z2,z868,z4,z6]),(0,[z695,z11,z2,z3,z4,z106])],[(0,[z1,z219,z2,z3,z4,z67]),(0,[z1,z2,z3,z239,z734,z6]),(0,[z11,z1,z2,z163,z4,z37]),(0,[z11,z1,z2,z3,z869,z6])],[(0,[z9,z1,z2,z3,z4,z503]),(0,[z1,z2,z3,z4,z870,z6]),(0,[z871,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z775,z6])],[(0,[z21,z355,z2,z3,z4,z6]),(0,[z11,z1,z12,z238,z4,z6]),(1,[z11,z1,z3,z872,z6])],[(0,[z1,z2,z3,z39,z5,z6]),(0,[z873,z1,z2,z3,z4,z6]),(0,[z874,z1,z2,z3,z4,z6]),(0,[z875,z1,z2,z3,z4,z6])],[(0,[z844,z1,z3,z4,z159,z6]),(0,[z21,z1,z2,z3,z4,z65]),(0,[z11,z1,z2,z3,z876,z6]),(0,[z54,z141,z10,z3,z4,z6])],[(0,[z11,z1,z2,z3,z877,z6])],[(0,[z1,z878,z2,z3,z4,z6]),(0,[z11,z493,z10,z3,z4,z6]),(0,[z14,z346,z2,z3,z118,z6]),(0,[z11,z1,z879,z3,z4,z6])],[(0,[z11,z1,z880,z3,z4,z6]),(0,[z380,z1,z2,z4,z296,z6]),(0,[z11,z1,z2,z52,z180,z6]),(0,[z26,z1,z2,z3,z131,z6]),(0,[z11,z1,z2,z173,z4,z86])],[(1,[z11,z2,z3,z717,z6]),(0,[z11,z1,z2,z3,z4,z881]),(0,[z1,z2,z3,z109,z408,z51])],[(0,[z1,z2,z3,z4,z882,z6]),(0,[z11,z1,z2,z3,z4,z883]),(0,[z884,z1,z2,z3,z4,z6])],[(0,[z9,z1,z2,z3,z538,z6]),(0,[z1,z28,z2,z238,z4,z6]),(0,[z21,z668,z2,z3,z4,z6]),(0,[z1,z2,z3,z127,z145,z6]),(0,[z68,z21,z1,z2,z3,z73]),(0,[z1,z885,z2,z3,z4,z6]),(0,[z330,z212,z2,z52,z4,z6]),(0,[z241,z1,z2,z3,z886,z6])],[(0,[z887,z28,z2,z3,z4,z6]),(0,[z21,z95,z2,z3,z96,z6]),(1,[z95,z2,z3,z382,z6]),(0,[z1,z2,z3,z32,z841,z6]),(0,[z888,z1,z2,z3,z4,z6]),(0,[z889,z1,z2,z3,z4,z6]),(0,[z890,z1,z2,z3,z4,z6])],[(0,[z110,z1,z2,z3,z4,z6]),(0,[z1,z2,z3,z109,z145,z6]),(0,[z1,z2,z3,z4,z891,z6]),(0,[z1,z2,z3,z5,z6,z69]),(0,[z68,z1,z2,z3,z73,z5]),(0,[z11,z1,z892,z3,z4,z6]),(0,[z11,z1,z2,z3,z893,z6]),(0,[z1,z894,z2,z3,z4,z6])]],
   [[],[(0,[z9,z1,z2,z3,z4,z6]),(0,[z1,z2,z3,z145,z67,z6]),(0,[z11,z1,z2,z3,z4,z895]),(0,[z805,z1,z2,z3,z5,z6]),(0,[z380,z1,z2,z5,z19,z6]),(0,[z1,z2,z3,z4,z6,z896])],[(0,[z11,z1,z2,z238,z4,z210]),(0,[z1,z2,z3,z104,z6,z51]),(0,[z897,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z4,z898])],[(0,[z1,z2,z3,z88,z5,z6]),(0,[z899,z1,z2,z3,z4,z6])],[(0,[z11,z1,z2,z15,z96,z6]),(0,[z422,z1,z2,z3,z131,z6])],[(0,[z21,z1,z2,z3,z4,z217]),(0,[z11,z1,z2,z3,z900,z6]),(0,[z14,z11,z2,z3,z168,z6])],[(0,[z9,z1,z2,z171,z48,z6]),(0,[z11,z1,z2,z3,z901,z6]),(0,[z11,z1,z2,z3,z902,z6]),(0,[z1,z2,z3,z4,z903,z6])],[(0,[z1,z2,z3,z145,z6,z196]),(0,[z904,z1,z2,z3,z4,z6])],[(0,[z905,z1,z2,z3,z4,z6])],[(0,[z11,z1,z2,z3,z4,z906]),(0,[z1,z2,z3,z4,z907,z6])],[(0,[z1,z2,z173,z4,z5,z86]),(0,[z11,z1,z2,z3,z908,z6]),(0,[z909,z1,z2,z3,z4,z6]),(0,[z833,z1,z2,z3,z4,z6])],[(0,[z1,z2,z173,z3,z145,z6]),(0,[z11,z1,z46,z102,z4,z6])],[(0,[z11,z1,z2,z3,z910,z6]),(0,[z45,z11,z2,z102,z4,z6]),(0,[z11,z1,z29,z2,z4,z429]),(0,[z11,z1,z2,z911,z4,z6])],[(0,[z9,z1,z2,z3,z24,z6]),(0,[z9,z1,z2,z3,z626,z6]),(0,[z912,z1,z2,z3,z4,z6]),(0,[z11,z336,z2,z3,z96,z6])],[(0,[z95,z1,z2,z3,z145,z6]),(0,[z11,z1,z2,z913,z4,z6]),(0,[z1,z2,z3,z4,z775,z6]),(0,[z1,z2,z3,z4,z914,z6])],[(0,[z95,z527,z2,z3,z4,z6]),(0,[z113,z9,z1,z2,z19,z6]),(0,[z915,z1,z2,z3,z4,z6]),(0,[z11,z1,z8,z779,z4,z6])]],
   [[(0,[z1,z2,z3,z145,z133,z6]),(0,[z916,z1,z2,z3,z4,z6]),(0,[z1,z2,z3,z5,z351,z6]),(0,[z9,z1,z79,z3,z4,z6]),(0,[z1,z2,z3,z4,z917,z6])],[(0,[z11,z1,z918,z3,z4,z6]),(0,[z9,z1,z2,z3,z129,z6]),(0,[z11,z1,z2,z238,z4,z6]),(0,[z919,z1,z2,z3,z4,z6])],[(0,[z50,z1,z17,z3,z4,z6]),(0,[z1,z2,z3,z5,z147,z6]),(0,[z63,z9,z1,z3,z13,z6]),(0,[z11,z1,z2,z3,z335,z51]),(0,[z1,z2,z3,z4,z920,z6])],[(0,[z1,z2,z3,z145,z6,z86]),(0,[z22,z1,z2,z381,z4,z6])],[(0,[z21,z1,z2,z3,z179,z6]),(0,[z169,z2,z3,z4,z5,z106]),(0,[z11,z1,z2,z3,z4,z831]),(0,[z11,z1,z2,z3,z4,z252]),(0,[z921,z1,z2,z3,z4,z6]),(0,[z922,z1,z2,z3,z4,z6]),(0,[z11,z923,z2,z3,z4,z6])],[(0,[z281,z1,z2,z3,z5,z51]),(0,[z924,z1,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z925,z6])],[(0,[z306,z1,z2,z3,z5,z6]),(0,[z11,z1,z2,z3,z4,z926])],[(0,[z1,z2,z42,z3,z39,z6]),(0,[z927,z1,z2,z3,z4,z6])],[(0,[z928,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z4,z929]),(0,[z930,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z931,z6]),(0,[z1,z2,z3,z932,z4,z6])],[(0,[z1,z28,z2,z3,z933,z6]),(0,[z1,z2,z3,z610,z5,z6]),(0,[z68,z11,z1,z2,z3,z348])],[(0,[z1,z2,z746,z4,z5,z6]),(0,[z1,z2,z774,z4,z5,z6]),(0,[z11,z1,z55,z3,z4,z136]),(0,[z11,z1,z91,z3,z4,z795])],[(0,[z1,z2,z3,z5,z175,z6]),(0,[z111,z1,z176,z3,z359,z6]),(0,[z11,z1,z46,z3,z32,z6]),(0,[z11,z1,z2,z934,z4,z6])],[(1,[z1,z2,z15,z5,z6])],[(0,[z1,z1,z2,z3,z145,z6]),(0,[z9,z1,z2,z130,z4,z6]),(0,[z935,z1,z2,z3,z4,z6])],[(0,[z1,z527,z2,z3,z4,z6]),(0,[z21,z312,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z96,z136])],[(0,[z11,z1,z2,z3,z180,z217]),(0,[z11,z1,z2,z3,z936,z6]),(0,[z11,z1,z2,z486,z131,z6])]],
   [[(0,[z1,z28,z2,z321,z4,z6]),(0,[z9,z1,z2,z3,z39,z6]),(0,[z937,z1,z2,z3,z4,z6]),(0,[z11,z1,z481,z3,z4,z36]),(0,[z1,z2,z3,z4,z6,z938])],[(0,[z1,z2,z3,z4,z939,z6]),(0,[z11,z1,z940,z3,z4,z6])],[(0,[z21,z1,z164,z3,z94,z6]),(0,[z21,z1,z3,z188,z4,z6]),(0,[z1,z2,z3,z630,z5,z6]),(0,[z185,z1,z2,z3,z4,z217]),(0,[z1,z2,z3,z4,z941,z6])],[(0,[z1,z2,z3,z4,z5,z503]),(0,[z11,z54,z739,z3,z4,z6])],[(0,[z151,z1,z2,z3,z5,z6]),(0,[z68,z11,z1,z2,z3,z227]),(0,[z11,z1,z942,z3,z4,z6]),(0,[z11,z1,z323,z127,z4,z6])],[(0,[z28,z2,z3,z591,z4,z6]),(0,[z21,z1,z2,z3,z232,z6]),(0,[z11,z1,z2,z943,z4,z6])],[(0,[z1,z944,z2,z3,z4,z6]),(0,[z26,z1,z2,z3,z4,z6]),(0,[z21,z1,z2,z3,z239,z6]),(0,[z1,z2,z3,z4,z67,z189]),(0,[z11,z1,z2,z3,z945,z6]),(0,[z946,z1,z2,z3,z4,z6]),(0,[z11,z283,z2,z3,z96,z6])],[(0,[z0,z1,z2,z3,z145,z6]),(0,[z947,z1,z2,z3,z4,z6]),(0,[z464,z1,z2,z3,z5,z6]),(0,[z9,z1,z2,z3,z259,z6]),(0,[z108,z1,z2,z3,z32,z6]),(0,[z11,z1,z948,z3,z4,z6])],[(0,[z949,z11,z1,z2,z3,z6]),(0,[z950,z1,z2,z3,z4,z6]),(0,[z1,z2,z3,z951,z4,z6]),(0,[z1,z3,z952,z188,z4,z6]),(0,[z953,z1,z2,z3,z4,z6]),(0,[z954,z1,z2,z3,z4,z6])],[(0,[z1,z28,z2,z173,z4,z86]),(0,[z66,z21,z1,z3,z4,z36]),(0,[z955,z1,z2,z3,z180,z6]),(0,[z11,z2,z52,z743,z4,z6]),(0,[z956,z1,z2,z3,z4,z6])],[(0,[z332,z1,z2,z3,z232,z6]),(0,[z11,z2,z743,z102,z4,z6]),(0,[z957,z1,z2,z3,z4,z6])],[(0,[z1,z2,z3,z145,z6,z958])],[(0,[z304,z1,z2,z3,z5,z6])],[(0,[z11,z1,z2,z3,z933,z6]),(0,[z21,z1,z2,z15,z4,z6]),(0,[z959,z1,z2,z3,z4,z6])],[(0,[z183,z1,z2,z3,z5,z6]),(0,[z228,z1,z2,z3,z5,z6]),(0,[z762,z1,z2,z3,z4,z6]),(0,[z11,z1,z570,z3,z4,z6])],[(0,[z11,z1,z2,z3,z749,z6]),(0,[z21,z1,z2,z3,z44,z6]),(0,[z537,z11,z1,z3,z13,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z6]),(0,[z422,z1,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z960,z6])],[(0,[z11,z1,z2,z3,z4,z961]),(0,[z1,z2,z3,z962,z4,z6])],[(0,[z268,z1,z236,z3,z4,z6]),(0,[z644,z1,z2,z3,z5,z6]),(0,[z9,z1,z2,z3,z963,z6]),(0,[z11,z1,z137,z3,z4,z37]),(0,[z26,z1,z2,z3,z626,z6])],[(0,[z14,z28,z2,z3,z118,z6]),(0,[z54,z1,z2,z3,z145,z6]),(0,[z964,z1,z2,z3,z4,z6]),(0,[z11,z1,z590,z29,z4,z6]),(0,[z11,z0,z2,z3,z4,z162])],[(0,[z21,z28,z2,z3,z4,z6]),(0,[z1,z2,z3,z145,z5,z6]),(0,[z1,z2,z3,z94,z5,z6]),(0,[z504,z1,z2,z3,z5,z6])],[(0,[z105,z1,z2,z3,z145,z6]),(0,[z1,z2,z3,z48,z5,z6]),(0,[z26,z1,z79,z3,z4,z6])],[(0,[z21,z1,z2,z3,z965,z6]),(0,[z9,z1,z90,z2,z4,z6]),(0,[z11,z1,z966,z3,z4,z6])],[(0,[z1,z28,z2,z486,z4,z6]),(0,[z1,z2,z3,z967,z145,z6]),(0,[z9,z1,z2,z3,z145,z6]),(0,[z1,z2,z3,z4,z968,z6]),(0,[z11,z1,z969,z3,z4,z6]),(0,[z11,z1,z2,z970,z4,z6])],[(0,[z342,z1,z2,z392,z4,z6]),(0,[z11,z1,z2,z971,z4,z6]),(0,[z11,z1,z2,z3,z438,z6]),(0,[z972,z1,z2,z3,z4,z6]),(0,[z428,z1,z55,z3,z4,z6]),(0,[z11,z1,z3,z4,z872,z6]),(0,[z66,z11,z1,z3,z4,z36])],[(0,[z973,z1,z2,z3,z4,z6])],[(0,[z11,z2,z3,z96,z717,z6])],[(0,[z1,z124,z2,z3,z4,z6])],[(0,[z1,z28,z2,z3,z974,z6]),(0,[z1,z975,z2,z3,z4,z6]),(0,[z1,z2,z12,z3,z145,z6]),(0,[z1,z2,z3,z4,z963,z6]),(0,[z1,z2,z229,z3,z5,z6]),(0,[z11,z1,z10,z3,z179,z6]),(0,[z422,z1,z2,z3,z626,z6]),(0,[z11,z1,z3,z94,z872,z6])],[(0,[z1,z2,z3,z4,z976,z6]),(0,[z21,z1,z267,z3,z4,z6]),(0,[z11,z1,z977,z2,z4,z6]),(0,[z11,z1,z3,z978,z4,z6]),(0,[z536,z1,z2,z3,z5,z6]),(0,[z49,z1,z2,z3,z4,z831])],[(0,[z21,z1,z2,z313,z4,z6]),(0,[z1,z979,z2,z3,z4,z6]),(0,[z980,z1,z2,z3,z4,z6]),(0,[z981,z1,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z982,z6])],[(0,[z1,z298,z2,z3,z145,z6]),(0,[z11,z54,z10,z3,z4,z6]),(0,[z11,z450,z10,z3,z4,z6]),(0,[z11,z1,z2,z3,z4,z983]),(0,[z11,z1,z2,z3,z118,z136]),(0,[z422,z1,z79,z3,z4,z6]),(0,[z984,z1,z2,z3,z4,z6])]],
   [[(0,[z1,z141,z2,z3,z4,z6]),(0,[z11,z1,z2,z321,z626,z6])],[(0,[z1,z2,z3,z4,z145,z6]),(0,[z1,z28,z278,z3,z4,z6]),(0,[z122,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z4,z985,z6]),(0,[z95,z153,z2,z3,z96,z6])],[(0,[z11,z1,z2,z3,z4,z986]),(0,[z1,z2,z3,z239,z5,z6]),(0,[z128,z95,z2,z3,z5,z6]),(0,[z11,z1,z2,z987,z4,z6]),(0,[z1,z988,z2,z3,z4,z6])],[(0,[z1,z28,z2,z3,z4,z252]),(0,[z1,z2,z3,z5,z305,z6]),(0,[z62,z11,z12,z3,z4,z6]),(0,[z11,z1,z79,z321,z4,z6])],[],[(0,[z1,z2,z3,z94,z145,z6]),(0,[z9,z1,z2,z3,z628,z6]),(0,[z1,z2,z130,z4,z5,z6]),(0,[z1,z2,z3,z4,z6,z989]),(0,[z11,z1,z990,z3,z4,z6]),(0,[z11,z1,z570,z3,z131,z6]),(0,[z11,z1,z2,z3,z991,z4]),(0,[z11,z1,z992,z3,z4,z6])],[(0,[z1,z2,z3,z48,z145,z6]),(0,[z1,z2,z3,z145,z6,z31]),(0,[z265,z1,z2,z3,z5,z6]),(0,[z11,z1,z55,z3,z5,z6])],[(0,[z30,z1,z2,z3,z4,z31]),(0,[z993,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z591,z4,z86])],[(0,[z1,z994,z2,z3,z4,z6]),(0,[z674,z28,z2,z3,z4,z6]),(0,[z1,z2,z3,z5,z6,z326]),(0,[z87,z11,z1,z3,z13,z6]),(0,[z11,z1,z2,z313,z179,z6])],[(0,[z11,z1,z2,z995,z4,z6]),(0,[z1,z996,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z4,z997])],[(0,[z998,z11,z1,z2,z4,z6]),(0,[z332,z1,z2,z3,z4,z389])],[(0,[z11,z1,z2,z486,z4,z6])],[(0,[z1,z2,z3,z32,z5,z6]),(0,[z283,z1,z2,z3,z5,z6]),(0,[z11,z1,z81,z127,z4,z6])],[(0,[z11,z1,z2,z3,z4,z999]),(0,[z11,z1,z1000,z3,z4,z6]),(0,[z1001,z1,z2,z3,z4,z6]),(0,[z108,z1,z46,z3,z4,z6]),(0,[z11,z1,z2,z3,z4,z453]),(0,[z1002,z1,z2,z3,z4,z6])],[(0,[z1,z2,z3,z4,z1003,z6]),(0,[z9,z1,z2,z3,z32,z6]),(0,[z11,z1,z2,z1004,z4,z6])],[(0,[z11,z1,z2,z3,z872,z6]),(0,[z68,z11,z1,z2,z3,z73])]],
   [[(0,[z1,z28,z55,z3,z4,z6]),(0,[z11,z1,z2,z3,z974,z6]),(0,[z354,z1,z2,z3,z5,z6]),(0,[z1005,z1,z2,z3,z4,z6]),(0,[z1006,z1,z2,z3,z4,z6])],[(0,[z47,z1,z2,z3,z438,z6]),(0,[z771,z11,z1,z3,z4,z6]),(0,[z1007,z11,z1,z2,z3,z6]),(0,[z1008,z1,z2,z3,z4,z6])],[(0,[z849,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z1009,z6]),(0,[z1,z2,z3,z4,z1010,z6])],[(0,[z58,z1,z2,z3,z145,z6]),(0,[z21,z1,z2,z3,z1011,z6]),(0,[z111,z1,z176,z3,z4,z6]),(0,[z11,z1,z1012,z3,z4,z6])],[(0,[z58,z527,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z4,z1013])],[(0,[z330,z1,z2,z3,z4,z6]),(0,[z11,z1,z278,z3,z4,z6])],[],[(0,[z11,z1,z55,z3,z4,z503]),(0,[z11,z1,z2,z486,z626,z6]),(0,[z1014,z1,z2,z3,z4,z6])],[(0,[z21,z1,z2,z3,z1015,z6]),(0,[z1,z2,z3,z322,z5,z6]),(0,[z1,z2,z3,z4,z1016,z6])],[(0,[z1,z2,z3,z4,z226,z6]),(0,[z45,z11,z2,z102,z32,z6])],[(0,[z11,z1,z2,z313,z239,z6]),(0,[z11,z1,z79,z486,z4,z6]),(0,[z11,z1,z2,z1017,z4,z6])],[(0,[z11,z1,z2,z3,z1018,z6]),(0,[z11,z1,z2,z3,z4,z723]),(0,[z11,z1,z2,z3,z4,z1019])],[(0,[z11,z1,z2,z3,z4,z1020]),(0,[z11,z1,z2,z1021,z4,z6]),(0,[z1,z2,z3,z5,z370,z6])],[(0,[z1,z28,z570,z3,z4,z6]),(0,[z1,z2,z3,z335,z5,z6]),(0,[z11,z1,z2,z3,z1022,z6]),(0,[z11,z1,z397,z3,z13,z6]),(0,[z68,z7,z1,z2,z3,z73])],[(0,[z393,z1,z2,z3,z145,z6]),(0,[z11,z1,z474,z127,z4,z6]),(0,[z11,z10,z739,z3,z4,z6]),(0,[z1023,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z4,z1024,z6]),(0,[z11,z1,z2,z1025,z4,z6])],[(0,[z11,z1,z2,z3,z4,z1026]),(0,[z63,z35,z1,z3,z13,z6]),(0,[z1027,z1,z2,z3,z4,z6])]],
   [[(0,[z28,z705,z2,z3,z4,z6]),(0,[z1,z124,z2,z3,z5,z6]),(0,[z30,z1,z2,z3,z4,z231]),(0,[z1028,z1,z2,z3,z4,z6]),(1,[z11,z1,z2,z3,z991])],[(0,[z287,z1,z2,z3,z179,z6]),(0,[z11,z1,z1029,z2,z3,z4])],[(0,[z345,z1,z2,z3,z5,z6])],[(0,[z11,z1,z2,z3,z4,z1030]),(0,[z1,z2,z3,z15,z5,z6]),(0,[z9,z1,z2,z163,z4,z6]),(0,[z1,z2,z3,z4,z1031,z6]),(0,[z11,z1,z2,z48,z1024,z6])],[(0,[z20,z1,z386,z3,z4,z6]),(0,[z11,z1,z55,z3,z4,z6]),(0,[z927,z1,z2,z3,z32,z6]),(0,[z1032,z1,z2,z3,z4,z6]),(0,[z1033,z1,z2,z3,z4,z6])],[(0,[z22,z1,z2,z301,z4,z6]),(0,[z1,z2,z3,z4,z5,z707])],[(0,[z476,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z396,z6]),(0,[z1,z1034,z2,z3,z4,z6])],[(0,[z11,z1,z2,z3,z4,z1035]),(0,[z1,z28,z2,z3,z438,z6]),(0,[z21,z1,z2,z3,z180,z6]),(0,[z1,z2,z3,z4,z1036,z6]),(0,[z1,z1037,z2,z3,z4,z6]),(0,[z1038,z1,z2,z3,z4,z6])],[(0,[z1,z2,z3,z84,z145,z6]),(0,[z1039,z1,z2,z3,z4,z6])],[(0,[z154,z1,z2,z3,z359,z6]),(0,[z1,z298,z127,z4,z5,z6]),(0,[z1,z2,z163,z4,z5,z6]),(0,[z45,z108,z2,z102,z4,z6])],[(0,[z21,z28,z2,z3,z145,z6]),(0,[z306,z1,z2,z3,z145,z6]),(0,[z11,z1,z2,z3,z4,z1040])],[(0,[z306,z527,z2,z3,z4,z6]),(0,[z1041,z1,z2,z3,z4,z6])],[(0,[z11,z1,z1042,z3,z4,z6]),(0,[z11,z1,z1043,z2,z4,z6]),(0,[z1044,z1,z2,z3,z4,z6])],[(0,[z400,z1,z2,z3,z4,z6]),(0,[z122,z1,z2,z501,z4,z6])],[(0,[z1,z2,z3,z1045,z145,z6]),(0,[z583,z1,z2,z3,z5,z6]),(0,[z66,z11,z1,z3,z4,z795])],[(0,[z1,z2,z3,z4,z1046,z6]),(0,[z1,z2,z3,z4,z770,z6])]],
   [[(0,[z1,z2,z3,z159,z6,z51]),(0,[z11,z1,z2,z3,z4,z1047]),(0,[z11,z1,z55,z3,z24,z6]),(0,[z30,z1,z2,z3,z88,z31]),(0,[z11,z1,z2,z1048,z4,z6]),(0,[z11,z1,z2,z3,z4,z1049]),(0,[z11,z1050,z2,z3,z4,z6]),(0,[z1051,z1,z2,z3,z4,z6])],[(0,[z1052,z1,z2,z3,z4,z6])],[(0,[z111,z1,z176,z3,z39,z6]),(0,[z368,z1,z2,z3,z5,z6]),(0,[z1,z55,z3,z4,z5,z6]),(0,[z1,z267,z3,z4,z5,z6])],[(0,[z11,z1,z2,z3,z1053,z6]),(0,[z1,z2,z190,z3,z5,z6]),(0,[z1,z2,z3,z4,z67,z831]),(0,[z287,z1,z2,z3,z239,z6])],[(0,[z11,z1,z2,z1054,z4,z6]),(0,[z7,z1,z2,z3,z4,z6]),(0,[z480,z1,z2,z3,z5,z6]),(0,[z9,z1,z46,z3,z4,z6]),(0,[z1,z2,z3,z4,z787,z6])],[(0,[z1,z91,z2,z3,z145,z6]),(0,[z1055,z1,z2,z3,z4,z6]),(0,[z11,z1,z170,z3,z4,z37])],[(0,[z11,z1,z2,z1056,z4,z6]),(0,[z1,z278,z3,z4,z5,z6]),(0,[z1,z2,z3,z5,z19,z6]),(0,[z380,z11,z1,z2,z19,z6]),(0,[z11,z414,z2,z3,z4,z162])],[(0,[z1,z2,z3,z5,z6,z594]),(0,[z350,z1,z2,z3,z179,z6])],[(0,[z1,z28,z2,z3,z4,z217]),(0,[z317,z11,z2,z102,z4,z6]),(0,[z1057,z1,z2,z3,z4,z6]),(1,[z11,z1,z3,z4,z795])],[(0,[z1,z2,z3,z145,z82,z6]),(0,[z49,z1,z2,z3,z4,z82]),(1,[z1,z2,z3,z5,z136]),(0,[z11,z1,z2,z1058,z4,z6])],[(0,[z272,z1,z2,z3,z159,z6]),(0,[z11,z1,z2,z3,z1059,z6]),(0,[z14,z125,z2,z3,z118,z6]),(0,[z1060,z1,z2,z3,z4,z6])],[(0,[z1061,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z1062,z6]),(0,[z11,z1,z2,z1063,z4,z6])],[(0,[z1,z28,z2,z3,z4,z453]),(0,[z1,z2,z3,z145,z6,z51]),(0,[z21,z212,z2,z52,z4,z6]),(0,[z197,z1,z2,z3,z145,z6]),(0,[z197,z1,z2,z855,z4,z6]),(0,[z1,z2,z3,z1064,z5,z6]),(0,[z281,z1,z2,z3,z4,z67]),(0,[z1065,z1,z2,z3,z4,z6]),(0,[z68,z1,z2,z3,z408,z6])],[(0,[z1066,z1,z2,z3,z4,z6]),(0,[z11,z1,z1067,z3,z4,z6]),(0,[z1,z2,z3,z4,z1068,z6]),(0,[z1069,z1,z2,z3,z4,z6]),(0,[z11,z1,z570,z3,z626,z6]),(1,[z11,z2,z3,z4,z723]),(0,[z11,z1,z2,z4,z1070,z6])],[(0,[z11,z1,z2,z3,z4,z65])],[(0,[z1,z772,z28,z2,z3,z4]),(0,[z1,z2,z171,z3,z145,z6]),(0,[z1,z2,z3,z4,z1071,z6]),(0,[z1,z2,z3,z5,z6,z606]),(0,[z11,z1,z12,z3,z179,z6]),(0,[z45,z11,z46,z102,z4,z6])]],
   [[(0,[z1,z402,z2,z42,z4,z6]),(0,[z1,z1072,z2,z3,z4,z6]),(0,[z11,z1,z55,z130,z4,z6]),(0,[z11,z1,z298,z127,z4,z429]),(0,[z57,z1,z91,z3,z4,z37])],[],[(0,[z1,z1073,z2,z3,z4,z6]),(0,[z21,z1,z2,z3,z4,z210]),(0,[z11,z1074,z2,z3,z4,z6])],[(0,[z1,z91,z3,z4,z5,z37]),(0,[z154,z1,z2,z3,z5,z6]),(0,[z11,z1,z173,z188,z4,z86]),(0,[z1,z2,z3,z787,z6,z86])],[(0,[z1,z2,z251,z3,z5,z6]),(0,[z11,z1,z2,z3,z1075,z6]),(0,[z185,z1,z2,z3,z180,z6]),(0,[z330,z1,z2,z3,z1068,z6])],[(0,[z1076,z1,z2,z3,z4,z6]),(0,[z1077,z1,z2,z3,z4,z6]),(0,[z11,z95,z2,z3,z96,z6]),(0,[z1,z2,z3,z1078,z4,z6])],[(0,[z266,z1,z2,z3,z5,z6]),(0,[z1079,z1,z2,z3,z4,z6])],[(0,[z21,z28,z2,z3,z129,z6]),(0,[z28,z2,z3,z4,z168,z6]),(0,[z28,z2,z170,z3,z4,z6]),(0,[z221,z1,z2,z3,z4,z6])],[(0,[z95,z28,z2,z3,z96,z6]),(0,[z1,z2,z3,z145,z145,z6]),(0,[z111,z1,z386,z3,z4,z6]),(0,[z9,z1,z2,z3,z387,z6]),(0,[z686,z11,z1,z3,z13,z6])],[(0,[z350,z1,z2,z3,z239,z6]),(0,[z11,z2,z3,z4,z723,z106])],[(0,[z1,z124,z2,z3,z24,z6]),(0,[z21,z1,z2,z3,z4,z136]),(0,[z11,z1,z1080,z3,z4,z6]),(0,[z346,z1,z55,z3,z4,z6])],[(0,[z60,z1,z23,z3,z4,z6]),(1,[z1,z714,z3,z4,z6]),(0,[z1,z8,z29,z4,z5,z6]),(0,[z287,z1,z2,z313,z4,z6]),(0,[z1081,z1,z2,z3,z4,z6]),(0,[z11,z309,z2,z52,z4,z6]),(0,[z704,z11,z1,z2,z19,z6]),(0,[z1,z1082,z2,z3,z4,z6])],[(0,[z11,z1,z2,z3,z179,z210]),(0,[z11,z1,z2,z3,z4,z217])],[(0,[z45,z28,z2,z102,z4,z6]),(0,[z1083,z1,z2,z3,z4,z6])],[(0,[z1,z2,z3,z179,z1084,z6])],[(0,[z1,z255,z3,z4,z5,z6]),(0,[z11,z1,z2,z3,z4,z1085]),(0,[z671,z11,z12,z3,z4,z6]),(0,[z11,z1,z3,z1086,z4,z6]),(0,[z11,z1,z2,z3,z4,z795])]],
   [[(0,[z14,z1,z55,z3,z5,z6])],[(1,[z1,z2,z855,z4,z6]),(0,[z1,z2,z3,z232,z5,z6]),(0,[z9,z1,z298,z127,z4,z6]),(0,[z11,z1,z492,z3,z4,z37])],[(0,[z22,z1,z2,z84,z438,z6]),(0,[z400,z1,z2,z3,z5,z6]),(0,[z9,z1,z2,z3,z418,z6]),(0,[z119,z11,z2,z3,z4,z106]),(0,[z1,z2,z3,z4,z1087,z6])],[(0,[z1,z2,z3,z129,z5,z6])],[(0,[z1,z2,z3,z1088,z4,z6])],[(0,[z1,z28,z164,z3,z94,z6]),(0,[z21,z1,z91,z3,z4,z37]),(0,[z1089,z1,z2,z3,z4,z6])],[(0,[z160,z1,z2,z3,z4,z6]),(0,[z955,z1,z2,z3,z4,z6]),(0,[z9,z1,z2,z3,z4,z429]),(0,[z400,z1,z2,z3,z88,z6]),(0,[z1,z1090,z2,z3,z4,z6])],[(0,[z197,z1,z2,z501,z4,z6]),(0,[z9,z1,z2,z321,z4,z6]),(0,[z615,z11,z1,z3,z13,z6]),(0,[z11,z1,z46,z52,z4,z6]),(0,[z11,z1,z3,z1091,z4,z6])],[(0,[z1,z28,z2,z3,z232,z6]),(0,[z1,z2,z3,z4,z1092,z6]),(0,[z1,z2,z3,z104,z13,z6])],[(1,[z1,z2,z3,z903,z6])],[(0,[z105,z1,z2,z3,z4,z196]),(0,[z11,z1,z2,z3,z4,z1093]),(0,[z11,z1,z2,z3,z32,z453])],[(0,[z169,z21,z2,z3,z4,z106]),(0,[z11,z1,z2,z3,z179,z6])],[(0,[z21,z1,z2,z3,z359,z6])],[(0,[z11,z1,z2,z3,z1094,z6]),(0,[z11,z1,z739,z3,z4,z6])],[(0,[z22,z1,z2,z3,z145,z6]),(0,[z22,z1,z2,z855,z4,z6]),(0,[z11,z1,z2,z3,z239,z210])],[(0,[z87,z1,z3,z5,z13,z6]),(0,[z11,z1,z2,z138,z4,z86]),(0,[z1095,z1,z2,z3,z4,z6])]],
   [[(0,[z9,z1,z2,z173,z4,z86])],[(0,[z154,z1,z2,z3,z4,z6]),(0,[z95,z2,z3,z96,z5,z6]),(0,[z1096,z1,z2,z3,z4,z6]),(0,[z350,z1,z2,z313,z4,z6]),(1,[z1,z2,z3,z775,z6]),(0,[z68,z400,z1,z2,z3,z73])],[(0,[z21,z1,z2,z3,z1097,z6]),(0,[z197,z1,z2,z284,z4,z6]),(0,[z113,z1,z2,z5,z19,z6]),(0,[z68,z1,z2,z3,z1064,z6]),(0,[z11,z1,z278,z3,z32,z6]),(0,[z11,z1,z779,z127,z4,z6])],[(0,[z1098,z1,z2,z3,z4,z6]),(0,[z1,z2,z3,z1099,z4,z6]),(0,[z1,z2,z3,z232,z6,z31]),(0,[z11,z1,z188,z4,z6,z86])],[(0,[z11,z1,z2,z1100,z4,z6]),(0,[z11,z1,z2,z743,z4,z6]),(0,[z11,z1,z779,z298,z4,z6])],[(0,[z95,z2,z3,z382,z5,z6])],[(0,[z1,z2,z3,z73,z145,z6]),(0,[z21,z1,z8,z29,z4,z6]),(0,[z11,z1,z3,z1101,z4,z6]),(0,[z11,z1,z3,z753,z4,z6])],[(0,[z21,z629,z2,z3,z4,z6]),(0,[z1,z2,z3,z127,z877,z6]),(0,[z1,z2,z3,z4,z1102,z6]),(0,[z1103,z1,z2,z3,z4,z6])],[(0,[z21,z1,z2,z3,z131,z6]),(0,[z11,z1,z2,z1104,z4,z6]),(0,[z1,z2,z3,z4,z1105,z6]),(1,[z11,z1,z779,z4,z6])],[(0,[z1,z28,z2,z3,z1059,z6]),(0,[z1,z2,z3,z5,z557,z6]),(0,[z1,z2,z3,z24,z963,z6]),(0,[z11,z1,z3,z188,z4,z6]),(0,[z11,z1,z164,z3,z94,z6])],[(0,[z14,z9,z2,z3,z118,z6]),(0,[z1106,z1,z2,z3,z4,z6]),(0,[z11,z1,z10,z3,z4,z210])],[(0,[z11,z1,z2,z3,z886,z6]),(0,[z11,z1,z2,z1107,z4,z6])],[(0,[z11,z887,z2,z3,z4,z6]),(0,[z21,z1,z255,z3,z4,z6]),(0,[z11,z1,z2,z3,z232,z6])],[(0,[z1,z28,z2,z3,z4,z65]),(0,[z154,z1,z2,z3,z24,z6]),(0,[z11,z1,z2,z3,z239,z6]),(0,[z11,z1,z2,z15,z4,z136])],[(0,[z1,z2,z3,z24,z145,z6]),(0,[z11,z1,z1108,z3,z4,z6]),(0,[z11,z1,z2,z3,z4,z1109]),(0,[z1110,z1,z2,z3,z4,z6]),(0,[z11,z1,z3,z138,z4,z37])],[(0,[z11,z1,z2,z1111,z4,z6]),(0,[z368,z1,z2,z3,z39,z6]),(0,[z1,z2,z3,z862,z4,z5]),(0,[z1,z2,z3,z382,z19,z6]),(0,[z1112,z1,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z736,z6]),(0,[z11,z1,z3,z872,z13,z6])]],
   [[(0,[z11,z1,z2,z3,z1113,z6]),(0,[z11,z1,z2,z3,z1114,z6]),(0,[z11,z640,z2,z3,z4,z162]),(0,[z1,z2,z3,z408,z6,z51])],[(0,[z1,z2,z3,z4,z248,z6]),(0,[z1,z1115,z2,z4,z5,z6])],[(0,[z28,z2,z311,z3,z4,z6]),(0,[z1,z2,z3,z4,z1116,z6])],[(0,[z1,z2,z3,z4,z1117,z6]),(0,[z21,z1,z2,z3,z1118,z6]),(0,[z1,z2,z3,z4,z1119,z6])],[(0,[z134,z1,z2,z3,z145,z6]),(0,[z1,z2,z3,z5,z584,z6]),(0,[z11,z1,z2,z3,z1120,z6]),(0,[z1121,z1,z2,z3,z4,z6])],[(0,[z11,z0,z2,z3,z4,z723])],[(0,[z11,z1,z2,z3,z44,z6]),(0,[z11,z1,z2,z313,z4,z210]),(0,[z11,z1,z2,z3,z1122,z6]),(0,[z54,z1,z2,z3,z808,z6]),(0,[z1,z2,z3,z4,z1123,z6]),(0,[z11,z1,z3,z163,z4,z37])],[(0,[z11,z1,z2,z3,z4,z1124]),(0,[z9,z1,z2,z238,z4,z6])],[(0,[z21,z1,z2,z3,z1125,z6]),(0,[z60,z1,z17,z3,z4,z6]),(0,[z844,z1,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z162]),(0,[z1,z2,z544,z5,z19,z6]),(0,[z11,z1,z1126,z3,z4,z6])],[(0,[z1,z2,z3,z555,z5,z6]),(0,[z304,z11,z1,z2,z3,z73]),(0,[z1,z2,z3,z1127,z4,z6]),(0,[z11,z1,z1128,z3,z4,z6]),(1,[z11,z1,z188,z4,z86])],[(0,[z21,z1,z2,z3,z88,z6]),(0,[z1,z2,z486,z4,z5,z6]),(0,[z9,z1,z2,z3,z4,z252]),(0,[z57,z1,z2,z3,z903,z6])],[(0,[z35,z1,z2,z3,z4,z6]),(0,[z332,z1,z2,z3,z5,z6]),(0,[z11,z95,z2,z3,z382,z6]),(0,[z14,z11,z55,z3,z118,z6]),(1,[z11,z1,z127,z4,z429]),(0,[z11,z1,z2,z163,z4,z36])],[(0,[z11,z1,z2,z1129,z4,z6]),(0,[z1,z402,z2,z276,z4,z6]),(0,[z28,z2,z3,z341,z4,z6]),(0,[z400,z1,z2,z3,z24,z6]),(0,[z26,z1,z2,z321,z4,z6]),(0,[z1,z2,z171,z48,z209,z6])],[(0,[z40,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z965,z6]),(0,[z11,z181,z2,z52,z4,z6]),(0,[z11,z1,z127,z4,z37,z86])],[(0,[z1130,z1,z2,z3,z4,z6])],[(0,[z1,z2,z3,z4,z1131,z6]),(0,[z692,z28,z2,z3,z4,z6]),(0,[z57,z1,z2,z3,z4,z6]),(0,[z1,z2,z3,z1132,z4,z6]),(0,[z11,z1,z2,z1024,z19,z6])]],
   [[(0,[z1,z28,z2,z3,z1133,z6]),(0,[z1,z2,z3,z145,z1134,z6]),(0,[z11,z1,z46,z3,z4,z453])],[(0,[z1,z2,z3,z96,z145,z6]),(0,[z1,z2,z3,z5,z92,z6]),(0,[z169,z11,z2,z3,z131,z106])],[(0,[z1,z2,z3,z426,z5,z6]),(0,[z1,z2,z3,z4,z1135,z6]),(0,[z1,z2,z3,z4,z1136,z6])],[(0,[z1,z2,z580,z3,z5,z6])],[(0,[z62,z28,z12,z3,z4,z6]),(0,[z1,z2,z3,z4,z808,z6]),(0,[z11,z1,z2,z1137,z4,z6]),(0,[z11,z1,z2,z1138,z4,z6])],[(0,[z113,z21,z1,z2,z19,z6]),(0,[z1,z2,z3,z4,z5,z429]),(0,[z11,z1,z2,z313,z4,z6])],[(0,[z14,z1,z2,z3,z159,z6]),(0,[z11,z1,z2,z3,z4,z1139]),(0,[z422,z1,z2,z321,z4,z6])],[(0,[z1,z28,z2,z3,z862,z4]),(0,[z21,z1,z2,z3,z4,z503]),(0,[z100,z1,z2,z3,z4,z69]),(0,[z9,z1,z55,z3,z4,z6]),(0,[z1140,z1,z2,z3,z4,z6]),(0,[z1,z1141,z2,z3,z4,z6])],[(0,[z63,z21,z1,z3,z13,z6]),(0,[z30,z1,z2,z3,z44,z6]),(0,[z1,z2,z3,z438,z5,z6]),(0,[z11,z1,z349,z3,z4,z37])],[(0,[z11,z1,z2,z102,z4,z217]),(0,[z11,z1,z2,z486,z4,z162])],[(0,[z1,z28,z2,z3,z179,z6]),(0,[z1142,z1,z2,z3,z4,z6]),(0,[z66,z1,z2,z3,z145,z6]),(0,[z22,z1,z2,z3,z39,z6]),(0,[z160,z1,z2,z3,z94,z6])],[(0,[z11,z1,z1143,z3,z4,z6]),(0,[z11,z1,z2,z3,z1144,z6]),(0,[z428,z1,z2,z15,z4,z6]),(0,[z11,z1,z2,z3,z991,z51])],[(0,[z66,z1,z28,z3,z4,z36]),(0,[z108,z1,z2,z3,z4,z453])],[(0,[z1,z1145,z2,z3,z4,z6]),(0,[z290,z28,z2,z3,z4,z6]),(0,[z11,z1,z2,z486,z4,z106]),(0,[z11,z1,z163,z4,z6,z37])],[(0,[z1,z2,z3,z5,z162,z51]),(0,[z1146,z1,z2,z3,z4,z6]),(0,[z1,z1147,z2,z3,z4,z6])],[(0,[z28,z2,z3,z4,z382,z6]),(0,[z456,z1,z2,z3,z4,z149]),(1,[z1,z2,z3,z963,z6]),(0,[z287,z1,z2,z3,z4,z210]),(0,[z1148,z1,z2,z3,z4,z6]),(0,[z11,z1,z255,z15,z4,z6]),(0,[z1,z1149,z2,z3,z4,z6])]],
   [[(0,[z1,z2,z3,z5,z634,z6]),(0,[z62,z350,z12,z3,z4,z6]),(0,[z11,z1,z2,z188,z4,z86])],[(0,[z11,z1,z314,z3,z94,z6]),(0,[z11,z1,z2,z3,z4,z1150])],[(0,[z68,z1,z2,z3,z5,z51]),(0,[z11,z1,z2,z127,z4,z429])],[(0,[z11,z1,z2,z3,z1151,z6]),(0,[z11,z739,z12,z3,z4,z6]),(0,[z11,z1,z2,z274,z4,z86]),(0,[z68,z1,z2,z3,z104,z6]),(0,[z1152,z1,z2,z3,z4,z6])],[(0,[z21,z1,z2,z3,z4,z6]),(1,[z1,z2,z3,z145,z6]),(0,[z11,z1,z2,z3,z1133,z6]),(0,[z11,z1,z1153,z3,z4,z6]),(0,[z9,z1,z570,z3,z4,z6]),(0,[z108,z1,z278,z3,z4,z6])],[(0,[z1,z3,z4,z1154,z159,z6]),(0,[z1155,z1,z2,z3,z4,z6]),(0,[z1,z2,z3,z1156,z4,z6]),(0,[z45,z11,z2,z743,z4,z6]),(0,[z1157,z1,z2,z3,z4,z6])],[(0,[z11,z1158,z2,z3,z4,z6]),(0,[z1,z1159,z2,z3,z4,z6])],[(0,[z14,z1,z2,z3,z1160,z6]),(0,[z110,z0,z2,z3,z4,z162]),(0,[z63,z11,z1,z3,z13,z6])],[(0,[z1,z28,z3,z188,z4,z6]),(0,[z1,z2,z3,z855,z4,z6]),(0,[z11,z2,z739,z3,z4,z6])],[(0,[z1,z2,z3,z617,z5,z6]),(0,[z11,z1,z2,z15,z5,z6]),(0,[z9,z0,z2,z3,z4,z162]),(0,[z11,z1,z2,z3,z32,z217])],[(0,[z1,z28,z2,z3,z180,z6]),(0,[z11,z1,z2,z3,z1011,z6]),(0,[z247,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z619,z5,z6]),(0,[z1,z2,z3,z180,z1161,z6]),(0,[z346,z1,z2,z15,z4,z6]),(0,[z1,z1162,z2,z3,z4,z6])],[(0,[z11,z1,z2,z3,z862,z4]),(0,[z11,z1,z2,z3,z4,z1163]),(0,[z1,z2,z3,z5,z186,z6]),(0,[z1164,z1,z2,z3,z4,z6]),(0,[z14,z1,z2,z3,z104,z6])],[(0,[z11,z1,z1165,z3,z4,z6]),(0,[z1,z28,z2,z3,z239,z6]),(0,[z221,z1,z2,z3,z761,z6])],[(0,[z11,z1,z1166,z3,z4,z6]),(0,[z1167,z1,z2,z3,z4,z6])],[(0,[z9,z1,z2,z3,z438,z6])],[(0,[z1,z535,z459,z3,z4,z6]),(0,[z1,z2,z631,z3,z5,z6]),(0,[z75,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z663,z6]),(0,[z11,z1,z2,z3,z121,z51]),(0,[z1168,z1,z2,z3,z4,z6]),(0,[z1,z2,z3,z952,z4,z6]),(0,[z195,z1,z2,z3,z109,z51])]],
   [[(0,[z1,z1169,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z1170,z6]),(0,[z21,z1,z2,z3,z626,z6]),(0,[z68,z1,z2,z3,z382,z6]),(0,[z193,z11,z12,z3,z4,z6])],[(0,[z1,z2,z3,z4,z1171,z6])],[(0,[z1,z2,z1172,z3,z145,z6]),(0,[z40,z1,z2,z3,z5,z6]),(0,[z1173,z1,z2,z3,z4,z6])],[(0,[z1,z28,z2,z15,z4,z6]),(0,[z1174,z1,z2,z3,z4,z6]),(0,[z68,z1,z28,z2,z3,z73]),(0,[z45,z1,z2,z3,z145,z6]),(0,[z21,z1,z79,z3,z4,z6]),(0,[z11,z1,z2,z3,z1175,z6]),(0,[z1,z2,z3,z5,z213,z6])],[(0,[z21,z1,z2,z3,z129,z6]),(0,[z71,z1,z2,z301,z4,z6]),(0,[z11,z1,z2,z3,z1176,z6])],[(0,[z11,z1,z2,z3,z1177,z6]),(0,[z1,z28,z2,z3,z44,z6]),(0,[z785,z11,z1,z2,z4,z6]),(0,[z368,z1,z61,z3,z4,z6]),(0,[z350,z1,z2,z3,z4,z210]),(0,[z11,z1,z199,z127,z4,z6]),(0,[z1178,z1,z3,z188,z4,z6])],[(0,[z1,z2,z3,z511,z5,z6])],[(0,[z1,z2,z3,z129,z145,z6]),(0,[z1,z3,z4,z5,z1154,z6]),(0,[z1,z2,z3,z4,z1010,z429]),(0,[z1,z2,z3,z1179,z4,z6]),(1,[z11,z1,z2,z1024,z6])],[(0,[z21,z1,z2,z3,z763,z6]),(0,[z11,z1,z2,z3,z1180,z6]),(0,[z14,z1,z2,z3,z382,z6]),(0,[z1181,z1,z2,z3,z4,z6])],[(0,[z28,z2,z3,z460,z4,z6]),(0,[z1,z2,z3,z648,z5,z6]),(0,[z1,z2,z3,z4,z5,z252]),(0,[z11,z1,z1182,z3,z4,z6]),(0,[z11,z1,z255,z3,z4,z136])],[(0,[z1,z2,z3,z4,z408,z6]),(0,[z11,z1,z2,z436,z4,z86]),(0,[z11,z1,z2,z15,z4,z503]),(0,[z1183,z1,z2,z3,z4,z6])],[(0,[z1168,z1,z2,z3,z626,z6]),(0,[z784,z1,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z877,z6])],[(0,[z53,z1,z2,z3,z1184,z6]),(0,[z11,z1,z2,z1185,z4,z6])],[(0,[z1,z2,z176,z3,z39,z6]),(0,[z1,z2,z3,z4,z1084,z6]),(0,[z1,z2,z3,z4,z1186,z6]),(0,[z11,z1,z12,z3,z4,z210]),(0,[z1,z1187,z2,z3,z4,z6]),(0,[z169,z11,z2,z3,z4,z106])],[(0,[z11,z1,z2,z3,z180,z6])],[(0,[z11,z1188,z2,z3,z4,z6]),(0,[z195,z1,z2,z3,z4,z6])]],
   [[(0,[z11,z1,z2,z4,z1189,z6]),(0,[z21,z1,z2,z130,z4,z6]),(0,[z241,z1,z2,z3,z4,z6]),(0,[z221,z1,z2,z3,z787,z6])],[(0,[z185,z1,z2,z3,z4,z6]),(0,[z9,z1,z2,z486,z4,z6]),(0,[z1190,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z1191,z6]),(0,[z1192,z1,z2,z3,z4,z6]),(0,[z1,z1193,z2,z3,z4,z6])],[(0,[z1194,z1,z2,z3,z4,z6]),(0,[z659,z11,z1,z127,z4,z6]),(0,[z11,z1,z2,z3,z991,z109])],[(0,[z1,z28,z267,z3,z4,z6]),(0,[z40,z1,z2,z3,z145,z6]),(0,[z21,z1,z2,z3,z39,z6]),(0,[z11,z1,z2,z3,z5,z136]),(0,[z1195,z1,z2,z3,z4,z6]),(0,[z9,z1,z2,z3,z4,z453])],[(0,[z1,z28,z2,z313,z4,z6]),(0,[z11,z1,z2,z3,z1196,z6]),(0,[z60,z1,z714,z3,z4,z6]),(0,[z11,z1,z2,z3,z1197,z6]),(0,[z1198,z1,z2,z3,z4,z6]),(0,[z1199,z1,z2,z3,z4,z6]),(0,[z1,z1200,z2,z3,z4,z6])],[(0,[z21,z633,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z1201,z6]),(0,[z49,z1,z2,z3,z4,z389])],[],[(0,[z11,z1,z2,z15,z4,z6])],[(0,[z53,z1,z2,z3,z4,z6]),(0,[z272,z1,z2,z3,z5,z6]),(0,[z111,z1,z2,z3,z232,z6]),(0,[z1202,z1,z2,z3,z4,z6]),(0,[z1203,z1,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z1204,z6])],[(0,[z95,z1,z2,z3,z159,z6]),(0,[z1,z772,z2,z3,z4,z159]),(0,[z62,z11,z12,z238,z4,z6]),(0,[z26,z1,z570,z3,z4,z6]),(0,[z169,z11,z2,z3,z626,z106])],[(0,[z11,z1,z8,z526,z4,z6]),(0,[z1205,z1,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z1206,z6])],[(0,[z1207,z1,z2,z3,z4,z6]),(0,[z1,z2,z3,z5,z292,z6]),(0,[z9,z1,z278,z3,z4,z6]),(0,[z1,z1208,z2,z3,z4,z6]),(0,[z1209,z1,z2,z3,z4,z6])],[(0,[z1,z2,z3,z553,z5,z6]),(0,[z1,z2,z3,z382,z6,z51]),(0,[z62,z11,z12,z3,z4,z252]),(0,[z169,z11,z79,z3,z4,z106])],[(0,[z1,z28,z2,z3,z4,z136]),(0,[z1,z89,z2,z3,z4,z6]),(0,[z1,z2,z52,z5,z19,z6]),(0,[z11,z1210,z2,z3,z4,z6]),(0,[z263,z1,z2,z3,z19,z6])],[(0,[z1,z2,z3,z1211,z4,z6]),(0,[z1,z467,z3,z4,z505,z6]),(0,[z1,z2,z3,z109,z5,z51]),(0,[z45,z11,z2,z102,z4,z453])],[(0,[z11,z1,z46,z3,z4,z217]),(0,[z212,z1,z2,z3,z1068,z6]),(0,[z11,z1,z1212,z3,z4,z6])]],
   [[(0,[z21,z1,z2,z3,z1213,z6]),(0,[z330,z1,z2,z3,z902,z6])],[(0,[z68,z1,z2,z3,z159,z6])],[(0,[z111,z1,z2,z3,z44,z6]),(1,[z11,z739,z3,z4,z6]),(0,[z11,z1,z2,z3,z4,z1214]),(0,[z14,z11,z2,z3,z717,z6]),(0,[z1,z2,z3,z4,z1215,z6])],[(0,[z785,z1,z2,z4,z159,z6]),(0,[z11,z1,z2,z15,z24,z6]),(0,[z11,z1,z1216,z2,z4,z6]),(0,[z11,z212,z2,z52,z4,z6]),(0,[z422,z1,z570,z3,z4,z6]),(0,[z11,z1,z2,z3,z748,z6]),(0,[z1,z1217,z2,z3,z4,z6])],[(0,[z113,z1,z2,z3,z145,z6]),(0,[z1,z2,z176,z3,z145,z6]),(0,[z45,z9,z2,z102,z4,z6]),(0,[z1,z91,z3,z4,z248,z37]),(0,[z11,z1,z1218,z3,z4,z6])],[],[(0,[z1,z2,z3,z159,z13,z6]),(0,[z212,z1,z2,z3,z145,z6]),(0,[z1,z2,z3,z5,z6,z51]),(0,[z527,z2,z3,z4,z118,z6]),(0,[z45,z11,z278,z102,z4,z6]),(0,[z1219,z1,z2,z3,z4,z6])],[(0,[z21,z1,z2,z3,z109,z51]),(0,[z11,z1,z570,z321,z4,z6]),(0,[z11,z1,z267,z3,z4,z6]),(0,[z11,z1,z2,z3,z1220,z6]),(1,[z1,z2,z3,z787,z6])],[(0,[z1,z2,z3,z382,z145,z6]),(0,[z1221,z1,z2,z3,z4,z6])],[(0,[z1,z164,z2,z3,z145,z6]),(0,[z21,z1,z90,z2,z4,z6]),(0,[z11,z1,z2,z3,z4,z210]),(1,[z11,z2,z743,z4,z6])],[(0,[z21,z1,z2,z3,z145,z6]),(0,[z1,z2,z3,z5,z6,z116]),(0,[z11,z1,z2,z1222,z4,z6]),(0,[z75,z11,z2,z3,z118,z6]),(0,[z1223,z1,z2,z3,z4,z6])],[(0,[z21,z527,z2,z3,z4,z6]),(0,[z11,z1,z2,z198,z48,z6]),(0,[z108,z1,z2,z3,z4,z217]),(0,[z63,z11,z1,z3,z872,z6])],[(0,[z1224,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z1225,z6]),(0,[z40,z1,z2,z3,z24,z6]),(0,[z1226,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z1227,z4,z6])],[(0,[z11,z1,z2,z3,z1228,z6]),(0,[z1,z2,z55,z3,z5,z6]),(0,[z11,z1,z2,z238,z4,z252])],[(0,[z95,z1,z2,z3,z104,z6])],[(0,[z1,z28,z2,z3,z359,z6]),(0,[z1229,z1,z2,z3,z4,z6]),(0,[z1230,z1,z2,z3,z4,z6]),(0,[z1231,z1,z2,z3,z4,z6]),(0,[z1232,z1,z2,z3,z4,z6])]],
   [[(0,[z11,z1,z2,z3,z4,z1233]),(0,[z1,z2,z3,z4,z1064,z6]),(1,[z1,z2,z3,z1068,z6])],[(0,[z1,z2,z3,z1234,z4,z6]),(0,[z1,z535,z23,z3,z4,z6]),(0,[z1,z3,z94,z5,z13,z6]),(0,[z11,z1,z2,z3,z4,z136])],[(0,[z456,z1,z2,z3,z4,z31]),(0,[z1,z2,z3,z145,z13,z6])],[(0,[z664,z28,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z1235,z6]),(0,[z615,z1,z2,z3,z5,z6]),(0,[z119,z1,z2,z3,z5,z6]),(0,[z11,z235,z2,z3,z4,z162]),(0,[z11,z1,z2,z3,z1236,z6]),(0,[z1,z2,z3,z4,z1237,z6])],[(0,[z218,z95,z2,z3,z96,z6])],[(0,[z72,z1,z2,z3,z5,z6]),(0,[z66,z11,z1,z3,z4,z657]),(0,[z11,z1,z29,z779,z4,z6])],[(0,[z21,z1,z2,z3,z837,z6]),(0,[z26,z1,z2,z486,z4,z6]),(0,[z1238,z1,z2,z3,z4,z6])],[(0,[z113,z11,z1,z2,z19,z6]),(0,[z113,z11,z1,z2,z1024,z6])],[(0,[z1,z2,z4,z1189,z159,z6]),(0,[z1,z2,z3,z301,z145,z6]),(0,[z49,z1,z2,z3,z232,z6])],[],[(0,[z1,z28,z2,z3,z1239,z6]),(0,[z11,z1,z2,z3,z1240,z6])],[(0,[z1,z28,z2,z3,z131,z6]),(0,[z1,z2,z3,z5,z178,z6]),(0,[z95,z1,z2,z3,z382,z6]),(0,[z1241,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z775,z6]),(0,[z11,z1,z1242,z3,z4,z6])],[(0,[z21,z1,z2,z171,z48,z6]),(0,[z1,z2,z3,z4,z1243,z6]),(0,[z11,z1,z91,z3,z4,z37]),(0,[z1244,z1,z2,z3,z4,z6])],[(0,[z50,z1,z2,z3,z145,z6]),(0,[z71,z1,z2,z3,z145,z6]),(0,[z393,z1,z2,z3,z4,z82]),(0,[z112,z1,z2,z3,z5,z6]),(0,[z11,z1,z2,z3,z24,z136]),(0,[z1245,z1,z2,z3,z4,z6])],[(0,[z11,z1,z570,z486,z4,z6])],[(0,[z1,z28,z255,z3,z4,z6]),(0,[z1,z28,z2,z4,z1189,z6]),(0,[z1,z2,z3,z131,z5,z6])]],
   [[(0,[z1,z3,z978,z4,z5,z6]),(0,[z49,z1,z2,z3,z4,z67]),(0,[z1246,z1,z2,z3,z4,z6]),(0,[z422,z1,z2,z486,z4,z6]),(0,[z1247,z1,z2,z3,z4,z6])],[(0,[z287,z1,z2,z3,z4,z6]),(0,[z508,z28,z2,z3,z4,z6]),(0,[z21,z1,z2,z3,z32,z6]),(0,[z72,z1,z2,z3,z963,z6]),(0,[z1,z2,z3,z627,z5,z6]),(0,[z1248,z1,z2,z3,z4,z6]),(0,[z11,z2,z3,z717,z118,z6]),(0,[z14,z2,z3,z118,z159,z6]),(0,[z1,z1249,z2,z3,z4,z6])],[(0,[z1250,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z1015,z6]),(0,[z1,z10,z3,z5,z13,z6]),(0,[z1,z2,z3,z4,z5,z453]),(0,[z1,z2,z3,z1251,z4,z6])],[(0,[z11,z1,z2,z3,z359,z6]),(0,[z14,z1,z2,z15,z5,z6]),(0,[z11,z1,z2,z1252,z4,z6]),(0,[z1253,z1,z2,z3,z4,z6]),(0,[z1254,z1,z2,z3,z4,z6]),(0,[z57,z1,z2,z3,z777,z6])],[(0,[z9,z1,z2,z3,z4,z65])],[(0,[z1255,z1,z2,z3,z4,z6])],[(0,[z11,z1,z1256,z3,z4,z6]),(0,[z72,z1,z2,z3,z145,z6]),(0,[z11,z1,z255,z3,z4,z503]),(0,[z317,z11,z2,z3,z118,z6]),(0,[z221,z1,z2,z173,z4,z86])],[(0,[z11,z1,z2,z1257,z4,z6])],[(0,[z1,z2,z4,z5,z1189,z6]),(0,[z1,z164,z3,z94,z5,z6]),(0,[z11,z1,z3,z4,z1258,z6]),(0,[z428,z1,z2,z3,z4,z136]),(0,[z1,z1259,z2,z3,z4,z6])],[(0,[z11,z1,z2,z3,z1097,z6]),(0,[z998,z1,z2,z4,z5,z6])],[(0,[z1,z2,z313,z4,z5,z6])],[(0,[z1,z2,z3,z963,z5,z6]),(0,[z9,z95,z2,z3,z96,z6]),(0,[z1,z1260,z2,z3,z4,z6]),(0,[z11,z1,z2,z102,z180,z6]),(0,[z1261,z1,z2,z3,z4,z6]),(0,[z1262,z1,z2,z3,z4,z6])],[(0,[z11,z1,z2,z3,z4,z1263]),(0,[z1264,z1,z2,z3,z4,z6]),(0,[z1265,z1,z2,z3,z4,z6])],[(0,[z693,z1,z2,z3,z5,z6]),(0,[z11,z1,z2,z130,z4,z136]),(0,[z671,z11,z2,z3,z4,z106]),(0,[z11,z1,z8,z29,z4,z6])],[(0,[z11,z1,z2,z3,z1239,z6]),(0,[z63,z1,z3,z5,z13,z6])],[(0,[z197,z1,z2,z42,z4,z6]),(0,[z11,z1,z2,z3,z131,z6]),(0,[z1266,z1,z2,z3,z4,z6])]],
   [[(0,[z9,z1,z2,z3,z425,z6]),(0,[z1267,z1,z2,z3,z4,z6]),(0,[z11,z1,z3,z1268,z4,z6])],[(0,[z47,z1,z2,z3,z4,z6]),(0,[z1,z2,z3,z5,z440,z6])],[(0,[z9,z1,z2,z3,z4,z217]),(0,[z1269,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z173,z4,z1070])],[(0,[z30,z1,z2,z3,z4,z69]),(0,[z11,z1,z255,z3,z4,z6])],[(0,[z11,z1,z2,z1270,z4,z6]),(0,[z1,z2,z3,z145,z162,z6]),(0,[z11,z1,z2,z3,z4,z790]),(0,[z1271,z1,z2,z3,z4,z6])],[(0,[z547,z28,z2,z3,z4,z6]),(0,[z1,z2,z42,z4,z6,z269]),(0,[z1,z2,z3,z206,z5,z6])],[(0,[z21,z1,z2,z163,z4,z6]),(0,[z1,z1272,z2,z3,z4,z6])],[(0,[z350,z1,z2,z3,z4,z6]),(0,[z30,z1,z2,z3,z4,z83]),(0,[z346,z1,z2,z3,z4,z136]),(0,[z169,z26,z2,z3,z4,z106]),(0,[z1,z1273,z2,z3,z4,z6])],[(0,[z1,z887,z2,z3,z4,z6]),(0,[z1,z28,z2,z3,z4,z210]),(0,[z329,z1,z2,z3,z5,z6]),(0,[z11,z1,z2,z3,z1024,z6])],[(0,[z1,z2,z386,z3,z145,z6]),(0,[z1274,z1,z2,z3,z4,z6]),(0,[z1,z1153,z3,z4,z5,z6]),(0,[z193,z11,z2,z102,z4,z6])],[(0,[z1,z1275,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z1118,z6]),(0,[z1,z2,z3,z5,z463,z6]),(0,[z11,z1,z2,z3,z4,z1070])],[(0,[z1276,z1,z2,z3,z145,z6]),(0,[z62,z9,z12,z3,z4,z6]),(0,[z11,z1,z2,z3,z4,z1277]),(0,[z1,z2,z3,z4,z1278,z6])],[(0,[z212,z28,z2,z52,z4,z6]),(0,[z1,z2,z3,z1279,z145,z6]),(0,[z11,z1,z1280,z3,z4,z6]),(0,[z1281,z1,z2,z3,z4,z6])],[(0,[z424,z1,z2,z3,z145,z6]),(0,[z1,z2,z3,z145,z118,z6]),(0,[z1,z2,z3,z4,z1282,z6]),(0,[z14,z1,z2,z3,z5,z136]),(0,[z1,z2,z3,z4,z1160,z6]),(0,[z45,z11,z2,z102,z4,z217]),(0,[z11,z582,z2,z52,z4,z6]),(0,[z1283,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z171,z1024,z6]),(0,[z11,z1,z1284,z3,z4,z6])],[(0,[z1,z2,z3,z1160,z5,z6]),(0,[z317,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z293,z6]),(0,[z185,z1,z2,z3,z32,z6]),(0,[z119,z11,z2,z3,z118,z6]),(0,[z11,z1,z79,z3,z131,z6])],[(0,[z11,z1,z2,z3,z1285,z6]),(0,[z11,z1,z2,z3,z1125,z6]),(0,[z11,z1,z2,z3,z4,z1286]),(0,[z95,z2,z3,z4,z382,z6])]],
   [[(0,[z11,z1,z2,z3,z4,z1287]),(0,[z1,z2,z3,z180,z5,z6]),(0,[z1,z2,z3,z691,z5,z6]),(0,[z1,z2,z3,z5,z473,z6]),(0,[z11,z1,z2,z3,z1288,z6]),(0,[z11,z1,z8,z3,z4,z429]),(0,[z11,z1,z2,z3,z577,z51])],[(0,[z1,z2,z3,z4,z104,z6]),(0,[z9,z1,z2,z3,z179,z6]),(0,[z11,z1,z2,z1289,z4,z6]),(0,[z11,z1,z1290,z3,z4,z6]),(0,[z11,z1,z2,z3,z1291,z6])],[(0,[z1,z2,z3,z4,z1292,z6]),(0,[z1,z2,z1179,z163,z4,z6])],[(0,[z496,z28,z2,z3,z4,z6]),(0,[z1,z153,z2,z3,z4,z6]),(0,[z21,z1,z2,z3,z797,z6]),(0,[z11,z1,z2,z3,z4,z1293])],[(0,[z11,z1,z2,z3,z4,z818]),(0,[z360,z1,z251,z3,z4,z6])],[(0,[z1,z1294,z2,z3,z4,z6]),(0,[z1295,z1,z2,z3,z4,z6]),(0,[z11,z1,z127,z4,z6,z429]),(0,[z1,z2,z3,z4,z1296,z6]),(0,[z1,z2,z3,z4,z6,z1297]),(0,[z1,z2,z3,z4,z1298,z6])],[(0,[z1,z1299,z2,z3,z4,z6]),(0,[z1,z23,z2,z3,z232,z6]),(0,[z1,z2,z3,z48,z104,z6]),(0,[z1300,z1,z2,z3,z4,z6])],[(0,[z1,z28,z2,z3,z4,z6]),(0,[z21,z1,z46,z3,z4,z6]),(0,[z22,z1,z2,z352,z4,z6]),(0,[z1,z2,z3,z4,z1301,z6]),(0,[z1,z2,z3,z121,z4,z31]),(0,[z68,z9,z1,z2,z3,z73]),(0,[z11,z1,z278,z3,z4,z453]),(0,[z1302,z1,z2,z3,z4,z6])],[(0,[z11,z1,z714,z3,z4,z6]),(0,[z1,z2,z3,z275,z5,z6])],[(0,[z1,z2,z42,z3,z232,z6])],[(0,[z62,z287,z12,z3,z4,z6]),(0,[z428,z1,z255,z3,z4,z6])],[(0,[z1,z28,z91,z3,z4,z37]),(0,[z342,z1,z2,z84,z4,z6]),(0,[z411,z1,z2,z3,z5,z6])],[(0,[z11,z1,z2,z3,z1303,z6])],[(0,[z11,z1,z1304,z3,z4,z6])],[(0,[z11,z1,z2,z855,z4,z6]),(0,[z1,z3,z505,z5,z13,z6]),(0,[z11,z1,z2,z3,z4,z503]),(0,[z14,z11,z2,z15,z118,z6])],[(0,[z9,z1,z164,z3,z94,z6]),(0,[z9,z1,z3,z188,z4,z6]),(0,[z11,z1,z2,z3,z1184,z6]),(0,[z1305,z1,z2,z3,z4,z6]),(0,[z11,z1,z55,z3,z118,z6]),(0,[z11,z1,z255,z130,z4,z6]),(0,[z1306,z1,z2,z3,z4,z6])]],
   [[(0,[z1307,z1,z2,z3,z4,z6]),(0,[z844,z11,z1,z3,z4,z6]),(0,[z1,z23,z2,z3,z44,z6]),(0,[z11,z1,z2,z3,z4,z1308]),(0,[z11,z1,z2,z3,z4,z1309]),(0,[z1310,z1,z2,z3,z4,z6]),(0,[z11,z1,z1311,z3,z4,z6])],[(0,[z11,z1,z2,z238,z179,z6]),(0,[z11,z1,z298,z127,z4,z65]),(0,[z1,z164,z3,z94,z226,z6]),(0,[z11,z1,z2,z3,z73,z991])],[(0,[z1,z2,z258,z4,z544,z6]),(0,[z9,z1,z2,z3,z232,z6]),(0,[z1312,z1,z2,z3,z4,z6]),(0,[z1313,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z4,z1314])],[(0,[z11,z1,z1315,z3,z4,z6]),(0,[z22,z1,z2,z84,z44,z6]),(0,[z1,z2,z3,z4,z209,z6]),(0,[z1,z2,z3,z4,z5,z65]),(0,[z9,z1,z2,z3,z239,z6]),(0,[z1,z1316,z2,z3,z4,z6])],[(0,[z11,z1,z2,z3,z1317,z6]),(0,[z428,z1,z2,z3,z5,z6]),(0,[z1178,z1,z2,z3,z4,z6])],[(0,[z1,z2,z3,z5,z51,z106]),(0,[z11,z1,z2,z52,z4,z217])],[(0,[z1,z28,z79,z3,z4,z6]),(0,[z1,z2,z171,z48,z5,z6]),(0,[z47,z1,z2,z3,z5,z6]),(0,[z1318,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z171,z610,z6]),(0,[z11,z1,z2,z3,z903,z6])],[(1,[z1,z2,z3,z4,z831]),(0,[z1319,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z1320,z6]),(1,[z1,z2,z3,z808,z6]),(0,[z11,z1,z164,z3,z630,z6])],[],[(0,[z281,z1,z2,z3,z465,z4]),(0,[z1321,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z4,z1322]),(0,[z346,z1,z255,z3,z4,z6]),(0,[z1323,z1,z2,z3,z4,z6])],[(0,[z11,z1,z772,z2,z3,z4]),(0,[z9,z1,z2,z15,z4,z6]),(0,[z11,z1,z2,z1324,z4,z6]),(0,[z11,z1325,z2,z3,z4,z6])],[(0,[z11,z1,z2,z3,z4,z6]),(0,[z1,z17,z2,z3,z145,z6]),(0,[z11,z1,z2,z3,z4,z1326]),(0,[z111,z1,z549,z3,z4,z6])],[(0,[z1,z28,z8,z29,z4,z6]),(0,[z9,z1,z2,z3,z44,z6]),(0,[z11,z1,z2,z3,z4,z1327])],[(0,[z11,z1,z1115,z2,z4,z6]),(0,[z336,z1,z2,z3,z5,z6])],[(0,[z1274,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z6,z376])],[(0,[z1,z2,z3,z145,z6,z37]),(0,[z609,z1,z2,z3,z5,z6]),(0,[z14,z1,z255,z3,z5,z6]),(0,[z279,z1,z2,z3,z5,z6]),(0,[z1,z1328,z2,z3,z4,z6]),(0,[z68,z11,z1,z2,z3,z991])]],
   [[(0,[z30,z1,z2,z3,z145,z6]),(0,[z11,z1,z2,z1329,z4,z6]),(0,[z1,z1330,z2,z3,z4,z6])],[(0,[z1,z2,z3,z4,z5,z217]),(0,[z11,z1,z46,z3,z180,z6]),(0,[z11,z2,z3,z4,z162,z723])],[(0,[z11,z1,z2,z3,z625,z51])],[(0,[z125,z1,z2,z3,z4,z6]),(0,[z1,z28,z2,z130,z4,z6]),(0,[z21,z318,z2,z3,z4,z6]),(0,[z1,z8,z2,z3,z145,z6]),(0,[z263,z1,z2,z3,z4,z6])],[(0,[z1,z1331,z2,z3,z4,z6]),(0,[z21,z1,z298,z127,z4,z6]),(0,[z11,z1,z2,z1332,z4,z6]),(0,[z185,z1,z46,z3,z4,z6]),(0,[z1333,z1,z2,z3,z4,z6])],[(0,[z21,z1,z2,z3,z858,z6]),(0,[z428,z1,z2,z3,z4,z503]),(0,[z11,z1,z1334,z3,z4,z6]),(0,[z11,z151,z2,z3,z96,z6])],[(0,[z1,z28,z3,z4,z1154,z6]),(0,[z22,z1,z2,z431,z4,z6])],[(0,[z11,z1,z2,z3,z626,z6]),(0,[z11,z1,z2,z4,z1070,z86])],[(0,[z1,z2,z3,z359,z5,z6]),(0,[z1,z2,z3,z361,z5,z6]),(0,[z14,z11,z2,z3,z118,z136])],[(0,[z1,z124,z2,z3,z118,z6]),(0,[z1,z2,z3,z145,z1335,z6]),(0,[z21,z1,z2,z3,z4,z429]),(0,[z11,z1,z2,z3,z4,z1336]),(0,[z1,z2,z3,z4,z1337,z6]),(0,[z11,z1,z164,z3,z872,z6]),(0,[z11,z1,z1338,z3,z4,z6])],[(0,[z21,z1,z2,z321,z4,z6]),(0,[z9,z1,z267,z3,z4,z6]),(0,[z11,z1,z79,z3,z4,z6]),(0,[z11,z1,z2,z130,z4,z503]),(0,[z11,z1,z148,z2,z4,z86])],[(0,[z63,z1,z28,z3,z13,z6]),(0,[z9,z1,z2,z313,z4,z6]),(0,[z169,z11,z2,z3,z4,z723]),(0,[z11,z1,z705,z127,z4,z6])],[(0,[z1,z2,z3,z1339,z145,z6]),(0,[z1340,z1,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z1341,z6]),(0,[z113,z263,z1,z2,z19,z6]),(0,[z1,z2,z173,z4,z245,z86])],[(0,[z1342,z1,z2,z3,z4,z6]),(0,[z108,z1,z2,z3,z180,z6])],[(0,[z58,z887,z2,z3,z4,z6]),(0,[z169,z28,z2,z3,z4,z106]),(0,[z167,z1,z2,z3,z5,z6]),(0,[z11,z1,z588,z3,z4,z37]),(0,[z53,z1,z2,z3,z808,z6])],[(0,[z1,z2,z3,z4,z159,z6]),(0,[z1343,z1,z2,z3,z4,z6]),(0,[z1,z23,z3,z4,z6,z420]),(0,[z11,z1,z10,z238,z4,z6])]],
   [[(0,[z1,z28,z2,z3,z88,z6]),(0,[z1344,z1,z2,z3,z4,z6])],[(0,[z11,z1,z55,z3,z96,z6])],[(0,[z428,z1,z2,z3,z4,z6]),(0,[z11,z1,z1345,z2,z4,z6]),(0,[z1,z2,z3,z104,z19,z6])],[(0,[z1,z2,z3,z94,z159,z6]),(0,[z62,z1,z2,z3,z145,z6]),(0,[z1,z2,z3,z145,z159,z6]),(0,[z125,z1,z2,z3,z129,z6]),(0,[z21,z1,z2,z173,z4,z86]),(0,[z66,z9,z1,z3,z4,z36])],[(0,[z1,z2,z3,z48,z159,z6]),(0,[z1,z2,z48,z5,z19,z6]),(0,[z224,z11,z1,z2,z19,z6]),(0,[z346,z1,z2,z3,z4,z503])],[],[(0,[z412,z1,z2,z3,z145,z6]),(0,[z1,z2,z15,z4,z5,z6]),(0,[z11,z1,z79,z3,z626,z6]),(0,[z11,z1,z621,z2,z19,z6]),(0,[z1,z2,z3,z4,z1346,z6])],[(0,[z1347,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z130,z4,z6]),(0,[z1348,z1,z2,z3,z4,z6])],[(0,[z11,z1,z2,z1349,z4,z6]),(0,[z1,z1350,z2,z3,z4,z6]),(0,[z11,z1,z323,z3,z4,z37]),(0,[z1351,z1,z2,z3,z4,z6]),(0,[z11,z1,z2,z3,z991,z6])],[(0,[z785,z1,z28,z2,z4,z6]),(0,[z1,z2,z3,z626,z5,z6]),(0,[z11,z1,z1352,z3,z4,z6]),(0,[z47,z1,z2,z171,z48,z6])],[(0,[z1,z28,z2,z3,z109,z51]),(0,[z11,z1,z3,z4,z1154,z6]),(0,[z21,z375,z2,z3,z4,z6]),(0,[z11,z1,z1353,z3,z4,z6]),(0,[z11,z1,z1354,z3,z4,z6])],[(0,[z212,z103,z2,z52,z4,z6]),(0,[z1355,z1,z2,z3,z4,z6])],[(0,[z28,z2,z3,z4,z6,z135]),(0,[z1,z28,z90,z2,z4,z6]),(0,[z1274,z1,z2,z3,z48,z6])],[(0,[z58,z28,z2,z3,z4,z6]),(0,[z1,z28,z2,z3,z145,z6]),(0,[z1,z28,z2,z3,z4,z503]),(0,[z1,z2,z3,z145,z36,z6]),(0,[z1,z1356,z2,z3,z4,z6])],[(0,[z428,z1,z2,z3,z24,z6]),(0,[z11,z1,z2,z3,z1357,z6]),(0,[z11,z1,z2,z3,z4,z1358]),(1,[z1,z2,z3,z877,z6]),(0,[z1244,z1,z2,z163,z4,z6]),(0,[z1359,z1,z2,z3,z4,z6])],[(0,[z66,z11,z1,z3,z4,z461])]],
   [[(0,[z60,z1,z2,z3,z145,z6]),(0,[z1,z2,z3,z39,z67,z6]),(0,[z1,z2,z855,z84,z4,z6]),(0,[z47,z1,z2,z3,z24,z6]),(0,[z241,z1,z298,z127,z4,z6])],[(0,[z11,z1,z2,z1360,z4,z6]),(0,[z346,z1,z2,z3,z4,z6]),(0,[z9,z1,z2,z3,z531,z6])],[(0,[z428,z1,z2,z3,z129,z6]),(0,[z1361,z1,z2,z3,z4,z6])],[(0,[z11,z1362,z2,z3,z4,z6]),(0,[z1,z2,z102,z5,z19,z6]),(0,[z62,z11,z12,z3,z179,z6]),(0,[z1363,z1,z2,z3,z4,z6]),(0,[z609,z11,z1,z2,z19,z6]),(0,[z11,z212,z2,z743,z4,z6]),(0,[z169,z11,z2,z321,z4,z106]),(0,[z11,z1,z29,z597,z4,z6])],[(0,[z11,z1,z2,z3,z88,z6]),(0,[z1364,z1,z2,z3,z4,z6])],[(0,[z14,z2,z3,z5,z118,z6]),(0,[z1,z2,z3,z1365,z4,z6]),(0,[z1,z2,z3,z4,z831,z31]),(0,[z0,z89,z2,z3,z4,z162])],[(0,[z1,z103,z2,z3,z4,z6]),(0,[z1,z2,z3,z121,z4,z93]),(0,[z1366,z1,z2,z3,z4,z6]),(0,[z11,z1,z278,z3,z4,z217]),(0,[z11,z1,z779,z2,z4,z6])],[(0,[z11,z1,z2,z3,z1213,z6]),(0,[z1,z2,z3,z4,z1161,z6]),(0,[z14,z1,z2,z3,z5,z6]),(0,[z11,z1,z656,z127,z4,z6]),(0,[z11,z1,z2,z3,z1367,z6]),(0,[z11,z1,z2,z607,z48,z6]),(0,[z1368,z1,z2,z3,z4,z6])],[(0,[z1369,z1,z2,z3,z145,z6]),(0,[z1370,z1,z2,z3,z4,z6]),(0,[z1,z2,z3,z94,z104,z6])],[(0,[z1,z1371,z2,z3,z4,z6]),(0,[z1,z2,z238,z4,z5,z6]),(1,[z1,z55,z3,z5,z6]),(0,[z11,z1,z1372,z3,z4,z6]),(0,[z1,z2,z3,z903,z6,z37])],[(0,[z21,z1,z2,z238,z4,z6]),(0,[z11,z1,z2,z3,z1068,z6]),(0,[z14,z11,z255,z3,z118,z6]),(0,[z11,z1373,z2,z3,z4,z6]),(0,[z1374,z1,z2,z3,z4,z6])],[(0,[z1,z124,z2,z3,z96,z6]),(0,[z11,z1,z2,z3,z4,z1375]),(0,[z11,z1,z2,z1376,z4,z6]),(0,[z11,z1,z2,z1377,z4,z6]),(0,[z1,z2,z3,z4,z1378,z6])],[(0,[z30,z1,z2,z3,z39,z6]),(0,[z11,z1,z2,z3,z963,z6]),(0,[z1,z2,z3,z4,z5,z1124])],[(0,[z21,z1,z2,z3,z4,z252]),(0,[z1,z2,z3,z84,z44,z6]),(0,[z1,z298,z257,z127,z4,z6]),(0,[z241,z1,z2,z3,z877,z6])],[(0,[z21,z433,z2,z3,z4,z6]),(0,[z87,z1,z176,z3,z4,z6]),(0,[z1,z2,z3,z179,z5,z6]),(0,[z428,z1,z2,z130,z4,z6]),(0,[z11,z1,z2,z3,z109,z51])],[(0,[z1,z28,z2,z171,z48,z6]),(0,[z1379,z1,z2,z3,z4,z6]),(0,[z11,z1,z1380,z3,z4,z6]),(0,[z1,z2,z3,z4,z1381,z6]),(0,[z1,z2,z3,z4,z6,z1382]),(0,[z1,z2,z3,z4,z1383,z6]),(0,[z113,z403,z1,z2,z19,z6])]]]

def SA : ℕ × List W → Bool := fun c => !inB2 8 256 bkA c

def SB : ℕ × List W → Bool := fun c => !inB2 16 512 bkB c

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 492) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 492).take 494) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 986).take 429) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1415)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [492, 494, 429] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 109).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 109).take 118).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 227).take 108).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 335).take 107).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc4 : chunkOK 5 ((bkB.flatten.drop 442).take 70).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 512)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [109, 118, 108, 107, 70] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_cons pc3 (windowsF_cons pc4 (windowsF_nil pcend)))))

theorem reject : search 8 rows = false :=
  search_false_C2 (dp := 0) (J := 5) (d := 2) (g1 := 8) (nb1 := 256) (g2 := 16) (nb2 := 512) (by norm_num) gf windowsC windowsB windowsA

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

end PEqualNP.Outside.L_meta_37651

theorem PEqualNP.Outside.L_meta_37651 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276813544 * 2 ^ 32 + 4276791976) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276813544 * 2 ^ 32 + 4276791976) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_37651.solve