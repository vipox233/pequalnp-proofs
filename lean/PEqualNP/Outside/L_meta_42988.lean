import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_42988

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
  Nat.testBit (4276677320 * 2 ^ 32 + 4209043968) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x00236270c170e158#64 ++ 0x000236270c170e15#64 ++ 0x4067e7f1c3f1e3f7#64 ++ 0xe4067e7f1c3f1e3f#64 : BitVec 256),
   (0x0388a91763362cc0#64 ++ 0x10388a91763362cc#64 ++ 0x0798f93fe33e3ccd#64 ++ 0xf0798f93fe33e3cc#64 : BitVec 256),
   (0x5815163a0c1b7700#64 ++ 0x25815163a0c1b770#64 ++ 0xf81f1e3e3c3fff0e#64 ++ 0xff81f1e3e3c3fff0#64 : BitVec 256),
   (0x2dc01d8036801aa0#64 ++ 0x42dc01d8036801aa#64 ++ 0xffe01fc03fc03fff#64 ++ 0x7ffe01fc03fc03ff#64 : BitVec 256),
   (0xf6fee0003bed8000#64 ++ 0x8f6fee0003bed800#64 ++ 0xffffe0003fffc00f#64 ++ 0xbffffe0003fffc00#64 : BitVec 256),
   (0xbf7fdfed80000001#64 ++ 0x0bf7fdfed8000000#64 ++ 0xbfffffffc000000f#64 ++ 0xcbfffffffc000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [1, 2]⟩, ⟨.or, [0, 6]⟩, ⟨.and, [1, 5]⟩, ⟨.or, [8, 2]⟩, ⟨.or, [8, 3]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [7, 10]⟩, ⟨.and, [9, 11]⟩, ⟨.and, [13, 4]⟩, ⟨.or, [12, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x00236270c170e158 0x000236270c170e15 0x4067e7f1c3f1e3f7 0xe4067e7f1c3f1e3f

def z1 : W := mkw 0x0388a91763362cc0 0x10388a91763362cc 0x0798f93fe33e3ccd 0xf0798f93fe33e3cc

def z2 : W := mkw 0x0801167ac4127758 0x20801167ac412775 0x00001fffc0003ff0 0x400001fffc0003ff

def z3 : W := mkw 0x2dc01d8036801aa0 0x42dc01d8036801aa 0xffe01fc03fc03fff 0x7ffe01fc03fc03ff

def z4 : W := mkw 0x5815163a0c1b7700 0x25815163a0c1b770 0xf81f1e3e3c3fff0e 0xff81f1e3e3c3fff0

def z5 : W := mkw 0xbf7fdfed80000001 0x0bf7fdfed8000000 0xbfffffffc000000f 0xcbfffffffc000000

def z6 : W := mkw 0xf6fee0003bed8000 0x8f6fee0003bed800 0xffffe0003fffc00f 0xbffffe0003fffc00

def z7 : W := mkw 0x0100090000000000 0x0010009000000000 0x078019000000000d 0x4078019000000000

def z8 : W := mkw 0x0080201263362cc0 0x10080201263362cc 0x00000000233e3cc0 0x300000000233e3cc

def z9 : W := mkw 0x581516280c095300 0x2581516280c09530 0xf81f1e3e1c01c30e 0xcf81f1e3e1c01c30

def z10 : W := mkw 0x581516280c095300 0x2581516280c09530 0xf81f06003c3fc30e 0xbf81f06003c3fc30

def z11 : W := mkw 0x00236270c170e158 0x000236270c170e15 0x4007e631c031e306 0xe4007e631c031e30

def z12 : W := mkw 0x00800000328008a0 0x400800000328008a 0x0000000003c000f0 0x00000000003c000f

def z13 : W := mkw 0x0023426080000000 0x0002342608000000 0x4067e7f1c3c023f7 0xe4067e7f1c3c023f

def z14 : W := mkw 0x09011ffdc0106159 0x009011ffdc010615 0x00001fffc00023f0 0x400001fffc00023f

def z15 : W := mkw 0x5015022808094100 0x2501502280809410 0x000700000001c000 0x0000700000001c00

def z16 : W := mkw 0x03abeb75e374e9d8 0x103abeb75e374e9d 0x47e7e7f1c3f1e3f7 0xe47e7e7f1c3f1e3f

def z17 : W := mkw 0xa76ac9c580000001 0x0a76ac9c58000000 0x07e0e1c1c0000001 0x007e0e1c1c000000

def z18 : W := mkw 0xa7eae90573e488c0 0x9a7eae90573e488c 0x07e0e101c3c000c1 0x007e0e101c3c000c

def z19 : W := mkw 0xa6eae00033e48000 0x8a6eae00033e4800 0x07e0e00003c00001 0x007e0e00003c0000

def z20 : W := mkw 0xfefff63a3ffff700 0xafefff63a3ffff70 0xfffffe3e3fffff0f 0xffffffe3e3fffff0

def z21 : W := mkw 0x25c00980328008a0 0x425c00980328008a 0x07e001c003c000f1 0x007e001c003c000f

def z22 : W := mkw 0x7dd41d8a3e8b1ea0 0x67dd41d8a3e8b1ea 0xbf98180e3c0e1c08 0x1bf98180e3c0e1c0

def z23 : W := mkw 0x0080000036801aa0 0x40080000036801aa 0x400000003fc03ff0 0x3400000003fc03ff

def z24 : W := mkw 0x0308890500000000 0x0030889050000000 0x0798f93fc000000d 0xc0798f93fc000000

def z25 : W := mkw 0x03abeb77e376edd8 0x103abeb77e376edd 0x47ffffffe3ffffff 0xf47ffffffe3fffff

def z26 : W := mkw 0x0000000000000000 0x0000000000000000 0x406007c003c023f7 0x6406007c003c023f

def z27 : W := mkw 0x2de37ff0f7f0fbf8 0x42de37ff0f7f0fbf 0xffe7fff1fff1ffff 0xfffe7fff1fff1fff

def z28 : W := mkw 0x0000000000000000 0x0000000000000000 0x400700000031c006 0xa400700000031c00

def z29 : W := mkw 0xf6ffe260bbed8000 0x8f6ffe260bbed800 0xffffe7f1ffffc00f 0xfffffe7f1ffffc00

def z30 : W := mkw 0x5814140a0c0b1600 0x25814140a0c0b160 0xf81f180e3c3fdc0e 0xbf81f180e3c3fdc0

def z31 : W := mkw 0x0800140004001200 0x0080014000400120 0xf80006001c000302 0x0f80006001c00030

def z32 : W := mkw 0x4288a0003bed8000 0x84288a0003bed800 0x4798e0003fffc00d 0xb4798e0003fffc00

def z33 : W := mkw 0x2cc0148036801220 0x42cc014803680122 0xffe006c03fc0033f 0x3ffe006c03fc0033

def z34 : W := mkw 0x2fc8bd9777b63ee0 0x52fc8bd9777b63ee 0xfff8fffffffe3fff 0xffff8fffffffe3ff

def z35 : W := mkw 0x032bcb6580000000 0x0032bcb658000000 0x07ffffffc000000f 0xc07ffffffc000000

def z36 : W := mkw 0x0001023000106100 0x0000102300010610 0x400706300031e306 0xe400706300031e30

def z37 : W := mkw 0x5814140a0c0b1600 0x25814140a0c0b160 0xb818180e3c0e1c08 0x1b818180e3c0e1c0

def z38 : W := mkw 0x0388891722162c80 0x10388891722162c8 0x0798183e203e3c0c 0xf0798183e203e3c0

def z39 : W := mkw 0xf6fee0107bfde158 0x8f6fee0107bfde15 0xffffe0003fffe3ff 0xbffffe0003fffe3f

def z40 : W := mkw 0x2dc03d9277b63ee0 0x52dc03d9277b63ee 0xffe01fc03ffe3fff 0x7ffe01fc03ffe3ff

def z41 : W := mkw 0xb67fe270c170e158 0x0b67fe270c170e15 0xffffe7f1c3f1e3ff 0xeffffe7f1c3f1e3f

def z42 : W := mkw 0x5837767acd7bf758 0x25837767acd7bf75 0xf87fffffffffffff 0xff87ffffffffffff

def z43 : W := mkw 0x00236272c172e558 0x000236272c172e55 0x407fffffe3ffffff 0xf407fffffe3fffff

def z44 : W := mkw 0x0000000000000000 0x0000000000000000 0x0018183e0000000c 0xc0018183e0000000

def z45 : W := mkw 0x0022600001608000 0x0002260000160800 0x4067e7c003f1e3f7 0xe4067e7c003f1e3f

def z46 : W := mkw 0x501400120c1b7700 0x2501400120c1b770 0xf81f00003c3fff0e 0xbf81f00003c3fff0

def z47 : W := mkw 0x0388890722060c80 0x10388890722060c8 0x0798180e200e1c08 0x10798180e200e1c0

def z48 : W := mkw 0xf6fee0003bed8000 0x8f6fee0003bed800 0xffffe7c03fffe3ff 0xfffffe7c03fffe3f

def z49 : W := mkw 0x0388a915633428c0 0x10388a915633428c 0x0780e131c33020c5 0xe0780e131c33020c

def z50 : W := mkw 0xf6dca0003bed8000 0x8f6dca0003bed800 0xff9800003fffc008 0x3ff9800003fffc00

def z51 : W := mkw 0x0388a905632408c0 0x10388a905632408c 0x0780f901e3003ccd 0x70780f901e3003cc

def z52 : W := mkw 0x0080201263362cc0 0x10080201263362cc 0x0018183e233e3ccc 0xf0018183e233e3cc

def z53 : W := mkw 0x2febfff7f7f6fff8 0x52febfff7f7f6fff 0xffffffffffffffff 0xffffffffffffffff

def z54 : W := mkw 0xbf7fdfed8040c119 0x0bf7fdfed8040c11 0xffffffffc0c1c33f 0xcffffffffc0c1c33

def z55 : W := mkw 0x5037627ac97be558 0x25037627ac97be55 0x407fe7ffc3ffe3f7 0xe407fe7ffc3ffe3f

def z56 : W := mkw 0x0388a91777b63ee0 0x50388a91777b63ee 0x4798f93ffffe3ffd 0xf4798f93ffffe3ff

def z57 : W := mkw 0xa7eae98033e488a0 0xca7eae98033e488a 0x07e0e1c003c000f1 0x007e0e1c003c000f

def z58 : W := mkw 0xbf5c9d8d00000001 0x0bf5c9d8d0000000 0xbf98180e00000008 0x0bf98180e0000000

def z59 : W := mkw 0x581516280c095300 0x2581516280c09530 0xf80706001c01c302 0x0f80706001c01c30

def z60 : W := mkw 0xbc7756e880000001 0x0bc7756e88000000 0xb86706c000000002 0x0b86706c00000000

def z61 : W := mkw 0x5837763a0d7bf700 0x25837763a0d7bf70 0xf87ffe3e3fffff0f 0xff87ffe3e3fffff0

def z62 : W := mkw 0xf67ec00018c98000 0x8f67ec00018c9800 0xffffe0001cc1c00f 0x8ffffe0001cc1c00

def z63 : W := mkw 0x822ac04580000001 0x0822ac0458000000 0x0000e001c0000000 0x00000e001c000000

def z64 : W := mkw 0xffdc9d803e8d1aa0 0xcffdc9d803e8d1aa 0xbf9818003c0e1c08 0x1bf9818003c0e1c0

def z65 : W := mkw 0xd21c8000080d0000 0x8d21c8000080d000 0x00180000000e0000 0x000180000000e000

def z66 : W := mkw 0xb67ee00001608000 0x0b67ee0000160800 0xffffe00003f1c00f 0xaffffe00003f1c00

def z67 : W := mkw 0x5895163a3e9b7fa0 0x65895163a3e9b7fa 0xf81f1e3e3ffffffe 0xff81f1e3e3ffffff

def z68 : W := mkw 0x581516380c197300 0x2581516380c19730 0xf80706301c31e306 0xef80706301c31e30

def z69 : W := mkw 0x00226040c1608058 0x000226040c160805 0x0060e1c1c3c000f1 0x00060e1c1c3c000f

def z70 : W := mkw 0xfffefd8d3bed8001 0x8fffefd8d3bed800 0xfffff80e3fffc00f 0xbfffff80e3fffc00

def z71 : W := mkw 0x2fc89d8536801aa0 0x42fc89d8536801aa 0xfff8ffffffc03fff 0xffff8ffffffc03ff

def z72 : W := mkw 0x00236270c170e158 0x000236270c170e15 0x0007e7f1c031e3f0 0xc0007e7f1c031e3f

def z73 : W := mkw 0x0388a91763362cc0 0x10388a91763362cc 0x0798f83fe03e1c08 0x90798f83fe03e1c0

def z74 : W := mkw 0x0000001200122400 0x0000000120012240 0x0018183e203e3c0c 0xf0018183e203e3c0

def z75 : W := mkw 0x0801163a04127700 0x20801163a0412770 0x00001e3e00003f00 0x400001e3e00003f0

def z76 : W := mkw 0xbfffdfedb2800001 0x0bfffdfedb280000 0xffffffffffc0000f 0xfffffffffffc0000

def z77 : W := mkw 0xf7dca9177bbf2cc0 0x9f7dca9177bbf2cc 0xbf98f93fff3e3ccd 0xfbf98f93fff3e3cc

def z78 : W := mkw 0x09235fed80000001 0x009235fed8000000 0x0067ffffc0000007 0xc0067ffffc000000

def z79 : W := mkw 0x0100091740122cc0 0x10100091740122cc 0x0000193fc0003cc0 0x40000193fc0003cc

def z80 : W := mkw 0x25c0090032800880 0x025c009003280088 0xffe019003fc03ccf 0x7ffe019003fc03cc

def z81 : W := mkw 0xffffffedbfed9aa1 0xcffffffedbfed9aa 0xffffffffffffffff 0xffffffffffffffff

def z82 : W := mkw 0x5815162a0c0b5700 0x25815162a0c0b570 0xf81f1e0e3c0fdf0a 0x1f81f1e0e3c0fdf0

def z83 : W := mkw 0xff7fdfef8c0b1601 0x2ff7fdfef8c0b160 0xbffffffffc0e1c0f 0xdbffffffffc0e1c0

def z84 : W := mkw 0xbf7ffffdc170e159 0x0bf7ffffdc170e15 0xffffffffc3f1e3ff 0xeffffffffc3f1e3f

def z85 : W := mkw 0xbfffdfedb6801aa1 0x4bfffdfedb6801aa 0xffffffffffc03fff 0xfffffffffffc03ff

def z86 : W := mkw 0x2dc01d9776923ee0 0x52dc01d9776923ee 0xffe01fffffc03fff 0x7ffe01fffffc03ff

def z87 : W := mkw 0x2dc01d8036801aa0 0x42dc01d8036801aa 0xbf801fc03c003ff8 0x5bf801fc03c003ff

def z88 : W := mkw 0xf476400018c98000 0x8f476400018c9800 0xf86700001cc1c002 0x0f86700001cc1c00

def z89 : W := mkw 0xbfffffffe3362cc1 0x1bfffffffe3362cc 0xbfffffffe33e3ccf 0xfbfffffffe33e3cc

def z90 : W := mkw 0xd3bee9176b7facc0 0x9d3bee9176b7facc 0x079ff93fe33ffccd 0xf079ff93fe33ffcc

def z91 : W := mkw 0xb67ec00000000000 0x0b67ec0000000000 0xbfffe0000000000f 0x8bfffe0000000000

def z92 : W := mkw 0xffffffedbbed8001 0x8ffffffedbbed800 0xffffffffffffc00f 0xfffffffffffffc00

def z93 : W := mkw 0x09001d8004001aa0 0x409001d8004001aa 0x00001fc000003ff0 0x400001fc000003ff

def z94 : W := mkw 0xf6fee040fbed8058 0x8f6fee040fbed805 0xffffe1c1ffffc0ff 0xbffffe1c1ffffc0f

def z95 : W := mkw 0xa76ac9c580000001 0x0a76ac9c58000000 0x07f8f9ffc000000d 0xc07f8f9ffc000000

def z96 : W := mkw 0x0180090036801aa0 0x40180090036801aa 0x478019003fc03ffd 0x7478019003fc03ff

def z97 : W := mkw 0xbf7fdfed80000001 0x0bf7fdfed8000000 0xbf9ff83fc0000008 0x8bf9ff83fc000000

def z98 : W := mkw 0x5014000008090000 0x0501400000809000 0xb81800003c0e0008 0x1b81800003c0e000

def z99 : W := mkw 0x2f489d8500000000 0x02f489d850000000 0xbff8ffffc000000f 0xcbff8ffffc000000

def z100 : W := mkw 0x0080201277b63ee0 0x50080201277b63ee 0x400000003ffe3ff0 0x3400000003ffe3ff

def z101 : W := mkw 0x00a36270f7f0fbf8 0x400a36270f7f0fbf 0x4067e7f1fff1fff7 0xf4067e7f1fff1fff

def z102 : W := mkw 0x59151fff8c1b7701 0x259151fff8c1b770 0xf81f1ffffc3fff0e 0xff81f1ffffc3fff0

def z103 : W := mkw 0x0800140004001200 0x0080014000400120 0xf8001e003c003f0e 0x7f8001e003c003f0

def z104 : W := mkw 0x24c0000032800000 0x024c000003280000 0xffe000003fc0000f 0x3ffe000003fc0000

def z105 : W := mkw 0x5014000008090000 0x0501400000809000 0xf81f00003c3fc00e 0xbf81f00003c3fc00

def z106 : W := mkw 0xf476600019e98000 0x8f476600019e9800 0xf867e0001ff1c007 0xaf867e0001ff1c00

def z107 : W := mkw 0x923fc26d80000001 0x0923fc26d8000000 0x001fe03fc0000000 0x8001fe03fc000000

def z108 : W := mkw 0xf67ee00019ed8000 0x8f67ee00019ed800 0xf87fe0001cffc002 0x8f87fe0001cffc00

def z109 : W := mkw 0x0180090022000880 0x0018009002200088 0x0780190023003ccd 0x70780190023003cc

def z110 : W := mkw 0x00802000632408c0 0x100802000632408c 0x00000000030000c0 0x000000000030000c

def z111 : W := mkw 0xfefef4003fed9200 0x8fefef4003fed920 0xfffffe003fffff0f 0xffffffe003fffff0

def z112 : W := mkw 0x0208800700060400 0x1020880070006040 0x0018000e000e0000 0x00018000e000e000

def z113 : W := mkw 0x2c6376f0d5f0f378 0x42c6376f0d5f0f37 0xf867e7f1dff1e3f7 0xef867e7f1dff1e3f

def z114 : W := mkw 0xf7fee9073bef8c80 0x9f7fee9073bef8c8 0xfffff80e3fffdc0f 0xbfffff80e3fffdc0

def z115 : W := mkw 0x0389ab77e3366dd8 0x10389ab77e3366dd 0x0798ffffe33e3ffd 0xf0798ffffe33e3ff

def z116 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000100030020c5 0x600000100030020c

def z117 : W := mkw 0x0023426080000000 0x0002342608000000 0x006706c000000002 0x0006706c00000000

def z118 : W := mkw 0x0308890500000000 0x0030889050000000 0x0798180e00000008 0x00798180e0000000

def z119 : W := mkw 0xf6dc80003a8d0000 0x8f6dc80003a8d000 0xff9f00003c3fc00e 0xbff9f00003c3fc00

def z120 : W := mkw 0x7dd51fba3e9b7fa0 0x67dd51fba3e9b7fa 0xffff1ffe3fffffff 0xfffff1ffe3ffffff

def z121 : W := mkw 0xbf7fdfed94801221 0x4bf7fdfed9480122 0xffffffffdcc0033f 0xcffffffffdcc0033

def z122 : W := mkw 0xb7fee91763362cc0 0x1b7fee91763362cc 0xbffff93fe33e3ccf 0xfbffff93fe33e3cc

def z123 : W := mkw 0x2c40148014801220 0x42c4014801480122 0xb80000001c000000 0x0b80000001c00000

def z124 : W := mkw 0xd23ee000096d8000 0x8d23ee000096d800 0x001fe000003fc000 0x8001fe000003fc00

def z125 : W := mkw 0xf6ffe270fbfde158 0x8f6ffe270fbfde15 0xffffe7f1ffffe3ff 0xfffffe7f1ffffe3f

def z126 : W := mkw 0x5815163a0c1b7700 0x25815163a0c1b770 0xf8071e3e1c01ff02 0x4f8071e3e1c01ff0

def z127 : W := mkw 0x408020003bed8000 0x8408020003bed800 0x400000003fffc000 0x3400000003fffc00

def z128 : W := mkw 0xf6fee0003bed8000 0x8f6fee0003bed800 0xbf9fe0003c3fc008 0x9bf9fe0003c3fc00

def z129 : W := mkw 0x2dc01d8036801aa0 0x42dc01d8036801aa 0xffe018003fc01c0f 0x3ffe018003fc01c0

def z130 : W := mkw 0x5b9dbf3f6f3f7fc0 0x35b9dbf3f6f3f7fc 0xff9fff3fff3fffcf 0xfff9fff3fff3fffc

def z131 : W := mkw 0xfffefd803fed9aa0 0xcfffefd803fed9aa 0xffffffc03fffffff 0xfffffffc03ffffff

def z132 : W := mkw 0x18377678c170e158 0x018377678c170e15 0xf87fffffc3f1e3ff 0xef87fffffc3f1e3f

def z133 : W := mkw 0x5837767acd7bf758 0x25837767acd7bf75 0xf81ffe3ffc3fff0e 0xff81ffe3ffc3fff0

def z134 : W := mkw 0xfefff67afffff758 0xafefff67afffff75 0xffffffffffffffff 0xffffffffffffffff

def z135 : W := mkw 0x3d551fa800000000 0x03d551fa80000000 0xbfff1ffe0000000f 0xcbfff1ffe0000000

def z136 : W := mkw 0x2dc01d8036801aa0 0x42dc01d8036801aa 0xbf8018003c001c08 0x1bf8018003c001c0

def z137 : W := mkw 0xf6ffe26dbbed8001 0x8f6ffe26dbbed800 0xffffe03fffffc00f 0xbffffe03fffffc00

def z138 : W := mkw 0x5b9d9f3f2e1f7f80 0x35b9d9f3f2e1f7f8 0xff9f1e3e3c3fff0e 0xfff9f1e3e3c3fff0

def z139 : W := mkw 0x0388a90763260cc0 0x10388a90763260cc 0x0798f90fe30e1cc9 0x10798f90fe30e1cc

def z140 : W := mkw 0x1814140800000000 0x0181414080000000 0xb818180e00000008 0x0b818180e0000000

def z141 : W := mkw 0x0388890722060c80 0x10388890722060c8 0x0798f93fe00e1c0d 0xd0798f93fe00e1c0

def z142 : W := mkw 0x0388a91763362cc0 0x10388a91763362cc 0x0798e13fc33e00c1 0x80798e13fc33e00c

def z143 : W := mkw 0x4000000008090000 0x0400000000809000 0x400000003c3fc000 0x3400000003c3fc00

def z144 : W := mkw 0x09001d8004001aa0 0x409001d8004001aa 0xf8001fc03c003ffe 0x7f8001fc03c003ff

def z145 : W := mkw 0x0288a01263362cc0 0x10288a01263362cc 0x0798e000233e3ccd 0xb0798e000233e3cc

def z146 : W := mkw 0x00010270c0106158 0x000010270c010615 0x000007f1c00023f0 0x4000007f1c00023f

def z147 : W := mkw 0xf6dc80003a8d0000 0x8f6dc80003a8d000 0xbf9800003c0e0008 0x1bf9800003c0e000

def z148 : W := mkw 0x27c8a91773b62cc0 0x127c8a91773b62cc 0xfff8f93ffffe3ccf 0xffff8f93ffffe3cc

def z149 : W := mkw 0x2de35fe0b6801aa0 0x42de35fe0b6801aa 0xffe7fff1ffc03fff 0xfffe7fff1ffc03ff

def z150 : W := mkw 0x933fcb6d80000001 0x0933fcb6d8000000 0x079ff93fc000000d 0xc079ff93fc000000

def z151 : W := mkw 0x400000120c1b7700 0x2400000120c1b770 0x400000003c3fff00 0x3400000003c3fff0

def z152 : W := mkw 0x09011f3f44127fc0 0x309011f3f44127fc 0x00001f3fc0003fc0 0x400001f3fc0003fc

def z153 : W := mkw 0x0288a00023240000 0x00288a0002324000 0x0798e000233e000d 0xb0798e000233e000

def z154 : W := mkw 0x0000001040106158 0x0000000104010615 0x00000000000023f0 0x000000000000023f

def z155 : W := mkw 0x529ca0002b2d0000 0x0529ca0002b2d000 0xff9fe0003f3fc00f 0xbff9fe0003f3fc00

def z156 : W := mkw 0x080116e880000001 0x0080116e88000000 0x000006c000000000 0x0000006c00000000

def z157 : W := mkw 0x09011fed80000001 0x009011fed8000000 0x00001fffc0000000 0x400001fffc000000

def z158 : W := mkw 0x0388a9176376edd8 0x10388a9176376edd 0x4798f93fe3fffffd 0xf4798f93fe3fffff

def z159 : W := mkw 0xf454000018890000 0x8f45400001889000 0xb80000001c000000 0x0b80000001c00000

def z160 : W := mkw 0xbc7756e880000001 0x0bc7756e88000000 0xb867e7f1c0000007 0xcb867e7f1c000000

def z161 : W := mkw 0x5895363a6f3f7fc0 0x35895363a6f3f7fc 0xf81f1e3e3f3fffce 0xff81f1e3e3f3fffc

def z162 : W := mkw 0xfc7756e898c98001 0x8fc7756e898c9800 0xf86706c01cc1c002 0x0f86706c01cc1c00

def z163 : W := mkw 0x0180090022000880 0x0018009002200088 0x47e01fc023c03fff 0x747e01fc023c03ff

def z164 : W := mkw 0x0080201077f0fbf8 0x40080201077f0fbf 0x400000003ff1fff0 0x3400000003ff1fff

def z165 : W := mkw 0x0388a905632408c0 0x10388a905632408c 0x0780e101c30000c1 0x00780e101c30000c

def z166 : W := mkw 0x4388a9177bffacc0 0x94388a9177bffacc 0x4798f93ffffffccd 0xf4798f93ffffffcc

def z167 : W := mkw 0x000020104170e158 0x0000020104170e15 0x4000000003f1e3f0 0x24000000003f1e3f

def z168 : W := mkw 0x0023426080000000 0x0002342608000000 0x0067e7f1c0000007 0xc0067e7f1c000000

def z169 : W := mkw 0x0000000000000000 0x0000000000000000 0xf80000003c00000e 0x3f80000003c00000

def z170 : W := mkw 0x0080000032800000 0x0008000003280000 0x400000003fc00000 0x3400000003fc0000

def z171 : W := mkw 0x0288a01763362440 0x10288a0176336244 0x0798e03fe33e000d 0xb0798e03fe33e000

def z172 : W := mkw 0x5815162808090000 0x0581516280809000 0xf81f1e3e3c3fc00e 0xff81f1e3e3c3fc00

def z173 : W := mkw 0xf6fee0003bed8000 0x8f6fee0003bed800 0x07ffe00003ffc001 0x807ffe00003ffc00

def z174 : W := mkw 0x5015023008196100 0x0501502300819610 0xf81f06303c3fe30e 0xff81f06303c3fe30

def z175 : W := mkw 0xf67ec00008090000 0x0f67ec0000809000 0xffffe0003c3fc00f 0xbffffe0003c3fc00

def z176 : W := mkw 0xff7fdfff8c1b7701 0x2ff7fdfff8c1b770 0xfffffffffc3fff0f 0xffffffffffc3fff0

def z177 : W := mkw 0x000000000040c118 0x0000000000040c11 0x4000000000c1c330 0x04000000000c1c33

def z178 : W := mkw 0x09801d8026001aa0 0x409801d8026001aa 0x07801fc023003ffd 0x707801fc023003ff

def z179 : W := mkw 0x583756688c49d318 0x2583756688c49d31 0xf86706c01cc1c332 0x0f86706c01cc1c33

def z180 : W := mkw 0xf7fee9177bffacc0 0x9f7fee9177bffacc 0xfffff93ffffffccf 0xffffff93ffffffcc

def z181 : W := mkw 0x50140012081b2400 0x050140012081b240 0xf81f183e3c3ffc0e 0xff81f183e3c3ffc0

def z182 : W := mkw 0xbf7fdfff84127701 0x2bf7fdfff8412770 0xbfffffffc0003f0f 0xcbfffffffc0003f0

def z183 : W := mkw 0x008020126376edd8 0x1008020126376edd 0x4000000023fffff0 0x34000000023fffff

def z184 : W := mkw 0x5815363a4d7bf758 0x25815363a4d7bf75 0xf81f1e3e3ffffffe 0xff81f1e3e3ffffff

def z185 : W := mkw 0x5815167acc1b7758 0x25815167acc1b775 0xf81f1ffffc3ffffe 0xff81f1ffffc3ffff

def z186 : W := mkw 0x0000201241362440 0x1000020124136244 0x00000000003e0000 0x000000000003e000

def z187 : W := mkw 0x01000905400008c0 0x101000905400008c 0x00000101c00000c0 0x000000101c00000c

def z188 : W := mkw 0xf4f660003bed8000 0x8f4f660003bed800 0xf86700003fffc002 0x3f86700003fffc00

def z189 : W := mkw 0x0388a90023240880 0x00388a9002324088 0x0798f900233e3ccd 0xf0798f900233e3cc

def z190 : W := mkw 0x923fe27dc170e159 0x0923fe27dc170e15 0x001fe03fc031c000 0x8001fe03fc031c00

def z191 : W := mkw 0x5815163a0c1b7700 0x25815163a0c1b770 0xb81f183e3c3fdc08 0x9b81f183e3c3fdc0

def z192 : W := mkw 0x0022600001608000 0x0002260000160800 0x0060e00003c00001 0x00060e00003c0000

def z193 : W := mkw 0xa76bcbe580000001 0x0a76bcbe58000000 0x07e7e7f1c0000007 0xc07e7e7f1c000000

def z194 : W := mkw 0x0022600001608000 0x0002260000160800 0x4067e00003f1c007 0xa4067e00003f1c00

def z195 : W := mkw 0x408020127bffacc0 0x9408020127bffacc 0x400000003ffffcc0 0x3400000003ffffcc

def z196 : W := mkw 0x539dab3f6b3f6dc0 0x3539dab3f6b3f6dc 0x079ff93fe33ffccd 0xf079ff93fe33ffcc

def z197 : W := mkw 0xaf6addc580000001 0x0af6addc58000000 0xbfe0ffc1c000000f 0x4bfe0ffc1c000000

def z198 : W := mkw 0xfedc940a3e8f1600 0xafedc940a3e8f160 0xbf98180e3c0e1c08 0x1bf98180e3c0e1c0

def z199 : W := mkw 0x40a36270fbfde158 0x840a36270fbfde15 0x4067e7f1ffffe3f7 0xf4067e7f1ffffe3f

def z200 : W := mkw 0x0208a01741362440 0x10208a0174136244 0x0018e03fc03e0000 0x80018e03fc03e000

def z201 : W := mkw 0x2c40148014801220 0x42c4014801480122 0xf86006c01cc00332 0x0f86006c01cc0033

def z202 : W := mkw 0x0801162804005300 0x2080116280400530 0x0000060000000300 0x0000006000000030

def z203 : W := mkw 0x00236270c170e158 0x000236270c170e15 0x406706c003f1e3f2 0x2406706c003f1e3f

def z204 : W := mkw 0x923fc26d80000001 0x0923fc26d8000000 0x007fe7ffc0000007 0xc007fe7ffc000000

def z205 : W := mkw 0xbfffffede32408c1 0x1bfffffede32408c 0xbfffffffc30000cf 0xcbfffffffc30000c

def z206 : W := mkw 0x0001026d80000001 0x00001026d8000000 0x0000003fc0000000 0x00000003fc000000

def z207 : W := mkw 0x0b099fed80000001 0x00b099fed8000000 0x0798ffffc000000d 0xc0798ffffc000000

def z208 : W := mkw 0x00010270c0106158 0x000010270c010615 0x406007f1c3c023f7 0x6406007f1c3c023f

def z209 : W := mkw 0x0b89bf3f67367fc0 0x30b89bf3f67367fc 0x0798ff3fe33e3fcd 0xf0798ff3fe33e3fc

def z210 : W := mkw 0x0000001040102040 0x0000000104010204 0x00000131c00020c0 0x400000131c00020c

def z211 : W := mkw 0xf477426098c9c118 0x8f477426098c9c11 0xf86706c01cc1c332 0x0f86706c01cc1c33

def z212 : W := mkw 0x09001d9744123ee0 0x509001d9744123ee 0x00001fffc0003ff0 0x400001fffc0003ff

def z213 : W := mkw 0x0000200001200000 0x0000020000120000 0x0000e00003300005 0xa0000e0000330000

def z214 : W := mkw 0x1815162800000000 0x0181516280000000 0xb807060000000002 0x0b80706000000000

def z215 : W := mkw 0xff7fdfed98c98001 0x8ff7fdfed98c9800 0xffffffffdcc1c00f 0xcffffffffdcc1c00

def z216 : W := mkw 0x0180091762122cc0 0x10180091762122cc 0x0780193fe3003ccd 0x70780193fe3003cc

def z217 : W := mkw 0x0180291763362cc0 0x10180291763362cc 0x0000193fe33e3cc0 0x70000193fe33e3cc

def z218 : W := mkw 0xb77fcbed80000001 0x0b77fcbed8000000 0x07ffe1ffc0000001 0x807ffe1ffc000000

def z219 : W := mkw 0xbfdc9d8d36801aa1 0x4bfdc9d8d36801aa 0xbf98180e3c001c08 0x1bf98180e3c001c0

def z220 : W := mkw 0xbf5c9d8d00000001 0x0bf5c9d8d0000000 0xbf98f93fc000000d 0xcbf98f93fc000000

def z221 : W := mkw 0x0388891762162cc0 0x10388891762162cc 0x0798193fe00e3cc8 0x50798193fe00e3cc

def z222 : W := mkw 0x581516280c095300 0x2581516280c09530 0xf8071e003c01ff0e 0x7f8071e003c01ff0

def z223 : W := mkw 0x1b9dbf3f63362cc0 0x11b9dbf3f63362cc 0xbf9fff3fe33e3ccf 0xfbf9fff3fe33e3cc

def z224 : W := mkw 0x4000000018c98000 0x84000000018c9800 0x400000001cc1c000 0x0400000001cc1c00

def z225 : W := mkw 0x5015023a081b6500 0x25015023a081b650 0x001f003e003fc000 0x8001f003e003fc00

def z226 : W := mkw 0x74d400003a890000 0x074d400003a89000 0xffff00003fffc00f 0xbffff00003fffc00

def z227 : W := mkw 0x000020104170e158 0x0000020104170e15 0x406007c003f1e3f7 0x6406007c003f1e3f

def z228 : W := mkw 0x00236270c170e158 0x000236270c170e15 0x0007e131c331e0c5 0xe0007e131c331e0c

def z229 : W := mkw 0x0208800000000000 0x0020880000000000 0x0798e0000000000d 0x80798e0000000000

def z230 : W := mkw 0x2540098000000000 0x0254009800000000 0x07e001c000000001 0x007e001c00000000

def z231 : W := mkw 0x0308891700122400 0x0030889170012240 0x0798f93fe03e3c0d 0xf0798f93fe03e3c0

def z232 : W := mkw 0xbf7fdfed80000001 0x0bf7fdfed8000000 0xbfe7e7c1c0000003 0x0bfe7e7c1c000000

def z233 : W := mkw 0x032beb75c170e158 0x0032beb75c170e15 0x47ffffffc3f1e3ff 0xe47ffffffc3f1e3f

def z234 : W := mkw 0x09801d8036801aa0 0x409801d8036801aa 0x40001fc03fc03ff0 0x740001fc03fc03ff

def z235 : W := mkw 0x0388a90523240000 0x00388a9052324000 0x0798f93fe33e000d 0xf0798f93fe33e000

def z236 : W := mkw 0x0000201041302040 0x0000020104130204 0x0000e131c33020c5 0xe0000e131c33020c

def z237 : W := mkw 0x5814141a0c1b7700 0x25814141a0c1b770 0xf818180e3c3fff08 0x3f818180e3c3fff0

def z238 : W := mkw 0x2c40148014801220 0x42c4014801480122 0xf8601ec03cc03f3e 0x7f8601ec03cc03f3

def z239 : W := mkw 0xfefff6e8bbed8001 0x8fefff6e8bbed800 0xffffe6c03fffc00f 0xbffffe6c03fffc00

def z240 : W := mkw 0xbffedd8036801aa0 0x4bffedd8036801aa 0xffffffc03fc03fff 0xfffffffc03fc03ff

def z241 : W := mkw 0x9037426880000001 0x0903742688000000 0x0007000000000000 0x0000700000000000

def z242 : W := mkw 0x0000201041302040 0x0000020104130204 0x00000000033020c0 0x200000000033020c

def z243 : W := mkw 0x5815163a0c1b7700 0x25815163a0c1b770 0xf80706003c3fff02 0x3f80706003c3fff0

def z244 : W := mkw 0x2d401d8000000000 0x02d401d800000000 0xbfe01fc00000000f 0x4bfe01fc00000000

def z245 : W := mkw 0x923fe27fc1362441 0x1923fe27fc136244 0x001fe03fc03e0000 0x8001fe03fc03e000

def z246 : W := mkw 0x000122304170e158 0x0000122304170e15 0x4007063003f1e3f6 0xe4007063003f1e3f

def z247 : W := mkw 0x002260104170e158 0x0002260104170e15 0x4067e00003f1e3f7 0xa4067e00003f1e3f

def z248 : W := mkw 0x0801163a04127700 0x20801163a0412770 0x40071e3e0031ff06 0xe40071e3e0031ff0

def z249 : W := mkw 0x00226050c170a058 0x000226050c170a05 0x0060e1f1c3f020f5 0xe0060e1f1c3f020f

def z250 : W := mkw 0x002342608040c118 0x0002342608040c11 0x4067e7f1c0c1c337 0xc4067e7f1c0c1c33

def z251 : W := mkw 0x03abeb77e3362cc0 0x103abeb77e3362cc 0x07ffffffe33e3ccf 0xf07ffffffe33e3cc

def z252 : W := mkw 0x24c0000036801aa0 0x424c0000036801aa 0xffe000003fc03fff 0x3ffe000003fc03ff

def z253 : W := mkw 0xf6ffe270fbfde158 0x8f6ffe270fbfde15 0xffffe031ffffc00f 0xbffffe031ffffc00

def z254 : W := mkw 0x002342608040c118 0x0002342608040c11 0x406707c003c1e3f7 0x6406707c003c1e3f

def z255 : W := mkw 0xff7fffed896d8001 0x8ff7fffed896d800 0xbfffffffc03fc00f 0xcbfffffffc03fc00

def z256 : W := mkw 0x00236270c170e158 0x000236270c170e15 0x0007e031c031c000 0x80007e031c031c00

def z257 : W := mkw 0x0208800500000000 0x0020880050000000 0x0018e03fc0000000 0x80018e03fc000000

def z258 : W := mkw 0x0388a91763362cc0 0x10388a91763362cc 0x0780f93fc3003cc1 0x40780f93fc3003cc

def z259 : W := mkw 0x0001026080004118 0x0000102608000411 0x000006c000000330 0x0000006c00000033

def z260 : W := mkw 0x7dd51fba3e9b7fa0 0x67dd51fba3e9b7fa 0xff9f1e3e3c3fff0e 0xfff9f1e3e3c3fff0

def z261 : W := mkw 0x59151fba0c1b7fa0 0x659151fba0c1b7fa 0xf81f1ffe3c3ffffe 0xff81f1ffe3c3ffff

def z262 : W := mkw 0xafeaddc5b6801aa1 0x4afeaddc5b6801aa 0xffe0ffc1ffc03fff 0x7ffe0ffc1ffc03ff

def z263 : W := mkw 0x002342608040c118 0x0002342608040c11 0x406706c000c1c332 0x0406706c000c1c33

def z264 : W := mkw 0x1b1d9f2d00000000 0x01b1d9f2d0000000 0xbf9fff3fc000000f 0xcbf9fff3fc000000

def z265 : W := mkw 0xff7fdfff881b6501 0x2ff7fdfff881b650 0xbfffffffc03fc00f 0xcbfffffffc03fc00

def z266 : W := mkw 0xbe7fd62800000000 0x0be7fd6280000000 0xbffffe3e0000000f 0xcbffffe3e0000000

def z267 : W := mkw 0x0208a00541240040 0x10208a0054124004 0x0000e001c0000000 0x00000e001c000000

def z268 : W := mkw 0xd23fe23a097fe500 0xad23fe23a097fe50 0x001fe03e003fc000 0x8001fe03e003fc00

def z269 : W := mkw 0x022be277c176e558 0x1022be277c176e55 0x001fe03fc03fc000 0x8001fe03fc03fc00

def z270 : W := mkw 0x0800140004001200 0x0080014000400120 0x00001e0000003f00 0x400001e0000003f0

def z271 : W := mkw 0x00236270c170e158 0x000236270c170e15 0x0067e7f1c031c007 0xc0067e7f1c031c00

def z272 : W := mkw 0x5815162a0c0b1600 0x25815162a0c0b160 0xb81f1e3e3c0e1c0e 0xdb81f1e3e3c0e1c0

def z273 : W := mkw 0x0000000014801220 0x4000000001480122 0x400000001cc00330 0x0400000001cc0033

def z274 : W := mkw 0x2fc8bd9763362cc0 0x12fc8bd9763362cc 0xbff8ffffe33e3ccf 0xfbff8ffffe33e3cc

def z275 : W := mkw 0xd23fe270c97de158 0x8d23fe270c97de15 0x407fe7f1c3ffe3f7 0xe407fe7f1c3ffe3f

def z276 : W := mkw 0xfc7756e88c095301 0x2fc7756e88c09530 0xf86706c01c01c302 0x0f86706c01c01c30

def z277 : W := mkw 0x0388a91763362cc0 0x10388a91763362cc 0x0780e101e33e3cc1 0x30780e101e33e3cc

def z278 : W := mkw 0x00226040c1608058 0x000226040c160805 0x4067e1c1c3f1c0f7 0xa4067e1c1c3f1c0f

def z279 : W := mkw 0x5815163a0c1b7700 0x25815163a0c1b770 0xf87f1ffe3fffffff 0xff87f1ffe3ffffff

def z280 : W := mkw 0xbf7fdfed80000001 0x0bf7fdfed8000000 0xffffffffc3c023ff 0xeffffffffc3c023f

def z281 : W := mkw 0xbc7756e88040c119 0x0bc7756e88040c11 0xf86706c000c1c332 0x0f86706c000c1c33

def z282 : W := mkw 0x03aae9176376acc0 0x103aae9176376acc 0x47fff93fe3fffccf 0xf47fff93fe3fffcc

def z283 : W := mkw 0x0801163a04127700 0x20801163a0412770 0x00181e3e203e3f0c 0xf00181e3e203e3f0

def z284 : W := mkw 0x2440000000000000 0x0244000000000000 0xbfe000000000000f 0x0bfe000000000000

def z285 : W := mkw 0x00234270c0106158 0x000234270c010615 0x0067e7f1c00023f7 0xc0067e7f1c00023f

def z286 : W := mkw 0x5bbfff7fef7fffd8 0x35bbfff7fef7fffd 0xffffffffffffffff 0xffffffffffffffff

def z287 : W := mkw 0x408000123e9b7fa0 0x6408000123e9b7fa 0x400000003ffffff0 0x3400000003ffffff

def z288 : W := mkw 0x0000201241322440 0x0000020124132244 0x0018f93fe33e3ccd 0xf0018f93fe33e3cc

def z289 : W := mkw 0x0308a91741362440 0x10308a9174136244 0x0798f93fc03e000d 0xc0798f93fc03e000

def z290 : W := mkw 0xf6fee0123ffff700 0xaf6fee0123ffff70 0xffffe0003fffff0f 0xbffffe0003fffff0

def z291 : W := mkw 0x2c40148014801220 0x42c4014801480122 0xf86007c01fc023f7 0x6f86007c01fc023f

def z292 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z293 : W := mkw 0xfdf65d803ec99aa0 0xcfdf65d803ec99aa 0xffe71fc03fc1ffff 0x7ffe71fc03fc1fff

def z294 : W := mkw 0x2dc01d8036801aa0 0x42dc01d8036801aa 0xff8018003fc03ff8 0x3ff8018003fc03ff

def z295 : W := mkw 0x1815163a00122400 0x01815163a0012240 0xb81f1e3e203e3c0e 0xfb81f1e3e203e3c0

def z296 : W := mkw 0x5a1db63f4d3f7740 0x35a1db63f4d3f774 0xf81ffe3ffc3fff0e 0xff81ffe3ffc3fff0

def z297 : W := mkw 0x0100090500000000 0x0010009050000000 0x0000193fc0000000 0x40000193fc000000

def z298 : W := mkw 0x0001023000106100 0x0000102300010610 0x406707f003f1e3f7 0xe406707f003f1e3f

def z299 : W := mkw 0x400000120c1b7700 0x2400000120c1b770 0x4018183e3c3fff0c 0xf4018183e3c3fff0

def z300 : W := mkw 0x400020124d7bf758 0x2400020124d7bf75 0x400000003ffffff0 0x3400000003ffffff

def z301 : W := mkw 0x2dc01d8036801aa0 0x42dc01d8036801aa 0xff801e003c003f0e 0x7ff801e003c003f0

def z302 : W := mkw 0x09011fed84001aa1 0x409011fed84001aa 0x00001fffc0003ff0 0x400001fffc0003ff

def z303 : W := mkw 0xf7fee9c5bbed8001 0x8f7fee9c5bbed800 0xffffe1c1ffffc00f 0xbffffe1c1ffffc00

def z304 : W := mkw 0x1815162800000000 0x0181516280000000 0xb81f1e3e0000000e 0xcb81f1e3e0000000

def z305 : W := mkw 0x0023427080106100 0x0002342708010610 0x4067e7f1c031e307 0xe4067e7f1c031e30

def z306 : W := mkw 0xa748898500000001 0x0a74889850000000 0x0780000000000000 0x0078000000000000

def z307 : W := mkw 0xa6c8800032840000 0x8a6c880003284000 0x0780000000000000 0x0078000000000000

def z308 : W := mkw 0x400102320c1b7700 0x2400102320c1b770 0x400706303c3fff06 0xf400706303c3fff0

def z309 : W := mkw 0x0080000022000880 0x0008000002200088 0x0000000023003cc0 0x30000000023003cc

def z310 : W := mkw 0x08237670c570f358 0x008237670c570f35 0xf867fff1fff1ffff 0xff867fff1fff1fff

def z311 : W := mkw 0x01000980000008a0 0x401000980000008a 0x000001c0000000f0 0x0000001c0000000f

def z312 : W := mkw 0x0000000004001aa0 0x40000000004001aa 0x0000000000003ff0 0x00000000000003ff

def z313 : W := mkw 0x2d401d8004001200 0x02d401d800400120 0xffe01fc03c003f0f 0x7ffe01fc03c003f0

def z314 : W := mkw 0xf6fec0003acd8000 0x8f6fec0003acd800 0xffff00003ccfc00a 0x1ffff00003ccfc00

def z315 : W := mkw 0x40a260003bed8000 0x840a260003bed800 0x4067e0003fffc007 0xb4067e0003fffc00

def z316 : W := mkw 0xf4f640003ac98000 0x8f4f640003ac9800 0xffe700003fc1c00f 0x3ffe700003fc1c00

def z317 : W := mkw 0x0000001200122400 0x0000000120012240 0x00000000203e3c00 0x300000000203e3c0

def z318 : W := mkw 0x2dc03d9077b03ae0 0x42dc03d9077b03ae 0xffe0fff1fff03fff 0xfffe0fff1fff03ff

def z319 : W := mkw 0x00a36272e376edd8 0x100a36272e376edd 0x4067e7f1e3fffff7 0xf4067e7f1e3fffff

def z320 : W := mkw 0x2dc01d80328008a0 0x42dc01d80328008a 0xbfe01fc003c000ff 0x4bfe01fc003c000f

def z321 : W := mkw 0x0800140004001200 0x0080014000400120 0xb80018003c001c08 0x1b80018003c001c0

def z322 : W := mkw 0xbc7756e894801221 0x4bc7756e89480122 0xf86706c01cc00332 0x0f86706c01cc0033

def z323 : W := mkw 0x01a36b70e370e9d8 0x001a36b70e370e9d 0x47e7fff1e3f1ffff 0xf47e7fff1e3f1fff

def z324 : W := mkw 0x7c5516ba1c9b7720 0x67c5516ba1c9b772 0xf87f1efe3cffff3e 0xff87f1efe3cffff3

def z325 : W := mkw 0x0080000222060c80 0x10080000222060c8 0x00000000200e1c00 0x100000000200e1c0

def z326 : W := mkw 0x2de27d8037e09aa0 0x42de27d8037e09aa 0xffe7ffc03ff1ffff 0xfffe7ffc03ff1fff

def z327 : W := mkw 0xf6fee0123bffa400 0x8f6fee0123bffa40 0xfffff83e3ffffc0f 0xffffff83e3ffffc0

def z328 : W := mkw 0x2d637ff0c170e158 0x02d637ff0c170e15 0xffe7fff1c3f1e3ff 0xeffe7fff1c3f1e3f

def z329 : W := mkw 0xf6ffe2303bfde100 0x8f6ffe2303bfde10 0xffffe6303fffe30f 0xfffffe6303fffe30

def z330 : W := mkw 0x2440000010800000 0x0244000001080000 0xf86000001cc00002 0x0f86000001cc0000

def z331 : W := mkw 0xfffffffffbffacc1 0x9fffffffffbffacc 0xfffffffffffffccf 0xffffffffffffffcc

def z332 : W := mkw 0x24e2600033e08000 0x024e2600033e0800 0xffe7e0003ff1c00f 0xbffe7e0003ff1c00

def z333 : W := mkw 0x59951f3a2e1b7f80 0x259951f3a2e1b7f8 0xff9f1f3e3f3fffcf 0xfff9f1f3e3f3fffc

def z334 : W := mkw 0x0180091222122c80 0x00180091222122c8 0x0798193e233e3ccd 0xf0798193e233e3cc

def z335 : W := mkw 0x2d401d8000000000 0x02d401d800000000 0xbf80180000000008 0x0bf8018000000000

def z336 : W := mkw 0xbfdc9d8f22060c81 0x1bfdc9d8f22060c8 0xbf98180e200e1c08 0x1bf98180e200e1c0

def z337 : W := mkw 0x93bfeb7fe3362cc1 0x193bfeb7fe3362cc 0x079ff93fe33e3ccd 0xf079ff93fe33e3cc

def z338 : W := mkw 0x2dc01d8036801aa0 0x42dc01d8036801aa 0xffe01ec03cc01f3a 0x1ffe01ec03cc01f3

def z339 : W := mkw 0xb67fc26080000000 0x0b67fc2608000000 0xbfffe7f1c000000f 0xcbfffe7f1c000000

def z340 : W := mkw 0x002342708050e118 0x0002342708050e11 0x406706f000f1e336 0xe406706f000f1e33

def z341 : W := mkw 0x9a3fd66d80000001 0x09a3fd66d8000000 0xb81ffe3fc000000e 0xcb81ffe3fc000000

def z342 : W := mkw 0xb6fec00032800000 0x0b6fec0003280000 0xffffe0003fc0000f 0xbffffe0003fc0000

def z343 : W := mkw 0x0180291263362cc0 0x10180291263362cc 0x07801900233e3ccd 0x707801900233e3cc

def z344 : W := mkw 0xbd775fe880000001 0x0bd775fe88000000 0xbfe71fc00000000f 0x4bfe71fc00000000

def z345 : W := mkw 0xa7eac9c5b28008a1 0x4a7eac9c5b28008a 0x07e0e1c1c3c000f1 0x007e0e1c1c3c000f

def z346 : W := mkw 0x521da23f493f6540 0x3521da23f493f654 0x001fe03fc03fc000 0x8001fe03fc03fc00

def z347 : W := mkw 0x64c020003bed8000 0x864c020003bed800 0xffe000003fffc00f 0x3ffe000003fffc00

def z348 : W := mkw 0x2dc01d9236923ea0 0x42dc01d9236923ea 0xfff81ffe3ffe3fff 0xffff81ffe3ffe3ff

def z349 : W := mkw 0xd2bee0003bed8000 0x8d2bee0003bed800 0x401fe0003fffc000 0xb401fe0003fffc00

def z350 : W := mkw 0x0308890500000000 0x0030889050000000 0x0780e101c0000001 0x00780e101c000000

def z351 : W := mkw 0x9b3fdfed80000001 0x09b3fdfed8000000 0x001fffffc0000000 0xc001fffffc000000

def z352 : W := mkw 0x0388890522040880 0x1038889052204088 0x0780000000000000 0x0078000000000000

def z353 : W := mkw 0x5b1d9f3f0c1b7700 0x25b1d9f3f0c1b770 0xff9fff3ffc3fff0f 0xfff9fff3ffc3fff0

def z354 : W := mkw 0x24c0000032800000 0x024c000003280000 0x07e0000003c00001 0x007e0000003c0000

def z355 : W := mkw 0xbf7fdfed84001aa1 0x4bf7fdfed84001aa 0xbfffffffc0003fff 0xcbfffffffc0003ff

def z356 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000e131c0000005 0xc0000e131c000000

def z357 : W := mkw 0x0080000036801aa0 0x40080000036801aa 0x000000003c001c00 0x1000000003c001c0

def z358 : W := mkw 0x2fc89d8736861ea0 0x52fc89d8736861ea 0xfff81fce3fce3fff 0x7fff81fce3fce3ff

def z359 : W := mkw 0xff7fdfed8c095301 0x2ff7fdfed8c09530 0xffffffffdc01c30f 0xcffffffffdc01c30

def z360 : W := mkw 0xf7fee9803bed88a0 0xcf7fee9803bed88a 0xffffe1c03fffc0ff 0xbffffe1c03fffc0f

def z361 : W := mkw 0x0388a91763362cc0 0x10388a91763362cc 0x47f8ffffe3fe3fff 0xf47f8ffffe3fe3ff

def z362 : W := mkw 0x09011fba04127fa0 0x609011fba04127fa 0x00001ffe00003ff0 0x400001ffe00003ff

def z363 : W := mkw 0x25c00980328008a0 0x425c00980328008a 0x47e007c003c023f7 0x647e007c003c023f

def z364 : W := mkw 0x1815163800106100 0x0181516380010610 0xf81f1e3e0031e30e 0xef81f1e3e0031e30

def z365 : W := mkw 0x2d401d8014801220 0x42d401d801480122 0xffe01fc01cc0033f 0x4ffe01fc01cc0033

def z366 : W := mkw 0x0208a00001240000 0x00208a0000124000 0x0018e000003e0000 0x80018e000003e000

def z367 : W := mkw 0x5895363a3ffff700 0xa5895363a3ffff70 0xf81f1e3e3fffff0e 0xff81f1e3e3fffff0

def z368 : W := mkw 0x0001023200126500 0x0000102320012650 0x401f1e3e203fff0e 0xf401f1e3e203fff0

def z369 : W := mkw 0x0000200041200040 0x0000020004120004 0x0000e101c30000c1 0x00000e101c30000c

def z370 : W := mkw 0x50376270c979e158 0x050376270c979e15 0xf87fe7f1ffffe3ff 0xff87fe7f1ffffe3f

def z371 : W := mkw 0x5015023a081b6500 0x25015023a081b650 0x401f063e003fe306 0xe401f063e003fe30

def z372 : W := mkw 0xfe7fd63a0c1b7700 0x2fe7fd63a0c1b770 0xfffffe3e3c3fff0f 0xffffffe3e3c3fff0

def z373 : W := mkw 0x2dc01d8036801aa0 0x42dc01d8036801aa 0xffe007c01fc003f3 0x0ffe007c01fc003f

def z374 : W := mkw 0x7df77ffafffbfff8 0x67df77ffafffbfff 0xffffffffffffffff 0xffffffffffffffff

def z375 : W := mkw 0xbffffffdf7f0fbf9 0x4bffffffdf7f0fbf 0xfffffffffff1ffff 0xffffffffffff1fff

def z376 : W := mkw 0x0288a01223362400 0x00288a0122336240 0x0798f83e233e3c0d 0xf0798f83e233e3c0

def z377 : W := mkw 0x5814141a0c1b3600 0x25814141a0c1b360 0xb818183e3c3e3c0c 0xfb818183e3c3e3c0

def z378 : W := mkw 0x0080200023240000 0x0008020002324000 0x00000000233e0000 0x300000000233e000

def z379 : W := mkw 0x02abe270e374e158 0x002abe270e374e15 0x47ffe7f1e3ffe3ff 0xf47ffe7f1e3ffe3f

def z380 : W := mkw 0xfffffffdfbfde159 0x8fffffffdfbfde15 0xffffffffffffe3ff 0xfffffffffffffe3f

def z381 : W := mkw 0xff5d9fbf0c1b7701 0x2ff5d9fbf0c1b770 0xff9f1e3e3c3fff0e 0xfff9f1e3e3c3fff0

def z382 : W := mkw 0xb77ec90500000000 0x0b77ec9050000000 0xbffff93fc000000f 0xcbffff93fc000000

def z383 : W := mkw 0xff7fdfed88090001 0x0ff7fdfed8809000 0xfffffffffc3fc00f 0xffffffffffc3fc00

def z384 : W := mkw 0xbdf75fe8b6801aa1 0x4bdf75fe8b6801aa 0xffe71fc03fc03fff 0x7ffe71fc03fc03ff

def z385 : W := mkw 0x5015023a081b6500 0x25015023a081b650 0xf81f003e3c3fc00e 0xbf81f003e3c3fc00

def z386 : W := mkw 0xb6fee00033e48000 0x8b6fee00033e4800 0xbfffe00003c0000f 0x8bfffe00003c0000

def z387 : W := mkw 0xbe7fd6ed80000001 0x0be7fd6ed8000000 0xb87fe6ffc0000002 0x8b87fe6ffc000000

def z388 : W := mkw 0x0800148004001220 0x4080014800400122 0x000006c000000330 0x0000006c00000033

def z389 : W := mkw 0xfffefd803fed9aa0 0xcfffefd803fed9aa 0xfffff8003fffdc0f 0xbfffff8003fffdc0

def z390 : W := mkw 0xbf5d9fed80000001 0x0bf5d9fed8000000 0xbf981fffc0000008 0x4bf981fffc000000

def z391 : W := mkw 0xbfffffedb3e48001 0x8bfffffedb3e4800 0xbfffffffc3c0000f 0xcbfffffffc3c0000

def z392 : W := mkw 0x1837566880000000 0x0183756688000000 0xb87fffffc000000f 0xcb87fffffc000000

def z393 : W := mkw 0x0b88bd9767363ee0 0x50b88bd9767363ee 0x0798ffffe33e3ffd 0xf0798ffffe33e3ff

def z394 : W := mkw 0xb67fc26d80000001 0x0b67fc26d8000000 0xbfffe03fc000000f 0x8bfffe03fc000000

def z395 : W := mkw 0x010009c580000001 0x0010009c58000000 0x000001c1c0000000 0x0000001c1c000000

def z396 : W := mkw 0x0100090000000880 0x0010009000000088 0x0000190000003cc0 0x40000190000003cc

def z397 : W := mkw 0xda3ff63a0d7ff700 0xada3ff63a0d7ff70 0xf81ffe3e3c3fff0e 0xff81ffe3e3c3fff0

def z398 : W := mkw 0x25c00980328008a0 0x425c00980328008a 0xffe001c03fc000ff 0x3ffe001c03fc000f

def z399 : W := mkw 0xbf5c9d8d00000001 0x0bf5c9d8d0000000 0xbff81fce0000000f 0x4bff81fce0000000

def z400 : W := mkw 0x0000200041608058 0x0000020004160805 0x0000000003c000f0 0x00000000003c000f

def z401 : W := mkw 0x400000020c0b1600 0x2400000020c0b160 0x000000003c0e1c00 0x1000000003c0e1c0

def z402 : W := mkw 0xbe7fd6e880000001 0x0be7fd6e88000000 0xbfffe6c00000000f 0x8bfffe6c00000000

def z403 : W := mkw 0xbfffdfedb6801aa1 0x4bfffdfedb6801aa 0xbffffffffc001c0f 0xdbffffffffc001c0

def z404 : W := mkw 0x03aae957e376acd8 0x103aae957e376acd 0x07f8f9ffe3fe3cfd 0xf07f8f9ffe3fe3cf

def z405 : W := mkw 0xbf7fffedc1608059 0x0bf7fffedc160805 0xbfffffffc3c000ff 0xcbfffffffc3c000f

def z406 : W := mkw 0x0000001240122cc0 0x10000001240122cc 0x0000000000003cc0 0x00000000000003cc

def z407 : W := mkw 0x2dc11fedb6801aa1 0x42dc11fedb6801aa 0xffe01fffffc03fff 0x7ffe01fffffc03ff

def z408 : W := mkw 0x01010b77c0126dd8 0x101010b77c0126dd 0x00001fffc0003ff0 0x400001fffc0003ff

def z409 : W := mkw 0x00226040c1608058 0x000226040c160805 0x0000e001c0000000 0x00000e001c000000

def z410 : W := mkw 0xbf7fdffd80106101 0x0bf7fdffd8010610 0xffffffffc031e30f 0xeffffffffc031e30

def z411 : W := mkw 0x5815163a0c1b7700 0x25815163a0c1b770 0xb8181e3e3c0e3f08 0x5b8181e3e3c0e3f0

def z412 : W := mkw 0x2dc01d8022000880 0x02dc01d802200088 0xbfe01fc023003ccf 0x7bfe01fc023003cc

def z413 : W := mkw 0xbf7eddcd80000001 0x0bf7eddcd8000000 0xbff8f9cfc0000009 0x0bff8f9cfc000000

def z414 : W := mkw 0xffffffffbffff701 0xaffffffffbffff70 0xffffffffffffff0f 0xfffffffffffffff0

def z415 : W := mkw 0x509420003bed8000 0x8509420003bed800 0xf81f00003fffc00e 0xbf81f00003fffc00

def z416 : W := mkw 0xf7ffeb77fbffedd8 0x9f7ffeb77fbffedd 0xffffffffffffffff 0xffffffffffffffff

def z417 : W := mkw 0x5015023a081b6500 0x25015023a081b650 0x001f183e203ffc0c 0xf001f183e203ffc0

def z418 : W := mkw 0x408020003fed9aa0 0xc408020003fed9aa 0x400000003ffffff0 0x3400000003ffffff

def z419 : W := mkw 0x0000200001608000 0x0000020000160800 0x4000000003f1c000 0x24000000003f1c00

def z420 : W := mkw 0xd23fe270c97de158 0x8d23fe270c97de15 0x001fe031c03fc000 0x8001fe031c03fc00

def z421 : W := mkw 0xa76ae9c5c1608059 0x0a76ae9c5c160805 0x07e0e1c1c3c000f1 0x007e0e1c1c3c000f

def z422 : W := mkw 0xa6eae040f3e48058 0x8a6eae040f3e4805 0x07e0e1c1c3c000f1 0x007e0e1c1c3c000f

def z423 : W := mkw 0x09001d8000000000 0x009001d800000000 0x00001fc000000000 0x400001fc00000000

def z424 : W := mkw 0x2cc0140036801200 0x02cc014003680120 0xffe01e003fc03f0f 0x7ffe01e003fc03f0

def z425 : W := mkw 0x0001023000106100 0x0000102300010610 0x0000063000002300 0x4000006300000230

def z426 : W := mkw 0x3dd51fa836801aa0 0x43dd51fa836801aa 0xffff1ffe3fc03fff 0xfffff1ffe3fc03ff

def z427 : W := mkw 0xf6dca0003bad0000 0x8f6dca0003bad000 0xbf98e0003f3e000d 0xbbf98e0003f3e000

def z428 : W := mkw 0xbc54148800000001 0x0bc5414880000000 0xb800000000000000 0x0b80000000000000

def z429 : W := mkw 0x0000000000000000 0x0000000000000000 0x4000000003c023f0 0x24000000003c023f

def z430 : W := mkw 0x5b9cbd1f6f3f3ec0 0x35b9cbd1f6f3f3ec 0xbf98f93fff3e3ccd 0xfbf98f93fff3e3cc

def z431 : W := mkw 0x7c5516a81c895320 0x67c5516a81c89532 0xf86706c01cc1c332 0x0f86706c01cc1c33

def z432 : W := mkw 0x4801163a0c1b7700 0x24801163a0c1b770 0x40001e3e3c3fff00 0x740001e3e3c3fff0

def z433 : W := mkw 0xffffdfedba8d0001 0x8ffffdfedba8d000 0xbffffffffc0e000f 0xdbffffffffc0e000

def z434 : W := mkw 0x0000001200122400 0x0000000120012240 0x0000183e00003c00 0x40000183e00003c0

def z435 : W := mkw 0xa46240c080000001 0x0a46240c08000000 0x006000c000000000 0x0006000c00000000

def z436 : W := mkw 0x0080201263362cc0 0x10080201263362cc 0x0000e131e33e3cc5 0xf0000e131e33e3cc

def z437 : W := mkw 0xa6eae00033e48000 0x8a6eae00033e4800 0x07f8e00023fe000d 0xb07f8e00023fe000

def z438 : W := mkw 0x09237ff0c570fbf8 0x409237ff0c570fbf 0x4067fff1c3f1fff7 0xe4067fff1c3f1fff

def z439 : W := mkw 0xf6fee0003fed9aa0 0xcf6fee0003fed9aa 0xffffe0003fffffff 0xbffffe0003ffffff

def z440 : W := mkw 0x0880140036801aa0 0x40880140036801aa 0xf8001e003fc03ffe 0x7f8001e003fc03ff

def z441 : W := mkw 0xffdc9d8d3a8d0001 0x8ffdc9d8d3a8d000 0xbf98180e3c0e0008 0x1bf98180e3c0e000

def z442 : W := mkw 0x01802910633028c0 0x001802910633028c 0x0780f931e3303ccd 0xf0780f931e3303cc

def z443 : W := mkw 0xd23fe26d896d8001 0x8d23fe26d896d800 0x001fe03fc03fc000 0x8001fe03fc03fc00

def z444 : W := mkw 0x09001d8004001aa0 0x409001d8004001aa 0x0000180000001c00 0x00000180000001c0

def z445 : W := mkw 0x0800140004001200 0x0080014000400120 0xf8601fc03fc03fff 0x7f8601fc03fc03ff

def z446 : W := mkw 0x002260104170a040 0x0002260104170a04 0x4067e131c3f1e0c7 0xe4067e131c3f1e0c

def z447 : W := mkw 0xa6eae00033e48000 0x8a6eae00033e4800 0xffe0e0003fc0000f 0x3ffe0e0003fc0000

def z448 : W := mkw 0xbf7ffffdc170e159 0x0bf7ffffdc170e15 0xbfffffffc031c00f 0xcbfffffffc031c00

def z449 : W := mkw 0x0000201041302040 0x0000020104130204 0x0000e031c0300000 0x80000e031c030000

def z450 : W := mkw 0x5814140a0c0b1600 0x25814140a0c0b160 0xf8181e0e3c0e3f0e 0x7f8181e0e3c0e3f0

def z451 : W := mkw 0x1014000000000000 0x0101400000000000 0xb81f00000000000e 0x8b81f00000000000

def z452 : W := mkw 0x1815163a04127700 0x21815163a0412770 0xb81f1e3e00003f0e 0xcb81f1e3e00003f0

def z453 : W := mkw 0xffffffffef3f7fc1 0x3ffffffffef3f7fc 0xffffffffff3fffcf 0xfffffffffff3fffc

def z454 : W := mkw 0xf7fee9053bed8000 0x8f7fee9053bed800 0xfffff93fffffc00f 0xffffff93fffffc00

def z455 : W := mkw 0x01236b77c172edd8 0x101236b77c172edd 0x4067ffffc3f1fff7 0xe4067ffffc3f1fff

def z456 : W := mkw 0x0001022000004100 0x0000102200000410 0x400706000001c302 0x0400706000001c30

def z457 : W := mkw 0x2dc11ff0f6907bf8 0x42dc11ff0f6907bf 0xffe01ff1ffc03fff 0x7ffe01ff1ffc03ff

def z458 : W := mkw 0xf7fee9057bed88c0 0x9f7fee9057bed88c 0xffffe101ffffc0cf 0xbffffe101ffffc0c

def z459 : W := mkw 0xfc7756fa8c1b7701 0x2fc7756fa8c1b770 0xf87f1efe3c3fff0e 0xff87f1efe3c3fff0

def z460 : W := mkw 0x0000001204127700 0x2000000120412770 0x0000000000003f00 0x00000000000003f0

def z461 : W := mkw 0x0022404080000000 0x0002240408000000 0x0060e1c1c0000001 0x00060e1c1c000000

def z462 : W := mkw 0x0001026080000000 0x0000102608000000 0x000007f1c0000000 0x4000007f1c000000

def z463 : W := mkw 0x25e269c0f3e088f8 0x425e269c0f3e088f 0x07e0e1c1c3c000f1 0x007e0e1c1c3c000f

def z464 : W := mkw 0xbf7fdfff80122401 0x0bf7fdfff8012240 0xbfffffffe03e3c0f 0xfbfffffffe03e3c0

def z465 : W := mkw 0x2de35fe0b6c0dbb8 0x42de35fe0b6c0dbb 0xffe71fc03fc1ffff 0x7ffe71fc03fc1fff

def z466 : W := mkw 0x921c800d00000001 0x0921c800d0000000 0x0018000e00000000 0x00018000e0000000

def z467 : W := mkw 0xaf6bdfed80000001 0x0af6bdfed8000000 0x07e0ffffc0000001 0x407e0ffffc000000

def z468 : W := mkw 0x03abeb77e376edd8 0x103abeb77e376edd 0x079ff93fe33ffccd 0xf079ff93fe33ffcc

def z469 : W := mkw 0x5036600009698000 0x0503660000969800 0xf87fe0003fffc00f 0xbf87fe0003fffc00

def z470 : W := mkw 0xfedd963a3e9f7700 0xafedd963a3e9f770 0xff9f1e3e3c3fff0e 0xfff9f1e3e3c3fff0

def z471 : W := mkw 0xbfffdfeda2000881 0x0bfffdfeda200088 0xbfffffffe3003ccf 0xfbfffffffe3003cc

def z472 : W := mkw 0xf6fee0107bfda040 0x8f6fee0107bfda04 0xffffe131ffffe0cf 0xfffffe131ffffe0c

def z473 : W := mkw 0xf7dc89073a8f0c80 0x9f7dc89073a8f0c8 0xbf98180e3c0e1c08 0x1bf98180e3c0e1c0

def z474 : W := mkw 0x0000000000000000 0x0000000000000000 0x406006c000c00332 0x0406006c000c0033

def z475 : W := mkw 0x408020107bfde158 0x8408020107bfde15 0x400000003fffe3f0 0x3400000003fffe3f

def z476 : W := mkw 0x0023426080000000 0x0002342608000000 0x0007e031c0000000 0x80007e031c000000

def z477 : W := mkw 0x0800140000000000 0x0080014000000000 0xb8001e000000000e 0x4b8001e000000000

def z478 : W := mkw 0xffffffba3fffffa0 0xeffffffba3fffffa 0xfffffffe3fffffff 0xffffffffe3ffffff

def z479 : W := mkw 0x5014000a080b0400 0x25014000a080b040 0x0018000e000e0000 0x00018000e000e000

def z480 : W := mkw 0x2fc89d8736861ea0 0x52fc89d8736861ea 0xbf98180e3c0e1c08 0x1bf98180e3c0e1c0

def z481 : W := mkw 0x00236260c160c158 0x000236260c160c15 0x4067e7c1c3c1c3f3 0x04067e7c1c3c1c3f

def z482 : W := mkw 0x58377678cd79f358 0x258377678cd79f35 0xf867e7f1dff1e3f7 0xef867e7f1dff1e3f

def z483 : W := mkw 0x2d401d8004001aa0 0x42d401d8004001aa 0xbfe01fc000003fff 0x4bfe01fc000003ff

def z484 : W := mkw 0x0000000000000000 0x0000000000000000 0x00180000203e000c 0xb00180000203e000

def z485 : W := mkw 0x2fc8bd8577a41ae0 0x52fc8bd8577a41ae 0xffe0ffc1ffc03fff 0x7ffe0ffc1ffc03ff

def z486 : W := mkw 0xbfffffffe376edd9 0x1bfffffffe376edd 0xffffffffe3ffffff 0xfffffffffe3fffff

def z487 : W := mkw 0x0388a90723260c80 0x10388a90723260c8 0x0798f80e233e1c0d 0xb0798f80e233e1c0

def z488 : W := mkw 0x5014000008090000 0x0501400000809000 0xf80700001c01c002 0x0f80700001c01c00

def z489 : W := mkw 0x00234270c050e158 0x000234270c050e15 0x406707f1c0c1e3f2 0x4406707f1c0c1e3f

def z490 : W := mkw 0x0823767ac572f758 0x20823767ac572f75 0x4067ffffc3f1fff7 0xe4067ffffc3f1fff

def z491 : W := mkw 0xbd775fed80000001 0x0bd775fed8000000 0xb8671fffc0000002 0x4b8671fffc000000

def z492 : W := mkw 0x002362608160c118 0x0002362608160c11 0x4067e6c003f1c337 0xa4067e6c003f1c33

def z493 : W := mkw 0x09237ffdc170e159 0x009237ffdc170e15 0x4067ffffc3f1e3f7 0xe4067ffffc3f1e3f

def z494 : W := mkw 0x0022600001608000 0x0002260000160800 0x0007e0000031c000 0x80007e0000031c00

def z495 : W := mkw 0x5837567a8c1b7700 0x25837567a8c1b770 0xf87ffffffc3fff0f 0xff87ffffffc3fff0

def z496 : W := mkw 0x5815163a081b6500 0x25815163a081b650 0xb81f1e3e003fc00e 0xcb81f1e3e003fc00

def z497 : W := mkw 0x0800140a04021600 0x20800140a0402160 0x0000180e00001c00 0x00000180e00001c0

def z498 : W := mkw 0x822ae00001648000 0x8822ae0000164800 0x0000e00000000000 0x00000e0000000000

def z499 : W := mkw 0xf67ee000096d8000 0x8f67ee000096d800 0xbfffe000003fc00f 0x8bfffe000003fc00

def z500 : W := mkw 0xfefef40a3fef9600 0xafefef40a3fef960 0xfffff80e3fffdc0f 0xbfffff80e3fffdc0

def z501 : W := mkw 0x09001d8d00000001 0x009001d8d0000000 0x0000180e00000000 0x00000180e0000000

def z502 : W := mkw 0xf6ffe260bbedc118 0x8f6ffe260bbedc11 0xffffe6c03fffc33f 0xbffffe6c03fffc33

def z503 : W := mkw 0xfefef4803fed9220 0xcfefef4803fed922 0xffffe6c03fffc33f 0xbffffe6c03fffc33

def z504 : W := mkw 0xa462400010c08000 0x8a462400010c0800 0x0060000000c00000 0x00060000000c0000

def z505 : W := mkw 0xfefff6283fedd300 0xafefff6283fedd30 0xffffe6003fffc30f 0xbffffe6003fffc30

def z506 : W := mkw 0x00010270c0106158 0x000010270c010615 0x400707f1c031e3f6 0xe400707f1c031e3f

def z507 : W := mkw 0x03aae945e36488d8 0x103aae945e36488d 0x07e0e1c1c3c000f1 0x007e0e1c1c3c000f

def z508 : W := mkw 0x26c8a00033a40000 0x026c8a00033a4000 0xfff8e0003ffe000f 0xbfff8e0003ffe000

def z509 : W := mkw 0xbfffffeda3240001 0x0bfffffeda324000 0xbfffffffe33e000f 0xfbfffffffe33e000

def z510 : W := mkw 0x0288a01763362cc0 0x10288a01763362cc 0x0018e03fe33e3cc0 0xb0018e03fe33e3cc

def z511 : W := mkw 0xf4776270d9f9e158 0x8f4776270d9f9e15 0xf867e7f1dff1e3f7 0xef867e7f1dff1e3f

def z512 : W := mkw 0x09011fff84127701 0x209011fff8412770 0x00001fffc0003f00 0x400001fffc0003f0

def z513 : W := mkw 0xbfffdfefa2060c81 0x1bfffdfefa2060c8 0xbfffffffe00e1c0f 0xdbfffffffe00e1c0

def z514 : W := mkw 0x09801d0026001a80 0x009801d0026001a8 0xff801f003f003fcf 0x7ff801f003f003fc

def z515 : W := mkw 0x00236270c1302040 0x000236270c130204 0x0067e7f1c33020c7 0xe0067e7f1c33020c

def z516 : W := mkw 0x581414000c091200 0x0581414000c09120 0xf81f1e003c3fff0e 0xff81f1e003c3fff0

def z517 : W := mkw 0xf6ffe23a3bffe500 0xaf6ffe23a3bffe50 0xffffe03e3fffc00f 0xbffffe03e3fffc00

def z518 : W := mkw 0xd23fc27f881b6501 0x2d23fc27f881b650 0x001fe03fc03fc000 0x8001fe03fc03fc00

def z519 : W := mkw 0x2dc11fba36927fa0 0x62dc11fba36927fa 0xffe01ffe3fc03fff 0x7ffe01ffe3fc03ff

def z520 : W := mkw 0x0801163004107300 0x0080116300410730 0xf8071e303c31ff0e 0xff8071e303c31ff0

def z521 : W := mkw 0x1015022800000000 0x0101502280000000 0x001f003e00000000 0x8001f003e0000000

def z522 : W := mkw 0x7dd51fa83e895ba0 0x67dd51fa83e895ba 0xffe71fc03fc1ffff 0x7ffe71fc03fc1fff

def z523 : W := mkw 0x2d401d8014801aa0 0x42d401d8014801aa 0xf8601fc01cc03ff2 0x4f8601fc01cc03ff

def z524 : W := mkw 0xbf7fdfed84001201 0x0bf7fdfed8400120 0xfffffffffc003f0f 0xffffffffffc003f0

def z525 : W := mkw 0x0288a01063342040 0x00288a0106334204 0x0798e131e33e20cd 0xf0798e131e33e20c

def z526 : W := mkw 0x7fddbfbf7fbf7fe0 0x77fddbfbf7fbf7fe 0xffffffffffffffff 0xffffffffffffffff

def z527 : W := mkw 0xbf5d9fad00000001 0x0bf5d9fad0000000 0xbf9f1e3e0000000e 0xcbf9f1e3e0000000

def z528 : W := mkw 0xa7eae9d7e3362cc1 0x1a7eae9d7e3362cc 0x07f8f9ffe33e3ccd 0xf07f8f9ffe33e3cc

def z529 : W := mkw 0xfefff6283bed8000 0x8fefff6283bed800 0xfffffe3e3fffc00f 0xffffffe3e3fffc00

def z530 : W := mkw 0x5a9db63a2f3f7700 0x25a9db63a2f3f770 0xff9ffe3e3f3fff0f 0xfff9ffe3e3f3fff0

def z531 : W := mkw 0x022be277c176e558 0x1022be277c176e55 0x407fe7ffc3ffe3f7 0xe407fe7ffc3ffe3f

def z532 : W := mkw 0x24e36270f3f0e158 0x024e36270f3f0e15 0xffe7e7f1fff1e3ff 0xfffe7e7f1fff1e3f

def z533 : W := mkw 0x0023626081608000 0x0002362608160800 0x4067e7f1c3f1c007 0xe4067e7f1c3f1c00

def z534 : W := mkw 0x0180090022000880 0x0018009002200088 0x0780180020001c08 0x10780180020001c0

def z535 : W := mkw 0x7cd5163a3e9b7700 0x27cd5163a3e9b770 0xffff1e3e3fffff0f 0xfffff1e3e3fffff0

def z536 : W := mkw 0x2fc8bd9777b63ee0 0x52fc8bd9777b63ee 0xbf98f93fff3e3ccd 0xfbf98f93fff3e3cc

def z537 : W := mkw 0x5014000008090000 0x0501400000809000 0x001f0000003fc000 0x8001f0000003fc00

def z538 : W := mkw 0x923ec00000000000 0x0923ec0000000000 0x001fe00000000000 0x8001fe0000000000

def z539 : W := mkw 0x6dc03d803fed9aa0 0xc6dc03d803fed9aa 0xffe01fc03fffffff 0x7ffe01fc03ffffff

def z540 : W := mkw 0x24c0000032800000 0x024c000003280000 0xbf8000003c000008 0x1bf8000003c00000

def z541 : W := mkw 0x0801162800000000 0x0080116280000000 0x00001e3e00000000 0x400001e3e0000000

def z542 : W := mkw 0xbf7edd8d00000001 0x0bf7edd8d0000000 0xbffff80e0000000f 0x8bffff80e0000000

def z543 : W := mkw 0x2fc8bd8037a41aa0 0x42fc8bd8037a41aa 0xfff8ffc03ffe3fff 0xffff8ffc03ffe3ff

def z544 : W := mkw 0x0388890522000880 0x0038889052200088 0x0798f93fe3003ccd 0xf0798f93fe3003cc

def z545 : W := mkw 0xbf7fdfed80000001 0x0bf7fdfed8000000 0xbfff1ece0000000a 0x0bfff1ece0000000

def z546 : W := mkw 0x0388a91763362cc0 0x10388a91763362cc 0x0798180e233e3cc8 0x30798180e233e3cc

def z547 : W := mkw 0x27c8a98573a408e0 0x527c8a98573a408e 0x07e0e1c1c3c000f1 0x007e0e1c1c3c000f

def z548 : W := mkw 0x0b88bd1767363ec0 0x10b88bd1767363ec 0xff98ff3fff3e3fcf 0xfff98ff3fff3e3fc

def z549 : W := mkw 0x2dc01d8036801aa0 0x42dc01d8036801aa 0x07e01fc003c03ff1 0x407e01fc003c03ff

def z550 : W := mkw 0x5015023a0c1b7700 0x25015023a0c1b770 0x401f003e3c3fff00 0xb401f003e3c3fff0

def z551 : W := mkw 0x00236270c170e158 0x000236270c170e15 0x4067e6f1c0f1c332 0x84067e6f1c0f1c33

def z552 : W := mkw 0x000020104170e158 0x0000020104170e15 0x4000e131c3f1e3f5 0xe4000e131c3f1e3f

def z553 : W := mkw 0xf6fee0003bed8000 0x8f6fee0003bed800 0xffe7e0001fc1c003 0x0ffe7e0001fc1c00

def z554 : W := mkw 0x408020126f3f7fc0 0x3408020126f3f7fc 0x400000003f3fffc0 0x3400000003f3fffc

def z555 : W := mkw 0xbc7776f8c170e159 0x0bc7776f8c170e15 0xf867e7f1c3f1e3f7 0xef867e7f1c3f1e3f

def z556 : W := mkw 0x2dc01d8036801aa0 0x42dc01d8036801aa 0xbf8019003f003ccd 0x7bf8019003f003cc

def z557 : W := mkw 0x2d635fe080000000 0x02d635fe08000000 0xbfe7fff1c000000f 0xcbfe7fff1c000000

def z558 : W := mkw 0x0100091740122cc0 0x10100091740122cc 0x0018193fe03e3ccc 0xf0018193fe03e3cc

def z559 : W := mkw 0x2c6356e094c0d338 0x42c6356e094c0d33 0xf86706c01cc1c332 0x0f86706c01cc1c33

def z560 : W := mkw 0x2dc11fb036907ba0 0x42dc11fb036907ba 0xffe71ff03ff1ffff 0xfffe71ff03ff1fff

def z561 : W := mkw 0x0801163a04127700 0x20801163a0412770 0xf8001e3e3c003f0e 0x7f8001e3e3c003f0

def z562 : W := mkw 0xe6eae0003bed8000 0x8e6eae0003bed800 0x47e0e0003fffc001 0x347e0e0003fffc00

def z563 : W := mkw 0x0180090022000880 0x0018009002200088 0x07800100030000c1 0x007800100030000c

def z564 : W := mkw 0xfffefd977fffbee0 0xdfffefd977fffbee 0xffffffffffffffff 0xffffffffffffffff

def z565 : W := mkw 0xffffff3f7fffffc0 0xbffffff3f7fffffc 0xffffff3fffffffcf 0xfffffff3fffffffc

def z566 : W := mkw 0x25c00980328008a0 0x425c00980328008a 0x07e019c023c03cfd 0x707e019c023c03cf

def z567 : W := mkw 0x2cc0148036801aa0 0x42cc0148036801aa 0xf86006c03fc03ff2 0x3f86006c03fc03ff

def z568 : W := mkw 0x400000000c095300 0x2400000000c09530 0x400000001c01c300 0x0400000001c01c30

def z569 : W := mkw 0xfc77563a1cdbf700 0xafc77563a1cdbf70 0xf87f1e3e3cffff0e 0xff87f1e3e3cffff0

def z570 : W := mkw 0xff5c9d8f0c0b1601 0x2ff5c9d8f0c0b160 0xbf98180e3c0e1c08 0x1bf98180e3c0e1c0

def z571 : W := mkw 0xa7eae91773f6acc0 0x9a7eae91773f6acc 0x07f8f93fe3fe3ccd 0xf07f8f93fe3fe3cc

def z572 : W := mkw 0x408000003a8d0000 0x8408000003a8d000 0x000000003c0e0000 0x1000000003c0e000

def z573 : W := mkw 0xd23ee017497fa440 0x9d23ee017497fa44 0x001fe03fc03fc000 0x8001fe03fc03fc00

def z574 : W := mkw 0x7dd41d803e891aa0 0x47dd41d803e891aa 0xffff1fc03fffffff 0xfffff1fc03ffffff

def z575 : W := mkw 0x2dc01d8032800000 0x02dc01d803280000 0xffe01fc03fc0000f 0x7ffe01fc03fc0000

def z576 : W := mkw 0xf6dc80003a8d0000 0x8f6dc80003a8d000 0xfff800003fce000f 0x3fff800003fce000

def z577 : W := mkw 0xb65c800000000000 0x0b65c80000000000 0xbf98000000000008 0x0bf9800000000000

def z578 : W := mkw 0xffffdfffbe9b7fa1 0x6ffffdfffbe9b7fa 0xffffffffffffffff 0xffffffffffffffff

def z579 : W := mkw 0x09001d8004001aa0 0x409001d8004001aa 0x40601fc003c03ff7 0x640601fc003c03ff

def z580 : W := mkw 0x0001023a00126500 0x20001023a0012650 0x0000003e00000000 0x00000003e0000000

def z581 : W := mkw 0x1815162804001200 0x0181516280400120 0xf81f1e3e3c003f0e 0xff81f1e3e3c003f0

def z582 : W := mkw 0x0000000000000000 0x0000000000000000 0x4060000003c00007 0x24060000003c0000

def z583 : W := mkw 0xf6fee0003bed8000 0x8f6fee0003bed800 0xbff8e0003fce0009 0x1bff8e0003fce000

def z584 : W := mkw 0xbf7fffed81608001 0x0bf7fffed8160800 0xffffffffc3f1c00f 0xeffffffffc3f1c00

def z585 : W := mkw 0xa76bebf5c170e159 0x0a76bebf5c170e15 0x47e7e7f1c3f1e3f7 0xe47e7e7f1c3f1e3f

def z586 : W := mkw 0xa6ebe270f3f4e158 0x8a6ebe270f3f4e15 0x47e7e7f1c3f1e3f7 0xe47e7e7f1c3f1e3f

def z587 : W := mkw 0x0388890722060c80 0x10388890722060c8 0x0798190e230e3ccd 0x70798190e230e3cc

def z588 : W := mkw 0x2dc01d8036801aa0 0x42dc01d8036801aa 0xbfe019c03fc01cf9 0x1bfe019c03fc01cf

def z589 : W := mkw 0x0100291741322cc0 0x10100291741322cc 0x0000f93fc3303cc5 0xe0000f93fc3303cc

def z590 : W := mkw 0xbffffffff7b63ee1 0x5bffffffff7b63ee 0xfffffffffffe3fff 0xffffffffffffe3ff

def z591 : W := mkw 0x923fe27dc170e159 0x0923fe27dc170e15 0x407fe7ffc3f1e3f7 0xe407fe7ffc3f1e3f

def z592 : W := mkw 0x480014120c1b7700 0x2480014120c1b770 0xf8001e003c3fff0e 0x7f8001e003c3fff0

def z593 : W := mkw 0xa7eae9c5b3e48001 0x8a7eae9c5b3e4800 0x07e0e1c1c3c00001 0x007e0e1c1c3c0000

def z594 : W := mkw 0x0000001740122440 0x1000000174012244 0x0000003fc0000000 0x00000003fc000000

def z595 : W := mkw 0x0308a91741362cc0 0x10308a91741362cc 0x0018f93fc03e3cc0 0xc0018f93fc03e3cc

def z596 : W := mkw 0x0308891740122cc0 0x10308891740122cc 0x0798f93fc0003ccd 0xc0798f93fc0003cc

def z597 : W := mkw 0x2dc01d8036801aa0 0x42dc01d8036801aa 0xbfe01fc03c001c0f 0x5bfe01fc03c001c0

def z598 : W := mkw 0x40002000096d8000 0x840002000096d800 0x00000000003fc000 0x000000000003fc00

def z599 : W := mkw 0xfc7654801cc99220 0xcfc7654801cc9922 0xf86706c01cc1c332 0x0f86706c01cc1c33

def z600 : W := mkw 0x0388a905632408c0 0x10388a905632408c 0x0798f93fc30000cd 0xc0798f93fc30000c

def z601 : W := mkw 0xfc7756281cc9d300 0xafc7756281cc9d30 0xf86706001cc1c302 0x0f86706001cc1c30

def z602 : W := mkw 0xbfffdfedb28008a1 0x4bfffdfedb28008a 0xbfffffffc3c000ff 0xcbfffffffc3c000f

def z603 : W := mkw 0x539ca9176b3f2cc0 0x1539ca9176b3f2cc 0xff9ff93fff3ffccf 0xfff9ff93fff3ffcc

def z604 : W := mkw 0x00010270c0106158 0x000010270c010615 0x00000031c0000000 0x000000031c000000

def z605 : W := mkw 0xa6eae00033e48000 0x8a6eae00033e4800 0x47e7e00003f1c007 0xa47e7e00003f1c00

def z606 : W := mkw 0x0080000022000000 0x0008000002200000 0x078000002300000d 0x3078000002300000

def z607 : W := mkw 0x6dc01d923e9b7fa0 0x66dc01d923e9b7fa 0xffe01fc03fffffff 0x7ffe01fc03ffffff

def z608 : W := mkw 0x2dc03d9077f0fbf8 0x42dc03d9077f0fbf 0xffe01fc03ff1ffff 0x7ffe01fc03ff1fff

def z609 : W := mkw 0xbfdcbd9f63362cc1 0x1bfdcbd9f63362cc 0xbf98f93fe33e3ccd 0xfbf98f93fe33e3cc

def z610 : W := mkw 0xd036400008498000 0x8d03640000849800 0x000700000001c000 0x0000700000001c00

def z611 : W := mkw 0x0288800022040000 0x0028880002204000 0x07980000200e0008 0x107980000200e000

def z612 : W := mkw 0x5b9c9d0f2e0f1e80 0x35b9c9d0f2e0f1e8 0xbf98180e3c0e1c08 0x1bf98180e3c0e1c0

def z613 : W := mkw 0x00236270c170e158 0x000236270c170e15 0x0060e7f1c3c023f1 0x40060e7f1c3c023f

def z614 : W := mkw 0xb77ec9c580000001 0x0b77ec9c58000000 0xbfffe1c1c000000f 0x8bfffe1c1c000000

def z615 : W := mkw 0x2c40148000000000 0x02c4014800000000 0xb86006c000000002 0x0b86006c00000000

def z616 : W := mkw 0x09011fffc0122cc1 0x109011fffc0122cc 0x00001fffc0003cc0 0x400001fffc0003cc

def z617 : W := mkw 0xf6fee0177bffa440 0x9f6fee0177bffa44 0xffffe03fffffc00f 0xbffffe03fffffc00

def z618 : W := mkw 0x5815363a4d3b7740 0x25815363a4d3b774 0xf81fff3fff3fffcf 0xff81fff3fff3fffc

def z619 : W := mkw 0x0000000000000000 0x0000000000000000 0x006001c003c000f1 0x0006001c003c000f

def z620 : W := mkw 0x000020104170e158 0x0000020104170e15 0x000000000031c000 0x0000000000031c00

def z621 : W := mkw 0xf7fee9003bed8880 0x8f7fee9003bed888 0xfffff9003ffffccf 0xffffff9003ffffcc

def z622 : W := mkw 0x2440008010800020 0x4244000801080002 0x006000c000c00030 0x0006000c000c0003

def z623 : W := mkw 0x0000000000000000 0x0000000000000000 0x4000060000002306 0x6400006000000230

def z624 : W := mkw 0x0080000036801aa0 0x40080000036801aa 0x406007c03fc03ff7 0x7406007c03fc03ff

def z625 : W := mkw 0x0800141204123600 0x0080014120412360 0xf8181e3e3c3e3f0e 0xff8181e3e3c3e3f0

def z626 : W := mkw 0x0000000004001200 0x0000000000400120 0x400000003c003f00 0x3400000003c003f0

def z627 : W := mkw 0xb6fee00023240000 0x0b6fee0002324000 0xbfffe000233e000f 0xbbfffe000233e000

def z628 : W := mkw 0x00012270c1306158 0x000012270c130615 0x0000e7f1c33023f5 0xe0000e7f1c33023f

def z629 : W := mkw 0x27c8a99773b62ce0 0x527c8a99773b62ce 0x07f8f9ffe3fe3cfd 0xf07f8f9ffe3fe3cf

def z630 : W := mkw 0x40000012081b6500 0x240000012081b650 0x00000000003fc000 0x000000000003fc00

def z631 : W := mkw 0x0388a905632408c0 0x10388a905632408c 0x0798e101e33e00cd 0xb0798e101e33e00c

def z632 : W := mkw 0xbf7ffffdc1302041 0x0bf7ffffdc130204 0xbfffffffc33020cf 0xebfffffffc33020c

def z633 : W := mkw 0x2d401d8000000000 0x02d401d800000000 0xffe01fc003c023ff 0x6ffe01fc003c023f

def z634 : W := mkw 0x5815163a0c1b7700 0x25815163a0c1b770 0xf81f063e1c3fc302 0x8f81f063e1c3fc30

def z635 : W := mkw 0x0208a01741362440 0x10208a0174136244 0x0018f83fe03e3c0c 0xf0018f83fe03e3c0

def z636 : W := mkw 0x0080200033e48000 0x80080200033e4800 0x0000000003c00000 0x00000000003c0000

def z637 : W := mkw 0xffdc9d803e8d1aa0 0xcffdc9d803e8d1aa 0xfff81fc03fce3fff 0x7fff81fc03fce3ff

def z638 : W := mkw 0x0389ab3763366dc0 0x10389ab3763366dc 0x479fff3fe33fffcf 0xf479fff3fe33fffc

def z639 : W := mkw 0x0b89bfffe3362cc1 0x10b89bfffe3362cc 0x0798ffffe33e3ccd 0xf0798ffffe33e3cc

def z640 : W := mkw 0xf6fec0003a8d0000 0x8f6fec0003a8d000 0xbfffe0003c0e000f 0x9bfffe0003c0e000

def z641 : W := mkw 0xbf7fdfffc0122cc1 0x1bf7fdfffc0122cc 0xbfffffffc0003ccf 0xcbfffffffc0003cc

def z642 : W := mkw 0xbf7edd8000000000 0x0bf7edd800000000 0xbfffffc00000000f 0xcbfffffc00000000

def z643 : W := mkw 0x0288a00023240000 0x00288a0002324000 0x0780e00003000001 0x00780e0000300000

def z644 : W := mkw 0x00226040c1608058 0x000226040c160805 0x4060e7c1c3c023f7 0x64060e7c1c3c023f

def z645 : W := mkw 0x002342608040c118 0x0002342608040c11 0x000700000001c000 0x0000700000001c00

def z646 : W := mkw 0x0000000000000000 0x0000000000000000 0x006007c000000007 0x4006007c00000000

def z647 : W := mkw 0x7dd41d8a3e8b1ea0 0x67dd41d8a3e8b1ea 0xfff81fce3fce3fff 0x7fff81fce3fce3ff

def z648 : W := mkw 0xf6fee0127bffacc0 0x9f6fee0127bffacc 0xffffe0003ffffccf 0xbffffe0003ffffcc

def z649 : W := mkw 0xafeafd8037e49aa0 0xcafeafd8037e49aa 0xffe0ffc03fc03fff 0x7ffe0ffc03fc03ff

def z650 : W := mkw 0x0000000000000000 0x0000000000000000 0x000007c0000023f0 0x4000007c0000023f

def z651 : W := mkw 0x0000001000106100 0x0000000100010610 0x400000000031e300 0x2400000000031e30

def z652 : W := mkw 0x40236272cd7bf758 0x240236272cd7bf75 0x4067e7f1fffffff7 0xf4067e7f1fffffff

def z653 : W := mkw 0xa7eae9c5e32408c1 0x1a7eae9c5e32408c 0x07e0e1c1c30000c1 0x007e0e1c1c30000c

def z654 : W := mkw 0xd23ee000096d8000 0x8d23ee000096d800 0xf81fe0003c3fc00e 0xbf81fe0003c3fc00

def z655 : W := mkw 0xda3fd67f8c1b7701 0x2da3fd67f8c1b770 0xf81ffe3ffc3fff0e 0xff81ffe3ffc3fff0

def z656 : W := mkw 0x2d411fed80000001 0x02d411fed8000000 0xbfe01fffc000000f 0x4bfe01fffc000000

def z657 : W := mkw 0x25c0098036801aa0 0x425c0098036801aa 0x47e001c03fc03ff1 0x347e001c03fc03ff

def z658 : W := mkw 0x02aae00023648000 0x002aae0002364800 0x47ffe00023ffc00f 0xb47ffe00023ffc00

def z659 : W := mkw 0x0022404080408018 0x0002240408040801 0x006000c000c00030 0x0006000c000c0003

def z660 : W := mkw 0x0001022000000000 0x0000102200000000 0x0007063000000006 0xc000706300000000

def z661 : W := mkw 0x0022400000000000 0x0002240000000000 0x0067e00000000007 0x80067e0000000000

def z662 : W := mkw 0x5815163a0c1b7700 0x25815163a0c1b770 0x001f1e3e003fff00 0xc001f1e3e003fff0

def z663 : W := mkw 0x2de27dc0f7e09af8 0x42de27dc0f7e09af 0xffe0ffc1ffc03fff 0x7ffe0ffc1ffc03ff

def z664 : W := mkw 0xf476400018c98000 0x8f476400018c9800 0xf87f00003cffc00e 0xbf87f00003cffc00

def z665 : W := mkw 0xa66ac00000000000 0x0a66ac0000000000 0x07e0e00000000001 0x007e0e0000000000

def z666 : W := mkw 0x09011ff0c4107bf8 0x409011ff0c4107bf 0x00001ff1c0003ff0 0x400001ff1c0003ff

def z667 : W := mkw 0x00000040c0000058 0x000000040c000005 0x000001c1c00000f0 0x0000001c1c00000f

def z668 : W := mkw 0xbc7756e880000001 0x0bc7756e88000000 0xb87f1efe0000000e 0xcb87f1efe0000000

def z669 : W := mkw 0x002362300170e100 0x0002362300170e10 0x4067e63003f1e307 0xe4067e63003f1e30

def z670 : W := mkw 0x19151fed80000001 0x019151fed8000000 0xb81f1fffc000000e 0xcb81f1fffc000000

def z671 : W := mkw 0xbf7fffffc1362441 0x1bf7fffffc136244 0xbfffffffc03e000f 0xcbfffffffc03e000

def z672 : W := mkw 0x0001223041306140 0x0000122304130614 0x4007e731c331e3c7 0xe4007e731c331e3c

def z673 : W := mkw 0x00226050c170e158 0x000226050c170e15 0x4060e1c1c3f1e3f1 0x24060e1c1c3f1e3f

def z674 : W := mkw 0x408020123ffff700 0xa408020123ffff70 0x400000003fffff00 0x3400000003fffff0

def z675 : W := mkw 0x00012270c170e158 0x000012270c170e15 0x400007f1c3f1e3f0 0x6400007f1c3f1e3f

def z676 : W := mkw 0x0208a01741362440 0x10208a0174136244 0x0018e13fc33e20c5 0xe0018e13fc33e20c

def z677 : W := mkw 0xfffffff0fffdfbf8 0xcfffffff0fffdfbf 0xfffffff1ffffffff 0xffffffff1fffffff

def z678 : W := mkw 0xfffefd803bed8000 0x8fffefd803bed800 0xffffffc03fffc00f 0xfffffffc03fffc00

def z679 : W := mkw 0x581414080c091200 0x2581414080c09120 0xb80000001c000000 0x0b80000001c00000

def z680 : W := mkw 0x0308a91541302040 0x00308a9154130204 0x0798f93fc33020cd 0xe0798f93fc33020c

def z681 : W := mkw 0x25e36bf0f3f0e9f8 0x425e36bf0f3f0e9f 0x47e7e7f1c3f1e3f7 0xe47e7e7f1c3f1e3f

def z682 : W := mkw 0x00236270c170e158 0x000236270c170e15 0x4067e031c3f1c007 0xa4067e031c3f1c00

def z683 : W := mkw 0x00236260c1608058 0x000236260c160805 0x0067e7f1c3c000f7 0xc0067e7f1c3c000f

def z684 : W := mkw 0xb476400000000000 0x0b47640000000000 0xb867000000000002 0x0b86700000000000

def z685 : W := mkw 0x0000001000102000 0x0000000100010200 0x0000003000302004 0xe000000300030200

def z686 : W := mkw 0x25c00980328008a0 0x425c00980328008a 0x0780000000000000 0x0078000000000000

def z687 : W := mkw 0x5037627ac97be558 0x25037627ac97be55 0x001fe03fc03fc000 0x8001fe03fc03fc00

def z688 : W := mkw 0x24c0000032800000 0x024c000003280000 0xffe007c03fc023ff 0x7ffe007c03fc023f

def z689 : W := mkw 0x0000201041302040 0x0000020104130204 0x4060e7f1c3f023f7 0xe4060e7f1c3f023f

def z690 : W := mkw 0x0000001200122400 0x0000000120012240 0x0018003e003e0000 0x80018003e003e000

def z691 : W := mkw 0x00236270c170e158 0x000236270c170e15 0x4007e031c3f1e3f0 0xa4007e031c3f1e3f

def z692 : W := mkw 0x0100090700020c80 0x10100090700020c8 0x0000180e00001c00 0x00000180e00001c0

def z693 : W := mkw 0x0001023000106100 0x0000102300010610 0x000700300031c000 0x8000700300031c00

def z694 : W := mkw 0x7d551fba0c1b7700 0x27d551fba0c1b770 0xffff1ffe3c3fff0f 0xfffff1ffe3c3fff0

def z695 : W := mkw 0xbf7fdffdc0106159 0x0bf7fdffdc010615 0xbfffffffc00023ff 0xcbfffffffc00023f

def z696 : W := mkw 0xd23ee000096d8000 0x8d23ee000096d800 0x407fe00003ffc007 0xa407fe00003ffc00

def z697 : W := mkw 0xff7fffffcd7bf759 0x2ff7fffffcd7bf75 0xffffffffffffffff 0xffffffffffffffff

def z698 : W := mkw 0xbfdc9d8d36801aa1 0x4bfdc9d8d36801aa 0xfff81fce3fc03fff 0x7fff81fce3fc03ff

def z699 : W := mkw 0x5837567a8c5bf718 0x25837567a8c5bf71 0xf87f1efe3cffff3e 0xff87f1efe3cffff3

def z700 : W := mkw 0x0000000200020400 0x0000000020002040 0x0018180e200e1c08 0x10018180e200e1c0

def z701 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000180020003c0c 0x70000180020003c0

def z702 : W := mkw 0x0022400000408000 0x0002240000040800 0x4067000000c1c002 0x04067000000c1c00

def z703 : W := mkw 0xd2bee0002b6d8000 0x8d2bee0002b6d800 0x079fe000233fc00d 0xb079fe000233fc00

def z704 : W := mkw 0x59151f3f4c1b7fc0 0x359151f3f4c1b7fc 0xf81f1f3ffc3fffce 0xff81f1f3ffc3fffc

def z705 : W := mkw 0x4388a9176f3f7fc0 0x34388a9176f3f7fc 0x4798f93fff3fffcd 0xf4798f93fff3fffc

def z706 : W := mkw 0x00236270c170e158 0x000236270c170e15 0x0067e1f1c3f1c0f1 0x80067e1f1c3f1c0f

def z707 : W := mkw 0x09011f7fc4127fd8 0x309011f7fc4127fd 0x00001fffc0003ff0 0x400001fffc0003ff

def z708 : W := mkw 0xf67ec00018c98000 0x8f67ec00018c9800 0xffffe0003cffc00f 0xbffffe0003cffc00

def z709 : W := mkw 0x0b089d0500000000 0x00b089d050000000 0xbf98ff3fc000000f 0xcbf98ff3fc000000

def z710 : W := mkw 0x032bcb658040c118 0x0032bcb658040c11 0x47ffffffc0c1c33f 0xc47ffffffc0c1c33

def z711 : W := mkw 0x27eae9c5f3e488f8 0x527eae9c5f3e488f 0x07e0e1c1c3c000f1 0x007e0e1c1c3c000f

def z712 : W := mkw 0x03abcb67a246cd98 0x103abcb67a246cd9 0x47ff1ece20cfdf3a 0x147ff1ece20cfdf3

def z713 : W := mkw 0xf6fee0003bed8880 0x8f6fee0003bed888 0xffffe0003ffffccf 0xbffffe0003ffffcc

def z714 : W := mkw 0x0b089d8504001aa0 0x40b089d8504001aa 0x0798ffffc0003ffd 0xc0798ffffc0003ff

def z715 : W := mkw 0x0b089d8500000000 0x00b089d850000000 0x0798ffffc000000d 0xc0798ffffc000000

def z716 : W := mkw 0xf4f660127bffacc0 0x9f4f660127bffacc 0xf86700003ffffcc2 0x3f86700003ffffcc

def z717 : W := mkw 0xbf7fdfed80000001 0x0bf7fdfed8000000 0xffffffffc000230f 0xeffffffffc000230

def z718 : W := mkw 0x2dc01d8036801aa0 0x42dc01d8036801aa 0xfff81ffe3fc03fff 0xffff81ffe3fc03ff

def z719 : W := mkw 0x00236260c160c158 0x000236260c160c15 0x4067e7f1c3c1c3f7 0xc4067e7f1c3c1c3f

def z720 : W := mkw 0x2dc01d8036801aa0 0x42dc01d8036801aa 0xbfe01fc03fc03ff9 0x5bfe01fc03fc03ff

def z721 : W := mkw 0x5b9dbf2d6f2d5bc0 0x35b9dbf2d6f2d5bc 0xff87e701df01c3c3 0x0ff87e701df01c3c

def z722 : W := mkw 0x0388a9176376acc0 0x10388a9176376acc 0x4798f93fe3fffccd 0xf4798f93fe3fffcc

def z723 : W := mkw 0xa7eae945f3e488d8 0x9a7eae945f3e488d 0x07e0e1c1c3c000f1 0x007e0e1c1c3c000f

def z724 : W := mkw 0xf67ee00019ed8000 0x8f67ee00019ed800 0xffffe0001cffc00f 0x8ffffe0001cffc00

def z725 : W := mkw 0x509420126b3f2cc0 0x1509420126b3f2cc 0xf81f00003f3ffcce 0xbf81f00003f3ffcc

def z726 : W := mkw 0xf576491758dbacc0 0x9f576491758dbacc 0xf867193fdcc1fcc2 0x4f867193fdcc1fcc

def z727 : W := mkw 0x0388a91763362cc0 0x10388a91763362cc 0x0798f93fc33e3cc1 0xc0798f93fc33e3cc

def z728 : W := mkw 0xb67fc26d80000001 0x0b67fc26d8000000 0xbfffe7ffc000000f 0xcbfffe7ffc000000

def z729 : W := mkw 0x529ca0003bed8000 0x8529ca0003bed800 0xff9fe0003fffc00f 0xbff9fe0003fffc00

def z730 : W := mkw 0x75d50bba3a9b6da0 0x675d50bba3a9b6da 0x07ff01fe03ffc0f1 0x807ff01fe03ffc0f

def z731 : W := mkw 0x0b099f2d00000000 0x00b099f2d0000000 0x0798ff3fc000000d 0xc0798ff3fc000000

def z732 : W := mkw 0xa7eae90533e48880 0x9a7eae90533e4888 0x07e0e00003c00001 0x007e0e00003c0000

def z733 : W := mkw 0xaeebf63a37f6f700 0xaaeebf63a37f6f70 0x07e0fe3e03c03f01 0x407e0fe3e03c03f0

def z734 : W := mkw 0xbf7fdfed80000001 0x0bf7fdfed8000000 0xbfffffffc00023ff 0xcbfffffffc00023f

def z735 : W := mkw 0x0b089d8d00000001 0x00b089d8d0000000 0x0798f93fc000000d 0xc0798f93fc000000

def z736 : W := mkw 0xfc7756e89cc9d301 0xafc7756e89cc9d30 0xf86706c01cc1c302 0x0f86706c01cc1c30

def z737 : W := mkw 0xb67fc26d80000001 0x0b67fc26d8000000 0x07ffe03fc0000001 0x807ffe03fc000000

def z738 : W := mkw 0x0308890500000000 0x0030889050000000 0x0798f83fc0000008 0x80798f83fc000000

def z739 : W := mkw 0x0308890500000000 0x0030889050000000 0x0798f93fc30020cd 0xe0798f93fc30020c

def z740 : W := mkw 0xbf7fdfed94801221 0x4bf7fdfed9480122 0xffffffffdfc023ff 0xeffffffffdfc023f

def z741 : W := mkw 0x0208800500000000 0x0020880050000000 0x0798e03fc000000d 0x80798e03fc000000

def z742 : W := mkw 0x2de37ff0f7f0fbf8 0x42de37ff0f7f0fbf 0xbf87f831fc31dc08 0x9bf87f831fc31dc0

def z743 : W := mkw 0xf6fee0003bed8000 0x8f6fee0003bed800 0xffffe131ffffc00f 0xfffffe131ffffc00

def z744 : W := mkw 0x25c0090032800880 0x025c009003280088 0xffe01fc03fc03fff 0x7ffe01fc03fc03ff

def z745 : W := mkw 0x933fcb6d80000001 0x0933fcb6d8000000 0x079ff83fc0000008 0x8079ff83fc000000

def z746 : W := mkw 0x09801d0026001a80 0x009801d0026001a8 0xffe01fc03fc03fff 0x7ffe01fc03fc03ff

def z747 : W := mkw 0xf6fee0003bed8000 0x8f6fee0003bed800 0xffffe6003fffe30f 0xfffffe6003fffe30

def z748 : W := mkw 0xbf7fdfed84001aa1 0x4bf7fdfed84001aa 0xffffffffc3c03fff 0xeffffffffc3c03ff

def z749 : W := mkw 0x00236270c170e158 0x000236270c170e15 0x0067e7f1c3f1e3f1 0xc0067e7f1c3f1e3f

def z750 : W := mkw 0x92bfc26db6801aa1 0x492bfc26db6801aa 0x401fe03fffc03ff0 0xb401fe03fffc03ff

def z751 : W := mkw 0xa76bcbed80000001 0x0a76bcbed8000000 0x07e0e1ffc0000001 0x007e0e1ffc000000

def z752 : W := mkw 0x5895363a6f3f7fc0 0x35895363a6f3f7fc 0xf80706003f3fffc2 0x3f80706003f3fffc

def z753 : W := mkw 0x0388890722060c80 0x10388890722060c8 0x0798f93fe30e3ccd 0xf0798f93fe30e3cc

def z754 : W := mkw 0x3d775fe880000000 0x03d775fe88000000 0xbfffffffc000000f 0xcbfffffffc000000

def z755 : W := mkw 0xd2bee0002b6d8000 0x8d2bee0002b6d800 0xff9fe0003f3fc00f 0xbff9fe0003f3fc00

def z756 : W := mkw 0x0388a91763362cc0 0x10388a91763362cc 0xff98f93fff3e3ccf 0xfff98f93fff3e3cc

def z757 : W := mkw 0x7fdc9d8f3e8f1ea0 0x77fdc9d8f3e8f1ea 0xbf98180e3c0e1c08 0x1bf98180e3c0e1c0

def z758 : W := mkw 0xbf7fdfed84001221 0x4bf7fdfed8400122 0xbfffffffc000033f 0xcbfffffffc000033

def z759 : W := mkw 0x5815167a8c1b7718 0x25815167a8c1b771 0xf81f1efe3c3fff3e 0xff81f1efe3c3fff3

def z760 : W := mkw 0x0308890500000000 0x0030889050000000 0x47f8ffffc3c023ff 0xe47f8ffffc3c023f

def z761 : W := mkw 0x64e260003bed8000 0x864e260003bed800 0xffe7e0003fffc00f 0xbffe7e0003fffc00

def z762 : W := mkw 0xf6dca0003bad0000 0x8f6dca0003bad000 0xff9fe0003f3fc00f 0xbff9fe0003f3fc00

def z763 : W := mkw 0x0388a91773b62cc0 0x10388a91773b62cc 0x4798f93ffffe3ccd 0xf4798f93ffffe3cc

def z764 : W := mkw 0x0308890500000000 0x0030889050000000 0x07f8ffffc000000f 0xc07f8ffffc000000

def z765 : W := mkw 0xbcf776fae3362cc1 0x1bcf776fae3362cc 0xb86706c0233e3cc2 0x3b86706c0233e3cc

def z766 : W := mkw 0x0023427080106100 0x0002342708010610 0x4067e7f1c3f1e3f7 0xe4067e7f1c3f1e3f

def z767 : W := mkw 0x00236270c170e158 0x000236270c170e15 0xf867e7f1fff1e3ff 0xff867e7f1fff1e3f

def z768 : W := mkw 0xa7eae9c5b3e488a1 0xca7eae9c5b3e488a 0x07e0e1c1c3c000f1 0x007e0e1c1c3c000f

def z769 : W := mkw 0xf6fee0057bed8040 0x9f6fee0057bed804 0xffffe001ffffc00f 0xbffffe001ffffc00

def z770 : W := mkw 0xf6dc80003a8d0000 0x8f6dc80003a8d000 0xffff00003fffc00f 0xbffff00003fffc00

def z771 : W := mkw 0x5b1d9f2d0c095300 0x25b1d9f2d0c09530 0xff9fff3fdc01c30f 0xcff9fff3fdc01c30

def z772 : W := mkw 0x5836744acd6b9658 0x25836744acd6b965 0xb878f9cfffce1cf9 0x1b878f9cfffce1cf

def z773 : W := mkw 0xbf7fdfed94801221 0x4bf7fdfed9480122 0xbfffffffdc00000f 0xcbfffffffdc00000

def z774 : W := mkw 0xbf5d9fad00000001 0x0bf5d9fad0000000 0xbf9fff3fc000000f 0xcbf9fff3fc000000

def z775 : W := mkw 0xf6fee0003bed8000 0x8f6fee0003bed800 0xbfffe0003fffc009 0x9bfffe0003fffc00

def z776 : W := mkw 0x0388a91763362cc0 0x10388a91763362cc 0x0798f83fe03e3c0c 0xf0798f83fe03e3c0

def z777 : W := mkw 0xf6fee0003bed8000 0x8f6fee0003bed800 0xffffe7c03fffc00f 0xfffffe7c03fffc00

def z778 : W := mkw 0xf6fee0003bed8000 0x8f6fee0003bed800 0xffff00003fffc00a 0x3ffff00003fffc00

def z779 : W := mkw 0xdb3efd800d6d9aa0 0xcdb3efd800d6d9aa 0x001fffc0003ffff0 0xc001fffc0003ffff

def z780 : W := mkw 0xe76ac9d78c1b7701 0x2e76ac9d78c1b770 0x47e0e1c1fc3fff01 0x347e0e1c1fc3fff0

def z781 : W := mkw 0x5815163a0c1b7700 0x25815163a0c1b770 0xf81f1e3e3c3fdf0a 0x9f81f1e3e3c3fdf0

def z782 : W := mkw 0x5815167a8c1b7700 0x25815167a8c1b770 0xf81f1ffffc3fff0e 0xff81f1ffffc3fff0

def z783 : W := mkw 0xf6dc80003a8d0000 0x8f6dc80003a8d000 0xbf9f00003c3fc008 0x9bf9f00003c3fc00

def z784 : W := mkw 0x0308891740122cc0 0x10308891740122cc 0x0798f93fe03e3ccd 0xf0798f93fe03e3cc

def z785 : W := mkw 0x408020127bbf2cc0 0x9408020127bbf2cc 0x000000003f3e3cc0 0x3000000003f3e3cc

def z786 : W := mkw 0x00a36272e376edd8 0x100a36272e376edd 0x406706c023fffff2 0x3406706c023fffff

def z787 : W := mkw 0xbf7fdfed84001aa1 0x4bf7fdfed84001aa 0xbfffffffc0001c0f 0xcbfffffffc0001c0

def z788 : W := mkw 0x09011fff84127fa1 0x609011fff84127fa 0x00001fffc0003ff0 0x400001fffc0003ff

def z789 : W := mkw 0x0388891722162c80 0x10388891722162c8 0x0798f93fe03e3c0d 0xf0798f93fe03e3c0

def z790 : W := mkw 0x09011f3f04127700 0x209011f3f0412770 0x00001f3fc0003f00 0x400001f3fc0003f0

def z791 : W := mkw 0xf6fee0003bed8000 0x8f6fee0003bed800 0xffe7e0003fffc003 0x3ffe7e0003fffc00

def z792 : W := mkw 0x03098b6d80000001 0x003098b6d8000000 0x0798f93fc000000d 0xc0798f93fc000000

def z793 : W := mkw 0x09011ffac4127ff8 0x609011ffac4127ff 0x00001fffc0003ff0 0x400001fffc0003ff

def z794 : W := mkw 0x03098b2500000000 0x003098b250000000 0x079fff3fc000000f 0xc079fff3fc000000

def z795 : W := mkw 0xff7fdfed9cc99221 0xcff7fdfed9cc9922 0xffffffffdcc1c33f 0xcffffffffdcc1c33

def z796 : W := mkw 0x408020126f7fffd8 0x3408020126f7fffd 0x400000003ffffff0 0x3400000003ffffff

def z797 : W := mkw 0xf6dd8270fa9d6158 0x8f6dd8270fa9d615 0xbf9807f1fc0e23f8 0x5bf9807f1fc0e23f

def z798 : W := mkw 0x0308a91741362cc0 0x10308a91741362cc 0x0798f93fc03e3ccd 0xc0798f93fc03e3cc

def z799 : W := mkw 0xf6fee0003bed8000 0x8f6fee0003bed800 0xffffe6c03fffc33f 0xbffffe6c03fffc33

def z800 : W := mkw 0x09011fffc4127759 0x209011fffc412775 0x00001fffc0003ff0 0x400001fffc0003ff

def z801 : W := mkw 0x76dca0003bad0000 0x076dca0003bad000 0xffffe0003fffc00f 0xbffffe0003fffc00

def z802 : W := mkw 0xf4f660003bed8000 0x8f4f660003bed800 0xffe700003fffc00f 0x3ffe700003fffc00

def z803 : W := mkw 0x581516280c091200 0x0581516280c09120 0xf81f1e3e3c3fff0e 0xff81f1e3e3c3fff0

def z804 : W := mkw 0x0080201263362cc0 0x10080201263362cc 0x4000000023fe3ff0 0x34000000023fe3ff

def z805 : W := mkw 0xb77fcb6d80000001 0x0b77fcb6d8000000 0xbffff93fc000000f 0xcbffff93fc000000

def z806 : W := mkw 0x1b1c9d0d00000000 0x01b1c9d0d0000000 0xbf98f93fc000000d 0xcbf98f93fc000000

def z807 : W := mkw 0xb67fc26d80000001 0x0b67fc26d8000000 0xbf9fe03fc0000008 0x8bf9fe03fc000000

def z808 : W := mkw 0x74d420003bed8000 0x874d420003bed800 0xffff00003fffc00f 0xbffff00003fffc00

def z809 : W := mkw 0x0080201263362cc0 0x10080201263362cc 0x00000000203e1c00 0x100000000203e1c0

def z810 : W := mkw 0xbe7fd6ed80000001 0x0be7fd6ed8000000 0xbfffe6ffc000000f 0x8bfffe6ffc000000

def z811 : W := mkw 0x2dc01d8036801aa0 0x42dc01d8036801aa 0xffe007c03fc03ff3 0x3ffe007c03fc03ff

def z812 : W := mkw 0xf6fee0003bed8000 0x8f6fee0003bed800 0xfffff83e3fffc00f 0xffffff83e3fffc00

def z813 : W := mkw 0x581516fa8c1b7701 0x2581516fa8c1b770 0xf81f1efe3c3fff0e 0xff81f1efe3c3fff0

def z814 : W := mkw 0xd23fe277c97fe558 0x9d23fe277c97fe55 0x001fe03fc03fc000 0x8001fe03fc03fc00

def z815 : W := mkw 0xd23fe27fc97be559 0x2d23fe27fc97be55 0x001fe03fc03fc000 0x8001fe03fc03fc00

def z816 : W := mkw 0xbf5cbd9d4170e159 0x0bf5cbd9d4170e15 0xff98180e03f1e3f8 0x2ff98180e03f1e3f

def z817 : W := mkw 0xb77ec9c580000001 0x0b77ec9c58000000 0xbffff9ffc000000f 0xcbffff9ffc000000

def z818 : W := mkw 0xb77fcbed80000001 0x0b77fcbed8000000 0x07ffe7ffc0000007 0xc07ffe7ffc000000

def z819 : W := mkw 0xf6fee0007bed88c0 0x9f6fee0007bed88c 0xffffe0003fffc0cf 0xbffffe0003fffc0c

def z820 : W := mkw 0x408020126b7facc0 0x9408020126b7facc 0x00000000233ffcc0 0x300000000233ffcc

def z821 : W := mkw 0x50150232081b6500 0x050150232081b650 0xf81f1e3e3c3fff0e 0xff81f1e3e3c3fff0

def z822 : W := mkw 0xf6fee0003bed8000 0x8f6fee0003bed800 0xff9fe0003fffc008 0xbff9fe0003fffc00

def z823 : W := mkw 0x0080201263366dc0 0x10080201263366dc 0x40000000233fffc0 0x340000000233fffc

def z824 : W := mkw 0xf6fee0803bed8020 0xcf6fee0803bed802 0xffffe0c03fffc03f 0xbffffe0c03fffc03

def z825 : W := mkw 0xffdc9d8d3e8d1aa1 0xcffdc9d8d3e8d1aa 0xbf98180e3c0e1c08 0x1bf98180e3c0e1c0

def z826 : W := mkw 0xff7fdfed8c49d319 0x2ff7fdfed8c49d31 0xffffffffdcc1c33f 0xcffffffffdcc1c33

def z827 : W := mkw 0x531c890508090000 0x0531c89050809000 0xff9ff93ffc3fc00f 0xfff9ff93ffc3fc00

def z828 : W := mkw 0xf6fee00d3bed8001 0x8f6fee00d3bed800 0xffffe00e3fffc00f 0xbffffe00e3fffc00

def z829 : W := mkw 0xb75c890500000000 0x0b75c89050000000 0xbf98f93fc000000d 0xcbf98f93fc000000

def z830 : W := mkw 0x0080201263362cc0 0x10080201263362cc 0x00180000233e3ccc 0xb00180000233e3cc

def z831 : W := mkw 0xbf7fdfed80000001 0x0bf7fdfed8000000 0xbfffffffc30020cf 0xebfffffffc30020c

def z832 : W := mkw 0xaf6addc580000001 0x0af6addc58000000 0xbff8ffffc000000f 0xcbff8ffffc000000

def z833 : W := mkw 0xa76bcbe580000001 0x0a76bcbe58000000 0x07ffffffc000000f 0xc07ffffffc000000

def z834 : W := mkw 0xbf7edd8d00000001 0x0bf7edd8d0000000 0xbffff93fc000000f 0xcbffff93fc000000

def z835 : W := mkw 0xbf7fdfed80000001 0x0bf7fdfed8000000 0xbf9ffe3fc000000e 0xcbf9ffe3fc000000

def z836 : W := mkw 0xf6fee0007bed8058 0x8f6fee0007bed805 0xffffe0003fffc0ff 0xbffffe0003fffc0f

def z837 : W := mkw 0x00236272c172e558 0x000236272c172e55 0x4067e7f1e3fffff7 0xf4067e7f1e3fffff

def z838 : W := mkw 0x2e48b49755b63660 0x52e48b49755b6366 0xf878e6ffdcfe0332 0x8f878e6ffdcfe033

def z839 : W := mkw 0xbf7fdfed80408001 0x0bf7fdfed8040800 0xffffffffc0c1c00f 0xcffffffffc0c1c00

def z840 : W := mkw 0xf67ee00009698000 0x0f67ee0000969800 0xffffe0003fffc00f 0xbffffe0003fffc00

def z841 : W := mkw 0x0308890500000000 0x0030889050000000 0x0780f93fc0000001 0x40780f93fc000000

def z842 : W := mkw 0x521c800008090000 0x0521c80000809000 0xff9fe0003c3fc00f 0xbff9fe0003c3fc00

def z843 : W := mkw 0xbf7fdfed800008a1 0x4bf7fdfed800008a 0xbfffffffc00000ff 0xcbfffffffc00000f

def z844 : W := mkw 0xf65c800008090000 0x0f65c80000809000 0xff9f00003c3fc00e 0xbff9f00003c3fc00

def z845 : W := mkw 0x5815163a0c1b7700 0x25815163a0c1b770 0xf81f1e3e3ffffffe 0xff81f1e3e3ffffff

def z846 : W := mkw 0x2d401d8004001200 0x02d401d800400120 0xffe01fc03fc03fff 0x7ffe01fc03fc03ff

def z847 : W := mkw 0xf67ee000096d8000 0x8f67ee000096d800 0xffffe0003c3fc00f 0xbffffe0003c3fc00

def z848 : W := mkw 0xb67ec00500000000 0x0b67ec0050000000 0xbfffe03fc000000f 0x8bfffe03fc000000

def z849 : W := mkw 0xff7fdfed8c091201 0x2ff7fdfed8c09120 0xbfffffffdc00000f 0xcbfffffffdc00000

def z850 : W := mkw 0x9b3fdf6d80000001 0x09b3fdf6d8000000 0xbf9fff3fc000000f 0xcbf9fff3fc000000

def z851 : W := mkw 0xff7fdfed9cc9d301 0xaff7fdfed9cc9d30 0xffffffffdcc1c30f 0xcffffffffdcc1c30

def z852 : W := mkw 0x2dc01d8036801aa0 0x42dc01d8036801aa 0xffe71fc03ff1ffff 0xfffe71fc03ff1fff

def z853 : W := mkw 0x008020126376acd8 0x1008020126376acd 0x0000000023fe3cf0 0x30000000023fe3cf

def z854 : W := mkw 0x2cc0148036801aa0 0x42cc0148036801aa 0xffe006c03fc03fff 0x3ffe006c03fc03ff

def z855 : W := mkw 0x00236270c170e158 0x000236270c170e15 0x407fffffc3f1e3ff 0xe407fffffc3f1e3f

def z856 : W := mkw 0xf6fee040bbed8000 0x8f6fee040bbed800 0xffffe1c1ffffc00f 0xbffffe1c1ffffc00

def z857 : W := mkw 0x09011fbf44127fe0 0x709011fbf44127fe 0x00001fffc0003ff0 0x400001fffc0003ff

def z858 : W := mkw 0x00236272c172e558 0x000236272c172e55 0x407fe7ffc3ffe3f7 0xe407fe7ffc3ffe3f

def z859 : W := mkw 0xbf7fdfed84001201 0x0bf7fdfed8400120 0xffffffffffc03fff 0xfffffffffffc03ff

def z860 : W := mkw 0x0080201273b62ce0 0x50080201273b62ce 0x0000000023fe3cf0 0x30000000023fe3cf

def z861 : W := mkw 0xbf7fdfed80000001 0x0bf7fdfed8000000 0xbffffeffc000000a 0x8bffffeffc000000

def z862 : W := mkw 0x5815163a0c1b7700 0x25815163a0c1b770 0xf87f1efe3cffff3e 0xff87f1efe3cffff3

def z863 : W := mkw 0x0388a91763362cc0 0x10388a91763362cc 0x07f8ffffe33e3ccf 0xf07f8ffffe33e3cc

def z864 : W := mkw 0x0388a91763362cc0 0x10388a91763362cc 0x47f8f93fe3fe3ccf 0xf47f8f93fe3fe3cc

def z865 : W := mkw 0x5815163a0c1b7700 0x25815163a0c1b770 0xf81fff3ffc3fff0f 0xff81fff3ffc3fff0

def z866 : W := mkw 0xbf7fdfed80000001 0x0bf7fdfed8000000 0xffffffffc031c00f 0xeffffffffc031c00

def z867 : W := mkw 0x0308890500000000 0x0030889050000000 0x0798f93fe03e000d 0xf0798f93fe03e000

def z868 : W := mkw 0x008020126376edd8 0x1008020126376edd 0x00000000233ffcc0 0x300000000233ffcc

def z869 : W := mkw 0x5814141a0c1b7700 0x25814141a0c1b770 0xf81f180e3c3fff0e 0xbf81f180e3c3fff0

def z870 : W := mkw 0x00236272c176e558 0x100236272c176e55 0x4067e7f1c3ffe3f7 0xe4067e7f1c3ffe3f

def z871 : W := mkw 0x5815167acc1b7758 0x25815167acc1b775 0xf87f1fffffffffff 0xff87f1ffffffffff

def z872 : W := mkw 0xff7fdfed98c98001 0x8ff7fdfed98c9800 0xfffffffffcffc00f 0xffffffffffcffc00

def z873 : W := mkw 0x0080201263362cc0 0x10080201263362cc 0x00000000033e00c0 0x000000000033e00c

def z874 : W := mkw 0x408020127ffff758 0xa408020127ffff75 0x400000003ffffff0 0x3400000003ffffff

def z875 : W := mkw 0x2dc01d8d36801aa1 0x42dc01d8d36801aa 0xffe01fce3fc03fff 0x7ffe01fce3fc03ff

def z876 : W := mkw 0x002342608040c118 0x0002342608040c11 0x4067e7f1c3c1e3f7 0xe4067e7f1c3c1e3f

def z877 : W := mkw 0x5815163a0c1b7700 0x25815163a0c1b770 0xf87f1e3e3fffff0f 0xff87f1e3e3fffff0

def z878 : W := mkw 0xffdc9d8f3e8b1ea1 0x6ffdc9d8f3e8b1ea 0xbf98180e3c0e1c08 0x1bf98180e3c0e1c0

def z879 : W := mkw 0xff7fdfed88094101 0x2ff7fdfed8809410 0xbfffffffc001c00f 0xcbfffffffc001c00

def z880 : W := mkw 0x408020126b3f2cc0 0x1408020126b3f2cc 0x400000003f3ffcc0 0x3400000003f3ffcc

def z881 : W := mkw 0xb77fcbed80000001 0x0b77fcbed8000000 0x079fe03fc0000000 0x8079fe03fc000000

def z882 : W := mkw 0x9b3fdfed80000001 0x09b3fdfed8000000 0x079fffffc000000d 0xc079fffffc000000

def z883 : W := mkw 0x2dc01d8036801aa0 0x42dc01d8036801aa 0xfff81fc03ffe3fff 0xffff81fc03ffe3ff

def z884 : W := mkw 0x00236272c172e558 0x000236272c172e55 0x4067ffffc3f1fff7 0xe4067ffffc3f1fff

def z885 : W := mkw 0x0080201277f6fff8 0x50080201277f6fff 0x400000003ffffff0 0x3400000003ffffff

def z886 : W := mkw 0x09011ff7c4127ff8 0x509011ff7c4127ff 0x00001fffc0003ff0 0x400001fffc0003ff

def z887 : W := mkw 0x2cc0140036801200 0x02cc014003680120 0xffe01fc03fc03fff 0x7ffe01fc03fc03ff

def z888 : W := mkw 0xd23fe27ac97fe558 0xad23fe27ac97fe55 0x001fe03fc03fc000 0x8001fe03fc03fc00

def z889 : W := mkw 0xbf7fdfed80000881 0x0bf7fdfed8000088 0xbfffffffc0003ccf 0xcbfffffffc0003cc

def z890 : W := mkw 0xbf7fdfed84005301 0x2bf7fdfed8400530 0xbfffffffc000030f 0xcbfffffffc000030

def z891 : W := mkw 0x74d400003a890000 0x074d400003a89000 0xff9f00003c3fc00e 0xbff9f00003c3fc00

def z892 : W := mkw 0xbf7fdfed90c08001 0x8bf7fdfed90c0800 0xbfffffffc0c0000f 0xcbfffffffc0c0000

def z893 : W := mkw 0xff7fdfed880d0001 0x8ff7fdfed880d000 0xbfffffffc00e000f 0xcbfffffffc00e000

def z894 : W := mkw 0xa7eae9c5f3e488c1 0x9a7eae9c5f3e488c 0x07e0e1c1c3c000c1 0x007e0e1c1c3c000c

def z895 : W := mkw 0x5814140a0c0b1600 0x25814140a0c0b160 0xf81f1e0e3c3fff0e 0xff81f1e0e3c3fff0

def z896 : W := mkw 0xff7fdfed98c9c119 0x8ff7fdfed98c9c11 0xffffffffdcc1c33f 0xcffffffffdcc1c33

def z897 : W := mkw 0x0880341267363ec0 0x10880341267363ec 0xf8001e003f3e3fce 0x7f8001e003f3e3fc

def z898 : W := mkw 0xfc7756e89c895321 0x6fc7756e89c89532 0xf86706c01cc1c332 0x0f86706c01cc1c33

def z899 : W := mkw 0x0080201267363ee0 0x50080201267363ee 0x00000000233e3ff0 0x300000000233e3ff

def z900 : W := mkw 0x5815163a0c1b7700 0x25815163a0c1b770 0xb81f1e3e3c3fff08 0xdb81f1e3e3c3fff0

def z901 : W := mkw 0x2dc01d8036801aa0 0x42dc01d8036801aa 0xffe0fff1ffc03fff 0xfffe0fff1ffc03ff

def z902 : W := mkw 0x2dc01d8536801aa0 0x42dc01d8536801aa 0xffe01fffffc03fff 0x7ffe01fffffc03ff

def z903 : W := mkw 0xbf5d9fed80000001 0x0bf5d9fed8000000 0xbf98ffffc000000d 0xcbf98ffffc000000

def z904 : W := mkw 0x408020127bffa440 0x9408020127bffa44 0x400000003fffc000 0x3400000003fffc00

def z905 : W := mkw 0x5814140a0c0b1600 0x25814140a0c0b160 0xb81f180e3c3fdc08 0x9b81f180e3c3fdc0

def z906 : W := mkw 0xbf7fdfed84001201 0x0bf7fdfed8400120 0xbffffffffc001c0f 0xdbffffffffc001c0

def z907 : W := mkw 0x933fcb6d80000001 0x0933fcb6d8000000 0x079fe13fc0000001 0x8079fe13fc000000

def z908 : W := mkw 0x5814141a0c1b3600 0x25814141a0c1b360 0xf81f183e3c3ffc0e 0xff81f183e3c3ffc0

def z909 : W := mkw 0xf6dca0003bed8000 0x8f6dca0003bed800 0xff9f00003fffc00e 0xbff9f00003fffc00

def z910 : W := mkw 0x032ac90500000000 0x0032ac9050000000 0x07fff93fc000000f 0xc07fff93fc000000

def z911 : W := mkw 0x00236270c170e158 0x000236270c170e15 0x407fe7f1e3ffe3ff 0xf407fe7f1e3ffe3f

def z912 : W := mkw 0x5815167acc1b7758 0x25815167acc1b775 0xf81f1e3ffc3fff0e 0xff81f1e3ffc3fff0

def z913 : W := mkw 0x26eae00033e48000 0x026eae00033e4800 0xffffe0003fffc00f 0xbffffe0003fffc00

def z914 : W := mkw 0x0080201263362cc0 0x10080201263362cc 0x00001800233e3ccc 0x700001800233e3cc

def z915 : W := mkw 0x09011fffc4127fc1 0x309011fffc4127fc 0x00001fffc0003fc0 0x400001fffc0003fc

def z916 : W := mkw 0xbf7fdfed80004119 0x0bf7fdfed8000411 0xbfffffffc000033f 0xcbfffffffc000033

def z917 : W := mkw 0x0180291263362cc0 0x10180291263362cc 0x00001900233e3cc0 0x700001900233e3cc

def z918 : W := mkw 0xff7fdfed98890001 0x8ff7fdfed9889000 0xbfffffffdc00000f 0xcbfffffffdc00000

def z919 : W := mkw 0x5815163a0c1b7700 0x25815163a0c1b770 0xf87f1ffe3c3fff0f 0xff87f1ffe3c3fff0

def z920 : W := mkw 0xffdc9d873e8f1ea0 0xdffdc9d873e8f1ea 0xbf98180e3c0e1c08 0x1bf98180e3c0e1c0

def z921 : W := mkw 0xaf6bdfed80000001 0x0af6bdfed8000000 0x07e7ffffc0000007 0xc07e7ffffc000000

def z922 : W := mkw 0x24c0000036801aa0 0x424c0000036801aa 0xffe007c03fc03fff 0x7ffe007c03fc03ff

def z923 : W := mkw 0xff7fdfed8c095301 0x2ff7fdfed8c09530 0xfffffffffc01ff0f 0xffffffffffc01ff0

def z924 : W := mkw 0x933ec90500000000 0x0933ec9050000000 0x079ff93fc000000d 0xc079ff93fc000000

def z925 : W := mkw 0x5815163a0c1b7700 0x25815163a0c1b770 0xb81f1e3e3c3fdc0e 0xdb81f1e3e3c3fdc0

def z926 : W := mkw 0xfc7756689cc9d318 0xafc7756689cc9d31 0xf86706c01cc1c332 0x0f86706c01cc1c33

def z927 : W := mkw 0x0308a91741362440 0x10308a9174136244 0x0798f93fe03e3c0d 0xf0798f93fe03e3c0

def z928 : W := mkw 0x0080201267367fc0 0x30080201267367fc 0x00000000233e3fc0 0x300000000233e3fc

def z929 : W := mkw 0x0388a90763260cc0 0x10388a90763260cc 0x0798f93fe30e1ccd 0xd0798f93fe30e1cc

def z930 : W := mkw 0x00236270c170e158 0x000236270c170e15 0x4067fff1e3f1ffff 0xf4067fff1e3f1fff

def z931 : W := mkw 0x931c890d00000001 0x0931c890d0000000 0x0798f93fc000000d 0xc0798f93fc000000

def z932 : W := mkw 0x0288a01263362440 0x00288a0126336244 0x0798f93fe33e3ccd 0xf0798f93fe33e3cc

def z933 : W := mkw 0x0388a91763366dd8 0x10388a91763366dd 0x0798f93fe33e3ffd 0xf0798f93fe33e3ff

def z934 : W := mkw 0x0388a91763362cc0 0x10388a91763362cc 0x0798f93fe30e3cc9 0x50798f93fe30e3cc

def z935 : W := mkw 0x408020126f3f3ec0 0x3408020126f3f3ec 0x000000003f3e3cc0 0x3000000003f3e3cc

def z936 : W := mkw 0xf4f640003ac98000 0x8f4f640003ac9800 0xffff00003fffc00f 0xbffff00003fffc00

def z937 : W := mkw 0xbf7fdfed80000001 0x0bf7fdfed8000000 0x07ffffffc0000001 0xc07ffffffc000000

def z938 : W := mkw 0xbf7fdfed94801221 0x4bf7fdfed9480122 0xfffffffffcc03f3f 0xffffffffffcc03f3

def z939 : W := mkw 0x131c890500000000 0x0131c89050000000 0xbf9ff93fc000000f 0xcbf9ff93fc000000

def z940 : W := mkw 0xf6fee0003bed8000 0x8f6fee0003bed800 0xffffe1003fffe0cf 0xfffffe1003fffe0c

def z941 : W := mkw 0x0388a91763362cc0 0x10388a91763362cc 0x0798f93fe33e1cc9 0x90798f93fe33e1cc

def z942 : W := mkw 0xf6fee0003bed8000 0x8f6fee0003bed800 0xffffe0001fffc003 0x8ffffe0001fffc00

def z943 : W := mkw 0x00236260c160c158 0x000236260c160c15 0x4067e7c1c3f1c3f7 0xa4067e7c1c3f1c3f

def z944 : W := mkw 0x0388a91763362cc0 0x10388a91763362cc 0x4798ff3fe33e3fcf 0xf4798ff3fe33e3fc

def z945 : W := mkw 0xbf7fdfed94c0d339 0x4bf7fdfed94c0d33 0xffffffffdcc1c33f 0xcffffffffdcc1c33

def z946 : W := mkw 0x49813fedbbed8001 0x849813fedbbed800 0x40001fffffffc000 0x740001fffffffc00

def z947 : W := mkw 0x523fe27fc97fe558 0x3523fe27fc97fe55 0x001fe03fc03fc000 0x8001fe03fc03fc00

def z948 : W := mkw 0xbf7eddcd80000001 0x0bf7eddcd8000000 0xbff8f9ffc000000d 0xcbff8f9ffc000000

def z949 : W := mkw 0x0308890700020400 0x0030889070002040 0x0798f93fe00e1c0d 0xd0798f93fe00e1c0

def z950 : W := mkw 0xb77fcbed80000001 0x0b77fcbed8000000 0x07fff9ffc000000d 0xc07fff9ffc000000

def z951 : W := mkw 0x2f499fed80000001 0x02f499fed8000000 0xbff8ffffc000000f 0xcbff8ffffc000000

def z952 : W := mkw 0x501400120c1b7700 0x2501400120c1b770 0xf81f183e3c3fff0e 0xff81f183e3c3fff0

def z953 : W := mkw 0x030889c580000001 0x0030889c58000000 0x0798f9ffc000000d 0xc0798f9ffc000000

def z954 : W := mkw 0x0388a91763362cc0 0x10388a91763362cc 0x4798f93fe3fe3ffd 0xf4798f93fe3fe3ff

def z955 : W := mkw 0x0388a91763362cc0 0x10388a91763362cc 0x0798ffffe33e3ffd 0xf0798ffffe33e3ff

def z956 : W := mkw 0x5815163a0c1b7700 0x25815163a0c1b770 0xf81f1e0e3c3fff0a 0x3f81f1e0e3c3fff0

def z957 : W := mkw 0xf6fee0003bed8000 0x8f6fee0003bed800 0xffffe0003fffe3ff 0xbffffe0003fffe3f

def z958 : W := mkw 0xbf7fdfed80000001 0x0bf7fdfed8000000 0xbfffffffe03e000f 0xfbfffffffe03e000

def z959 : W := mkw 0xff7fdfed88090001 0x0ff7fdfed8809000 0xbffffffffc0e000f 0xdbffffffffc0e000

def z960 : W := mkw 0xaf6bdfed80000001 0x0af6bdfed8000000 0x07f8ffffc000000d 0xc07f8ffffc000000

def z961 : W := mkw 0x0388a90523240880 0x00388a9052324088 0x0798f93fe33e3ccd 0xf0798f93fe33e3cc

def z962 : W := mkw 0x0288a01763362440 0x10288a0176336244 0x0798f83fe33e3c0d 0xf0798f83fe33e3c0

def z963 : W := mkw 0x09011f3a04127f80 0x209011f3a04127f8 0x00001f3e00003fc0 0x400001f3e00003fc

def z964 : W := mkw 0x5015023a081b6500 0x25015023a081b650 0xf81f183e3c3ffc0e 0xff81f183e3c3ffc0

def z965 : W := mkw 0x09803d9267363ee0 0x509803d9267363ee 0x00001fc0233e3ff0 0x700001fc0233e3ff

def z966 : W := mkw 0xa76ac9c580000001 0x0a76ac9c58000000 0x07e0f9ffc0000001 0x407e0f9ffc000000

def z967 : W := mkw 0xf6fee040fbed8058 0x8f6fee040fbed805 0xffffe7c1ffffe3ff 0xfffffe7c1ffffe3f

def z968 : W := mkw 0xff7fdfed8c095301 0x2ff7fdfed8c09530 0xfffffffffc3fc30f 0xffffffffffc3fc30

def z969 : W := mkw 0x0388a91773f6acc0 0x90388a91773f6acc 0x0798f93fe3fe3ccd 0xf0798f93fe3fe3cc

def z970 : W := mkw 0x0388a91763366dc0 0x10388a91763366dc 0x4798f93fe33fffcd 0xf4798f93fe33fffc

def z971 : W := mkw 0x0388a99763362ce0 0x50388a99763362ce 0x0798f9ffe33e3cfd 0xf0798f9ffe33e3cf

def z972 : W := mkw 0x2f489d8500000000 0x02f489d850000000 0xbf98f93fc000000d 0xcbf98f93fc000000

def z973 : W := mkw 0xf6fee045bbed8001 0x8f6fee045bbed800 0xffffe001ffffc00f 0xbffffe001ffffc00

def z974 : W := mkw 0x0308890500000880 0x0030889050000088 0x0798f93fc0003ccd 0xc0798f93fc0003cc

def z975 : W := mkw 0xf6fee0003bed8000 0x8f6fee0003bed800 0xffffe1c03fffc0ff 0xbffffe1c03fffc0f

def z976 : W := mkw 0xbf7fdfed80000001 0x0bf7fdfed8000000 0xbffff83fc000000f 0x8bffff83fc000000

def z977 : W := mkw 0x00236260c160c158 0x000236260c160c15 0x4067e7c1c3c1e3f7 0x64067e7c1c3c1e3f

def z978 : W := mkw 0xff7fdfed88090001 0x0ff7fdfed8809000 0xffffffffdc01c00f 0xcffffffffdc01c00

def z979 : W := mkw 0x2cc0349277b63ee0 0x52cc0349277b63ee 0xf86006c03ffe3ff2 0x3f86006c03ffe3ff

def z980 : W := mkw 0x3f5d9fad00000000 0x03f5d9fad0000000 0xbfffffffc000000f 0xcbfffffffc000000

def z981 : W := mkw 0xa76ac9c580000001 0x0a76ac9c58000000 0x07f8e1ffc0000001 0x807f8e1ffc000000

def z982 : W := mkw 0x00236270c170e158 0x000236270c170e15 0x4067e7c1c3f1e3f3 0x24067e7c1c3f1e3f

def z983 : W := mkw 0x0388a91763362cc0 0x10388a91763362cc 0x07f8f9ffe3fe3cfd 0xf07f8f9ffe3fe3cf

def z984 : W := mkw 0xf6fee0003bed8000 0x8f6fee0003bed800 0xbfffe0003c3fc00f 0x9bfffe0003c3fc00

def z985 : W := mkw 0x408020127fbf7fe0 0x7408020127fbf7fe 0x400000003ffffff0 0x3400000003ffffff

def z986 : W := mkw 0xff7fdfed88498001 0x8ff7fdfed8849800 0xbfffffffc001c00f 0xcbfffffffc001c00

def z987 : W := mkw 0xf6fee040bbed8018 0x8f6fee040bbed801 0xffffe0c03fffc03f 0xbffffe0c03fffc03

def z988 : W := mkw 0x0080201263362cc0 0x10080201263362cc 0x00000100233e3cc5 0x700000100233e3cc

def z989 : W := mkw 0xbf7fdfed80000001 0x0bf7fdfed8000000 0xbf9fffffc0000008 0xcbf9fffffc000000

def z990 : W := mkw 0x5815163a0c1b7700 0x25815163a0c1b770 0xf81f183e3c3fff08 0xbf81f183e3c3fff0

def z991 : W := mkw 0x5815163a0c1b7700 0x25815163a0c1b770 0xf81f1ffe3c3ffffe 0xff81f1ffe3c3ffff

def z992 : W := mkw 0xf6fee0003bed8000 0x8f6fee0003bed800 0xfffff8003ffffc0f 0xffffff8003ffffc0

def z993 : W := mkw 0x0080201263362440 0x1008020126336244 0x00000000233e0000 0x300000000233e000

def z994 : W := mkw 0xff7fdfed88090001 0x0ff7fdfed8809000 0xbfffffffc03fc00f 0xcbfffffffc03fc00

def z995 : W := mkw 0x2f6bdfe580000000 0x02f6bdfe58000000 0xbfffffffc000000f 0xcbfffffffc000000

def z996 : W := mkw 0x2dc01d8036801aa0 0x42dc01d8036801aa 0xffe01fc01fc03ff3 0x4ffe01fc01fc03ff

def z997 : W := mkw 0x0388890722060c80 0x10388890722060c8 0x0798f83fe00e1c08 0x90798f83fe00e1c0

def z998 : W := mkw 0xa76ac90500000000 0x0a76ac9050000000 0x07f8f93fc000000d 0xc07f8f93fc000000

def z999 : W := mkw 0xf77ec90518c98000 0x8f77ec90518c9800 0xfffff93fdcc1c00f 0xcfffff93fdcc1c00

def z1000 : W := mkw 0xf6fec0003a890000 0x0f6fec0003a89000 0xffffe0003fffc00f 0xbffffe0003fffc00

def z1001 : W := mkw 0x0801163204127700 0x0080116320412770 0xf81f1e3e3c3fff0e 0xff81f1e3e3c3fff0

def z1002 : W := mkw 0xfc7756e89cc99221 0xcfc7756e89cc9922 0xf86706c01cc1c332 0x0f86706c01cc1c33

def z1003 : W := mkw 0x0388891722122c80 0x00388891722122c8 0x0798f93fe33e3ccd 0xf0798f93fe33e3cc

def z1004 : W := mkw 0x5815163a0c1b7700 0x25815163a0c1b770 0xf81f1f3e3f3fffcf 0xff81f1f3e3f3fffc

def z1005 : W := mkw 0xb77fcb6580000000 0x0b77fcb658000000 0xbfffffffc000000f 0xcbfffffffc000000

def z1006 : W := mkw 0x529c80002a0d0000 0x0529c80002a0d000 0xff9f00003c3fc00e 0xbff9f00003c3fc00

def z1007 : W := mkw 0x008020126376acc0 0x1008020126376acc 0x4000000023fffcc0 0x34000000023fffcc

def z1008 : W := mkw 0x0b099fed80000001 0x00b099fed8000000 0x0780ffffc0000001 0x40780ffffc000000

def z1009 : W := mkw 0x5815162a0c0b5700 0x25815162a0c0b570 0xf81f1e0e3c3fdf0e 0xbf81f1e0e3c3fdf0

def z1010 : W := mkw 0xf6fec0003a8d0000 0x8f6fec0003a8d000 0xffffe0003c3fc00f 0xbffffe0003c3fc00

def z1011 : W := mkw 0xbf7fdfed80408019 0x0bf7fdfed8040801 0xbfffffffc0c0003f 0xcbfffffffc0c0003

def z1012 : W := mkw 0x0080201263362cc0 0x10080201263362cc 0x406007c023fe3ff7 0x7406007c023fe3ff

def z1013 : W := mkw 0x002260104170a040 0x0002260104170a04 0x4067e7f1c3f1e3f7 0xe4067e7f1c3f1e3f

def z1014 : W := mkw 0x2dc01d8036801aa0 0x42dc01d8036801aa 0xffe01ec03fc03ffa 0x3ffe01ec03fc03ff

def z1015 : W := mkw 0xa7eae98573e488e0 0xda7eae98573e488e 0x07e0e1c1c3c000f1 0x007e0e1c1c3c000f

def z1016 : W := mkw 0x09011f3f04127f80 0x309011f3f04127f8 0x00001e3e00003f00 0x400001e3e00003f0

def z1017 : W := mkw 0x0180291263322cc0 0x00180291263322cc 0x0798f93fe33e3ccd 0xf0798f93fe33e3cc

def z1018 : W := mkw 0x2f489d8514801220 0x42f489d851480122 0xfff8ffffdcc0033f 0xcfff8ffffdcc0033

def z1019 : W := mkw 0x00236270c170e158 0x000236270c170e15 0x4067e7f1c3c1e3f3 0x44067e7f1c3c1e3f

def z1020 : W := mkw 0xf6fee0003bed8000 0x8f6fee0003bed800 0xff9fe0003c3fc00e 0xbff9fe0003c3fc00

def z1021 : W := mkw 0x5815163a0c1b7700 0x25815163a0c1b770 0xf81f183e3c3fdc0e 0xbf81f183e3c3fdc0

def z1022 : W := mkw 0x74f660003be98000 0x074f660003be9800 0xffffe0003fffc00f 0xbffffe0003fffc00

def z1023 : W := mkw 0x509400002a090000 0x0509400002a09000 0xff9f00003f3fc00f 0xbff9f00003f3fc00

def z1024 : W := mkw 0xf6fee0003bed88a0 0xcf6fee0003bed88a 0xffffe0003fffc0ff 0xbffffe0003fffc0f

def z1025 : W := mkw 0xfc7756e88c49d319 0x2fc7756e88c49d31 0xf86706c01cc1c332 0x0f86706c01cc1c33

def z1026 : W := mkw 0xb77fcbed80000001 0x0b77fcbed8000000 0xbfffe1ffc000000f 0x8bfffe1ffc000000

def z1027 : W := mkw 0x00226040c1608058 0x000226040c160805 0x4067e7c1c3f1e3f7 0xe4067e7c1c3f1e3f

def z1028 : W := mkw 0xbf7fdfed80000001 0x0bf7fdfed8000000 0xbfffffffc3c000ff 0xcbfffffffc3c000f

def z1029 : W := mkw 0x032ac94580000000 0x0032ac9458000000 0x07f8f9ffc000000d 0xc07f8f9ffc000000

def z1030 : W := mkw 0xbf7edd8500000000 0x0bf7edd850000000 0xbfffffffc000000f 0xcbfffffffc000000

def z1031 : W := mkw 0xf6fee0053bed8000 0x8f6fee0053bed800 0xffffe03fffffc00f 0xbffffe03fffffc00

def z1032 : W := mkw 0xbf5c9d8d00000001 0x0bf5c9d8d0000000 0xbff8ffffc000000f 0xcbff8ffffc000000

def z1033 : W := mkw 0xbf7fdfed84001201 0x0bf7fdfed8400120 0xffffffffdc00030f 0xcffffffffdc00030

def z1034 : W := mkw 0xff7fdfed8c091201 0x0ff7fdfed8c09120 0xfffffffffc3fff0f 0xffffffffffc3fff0

def z1035 : W := mkw 0x03098b6580000000 0x003098b658000000 0x0798ffffc000000d 0xc0798ffffc000000

def z1036 : W := mkw 0xbf7fdfed80000001 0x0bf7fdfed8000000 0xfffffffffc00000f 0xffffffffffc00000

def z1037 : W := mkw 0x0388a9176376edd8 0x10388a9176376edd 0x47f8ffffe3ffffff 0xf47f8ffffe3fffff

def z1038 : W := mkw 0x7c7756e89cc9d338 0x67c7756e89cc9d33 0xf86706c01cc1c332 0x0f86706c01cc1c33

def z1039 : W := mkw 0x0388a91763362cc0 0x10388a91763362cc 0x479ff93fe33ffccf 0xf479ff93fe33ffcc

def z1040 : W := mkw 0x5815162a0c0b1600 0x25815162a0c0b160 0xf81f1e3e3c3fdc0e 0xff81f1e3e3c3fdc0

def z1041 : W := mkw 0x0080201273b62cc0 0x10080201273b62cc 0x400000003ffe3cc0 0x3400000003ffe3cc

def z1042 : W := mkw 0xbf7fdfed80000001 0x0bf7fdfed8000000 0xffffffffc0c0033f 0xcffffffffc0c0033

def z1043 : W := mkw 0x581516ba0c1b7720 0x6581516ba0c1b772 0xf81f1efe3c3fff3e 0xff81f1efe3c3fff3

def z1044 : W := mkw 0xfc7756e88c091201 0x2fc7756e88c09120 0xb86706c01c000002 0x0b86706c01c00000

def z1045 : W := mkw 0xbf7fdfed80004101 0x0bf7fdfed8000410 0xffffffffc001c30f 0xcffffffffc001c30

def z1046 : W := mkw 0x1b3fdf6d80000000 0x01b3fdf6d8000000 0xbfffffffc000000f 0xcbfffffffc000000

def z1047 : W := mkw 0x0388a90723260c80 0x10388a90723260c8 0x0798f93fe33e1c0d 0xf0798f93fe33e1c0

def z1048 : W := mkw 0x032bcb6580000000 0x0032bcb658000000 0x079ff93fc000000d 0xc079ff93fc000000

def z1049 : W := mkw 0xbe7fd66880000000 0x0be7fd6688000000 0xbfffffffc000000f 0xcbfffffffc000000

def z1050 : W := mkw 0xbf7fdfed90800001 0x0bf7fdfed9080000 0xffffffffdcc0000f 0xcffffffffdcc0000

def z1051 : W := mkw 0x131d8b2d00000000 0x0131d8b2d0000000 0x079ff93fc000000d 0xc079ff93fc000000

def z1052 : W := mkw 0x581414120c1b3600 0x0581414120c1b360 0xf81f1e3e3c3fff0e 0xff81f1e3e3c3fff0

def z1053 : W := mkw 0x0308890500000000 0x0030889050000000 0x0798e13fc0000001 0x80798e13fc000000

def z1054 : W := mkw 0x408020127fffffc0 0xb408020127fffffc 0x400000003fffffc0 0x3400000003fffffc

def z1055 : W := mkw 0x0388a91763362cc0 0x10388a91763362cc 0x0798f93fe03e1c0d 0xd0798f93fe03e1c0

def z1056 : W := mkw 0xa748898500000001 0x0a74889850000000 0x0798f93fc000000d 0xc0798f93fc000000

def z1057 : W := mkw 0x0388a91763362cc0 0x10388a91763362cc 0x0798f83fe33e1c0d 0xb0798f83fe33e1c0

def z1058 : W := mkw 0x0080201267363ec0 0x10080201267363ec 0x400000003f3e3fc0 0x3400000003f3e3fc

def z1059 : W := mkw 0x0388a91763362cc0 0x10388a91763362cc 0x0798f93fe03e3cc8 0xd0798f93fe03e3cc

def z1060 : W := mkw 0x0388a91763362cc0 0x10388a91763362cc 0x0798f83fe33e3cc8 0xb0798f83fe33e3cc

def z1061 : W := mkw 0x2d635fed80000001 0x02d635fed8000000 0xbfe7ffffc000000f 0xcbfe7ffffc000000

def z1062 : W := mkw 0x5815163a081b2400 0x05815163a081b240 0xf81f1e3e3c3ffc0e 0xff81f1e3e3c3ffc0

def z1063 : W := mkw 0x408020127bffedd8 0x9408020127bffedd 0x400000003ffffff0 0x3400000003ffffff

def z1064 : W := mkw 0x0388891762162cc0 0x10388891762162cc 0x0798f93fe00e3ccd 0xd0798f93fe00e3cc

def z1065 : W := mkw 0x00236270c170e158 0x000236270c170e15 0x4067e7f1c3f1c3f3 0x84067e7f1c3f1c3f

def z1066 : W := mkw 0x0080201263366dd8 0x10080201263366dd 0x00000000233e3ff0 0x300000000233e3ff

def z1067 : W := mkw 0x0023627ac172e558 0x20023627ac172e55 0x4067e7ffc3f1e3f7 0xe4067e7ffc3f1e3f

def z1068 : W := mkw 0xbf7fdfed84001aa1 0x4bf7fdfed84001aa 0xfffffffffc003fff 0xffffffffffc003ff

def z1069 : W := mkw 0x09011fba04127fa0 0x609011fba04127fa 0x00001e3e00003f00 0x400001e3e00003f0

def z1070 : W := mkw 0xbf7fdfed8040c119 0x0bf7fdfed8040c11 0xffffffffc3c1e3ff 0xeffffffffc3c1e3f

def z1071 : W := mkw 0x0023626081608000 0x0002362608160800 0x4067e7f1c3f1e3f7 0xe4067e7f1c3f1e3f

def z1072 : W := mkw 0x09011fbf04127701 0x209011fbf0412770 0x00001e3e00003f00 0x400001e3e00003f0

def z1073 : W := mkw 0x52bee0002b6d8000 0x052bee0002b6d800 0xffffe0003fffc00f 0xbffffe0003fffc00

def z1074 : W := mkw 0x0001223041306140 0x0000122304130614 0x4067e7f1c3f1e3f7 0xe4067e7f1c3f1e3f

def z1075 : W := mkw 0x408020126b3f6dc0 0x3408020126b3f6dc 0x00000000233ffcc0 0x300000000233ffcc

def z1076 : W := mkw 0xbf7fdfed90800021 0x4bf7fdfed9080002 0xbfffffffc0c0003f 0xcbfffffffc0c0003

def z1077 : W := mkw 0xbf7fdfed80000001 0x0bf7fdfed8000000 0xbfe7ffffc0000003 0x4bfe7ffffc000000

def z1078 : W := mkw 0x0308890500000000 0x0030889050000000 0x0798f93fe0003c0d 0xf0798f93fe0003c0

def z1079 : W := mkw 0x0b089d0504001200 0x00b089d050400120 0xff98ff3ffc003f0f 0xfff98ff3ffc003f0

def z1080 : W := mkw 0xbf5c9d8d00000001 0x0bf5c9d8d0000000 0xbf98f83fc0000008 0x8bf98f83fc000000

def z1081 : W := mkw 0xf6fee0003bed8000 0x8f6fee0003bed800 0xffffe0003cffc00a 0x9ffffe0003cffc00

def z1082 : W := mkw 0x933fcb6d80000001 0x0933fcb6d8000000 0x07ffffffc000000f 0xc07ffffffc000000

def z1083 : W := mkw 0x0b2bdfed80000001 0x00b2bdfed8000000 0x07ffffffc000000f 0xc07ffffffc000000

def z1084 : W := mkw 0x0080201263362cc0 0x10080201263362cc 0x0000000003003cc0 0x00000000003003cc

def z1085 : W := mkw 0xbf7fdfed80000001 0x0bf7fdfed8000000 0xbf9ff93fc000000d 0xcbf9ff93fc000000

def z1086 : W := mkw 0xff7fdfed9c895321 0x6ff7fdfed9c89532 0xffffffffdcc1c33f 0xcffffffffdcc1c33

def z1087 : W := mkw 0x1b1d9fed80000001 0x01b1d9fed8000000 0xbf9fffffc000000f 0xcbf9fffffc000000

def z1088 : W := mkw 0x0388a9176376acd8 0x10388a9176376acd 0x0798f93fe3fe3cfd 0xf0798f93fe3fe3cf

def z1089 : W := mkw 0x5815163a4c1b7758 0x25815163a4c1b775 0xf81f1e3e3c3ffffe 0xff81f1e3e3c3ffff

def z1090 : W := mkw 0x408020127ffbfff8 0x6408020127ffbfff 0x400000003ffffff0 0x3400000003ffffff

def z1091 : W := mkw 0xbf7fdfed94801aa1 0x4bf7fdfed94801aa 0xffffffffdcc03fff 0xcffffffffdcc03ff

def z1092 : W := mkw 0x923fc26d80000001 0x0923fc26d8000000 0x079fe03fc000000d 0x8079fe03fc000000

def z1093 : W := mkw 0xbe7fd66d80000001 0x0be7fd66d8000000 0xbffffe3fc000000f 0xcbffffe3fc000000

def z1094 : W := mkw 0xf6fee0003bed8000 0x8f6fee0003bed800 0xbf9fe0003f3fc00d 0xbbf9fe0003f3fc00

def z1095 : W := mkw 0xbf7fdfed84001201 0x0bf7fdfed8400120 0xbfffffffc0003f0f 0xcbfffffffc0003f0

def z1096 : W := mkw 0xbf7fdfed80000001 0x0bf7fdfed8000000 0xbfffffffe0003c0f 0xfbfffffffe0003c0

def z1097 : W := mkw 0xbf7fdfed80000001 0x0bf7fdfed8000000 0xbfffe7ffc0000003 0x8bfffe7ffc000000

def z1098 : W := mkw 0xf6fee0002b2d0000 0x0f6fee0002b2d000 0xffffe0003f3fc00f 0xbffffe0003f3fc00

def z1099 : W := mkw 0xf6fee0c0bbed8001 0x8f6fee0c0bbed800 0xffffe0c03fffc00f 0xbffffe0c03fffc00

def z1100 : W := mkw 0x0388a91773b62ce0 0x50388a91773b62ce 0x0798f93fe3fe3cfd 0xf0798f93fe3fe3cf

def z1101 : W := mkw 0xf6fee0007bed8040 0x8f6fee0007bed804 0xffffe101ffffc0cf 0xbffffe101ffffc0c

def z1102 : W := mkw 0x408020127fffbee0 0xd408020127fffbee 0x400000003ffffff0 0x3400000003ffffff

def z1103 : W := mkw 0xbf7fdfed80000001 0x0bf7fdfed8000000 0xffffffffc3c0000f 0xeffffffffc3c0000

def z1104 : W := mkw 0x0388a9176376edd8 0x10388a9176376edd 0x0798f93fe33ffccd 0xf0798f93fe33ffcc

def z1105 : W := mkw 0x0080201273f6acc0 0x90080201273f6acc 0x0000000023fe3cc0 0x30000000023fe3cc

def z1106 : W := mkw 0x5815163a0c1b7700 0x25815163a0c1b770 0xb81f183e3c3ffc0c 0xfb81f183e3c3ffc0

def z1107 : W := mkw 0xbf7fdfed8040c119 0x0bf7fdfed8040c11 0xbfffffffc001c00f 0xcbfffffffc001c00

def z1108 : W := mkw 0x50140002080b0400 0x050140002080b040 0xf81f180e3c3fdc0e 0xbf81f180e3c3fdc0

def z1109 : W := mkw 0x0080201277b63ee0 0x50080201277b63ee 0x000000003f3e3cc0 0x3000000003f3e3cc

def z1110 : W := mkw 0x0308a91741322440 0x00308a9174132244 0x0798f93fe33e3ccd 0xf0798f93fe33e3cc

def z1111 : W := mkw 0xaf6bdfed80000001 0x0af6bdfed8000000 0xbfe0ffffc000000f 0x4bfe0ffffc000000

def z1112 : W := mkw 0x5815163a4c1b7740 0x25815163a4c1b774 0xf81f1f3ffc3fffce 0xff81f1f3ffc3fffc

def z1113 : W := mkw 0xf6fee040fbed8058 0x8f6fee040fbed805 0xffffe001ffffc00f 0xbffffe001ffffc00

def z1114 : W := mkw 0x2748890500000000 0x0274889050000000 0xbff8f93fc000000f 0xcbff8f93fc000000

def z1115 : W := mkw 0x2748898500000000 0x0274889850000000 0x07f8f9ffc000000d 0xc07f8f9ffc000000

def z1116 : W := mkw 0x7454000008090000 0x0745400000809000 0xffff00003c3fc00f 0xbffff00003c3fc00

def z1117 : W := mkw 0xbf7fdf2d00000000 0x0bf7fdf2d0000000 0xbfffff3fc000000f 0xcbfffff3fc000000

def z1118 : W := mkw 0x832ac94580000001 0x0832ac9458000000 0x0798f93fc000000d 0xc0798f93fc000000

def z1119 : W := mkw 0x0388a91723362400 0x00388a9172336240 0x0798f93fe33e3c0d 0xf0798f93fe33e3c0

def z1120 : W := mkw 0xf6fec0003acd8000 0x8f6fec0003acd800 0xffff00003cffc00e 0xbffff00003cffc00

def z1121 : W := mkw 0x09011fba04127700 0x209011fba0412770 0x00001ffe00003f00 0x400001ffe00003f0

def z1122 : W := mkw 0xbf7fdfed80000001 0x0bf7fdfed8000000 0xbffff9ffc0000009 0x8bffff9ffc000000

def z1123 : W := mkw 0xbf7fdfed80000001 0x0bf7fdfed8000000 0xbff8ffffc0000009 0x4bff8ffffc000000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z0,z7,z1,z3,z4,z5,z6]),(0,[z0,z8,z1,z3,z9,z4,z6]),(0,[z0,z1,z3,z10,z4,z5,z6]),(0,[z11,z0,z1,z3,z4,z5,z6]),(0,[z0,z12,z1,z3,z4,z5,z6]),(0,[z13,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z14,z3,z4,z5,z6]),(0,[z0,z1,z3,z15,z4,z5,z6]),(0,[z0,z1,z16,z3,z4,z5,z6]),(0,[z0,z8,z1,z3,z4,z17,z6]),(0,[z0,z1,z3,z4,z18,z5,z6]),(0,[z0,z1,z3,z19,z5,z6,z20])],[(0,[z0,z8,z1,z21,z3,z4,z6]),(0,[z0,z1,z3,z4,z22,z5,z6]),(0,[z0,z23,z1,z3,z4,z5,z6])],[(0,[z0,z24,z25,z3,z4,z5,z6]),(0,[z26,z1,z3,z27,z4,z5,z6]),(0,[z28,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z29]),(0,[z0,z1,z3,z30,z4,z5,z6]),(0,[z0,z1,z31,z3,z4,z5,z6]),(0,[z0,z1,z3,z32,z4,z5,z6]),(0,[z0,z1,z33,z3,z4,z5,z6])],[(0,[z0,z25,z3,z34,z4,z5,z6]),(0,[z0,z35,z1,z3,z4,z5,z6]),(0,[z36,z0,z1,z3,z37,z5,z6]),(0,[z0,z38,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z39]),(0,[z0,z1,z3,z40,z4,z5,z6]),(0,[z0,z1,z3,z4,z41,z5,z6])],[(0,[z36,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z42,z5,z6]),(0,[z0,z43,z1,z3,z4,z5,z6]),(0,[z44,z0,z24,z1,z3,z4,z6]),(0,[z45,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z46,z4,z5,z6])],[(0,[z0,z24,z47,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z48]),(0,[z0,z49,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z50,z6]),(0,[z0,z51,z1,z3,z4,z5,z6]),(0,[z0,z52,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z53,z4,z5,z6]),(1,[z0,z1,z3,z4,z54,z6]),(0,[z0,z1,z3,z55,z4,z5,z6]),(0,[z0,z1,z56,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z57,z5,z6])]],
   [[(0,[z0,z24,z1,z3,z4,z58,z6]),(0,[z0,z3,z59,z4,z60,z5,z6])],[(0,[z0,z8,z1,z3,z4,z58,z6]),(0,[z0,z1,z3,z4,z61,z5,z6]),(0,[z0,z1,z3,z4,z5,z62,z6]),(0,[z0,z1,z3,z4,z63,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z64])],[(0,[z0,z1,z3,z4,z5,z65,z6]),(0,[z0,z1,z3,z4,z66,z5,z6]),(1,[z0,z8,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z67,z5,z6])],[(0,[z0,z1,z3,z68,z4,z5,z6]),(0,[z69,z0,z1,z3,z42,z5,z6]),(0,[z1,z3,z37,z4,z42,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z70]),(0,[z0,z1,z3,z71,z4,z5,z6]),(0,[z72,z0,z1,z3,z4,z5,z6])],[(0,[z0,z73,z1,z3,z4,z5,z6]),(0,[z74,z0,z8,z1,z3,z4,z6]),(0,[z0,z24,z1,z75,z3,z4,z6]),(0,[z0,z1,z3,z4,z5,z76,z6])],[(0,[z0,z1,z3,z4,z5,z6,z77]),(0,[z0,z1,z78,z3,z4,z5,z6]),(0,[z0,z8,z1,z1,z3,z4,z6]),(0,[z0,z79,z1,z3,z4,z5,z6]),(0,[z0,z1,z80,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z81])],[(0,[z0,z1,z3,z82,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z83]),(0,[z0,z1,z3,z4,z84,z85,z6]),(0,[z0,z1,z3,z86,z4,z5,z6])],[(0,[z0,z1,z87,z3,z4,z5,z6])]],
   [[(0,[z0,z24,z1,z3,z4,z88,z6]),(0,[z0,z24,z1,z3,z4,z89,z6]),(0,[z0,z1,z3,z4,z5,z90,z6]),(0,[z0,z1,z3,z4,z91,z5,z92])],[(0,[z0,z24,z1,z93,z3,z4,z6]),(0,[z0,z8,z1,z3,z4,z88,z6])],[(0,[z69,z0,z1,z3,z4,z5,z94]),(1,[z0,z1,z3,z4,z95,z6]),(1,[z0,z8,z24,z3,z4,z6]),(0,[z0,z8,z1,z93,z3,z4,z6]),(0,[z0,z96,z1,z3,z4,z5,z6])],[(0,[z26,z0,z1,z3,z4,z97,z6]),(0,[z0,z1,z3,z98,z4,z5,z6]),(1,[z0,z1,z3,z99,z4,z6]),(1,[z0,z100,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z17,z85,z6]),(0,[z0,z101,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z102,z5,z6])],[(1,[z0,z24,z47,z3,z4,z6]),(0,[z0,z8,z1,z103,z3,z4,z6]),(0,[z0,z1,z104,z3,z105,z4,z5])],[(0,[z0,z24,z1,z25,z3,z4,z6]),(0,[z0,z1,z3,z4,z5,z106,z6]),(0,[z0,z1,z3,z4,z107,z58,z6]),(0,[z0,z1,z3,z4,z5,z108,z6]),(0,[z0,z109,z1,z34,z4,z5,z6]),(0,[z0,z110,z8,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z5,z6,z111])],[(0,[z0,z112,z1,z3,z4,z5,z6]),(0,[z0,z1,z113,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z114]),(0,[z0,z1,z115,z3,z4,z5,z6]),(0,[z0,z8,z1,z3,z4,z62,z6])]],
   [[(0,[z116,z0,z1,z3,z4,z5,z6]),(0,[z117,z0,z1,z3,z4,z5,z6]),(0,[z0,z118,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z119,z6]),(0,[z0,z1,z3,z37,z120,z5,z6]),(0,[z0,z1,z3,z4,z5,z121,z6]),(0,[z0,z8,z1,z3,z40,z4,z6]),(0,[z0,z1,z3,z4,z122,z5,z6])],[(0,[z0,z1,z123,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z124,z125]),(0,[z0,z1,z3,z126,z4,z5,z6]),(0,[z0,z1,z93,z104,z4,z5,z6]),(0,[z0,z1,z3,z127,z4,z91,z5])],[(0,[z0,z1,z3,z4,z5,z128,z6]),(0,[z0,z1,z129,z3,z4,z5,z6]),(0,[z0,z24,z1,z3,z4,z130,z6]),(0,[z0,z1,z103,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z131]),(0,[z0,z1,z132,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z133,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z134]),(0,[z0,z1,z3,z135,z4,z5,z6])],[(0,[z26,z0,z1,z136,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z137])],[(0,[z0,z1,z3,z4,z138,z5,z6]),(0,[z0,z139,z1,z3,z4,z5,z6]),(0,[z0,z1,z140,z3,z4,z5,z6]),(0,[z0,z141,z1,z3,z4,z5,z6]),(0,[z0,z8,z24,z1,z3,z4,z6]),(0,[z0,z142,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z143,z4,z5,z6]),(0,[z0,z1,z144,z3,z4,z5,z6]),(0,[z0,z145,z1,z3,z4,z5,z6])],[(1,[z146,z1,z3,z4,z5,z147])],[(0,[z0,z1,z148,z3,z4,z5,z6])]],
   [[(0,[z0,z1,z3,z42,z19,z5,z6]),(1,[z0,z1,z104,z4,z5,z131]),(0,[z0,z1,z75,z3,z4,z19,z5])],[(0,[z0,z1,z3,z149,z4,z5,z6]),(1,[z0,z1,z3,z4,z150,z6]),(0,[z0,z8,z1,z3,z151,z4,z6])],[(0,[z0,z1,z152,z3,z4,z130,z5]),(0,[z0,z153,z24,z1,z3,z4,z6])],[(0,[z0,z47,z1,z3,z4,z5,z6]),(0,[z154,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z155,z4,z5]),(0,[z0,z1,z156,z3,z4,z5,z6]),(0,[z0,z1,z3,z151,z17,z5,z6]),(0,[z0,z1,z157,z3,z127,z4,z5])],[],[(0,[z0,z1,z158,z3,z4,z5,z6]),(0,[z0,z1,z103,z21,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z159,z6]),(0,[z0,z1,z3,z4,z160,z5,z6]),(0,[z0,z1,z3,z27,z4,z5,z6]),(0,[z1,z3,z4,z5,z147,z6,z125]),(1,[z0,z1,z152,z3,z4,z5]),(0,[z0,z8,z1,z3,z4,z161,z6]),(0,[z0,z1,z93,z3,z105,z4,z5]),(0,[z0,z1,z3,z4,z5,z6,z162])],[(0,[z0,z163,z1,z3,z4,z5,z6]),(0,[z0,z164,z1,z3,z4,z5,z6])]],
   [[(0,[z1,z3,z4,z58,z5,z84,z6]),(0,[z0,z1,z3,z4,z130,z5,z6]),(0,[z0,z165,z1,z3,z19,z5,z6]),(0,[z0,z8,z1,z3,z4,z6,z131]),(0,[z0,z1,z3,z166,z4,z5,z6])],[(0,[z0,z8,z1,z136,z3,z4,z6]),(0,[z167,z168,z1,z3,z4,z5,z6]),(0,[z169,z0,z1,z3,z4,z5,z6]),(0,[z0,z170,z1,z3,z4,z5,z6]),(0,[z0,z171,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z105,z5,z6,z20]),(0,[z0,z1,z157,z3,z105,z4,z5]),(0,[z0,z1,z3,z172,z4,z5,z6])],[(0,[z74,z0,z1,z3,z105,z5,z6]),(0,[z0,z1,z3,z4,z5,z173,z6])],[(0,[z0,z1,z3,z174,z4,z5,z6]),(0,[z0,z1,z3,z4,z150,z5,z6]),(0,[z0,z1,z3,z4,z5,z175,z176])],[(0,[z177,z0,z1,z3,z4,z5,z6]),(1,[z0,z24,z1,z3,z4,z6]),(0,[z0,z1,z178,z3,z4,z5,z6]),(0,[z0,z1,z3,z127,z4,z85,z6])],[(0,[z47,z1,z25,z3,z4,z5,z6]),(0,[z168,z1,z3,z4,z5,z84,z6]),(0,[z0,z24,z1,z3,z4,z6,z176]),(0,[z0,z1,z3,z151,z4,z17,z6])],[(0,[z0,z1,z3,z4,z179,z5,z6]),(0,[z74,z0,z24,z1,z3,z4,z6]),(0,[z0,z153,z3,z4,z5,z6,z180]),(0,[z0,z1,z3,z181,z4,z5,z6]),(0,[z0,z1,z104,z3,z4,z5,z131]),(0,[z0,z1,z3,z105,z4,z91,z5]),(0,[z0,z1,z3,z4,z5,z182,z6])],[(0,[z0,z183,z1,z25,z3,z4,z6]),(0,[z0,z1,z3,z4,z184,z5,z6]),(0,[z146,z0,z1,z3,z185,z5,z6]),(0,[z186,z0,z1,z3,z4,z5,z6]),(0,[z0,z79,z1,z3,z4,z5,z180]),(0,[z0,z1,z3,z4,z17,z5,z6])]],
   [[(0,[z0,z1,z3,z4,z5,z124,z147]),(0,[z0,z109,z24,z1,z3,z4,z6]),(0,[z0,z187,z1,z3,z4,z5,z6]),(0,[z0,z24,z1,z3,z4,z188,z6]),(0,[z0,z1,z3,z4,z120,z5,z6]),(0,[z0,z189,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z190,z5,z6])],[(0,[z26,z0,z1,z3,z191,z5,z6]),(0,[z192,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z193,z5,z6]),(0,[z194,z0,z1,z3,z4,z5,z147]),(0,[z0,z153,z1,z3,z105,z4,z5]),(0,[z0,z1,z3,z195,z4,z5,z6]),(0,[z0,z1,z3,z196,z4,z5,z6]),(0,[z0,z1,z3,z4,z197,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z198]),(0,[z0,z1,z3,z199,z4,z5,z6])],[(1,[z0,z200,z201,z4,z5,z6]),(0,[z0,z1,z202,z3,z4,z5,z6]),(0,[z203,z0,z24,z1,z3,z4,z6])],[(0,[z0,z1,z3,z4,z204,z5,z6]),(0,[z0,z1,z3,z4,z5,z205,z6]),(0,[z206,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z175,z6])],[(1,[z0,z1,z3,z4,z121,z6]),(0,[z0,z1,z3,z195,z4,z6,z180]),(0,[z0,z1,z207,z3,z4,z5,z6]),(0,[z208,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z209,z3,z4,z5,z6])],[(0,[z210,z0,z1,z3,z4,z5,z6]),(1,[z0,z141,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z211,z6]),(0,[z0,z1,z212,z3,z4,z5,z6])],[(0,[z213,z0,z1,z3,z4,z5,z6]),(0,[z194,z1,z3,z4,z5,z6,z125]),(0,[z0,z1,z214,z3,z4,z5,z6]),(0,[z0,z79,z1,z75,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z6,z215]),(0,[z0,z216,z1,z3,z4,z5,z6]),(0,[z0,z217,z1,z3,z4,z5,z6])]],
   [[(1,[z0,z73,z3,z4,z5,z6]),(0,[z0,z24,z1,z3,z37,z4,z6]),(0,[z0,z79,z1,z3,z4,z5,z88]),(0,[z0,z1,z103,z3,z4,z218,z6]),(0,[z0,z1,z3,z4,z5,z219,z6])],[(0,[z0,z1,z3,z4,z220,z5,z6]),(0,[z36,z0,z1,z3,z42,z5,z6]),(0,[z69,z0,z8,z1,z3,z4,z6]),(0,[z0,z8,z1,z3,z37,z4,z6]),(0,[z0,z221,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z222,z4,z5,z6]),(0,[z0,z24,z1,z3,z4,z85,z6]),(1,[z0,z1,z3,z195,z4,z6]),(0,[z0,z1,z223,z3,z4,z5,z6])],[(0,[z0,z1,z3,z224,z4,z5,z6]),(0,[z0,z8,z3,z4,z60,z5,z6]),(0,[z0,z8,z1,z3,z4,z85,z6]),(0,[z0,z1,z103,z3,z225,z5,z6]),(0,[z0,z1,z3,z4,z226,z5,z6]),(0,[z227,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z107,z6,z176])],[(0,[z228,z0,z1,z3,z4,z5,z6]),(0,[z0,z229,z24,z1,z3,z4,z6]),(0,[z0,z1,z230,z3,z4,z5,z6]),(0,[z0,z231,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z34,z4,z5,z6]),(0,[z0,z1,z3,z4,z232,z5,z6]),(0,[z0,z24,z233,z1,z3,z4,z6]),(0,[z0,z1,z234,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z91,z92]),(0,[z0,z235,z1,z3,z4,z5,z6])],[(0,[z236,z1,z25,z3,z4,z5,z6]),(0,[z0,z1,z3,z237,z4,z5,z6]),(0,[z0,z1,z238,z3,z4,z5,z6]),(0,[z0,z1,z104,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z6,z176,z92])],[(0,[z0,z8,z1,z3,z4,z42,z6]),(0,[z44,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z239]),(0,[z0,z1,z3,z4,z5,z240,z6])],[(0,[z0,z1,z3,z4,z241,z5,z6])]],
   [[(0,[z242,z0,z1,z3,z4,z5,z6]),(0,[z36,z69,z1,z3,z4,z5,z6]),(0,[z69,z1,z3,z37,z4,z5,z6]),(0,[z0,z1,z3,z243,z4,z5,z6]),(0,[z0,z24,z1,z244,z3,z4,z6]),(0,[z0,z1,z3,z4,z245,z5,z6]),(0,[z0,z1,z93,z3,z4,z5,z131]),(0,[z246,z0,z1,z3,z4,z5,z6]),(0,[z247,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z248,z3,z4,z5,z6]),(0,[z249,z0,z1,z3,z4,z5,z6]),(0,[z250,z0,z8,z1,z3,z4,z6])],[(1,[z0,z1,z3,z4,z5,z48]),(0,[z0,z1,z251,z3,z4,z5,z6]),(0,[z167,z1,z3,z4,z58,z5,z6]),(0,[z0,z200,z1,z3,z4,z5,z6]),(0,[z0,z1,z252,z3,z4,z5,z6])],[],[(0,[z0,z1,z3,z4,z5,z6,z253]),(0,[z254,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z255])],[(0,[z256,z0,z1,z27,z4,z5,z6]),(0,[z0,z257,z1,z3,z4,z5,z6]),(0,[z0,z258,z1,z3,z4,z5,z6])],[(0,[z259,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z260,z5,z6]),(0,[z0,z1,z3,z4,z5,z89,z6]),(0,[z0,z1,z3,z4,z5,z88,z6]),(0,[z0,z1,z3,z18,z5,z6,z180]),(0,[z0,z1,z3,z4,z17,z6,z92])],[(0,[z0,z24,z1,z3,z4,z147,z6]),(0,[z0,z1,z3,z4,z261,z5,z6])]],
   [[(0,[z0,z1,z3,z59,z4,z5,z6]),(0,[z0,z1,z3,z4,z262,z5,z6]),(0,[z0,z1,z3,z127,z4,z5,z6])],[(0,[z236,z263,z1,z3,z4,z5,z6]),(0,[z0,z1,z264,z3,z4,z5,z6]),(0,[z0,z24,z1,z3,z4,z19,z6]),(0,[z0,z1,z3,z4,z5,z6,z265]),(0,[z0,z1,z3,z4,z266,z5,z6])],[(0,[z167,z0,z158,z3,z4,z5,z6]),(0,[z0,z267,z1,z3,z4,z5,z6]),(0,[z0,z8,z1,z3,z4,z19,z6]),(0,[z0,z1,z3,z4,z5,z268,z6])],[(0,[z0,z24,z1,z3,z4,z84,z6]),(0,[z74,z0,z3,z4,z60,z5,z6])],[(0,[z0,z269,z1,z3,z4,z5,z6]),(1,[z0,z1,z207,z3,z4,z6]),(0,[z0,z1,z270,z3,z4,z5,z6]),(0,[z0,z23,z1,z244,z4,z5,z6]),(0,[z271,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z272,z4,z5,z6]),(0,[z273,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z274,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z275,z6]),(1,[z0,z3,z4,z5,z6,z276])],[(0,[z194,z0,z8,z1,z3,z4,z6]),(0,[z0,z277,z1,z3,z4,z5,z6]),(0,[z278,z0,z1,z3,z4,z5,z6])],[(1,[z0,z1,z3,z279,z5,z6]),(1,[z0,z1,z3,z4,z280,z6]),(0,[z0,z1,z93,z3,z4,z5,z6])]],
   [[(0,[z0,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z281,z5,z6]),(0,[z0,z1,z282,z3,z4,z5,z6]),(0,[z0,z8,z1,z75,z3,z4,z6]),(0,[z0,z1,z283,z3,z4,z5,z6]),(0,[z0,z1,z284,z3,z4,z5,z6]),(0,[z285,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z286,z5,z6]),(0,[z0,z1,z264,z3,z4,z130,z6]),(0,[z0,z1,z3,z287,z4,z5,z6])],[(0,[z288,z0,z1,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z88,z6,z180]),(0,[z0,z289,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z290]),(0,[z0,z1,z157,z3,z4,z5,z6])],[(0,[z0,z1,z291,z3,z4,z5,z6]),(0,[z292,z0,z24,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z5,z6,z293])],[(0,[z256,z0,z8,z1,z3,z4,z6]),(0,[z0,z1,z294,z3,z4,z5,z6]),(0,[z0,z8,z1,z3,z4,z89,z6]),(0,[z0,z1,z295,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z6,z215])],[(0,[z0,z1,z3,z99,z4,z5,z6]),(0,[z0,z1,z3,z4,z296,z5,z6]),(1,[z74,z0,z24,z3,z4,z6]),(0,[z0,z297,z24,z1,z3,z4,z6]),(0,[z0,z24,z1,z3,z4,z5,z6]),(0,[z298,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z136,z3,z4,z5,z6]),(0,[z0,z8,z1,z3,z4,z5,z6]),(0,[z0,z8,z153,z1,z3,z4,z6]),(0,[z0,z1,z3,z299,z4,z5,z6]),(0,[z0,z79,z153,z3,z4,z5,z6])],[(0,[z0,z1,z3,z300,z4,z5,z6]),(0,[z0,z1,z301,z3,z4,z5,z6]),(0,[z0,z201,z3,z34,z4,z5,z6]),(0,[z0,z24,z1,z3,z4,z120,z6]),(0,[z0,z1,z302,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z303])]],
   [[(0,[z0,z1,z3,z4,z107,z84,z6]),(0,[z0,z24,z1,z3,z4,z6,z180]),(0,[z0,z1,z304,z3,z4,z5,z6]),(0,[z305,z0,z1,z3,z4,z5,z6])],[(0,[z0,z8,z1,z25,z3,z4,z6]),(0,[z0,z1,z3,z4,z306,z5,z6]),(0,[z0,z1,z3,z4,z307,z5,z6]),(0,[z0,z1,z3,z308,z4,z5,z6]),(0,[z0,z309,z1,z3,z4,z5,z6]),(0,[z0,z165,z1,z3,z59,z5,z6]),(0,[z0,z24,z1,z3,z225,z4,z6]),(0,[z0,z8,z1,z3,z4,z6,z180]),(0,[z0,z1,z310,z3,z4,z5,z6]),(0,[z0,z311,z1,z3,z4,z5,z6]),(0,[z312,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z313,z3,z4,z5,z6]),(1,[z0,z1,z3,z105,z5,z20])],[(0,[z0,z1,z3,z4,z5,z314,z6]),(0,[z263,z0,z1,z3,z4,z54,z6]),(0,[z0,z1,z3,z315,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z316,z6]),(0,[z317,z0,z8,z1,z3,z4,z6])],[(0,[z0,z1,z3,z318,z4,z5,z6]),(0,[z69,z0,z24,z1,z3,z4,z6]),(0,[z0,z319,z1,z3,z4,z5,z6]),(0,[z0,z1,z320,z3,z4,z5,z6])],[(0,[z0,z1,z321,z3,z4,z5,z6]),(0,[z0,z1,z3,z105,z37,z5,z6]),(0,[z0,z1,z3,z4,z322,z5,z6])],[(0,[z263,z0,z8,z1,z3,z4,z6]),(0,[z0,z323,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z324,z5,z6]),(1,[z43,z1,z3,z4,z5,z6]),(0,[z0,z325,z8,z1,z3,z4,z6]),(0,[z0,z1,z3,z105,z4,z5,z6])],[(0,[z168,z0,z8,z1,z3,z4,z6]),(0,[z0,z1,z3,z326,z4,z5,z6]),(0,[z194,z0,z1,z3,z4,z5,z125]),(0,[z0,z100,z1,z3,z34,z4,z6]),(0,[z0,z8,z1,z3,z4,z130,z6])],[(0,[z74,z43,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z327]),(0,[z0,z1,z328,z3,z4,z5,z6])]],
   [[(0,[z0,z1,z3,z4,z5,z6,z329]),(0,[z146,z1,z3,z4,z5,z147,z6]),(0,[z0,z8,z200,z1,z3,z4,z6]),(0,[z0,z1,z330,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z331])],[(0,[z0,z47,z3,z34,z4,z5,z6]),(0,[z0,z1,z332,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z333,z5,z6]),(0,[z0,z334,z1,z3,z4,z5,z6])],[(0,[z0,z1,z335,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z336,z6]),(0,[z0,z1,z3,z4,z107,z5,z6]),(0,[z0,z1,z3,z4,z337,z5,z6])],[(0,[z0,z1,z338,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z176])],[(0,[z0,z23,z8,z1,z3,z4,z6])],[(1,[z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z339,z5,z6]),(0,[z340,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z341,z5,z6])],[(0,[z1,z136,z3,z27,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z188,z6]),(0,[z0,z1,z3,z4,z342,z5,z6]),(0,[z0,z343,z1,z3,z4,z5,z6]),(0,[z0,z1,z93,z4,z5,z124,z6])],[(0,[z0,z25,z3,z4,z60,z5,z6]),(1,[z0,z1,z3,z4,z5,z119]),(1,[z0,z1,z3,z30,z5,z6]),(0,[z0,z24,z1,z3,z4,z6,z20])]],
   [[(0,[z0,z1,z3,z4,z344,z5,z6]),(0,[z0,z165,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z345,z5,z6])],[(0,[z0,z109,z1,z3,z4,z5,z6])],[(1,[z0,z1,z3,z4,z5,z128]),(0,[z0,z200,z201,z3,z4,z5,z6]),(0,[z74,z0,z1,z3,z19,z5,z6]),(0,[z0,z1,z3,z346,z4,z5,z6]),(0,[z0,z1,z3,z4,z347,z5,z6])],[(0,[z0,z1,z3,z348,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z349,z6])],[(0,[z0,z1,z3,z4,z5,z6,z6]),(0,[z0,z350,z24,z1,z3,z4,z6]),(0,[z203,z0,z1,z3,z4,z5,z6]),(0,[z0,z24,z1,z3,z4,z6,z92]),(0,[z0,z1,z3,z4,z351,z5,z6])],[(0,[z0,z24,z1,z3,z59,z4,z6]),(0,[z0,z1,z157,z3,z4,z6,z176])],[(0,[z0,z352,z1,z3,z4,z5,z6]),(0,[z0,z1,z75,z3,z4,z5,z125]),(0,[z0,z1,z3,z4,z5,z147,z131]),(0,[z0,z1,z3,z155,z4,z5,z6]),(0,[z0,z1,z3,z4,z353,z5,z6])],[(0,[z0,z183,z1,z3,z4,z5,z6]),(1,[z167,z1,z3,z4,z58,z6]),(0,[z0,z1,z354,z3,z4,z5,z6]),(0,[z0,z1,z244,z3,z4,z107,z6]),(0,[z0,z1,z3,z4,z5,z85,z6]),(0,[z0,z1,z93,z3,z4,z355,z6])]],
   [[(0,[z356,z0,z1,z3,z4,z5,z6]),(0,[z0,z357,z1,z3,z4,z5,z6]),(0,[z194,z0,z24,z1,z3,z4,z6]),(0,[z0,z110,z1,z3,z4,z5,z6]),(0,[z0,z1,z75,z3,z4,z5,z20])],[(0,[z0,z1,z3,z358,z4,z5,z6]),(0,[z0,z24,z1,z201,z3,z4,z6]),(0,[z0,z1,z3,z59,z4,z6,z359]),(0,[z0,z24,z1,z3,z4,z353,z6]),(0,[z0,z24,z1,z3,z4,z124,z6]),(0,[z0,z8,z1,z3,z4,z6,z176]),(0,[z0,z1,z3,z4,z5,z6,z360])],[(1,[z0,z361,z3,z4,z5,z6]),(0,[z0,z8,z1,z201,z3,z4,z6]),(0,[z0,z1,z21,z3,z4,z5,z6]),(1,[z0,z1,z362,z3,z4,z5]),(0,[z0,z1,z104,z3,z4,z5,z124])],[(0,[z0,z1,z363,z3,z4,z5,z6]),(0,[z0,z1,z364,z3,z4,z5,z6]),(1,[z0,z24,z3,z4,z89,z6]),(0,[z0,z8,z1,z365,z3,z4,z6]),(0,[z0,z1,z304,z3,z4,z6,z176])],[(1,[z0,z183,z1,z3,z4,z6]),(0,[z0,z366,z1,z3,z4,z5,z6]),(0,[z0,z229,z1,z3,z4,z5,z6]),(0,[z0,z1,z362,z3,z4,z120,z5])],[(0,[z0,z1,z3,z4,z5,z280,z6]),(0,[z0,z1,z3,z4,z367,z5,z6])],[(0,[z368,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z97,z5,z6]),(0,[z256,z0,z24,z1,z3,z4,z6]),(0,[z0,z1,z3,z17,z5,z6,z176])],[(0,[z369,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z103,z4,z120,z5,z6]),(0,[z0,z1,z3,z370,z4,z5,z6])]],
   [[(1,[z0,z24,z25,z3,z4,z6]),(0,[z0,z1,z3,z371,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z372])],[(0,[z146,z0,z1,z3,z4,z5,z147]),(0,[z0,z1,z373,z3,z4,z5,z6]),(0,[z0,z1,z103,z3,z120,z5,z6]),(0,[z0,z1,z3,z4,z85,z6,z176])],[(0,[z0,z1,z3,z4,z374,z5,z6]),(0,[z0,z200,z1,z201,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z375,z6]),(0,[z0,z1,z21,z225,z4,z5,z6]),(0,[z0,z376,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z377,z4,z5,z6]),(0,[z0,z1,z3,z42,z120,z5,z6]),(0,[z0,z165,z1,z3,z130,z5,z6]),(0,[z0,z378,z8,z1,z3,z4,z6]),(0,[z0,z379,z1,z3,z4,z5,z6]),(0,[z0,z1,z75,z3,z105,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z380]),(0,[z0,z1,z3,z4,z5,z6,z381]),(0,[z0,z1,z3,z4,z5,z147,z6]),(1,[z0,z1,z3,z4,z382,z6]),(0,[z0,z1,z244,z4,z5,z85,z6]),(0,[z0,z1,z3,z4,z5,z6,z383])],[(0,[z0,z1,z3,z4,z95,z5,z6]),(0,[z0,z1,z3,z4,z384,z5,z6]),(0,[z0,z1,z225,z4,z120,z5,z6]),(0,[z0,z1,z3,z385,z4,z5,z6]),(0,[z0,z1,z3,z4,z386,z5,z6])],[(0,[z263,z0,z24,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z387,z5,z6]),(0,[z0,z1,z388,z3,z4,z5,z6])]],
   [[(0,[z26,z0,z1,z27,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z389]),(0,[z0,z1,z3,z4,z390,z5,z6]),(0,[z0,z1,z3,z4,z5,z391,z6])],[(0,[z0,z1,z392,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z84,z6]),(0,[z0,z24,z1,z157,z3,z4,z6]),(0,[z0,z1,z393,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z394,z5,z6]),(0,[z0,z395,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z105,z4,z19,z5])],[(0,[z0,z396,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z397,z6])],[(1,[z0,z1,z3,z4,z5,z175]),(0,[z0,z1,z398,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z399,z5,z6]),(0,[z400,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z401,z4,z5,z6]),(0,[z0,z8,z1,z244,z3,z4,z6]),(0,[z0,z1,z3,z4,z402,z5,z6]),(0,[z0,z1,z93,z3,z4,z5,z124])],[(0,[z0,z1,z3,z4,z5,z403,z6]),(0,[z0,z1,z404,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z405,z6]),(0,[z167,z0,z8,z1,z3,z4,z6]),(0,[z0,z1,z75,z3,z4,z5,z147])],[(0,[z236,z0,z8,z1,z3,z4,z6]),(0,[z0,z8,z319,z1,z3,z4,z6]),(0,[z406,z0,z8,z1,z3,z4,z6]),(0,[z0,z153,z1,z3,z4,z5,z88]),(0,[z0,z1,z3,z407,z4,z5,z6])],[(0,[z0,z408,z1,z3,z4,z5,z6]),(0,[z409,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z410,z6]),(0,[z0,z1,z3,z411,z4,z5,z6]),(0,[z0,z1,z412,z3,z4,z5,z6])]],
   [[(0,[z0,z1,z3,z4,z413,z5,z6]),(1,[z0,z79,z3,z4,z5,z88]),(0,[z0,z1,z3,z4,z218,z5,z6]),(0,[z0,z1,z4,z5,z124,z6,z131]),(0,[z0,z1,z3,z4,z5,z6,z414]),(0,[z0,z1,z3,z415,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z416]),(0,[z0,z24,z1,z3,z27,z4,z6])],[(1,[z194,z1,z3,z4,z5,z125]),(0,[z0,z1,z3,z417,z4,z5,z6])],[(0,[z263,z47,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z5,z6]),(0,[z0,z8,z1,z3,z4,z147,z6]),(0,[z0,z1,z3,z4,z161,z5,z6]),(0,[z0,z1,z3,z418,z4,z5,z6])],[(0,[z292,z0,z1,z3,z4,z5,z6]),(0,[z419,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z420,z6])],[(0,[z263,z0,z1,z3,z4,z220,z6]),(0,[z0,z1,z3,z4,z421,z5,z6]),(0,[z0,z1,z3,z4,z422,z5,z6]),(0,[z74,z0,z165,z3,z4,z5,z6]),(0,[z0,z1,z423,z3,z4,z5,z6]),(0,[z0,z1,z424,z3,z4,z5,z6])],[(1,[z236,z25,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z97,z6]),(0,[z425,z0,z1,z3,z4,z5,z6]),(0,[z0,z297,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z180]),(0,[z0,z1,z3,z426,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z427,z6]),(0,[z26,z0,z8,z1,z3,z4,z6]),(0,[z0,z8,z1,z3,z4,z84,z6])]],
   [[(0,[z0,z1,z3,z4,z428,z5,z6]),(0,[z429,z0,z1,z3,z4,z5,z6]),(0,[z0,z23,z1,z3,z4,z107,z6])],[(0,[z0,z1,z3,z105,z42,z5,z6]),(0,[z0,z1,z3,z4,z430,z5,z6]),(0,[z0,z3,z59,z4,z130,z5,z6]),(0,[z186,z0,z8,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z431,z5,z6]),(0,[z0,z23,z1,z4,z107,z5,z6]),(0,[z0,z1,z3,z4,z19,z5,z6]),(0,[z0,z1,z3,z432,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z433]),(0,[z434,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z435,z5,z6]),(0,[z0,z1,z21,z3,z225,z5,z6]),(0,[z0,z1,z3,z105,z4,z6,z383])],[(0,[z69,z0,z1,z3,z37,z5,z6]),(0,[z167,z0,z1,z3,z4,z58,z6]),(0,[z0,z436,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z437,z5,z6]),(0,[z0,z1,z438,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z439]),(0,[z0,z1,z440,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z441])],[(0,[z0,z442,z1,z3,z4,z5,z6]),(0,[z146,z0,z8,z1,z3,z4,z6]),(1,[z0,z1,z3,z18,z5,z6]),(0,[z0,z1,z4,z107,z5,z85,z6]),(0,[z0,z1,z3,z4,z5,z443,z6])],[(0,[z0,z1,z444,z3,z4,z5,z6]),(0,[z0,z1,z445,z3,z4,z5,z6]),(0,[z69,z0,z1,z3,z4,z5,z119]),(0,[z0,z1,z3,z4,z58,z85,z6]),(0,[z446,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z447,z5,z6])],[(0,[z0,z1,z3,z4,z5,z448,z6]),(0,[z0,z1,z75,z104,z3,z4,z5])]],
   [[(0,[z449,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z450,z4,z5,z6]),(0,[z0,z1,z3,z225,z37,z5,z6]),(0,[z0,z79,z3,z4,z5,z88,z6]),(0,[z0,z1,z451,z3,z4,z5,z6]),(0,[z0,z1,z452,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z88,z6,z215]),(0,[z0,z1,z3,z225,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z453]),(0,[z0,z24,z1,z3,z4,z6,z454]),(0,[z0,z455,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z6,z383])],[(0,[z456,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z457,z4,z5,z6]),(0,[z74,z0,z1,z3,z59,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z458]),(0,[z0,z8,z1,z3,z4,z120,z6]),(0,[z0,z1,z3,z4,z5,z6,z459]),(0,[z460,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z75,z157,z3,z4,z5])],[(0,[z461,z0,z1,z3,z4,z5,z6]),(0,[z462,z0,z1,z3,z4,z5,z6]),(0,[z250,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z463,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z464,z6]),(0,[z0,z24,z3,z4,z5,z89,z6]),(0,[z0,z8,z1,z3,z225,z4,z6]),(0,[z0,z1,z3,z4,z5,z6,z20])],[(0,[z0,z1,z3,z465,z4,z5,z6]),(0,[z0,z1,z3,z4,z466,z5,z6]),(0,[z0,z153,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z382,z5,z6]),(0,[z0,z1,z3,z4,z467,z5,z6])],[(0,[z0,z1,z468,z3,z4,z5,z6]),(0,[z0,z1,z3,z469,z4,z5,z6]),(1,[z69,z1,z3,z37,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z470]),(0,[z0,z1,z3,z4,z5,z471,z6]),(0,[z0,z1,z201,z3,z4,z150,z6]),(1,[z0,z1,z264,z3,z4,z6]),(0,[z0,z24,z3,z59,z4,z5,z6]),(0,[z0,z1,z3,z4,z60,z5,z6]),(1,[z0,z1,z75,z3,z19,z5])]],
   [[(0,[z0,z1,z3,z4,z5,z6,z472]),(0,[z0,z24,z1,z3,z4,z107,z6]),(0,[z0,z1,z3,z4,z5,z6,z473])],[(0,[z474,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z475,z4,z5,z6]),(0,[z0,z1,z3,z4,z382,z6,z180])],[(0,[z476,z0,z1,z3,z4,z5,z6]),(0,[z242,z0,z8,z1,z3,z4,z6]),(0,[z0,z1,z477,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z478]),(0,[z0,z1,z3,z127,z4,z6,z92]),(0,[z0,z1,z3,z4,z5,z6,z92])],[(0,[z1,z25,z3,z4,z42,z5,z6]),(0,[z0,z1,z3,z479,z4,z5,z6]),(0,[z146,z194,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z480,z4,z5,z6]),(0,[z481,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z482,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z276]),(0,[z0,z1,z483,z3,z4,z5,z6])],[(1,[z0,z1,z3,z185,z5,z6]),(0,[z484,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z485,z4,z5,z6]),(0,[z0,z24,z1,z304,z3,z4,z6])],[(0,[z0,z1,z3,z4,z5,z486,z6]),(0,[z146,z0,z1,z3,z4,z5,z125]),(0,[z0,z487,z1,z3,z4,z5,z6]),(0,[z0,z350,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z488,z4,z5,z6]),(0,[z489,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z490,z3,z4,z5,z6])],[(0,[z0,z1,z3,z155,z4,z130,z5]),(0,[z0,z1,z3,z4,z491,z5,z6]),(0,[z492,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z226,z5]),(0,[z0,z1,z493,z3,z4,z5,z6])],[(0,[z494,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z94]),(0,[z0,z1,z3,z4,z495,z5,z6]),(0,[z167,z0,z24,z1,z3,z4,z6]),(0,[z0,z1,z3,z496,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z124,z6])]],
   [[(0,[z236,z0,z24,z1,z3,z4,z6]),(0,[z0,z1,z497,z3,z4,z5,z6]),(0,[z0,z24,z1,z3,z4,z6,z125]),(0,[z0,z1,z3,z4,z498,z5,z6]),(0,[z0,z1,z3,z4,z5,z499,z6])],[(0,[z263,z0,z25,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z500]),(0,[z0,z1,z501,z3,z4,z5,z6]),(0,[z0,z8,z24,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z502]),(0,[z36,z0,z8,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z5,z6,z503]),(0,[z74,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z504,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z505]),(0,[z506,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z507,z3,z4,z5,z6]),(0,[z0,z200,z1,z34,z4,z5,z6]),(0,[z0,z1,z508,z3,z4,z5,z6]),(0,[z0,z8,z1,z3,z4,z6,z20]),(0,[z0,z1,z3,z4,z5,z509,z6]),(0,[z0,z510,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z355,z6])],[(0,[z0,z1,z25,z3,z4,z5,z6]),(0,[z263,z0,z47,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z511,z6]),(1,[z0,z1,z512,z3,z4,z5])],[(1,[z0,z1,z3,z191,z5,z6])],[],[(0,[z0,z1,z3,z4,z5,z513,z6]),(0,[z168,z0,z1,z3,z4,z58,z6]),(0,[z0,z1,z3,z4,z226,z120,z5])]],
   [[(0,[z263,z1,z3,z4,z42,z5,z6]),(0,[z0,z1,z514,z3,z4,z5,z6]),(0,[z515,z0,z1,z3,z4,z5,z6]),(0,[z0,z8,z1,z3,z4,z6,z92]),(0,[z0,z1,z3,z516,z4,z5,z6])],[(0,[z26,z0,z24,z1,z3,z4,z6]),(0,[z167,z0,z141,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z125,z131]),(0,[z0,z8,z1,z3,z59,z4,z6]),(0,[z0,z1,z3,z4,z5,z6,z517]),(0,[z0,z1,z3,z4,z5,z518,z6]),(0,[z0,z1,z3,z519,z4,z5,z6])],[(0,[z0,z1,z520,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z58,z5,z6]),(0,[z0,z165,z3,z59,z4,z5,z6]),(0,[z0,z3,z4,z60,z5,z89,z6]),(0,[z0,z1,z521,z3,z4,z5,z6])],[(1,[z0,z35,z1,z3,z4,z6]),(0,[z0,z1,z201,z3,z4,z121,z6]),(0,[z0,z1,z3,z4,z522,z5,z6]),(0,[z0,z24,z1,z3,z4,z91,z6]),(0,[z0,z24,z1,z3,z127,z4,z6]),(0,[z0,z1,z523,z3,z4,z5,z6]),(0,[z0,z1,z103,z3,z4,z524,z6])],[(0,[z0,z525,z1,z3,z4,z5,z6]),(0,[z0,z24,z1,z3,z34,z4,z6]),(0,[z0,z1,z3,z4,z526,z5,z6]),(0,[z0,z1,z3,z99,z34,z4,z6]),(0,[z0,z1,z3,z4,z5,z6,z359]),(1,[z0,z231,z3,z4,z5,z6]),(1,[z0,z1,z3,z151,z17,z6])],[(0,[z0,z1,z3,z4,z527,z5,z6]),(0,[z317,z0,z1,z3,z4,z5,z6]),(0,[z0,z8,z1,z3,z4,z124,z6]),(1,[z0,z1,z93,z4,z5,z124]),(0,[z0,z1,z3,z4,z528,z5,z6])],[(1,[z0,z23,z1,z4,z107,z6])],[(0,[z146,z0,z24,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z5,z6,z529])]],
   [[(0,[z0,z325,z1,z3,z4,z5,z6]),(0,[z0,z8,z109,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z530,z5,z6])],[(0,[z0,z1,z3,z37,z4,z5,z6]),(0,[z0,z531,z1,z3,z4,z5,z6]),(0,[z0,z24,z1,z3,z105,z4,z6]),(0,[z0,z1,z532,z3,z4,z5,z6]),(0,[z533,z0,z1,z3,z4,z5,z6])],[(0,[z0,z534,z1,z3,z4,z5,z6]),(0,[z36,z1,z3,z4,z42,z5,z6]),(0,[z74,z0,z24,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z535,z5,z6])],[(0,[z0,z1,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z279,z5,z6]),(0,[z0,z1,z3,z536,z4,z5,z6]),(0,[z0,z233,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z537,z4,z5,z6]),(0,[z0,z1,z3,z4,z538,z5,z6]),(0,[z0,z1,z3,z105,z4,z467,z6]),(0,[z0,z1,z3,z4,z539,z5,z6])],[(0,[z0,z1,z540,z3,z4,z5,z6]),(0,[z0,z1,z3,z37,z19,z5,z6]),(0,[z0,z109,z200,z3,z4,z5,z6]),(1,[z0,z109,z34,z4,z5,z6]),(0,[z0,z1,z541,z3,z4,z5,z6]),(0,[z0,z1,z75,z3,z19,z5,z6])],[(0,[z0,z24,z47,z1,z3,z4,z6]),(0,[z26,z0,z73,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z542,z5,z6]),(0,[z0,z24,z1,z3,z4,z17,z6])],[(0,[z0,z8,z47,z1,z3,z4,z6]),(0,[z74,z0,z1,z3,z130,z5,z6]),(0,[z0,z24,z1,z21,z3,z4,z6]),(0,[z0,z1,z3,z543,z4,z5,z6]),(0,[z0,z544,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z91,z85,z6])],[(1,[z0,z165,z3,z59,z5,z6])]],
   [[(0,[z26,z256,z1,z3,z4,z5,z6]),(0,[z0,z24,z1,z104,z3,z4,z6]),(0,[z0,z153,z1,z3,z4,z5,z180]),(0,[z0,z1,z3,z4,z107,z91,z6]),(0,[z0,z1,z304,z3,z4,z17,z6])],[(0,[z0,z1,z3,z4,z545,z5,z6]),(1,[z263,z47,z3,z4,z5,z6]),(0,[z0,z546,z1,z3,z4,z5,z6]),(0,[z0,z1,z547,z3,z4,z5,z6]),(0,[z0,z8,z1,z104,z3,z4,z6])],[(0,[z0,z8,z79,z1,z3,z4,z6]),(0,[z0,z1,z548,z3,z4,z5,z6]),(0,[z0,z1,z549,z3,z4,z5,z6])],[(0,[z168,z0,z24,z1,z3,z4,z6]),(0,[z0,z1,z3,z550,z4,z5,z6]),(1,[z0,z1,z3,z4,z467,z6])],[(0,[z0,z35,z1,z25,z3,z4,z6]),(0,[z0,z47,z3,z4,z60,z5,z6]),(0,[z551,z0,z1,z3,z4,z5,z6]),(0,[z552,z0,z1,z3,z4,z5,z6])],[(1,[z26,z1,z27,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z553,z6]),(0,[z0,z1,z3,z554,z4,z5,z6]),(0,[z0,z8,z1,z157,z3,z4,z6]),(0,[z0,z1,z3,z4,z555,z5,z6]),(0,[z0,z1,z244,z3,z4,z85,z6]),(0,[z0,z1,z3,z151,z4,z5,z6])],[(0,[z0,z1,z556,z3,z4,z5,z6]),(0,[z0,z1,z557,z3,z4,z5,z6]),(0,[z0,z200,z24,z1,z3,z4,z6]),(1,[z0,z1,z3,z4,z218,z6]),(0,[z0,z558,z1,z3,z4,z5,z6])],[(0,[z26,z0,z1,z3,z4,z5,z48]),(0,[z0,z1,z559,z3,z4,z5,z6]),(1,[z481,z1,z3,z4,z5,z6]),(0,[z0,z7,z24,z1,z3,z4,z6]),(0,[z0,z1,z104,z4,z5,z6,z131])]],
   [[(0,[z0,z1,z361,z3,z4,z5,z6]),(0,[z0,z153,z1,z75,z3,z4,z5]),(1,[z0,z1,z3,z4,z355,z6])],[(0,[z0,z1,z3,z560,z4,z5,z6]),(0,[z74,z481,z1,z3,z4,z5,z6]),(0,[z0,z24,z1,z1,z3,z4,z6]),(0,[z0,z257,z24,z1,z3,z4,z6]),(0,[z0,z23,z24,z1,z3,z4,z6])],[(0,[z0,z1,z3,z4,z107,z17,z6]),(0,[z0,z1,z561,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z562,z6])],[(0,[z0,z563,z1,z3,z4,z5,z6]),(0,[z0,z1,z157,z3,z4,z5,z92])],[(0,[z36,z0,z24,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z5,z6,z564]),(0,[z0,z1,z3,z4,z5,z6,z565]),(0,[z0,z1,z566,z3,z4,z5,z6]),(0,[z0,z1,z567,z3,z4,z5,z6]),(0,[z0,z1,z512,z3,z4,z5,z176])],[(0,[z0,z8,z1,z3,z27,z4,z6]),(0,[z0,z1,z3,z225,z42,z5,z6]),(0,[z0,z1,z3,z4,z185,z5,z6]),(0,[z0,z1,z3,z554,z4,z130,z6]),(0,[z0,z1,z3,z568,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z569]),(0,[z0,z1,z3,z4,z5,z6,z570]),(0,[z0,z1,z75,z3,z4,z91,z5]),(0,[z0,z1,z3,z4,z571,z5,z6])],[(0,[z0,z1,z3,z572,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z573,z6]),(0,[z0,z1,z3,z4,z574,z5,z6]),(0,[z0,z1,z575,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z576,z6]),(1,[z0,z158,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z577,z5,z6]),(0,[z0,z1,z3,z105,z4,z5,z125]),(0,[z0,z1,z3,z4,z5,z6,z578])]],
   [[(0,[z0,z1,z579,z3,z4,z5,z6]),(1,[z0,z24,z3,z59,z4,z6]),(0,[z0,z24,z1,z103,z3,z4,z6]),(0,[z0,z1,z3,z4,z5,z6,z454]),(1,[z0,z153,z3,z4,z5,z180]),(0,[z580,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z581,z3,z4,z5,z6])],[(0,[z582,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z583,z6]),(0,[z0,z1,z3,z4,z5,z584,z6]),(1,[z0,z1,z3,z4,z6,z359]),(0,[z0,z1,z21,z3,z120,z5,z6]),(0,[z0,z3,z4,z5,z6,z276,z176]),(0,[z0,z1,z3,z4,z585,z5,z6]),(0,[z0,z1,z3,z105,z4,z5,z20]),(0,[z0,z1,z3,z4,z586,z5,z6])],[(0,[z236,z0,z25,z3,z4,z5,z6]),(0,[z0,z587,z1,z3,z4,z5,z6]),(0,[z0,z1,z588,z3,z4,z5,z6]),(0,[z0,z589,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z590,z6]),(0,[z0,z1,z3,z4,z591,z5,z6]),(0,[z0,z1,z3,z592,z4,z5,z6]),(0,[z0,z1,z3,z4,z593,z5,z6])],[(0,[z26,z0,z1,z3,z279,z5,z6]),(0,[z26,z0,z1,z3,z4,z280,z6]),(0,[z594,z0,z1,z3,z4,z5,z6]),(0,[z74,z0,z3,z4,z130,z5,z6]),(0,[z0,z79,z24,z1,z3,z4,z6]),(0,[z0,z595,z1,z3,z4,z5,z6]),(0,[z0,z596,z1,z3,z4,z5,z6])],[(0,[z236,z0,z47,z3,z4,z5,z6]),(0,[z0,z1,z597,z3,z4,z5,z6]),(0,[z0,z1,z3,z598,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z599]),(0,[z0,z1,z512,z3,z4,z5,z6]),(0,[z0,z600,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z601])],[(0,[z167,z0,z1,z3,z4,z84,z6]),(0,[z0,z24,z1,z3,z71,z4,z6]),(1,[z0,z8,z3,z4,z60,z6]),(0,[z0,z1,z3,z4,z5,z602,z6]),(1,[z0,z1,z244,z4,z85,z6]),(0,[z0,z1,z3,z127,z4,z107,z6]),(0,[z0,z1,z3,z603,z4,z5,z6])],[(0,[z604,z0,z1,z3,z4,z5,z6]),(0,[z69,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z605,z5,z6]),(0,[z0,z606,z1,z3,z4,z5,z6]),(0,[z0,z378,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z607,z5,z6])]],
   [[(0,[z0,z1,z3,z608,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z609,z6]),(0,[z0,z1,z3,z4,z5,z610,z6]),(0,[z0,z24,z1,z3,z4,z60,z6])],[(0,[z0,z611,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z612,z5,z6]),(0,[z0,z24,z24,z1,z3,z4,z6]),(0,[z0,z1,z3,z9,z4,z5,z6]),(0,[z0,z8,z1,z3,z4,z60,z6]),(0,[z613,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z614,z5,z6])],[(0,[z0,z1,z615,z3,z4,z5,z6]),(0,[z0,z1,z616,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z91,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z617])],[(0,[z0,z1,z3,z4,z618,z5,z6]),(0,[z619,z0,z1,z3,z4,z5,z6]),(0,[z620,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z621]),(0,[z0,z1,z622,z3,z4,z5,z6])],[(0,[z623,z0,z1,z3,z4,z5,z6]),(0,[z0,z624,z1,z3,z4,z5,z6]),(0,[z0,z1,z625,z3,z4,z5,z6]),(0,[z0,z24,z1,z3,z151,z4,z6]),(0,[z626,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z125]),(0,[z0,z1,z3,z4,z627,z5,z6]),(0,[z628,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z629,z3,z4,z5,z6]),(0,[z0,z1,z3,z630,z4,z5,z6]),(0,[z0,z1,z93,z3,z4,z394,z6]),(0,[z0,z631,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z632,z6]),(0,[z0,z1,z633,z3,z4,z5,z6]),(0,[z0,z118,z24,z1,z3,z4,z6])]],
   [[(0,[z167,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z634,z4,z5,z6]),(0,[z0,z635,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z151,z4,z6,z176]),(0,[z0,z636,z1,z3,z4,z5,z6])],[(0,[z236,z0,z1,z3,z4,z5,z6]),(0,[z256,z0,z1,z136,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z637]),(0,[z406,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z524,z6]),(1,[z0,z1,z103,z120,z5,z6]),(0,[z0,z1,z244,z3,z4,z5,z6])],[(0,[z0,z1,z638,z3,z4,z5,z6]),(0,[z0,z1,z639,z3,z4,z5,z6])],[(1,[z0,z1,z3,z4,z5,z94]),(0,[z0,z1,z3,z4,z5,z640,z6]),(0,[z0,z1,z201,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z641,z6]),(0,[z0,z231,z3,z4,z5,z6,z176])],[(0,[z0,z109,z1,z201,z4,z5,z6]),(0,[z0,z24,z1,z3,z4,z6,z131]),(0,[z0,z8,z1,z3,z4,z107,z6]),(0,[z0,z79,z1,z3,z105,z4,z5]),(0,[z0,z1,z3,z4,z642,z5,z6])],[(0,[z0,z24,z1,z136,z3,z4,z6]),(0,[z0,z643,z1,z3,z4,z5,z6]),(0,[z644,z0,z1,z3,z4,z5,z6])],[(0,[z645,z0,z1,z3,z4,z5,z6]),(0,[z646,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z105,z4,z5,z147]),(0,[z0,z23,z1,z3,z4,z85,z6])],[(0,[z0,z1,z3,z4,z647,z5,z6]),(1,[z168,z1,z3,z4,z84,z6]),(0,[z0,z1,z3,z4,z5,z6,z648]),(0,[z0,z1,z3,z4,z649,z5,z6])]],
   [[(0,[z650,z0,z1,z3,z4,z5,z6]),(0,[z651,z0,z1,z3,z4,z5,z6]),(0,[z0,z165,z1,z3,z105,z5,z6]),(0,[z0,z8,z1,z304,z3,z4,z6]),(0,[z0,z1,z75,z93,z3,z4,z5]),(0,[z0,z1,z3,z652,z4,z5,z6])],[(0,[z0,z1,z3,z4,z653,z5,z6]),(0,[z0,z1,z3,z4,z5,z654,z6]),(0,[z0,z1,z3,z4,z5,z655,z6]),(0,[z0,z1,z656,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z54,z6]),(0,[z26,z0,z1,z3,z4,z5,z6]),(0,[z0,z109,z3,z34,z4,z5,z6]),(1,[z0,z1,z3,z554,z4,z6]),(0,[z0,z1,z152,z3,z4,z5,z6]),(0,[z0,z24,z1,z3,z243,z4,z6]),(0,[z0,z1,z365,z3,z4,z5,z6]),(0,[z0,z1,z657,z3,z4,z5,z6]),(0,[z0,z1,z304,z3,z5,z6,z176])],[(0,[z0,z1,z3,z181,z5,z6,z180]),(1,[z0,z1,z304,z3,z6,z176])],[(0,[z0,z658,z1,z3,z4,z5,z6]),(0,[z659,z0,z1,z3,z4,z5,z6]),(0,[z660,z0,z1,z3,z4,z5,z6]),(0,[z661,z0,z1,z3,z4,z5,z6]),(0,[z194,z0,z1,z3,z4,z5,z6]),(0,[z0,z8,z1,z3,z4,z6,z125]),(0,[z0,z1,z3,z662,z4,z5,z6])],[(0,[z0,z1,z3,z663,z4,z5,z6]),(1,[z74,z0,z3,z130,z5,z6]),(0,[z0,z1,z3,z4,z5,z664,z6]),(0,[z0,z1,z3,z4,z665,z5,z6])],[(0,[z0,z1,z666,z3,z4,z5,z6]),(0,[z667,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z668,z5,z6]),(0,[z292,z0,z8,z1,z3,z4,z6]),(0,[z669,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z670,z3,z4,z5,z6])],[(0,[z26,z0,z1,z3,z4,z5,z128]),(0,[z0,z1,z3,z4,z5,z671,z6]),(0,[z0,z24,z165,z1,z3,z4,z6])]],
   [[(0,[z69,z1,z25,z3,z4,z5,z6]),(0,[z0,z200,z25,z3,z4,z5,z6]),(0,[z146,z0,z1,z3,z4,z5,z6]),(0,[z672,z0,z1,z3,z4,z5,z6]),(0,[z0,z8,z165,z1,z3,z4,z6]),(0,[z0,z1,z207,z3,z4,z88,z6]),(0,[z673,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z674,z4,z5,z6]),(0,[z675,z0,z1,z3,z4,z5,z6])],[(0,[z0,z676,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z91,z6,z92])],[(0,[z256,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z191,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z677]),(0,[z168,z0,z1,z3,z4,z84,z6]),(0,[z146,z0,z1,z3,z30,z5,z6]),(1,[z0,z1,z3,z181,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z678])],[(0,[z0,z1,z3,z679,z4,z5,z6]),(0,[z0,z200,z47,z3,z4,z5,z6]),(0,[z0,z680,z1,z3,z4,z5,z6]),(0,[z0,z1,z681,z3,z4,z5,z6]),(0,[z0,z1,z157,z3,z4,z91,z6]),(0,[z0,z1,z157,z3,z127,z4,z6])],[(0,[z356,z0,z24,z1,z3,z4,z6]),(0,[z682,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z394,z6]),(0,[z683,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z59,z4,z95,z6]),(0,[z0,z24,z1,z567,z3,z4,z6]),(0,[z0,z8,z1,z3,z4,z6,z648]),(0,[z0,z1,z3,z4,z684,z5,z6])],[(0,[z685,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z686,z3,z4,z5,z6]),(0,[z0,z1,z3,z687,z4,z5,z6]),(0,[z0,z1,z688,z3,z4,z5,z6]),(0,[z689,z0,z1,z3,z4,z5,z6]),(0,[z690,z0,z1,z3,z4,z5,z6]),(0,[z691,z0,z1,z3,z4,z5,z6])],[(1,[z0,z1,z3,z4,z220,z6]),(0,[z0,z692,z1,z3,z4,z5,z6]),(0,[z26,z0,z361,z3,z4,z5,z6]),(0,[z693,z0,z1,z3,z4,z5,z6]),(0,[z0,z8,z1,z3,z4,z91,z6]),(0,[z0,z8,z1,z3,z127,z4,z6]),(0,[z0,z1,z3,z4,z694,z5,z6])]],
   [[(0,[z256,z1,z136,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z695,z6]),(0,[z0,z8,z1,z3,z34,z4,z6])],[(0,[z0,z1,z3,z4,z5,z696,z6]),(0,[z0,z1,z3,z4,z5,z6,z697]),(0,[z0,z1,z3,z4,z5,z698,z6])],[(0,[z0,z1,z3,z4,z699,z5,z6]),(0,[z0,z24,z1,z3,z4,z42,z6])],[(0,[z263,z0,z1,z3,z4,z5,z6]),(0,[z0,z8,z8,z1,z3,z4,z6])],[(0,[z69,z263,z1,z3,z4,z5,z6]),(0,[z168,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z304,z3,z151,z5,z6]),(0,[z0,z1,z75,z3,z4,z5,z6])],[(0,[z700,z0,z1,z3,z4,z5,z6]),(0,[z701,z0,z1,z3,z4,z5,z6]),(0,[z0,z8,z1,z3,z105,z4,z6]),(0,[z0,z1,z157,z3,z4,z17,z6])],[(0,[z702,z0,z1,z3,z4,z5,z6]),(1,[z36,z1,z3,z42,z5,z6]),(0,[z0,z1,z3,z4,z5,z703,z6]),(0,[z0,z309,z8,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z704,z5,z6]),(1,[z0,z1,z3,z4,z524,z6]),(0,[z0,z1,z3,z705,z4,z5,z6]),(1,[z0,z1,z157,z3,z127,z4])],[(0,[z0,z100,z1,z3,z4,z5,z6]),(0,[z706,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z362,z3,z4,z5,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z707,z3,z4,z5]),(0,[z0,z1,z3,z30,z5,z125]),(0,[z0,z1,z3,z4,z5,z708]),(0,[z0,z1,z3,z151,z161,z6]),(0,[z0,z1,z709,z3,z4,z6])],[(0,[z0,z710,z1,z3,z4,z6]),(0,[z0,z1,z711,z3,z5,z6]),(0,[z47,z712,z3,z4,z5,z6]),(0,[z69,z1,z3,z37,z5,z94]),(0,[z0,z1,z3,z4,z5,z713]),(0,[z43,z1,z3,z19,z5,z6]),(0,[z0,z24,z1,z152,z3,z4]),(0,[z0,z1,z714,z3,z4,z6]),(0,[z0,z1,z715,z3,z4,z6])],[(0,[z146,z1,z3,z4,z5,z147]),(0,[z0,z1,z3,z4,z716,z6])],[(0,[z0,z24,z3,z4,z513,z6]),(0,[z0,z1,z3,z4,z717,z6]),(0,[z0,z24,z1,z718,z4,z6]),(0,[z719,z8,z1,z3,z4,z6])],[(0,[z146,z1,z3,z30,z5,z147]),(0,[z0,z24,z3,z4,z431,z6])],[(0,[z0,z1,z720,z4,z5,z6]),(0,[z74,z0,z3,z721,z5,z6]),(0,[z0,z8,z1,z3,z181,z6])],[(0,[z0,z73,z3,z279,z5,z6]),(0,[z0,z73,z3,z4,z280,z6]),(0,[z0,z297,z1,z3,z4,z188])],[(0,[z0,z722,z3,z4,z5,z6]),(0,[z0,z8,z1,z3,z30,z6]),(0,[z0,z24,z1,z362,z3,z4]),(0,[z0,z231,z157,z3,z4,z6])]],
   [[(0,[z0,z1,z3,z723,z5,z6]),(0,[z0,z1,z3,z4,z5,z724]),(0,[z43,z24,z1,z3,z4,z6]),(0,[z0,z24,z3,z4,z6,z359]),(0,[z0,z1,z3,z725,z4,z6]),(0,[z0,z3,z4,z5,z726,z180]),(0,[z0,z727,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z728,z6]),(0,[z0,z1,z3,z729,z4,z5]),(0,[z0,z1,z4,z730,z5,z6])],[(0,[z0,z183,z158,z3,z4,z6]),(0,[z0,z1,z3,z4,z5,z94]),(0,[z74,z481,z24,z3,z4,z6]),(0,[z0,z79,z3,z4,z88,z215]),(0,[z0,z1,z731,z3,z4,z6])],[],[(0,[z0,z1,z3,z732,z5,z6]),(0,[z0,z24,z1,z3,z191,z6]),(0,[z0,z8,z1,z3,z4,z175]),(0,[z0,z1,z103,z362,z120,z5]),(0,[z0,z1,z157,z3,z4,z383]),(0,[z0,z1,z3,z105,z733,z5])],[(0,[z0,z1,z3,z4,z734,z6]),(0,[z0,z1,z735,z3,z4,z6]),(0,[z356,z233,z1,z3,z4,z6]),(0,[z0,z3,z4,z5,z6,z736]),(0,[z0,z1,z3,z4,z737,z6])],[(0,[z0,z738,z73,z3,z4,z6]),(0,[z0,z739,z1,z3,z4,z6]),(0,[z0,z8,z165,z3,z59,z6])],[(0,[z0,z25,z3,z4,z220,z6]),(0,[z0,z1,z3,z4,z740,z6]),(0,[z0,z741,z1,z3,z4,z6]),(0,[z0,z153,z3,z4,z382,z180])]],
   [[(0,[z0,z1,z3,z279,z5,z48]),(0,[z0,z1,z3,z4,z280,z48])],[(0,[z0,z1,z742,z4,z5,z6]),(0,[z613,z1,z3,z37,z5,z6]),(0,[z0,z1,z3,z554,z4,z6]),(0,[z0,z1,z157,z3,z4,z182])],[(0,[z0,z1,z3,z4,z5,z743]),(0,[z0,z1,z744,z4,z5,z6]),(0,[z0,z47,z3,z4,z220,z6]),(0,[z0,z1,z3,z4,z745,z6]),(0,[z0,z24,z1,z103,z120,z6]),(0,[z0,z1,z304,z3,z6,z176])],[(0,[z194,z8,z1,z3,z4,z125]),(0,[z0,z24,z3,z4,z337,z6])],[(0,[z74,z0,z3,z130,z5,z6])],[(0,[z0,z1,z746,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z747]),(0,[z26,z1,z27,z4,z97,z6]),(0,[z0,z24,z1,z3,z4,z128]),(0,[z0,z1,z3,z4,z748,z6]),(0,[z749,z1,z3,z4,z5,z6]),(0,[z0,z1,z4,z750,z85,z6])],[(0,[z0,z436,z24,z3,z4,z6]),(0,[z0,z1,z3,z4,z751,z6])],[(0,[z263,z38,z3,z4,z5,z6]),(0,[z0,z1,z3,z30,z5,z147]),(0,[z0,z1,z3,z4,z752,z6])]],
   [[(0,[z0,z753,z3,z4,z5,z6]),(0,[z0,z8,z1,z75,z3,z19]),(0,[z0,z1,z75,z3,z704,z5])],[(0,[z0,z1,z3,z754,z4,z6]),(0,[z0,z1,z3,z4,z121,z6]),(0,[z0,z1,z3,z4,z5,z755]),(0,[z0,z1,z567,z4,z107,z6]),(0,[z0,z756,z3,z4,z5,z6])],[(0,[z0,z141,z3,z4,z5,z6]),(0,[z1,z3,z4,z757,z5,z6]),(0,[z0,z1,z3,z4,z758,z6])],[(0,[z236,z35,z25,z3,z4,z6]),(0,[z0,z1,z3,z759,z5,z6]),(0,[z0,z760,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z761,z5]),(0,[z0,z1,z3,z4,z394,z6])],[(0,[z0,z73,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z762]),(0,[z74,z0,z8,z3,z130,z6]),(0,[z0,z763,z3,z4,z5,z6])],[(0,[z24,z233,z47,z3,z4,z6]),(0,[z0,z764,z1,z3,z4,z6]),(0,[z0,z24,z3,z4,z765,z6]),(0,[z0,z1,z3,z195,z4,z6]),(0,[z766,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z220,z6]),(0,[z0,z24,z468,z3,z4,z6]),(0,[z0,z231,z304,z3,z6,z176])],[(0,[z236,z183,z25,z3,z4,z6]),(0,[z0,z24,z282,z3,z4,z6]),(0,[z767,z1,z3,z4,z5,z6])]],
   [[(0,[z0,z8,z56,z3,z4,z6]),(0,[z0,z1,z3,z768,z5,z6])],[(0,[z0,z73,z3,z191,z5,z6]),(0,[z0,z73,z3,z4,z5,z128]),(0,[z0,z1,z3,z4,z5,z769]),(0,[z250,z325,z1,z3,z4,z6]),(0,[z0,z3,z4,z5,z88,z726])],[(0,[z0,z1,z3,z4,z5,z770]),(0,[z0,z153,z3,z4,z5,z726])],[(0,[z74,z0,z3,z554,z130,z6]),(0,[z0,z3,z59,z4,z771,z6]),(0,[z0,z110,z1,z3,z9,z6])],[(1,[z1,z3,z772,z5,z6]),(0,[z167,z141,z3,z4,z58,z6])],[(0,[z0,z1,z3,z4,z773,z6]),(0,[z0,z1,z3,z4,z774,z6]),(0,[z0,z1,z3,z4,z5,z775]),(0,[z0,z776,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z777]),(0,[z36,z1,z3,z42,z5,z6]),(0,[z43,z3,z4,z60,z5,z6]),(0,[z74,z0,z24,z3,z59,z6]),(0,[z0,z24,z1,z3,z4,z778]),(0,[z0,z1,z3,z4,z524,z6]),(0,[z0,z1,z4,z5,z779,z131]),(0,[z0,z1,z3,z4,z780,z6]),(0,[z0,z1,z157,z3,z127,z4])],[(0,[z0,z1,z3,z781,z5,z6]),(0,[z0,z1,z3,z4,z5,z48]),(0,[z0,z24,z295,z3,z4,z6]),(0,[z0,z231,z3,z4,z107,z6])],[(0,[z24,z25,z3,z4,z42,z6]),(0,[z506,z1,z3,z42,z5,z6]),(0,[z0,z1,z3,z782,z5,z6]),(0,[z74,z43,z24,z3,z4,z6]),(0,[z0,z24,z1,z3,z181,z6]),(0,[z0,z153,z3,z18,z5,z180]),(0,[z0,z1,z3,z4,z5,z783])]],
   [[(0,[z1,z3,z37,z772,z5,z6]),(0,[z0,z7,z1,z71,z4,z6]),(1,[z0,z1,z4,z5,z779]),(0,[z0,z1,z104,z4,z574,z5]),(0,[z0,z1,z93,z4,z394,z124]),(0,[z0,z784,z3,z4,z5,z6])],[(0,[z0,z24,z1,z3,z30,z6]),(0,[z0,z1,z3,z785,z4,z6]),(0,[z0,z24,z3,z4,z6,z599]),(0,[z0,z24,z3,z4,z6,z601])],[(0,[z0,z231,z304,z3,z4,z6])],[(0,[z0,z786,z25,z3,z4,z6]),(0,[z0,z1,z3,z191,z5,z48]),(0,[z0,z1,z3,z4,z787,z6]),(0,[z0,z79,z24,z3,z4,z88]),(0,[z0,z1,z788,z3,z4,z5]),(0,[z0,z1,z3,z780,z6,z176])],[(0,[z0,z789,z3,z4,z5,z6]),(0,[z0,z24,z3,z4,z609,z6]),(0,[z0,z24,z1,z790,z3,z4])],[(0,[z0,z24,z1,z3,z4,z791]),(0,[z0,z792,z1,z3,z4,z6])],[(0,[z0,z712,z3,z4,z5,z6]),(0,[z0,z1,z793,z3,z4,z5]),(0,[z0,z794,z1,z3,z4,z6]),(0,[z0,z24,z1,z3,z4,z175]),(0,[z0,z1,z3,z4,z6,z795])],[(0,[z0,z1,z3,z796,z4,z6]),(1,[z1,z3,z4,z5,z797]),(0,[z0,z798,z3,z4,z5,z6])]],
   [[(0,[z689,z25,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z799]),(0,[z69,z1,z3,z377,z5,z6]),(0,[z0,z1,z800,z3,z4,z5]),(0,[z0,z1,z3,z4,z801,z5]),(0,[z0,z24,z1,z3,z4,z802]),(0,[z0,z1,z3,z803,z5,z6]),(0,[z0,z1,z75,z3,z4,z394])],[(0,[z0,z804,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z805,z6]),(0,[z0,z8,z231,z3,z4,z6]),(0,[z0,z1,z4,z750,z5,z6])],[(0,[z0,z1,z806,z3,z4,z6]),(0,[z0,z1,z3,z4,z807,z6]),(0,[z0,z264,z3,z59,z4,z6]),(0,[z0,z1,z3,z4,z808,z5])],[(0,[z0,z361,z3,z4,z5,z48]),(0,[z0,z809,z1,z3,z4,z6]),(0,[z288,z0,z24,z3,z4,z6]),(0,[z0,z1,z75,z3,z422,z5]),(0,[z0,z1,z3,z4,z810,z6]),(0,[z0,z1,z811,z4,z5,z6]),(0,[z0,z24,z1,z3,z4,z812]),(0,[z0,z1,z3,z813,z5,z6])],[(0,[z0,z1,z4,z5,z814,z6]),(0,[z0,z1,z4,z5,z815,z6]),(0,[z0,z1,z3,z195,z181,z6]),(0,[z0,z1,z4,z5,z779,z6])],[(0,[z0,z1,z3,z4,z816,z6]),(0,[z194,z24,z1,z3,z4,z125]),(0,[z0,z1,z3,z4,z817,z6]),(0,[z0,z8,z1,z93,z4,z124])],[],[(0,[z263,z47,z3,z4,z220,z6]),(0,[z0,z1,z3,z4,z818,z6]),(0,[z74,z0,z24,z3,z243,z6]),(0,[z0,z1,z3,z4,z5,z819]),(0,[z0,z1,z3,z820,z4,z6])]],
   [[(0,[z0,z1,z3,z821,z5,z6]),(0,[z0,z1,z3,z279,z5,z128]),(0,[z0,z1,z3,z4,z280,z128])],[(0,[z0,z1,z3,z4,z5,z822]),(0,[z0,z200,z24,z201,z4,z6]),(0,[z0,z1,z3,z4,z95,z6]),(0,[z0,z8,z24,z3,z4,z6]),(0,[z0,z8,z600,z3,z4,z6]),(0,[z0,z1,z104,z4,z5,z779])],[(0,[z0,z823,z1,z3,z4,z6]),(0,[z0,z100,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z5,z824]),(0,[z0,z24,z1,z75,z3,z19]),(0,[z1,z3,z4,z5,z6,z825])],[(0,[z0,z1,z3,z4,z6,z826])],[(0,[z0,z1,z3,z827,z4,z6]),(0,[z0,z3,z4,z5,z175,z276])],[],[(0,[z263,z8,z47,z3,z4,z6]),(0,[z0,z1,z3,z4,z5,z828]),(0,[z0,z1,z3,z4,z829,z6]),(0,[z0,z1,z3,z4,z91,z383]),(0,[z0,z830,z1,z3,z4,z6])],[(0,[z0,z1,z3,z4,z831,z6]),(0,[z0,z1,z3,z105,z5,z470]),(0,[z0,z1,z3,z4,z832,z6])]],
   [[(0,[z0,z1,z3,z4,z833,z6]),(0,[z0,z361,z3,z279,z5,z6]),(0,[z0,z343,z24,z3,z4,z6]),(0,[z0,z257,z1,z567,z4,z6]),(0,[z0,z1,z3,z733,z5,z20])],[(0,[z43,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z834,z6]),(0,[z146,z1,z3,z185,z5,z147]),(0,[z0,z153,z3,z181,z5,z180])],[(0,[z0,z1,z3,z4,z835,z6])],[(0,[z203,z47,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z836])],[(0,[z837,z1,z3,z4,z5,z6]),(0,[z0,z8,z1,z3,z155,z4]),(0,[z0,z510,z24,z3,z4,z6]),(0,[z0,z1,z103,z226,z120,z5]),(0,[z0,z1,z512,z304,z3,z176])],[(0,[z24,z47,z25,z3,z4,z6]),(0,[z0,z73,z3,z4,z97,z6]),(0,[z203,z1,z3,z4,z58,z6]),(0,[z0,z3,z838,z4,z5,z6])],[(0,[z0,z1,z3,z4,z839,z6]),(0,[z0,z1,z3,z4,z5,z840]),(0,[z0,z24,z3,z9,z4,z6]),(0,[z0,z841,z1,z3,z4,z6])],[(0,[z263,z47,z3,z4,z54,z6]),(0,[z0,z8,z200,z201,z4,z6]),(0,[z74,z0,z1,z3,z155,z5]),(0,[z0,z24,z1,z3,z842,z4]),(0,[z0,z24,z3,z4,z528,z6]),(0,[z0,z8,z235,z3,z4,z6]),(0,[z0,z1,z3,z4,z843,z6]),(0,[z0,z1,z104,z4,z5,z131])]],
   [[(0,[z0,z1,z3,z4,z5,z844]),(0,[z0,z1,z3,z4,z150,z6]),(0,[z0,z1,z244,z4,z750,z6])],[(0,[z0,z1,z3,z845,z5,z6]),(0,[z0,z1,z3,z105,z5,z500]),(0,[z74,z0,z24,z3,z19,z6])],[(0,[z0,z1,z846,z4,z5,z6]),(0,[z0,z24,z404,z3,z4,z6]),(0,[z0,z1,z3,z37,z5,z119]),(0,[z0,z1,z3,z155,z4,z5]),(0,[z0,z1,z3,z4,z5,z847])],[(0,[z208,z1,z3,z4,z5,z147]),(0,[z0,z1,z3,z4,z848,z6]),(0,[z0,z1,z3,z4,z85,z175])],[(0,[z0,z1,z3,z4,z6,z849]),(0,[z0,z1,z3,z19,z733,z5])],[(0,[z0,z1,z152,z3,z4,z5])],[(0,[z0,z1,z3,z4,z850,z6]),(0,[z0,z3,z4,z6,z276,z359]),(0,[z0,z1,z157,z3,z4,z188]),(0,[z0,z1,z3,z4,z6,z851])],[(0,[z0,z1,z3,z4,z97,z48]),(0,[z0,z1,z852,z4,z5,z6]),(0,[z0,z853,z1,z3,z4,z6]),(0,[z0,z1,z854,z4,z5,z6])]],
   [[(0,[z1,z3,z4,z5,z797,z6]),(0,[z481,z8,z1,z3,z4,z6]),(0,[z0,z165,z3,z59,z95,z6]),(0,[z855,z24,z1,z3,z4,z6]),(0,[z0,z8,z79,z3,z4,z88])],[(0,[z1,z3,z742,z4,z5,z6]),(0,[z43,z24,z3,z4,z5,z6]),(0,[z0,z1,z75,z3,z261,z5])],[],[(0,[z0,z24,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z5,z856]),(0,[z167,z1,z3,z4,z58,z6]),(0,[z0,z141,z3,z4,z84,z6]),(0,[z0,z1,z857,z3,z4,z5]),(0,[z858,z1,z3,z4,z5,z6]),(0,[z0,z24,z231,z3,z4,z6]),(0,[z0,z79,z207,z3,z4,z88])],[(0,[z254,z47,z3,z4,z5,z6]),(0,[z0,z558,z24,z3,z4,z6])],[(0,[z0,z1,z3,z4,z859,z6]),(0,[z0,z24,z1,z3,z4,z119]),(0,[z0,z860,z1,z3,z4,z6])],[(0,[z0,z1,z3,z4,z861,z6]),(0,[z0,z1,z3,z862,z5,z6]),(0,[z0,z863,z3,z4,z5,z6]),(0,[z0,z864,z3,z4,z5,z6]),(1,[z0,z838,z4,z5,z6]),(0,[z0,z1,z304,z3,z353,z6])],[(0,[z0,z1,z3,z865,z5,z6]),(0,[z0,z1,z3,z4,z866,z6]),(0,[z36,z8,z1,z3,z42,z6]),(0,[z0,z1,z688,z4,z5,z131]),(0,[z0,z867,z1,z3,z4,z6])]],
   [[(0,[z0,z183,z1,z3,z4,z6]),(0,[z0,z868,z1,z3,z4,z6]),(0,[z0,z8,z3,z4,z6,z162]),(1,[z0,z1,z3,z780,z6])],[(0,[z0,z1,z3,z869,z5,z6]),(0,[z870,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z871,z5,z6])],[(0,[z0,z8,z680,z3,z4,z6]),(0,[z0,z200,z201,z4,z5,z6]),(0,[z74,z0,z3,z353,z5,z6]),(0,[z0,z1,z3,z4,z6,z872]),(0,[z0,z52,z24,z3,z4,z6])],[(0,[z0,z361,z3,z4,z5,z128]),(0,[z0,z325,z141,z3,z4,z6]),(0,[z0,z109,z99,z34,z4,z6]),(0,[z0,z873,z1,z3,z4,z6]),(0,[z0,z1,z3,z105,z5,z372])],[(0,[z0,z1,z3,z279,z97,z6]),(0,[z0,z1,z3,z874,z4,z6]),(0,[z0,z24,z546,z3,z4,z6]),(0,[z0,z8,z3,z4,z281,z6]),(0,[z0,z624,z1,z4,z107,z6]),(0,[z0,z1,z875,z4,z5,z6]),(0,[z876,z1,z3,z4,z5,z6]),(0,[z74,z0,z3,z155,z130,z5])],[(0,[z0,z1,z3,z877,z5,z6]),(0,[z13,z1,z3,z4,z84,z6]),(0,[z74,z0,z24,z3,z130,z6]),(0,[z0,z376,z24,z3,z4,z6]),(0,[z1,z3,z4,z5,z6,z878])],[(0,[z0,z1,z3,z4,z5,z778]),(0,[z0,z8,z73,z3,z4,z6]),(0,[z0,z109,z838,z4,z5,z6]),(0,[z0,z1,z3,z4,z6,z879]),(0,[z719,z1,z3,z4,z5,z6]),(0,[z74,z0,z3,z603,z5,z6]),(0,[z0,z1,z103,z120,z524,z6]),(0,[z0,z1,z3,z880,z4,z6])],[(0,[z74,z0,z152,z3,z130,z5]),(0,[z0,z1,z75,z3,z733,z5])]],
   [[(0,[z368,z0,z24,z3,z4,z6]),(0,[z0,z24,z3,z679,z4,z6]),(0,[z263,z24,z47,z3,z4,z6]),(0,[z0,z1,z3,z279,z280,z6]),(0,[z298,z1,z3,z42,z5,z6]),(0,[z0,z1,z3,z4,z881,z6]),(0,[z0,z1,z3,z4,z882,z6]),(0,[z0,z1,z883,z4,z5,z6]),(0,[z884,z1,z3,z4,z5,z6]),(0,[z0,z8,z1,z3,z18,z6])],[(0,[z0,z885,z1,z3,z4,z6]),(0,[z0,z1,z886,z3,z4,z5]),(0,[z0,z24,z3,z68,z4,z6]),(0,[z0,z1,z887,z4,z5,z6]),(0,[z0,z1,z4,z5,z888,z6]),(0,[z0,z1,z3,z4,z889,z6]),(0,[z0,z3,z59,z721,z5,z6]),(0,[z0,z1,z3,z4,z890,z6])],[(0,[z0,z1,z3,z4,z891,z5]),(0,[z0,z1,z3,z4,z892,z6]),(0,[z0,z3,z4,z765,z89,z6]),(0,[z0,z1,z75,z3,z102,z5])],[(0,[z0,z1,z3,z4,z6,z893]),(0,[z0,z1,z3,z894,z5,z6]),(0,[z0,z231,z3,z151,z4,z6]),(0,[z0,z1,z3,z4,z91,z92])],[],[(0,[z0,z1,z3,z895,z5,z6]),(0,[z0,z24,z638,z3,z4,z6]),(0,[z0,z1,z3,z4,z6,z896]),(0,[z0,z1,z3,z842,z4,z5])],[(0,[z236,z712,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z791])],[(0,[z0,z183,z3,z4,z60,z6]),(0,[z0,z1,z3,z554,z155,z4]),(0,[z0,z378,z1,z3,z4,z648]),(0,[z0,z1,z897,z3,z4,z6]),(0,[z0,z3,z4,z5,z6,z898]),(0,[z0,z899,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z5,z175])]],
   [[(0,[z0,z1,z3,z900,z5,z6]),(0,[z0,z24,z1,z901,z4,z6]),(0,[z0,z217,z24,z3,z4,z6]),(0,[z0,z24,z1,z902,z4,z6]),(0,[z0,z1,z302,z3,z127,z4])],[(0,[z0,z1,z3,z4,z903,z6]),(0,[z0,z1,z3,z4,z5,z802])],[(0,[z288,z25,z3,z4,z5,z6]),(0,[z0,z1,z3,z904,z4,z6]),(0,[z0,z1,z790,z3,z4,z5]),(0,[z0,z8,z289,z3,z4,z6]),(0,[z0,z8,z1,z3,z4,z724]),(0,[z0,z1,z3,z905,z5,z6])],[(0,[z0,z1,z3,z4,z906,z6]),(0,[z0,z165,z3,z571,z5,z6]),(0,[z0,z24,z3,z4,z482,z6])],[(0,[z0,z8,z1,z3,z4,z94]),(0,[z0,z1,z3,z4,z907,z6]),(0,[z0,z79,z3,z4,z5,z88])],[(0,[z0,z1,z3,z908,z5,z6]),(0,[z0,z1,z3,z4,z5,z909]),(0,[z0,z910,z1,z3,z4,z6]),(0,[z911,z1,z3,z4,z5,z6]),(0,[z317,z0,z1,z3,z161,z6])],[(0,[z194,z1,z3,z4,z5,z125])],[(0,[z0,z8,z361,z3,z4,z6]),(0,[z0,z1,z3,z912,z5,z6]),(0,[z0,z24,z3,z4,z122,z6]),(0,[z0,z1,z3,z4,z5,z779])]],
   [[(0,[z0,z1,z838,z4,z5,z6])],[(0,[z227,z1,z3,z4,z58,z6])],[(0,[z0,z1,z913,z3,z4,z5]),(0,[z0,z838,z34,z4,z5,z6]),(0,[z481,z24,z1,z3,z4,z6]),(0,[z0,z914,z1,z3,z4,z6])],[(0,[z0,z1,z915,z3,z4,z5]),(0,[z0,z24,z165,z3,z59,z6]),(0,[z0,z1,z207,z3,z4,z6]),(0,[z0,z231,z3,z4,z5,z175])],[(0,[z0,z1,z3,z4,z916,z6]),(0,[z0,z3,z4,z5,z6,z276]),(1,[z0,z1,z4,z750,z6])],[(0,[z0,z917,z1,z3,z4,z6])],[(0,[z0,z1,z3,z4,z6,z918]),(0,[z0,z1,z3,z279,z5,z6]),(0,[z0,z1,z3,z4,z280,z6]),(0,[z0,z1,z3,z919,z5,z6]),(0,[z1,z3,z4,z5,z6,z920])],[(0,[z0,z1,z3,z4,z97,z128]),(0,[z0,z1,z3,z4,z921,z6])]],
   [[(0,[z0,z1,z922,z4,z5,z6]),(0,[z0,z1,z3,z4,z6,z923]),(0,[z0,z1,z3,z4,z924,z6])],[(0,[z0,z1,z3,z925,z5,z6]),(0,[z36,z24,z1,z3,z42,z6]),(0,[z0,z3,z4,z5,z6,z926]),(0,[z0,z927,z3,z4,z5,z6]),(0,[z0,z928,z1,z3,z4,z6])],[(0,[z0,z929,z3,z4,z5,z6]),(0,[z930,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z191,z280,z6]),(0,[z0,z1,z3,z4,z931,z6]),(0,[z0,z932,z3,z4,z5,z6]),(0,[z0,z933,z3,z4,z5,z6]),(0,[z0,z1,z3,z19,z5,z458]),(0,[z0,z24,z639,z3,z4,z6]),(0,[z0,z1,z3,z4,z6,z215])],[(0,[z26,z73,z27,z4,z5,z6]),(0,[z0,z934,z3,z4,z5,z6]),(0,[z0,z1,z3,z772,z5,z6]),(0,[z74,z0,z24,z3,z4,z6]),(0,[z203,z118,z1,z3,z4,z6]),(1,[z0,z3,z4,z5,z726]),(0,[z0,z231,z3,z4,z85,z6])],[],[(0,[z0,z1,z3,z935,z4,z6]),(0,[z168,z1,z3,z4,z816,z6]),(0,[z0,z1,z3,z4,z5,z936]),(0,[z0,z1,z3,z4,z937,z6]),(0,[z0,z1,z3,z4,z6,z383])],[(0,[z0,z1,z3,z4,z938,z6])]],
   [[(0,[z0,z1,z440,z4,z107,z6]),(0,[z0,z1,z3,z105,z5,z20])],[(0,[z0,z24,z3,z274,z4,z6]),(0,[z0,z1,z939,z3,z4,z6])],[(0,[z0,z1,z3,z4,z5,z940]),(0,[z0,z24,z1,z3,z18,z6]),(0,[z186,z0,z1,z365,z4,z6])],[(0,[z0,z361,z3,z4,z280,z6]),(0,[z0,z941,z3,z4,z5,z6]),(0,[z69,z1,z3,z37,z5,z6]),(0,[z0,z1,z3,z4,z5,z942]),(0,[z943,z1,z3,z4,z5,z6]),(0,[z0,z1,z264,z3,z4,z6]),(0,[z0,z187,z1,z3,z105,z5]),(0,[z44,z0,z1,z3,z353,z6]),(0,[z0,z1,z3,z4,z62,z92]),(0,[z0,z1,z3,z17,z780,z6]),(0,[z0,z1,z75,z3,z19,z5])],[(0,[z0,z944,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z945,z6]),(0,[z0,z304,z3,z6,z276,z176]),(0,[z0,z1,z157,z3,z946,z4])],[(0,[z0,z1,z947,z4,z5,z6]),(0,[z0,z1,z3,z4,z948,z6]),(0,[z69,z1,z3,z37,z5,z119]),(0,[z0,z1,z3,z46,z17,z6])],[(0,[z26,z1,z27,z4,z5,z48]),(0,[z0,z949,z3,z4,z5,z6]),(0,[z0,z8,z109,z34,z4,z6]),(0,[z0,z1,z3,z4,z950,z6]),(0,[z0,z8,z1,z3,z105,z20]),(0,[z0,z1,z4,z5,z124,z779])],[(0,[z0,z1,z3,z4,z5,z797])]],
   [[(0,[z0,z24,z587,z3,z4,z6]),(0,[z0,z1,z3,z185,z5,z6]),(0,[z0,z1,z633,z4,z85,z6]),(0,[z0,z229,z1,z3,z4,z454]),(0,[z0,z153,z3,z195,z4,z180])],[(0,[z0,z1,z3,z37,z226,z5]),(0,[z0,z1,z3,z951,z4,z6]),(0,[z855,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z952,z5,z6]),(0,[z0,z1,z3,z4,z175,z383])],[(0,[z0,z8,z3,z4,z322,z6]),(0,[z0,z1,z3,z4,z226,z5]),(0,[z0,z1,z93,z4,z5,z779])],[(0,[z552,z25,z3,z4,z5,z6]),(0,[z0,z24,z223,z3,z4,z6]),(0,[z0,z953,z1,z3,z4,z6])],[(0,[z0,z1,z3,z4,z5,z6]),(0,[z0,z954,z3,z4,z5,z6]),(0,[z0,z955,z3,z4,z5,z6]),(0,[z167,z1,z3,z4,z816,z6]),(0,[z0,z24,z3,z4,z571,z6]),(0,[z0,z1,z3,z4,z733,z5])],[(0,[z0,z1,z3,z956,z5,z6]),(0,[z0,z1,z3,z4,z5,z957]),(0,[z1,z3,z4,z816,z5,z6]),(0,[z0,z1,z3,z4,z958,z6]),(0,[z0,z1,z4,z107,z750,z6])],[(0,[z26,z8,z1,z27,z4,z6]),(0,[z0,z1,z3,z4,z5,z119]),(0,[z0,z1,z3,z30,z5,z6]),(0,[z0,z8,z1,z104,z4,z131]),(0,[z0,z79,z3,z4,z5,z726])],[(0,[z0,z100,z109,z34,z4,z6]),(0,[z0,z1,z3,z195,z18,z6])]],
   [[(0,[z0,z24,z139,z3,z4,z6]),(0,[z0,z1,z3,z4,z6,z959]),(0,[z0,z24,z115,z3,z4,z6]),(0,[z0,z1,z3,z4,z960,z6]),(0,[z0,z153,z1,z3,z181,z5]),(0,[z0,z961,z3,z4,z5,z6]),(0,[z0,z1,z304,z3,z780,z6]),(0,[z0,z1,z512,z3,z4,z5])],[(0,[z0,z1,z3,z191,z5,z6]),(0,[z0,z1,z3,z4,z5,z128]),(0,[z0,z24,z1,z3,z956,z6]),(0,[z0,z1,z3,z4,z91,z454])],[(0,[z45,z1,z3,z4,z5,z125]),(0,[z0,z8,z3,z4,z6,z276]),(0,[z0,z962,z3,z4,z5,z6])],[(0,[z0,z24,z221,z3,z4,z6]),(0,[z0,z1,z963,z3,z4,z5]),(0,[z0,z1,z3,z964,z5,z6]),(0,[z0,z1,z965,z3,z4,z6]),(0,[z0,z1,z3,z4,z966,z6]),(0,[z0,z1,z3,z4,z5,z967])],[(0,[z0,z1,z3,z4,z6,z968]),(0,[z0,z969,z3,z4,z5,z6])],[(0,[z0,z970,z3,z4,z5,z6]),(0,[z74,z0,z264,z3,z130,z6]),(0,[z0,z971,z3,z4,z5,z6]),(0,[z0,z1,z3,z946,z4,z91])],[(0,[z263,z712,z3,z4,z5,z6]),(0,[z0,z1,z3,z191,z5,z128]),(0,[z0,z1,z3,z4,z771,z6]),(0,[z0,z1,z3,z172,z6,z176])],[(0,[z0,z35,z1,z3,z4,z6]),(0,[z69,z24,z25,z3,z4,z6]),(0,[z0,z1,z3,z972,z4,z6]),(0,[z1,z3,z4,z58,z816,z6])]],
   [[(0,[z0,z201,z838,z4,z5,z6]),(0,[z0,z231,z3,z4,z5,z6]),(0,[z0,z1,z3,z151,z17,z6])],[(0,[z1,z712,z3,z4,z5,z6]),(0,[z0,z361,z3,z4,z5,z6]),(1,[z43,z24,z3,z4,z6]),(0,[z0,z3,z4,z60,z6,z359]),(0,[z0,z1,z362,z3,z4,z5]),(0,[z0,z1,z93,z4,z5,z124])],[(0,[z0,z1,z579,z4,z5,z124]),(0,[z0,z24,z1,z93,z4,z124]),(0,[z0,z24,z3,z4,z89,z6]),(0,[z0,z1,z244,z71,z4,z6]),(0,[z0,z512,z3,z4,z5,z276])],[(0,[z700,z0,z24,z3,z4,z6]),(0,[z613,z1,z3,z4,z5,z147]),(0,[z0,z1,z3,z592,z17,z6]),(0,[z0,z1,z3,z105,z467,z20]),(0,[z0,z1,z3,z946,z4,z6])],[(0,[z0,z1,z3,z4,z5,z973]),(0,[z0,z974,z1,z3,z4,z6])],[(0,[z0,z1,z3,z4,z5,z975]),(0,[z0,z24,z148,z3,z4,z6])],[(0,[z0,z764,z361,z3,z4,z6]),(0,[z0,z361,z3,z191,z5,z6]),(0,[z0,z738,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z976,z6]),(0,[z0,z8,z1,z3,z185,z6]),(0,[z977,z1,z3,z4,z5,z6]),(0,[z0,z1,z152,z3,z554,z4])],[(0,[z0,z24,z25,z3,z4,z6]),(0,[z0,z1,z3,z4,z6,z978])]],
   [[(0,[z0,z8,z158,z3,z4,z6]),(0,[z0,z1,z979,z3,z4,z6]),(0,[z0,z1,z3,z980,z4,z6]),(0,[z0,z1,z3,z4,z981,z6]),(0,[z74,z0,z24,z3,z105,z6]),(0,[z982,z24,z1,z3,z4,z6])],[(0,[z0,z983,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z984]),(0,[z0,z1,z3,z985,z4,z6]),(0,[z0,z1,z3,z4,z6,z986])],[(0,[z0,z1,z3,z4,z5,z987]),(0,[z74,z481,z3,z130,z5,z6]),(0,[z0,z24,z629,z3,z4,z6])],[(0,[z0,z183,z24,z3,z4,z6]),(0,[z0,z809,z73,z3,z4,z6]),(0,[z0,z988,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z989,z6]),(0,[z0,z165,z3,z59,z5,z6])],[(0,[z0,z1,z3,z990,z5,z6]),(0,[z0,z24,z1,z854,z4,z6]),(0,[z0,z1,z3,z4,z382,z6])],[(0,[z263,z47,z3,z4,z5,z6]),(0,[z0,z1,z3,z991,z5,z6]),(0,[z0,z1,z3,z4,z5,z992]),(0,[z0,z1,z3,z243,z17,z6]),(0,[z0,z8,z1,z3,z4,z708]),(0,[z0,z8,z1,z3,z4,z226]),(0,[z0,z993,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z6,z994])],[(0,[z0,z1,z3,z995,z4,z6]),(0,[z0,z8,z1,z3,z4,z713])],[(0,[z69,z8,z1,z3,z37,z6]),(0,[z146,z8,z1,z3,z4,z147]),(0,[z0,z3,z4,z765,z5,z6])]],
   [[(0,[z1,z742,z27,z4,z5,z6]),(0,[z0,z1,z996,z4,z5,z6]),(0,[z0,z1,z3,z127,z4,z648]),(0,[z0,z8,z3,z705,z4,z6]),(0,[z0,z997,z3,z4,z5,z6]),(0,[z0,z1,z234,z4,z107,z6]),(0,[z0,z1,z3,z4,z998,z6])],[(0,[z0,z1,z901,z4,z5,z6]),(0,[z0,z24,z1,z3,z155,z4]),(0,[z0,z1,z3,z4,z6,z999]),(0,[z0,z1,z365,z4,z85,z6]),(0,[z0,z1,z3,z4,z5,z1000]),(0,[z0,z376,z1,z3,z105,z5])],[(0,[z0,z1,z1001,z3,z5,z6]),(0,[z0,z1,z3,z4,z218,z6]),(0,[z0,z3,z4,z5,z6,z1002])],[(0,[z481,z1,z3,z4,z5,z6]),(0,[z0,z8,z1,z3,z279,z6]),(0,[z0,z1003,z3,z4,z5,z6])],[(0,[z0,z1,z3,z1004,z5,z6]),(0,[z0,z1,z3,z4,z1005,z6]),(0,[z0,z1,z3,z1006,z4,z5]),(0,[z0,z1007,z1,z3,z4,z6]),(0,[z0,z1,z1008,z3,z4,z6]),(0,[z0,z1,z3,z4,z355,z6])],[(0,[z0,z1,z3,z1009,z5,z6]),(0,[z0,z1,z3,z4,z5,z1010])],[(0,[z0,z1,z3,z4,z1011,z6]),(0,[z26,z1,z27,z4,z5,z128]),(0,[z0,z3,z4,z60,z765,z6]),(0,[z0,z1,z3,z4,z175,z92])],[(0,[z0,z1,z3,z4,z5,z812]),(0,[z0,z231,z3,z4,z6,z92])]],
   [[(0,[z26,z24,z1,z27,z4,z6]),(0,[z0,z1012,z1,z3,z4,z6]),(0,[z1013,z1,z3,z4,z5,z6]),(0,[z0,z24,z1,z104,z4,z131]),(1,[z0,z3,z4,z765,z6])],[(0,[z0,z8,z1,z512,z3,z4])],[(0,[z0,z1,z1014,z4,z5,z6]),(0,[z0,z804,z361,z3,z4,z6]),(0,[z0,z1,z3,z1015,z5,z6]),(1,[z0,z1,z3,z946,z4])],[(0,[z0,z1,z1016,z3,z4,z5]),(0,[z0,z1017,z3,z4,z5,z6]),(0,[z278,z1,z3,z4,z5,z125]),(0,[z0,z24,z1,z3,z865,z6])],[(0,[z1,z3,z4,z5,z147,z797]),(0,[z0,z1,z3,z1018,z4,z6]),(0,[z1019,z1,z3,z4,z5,z6]),(0,[z74,z0,z264,z3,z4,z6]),(0,[z74,z0,z24,z3,z353,z6]),(0,[z0,z24,z1,z811,z4,z6])],[(0,[z236,z25,z3,z4,z5,z6]),(0,[z236,z8,z25,z3,z4,z6]),(0,[z0,z1,z3,z4,z97,z6]),(0,[z0,z1,z3,z4,z5,z1020]),(0,[z0,z1,z3,z1021,z5,z6]),(0,[z644,z1,z3,z37,z5,z6]),(0,[z0,z1,z3,z4,z6,z359]),(0,[z0,z635,z24,z3,z4,z6])],[(0,[z0,z73,z3,z4,z5,z48]),(0,[z0,z1,z3,z4,z1022,z5]),(0,[z0,z1,z3,z1023,z4,z5]),(0,[z0,z153,z24,z3,z4,z180]),(0,[z0,z24,z3,z4,z336,z6]),(0,[z0,z1,z3,z4,z5,z1024]),(0,[z0,z1,z3,z127,z946,z4])],[(0,[z0,z3,z4,z5,z6,z1025]),(0,[z69,z1,z3,z772,z5,z6]),(0,[z146,z1,z3,z4,z5,z797])]],
   [[(0,[z1,z3,z772,z42,z5,z6]),(0,[z0,z24,z487,z3,z4,z6]),(0,[z0,z24,z595,z3,z4,z6]),(0,[z0,z8,z3,z4,z765,z6]),(0,[z0,z1,z3,z4,z1026,z6])],[(0,[z1027,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z191,z97,z6]),(1,[z0,z3,z721,z5,z6]),(0,[z0,z1,z244,z4,z85,z6])],[(0,[z0,z1,z3,z105,z5,z134]),(0,[z870,z8,z1,z3,z4,z6])],[(0,[z0,z1,z3,z4,z1028,z6]),(0,[z0,z1029,z1,z3,z4,z6]),(0,[z168,z233,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z1030,z6]),(0,[z0,z1,z3,z18,z5,z6]),(0,[z0,z24,z1,z3,z4,z1031])],[(0,[z167,z158,z3,z4,z58,z6]),(0,[z0,z8,z544,z3,z4,z6])],[(0,[z0,z1,z3,z42,z226,z5]),(0,[z876,z8,z1,z3,z4,z6])],[(0,[z0,z1,z3,z4,z1032,z6]),(0,[z0,z1,z3,z4,z1033,z6]),(0,[z74,z43,z3,z130,z5,z6]),(0,[z0,z1,z3,z4,z6,z1034]),(1,[z0,z1,z3,z733,z5])]],
   [[(0,[z0,z1035,z1,z3,z4,z6]),(0,[z0,z24,z1,z3,z185,z6]),(0,[z0,z1,z3,z4,z1036,z6]),(0,[z0,z1037,z3,z4,z5,z6])],[(0,[z0,z3,z4,z1038,z5,z6]),(0,[z0,z1039,z3,z4,z5,z6]),(0,[z0,z1,z3,z1040,z5,z6]),(0,[z43,z1,z3,z105,z5,z6]),(0,[z0,z23,z1,z4,z750,z6]),(0,[z0,z1041,z1,z3,z4,z6])],[(0,[z0,z361,z3,z4,z97,z6]),(0,[z0,z1,z3,z42,z5,z119]),(0,[z0,z24,z158,z3,z4,z6]),(0,[z1,z3,z4,z5,z797,z125]),(0,[z0,z24,z277,z3,z4,z6])],[(0,[z0,z1,z3,z4,z1042,z6]),(0,[z0,z24,z73,z3,z4,z6]),(0,[z0,z200,z838,z4,z5,z6])],[(0,[z0,z1,z718,z4,z5,z6]),(0,[z0,z319,z24,z3,z4,z6]),(0,[z317,z0,z231,z3,z4,z6])],[(0,[z0,z1,z3,z1043,z5,z6]),(0,[z0,z309,z1,z40,z4,z6]),(0,[z0,z1,z103,z120,z5,z6])],[(0,[z1,z3,z4,z816,z84,z6])],[(0,[z0,z325,z24,z3,z4,z6]),(0,[z0,z24,z1,z3,z4,z226]),(0,[z0,z1,z157,z3,z415,z4])]],
   [[(0,[z0,z3,z4,z5,z6,z1044]),(0,[z0,z1,z3,z730,z5,z6])],[(0,[z0,z1,z3,z4,z1045,z6]),(0,[z69,z24,z1,z3,z37,z6]),(0,[z146,z24,z1,z3,z4,z147]),(0,[z0,z1,z3,z151,z780,z6])],[(0,[z0,z1,z3,z4,z765,z6])],[(0,[z0,z8,z1,z3,z4,z48]),(0,[z168,z1,z3,z4,z84,z6]),(0,[z0,z79,z209,z3,z4,z5]),(0,[z0,z1,z3,z946,z4,z5])],[(0,[z0,z1,z1046,z3,z4,z6]),(0,[z0,z1047,z3,z4,z5,z6]),(0,[z317,z0,z24,z3,z4,z6]),(0,[z0,z165,z3,z59,z6,z359]),(0,[z0,z1,z3,z733,z5,z6])],[(0,[z0,z24,z1,z3,z279,z6]),(0,[z0,z1048,z1,z3,z4,z6]),(0,[z0,z141,z3,z4,z58,z6]),(0,[z0,z8,z141,z3,z4,z6]),(0,[z0,z1,z902,z4,z5,z6]),(0,[z0,z153,z3,z603,z4,z5])],[(0,[z0,z1,z3,z4,z1049,z6]),(0,[z0,z1,z3,z4,z1050,z6]),(0,[z0,z23,z1,z40,z4,z6]),(0,[z0,z1,z1051,z3,z4,z6])],[(0,[z0,z1,z3,z1052,z5,z6]),(0,[z0,z1053,z1,z3,z4,z6])]],
   [[(0,[z0,z1,z2,z3,z19,z5]),(0,[z167,z319,z1,z3,z4,z6]),(0,[z0,z1,z3,z1054,z4,z6])],[(0,[z0,z1055,z3,z4,z5,z6]),(0,[z0,z24,z1,z3,z4,z94]),(0,[z0,z1,z3,z946,z4,z92])],[(0,[z0,z1,z3,z4,z1056,z6]),(0,[z0,z1,z3,z105,z5,z198])],[(0,[z0,z1057,z3,z4,z5,z6]),(0,[z0,z200,z201,z4,z150,z6]),(0,[z0,z24,z1,z512,z3,z4]),(0,[z0,z1058,z1,z3,z4,z6])],[(0,[z0,z24,z361,z3,z4,z6]),(0,[z0,z1,z3,z721,z5,z6]),(0,[z0,z1,z152,z264,z3,z4]),(0,[z0,z1,z3,z18,z382,z6])],[(0,[z712,z25,z3,z4,z5,z6]),(0,[z0,z1059,z3,z4,z5,z6]),(0,[z0,z3,z721,z130,z5,z6]),(0,[z0,z24,z189,z3,z4,z6])],[(1,[z712,z3,z4,z5,z6]),(0,[z26,z1,z27,z279,z5,z6]),(0,[z26,z1,z27,z4,z280,z6]),(0,[z0,z1,z3,z181,z5,z6]),(0,[z0,z1,z157,z3,z4,z175])],[(0,[z236,z24,z25,z3,z4,z6]),(0,[z0,z1060,z3,z4,z5,z6]),(0,[z0,z1,z730,z120,z5,z6])]],
   [[(0,[z0,z1,z1061,z3,z4,z6])],[(0,[z982,z1,z3,z4,z5,z6]),(0,[z0,z1,z264,z3,z155,z4]),(0,[z0,z24,z1,z3,z4,z743]),(0,[z0,z145,z24,z3,z4,z6]),(0,[z0,z1,z3,z1062,z5,z6]),(0,[z0,z1,z3,z4,z5,z726])],[(0,[z368,z1,z3,z42,z5,z6]),(0,[z0,z1,z3,z1063,z4,z6]),(0,[z0,z1064,z3,z4,z5,z6]),(0,[z0,z1,z93,z519,z4,z5]),(0,[z0,z1,z304,z3,z175,z176]),(0,[z0,z1,z3,z105,z20,z383])],[(0,[z26,z1,z742,z4,z5,z6])],[(0,[z1065,z1,z3,z4,z5,z6]),(0,[z0,z8,z1,z3,z4,z819])],[(1,[z1,z3,z4,z816,z6]),(0,[z0,z1066,z1,z3,z4,z6]),(0,[z0,z23,z1,z4,z107,z6]),(0,[z0,z1,z3,z4,z91,z137]),(0,[z0,z1,z3,z105,z4,z394])],[(0,[z1067,z1,z3,z4,z5,z6])],[(0,[z0,z786,z1,z3,z4,z6]),(0,[z0,z8,z1,z152,z3,z4]),(0,[z0,z1,z3,z5,z780,z6]),(0,[z0,z231,z512,z3,z4,z5])]],
   [[(0,[z0,z8,z596,z3,z4,z6]),(0,[z0,z1,z3,z4,z1068,z6])],[(0,[z0,z1,z1069,z3,z4,z5]),(0,[z36,z1,z3,z772,z5,z6]),(0,[z0,z1,z3,z4,z1070,z6]),(0,[z0,z24,z1,z1014,z4,z6])],[(0,[z0,z1,z3,z105,z530,z5]),(0,[z1071,z1,z3,z4,z5,z6])],[(0,[z0,z1,z1072,z3,z4,z5]),(0,[z0,z109,z34,z4,z5,z6]),(0,[z0,z3,z59,z5,z6,z459]),(0,[z0,z1,z103,z120,z218,z6])],[(0,[z0,z1,z3,z1073,z4,z5]),(0,[z250,z1,z3,z4,z84,z6]),(0,[z1074,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z1075,z4,z6]),(0,[z0,z1,z313,z4,z85,z6])],[(0,[z0,z8,z1,z362,z3,z4]),(0,[z0,z1,z103,z730,z5,z6])],[(0,[z0,z1,z3,z4,z1076,z6]),(0,[z43,z8,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z1077,z6]),(0,[z0,z3,z4,z5,z726,z6]),(0,[z0,z1078,z1,z3,z4,z6]),(0,[z0,z1,z3,z105,z535,z5])],[(0,[z0,z786,z24,z3,z4,z6]),(0,[z0,z200,z201,z4,z121,z6]),(0,[z0,z1,z1079,z3,z4,z6]),(0,[z0,z1,z3,z9,z6,z176])]],
   [[(0,[z0,z25,z3,z99,z4,z6]),(0,[z0,z1,z3,z4,z1080,z6])],[(0,[z0,z1,z3,z4,z5,z1081]),(0,[z0,z1,z3,z4,z1082,z6]),(0,[z0,z24,z3,z4,z771,z6]),(0,[z837,z8,z1,z3,z4,z6])],[(0,[z0,z1,z1083,z3,z4,z6]),(0,[z0,z200,z291,z4,z5,z6]),(0,[z0,z8,z1,z3,z191,z6]),(0,[z0,z3,z4,z721,z5,z6]),(0,[z0,z24,z3,z568,z4,z6]),(0,[z0,z1084,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z467,z6])],[(0,[z0,z1,z3,z4,z54,z6]),(0,[z0,z1,z3,z4,z1085,z6]),(0,[z0,z47,z3,z99,z4,z6]),(0,[z0,z24,z1,z3,z105,z20]),(0,[z0,z8,z153,z3,z4,z180]),(0,[z0,z1,z3,z4,z6,z1086])],[(0,[z26,z1,z27,z4,z5,z6]),(0,[z0,z1,z1087,z3,z4,z6])],[(0,[z0,z24,z1,z3,z4,z48]),(0,[z0,z1088,z3,z4,z5,z6]),(0,[z0,z24,z251,z3,z4,z6]),(0,[z0,z1,z3,z1089,z5,z6]),(0,[z0,z350,z1,z3,z243,z6])],[(0,[z0,z8,z1,z3,z4,z6]),(0,[z0,z1,z3,z1090,z4,z6]),(0,[z0,z1,z3,z4,z1091,z6]),(0,[z0,z1,z3,z181,z382,z6])],[(0,[z0,z24,z141,z3,z4,z6]),(0,[z0,z1,z3,z4,z1092,z6]),(0,[z0,z1,z3,z4,z1093,z6])]],
   [[(0,[z0,z163,z34,z4,z5,z6]),(0,[z0,z8,z1,z3,z4,z119]),(0,[z0,z8,z1,z103,z120,z6])],[(0,[z0,z1,z3,z4,z5,z1094]),(0,[z26,z1,z27,z191,z5,z6]),(0,[z0,z43,z24,z3,z4,z6]),(0,[z0,z24,z3,z4,z464,z6]),(0,[z0,z1,z3,z4,z1095,z6])],[(0,[z0,z1,z3,z4,z1096,z6]),(0,[z406,z0,z1,z3,z4,z62])],[(0,[z0,z8,z1,z3,z4,z128]),(0,[z0,z1,z3,z4,z1097,z6]),(0,[z0,z1,z3,z4,z5,z1098]),(0,[z0,z1,z3,z4,z5,z1099]),(0,[z0,z1100,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z1101]),(0,[z0,z1,z3,z1102,z4,z6])],[(0,[z0,z1,z3,z4,z1103,z6]),(0,[z0,z24,z3,z4,z179,z6]),(0,[z0,z1,z3,z4,z5,z1031]),(0,[z0,z1,z3,z4,z107,z175])],[(0,[z0,z158,z3,z4,z5,z6]),(0,[z0,z1104,z3,z4,z5,z6]),(0,[z0,z1105,z1,z3,z4,z6])],[(0,[z0,z1,z3,z1106,z5,z6]),(0,[z0,z1,z3,z4,z1107,z6]),(0,[z0,z1,z3,z1108,z5,z6]),(0,[z0,z1109,z1,z3,z4,z6]),(0,[z0,z1,z445,z120,z5,z6]),(0,[z194,z1,z3,z4,z5,z797]),(0,[z0,z109,z24,z34,z4,z6]),(0,[z0,z1,z3,z99,z4,z6]),(0,[z0,z24,z3,z59,z4,z6]),(0,[z0,z24,z3,z4,z6,z276]),(0,[z0,z8,z3,z166,z4,z6]),(0,[z0,z153,z3,z4,z5,z180])]],
   [[(0,[z0,z24,z47,z3,z4,z6]),(0,[z0,z1110,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z1111,z6])],[(0,[z0,z1,z3,z1112,z5,z6]),(0,[z0,z24,z3,z4,z486,z6]),(0,[z26,z361,z27,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1113]),(0,[z0,z165,z1,z3,z155,z5]),(0,[z0,z1,z581,z3,z6,z176]),(0,[z0,z1,z1114,z3,z4,z6])],[(0,[z0,z165,z3,z721,z5,z6]),(0,[z242,z319,z1,z3,z4,z6]),(0,[z0,z1,z1115,z3,z4,z6]),(0,[z0,z1,z3,z4,z1116,z5])],[(0,[z0,z1,z3,z4,z1117,z6]),(0,[z0,z1,z3,z4,z1118,z6])],[(0,[z0,z334,z24,z3,z4,z6]),(0,[z0,z79,z1,z3,z181,z5]),(0,[z0,z1,z93,z4,z355,z124]),(0,[z0,z1119,z3,z4,z5,z6])],[(0,[z1,z3,z4,z772,z5,z6]),(0,[z0,z8,z3,z4,z60,z6]),(0,[z0,z1,z483,z4,z85,z6])],[(0,[z0,z1,z3,z4,z5,z1120]),(0,[z203,z24,z47,z3,z4,z6]),(0,[z0,z24,z38,z3,z4,z6]),(0,[z0,z1,z1121,z3,z4,z5]),(0,[z0,z1,z3,z4,z750,z6])],[(0,[z0,z1,z3,z4,z1122,z6]),(0,[z0,z1,z3,z4,z1123,z6]),(0,[z0,z1,z3,z105,z5,z327])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 536) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 536).take 537) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1073).take 101) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1174)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [536, 537, 101] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 134).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 134).take 122).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [134, 122] = true :=
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

end PEqualNP.Outside.L_meta_42988

theorem PEqualNP.Outside.L_meta_42988 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276677320 * 2 ^ 32 + 4209043968) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276677320 * 2 ^ 32 + 4209043968) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_42988.solve