import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_38841

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
  Nat.testBit (4276808928 * 2 ^ 32 + 4274580672) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x1022b391c0e33cc2#64 ++ 0x21022b391c0e33cc#64 ++ 0xb067f793c1e77cc7#64 ++ 0xdb067f793c1e77cc#64 : BitVec 256),
   (0x008980b4020d0550#64 ++ 0x4008980b4020d055#64 ++ 0x719989fc063f8fff#64 ++ 0xb719989fc063f8ff#64 : BitVec 256),
   (0x06160c0ad830d0a4#64 ++ 0x806160c0ad830d0a#64 ++ 0xde1e0e1ff838f0ff#64 ++ 0x7de1e0e1ff838f0f#64 : BitVec 256),
   (0x0b600f402d40ea07#64 ++ 0x00b600f402d40ea0#64 ++ 0xffe00fe07fc0ff0e#64 ++ 0xfffe00fe07fc0ff0#64 : BitVec 256),
   (0x2ddf500077be0008#64 ++ 0x02ddf500077be000#64 ++ 0xaffff0007fff000d#64 ++ 0xfaffff0007fff000#64 : BitVec 256),
   (0x4ffdefff00000000#64 ++ 0x04ffdefff0000000#64 ++ 0x4fffffff80000003#64 ++ 0xf4fffffff8000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 2]⟩, ⟨.and, [6, 4]⟩, ⟨.or, [1, 7]⟩, ⟨.or, [2, 7]⟩, ⟨.and, [8, 3]⟩, ⟨.or, [3, 5]⟩, ⟨.and, [0, 11]⟩, ⟨.or, [12, 1]⟩, ⟨.and, [13, 9]⟩, ⟨.or, [14, 10]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x008980b4020d0550 0x4008980b4020d055 0x719989fc063f8fff 0xb719989fc063f8ff

def z1 : W := mkw 0x06160c0ad830d0a4 0x806160c0ad830d0a 0xde1e0e1ff838f0ff 0x7de1e0e1ff838f0f

def z2 : W := mkw 0x06160c0ada3dd5f4 0xc06160c0ada3dd5f 0xfe1e0e1ffe3fffff 0x7fe1e0e1ffe3ffff

def z3 : W := mkw 0x0b600f402d40ea07 0x00b600f402d40ea0 0xffe00fe07fc0ff0e 0xfffe00fe07fc0ff0

def z4 : W := mkw 0x1022b391c0e33cc2 0x21022b391c0e33cc 0xb067f793c1e77cc7 0xdb067f793c1e77cc

def z5 : W := mkw 0x2ddf500077be0008 0x02ddf500077be000 0xaffff0007fff000d 0xfaffff0007fff000

def z6 : W := mkw 0x4ffdefff00000000 0x04ffdefff0000000 0x4fffffff80000003 0xf4fffffff8000000

def z7 : W := mkw 0x0000000000000000 0x0000000000000000 0x9000060040007006 0x5900006004000700

def z8 : W := mkw 0x0020030000402802 0x0002003000040280 0xb060078041c07c06 0xdb060078041c07c0

def z9 : W := mkw 0x4ffdefff2d40ea07 0x04ffdefff2d40ea0 0xffffffffffc0ff0f 0xfffffffffffc0ff0

def z10 : W := mkw 0x0b400c402d00c205 0x00b400c402d00c20 0x4f8008603e008308 0x24f8008603e00830

def z11 : W := mkw 0x1002b091c0a314c0 0x21002b091c0a314c 0x0007f013802700c1 0x00007f013802700c

def z12 : W := mkw 0x1020a39180413cc2 0x21020a39180413cc 0x1000079380007cc2 0x01000079380007cc

def z13 : W := mkw 0x2ddd4000371c0008 0x02ddd4000371c000 0x0f9800003e180008 0x20f9800003e18000

def z14 : W := mkw 0x0020a39100000000 0x00020a3910000000 0x0067f79380000003 0xd0067f7938000000

def z15 : W := mkw 0x0000000000000000 0x0000000000000000 0x3000018000000c06 0x93000018000000c0

def z16 : W := mkw 0x0be90f642f4ceb17 0x40be90f642f4ceb1 0xfff80fec7fd8ff3e 0xffff80fec7fd8ff3

def z17 : W := mkw 0x1636bf9bc0e33cc2 0x21636bf9bc0e33cc 0xfe7fff9fc1e77cc7 0xffe7fff9fc1e77cc

def z18 : W := mkw 0x0002100040a20000 0x00002100040a2000 0xa067f00041e70005 0xda067f00041e7000

def z19 : W := mkw 0x1000000080413cc2 0x21000000080413cc 0x1000000000007cc0 0x01000000000007cc

def z20 : W := mkw 0x10021000c0e33cc2 0x210021000c0e33cc 0xb000000041e77cc4 0x0b000000041e77cc

def z21 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z22 : W := mkw 0x1022b391c0e33cc2 0x21022b391c0e33cc 0xf07fff9fc1fffcff 0xff07fff9fc1fffcf

def z23 : W := mkw 0x0000000000000000 0x0000000000000000 0x5018081c003880ff 0x35018081c003880f

def z24 : W := mkw 0x0000000000000000 0x0000000000000000 0x218001e006000f00 0x8218001e006000f0

def z25 : W := mkw 0x00000000020d0550 0x400000000020d055 0x30000000063f8ffc 0x030000000063f8ff

def z26 : W := mkw 0x4ffdefff020d0550 0x44ffdefff020d055 0x7fffffff863f8fff 0xf7fffffff863f8ff

def z27 : W := mkw 0x29c95000278e0008 0x029c95000278e000 0x21e1f00007c70000 0x821e1f00007c7000

def z28 : W := mkw 0x0b60afd100000000 0x00b60afd10000000 0x4fe7fff380000003 0xf4fe7fff38000000

def z29 : W := mkw 0x000080b400010550 0x4000080b40001055 0x718009fc06008ffe 0xb718009fc06008ff

def z30 : W := mkw 0x1022b391c0e23882 0x21022b391c0e2388 0x8067f793c1c07003 0xd8067f793c1c0700

def z31 : W := mkw 0x0960034025402a03 0x00960034025402a0 0x21e001e007c00f00 0x821e001e007c00f0

def z32 : W := mkw 0x469decbf00000000 0x0469decbf0000000 0x4e1ffe1f80000003 0x74e1ffe1f8000000

def z33 : W := mkw 0x4fdd4c6e1810c024 0x84fdd4c6e1810c02 0x4f98086c38188038 0x24f98086c3818803

def z34 : W := mkw 0x06360f4ad870faa7 0x806360f4ad870faa 0xde1e0ffff838ffff 0x7de1e0ffff838fff

def z35 : W := mkw 0x00008090020d0550 0x400008090020d055 0x30018190063f8fff 0x930018190063f8ff

def z36 : W := mkw 0x02000c000800c004 0x002000c000800c00 0xff800fe07e00ff0e 0xfff800fe07e00ff0

def z37 : W := mkw 0x00890000020c0000 0x000890000020c000 0x21998000063f000d 0xb21998000063f000

def z38 : W := mkw 0x5fffffffc0e33cc2 0x25fffffffc0e33cc 0xffffffffc1e77cc7 0xfffffffffc1e77cc

def z39 : W := mkw 0x4f746f4b00000000 0x04f746f4b0000000 0x0e66760380000000 0x40e6676038000000

def z40 : W := mkw 0x0000000080001080 0x0000000008000108 0x10000613800070c2 0x010000613800070c

def z41 : W := mkw 0x4ffdefff00000000 0x04ffdefff0000000 0x4ff9f9ec00000000 0xa4ff9f9ec0000000

def z42 : W := mkw 0x44bde3bf00000000 0x044bde3bf0000000 0x007ff79f80000003 0xd007ff79f8000000

def z43 : W := mkw 0x0000000025000000 0x0000000002500000 0xa00000007fc0000c 0x0a00000007fc0000

def z44 : W := mkw 0x269f5c0adabed0ac 0x8269f5c0adabed0a 0xde1ffe1ff83ff0ff 0x7de1ffe1ff83ff0f

def z45 : W := mkw 0x2002100077be0008 0x02002100077be000 0xa00000007fff000c 0x0a00000007fff000

def z46 : W := mkw 0x4220afff00000000 0x04220afff0000000 0x40000fff80000002 0x040000fff8000000

def z47 : W := mkw 0x1636bf9bd8f3fce6 0xa1636bf9bd8f3fce 0xfe7fff9ff9fffcff 0xffe7fff9ff9fffcf

def z48 : W := mkw 0x0b400c002d00c004 0x00b400c002d00c00 0xffe00e007fc0f00e 0xfffe00e007fc0f00

def z49 : W := mkw 0x3dfff391f7ff3cca 0x23dfff391f7ff3cc 0xbffff793ffff7ccf 0xfbffff793ffff7cc

def z50 : W := mkw 0x0fdf4c0ad830d0a4 0x80fdf4c0ad830d0a 0xdffffe1ff838f0ff 0xfdffffe1ff838f0f

def z51 : W := mkw 0x0000000000000000 0x0000000000000000 0x718009e006008f0e 0xb718009e006008f0

def z52 : W := mkw 0x0be98ff42f4def57 0x40be98ff42f4def5 0xfff98ffc7fffffff 0xffff98ffc7ffffff

def z53 : W := mkw 0x02200f400840ea07 0x002200f400840ea0 0x50000fe00000ff02 0x050000fe00000ff0

def z54 : W := mkw 0x49e9e3f500000000 0x049e9e3f50000000 0x01e1f1e000000000 0x801e1f1e00000000

def z55 : W := mkw 0x5f76ffdbc0e33cc2 0x25f76ffdbc0e33cc 0xbe67f793c1e77cc7 0xdbe67f793c1e77cc

def z56 : W := mkw 0x449de0bf00000000 0x0449de0bf0000000 0x001ff01f80000001 0x0001ff01f8000000

def z57 : W := mkw 0x008980b4020d0550 0x4008980b4020d055 0x219981fc063f0ff1 0x8219981fc063f0ff

def z58 : W := mkw 0x02000c000800c004 0x002000c000800c00 0xde000e007800f00e 0x7de000e007800f00

def z59 : W := mkw 0x0000000000000000 0x0000000000000000 0x719809fc06388fff 0xb719809fc06388ff

def z60 : W := mkw 0x0d56000075300000 0x00d5600007530000 0xaffe00007ff8000d 0xfaffe00007ff8000

def z61 : W := mkw 0x0b60afd12d40ea07 0x00b60afd12d40ea0 0xffe7fff3ffc0ff0f 0xfffe7fff3ffc0ff0

def z62 : W := mkw 0x002003002d40ea07 0x0002003002d40ea0 0xb06007807fc0ff0e 0xdb06007807fc0ff0

def z63 : W := mkw 0x2ddfd0b477bf0558 0x42ddfd0b477bf055 0xfffff9fc7fff8fff 0xffffff9fc7fff8ff

def z64 : W := mkw 0x0416000050300000 0x0041600005030000 0x8e1e00007838000d 0x78e1e00007838000

def z65 : W := mkw 0x06140c0a00000000 0x006140c0a0000000 0x4e1e0e1f80000003 0x74e1e0e1f8000000

def z66 : W := mkw 0x4fffefffd830d0a4 0x84fffefffd830d0a 0xdffffffff838f0ff 0xfdffffffff838f0f

def z67 : W := mkw 0x02000c0a8800d0a4 0x802000c0a8800d0a 0xde000e1ff800f0fe 0x7de000e1ff800f0f

def z68 : W := mkw 0x02000c0a0800c024 0x802000c0a0800c02 0x4000080c00008030 0x04000080c0000803

def z69 : W := mkw 0x1b62bfd1ede3fec7 0x21b62bfd1ede3fec 0xffe7fff3ffe7ffcf 0xfffe7fff3ffe7ffc

def z70 : W := mkw 0x249f500052be0008 0x0249f500052be000 0x001ff000003f0001 0x0001ff000003f000

def z71 : W := mkw 0x2ddf50007ffeea0f 0x02ddf50007ffeea0 0xbffff0007fffff0d 0xfbffff0007fffff0

def z72 : W := mkw 0x0000000000000000 0x0000000000000000 0x0067f00000000001 0xd0067f0000000000

def z73 : W := mkw 0x0b600f402d40ea07 0x00b600f402d40ea0 0x8e60060079c07000 0x48e60060079c0700

def z74 : W := mkw 0x4fdd4c6e00000000 0x04fdd4c6e0000000 0x4f98086c00000000 0x24f98086c0000000

def z75 : W := mkw 0x0942100065a20000 0x00942100065a2000 0xafe7f0007fe7000d 0xfafe7f0007fe7000

def z76 : W := mkw 0x4fdd4c6e2d00c205 0x04fdd4c6e2d00c20 0x4f98086c3e008308 0x24f98086c3e00830

def z77 : W := mkw 0x0ddd400000000000 0x00ddd40000000000 0x0ffff00000000001 0xf0ffff0000000000

def z78 : W := mkw 0x2ddf500077be0008 0x02ddf500077be000 0xafe7f0007fc70000 0xcafe7f0007fc7000

def z79 : W := mkw 0x4ffdefff020d0550 0x44ffdefff020d055 0x6fffffff86070f03 0xf6fffffff86070f0

def z80 : W := mkw 0x06168c9ad831d4e4 0x806168c9ad831d4e 0xfe1f8f9ff83ffcff 0xffe1f8f9ff83ffcf

def z81 : W := mkw 0x0f760f4afd70faa7 0x80f760f4afd70faa 0x8e660603f9c07000 0x48e660603f9c0700

def z82 : W := mkw 0x00020000c0201080 0x000020000c020108 0x90060613c02070c7 0x590060613c02070c

def z83 : W := mkw 0x2ddf500052be0008 0x02ddf500052be000 0x0ffff000003f0001 0xf0ffff000003f000

def z84 : W := mkw 0x008980b4020c0000 0x0008980b4020c000 0x619989fc063f000f 0xb619989fc063f000

def z85 : W := mkw 0x0b600f402d40ea07 0x00b600f402d40ea0 0xbe60078079c07c06 0xdbe60078079c07c0

def z86 : W := mkw 0x000080b400010550 0x4000080b40001055 0x500009fc00008ff2 0x0500009fc00008ff

def z87 : W := mkw 0x0020a39100010440 0x00020a3910001044 0x3067f79380270cc7 0xd3067f79380270cc

def z88 : W := mkw 0x02898cb40a0dc554 0x402898cb40a0dc55 0xff998ffc7e3fffff 0xfff998ffc7e3ffff

def z89 : W := mkw 0x4ffdefff2d40ea07 0x04ffdefff2d40ea0 0xcffffffff9c07003 0xfcffffffff9c0700

def z90 : W := mkw 0x0b600f402d40ea07 0x00b600f402d40ea0 0xcfe00fe079c07002 0xfcfe00fe079c0700

def z91 : W := mkw 0x6fffffffffbed0ac 0x86fffffffffbed0a 0xfffffffffffff0ff 0xffffffffffffff0f

def z92 : W := mkw 0x59e9f3f500c32c42 0x259e9f3f500c32c4 0x21e1f1e001c70c00 0x821e1f1e001c70c0

def z93 : W := mkw 0x008980b4020d0550 0x4008980b4020d055 0x0019801c003f00f1 0x00019801c003f00f

def z94 : W := mkw 0x4f746f4b00000000 0x04f746f4b0000000 0x4fe67fe380000002 0xf4fe67fe38000000

def z95 : W := mkw 0x00890024020c0110 0x400890024020c011 0x4198086c06188338 0x24198086c0618833

def z96 : W := mkw 0x4f74efdb00000000 0x04f74efdb0000000 0x0e67f79380000003 0xd0e67f7938000000

def z97 : W := mkw 0x4ffdefff00010550 0x44ffdefff0001055 0x5fffffff80008ff3 0xf5fffffff80008ff

def z98 : W := mkw 0x00020000d03010a0 0x800020000d03010a 0x00000000003800f0 0x000000000003800f

def z99 : W := mkw 0x2ddfd0b477bf0558 0x42ddfd0b477bf055 0xaffff1e07fff0f0d 0xfaffff1e07fff0f0

def z100 : W := mkw 0x0b600f4000000000 0x00b600f400000000 0x7fe00fe006008f0e 0xf7fe00fe006008f0

def z101 : W := mkw 0x4fffeffffd70faa7 0x84fffeffffd70faa 0xfffffffffff8ffff 0xffffffffffff8fff

def z102 : W := mkw 0x0b600f402d40ea07 0x00b600f402d40ea0 0xfff80ffc7ff8ffff 0xffff80ffc7ff8fff

def z103 : W := mkw 0x10021000c0e23882 0x210021000c0e2388 0x8000000041c07000 0x08000000041c0700

def z104 : W := mkw 0x6fffffff7ffeea0f 0x06fffffff7ffeea0 0xffffffffffffff0f 0xfffffffffffffff0

def z105 : W := mkw 0x2940500025820008 0x0294050002582000 0x0060700001c00000 0x00060700001c0000

def z106 : W := mkw 0x1020a3b580413dd2 0x61020a3b580413dd 0x50000fff8000fff2 0x050000fff8000fff

def z107 : W := mkw 0x20895000028e0008 0x020895000028e000 0x0001f00000070000 0x00001f0000007000

def z108 : W := mkw 0x2002100052be0008 0x02002100052be000 0x00000000003f0000 0x000000000003f000

def z109 : W := mkw 0x10abb3b5c2ef3dd2 0x610abb3b5c2ef3dd 0xf1ffffffc7ffffff 0xff1ffffffc7fffff

def z110 : W := mkw 0x1022b391c0e33cc2 0x21022b391c0e33cc 0xa067f783c1c77c00 0xca067f783c1c77c0

def z111 : W := mkw 0x10021000c2ef3dd2 0x610021000c2ef3dd 0xb000000047fffffc 0x0b000000047fffff

def z112 : W := mkw 0x2fdf5c0affbed0ac 0x82fdf5c0affbed0a 0xfffffe1ffffff0ff 0xffffffe1ffffff0f

def z113 : W := mkw 0x02000c002d40ea07 0x002000c002d40ea0 0xfe000e007fc0ff0e 0x7fe000e007fc0ff0

def z114 : W := mkw 0x4000a0bf00000000 0x04000a0bf0000000 0x0000001f80000000 0x00000001f8000000

def z115 : W := mkw 0x0dddc0b4020d0550 0x40dddc0b4020d055 0x7ffff9fc063f8fff 0xf7ffff9fc063f8ff

def z116 : W := mkw 0x0416000ad03010a0 0x80416000ad03010a 0x901e061fc03870f7 0x5901e061fc03870f

def z117 : W := mkw 0x02000c0a8800d0a4 0x802000c0a8800d0a 0x50000e1f8000f0f2 0x050000e1f8000f0f

def z118 : W := mkw 0x008980b4020d0550 0x4008980b4020d055 0x318181e0063f8ffc 0x8318181e0063f8ff

def z119 : W := mkw 0x4fffefffda3dd5f4 0xc4fffefffda3dd5f 0xfffffffffe3fffff 0xffffffffffe3ffff

def z120 : W := mkw 0x4020a3f500000000 0x04020a3f50000000 0x000001e000000000 0x0000001e00000000

def z121 : W := mkw 0x09c90000270c0000 0x009c90000270c000 0xaff980007fff000d 0xfaff980007fff000

def z122 : W := mkw 0x2ddf500077be0008 0x02ddf500077be000 0x21fff00007ff0001 0x821fff00007ff000

def z123 : W := mkw 0x449de0bf020d0550 0x4449de0bf020d055 0x719ff9ff863f8fff 0xb719ff9ff863f8ff

def z124 : W := mkw 0x2d56500075b20008 0x02d56500075b2000 0xae67f00079e70005 0xdae67f00079e7000

def z125 : W := mkw 0x0bc98cf42f0dc755 0x40bc98cf42f0dc75 0x7f9989fc3e3f8fff 0xb7f9989fc3e3f8ff

def z126 : W := mkw 0x2fdf5c407fbec20d 0x02fdf5c407fbec20 0xeffff8607fff830d 0xfeffff8607fff830

def z127 : W := mkw 0x2fff5f407ffeea0f 0x02fff5f407ffeea0 0xffffffe07fffff0f 0xfffffffe07fffff0

def z128 : W := mkw 0x008980b4020d0550 0x4008980b4020d055 0x218181e006070f00 0x8218181e006070f0

def z129 : W := mkw 0x06160c0ad830d0a4 0x806160c0ad830d0a 0xff9e0ffffe38ffff 0xfff9e0ffffe38fff

def z130 : W := mkw 0x5fffffffc0e23882 0x25fffffffc0e2388 0xcfffffffc1c07003 0xfcfffffffc1c0700

def z131 : W := mkw 0x06160c0ad830d0a4 0x806160c0ad830d0a 0x8e1e0603f838700d 0x78e1e0603f838700

def z132 : W := mkw 0x02200f400840ea07 0x002200f400840ea0 0x71800fe00600ff0e 0xb71800fe00600ff0

def z133 : W := mkw 0x2ddf5000f7be1088 0x02ddf5000f7be108 0xbffff613ffff70cf 0xfbffff613ffff70c

def z134 : W := mkw 0x2ddd5000379e0008 0x02ddd5000379e000 0x2ff9f0003fdf0008 0xa2ff9f0003fdf000

def z135 : W := mkw 0x0020a39100402802 0x00020a3910040280 0xb067f793c1c07c07 0xdb067f793c1c07c0

def z136 : W := mkw 0x0020a39100000000 0x00020a3910000000 0x0000079380000002 0x0000007938000000

def z137 : W := mkw 0x2ddd4024371c0118 0x42ddd4024371c011 0x4f98086c3e188338 0x24f98086c3e18833

def z138 : W := mkw 0x4220afff8800d0a4 0x84220afff8800d0a 0x50000fff8000f0f2 0x050000fff8000f0f

def z139 : W := mkw 0x1b62bfd1c0e33cc2 0x21b62bfd1c0e33cc 0xffe7fff3c1e77cc7 0xfffe7fff3c1e77cc

def z140 : W := mkw 0x2fff5f407ffeea0f 0x02fff5f407ffeea0 0xaffff6007fff700d 0xfaffff6007fff700

def z141 : W := mkw 0x1020b39100c32c42 0x21020b39100c32c4 0x2061f18001c70c00 0x82061f18001c70c0

def z142 : W := mkw 0x00020000d830d0a4 0x800020000d830d0a 0x900000007838f0fc 0x0900000007838f0f

def z143 : W := mkw 0x0416000ad830d0a4 0x80416000ad830d0a 0x901e001ff838f0fd 0x0901e001ff838f0f

def z144 : W := mkw 0x008980b400000000 0x0008980b40000000 0x719989fc06008f0f 0xb719989fc06008f0

def z145 : W := mkw 0x0ddd400025000000 0x00ddd40002500000 0xaffff0007fc0000d 0xfaffff0007fc0000

def z146 : W := mkw 0x06140c0a1810c024 0x806140c0a1810c02 0x4e18080c38188038 0x24e18080c3818803

def z147 : W := mkw 0x469fecbfd830d0a4 0x8469fecbfd830d0a 0xde1ffe1ff838f0ff 0x7de1ffe1ff838f0f

def z148 : W := mkw 0x49e9e3f5020d0550 0x449e9e3f5020d055 0x21e1f1e006070f00 0x821e1f1e006070f0

def z149 : W := mkw 0x0414000a10100020 0x80414000a1010002 0x0018000c00180030 0x00018000c0018003

def z150 : W := mkw 0x06140c0a1810c024 0x806140c0a1810c02 0x5e18081c383880ff 0x35e18081c383880f

def z151 : W := mkw 0x1f76bfdbfdf3fee7 0xa1f76bfdbfdf3fee 0xffffffffffffffff 0xffffffffffffffff

def z152 : W := mkw 0x4be9efff00000000 0x04be9efff0000000 0x41e1ffff80000002 0x841e1ffff8000000

def z153 : W := mkw 0x0fdd4c0a00000000 0x00fdd4c0a0000000 0x4ffffe1f80000003 0xf4ffffe1f8000000

def z154 : W := mkw 0x4ffdefff00402802 0x04ffdefff0040280 0xffffffffc1c07c07 0xfffffffffc1c07c0

def z155 : W := mkw 0x4f746f4b2d40ea07 0x04f746f4b2d40ea0 0x8e667603f9c07000 0x48e667603f9c0700

def z156 : W := mkw 0x4220afff0840ea07 0x04220afff0840ea0 0x50000fff8000ff02 0x050000fff8000ff0

def z157 : W := mkw 0x10223301c0e23882 0x210223301c0e2388 0x80667603c1c07000 0x480667603c1c0700

def z158 : W := mkw 0x06140c0a00000000 0x006140c0a0000000 0x5e1e0e1f803880ff 0x75e1e0e1f803880f

def z159 : W := mkw 0x0f760f4afd70faa7 0x80f760f4afd70faa 0xfffe0ffffff8ffff 0xffffe0ffffff8fff

def z160 : W := mkw 0x06360f0ad870f8a6 0x806360f0ad870f8a 0xfe7e0f9ff9f8fcff 0xffe7e0f9ff9f8fcf

def z161 : W := mkw 0x108bb0b5c2af15d0 0x6108bb0b5c2af15d 0x719ff9ff863f8fff 0xb719ff9ff863f8ff

def z162 : W := mkw 0x00000000020d0550 0x400000000020d055 0x718009e0063f8ffe 0xb718009e0063f8ff

def z163 : W := mkw 0x0000000000010440 0x0000000000001044 0x3000000000270cc4 0x03000000000270cc

def z164 : W := mkw 0x02200f402d40ea07 0x002200f402d40ea0 0xf0000fe07fc0ff0e 0x0f0000fe07fc0ff0

def z165 : W := mkw 0x00890000020d0550 0x400890000020d055 0x31998000063f8ffd 0xb31998000063f8ff

def z166 : W := mkw 0x4414600b00000000 0x04414600b0000000 0x0006700380000000 0x0000670038000000

def z167 : W := mkw 0x10029090c0e33cc2 0x210029090c0e33cc 0xb001819041e77cc7 0x9b001819041e77cc

def z168 : W := mkw 0x02a98ff40a4def57 0x402a98ff40a4def5 0x71998ffc063fffff 0xb71998ffc063ffff

def z169 : W := mkw 0x0020230100000000 0x0002023010000000 0x0066760380000000 0x4006676038000000

def z170 : W := mkw 0x2dfff39177be0008 0x02dfff39177be000 0xaffff793ffff000f 0xfaffff793ffff000

def z171 : W := mkw 0x06160c0ad830d0a4 0x806160c0ad830d0a 0x8e060603f8007000 0x48e060603f800700

def z172 : W := mkw 0x0b600f4000000000 0x00b600f400000000 0x0e60060000000000 0x40e6006000000000

def z173 : W := mkw 0x008980b400000000 0x0008980b40000000 0x419989fc00000003 0xb419989fc0000000

def z174 : W := mkw 0x4ffdefff25402a03 0x04ffdefff25402a0 0x6fffffff87c00f03 0xf6fffffff87c00f0

def z175 : W := mkw 0x3ddf5000f7ff3cca 0x23ddf5000f7ff3cc 0xbffff0007fff7ccd 0xfbffff0007fff7cc

def z176 : W := mkw 0x0b600f400840ea07 0x00b600f400840ea0 0x5fe00fe00000ff02 0xf5fe00fe00000ff0

def z177 : W := mkw 0x10021000c0a314c0 0x210021000c0a314c 0x00000000002700c0 0x000000000002700c

def z178 : W := mkw 0x1022b391c0e33cc2 0x21022b391c0e33cc 0xb0000793c1e77cc6 0x0b0000793c1e77cc

def z179 : W := mkw 0x2416500050b20008 0x02416500050b2000 0x0006700000000000 0x0000670000000000

def z180 : W := mkw 0x06160c0ad830d0a4 0x806160c0ad830d0a 0x9e060613f82070c7 0x59e060613f82070c

def z181 : W := mkw 0x0b600f402d40ea07 0x00b600f402d40ea0 0xde600fe079c0ff02 0x4de600fe079c0ff0

def z182 : W := mkw 0x29c95000278e0008 0x029c95000278e000 0xafe1f0007fc7000c 0xfafe1f0007fc7000

def z183 : W := mkw 0x02200f000840e806 0x002200f000840e80 0xfe600f8079c0fc0e 0xffe600f8079c0fc0

def z184 : W := mkw 0x000000002d40ea07 0x0000000002d40ea0 0xb00000007fc0ff0c 0x0b00000007fc0ff0

def z185 : W := mkw 0x0b600f4000000000 0x00b600f400000000 0x4fe00fe000000002 0xf4fe00fe00000000

def z186 : W := mkw 0x2942100077be0008 0x02942100077be000 0xafe000007fff000c 0xfafe000007fff000

def z187 : W := mkw 0x00020000d830d0a4 0x800020000d830d0a 0x90060613f838f0ff 0x590060613f838f0f

def z188 : W := mkw 0x4089e0b500000000 0x04089e0b50000000 0x0001f00000000000 0x00001f0000000000

def z189 : W := mkw 0x00021000c0a21080 0x000021000c0a2108 0xb067f613c1e770c7 0xdb067f613c1e770c

def z190 : W := mkw 0x1222bfd1c8e3fec7 0x21222bfd1c8e3fec 0xf067fff3c1e7ffc7 0xdf067fff3c1e7ffc

def z191 : W := mkw 0x10221300c0e33cc2 0x210221300c0e33cc 0xb060078041e77cc6 0xdb060078041e77cc

def z192 : W := mkw 0x4ffdefff2f4def57 0x44ffdefff2f4def5 0xffffffffffffffff 0xffffffffffffffff

def z193 : W := mkw 0x449de0bf00000000 0x0449de0bf0000000 0x419ff9ff80000003 0xb419ff9ff8000000

def z194 : W := mkw 0x0000809000010440 0x0000080900001044 0x3001819000270cc7 0x93001819000270cc

def z195 : W := mkw 0x1220afd18841fec7 0x21220afd18841fec 0x50000ff38000ffc2 0x050000ff38000ffc

def z196 : W := mkw 0x0940000025000000 0x0094000002500000 0xafe000007fc0000c 0xfafe000007fc0000

def z197 : W := mkw 0x000000000840ea07 0x0000000000840ea0 0x100000000000ff00 0x0100000000000ff0

def z198 : W := mkw 0x2ddf500077be0008 0x02ddf500077be000 0xfffff9e07fff8f0f 0xffffff9e07fff8f0

def z199 : W := mkw 0x4ddde0bf00000000 0x04ddde0bf0000000 0x0ffff01f80000001 0xf0ffff01f8000000

def z200 : W := mkw 0x10223301c0e33cc2 0x210223301c0e33cc 0xb0667603c1e77cc4 0x4b0667603c1e77cc

def z201 : W := mkw 0x46bdefff00000000 0x046bdefff0000000 0x401fffff80000003 0x0401fffff8000000

def z202 : W := mkw 0x6fffffff77be0008 0x06fffffff77be000 0xefffffffffff000f 0xfefffffffffff000

def z203 : W := mkw 0x2ddf500077be0008 0x02ddf500077be000 0x8e7ff00079ff0001 0x48e7ff00079ff000

def z204 : W := mkw 0x6fffffff77bf0558 0x46fffffff77bf055 0xffffffffffff8fff 0xfffffffffffff8ff

def z205 : W := mkw 0x06140c0a00000000 0x006140c0a0000000 0x0e06060380000000 0x40e0606038000000

def z206 : W := mkw 0x1020b39100c32c42 0x21020b39100c32c4 0xb061f78041c77c06 0xdb061f78041c77c0

def z207 : W := mkw 0x5fffffffc0a314c0 0x25fffffffc0a314c 0x4fffffff802700c3 0xf4fffffff802700c

def z208 : W := mkw 0x4b60afff00000000 0x04b60afff0000000 0x4fe00fff80000002 0xf4fe00fff8000000

def z209 : W := mkw 0x06160c0a50300000 0x006160c0a5030000 0xce1e0e1ff838000f 0x7ce1e0e1ff838000

def z210 : W := mkw 0x00020000d830d0a4 0x800020000d830d0a 0x8000000078007000 0x0800000007800700

def z211 : W := mkw 0x0020839000412c42 0x00020839000412c4 0xb061879041e77cc7 0xdb061879041e77cc

def z212 : W := mkw 0x2ddf502477be0118 0x42ddf502477be011 0xeffff86c7fff833d 0xfeffff86c7fff833

def z213 : W := mkw 0x4ffdefff020c0000 0x04ffdefff020c000 0x6fffffff863f000f 0xf6fffffff863f000

def z214 : W := mkw 0x049f80bed23d15f0 0xc049f80bed23d15f 0x719f89ff863f8fff 0xb719f89ff863f8ff

def z215 : W := mkw 0x49e9e3f500000000 0x049e9e3f50000000 0x01e7f7f380000003 0xd01e7f7f38000000

def z216 : W := mkw 0x1020a39180413cc2 0x21020a39180413cc 0x1067f79380007cc3 0xd1067f79380007cc

def z217 : W := mkw 0x0416000ad03010a0 0x80416000ad03010a 0x001e001f803800f1 0x0001e001f803800f

def z218 : W := mkw 0x1220af9b8841fce6 0xa1220af9b8841fce 0x50000f9f8000fcf2 0x050000f9f8000fcf

def z219 : W := mkw 0x1960b3d125c32e43 0x21960b3d125c32e4 0x21e1f1e007c70f00 0x821e1f1e007c70f0

def z220 : W := mkw 0x06160c0ad830d0a4 0x806160c0ad830d0a 0x8e1e061ff83870f1 0x48e1e061ff83870f

def z221 : W := mkw 0x0960034025402a03 0x00960034025402a0 0xb1e007e047c07f06 0xdb1e007e047c07f0

def z222 : W := mkw 0x20021000ffbed0ac 0x820021000ffbed0a 0xb00000007ffff0fc 0x0b00000007ffff0f

def z223 : W := mkw 0x06160c0ad03010a0 0x806160c0ad03010a 0x4e1e0e1f803800f3 0x74e1e0e1f803800f

def z224 : W := mkw 0x0b600f402d40ea07 0x00b600f402d40ea0 0x5f800fe03e00ff0a 0x25f800fe03e00ff0

def z225 : W := mkw 0x04160000d830d0a4 0x804160000d830d0a 0x9e1e00007838f0fd 0x79e1e00007838f0f

def z226 : W := mkw 0x4960634100000000 0x0496063410000000 0x0060700000000000 0x0006070000000000

def z227 : W := mkw 0x000000002d40ea07 0x0000000002d40ea0 0x8000000079c07000 0x08000000079c0700

def z228 : W := mkw 0x00020000d830d0a4 0x800020000d830d0a 0xd018081c7838f0ff 0x3d018081c7838f0f

def z229 : W := mkw 0x1000b09100830440 0x21000b0910083044 0x0001f00000070000 0x00001f0000007000

def z230 : W := mkw 0x0416100050b20000 0x00416100050b2000 0xae7ff00079ff000d 0xfae7ff00079ff000

def z231 : W := mkw 0x449fe0bfd03010a0 0x8449fe0bfd03010a 0x001ff01f803800f1 0x0001ff01f803800f

def z232 : W := mkw 0x0dfde39100000000 0x00dfde3910000000 0x0ffff79380000003 0xf0ffff7938000000

def z233 : W := mkw 0x0000000000402802 0x0000000000040280 0xb000000041c07c04 0x0b000000041c07c0

def z234 : W := mkw 0x008980b4020d0550 0x4008980b4020d055 0x318181f006270fc7 0x9318181f006270fc

def z235 : W := mkw 0x0022a391c0201080 0x00022a391c020108 0x9067f793c02070c7 0xd9067f793c02070c

def z236 : W := mkw 0x4fddccfe00000000 0x04fddccfe0000000 0x4f9989fc00000003 0xb4f9989fc0000000

def z237 : W := mkw 0x00890000020c0000 0x000890000020c000 0x719989e0063f8f0f 0xb719989e0063f8f0

def z238 : W := mkw 0x0b400c402d40ea07 0x00b400c402d40ea0 0xff8008607fc0ff0c 0x2ff8008607fc0ff0

def z239 : W := mkw 0x549ff0bfc0a314c0 0x2549ff0bfc0a314c 0x001ff01f802700c1 0x0001ff01f802700c

def z240 : W := mkw 0x16363f0bd8f2f8a6 0xa16363f0bd8f2f8a 0xde7e7e1ff9f8f0ff 0x7de7e7e1ff9f8f0f

def z241 : W := mkw 0x4634afff00000000 0x04634afff0000000 0x4e1e0fff80000003 0x74e1e0fff8000000

def z242 : W := mkw 0x1b623f41ede2fa87 0x21b623f41ede2fa8 0x8e667603f9c07000 0x48e667603f9c0700

def z243 : W := mkw 0x6ffdefff371c0008 0x06ffdefff371c000 0x4fffffffbe18000b 0xf4fffffffbe18000

def z244 : W := mkw 0x108bb0b5c2af15d0 0x6108bb0b5c2af15d 0x001ff01f803f00f1 0x0001ff01f803f00f

def z245 : W := mkw 0x00000000020d0550 0x400000000020d055 0x00000000003f00f0 0x000000000003f00f

def z246 : W := mkw 0x000080b4020d0550 0x4000080b4020d055 0x700009fc063f8ffe 0x0700009fc063f8ff

def z247 : W := mkw 0x10abb3b5c2ef3dd2 0x610abb3b5c2ef3dd 0xb07ff79fc1ff7cf7 0xdb07ff79fc1ff7cf

def z248 : W := mkw 0x0634af9b00000000 0x00634af9b0000000 0x4e7fff9f80000003 0xf4e7fff9f8000000

def z249 : W := mkw 0x4ffdefff1810c024 0x84ffdefff1810c02 0x4fffffffb818803b 0xf4fffffffb818803

def z250 : W := mkw 0x06160c0ad830d0a4 0x806160c0ad830d0a 0x4e1e081fb83880f9 0x24e1e081fb83880f

def z251 : W := mkw 0x4ffdefff2d00c205 0x04ffdefff2d00c20 0x4fffffffbe00830b 0xf4fffffffbe00830

def z252 : W := mkw 0x0000000000000000 0x0000000000000000 0x10000000003880fc 0x010000000003880f

def z253 : W := mkw 0x0414000a00000000 0x00414000a0000000 0x001e001f80000001 0x0001e001f8000000

def z254 : W := mkw 0x00a9a3b5020d0550 0x400a9a3b5020d055 0x71ffffff863f8fff 0xf71ffffff863f8ff

def z255 : W := mkw 0x29c9d0b4278f0558 0x429c9d0b4278f055 0x21e1f1e007c70f00 0x821e1f1e007c70f0

def z256 : W := mkw 0x2d56500075b20008 0x02d56500075b2000 0x8e66700079c00000 0x48e66700079c0000

def z257 : W := mkw 0x0b600f402d40ea07 0x00b600f402d40ea0 0x6fe009e03fc08f08 0xa6fe009e03fc08f0

def z258 : W := mkw 0x06140c0a1810c024 0x806140c0a1810c02 0xde180e0c7818f03e 0x7de180e0c7818f03

def z259 : W := mkw 0x0b600f4000402802 0x00b600f400040280 0xffe00fe041c07c06 0xfffe00fe041c07c0

def z260 : W := mkw 0x2fdd4c403f1cc20d 0x02fdd4c403f1cc20 0x4f9808603e188308 0x24f9808603e18830

def z261 : W := mkw 0x1000100000c32c42 0x21000100000c32c4 0x2000000001c70c00 0x02000000001c70c0

def z262 : W := mkw 0x2d56500075b20008 0x02d56500075b2000 0x8e7e700079f8000d 0x78e7e700079f8000

def z263 : W := mkw 0x1b60afd1ad41fec7 0x21b60afd1ad41fec 0xffe00ff3ffc0ffce 0xfffe00ff3ffc0ffc

def z264 : W := mkw 0x1222bf91c8e3fcc6 0x21222bf91c8e3fcc 0xfe67ff93f9e7fccf 0xffe67ff93f9e7fcc

def z265 : W := mkw 0x09c980b4270d0550 0x409c980b4270d055 0xfff989fc7fff8fff 0xffff989fc7fff8ff

def z266 : W := mkw 0x4f74efff00000000 0x04f74efff0000000 0x4e667fff80000002 0x44e667fff8000000

def z267 : W := mkw 0x2fdd4c0a3f1cc02c 0x82fdd4c0a3f1cc02 0x4f98080c3e188038 0x24f98080c3e18803

def z268 : W := mkw 0x4fddecff00000000 0x04fddecff0000000 0x4f9ff87f80000001 0x24f9ff87f8000000

def z269 : W := mkw 0x2002100077be0008 0x02002100077be000 0xa067f0007fff000d 0xda067f0007fff000

def z270 : W := mkw 0x00000000020d0550 0x400000000020d055 0x2000000006070f00 0x02000000006070f0

def z271 : W := mkw 0x008980b4020c0110 0x4008980b4020c011 0x419989fc0618833b 0xb419989fc0618833

def z272 : W := mkw 0x2b621f407ffeea0f 0x02b621f407ffeea0 0xffe00fe07fffff0e 0xfffe00fe07fffff0

def z273 : W := mkw 0x069f8cbeda3dd5f4 0xc069f8cbeda3dd5f 0xff9f8ffffe3fffff 0xfff9f8ffffe3ffff

def z274 : W := mkw 0x0000000000000000 0x0000000000000000 0x8e0000007800000c 0x78e0000007800000

def z275 : W := mkw 0x0b600f400800c004 0x00b600f400800c00 0xdfe00fe07800f00e 0xfdfe00fe07800f00

def z276 : W := mkw 0x0000809000000000 0x0000080900000000 0x0001819000000003 0x9000181900000000

def z277 : W := mkw 0x1022b3b5c0e33dd2 0x61022b3b5c0e33dd 0xf067ffffc1e7fff7 0xdf067ffffc1e7fff

def z278 : W := mkw 0x0002000040200000 0x0000200004020000 0x8006000040200005 0x5800600004020000

def z279 : W := mkw 0x54bff3bfc0e33cc2 0x254bff3bfc0e33cc 0xb07ff79fc1e77cc7 0xdb07ff79fc1e77cc

def z280 : W := mkw 0x2ddf500077be0008 0x02ddf500077be000 0xfffff81c7fff80ff 0xffffff81c7fff80f

def z281 : W := mkw 0x3dfff3b5f7ff3dda 0x63dfff3b5f7ff3dd 0xffffffffffffffff 0xffffffffffffffff

def z282 : W := mkw 0x0d54400000000000 0x00d5440000000000 0x0e66700000000000 0x40e6670000000000

def z283 : W := mkw 0x6fff7f4b77be0008 0x06fff7f4b77be000 0xaffff603ffff000d 0xfaffff603ffff000

def z284 : W := mkw 0x0940000025000000 0x0094000002500000 0x21e0000007c00000 0x821e0000007c0000

def z285 : W := mkw 0x00000000020d0550 0x400000000020d055 0x7018081c063f8fff 0x37018081c063f8ff

def z286 : W := mkw 0x6dfff3f577be0008 0x06dfff3f577be000 0xaffff1e07fff000d 0xfaffff1e07fff000

def z287 : W := mkw 0x008980b4020d0550 0x4008980b4020d055 0x519809fc06188ffa 0x2519809fc06188ff

def z288 : W := mkw 0x02000c000800c004 0x002000c000800c00 0xde180e1c7838f0ff 0x7de180e1c7838f0f

def z289 : W := mkw 0x4ffdefff00010440 0x04ffdefff0001044 0x7fffffff80270cc7 0xf7fffffff80270cc

def z290 : W := mkw 0x008980b4020d0550 0x4008980b4020d055 0x619989ec061f8f38 0xa619989ec061f8f3

def z291 : W := mkw 0x1962b391e5e33cc2 0x21962b391e5e33cc 0xbfe7f793ffe77ccf 0xfbfe7f793ffe77cc

def z292 : W := mkw 0x49e9e3f525402a03 0x049e9e3f525402a0 0x21e1f1e007c00f00 0x821e1f1e007c00f0

def z293 : W := mkw 0x00020000c0201080 0x000020000c020108 0x00060013802000c1 0x000060013802000c

def z294 : W := mkw 0x2ddf500af7be10a8 0x82ddf500af7be10a 0xaffff01fffff00fd 0xfaffff01fffff00f

def z295 : W := mkw 0x008980b4020d0550 0x4008980b4020d055 0x3019819c003f0cf7 0x93019819c003f0cf

def z296 : W := mkw 0x0bc90c642f0cc315 0x40bc90c642f0cc31 0x4f98086c3e188338 0x24f98086c3e18833

def z297 : W := mkw 0x4ffd6f6f00000000 0x04ffd6f6f0000000 0x4ffe7e6f80000000 0x64ffe7e6f8000000

def z298 : W := mkw 0x208b100077be0008 0x0208b100077be000 0xa19980007fff000d 0xba19980007fff000

def z299 : W := mkw 0x0020030000402802 0x0002003000040280 0x8060060041c07000 0x48060060041c0700

def z300 : W := mkw 0x000000002d40ea07 0x0000000002d40ea0 0xf18009e07fc0ff0e 0xbf18009e07fc0ff0

def z301 : W := mkw 0x1002b091c0a314c0 0x21002b091c0a314c 0x9007f613c02770c7 0x59007f613c02770c

def z302 : W := mkw 0x6ddff0bf77be0008 0x06ddff0bf77be000 0xaffff01fffff000d 0xfaffff01fffff000

def z303 : W := mkw 0x1022b391c0e33cc2 0x21022b391c0e33cc 0x8067f613c1e770c1 0x48067f613c1e770c

def z304 : W := mkw 0x0000809000010440 0x0000080900001044 0x1000019000000cc2 0x01000019000000cc

def z305 : W := mkw 0x00020000c0201080 0x000020000c020108 0x90000000402070c4 0x090000000402070c

def z306 : W := mkw 0x4ffdefff00000000 0x04ffdefff0000000 0x7fffffff86008f0f 0xf7fffffff86008f0

def z307 : W := mkw 0x008980b400000000 0x0008980b40000000 0x0019801c00000001 0x00019801c0000000

def z308 : W := mkw 0x02020c00d830d0a4 0x802020c00d830d0a 0xde000e007838f0fe 0x7de000e007838f0f

def z309 : W := mkw 0x0414000000000000 0x0041400000000000 0x0e1e000000000001 0x70e1e00000000000

def z310 : W := mkw 0x4ffdefff00000000 0x04ffdefff0000000 0x4f980fff80000002 0x24f980fff8000000

def z311 : W := mkw 0x00890024020c0110 0x400890024020c011 0x0180006006000300 0x0018000600600030

def z312 : W := mkw 0x3d76f391f5f33cca 0x23d76f391f5f33cc 0xbe67f793f9e77cc7 0xdbe67f793f9e77cc

def z313 : W := mkw 0x4f746f4b00000000 0x04f746f4b0000000 0x4e7e7e1f80000003 0x74e7e7e1f8000000

def z314 : W := mkw 0x0002100040a20000 0x00002100040a2000 0x0007f00000270001 0x00007f0000027000

def z315 : W := mkw 0x1022b391ede3fec7 0x21022b391ede3fec 0xb067f793ffe7ffcf 0xdb067f793ffe7ffc

def z316 : W := mkw 0x0416000050300000 0x0041600005030000 0x8e06000078000000 0x48e0600007800000

def z317 : W := mkw 0x0b608fd02d41ee47 0x00b608fd02d41ee4 0xffe18ff07fe7ffcf 0xfffe18ff07fe7ffc

def z318 : W := mkw 0x42202f4b00000000 0x042202f4b0000000 0x0000060380000000 0x0000006038000000

def z319 : W := mkw 0x0ddf400050300000 0x00ddf40005030000 0x8ffff0007838000d 0xf8ffff0007838000

def z320 : W := mkw 0x4ffdefff00000000 0x04ffdefff0000000 0x0fe7f7e380000000 0xc0fe7f7e38000000

def z321 : W := mkw 0x008b80b4c22d15d0 0x4008b80b4c22d15d 0xf19f8fffc63fffff 0xff19f8fffc63ffff

def z322 : W := mkw 0x00890024020c0110 0x400890024020c011 0x5198087c063883ff 0x35198087c063883f

def z323 : W := mkw 0x1b60bfd12dc3ee47 0x21b60bfd12dc3ee4 0xffe1ffe07fc7ff0e 0xfffe1ffe07fc7ff0

def z324 : W := mkw 0x4ffdefff00000000 0x04ffdefff0000000 0x0e7ff61f80000001 0x40e7ff61f8000000

def z325 : W := mkw 0x06160c0ad830d0a4 0x806160c0ad830d0a 0xce1e0e0ff818f038 0x6ce1e0e0ff818f03

def z326 : W := mkw 0x09e983f4274d2f53 0x409e983f4274d2f5 0x71f989fc07ff8fff 0xb71f989fc07ff8ff

def z327 : W := mkw 0x00890024020c0110 0x400890024020c011 0x6199886c063f833d 0xb6199886c063f833

def z328 : W := mkw 0x4220afff00000000 0x04220afff0000000 0x4067ffff80000003 0xd4067ffff8000000

def z329 : W := mkw 0x4ffdefff020c0110 0x44ffdefff020c011 0x4fffffff8618833b 0xf4fffffff8618833

def z330 : W := mkw 0x4f746f4b2d40ea07 0x04f746f4b2d40ea0 0xffe67fe3ffc0ff0e 0xfffe67fe3ffc0ff0

def z331 : W := mkw 0x06140c0a0800c004 0x006140c0a0800c00 0xde1e0e1ff800f00f 0x7de1e0e1ff800f00

def z332 : W := mkw 0x16161c0ad8f3fce6 0xa16161c0ad8f3fce 0xfe1e0e1ff9fffcff 0x7fe1e0e1ff9fffcf

def z333 : W := mkw 0x02000c000800c004 0x002000c000800c00 0x8e00060078007000 0x48e0006007800700

def z334 : W := mkw 0x0000000000000000 0x0000000000000000 0x4180086006008308 0x2418008600600830

def z335 : W := mkw 0x0000000000000000 0x0000000000000000 0x10000010002000c7 0x110000010002000c

def z336 : W := mkw 0x0fff8ffeff7dfff7 0xc0fff8ffeff7dfff 0xffff8fffffffffff 0xfffff8ffffffffff

def z337 : W := mkw 0x2fdfdcbeffbfd5fc 0xc2fdfdcbeffbfd5f 0xffffffffffffffff 0xffffffffffffffff

def z338 : W := mkw 0x1436b391d0f33cc2 0x21436b391d0f33cc 0xbe7ff793f9ff7ccf 0xfbe7ff793f9ff7cc

def z339 : W := mkw 0x59ebf3f5c0e33cc2 0x259ebf3f5c0e33cc 0xb1e7f7f3c1e77cc7 0xdb1e7f7f3c1e77cc

def z340 : W := mkw 0x00890024020d0550 0x400890024020d055 0x7198086c063f8ffc 0x27198086c063f8ff

def z341 : W := mkw 0x008980b400000000 0x0008980b40000000 0x018181e000000000 0x8018181e00000000

def z342 : W := mkw 0x000000000800c004 0x0000000000800c00 0x900000007800f00c 0x0900000007800f00

def z343 : W := mkw 0x06161c0ad8b2d0a4 0x806161c0ad8b2d0a 0xfe7ffe1ff9fff0ff 0xffe7ffe1ff9fff0f

def z344 : W := mkw 0x069f0c2eda3cd1b4 0xc069f0c2eda3cd1b 0xdf9e0e7ffe38f3ff 0x7df9e0e7ffe38f3f

def z345 : W := mkw 0x3dff7301f7fe388a 0x23dff7301f7fe388 0xaffff603ffff700d 0xfaffff603ffff700

def z346 : W := mkw 0x4fdd4c6e020c0110 0x44fdd4c6e020c011 0x4f98086c06188338 0x24f98086c0618833

def z347 : W := mkw 0x06140c0a8800d0a4 0x806140c0a8800d0a 0x5e1e0e1f8000f0f3 0x75e1e0e1f8000f0f

def z348 : W := mkw 0x2ddf500075b20008 0x02ddf500075b2000 0x8ffff00079c00001 0xf8ffff00079c0000

def z349 : W := mkw 0x3ddff091f7bf14c8 0x23ddff091f7bf14c 0xaffff013ffff00cd 0xfaffff013ffff00c

def z350 : W := mkw 0x3022b391f7ff3cca 0x23022b391f7ff3cc 0xb067f793ffff7ccf 0xdb067f793ffff7cc

def z351 : W := mkw 0x0960034025402a03 0x00960034025402a0 0xafe001e07fc00f0c 0xfafe001e07fc00f0

def z352 : W := mkw 0x008980b400000000 0x0008980b40000000 0x519989fc003880ff 0xb519989fc003880f

def z353 : W := mkw 0x0000000000000000 0x0000000000000000 0x5000081c000080f2 0x05000081c000080f

def z354 : W := mkw 0x2fdf5c0a7fbec02c 0x82fdf5c0a7fbec02 0xeffff80c7fff803d 0xfeffff80c7fff803

def z355 : W := mkw 0x200210007ffeea0f 0x0200210007ffeea0 0xb00000007fffff0c 0x0b00000007fffff0

def z356 : W := mkw 0x06140c0a1810c024 0x806140c0a1810c02 0x4e1e0e1fb818803b 0x74e1e0e1fb818803

def z357 : W := mkw 0x06160c0ad830d0a4 0x806160c0ad830d0a 0xde060e1ff800f0f2 0x4de060e1ff800f0f

def z358 : W := mkw 0x4f544c4a00000000 0x04f544c4a0000000 0x0e00000000000000 0x00e0000000000000

def z359 : W := mkw 0x29e9534027ce2a0b 0x029e9534027ce2a0 0x21e1f1e007c70f00 0x821e1f1e007c70f0

def z360 : W := mkw 0x2ddf500077be0008 0x02ddf500077be000 0xaf9800007fff000c 0x2af9800007fff000

def z361 : W := mkw 0x16bfbfbfdafffdf6 0xe16bfbfbfdafffdf 0xffffffffffffffff 0xffffffffffffffff

def z362 : W := mkw 0x0b620f40fd70faa7 0x80b620f40fd70faa 0xffe00fe07ff8fffe 0xfffe00fe07ff8fff

def z363 : W := mkw 0x069d8cbe00000000 0x0069d8cbe0000000 0x4f9f8fff80000003 0xf4f9f8fff8000000

def z364 : W := mkw 0x0ddd4000020c0000 0x00ddd4000020c000 0x2ffff000063f000d 0xf2ffff000063f000

def z365 : W := mkw 0x06160c0a5830c024 0x806160c0a5830c02 0xce1e080c7838803d 0x7ce1e080c7838803

def z366 : W := mkw 0x2002100075b20008 0x02002100075b2000 0x8000000079c00000 0x08000000079c0000

def z367 : W := mkw 0x00890024020c0110 0x400890024020c011 0x0018000c00180030 0x00018000c0018003

def z368 : W := mkw 0x1020a39180413cc2 0x21020a39180413cc 0xb0600793c1c07cc6 0xdb0600793c1c07cc

def z369 : W := mkw 0x6fffffff75b20008 0x06fffffff75b2000 0xcffffffff9c00003 0xfcffffffff9c0000

def z370 : W := mkw 0x069f8cbed830d0a4 0x8069f8cbed830d0a 0xdf9f8ffff838f0ff 0xfdf9f8ffff838f0f

def z371 : W := mkw 0x4ffdefff0800c004 0x04ffdefff0800c00 0xdffffffff800f00f 0xfdffffffff800f00

def z372 : W := mkw 0x5fffffffd8f3fce6 0xa5fffffffd8f3fce 0xfffffffff9fffcff 0xffffffffff9fffcf

def z373 : W := mkw 0x008980b4020d0550 0x4008980b4020d055 0x619989fc06070f03 0xb619989fc06070f0

def z374 : W := mkw 0x4ffdefff0840ea07 0x04ffdefff0840ea0 0x5fffffff8000ff03 0xf5fffffff8000ff0

def z375 : W := mkw 0x108b90b4c2ef3dd2 0x6108b90b4c2ef3dd 0xf19989fc47ffffff 0xbf19989fc47fffff

def z376 : W := mkw 0x2d54400035100008 0x02d5440003510000 0x0e00000038000000 0x00e0000003800000

def z377 : W := mkw 0x0022b39140a20000 0x00022b39140a2000 0xa067f793c1e70007 0xda067f793c1e7000

def z378 : W := mkw 0x26161c0affbed0ac 0x826161c0affbed0a 0xfe1e0e1ffffff0ff 0x7fe1e0e1ffffff0f

def z379 : W := mkw 0x4ffd6f4b00000000 0x04ffd6f4b0000000 0x0ffff60380000001 0xf0ffff6038000000

def z380 : W := mkw 0x1020b39180c33cc2 0x21020b39180c33cc 0x3061f79381c77cc2 0x83061f79381c77cc

def z381 : W := mkw 0x0416000ad03010a0 0x80416000ad03010a 0x501e081f803880ff 0x3501e081f803880f

def z382 : W := mkw 0x0940004025000201 0x0094000402500020 0x0180006006000300 0x0018000600600030

def z383 : W := mkw 0x1000a091800114c0 0x21000a091800114c 0x00000013800000c0 0x000000013800000c

def z384 : W := mkw 0x1020b39100c32c42 0x21020b39100c32c4 0x2067f79381c70c03 0xd2067f79381c70c0

def z385 : W := mkw 0x0ffd4f4000000000 0x00ffd4f400000000 0x4fffffe000000003 0xf4fffffe00000000

def z386 : W := mkw 0x094000002d40ea07 0x0094000002d40ea0 0xbfe000007fc0ff0c 0xfbfe000007fc0ff0

def z387 : W := mkw 0x2fdf5c007fbec00c 0x02fdf5c007fbec00 0xfffffe007ffff00f 0xffffffe007ffff00

def z388 : W := mkw 0x10021000c0e33cc2 0x210021000c0e33cc 0xb067f00041e77cc5 0xdb067f00041e77cc

def z389 : W := mkw 0x2ddd5000278e0008 0x02ddd5000278e000 0x2ffff00007c70001 0xf2ffff00007c7000

def z390 : W := mkw 0x0636af9bd830d0a4 0x80636af9bd830d0a 0xde7fff9ff838f0ff 0xfde7fff9ff838f0f

def z391 : W := mkw 0x0000000000000000 0x0000000000000000 0x0018001c003800f1 0x00018001c003800f

def z392 : W := mkw 0x2ddfd0b477bf0558 0x42ddfd0b477bf055 0xaffff01c7fff00fd 0xfaffff01c7fff00f

def z393 : W := mkw 0x4fdf4c6ed830d0a4 0x84fdf4c6ed830d0a 0xdf9e0e7ff838f0ff 0x7df9e0e7ff838f0f

def z394 : W := mkw 0x2fdf5c0affbed0ac 0x82fdf5c0affbed0a 0xaffff603ffff700d 0xfaffff603ffff700

def z395 : W := mkw 0x10a9b3b502cf2d52 0x610a9b3b502cf2d5 0x21e1f1e007c70f00 0x821e1f1e007c70f0

def z396 : W := mkw 0x2f765f407df2ea0f 0x02f765f407df2ea0 0xffe67fe07fc0ff0e 0xfffe67fe07fc0ff0

def z397 : W := mkw 0x0ffd4f402d40ea07 0x00ffd4f402d40ea0 0xffffffe07fc0ff0f 0xfffffffe07fc0ff0

def z398 : W := mkw 0x02200f400840ea07 0x002200f400840ea0 0x0000060000007000 0x0000006000000700

def z399 : W := mkw 0x4ffdefff25000000 0x04ffdefff2500000 0xefffffffffc0000f 0xfefffffffffc0000

def z400 : W := mkw 0x0b600f402d40ea07 0x00b600f402d40ea0 0xafe007e07fc07f00 0xcafe007e07fc07f0

def z401 : W := mkw 0x0be90f402f4cea07 0x00be90f402f4cea0 0xfff98fe07fffff0f 0xffff98fe07fffff0

def z402 : W := mkw 0x10abb391c2ef3cc2 0x210abb391c2ef3cc 0xb1fff793c7ff7ccf 0xfb1fff793c7ff7cc

def z403 : W := mkw 0x4ffdefff020d0550 0x44ffdefff020d055 0x4fffffff803f00f3 0xf4fffffff803f00f

def z404 : W := mkw 0x2f765f407df2ea0f 0x02f765f407df2ea0 0x8e66760079c07000 0x48e66760079c0700

def z405 : W := mkw 0x0b400c402d00c205 0x00b400c402d00c20 0x7f8009e03e008f0e 0xb7f8009e03e008f0

def z406 : W := mkw 0x1020a39180413cc2 0x21020a39180413cc 0x3001879380277cc7 0x93001879380277cc

def z407 : W := mkw 0x1962b3d1e5e33ec3 0x21962b3d1e5e33ec 0xb1e7f7f3c7e77fc7 0xdb1e7f7f3c7e77fc

def z408 : W := mkw 0x10021000ede3fec7 0x210021000ede3fec 0xb00000007fe7ffcc 0x0b00000007fe7ffc

def z409 : W := mkw 0x34bff391d2ff3cca 0x234bff391d2ff3cc 0xb07ff793c1ff7cc7 0xdb07ff793c1ff7cc

def z410 : W := mkw 0x0960030025402802 0x0096003002540280 0xbfe007807fc07c0e 0xfbfe007807fc07c0

def z411 : W := mkw 0x02020c0ad830d0a4 0x802020c0ad830d0a 0xd0000e1ff838f0fe 0x0d0000e1ff838f0f

def z412 : W := mkw 0x20001000278e0008 0x020001000278e000 0x2000000007c70000 0x02000000007c7000

def z413 : W := mkw 0x06140c0a1810c024 0x806140c0a1810c02 0x0e00000038000000 0x00e0000003800000

def z414 : W := mkw 0x008980b4020d0550 0x4008980b4020d055 0x718189e006078f0e 0xb718189e006078f0

def z415 : W := mkw 0x0b400c4000000000 0x00b400c400000000 0x4f80086000000000 0x24f8008600000000

def z416 : W := mkw 0x4ffdefff00000000 0x04ffdefff0000000 0x5fffffff803880ff 0xf5fffffff803880f

def z417 : W := mkw 0x02898cbe8a0dd5f4 0xc02898cbe8a0dd5f 0x71998fff863fffff 0xb71998fff863ffff

def z418 : W := mkw 0x4fddccfe020d0550 0x44fddccfe020d055 0x7f9989fc063f8fff 0xb7f9989fc063f8ff

def z419 : W := mkw 0x0b600f402d40ea07 0x00b600f402d40ea0 0xde600e0079c0f00e 0x7de600e0079c0f00

def z420 : W := mkw 0x0be98ff400000000 0x00be98ff40000000 0x4ff98ffc00000003 0xf4ff98ffc0000000

def z421 : W := mkw 0x29c95000278e0008 0x029c95000278e000 0x21f9f00007ff000d 0xb21f9f00007ff000

def z422 : W := mkw 0x0416000ad03010a0 0x80416000ad03010a 0x0006000380000000 0x0000600038000000

def z423 : W := mkw 0x1022b391c0e33cc2 0x21022b391c0e33cc 0xf1e7fff3c7e7ffcf 0xff1e7fff3c7e7ffc

def z424 : W := mkw 0x449de0bf020d0550 0x4449de0bf020d055 0x001ff01f803f00f1 0x0001ff01f803f00f

def z425 : W := mkw 0x0000000000000000 0x0000000000000000 0x0006061380000003 0x5000606138000000

def z426 : W := mkw 0x02000c000800c004 0x002000c000800c00 0x50000e000000f002 0x050000e000000f00

def z427 : W := mkw 0x000080b400000000 0x0000080b40000000 0x400009fc00000002 0x0400009fc0000000

def z428 : W := mkw 0x0002100040a20000 0x00002100040a2000 0xa000000041e70004 0x0a000000041e7000

def z429 : W := mkw 0x2d56500075b20008 0x02d56500075b2000 0xafe670007fc0000c 0xfafe670007fc0000

def z430 : W := mkw 0x0000809000010440 0x0000080900001044 0x718189f006278fcf 0xb718189f006278fc

def z431 : W := mkw 0x02200f4a8840faa7 0x802200f4a8840faa 0x50000fff8000fff2 0x050000fff8000fff

def z432 : W := mkw 0x5222bfffc0e33cc2 0x25222bfffc0e33cc 0xf067ffffc1e77cc7 0xdf067ffffc1e77cc

def z433 : W := mkw 0x4220afff00010550 0x44220afff0001055 0x50000fff80008ff2 0x050000fff80008ff

def z434 : W := mkw 0x249f500052be0008 0x0249f500052be000 0x8e1ff000783f000d 0x78e1ff000783f000

def z435 : W := mkw 0x049f80bed23d15f0 0xc049f80bed23d15f 0x001f801f803f00f1 0x0001f801f803f00f

def z436 : W := mkw 0x4f766f4bd830d0a4 0x84f766f4bd830d0a 0xde7e7e1ff838f0ff 0x7de7e7e1ff838f0f

def z437 : W := mkw 0x008980b42f4def57 0x4008980b42f4def5 0xf19989fc7fffffff 0xbf19989fc7ffffff

def z438 : W := mkw 0x30021000f7ff3cca 0x230021000f7ff3cc 0xb00000007fff7ccc 0x0b00000007fff7cc

def z439 : W := mkw 0x008980b4020d0550 0x4008980b4020d055 0x219981e0063f0f0d 0xb219981e0063f0f0

def z440 : W := mkw 0x2be95f402fceea0f 0x02be95f402fceea0 0xffe1ffe07fc7ff0e 0xfffe1ffe07fc7ff0

def z441 : W := mkw 0x29c9d0b4278f0558 0x429c9d0b4278f055 0x71f9f9fc07ff8fff 0xb71f9f9fc07ff8ff

def z442 : W := mkw 0x49e9e3f500000000 0x049e9e3f50000000 0x41f9f9fc00000003 0xb41f9f9fc0000000

def z443 : W := mkw 0x06140c0a9810d0a4 0x806140c0a9810d0a 0x5e180e1fb818f0fa 0x25e180e1fb818f0f

def z444 : W := mkw 0x0b400c402d00c205 0x00b400c402d00c20 0x0e00000038000000 0x00e0000003800000

def z445 : W := mkw 0x0416000ad03010a0 0x80416000ad03010a 0x8e1e001ff83800fd 0x78e1e001ff83800f

def z446 : W := mkw 0x2ffd4f403f5cea0f 0x02ffd4f403f5cea0 0xfff80fe07fd8ff0e 0xffff80fe07fd8ff0

def z447 : W := mkw 0x4636afffd830d0a4 0x84636afffd830d0a 0xde1e0ffff838f0ff 0x7de1e0ffff838f0f

def z448 : W := mkw 0x39e9f39127cf2c4a 0x239e9f39127cf2c4 0x21e1f18007c70c00 0x821e1f18007c70c0

def z449 : W := mkw 0x4fffefffc0201080 0x04fffefffc020108 0xdfffffffc02070c7 0xfdfffffffc02070c

def z450 : W := mkw 0x008b100042ae0000 0x0008b100042ae000 0xa1fff00047ff000d 0xfa1fff00047ff000

def z451 : W := mkw 0x0940000025000000 0x0094000002500000 0xffe009e07fc08f0e 0xfffe009e07fc08f0

def z452 : W := mkw 0x09c9400000000000 0x009c940000000000 0x01e1f00000000000 0x801e1f0000000000

def z453 : W := mkw 0x0020030000402802 0x0002003000040280 0x2060018001c00c00 0x82060018001c00c0

def z454 : W := mkw 0x0f740f4a3d50ea27 0x80f740f4a3d50ea2 0xfff80fec7fd8ff3e 0xffff80fec7fd8ff3

def z455 : W := mkw 0x249f500077be0008 0x0249f500077be000 0xa01ff0007fff000d 0x0a01ff0007fff000

def z456 : W := mkw 0x449d402e00000000 0x0449d402e0000000 0x0018000c00000000 0x00018000c0000000

def z457 : W := mkw 0x0000a09100000000 0x00000a0910000000 0x0007f01380000001 0x00007f0138000000

def z458 : W := mkw 0x0000809000010440 0x0000080900001044 0x2001818000070c00 0x82001818000070c0

def z459 : W := mkw 0x02200f400840ea07 0x002200f400840ea0 0xde000fe07800ff0e 0x7de000fe07800ff0

def z460 : W := mkw 0x249f500052be0008 0x0249f500052be000 0xa07ff00041ff0005 0xda07ff00041ff000

def z461 : W := mkw 0x0b621f406de2ea07 0x00b621f406de2ea0 0xffe7ffe07fe7ff0f 0xfffe7ffe07fe7ff0

def z462 : W := mkw 0x4fdd4c6e00000000 0x04fdd4c6e0000000 0x4ffff86c00000001 0xf4ffff86c0000000

def z463 : W := mkw 0x10223301c0e23882 0x210223301c0e2388 0xa067f603c1e77005 0xda067f603c1e7700

def z464 : W := mkw 0x06160c0ad830d0a4 0x806160c0ad830d0a 0x9e060603f838f0fc 0x49e060603f838f0f

def z465 : W := mkw 0x0000000025402a03 0x00000000025402a0 0x2000000007c00f00 0x02000000007c00f0

def z466 : W := mkw 0x249d4000121c0008 0x0249d4000121c000 0x0018000000180000 0x0001800000018000

def z467 : W := mkw 0x049f0000523c0000 0x0049f0000523c000 0xaf9f80007e3f000d 0xfaf9f80007e3f000

def z468 : W := mkw 0x0002909040a30440 0x00002909040a3044 0xb067f19041e70cc7 0xdb067f19041e70cc

def z469 : W := mkw 0x4fffefffd830d0a4 0x84fffefffd830d0a 0xcffffffff8007003 0xfcffffffff800700

def z470 : W := mkw 0x096003402d40ea07 0x0096003402d40ea0 0xb1e001e07fc0ff0c 0x8b1e001e07fc0ff0

def z471 : W := mkw 0x0b600f402d40ea07 0x00b600f402d40ea0 0xafe006007fc0700c 0xfafe006007fc0700

def z472 : W := mkw 0x0000809000010440 0x0000080900001044 0x7019899c003f8cff 0xb7019899c003f8cf

def z473 : W := mkw 0x0000000000010550 0x4000000000001055 0x1000000000008ff0 0x01000000000008ff

def z474 : W := mkw 0x4fffefff50300000 0x04fffefff5030000 0xcffffffff838000f 0xfcffffffff838000

def z475 : W := mkw 0x06160c0ad830d0a4 0x806160c0ad830d0a 0xde060e03f800f00e 0x7de060e03f800f00

def z476 : W := mkw 0x00a9a3b500000000 0x000a9a3b50000000 0x41ffffff80000003 0xf41ffffff8000000

def z477 : W := mkw 0x0b600f402f4def57 0x40b600f402f4def5 0xffe00fe07ffffffe 0xfffe00fe07ffffff

def z478 : W := mkw 0x4dfde3ff00000000 0x04dfde3ff0000000 0x01fff1ff80000001 0x801fff1ff8000000

def z479 : W := mkw 0x1222bf9bc8e3fce6 0xa1222bf9bc8e3fce 0xf067ff9fc1e7fcf7 0xdf067ff9fc1e7fcf

def z480 : W := mkw 0x0020030000402802 0x0002003000040280 0x1000078000007c02 0x01000078000007c0

def z481 : W := mkw 0x2ddf500077bf0558 0x42ddf500077bf055 0xbffff0007fff8ffd 0xfbffff0007fff8ff

def z482 : W := mkw 0x5220afff80413cc2 0x25220afff80413cc 0x50000fff80007cc2 0x050000fff80007cc

def z483 : W := mkw 0x4ffd4f6e2d40ea07 0x04ffd4f6e2d40ea0 0xfff80fec7fc0ff0e 0xffff80fec7fc0ff0

def z484 : W := mkw 0x2dff534077fe2a0b 0x02dff534077fe2a0 0xaffff1e07fff0f0d 0xfaffff1e07fff0f0

def z485 : W := mkw 0x1002b091c0a314c0 0x21002b091c0a314c 0xa067f013c1e700c5 0xda067f013c1e700c

def z486 : W := mkw 0x06160c0ad830d0a4 0x806160c0ad830d0a 0xde18080c7838f0fc 0x2de18080c7838f0f

def z487 : W := mkw 0x0000000000000000 0x0000000000000000 0x500008000000800e 0x3500008000000800

def z488 : W := mkw 0x0f760f407d70ea07 0x00f760f407d70ea0 0xfffe0fe07ff8ff0f 0xffffe0fe07ff8ff0

def z489 : W := mkw 0x5fffffffede3fec7 0x25fffffffede3fec 0xffffffffffe7ffcf 0xfffffffffffe7ffc

def z490 : W := mkw 0x249fd0b452bf0558 0x4249fd0b452bf055 0x719ff9fc063f8fff 0xb719ff9fc063f8ff

def z491 : W := mkw 0x5f767f4bc0e23882 0x25f767f4bc0e2388 0x8e667603c1c07000 0x48e667603c1c0700

def z492 : W := mkw 0x0000000000000000 0x0000000000000000 0x2001800000270005 0x9200180000027000

def z493 : W := mkw 0x0ddf500040a20000 0x00ddf500040a2000 0xaffff00041e70005 0xfaffff00041e7000

def z494 : W := mkw 0x00890000020c0000 0x000890000020c000 0x00198000003f0001 0x000198000003f000

def z495 : W := mkw 0x1022b391c0e33cc2 0x21022b391c0e33cc 0x90667793c1c07cc2 0x490667793c1c07cc

def z496 : W := mkw 0x10021000d8f3fce6 0xa10021000d8f3fce 0xb000000079fffcfc 0x0b000000079fffcf

def z497 : W := mkw 0x4ffd4f6e00000000 0x04ffd4f6e0000000 0x4ff80fec00000002 0xf4ff80fec0000000

def z498 : W := mkw 0x2fff5f4afffefaaf 0x82fff5f4afffefaa 0xffffffffffffffff 0xffffffffffffffff

def z499 : W := mkw 0x008980b4020d0550 0x4008980b4020d055 0x4199887c063f83f9 0x24199887c063f83f

def z500 : W := mkw 0x5fffffffc2ef3dd2 0x65fffffffc2ef3dd 0xffffffffc7ffffff 0xfffffffffc7fffff

def z501 : W := mkw 0x000000001810c024 0x8000000001810c02 0x0000000038188038 0x0000000003818803

def z502 : W := mkw 0x0940000000000000 0x0094000000000000 0x0fe0000000000000 0xf0fe000000000000

def z503 : W := mkw 0x0000000000000000 0x0000000000000000 0x418009e000000002 0xb418009e00000000

def z504 : W := mkw 0x02020c00c820d084 0x002020c00c820d08 0xde060e13f820f0cf 0x7de060e13f820f0c

def z505 : W := mkw 0x0940000025000000 0x0094000002500000 0x8e60000079c00000 0x48e60000079c0000

def z506 : W := mkw 0x1b621f40ede3fec7 0x21b621f40ede3fec 0xffe00fe07fe7ffce 0xfffe00fe07fe7ffc

def z507 : W := mkw 0x0960034025402a03 0x00960034025402a0 0x71e009e007c08f0e 0xb71e009e007c08f0

def z508 : W := mkw 0x1020230180403882 0x2102023018040388 0x0000060380007000 0x0000006038000700

def z509 : W := mkw 0x02000c0000000000 0x002000c000000000 0x4e000e0000000002 0x74e000e000000000

def z510 : W := mkw 0x4fffefffd03010a0 0x84fffefffd03010a 0x4fffffff803800f3 0xf4fffffff803800f

def z511 : W := mkw 0x1002b091c0e33cc2 0x21002b091c0e33cc 0xb007f013c1e77cc5 0x0b007f013c1e77cc

def z512 : W := mkw 0x069f0c0ada3cd0a4 0x8069f0c0ada3cd0a 0xff9f8e1ffe3ff0ff 0xfff9f8e1ffe3ff0f

def z513 : W := mkw 0x0b600f402d00c205 0x00b600f402d00c20 0x4fe00fe03e00830a 0xf4fe00fe03e00830

def z514 : W := mkw 0x42a9afff020d0550 0x442a9afff020d055 0x71998fff863f8fff 0xb71998fff863f8ff

def z515 : W := mkw 0x00020000da3dd5f4 0xc00020000da3dd5f 0xb00000007e3ffffc 0x0b00000007e3ffff

def z516 : W := mkw 0x02000c400800c205 0x002000c400800c20 0x4000086000008300 0x0400008600000830

def z517 : W := mkw 0x0000000000000000 0x0000000000000000 0x500009e000008f02 0x0500009e000008f0

def z518 : W := mkw 0x42a9afff00000000 0x042a9afff0000000 0x41998fff80000003 0xb41998fff8000000

def z519 : W := mkw 0x0000000000000000 0x0000000000000000 0x001800000038000d 0x3001800000038000

def z520 : W := mkw 0x0020a39100000000 0x00020a3910000000 0x0061f18000000000 0x80061f1800000000

def z521 : W := mkw 0x0be98ff42f4def57 0x40be98ff42f4def5 0xffe18fe07fc7ff0e 0xfffe18fe07fc7ff0

def z522 : W := mkw 0x1636bf9bd8f3fce6 0xa1636bf9bd8f3fce 0xbe67f793f9e77cc7 0xdbe67f793f9e77cc

def z523 : W := mkw 0x0f760f4afd70faa7 0x80f760f4afd70faa 0xde7e0e1ff9f8f0ff 0x7de7e0e1ff9f8f0f

def z524 : W := mkw 0x0089000000000000 0x0008900000000000 0x0199800000000001 0xb019980000000000

def z525 : W := mkw 0x1bebbff5efefffd7 0x61bebbff5efefffd 0xffffffffffffffff 0xffffffffffffffff

def z526 : W := mkw 0x1022b391d8f3fce6 0xa1022b391d8f3fce 0xb067f793f9fffcff 0xdb067f793f9fffcf

def z527 : W := mkw 0x10a9a3b5824d3dd2 0x610a9a3b5824d3dd 0x71998fff863fffff 0xb71998fff863ffff

def z528 : W := mkw 0x06160c0ac0201080 0x006160c0ac020108 0xde1e0e1fc02070c7 0x7de1e0e1fc02070c

def z529 : W := mkw 0x02000c000800c004 0x002000c000800c00 0x4e00080038008008 0x24e0008003800800

def z530 : W := mkw 0x0940000025000000 0x0094000002500000 0x0f8000003e000008 0x20f8000003e00000

def z531 : W := mkw 0x000080b400010550 0x4000080b40001055 0x0000001c000000f0 0x00000001c000000f

def z532 : W := mkw 0x0002100040a20000 0x00002100040a2000 0x8066700041c00000 0x48066700041c0000

def z533 : W := mkw 0x0b600f402d40ea07 0x00b600f402d40ea0 0xbe6006007fc0ff0c 0x4be6006007fc0ff0

def z534 : W := mkw 0x1022b391c0e33cc2 0x21022b391c0e33cc 0x1007f79380277cc3 0x01007f79380277cc

def z535 : W := mkw 0x649ff0bf52be0008 0x0649ff0bf52be000 0x001ff01f803f0001 0x0001ff01f803f000

def z536 : W := mkw 0x0b600f402d40ea07 0x00b600f402d40ea0 0xcfe00e607fc0f308 0x6cfe00e607fc0f30

def z537 : W := mkw 0x1416b09bd0b314e0 0xa1416b09bd0b314e 0x001ff01f803f00f1 0x0001ff01f803f00f

def z538 : W := mkw 0x0000000000000000 0x0000000000000000 0x4018080c00188038 0x24018080c0018803

def z539 : W := mkw 0x3d767301f5f2388a 0x23d767301f5f2388 0x8e667603f9c07000 0x48e667603f9c0700

def z540 : W := mkw 0x1020b39100c32c42 0x21020b39100c32c4 0x3061f19001e70cc7 0x93061f19001e70cc

def z541 : W := mkw 0x0dddc0b400000000 0x00dddc0b40000000 0x4ffff9fc00000003 0xf4ffff9fc0000000

def z542 : W := mkw 0x1436b39bd0f33ce2 0xa1436b39bd0f33ce 0xb07ff79fc1ff7cf7 0xdb07ff79fc1ff7cf

def z543 : W := mkw 0x0ddd400000000000 0x00ddd40000000000 0x0f98000000000000 0x20f9800000000000

def z544 : W := mkw 0x6fdf5c6e77be0008 0x06fdf5c6e77be000 0xeffff86c7fff000d 0xfeffff86c7fff000

def z545 : W := mkw 0x02000c0a8800d0a4 0x802000c0a8800d0a 0x50180e1f8038f0ff 0x350180e1f8038f0f

def z546 : W := mkw 0x0002000050300000 0x0000200005030000 0x800000007838000c 0x0800000007838000

def z547 : W := mkw 0x02200f4000000000 0x002200f400000000 0x40000fe000000002 0x040000fe00000000

def z548 : W := mkw 0x10abb3b5c2ef3dd2 0x610abb3b5c2ef3dd 0xb1e7f7f3c7e77fc7 0xdb1e7f7f3c7e77fc

def z549 : W := mkw 0x4be9eff52d40ea07 0x04be9eff52d40ea0 0xffe1ffe07fc0ff0e 0xfffe1ffe07fc0ff0

def z550 : W := mkw 0x3fffffd1fffffecf 0x23fffffd1fffffec 0xfffffff3ffffffcf 0xffffffff3ffffffc

def z551 : W := mkw 0x10223301c0e23882 0x210223301c0e2388 0x90667613c1e070c7 0x590667613c1e070c

def z552 : W := mkw 0x0000000000000000 0x0000000000000000 0xa060000041c00004 0xda060000041c0000

def z553 : W := mkw 0x69e9f3f5278e0008 0x069e9f3f5278e000 0x21e1f1e007c70000 0x821e1f1e007c7000

def z554 : W := mkw 0x06140c0a00000000 0x006140c0a0000000 0x4e18080c00000000 0x24e18080c0000000

def z555 : W := mkw 0x000000008800d0a4 0x8000000008800d0a 0x100000000000f0f0 0x0100000000000f0f

def z556 : W := mkw 0x4f766f4bd830d0a4 0x84f766f4bd830d0a 0x8e667603f8007000 0x48e667603f800700

def z557 : W := mkw 0x0960034025402a03 0x00960034025402a0 0x0060000001c00000 0x00060000001c0000

def z558 : W := mkw 0x0f560c0afd30d0a4 0x80f560c0afd30d0a 0xfffe0e1ffff8f0ff 0xffffe0e1ffff8f0f

def z559 : W := mkw 0x008980b400010550 0x4008980b40001055 0x519989fc00008ff3 0xb519989fc00008ff

def z560 : W := mkw 0x04160000d0301080 0x004160000d030108 0x9e1e0613f83870cf 0x79e1e0613f83870c

def z561 : W := mkw 0x0416000050300000 0x0041600005030000 0x001e000000380001 0x0001e00000038000

def z562 : W := mkw 0x2ddf5000ffbed0ac 0x82ddf5000ffbed0a 0xbffff0007ffff0fd 0xfbffff0007ffff0f

def z563 : W := mkw 0x049d400000000000 0x0049d40000000000 0x001ff00000000001 0x0001ff0000000000

def z564 : W := mkw 0x0be98ff42d40ea07 0x00be98ff42d40ea0 0xfff98ffc7fc0ff0f 0xffff98ffc7fc0ff0

def z565 : W := mkw 0x2ddfd0b477be0008 0x02ddfd0b477be000 0xeffff9fc7fff000f 0xfeffff9fc7fff000

def z566 : W := mkw 0x2ddd4000371c0008 0x02ddd4000371c000 0x0ffff0003e180009 0xf0ffff0003e18000

def z567 : W := mkw 0x06168cbed831d5f4 0xc06168cbed831d5f 0xde1e0ffff838ffff 0x7de1e0ffff838fff

def z568 : W := mkw 0x0020034000402a03 0x00020034000402a0 0x000001e000000f00 0x0000001e000000f0

def z569 : W := mkw 0x1022b391c0e33cc2 0x21022b391c0e33cc 0xb061f18041e77cc4 0x8b061f18041e77cc

def z570 : W := mkw 0x000000002d00c205 0x0000000002d00c20 0x000000003e008308 0x0000000003e00830

def z571 : W := mkw 0x29cb500067ae0008 0x029cb500067ae000 0xa1e7f00047e70005 0xda1e7f00047e7000

def z572 : W := mkw 0x008b90b442af0550 0x4008b90b442af055 0xf1fff9fc47ff8fff 0xff1fff9fc47ff8ff

def z573 : W := mkw 0x29c94000270c0008 0x029c94000270c000 0x0180000006000000 0x0018000000600000

def z574 : W := mkw 0x1022b39140e32c42 0x21022b39140e32c4 0xa067f18041e70c05 0xda067f18041e70c0

def z575 : W := mkw 0x069d0c2e1a1cc134 0xc069d0c2e1a1cc13 0x4f98086c3e188338 0x24f98086c3e18833

def z576 : W := mkw 0x02000c0a8800d0a4 0x802000c0a8800d0a 0x0000060380007000 0x0000006038000700

def z577 : W := mkw 0x10abb3b5c0e33cc2 0x210abb3b5c0e33cc 0xf1ffffffc1e77cc7 0xff1ffffffc1e77cc

def z578 : W := mkw 0x6ffdffff278e0008 0x06ffdffff278e000 0x6fffffff87c70003 0xf6fffffff87c7000

def z579 : W := mkw 0x0000100000820000 0x0000010000082000 0x2061f00001c70000 0x82061f00001c7000

def z580 : W := mkw 0x2f565c0afdb2d0ac 0x82f565c0afdb2d0a 0x8e667603f9c07000 0x48e667603f9c0700

def z581 : W := mkw 0x1636af9bd871fce6 0xa1636af9bd871fce 0xde1e0f9ff838fcff 0x7de1e0f9ff838fcf

def z582 : W := mkw 0x0414000010100000 0x0041400001010000 0x0e18000038180008 0x20e1800003818000

def z583 : W := mkw 0x049f80b4523d0550 0x4049f80b4523d055 0xff9f89fc7e3f8fff 0xfff9f89fc7e3f8ff

def z584 : W := mkw 0x008980b400010440 0x0008980b40001044 0x719989fc00270cc7 0xb719989fc00270cc

def z585 : W := mkw 0x2fffdff47fffef5f 0x42fffdff47fffef5 0xfffffffc7fffffff 0xffffffffc7ffffff

def z586 : W := mkw 0x06160c0afd70faa7 0x806160c0afd70faa 0xfe1e0e1ffff8ffff 0x7fe1e0e1ffff8fff

def z587 : W := mkw 0x0b620f40ed60fa87 0x00b620f40ed60fa8 0xffe60ff3ffe0ffcf 0xfffe60ff3ffe0ffc

def z588 : W := mkw 0x0000002400000110 0x4000000240000011 0x4000086c00008330 0x04000086c0000833

def z589 : W := mkw 0x0960034000000000 0x0096003400000000 0x01e001e000000000 0x801e001e00000000

def z590 : W := mkw 0x2ddf500077be0008 0x02ddf500077be000 0x0f9ff0003e3f0009 0x20f9ff0003e3f000

def z591 : W := mkw 0x06160c0ad830d0a4 0x806160c0ad830d0a 0x501e0e1f8038f0f3 0x0501e0e1f8038f0f

def z592 : W := mkw 0x6fdd4c6e371c0008 0x06fdd4c6e371c000 0x4f98086c3e180008 0x24f98086c3e18000

def z593 : W := mkw 0x49e9e3f5020d0550 0x449e9e3f5020d055 0x71f9f9fc063f8fff 0xb71f9f9fc063f8ff

def z594 : W := mkw 0x00a983b4024d2d52 0x400a983b4024d2d5 0xf1f98ffc47ffffff 0xff1f98ffc47fffff

def z595 : W := mkw 0x0b600f402d40ea07 0x00b600f402d40ea0 0x71e00fe007c0ff02 0x871e00fe007c0ff0

def z596 : W := mkw 0x2ddd4000371c0008 0x02ddd4000371c000 0x2f9980003e3f000d 0xb2f9980003e3f000

def z597 : W := mkw 0x5ffdefff80413cc2 0x25ffdefff80413cc 0x5fffffff80007cc3 0xf5fffffff80007cc

def z598 : W := mkw 0x0000000000000000 0x0000000000000000 0x4018081c00000003 0x34018081c0000000

def z599 : W := mkw 0x249f500052be0008 0x0249f500052be000 0x219ff000063f000d 0xb219ff000063f000

def z600 : W := mkw 0x00220300c0603882 0x000220300c060388 0xb0660793c1e07cc7 0xdb0660793c1e07cc

def z601 : W := mkw 0x29cb500077be0008 0x029cb500077be000 0xa1e1f0007fff000c 0x8a1e1f0007fff000

def z602 : W := mkw 0x0f760f4ad830d0a4 0x80f760f4ad830d0a 0xdffe0ffff838f0ff 0xfdffe0ffff838f0f

def z603 : W := mkw 0x00028090c02114c0 0x000028090c02114c 0xb0078793c0277cc7 0xdb0078793c0277cc

def z604 : W := mkw 0x02000c0a00000000 0x002000c0a0000000 0x40000e1f80000002 0x040000e1f8000000

def z605 : W := mkw 0x10021000c0e33cc2 0x210021000c0e33cc 0xb0060613c1e77cc7 0x5b0060613c1e77cc

def z606 : W := mkw 0x1616bc9bd8b3d4e4 0xa1616bc9bd8b3d4e 0xde1ffe1ff83ff0ff 0x7de1ffe1ff83ff0f

def z607 : W := mkw 0x069f8cbeda3dd5f4 0xc069f8cbeda3dd5f 0xde1f8e1ff83ff0ff 0x7de1f8e1ff83ff0f

def z608 : W := mkw 0x1020a39100412c42 0x21020a39100412c4 0x0000018000000c00 0x00000018000000c0

def z609 : W := mkw 0x0f540c4a3d10c225 0x80f540c4a3d10c22 0x4f98086c3e188338 0x24f98086c3e18833

def z610 : W := mkw 0x06160c005830c004 0x006160c005830c00 0xde1e0e007838f00f 0x7de1e0e007838f00

def z611 : W := mkw 0x5ffdffff00c32c42 0x25ffdffff00c32c4 0x6fffffff81c70c03 0xf6fffffff81c70c0

def z612 : W := mkw 0x208b90b477bf0558 0x4208b90b477bf055 0xf19989fc7fff8fff 0xbf19989fc7fff8ff

def z613 : W := mkw 0x008b80b4da3dd5f4 0xc008b80b4da3dd5f 0xf19989fc7e3fffff 0xbf19989fc7e3ffff

def z614 : W := mkw 0x4fffffff40a20000 0x04fffffff40a2000 0xefffffffc1e70007 0xfefffffffc1e7000

def z615 : W := mkw 0x00898090020d0440 0x000898090020d044 0x31998190063f0ccf 0xb31998190063f0cc

def z616 : W := mkw 0x0020030000000000 0x0002003000000000 0x0060078000000002 0xd006007800000000

def z617 : W := mkw 0x1dfff391c0e33cc2 0x21dfff391c0e33cc 0xbffff793c1e77cc7 0xfbffff793c1e77cc

def z618 : W := mkw 0x4fdd4c6e00000000 0x04fdd4c6e0000000 0x4f9e0e7f80000003 0x74f9e0e7f8000000

def z619 : W := mkw 0x0b600f4025402a03 0x00b600f4025402a0 0x6fe00fe007c00f02 0xf6fe00fe007c00f0

def z620 : W := mkw 0x2dddc0b4371d0558 0x42dddc0b4371d055 0x7f9989fc3e3f8fff 0xb7f9989fc3e3f8ff

def z621 : W := mkw 0x2002100077bf0558 0x42002100077bf055 0xb00000007fff8ffc 0x0b00000007fff8ff

def z622 : W := mkw 0x0be98ff4020d0550 0x40be98ff4020d055 0x7ff98ffc063f8fff 0xf7ff98ffc063f8ff

def z623 : W := mkw 0x00000000020c0110 0x400000000020c011 0x0000000006188338 0x0000000000618833

def z624 : W := mkw 0x0022130040e22802 0x00022130040e2280 0xb067f78041e77c07 0xdb067f78041e77c0

def z625 : W := mkw 0x008980b4020d0550 0x4008980b4020d055 0x0001800000070000 0x0000180000007000

def z626 : W := mkw 0x1b623f41ede2fa87 0x21b623f41ede2fa8 0xffe67fe3ffc0ff0e 0xfffe67fe3ffc0ff0

def z627 : W := mkw 0x249f500ad2be10a8 0x8249f500ad2be10a 0x001ff01f803f00f1 0x0001ff01f803f00f

def z628 : W := mkw 0x02200f400840ea07 0x002200f400840ea0 0xf0600fe041c0ff06 0xdf0600fe041c0ff0

def z629 : W := mkw 0x1020330100c22802 0x21020330100c2280 0x0060700001c00000 0x00060700001c0000

def z630 : W := mkw 0x0089002400000000 0x0008900240000000 0x4198086c00000000 0x24198086c0000000

def z631 : W := mkw 0x069d8cbe020d0550 0x4069d8cbe020d055 0x7f9f8fff863f8fff 0xf7f9f8fff863f8ff

def z632 : W := mkw 0x008980b4020d0550 0x4008980b4020d055 0x5019881c003f80ff 0x35019881c003f80f

def z633 : W := mkw 0x0020030000402802 0x0002003000040280 0xf1e00fe047c0ff0e 0xff1e00fe047c0ff0

def z634 : W := mkw 0x10223301c0e23882 0x210223301c0e2388 0xb0667783c1c07c06 0xdb0667783c1c07c0

def z635 : W := mkw 0x2ddf500077be0008 0x02ddf500077be000 0x8ffe70007fd80008 0x68ffe70007fd8000

def z636 : W := mkw 0x0b608ff42d41ef57 0x40b608ff42d41ef5 0xffe00ffc7fc0fffe 0xfffe00ffc7fc0fff

def z637 : W := mkw 0x2416100077be0008 0x02416100077be000 0xae1e00007fff000d 0x7ae1e00007fff000

def z638 : W := mkw 0x4b60afff2d40ea07 0x04b60afff2d40ea0 0xffe00fffffc0ff0e 0xfffe00fffffc0ff0

def z639 : W := mkw 0x1022b391c0a314c0 0x21022b391c0a314c 0x0067f793802700c3 0xd0067f793802700c

def z640 : W := mkw 0x0b400c402d00c205 0x00b400c402d00c20 0xdf800e607e00f30e 0x7df800e607e00f30

def z641 : W := mkw 0x349ff091d2bf14c8 0x2349ff091d2bf14c 0x001ff013803f00c1 0x0001ff013803f00c

def z642 : W := mkw 0x7ffffffff7ff3cca 0x27ffffffff7ff3cc 0xffffffffffff7ccf 0xfffffffffffff7cc

def z643 : W := mkw 0x6f767f4b75b20008 0x06f767f4b75b2000 0x8e667603f9c00000 0x48e667603f9c0000

def z644 : W := mkw 0x02208ff40841ef57 0x402208ff40841ef5 0x50000ffc0000fff2 0x050000ffc0000fff

def z645 : W := mkw 0x0000809000010440 0x0000080900001044 0x00018010002700c1 0x000018010002700c

def z646 : W := mkw 0x6fffffff52be0008 0x06fffffff52be000 0x4fffffff803f0003 0xf4fffffff803f000

def z647 : W := mkw 0x10023001c0a21080 0x210023001c0a2108 0x0006700380000000 0x0000670038000000

def z648 : W := mkw 0x00000000020c0000 0x000000000020c000 0x20000000063f000c 0x020000000063f000

def z649 : W := mkw 0x2ddd4000371c0008 0x02ddd4000371c000 0xaff800007fd8000c 0xfaff800007fd8000

def z650 : W := mkw 0x008980b4020d0550 0x4008980b4020d055 0x419989fc003f00f3 0xb419989fc003f00f

def z651 : W := mkw 0x00890000020c0000 0x000890000020c000 0x2181800006070000 0x8218180000607000

def z652 : W := mkw 0x069d8cbe1a1dc574 0xc069d8cbe1a1dc57 0x7f9989fc3e3f8fff 0xb7f9989fc3e3f8ff

def z653 : W := mkw 0x2d56500077be0008 0x02d56500077be000 0xae6670007fff000c 0x4ae6670007fff000

def z654 : W := mkw 0x06160c0ad830d0a4 0x806160c0ad830d0a 0xce1e0e1ff8007003 0x7ce1e0e1ff800700

def z655 : W := mkw 0x1022a391c0613cc2 0x21022a391c0613cc 0x90060793c0207cc7 0x590060793c0207cc

def z656 : W := mkw 0x2dff530077fe280a 0x02dff530077fe280 0xbffff7807fff7c0f 0xfbffff7807fff7c0

def z657 : W := mkw 0x0f760f4afd70faa7 0x80f760f4afd70faa 0xffe60fe3ffc0ff0e 0xfffe60fe3ffc0ff0

def z658 : W := mkw 0x16363f0bd8f2f8a6 0xa16363f0bd8f2f8a 0x8e667603f9c07000 0x48e667603f9c0700

def z659 : W := mkw 0x2ddf4000773c0008 0x02ddf4000773c000 0x8f9e00007e38000d 0x78f9e00007e38000

def z660 : W := mkw 0x00890000020c0000 0x000890000020c000 0x7199881c063f80ff 0xb7199881c063f80f

def z661 : W := mkw 0x42000c6e00000000 0x042000c6e0000000 0x4000086c00000000 0x04000086c0000000

def z662 : W := mkw 0x000000002f4def57 0x4000000002f4def5 0xb00000007ffffffc 0x0b00000007ffffff

def z663 : W := mkw 0x2ddfd09077bf0448 0x02ddfd09077bf044 0xbffff1907fff0ccf 0xfbffff1907fff0cc

def z664 : W := mkw 0x0f560c4afd30d2a5 0x80f560c4afd30d2a 0xdf9e0e7ffe38f3ff 0x7df9e0e7ffe38f3f

def z665 : W := mkw 0x000080b400010550 0x4000080b40001055 0x700189fc00278ff7 0x9700189fc00278ff

def z666 : W := mkw 0x2fdf4c0aff3cd0ac 0x82fdf4c0aff3cd0a 0xdf9e0e1ffe38f0ff 0x7df9e0e1ffe38f0f

def z667 : W := mkw 0x00020000c0201080 0x000020000c020108 0x80060603c0007000 0x480060603c000700

def z668 : W := mkw 0x0f740f4a00000000 0x00f740f4a0000000 0x4ffe0fff80000003 0xf4ffe0fff8000000

def z669 : W := mkw 0x008980b4020d0550 0x4008980b4020d055 0x501989fc003f8ff3 0x0501989fc003f8ff

def z670 : W := mkw 0x0b400c402d00c205 0x00b400c402d00c20 0xefe008607fc0830c 0xfefe008607fc0830

def z671 : W := mkw 0x2f565c0afdb2d0ac 0x82f565c0afdb2d0a 0xde7e7e1ff9f8f0ff 0x7de7e7e1ff9f8f0f

def z672 : W := mkw 0x00020000c0201080 0x000020000c020108 0xd01e0e1fc038f0ff 0x7d01e0e1fc038f0f

def z673 : W := mkw 0x249fd0b452bf0558 0x4249fd0b452bf055 0x001ff01c003f00f1 0x0001ff01c003f00f

def z674 : W := mkw 0x1022b391c2ef3dd2 0x61022b391c2ef3dd 0xb067f793c7ffffff 0xdb067f793c7fffff

def z675 : W := mkw 0x0f740f4a2d40ea07 0x00f740f4a2d40ea0 0xfffe0fffffc0ff0f 0xffffe0fffffc0ff0

def z676 : W := mkw 0x0000000000000000 0x0000000000000000 0x218000000600000c 0xb218000000600000

def z677 : W := mkw 0x1b62bfd1ede3fec7 0x21b62bfd1ede3fec 0xbe67f793f9e77cc7 0xdbe67f793f9e77cc

def z678 : W := mkw 0x3dfff39177ff2c4a 0x23dfff39177ff2c4 0xaffff1807fff0c0d 0xfaffff1807fff0c0

def z679 : W := mkw 0x4ffdefff8800d0a4 0x84ffdefff8800d0a 0x5fffffff8000f0f3 0xf5fffffff8000f0f

def z680 : W := mkw 0x39ebf391e7ef3cca 0x239ebf391e7ef3cc 0xb1e7f793c7e77cc7 0xdb1e7f793c7e77cc

def z681 : W := mkw 0x02008cbe8801d5f4 0xc02008cbe8801d5f 0x50000fff8000fff2 0x050000fff8000fff

def z682 : W := mkw 0x09e983f4274d2f53 0x409e983f4274d2f5 0x21e181e007c70f00 0x821e181e007c70f0

def z683 : W := mkw 0x00890000020c0000 0x000890000020c000 0x0198000006180008 0x2019800000618000

def z684 : W := mkw 0x00020000fd70faa7 0x800020000fd70faa 0xb00000007ff8fffc 0x0b00000007ff8fff

def z685 : W := mkw 0x000080b400010550 0x4000080b40001055 0x000001e000000f00 0x0000001e000000f0

def z686 : W := mkw 0x008980b4020d0550 0x4008980b4020d055 0x718189fc06078ff2 0x8718189fc06078ff

def z687 : W := mkw 0x008980b4020d0550 0x4008980b4020d055 0x2199801c063f00fd 0xb2199801c063f00f

def z688 : W := mkw 0x0b600f4025000000 0x00b600f402500000 0xefe00fe07fc0000e 0xfefe00fe07fc0000

def z689 : W := mkw 0x3fffff9bfffffcee 0xa3fffff9bfffffce 0xffffff9ffffffcff 0xfffffff9ffffffcf

def z690 : W := mkw 0x000080b400010550 0x4000080b40001055 0x501809fc00388fff 0x3501809fc00388ff

def z691 : W := mkw 0x2fdf5c0a77be0008 0x02fdf5c0a77be000 0xeffffe1fffff000f 0xfeffffe1fffff000

def z692 : W := mkw 0x0000000000000000 0x0000000000000000 0x3000000006008f0c 0x03000000006008f0

def z693 : W := mkw 0x1002b091c0a314c0 0x21002b091c0a314c 0x3007f19380270cc7 0x93007f19380270cc

def z694 : W := mkw 0x1022b391c0e33cc2 0x21022b391c0e33cc 0x2067f19381e70cc1 0x82067f19381e70cc

def z695 : W := mkw 0x10a9b3b502cf2d52 0x610a9b3b502cf2d5 0x71f9f9fc07ff8fff 0xb71f9f9fc07ff8ff

def z696 : W := mkw 0x4dfde3f500000000 0x04dfde3f50000000 0x0ffff1e000000001 0xf0ffff1e00000000

def z697 : W := mkw 0x00890024020c0110 0x400890024020c011 0x719809ec06188f3e 0xb719809ec06188f3

def z698 : W := mkw 0x0000000a800010a0 0x80000000a800010a 0x0000001f800000f0 0x00000001f800000f

def z699 : W := mkw 0x49c9406400000000 0x049c940640000000 0x0180006000000000 0x0018000600000000

def z700 : W := mkw 0x0b600f4aad40faa7 0x80b600f4aad40faa 0xffe00fffffc0fffe 0xfffe00fffffc0fff

def z701 : W := mkw 0x2fff5f4077be0008 0x02fff5f4077be000 0xefffffe07fff000f 0xfefffffe07fff000

def z702 : W := mkw 0x02020c0ac820d0a4 0x802020c0ac820d0a 0xd0060e1fc020f0f7 0x5d0060e1fc020f0f

def z703 : W := mkw 0x4be9eff500000000 0x04be9eff50000000 0x4fe1ffe000000002 0xf4fe1ffe00000000

def z704 : W := mkw 0x20000000371c0008 0x020000000371c000 0x000000003e180008 0x0000000003e18000

def z705 : W := mkw 0x0416000050300000 0x0041600005030000 0xde1e081c783880ff 0x7de1e081c783880f

def z706 : W := mkw 0x008980b4020d0550 0x4008980b4020d055 0x3019801c063f8ffd 0x03019801c063f8ff

def z707 : W := mkw 0x46bdefff00000000 0x046bdefff0000000 0x407fffff80000003 0xd407fffff8000000

def z708 : W := mkw 0x0b600f402d40ea07 0x00b600f402d40ea0 0xdfe00fe07fc0ff0a 0x6dfe00fe07fc0ff0

def z709 : W := mkw 0x0be9aff52d40ea07 0x00be9aff52d40ea0 0xffffffffffc0ff0f 0xfffffffffffc0ff0

def z710 : W := mkw 0x1022b3b5c0e33dd2 0x61022b3b5c0e33dd 0xf07fffffc1ffffff 0xff07fffffc1fffff

def z711 : W := mkw 0x49e9e3f500000000 0x049e9e3f50000000 0x01e7f1f380000001 0x801e7f1f38000000

def z712 : W := mkw 0x10021000c0e33cc2 0x210021000c0e33cc 0xf018081c41fffcff 0x3f018081c41fffcf

def z713 : W := mkw 0x4ffdefff020d0550 0x44ffdefff020d055 0x6fffffff863f0ff3 0xf6fffffff863f0ff

def z714 : W := mkw 0x06160c0ad830d0a4 0x806160c0ad830d0a 0xde180e1ff838f0fe 0x2de180e1ff838f0f

def z715 : W := mkw 0x1022b391c0e33cc2 0x21022b391c0e33cc 0xb067f783c1e77cc4 0xcb067f783c1e77cc

def z716 : W := mkw 0x4fdd6c6f00000000 0x04fdd6c6f0000000 0x4f9e786f80000000 0x24f9e786f8000000

def z717 : W := mkw 0x10ab3325c2ee3992 0x610ab3325c2ee399 0xc1fe7e6fc7d8f338 0x6c1fe7e6fc7d8f33

def z718 : W := mkw 0x10021000c0e33cc2 0x210021000c0e33cc 0x2000000001e70cc0 0x02000000001e70cc

def z719 : W := mkw 0x29c95000278e0008 0x029c95000278e000 0x2fe1f0003fc70008 0xa2fe1f0003fc7000

def z720 : W := mkw 0x1022b391c0e33cc2 0x21022b391c0e33cc 0xf067ff9fc1e7fcf7 0xdf067ff9fc1e7fcf

def z721 : W := mkw 0x4ffdefff00000000 0x04ffdefff0000000 0x4e7ffe1f80000003 0x74e7ffe1f8000000

def z722 : W := mkw 0x0020a39100000000 0x00020a3910000000 0x0067f61380000001 0x40067f6138000000

def z723 : W := mkw 0x449de0bf00000000 0x0449de0bf0000000 0x019ff1ff80000001 0x8019ff1ff8000000

def z724 : W := mkw 0x469decbf00000000 0x0469decbf0000000 0x0e1ff61f80000001 0x40e1ff61f8000000

def z725 : W := mkw 0x2ddf500077be0008 0x02ddf500077be000 0xfffff9fc7fff8fff 0xffffff9fc7fff8ff

def z726 : W := mkw 0x4ffd6f4b00000000 0x04ffd6f4b0000000 0x4fffffe380000003 0xf4fffffe38000000

def z727 : W := mkw 0x0ffdefd12d40ea07 0x00ffdefd12d40ea0 0xfffffff3ffc0ff0f 0xffffffff3ffc0ff0

def z728 : W := mkw 0x4fddecff020d0550 0x44fddecff020d055 0x4f9ff87f863f83f9 0x24f9ff87f863f83f

def z729 : W := mkw 0x5fdf5c6ec0e33cc2 0x25fdf5c6ec0e33cc 0xff98086c41e77cc4 0x2ff98086c41e77cc

def z730 : W := mkw 0x6ffdefff270c0008 0x06ffdefff270c000 0x4fffffff86000003 0xf4fffffff8600000

def z731 : W := mkw 0x4f746f4b00000000 0x04f746f4b0000000 0x4e7e7e0f80000000 0x64e7e7e0f8000000

def z732 : W := mkw 0x108b90b4efefffd7 0x6108b90b4efefffd 0xf19989fc7fffffff 0xbf19989fc7ffffff

def z733 : W := mkw 0x4ddde0bf00000000 0x04ddde0bf0000000 0x0f9ff01f80000001 0x20f9ff01f8000000

def z734 : W := mkw 0x2d56d0b475b30558 0x42d56d0b475b3055 0xde6679fc79c08ff2 0x4de6679fc79c08ff

def z735 : W := mkw 0x10021000c0a314c0 0x210021000c0a314c 0xa000000041e700c4 0x0a000000041e700c

def z736 : W := mkw 0x4ffd6f6f00000000 0x04ffd6f6f0000000 0x0e7e760f80000000 0x40e7e760f8000000

def z737 : W := mkw 0x0089a0b5020d0550 0x40089a0b5020d055 0x719ff9ff863f8fff 0xb719ff9ff863f8ff

def z738 : W := mkw 0x2ddf500077be0008 0x02ddf500077be000 0xeffff8607fff830d 0xfeffff8607fff830

def z739 : W := mkw 0x10021000c0a21080 0x210021000c0a2108 0x0000000000000000 0x0000000000000000

def z740 : W := mkw 0x10021000c0e33dd2 0x610021000c0e33dd 0xb000000041e7fff4 0x0b000000041e7fff

def z741 : W := mkw 0x2f765f4afdf2faaf 0x82f765f4afdf2faa 0x8e667603f9c07000 0x48e667603f9c0700

def z742 : W := mkw 0x2ddf502477be0118 0x42ddf502477be011 0xfffff87c7fff83ff 0xffffff87c7fff83f

def z743 : W := mkw 0x06160c0ad830d0a4 0x806160c0ad830d0a 0x5e1e0e1fb838f0fb 0x25e1e0e1fb838f0f

def z744 : W := mkw 0x0960a39125000000 0x00960a3912500000 0xafe7f793ffc0000f 0xfafe7f793ffc0000

def z745 : W := mkw 0x0020230100000000 0x0002023010000000 0x0067f60380000001 0xd0067f6038000000

def z746 : W := mkw 0x1022b391c0e23882 0x21022b391c0e2388 0xa067f793c1e77007 0xda067f793c1e7700

def z747 : W := mkw 0x449de0bf00000000 0x0449de0bf0000000 0x401ff81f80000003 0x3401ff81f8000000

def z748 : W := mkw 0x10221300c0e23882 0x210221300c0e2388 0xb060078041c07c06 0xdb060078041c07c0

def z749 : W := mkw 0x0ddf500065a20000 0x00ddf500065a2000 0xaffff0007fe7000d 0xfaffff0007fe7000

def z750 : W := mkw 0x02200f000840e806 0x002200f000840e80 0xffe00fe07fc0ff0e 0xfffe00fe07fc0ff0

def z751 : W := mkw 0x00021000c0a21080 0x000021000c0a2108 0xa067f603c1e77005 0xda067f603c1e7700

def z752 : W := mkw 0x4ffdefff0841ef57 0x44ffdefff0841ef5 0x5fffffff8000fff3 0xf5fffffff8000fff

def z753 : W := mkw 0x108b90b4c2ef3dd2 0x6108b90b4c2ef3dd 0xb019801c41ff7cf5 0x0b019801c41ff7cf

def z754 : W := mkw 0x0f74afdb00000000 0x00f74afdb0000000 0x4fffffff80000003 0xf4fffffff8000000

def z755 : W := mkw 0x4ffdefff2d00c205 0x04ffdefff2d00c20 0xdffffffffe00f30f 0xfdffffffffe00f30

def z756 : W := mkw 0x4f74efff00000000 0x04f74efff0000000 0x0e6677e380000000 0x40e6677e38000000

def z757 : W := mkw 0x4fddecff00000000 0x04fddecff0000000 0x4ffff87f80000001 0xf4ffff87f8000000

def z758 : W := mkw 0x10021000c0a314c0 0x210021000c0a314c 0x3000000000270cc4 0x03000000000270cc

def z759 : W := mkw 0x10021000fdf3fee7 0xa10021000fdf3fee 0xb00000007ffffffc 0x0b00000007ffffff

def z760 : W := mkw 0x0220af9100000000 0x00220af910000000 0x4e67ff9380000003 0xf4e67ff938000000

def z761 : W := mkw 0x2ddd5000379e0008 0x02ddd5000379e000 0x2ffff0003fdf0009 0xf2ffff0003fdf000

def z762 : W := mkw 0x1634bf9b18d3ec66 0xa1634bf9b18d3ec6 0x6e79f98c39df8c38 0xa6e79f98c39df8c3

def z763 : W := mkw 0x06140c0a9810d0a4 0x806140c0a9810d0a 0x5e1e0e1fb818f0fb 0x75e1e0e1fb818f0f

def z764 : W := mkw 0x4ffdefff2d40ea07 0x04ffdefff2d40ea0 0x5fffffffbe00ff0b 0xf5fffffffbe00ff0

def z765 : W := mkw 0x0b602f412d40ea07 0x00b602f412d40ea0 0xffe67fe3ffc0ff0e 0xfffe67fe3ffc0ff0

def z766 : W := mkw 0x6ddf506477be0008 0x06ddf506477be000 0xaffff0607fff000d 0xfaffff0607fff000

def z767 : W := mkw 0x1022b391c0e33cc2 0x21022b391c0e33cc 0xb1e7f793c7e77ccf 0xfb1e7f793c7e77cc

def z768 : W := mkw 0x1022b391c0e33cc2 0x21022b391c0e33cc 0xb067f613c1e77cc5 0x4b067f613c1e77cc

def z769 : W := mkw 0x4ffdefff10100000 0x04ffdefff1010000 0x4fffffffb818000b 0xf4fffffffb818000

def z770 : W := mkw 0x2bc95c0aaf8ed0ac 0x82bc95c0aaf8ed0a 0x71e1fe1f87c7f0f2 0x871e1fe1f87c7f0f

def z771 : W := mkw 0x4ffdefff020d0550 0x44ffdefff020d055 0x5fffffff803f8ff3 0xf5fffffff803f8ff

def z772 : W := mkw 0x4ffdefff020d0550 0x44ffdefff020d055 0x5fffffff803f80ff 0xf5fffffff803f80f

def z773 : W := mkw 0x4fddecff020d0550 0x44fddecff020d055 0x7f9ff9ff863f8fff 0xb7f9ff9ff863f8ff

def z774 : W := mkw 0x00021000d8b2d0a4 0x800021000d8b2d0a 0xb000000079fff0fc 0x0b000000079fff0f

def z775 : W := mkw 0x4ffdefff00000000 0x04ffdefff0000000 0x0ffff7e380000001 0xf0ffff7e38000000

def z776 : W := mkw 0x0020230100402802 0x0002023010040280 0xb0667783c1c07c06 0xdb0667783c1c07c0

def z777 : W := mkw 0x0ddd400a00000000 0x00ddd400a0000000 0x0ffff01f80000001 0xf0ffff01f8000000

def z778 : W := mkw 0x069d4c0a00000000 0x0069d4c0a0000000 0x4e1ffe1f80000003 0x74e1ffe1f8000000

def z779 : W := mkw 0x0be98ff42f4def57 0x40be98ff42f4def5 0x8e79861c79ff70f1 0x48e79861c79ff70f

def z780 : W := mkw 0x10221300c0e23882 0x210221300c0e2388 0x8060060041c07000 0x48060060041c0700

def z781 : W := mkw 0x26bf5f405afeea0f 0x026bf5f405afeea0 0x501fffe0003fff03 0x0501fffe0003fff0

def z782 : W := mkw 0x4ffdefff00010440 0x04ffdefff0001044 0x5fffffff80000cc3 0xf5fffffff80000cc

def z783 : W := mkw 0x12221f40c8e3fec7 0x212221f40c8e3fec 0xf0000fe041e7ffc6 0x0f0000fe041e7ffc

def z784 : W := mkw 0x10221300c0e33cc2 0x210221300c0e33cc 0xb060060041e77cc4 0x4b060060041e77cc

def z785 : W := mkw 0x10221300c0e33cc2 0x210221300c0e33cc 0xb060018041e77cc4 0x8b060018041e77cc

def z786 : W := mkw 0x6ffdefff3f5cea0f 0x06ffdefff3f5cea0 0xffffffffffd8ff0f 0xfffffffffffd8ff0

def z787 : W := mkw 0x10ab93b4c2ef3dd2 0x610ab93b4c2ef3dd 0xf1f98ffc47ffffff 0xff1f98ffc47fffff

def z788 : W := mkw 0x108b1024c2ef3dd2 0x6108b1024c2ef3dd 0xf198086c47fffffc 0x2f198086c47fffff

def z789 : W := mkw 0x2ddf5000f7be1088 0x02ddf5000f7be108 0xbffff0007fff70cd 0xfbffff0007fff70c

def z790 : W := mkw 0x4f746f4b00402802 0x04f746f4b0040280 0x8e667603c1c07000 0x48e667603c1c0700

def z791 : W := mkw 0x6222bfff77be0008 0x06222bfff77be000 0xe0000fffffff000e 0x0e0000fffffff000

def z792 : W := mkw 0x1220afd18841fec7 0x21220afd18841fec 0x1000079380007cc2 0x01000079380007cc

def z793 : W := mkw 0x449de0bf00000000 0x0449de0bf0000000 0x419ff87f80000001 0x2419ff87f8000000

def z794 : W := mkw 0x2d56500077be0008 0x02d56500077be000 0xae67f0007fff000d 0xdae67f0007fff000

def z795 : W := mkw 0x4ffdefff3d10c225 0x84ffdefff3d10c22 0x4fffffffbe18833b 0xf4fffffffbe18833

def z796 : W := mkw 0x4ffdefff020c0110 0x44ffdefff020c011 0x5fffffff863883ff 0xf5fffffff863883f

def z797 : W := mkw 0x4f746f4b25000000 0x04f746f4b2500000 0x8e667603f9c00000 0x48e667603f9c0000

def z798 : W := mkw 0x06160c0ad830d0a4 0x806160c0ad830d0a 0xce1e0e1ff838f0f9 0x6ce1e0e1ff838f0f

def z799 : W := mkw 0x4ffdefff00000000 0x04ffdefff0000000 0x6fffffff8600000f 0xf6fffffff8600000

def z800 : W := mkw 0x0020a39100000000 0x00020a3910000000 0x1067f793802000c7 0xd1067f793802000c

def z801 : W := mkw 0x4fdd4c6e00000000 0x04fdd4c6e0000000 0x4ffffe7f80000003 0xf4ffffe7f8000000

def z802 : W := mkw 0x0020a3912d40ea07 0x00020a3912d40ea0 0xb067f793ffc0ff0f 0xdb067f793ffc0ff0

def z803 : W := mkw 0x0b602f412d40ea07 0x00b602f412d40ea0 0x8e667603f9c07000 0x48e667603f9c0700

def z804 : W := mkw 0x4f746f4b020d0550 0x44f746f4b020d055 0x3e667603863f8ffc 0x43e667603863f8ff

def z805 : W := mkw 0x0b600f4a2d40ea27 0x80b600f4a2d40ea2 0xffe00fec7fc0ff3e 0xfffe00fec7fc0ff3

def z806 : W := mkw 0x4f74efdb00000000 0x04f74efdb0000000 0x0e66779380000002 0x40e6677938000000

def z807 : W := mkw 0x00a9a3b5020d0550 0x400a9a3b5020d055 0x21e7f7f386070f03 0xd21e7f7f386070f0

def z808 : W := mkw 0x4f74efdb00000000 0x04f74efdb0000000 0x0e67f78380000000 0xc0e67f7838000000

def z809 : W := mkw 0x008980b4020d0550 0x4008980b4020d055 0xff9989fc7e3f8fff 0xfff9989fc7e3f8ff

def z810 : W := mkw 0x44bde3bf00000000 0x044bde3bf0000000 0x007ff61f80000001 0x4007ff61f8000000

def z811 : W := mkw 0x0ffdef9b00000000 0x00ffdef9b0000000 0x4fffff9f80000003 0xf4fffff9f8000000

def z812 : W := mkw 0x0b600f4a2d40ea07 0x00b600f4a2d40ea0 0xffe00fffffc0ff0e 0xfffe00fffffc0ff0

def z813 : W := mkw 0x1022b391c0e33cc2 0x21022b391c0e33cc 0xb1e7f7f3c7e77fc7 0xdb1e7f7f3c7e77fc

def z814 : W := mkw 0x10223301c0e23882 0x210223301c0e2388 0xb067f783c1e77c07 0xdb067f783c1e77c0

def z815 : W := mkw 0x4ffdefff00000000 0x04ffdefff0000000 0xdfffffffc0007007 0xfdfffffffc000700

def z816 : W := mkw 0x1020b39100c32c42 0x21020b39100c32c4 0xb067f793c1c77c07 0xdb067f793c1c77c0

def z817 : W := mkw 0x4ffdefff00000000 0x04ffdefff0000000 0x4fe7ffff80000002 0xc4fe7ffff8000000

def z818 : W := mkw 0x4220afff00010550 0x44220afff0001055 0x7067ffff80278ff7 0xd7067ffff80278ff

def z819 : W := mkw 0x0020a39100000000 0x00020a3910000000 0x0007f79380000003 0x00007f7938000000

def z820 : W := mkw 0x4ffdefff00000000 0x04ffdefff0000000 0x4e7fffff80000003 0x44e7fffff8000000

def z821 : W := mkw 0x2ddd5000379e0008 0x02ddd5000379e000 0xaff9f0007fdf000c 0xfaff9f0007fdf000

def z822 : W := mkw 0x0020a39100000000 0x00020a3910000000 0x0067f78380000000 0xc0067f7838000000

def z823 : W := mkw 0x2ddf500075b20008 0x02ddf500075b2000 0xaffff00079e70005 0xfaffff00079e7000

def z824 : W := mkw 0x4ffdefff00402802 0x04ffdefff0040280 0x5fffffff80007c03 0xf5fffffff80007c0

def z825 : W := mkw 0x0960034025402a03 0x00960034025402a0 0xbfe007e07fc07f0e 0xfbfe007e07fc07f0

def z826 : W := mkw 0x4ffdefdb00000000 0x04ffdefdb0000000 0x0ffff79380000003 0xf0ffff7938000000

def z827 : W := mkw 0x4020a3f500000000 0x04020a3f50000000 0x0067f7f380000003 0xd0067f7f38000000

def z828 : W := mkw 0x2ddf500a77be0008 0x02ddf500a77be000 0xaffff01fffff000d 0xfaffff01fffff000

def z829 : W := mkw 0x2ddf500077be0008 0x02ddf500077be000 0x8ffff0007fff0009 0x68ffff0007fff000

def z830 : W := mkw 0x1022b391c0e33cc2 0x21022b391c0e33cc 0xb067f783c1c77c06 0xdb067f783c1c77c0

def z831 : W := mkw 0x149fb0bfd2bf15f0 0xe149fb0bfd2bf15f 0x001ff01f803f00f1 0x0001ff01f803f00f

def z832 : W := mkw 0x10021000c0e23882 0x210021000c0e2388 0xa000000041e77004 0x0a000000041e7700

def z833 : W := mkw 0x4f746f4b00402802 0x04f746f4b0040280 0xbe667783c1c07c06 0xdbe667783c1c07c0

def z834 : W := mkw 0x449de0bf2d40ea07 0x0449de0bf2d40ea0 0xb01ff01fffc0ff0d 0x0b01ff01fffc0ff0

def z835 : W := mkw 0x4ffdefff2d00c205 0x04ffdefff2d00c20 0xefffffffffc0830f 0xfefffffffffc0830

def z836 : W := mkw 0x4f74efff2d40ea07 0x04f74efff2d40ea0 0xde667ffff9c0ff02 0x4de667ffff9c0ff0

def z837 : W := mkw 0x449de0bf00000000 0x0449de0bf0000000 0x401ff9ff80000003 0x0401ff9ff8000000

def z838 : W := mkw 0x4ffdefff00000000 0x04ffdefff0000000 0x5fffffff800080f3 0xf5fffffff800080f

def z839 : W := mkw 0x4f746f4b0800c004 0x04f746f4b0800c00 0x8e667603f8007000 0x48e667603f800700

def z840 : W := mkw 0x4f746f4b25402a03 0x04f746f4b25402a0 0x0e66760381c00000 0x40e66760381c0000

def z841 : W := mkw 0x4ffdefff2d40ea07 0x04ffdefff2d40ea0 0x6fffffffbfc08f0b 0xf6fffffffbfc08f0

def z842 : W := mkw 0x20021000f7be1088 0x020021000f7be108 0xb00000007fff70cc 0x0b00000007fff70c

def z843 : W := mkw 0x10223301c0e23882 0x210223301c0e2388 0x8067f603c1e77001 0x48067f603c1e7700

def z844 : W := mkw 0x2ddf500077be0008 0x02ddf500077be000 0xaffff0007fff0001 0xcaffff0007fff000

def z845 : W := mkw 0x2ddf5000f7be1088 0x02ddf5000f7be108 0xaffff603ffff700d 0xfaffff603ffff700

def z846 : W := mkw 0x0dfde391020d0440 0x00dfde391020d044 0x3ffff793863f0ccf 0xf3ffff793863f0cc

def z847 : W := mkw 0x4ffdefff0840ea07 0x04ffdefff0840ea0 0xffffffffc1c0ff07 0xfffffffffc1c0ff0

def z848 : W := mkw 0x4be9eff500000000 0x04be9eff50000000 0x4fe7fff380000003 0xf4fe7fff38000000

def z849 : W := mkw 0x10021000c0e33cc2 0x210021000c0e33cc 0xa000000041c77c00 0x0a000000041c77c0

def z850 : W := mkw 0x4ffdefff020d0550 0x44ffdefff020d055 0x6fffffff863f0f0f 0xf6fffffff863f0f0

def z851 : W := mkw 0x39621300f7ff3cca 0x239621300f7ff3cc 0xbfe007807fff7cce 0xfbfe007807fff7cc

def z852 : W := mkw 0x0000a09100000000 0x00000a0910000000 0x0007f19380000003 0x90007f1938000000

def z853 : W := mkw 0x4dfde3ff020d0550 0x44dfde3ff020d055 0x71fff9ff863f8fff 0xb71fff9ff863f8ff

def z854 : W := mkw 0x2ddf500077be0008 0x02ddf500077be000 0xaffff0007fdf0008 0xeaffff0007fdf000

def z855 : W := mkw 0x0000a09100010440 0x00000a0910001044 0x0007f013802700c1 0x00007f013802700c

def z856 : W := mkw 0x02000c002d40ea07 0x002000c002d40ea0 0xff800fe07fc0ff0e 0xfff800fe07fc0ff0

def z857 : W := mkw 0x20021000fffefaaf 0x820021000fffefaa 0xb00000007ffffffc 0x0b00000007ffffff

def z858 : W := mkw 0x0434a39b00000000 0x00434a39b0000000 0x007ff79f80000003 0xd007ff79f8000000

def z859 : W := mkw 0x1022b391c0e33cc2 0x21022b391c0e33cc 0xf07fff9fc1e77cc7 0xff07fff9fc1e77cc

def z860 : W := mkw 0x469decbf00000000 0x0469decbf0000000 0x4f9fffff80000003 0xf4f9fffff8000000

def z861 : W := mkw 0x4ffdefff10100020 0x84ffdefff1010002 0x4fffffff80180033 0xf4fffffff8018003

def z862 : W := mkw 0x4ffdefff2d40ea07 0x04ffdefff2d40ea0 0xdffffffff9c0ff03 0xfdffffffff9c0ff0

def z863 : W := mkw 0x208b1000ffbed0ac 0x8208b1000ffbed0a 0xf199881c7ffff0ff 0xbf199881c7ffff0f

def z864 : W := mkw 0x1b621f40c0e33cc2 0x21b621f40c0e33cc 0xffe00fe041e77cc6 0xfffe00fe041e77cc

def z865 : W := mkw 0x4ffdefff2d40ea07 0x04ffdefff2d40ea0 0xdffffffff9c0f00f 0xfdffffffff9c0f00

def z866 : W := mkw 0x4ffdefff00010550 0x44ffdefff0001055 0x5fffffff80388fff 0xf5fffffff80388ff

def z867 : W := mkw 0x0089a0b500000000 0x00089a0b50000000 0x001ff01f80000001 0x0001ff01f8000000

def z868 : W := mkw 0x449de0bf020d0550 0x4449de0bf020d055 0x301ff01f863f8ffd 0x0301ff01f863f8ff

def z869 : W := mkw 0x1022b391c0e33cc2 0x21022b391c0e33cc 0x8067f603c1c77000 0x48067f603c1c7700

def z870 : W := mkw 0x4089e0b500000000 0x04089e0b50000000 0x0007f01380000001 0x00007f0138000000

def z871 : W := mkw 0x4ffdefff1810c024 0x84ffdefff1810c02 0x4fffffffb8000003 0xf4fffffffb800000

def z872 : W := mkw 0x06160c0ad830d0a4 0x806160c0ad830d0a 0xfe7e0e1ff9f8f0ff 0xffe7e0e1ff9f8f0f

def z873 : W := mkw 0x4ffd6f6f00000000 0x04ffd6f6f0000000 0x4ffe7fef80000002 0xf4ffe7fef8000000

def z874 : W := mkw 0x10021000e5e33cc2 0x210021000e5e33cc 0xb00000007fe77ccc 0x0b00000007fe77cc

def z875 : W := mkw 0x3dfde391b75d3cca 0x23dfde391b75d3cc 0x1f980793be187cca 0x21f980793be187cc

def z876 : W := mkw 0x0d74630100000000 0x00d7463010000000 0x0e66760380000000 0x40e6676038000000

def z877 : W := mkw 0x10021000c0e33cc2 0x210021000c0e33cc 0xb060000041e77cc4 0xdb060000041e77cc

def z878 : W := mkw 0x0b600f402d40ea07 0x00b600f402d40ea0 0xbfe007e07fc07f06 0xdbfe007e07fc07f0

def z879 : W := mkw 0x10021000c0e33cc2 0x210021000c0e33cc 0xb000000047e7ffcc 0x0b000000047e7ffc

def z880 : W := mkw 0x449de0bf10100020 0x8449de0bf1010002 0x001ff01f80180031 0x0001ff01f8018003

def z881 : W := mkw 0x4dfde3ff00000000 0x04dfde3ff0000000 0x01e7f1e380000000 0x801e7f1e38000000

def z882 : W := mkw 0x4ffdefff00000000 0x04ffdefff0000000 0x0e67f60380000000 0x40e67f6038000000

def z883 : W := mkw 0x0020a3b500000000 0x00020a3b50000000 0x4067ffff80000003 0xd4067ffff8000000

def z884 : W := mkw 0x0d76034af5703aa3 0x80d76034af5703aa 0x21fe01ff87f80ff1 0x821fe01ff87f80ff

def z885 : W := mkw 0x1022b391c0e33cc2 0x21022b391c0e33cc 0x9067f613c1e770c7 0x59067f613c1e770c

def z886 : W := mkw 0x4dfde3bf00000000 0x04dfde3bf0000000 0x0ffff79f80000003 0xf0ffff79f8000000

def z887 : W := mkw 0x449d602f00000000 0x0449d602f0000000 0x001e700f80000000 0x0001e700f8000000

def z888 : W := mkw 0x1b621f40ede2fa87 0x21b621f40ede2fa8 0xffe00fe07fc0ff0e 0xfffe00fe07fc0ff0

def z889 : W := mkw 0x469decbf1810c024 0x8469decbf1810c02 0x4e1ff81fb8188039 0x24e1ff81fb818803

def z890 : W := mkw 0x096003402d40ea07 0x0096003402d40ea0 0xbfe001e07fc0ff0c 0xfbfe001e07fc0ff0

def z891 : W := mkw 0x4f746f4b0840ea07 0x04f746f4b0840ea0 0x0e66760380007000 0x40e6676038000700

def z892 : W := mkw 0x4ffdefff0800c004 0x04ffdefff0800c00 0xdffffffff838f0ff 0xfdffffffff838f0f

def z893 : W := mkw 0x4f746f4b2d00c205 0x04f746f4b2d00c20 0x0e667603b8000000 0x40e667603b800000

def z894 : W := mkw 0x4ffdefff00010440 0x04ffdefff0001044 0x6fffffff80070c03 0xf6fffffff80070c0

def z895 : W := mkw 0x4b602f4b2d40ea07 0x04b602f4b2d40ea0 0xffe00fe3ffc0ff0e 0xfffe00fe3ffc0ff0

def z896 : W := mkw 0x4f746f4b25000000 0x04f746f4b2500000 0xafe67603ffc0000c 0xfafe67603ffc0000

def z897 : W := mkw 0x0960030025402802 0x0096003002540280 0xffe00fe07fc0ff0e 0xfffe00fe07fc0ff0

def z898 : W := mkw 0x449de0bf020c0110 0x4449de0bf020c011 0x001ff01f80180031 0x0001ff01f8018003

def z899 : W := mkw 0x4d54600b00000000 0x04d54600b0000000 0x0e66700380000000 0x40e6670038000000

def z900 : W := mkw 0x0000a09100000000 0x00000a0910000000 0x0067f01380000001 0xd0067f0138000000

def z901 : W := mkw 0x0ddd4000270c0000 0x00ddd4000270c000 0xaffff0007fff000d 0xfaffff0007fff000

def z902 : W := mkw 0x4f746f4b00000000 0x04f746f4b0000000 0x0e66761380000003 0x50e6676138000000

def z903 : W := mkw 0x4ffdefff00402802 0x04ffdefff0040280 0x6fffffff81c00c03 0xf6fffffff81c00c0

def z904 : W := mkw 0x49e9e3f5020d0550 0x449e9e3f5020d055 0x71ffffff863f8fff 0xf71ffffff863f8ff

def z905 : W := mkw 0x4ffdefff020c0110 0x44ffdefff020c011 0x6fffffff863f833f 0xf6fffffff863f833

def z906 : W := mkw 0x0089a0b5020d0550 0x40089a0b5020d055 0x001ff01f803f00f1 0x0001ff01f803f00f

def z907 : W := mkw 0x4f746f4b00000000 0x04f746f4b0000000 0x0e67f60380000001 0xd0e67f6038000000

def z908 : W := mkw 0x2ddf500a77be0028 0x82ddf500a77be002 0xaffff00c7fff003d 0xfaffff00c7fff003

def z909 : W := mkw 0x06160c0ad830d0a4 0x806160c0ad830d0a 0xde1e0e1ff818f0fa 0x6de1e0e1ff818f0f

def z910 : W := mkw 0x0634af9b00010440 0x00634af9b0001044 0x7e7fff9f803f8cff 0xf7e7fff9f803f8cf

def z911 : W := mkw 0x2416100077be0008 0x02416100077be000 0xae7ff0007fff000d 0xfae7ff0007fff000

def z912 : W := mkw 0x0220af9b00000000 0x00220af9b0000000 0x4067ff9f80000003 0xd4067ff9f8000000

def z913 : W := mkw 0x449de0bf00000000 0x0449de0bf0000000 0x007ff01f80000001 0xd007ff01f8000000

def z914 : W := mkw 0x0020a39100000000 0x00020a3910000000 0x407fff9f80000003 0xf407fff9f8000000

def z915 : W := mkw 0x2ddf500af7be10a8 0x82ddf500af7be10a 0xfffff81fffff80ff 0xffffff81fffff80f

def z916 : W := mkw 0x469decbf020d0550 0x4469decbf020d055 0x5e1ffe1f803f80ff 0x75e1ffe1f803f80f

def z917 : W := mkw 0x0020a39100402802 0x00020a3910040280 0x2067f79381c00c03 0xd2067f79381c00c0

def z918 : W := mkw 0x4ffdefff00000000 0x04ffdefff0000000 0x6fffffff86000f03 0xf6fffffff86000f0

def z919 : W := mkw 0x4ddde0bf020d0550 0x44ddde0bf020d055 0x2ffff01f863f00fd 0xf2ffff01f863f00f

def z920 : W := mkw 0x49ebe3f5d830d0a4 0x849ebe3f5d830d0a 0x91e1f1e07838f0fc 0x891e1f1e07838f0f

def z921 : W := mkw 0x06160c0ad830d0a4 0x806160c0ad830d0a 0xde7ffe1ff838f0ff 0xfde7ffe1ff838f0f

def z922 : W := mkw 0x0b600f402d40ea07 0x00b600f402d40ea0 0xbfe007e07fc0ff0c 0xcbfe007e07fc0ff0

def z923 : W := mkw 0x10223301c0e23882 0x210223301c0e2388 0xb067f613c1e770c7 0xdb067f613c1e770c

def z924 : W := mkw 0x1beb9ff4efefffd7 0x61beb9ff4efefffd 0xfff98ffc7fffffff 0xffff98ffc7ffffff

def z925 : W := mkw 0x4ffdefff00010550 0x44ffdefff0001055 0x4fffffff800000f3 0xf4fffffff800000f

def z926 : W := mkw 0x00890024020d0550 0x400890024020d055 0x719809ec063f8ffe 0xb719809ec063f8ff

def z927 : W := mkw 0x1b42bcd1eda3d6c5 0x21b42bcd1eda3d6c 0x4f87f873be2783c9 0x24f87f873be2783c

def z928 : W := mkw 0x49e9e3f500000000 0x049e9e3f50000000 0x01e7f7e380000000 0xc01e7f7e38000000

def z929 : W := mkw 0x10021000c0e33cc2 0x210021000c0e33cc 0x9000000041c07cc0 0x09000000041c07cc

def z930 : W := mkw 0x0b60afd100010440 0x00b60afd10001044 0x7fe7fff386278fcf 0xf7fe7fff386278fc

def z931 : W := mkw 0x29cb500067ae0008 0x029cb500067ae000 0xafe7f0007fe7000d 0xfafe7f0007fe7000

def z932 : W := mkw 0x1b629fd0ede3fec7 0x21b629fd0ede3fec 0xffe18ff07fe7ffcf 0xfffe18ff07fe7ffc

def z933 : W := mkw 0x1022b3d1c0e33ec3 0x21022b3d1c0e33ec 0xb067f7f3c1e77fc7 0xdb067f7f3c1e77fc

def z934 : W := mkw 0x4ffdefff25000000 0x04ffdefff2500000 0x4fffffffbe00000b 0xf4fffffffbe00000

def z935 : W := mkw 0x0416000ad03010a0 0x80416000ad03010a 0x9e1e061ff83870ff 0x79e1e061ff83870f

def z936 : W := mkw 0x0020a39100402802 0x00020a3910040280 0x8067f793c1c07003 0xd8067f793c1c0700

def z937 : W := mkw 0x0000000000000000 0x0000000000000000 0x0067f61380000003 0xd0067f6138000000

def z938 : W := mkw 0x10021000c0e33cc2 0x210021000c0e33cc 0x8000000041e770c0 0x08000000041e770c

def z939 : W := mkw 0x44bde3bf00000000 0x044bde3bf0000000 0x41ffffff80000003 0xf41ffffff8000000

def z940 : W := mkw 0x4f74efff2d40ea07 0x04f74efff2d40ea0 0xffe67fffffc0ff0e 0xfffe67fffffc0ff0

def z941 : W := mkw 0x449de0bf00010550 0x4449de0bf0001055 0x001ff01f800000f1 0x0001ff01f800000f

def z942 : W := mkw 0x00029090c0a314c0 0x000029090c0a314c 0xb067f793c1e77cc7 0xdb067f793c1e77cc

def z943 : W := mkw 0x0940100025820000 0x0094010002582000 0xafe1f0007fc7000c 0xfafe1f0007fc7000

def z944 : W := mkw 0x10021000c0e33cc2 0x210021000c0e33cc 0xb000000041fffcfc 0x0b000000041fffcf

def z945 : W := mkw 0x4ffdefff2f0cc315 0x44ffdefff2f0cc31 0x4fffffffbe18833b 0xf4fffffffbe18833

def z946 : W := mkw 0x4ffd6f4b2d40ea07 0x04ffd6f4b2d40ea0 0xffffffe3ffc0ff0f 0xfffffffe3ffc0ff0

def z947 : W := mkw 0x16161c0ad8f3fce6 0xa16161c0ad8f3fce 0xfe18080c79fffcfc 0x2fe18080c79fffcf

def z948 : W := mkw 0x4b60afff00000000 0x04b60afff0000000 0x4fe7ffff80000003 0xf4fe7ffff8000000

def z949 : W := mkw 0x4ddde0ff00000000 0x04ddde0ff0000000 0x019ff07f80000001 0x0019ff07f8000000

def z950 : W := mkw 0x4220afff0840ea07 0x04220afff0840ea0 0xf067ffffc1c0ff07 0xdf067ffffc1c0ff0

def z951 : W := mkw 0x2ddf5000f7be10a8 0x82ddf5000f7be10a 0xaffff0007fff00fd 0xfaffff0007fff00f

def z952 : W := mkw 0x10221300c0e33cc2 0x210221300c0e33cc 0xb000078041e77cc6 0x0b000078041e77cc

def z953 : W := mkw 0x1022b3b5c0e33dd2 0x61022b3b5c0e33dd 0xb067f7f3c1e77fc7 0xdb067f7f3c1e77fc

def z954 : W := mkw 0x10021000c0e33cc2 0x210021000c0e33cc 0xb000001041e77cc7 0x1b000001041e77cc

def z955 : W := mkw 0x4ffdefff020d0550 0x44ffdefff020d055 0x4fffffff80070003 0xf4fffffff8007000

def z956 : W := mkw 0x6ffdefff371c0008 0x06ffdefff371c000 0xefffffffffd8000f 0xfefffffffffd8000

def z957 : W := mkw 0x4ffdefff2d40ea07 0x04ffdefff2d40ea0 0xafe7f7e3ffc07f00 0xcafe7f7e3ffc07f0

def z958 : W := mkw 0x30021000f5f2388a 0x230021000f5f2388 0x8000000079c07000 0x08000000079c0700

def z959 : W := mkw 0x2ddf500077be0008 0x02ddf500077be000 0xbffff1807fff0c0f 0xfbffff1807fff0c0

def z960 : W := mkw 0x44bde3ff00000000 0x044bde3ff0000000 0x001ff1ff80000001 0x0001ff1ff8000000

def z961 : W := mkw 0x4000a0bf00000000 0x04000a0bf0000000 0x0007f01f80000001 0x00007f01f8000000

def z962 : W := mkw 0x4ffdefff00000000 0x04ffdefff0000000 0x5fffffff8000800f 0xf5fffffff8000800

def z963 : W := mkw 0x4ffdefff2d40ea07 0x04ffdefff2d40ea0 0xcfffffffffc0f30b 0xfcfffffffffc0f30

def z964 : W := mkw 0x0ddd400000000000 0x00ddd40000000000 0x0ffff61380000003 0xf0ffff6138000000

def z965 : W := mkw 0x10021000c2af15d0 0x610021000c2af15d 0x30000000063f8ffc 0x030000000063f8ff

def z966 : W := mkw 0x2ddf502477be0008 0x02ddf502477be000 0xeffff86c7fff000d 0xfeffff86c7fff000

def z967 : W := mkw 0x6ffd6f4b371c0008 0x06ffd6f4b371c000 0x0ffe7603be180008 0x60ffe7603be18000

def z968 : W := mkw 0x4f746f4b00000000 0x04f746f4b0000000 0x5e7e7e1f803880ff 0x75e7e7e1f803880f

def z969 : W := mkw 0x26165c0ad8b2d0ac 0x826165c0ad8b2d0a 0xde1e7e1ff838f0ff 0x7de1e7e1ff838f0f

def z970 : W := mkw 0x0b600f402d40ea07 0x00b600f402d40ea0 0xffe009e07fc0ff0c 0xaffe009e07fc0ff0

def z971 : W := mkw 0x09cb100067ae0000 0x009cb100067ae000 0xaffff0007fff000d 0xfaffff0007fff000

def z972 : W := mkw 0x2ddf500077be0118 0x42ddf500077be011 0xaffff0007fff833d 0xfaffff0007fff833

def z973 : W := mkw 0x1022b391c0e33cc2 0x21022b391c0e33cc 0xbe67f793f9e77ccf 0xfbe67f793f9e77cc

def z974 : W := mkw 0x449de0bf020d0550 0x4449de0bf020d055 0x001ff01f80070001 0x0001ff01f8007000

def z975 : W := mkw 0x10021000c0e23882 0x210021000c0e2388 0x9000000041e070c4 0x09000000041e070c

def z976 : W := mkw 0x4ffdefff020c0000 0x04ffdefff020c000 0x4fffffff8618000b 0xf4fffffff8618000

def z977 : W := mkw 0x0d56100075b20000 0x00d56100075b2000 0xaffff0007fff000d 0xfaffff0007fff000

def z978 : W := mkw 0x2ddf5000f7be1088 0x02ddf5000f7be108 0xaffff013ffff00cd 0xfaffff013ffff00c

def z979 : W := mkw 0x0b600f402d40ea07 0x00b600f402d40ea0 0xffe00ff07fe0ffcf 0xfffe00ff07fe0ffc

def z980 : W := mkw 0x4ffdefff00000000 0x04ffdefff0000000 0x5fffffff802000c7 0xf5fffffff802000c

def z981 : W := mkw 0x1022b391c0e33cc2 0x21022b391c0e33cc 0x9067f793c1e77cc3 0x49067f793c1e77cc

def z982 : W := mkw 0x0b400c002d00c004 0x00b400c002d00c00 0xffe00fe07fc0ff0e 0xfffe00fe07fc0ff0

def z983 : W := mkw 0x4ffdefff020c0110 0x44ffdefff020c011 0x4fffffff86000303 0xf4fffffff8600030

def z984 : W := mkw 0x008980b4020d0550 0x4008980b4020d055 0x719f8fff863f8fff 0xf719f8fff863f8ff

def z985 : W := mkw 0x2ddd5000278e0008 0x02ddd5000278e000 0xaffff0007fc7000d 0xfaffff0007fc7000

def z986 : W := mkw 0x4ffdefff25402a03 0x04ffdefff25402a0 0xefffffffffc00f0f 0xfefffffffffc00f0

def z987 : W := mkw 0x069f8cbeda3dd5f4 0xc069f8cbeda3dd5f 0xaf8787e3fe077f00 0xcaf8787e3fe077f0

def z988 : W := mkw 0x0dfde3b500000000 0x00dfde3b50000000 0x4fffffff80000003 0xf4fffffff8000000

def z989 : W := mkw 0x20021000d2be10a8 0x820021000d2be10a 0x00000000003f00f0 0x000000000003f00f

def z990 : W := mkw 0x0020a39100000000 0x00020a3910000000 0xa067f793c1c00007 0xda067f793c1c0000

def z991 : W := mkw 0x0020a391020d0550 0x40020a391020d055 0x3067f793863f8fff 0xd3067f793863f8ff

def z992 : W := mkw 0x4ffdefff00000000 0x04ffdefff0000000 0x41ffffff80000003 0x841ffffff8000000

def z993 : W := mkw 0x20021000f7be10a8 0x820021000f7be10a 0xa00000007fff00fc 0x0a00000007fff00f

def z994 : W := mkw 0x4ffdefff020d0550 0x44ffdefff020d055 0x4fffffff863f83fb 0xf4fffffff863f83f

def z995 : W := mkw 0x0020a39100010440 0x00020a3910001044 0x2067f79380070c03 0xd2067f79380070c0

def z996 : W := mkw 0x1220afbf8841fdf6 0xe1220afbf8841fdf 0x50000fff8000fff2 0x050000fff8000fff

def z997 : W := mkw 0x2d56500075b20008 0x02d56500075b2000 0x8e67f00079e70001 0x48e67f00079e7000

def z998 : W := mkw 0x4ffdefff020c0110 0x44ffdefff020c011 0x4fffffff80180033 0xf4fffffff8018003

def z999 : W := mkw 0x1220afdb8841fee7 0xa1220afdb8841fee 0x50000fff8000fff2 0x050000fff8000fff

def z1000 : W := mkw 0x049f100052be0000 0x0049f100052be000 0xaffff0007fff000d 0xfaffff0007fff000

def z1001 : W := mkw 0x4ddde0bf00000000 0x04ddde0bf0000000 0x0e7ff01f80000001 0x40e7ff01f8000000

def z1002 : W := mkw 0x19e9b3f527cf2f53 0x619e9b3f527cf2f5 0x21e1f1e007c70f00 0x821e1f1e007c70f0

def z1003 : W := mkw 0x40a9e3b500000000 0x040a9e3b50000000 0x0067f79380000003 0xd0067f7938000000

def z1004 : W := mkw 0x108b90b4c2ef3dd2 0x6108b90b4c2ef3dd 0xb18181e047e77fc4 0x8b18181e047e77fc

def z1005 : W := mkw 0x0be9aff52f4def57 0x40be9aff52f4def5 0xffffffffffffffff 0xffffffffffffffff

def z1006 : W := mkw 0x449de0bf00000000 0x0449de0bf0000000 0x0007f00380000000 0x00007f0038000000

def z1007 : W := mkw 0x2ddf500077be0008 0x02ddf500077be000 0xae7ff0007fff000d 0x4ae7ff0007fff000

def z1008 : W := mkw 0x0634af9b0840e806 0x00634af9b0840e80 0xfe7fff9ff9c0fc0f 0xffe7fff9ff9c0fc0

def z1009 : W := mkw 0x4ffdefff00000000 0x04ffdefff0000000 0xefffffffc1c00007 0xfefffffffc1c0000

def z1010 : W := mkw 0x4f746f4b00000000 0x04f746f4b0000000 0x0e7e761f80000001 0x40e7e761f8000000

def z1011 : W := mkw 0x2d56500075b20008 0x02d56500075b2000 0xae7ff00079ff000d 0xfae7ff00079ff000

def z1012 : W := mkw 0x008980b4020d0550 0x4008980b4020d055 0x719989fc063f8ff3 0x8719989fc063f8ff

def z1013 : W := mkw 0x10223301c0e23882 0x210223301c0e2388 0xa067f603c1c77000 0xca067f603c1c7700

def z1014 : W := mkw 0x6ffdefff371c0008 0x06ffdefff371c000 0x6fffffffbe3f000f 0xf6fffffffbe3f000

def z1015 : W := mkw 0x4ffdefff25000000 0x04ffdefff2500000 0xcffffffff9c00003 0xfcffffffff9c0000

def z1016 : W := mkw 0x2d56500075b20008 0x02d56500075b2000 0xae67f00079c70000 0xcae67f00079c7000

def z1017 : W := mkw 0x0b600f402d40ea07 0x00b600f402d40ea0 0xffe7ffe07fc0ff0f 0xfffe7ffe07fc0ff0

def z1018 : W := mkw 0x4ffd6f4b00000000 0x04ffd6f4b0000000 0x0ffe760380000000 0x60ffe76038000000

def z1019 : W := mkw 0x4f746f4b25402a03 0x04f746f4b25402a0 0x2fe677e387c00f00 0xc2fe677e387c00f0

def z1020 : W := mkw 0x0b600f402d40ea07 0x00b600f402d40ea0 0xfff80fec7fd8ff3e 0xffff80fec7fd8ff3

def z1021 : W := mkw 0x46346f4b00000000 0x046346f4b0000000 0x0006760380000000 0x0000676038000000

def z1022 : W := mkw 0x10021000c0e33cc2 0x210021000c0e33cc 0xb000018041e77cc6 0x9b000018041e77cc

def z1023 : W := mkw 0x10021000c2af15d0 0x610021000c2af15d 0x00000000003f00f0 0x000000000003f00f

def z1024 : W := mkw 0x10021000c0e33cc2 0x210021000c0e33cc 0xb000060041e77cc6 0x5b000060041e77cc

def z1025 : W := mkw 0x249f500052be0008 0x0249f500052be000 0xae7ff00079ff000d 0xfae7ff00079ff000

def z1026 : W := mkw 0x30021000d2bf14c8 0x230021000d2bf14c 0x00000000003f00c0 0x000000000003f00c

def z1027 : W := mkw 0x2ddf500077be0008 0x02ddf500077be000 0x8ffff00079ff0001 0xf8ffff00079ff000

def z1028 : W := mkw 0x4ffdefff00000000 0x04ffdefff0000000 0x4ffff9ff80000001 0xa4ffff9ff8000000

def z1029 : W := mkw 0x4ddd600b00000000 0x04ddd600b0000000 0x0ffff00380000001 0xf0ffff0038000000

def z1030 : W := mkw 0x6ddf502e77be0008 0x06ddf502e77be000 0xaffff00c7fff000d 0xfaffff00c7fff000

def z1031 : W := mkw 0x008980b4020d0550 0x4008980b4020d055 0x719809fc063f8ffe 0x2719809fc063f8ff

def z1032 : W := mkw 0x308b9090f7ff3cca 0x2308b9090f7ff3cc 0xb19981907fff7ccf 0xbb19981907fff7cc

def z1033 : W := mkw 0x4089e0b5020d0550 0x44089e0b5020d055 0x7199f9fc063f8fff 0xb7199f9fc063f8ff

def z1034 : W := mkw 0x0be9aff500000000 0x00be9aff50000000 0x4fffffff80000003 0xf4fffffff8000000

def z1035 : W := mkw 0x4220afdb00000000 0x04220afdb0000000 0x0067f79380000003 0xd0067f7938000000

def z1036 : W := mkw 0x10021000d8f2f8a6 0xa10021000d8f2f8a 0x8000000079c07000 0x08000000079c0700

def z1037 : W := mkw 0x4f746f4b00000000 0x04f746f4b0000000 0x7fe67fe386008f0e 0xf7fe67fe386008f0

def z1038 : W := mkw 0x0020a39100000000 0x00020a3910000000 0x71e7fff386008f0f 0xf71e7fff386008f0

def z1039 : W := mkw 0x2ddf500077be0008 0x02ddf500077be000 0xbffff6007fff700f 0xfbffff6007fff700

def z1040 : W := mkw 0x1b421c40ede3fec7 0x21b421c40ede3fec 0xff8008607fe7ffcc 0x2ff8008607fe7ffc

def z1041 : W := mkw 0x0b602f4100000000 0x00b602f410000000 0x0e66760380000000 0x40e6676038000000

def z1042 : W := mkw 0x10021000d8f3fce6 0xa10021000d8f3fce 0xb000000079e77cc4 0x0b000000079e77cc

def z1043 : W := mkw 0x1022b391c0e33cc2 0x21022b391c0e33cc 0xb07ff79fc1ff7cf7 0xdb07ff79fc1ff7cf

def z1044 : W := mkw 0x0ffdefd100000000 0x00ffdefd10000000 0x4ffffff380000003 0xf4ffffff38000000

def z1045 : W := mkw 0x2ddf500077be0008 0x02ddf500077be000 0xbffff0107fff00cf 0xfbffff0107fff00c

def z1046 : W := mkw 0x02020c00c820d084 0x002020c00c820d08 0xde1e0e1ff838f0ff 0x7de1e0e1ff838f0f

def z1047 : W := mkw 0x1022b391d0f33ce2 0xa1022b391d0f33ce 0xb067f793c1ff7cf7 0xdb067f793c1ff7cf

def z1048 : W := mkw 0x10021000c8e3fce6 0xa10021000c8e3fce 0xb000000041e7fcf4 0x0b000000041e7fcf

def z1049 : W := mkw 0x4ffdefff2d40ea07 0x04ffdefff2d40ea0 0xfffffffffff8ffff 0xffffffffffff8fff

def z1050 : W := mkw 0x4fddecff00000000 0x04fddecff0000000 0x4f9ffe7f80000003 0x74f9ffe7f8000000

def z1051 : W := mkw 0x4ffdefff25402a03 0x04ffdefff25402a0 0x4fffffff81c00003 0xf4fffffff81c0000

def z1052 : W := mkw 0x4ffdefff0800c004 0x04ffdefff0800c00 0xcffffffff8007003 0xfcffffffff800700

def z1053 : W := mkw 0x449de0bf00010440 0x0449de0bf0001044 0x001ff01f802700c1 0x0001ff01f802700c

def z1054 : W := mkw 0x10021000c0e33cc2 0x210021000c0e33cc 0x1000000000277cc0 0x01000000000277cc

def z1055 : W := mkw 0x10021000d0b314e0 0xa10021000d0b314e 0x00000000003f00f0 0x000000000003f00f

def z1056 : W := mkw 0x1b621f40ede3fec7 0x21b621f40ede3fec 0xbe60060079e77cc4 0x4be60060079e77cc

def z1057 : W := mkw 0x30021000f7ff3dda 0x630021000f7ff3dd 0xb00000007ffffffc 0x0b00000007ffffff

def z1058 : W := mkw 0x0dfde3b5020d0550 0x40dfde3b5020d055 0x7fffffff863f8fff 0xf7fffffff863f8ff

def z1059 : W := mkw 0x4ffdefff00000000 0x04ffdefff0000000 0x5fffffff80008f03 0xf5fffffff80008f0

def z1060 : W := mkw 0x0ffd4f4a2d40ea07 0x00ffd4f4a2d40ea0 0xffffffffffc0ff0f 0xfffffffffffc0ff0

def z1061 : W := mkw 0x4ffdefff00000000 0x04ffdefff0000000 0x6fffffff80270007 0xf6fffffff8027000

def z1062 : W := mkw 0x4f74efdb2d40ea07 0x04f74efdb2d40ea0 0xbe67f793f9c07c07 0xdbe67f793f9c07c0

def z1063 : W := mkw 0x094000002d40ea07 0x0094000002d40ea0 0xffe009e07fc0ff0e 0xfffe009e07fc0ff0

def z1064 : W := mkw 0x4ffdefff25000201 0x04ffdefff2500020 0x4fffffff86000303 0xf4fffffff8600030

def z1065 : W := mkw 0x46bdefff00000000 0x046bdefff0000000 0x4e1fffff80000003 0x74e1fffff8000000

def z1066 : W := mkw 0x1022b391c0e33cc2 0x21022b391c0e33cc 0xf067ff93c1e7fccf 0xff067ff93c1e7fcc

def z1067 : W := mkw 0x10021000c0e23882 0x210021000c0e2388 0xb000000041c07c04 0x0b000000041c07c0

def z1068 : W := mkw 0x108b90b4c0e33cc2 0x2108b90b4c0e33cc 0xf19989fc41e77cc7 0xbf19989fc41e77cc

def z1069 : W := mkw 0x4dfde3ff00000000 0x04dfde3ff0000000 0x01fff7ff80000003 0xd01fff7ff8000000

def z1070 : W := mkw 0x10021000c0a314c0 0x210021000c0a314c 0x90000000402770c4 0x090000000402770c

def z1071 : W := mkw 0x49e9e3f5020d0550 0x449e9e3f5020d055 0x31e7f7f386270fc7 0xd31e7f7f386270fc

def z1072 : W := mkw 0x2ddf500077be0008 0x02ddf500077be000 0x8e67f00079c70000 0x48e67f00079c7000

def z1073 : W := mkw 0x2ddf500077be0008 0x02ddf500077be000 0xbffff0007fff80fd 0xfbffff0007fff80f

def z1074 : W := mkw 0x0942100065a20000 0x00942100065a2000 0xae67f00079e70005 0xdae67f00079e7000

def z1075 : W := mkw 0x0020230100402802 0x0002023010040280 0x80667603c1c07000 0x480667603c1c0700

def z1076 : W := mkw 0x1f763f4bfdf2faa7 0xa1f763f4bfdf2faa 0x8e667603f9c07000 0x48e667603f9c0700

def z1077 : W := mkw 0x2ddf500077be0008 0x02ddf500077be000 0xaff9f0007fff000c 0xaaff9f0007fff000

def z1078 : W := mkw 0x469decbf020d0550 0x4469decbf020d055 0x7f9fffff863f8fff 0xf7f9fffff863f8ff

def z1079 : W := mkw 0x249fd0bed2bf15f8 0xc249fd0bed2bf15f 0x001ff01f803f00f1 0x0001ff01f803f00f

def z1080 : W := mkw 0x4020a3bf00000000 0x04020a3bf0000000 0x0067f79f80000003 0xd0067f79f8000000

def z1081 : W := mkw 0x6f746f4b35100008 0x06f746f4b3510000 0x0e667603b8000000 0x40e667603b800000

def z1082 : W := mkw 0x008980b4020d0550 0x4008980b4020d055 0x519989fc063f8ffb 0x2519989fc063f8ff

def z1083 : W := mkw 0x449de0bf00010440 0x0449de0bf0001044 0x301ff19f80270cc7 0x9301ff19f80270cc

def z1084 : W := mkw 0x4ffdefff1a1dc574 0xc4ffdefff1a1dc57 0x7fffffffbe3f8fff 0xf7fffffffbe3f8ff

def z1085 : W := mkw 0x4f74efff00000000 0x04f74efff0000000 0x4e67ffff80000003 0xd4e67ffff8000000

def z1086 : W := mkw 0x0020a3b500010550 0x40020a3b50001055 0x5067ffff80008ff3 0xd5067ffff80008ff

def z1087 : W := mkw 0x20021000fdb2d0ac 0x820021000fdb2d0a 0x9000000079f8f0fc 0x09000000079f8f0f

def z1088 : W := mkw 0x4b606f412d40ea07 0x04b606f412d40ea0 0xffe07fe07fc0ff0e 0xfffe07fe07fc0ff0

def z1089 : W := mkw 0x1022b391c0e33cc2 0x21022b391c0e33cc 0xb000018041e77cc4 0x0b000018041e77cc

def z1090 : W := mkw 0x4ffdefff00000000 0x04ffdefff0000000 0x4fe7ffe380000002 0xf4fe7ffe38000000

def z1091 : W := mkw 0x449de0bf00000000 0x0449de0bf0000000 0x001ff01f803800f1 0x0001ff01f803800f

def z1092 : W := mkw 0x4ffdefff0840ea07 0x04ffdefff0840ea0 0x4fffffff80007003 0xf4fffffff8000700

def z1093 : W := mkw 0x4ffdefff2d00c205 0x04ffdefff2d00c20 0x4fffffffb8000003 0xf4fffffffb800000

def z1094 : W := mkw 0x0020a39100000000 0x00020a3910000000 0x41e7fff380000003 0xf41e7fff38000000

def z1095 : W := mkw 0x108b90b4c2af15d0 0x6108b90b4c2af15d 0x719989fc063f8fff 0xb719989fc063f8ff

def z1096 : W := mkw 0x42202f4b00000000 0x042202f4b0000000 0x0066760380000000 0x4006676038000000

def z1097 : W := mkw 0x1022b3b5c0e33dd2 0x61022b3b5c0e33dd 0xf1e7ffffc7e7ffff 0xff1e7ffffc7e7fff

def z1098 : W := mkw 0x2fdd4c2e3f1cc13c 0xc2fdd4c2e3f1cc13 0x4f98086c3e188338 0x24f98086c3e18833

def z1099 : W := mkw 0x4ffd6f4b020c0000 0x04ffd6f4b020c000 0x2ffff603863f000d 0xf2ffff603863f000

def z1100 : W := mkw 0x4ddde0bf00000000 0x04ddde0bf0000000 0x4ffff9ff80000003 0xf4ffff9ff8000000

def z1101 : W := mkw 0x2fdd4c4a3f1cc22d 0x82fdd4c4a3f1cc22 0x4f98086c3e188338 0x24f98086c3e18833

def z1102 : W := mkw 0x0960a3d100000000 0x00960a3d10000000 0x01e7f7f380000003 0xd01e7f7f38000000

def z1103 : W := mkw 0x1022b391c0e33cc2 0x21022b391c0e33cc 0xf067fff3c1e7ffc7 0xdf067fff3c1e7ffc

def z1104 : W := mkw 0x0b60afd12d40ea07 0x00b60afd12d40ea0 0x8e67f793f9c07003 0xd8e67f793f9c0700

def z1105 : W := mkw 0x469decbf00000000 0x0469decbf0000000 0x401ffe1f80000003 0x0401ffe1f8000000

def z1106 : W := mkw 0x0000200100000000 0x0000020010000000 0x0006700380000000 0x0000670038000000

def z1107 : W := mkw 0x46bdefff00000000 0x046bdefff0000000 0x001ff61f80000001 0x0001ff61f8000000

def z1108 : W := mkw 0x10021000e5e33ec3 0x210021000e5e33ec 0xb000000047e77fc4 0x0b000000047e77fc

def z1109 : W := mkw 0x4634afff00000000 0x04634afff0000000 0x4e7fffff80000003 0xf4e7fffff8000000

def z1110 : W := mkw 0x29c95000278e0008 0x029c95000278e000 0xafe1f0007fc70000 0xcafe1f0007fc7000

def z1111 : W := mkw 0x4dfde3ff25402a03 0x04dfde3ff25402a0 0x21fff1ff87c00f01 0x821fff1ff87c00f0

def z1112 : W := mkw 0x10021000dafffdf6 0xe10021000dafffdf 0xb00000007ffffffc 0x0b00000007ffffff

def z1113 : W := mkw 0x4f746f4b00000000 0x04f746f4b0000000 0x4ffe7fff80000003 0xf4ffe7fff8000000

def z1114 : W := mkw 0x06160c0ad830d0a4 0x806160c0ad830d0a 0x9e1e061ff83870f7 0x59e1e061ff83870f

def z1115 : W := mkw 0x0020a39100412c42 0x00020a39100412c4 0xb067f793c1e77cc7 0xdb067f793c1e77cc

def z1116 : W := mkw 0x108b1000c2ef3cc2 0x2108b1000c2ef3cc 0xb199800047ff7ccd 0xbb199800047ff7cc

def z1117 : W := mkw 0x4ffdefff00402802 0x04ffdefff0040280 0xcfffffffc1c07003 0xfcfffffffc1c0700

def z1118 : W := mkw 0x0220afd100000000 0x00220afd10000000 0x4067fff380000003 0xd4067fff38000000

def z1119 : W := mkw 0x1022b391c0e33cc2 0x21022b391c0e33cc 0xb067f793c1c77cc2 0xcb067f793c1c77cc

def z1120 : W := mkw 0x4960e3d100000000 0x04960e3d10000000 0x0067f79380000003 0xd0067f7938000000

def z1121 : W := mkw 0x0002100040a20000 0x00002100040a2000 0xae67f00079e7000d 0xfae67f00079e7000

def z1122 : W := mkw 0x4b60afff2d40ea07 0x04b60afff2d40ea0 0xffe7ffffffc0ff0f 0xfffe7ffffffc0ff0

def z1123 : W := mkw 0x449de0bf020c0000 0x0449de0bf020c000 0x001ff01f803f0001 0x0001ff01f803f000

def z1124 : W := mkw 0x6ffdefff371c0118 0x46ffdefff371c011 0x4fffffffbe18833b 0xf4fffffffbe18833

def z1125 : W := mkw 0x449de0bf020d0550 0x4449de0bf020d055 0x219ff1ff86070f01 0x8219ff1ff86070f0

def z1126 : W := mkw 0x4414600b00000000 0x04414600b0000000 0x001e701f80000001 0x0001e701f8000000

def z1127 : W := mkw 0x12221f00d8f3fce6 0xa12221f00d8f3fce 0xfe600f8079fffcfe 0xffe600f8079fffcf

def z1128 : W := mkw 0x4ffd6f6f2d40ea07 0x04ffd6f6f2d40ea0 0xcffe7e6fffc0f308 0x6cffe7e6fffc0f30

def z1129 : W := mkw 0x4ffdefff00010550 0x44ffdefff0001055 0x4fffffff80000f03 0xf4fffffff80000f0

def z1130 : W := mkw 0x10029090d8f3fce6 0xa10029090d8f3fce 0xf019899c79fffcff 0xbf019899c79fffcf

def z1131 : W := mkw 0x49e9e3f525402a03 0x049e9e3f525402a0 0xb1e7f7f3c7c07f07 0xdb1e7f7f3c7c07f0

def z1132 : W := mkw 0x008980b4020d0550 0x4008980b4020d055 0x619989fc063f8ff9 0xa619989fc063f8ff

def z1133 : W := mkw 0x0614ac9b00000000 0x00614ac9b0000000 0x4e1ffe1f80000003 0x74e1ffe1f8000000

def z1134 : W := mkw 0x0960a39100000000 0x00960a3910000000 0x0fe7f79380000003 0xf0fe7f7938000000

def z1135 : W := mkw 0x4ffdefff2d00c004 0x04ffdefff2d00c00 0xffffffffffc0f00f 0xfffffffffffc0f00

def z1136 : W := mkw 0x4ffdefff00010440 0x04ffdefff0001044 0x4fffffff802700c3 0xf4fffffff802700c

def z1137 : W := mkw 0x469decbf00000000 0x0469decbf0000000 0x4e1ff81f80000001 0x24e1ff81f8000000

def z1138 : W := mkw 0x06342f0b00000000 0x006342f0b0000000 0x0e66760380000000 0x40e6676038000000

def z1139 : W := mkw 0x4be9eff52d40ea07 0x04be9eff52d40ea0 0xffe7fff3ffc0ff0f 0xfffe7fff3ffc0ff0

def z1140 : W := mkw 0x4ddde0bf00000000 0x04ddde0bf0000000 0x01fff01f80000001 0x801fff01f8000000

def z1141 : W := mkw 0x44bde3bf020d0550 0x444bde3bf020d055 0x71ffffff863f8fff 0xf71ffffff863f8ff

def z1142 : W := mkw 0x0ddf500050b20000 0x00ddf500050b2000 0xaffff00079ff000d 0xfaffff00079ff000

def z1143 : W := mkw 0x0dfd630100000000 0x00dfd63010000000 0x0ffff60380000001 0xf0ffff6038000000

def z1144 : W := mkw 0x00890000020c0000 0x000890000020c000 0x719989fc063f8fff 0xb719989fc063f8ff

def z1145 : W := mkw 0x4ffdefff00000000 0x04ffdefff0000000 0x4fffffff8600830b 0xf4fffffff8600830

def z1146 : W := mkw 0x06160c0ad830d0a4 0x806160c0ad830d0a 0xff9e0e1ffe38f0ff 0xfff9e0e1ffe38f0f

def z1147 : W := mkw 0x4ffdefff3d50ea27 0x84ffdefff3d50ea2 0xffffffffffd8ff3f 0xfffffffffffd8ff3

def z1148 : W := mkw 0x46bdefff0840ea07 0x046bdefff0840ea0 0x501fffff8000ff03 0x0501fffff8000ff0

def z1149 : W := mkw 0x06140c0a9810d0a4 0x806140c0a9810d0a 0x5e180e1fb838f0ff 0x35e180e1fb838f0f

def z1150 : W := mkw 0x2ddf502477be0118 0x42ddf502477be011 0xaffff00c7fff003d 0xfaffff00c7fff003

def z1151 : W := mkw 0x4f746f6f00000000 0x04f746f6f0000000 0x4e667e6f80000000 0x44e667e6f8000000

def z1152 : W := mkw 0x4ffdefff0840ea07 0x04ffdefff0840ea0 0xdffffffff800ff0f 0xfdffffffff800ff0

def z1153 : W := mkw 0x44bde3bf00000000 0x044bde3bf0000000 0x007ff19f80000001 0x8007ff19f8000000

def z1154 : W := mkw 0x00000000020d0550 0x400000000020d055 0x719809fc063f8fff 0xb719809fc063f8ff

def z1155 : W := mkw 0x1022b391c0e33cc2 0x21022b391c0e33cc 0xa067f783c1e77c05 0xda067f783c1e77c0

def z1156 : W := mkw 0x2d56500075b20008 0x02d56500075b2000 0xafe7f0007fe7000d 0xfafe7f0007fe7000

def z1157 : W := mkw 0x4ffd6f6f2d40ea07 0x04ffd6f6f2d40ea0 0xfffe7fefffc0ff0e 0xffffe7fefffc0ff0

def z1158 : W := mkw 0x2ddd5000379e0008 0x02ddd5000379e000 0x2fe1f0003fc70000 0x82fe1f0003fc7000

def z1159 : W := mkw 0x4f746f4b00000000 0x04f746f4b0000000 0x0e7e760380000001 0x70e7e76038000000

def z1160 : W := mkw 0x2ddf500077be0008 0x02ddf500077be000 0x8e7ff00079ff000d 0x78e7ff00079ff000

def z1161 : W := mkw 0x0b600f402d40ea07 0x00b600f402d40ea0 0xff800fe07fc0ff0e 0x2ff800fe07fc0ff0

def z1162 : W := mkw 0x0020a39100010440 0x00020a3910001044 0x1067f79380000cc3 0xd1067f79380000cc

def z1163 : W := mkw 0x10029090c0a314c0 0x210029090c0a314c 0x3001819000270cc7 0x93001819000270cc

def z1164 : W := mkw 0x4ffd6f6f00000000 0x04ffd6f6f0000000 0x4ffe7e7f80000003 0x74ffe7e7f8000000

def z1165 : W := mkw 0x4ffdefff00000000 0x04ffdefff0000000 0x4fffffff8018803b 0xf4fffffff8018803

def z1166 : W := mkw 0x4ffdefff020d0550 0x44ffdefff020d055 0x0e7ff61f803f00f1 0x40e7ff61f803f00f

def z1167 : W := mkw 0x4ffdefff2f4ceb17 0x44ffdefff2f4ceb1 0xffffffffffd8ff3f 0xfffffffffffd8ff3

def z1168 : W := mkw 0x4ffd6f6f00000000 0x04ffd6f6f0000000 0x4ffffe6f80000001 0xf4ffffe6f8000000

def z1169 : W := mkw 0x4f746f4b0800c004 0x04f746f4b0800c00 0xde667e03f800f00e 0x7de667e03f800f00

def z1170 : W := mkw 0x4ffdefff00000110 0x44ffdefff0000011 0x4fffffff80008333 0xf4fffffff8000833

def z1171 : W := mkw 0x4ffdefff2d40ea07 0x04ffdefff2d40ea0 0x7fffffff87c0ff03 0xf7fffffff87c0ff0

def z1172 : W := mkw 0x39e9f3b527cf2d5a 0x639e9f3b527cf2d5 0x21e1f1e007c70f00 0x821e1f1e007c70f0

def z1173 : W := mkw 0x2ddf500077be0008 0x02ddf500077be000 0xae7ff00079ff0005 0xdae7ff00079ff000

def z1174 : W := mkw 0x4f546c4b00000000 0x04f546c4b0000000 0x0e06700380000000 0x00e0670038000000

def z1175 : W := mkw 0x1220af918841fcc6 0x21220af918841fcc 0x50000f938000fcc2 0x050000f938000fcc

def z1176 : W := mkw 0x4ffdefff0800c004 0x04ffdefff0800c00 0x4fffffffb800800b 0xf4fffffffb800800

def z1177 : W := mkw 0x0414a09b00000000 0x00414a09b0000000 0x001ff01f80000001 0x0001ff01f8000000

def z1178 : W := mkw 0x4ffdefff00000000 0x04ffdefff0000000 0x4fffffff803800f3 0xf4fffffff803800f

def z1179 : W := mkw 0x0022b39140e22802 0x00022b39140e2280 0xb067f793c1e77c07 0xdb067f793c1e77c0

def z1180 : W := mkw 0x2ddf500077be0008 0x02ddf500077be000 0xaffff1e07fff0f0d 0xfaffff1e07fff0f0

def z1181 : W := mkw 0x06161c0ad8b2d0a4 0x806161c0ad8b2d0a 0xfe1e0e1ff9fff0ff 0x7fe1e0e1ff9fff0f

def z1182 : W := mkw 0x4ffdefff00000000 0x04ffdefff0000000 0x4fffffff8038000f 0xf4fffffff8038000

def z1183 : W := mkw 0x449de0bf00000000 0x0449de0bf0000000 0x001ff61f80000003 0x5001ff61f8000000

def z1184 : W := mkw 0x04bde39100000000 0x004bde3910000000 0x007ff79380000003 0xd007ff7938000000

def z1185 : W := mkw 0x06140c0a0800c004 0x006140c0a0800c00 0xde1e0e1ff838f0ff 0x7de1e0e1ff838f0f

def z1186 : W := mkw 0x2ddf500077be0008 0x02ddf500077be000 0xaffff613ffff000f 0xfaffff613ffff000

def z1187 : W := mkw 0x0022b391c0a21080 0x00022b391c0a2108 0xb067f793c1e770c7 0xdb067f793c1e770c

def z1188 : W := mkw 0x1b621f40ede2fa87 0x21b621f40ede2fa8 0x8e60060079c07000 0x48e60060079c0700

def z1189 : W := mkw 0x06160c0ad830d0a4 0x806160c0ad830d0a 0x8e1e061ff83870fd 0x78e1e061ff83870f

def z1190 : W := mkw 0x4ffdefff00000000 0x04ffdefff0000000 0x4ffe7fff80000002 0x64ffe7fff8000000

def z1191 : W := mkw 0x4220afff0841ef57 0x44220afff0841ef5 0x50000fff8000fff2 0x050000fff8000fff

def z1192 : W := mkw 0x10029090c0e33cc2 0x210029090c0e33cc 0xb000019041e77cc6 0x0b000019041e77cc

def z1193 : W := mkw 0x4ffdefff00000000 0x04ffdefff0000000 0x4fffffef80000000 0xe4fffffef8000000

def z1194 : W := mkw 0x4634efff00000000 0x04634efff0000000 0x40067fff80000002 0x040067fff8000000

def z1195 : W := mkw 0x5ffdefff00412c42 0x25ffdefff00412c4 0x4fffffff80000c03 0xf4fffffff80000c0

def z1196 : W := mkw 0x10029090c0a314c0 0x210029090c0a314c 0x00018010002700c1 0x000018010002700c

def z1197 : W := mkw 0x2ddf502477be0118 0x42ddf502477be011 0xaffff0607fff030d 0xfaffff0607fff030

def z1198 : W := mkw 0x04160000d0301080 0x004160000d030108 0xde1e0e1ff838f0ff 0x7de1e0e1ff838f0f

def z1199 : W := mkw 0x10229390c0e33cc2 0x210229390c0e33cc 0xb061879041e77cc7 0xdb061879041e77cc

def z1200 : W := mkw 0x2ddf504077be0209 0x02ddf504077be020 0xaffff0607fff030d 0xfaffff0607fff030

def z1201 : W := mkw 0x2b421c00ffbed0ac 0x82b421c00ffbed0a 0xffe00e007ffff0fe 0xfffe00e007ffff0f

def z1202 : W := mkw 0x4f746f4b00000000 0x04f746f4b0000000 0x4e667e1f80000002 0x44e667e1f8000000

def z1203 : W := mkw 0x0b600f402d40ea07 0x00b600f402d40ea0 0xffe00ffc7fc0fffe 0xfffe00ffc7fc0fff

def z1204 : W := mkw 0x4ffdefff2f0dc755 0x44ffdefff2f0dc75 0x7fffffffbe3f8fff 0xf7fffffffbe3f8ff

def z1205 : W := mkw 0x1436a391d0713cc2 0x21436a391d0713cc 0x9e1e0793f8387ccf 0x79e1e0793f8387cc

def z1206 : W := mkw 0x30021000fffffecf 0x230021000fffffec 0xb00000007fffffcc 0x0b00000007fffffc

def z1207 : W := mkw 0x4ffdefff2d41ef57 0x44ffdefff2d41ef5 0xffffffffffc0ffff 0xfffffffffffc0fff

def z1208 : W := mkw 0x0000809000010440 0x0000080900001044 0x719989fc063f8fff 0xb719989fc063f8ff

def z1209 : W := mkw 0x19421000e5e33cc2 0x219421000e5e33cc 0xbfe000007fe77ccc 0xfbfe000007fe77cc

def z1210 : W := mkw 0x4dfde3ff00000000 0x04dfde3ff0000000 0x0ffff1ff80000001 0xf0ffff1ff8000000

def z1211 : W := mkw 0x0020a39100010440 0x00020a3910001044 0x0067f793802700c3 0xd0067f793802700c

def z1212 : W := mkw 0x10021000c0e33cc2 0x210021000c0e33cc 0xb001800041e77cc5 0x9b001800041e77cc

def z1213 : W := mkw 0x4f74efff00010550 0x44f74efff0001055 0x5e667fff80008ff2 0x45e667fff80008ff

def z1214 : W := mkw 0x108b90b4dafffdf6 0xe108b90b4dafffdf 0xf19989fc7fffffff 0xbf19989fc7ffffff

def z1215 : W := mkw 0x449de0bf020c0000 0x0449de0bf020c000 0x219ff01f863f000d 0xb219ff01f863f000

def z1216 : W := mkw 0x00021000c0a21080 0x000021000c0a2108 0xb000000041e770c4 0x0b000000041e770c

def z1217 : W := mkw 0x6ffdefff3f1cc02c 0x86ffdefff3f1cc02 0x4fffffffbe18803b 0xf4fffffffbe18803

def z1218 : W := mkw 0x0b600f402d40ea07 0x00b600f402d40ea0 0xefe00fe07fc07f02 0xfefe00fe07fc07f0

def z1219 : W := mkw 0x29c95000278e0008 0x029c95000278e000 0xaff9f0007fff000d 0xfaff9f0007fff000

def z1220 : W := mkw 0x4ffdefff020c0000 0x04ffdefff020c000 0x4fffffff803f0003 0xf4fffffff803f000

def z1221 : W := mkw 0x46bdefff00000000 0x046bdefff0000000 0x419fffff80000003 0xb419fffff8000000

def z1222 : W := mkw 0x1022b391c0e33cc2 0x21022b391c0e33cc 0xf1e7fff3c1e77cc7 0xff1e7fff3c1e77cc

def z1223 : W := mkw 0x0be9aff5020d0550 0x40be9aff5020d055 0x7fffffff863f8fff 0xf7fffffff863f8ff

def z1224 : W := mkw 0x4ffdefff020d0550 0x44ffdefff020d055 0x7fffffff86078ff3 0xf7fffffff86078ff

def z1225 : W := mkw 0x4ffdefff024d2d52 0x44ffdefff024d2d5 0xffffffffc7ffffff 0xfffffffffc7fffff

def z1226 : W := mkw 0x4ffdefff270d0550 0x44ffdefff270d055 0xffffffffffff8fff 0xfffffffffffff8ff

def z1227 : W := mkw 0x4f74efdb00000000 0x04f74efdb0000000 0x0e67f61380000001 0x40e67f6138000000

def z1228 : W := mkw 0x44bde3bf00402802 0x044bde3bf0040280 0xb07ff79fc1c07c07 0xdb07ff79fc1c07c0

def z1229 : W := mkw 0x2ddf5000f7be1088 0x02ddf5000f7be108 0xfffffe1ffffff0ff 0xffffffe1ffffff0f

def z1230 : W := mkw 0x0960a3d125402a03 0x00960a3d125402a0 0x21e7f7f387c00f03 0xd21e7f7f387c00f0

def z1231 : W := mkw 0x1022b391d0f33cc2 0x21022b391d0f33cc 0xb067f793f9ff7ccf 0xdb067f793f9ff7cc

def z1232 : W := mkw 0x06161c0ad8b2d0a4 0x806161c0ad8b2d0a 0xde1ffe1ff83ff0ff 0x7de1ffe1ff83ff0f

def z1233 : W := mkw 0x10021000c8e3fcc6 0x210021000c8e3fcc 0xb000000079e7fccc 0x0b000000079e7fcc

def z1234 : W := mkw 0x008980b4020d0550 0x4008980b4020d055 0xf1f989fc47ff8fff 0xff1f989fc47ff8ff

def z1235 : W := mkw 0x46146c0b00000000 0x046146c0b0000000 0x4e1e7e1f80000003 0x74e1e7e1f8000000

def z1236 : W := mkw 0x4ffdefff2f4def57 0x44ffdefff2f4def5 0xffffffffffc7ff0f 0xfffffffffffc7ff0

def z1237 : W := mkw 0x1220aff58841ffd7 0x61220aff58841ffd 0x50000fff8000fff2 0x050000fff8000fff

def z1238 : W := mkw 0x20021000dabed0ac 0x820021000dabed0a 0x90000000783ff0fc 0x090000000783ff0f

def z1239 : W := mkw 0x1022b391c0e33cc2 0x21022b391c0e33cc 0xb067f793c1fffcff 0xdb067f793c1fffcf

def z1240 : W := mkw 0x4f746f4b2d40ea07 0x04f746f4b2d40ea0 0xde7e7e1ff9c0f00f 0x7de7e7e1ff9c0f00

def z1241 : W := mkw 0x00a9a3b500402802 0x000a9a3b50040280 0xf1ffffffc7c0ff0f 0xff1ffffffc7c0ff0

def z1242 : W := mkw 0x0fddccbe00000000 0x00fddccbe0000000 0x4fffffff80000003 0xf4fffffff8000000

def z1243 : W := mkw 0x4414e09b00000000 0x04414e09b0000000 0x0007f01380000001 0x00007f0138000000

def z1244 : W := mkw 0x1022b3b5c0e33cc2 0x21022b3b5c0e33cc 0xf067ffffc1e77cc7 0xdf067ffffc1e77cc

def z1245 : W := mkw 0x1022b391c0e33cc2 0x21022b391c0e33cc 0xb07ff793c1ff7ccf 0xfb07ff793c1ff7cc

def z1246 : W := mkw 0x0b400c402d40ea07 0x00b400c402d40ea0 0xff8009e07fc0ff0e 0xbff8009e07fc0ff0

def z1247 : W := mkw 0x1002b091c0a314c0 0x21002b091c0a314c 0xb067f613c1e770c7 0xdb067f613c1e770c

def z1248 : W := mkw 0x30021000fffffcee 0xa30021000fffffce 0xb00000007ffffcfc 0x0b00000007ffffcf

def z1249 : W := mkw 0x449de0bf00000000 0x0449de0bf0000000 0x719ff9ff86008f0f 0xb719ff9ff86008f0

def z1250 : W := mkw 0x0f544c0a00000000 0x00f544c0a0000000 0x0e66760380000000 0x40e6676038000000

def z1251 : W := mkw 0x10021000d0f33ce2 0xa10021000d0f33ce 0xb000000041ff7cf4 0x0b000000041ff7cf

def z1252 : W := mkw 0x4ffdefff2d40ea07 0x04ffdefff2d40ea0 0x8e7ff61ff9c07001 0x48e7ff61ff9c0700

def z1253 : W := mkw 0x4d74634b00000000 0x04d74634b0000000 0x0066700380000000 0x0006670038000000

def z1254 : W := mkw 0x0b600f402d40ea07 0x00b600f402d40ea0 0xefe00fe07fc0ff08 0xeefe00fe07fc0ff0

def z1255 : W := mkw 0x4fdd4c6e2f0cc315 0x44fdd4c6e2f0cc31 0x4f98086c3e188338 0x24f98086c3e18833

def z1256 : W := mkw 0x4ffdefff0800c024 0x84ffdefff0800c02 0x4fffffff80008033 0xf4fffffff8000803

def z1257 : W := mkw 0x208b90b4ffbfd5fc 0xc208b90b4ffbfd5f 0xf19989fc7fffffff 0xbf19989fc7ffffff

def z1258 : W := mkw 0x1020b39180c33cc2 0x21020b39180c33cc 0x3067f79381c77cc3 0xd3067f79381c77cc

def z1259 : W := mkw 0x0b600f402d40ea07 0x00b600f402d40ea0 0xfff80ffc7fc0ff0f 0xffff80ffc7fc0ff0

def z1260 : W := mkw 0x4ffdefff0a0dc554 0x44ffdefff0a0dc55 0xfffffffffe3fffff 0xffffffffffe3ffff

def z1261 : W := mkw 0x4ffdefff274d2f53 0x44ffdefff274d2f5 0x7fffffff87ff8fff 0xf7fffffff87ff8ff

def z1262 : W := mkw 0x0000a09100000000 0x00000a0910000000 0x0007f61380000003 0x50007f6138000000

def z1263 : W := mkw 0x2ddd5000379e0008 0x02ddd5000379e000 0x2ff9f0003fff000d 0xb2ff9f0003fff000

def z1264 : W := mkw 0x1022b391c0e33cc2 0x21022b391c0e33cc 0x3067f79381e77cc3 0x83067f79381e77cc

def z1265 : W := mkw 0x46bdefbf00000000 0x046bdefbf0000000 0x4e7fff9f80000003 0xf4e7fff9f8000000

def z1266 : W := mkw 0x0020a39100000000 0x00020a3910000000 0x0067f19380000001 0x80067f1938000000

def z1267 : W := mkw 0x6ffdefff3f1cc20d 0x06ffdefff3f1cc20 0x4fffffffbe18830b 0xf4fffffffbe18830

def z1268 : W := mkw 0x4ffdefff25402802 0x04ffdefff2540280 0xffffffffffc07c0f 0xfffffffffffc07c0

def z1269 : W := mkw 0x06bdafbf020d0550 0x406bdafbf020d055 0x7fffffff863f8fff 0xf7fffffff863f8ff

def z1270 : W := mkw 0x4f746f4b00000000 0x04f746f4b0000000 0x0fe6760380000000 0xf0fe676038000000

def z1271 : W := mkw 0x4fddecff2d00c205 0x04fddecff2d00c20 0x4f9ff87fbe008309 0x24f9ff87fbe00830

def z1272 : W := mkw 0x0d74e39100000000 0x00d74e3910000000 0x0e67f79380000003 0xd0e67f7938000000

def z1273 : W := mkw 0x049d400a00000000 0x0049d400a0000000 0x001ff01f80000001 0x0001ff01f8000000

def z1274 : W := mkw 0x008980b4020d0550 0x4008980b4020d055 0x71fff9fc063f8fff 0xf71fff9fc063f8ff

def z1275 : W := mkw 0x4ffdefff2d40ea07 0x04ffdefff2d40ea0 0xffe7ffe3ffc0ff0e 0xfffe7ffe3ffc0ff0

def z1276 : W := mkw 0x4fddecff00000000 0x04fddecff0000000 0x0e1ff01f80000001 0x00e1ff01f8000000

def z1277 : W := mkw 0x00a9a3b5024d2d52 0x400a9a3b5024d2d5 0xf1ffffffc7ffffff 0xff1ffffffc7fffff

def z1278 : W := mkw 0x0634af9b00000000 0x00634af9b0000000 0x0e67f79380000003 0xd0e67f7938000000

def z1279 : W := mkw 0x06160c0ad830d0a4 0x806160c0ad830d0a 0xdf9e0e7ffe38f3ff 0x7df9e0e7ffe38f3f

def z1280 : W := mkw 0x008980b4020d0550 0x4008980b4020d055 0xf1998ffc463fffff 0xff1998ffc463ffff

def z1281 : W := mkw 0x4220afff00000000 0x04220afff0000000 0x40667fff80000002 0x440667fff8000000

def z1282 : W := mkw 0x2ddf500077be0008 0x02ddf500077be000 0xeffff9e07fff000f 0xfeffff9e07fff000

def z1283 : W := mkw 0x4f746f4b0840ea07 0x04f746f4b0840ea0 0x5e667fe38000ff02 0x45e667fe38000ff0

def z1284 : W := mkw 0x10021000ede2fa87 0x210021000ede2fa8 0xb00000007fc0ff0c 0x0b00000007fc0ff0

def z1285 : W := mkw 0x1020a39100412c42 0x21020a39100412c4 0x0067f79380000c03 0xd0067f79380000c0

def z1286 : W := mkw 0x00a9a39100000000 0x000a9a3910000000 0x01fff79380000003 0xf01fff7938000000

def z1287 : W := mkw 0x3b621f40fffffecf 0x23b621f40fffffec 0xffe00fe07fffffce 0xfffe00fe07fffffc

def z1288 : W := mkw 0x06140c0a9810d0a4 0x806140c0a9810d0a 0xde180e1ff818f0fe 0x7de180e1ff818f0f

def z1289 : W := mkw 0x4960634100000000 0x0496063410000000 0x0066760380000000 0x4006676038000000

def z1290 : W := mkw 0x0f74afdb2d40ea07 0x00f74afdb2d40ea0 0xffffffffffc0ff0f 0xfffffffffffc0ff0

def z1291 : W := mkw 0x4ffdefff00010550 0x44ffdefff0001055 0x7fffffff86008fff 0xf7fffffff86008ff

def z1292 : W := mkw 0x0dfde39125402802 0x00dfde3912540280 0xbffff793ffc07c0f 0xfbffff793ffc07c0

def z1293 : W := mkw 0x2ddf500077be0008 0x02ddf500077be000 0x2ffff0003fff0009 0xa2ffff0003fff000

def z1294 : W := mkw 0x4ffdefff00000000 0x04ffdefff0000000 0x4f9fffff80000003 0x24f9fffff8000000

def z1295 : W := mkw 0x4ffdefff00000000 0x04ffdefff0000000 0xcffffffff800000f 0xfcffffffff800000

def z1296 : W := mkw 0x2b621f40fffefaaf 0x82b621f40fffefaa 0xffe00fe07ffffffe 0xfffe00fe07ffffff

def z1297 : W := mkw 0x5220afff8841fec7 0x25220afff8841fec 0x50000fff8000ffc2 0x050000fff8000ffc

def z1298 : W := mkw 0x4ffdefff0a4def57 0x44ffdefff0a4def5 0x7fffffff863fffff 0xf7fffffff863ffff

def z1299 : W := mkw 0x10021000c0e33cc2 0x210021000c0e33cc 0xf18009e047e7ffce 0xbf18009e047e7ffc

def z1300 : W := mkw 0x00221300c0e23882 0x000221300c0e2388 0xb067f793c1e77cc7 0xdb067f793c1e77cc

def z1301 : W := mkw 0x2ddf500af7be10a8 0x82ddf500af7be10a 0xbffff61fffff70ff 0xfbffff61fffff70f

def z1302 : W := mkw 0x19621340e5e33ec3 0x219621340e5e33ec 0xb1e001e047e77fc4 0x8b1e001e047e77fc

def z1303 : W := mkw 0x1b621f40fdf3fee7 0xa1b621f40fdf3fee 0xffe00fe07ffffffe 0xfffe00fe07ffffff

def z1304 : W := mkw 0x0020230100000000 0x0002023010000000 0x0066761380000003 0x5006676138000000

def z1305 : W := mkw 0x06160c0ad830d0a4 0x806160c0ad830d0a 0xdf9e0ffff838f0ff 0xfdf9e0ffff838f0f

def z1306 : W := mkw 0x10021000c2ef3dd2 0x610021000c2ef3dd 0xb000000041ff7cf4 0x0b000000041ff7cf

def z1307 : W := mkw 0x4ddde0bf020d0550 0x44ddde0bf020d055 0x7ffff9ff863f8fff 0xf7ffff9ff863f8ff

def z1308 : W := mkw 0x4f746f4b1810c024 0x84f746f4b1810c02 0x4e7e7e0fb8188038 0x64e7e7e0fb818803

def z1309 : W := mkw 0x0020a39100000000 0x00020a3910000000 0x0066779380000002 0x4006677938000000

def z1310 : W := mkw 0x0220afd10840ea07 0x00220afd10840ea0 0x5067fff38000ff03 0xd5067fff38000ff0

def z1311 : W := mkw 0x6fdd4c6e3f1cc20d 0x06fdd4c6e3f1cc20 0x4f98086c3e188308 0x24f98086c3e18830

def z1312 : W := mkw 0x10021000c2ef3cc2 0x210021000c2ef3cc 0xb000000047ff7ccc 0x0b000000047ff7cc

def z1313 : W := mkw 0x2942100077be0008 0x02942100077be000 0xafe7f0007fff000d 0xfafe7f0007fff000

def z1314 : W := mkw 0x4ffdefff0800c205 0x04ffdefff0800c20 0x4fffffff80008303 0xf4fffffff8000830

def z1315 : W := mkw 0x30021000f5f33cca 0x230021000f5f33cc 0xb000000079e77cc4 0x0b000000079e77cc

def z1316 : W := mkw 0x0b60afd12d00c205 0x00b60afd12d00c20 0x4fe7fff3be00830b 0xf4fe7fff3be00830

def z1317 : W := mkw 0x469decff00000000 0x0469decff0000000 0x401ff87f80000001 0x0401ff87f8000000

def z1318 : W := mkw 0x4ffd6f4b00000000 0x04ffd6f4b0000000 0x4ffffe1f80000003 0xf4ffffe1f8000000

def z1319 : W := mkw 0x49e9e3f5274d2f53 0x449e9e3f5274d2f5 0x21e1f1e007c70f00 0x821e1f1e007c70f0

def z1320 : W := mkw 0x0b60afd100000000 0x00b60afd10000000 0x0e67f79380000003 0xd0e67f7938000000

def z1321 : W := mkw 0x4ffdefff2d41ee47 0x04ffdefff2d41ee4 0xffffffffffe7ffcf 0xfffffffffffe7ffc

def z1322 : W := mkw 0x06160c0ad830d0a4 0x806160c0ad830d0a 0xce1e0e1ff83870f3 0x7ce1e0e1ff83870f

def z1323 : W := mkw 0x4ffdefff020d0550 0x44ffdefff020d055 0x7fffffff86078f0f 0xf7fffffff86078f0

def z1324 : W := mkw 0x4ffdefff2d40ea07 0x04ffdefff2d40ea0 0xfffffffff9c07c07 0xffffffffff9c07c0

def z1325 : W := mkw 0x449de0bf00010550 0x4449de0bf0001055 0x501ff9ff80008ff3 0x0501ff9ff80008ff

def z1326 : W := mkw 0x06160c4ad830d2a5 0x806160c4ad830d2a 0xde1e0e7ff838f3ff 0x7de1e0e7ff838f3f

def z1327 : W := mkw 0x4f74efdb00000000 0x04f74efdb0000000 0x4fe7fff380000003 0xf4fe7fff38000000

def z1328 : W := mkw 0x449de0bf00000000 0x0449de0bf0000000 0x0e1ff01f80000001 0x70e1ff01f8000000

def z1329 : W := mkw 0x2ddf500077be0008 0x02ddf500077be000 0xaffff01c7fff00fd 0xfaffff01c7fff00f

def z1330 : W := mkw 0x2ddf500077be0008 0x02ddf500077be000 0xafe7f0007fe70005 0xdafe7f0007fe7000

def z1331 : W := mkw 0x4ffdefff00000000 0x04ffdefff0000000 0x0fe7f7f380000003 0xd0fe7f7f38000000

def z1332 : W := mkw 0x4ffdefff020d0440 0x04ffdefff020d044 0x7fffffff863f0ccf 0xf7fffffff863f0cc

def z1333 : W := mkw 0x649de0bf121c0008 0x0649de0bf121c000 0x001ff01f80180001 0x0001ff01f8018000

def z1334 : W := mkw 0x4ffdefff020d0550 0x44ffdefff020d055 0x7fffffff86270fc7 0xf7fffffff86270fc

def z1335 : W := mkw 0x2ddf500077be0008 0x02ddf500077be000 0xfffff8007fff800f 0xffffff8007fff800

def z1336 : W := mkw 0x46bdefff020d0550 0x446bdefff020d055 0x501fffff803f8ff3 0x0501fffff803f8ff

def z1337 : W := mkw 0x02021c0ac8a2d0a4 0x802021c0ac8a2d0a 0xf067fe1fc1e7f0f7 0xdf067fe1fc1e7f0f

def z1338 : W := mkw 0x4dfde3ff020d0550 0x44dfde3ff020d055 0x21fff1ff863f0ff1 0x821fff1ff863f0ff

def z1339 : W := mkw 0x0ffd4f4a00000000 0x00ffd4f4a0000000 0x4fffffff80000003 0xf4fffffff8000000

def z1340 : W := mkw 0x4f74efff00000000 0x04f74efff0000000 0x0e66761f80000000 0x40e66761f8000000

def z1341 : W := mkw 0x2ddf500077be0008 0x02ddf500077be000 0xafe7f0007fc7000c 0xfafe7f0007fc7000

def z1342 : W := mkw 0x2ddf500077be0008 0x02ddf500077be000 0xbffff0007fff8f0d 0xfbffff0007fff8f0

def z1343 : W := mkw 0x4dfde3ff00000000 0x04dfde3ff0000000 0x007ff01f80000001 0x0007ff01f8000000

def z1344 : W := mkw 0x2ddf500af7be10a8 0x82ddf500af7be10a 0xaffff003ffff000d 0xfaffff003ffff000

def z1345 : W := mkw 0x10029090ede3fec7 0x210029090ede3fec 0xf18189f07fe7ffcf 0xbf18189f07fe7ffc

def z1346 : W := mkw 0x4f746f4b00000000 0x04f746f4b0000000 0x0fe677e380000000 0xc0fe677e38000000

def z1347 : W := mkw 0x4ddde0bf25000000 0x04ddde0bf2500000 0xaffff01fffc0000d 0xfaffff01fffc0000

def z1348 : W := mkw 0x0020a39100402802 0x00020a3910040280 0x1067f79380007c03 0xd1067f79380007c0

def z1349 : W := mkw 0x4f74efff00000000 0x04f74efff0000000 0x4e7e7fff80000003 0x74e7e7fff8000000

def z1350 : W := mkw 0x4ffd6f4b2d40ea07 0x04ffd6f4b2d40ea0 0xaffff603ffc0700d 0xfaffff603ffc0700

def z1351 : W := mkw 0x4f746f4b2d00c205 0x04f746f4b2d00c20 0x4fe67e63be008308 0x64fe67e63be00830

def z1352 : W := mkw 0x2fdd4c0a3f1cc02c 0x82fdd4c0a3f1cc02 0x4ffffe1fbe18803b 0xf4ffffe1fbe18803

def z1353 : W := mkw 0x5022b3f5c0e33cc2 0x25022b3f5c0e33cc 0xb067f7f3c1e77cc7 0xdb067f7f3c1e77cc

def z1354 : W := mkw 0x3ddf5000f7ff3cca 0x23ddf5000f7ff3cc 0xbf9800007fff7ccc 0x2bf9800007fff7cc

def z1355 : W := mkw 0x4ffdefff020d0550 0x44ffdefff020d055 0x2fe7f7e386070f00 0xc2fe7f7e386070f0

def z1356 : W := mkw 0x10029090c0e33cc2 0x210029090c0e33cc 0xb001818041e77cc4 0x8b001818041e77cc

def z1357 : W := mkw 0x00a9a3b500000000 0x000a9a3b50000000 0x007ff79f80000003 0xd007ff79f8000000

def z1358 : W := mkw 0x4ffdefff2d40ea07 0x04ffdefff2d40ea0 0xefffffffffc07f03 0xfefffffffffc07f0

def z1359 : W := mkw 0x1022b391c0e33cc2 0x21022b391c0e33cc 0xa067f613c1e770c5 0xda067f613c1e770c

def z1360 : W := mkw 0x0f544c0a00000000 0x00f544c0a0000000 0x4e7e7e1f80000003 0x74e7e7e1f8000000

def z1361 : W := mkw 0x4fddecbf00000000 0x04fddecbf0000000 0x4ffffe1f80000003 0xf4ffffe1f8000000

def z1362 : W := mkw 0x5220afff8841fce6 0xa5220afff8841fce 0x50000fff8000fcf2 0x050000fff8000fcf

def z1363 : W := mkw 0x4ffdefff020d0550 0x44ffdefff020d055 0x7fffffff803f0cf7 0xf7fffffff803f0cf

def z1364 : W := mkw 0x30021000d2ff3cca 0x230021000d2ff3cc 0xb000000041ff7cc4 0x0b000000041ff7cc

def z1365 : W := mkw 0x4ffdefff00000000 0x04ffdefff0000000 0x0ffff61f80000001 0xf0ffff61f8000000

def z1366 : W := mkw 0x0b600f402d40ea07 0x00b600f402d40ea0 0xffe60ff3ffc0ff0f 0xfffe60ff3ffc0ff0

def z1367 : W := mkw 0x308b90b4f7ff3dda 0x6308b90b4f7ff3dd 0xf19989fc7fffffff 0xbf19989fc7ffffff

def z1368 : W := mkw 0x1220af9b8841fce6 0xa1220af9b8841fce 0x1000079380007cc2 0x01000079380007cc

def z1369 : W := mkw 0x1022b391c0e33dd2 0x61022b391c0e33dd 0xb067f793c1e7fff7 0xdb067f793c1e7fff

def z1370 : W := mkw 0x4ffdefff020c0110 0x44ffdefff020c011 0x7fffffff86188f3f 0xf7fffffff86188f3

def z1371 : W := mkw 0x2dfde391371c0008 0x02dfde391371c000 0x0ffff793be18000b 0xf0ffff793be18000

def z1372 : W := mkw 0x008980b4020d0550 0x4008980b4020d055 0x719989ec063f8ffc 0xa719989ec063f8ff

def z1373 : W := mkw 0x6fdd4c6e3f1cc02c 0x86fdd4c6e3f1cc02 0x4f98086c3e188038 0x24f98086c3e18803

def z1374 : W := mkw 0x1022b391c0e33cc2 0x21022b391c0e33cc 0xb067f793c7e7ffcf 0xdb067f793c7e7ffc

def z1375 : W := mkw 0x4ffdefff1810c024 0x84ffdefff1810c02 0xdffffffff818f03f 0xfdffffffff818f03

def z1376 : W := mkw 0x0fdd4c0a2d00c004 0x00fdd4c0a2d00c00 0xfffffe1fffc0f00f 0xffffffe1fffc0f00

def z1377 : W := mkw 0x06140c0a00000000 0x006140c0a0000000 0x4e7ffe1f80000003 0xf4e7ffe1f8000000

def z1378 : W := mkw 0x4be9efff00000000 0x04be9efff0000000 0x41e7ffff80000003 0xd41e7ffff8000000

def z1379 : W := mkw 0x4ffdefff020c0000 0x04ffdefff020c000 0x7fffffff863f80ff 0xf7fffffff863f80f

def z1380 : W := mkw 0x2ddf502477be0118 0x42ddf502477be011 0xfffff9ec7fff8f3f 0xffffff9ec7fff8f3

def z1381 : W := mkw 0x06160c0ad830d0a4 0x806160c0ad830d0a 0xfe1e0e1ffe38ffff 0x7fe1e0e1ffe38fff

def z1382 : W := mkw 0x4fddecff00000000 0x04fddecff0000000 0x4f9ff9ff80000003 0xb4f9ff9ff8000000

def z1383 : W := mkw 0x469decbf0800c004 0x0469decbf0800c00 0xde1ffe1ff800f00f 0x7de1ffe1ff800f00

def z1384 : W := mkw 0x0020a39100000000 0x00020a3910000000 0x507fff9f803880ff 0xf507fff9f803880f

def z1385 : W := mkw 0x6ffdefff35100008 0x06ffdefff3510000 0x4fffffffb8000003 0xf4fffffffb800000

def z1386 : W := mkw 0x10029090c0e33cc2 0x210029090c0e33cc 0xb001801041e77cc5 0x0b001801041e77cc

def z1387 : W := mkw 0x00a9a3b5020d0550 0x400a9a3b5020d055 0x007ff79f803f00f3 0xd007ff79f803f00f

def z1388 : W := mkw 0x4ffdefff25000000 0x04ffdefff2500000 0xffffffffffc08f0f 0xfffffffffffc08f0

def z1389 : W := mkw 0x0000a09100010440 0x00000a0910001044 0x3007f19380270cc7 0x93007f19380270cc

def z1390 : W := mkw 0x0020a39100000000 0x00020a3910000000 0x3067f79380000c07 0xd3067f79380000c0

def z1391 : W := mkw 0x0b600f402d40ea07 0x00b600f402d40ea0 0xffe00fe07fc0ff02 0xcffe00fe07fc0ff0

def z1392 : W := mkw 0x4ffdefff2f4cea07 0x04ffdefff2f4cea0 0xffffffffffffff0f 0xfffffffffffffff0

def z1393 : W := mkw 0x4f746f4b00000000 0x04f746f4b0000000 0x4fe67e6380000000 0x64fe67e638000000

def z1394 : W := mkw 0x0ddde09100000000 0x00ddde0910000000 0x0ffff01380000001 0xf0ffff0138000000

def z1395 : W := mkw 0x4f746f4b2d40ea07 0x04f746f4b2d40ea0 0xfffe7fffffc0ff0f 0xffffe7fffffc0ff0

def z1396 : W := mkw 0x0fdd4c0a020c0000 0x00fdd4c0a020c000 0x7ffffe1f863f80ff 0xf7ffffe1f863f80f

def z1397 : W := mkw 0x4ffd6f6f00000000 0x04ffd6f6f0000000 0x0fe6766380000000 0x40fe676638000000

def z1398 : W := mkw 0x42a9afff00000000 0x042a9afff0000000 0x41ffffff80000003 0xf41ffffff8000000

def z1399 : W := mkw 0x4ffdefff25402a03 0x04ffdefff25402a0 0xffffffffc7c07f07 0xfffffffffc7c07f0

def z1400 : W := mkw 0x0020a39100000000 0x00020a3910000000 0x9067f793c0007007 0xd9067f793c000700

def z1401 : W := mkw 0x00a9a3b5020c0110 0x400a9a3b5020c011 0x41ffffff8618833b 0xf41ffffff8618833

def z1402 : W := mkw 0x4f746f4b00000000 0x04f746f4b0000000 0x0e66778380000002 0xd0e6677838000000

def z1403 : W := mkw 0x00a9a391020c0000 0x000a9a391020c000 0x21fff793863f000f 0xf21fff793863f000

def z1404 : W := mkw 0x0fdd4c0a00000000 0x00fdd4c0a0000000 0x0ffff60380000001 0xf0ffff6038000000

def z1405 : W := mkw 0x10221300c2ef3dd2 0x610221300c2ef3dd 0xf1e00fe047fffffe 0xff1e00fe047fffff

def z1406 : W := mkw 0x10223301c0e33cc2 0x210223301c0e33cc 0xb067f603c1e77cc5 0xdb067f603c1e77cc

def z1407 : W := mkw 0x0b600f402d40ea07 0x00b600f402d40ea0 0xffe00fe07ff8fffe 0xfffe00fe07ff8fff

def z1408 : W := mkw 0x449de0bf00000000 0x0449de0bf0000000 0x501ff81f803880ff 0x3501ff81f803880f

def z1409 : W := mkw 0x4ffdefff0840e806 0x04ffdefff0840e80 0xfffffffff9c0fc0f 0xffffffffff9c0fc0

def z1410 : W := mkw 0x0220af910800c004 0x00220af910800c00 0xde67ff93f800f00f 0xfde67ff93f800f00

def z1411 : W := mkw 0x4ffdefff274d2f53 0x44ffdefff274d2f5 0x6fffffff87c70f03 0xf6fffffff87c70f0

def z1412 : W := mkw 0x6ffdefff121c0008 0x06ffdefff121c000 0x4fffffff80180003 0xf4fffffff8018000

def z1413 : W := mkw 0x20021000fdb2d0ac 0x820021000fdb2d0a 0x8000000079c07000 0x08000000079c0700

def z1414 : W := mkw 0x46bdefff020d0550 0x446bdefff020d055 0x719fffff863f8fff 0xb719fffff863f8ff

def z1415 : W := mkw 0x4ffdefff0800c004 0x04ffdefff0800c00 0xfffffffffe00ff0f 0xffffffffffe00ff0

def z1416 : W := mkw 0x4ffdefff25402a03 0x04ffdefff25402a0 0x7fffffff87c08f0f 0xf7fffffff87c08f0

def z1417 : W := mkw 0x20021000ffbed0ac 0x820021000ffbed0a 0xa00000007fff700c 0x0a00000007fff700

def z1418 : W := mkw 0x0fddccbe020d0550 0x40fddccbe020d055 0x7fffffff863f8fff 0xf7fffffff863f8ff

def z1419 : W := mkw 0x4ffdefff25000000 0x04ffdefff2500000 0x6fffffff87c00003 0xf6fffffff87c0000

def z1420 : W := mkw 0x10021000d0f33cc2 0x210021000d0f33cc 0xb000000079ff7ccc 0x0b000000079ff7cc

def z1421 : W := mkw 0x0b600f402d40ea07 0x00b600f402d40ea0 0xafe007e07fc07f0c 0xfafe007e07fc07f0

def z1422 : W := mkw 0x1022b391c0e33cc2 0x21022b391c0e33cc 0xf1ffffffc7ffffff 0xff1ffffffc7fffff

def z1423 : W := mkw 0x44bde3bf00000000 0x044bde3bf0000000 0x001ff79f80000003 0x0001ff79f8000000

def z1424 : W := mkw 0x4ffdefff00000000 0x04ffdefff0000000 0x0ffff7ff80000001 0xc0ffff7ff8000000

def z1425 : W := mkw 0x349ff0b5d2bf15d8 0x6349ff0b5d2bf15d 0x001ff01f803f00f1 0x0001ff01f803f00f

def z1426 : W := mkw 0x10021000d8f2f8a6 0xa10021000d8f2f8a 0x9000000079f8f0fc 0x09000000079f8f0f

def z1427 : W := mkw 0x1022b391c0e33cc2 0x21022b391c0e33cc 0xa067f793c1e77cc1 0xca067f793c1e77cc

def z1428 : W := mkw 0x10021000c2ef3dd2 0x610021000c2ef3dd 0xb000000047e77fc4 0x0b000000047e77fc

def z1429 : W := mkw 0x4ffdefff00402a03 0x04ffdefff00402a0 0x4fffffff80000f03 0xf4fffffff80000f0

def z1430 : W := mkw 0x4f74efff00000000 0x04f74efff0000000 0x4fe67fff80000002 0xf4fe67fff8000000

def z1431 : W := mkw 0x4ffdefff020d0550 0x44ffdefff020d055 0x5fffffff86188ffb 0xf5fffffff86188ff

def z1432 : W := mkw 0x4dfde3f500000000 0x04dfde3f50000000 0x0ffff7f380000003 0xf0ffff7f38000000

def z1433 : W := mkw 0x4ffd6f4b00000000 0x04ffd6f4b0000000 0x0fe7f60380000000 0xc0fe7f6038000000

def z1434 : W := mkw 0x4ffdefff020d0550 0x44ffdefff020d055 0x6fffffff863f00ff 0xf6fffffff863f00f

def z1435 : W := mkw 0x4dfde3ff00000000 0x04dfde3ff0000000 0x41fff9ff80000003 0xb41fff9ff8000000

def z1436 : W := mkw 0x30021000f7bf14c8 0x230021000f7bf14c 0xa00000007fff00cc 0x0a00000007fff00c

def z1437 : W := mkw 0x4ffd6f4b00000000 0x04ffd6f4b0000000 0x0e7ff60380000001 0x40e7ff6038000000

def z1438 : W := mkw 0x00a9a3b500000000 0x000a9a3b50000000 0x01e7f7f380000003 0xd01e7f7f38000000

def z1439 : W := mkw 0x0020230100000000 0x0002023010000000 0x0066778380000002 0xd006677838000000

def z1440 : W := mkw 0x10021000ede2fa87 0x210021000ede2fa8 0x8000000079c07000 0x08000000079c0700

def z1441 : W := mkw 0x4ffdefff00000000 0x04ffdefff0000000 0x7fffffff86388fff 0xf7fffffff86388ff

def z1442 : W := mkw 0x449de0bf020c0110 0x4449de0bf020c011 0x419ff87f86188339 0x2419ff87f8618833

def z1443 : W := mkw 0x10021000ede3fec7 0x210021000ede3fec 0xb000000079e77cc4 0x0b000000079e77cc

def z1444 : W := mkw 0x4ffd6f6f020c0110 0x44ffd6f6f020c011 0x4ffe7e6f86188338 0x64ffe7e6f8618833

def z1445 : W := mkw 0x0b602f4100000000 0x00b602f410000000 0x4fe67fe380000002 0xf4fe67fe38000000

def z1446 : W := mkw 0x4414e0bf00000000 0x04414e0bf0000000 0x0006701f80000000 0x00006701f8000000

def z1447 : W := mkw 0x4f746f4b00000000 0x04f746f4b0000000 0x4e667e0380000002 0x74e667e038000000

def z1448 : W := mkw 0x10021000c8e3fec7 0x210021000c8e3fec 0xb000000041e7ffc4 0x0b000000041e7ffc

def z1449 : W := mkw 0x06160c0ad830d0a4 0x806160c0ad830d0a 0xfe1f8e1ff83ff0ff 0xffe1f8e1ff83ff0f

def z1450 : W := mkw 0x46146c0b00000000 0x046146c0b0000000 0x0e06760380000000 0x40e0676038000000

def z1451 : W := mkw 0x4434e39b00000000 0x04434e39b0000000 0x0067f79380000003 0xd0067f7938000000

def z1452 : W := mkw 0x0416100050b20000 0x00416100050b2000 0xae67f00079e70005 0xdae67f00079e7000

def z1453 : W := mkw 0x449d600b00000000 0x0449d600b0000000 0x001ff00380000001 0x0001ff0038000000

def z1454 : W := mkw 0x4ffdefff0840ea07 0x04ffdefff0840ea0 0x7fffffff8600ff0f 0xf7fffffff8600ff0

def z1455 : W := mkw 0x02000c0a8800d0a4 0x802000c0a8800d0a 0xde180e1ff838f0ff 0x7de180e1ff838f0f

def z1456 : W := mkw 0x4ffdefff2d00c205 0x04ffdefff2d00c20 0x7fffffffbe008f0f 0xf7fffffffbe008f0

def z1457 : W := mkw 0x1b621f40efefffd7 0x61b621f40efefffd 0xffe00fe07ffffffe 0xfffe00fe07ffffff

def z1458 : W := mkw 0x2fdd4c0a3f1cc02c 0x82fdd4c0a3f1cc02 0x0f9800003e180008 0x20f9800003e18000

def z1459 : W := mkw 0x4f746f4b1810c024 0x84f746f4b1810c02 0x0e667603b8000000 0x40e667603b800000

def z1460 : W := mkw 0x0089a0b500000000 0x00089a0b50000000 0x419ff9ff80000003 0xb419ff9ff8000000

def z1461 : W := mkw 0x0b600f402d40ea07 0x00b600f402d40ea0 0xfff80fe07ff8ff0f 0xffff80fe07ff8ff0

def z1462 : W := mkw 0x29cb500077be0008 0x029cb500077be000 0xafe1f0007fff000c 0xfafe1f0007fff000

def z1463 : W := mkw 0x09e9e39100000000 0x009e9e3910000000 0x01e7f79380000003 0xd01e7f7938000000

def z1464 : W := mkw 0x4ffdefff00412c42 0x04ffdefff00412c4 0xffffffffc1e77cc7 0xfffffffffc1e77cc

def z1465 : W := mkw 0x30021000f7fe388a 0x230021000f7fe388 0xa00000007fff700c 0x0a00000007fff700

def z1466 : W := mkw 0x449de0bf00000000 0x0449de0bf0000000 0x019ff01f80000001 0xb019ff01f8000000

def z1467 : W := mkw 0x2ddf500077be0008 0x02ddf500077be000 0xafe7f0007fff000c 0xcafe7f0007fff000

def z1468 : W := mkw 0x4ffdefff020c0000 0x04ffdefff020c000 0x7fffffff863f8f0f 0xf7fffffff863f8f0

def z1469 : W := mkw 0x06342f0b00000000 0x006342f0b0000000 0x4e7e7e1f80000003 0x74e7e7e1f8000000

def z1470 : W := mkw 0x4220afff00000000 0x04220afff0000000 0x4007ffff80000003 0x04007ffff8000000

def z1471 : W := mkw 0x4ffdefff00000000 0x04ffdefff0000000 0x4ffffe7f80000001 0x64ffffe7f8000000

def z1472 : W := mkw 0x4ffdefff00402802 0x04ffdefff0040280 0xffffffffc7c0ff0f 0xfffffffffc7c0ff0

def z1473 : W := mkw 0x6ffdefff371d0558 0x46ffdefff371d055 0x7fffffffbe3f8fff 0xf7fffffffbe3f8ff

def z1474 : W := mkw 0x49e9e3f500000000 0x049e9e3f50000000 0x41ffffff80000003 0xf41ffffff8000000

def z1475 : W := mkw 0x44bde3bf020d0550 0x444bde3bf020d055 0x307ff79f803f0cf7 0xd307ff79f803f0cf

def z1476 : W := mkw 0x30021000e7ef3cca 0x230021000e7ef3cc 0xb000000047e77cc4 0x0b000000047e77cc

def z1477 : W := mkw 0x2ddf500077be0008 0x02ddf500077be000 0xeffff81c7fff000f 0xfeffff81c7fff000

def z1478 : W := mkw 0x4f74efdb00000000 0x04f74efdb0000000 0x4e7fff9f80000003 0xf4e7fff9f8000000

def z1479 : W := mkw 0x4ffdefff00000000 0x04ffdefff0000000 0x0e7ff79f80000003 0xd0e7ff79f8000000

def z1480 : W := mkw 0x0b600f402d40ea07 0x00b600f402d40ea0 0xffe18fe07fe7ff0f 0xfffe18fe07fe7ff0

def z1481 : W := mkw 0x100290b4c0e33dd2 0x6100290b4c0e33dd 0xf00009fc41e7fff6 0x0f00009fc41e7fff

def z1482 : W := mkw 0x12021c00c8e3fcc6 0x212021c00c8e3fcc 0xfe000e0079e7fcce 0x7fe000e0079e7fcc

def z1483 : W := mkw 0x108b90b4c2af15d0 0x6108b90b4c2af15d 0x0019801c003f00f1 0x00019801c003f00f

def z1484 : W := mkw 0x1022b3b5c0e33dd2 0x61022b3b5c0e33dd 0xb067f79fc1e77cf7 0xdb067f79fc1e77cf

def z1485 : W := mkw 0x0b60afd12d41ee47 0x00b60afd12d41ee4 0xffe7fff3ffe7ffcf 0xfffe7fff3ffe7ffc

def z1486 : W := mkw 0x06160c0ad830d0a4 0x806160c0ad830d0a 0x9e1e061ff838f0fd 0x49e1e061ff838f0f

def z1487 : W := mkw 0x049de09100000000 0x0049de0910000000 0x001ff01380000001 0x0001ff0138000000

def z1488 : W := mkw 0x4ffdefff0800c004 0x04ffdefff0800c00 0x5fffffff8000f003 0xf5fffffff8000f00

def z1489 : W := mkw 0x2fdf5c0affbed0ac 0x82fdf5c0affbed0a 0xff98080c7ffff0fc 0x2ff98080c7ffff0f

def z1490 : W := mkw 0x42a9afff020d0550 0x442a9afff020d055 0x71ffffff863f8fff 0xf71ffffff863f8ff

def z1491 : W := mkw 0x2ddf500077be0008 0x02ddf500077be000 0xaffff0007fc70001 0xfaffff0007fc7000

def z1492 : W := mkw 0x06bdafbf00000000 0x006bdafbf0000000 0x4fffffff80000003 0xf4fffffff8000000

def z1493 : W := mkw 0x4f74efdb2d40ea07 0x04f74efdb2d40ea0 0xffe7fff3ffc0ff0f 0xfffe7fff3ffc0ff0

def z1494 : W := mkw 0x6ddde0bf371c0008 0x06ddde0bf371c000 0x0f9ff01fbe180009 0x20f9ff01fbe18000

def z1495 : W := mkw 0x0634af9b1810c024 0x80634af9b1810c02 0x4e7fff9fb818803b 0xf4e7fff9fb818803

def z1496 : W := mkw 0x4ffdefff1810c024 0x84ffdefff1810c02 0x5fffffffb83880ff 0xf5fffffffb83880f

def z1497 : W := mkw 0x4ffdefff1a1cc134 0xc4ffdefff1a1cc13 0x4fffffffbe18833b 0xf4fffffffbe18833

def z1498 : W := mkw 0x449de0bf00000000 0x0449de0bf0000000 0x001ff19f80000003 0x9001ff19f8000000

def z1499 : W := mkw 0x10021000c0e33cc2 0x210021000c0e33cc 0xb067f613c1e77cc7 0xdb067f613c1e77cc

def z1500 : W := mkw 0x4ffdefff00010440 0x04ffdefff0001044 0x7fffffff86278fcf 0xf7fffffff86278fc

def z1501 : W := mkw 0x1220afd10841ee47 0x21220afd10841ee4 0x50000fe00000ff02 0x050000fe00000ff0

def z1502 : W := mkw 0x06160c0ad830d0a4 0x806160c0ad830d0a 0xfe1e0f9ff838fcff 0xffe1e0f9ff838fcf

def z1503 : W := mkw 0x4ffdefff00000000 0x04ffdefff0000000 0x7fffffff80000c07 0xf7fffffff80000c0

def z1504 : W := mkw 0x4ffdefff2d40ea07 0x04ffdefff2d40ea0 0xefffffffffc0700f 0xfefffffffffc0700

def z1505 : W := mkw 0x2ddf500077be0008 0x02ddf500077be000 0xeffff80c7fff803d 0xfeffff80c7fff803

def z1506 : W := mkw 0x20021000ffbfd5fc 0xc20021000ffbfd5f 0xb00000007ffffffc 0x0b00000007ffffff

def z1507 : W := mkw 0x1022b391c0e33cc2 0x21022b391c0e33cc 0xa067f793c1c77c03 0xda067f793c1c77c0

def z1508 : W := mkw 0x4f746f4b2d40ea07 0x04f746f4b2d40ea0 0xbe667603ffc0ff0c 0x4be667603ffc0ff0

def z1509 : W := mkw 0x0434a39100000000 0x00434a3910000000 0x0e7ff79380000003 0xf0e7ff7938000000

def z1510 : W := mkw 0x4434630b00000000 0x04434630b0000000 0x0066760380000000 0x4006676038000000

def z1511 : W := mkw 0x10021000d8b3d4e4 0xa10021000d8b3d4e 0x90000000783ff0fc 0x090000000783ff0f

def z1512 : W := mkw 0x06160c0ad830d0a4 0x806160c0ad830d0a 0xde1e0e1ff838f0f3 0x4de1e0e1ff838f0f

def z1513 : W := mkw 0x1022b391c0e33cc2 0x21022b391c0e33cc 0x8067f793c1e770c3 0xd8067f793c1e770c

def z1514 : W := mkw 0x4ffdefff020c0000 0x04ffdefff020c000 0x6fffffff86070003 0xf6fffffff8607000

def z1515 : W := mkw 0x10021000efefffd7 0x610021000efefffd 0xb00000007ffffffc 0x0b00000007ffffff

def z1516 : W := mkw 0x0020a39100000000 0x00020a3910000000 0x2067f79380270007 0xd2067f7938027000

def z1517 : W := mkw 0x4f746f4b00000000 0x04f746f4b0000000 0x4e667fe380000002 0x44e667fe38000000

def z1518 : W := mkw 0x4ffdefff00010440 0x04ffdefff0001044 0x7fffffff803f8cff 0xf7fffffff803f8cf

def z1519 : W := mkw 0x4ffdefff270c0000 0x04ffdefff270c000 0xefffffffffff000f 0xfefffffffffff000

def z1520 : W := mkw 0x4ffdefff020d0550 0x44ffdefff020d055 0x6fffffff861f8f3b 0xf6fffffff861f8f3

def z1521 : W := mkw 0x06160c0ad830d0a4 0x806160c0ad830d0a 0xde1e0ffff838ffff 0x7de1e0ffff838fff

def z1522 : W := mkw 0x06161c0ad8b2d0a4 0x806161c0ad8b2d0a 0xde7e7e1ff9f8f0ff 0x7de7e7e1ff9f8f0f

def z1523 : W := mkw 0x4ffdefff00010550 0x44ffdefff0001055 0x7fffffff80278ff7 0xf7fffffff80278ff

def z1524 : W := mkw 0x4f74efdb00010440 0x04f74efdb0001044 0x3e67f79380270cc7 0xd3e67f79380270cc

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z7,z0,z1,z3,z4,z5,z6]),(0,[z8,z0,z1,z3,z4,z5,z9]),(0,[z0,z1,z10,z11,z4,z5,z6]),(1,[z0,z1,z3,z12,z13,z6]),(0,[z14,z0,z1,z3,z12,z4,z5])],[(0,[z15,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z16,z4,z5,z6]),(0,[z0,z1,z3,z4,z17,z5,z6]),(0,[z18,z14,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z19,z20,z4,z5])],[(0,[z21,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z22,z5,z6]),(0,[z23,z14,z0,z1,z3,z4,z5]),(0,[z24,z0,z1,z3,z4,z5,z6]),(0,[z25,z0,z1,z3,z4,z5,z26]),(0,[z14,z0,z1,z3,z4,z27,z5]),(0,[z0,z1,z3,z28,z4,z5,z6]),(0,[z29,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z30,z4,z5,z6]),(0,[z0,z1,z31,z3,z4,z5,z32]),(0,[z0,z1,z3,z4,z5,z33,z6]),(0,[z0,z1,z34,z3,z4,z5,z6]),(0,[z35,z0,z1,z3,z4,z5,z6])],[(0,[z0,z36,z1,z3,z4,z5,z6]),(0,[z37,z0,z1,z3,z4,z5,z9]),(0,[z0,z1,z3,z4,z5,z26,z38]),(0,[z0,z1,z3,z11,z4,z5,z39]),(0,[z40,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z41,z6]),(0,[z0,z1,z10,z3,z4,z5,z42]),(0,[z43,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z44,z5,z6]),(1,[z0,z1,z3,z4,z45,z46])],[(0,[z0,z1,z3,z4,z5,z32,z6]),(0,[z14,z0,z1,z3,z4,z47,z5]),(0,[z0,z1,z48,z3,z4,z5,z6]),(0,[z18,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z20,z4,z5,z49]),(0,[z0,z1,z3,z50,z4,z5,z6])],[(0,[z23,z0,z1,z3,z4,z5,z6]),(0,[z51,z0,z1,z52,z4,z5,z6]),(0,[z0,z53,z1,z3,z4,z5,z26]),(0,[z0,z1,z3,z4,z5,z54,z26]),(0,[z0,z1,z3,z4,z5,z39,z55]),(0,[z0,z1,z3,z4,z5,z56,z39]),(0,[z57,z0,z1,z3,z4,z5,z6]),(0,[z0,z58,z1,z3,z4,z5,z6]),(0,[z59,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z60,z4,z5,z6]),(0,[z0,z1,z3,z12,z4,z5,z9]),(0,[z18,z0,z1,z3,z12,z5,z6]),(1,[z0,z1,z3,z61,z4,z5]),(0,[z0,z1,z3,z61,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z38]),(0,[z62,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z63,z56]),(0,[z0,z64,z1,z3,z4,z5,z39]),(0,[z0,z65,z3,z4,z5,z6,z66]),(0,[z0,z67,z1,z3,z4,z5,z6])]],
   [[(0,[z0,z68,z1,z3,z4,z5,z6]),(0,[z8,z0,z1,z4,z69,z5,z6]),(0,[z0,z1,z3,z4,z70,z5,z56]),(0,[z0,z1,z3,z4,z5,z71,z6]),(0,[z72,z14,z0,z1,z3,z4,z5])],[(0,[z0,z1,z73,z3,z4,z5,z39]),(0,[z0,z1,z3,z4,z5,z74,z26]),(0,[z0,z64,z1,z3,z20,z4,z5]),(0,[z0,z1,z75,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z76,z6]),(0,[z0,z1,z3,z77,z4,z5,z6])],[(0,[z0,z1,z3,z4,z78,z5,z6]),(1,[z0,z1,z3,z4,z5,z79]),(0,[z0,z1,z80,z3,z4,z5,z6]),(0,[z0,z1,z3,z81,z4,z5,z6])],[(0,[z0,z1,z73,z3,z20,z4,z5]),(0,[z0,z1,z3,z11,z4,z5,z26]),(0,[z82,z0,z1,z3,z20,z4,z5]),(0,[z0,z1,z3,z4,z83,z5,z6]),(0,[z84,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z85,z3,z4,z5,z6]),(0,[z86,z14,z0,z1,z3,z4,z5]),(0,[z87,z0,z1,z3,z4,z5,z6]),(0,[z0,z88,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z27,z13,z6])],[(0,[z0,z1,z73,z3,z4,z5,z89]),(0,[z0,z1,z3,z4,z5,z56,z26]),(0,[z0,z1,z90,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z91]),(0,[z0,z1,z3,z4,z5,z6,z92])],[(0,[z51,z0,z1,z3,z4,z5,z9]),(0,[z93,z0,z1,z3,z4,z5,z94]),(0,[z0,z64,z1,z3,z4,z5,z26]),(0,[z8,z0,z1,z3,z20,z4,z5]),(0,[z18,z0,z1,z3,z4,z5,z56])],[(0,[z23,z0,z1,z3,z4,z5,z56]),(0,[z93,z0,z1,z3,z4,z5,z56]),(0,[z95,z0,z1,z3,z4,z5,z96]),(1,[z0,z1,z3,z4,z5,z97]),(0,[z0,z58,z1,z3,z4,z5,z56]),(0,[z98,z0,z1,z3,z4,z5,z6])]],
   [[(0,[z0,z1,z3,z4,z5,z99,z6]),(0,[z0,z1,z73,z3,z4,z5,z26]),(0,[z37,z0,z1,z3,z4,z5,z39]),(0,[z0,z1,z100,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z9,z101])],[(1,[z0,z1,z102,z4,z5,z6]),(0,[z0,z1,z3,z103,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z9,z104])],[(0,[z0,z1,z3,z4,z105,z5,z6]),(0,[z0,z1,z3,z106,z4,z5,z6]),(0,[z37,z0,z1,z3,z20,z4,z5]),(0,[z0,z1,z3,z12,z4,z5,z39]),(0,[z0,z1,z3,z4,z107,z5,z6]),(0,[z0,z1,z3,z4,z108,z5,z6]),(0,[z0,z1,z3,z77,z4,z5,z56])],[(0,[z0,z1,z3,z20,z4,z109,z5]),(0,[z0,z1,z3,z4,z5,z6,z9])],[(1,[z0,z1,z3,z110,z5,z6]),(1,[z0,z1,z3,z111,z4,z5]),(0,[z14,z0,z1,z3,z4,z5,z63]),(0,[z0,z1,z3,z4,z5,z112,z9]),(0,[z0,z1,z3,z4,z5,z56,z66]),(0,[z0,z113,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z114,z6]),(0,[z0,z1,z3,z115,z4,z5,z6])],[(0,[z0,z1,z31,z73,z4,z5,z6]),(0,[z0,z116,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z45,z5,z9])],[(0,[z0,z117,z3,z4,z47,z5,z6]),(0,[z118,z0,z1,z3,z4,z5,z6])],[(0,[z37,z0,z1,z3,z4,z5,z26]),(0,[z0,z1,z3,z4,z5,z26,z119]),(0,[z0,z1,z3,z4,z5,z120,z6]),(0,[z14,z0,z1,z3,z4,z5,z38])]],
   [[(0,[z0,z1,z121,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z55]),(0,[z0,z1,z3,z4,z122,z5,z6]),(0,[z0,z1,z3,z4,z5,z56,z123]),(1,[z18,z0,z1,z3,z49,z6])],[(0,[z95,z0,z1,z3,z4,z124,z6]),(0,[z86,z0,z1,z3,z4,z5,z56]),(0,[z0,z1,z3,z12,z4,z5,z26]),(0,[z18,z0,z64,z1,z3,z4,z6]),(0,[z0,z1,z3,z125,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z126,z6]),(0,[z0,z53,z1,z3,z4,z127,z6]),(0,[z0,z1,z3,z20,z4,z5,z74])],[(0,[z128,z0,z1,z3,z4,z5,z39]),(0,[z51,z0,z1,z3,z4,z5,z39]),(0,[z0,z64,z1,z3,z12,z4,z6])],[(1,[z0,z129,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z130])],[(0,[z51,z0,z1,z3,z20,z4,z5]),(0,[z0,z131,z1,z3,z4,z5,z6]),(0,[z0,z132,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z133,z6]),(0,[z82,z0,z1,z3,z4,z134,z6]),(0,[z0,z64,z1,z3,z4,z27,z6]),(0,[z135,z0,z1,z3,z4,z5,z6]),(0,[z136,z14,z0,z1,z3,z4,z5])],[(0,[z0,z1,z3,z4,z137,z5,z6]),(0,[z0,z65,z1,z3,z77,z4,z5]),(0,[z0,z1,z3,z4,z5,z138,z6]),(0,[z0,z1,z3,z20,z11,z4,z5]),(0,[z0,z1,z3,z4,z139,z5,z6]),(0,[z0,z1,z3,z4,z5,z114,z56])],[(0,[z0,z1,z3,z4,z5,z140,z6]),(0,[z0,z1,z3,z141,z109,z5,z6]),(0,[z0,z0,z1,z3,z4,z5,z39]),(0,[z0,z1,z3,z141,z4,z5,z9]),(0,[z0,z1,z3,z20,z141,z4,z5]),(0,[z142,z0,z1,z3,z4,z5,z9]),(0,[z0,z1,z10,z3,z69,z5,z6]),(0,[z0,z143,z1,z3,z4,z5,z6]),(0,[z144,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z145,z4,z5,z6]),(0,[z0,z1,z3,z4,z13,z5,z56])],[(0,[z0,z146,z1,z3,z4,z5,z39]),(0,[z82,z0,z1,z3,z13,z5,z6]),(0,[z0,z1,z3,z4,z5,z56,z147]),(0,[z0,z1,z3,z20,z4,z4,z5])]],
   [[(0,[z0,z1,z3,z4,z5,z148,z26]),(0,[z0,z149,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z20,z12,z4,z5])],[(0,[z128,z0,z1,z3,z4,z5,z26]),(0,[z51,z0,z1,z3,z4,z5,z26]),(0,[z0,z150,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z151,z5,z6]),(1,[z0,z1,z10,z11,z5,z6])],[(0,[z0,z1,z3,z4,z5,z152,z6]),(0,[z0,z1,z3,z153,z4,z5,z6]),(0,[z0,z1,z3,z20,z4,z27,z5]),(0,[z8,z0,z1,z3,z4,z5,z154]),(1,[z0,z1,z3,z4,z5,z155]),(0,[z0,z1,z3,z4,z5,z156,z9])],[(0,[z0,z1,z3,z4,z5,z6,z89]),(0,[z0,z1,z3,z157,z4,z5,z9]),(0,[z0,z158,z1,z3,z4,z5,z26]),(0,[z0,z1,z3,z159,z4,z5,z6]),(0,[z0,z1,z160,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z161,z5,z6]),(0,[z162,z0,z1,z3,z4,z5,z56]),(0,[z163,z0,z1,z3,z20,z4,z5]),(0,[z0,z164,z1,z3,z4,z5,z6]),(0,[z165,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z26,z26]),(0,[z0,z1,z3,z4,z5,z166,z39]),(0,[z0,z1,z3,z167,z4,z5,z6]),(1,[z142,z0,z3,z4,z5,z54]),(0,[z0,z168,z1,z3,z4,z5,z6]),(0,[z14,z0,z1,z3,z4,z5,z9]),(0,[z169,z14,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z170,z6])],[(0,[z0,z171,z1,z3,z4,z5,z39]),(0,[z0,z1,z172,z3,z4,z5,z6]),(0,[z173,z0,z1,z3,z4,z5,z6]),(0,[z0,z0,z1,z3,z4,z5,z26]),(0,[z0,z1,z31,z3,z4,z5,z174]),(0,[z0,z1,z3,z20,z4,z47,z5]),(0,[z0,z1,z3,z4,z5,z175,z6]),(0,[z0,z1,z176,z3,z4,z5,z6])],[(0,[z0,z146,z1,z3,z4,z5,z26]),(1,[z0,z1,z3,z177,z4,z5]),(0,[z0,z1,z3,z178,z4,z5,z6])],[(0,[z0,z1,z3,z4,z179,z5,z6]),(0,[z0,z180,z1,z3,z4,z5,z6]),(0,[z0,z1,z181,z3,z4,z5,z6]),(0,[z25,z1,z3,z4,z5,z39,z6]),(0,[z0,z1,z3,z4,z182,z5,z6]),(0,[z0,z183,z1,z3,z4,z5,z6]),(0,[z184,z0,z1,z185,z4,z5,z6]),(0,[z0,z1,z3,z4,z186,z5,z6]),(0,[z187,z0,z1,z3,z4,z5,z6])]],
   [[(0,[z169,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z188,z6]),(0,[z189,z0,z1,z3,z5,z112,z6]),(0,[z0,z1,z3,z4,z190,z5,z6]),(1,[z0,z1,z3,z191,z4,z5]),(0,[z0,z1,z3,z12,z13,z5,z6])],[(1,[z0,z1,z3,z4,z5,z192]),(1,[z0,z1,z3,z4,z5,z193]),(0,[z194,z0,z1,z3,z157,z5,z6]),(0,[z0,z1,z185,z3,z4,z5,z39]),(1,[z0,z1,z3,z4,z5,z32]),(0,[z0,z1,z3,z4,z195,z5,z6]),(0,[z0,z1,z196,z4,z5,z127,z6]),(0,[z197,z0,z1,z3,z4,z5,z6]),(0,[z18,z0,z1,z3,z4,z13,z6]),(0,[z0,z1,z3,z4,z45,z5,z46])],[(0,[z51,z0,z1,z3,z4,z198,z6]),(0,[z0,z1,z3,z4,z5,z198,z6]),(0,[z0,z53,z1,z3,z4,z5,z199])],[(0,[z0,z1,z3,z200,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z26,z66]),(0,[z0,z1,z3,z4,z27,z5,z6]),(0,[z184,z0,z1,z3,z4,z5,z6])],[(0,[z0,z171,z1,z3,z4,z5,z26]),(0,[z0,z1,z3,z109,z69,z5,z6]),(0,[z142,z0,z1,z3,z20,z4,z5]),(0,[z0,z1,z3,z4,z5,z201,z6]),(0,[z0,z1,z3,z20,z4,z5,z202])],[(0,[z51,z0,z1,z3,z4,z203,z6]),(0,[z0,z1,z3,z4,z5,z26,z204]),(0,[z0,z205,z1,z3,z4,z5,z39]),(0,[z0,z1,z10,z3,z4,z5,z39]),(0,[z0,z1,z3,z206,z4,z5,z6]),(0,[z0,z1,z3,z4,z47,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z207]),(0,[z0,z1,z3,z4,z5,z208,z6]),(0,[z0,z1,z3,z12,z4,z49,z6]),(0,[z0,z209,z1,z3,z4,z5,z6])],[(0,[z210,z0,z1,z3,z4,z5,z6]),(0,[z211,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z212,z6]),(1,[z0,z1,z3,z4,z5,z213]),(0,[z173,z0,z1,z3,z4,z5,z56]),(0,[z0,z1,z3,z4,z5,z127,z39]),(0,[z0,z214,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z5,z215]),(0,[z0,z53,z1,z196,z4,z5,z6]),(0,[z0,z1,z3,z216,z4,z5,z6])],[(0,[z0,z1,z3,z157,z4,z5,z39]),(0,[z0,z217,z1,z3,z4,z5,z9]),(0,[z0,z1,z3,z4,z218,z47,z6]),(0,[z0,z1,z3,z4,z219,z5,z6])]],
   [[(1,[z0,z220,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z5,z96]),(0,[z0,z1,z185,z3,z4,z5,z26]),(0,[z0,z1,z221,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z222,z5,z6]),(0,[z0,z1,z3,z4,z186,z5,z56])],[(1,[z169,z0,z1,z3,z4,z5]),(0,[z0,z65,z1,z3,z4,z5,z39]),(1,[z135,z0,z1,z3,z4,z5]),(0,[z0,z223,z1,z3,z4,z5,z6]),(0,[z0,z1,z224,z3,z4,z5,z6]),(0,[z0,z225,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z226,z6]),(0,[z227,z0,z1,z3,z4,z5,z6]),(0,[z194,z95,z1,z3,z4,z5,z6]),(0,[z25,z0,z1,z3,z4,z5,z9]),(0,[z228,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z229,z4,z5,z6]),(0,[z0,z230,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z231,z6]),(1,[z0,z1,z3,z4,z5,z42]),(1,[z0,z1,z3,z232,z4,z5]),(0,[z14,z0,z1,z3,z20,z4,z5])],[(0,[z0,z1,z3,z4,z5,z155,z6]),(0,[z233,z0,z1,z3,z20,z4,z5])],[(0,[z0,z171,z3,z159,z4,z5,z6]),(0,[z0,z1,z3,z20,z4,z5,z63]),(0,[z0,z1,z10,z3,z4,z5,z26]),(0,[z234,z0,z1,z3,z4,z5,z6]),(0,[z14,z0,z1,z3,z4,z5,z112]),(0,[z235,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z11,z4,z69,z5,z6])],[(0,[z0,z1,z3,z4,z5,z236,z6]),(0,[z0,z1,z3,z4,z5,z127,z26]),(0,[z0,z1,z31,z3,z4,z5,z39]),(0,[z0,z1,z3,z4,z5,z6,z154]),(1,[z184,z0,z1,z4,z5,z56])],[(0,[z0,z1,z3,z4,z109,z5,z6]),(0,[z0,z1,z3,z4,z47,z5,z56]),(0,[z237,z0,z1,z3,z4,z5,z6]),(0,[z0,z53,z1,z3,z4,z5,z9]),(0,[z14,z0,z1,z238,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z6,z239])],[(0,[z0,z1,z3,z4,z240,z5,z6]),(0,[z37,z0,z1,z3,z4,z63,z6]),(0,[z0,z1,z3,z4,z5,z241,z6]),(0,[z0,z1,z3,z4,z242,z5,z6]),(0,[z0,z1,z3,z4,z13,z5,z243]),(0,[z0,z1,z3,z20,z4,z5,z38])]],
   [[(0,[z0,z1,z73,z159,z4,z5,z6]),(0,[z0,z1,z3,z4,z244,z5,z6]),(0,[z0,z65,z1,z3,z4,z5,z26])],[(0,[z0,z1,z3,z12,z4,z63,z6]),(1,[z0,z1,z3,z4,z5,z201]),(0,[z245,z0,z1,z3,z4,z5,z9]),(0,[z0,z1,z3,z4,z5,z74,z9]),(0,[z246,z0,z1,z3,z4,z5,z6])],[(0,[z128,z0,z171,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z247,z5,z6]),(1,[z0,z1,z3,z4,z124,z6]),(0,[z95,z0,z1,z3,z4,z5,z39]),(0,[z0,z1,z3,z4,z5,z46,z39]),(1,[z0,z1,z248,z3,z4,z5]),(1,[z0,z1,z3,z4,z5,z249]),(0,[z0,z117,z1,z3,z4,z5,z6]),(0,[z0,z250,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z251]),(0,[z0,z1,z3,z3,z4,z5,z56]),(0,[z0,z1,z3,z4,z5,z123,z6])],[(0,[z252,z0,z1,z3,z4,z5,z6]),(0,[z14,z93,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z11,z109,z5,z6]),(0,[z0,z217,z1,z3,z4,z5,z39]),(0,[z0,z253,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z11,z4,z5,z9]),(1,[z0,z254,z1,z3,z4,z5])],[(0,[z23,z0,z1,z102,z4,z5,z6]),(0,[z0,z1,z3,z4,z255,z5,z6]),(0,[z0,z1,z3,z4,z27,z256,z6]),(0,[z0,z1,z31,z3,z4,z5,z26]),(0,[z0,z1,z257,z3,z4,z5,z6]),(0,[z0,z258,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z19,z4,z5,z6]),(0,[z0,z1,z259,z3,z4,z5,z6])],[(0,[z0,z217,z1,z3,z20,z4,z5]),(0,[z0,z1,z3,z4,z5,z260,z6]),(0,[z184,z0,z1,z4,z5,z56,z6]),(0,[z0,z1,z3,z261,z20,z4,z5])],[(0,[z0,z1,z3,z4,z262,z5,z6]),(0,[z14,z0,z64,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z263,z5,z6])],[(0,[z23,z0,z1,z3,z110,z5,z6]),(0,[z0,z1,z3,z4,z264,z5,z6]),(0,[z0,z65,z1,z3,z4,z5,z66]),(0,[z0,z1,z3,z177,z11,z4,z5]),(0,[z0,z1,z265,z3,z4,z5,z6])]],
   [[(0,[z37,z0,z1,z3,z4,z5,z266]),(0,[z25,z0,z1,z3,z20,z4,z5]),(0,[z0,z117,z1,z3,z4,z112,z6]),(0,[z0,z1,z3,z4,z5,z267,z6]),(0,[z0,z1,z3,z4,z5,z268,z6]),(0,[z14,z0,z1,z3,z4,z69,z5]),(0,[z0,z1,z238,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z269,z5,z6])],[(0,[z95,z0,z1,z3,z4,z5,z26]),(0,[z0,z1,z3,z4,z5,z46,z26]),(0,[z0,z146,z1,z3,z4,z5,z249]),(1,[z0,z146,z3,z141,z5,z6])],[(0,[z270,z0,z1,z3,z4,z5,z6]),(0,[z82,z14,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z70,z5,z6]),(0,[z271,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z272,z5,z6])],[(0,[z23,z0,z273,z3,z4,z5,z6]),(0,[z274,z0,z1,z3,z4,z5,z6]),(0,[z0,z117,z1,z3,z4,z5,z56]),(0,[z0,z1,z275,z3,z4,z5,z6]),(0,[z276,z14,z0,z1,z3,z4,z5])],[(0,[z0,z1,z3,z4,z277,z5,z6]),(0,[z14,z0,z217,z1,z3,z4,z5]),(0,[z278,z0,z1,z3,z4,z5,z6]),(0,[z0,z53,z1,z3,z20,z4,z5]),(0,[z0,z1,z3,z20,z4,z5,z9]),(0,[z0,z253,z1,z3,z4,z5,z56]),(0,[z0,z1,z3,z4,z5,z56,z279])],[(0,[z0,z1,z3,z4,z5,z280,z6]),(0,[z0,z1,z273,z3,z4,z5,z9]),(0,[z0,z1,z3,z4,z5,z281,z6]),(0,[z0,z1,z3,z157,z13,z5,z6]),(0,[z0,z1,z3,z282,z4,z5,z39]),(0,[z0,z1,z3,z4,z5,z6,z283]),(0,[z82,z0,z1,z3,z141,z5,z6]),(0,[z8,z14,z0,z1,z3,z4,z5])],[(0,[z0,z31,z3,z159,z4,z5,z6]),(0,[z0,z1,z284,z3,z4,z5,z6]),(0,[z82,z0,z1,z3,z4,z5,z6]),(0,[z285,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z286]),(0,[z0,z1,z196,z3,z4,z127,z6]),(0,[z287,z0,z1,z3,z4,z5,z6])],[(0,[z0,z288,z1,z3,z4,z5,z6]),(0,[z276,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z289]),(0,[z290,z0,z1,z3,z4,z5,z6]),(0,[z8,z0,z1,z3,z11,z5,z6]),(0,[z0,z1,z3,z4,z291,z5,z6]),(0,[z0,z1,z3,z4,z5,z292,z9])]],
   [[(0,[z18,z0,z1,z3,z157,z5,z6]),(0,[z0,z1,z3,z4,z256,z127,z6]),(0,[z293,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z294,z6]),(0,[z295,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z185,z4,z5,z6,z9])],[(0,[z93,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z296,z4,z5,z6]),(1,[z0,z1,z3,z4,z5,z297]),(0,[z0,z1,z3,z4,z298,z5,z39]),(0,[z8,z0,z1,z3,z4,z5,z6])],[(0,[z299,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z39,z6]),(0,[z300,z0,z1,z3,z4,z5,z39]),(0,[z0,z1,z3,z301,z4,z5,z6]),(0,[z189,z0,z1,z3,z4,z5,z6]),(0,[z0,z53,z1,z3,z4,z70,z6]),(0,[z0,z1,z3,z4,z5,z56,z302])],[(0,[z0,z1,z3,z303,z4,z5,z6]),(0,[z304,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z5,z174]),(0,[z0,z1,z3,z5,z74,z6,z38]),(0,[z305,z0,z1,z3,z20,z4,z5])],[(0,[z0,z1,z3,z4,z5,z6,z306]),(0,[z307,z0,z1,z3,z4,z5,z56]),(0,[z0,z308,z1,z3,z4,z5,z56]),(0,[z0,z1,z3,z4,z5,z56,z56]),(0,[z0,z1,z3,z13,z5,z49,z6])],[(0,[z0,z64,z1,z3,z4,z5,z56]),(0,[z0,z1,z196,z3,z4,z5,z201])],[(0,[z0,z309,z1,z3,z4,z5,z6]),(0,[z14,z0,z1,z3,z4,z13,z5])],[(0,[z0,z1,z73,z3,z4,z5,z56]),(1,[z37,z1,z3,z4,z63,z6]),(0,[z82,z0,z1,z3,z4,z5,z56]),(0,[z14,z0,z1,z185,z3,z4,z5]),(0,[z72,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z310,z6])]],
   [[(0,[z311,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z20,z4,z5,z39]),(0,[z0,z64,z3,z4,z5,z112,z6])],[(0,[z0,z1,z273,z3,z4,z5,z39]),(0,[z128,z0,z1,z3,z4,z5,z9]),(0,[z0,z1,z3,z4,z5,z312,z6])],[(0,[z0,z1,z3,z4,z5,z313,z6]),(0,[z142,z0,z3,z4,z5,z54,z6]),(0,[z8,z0,z1,z3,z4,z5,z56]),(0,[z314,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z315,z5,z6]),(0,[z0,z1,z3,z20,z20,z4,z5])],[(1,[z23,z273,z3,z4,z5,z6]),(0,[z0,z1,z273,z3,z20,z4,z5]),(0,[z0,z316,z1,z3,z4,z5,z6]),(0,[z51,z14,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z317,z4,z5,z6]),(0,[z86,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z318,z6]),(0,[z0,z1,z3,z4,z70,z256,z6]),(0,[z0,z1,z3,z319,z4,z5,z6]),(1,[z0,z1,z3,z4,z195,z6])],[(0,[z0,z1,z3,z4,z5,z320,z6]),(0,[z194,z0,z1,z3,z4,z5,z297]),(0,[z0,z1,z100,z3,z4,z5,z26]),(0,[z0,z1,z3,z4,z5,z26,z9]),(0,[z0,z321,z1,z3,z4,z5,z6]),(0,[z322,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z323,z5,z6])],[(0,[z51,z0,z1,z3,z4,z5,z324]),(0,[z0,z325,z1,z3,z4,z5,z6]),(0,[z0,z1,z326,z3,z4,z5,z6]),(0,[z0,z53,z1,z3,z12,z4,z6]),(0,[z327,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z5,z328])],[(0,[z95,z0,z1,z3,z4,z5,z329]),(0,[z37,z0,z1,z3,z4,z5,z56]),(0,[z0,z146,z1,z3,z4,z5,z9])],[(0,[z0,z1,z3,z4,z5,z5,z6]),(0,[z0,z1,z3,z20,z4,z5,z26]),(1,[z0,z1,z3,z4,z5,z330]),(0,[z0,z53,z1,z3,z4,z27,z6]),(0,[z0,z331,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z332,z5,z6])]],
   [[(0,[z0,z1,z273,z3,z4,z5,z26]),(0,[z0,z333,z1,z3,z4,z5,z6]),(0,[z334,z0,z1,z3,z4,z5,z6]),(0,[z14,z0,z1,z10,z3,z4,z5]),(0,[z0,z1,z3,z20,z4,z70,z5]),(0,[z0,z1,z3,z12,z4,z5,z56]),(0,[z0,z1,z3,z4,z13,z5,z6])],[(0,[z335,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z336,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z337,z6]),(0,[z18,z0,z1,z3,z4,z256,z6]),(1,[z0,z1,z3,z167,z4,z5]),(0,[z0,z1,z3,z4,z338,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z339]),(0,[z340,z0,z1,z3,z4,z5,z6])],[(0,[z23,z128,z1,z3,z4,z5,z6]),(0,[z341,z0,z1,z3,z4,z5,z6]),(0,[z342,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z101]),(0,[z0,z1,z343,z3,z4,z5,z6])],[(0,[z0,z217,z171,z3,z4,z5,z6]),(0,[z0,z1,z344,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z345,z6]),(1,[z0,z1,z3,z4,z5,z39]),(0,[z0,z1,z3,z4,z5,z346,z26]),(0,[z0,z1,z3,z4,z5,z6,z104]),(0,[z0,z347,z1,z3,z4,z5,z6])],[(0,[z0,z171,z1,z3,z4,z5,z9]),(0,[z1,z73,z3,z52,z4,z5,z6]),(0,[z0,z1,z3,z4,z348,z5,z6])],[(0,[z0,z1,z3,z157,z47,z5,z6]),(0,[z0,z1,z3,z4,z5,z112,z6]),(0,[z0,z1,z3,z4,z5,z349,z6]),(0,[z162,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z279]),(0,[z0,z1,z3,z4,z5,z350,z6])],[(1,[z0,z1,z3,z22,z5,z6]),(0,[z0,z1,z3,z4,z13,z112,z6]),(0,[z0,z1,z351,z3,z4,z5,z6]),(0,[z352,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z20,z4,z5,z66]),(0,[z0,z1,z3,z4,z45,z5,z6])],[(0,[z353,z0,z1,z3,z4,z5,z6]),(0,[z128,z0,z1,z3,z20,z4,z5]),(0,[z0,z217,z1,z3,z4,z182,z6]),(0,[z0,z1,z3,z4,z5,z354,z6]),(1,[z0,z64,z3,z4,z112,z6]),(0,[z0,z1,z3,z4,z355,z5,z6]),(0,[z0,z1,z3,z232,z4,z5,z6]),(0,[z0,z356,z1,z3,z20,z4,z5])]],
   [[(0,[z14,z0,z171,z1,z3,z4,z5]),(0,[z51,z0,z1,z3,z4,z5,z56]),(0,[z0,z1,z3,z52,z4,z5,z39]),(0,[z0,z357,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z358,z39]),(0,[z0,z1,z3,z20,z4,z69,z5]),(0,[z0,z1,z3,z4,z359,z5,z6]),(0,[z0,z1,z185,z3,z4,z5,z9]),(0,[z0,z1,z3,z4,z5,z9,z192]),(0,[z14,z0,z1,z3,z4,z360,z5])],[(0,[z0,z1,z3,z4,z361,z5,z6]),(0,[z0,z1,z3,z362,z4,z5,z6])],[(0,[z0,z1,z363,z3,z4,z5,z6]),(0,[z0,z1,z3,z20,z157,z4,z5]),(1,[z0,z1,z3,z4,z5,z26]),(0,[z0,z1,z3,z364,z4,z5,z6]),(0,[z0,z365,z1,z3,z4,z5,z6])],[(0,[z86,z1,z3,z4,z256,z5,z6]),(0,[z0,z1,z3,z4,z366,z5,z6]),(0,[z0,z1,z3,z4,z5,z39,z202]),(0,[z142,z14,z0,z1,z3,z4,z5]),(0,[z0,z1,z196,z3,z4,z5,z9]),(0,[z0,z1,z3,z4,z5,z6,z302]),(0,[z136,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z31,z52,z4,z5,z6]),(0,[z367,z0,z1,z3,z4,z5,z6]),(0,[z0,z146,z1,z3,z20,z4,z5]),(0,[z18,z0,z117,z1,z3,z4,z6]),(0,[z142,z0,z65,z3,z4,z5,z6]),(1,[z8,z0,z1,z69,z5,z6]),(0,[z0,z1,z3,z4,z69,z5,z9]),(0,[z0,z1,z10,z3,z4,z5,z9]),(0,[z0,z1,z3,z368,z4,z5,z6])],[(0,[z0,z1,z3,z4,z124,z5,z6]),(0,[z0,z1,z3,z4,z256,z5,z9]),(0,[z0,z1,z3,z4,z5,z6,z369]),(0,[z0,z1,z370,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z5,z371]),(0,[z0,z1,z3,z4,z5,z6,z372]),(0,[z373,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z127,z9]),(0,[z14,z0,z1,z3,z4,z5,z127]),(0,[z0,z53,z1,z3,z4,z5,z374]),(0,[z0,z1,z3,z4,z375,z5,z6]),(0,[z0,z1,z3,z77,z4,z5,z202])],[(0,[z93,z0,z1,z73,z4,z5,z6]),(0,[z194,z0,z1,z3,z4,z5,z39]),(0,[z0,z1,z3,z4,z376,z5,z6]),(0,[z0,z1,z3,z4,z5,z112,z56]),(1,[z0,z65,z3,z4,z5,z66]),(0,[z377,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z378,z5,z6])],[(0,[z0,z1,z3,z52,z4,z5,z26]),(0,[z0,z1,z3,z4,z5,z212,z6]),(0,[z142,z0,z1,z3,z4,z5,z6]),(0,[z18,z0,z53,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z45,z5,z56]),(0,[z0,z1,z3,z77,z4,z45,z6])]],
   [[(1,[z0,z1,z3,z4,z5,z379]),(0,[z0,z1,z3,z4,z27,z5,z39]),(0,[z0,z1,z3,z380,z4,z5,z6]),(0,[z0,z65,z1,z3,z4,z5,z9])],[(0,[z0,z381,z1,z3,z4,z5,z6]),(0,[z0,z1,z382,z3,z4,z5,z6]),(0,[z0,z1,z3,z383,z4,z5,z6]),(0,[z14,z14,z0,z1,z3,z4,z5])],[(0,[z0,z171,z1,z3,z20,z4,z5]),(1,[z95,z1,z3,z157,z5,z6]),(0,[z173,z1,z3,z4,z5,z6,z26]),(0,[z0,z217,z1,z159,z4,z5,z6]),(0,[z0,z1,z248,z3,z4,z5,z6]),(0,[z14,z0,z146,z1,z3,z4,z5]),(0,[z0,z1,z3,z384,z4,z5,z6])],[(0,[z0,z1,z3,z4,z63,z112,z6]),(0,[z0,z1,z3,z385,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z156,z6]),(0,[z0,z1,z386,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z387,z6]),(0,[z0,z1,z31,z3,z4,z5,z9]),(0,[z0,z1,z3,z388,z4,z5,z6])],[(0,[z194,z0,z1,z3,z4,z5,z26]),(0,[z0,z1,z3,z4,z389,z5,z6]),(0,[z0,z1,z390,z3,z4,z5,z6])],[(0,[z391,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z5,z320]),(1,[z0,z1,z3,z4,z203,z6]),(0,[z0,z1,z3,z4,z5,z392,z6]),(0,[z233,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z185,z3,z20,z4,z5]),(0,[z0,z1,z3,z4,z5,z9,z202]),(0,[z0,z1,z3,z4,z5,z393,z6])],[(0,[z14,z0,z1,z273,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z394,z6]),(0,[z0,z1,z3,z4,z395,z5,z6]),(0,[z0,z1,z3,z4,z5,z396,z6]),(0,[z0,z1,z3,z4,z27,z5,z26]),(0,[z0,z1,z196,z3,z4,z5,z39]),(0,[z0,z1,z3,z397,z4,z5,z6])]],
   [[(0,[z0,z398,z1,z3,z4,z5,z6]),(0,[z14,z0,z1,z73,z3,z4,z5]),(0,[z0,z1,z3,z4,z69,z5,z39]),(0,[z18,z0,z146,z1,z3,z5,z6]),(0,[z0,z1,z3,z141,z4,z5,z56]),(0,[z142,z0,z1,z3,z4,z5,z56]),(0,[z0,z1,z3,z4,z5,z6,z399])],[(1,[z0,z1,z400,z4,z5,z6]),(0,[z95,z0,z1,z3,z109,z5,z6]),(0,[z95,z0,z1,z3,z4,z5,z9]),(0,[z0,z1,z3,z401,z4,z5,z6]),(0,[z0,z1,z3,z4,z402,z5,z6]),(0,[z14,z37,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z256,z5,z39]),(0,[z0,z1,z196,z3,z20,z4,z5]),(0,[z0,z1,z3,z4,z5,z46,z9]),(0,[z0,z254,z1,z3,z4,z5,z6])],[(1,[z0,z1,z3,z4,z5,z403]),(0,[z210,z0,z1,z3,z4,z5,z26]),(0,[z0,z1,z3,z4,z5,z49,z39]),(0,[z0,z1,z10,z3,z20,z4,z5]),(0,[z0,z1,z3,z4,z5,z404,z6])],[(0,[z171,z1,z273,z3,z4,z5,z6]),(0,[z0,z1,z405,z3,z4,z5,z6]),(0,[z0,z1,z3,z406,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z330,z6]),(0,[z0,z1,z3,z4,z407,z5,z6]),(1,[z0,z1,z3,z408,z4,z5]),(0,[z0,z1,z3,z4,z5,z409,z6]),(0,[z0,z1,z410,z3,z4,z5,z6]),(0,[z0,z411,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z412,z5,z6])],[(0,[z0,z413,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z111,z4,z5,z6]),(0,[z0,z1,z3,z157,z4,z5,z56]),(0,[z414,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z415,z3,z4,z5,z6]),(0,[z14,z0,z1,z3,z4,z5,z170])],[(1,[z0,z1,z3,z4,z5,z416]),(0,[z0,z1,z196,z3,z4,z5,z26]),(0,[z0,z417,z1,z3,z4,z5,z6]),(0,[z0,z65,z1,z3,z20,z4,z5]),(0,[z21,z0,z1,z3,z4,z5,z9]),(0,[z14,z0,z1,z3,z4,z5,z56]),(0,[z0,z1,z3,z4,z5,z418,z6])],[(0,[z0,z1,z419,z3,z4,z5,z6]),(0,[z0,z1,z3,z420,z4,z5,z6]),(1,[z0,z1,z3,z4,z5,z329]),(0,[z0,z1,z3,z4,z69,z5,z26]),(0,[z25,z14,z0,z1,z3,z4,z5]),(0,[z0,z1,z196,z3,z4,z70,z6])]],
   [[(0,[z0,z1,z3,z4,z421,z5,z6]),(0,[z0,z1,z3,z4,z256,z5,z26]),(0,[z0,z146,z1,z3,z13,z5,z6]),(0,[z18,z0,z1,z3,z5,z49,z6])],[(0,[z0,z1,z3,z110,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z49,z26]),(0,[z0,z1,z3,z4,z5,z56,z54])],[(0,[z0,z422,z1,z3,z4,z5,z6]),(0,[z0,z1,z31,z3,z20,z4,z5])],[(0,[z0,z1,z3,z4,z423,z5,z6]),(0,[z25,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z5,z424]),(0,[z425,z14,z0,z1,z3,z4,z5]),(0,[z14,z0,z1,z3,z4,z5,z46])],[(0,[z0,z426,z1,z3,z4,z5,z6]),(1,[z0,z117,z3,z4,z27,z6])],[(0,[z427,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z76,z9]),(0,[z428,z0,z1,z3,z20,z4,z5])],[(0,[z194,z1,z3,z4,z109,z5,z6]),(0,[z0,z1,z3,z4,z5,z63,z39]),(1,[z0,z1,z3,z4,z5,z374]),(0,[z0,z1,z3,z4,z5,z6,z243])],[(0,[z0,z1,z3,z4,z429,z5,z6]),(0,[z0,z1,z3,z4,z4,z5,z6]),(0,[z95,z0,z1,z3,z20,z4,z5]),(0,[z0,z1,z3,z4,z70,z5,z39]),(1,[z0,z1,z3,z4,z182,z6]),(0,[z0,z1,z3,z4,z5,z54,z6]),(0,[z430,z0,z1,z3,z4,z5,z6])]],
   [[(0,[z0,z431,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z432])],[(0,[z0,z1,z3,z4,z5,z424,z26]),(0,[z0,z1,z3,z4,z5,z433,z26]),(0,[z0,z217,z1,z3,z4,z5,z56]),(0,[z0,z1,z3,z4,z434,z5,z6])],[(0,[z0,z435,z1,z3,z4,z5,z6]),(1,[z51,z1,z52,z4,z5,z6]),(0,[z21,z0,z1,z3,z4,z5,z39]),(0,[z0,z1,z3,z4,z5,z39,z436]),(0,[z142,z0,z1,z3,z4,z45,z5]),(0,[z0,z1,z196,z3,z12,z4,z6]),(0,[z0,z1,z3,z4,z5,z74,z6])],[(0,[z0,z1,z3,z4,z5,z39,z330]),(0,[z98,z0,z1,z3,z4,z5,z9]),(0,[z0,z437,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z438,z6])],[(0,[z25,z0,z1,z3,z4,z5,z56]),(0,[z439,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z196,z3,z4,z27,z6])],[(0,[z0,z1,z3,z4,z5,z63,z26]),(0,[z18,z0,z1,z3,z4,z5,z39]),(0,[z0,z1,z3,z4,z440,z5,z6]),(0,[z0,z1,z3,z20,z4,z5,z127])],[(0,[z0,z1,z400,z3,z4,z5,z6]),(0,[z23,z0,z1,z3,z4,z5,z39]),(0,[z128,z0,z1,z3,z4,z5,z79]),(0,[z307,z0,z1,z3,z4,z5,z6]),(0,[z93,z0,z1,z3,z4,z5,z39]),(0,[z0,z1,z3,z4,z70,z5,z26]),(0,[z0,z58,z1,z3,z4,z5,z39]),(0,[z0,z1,z3,z4,z441,z5,z6]),(1,[z0,z1,z3,z4,z5,z199]),(0,[z0,z1,z3,z4,z5,z56,z6]),(0,[z0,z1,z3,z4,z108,z5,z9]),(0,[z0,z308,z1,z3,z4,z5,z6])],[(0,[z128,z0,z1,z3,z4,z5,z313]),(0,[z0,z1,z3,z4,z5,z442,z6]),(0,[z86,z0,z1,z3,z4,z5,z97]),(1,[z173,z1,z3,z4,z5,z26]),(0,[z0,z1,z3,z4,z5,z39,z39]),(0,[z82,z0,z1,z3,z4,z133,z6]),(0,[z0,z64,z1,z3,z4,z5,z6]),(1,[z0,z443,z3,z4,z5,z6])]],
   [[(0,[z0,z1,z444,z3,z4,z5,z6]),(0,[z95,z1,z3,z157,z4,z5,z6]),(0,[z0,z445,z1,z3,z4,z5,z6]),(0,[z0,z53,z1,z3,z4,z5,z56]),(0,[z0,z1,z3,z4,z5,z446,z6]),(0,[z0,z1,z3,z4,z5,z447,z6])],[(0,[z23,z0,z1,z3,z22,z5,z6]),(0,[z0,z1,z73,z3,z4,z5,z6]),(0,[z21,z0,z1,z3,z4,z5,z26]),(0,[z0,z1,z3,z77,z4,z5,z39]),(0,[z14,z0,z117,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z448,z6])],[(0,[z51,z0,z1,z3,z4,z5,z306]),(0,[z0,z58,z217,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z46,z6,z202])],[(0,[z0,z1,z3,z4,z5,z6,z79]),(0,[z0,z58,z1,z31,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z449]),(1,[z0,z1,z75,z3,z4,z6]),(0,[z0,z1,z10,z3,z4,z5,z251])],[(0,[z18,z0,z1,z3,z4,z5,z26]),(0,[z14,z0,z53,z1,z3,z4,z5])],[(0,[z23,z0,z1,z3,z4,z5,z26]),(0,[z93,z0,z1,z3,z4,z5,z26]),(0,[z0,z450,z1,z3,z4,z5,z6]),(0,[z0,z1,z451,z3,z4,z5,z6]),(0,[z0,z58,z1,z3,z4,z5,z26]),(0,[z0,z64,z1,z3,z4,z112,z6]),(0,[z0,z1,z452,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z5,z268]),(0,[z0,z1,z3,z11,z4,z5,z56])],[(0,[z0,z1,z3,z4,z5,z39,z26]),(0,[z453,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z454,z4,z5,z6]),(0,[z0,z1,z3,z4,z455,z5,z6]),(1,[z0,z1,z185,z4,z5,z9]),(0,[z0,z1,z3,z4,z5,z456,z56]),(0,[z457,z14,z0,z1,z3,z4,z5])],[(0,[z458,z0,z1,z3,z4,z5,z6]),(1,[z93,z1,z73,z4,z5,z6]),(0,[z0,z459,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z460,z5,z6]),(0,[z0,z1,z3,z461,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z462,z6])]],
   [[(0,[z37,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z463,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z97]),(0,[z86,z0,z1,z3,z4,z5,z39]),(0,[z0,z464,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z77,z4,z5,z26]),(0,[z0,z58,z1,z3,z4,z5,z371]),(1,[z0,z58,z159,z4,z5,z6]),(0,[z465,z0,z1,z3,z4,z5,z6]),(0,[z0,z146,z1,z3,z47,z5,z6]),(0,[z0,z1,z3,z4,z466,z5,z6]),(0,[z0,z53,z1,z4,z70,z5,z6]),(0,[z135,z0,z1,z3,z4,z5,z9]),(0,[z0,z1,z3,z4,z5,z292,z6])],[(0,[z0,z467,z1,z3,z4,z5,z6]),(0,[z0,z1,z129,z3,z4,z5,z6]),(0,[z468,z0,z1,z3,z4,z5,z6]),(0,[z8,z0,z1,z10,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z469]),(1,[z0,z1,z3,z463,z5,z6]),(0,[z0,z1,z470,z3,z4,z5,z6]),(0,[z457,z0,z1,z3,z4,z5,z6]),(0,[z144,z0,z1,z3,z4,z5,z9]),(1,[z0,z1,z3,z4,z5,z9]),(0,[z0,z1,z3,z145,z4,z5,z9]),(0,[z0,z1,z3,z12,z4,z5,z6])],[(0,[z0,z1,z471,z3,z4,z5,z6]),(0,[z87,z0,z1,z3,z4,z5,z26]),(0,[z0,z1,z3,z4,z5,z39,z74]),(0,[z472,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z109,z13,z5,z6]),(0,[z0,z1,z4,z70,z5,z127,z6]),(0,[z0,z1,z3,z232,z4,z5,z49])],[(0,[z473,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z39,z66]),(0,[z0,z58,z3,z159,z4,z5,z6]),(0,[z14,z0,z1,z31,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z6,z474])],[(0,[z51,z0,z1,z3,z423,z5,z6]),(1,[z0,z1,z3,z4,z5,z324]),(0,[z0,z475,z1,z3,z4,z5,z6]),(0,[z0,z476,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z477,z4,z5,z6]),(1,[z0,z1,z3,z4,z5,z478]),(0,[z0,z1,z3,z4,z479,z5,z6]),(0,[z480,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z20,z4,z5,z56])],[(0,[z0,z1,z273,z3,z4,z5,z56]),(0,[z51,z0,z129,z3,z4,z5,z6]),(0,[z0,z1,z3,z52,z4,z5,z9]),(0,[z86,z0,z1,z3,z4,z5,z26]),(0,[z0,z1,z3,z4,z5,z481,z6]),(0,[z0,z1,z3,z159,z4,z5,z9]),(0,[z0,z1,z3,z4,z218,z5,z6]),(0,[z0,z1,z3,z20,z4,z5,z112]),(0,[z0,z1,z3,z4,z5,z6,z482]),(0,[z0,z1,z3,z4,z5,z483,z6])]],
   [[(0,[z1,z3,z4,z256,z5,z63,z6]),(0,[z0,z1,z3,z103,z4,z5,z26]),(0,[z0,z1,z3,z4,z5,z133,z6]),(0,[z14,z0,z1,z3,z61,z4,z5])],[(0,[z23,z0,z1,z3,z4,z5,z320]),(0,[z51,z1,z3,z52,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z148,z6]),(0,[z0,z1,z3,z4,z5,z484,z6]),(1,[z0,z1,z3,z4,z218,z6]),(0,[z0,z1,z3,z485,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z147,z6]),(0,[z0,z486,z1,z3,z4,z5,z6])],[(0,[z128,z0,z1,z3,z4,z5,z6]),(0,[z487,z0,z1,z3,z4,z5,z6]),(0,[z51,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z488,z4,z5,z6]),(0,[z18,z0,z1,z196,z3,z4,z6]),(0,[z0,z1,z3,z4,z5,z9,z489]),(1,[z0,z1,z3,z20,z5,z74])],[(0,[z0,z1,z3,z4,z490,z5,z6]),(0,[z457,z0,z1,z3,z4,z5,z56]),(0,[z0,z1,z3,z4,z5,z6,z491]),(0,[z0,z1,z3,z20,z4,z5,z46])],[(0,[z23,z0,z1,z400,z4,z5,z6]),(1,[z0,z1,z3,z103,z4,z5]),(0,[z0,z158,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z5,z267,z6]),(1,[z0,z1,z3,z4,z222,z5])],[(0,[z93,z0,z1,z3,z4,z5,z403]),(0,[z492,z0,z1,z3,z4,z5,z6]),(0,[z194,z0,z1,z3,z109,z5,z6]),(0,[z194,z0,z1,z3,z4,z5,z9]),(0,[z142,z0,z1,z3,z4,z5,z54]),(0,[z0,z1,z3,z493,z4,z5,z6])],[(0,[z494,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z495,z4,z5,z6]),(0,[z0,z1,z3,z496,z4,z5,z6]),(0,[z0,z146,z1,z3,z141,z5,z6]),(0,[z0,z1,z3,z4,z5,z497,z6])],[(0,[z0,z1,z3,z4,z5,z6,z6]),(0,[z0,z1,z3,z4,z5,z498,z6]),(0,[z0,z1,z3,z4,z27,z5,z9]),(0,[z499,z0,z1,z3,z4,z5,z6]),(0,[z184,z0,z1,z3,z4,z5,z9])]],
   [[(1,[z0,z1,z3,z4,z5,z94]),(1,[z0,z1,z3,z277,z5,z6]),(0,[z0,z1,z3,z4,z5,z26,z500]),(0,[z501,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z9,z66]),(0,[z0,z1,z502,z3,z4,z5,z6]),(1,[z0,z1,z3,z20,z4,z5])],[(0,[z23,z0,z1,z3,z4,z5,z416]),(0,[z503,z0,z1,z3,z4,z5,z6]),(0,[z163,z0,z1,z3,z4,z5,z6]),(1,[z0,z217,z31,z4,z5,z6]),(0,[z0,z504,z1,z3,z4,z5,z6]),(1,[z0,z343,z3,z4,z5,z6])],[(0,[z0,z1,z505,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z5,z89]),(0,[z0,z1,z3,z4,z5,z6,z500]),(0,[z0,z1,z3,z4,z5,z42,z6]),(0,[z14,z0,z1,z3,z4,z5,z49]),(0,[z0,z1,z3,z20,z4,z506,z5])],[(0,[z128,z0,z1,z3,z4,z5,z56]),(0,[z0,z1,z507,z3,z4,z5,z6]),(0,[z0,z1,z3,z508,z4,z5,z6]),(0,[z0,z1,z3,z103,z157,z4,z5]),(0,[z0,z1,z3,z159,z4,z5,z39]),(0,[z0,z1,z3,z4,z5,z436,z6]),(0,[z0,z509,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z510]),(0,[z14,z0,z1,z3,z4,z5,z54]),(0,[z0,z1,z3,z20,z4,z332,z5]),(1,[z0,z1,z3,z77,z4,z202])],[(0,[z0,z1,z3,z4,z5,z166,z6]),(0,[z0,z1,z3,z167,z4,z5,z39]),(1,[z0,z1,z4,z5,z56,z9])],[(0,[z0,z1,z3,z52,z20,z4,z5]),(0,[z173,z0,z1,z3,z4,z5,z39]),(0,[z0,z1,z172,z3,z4,z5,z39]),(0,[z0,z1,z3,z159,z20,z4,z5]),(0,[z0,z1,z3,z511,z4,z5,z6])],[(0,[z23,z0,z171,z3,z4,z5,z6]),(0,[z0,z1,z512,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z39,z6,z26]),(0,[z0,z1,z513,z3,z20,z4,z5]),(0,[z0,z1,z3,z4,z5,z514,z6])],[(0,[z515,z0,z1,z3,z4,z5,z6]),(0,[z86,z0,z1,z3,z4,z256,z6]),(0,[z0,z516,z1,z3,z4,z5,z6])]],
   [[(0,[z517,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z518,z6]),(0,[z0,z1,z3,z4,z5,z26,z192]),(0,[z169,z0,z1,z3,z4,z5,z39]),(0,[z0,z146,z1,z3,z4,z5,z56])],[(0,[z519,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z5,z166]),(0,[z0,z1,z3,z4,z5,z297,z6]),(0,[z0,z1,z185,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z49,z9]),(0,[z0,z1,z3,z177,z4,z5,z9]),(0,[z520,z14,z0,z1,z3,z4,z5])],[(0,[z0,z1,z3,z102,z4,z5,z6]),(0,[z0,z1,z3,z521,z4,z5,z6]),(0,[z0,z1,z3,z4,z522,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z192]),(0,[z0,z1,z3,z523,z4,z5,z6]),(0,[z0,z1,z3,z4,z109,z5,z9]),(0,[z0,z1,z3,z141,z157,z5,z6]),(0,[z524,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z159,z4,z5,z26]),(0,[z0,z1,z3,z141,z4,z5,z6])],[(0,[z51,z0,z1,z3,z303,z5,z6]),(0,[z0,z1,z3,z4,z525,z5,z6]),(0,[z194,z0,z1,z3,z20,z4,z5]),(0,[z184,z0,z1,z3,z4,z5,z39]),(0,[z0,z146,z3,z4,z5,z112,z6]),(0,[z0,z1,z3,z4,z526,z5,z6]),(0,[z0,z1,z10,z3,z11,z5,z6]),(0,[z0,z1,z3,z4,z527,z5,z6]),(0,[z0,z528,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z506,z5,z6])],[(0,[z51,z0,z220,z3,z4,z5,z6]),(0,[z0,z1,z3,z109,z47,z5,z6]),(0,[z173,z0,z1,z3,z4,z5,z26]),(0,[z0,z529,z1,z3,z4,z5,z6]),(0,[z0,z217,z1,z3,z4,z294,z6]),(0,[z0,z1,z530,z3,z4,z5,z6])],[(0,[z0,z205,z1,z3,z4,z5,z6]),(0,[z531,z0,z1,z3,z4,z5,z6]),(0,[z532,z0,z1,z3,z4,z5,z6]),(0,[z37,z1,z3,z4,z5,z63,z6]),(0,[z0,z1,z533,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z47,z5,z39]),(0,[z82,z0,z146,z3,z4,z5,z6]),(0,[z0,z1,z10,z3,z4,z5,z6]),(0,[z0,z1,z3,z534,z4,z5,z6]),(0,[z184,z0,z1,z3,z20,z4,z5]),(0,[z0,z1,z3,z4,z5,z166,z56]),(0,[z0,z1,z3,z77,z4,z6,z202]),(0,[z0,z1,z3,z4,z5,z6,z535])],[(0,[z0,z171,z1,z3,z4,z5,z56]),(1,[z0,z1,z3,z4,z198,z6]),(0,[z0,z1,z3,z52,z4,z5,z166]),(0,[z0,z1,z536,z3,z4,z5,z6]),(1,[z82,z0,z3,z47,z5,z6]),(0,[z0,z1,z3,z4,z537,z5,z6]),(0,[z0,z1,z3,z4,z5,z127,z6])],[(0,[z538,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z157,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z213]),(1,[z189,z0,z1,z3,z5,z6]),(0,[z0,z1,z3,z4,z5,z539,z6]),(0,[z14,z0,z1,z390,z3,z4,z5])]],
   [[(0,[z0,z1,z3,z540,z4,z5,z6]),(0,[z14,z0,z1,z3,z4,z109,z5]),(0,[z0,z1,z3,z541,z4,z5,z6]),(0,[z0,z1,z3,z4,z542,z5,z6]),(1,[z0,z1,z3,z4,z5,z123]),(0,[z0,z1,z3,z543,z4,z5,z6]),(0,[z14,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z544])],[(0,[z0,z1,z3,z4,z5,z266,z6]),(0,[z0,z545,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z39,z38]),(1,[z0,z1,z3,z4,z134,z6]),(0,[z0,z65,z1,z3,z4,z5,z6]),(0,[z18,z0,z443,z3,z4,z5,z6]),(0,[z0,z1,z3,z20,z4,z13,z5])],[(0,[z184,z0,z1,z3,z4,z5,z26]),(0,[z228,z0,z1,z3,z4,z5,z39]),(0,[z0,z1,z3,z4,z5,z226,z39]),(0,[z546,z0,z1,z3,z4,z5,z6]),(0,[z0,z547,z1,z3,z4,z5,z6]),(0,[z0,z1,z185,z3,z4,z5,z56])],[(0,[z0,z1,z3,z4,z548,z5,z6]),(0,[z0,z1,z3,z191,z4,z5,z56])],[(0,[z0,z1,z3,z4,z47,z5,z26]),(0,[z0,z1,z3,z4,z5,z549,z6]),(1,[z0,z1,z3,z4,z5,z154]),(0,[z0,z1,z3,z4,z5,z550,z6])],[(0,[z0,z217,z273,z3,z4,z5,z6]),(0,[z0,z1,z3,z551,z4,z5,z6]),(0,[z93,z0,z1,z52,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z63,z9]),(1,[z0,z230,z1,z3,z4,z6]),(0,[z0,z146,z3,z141,z4,z5,z6]),(0,[z552,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z196,z3,z4,z5,z56]),(0,[z0,z1,z3,z4,z5,z6,z553])],[(0,[z0,z1,z3,z4,z109,z5,z39]),(0,[z0,z554,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z69,z5,z56]),(0,[z0,z1,z10,z3,z4,z5,z56]),(1,[z457,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z70,z5,z9]),(0,[z0,z1,z3,z12,z4,z13,z6])],[(0,[z51,z0,z1,z73,z4,z5,z6]),(0,[z0,z1,z3,z4,z256,z5,z56]),(0,[z555,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z556,z6]),(0,[z0,z1,z3,z4,z5,z127,z56]),(0,[z0,z1,z3,z177,z20,z4,z5])]],
   [[(0,[z0,z1,z557,z3,z4,z5,z6]),(0,[z0,z1,z3,z111,z4,z109,z5]),(0,[z0,z117,z64,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z112,z49,z6]),(0,[z0,z1,z3,z558,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z438,z49]),(0,[z0,z1,z3,z4,z360,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z202]),(0,[z559,z0,z1,z3,z4,z5,z6])],[(0,[z227,z0,z1,z3,z4,z5,z26]),(0,[z0,z3,z4,z47,z5,z112,z6]),(1,[z0,z1,z3,z28,z4,z5]),(1,[z0,z1,z3,z4,z5,z251]),(0,[z0,z560,z1,z3,z4,z5,z6])],[(0,[z95,z0,z1,z3,z4,z5,z6]),(0,[z169,z0,z1,z3,z157,z4,z5]),(0,[z0,z117,z1,z3,z4,z5,z39]),(0,[z0,z561,z1,z3,z4,z5,z6]),(0,[z0,z65,z1,z3,z4,z5,z56]),(0,[z0,z1,z3,z4,z5,z562,z6]),(0,[z8,z0,z1,z3,z69,z5,z6]),(1,[z14,z0,z1,z3,z20,z5]),(0,[z0,z1,z3,z20,z4,z5,z175]),(0,[z0,z1,z3,z4,z5,z46,z6]),(0,[z0,z1,z3,z4,z45,z5,z202])],[(0,[z0,z217,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z261,z4,z5,z6]),(0,[z14,z0,z1,z3,z141,z4,z5]),(0,[z0,z563,z1,z3,z4,z5,z56]),(0,[z21,z14,z0,z1,z3,z4,z5])],[(0,[z18,z0,z1,z3,z109,z5,z6]),(0,[z0,z1,z3,z4,z63,z127,z6]),(0,[z0,z1,z3,z5,z267,z112,z6]),(0,[z18,z0,z1,z3,z4,z5,z9]),(0,[z0,z1,z3,z4,z5,z9,z38])],[(0,[z23,z0,z1,z3,z4,z5,z9]),(0,[z0,z1,z3,z4,z5,z94,z6]),(0,[z93,z0,z1,z3,z4,z5,z9]),(0,[z0,z1,z3,z4,z109,z5,z26]),(1,[z0,z476,z1,z3,z4,z5]),(0,[z0,z58,z1,z3,z4,z5,z9]),(0,[z14,z0,z65,z1,z3,z4,z5])],[(0,[z0,z1,z3,z564,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z565,z6]),(0,[z0,z1,z3,z4,z5,z39,z9]),(0,[z0,z1,z31,z3,z4,z5,z56]),(0,[z14,z0,z486,z1,z3,z4,z5]),(0,[z0,z1,z3,z20,z4,z566,z5])],[(0,[z0,z1,z567,z3,z4,z5,z6]),(0,[z568,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z248,z3,z4,z47,z5]),(0,[z0,z1,z3,z569,z4,z5,z6]),(0,[z570,z0,z1,z3,z4,z5,z6]),(0,[z14,z0,z1,z196,z3,z4,z5])]],
   [[(0,[z0,z1,z3,z4,z571,z5,z6]),(0,[z0,z1,z196,z3,z4,z5,z399]),(0,[z0,z1,z3,z77,z4,z5,z9]),(0,[z0,z572,z1,z3,z4,z5,z6])],[(0,[z14,z0,z1,z3,z4,z256,z5]),(0,[z0,z117,z1,z3,z4,z5,z26]),(0,[z0,z58,z1,z3,z4,z5,z478]),(0,[z0,z1,z3,z4,z573,z5,z6]),(0,[z0,z1,z3,z574,z4,z5,z6]),(0,[z0,z1,z3,z4,z45,z46,z6])],[(0,[z0,z1,z575,z3,z4,z5,z6]),(0,[z0,z576,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z577,z5,z6]),(0,[z0,z1,z3,z4,z134,z5,z6]),(0,[z425,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z578]),(0,[z0,z53,z1,z3,z4,z5,z6])],[(0,[z95,z0,z1,z3,z4,z5,z56]),(0,[z579,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z580,z6]),(0,[z0,z1,z3,z20,z4,z5,z54]),(0,[z0,z1,z3,z4,z5,z46,z56]),(0,[z0,z1,z3,z4,z581,z5,z6])],[(0,[z0,z582,z1,z3,z4,z5,z6]),(0,[z0,z583,z1,z3,z4,z5,z6]),(0,[z584,z0,z1,z3,z4,z5,z6]),(0,[z271,z0,z1,z3,z20,z4,z5])],[(0,[z23,z0,z1,z3,z4,z78,z6]),(0,[z0,z1,z3,z4,z5,z585,z6]),(0,[z245,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z282,z4,z5,z6]),(1,[z25,z1,z3,z4,z5,z39]),(0,[z0,z1,z586,z3,z4,z5,z6])],[(1,[z0,z1,z3,z4,z5,z289]),(0,[z82,z0,z1,z3,z4,z5,z39]),(0,[z14,z0,z58,z1,z3,z4,z5]),(0,[z0,z1,z3,z587,z4,z5,z6]),(0,[z0,z1,z3,z4,z27,z49,z6])],[(0,[z588,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z11,z157,z5,z6]),(0,[z86,z0,z1,z3,z463,z5,z6]),(0,[z86,z0,z1,z3,z4,z5,z9]),(0,[z0,z1,z589,z3,z4,z5,z6]),(0,[z0,z1,z3,z11,z4,z5,z6]),(0,[z0,z1,z3,z4,z590,z5,z6]),(0,[z0,z591,z1,z3,z4,z5,z6]),(0,[z0,z1,z4,z5,z56,z6,z9]),(0,[z0,z1,z3,z4,z5,z328,z6]),(0,[z21,z0,z1,z3,z20,z4,z5]),(0,[z0,z1,z3,z4,z5,z6,z592])]],
   [[(1,[z0,z1,z3,z4,z5,z313]),(0,[z0,z53,z1,z3,z4,z112,z6]),(0,[z0,z1,z3,z4,z5,z593,z6]),(0,[z0,z1,z3,z4,z5,z456,z6]),(0,[z21,z0,z1,z3,z4,z5,z56])],[(1,[z0,z1,z3,z4,z280,z6]),(0,[z0,z1,z3,z4,z203,z5,z6]),(0,[z14,z173,z0,z1,z3,z4,z5]),(0,[z8,z0,z1,z3,z4,z5,z39]),(0,[z0,z1,z3,z4,z298,z5,z6]),(0,[z305,z0,z1,z3,z4,z5,z6]),(0,[z0,z594,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z408,z4,z69,z5]),(0,[z0,z1,z3,z4,z5,z9,z9]),(0,[z14,z0,z1,z3,z4,z5,z202])],[(0,[z95,z0,z1,z3,z4,z212,z6]),(0,[z300,z0,z1,z3,z4,z5,z6]),(0,[z0,z230,z1,z3,z4,z47,z6]),(0,[z18,z0,z1,z3,z20,z4,z5])],[(0,[z23,z0,z1,z3,z20,z4,z5]),(1,[z0,z1,z3,z4,z5,z306]),(0,[z93,z0,z1,z3,z20,z4,z5]),(1,[z1,z3,z4,z5,z39,z26]),(0,[z0,z58,z1,z3,z20,z4,z5]),(0,[z0,z1,z595,z3,z4,z5,z6]),(0,[z0,z331,z1,z3,z4,z5,z9]),(0,[z18,z0,z343,z3,z4,z5,z6]),(0,[z14,z0,z1,z3,z4,z45,z5])],[(0,[z0,z1,z3,z4,z596,z5,z6]),(1,[z0,z1,z3,z4,z294,z6]),(0,[z0,z1,z3,z4,z5,z6,z174]),(1,[z0,z1,z3,z496,z4,z5]),(0,[z0,z65,z1,z3,z4,z45,z5]),(0,[z0,z1,z3,z4,z13,z5,z9]),(0,[z0,z1,z3,z4,z5,z6,z597])],[(0,[z598,z0,z1,z3,z4,z5,z6]),(0,[z82,z0,z1,z3,z4,z5,z26]),(0,[z0,z117,z1,z3,z12,z4,z6]),(0,[z0,z3,z4,z5,z54,z6,z66]),(0,[z14,z0,z254,z1,z3,z4,z5])],[(1,[z0,z1,z3,z4,z5,z266]),(0,[z0,z1,z3,z77,z20,z4,z5])],[(1,[z128,z171,z3,z4,z5,z6]),(0,[z0,z117,z1,z3,z4,z27,z6]),(0,[z0,z1,z3,z4,z5,z56,z74])]],
   [[(0,[z0,z1,z3,z4,z599,z5,z6]),(0,[z8,z0,z1,z3,z4,z5,z26]),(0,[z0,z1,z3,z20,z4,z5,z6])],[(0,[z0,z1,z273,z3,z4,z5,z6]),(0,[z194,z0,z1,z3,z4,z5,z289]),(0,[z0,z117,z3,z4,z27,z5,z6]),(0,[z0,z443,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z27,z63,z6]),(0,[z600,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z601,z5,z6]),(0,[z0,z1,z3,z602,z4,z5,z6]),(0,[z0,z1,z3,z4,z13,z5,z328])],[(0,[z603,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z318,z39]),(0,[z0,z604,z1,z3,z4,z5,z6]),(0,[z142,z0,z1,z3,z77,z4,z5]),(0,[z0,z1,z3,z605,z4,z5,z6]),(0,[z0,z1,z3,z4,z606,z5,z6]),(1,[z0,z1,z3,z4,z5,z438]),(0,[z0,z1,z3,z20,z5,z74,z6])],[(0,[z0,z1,z607,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z346,z6]),(0,[z0,z1,z3,z608,z4,z5,z6]),(0,[z0,z1,z3,z77,z4,z5,z46])],[(0,[z0,z1,z52,z159,z4,z5,z6]),(1,[z194,z1,z3,z109,z5,z6]),(0,[z86,z0,z1,z3,z277,z5,z6]),(0,[z86,z0,z1,z3,z20,z4,z5]),(0,[z0,z1,z3,z28,z4,z69,z5])],[(0,[z0,z1,z3,z4,z5,z6,z119]),(0,[z0,z1,z3,z609,z4,z5,z6]),(0,[z0,z610,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z103,z20,z4,z5])],[(0,[z128,z0,z273,z3,z4,z5,z6]),(1,[z0,z1,z3,z423,z5,z6]),(0,[z0,z1,z73,z3,z4,z5,z193]),(0,[z0,z1,z3,z4,z5,z215,z6]),(0,[z0,z1,z3,z4,z5,z6,z611]),(1,[z14,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z612,z5,z6])]],
   [[(0,[z0,z1,z3,z4,z13,z5,z39])],[(0,[z0,z476,z1,z3,z4,z109,z5]),(0,[z0,z613,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z614]),(0,[z615,z0,z1,z3,z4,z5,z6]),(0,[z616,z14,z0,z1,z3,z4,z5]),(0,[z14,z0,z1,z3,z77,z4,z5]),(0,[z0,z1,z3,z4,z617,z5,z6])],[(0,[z0,z1,z3,z4,z5,z618,z6]),(0,[z0,z1,z619,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z620,z5,z6])],[(1,[z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z621,z5,z6]),(0,[z0,z1,z3,z622,z4,z5,z6])],[(0,[z14,z0,z1,z3,z52,z4,z5]),(0,[z623,z0,z1,z3,z4,z5,z6]),(0,[z173,z0,z1,z3,z4,z5,z9]),(0,[z0,z217,z31,z3,z4,z5,z6]),(0,[z0,z1,z75,z3,z4,z69,z6]),(0,[z624,z0,z1,z3,z4,z5,z6])],[(1,[z0,z1,z3,z4,z78,z6]),(0,[z625,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z157,z69,z5,z6]),(0,[z86,z37,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z112,z39]),(0,[z0,z1,z3,z4,z5,z478,z6]),(0,[z14,z0,z1,z3,z159,z4,z5]),(0,[z616,z0,z1,z3,z4,z5,z6]),(0,[z0,z356,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z45,z5,z39]),(0,[z0,z3,z141,z4,z47,z5,z6])],[(0,[z0,z1,z3,z4,z626,z5,z6]),(0,[z0,z1,z3,z4,z13,z5,z26]),(0,[z82,z0,z3,z4,z47,z5,z6]),(0,[z0,z1,z3,z4,z627,z5,z6]),(0,[z457,z0,z1,z3,z11,z4,z5]),(1,[z0,z53,z1,z4,z70,z6]),(0,[z0,z628,z1,z3,z4,z5,z6])]],
   [[(0,[z0,z1,z3,z629,z4,z5,z6]),(0,[z0,z1,z3,z52,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z358,z6]),(0,[z630,z0,z1,z3,z4,z5,z6]),(0,[z86,z0,z1,z3,z4,z5,z379]),(0,[z0,z1,z631,z3,z4,z5,z6])],[(0,[z0,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z20,z4,z256,z5]),(0,[z632,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z196,z4,z127,z6]),(0,[z0,z1,z513,z3,z4,z5,z6])],[(0,[z194,z14,z0,z1,z3,z4,z5]),(0,[z633,z0,z1,z3,z4,z5,z6]),(0,[z0,z146,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z56,z202])],[(0,[z0,z1,z3,z634,z4,z5,z6]),(0,[z0,z1,z3,z4,z635,z5,z6]),(0,[z37,z0,z1,z3,z4,z5,z213]),(0,[z0,z1,z3,z636,z4,z5,z6]),(0,[z25,z173,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z26]),(0,[z0,z1,z3,z4,z637,z5,z6]),(0,[z18,z0,z1,z3,z4,z49,z6]),(0,[z14,z0,z1,z3,z20,z5,z6]),(0,[z0,z1,z3,z4,z5,z638,z6])],[(0,[z128,z171,z1,z3,z4,z5,z6]),(0,[z37,z0,z1,z3,z4,z256,z6]),(0,[z0,z1,z3,z4,z5,z112,z26]),(0,[z0,z1,z3,z4,z47,z5,z9]),(0,[z0,z117,z146,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z489]),(1,[z0,z1,z3,z4,z5,z56]),(0,[z0,z1,z3,z639,z4,z5,z6]),(0,[z184,z14,z0,z1,z3,z4,z5])],[(1,[z87,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z45,z5,z26]),(0,[z0,z1,z640,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z641,z6]),(0,[z0,z1,z3,z4,z5,z6,z642]),(0,[z0,z1,z3,z4,z5,z6,z643])],[(0,[z0,z220,z1,z3,z4,z5,z6]),(0,[z0,z644,z1,z3,z4,z5,z6]),(0,[z194,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z12,z4,z256,z6]),(0,[z0,z1,z3,z4,z5,z6,z371])],[(0,[z645,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z141,z4,z5,z39]),(0,[z142,z0,z1,z3,z4,z5,z39]),(0,[z0,z65,z1,z3,z4,z5,z54]),(0,[z0,z1,z3,z4,z5,z6,z646])]],
   [[(0,[z0,z171,z1,z3,z4,z5,z6]),(0,[z0,z273,z3,z159,z4,z5,z6]),(0,[z0,z1,z3,z647,z4,z5,z6]),(0,[z648,z0,z1,z3,z4,z5,z6]),(0,[z82,z18,z0,z1,z3,z5,z6]),(0,[z0,z1,z3,z4,z649,z5,z6]),(0,[z0,z1,z3,z3,z4,z5,z9]),(0,[z650,z0,z1,z3,z4,z5,z6])],[(0,[z651,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z324,z6]),(0,[z0,z1,z3,z52,z4,z5,z56]),(0,[z0,z1,z3,z4,z70,z63,z6]),(0,[z0,z1,z3,z364,z4,z5,z26]),(0,[z0,z1,z3,z159,z4,z5,z56]),(0,[z0,z1,z3,z153,z4,z5,z112])],[(0,[z173,z0,z1,z3,z20,z4,z5]),(0,[z0,z1,z3,z4,z366,z5,z26]),(0,[z0,z1,z3,z4,z5,z6,z66]),(0,[z0,z1,z3,z4,z5,z155,z9])],[(0,[z0,z1,z3,z52,z4,z5,z192]),(0,[z0,z1,z652,z3,z4,z5,z6]),(0,[z0,z1,z3,z20,z4,z45,z5])],[(1,[z0,z1,z3,z303,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z204]),(0,[z0,z1,z3,z4,z653,z5,z6]),(0,[z0,z654,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z655,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z656,z6]),(0,[z0,z1,z3,z20,z4,z375,z5])],[(0,[z0,z1,z3,z657,z4,z5,z6]),(0,[z14,z0,z1,z3,z4,z5,z39]),(0,[z0,z1,z3,z4,z658,z5,z6]),(0,[z0,z1,z3,z4,z659,z5,z6]),(0,[z660,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z191,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z56,z38]),(0,[z0,z1,z3,z4,z5,z661,z6])],[(0,[z51,z93,z1,z3,z4,z5,z6]),(0,[z662,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z663,z6]),(0,[z0,z1,z3,z141,z4,z5,z26]),(0,[z142,z0,z1,z3,z4,z5,z26]),(0,[z0,z1,z3,z664,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z188,z56]),(0,[z665,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z666,z6])],[(0,[z667,z0,z1,z3,z4,z5,z6]),(0,[z194,z0,z1,z3,z4,z5,z56]),(0,[z18,z0,z1,z3,z4,z63,z6]),(0,[z0,z1,z3,z668,z4,z5,z6]),(0,[z669,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z196,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z5,z399]),(1,[z14,z0,z1,z3,z5,z38])]],
   [[(0,[z14,z95,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z39,z283]),(0,[z520,z0,z1,z3,z4,z5,z6]),(0,[z0,z3,z4,z27,z5,z112,z6]),(0,[z0,z1,z3,z4,z69,z5,z6]),(0,[z0,z1,z670,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z506,z5])],[(0,[z93,z1,z73,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z256,z5,z6]),(1,[z86,z1,z3,z4,z256,z6]),(0,[z0,z117,z1,z3,z4,z5,z9]),(0,[z0,z1,z3,z4,z27,z5,z56]),(0,[z184,z0,z1,z3,z4,z5,z56])],[(0,[z0,z1,z3,z4,z5,z671,z6]),(0,[z0,z146,z1,z3,z4,z5,z215]),(0,[z0,z1,z3,z177,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z49,z6])],[(0,[z0,z1,z3,z4,z5,z6,z403]),(0,[z672,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z157,z4,z5,z26]),(0,[z0,z1,z3,z4,z673,z5,z6]),(0,[z0,z1,z3,z4,z674,z5,z6]),(0,[z0,z1,z3,z496,z4,z47,z5]),(0,[z0,z1,z3,z675,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z54,z9])],[(0,[z23,z0,z1,z3,z4,z280,z6]),(0,[z676,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z677,z5,z6]),(0,[z14,z0,z1,z3,z4,z5,z26]),(0,[z82,z0,z1,z3,z47,z5,z6]),(0,[z0,z1,z3,z4,z5,z678,z6]),(0,[z0,z1,z3,z4,z5,z6,z679]),(0,[z0,z1,z3,z4,z5,z680,z6]),(0,[z14,z0,z1,z3,z5,z6,z38])],[(0,[z0,z681,z1,z3,z4,z5,z6]),(0,[z0,z1,z682,z3,z4,z5,z6]),(0,[z683,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z379,z6]),(0,[z684,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z196,z3,z4,z112,z6]),(0,[z142,z0,z1,z3,z4,z5,z66]),(0,[z14,z0,z1,z3,z4,z70,z5]),(0,[z0,z563,z1,z3,z4,z5,z6])],[(0,[z23,z1,z273,z3,z4,z5,z6]),(0,[z685,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z408,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z416]),(0,[z0,z1,z3,z4,z256,z112,z6]),(0,[z686,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z222,z5,z112]),(1,[z0,z1,z3,z4,z375,z5]),(0,[z0,z1,z3,z4,z566,z5,z6])]],
   [[(0,[z14,z128,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z6,z329]),(0,[z0,z1,z31,z3,z4,z5,z6]),(0,[z0,z58,z1,z159,z4,z5,z6]),(1,[z0,z1,z3,z153,z4,z5]),(0,[z687,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z688,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z193,z6]),(0,[z0,z1,z3,z4,z5,z26,z202]),(0,[z0,z1,z3,z4,z5,z199,z6]),(0,[z14,z0,z1,z3,z4,z5,z74])],[(0,[z86,z0,z1,z3,z4,z63,z6]),(0,[z0,z1,z3,z4,z5,z424,z6]),(0,[z0,z1,z3,z4,z5,z433,z6]),(0,[z0,z1,z3,z4,z5,z689,z6]),(0,[z690,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z691,z6]),(0,[z0,z1,z3,z4,z5,z56,z9])],[(0,[z692,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z693,z4,z5,z6]),(0,[z25,z0,z1,z3,z4,z5,z39]),(0,[z0,z64,z1,z3,z4,z5,z9]),(0,[z14,z0,z1,z3,z4,z5,z66]),(0,[z8,z0,z1,z3,z4,z5,z268]),(0,[z0,z1,z3,z4,z5,z49,z56]),(0,[z428,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z109,z5,z56]),(0,[z0,z1,z3,z694,z4,z5,z6]),(0,[z0,z1,z3,z4,z695,z5,z6]),(0,[z0,z1,z3,z4,z5,z696,z6]),(0,[z0,z1,z3,z4,z195,z69,z6]),(0,[z697,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z73,z3,z4,z5,z9]),(0,[z1,z3,z157,z4,z109,z5,z6]),(0,[z0,z1,z3,z4,z5,z96,z6]),(0,[z95,z0,z1,z3,z157,z5,z6]),(0,[z698,z0,z1,z3,z4,z5,z6]),(0,[z0,z217,z1,z31,z4,z5,z6]),(0,[z82,z0,z1,z3,z4,z5,z9]),(0,[z0,z1,z3,z4,z5,z699,z6]),(0,[z0,z1,z3,z700,z4,z5,z6]),(0,[z14,z0,z1,z3,z11,z4,z5]),(0,[z0,z1,z3,z4,z5,z701,z6]),(0,[z0,z702,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z5,z243])],[(0,[z0,z1,z3,z4,z5,z63,z6]),(0,[z0,z1,z3,z4,z5,z703,z6]),(0,[z0,z1,z3,z4,z5,z6,z249]),(0,[z0,z1,z3,z4,z704,z5,z6]),(0,[z14,z340,z0,z1,z3,z4,z5])],[(0,[z14,z0,z1,z3,z157,z4,z5]),(0,[z0,z705,z1,z3,z4,z5,z6]),(0,[z0,z217,z1,z3,z4,z5,z26]),(0,[z0,z53,z1,z3,z4,z5,z39]),(0,[z0,z1,z3,z4,z5,z54,z39]),(0,[z0,z117,z1,z3,z20,z4,z5]),(0,[z0,z1,z3,z4,z5,z6,z374]),(0,[z706,z0,z1,z3,z4,z5,z6]),(0,[z14,z0,z1,z3,z4,z4,z5])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[],[(0,[z0,z1,z3,z110,z5,z56]),(0,[z0,z1,z3,z4,z5,z707])],[(0,[z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z708,z4,z5,z6]),(0,[z0,z1,z3,z709,z4,z5])],[(0,[z0,z1,z3,z710,z5,z6]),(0,[z0,z1,z4,z5,z56,z549]),(0,[z0,z1,z3,z4,z5,z711])],[(0,[z0,z1,z3,z712,z4,z5]),(0,[z0,z220,z3,z4,z5,z306]),(0,[z0,z1,z3,z277,z5,z39]),(0,[z0,z1,z3,z4,z218,z26]),(0,[z0,z1,z3,z4,z5,z713]),(0,[z0,z1,z61,z159,z4,z5]),(0,[z14,z0,z714,z3,z4,z5])],[(0,[z0,z1,z3,z715,z5,z6]),(0,[z0,z1,z3,z4,z5,z716]),(0,[z95,z1,z3,z717,z5,z6]),(0,[z0,z1,z3,z718,z4,z5]),(0,[z0,z1,z10,z11,z5,z6]),(0,[z0,z1,z3,z4,z719,z6])],[(0,[z0,z1,z3,z720,z5,z6]),(0,[z0,z1,z3,z4,z5,z721]),(0,[z722,z0,z1,z3,z303,z5]),(0,[z0,z1,z3,z4,z186,z114]),(0,[z0,z1,z3,z12,z13,z243])],[(0,[z0,z1,z3,z4,z5,z723]),(0,[z0,z1,z3,z4,z5,z724]),(0,[z0,z1,z3,z4,z725,z6])],[(0,[z0,z1,z3,z4,z5,z726]),(0,[z0,z1,z451,z4,z127,z6]),(0,[z14,z0,z1,z3,z200,z5]),(0,[z189,z0,z1,z3,z20,z5]),(0,[z0,z1,z196,z4,z127,z6]),(0,[z0,z1,z3,z727,z4,z5])],[(0,[z0,z1,z3,z4,z203,z9]),(0,[z86,z1,z3,z4,z256,z97]),(0,[z0,z1,z3,z4,z5,z728]),(0,[z0,z1,z4,z70,z5,z330]),(0,[z0,z1,z3,z20,z4,z133]),(0,[z0,z1,z3,z5,z729,z38])],[(0,[z0,z1,z3,z4,z5,z730]),(0,[z0,z1,z3,z177,z4,z5])],[(0,[z0,z1,z587,z4,z5,z9]),(0,[z0,z1,z3,z20,z315,z5])],[(0,[z0,z1,z400,z4,z5,z9]),(0,[z0,z1,z3,z22,z5,z26]),(0,[z87,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z731]),(0,[z0,z1,z3,z191,z4,z5]),(0,[z0,z1,z3,z4,z732,z5]),(0,[z135,z0,z1,z3,z177,z5]),(0,[z0,z1,z3,z4,z5,z733])],[(0,[z0,z1,z3,z4,z5,z192]),(0,[z1,z3,z4,z256,z734,z6]),(0,[z0,z64,z3,z4,z112,z26]),(0,[z1,z3,z4,z375,z5,z26]),(0,[z0,z1,z3,z735,z4,z5]),(0,[z377,z0,z1,z3,z20,z5])],[(0,[z14,z0,z1,z3,z277,z5]),(0,[z0,z1,z3,z4,z5,z736]),(0,[z0,z1,z10,z11,z5,z56]),(0,[z0,z737,z1,z3,z4,z5]),(0,[z233,z0,z1,z4,z506,z5])],[(0,[z0,z1,z3,z4,z738,z6]),(0,[z0,z1,z3,z739,z4,z5]),(0,[z0,z1,z3,z740,z4,z5]),(0,[z1,z3,z4,z5,z741,z6]),(0,[z0,z1,z3,z4,z742,z6]),(0,[z0,z743,z3,z4,z5,z6]),(0,[z0,z1,z744,z3,z4,z5])]],
   [[(0,[z0,z220,z3,z423,z5,z6]),(0,[z745,z0,z1,z3,z463,z5]),(0,[z0,z1,z3,z746,z5,z6]),(0,[z0,z132,z1,z4,z70,z6]),(0,[z1,z3,z4,z5,z39,z418])],[(0,[z0,z1,z3,z4,z5,z747]),(0,[z0,z1,z3,z748,z4,z5]),(0,[z0,z1,z3,z749,z4,z9])],[(0,[z0,z750,z1,z4,z5,z6]),(0,[z751,z0,z1,z3,z5,z6]),(0,[z0,z1,z3,z4,z198,z39]),(0,[z0,z1,z3,z4,z5,z752]),(0,[z0,z1,z3,z4,z753,z5]),(0,[z0,z1,z564,z4,z5,z56]),(0,[z8,z0,z1,z69,z5,z26]),(0,[z0,z1,z3,z754,z4,z5]),(0,[z0,z1,z3,z4,z5,z755]),(0,[z0,z1,z3,z4,z5,z756]),(0,[z0,z1,z3,z4,z5,z757])],[(0,[z0,z1,z3,z20,z110,z5]),(0,[z0,z1,z3,z303,z5,z6]),(0,[z0,z1,z3,z758,z4,z5]),(0,[z189,z0,z1,z3,z5,z39]),(0,[z0,z1,z3,z759,z4,z5])],[(0,[z0,z760,z1,z3,z4,z5])],[(0,[z98,z0,z3,z4,z5,z292])],[(0,[z0,z1,z3,z4,z761,z6]),(0,[z0,z146,z3,z762,z5,z6]),(0,[z0,z1,z3,z145,z4,z202]),(0,[z0,z763,z3,z20,z4,z5])],[(0,[z51,z254,z1,z3,z4,z5]),(0,[z0,z230,z1,z248,z3,z4]),(0,[z0,z117,z3,z4,z27,z9]),(0,[z0,z1,z3,z4,z5,z764])],[(0,[z0,z1,z3,z22,z5,z320])],[(0,[z0,z230,z1,z3,z4,z39])],[(0,[z0,z1,z400,z20,z4,z5]),(0,[z0,z1,z765,z4,z5,z6]),(0,[z0,z343,z196,z3,z4,z6])],[(0,[z0,z150,z3,z141,z5,z6]),(0,[z0,z3,z762,z47,z5,z6]),(0,[z135,z0,z1,z3,z47,z5]),(0,[z0,z1,z3,z4,z6,z766])],[(0,[z0,z129,z73,z4,z5,z6]),(0,[z0,z1,z3,z767,z5,z6]),(0,[z0,z1,z3,z768,z5,z6]),(0,[z0,z343,z3,z4,z256,z6]),(0,[z0,z1,z3,z4,z134,z26]),(0,[z0,z1,z3,z4,z5,z769]),(0,[z0,z3,z4,z770,z5,z6])],[(0,[z0,z1,z3,z4,z5,z771])],[(0,[z0,z1,z3,z4,z124,z6]),(0,[z194,z1,z3,z4,z375,z5]),(0,[z0,z1,z3,z4,z5,z772]),(0,[z0,z1,z248,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z773]),(0,[z774,z0,z1,z3,z4,z5])],[(0,[z0,z1,z3,z4,z5,z775]),(0,[z87,z0,z1,z10,z3,z5]),(0,[z776,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z777,z4,z5]),(0,[z0,z1,z3,z153,z4,z5]),(0,[z189,z0,z1,z196,z3,z6]),(0,[z457,z0,z1,z3,z191,z5]),(0,[z0,z1,z778,z3,z4,z5]),(0,[z18,z14,z0,z1,z3,z49])]],
   [[],[(0,[z51,z1,z52,z4,z5,z324])],[(1,[z1,z779,z4,z5,z6]),(0,[z93,z1,z779,z4,z5,z6]),(0,[z0,z1,z3,z780,z4,z5]),(0,[z0,z3,z4,z770,z112,z6]),(0,[z457,z0,z1,z61,z4,z5])],[],[(0,[z0,z1,z4,z626,z5,z9]),(0,[z14,z0,z1,z3,z463,z5]),(0,[z87,z0,z1,z3,z5,z38]),(0,[z0,z1,z61,z11,z4,z5]),(0,[z0,z1,z3,z4,z781,z6])],[(0,[z23,z273,z3,z4,z280,z6]),(0,[z0,z1,z3,z4,z5,z782]),(0,[z0,z1,z3,z4,z783,z5])],[(0,[z0,z1,z3,z784,z4,z5]),(0,[z472,z1,z3,z109,z5,z6]),(0,[z0,z1,z3,z4,z182,z39]),(0,[z0,z1,z3,z777,z4,z294]),(0,[z0,z1,z3,z785,z4,z5]),(0,[z14,z0,z1,z3,z5,z339]),(0,[z0,z1,z75,z3,z4,z9]),(0,[z0,z1,z3,z4,z5,z786]),(0,[z0,z1,z3,z4,z787,z5])],[(0,[z0,z1,z3,z4,z124,z56]),(0,[z0,z331,z3,z4,z5,z66]),(0,[z0,z1,z11,z4,z506,z5]),(0,[z0,z1,z3,z12,z13,z6])],[(0,[z14,z93,z1,z73,z4,z5]),(0,[z0,z1,z3,z4,z788,z5]),(0,[z14,z0,z1,z3,z5,z55]),(0,[z0,z1,z3,z20,z5,z729])],[(0,[z0,z288,z159,z4,z5,z6]),(0,[z0,z1,z3,z4,z789,z6]),(0,[z0,z1,z3,z4,z5,z790]),(0,[z0,z1,z3,z4,z5,z791])],[(0,[z0,z1,z3,z4,z792,z6]),(0,[z0,z1,z3,z4,z5,z793]),(0,[z0,z1,z3,z4,z794,z6]),(0,[z0,z1,z3,z4,z5,z795]),(0,[z0,z1,z3,z4,z5,z796]),(0,[z189,z0,z64,z3,z112,z6]),(0,[z0,z1,z3,z4,z5,z797])],[(0,[z0,z798,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z799]),(0,[z93,z1,z3,z4,z5,z123]),(0,[z0,z1,z196,z20,z4,z127]),(0,[z0,z1,z3,z4,z45,z46])],[(0,[z800,z0,z1,z3,z4,z5]),(0,[z0,z1,z31,z61,z4,z5]),(0,[z0,z1,z3,z4,z5,z801]),(0,[z802,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z803,z4,z5])],[(0,[z0,z1,z3,z4,z280,z39]),(0,[z0,z1,z3,z4,z5,z297]),(0,[z0,z1,z3,z463,z5,z9]),(0,[z14,z0,z1,z765,z4,z5])],[(0,[z173,z1,z3,z4,z5,z804]),(0,[z0,z1,z805,z4,z5,z6]),(0,[z0,z1,z3,z4,z6,z791])],[(0,[z0,z58,z159,z4,z5,z478]),(0,[z0,z1,z3,z4,z5,z806])]],
   [[(0,[z0,z807,z1,z3,z4,z5]),(0,[z25,z1,z3,z4,z5,z804]),(0,[z0,z443,z3,z20,z4,z5])],[(0,[z0,z1,z3,z4,z5,z808]),(1,[z0,z1,z3,z5,z729])],[(0,[z809,z1,z3,z4,z5,z6]),(0,[z82,z0,z230,z1,z3,z6])],[(0,[z51,z0,z1,z61,z4,z5]),(0,[z14,z95,z1,z3,z157,z5]),(0,[z0,z1,z3,z4,z5,z810]),(0,[z0,z1,z3,z20,z4,z218]),(0,[z0,z1,z3,z811,z4,z5]),(0,[z0,z1,z812,z4,z5,z6])],[(0,[z0,z1,z3,z813,z5,z6]),(0,[z51,z1,z52,z4,z5,z166]),(0,[z0,z1,z3,z814,z5,z6]),(0,[z0,z1,z3,z4,z5,z815]),(0,[z0,z1,z3,z816,z5,z6]),(0,[z0,z1,z3,z4,z218,z9]),(0,[z0,z3,z4,z27,z770,z6])],[(0,[z0,z1,z3,z4,z5,z817]),(0,[z59,z273,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z818]),(0,[z819,z0,z1,z3,z4,z5])],[(0,[z0,z1,z3,z4,z5,z820]),(0,[z93,z1,z73,z4,z5,z39]),(0,[z0,z1,z3,z4,z821,z6]),(0,[z0,z486,z3,z4,z5,z54])],[(0,[z0,z1,z3,z5,z267,z9]),(0,[z0,z1,z3,z4,z195,z6])],[(0,[z0,z563,z1,z3,z4,z302])],[(0,[z822,z0,z1,z3,z110,z5]),(0,[z194,z1,z3,z109,z5,z39]),(0,[z0,z1,z3,z4,z823,z6]),(0,[z0,z1,z405,z11,z5,z6]),(0,[z0,z1,z3,z4,z5,z824])],[(0,[z93,z1,z73,z4,z5,z89]),(0,[z0,z1,z825,z4,z5,z6]),(0,[z62,z0,z1,z4,z5,z56])],[(0,[z0,z1,z3,z423,z5,z39]),(0,[z0,z1,z3,z4,z5,z330]),(0,[z14,z37,z1,z3,z4,z63]),(0,[z135,z0,z1,z3,z20,z5])],[(0,[z0,z1,z3,z4,z5,z826]),(0,[z228,z0,z3,z4,z5,z226]),(0,[z0,z1,z3,z4,z5,z827]),(0,[z0,z343,z3,z4,z5,z9]),(0,[z0,z1,z3,z4,z828,z56])],[(0,[z0,z1,z3,z4,z829,z6])],[(0,[z0,z1,z3,z830,z5,z6]),(0,[z0,z1,z4,z831,z5,z6]),(0,[z0,z1,z3,z832,z463,z5]),(0,[z0,z1,z3,z4,z5,z833]),(0,[z0,z1,z4,z5,z834,z9])],[(0,[z0,z1,z4,z5,z424,z9]),(0,[z0,z1,z3,z4,z5,z835])]],
   [[(0,[z0,z1,z3,z4,z5,z836]),(0,[z0,z1,z3,z4,z195,z56])],[(0,[z0,z1,z3,z4,z5,z837]),(0,[z189,z0,z117,z1,z3,z6])],[(0,[z0,z1,z3,z4,z5,z838]),(0,[z672,z0,z3,z47,z5,z6]),(0,[z0,z117,z230,z3,z4,z6]),(0,[z0,z1,z4,z781,z127,z6])],[(0,[z0,z1,z400,z4,z280,z6]),(0,[z14,z0,z230,z1,z3,z4])],[(0,[z0,z1,z3,z4,z5,z839]),(0,[z0,z1,z3,z4,z5,z840]),(0,[z0,z1,z3,z4,z5,z841]),(0,[z0,z1,z3,z4,z842,z5]),(0,[z0,z1,z3,z4,z45,z791])],[(0,[z0,z1,z3,z843,z5,z6])],[(0,[z0,z1,z3,z4,z844,z6]),(0,[z0,z1,z3,z4,z845,z6]),(0,[z0,z1,z3,z846,z4,z5])],[(0,[z1,z3,z4,z5,z26,z643]),(0,[z0,z1,z3,z4,z5,z847])],[(0,[z0,z1,z3,z4,z280,z416]),(0,[z0,z1,z3,z4,z78,z26]),(0,[z0,z217,z31,z4,z5,z39]),(0,[z0,z1,z3,z4,z5,z848])],[(0,[z0,z1,z3,z849,z110,z5]),(0,[z0,z1,z3,z4,z5,z850]),(0,[z0,z1,z3,z4,z5,z851])],[(0,[z14,z0,z1,z3,z110,z5]),(0,[z852,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z5,z267,z26]),(0,[z0,z1,z3,z4,z5,z853]),(0,[z189,z0,z64,z1,z3,z6]),(0,[z0,z343,z3,z20,z4,z5]),(0,[z0,z1,z3,z4,z45,z175])],[(0,[z0,z1,z3,z4,z854,z6]),(0,[z855,z0,z1,z3,z4,z5]),(0,[z0,z856,z1,z4,z5,z39]),(0,[z0,z1,z3,z4,z857,z5]),(0,[z0,z858,z1,z3,z4,z5]),(0,[z142,z0,z3,z4,z5,z54])],[(0,[z0,z1,z3,z859,z5,z6]),(0,[z0,z1,z3,z4,z5,z860]),(0,[z0,z1,z196,z4,z127,z26]),(0,[z0,z1,z3,z4,z5,z861]),(0,[z0,z1,z3,z4,z134,z9]),(0,[z0,z230,z1,z3,z20,z4]),(0,[z457,z0,z1,z3,z5,z279]),(0,[z0,z1,z3,z4,z566,z202])],[(0,[z0,z1,z3,z4,z198,z324]),(0,[z93,z1,z73,z4,z5,z403]),(0,[z0,z1,z3,z4,z5,z862]),(0,[z0,z1,z3,z4,z863,z5]),(0,[z457,z0,z1,z10,z11,z5]),(0,[z0,z1,z3,z4,z864,z5])],[(0,[z0,z1,z3,z4,z5,z865]),(0,[z0,z1,z3,z423,z203,z6]),(0,[z722,z0,z1,z3,z4,z5]),(0,[z95,z1,z3,z157,z5,z6]),(0,[z1,z3,z103,z4,z375,z5]),(0,[z0,z1,z3,z4,z5,z866]),(0,[z18,z0,z1,z3,z20,z49])],[(0,[z0,z867,z1,z3,z4,z5]),(0,[z18,z0,z1,z3,z281,z6]),(0,[z0,z343,z3,z4,z5,z26]),(0,[z0,z1,z3,z4,z5,z868]),(0,[z0,z1,z3,z869,z5,z6]),(0,[z0,z1,z3,z222,z5,z267])]],
   [[(0,[z0,z1,z3,z4,z5,z193]),(1,[z1,z3,z717,z5,z6]),(0,[z0,z1,z3,z4,z5,z32]),(0,[z0,z1,z259,z4,z5,z9]),(0,[z0,z164,z1,z4,z5,z56])],[(0,[z14,z0,z220,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z870])],[(0,[z0,z1,z3,z4,z5,z871]),(0,[z0,z872,z3,z4,z5,z6]),(0,[z0,z1,z3,z408,z4,z195])],[(0,[z0,z1,z3,z4,z5,z873]),(0,[z0,z1,z3,z874,z4,z5]),(0,[z0,z1,z3,z875,z49,z6])],[(0,[z0,z1,z3,z4,z78,z320]),(0,[z0,z1,z3,z277,z5,z379]),(0,[z0,z1,z3,z876,z4,z5]),(0,[z0,z1,z3,z877,z4,z5]),(0,[z14,z0,z1,z3,z5,z260])],[(0,[z0,z1,z878,z4,z5,z6]),(0,[z0,z1,z3,z879,z4,z5]),(0,[z86,z1,z3,z4,z256,z39]),(0,[z82,z0,z3,z47,z5,z39]),(0,[z0,z1,z3,z4,z5,z880]),(0,[z0,z1,z3,z20,z639,z5]),(0,[z457,z0,z1,z238,z4,z5])],[(0,[z0,z1,z3,z4,z5,z881]),(0,[z352,z1,z3,z4,z5,z26]),(0,[z0,z1,z3,z4,z5,z882])],[(0,[z95,z1,z3,z157,z5,z56]),(0,[z883,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z77,z4,z283]),(0,[z0,z31,z884,z4,z5,z6]),(0,[z0,z1,z3,z12,z190,z6])],[(0,[z0,z230,z146,z1,z3,z6])],[(0,[z0,z1,z3,z885,z5,z6]),(0,[z0,z1,z3,z4,z5,z42])],[(0,[z0,z1,z3,z4,z5,z886])],[],[(0,[z0,z1,z3,z4,z5,z887]),(0,[z0,z1,z3,z4,z888,z5]),(0,[z0,z158,z3,z4,z5,z66]),(0,[z0,z1,z75,z3,z28,z4]),(0,[z0,z1,z10,z11,z5,z42])],[(0,[z0,z1,z3,z4,z5,z889]),(0,[z0,z1,z890,z4,z5,z6]),(0,[z0,z53,z1,z4,z781,z6])],[(0,[z0,z1,z3,z4,z5,z891]),(0,[z0,z1,z3,z12,z13,z328])],[(0,[z0,z1,z3,z4,z5,z892]),(0,[z1,z3,z4,z5,z556,z26]),(0,[z0,z1,z3,z4,z5,z893]),(0,[z14,z0,z1,z3,z5,z729])]],
   [[],[(0,[z0,z1,z3,z4,z5,z894]),(0,[z414,z171,z3,z4,z5,z6])],[(0,[z194,z254,z1,z3,z4,z5]),(0,[z0,z1,z4,z5,z895,z6]),(0,[z0,z1,z3,z4,z5,z896]),(0,[z0,z1,z4,z5,z56,z483])],[(0,[z0,z1,z75,z3,z109,z6]),(0,[z0,z1,z897,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z898]),(0,[z0,z1,z3,z4,z5,z899]),(0,[z900,z0,z1,z3,z4,z5]),(0,[z0,z343,z3,z4,z49,z6]),(0,[z169,z340,z1,z3,z4,z5])],[(0,[z632,z1,z73,z4,z5,z6]),(0,[z0,z64,z3,z153,z4,z112]),(0,[z0,z308,z3,z4,z5,z54]),(0,[z8,z0,z1,z69,z5,z154])],[(0,[z0,z1,z3,z901,z4,z6]),(0,[z0,z1,z3,z4,z5,z902])],[(0,[z51,z1,z52,z4,z5,z6]),(0,[z0,z88,z159,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z903]),(0,[z0,z1,z3,z4,z5,z904]),(0,[z0,z53,z1,z61,z4,z5]),(0,[z0,z1,z3,z4,z5,z905]),(0,[z0,z906,z1,z3,z4,z5])],[(0,[z0,z1,z3,z4,z212,z96]),(0,[z0,z1,z3,z4,z5,z907])],[(0,[z0,z1,z3,z4,z908,z6]),(0,[z82,z0,z3,z47,z134,z6]),(0,[z0,z1,z275,z4,z5,z9])],[(0,[z0,z909,z3,z4,z5,z6]),(0,[z0,z1,z910,z3,z4,z5]),(0,[z0,z1,z3,z4,z911,z6]),(0,[z189,z0,z343,z3,z5,z6]),(0,[z0,z912,z1,z3,z4,z5]),(0,[z0,z1,z196,z4,z440,z6]),(0,[z0,z1,z3,z4,z5,z913])],[(0,[z14,z0,z1,z3,z4,z218])],[(0,[z0,z1,z3,z12,z13,z26])],[(0,[z914,z0,z1,z3,z22,z5]),(0,[z0,z1,z3,z4,z915,z6]),(0,[z0,z1,z3,z4,z5,z916]),(0,[z0,z1,z3,z4,z182,z56]),(0,[z917,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z153,z5,z267])],[(0,[z23,z273,z102,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z918]),(0,[z0,z1,z3,z4,z5,z919])],[(0,[z0,z3,z4,z5,z54,z920]),(0,[z0,z921,z3,z4,z5,z6])],[(0,[z0,z1,z922,z4,z5,z6]),(0,[z0,z1,z3,z923,z5,z6]),(0,[z51,z1,z52,z4,z5,z56]),(0,[z0,z1,z3,z4,z924,z5]),(0,[z0,z1,z3,z4,z5,z925]),(0,[z0,z217,z1,z4,z5,z330]),(0,[z0,z230,z343,z3,z4,z6]),(0,[z425,z0,z390,z3,z4,z5]),(0,[z14,z926,z1,z3,z4,z5])]],
   [[(0,[z0,z1,z3,z901,z4,z192])],[(0,[z51,z1,z52,z4,z5,z192]),(0,[z0,z1,z3,z20,z384,z5]),(0,[z0,z1,z3,z927,z5,z6])],[(0,[z0,z1,z3,z4,z5,z928]),(0,[z0,z1,z3,z929,z4,z5]),(0,[z29,z1,z3,z4,z256,z6]),(0,[z0,z1,z3,z930,z4,z5]),(0,[z1,z3,z4,z5,z39,z804]),(0,[z0,z1,z3,z4,z931,z6]),(0,[z0,z1,z3,z4,z45,z562])],[(0,[z0,z1,z3,z22,z280,z6]),(0,[z128,z254,z1,z3,z4,z5]),(0,[z14,z0,z1,z3,z303,z5]),(0,[z0,z1,z3,z4,z294,z39]),(0,[z0,z1,z3,z4,z932,z5])],[(0,[z0,z1,z3,z167,z109,z5]),(0,[z0,z58,z159,z4,z5,z6]),(0,[z0,z1,z3,z933,z5,z6]),(0,[z0,z1,z3,z4,z5,z934]),(0,[z0,z935,z3,z4,z5,z6])],[(0,[z0,z1,z102,z4,z5,z39]),(0,[z936,z0,z1,z3,z4,z5]),(0,[z937,z0,z1,z3,z4,z5])],[(0,[z0,z1,z3,z4,z5,z9]),(0,[z0,z1,z3,z423,z5,z324]),(0,[z0,z1,z3,z938,z303,z5]),(0,[z0,z1,z3,z4,z828,z6]),(0,[z0,z1,z10,z927,z5,z6]),(0,[z0,z1,z3,z77,z4,z170])],[(0,[z51,z1,z52,z303,z5,z6]),(0,[z0,z1,z90,z4,z5,z9]),(0,[z0,z217,z884,z4,z5,z6]),(0,[z0,z1,z4,z5,z231,z9])],[(0,[z0,z1,z3,z4,z78,z9]),(0,[z0,z1,z3,z4,z5,z939]),(0,[z0,z1,z3,z4,z5,z940]),(0,[z0,z1,z3,z4,z5,z941]),(0,[z0,z146,z3,z141,z5,z215])],[],[(0,[z942,z0,z1,z3,z5,z6]),(0,[z0,z1,z3,z167,z5,z74]),(0,[z0,z1,z943,z3,z4,z6]),(0,[z0,z1,z4,z5,z9,z239])],[(0,[z0,z1,z3,z944,z22,z5]),(0,[z0,z1,z3,z938,z4,z5]),(0,[z0,z1,z3,z4,z5,z945]),(0,[z93,z1,z73,z4,z5,z94])],[(0,[z93,z1,z73,z4,z5,z56]),(0,[z0,z1,z73,z4,z5,z424]),(0,[z0,z1,z3,z4,z5,z946]),(0,[z1,z3,z622,z4,z5,z39]),(0,[z0,z1,z4,z927,z5,z6]),(0,[z0,z1,z196,z4,z127,z9]),(0,[z0,z1,z3,z4,z5,z328])],[(0,[z189,z0,z1,z3,z63,z6]),(0,[z0,z58,z159,z4,z5,z56]),(0,[z0,z1,z3,z4,z947,z5]),(0,[z0,z1,z3,z4,z5,z948])],[(0,[z118,z1,z3,z4,z5,z39]),(0,[z0,z1,z3,z4,z5,z949]),(0,[z0,z1,z3,z4,z5,z950])],[(0,[z0,z1,z3,z110,z5,z26]),(0,[z0,z129,z3,z4,z5,z39]),(0,[z0,z1,z3,z20,z303,z5]),(0,[z59,z1,z3,z4,z5,z26]),(0,[z0,z1,z3,z4,z951,z6]),(0,[z0,z1,z3,z952,z4,z5]),(0,[z0,z1,z3,z4,z5,z834])]],
   [[(0,[z0,z1,z3,z953,z5,z6]),(0,[z0,z1,z3,z103,z4,z5]),(0,[z194,z135,z0,z1,z3,z5]),(0,[z0,z1,z3,z4,z133,z39]),(0,[z189,z0,z3,z47,z5,z6]),(0,[z0,z1,z3,z4,z222,z5])],[(0,[z0,z1,z3,z954,z4,z5]),(0,[z1,z631,z3,z4,z5,z39]),(0,[z0,z1,z11,z927,z5,z6])],[(0,[z169,z0,z1,z3,z5,z55])],[(0,[z0,z1,z3,z4,z5,z955]),(0,[z0,z1,z10,z4,z5,z330]),(0,[z0,z1,z3,z4,z5,z956])],[(0,[z0,z1,z3,z4,z5,z957]),(0,[z0,z1,z3,z4,z5,z958])],[(0,[z0,z1,z3,z4,z959,z6]),(0,[z0,z1,z3,z4,z203,z306]),(0,[z237,z1,z3,z4,z63,z6])],[(0,[z0,z53,z1,z4,z70,z39]),(0,[z0,z1,z3,z4,z5,z960]),(0,[z0,z1,z3,z4,z5,z961])],[(0,[z0,z1,z3,z4,z5,z962]),(0,[z0,z1,z3,z303,z5,z9]),(0,[z0,z1,z3,z4,z5,z963]),(0,[z1,z3,z157,z717,z5,z6]),(0,[z169,z0,z1,z765,z4,z5]),(0,[z0,z1,z3,z964,z4,z133]),(0,[z0,z1,z3,z965,z4,z5]),(0,[z0,z1,z688,z4,z5,z9])],[(0,[z0,z560,z3,z4,z112,z6]),(0,[z0,z1,z927,z69,z5,z6]),(0,[z0,z1,z4,z5,z56,z9])],[(0,[z0,z1,z3,z4,z5,z26]),(0,[z0,z1,z3,z4,z966,z6]),(0,[z0,z1,z3,z4,z5,z967])],[(0,[z0,z1,z3,z4,z5,z968]),(0,[z0,z3,z4,z969,z5,z6]),(0,[z0,z1,z970,z4,z5,z6]),(0,[z0,z230,z1,z3,z496,z4])],[(0,[z0,z1,z3,z110,z5,z320]),(0,[z0,z1,z779,z4,z5,z6]),(0,[z0,z1,z971,z3,z4,z6]),(0,[z0,z1,z3,z4,z972,z6]),(0,[z0,z1,z3,z973,z5,z6])],[(0,[z0,z1,z3,z4,z5,z974]),(0,[z86,z1,z3,z463,z256,z6]),(0,[z0,z1,z10,z11,z5,z26]),(0,[z0,z1,z61,z4,z5,z127]),(0,[z0,z1,z3,z4,z46,z791])],[(0,[z0,z1,z3,z975,z4,z5]),(0,[z0,z1,z3,z4,z5,z976]),(0,[z169,z95,z1,z3,z157,z5]),(0,[z0,z1,z3,z277,z5,z56]),(0,[z0,z1,z3,z977,z4,z6]),(0,[z0,z1,z3,z4,z978,z6]),(0,[z0,z65,z3,z4,z5,z66])],[(0,[z0,z1,z979,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z980]),(0,[z0,z1,z3,z981,z5,z6]),(0,[z0,z217,z31,z4,z5,z56])],[(0,[z0,z1,z982,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z983]),(0,[z0,z1,z3,z20,z4,z203]),(0,[z14,z984,z1,z3,z4,z5])]],
   [[(0,[z0,z1,z102,z4,z5,z416]),(0,[z0,z1,z4,z5,z56,z330]),(0,[z0,z1,z3,z4,z985,z6]),(0,[z0,z1,z3,z4,z5,z986]),(0,[z0,z1,z351,z4,z5,z9]),(0,[z0,z1,z196,z4,z781,z6])],[(0,[z14,z0,z1,z3,z380,z5]),(0,[z0,z1,z3,z11,z191,z5]),(0,[z0,z1,z4,z5,z56,z834]),(0,[z14,z0,z343,z3,z4,z5])],[(0,[z1,z987,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z198,z6]),(0,[z0,z129,z3,z4,z203,z6]),(0,[z0,z1,z3,z4,z212,z39])],[(0,[z0,z1,z3,z988,z4,z5]),(0,[z14,z0,z1,z3,z617,z5])],[(0,[z0,z220,z3,z4,z5,z39]),(0,[z0,z1,z3,z4,z5,z123]),(0,[z14,z0,z1,z3,z167,z5]),(0,[z82,z0,z3,z218,z47,z6])],[(0,[z0,z1,z3,z4,z5,z320]),(0,[z254,z1,z73,z3,z4,z5]),(0,[z0,z1,z3,z4,z989,z5]),(0,[z0,z1,z177,z4,z506,z5]),(0,[z990,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z77,z4,z791])],[(0,[z86,z14,z1,z3,z4,z256]),(0,[z991,z0,z1,z3,z4,z5]),(0,[z0,z1,z172,z4,z5,z330]),(0,[z142,z0,z3,z4,z5,z920])],[(0,[z0,z1,z3,z4,z5,z992])],[(0,[z0,z65,z3,z4,z5,z147]),(0,[z235,z0,z1,z3,z20,z5]),(0,[z14,z0,z1,z196,z4,z127])],[(0,[z0,z230,z1,z3,z4,z6]),(0,[z135,z0,z1,z3,z69,z5])],[(0,[z0,z1,z3,z303,z5,z26]),(0,[z1,z3,z4,z5,z166,z123]),(0,[z0,z1,z3,z4,z993,z5]),(0,[z0,z1,z3,z4,z5,z994])],[(0,[z995,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z198,z56]),(0,[z82,z0,z3,z47,z5,z56]),(0,[z0,z1,z3,z12,z13,z9])],[(0,[z0,z1,z3,z4,z996,z6]),(0,[z189,z0,z1,z3,z5,z56]),(0,[z0,z1,z3,z4,z997,z6])],[(0,[z0,z1,z3,z4,z5,z998]),(0,[z93,z1,z3,z4,z5,z155]),(0,[z0,z1,z3,z4,z999,z6]),(0,[z0,z1,z3,z28,z4,z5])],[(0,[z0,z1000,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z5,z1001]),(0,[z373,z1,z3,z4,z5,z26])],[(0,[z0,z3,z4,z1002,z5,z6]),(0,[z0,z1,z3,z4,z5,z1003])]],
   [[(0,[z0,z1,z3,z4,z1004,z5]),(0,[z0,z1,z3,z1005,z4,z5])],[(0,[z0,z1,z3,z4,z993,z294]),(0,[z245,z1,z3,z4,z5,z155])],[(0,[z0,z230,z1,z3,z4,z56])],[(0,[z0,z1,z3,z303,z198,z6])],[(0,[z0,z1,z3,z4,z5,z1006]),(0,[z0,z1,z3,z4,z1007,z6]),(0,[z633,z0,z1,z69,z5,z6]),(0,[z0,z1,z1008,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z1009]),(0,[z0,z1,z224,z4,z5,z9])],[(0,[z0,z1,z3,z4,z124,z26]),(0,[z86,z1,z3,z4,z256,z379]),(0,[z0,z146,z3,z141,z5,z39])],[(0,[z0,z1,z3,z4,z182,z6]),(0,[z0,z1,z3,z4,z5,z1010]),(0,[z0,z1,z362,z4,z5,z9])],[(0,[z0,z1,z3,z20,z4,z280]),(0,[z0,z220,z3,z4,z203,z6]),(0,[z745,z0,z1,z3,z4,z5]),(0,[z14,z0,z1,z3,z206,z5]),(0,[z135,z0,z1,z3,z13,z5])],[(0,[z0,z1,z3,z4,z1011,z6]),(0,[z18,z0,z1,z3,z345,z6]),(0,[z1012,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z1013,z5,z6]),(0,[z0,z1,z3,z816,z5,z9]),(0,[z0,z1,z3,z20,z4,z761])],[(0,[z0,z1,z3,z106,z13,z6]),(0,[z0,z1,z3,z4,z5,z1014]),(0,[z0,z64,z343,z3,z4,z6]),(0,[z0,z1,z75,z3,z408,z4]),(0,[z0,z53,z1,z4,z70,z374]),(0,[z0,z1,z386,z4,z5,z56])],[(0,[z822,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z1015]),(0,[z0,z1,z3,z4,z1016,z6]),(0,[z0,z1,z1017,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1018])],[(0,[z0,z1,z3,z4,z5,z1019]),(0,[z14,z0,z53,z1,z4,z70])],[(0,[z0,z1,z1020,z4,z5,z6]),(0,[z1,z3,z4,z5,z804,z6]),(0,[z0,z1,z3,z4,z5,z1021])],[(0,[z0,z1,z3,z1022,z4,z5]),(0,[z0,z1,z3,z1023,z4,z5]),(0,[z95,z1,z3,z157,z124,z6]),(0,[z285,z1,z3,z4,z5,z39]),(0,[z0,z1,z3,z1024,z4,z5]),(0,[z0,z1,z3,z4,z5,z199])],[(0,[z0,z129,z52,z4,z5,z6]),(0,[z0,z1,z3,z4,z212,z329]),(0,[z173,z1,z3,z4,z5,z26]),(0,[z0,z58,z1,z4,z5,z330]),(0,[z0,z1,z3,z4,z1025,z6]),(0,[z14,z0,z1,z3,z178,z5])],[(0,[z0,z1,z3,z110,z5,z9]),(0,[z0,z1,z3,z4,z5,z1026])]],
   [[(0,[z0,z1,z3,z4,z1027,z6]),(0,[z184,z0,z1,z4,z5,z424]),(0,[z0,z1,z3,z4,z5,z1028])],[],[(0,[z1,z3,z81,z4,z5,z26]),(0,[z0,z308,z3,z4,z5,z188])],[(0,[z128,z171,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1029]),(0,[z0,z1,z3,z4,z6,z1030]),(0,[z1031,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z1032]),(0,[z1,z3,z4,z5,z1033,z6])],[(0,[z0,z1,z3,z1034,z4,z5]),(0,[z1,z3,z115,z4,z5,z39]),(0,[z18,z0,z1,z3,z291,z6]),(0,[z0,z1,z3,z20,z216,z5])],[(0,[z0,z1,z3,z4,z280,z56]),(0,[z93,z1,z73,z4,z5,z6]),(0,[z287,z1,z3,z157,z5,z6]),(0,[z0,z1,z3,z4,z5,z1035]),(0,[z0,z1,z3,z1036,z4,z5]),(0,[z0,z58,z884,z4,z5,z6]),(0,[z0,z253,z3,z4,z5,z147])],[(0,[z23,z273,z3,z4,z5,z39]),(0,[z0,z1,z3,z4,z5,z1037]),(0,[z1038,z0,z1,z3,z4,z5]),(0,[z189,z0,z1,z3,z13,z6])],[(0,[z0,z1,z3,z4,z1039,z6]),(0,[z0,z1,z3,z4,z1040,z5]),(0,[z14,z0,z1,z3,z139,z5])],[(0,[z194,z1,z3,z109,z5,z6]),(0,[z0,z1,z3,z717,z5,z6]),(0,[z0,z1,z3,z1041,z4,z5]),(0,[z0,z1,z3,z4,z294,z56])],[(0,[z0,z1,z3,z849,z4,z5]),(0,[z0,z1,z3,z1042,z4,z5]),(0,[z0,z129,z3,z4,z5,z324])],[(0,[z14,z0,z1,z3,z4,z5]),(0,[z0,z1,z102,z22,z5,z6]),(0,[z0,z1,z3,z1043,z5,z6]),(0,[z14,z128,z171,z3,z4,z5]),(0,[z194,z1,z3,z20,z109,z5]),(0,[z300,z0,z1,z4,z5,z166]),(0,[z0,z1,z3,z1044,z4,z5]),(0,[z14,z1031,z1,z3,z4,z5]),(0,[z163,z1,z3,z4,z375,z5])],[(0,[z0,z1,z3,z4,z1045,z6]),(0,[z0,z1046,z3,z4,z5,z6]),(0,[z0,z1,z3,z655,z13,z6]),(0,[z0,z1,z10,z11,z5,z9]),(0,[z305,z0,z3,z4,z332,z5])],[(0,[z0,z1,z3,z20,z4,z134]),(0,[z1,z3,z4,z5,z1033,z56]),(0,[z520,z0,z486,z3,z4,z5])],[(0,[z0,z1,z3,z4,z195,z26]),(0,[z0,z1,z3,z1047,z5,z6]),(0,[z82,z0,z343,z3,z5,z6]),(0,[z189,z0,z146,z3,z5,z6])],[(0,[z86,z1,z3,z4,z734,z6]),(0,[z18,z0,z1,z3,z49,z39])]],
   [[],[(0,[z0,z1,z3,z1048,z4,z5]),(0,[z0,z1,z3,z4,z875,z6])],[(0,[z0,z1,z102,z4,z5,z1049]),(0,[z194,z1,z3,z109,z5,z56]),(0,[z1,z3,z4,z612,z5,z26]),(0,[z18,z0,z1,z3,z438,z49]),(0,[z0,z1,z3,z12,z875,z6])],[(0,[z1,z3,z717,z109,z5,z6]),(0,[z0,z1,z3,z4,z5,z1050])],[(0,[z0,z1,z3,z4,z5,z1051]),(0,[z0,z1,z3,z4,z5,z1052]),(0,[z0,z1,z3,z423,z5,z56]),(0,[z0,z1,z3,z4,z5,z1053]),(0,[z0,z1,z10,z177,z11,z5]),(0,[z0,z1,z3,z1054,z4,z5])],[(0,[z0,z64,z3,z4,z222,z112])],[(0,[z14,z0,z1,z3,z4,z203]),(0,[z0,z1,z3,z1055,z4,z5])],[(0,[z0,z1,z3,z20,z4,z5]),(0,[z665,z1,z3,z109,z5,z6]),(0,[z0,z1,z3,z277,z5,z6]),(0,[z0,z146,z3,z141,z5,z249])],[(0,[z0,z1,z3,z4,z1056,z5]),(0,[z0,z1,z3,z4,z5,z1057]),(0,[z0,z343,z3,z157,z5,z6]),(0,[z0,z217,z31,z4,z5,z6]),(0,[z0,z1,z3,z1058,z4,z5])],[(0,[z0,z1,z3,z4,z5,z1059]),(0,[z37,z1,z3,z4,z63,z213]),(0,[z0,z1,z3,z1060,z4,z5])],[(0,[z0,z1,z3,z4,z5,z1061]),(0,[z0,z1,z3,z4,z5,z1062]),(0,[z0,z1,z1063,z4,z5,z39]),(0,[z0,z1,z3,z77,z4,z202])],[(0,[z0,z856,z1,z4,z5,z6]),(0,[z1,z3,z4,z161,z5,z26]),(0,[z0,z1,z3,z4,z5,z1064]),(0,[z0,z1,z3,z4,z5,z1065]),(0,[z18,z0,z117,z146,z3,z6])],[(0,[z0,z1,z3,z1066,z5,z6]),(0,[z0,z1,z3,z1067,z4,z5]),(0,[z0,z1,z3,z4,z1068,z5]),(0,[z0,z1,z3,z4,z5,z1069]),(0,[z0,z1,z3,z1070,z4,z5]),(0,[z0,z53,z1,z4,z70,z56])],[(0,[z23,z273,z400,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1071]),(0,[z0,z1,z3,z4,z1072,z6])],[(0,[z0,z1,z3,z4,z1073,z6]),(0,[z0,z1,z3,z20,z4,z294])],[(0,[z0,z220,z3,z4,z5,z324]),(0,[z0,z1,z1074,z3,z4,z6]),(0,[z1075,z0,z1,z3,z4,z5]),(0,[z72,z0,z1,z3,z4,z170])]],
   [[(0,[z1,z3,z4,z1076,z5,z6]),(0,[z14,z0,z1,z3,z4,z1077])],[(0,[z0,z1,z3,z20,z5,z267])],[(0,[z23,z273,z3,z4,z5,z416]),(0,[z0,z1,z3,z4,z203,z39]),(0,[z93,z0,z1,z61,z4,z5]),(0,[z926,z1,z3,z4,z5,z56]),(0,[z0,z1,z3,z5,z6,z729])],[(0,[z0,z1,z3,z4,z5,z1078])],[(0,[z0,z1,z4,z1079,z5,z6]),(0,[z0,z1,z3,z4,z5,z1080])],[(0,[z0,z1,z400,z4,z5,z39]),(0,[z0,z1,z3,z4,z124,z9]),(0,[z95,z1,z3,z157,z5,z26]),(0,[z0,z1,z3,z832,z4,z5]),(0,[z82,z0,z3,z47,z5,z6]),(0,[z14,z0,z1,z970,z4,z5])],[(0,[z1,z3,z52,z4,z5,z123]),(0,[z189,z0,z1,z3,z5,z6]),(0,[z18,z0,z560,z1,z3,z6]),(0,[z0,z1,z3,z4,z5,z1081])],[(0,[z23,z987,z3,z4,z5,z6])],[(0,[z0,z171,z102,z4,z5,z6]),(0,[z194,z476,z1,z3,z109,z5]),(0,[z0,z1,z3,z20,z30,z5]),(0,[z1082,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z1083]),(0,[z0,z1,z3,z4,z5,z1084]),(0,[z0,z1,z196,z4,z127,z399]),(0,[z0,z1,z3,z901,z4,z9])],[(0,[z0,z1,z3,z4,z5,z1085]),(0,[z1086,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z1087,z5]),(0,[z0,z1,z4,z5,z1088,z39])],[(0,[z1,z3,z4,z5,z123,z39]),(0,[z82,z0,z3,z496,z47,z5]),(0,[z0,z1,z3,z1089,z4,z5]),(0,[z0,z1,z3,z4,z5,z154])],[],[(0,[z0,z1,z3,z20,z5,z33])],[(0,[z0,z1,z3,z4,z5,z1090]),(0,[z14,z0,z1,z3,z4,z280]),(0,[z0,z1,z3,z4,z5,z1091]),(0,[z171,z1,z3,z4,z5,z123]),(0,[z0,z1,z3,z4,z5,z1092]),(0,[z0,z1,z3,z167,z157,z5]),(0,[z86,z1,z3,z4,z256,z56])],[(0,[z0,z1,z3,z4,z5,z1093])]],
   [[(0,[z1094,z0,z1,z3,z423,z5]),(0,[z0,z117,z3,z4,z27,z39]),(0,[z189,z0,z53,z1,z3,z6]),(0,[z0,z1,z3,z77,z4,z691]),(0,[z8,z14,z0,z1,z69,z5]),(0,[z0,z1,z3,z4,z1095,z5])],[(0,[z0,z1,z3,z4,z5,z1096]),(0,[z0,z1,z3,z1097,z5,z6])],[(0,[z0,z1,z3,z5,z1098,z6]),(0,[z0,z1,z3,z4,z5,z1099]),(0,[z0,z1,z3,z177,z5,z76])],[(0,[z0,z1,z3,z4,z5,z1100]),(0,[z0,z1,z3,z5,z1101,z6]),(0,[z0,z1,z1102,z3,z4,z5])],[(0,[z0,z1,z3,z1103,z5,z6]),(0,[z194,z1,z3,z109,z5,z297]),(0,[z0,z476,z1,z3,z4,z5]),(0,[z0,z1,z3,z20,z5,z350])],[(0,[z0,z1,z3,z1104,z4,z5]),(0,[z0,z1,z3,z4,z5,z1105])],[(0,[z0,z1,z3,z110,z280,z6]),(0,[z0,z1,z185,z61,z4,z5])],[(0,[z1106,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z1107]),(0,[z189,z0,z1,z3,z256,z6]),(0,[z0,z1,z3,z1108,z4,z5]),(1,[z0,z3,z762,z5,z6])],[(0,[z142,z0,z3,z4,z332,z5])],[(0,[z0,z205,z3,z4,z5,z436]),(0,[z0,z1,z3,z4,z5,z1109])],[(0,[z0,z1,z3,z4,z1110,z6]),(0,[z0,z1,z196,z4,z5,z330]),(0,[z0,z1,z3,z4,z5,z1111])],[(0,[z0,z1,z3,z1112,z4,z5]),(0,[z0,z1,z3,z4,z5,z1113]),(0,[z0,z1114,z3,z4,z5,z6]),(1,[z1115,z0,z1,z3,z5]),(0,[z0,z1,z3,z4,z1116,z5]),(0,[z0,z443,z3,z4,z5,z39]),(0,[z0,z1,z4,z781,z5,z6]),(0,[z616,z0,z1,z61,z4,z5])],[(0,[z0,z1,z3,z4,z5,z1117]),(0,[z1,z3,z157,z4,z375,z5]),(0,[z0,z1,z3,z901,z4,z26]),(0,[z984,z1,z3,z4,z5,z6])],[(0,[z51,z1,z52,z4,z5,z26]),(0,[z0,z1,z3,z4,z5,z289]),(0,[z0,z1,z3,z463,z5,z97])],[(0,[z0,z1,z3,z4,z5,z79]),(0,[z169,z0,z1,z3,z167,z5]),(0,[z0,z1,z3,z4,z195,z9]),(0,[z0,z1,z238,z4,z5,z56])],[(0,[z0,z1,z3,z4,z5,z313]),(0,[z87,z0,z1,z3,z20,z5]),(0,[z0,z1,z75,z3,z4,z39]),(0,[z0,z582,z3,z4,z112,z6])]],
   [[(0,[z0,z1,z3,z4,z280,z6]),(0,[z0,z1,z400,z4,z5,z416]),(0,[z128,z987,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z804,z26]),(0,[z0,z1118,z1,z3,z4,z5]),(0,[z0,z1,z4,z506,z5,z9])],[(0,[z0,z1,z3,z1119,z5,z6]),(0,[z0,z1,z3,z4,z5,z1120]),(0,[z1121,z0,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z5,z1122])],[(0,[z0,z1,z3,z4,z5,z306]),(0,[z0,z1,z405,z4,z5,z9]),(0,[z0,z1,z3,z4,z5,z1123]),(0,[z0,z1,z3,z4,z5,z1124]),(0,[z1,z3,z4,z5,z39,z26])],[(0,[z0,z1,z3,z4,z5,z1125]),(0,[z0,z1,z3,z4,z294,z6]),(0,[z0,z1,z3,z4,z951,z9])],[(0,[z0,z1,z3,z4,z5,z1126]),(0,[z14,z0,z1,z3,z542,z5]),(0,[z14,z0,z1,z3,z4,z134]),(0,[z0,z1,z3,z4,z1127,z5]),(0,[z0,z117,z343,z3,z4,z6]),(0,[z14,z0,z1,z75,z3,z4])],[(0,[z0,z1,z3,z4,z5,z1128]),(0,[z457,z737,z1,z3,z4,z5])],[(0,[z0,z1,z3,z4,z5,z1129]),(0,[z37,z1,z3,z4,z63,z39]),(0,[z0,z1,z3,z463,z5,z39]),(0,[z0,z1,z3,z1130,z4,z5]),(0,[z300,z0,z1,z4,z5,z56])],[(0,[z0,z1,z102,z4,z78,z6]),(0,[z0,z1,z3,z4,z5,z1131]),(1,[z0,z1,z3,z4,z791])],[(0,[z0,z1,z3,z111,z4,z5])],[(0,[z0,z1,z3,z364,z4,z204]),(0,[z1132,z1,z3,z4,z5,z6]),(0,[z0,z1133,z1,z3,z4,z5])],[(0,[z0,z1,z4,z69,z5,z330]),(0,[z0,z1,z1134,z3,z4,z5])],[(0,[z0,z58,z159,z4,z5,z26])],[(0,[z173,z1,z3,z4,z5,z123]),(0,[z321,z1,z3,z4,z5,z26]),(0,[z14,z0,z1,z3,z338,z5]),(0,[z0,z1,z3,z4,z5,z1135]),(0,[z18,z0,z1,z3,z539,z6])],[(0,[z23,z273,z3,z22,z5,z6]),(0,[z1,z3,z4,z5,z26,z491]),(0,[z0,z1,z3,z4,z218,z39]),(0,[z14,z0,z1,z3,z191,z5]),(1,[z0,z1,z3,z875,z6])],[(0,[z0,z1,z102,z4,z5,z56]),(0,[z0,z1,z3,z423,z5,z6]),(0,[z0,z1,z3,z4,z5,z1136]),(0,[z0,z1,z3,z4,z5,z1137]),(1,[z0,z3,z4,z5,z920]),(0,[z0,z65,z390,z3,z4,z5])],[(0,[z0,z129,z3,z4,z5,z6]),(0,[z0,z1,z1138,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z1139]),(0,[z0,z1,z3,z4,z5,z1140]),(0,[z0,z1,z3,z4,z5,z1141])]],
   [[(0,[z87,z0,z1,z3,z109,z5]),(0,[z0,z1,z3,z4,z133,z6]),(0,[z0,z1,z3,z1142,z4,z6]),(0,[z0,z146,z343,z3,z5,z6]),(0,[z0,z1,z470,z4,z5,z56])],[(0,[z144,z1,z3,z4,z5,z192])],[(0,[z0,z1,z3,z1143,z4,z5]),(0,[z1144,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z20,z4,z182])],[(0,[z0,z1,z3,z4,z5,z1145]),(0,[z0,z1,z3,z303,z5,z306]),(0,[z0,z1146,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1147]),(0,[z0,z1,z3,z4,z5,z1148])],[(0,[z93,z1,z73,z4,z5,z193]),(0,[z0,z1149,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z791,z202])],[(0,[z0,z1,z3,z22,z5,z39]),(0,[z0,z1,z3,z4,z1150,z6]),(0,[z95,z1,z3,z157,z5,z9]),(0,[z14,z0,z1,z3,z4,z294]),(0,[z0,z1,z3,z20,z526,z5]),(0,[z18,z0,z1,z3,z49,z56]),(0,[z0,z1,z3,z4,z5,z1151])],[(0,[z0,z1,z3,z4,z5,z155]),(0,[z0,z64,z3,z4,z112,z39]),(0,[z0,z1,z3,z4,z5,z1152]),(0,[z0,z53,z1,z4,z70,z6]),(0,[z0,z1,z196,z461,z4,z6]),(0,[z0,z1,z397,z4,z5,z56]),(0,[z0,z1,z3,z191,z5,z74])],[(0,[z290,z1,z3,z4,z5,z26]),(0,[z0,z1,z3,z4,z5,z1153])],[(0,[z0,z129,z3,z4,z5,z56]),(0,[z0,z1,z100,z4,z5,z192]),(0,[z1154,z1,z3,z4,z5,z6]),(0,[z14,z0,z1,z3,z5,z267])],[(0,[z0,z1,z3,z1155,z5,z6]),(0,[z0,z1,z3,z4,z1156,z6]),(0,[z0,z1,z3,z4,z133,z56])],[(0,[z0,z1,z3,z4,z5,z1157]),(0,[z1,z3,z4,z734,z63,z6])],[(0,[z987,z273,z3,z4,z5,z6]),(0,[z1,z779,z52,z4,z5,z6]),(0,[z0,z1,z3,z4,z1158,z6]),(0,[z0,z1,z3,z277,z5,z26]),(0,[z8,z0,z1,z69,z5,z39]),(0,[z135,z0,z1,z3,z5,z489])],[(0,[z0,z217,z31,z4,z5,z26]),(0,[z0,z1,z3,z4,z5,z1159]),(0,[z0,z64,z3,z20,z4,z112]),(0,[z926,z1,z3,z4,z5,z6]),(1,[z0,z1,z4,z781,z6])],[(0,[z0,z1,z3,z4,z203,z324]),(0,[z136,z0,z1,z3,z4,z360])],[(0,[z0,z1,z3,z4,z1160,z6]),(0,[z0,z1,z52,z4,z5,z424]),(0,[z0,z1,z1161,z4,z5,z6])],[(0,[z1162,z0,z1,z3,z4,z5]),(0,[z0,z884,z159,z4,z5,z6]),(0,[z0,z1,z3,z1163,z4,z5])]],
   [[(0,[z0,z1,z3,z4,z5,z1164]),(0,[z0,z129,z3,z303,z5,z6]),(0,[z0,z1,z75,z3,z157,z6])],[(0,[z0,z1,z3,z4,z5,z1165]),(0,[z0,z1,z3,z4,z5,z1166]),(0,[z0,z1,z3,z4,z5,z1167]),(0,[z1154,z1,z3,z4,z5,z56]),(0,[z276,z254,z1,z3,z4,z5])],[(0,[z0,z1,z3,z4,z212,z6]),(0,[z0,z1,z3,z4,z5,z1168]),(0,[z0,z1,z3,z4,z5,z1169]),(0,[z254,z1,z3,z4,z5,z39])],[(0,[z0,z1,z3,z4,z5,z1170]),(0,[z14,z0,z64,z3,z4,z112])],[(0,[z0,z220,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z96]),(0,[z0,z1,z3,z20,z4,z124])],[(0,[z0,z1,z3,z4,z134,z39]),(0,[z0,z1,z3,z4,z5,z1171]),(0,[z135,z0,z1,z3,z4,z5]),(0,[z18,z0,z343,z3,z49,z6])],[(0,[z0,z3,z4,z5,z1172,z6]),(0,[z0,z1,z3,z103,z5,z346]),(0,[z0,z217,z31,z4,z5,z32]),(0,[z0,z1,z3,z4,z5,z399]),(0,[z14,z0,z1,z3,z5,z38])],[(0,[z0,z1,z3,z4,z1173,z6]),(0,[z0,z1,z3,z765,z4,z5]),(0,[z0,z1,z3,z4,z5,z1174]),(0,[z0,z1,z3,z4,z1175,z6]),(0,[z0,z1,z3,z4,z5,z1176]),(0,[z0,z1177,z1,z3,z4,z5])],[(0,[z0,z1,z3,z4,z5,z1178]),(0,[z211,z14,z0,z1,z3,z5]),(0,[z86,z1,z3,z4,z256,z6]),(1,[z0,z3,z4,z770,z6]),(0,[z1179,z0,z1,z3,z5,z6])],[(0,[z0,z1,z3,z4,z1180,z6]),(0,[z0,z1,z3,z4,z198,z26]),(0,[z0,z1,z3,z20,z674,z5]),(0,[z184,z0,z1,z4,z5,z56]),(0,[z0,z1181,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z1182]),(0,[z189,z0,z1,z3,z5,z26]),(0,[z0,z1,z3,z20,z5,z346]),(0,[z0,z1,z3,z4,z182,z9]),(0,[z0,z1,z3,z4,z5,z1183])],[(0,[z0,z1,z400,z22,z5,z6]),(0,[z0,z1,z3,z4,z212,z56]),(0,[z0,z64,z3,z4,z770,z6]),(0,[z0,z1184,z1,z3,z4,z5])],[(0,[z0,z1185,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z1186,z6]),(0,[z1187,z0,z1,z3,z5,z6]),(0,[z0,z1,z3,z4,z1188,z5])],[(0,[z0,z220,z3,z4,z5,z56]),(0,[z0,z1189,z3,z4,z5,z6]),(0,[z51,z1,z52,z4,z5,z9]),(0,[z0,z1,z3,z4,z5,z1190])],[(0,[z0,z1,z3,z4,z1191,z6]),(0,[z0,z1,z3,z4,z375,z5]),(0,[z0,z1,z3,z1192,z4,z5])],[(0,[z0,z1,z3,z4,z5,z1193]),(0,[z0,z1,z3,z4,z5,z1194]),(0,[z0,z254,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z1195]),(0,[z307,z1,z3,z4,z5,z123])]],
   [[(0,[z0,z1,z3,z22,z5,z416]),(0,[z1,z3,z4,z734,z5,z6]),(0,[z0,z230,z1,z3,z4,z26]),(0,[z0,z1,z3,z1196,z4,z5]),(0,[z8,z0,z1,z20,z69,z5]),(0,[z18,z0,z1,z3,z232,z49])],[(0,[z0,z1,z3,z4,z1197,z6]),(0,[z0,z1198,z3,z4,z5,z6]),(0,[z737,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z1199,z4,z5]),(0,[z0,z1,z3,z4,z1200,z6]),(0,[z0,z1,z3,z4,z1201,z5]),(0,[z0,z1,z3,z4,z5,z1202]),(0,[z0,z1,z75,z3,z20,z4])],[(0,[z0,z1,z1203,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1204]),(0,[z0,z1,z3,z4,z1205,z6]),(0,[z0,z1,z3,z4,z5,z1206]),(0,[z0,z1,z196,z4,z127,z201])],[(0,[z254,z1,z3,z157,z4,z5])],[(0,[z0,z220,z3,z303,z5,z6]),(0,[z0,z1,z451,z4,z5,z9]),(0,[z697,z1,z3,z4,z5,z26]),(0,[z184,z0,z1,z4,z506,z5])],[(0,[z0,z1,z3,z4,z5,z1207]),(0,[z1208,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z1209,z5])],[(0,[z0,z1185,z3,z4,z5,z192]),(0,[z0,z1,z533,z4,z5,z56])],[(0,[z0,z1,z3,z4,z5,z1210])],[(0,[z0,z1,z3,z4,z1191,z192]),(0,[z1211,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z1212,z4,z5]),(0,[z0,z1,z3,z4,z5,z1213]),(0,[z0,z1,z3,z4,z1214,z5])],[(0,[z93,z1,z73,z4,z5,z9]),(0,[z0,z1,z3,z4,z5,z1215]),(0,[z1216,z189,z0,z1,z3,z5]),(0,[z0,z1,z3,z5,z267,z1217]),(0,[z737,z1,z3,z4,z5,z56])],[(0,[z0,z1,z1218,z4,z5,z6]),(0,[z0,z1,z3,z4,z1219,z6]),(0,[z51,z1,z52,z20,z4,z5]),(0,[z8,z87,z0,z1,z3,z5]),(0,[z437,z1,z3,z4,z5,z26]),(0,[z0,z58,z159,z4,z5,z9])],[(0,[z0,z1,z3,z4,z5,z1220]),(0,[z0,z1,z3,z4,z5,z1221]),(0,[z1,z3,z4,z109,z5,z123]),(0,[z0,z1,z513,z177,z4,z5])],[(0,[z0,z1,z3,z1222,z5,z6]),(0,[z0,z1,z3,z4,z182,z26]),(0,[z0,z1,z3,z1223,z4,z5]),(0,[z0,z1,z3,z19,z4,z566])],[(0,[z0,z1,z102,z110,z5,z6]),(0,[z0,z146,z3,z141,z5,z56]),(0,[z0,z1,z3,z4,z5,z1224]),(0,[z14,z0,z1,z1161,z4,z5])],[(0,[z194,z1,z3,z111,z109,z5]),(0,[z0,z1,z3,z4,z5,z174]),(0,[z8,z0,z1,z4,z506,z5])]],
   [[(0,[z0,z1,z3,z4,z5,z1225]),(0,[z14,z0,z1,z3,z4,z1186])],[(0,[z0,z1,z3,z4,z5,z1226]),(0,[z559,z1,z3,z4,z5,z26]),(0,[z0,z1,z3,z4,z5,z1227])],[(0,[z0,z273,z102,z4,z5,z6]),(0,[z0,z217,z507,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1228]),(0,[z0,z1,z3,z1047,z5,z9])],[(1,[z987,z3,z4,z5,z6]),(0,[z0,z64,z3,z267,z112,z6])],[(0,[z0,z1,z3,z4,z280,z26]),(0,[z14,z0,z129,z3,z4,z5]),(0,[z1115,z0,z1,z3,z5,z6]),(0,[z0,z1,z3,z4,z1229,z6]),(0,[z0,z1,z1230,z3,z4,z5]),(0,[z18,z0,z1,z3,z338,z6]),(0,[z0,z1,z3,z1231,z5,z6])],[(0,[z0,z1232,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z97])],[(0,[z0,z1,z3,z12,z137,z6]),(0,[z0,z1,z3,z4,z294,z26]),(0,[z142,z0,z3,z4,z5,z148]),(0,[z0,z1,z185,z4,z5,z330]),(0,[z0,z1,z3,z1233,z4,z5])],[(0,[z0,z1,z102,z4,z5,z6]),(0,[z14,z0,z1,z102,z4,z5]),(0,[z93,z1,z73,z20,z4,z5]),(0,[z271,z1,z3,z4,z5,z26]),(0,[z14,z0,z146,z3,z141,z5]),(0,[z1234,z1,z3,z4,z5,z6]),(0,[z0,z1,z4,z5,z56,z638])],[(0,[z23,z273,z3,z4,z78,z6]),(0,[z51,z1,z52,z4,z198,z6]),(0,[z0,z1,z3,z4,z5,z1235]),(0,[z254,z1,z3,z4,z5,z63]),(0,[z0,z58,z159,z20,z4,z5]),(0,[z14,z0,z1,z3,z4,z182]),(0,[z14,z0,z1,z3,z605,z5]),(0,[z8,z0,z1,z28,z69,z5])],[(0,[z0,z1,z3,z4,z5,z1236]),(0,[z128,z171,z3,z4,z5,z26]),(0,[z0,z1,z3,z4,z1237,z6]),(0,[z0,z1,z3,z4,z1238,z5]),(0,[z18,z135,z0,z1,z3,z5])],[(0,[z0,z1,z3,z1239,z5,z6]),(0,[z0,z1,z3,z4,z5,z1240]),(0,[z0,z1241,z1,z3,z4,z5]),(0,[z0,z1,z3,z277,z5,z9])],[(0,[z0,z1,z3,z1242,z4,z5]),(0,[z0,z343,z3,z109,z5,z6]),(0,[z0,z1,z3,z4,z5,z1243]),(0,[z37,z1,z3,z4,z63,z56]),(0,[z0,z1,z3,z1244,z5,z6]),(0,[z0,z217,z31,z4,z5,z9])],[(0,[z93,z1,z73,z4,z5,z26]),(0,[z8,z0,z1,z69,z5,z268])],[(0,[z0,z1,z3,z1245,z5,z6]),(0,[z169,z254,z1,z3,z4,z5]),(0,[z0,z3,z4,z5,z920,z6]),(0,[z0,z1,z10,z20,z11,z5])],[(0,[z1115,z0,z1,z3,z5,z192]),(0,[z0,z1,z1246,z4,z5,z39]),(0,[z0,z1,z3,z1247,z5,z6]),(0,[z0,z1,z3,z4,z5,z1248]),(0,[z18,z0,z1,z3,z49,z6])]],
   [[(0,[z0,z1,z3,z4,z280,z320]),(0,[z23,z273,z3,z4,z5,z56]),(0,[z0,z1,z3,z4,z5,z1249]),(0,[z194,z1,z3,z109,z5,z26]),(0,[z0,z1,z3,z1250,z4,z5]),(0,[z0,z1,z3,z1251,z4,z5])],[(0,[z0,z1,z3,z4,z78,z39]),(0,[z0,z1,z3,z4,z5,z1252]),(0,[z327,z1,z3,z4,z63,z6])],[(0,[z0,z1,z3,z20,z22,z5]),(0,[z0,z1,z3,z423,z5,z26]),(0,[z0,z1,z700,z4,z5,z9])],[(0,[z87,z0,z1,z3,z103,z5]),(0,[z0,z1,z3,z4,z5,z1253]),(0,[z0,z1,z3,z5,z267,z39])],[(0,[z0,z1,z3,z22,z78,z6]),(0,[z173,z254,z1,z3,z4,z5])],[(0,[z0,z1,z1254,z4,z5,z6]),(0,[z0,z1,z3,z5,z1255,z6]),(0,[z25,z1,z3,z4,z375,z5]),(0,[z0,z1,z196,z4,z127,z39]),(0,[z0,z1,z3,z964,z4,z5]),(0,[z8,z0,z1,z61,z4,z5])],[(0,[z0,z1,z3,z463,z5,z379])],[(0,[z0,z1,z3,z4,z5,z1256]),(0,[z0,z1,z3,z4,z985,z9])],[(0,[z1,z3,z52,z4,z5,z155]),(0,[z0,z343,z3,z4,z5,z39]),(0,[z0,z146,z3,z13,z112,z6])],[(0,[z0,z1,z3,z4,z198,z9]),(0,[z0,z1,z3,z4,z5,z371]),(0,[z82,z0,z3,z47,z5,z9]),(0,[z82,z0,z248,z3,z47,z5]),(0,[z0,z1,z3,z4,z1257,z5])],[(0,[z0,z1,z1063,z4,z5,z6]),(0,[z0,z217,z31,z20,z4,z5]),(0,[z0,z1,z3,z1258,z5,z6]),(0,[z189,z0,z1,z3,z5,z9]),(0,[z0,z53,z1,z20,z4,z70])],[(0,[z0,z1,z3,z22,z5,z56]),(0,[z0,z1,z1259,z4,z5,z6]),(0,[z14,z0,z1,z3,z4,z124]),(0,[z0,z1,z3,z4,z5,z1260]),(0,[z0,z1,z3,z4,z5,z1261]),(0,[z1262,z0,z1,z3,z4,z5])],[(0,[z0,z1,z3,z4,z1263,z6]),(0,[z690,z1,z3,z4,z256,z6]),(0,[z210,z0,z3,z4,z5,z148]),(0,[z0,z1,z3,z1264,z5,z6]),(0,[z0,z1,z3,z4,z5,z1265]),(0,[z0,z230,z3,z4,z112,z6]),(0,[z0,z64,z3,z4,z112,z56])],[(0,[z0,z1,z3,z879,z423,z5]),(0,[z1266,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z191,z69,z5]),(0,[z0,z1,z3,z4,z5,z1267]),(0,[z0,z1,z3,z4,z5,z1268]),(0,[z14,z0,z1,z3,z5,z432])],[(0,[z0,z1,z1269,z3,z4,z5]),(0,[z457,z926,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z1270])],[(0,[z228,z0,z3,z4,z5,z54]),(0,[z35,z1,z3,z4,z5,z39]),(0,[z0,z1,z3,z4,z5,z1271])]],
   [[(0,[z0,z1,z3,z5,z1255,z192]),(0,[z0,z1,z3,z1272,z4,z5]),(0,[z0,z230,z1,z3,z4,z9]),(0,[z0,z1273,z1,z3,z4,z5]),(0,[z14,z1274,z1,z3,z4,z5])],[(0,[z18,z0,z68,z1,z3,z6]),(0,[z8,z0,z1,z69,z5,z56])],[(0,[z0,z1,z3,z4,z5,z1275]),(0,[z0,z1,z3,z4,z5,z1276]),(0,[z0,z1277,z1,z3,z4,z5])],[(0,[z0,z1,z1278,z3,z4,z5]),(0,[z0,z1279,z3,z4,z5,z6]),(0,[z1280,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z1281]),(0,[z189,z0,z1,z3,z222,z5]),(0,[z0,z331,z3,z4,z5,z101])],[(0,[z0,z1,z3,z4,z5,z213]),(0,[z0,z1,z3,z4,z5,z215])],[(0,[z51,z1,z52,z4,z5,z306])],[(0,[z0,z1,z400,z4,z78,z6]),(0,[z0,z1,z3,z408,z4,z5]),(0,[z0,z1,z3,z13,z875,z6])],[(0,[z169,z0,z1,z3,z4,z5])],[(0,[z246,z1,z3,z4,z5,z39]),(1,[z0,z1,z927,z5,z6]),(0,[z0,z1,z3,z232,z4,z5])],[(0,[z0,z1,z4,z5,z1088,z6]),(0,[z0,z1,z3,z4,z1282,z6]),(0,[z0,z1,z3,z12,z479,z6]),(0,[z0,z1,z3,z749,z4,z6])],[(0,[z0,z1,z3,z4,z203,z56]),(0,[z0,z1,z3,z20,z4,z212]),(0,[z18,z0,z1,z3,z312,z6]),(0,[z0,z1,z3,z4,z5,z1283]),(0,[z0,z1,z3,z4,z186,z46])],[(0,[z0,z1,z3,z4,z78,z416]),(0,[z0,z1,z3,z1284,z4,z5]),(0,[z86,z1,z3,z4,z256,z26]),(0,[z82,z0,z3,z47,z5,z26]),(0,[z0,z1,z3,z1285,z4,z5]),(0,[z0,z1,z3,z20,z5,z76]),(0,[z14,z0,z1,z1246,z4,z5])],[(0,[z0,z1286,z1,z3,z4,z5]),(0,[z14,z0,z1,z3,z577,z5]),(1,[z1,z3,z4,z5,z804]),(0,[z0,z1,z3,z191,z5,z456]),(0,[z0,z1,z3,z4,z5,z1287])],[(0,[z0,z1,z400,z4,z5,z56]),(0,[z95,z1,z3,z157,z212,z6]),(0,[z0,z1,z3,z4,z366,z433]),(0,[z0,z1288,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z424]),(0,[z0,z1,z3,z4,z45,z433]),(0,[z0,z1,z3,z4,z5,z1289]),(0,[z0,z1,z3,z496,z4,z218]),(0,[z0,z1,z3,z1290,z4,z5]),(0,[z0,z1,z3,z4,z5,z1291]),(0,[z0,z1,z3,z1292,z4,z5])]],
   [[(0,[z0,z1,z3,z463,z63,z6]),(0,[z0,z1185,z3,z4,z5,z26]),(0,[z0,z117,z3,z4,z27,z6]),(0,[z0,z1,z3,z4,z5,z201])],[(0,[z23,z14,z273,z3,z4,z5]),(0,[z1,z3,z779,z4,z5,z6]),(0,[z0,z1,z3,z157,z124,z6]),(0,[z0,z1,z3,z4,z1293,z6]),(0,[z0,z1,z3,z4,z5,z249]),(0,[z0,z1,z3,z4,z5,z1294])],[(0,[z51,z1,z52,z423,z5,z6]),(0,[z0,z1,z3,z740,z277,z5]),(0,[z0,z1,z3,z4,z1191,z26])],[(0,[z51,z129,z52,z4,z5,z6]),(0,[z0,z1,z3,z4,z298,z318]),(0,[z0,z1,z3,z4,z5,z1295]),(0,[z14,z0,z1,z3,z569,z5]),(0,[z18,z0,z1,z3,z875,z6])],[(0,[z0,z1,z3,z4,z280,z9]),(0,[z0,z1,z3,z12,z13,z39]),(0,[z0,z1,z3,z4,z1296,z5]),(0,[z0,z1,z3,z4,z9,z1297])],[(0,[z0,z1,z3,z4,z5,z1298])],[(0,[z0,z1,z3,z1299,z4,z5]),(0,[z1300,z0,z1,z3,z5,z6]),(0,[z0,z117,z3,z4,z770,z6]),(0,[z0,z1,z3,z4,z1301,z6])],[(0,[z883,z0,z1,z3,z277,z5]),(0,[z0,z1,z3,z4,z294,z9]),(1,[z0,z1,z4,z5,z834])],[(0,[z572,z1,z3,z4,z5,z26]),(0,[z0,z1,z3,z4,z1302,z5]),(0,[z0,z146,z3,z141,z5,z6]),(0,[z0,z1,z3,z4,z1303,z5])],[(0,[z1304,z0,z1,z3,z4,z5]),(0,[z37,z1,z3,z4,z63,z266]),(0,[z1,z3,z4,z5,z593,z39]),(0,[z0,z1,z3,z4,z5,z1217]),(0,[z0,z117,z3,z4,z27,z56])],[(0,[z0,z1305,z3,z4,z5,z6]),(0,[z0,z1,z3,z1306,z4,z5]),(0,[z87,z0,z1,z3,z157,z5]),(0,[z0,z1,z3,z4,z5,z1307])],[(0,[z194,z14,z1,z3,z109,z5]),(0,[z0,z1,z3,z4,z5,z1308]),(0,[z0,z443,z3,z4,z5,z6])],[(0,[z1309,z0,z1,z3,z4,z5]),(0,[z0,z217,z31,z4,z182,z6]),(0,[z0,z1,z3,z762,z5,z6]),(0,[z0,z113,z1,z4,z5,z56]),(0,[z0,z1310,z1,z3,z4,z5]),(0,[z0,z1,z3,z5,z9,z1311])],[(0,[z95,z1,z3,z103,z157,z5]),(0,[z0,z1,z3,z1312,z4,z5]),(0,[z0,z1,z3,z4,z1313,z6]),(0,[z14,z0,z1,z3,z5,z279])],[(1,[z0,z884,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1314]),(0,[z14,z0,z1,z10,z11,z5])],[(0,[z0,z343,z3,z4,z63,z6]),(0,[z0,z1,z3,z4,z5,z1315])]],
   [[(0,[z23,z273,z3,z110,z5,z6]),(0,[z194,z1,z3,z109,z5,z9]),(0,[z25,z1,z3,z4,z5,z155]),(0,[z0,z1,z3,z1316,z4,z5]),(0,[z135,z0,z1,z3,z5,z38]),(0,[z0,z1,z3,z4,z5,z1317])],[(0,[z95,z1,z3,z20,z157,z5]),(0,[z0,z1,z100,z4,z5,z9]),(0,[z189,z0,z1,z3,z49,z6]),(0,[z0,z1,z3,z4,z5,z268])],[(0,[z0,z1,z3,z4,z5,z1318]),(0,[z0,z1,z3,z423,z5,z9]),(0,[z0,z3,z4,z5,z1319,z6]),(0,[z0,z1,z3,z1320,z4,z5]),(0,[z0,z1,z3,z4,z5,z1321]),(0,[z0,z1,z185,z4,z5,z9]),(0,[z271,z1,z3,z103,z4,z5])],[(0,[z0,z1322,z3,z4,z5,z6]),(0,[z0,z381,z31,z4,z5,z6]),(0,[z0,z1,z3,z4,z124,z96]),(0,[z0,z1,z3,z4,z5,z1323])],[(0,[z0,z443,z3,z4,z5,z56])],[(0,[z0,z1,z3,z4,z5,z1324]),(0,[z0,z1,z3,z4,z5,z1325]),(0,[z0,z1326,z3,z4,z5,z6]),(0,[z14,z624,z0,z1,z3,z5]),(0,[z0,z1,z3,z77,z4,z302])],[(0,[z0,z1,z3,z4,z5,z1327]),(0,[z1,z73,z779,z4,z5,z6]),(0,[z37,z1,z3,z4,z63,z6]),(0,[z0,z1,z3,z4,z5,z1328]),(0,[z0,z1,z3,z4,z1313,z56])],[(0,[z0,z1,z3,z4,z1329,z6])],[(0,[z0,z1,z3,z4,z1330,z6]),(0,[z0,z1,z3,z4,z5,z1331]),(0,[z0,z1,z3,z110,z5,z39]),(0,[z128,z171,z3,z20,z4,z5]),(0,[z51,z220,z52,z4,z5,z6]),(0,[z142,z0,z3,z4,z5,z292]),(0,[z0,z1,z75,z3,z4,z56]),(0,[z0,z1,z3,z4,z5,z1332]),(0,[z0,z1,z3,z4,z5,z1333])],[(0,[z14,z0,z1,z3,z22,z5])],[(0,[z23,z273,z3,z4,z5,z6]),(0,[z0,z65,z3,z4,z5,z436]),(0,[z0,z1,z3,z4,z5,z1334]),(0,[z0,z53,z1,z4,z70,z9])],[(0,[z0,z1,z3,z4,z1335,z6]),(0,[z0,z1,z3,z4,z5,z1336]),(0,[z0,z1337,z1,z3,z4,z6]),(0,[z0,z1,z185,z4,z5,z834])],[(0,[z0,z1,z102,z4,z5,z26]),(0,[z0,z1,z3,z20,z423,z5]),(0,[z0,z1,z3,z4,z5,z1338]),(0,[z0,z1,z3,z1339,z4,z5]),(0,[z0,z1,z3,z4,z5,z1340])],[(0,[z0,z1,z3,z4,z1341,z6]),(0,[z0,z1,z3,z4,z1342,z6]),(0,[z0,z3,z4,z5,z1319,z192]),(0,[z144,z1,z3,z4,z5,z26]),(0,[z0,z1,z3,z4,z218,z6])],[(0,[z0,z1,z3,z4,z5,z1343]),(0,[z0,z1,z3,z4,z1344,z6]),(0,[z0,z1,z3,z1345,z4,z5]),(0,[z0,z1,z3,z4,z5,z1346]),(0,[z0,z1,z3,z4,z5,z1347]),(0,[z1348,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z20,z5,z74])],[(0,[z0,z1,z3,z4,z5,z1349]),(0,[z0,z1,z3,z463,z5,z56]),(0,[z0,z1,z3,z4,z5,z1350]),(0,[z0,z1,z3,z4,z5,z1351]),(0,[z0,z1,z3,z4,z5,z1352]),(0,[z0,z1,z3,z20,z4,z195])]],
   [[(0,[z0,z1,z3,z167,z4,z5]),(0,[z0,z1,z3,z5,z6,z1353]),(0,[z0,z65,z3,z4,z5,z920]),(0,[z0,z1,z3,z4,z5,z1354])],[(0,[z0,z1,z3,z4,z5,z1355]),(0,[z14,z0,z1,z3,z296,z5]),(0,[z613,z1,z3,z4,z5,z26])],[(0,[z0,z1,z3,z4,z5,z39]),(0,[z0,z1,z3,z4,z198,z306]),(0,[z0,z705,z3,z4,z112,z6]),(0,[z0,z3,z141,z762,z5,z6])],[(0,[z0,z1,z3,z1356,z4,z5]),(0,[z51,z1,z779,z4,z5,z6]),(0,[z1115,z0,z1,z3,z4,z5]),(0,[z0,z1357,z1,z3,z4,z5]),(0,[z14,z0,z1,z3,z17,z5]),(0,[z0,z1,z3,z4,z5,z920])],[],[(0,[z0,z1,z3,z22,z5,z6]),(0,[z0,z1,z10,z11,z5,z39])],[(0,[z0,z129,z3,z4,z5,z26]),(0,[z0,z1,z3,z4,z5,z89]),(0,[z162,z1,z3,z4,z5,z39]),(0,[z0,z1,z3,z4,z842,z133]),(0,[z0,z1,z3,z4,z218,z56]),(0,[z0,z64,z3,z4,z112,z6])],[(0,[z0,z1,z400,z4,z5,z1358]),(0,[z0,z1,z3,z1359,z5,z6]),(0,[z0,z1,z3,z1360,z4,z5]),(0,[z0,z1,z3,z4,z133,z26]),(0,[z0,z1,z3,z4,z5,z1361]),(0,[z0,z1,z3,z4,z6,z1362]),(0,[z0,z1,z4,z272,z5,z9])],[(0,[z0,z1,z102,z4,z5,z320]),(0,[z0,z1,z3,z4,z5,z1363]),(0,[z0,z1,z3,z4,z5,z1364])],[(0,[z0,z1,z3,z4,z5,z1365]),(0,[z0,z1,z3,z5,z267,z56]),(0,[z8,z0,z1,z927,z5,z6]),(0,[z14,z0,z1,z1366,z4,z5])],[(0,[z1,z3,z4,z5,z514,z39]),(0,[z0,z1,z675,z4,z5,z56])],[(0,[z0,z158,z3,z4,z5,z119]),(0,[z8,z0,z1,z69,z5,z6]),(0,[z0,z1,z3,z4,z5,z1367])],[(0,[z0,z1,z3,z4,z5,z1049]),(0,[z0,z1,z3,z4,z1368,z6]),(0,[z86,z1,z3,z4,z256,z9]),(0,[z0,z1,z3,z167,z5,z358])],[(0,[z0,z1,z3,z4,z5,z166]),(0,[z0,z230,z1,z3,z109,z6]),(0,[z0,z1,z3,z1369,z5,z6]),(0,[z0,z53,z1,z4,z70,z26]),(0,[z0,z1,z1366,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1370]),(0,[z0,z1,z3,z4,z5,z1371]),(0,[z14,z1372,z1,z3,z4,z5])],[(0,[z0,z1,z400,z110,z5,z6]),(0,[z0,z1,z3,z423,z198,z6]),(0,[z0,z343,z3,z4,z5,z56])],[(0,[z0,z1,z3,z4,z5,z379]),(0,[z0,z1,z3,z5,z6,z1373])]],
   [[(0,[z0,z1,z3,z1374,z5,z6]),(0,[z0,z1185,z3,z4,z5,z9])],[(0,[z82,z0,z3,z762,z5,z6]),(0,[z162,z1,z3,z4,z5,z166])],[(0,[z14,z0,z1,z3,z4,z212]),(0,[z0,z1,z3,z4,z1191,z9])],[(0,[z0,z1,z3,z110,z5,z416]),(0,[z0,z1,z3,z303,z5,z39]),(0,[z0,z1,z4,z5,z424,z192]),(0,[z0,z1,z3,z4,z5,z1375])],[(0,[z254,z1,z273,z3,z4,z5]),(1,[z1,z3,z4,z734,z6]),(0,[z0,z1,z3,z1376,z4,z5]),(0,[z0,z1377,z343,z3,z4,z5]),(0,[z0,z763,z3,z4,z5,z6]),(0,[z0,z1,z3,z20,z4,z789])],[(0,[z0,z1,z3,z4,z203,z6]),(0,[z0,z1,z3,z4,z134,z6]),(0,[z0,z1,z3,z4,z5,z1378]),(0,[z0,z146,z3,z5,z666,z6]),(0,[z0,z1,z3,z4,z5,z1379]),(0,[z0,z1,z3,z4,z1380,z6])],[],[(0,[z0,z1381,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1382]),(0,[z0,z1,z3,z4,z5,z1383]),(0,[z8,z0,z1,z195,z69,z6])],[(0,[z0,z1,z400,z4,z5,z6]),(0,[z0,z1,z3,z28,z4,z195])],[(0,[z1384,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z403]),(0,[z0,z1,z3,z4,z5,z1385]),(0,[z0,z1,z3,z4,z212,z26]),(0,[z0,z1,z3,z5,z875,z6])],[(0,[z0,z1,z3,z1386,z4,z5]),(0,[z0,z1387,z1,z3,z4,z5]),(0,[z1,z3,z4,z717,z5,z6]),(0,[z0,z1,z3,z4,z5,z1388]),(0,[z86,z1,z3,z277,z256,z6]),(0,[z0,z1,z765,z4,z5,z39]),(0,[z0,z3,z4,z762,z5,z6])],[(0,[z0,z220,z3,z4,z5,z26]),(0,[z0,z1,z73,z4,z5,z330]),(0,[z1389,z0,z1,z3,z4,z5])],[(0,[z0,z987,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z416]),(0,[z0,z1,z3,z4,z770,z6]),(0,[z0,z1,z61,z4,z5,z56])],[(0,[z1390,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z329]),(0,[z0,z1,z3,z4,z124,z39]),(0,[z697,z1,z3,z157,z5,z6]),(0,[z0,z1,z3,z4,z134,z56])],[(0,[z0,z1,z3,z20,z4,z78]),(0,[z128,z171,z3,z4,z5,z79]),(0,[z0,z1,z4,z5,z895,z39]),(0,[z14,z0,z1,z3,z511,z5])]],
   [[(0,[z0,z1,z1391,z4,z5,z6]),(0,[z128,z171,z3,z4,z5,z313]),(0,[z0,z1,z3,z4,z5,z1392]),(0,[z82,z14,z0,z3,z47,z5]),(0,[z0,z1,z3,z13,z354,z6]),(0,[z14,z0,z921,z3,z4,z5]),(0,[z0,z356,z3,z261,z4,z5]),(0,[z0,z1,z3,z20,z5,z592])],[(0,[z0,z1,z3,z4,z5,z1393]),(0,[z0,z1,z3,z1394,z4,z5])],[(0,[z0,z1,z3,z4,z5,z1395]),(0,[z1,z3,z4,z5,z155,z192]),(0,[z18,z0,z1,z3,z133,z6])],[(0,[z95,z1,z3,z157,z5,z96]),(0,[z0,z1,z3,z1396,z4,z5]),(0,[z0,z1,z3,z4,z5,z1397])],[(0,[z194,z1,z3,z109,z5,z289]),(0,[z0,z1,z3,z4,z5,z1398]),(0,[z82,z0,z230,z3,z47,z6]),(0,[z0,z1,z3,z4,z5,z1399]),(0,[z0,z1,z176,z4,z5,z9]),(0,[z14,z0,z443,z3,z4,z5])],[(0,[z135,z95,z0,z1,z3,z5]),(0,[z706,z1,z3,z4,z5,z39]),(1,[z737,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z374])],[(0,[z0,z1,z3,z303,z203,z6])],[(0,[z0,z1,z400,z4,z5,z747]),(0,[z0,z435,z1,z4,z5,z9]),(0,[z59,z1,z52,z4,z5,z6]),(0,[z1400,z0,z1,z3,z4,z5])],[(0,[z0,z1401,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z1402])],[(0,[z25,z1,z3,z4,z5,z39]),(0,[z0,z343,z3,z4,z13,z6])],[(0,[z0,z1403,z1,z3,z4,z5]),(0,[z0,z146,z3,z4,z133,z6]),(0,[z135,z0,z1,z3,z141,z5])],[(0,[z14,z0,z1,z400,z4,z5]),(0,[z0,z1,z3,z1404,z4,z5]),(0,[z0,z1,z3,z1405,z4,z5]),(0,[z0,z1,z3,z1406,z5,z6])],[(0,[z0,z1,z102,z4,z5,z9]),(0,[z0,z1,z1407,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1408]),(0,[z0,z1,z765,z157,z4,z5]),(0,[z0,z146,z3,z141,z5,z26])],[(0,[z0,z1,z3,z4,z5,z1409])],[(0,[z914,z0,z1,z3,z4,z5]),(0,[z0,z1,z4,z5,z166,z330]),(0,[z0,z1410,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z6,z1297])],[(0,[z82,z0,z3,z20,z47,z5])]],
   [[(0,[z0,z1,z3,z4,z5,z1411]),(0,[z0,z1,z3,z496,z4,z5]),(0,[z189,z0,z1,z3,z153,z5])],[(0,[z0,z117,z3,z4,z581,z6]),(0,[z737,z1,z3,z11,z4,z5]),(0,[z0,z53,z1,z4,z70,z199]),(0,[z774,z0,z343,z3,z4,z5])],[(0,[z14,z0,z117,z3,z4,z27]),(0,[z0,z1,z75,z3,z4,z6]),(0,[z0,z1,z3,z4,z5,z1412]),(0,[z0,z1,z3,z4,z5,z729])],[(0,[z14,z0,z1,z3,z423,z5]),(0,[z0,z1,z3,z4,z1413,z5]),(0,[z142,z0,z3,z4,z378,z5]),(0,[z0,z1,z3,z4,z5,z1414]),(0,[z18,z0,z1,z3,z49,z9])],[(0,[z0,z36,z159,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1415]),(0,[z0,z1,z3,z4,z5,z1416]),(0,[z0,z1,z3,z4,z1417,z5]),(0,[z0,z1,z3,z1418,z4,z5])],[(0,[z0,z1,z3,z4,z5,z1419]),(0,[z0,z1,z3,z5,z74,z729])],[(0,[z0,z129,z3,z4,z5,z9]),(0,[z169,z0,z1,z1246,z4,z5]),(0,[z0,z3,z4,z5,z1319,z26]),(0,[z0,z1,z3,z1420,z4,z5]),(0,[z14,z0,z1,z3,z4,z195]),(0,[z0,z1,z3,z5,z6,z1311])],[(0,[z0,z1,z1421,z4,z5,z6]),(0,[z0,z1,z3,z4,z195,z39]),(0,[z0,z1,z3,z1422,z5,z6]),(0,[z0,z1,z3,z4,z133,z9])],[(0,[z0,z1,z3,z4,z5,z1423])],[(0,[z0,z1,z3,z4,z5,z1424]),(0,[z0,z1,z3,z463,z5,z6]),(0,[z0,z1,z4,z5,z1425,z6]),(0,[z0,z1,z3,z1426,z4,z5]),(0,[z0,z217,z31,z4,z294,z6]),(0,[z0,z1,z3,z145,z4,z104])],[(0,[z0,z1,z102,z20,z4,z5]),(0,[z0,z1,z3,z4,z124,z329]),(0,[z650,z1,z3,z4,z5,z26])],[(0,[z1115,z0,z1,z3,z5,z26]),(0,[z0,z58,z159,z4,z5,z371])],[(0,[z0,z1,z3,z1427,z5,z6]),(0,[z584,z1,z3,z4,z5,z26])],[(0,[z0,z1,z3,z944,z4,z5]),(0,[z0,z1,z3,z4,z5,z324]),(0,[z0,z1,z3,z4,z5,z478])],[(0,[z23,z273,z3,z4,z5,z26]),(0,[z0,z1377,z1,z3,z4,z5])],[(0,[z0,z1,z3,z1428,z4,z5]),(0,[z0,z1,z1246,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1429]),(0,[z0,z1,z3,z20,z12,z13])]],
   [[(0,[z87,z0,z1,z3,z5,z500]),(0,[z0,z1,z3,z4,z360,z46])],[(0,[z0,z1,z3,z4,z78,z6]),(0,[z0,z1,z3,z4,z5,z1430]),(0,[z0,z1,z3,z4,z5,z1431])],[(0,[z0,z1,z3,z4,z5,z1432]),(0,[z0,z1,z3,z4,z5,z1433]),(0,[z0,z1,z3,z4,z5,z1434])],[(0,[z0,z1,z3,z4,z5,z1435]),(0,[z84,z1,z3,z4,z5,z26]),(0,[z0,z1,z3,z5,z267,z6]),(0,[z0,z146,z3,z20,z141,z5]),(0,[z0,z1,z619,z4,z5,z9]),(0,[z0,z1,z3,z4,z5,z1436]),(0,[z0,z1,z3,z4,z5,z1437])],[(0,[z0,z1438,z1,z3,z4,z5]),(0,[z0,z129,z3,z20,z4,z5]),(0,[z0,z1,z3,z20,z4,z198]),(0,[z0,z545,z3,z4,z27,z6]),(0,[z0,z1,z3,z4,z1077,z6])],[(0,[z1439,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z1440,z4,z5]),(0,[z0,z1,z3,z364,z4,z202]),(0,[z0,z1,z3,z4,z5,z1441])],[(0,[z0,z1,z3,z4,z5,z1442]),(0,[z0,z1,z3,z4,z5,z804]),(0,[z18,z0,z1,z3,z49,z26])],[(0,[z0,z1,z3,z4,z5,z94]),(0,[z287,z1,z3,z4,z256,z6])],[(0,[z0,z1,z3,z4,z5,z56]),(0,[z0,z343,z3,z4,z5,z6])],[(0,[z0,z333,z159,z4,z5,z6]),(0,[z0,z1,z3,z1443,z4,z5]),(0,[z0,z1,z3,z4,z5,z1444]),(0,[z0,z1,z3,z4,z212,z9]),(0,[z0,z1,z3,z4,z108,z156])],[(0,[z0,z1,z3,z4,z78,z56]),(0,[z23,z273,z3,z4,z5,z320]),(0,[z0,z1,z3,z1445,z4,z5]),(0,[z0,z1,z3,z4,z5,z1446]),(0,[z37,z1,z3,z4,z734,z6]),(0,[z0,z1,z3,z463,z256,z6]),(0,[z135,z0,z1,z3,z11,z5]),(0,[z0,z1,z4,z5,z834,z6])],[(0,[z0,z220,z3,z4,z5,z9]),(0,[z0,z1,z3,z4,z5,z1447]),(0,[z0,z1,z3,z1448,z4,z5])],[(0,[z0,z1449,z3,z4,z5,z6]),(0,[z0,z1,z3,z5,z1255,z26]),(0,[z0,z1,z3,z4,z5,z1450]),(0,[z0,z3,z4,z5,z920,z66])],[(0,[z0,z1,z3,z4,z5,z1451]),(0,[z0,z1,z248,z3,z4,z218]),(0,[z0,z117,z3,z4,z571,z6]),(0,[z0,z3,z4,z338,z112,z6]),(0,[z14,z0,z1,z1017,z4,z5])],[(0,[z0,z1452,z1,z3,z4,z6]),(0,[z0,z1,z3,z303,z5,z324]),(0,[z95,z1,z3,z157,z5,z39]),(0,[z0,z1,z3,z4,z5,z1453]),(0,[z0,z1,z3,z4,z5,z1454]),(0,[z0,z1,z196,z4,z127,z56]),(0,[z0,z1,z3,z4,z45,z156])],[(0,[z23,z1,z3,z4,z5,z123]),(0,[z0,z1455,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1456]),(0,[z1179,z0,z1,z3,z5,z9])]],
   [[(0,[z0,z1,z3,z4,z1457,z5]),(0,[z322,z1,z3,z157,z5,z6]),(0,[z184,z0,z1,z4,z5,z834])],[],[(0,[z0,z1,z3,z5,z1458,z6]),(0,[z0,z129,z3,z4,z198,z6]),(0,[z430,z1,z3,z109,z5,z6]),(0,[z165,z1,z3,z4,z5,z39]),(0,[z0,z1,z3,z4,z5,z1459])],[(0,[z0,z3,z884,z4,z5,z6]),(0,[z82,z0,z3,z47,z133,z6]),(0,[z0,z1460,z1,z3,z4,z5]),(0,[z14,z737,z1,z3,z4,z5])],[(0,[z0,z1,z1461,z4,z5,z6]),(0,[z189,z0,z1,z3,z133,z6]),(0,[z0,z1,z3,z4,z506,z5]),(0,[z0,z1,z461,z4,z5,z9])],[(0,[z0,z1,z3,z109,z124,z6]),(0,[z0,z1,z3,z4,z1462,z6])],[(0,[z14,z0,z1,z3,z4,z78]),(0,[z0,z1,z3,z4,z298,z46]),(0,[z0,z1,z1463,z3,z4,z5])],[(0,[z0,z1,z3,z4,z5,z1464]),(0,[z0,z1,z3,z4,z5,z1465]),(0,[z0,z1,z3,z4,z5,z1466]),(0,[z0,z1,z3,z20,z277,z5])],[(0,[z14,z0,z217,z31,z4,z5]),(0,[z0,z65,z3,z50,z4,z5]),(0,[z8,z0,z1,z75,z69,z6])],[(0,[z0,z1,z3,z4,z1467,z6]),(0,[z0,z220,z3,z20,z4,z5]),(0,[z0,z1,z3,z303,z5,z56]),(0,[z0,z1,z3,z4,z203,z26]),(0,[z14,z0,z58,z159,z4,z5]),(0,[z0,z1,z3,z13,z133,z6]),(0,[z189,z14,z0,z1,z3,z5]),(0,[z0,z1,z3,z4,z5,z1468]),(0,[z0,z714,z3,z4,z5,z6])],[(0,[z0,z1,z102,z4,z5,z1006])],[(0,[z0,z1,z1469,z3,z4,z5]),(0,[z1,z3,z4,z5,z155,z26]),(0,[z0,z1,z477,z4,z5,z9]),(0,[z0,z1,z3,z4,z5,z1470]),(0,[z0,z1,z513,z4,z5,z9])],[(0,[z0,z1,z400,z4,z5,z26]),(0,[z0,z1,z3,z4,z5,z1471]),(0,[z0,z1,z3,z4,z5,z1472]),(0,[z340,z1,z3,z4,z5,z39]),(0,[z0,z3,z4,z47,z133,z6]),(0,[z0,z146,z3,z141,z5,z9])],[(0,[z0,z1,z3,z4,z5,z1473]),(0,[z457,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z56,z1030])],[(0,[z0,z1,z3,z4,z1462,z56]),(0,[z0,z1181,z3,z20,z4,z5]),(0,[z428,z0,z1,z3,z4,z175])],[(0,[z0,z1,z3,z4,z5,z1474]),(0,[z0,z1,z3,z4,z5,z1475]),(0,[z0,z443,z3,z4,z5,z9])]],
   [[(0,[z95,z1,z3,z4,z5,z123]),(0,[z0,z1,z3,z4,z5,z1476]),(0,[z0,z1,z3,z4,z5,z251])],[(0,[z0,z1,z3,z4,z1477,z6]),(0,[z0,z1,z3,z4,z5,z1478]),(0,[z86,z254,z1,z3,z4,z5]),(0,[z227,z0,z1,z4,z5,z424]),(0,[z0,z1,z3,z4,z5,z243]),(0,[z14,z0,z1,z3,z20,z5])],[],[(0,[z0,z1,z102,z4,z280,z6]),(0,[z0,z1,z3,z4,z5,z1479]),(0,[z0,z1,z1480,z4,z5,z6]),(0,[z0,z1,z3,z1481,z4,z5]),(0,[z0,z1,z3,z4,z1482,z5]),(0,[z0,z1,z10,z11,z5,z251]),(0,[z0,z1,z3,z4,z1483,z5])],[],[(0,[z0,z1,z3,z1484,z5,z6]),(0,[z0,z1,z3,z1485,z4,z5]),(0,[z18,z0,z443,z3,z49,z6])],[(0,[z0,z36,z1,z4,z5,z9]),(0,[z171,z987,z3,z4,z5,z6]),(0,[z0,z1486,z3,z4,z5,z6]),(0,[z51,z1,z52,z4,z5,z39]),(0,[z86,z1,z3,z20,z4,z256]),(0,[z0,z3,z4,z5,z1319,z9])],[(0,[z0,z220,z3,z4,z198,z6]),(0,[z0,z117,z3,z4,z27,z26]),(0,[z0,z1487,z1,z3,z4,z5])],[(0,[z0,z1,z400,z4,z5,z320]),(0,[z1094,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z1488]),(0,[z0,z1,z3,z4,z5,z1489]),(0,[z0,z53,z1,z4,z263,z6]),(0,[z0,z1,z3,z4,z5,z1490])],[],[(0,[z0,z1,z3,z4,z1491,z6]),(0,[z0,z1,z1492,z3,z4,z5]),(0,[z0,z1,z52,z4,z5,z330]),(0,[z95,z1,z3,z157,z5,z329]),(0,[z0,z1,z3,z4,z5,z1493]),(0,[z37,z1,z3,z4,z63,z9]),(0,[z0,z1,z3,z61,z4,z5])],[(0,[z1115,z0,z1,z3,z5,z9]),(0,[z0,z1,z3,z4,z5,z1494])],[(0,[z0,z1,z3,z282,z4,z283]),(0,[z0,z1,z1495,z3,z4,z5])],[(0,[z0,z1,z3,z4,z5,z1496]),(0,[z0,z1,z3,z20,z463,z5]),(0,[z0,z1,z3,z12,z13,z56])],[(0,[z23,z273,z3,z4,z5,z9]),(0,[z0,z1,z3,z4,z5,z1497]),(0,[z0,z1,z3,z423,z5,z306]),(0,[z1115,z0,z1,z3,z52,z5]),(0,[z0,z1,z3,z4,z5,z1498]),(0,[z660,z1,z3,z4,z63,z6]),(0,[z0,z1,z3,z1499,z5,z6]),(0,[z0,z591,z3,z4,z27,z6]),(0,[z0,z1,z3,z4,z5,z1500]),(0,[z14,z0,z1,z3,z388,z5])],[(0,[z0,z129,z3,z4,z5,z306]),(0,[z0,z1,z3,z4,z1501,z6])]],
   [[(0,[z937,z189,z0,z1,z3,z5])],[(0,[z0,z1,z3,z4,z5,z1358]),(0,[z0,z1502,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1503]),(0,[z1372,z1,z3,z4,z5,z6]),(0,[z0,z1,z4,z5,z9,z535])],[(0,[z0,z1,z3,z4,z5,z1504]),(0,[z0,z443,z3,z4,z5,z26]),(0,[z0,z445,z3,z4,z112,z6]),(0,[z1216,z0,z1,z3,z4,z5]),(0,[z0,z1,z4,z70,z781,z6])],[(0,[z0,z1,z3,z4,z1505,z6]),(0,[z0,z1,z884,z4,z5,z6]),(0,[z0,z1,z257,z4,z5,z9]),(0,[z8,z0,z1,z408,z69,z5])],[(0,[z0,z1,z3,z4,z1506,z5]),(0,[z0,z58,z159,z4,z5,z39])],[(0,[z0,z1,z3,z1507,z5,z6]),(0,[z0,z1,z3,z4,z5,z266]),(0,[z0,z1,z4,z673,z5,z9]),(0,[z0,z217,z31,z4,z5,z174]),(0,[z1274,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z1508]),(0,[z0,z1,z75,z3,z4,z26]),(0,[z0,z1509,z1,z3,z4,z5]),(0,[z14,z0,z1,z3,z12,z13])],[(0,[z0,z230,z1,z3,z157,z6]),(0,[z0,z53,z1,z4,z627,z6]),(0,[z0,z702,z3,z4,z27,z6]),(0,[z0,z53,z343,z3,z4,z6])],[(0,[z0,z1,z3,z110,z5,z6]),(0,[z51,z14,z1,z52,z4,z5]),(0,[z37,z1,z3,z20,z4,z63]),(0,[z0,z1,z3,z4,z5,z1510]),(0,[z0,z1,z3,z1511,z4,z5])],[(0,[z0,z1,z3,z22,z5,z9]),(0,[z0,z1512,z3,z4,z5,z6]),(0,[z51,z1,z52,z4,z203,z6]),(0,[z0,z1,z3,z1513,z5,z6]),(0,[z0,z356,z3,z4,z5,z66])],[(0,[z0,z1,z3,z110,z78,z6]),(0,[z0,z1,z3,z4,z5,z1514]),(0,[z0,z1,z3,z1515,z4,z5]),(0,[z287,z1,z3,z4,z5,z26]),(0,[z0,z64,z3,z4,z112,z9]),(0,[z0,z1,z3,z4,z5,z438])],[(0,[z0,z129,z3,z423,z5,z6]),(0,[z14,z0,z1,z3,z4,z198]),(0,[z1516,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z277,z5,z97]),(0,[z0,z1,z3,z4,z5,z1517])],[(0,[z23,z273,z3,z20,z4,z5]),(0,[z194,z1,z3,z717,z5,z6]),(0,[z0,z1,z3,z4,z5,z1518]),(0,[z0,z1,z3,z5,z1255,z9])],[(0,[z0,z1,z3,z4,z5,z1519]),(0,[z0,z1,z3,z4,z734,z6]),(0,[z37,z1,z3,z4,z63,z26]),(0,[z0,z1,z3,z463,z5,z26]),(0,[z0,z1,z3,z4,z5,z1520]),(0,[z14,z0,z1,z3,z4,z133]),(0,[z0,z146,z3,z574,z5,z6]),(0,[z0,z1,z3,z5,z267,z827])],[(0,[z0,z1521,z3,z4,z5,z6]),(0,[z0,z1522,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1523])],[(0,[z0,z1,z3,z4,z5,z1524]),(1,[z0,z1,z765,z4,z5]),(0,[z0,z117,z3,z20,z4,z27]),(0,[z8,z0,z1,z69,z5,z9])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 491) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 491).take 493) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 984).take 499) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb3 : chunkB SB 1 ((bkA.flatten.flatten.drop 1483).take 53) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1536)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [491, 493, 499, 53] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_cons pb3 (windowsG_nil pbend))))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 128).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 128).take 140).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 268).take 128).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 396).take 116).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 512)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [128, 140, 128, 116] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_cons pc3 (windowsF_nil pcend))))

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

end PEqualNP.Outside.L_meta_38841

theorem PEqualNP.Outside.L_meta_38841 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808928 * 2 ^ 32 + 4274580672) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808928 * 2 ^ 32 + 4274580672) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_38841.solve