import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_38823

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
  Nat.testBit (4276808928 * 2 ^ 32 + 4209682592) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x000851c42020a5ac#64 ++ 0x20010a38840414b5#64 ++ 0x9819f3c460e3ffff#64 ++ 0xd3033e788c1c7fff#64 : BitVec 256),
   (0x0862c45d988d92e1#64 ++ 0x410c588bb311b25c#64 ++ 0xe8e6ccff989d93e7#64 ++ 0xbd1cd99ff313b27c#64 : BitVec 256),
   (0x03050e02cb161851#64 ++ 0x8060a1c05962c30a#64 ++ 0xbf070f07ff1e1c7f#64 ++ 0x77e0e1e0ffe3c38f#64 : BitVec 256),
   (0x15b80fa81de01f06#64 ++ 0x02b701f503bc03e0#64 ++ 0xf7f80ff81fe01f86#64 ++ 0xfeff01ff03fc03f0#64 : BitVec 256),
   (0x06f7a00016db4000#64 ++ 0x00def40002db6800#64 ++ 0xdffff0001fffe005#64 ++ 0xfbfffe0003fffc00#64 : BitVec 256),
   (0x27dffbf760000000#64 ++ 0x04fbff7eec000000#64 ++ 0xe7ffffffe0000003#64 ++ 0xfcfffffffc000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 5]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [1, 6]⟩, ⟨.and, [2, 4]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [2, 4]⟩, ⟨.and, [0, 12]⟩, ⟨.and, [11, 8]⟩, ⟨.or, [13, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0000000000000000 0x0000000000000000 0x9801030460021c7f 0x530020608c00438f

def z1 : W := mkw 0x000851c42020a5ac 0x20010a38840414b5 0x9819f3c460e3ffff 0xd3033e788c1c7fff

def z2 : W := mkw 0x03050e02cb161851 0x8060a1c05962c30a 0xbf070f07ff1e1c7f 0x77e0e1e0ffe3c38f

def z3 : W := mkw 0x06f7a00016db4000 0x00def40002db6800 0xdffff3047ffffc7f 0xfbfffe608fffff8f

def z4 : W := mkw 0x0862c45d988d92e1 0x410c588bb311b25c 0xe8e6ccff989d93e7 0xbd1cd99ff313b27c

def z5 : W := mkw 0x15b80fa81de01f06 0x02b701f503bc03e0 0xf7f80ff81fe01f86 0xfeff01ff03fc03f0

def z6 : W := mkw 0x27dffbf760000000 0x04fbff7eec000000 0xe7ffffffe0000003 0xfcfffffffc000000

def z7 : W := mkw 0x06f7a00016db4000 0x00def40002db6800 0xdffff0001fffe005 0xfbfffe0003fffc00

def z8 : W := mkw 0x06fff1c436fbe5ac 0x20dffe3886df7cb5 0xdffff3c47fffffff 0xfbfffe788fffffff

def z9 : W := mkw 0x27d7aa3340000000 0x04faf54668000000 0x67e60c3b80000000 0x2cfcc18770000000

def z10 : W := mkw 0x27dffbf76020a5ac 0x24fbff7eec0414b5 0xffffffffe0e3ffff 0xfffffffffc1c7fff

def z11 : W := mkw 0x0a47e055821fc0e1 0x4148fc0ab043f81c 0x0807f007801fe061 0x0100fe00f003fc0c

def z12 : W := mkw 0x0ef7e45d9edfd2e1 0x41defc8bb3dbfa5c 0xfffffcff9ffff3e7 0xffffff9ff3fffe7c

def z13 : W := mkw 0x0695200006524000 0x00d2a40000ca4800 0x1719300007626000 0x42e3260000ec4c00

def z14 : W := mkw 0x0800445d880492e1 0x4100088bb100925c 0x20000cff800013e2 0x0400019ff000027c

def z15 : W := mkw 0x27dffbf760000000 0x04fbff7eec000000 0x071ff307e0000001 0x40e3fe60fc000000

def z16 : W := mkw 0x000851c42020a5ac 0x20010a38840414b5 0x0018f0c000e1e380 0x80031e18001c3c70

def z17 : W := mkw 0x03050e02cb161851 0x8060a1c05962c30a 0x27060c039f1c0000 0x24e0c18073e38000

def z18 : W := mkw 0x0020040818801200 0x0004008103100240 0xe0e00cf818801386 0xbc1c019f03100270

def z19 : W := mkw 0x15b00e281dc01a02 0x02b601c503b80340 0x67e00c381f000000 0x2cfc018703e00000

def z20 : W := mkw 0x0205000002120000 0x0040a00000424000 0x9f0700001f1e0005 0x73e0e00003e3c000

def z21 : W := mkw 0x02050002c2160051 0x8040a0005842c00a 0x08070007e01e0079 0x0100e000fc03c00f

def z22 : W := mkw 0x0042c05500000000 0x0008580aa0000000 0xe0e6ccff80000003 0xbc1cd99ff0000000

def z23 : W := mkw 0x11080fa809201f06 0x022101f5012403e0 0x20000ff800001f82 0x040001ff000003f0

def z24 : W := mkw 0x07ffaba016db4000 0x00fff57402db6800 0xfffffff81fffe007 0xffffffff03fffc00

def z25 : W := mkw 0x07f7ae02dfdf5851 0x80fef5c05bfbeb0a 0xffffff07fffffc7f 0xffffffe0ffffff8f

def z26 : W := mkw 0x15b84fec1de09fa6 0x02b709fd83bc13f4 0xfff8cffc1fe19fe7 0xffff19ff83fc33fc

def z27 : W := mkw 0x27dfabb340000000 0x04fbf57668000000 0xe7fe0ffb80000002 0xfcffc1ff70000000

def z28 : W := mkw 0x0020000016db4000 0x0004000002db6800 0x9819f0001fffe005 0xd3033e0003fffc00

def z29 : W := mkw 0x03050e02cb161851 0x8060a1c05962c30a 0x37010f07e7021c7a 0x46e021e0fce0438f

def z30 : W := mkw 0x0b67ce5fdb9f9af1 0xc16cf9cbfb73f35e 0xffe7cfffff9f9fff 0xfffcf9fffff3f3ff

def z31 : W := mkw 0x25dafbf760000000 0x04bb5f7eec000000 0x60f8ffffe0000002 0x8c1f1ffffc000000

def z32 : W := mkw 0x05b00e001dc01800 0x00b601c003b80300 0xf7f80f001fe01c06 0xfeff01e003fc0380

def z33 : W := mkw 0x14b801a814e00706 0x02970035029c00e0 0xd7f800f81fe00384 0xfaff001f03fc0070

def z34 : W := mkw 0x0062800010890000 0x000c500002112000 0xc8e6c000189d8005 0xb91cd8000313b000

def z35 : W := mkw 0x08200408988d92e1 0x410400811311b25c 0x08000000189d93e4 0x010000000313b27c

def z36 : W := mkw 0x1db84ffd9de49fe7 0x43b709ffb3bc93fc 0xf7f80fff9fe01fe6 0xfeff01fff3fc03fc

def z37 : W := mkw 0x1dfacffd9ded9fe7 0x43bf59ffb3bdb3fc 0xfffecfff9ffd9fe7 0xffffd9fff3ffb3fc

def z38 : W := mkw 0x06f7a00016db4000 0x00def40002db6800 0x47e600001f1c0000 0x28fcc00003e38000

def z39 : W := mkw 0x0000000000000000 0x0000000000000000 0x800000c000801386 0x9000001800100270

def z40 : W := mkw 0x01000e0009001800 0x002001c001200300 0xb7000f001f001c06 0x76e001e003e00380

def z41 : W := mkw 0x0862c05d908d82e1 0x410c580bb211b05c 0x48e6c0ff809d83e1 0x891cd81ff013b07c

def z42 : W := mkw 0x000004008b161851 0x800000801162c30a 0x980103047f1e1c7f 0x530020608fe3c38f

def z43 : W := mkw 0x2247a01340000000 0x0448f40268000000 0x0006000380000000 0x0000c00070000000

def z44 : W := mkw 0x0000000002120000 0x0000000000424000 0x180000001f1e0004 0x0300000003e3c000

def z45 : W := mkw 0x07f7aa0256db4000 0x00fef5404adb6800 0xffffff07ffffe007 0xffffffe0fffffc00

def z46 : W := mkw 0x35b85fff7de01f06 0x06b70bffefbc03e0 0xf7f80fffffe01f86 0xfeff01fffffc03f0

def z47 : W := mkw 0x04b0000014c00000 0x0096000002980000 0xd7f800001fe00004 0xfaff000003fc0000

def z48 : W := mkw 0x01000e02c9041851 0x802001c05920830a 0x20000f07e0001c7a 0x040001e0fc00038f

def z49 : W := mkw 0x04f2a00014c94000 0x009e540002992800 0x40f8f00000e1e000 0x881f1e00001c3c00

def z50 : W := mkw 0x0000040088041041 0x0000008011008208 0xa8060c07981c1067 0x3500c180f303820c

def z51 : W := mkw 0x0000405500000000 0x0000080aa0000000 0x20000cff80000002 0x0400019ff0000000

def z52 : W := mkw 0x14b0002814c00202 0x0296000502980040 0x40e0003800000000 0x081c000700000000

def z53 : W := mkw 0x000004008b36bdfd 0xa00000801166d7bf 0x180000001ffffffc 0x0300000003ffffff

def z54 : W := mkw 0x000004008b161851 0x800000801162c30a 0x180000001f1e1c7c 0x0300000003e3c38f

def z55 : W := mkw 0x179d0ba247720d16 0x82f3a17448ee41a2 0x1719030067620c18 0x42e320600cec4183

def z56 : W := mkw 0x17bd0faadff61f57 0x82f7a1f55bfec3ea 0xffff0ffffffe1fff 0xffffe1ffffffc3ff

def z57 : W := mkw 0x15980ba005600d06 0x02b3017400ac01a0 0x1718030007600c00 0x42e3006000ec0180

def z58 : W := mkw 0x37dffbf765600d06 0x06fbff7eecac01a0 0xf7ffffffe7600c03 0xfefffffffcec0180

def z59 : W := mkw 0x0b250e0adb9f9af1 0xc164a1c15b73f35e 0xbf070f07ff9f9fff 0x77e0e1e0fff3f3ff

def z60 : W := mkw 0x27ffbba276db4000 0x04fff7744edb6800 0xdffff3007fffe005 0xfbfffe600ffffc00

def z61 : W := mkw 0x08628419988d1241 0x410c50833311a248 0x60e60c3b981c0000 0x2c1cc18773038000

def z62 : W := mkw 0x0008018000200504 0x00010030000400a0 0x901803c000e01f86 0xd2030078001c03f0

def z63 : W := mkw 0x0962ce5fd98d9af1 0xc12c59cbfb31b35e 0xe8e6cffff89d9fff 0xbd1cd9ffff13b3ff

def z64 : W := mkw 0x00000002c0040051 0x800000005800800a 0x00000007e0000078 0x00000000fc00000f

def z65 : W := mkw 0x27fffbf774c94000 0x04ffff7eee992800 0xe7ffffffe0e1e003 0xfcfffffffc1c3c00

def z66 : W := mkw 0x03250e0adb961a51 0x8064a1c15b72c34a 0xffe70fffff9e1fff 0xfffce1fffff3c3ff

def z67 : W := mkw 0x05dacbf500000000 0x00bb597ea0000000 0xe7fecfff80000003 0xfcffd9fff0000000

def z68 : W := mkw 0x29085fffe80492e1 0x45210bfffd00925c 0x20000fffe00013e2 0x040001fffc00027c

def z69 : W := mkw 0x00004044000080a0 0x0000080880001014 0x8800c0c4008193e7 0x910018188010327c

def z70 : W := mkw 0x0820040898adb7ed 0x610400811315b6fd 0x1800000018fffffc 0x03000000031fffff

def z71 : W := mkw 0x27dffbf760200504 0x04fbff7eec0400a0 0xf7ffffffe0e01f87 0xfefffffffc1c03f0

def z72 : W := mkw 0x000000000020a5ac 0x20000000000414b5 0x1800000000e3fffc 0x03000000001c7fff

def z73 : W := mkw 0x15b80fa81de01f06 0x02b701f503bc03e0 0x67f80cf81fe00380 0xacff019f03fc0070

def z74 : W := mkw 0x000811802020250c 0x20010230040404a1 0x1019330060626c18 0x420326600c0c4d83

def z75 : W := mkw 0x27dffbf76020250c 0x24fbff7eec0404a1 0xf7ffffffe0626c1b 0xfefffffffc0c4d83

def z76 : W := mkw 0x15b85fec3de0bfae 0x22b70bfd87bc17f5 0xfff9fffc7fe3ffff 0xffff3fff8ffc7fff

def z77 : W := mkw 0x000050442000a0a8 0x20000a0884001415 0x0801f0046003e079 0x01003e008c007c0f

def z78 : W := mkw 0x08628419988d1241 0x410c50833311a248 0xe0e60cfb989c1386 0xbc1cc19f73138270

def z79 : W := mkw 0x0020000016db4000 0x0004000002db6800 0x180000001fffe004 0x0300000003fffc00

def z80 : W := mkw 0x0842c455880d90e1 0x4108588ab101b21c 0xa806cc07981d9067 0x3500d980f303b20c

def z81 : W := mkw 0x03050a0240000000 0x0060a14048000000 0xa7070f07e0000003 0x74e0e1e0fc000000

def z82 : W := mkw 0x21085bf760000000 0x04210b7eec000000 0x20000fffe0000002 0x040001fffc000000

def z83 : W := mkw 0x2ffffffff88d92e1 0x45ffffffff11b25c 0xeffffffff89d93e7 0xfdffffffff13b27c

def z84 : W := mkw 0x15b80fa81de01f06 0x02b701f503bc03e0 0xfff90ffc7fe21fff 0xffff21ff8ffc43ff

def z85 : W := mkw 0x27dffbf760000000 0x04fbff7eec000000 0xffffffffe0e3e007 0xfffffffffc1c7c00

def z86 : W := mkw 0x0ff7ee5fdfdfdaf1 0xc1fefdcbfbfbfb5e 0xffffffffffffffff 0xffffffffffffffff

def z87 : W := mkw 0x000851c42020a5ac 0x20010a38840414b5 0x901803c460e01ffe 0xd20300788c1c03ff

def z88 : W := mkw 0x03050a0243120810 0x8060a14048624102 0xb7070f07e7020c1b 0x76e0e1e0fce04183

def z89 : W := mkw 0x000000000020a5ac 0x20000000000414b5 0x0000000000e1e380 0x00000000001c3c70

def z90 : W := mkw 0x0000000000000000 0x0000000000000000 0x9819f00000e3e005 0xd3033e00001c7c00

def z91 : W := mkw 0x0008118020000000 0x0001023004000000 0x0019330060000000 0x400326600c000000

def z92 : W := mkw 0x05985be420000000 0x00b30b7c84000000 0xe7f9fffc60000003 0xfcff3fff8c000000

def z93 : W := mkw 0x279d3ba266524000 0x04f3a7744cca4800 0x1719330067626000 0x42e326600cec4c00

def z94 : W := mkw 0x06f7a00016db4000 0x00def40002db6800 0x47fef0001ffde000 0xa8ffde0003ffbc00

def z95 : W := mkw 0x030d1b8263322d1c 0xa061a3704c6645a3 0x1719330067626c18 0x42e326600cec4d83

def z96 : W := mkw 0x1dfadffdbdedbfef 0x63bf5bffb7bdb7fd 0xffffffffffffffff 0xffffffffffffffff

def z97 : W := mkw 0x24daf1f520000000 0x049b5e3ea4000000 0x40f8f0f800000000 0x881f1e1f00000000

def z98 : W := mkw 0x14b801a814e00706 0x02970035029c00e0 0xd0f803f800e01f86 0xda1f007f001c03f0

def z99 : W := mkw 0x15b80fa81dc01a02 0x02b701f503b80340 0xe7f80ff81f000002 0xfcff01ff03e00000

def z100 : W := mkw 0x27dffff7eb161851 0x84fbfffefd62c30a 0xffffffffff1e1c7f 0xffffffffffe3c38f

def z101 : W := mkw 0x2247f05760000000 0x0448fe0aec000000 0xe0e7fcffe0000003 0xbc1cff9ffc000000

def z102 : W := mkw 0x03050e0249001800 0x0060a1c049200300 0xb7070f07ff001c07 0x76e0e1e0ffe00380

def z103 : W := mkw 0x08200408988d92e1 0x410400811311b25c 0xe8e00cf8189d93e6 0xbd1c019f0313b27c

def z104 : W := mkw 0x000000000000a0a8 0x2000000000001415 0x080000000003e078 0x0100000000007c0f

def z105 : W := mkw 0x0842c45d880d92e1 0x4108588bb101b25c 0x2806ccff801d93e3 0x0500d99ff003b27c

def z106 : W := mkw 0x000050442000a0a8 0x20000a0884001415 0x9819f00460e3e07d 0xd3033e008c1c7c0f

def z107 : W := mkw 0x0062800010890000 0x000c500002112000 0x40e60000181c0000 0x281cc00003038000

def z108 : W := mkw 0x086ad5ddb8adb7ed 0x610d5abbb715b6fd 0xf8fffffff8ffffff 0xff1fffffff1fffff

def z109 : W := mkw 0x000851c420000000 0x00010a3884000000 0x8019f3c460000003 0xd0033e788c000000

def z110 : W := mkw 0x15b80ba815e00f06 0x02b7017502bc01e0 0x57f803f807e00f80 0xcaff007f00fc01f0

def z111 : W := mkw 0x15980fa80d601f06 0x02b301f501ac03e0 0x37180ff807601f82 0x46e301ff00ec03f0

def z112 : W := mkw 0x0247a000021b4000 0x0048f40000436800 0x0807f000001fe001 0x0100fe000003fc00

def z113 : W := mkw 0x17ffafa81ffb5f06 0x02fff5f503ff6be0 0xfffffff81fffff87 0xffffffff03fffff0

def z114 : W := mkw 0x1862c45d9ded9fe7 0x430c588bb3bdb3fc 0xf8e6ccff9ffd9fe7 0xbf1cd99ff3ffb3fc

def z115 : W := mkw 0x15b85fec3de01f06 0x02b70bfd87bc03e0 0xf7f9fffc7fe01f87 0xfeff3fff8ffc03f0

def z116 : W := mkw 0x279d3ba26020250c 0x24f3a7744c0404a1 0x1719330060626c18 0x42e326600c0c4d83

def z117 : W := mkw 0x1020000814e00706 0x02040001029c00e0 0x0000000000e00380 0x00000000001c0070

def z118 : W := mkw 0x0b67ce5fd88d92e1 0x416cf9cbfb11b25c 0xefe7cffff89d93e7 0xfdfcf9ffff13b27c

def z119 : W := mkw 0x21081ba260000000 0x042103744c000000 0x0000030060000000 0x000000600c000000

def z120 : W := mkw 0x27f7aa3356db4000 0x04fef5466adb6800 0x67e60c3b9f1c0000 0x2cfcc18773e38000

def z121 : W := mkw 0x05980ba000000000 0x00b3017400000000 0xe7f80ff800000002 0xfcff01ff00000000

def z122 : W := mkw 0x0862c45d9edfd2e1 0x410c588bb3dbfa5c 0xf8e6ccff9ffff3e7 0xbf1cd99ff3fffe7c

def z123 : W := mkw 0x0b67ce5fdb9f9af1 0xc16cf9cbfb73f35e 0xefe6ccff9f9d93e7 0xbdfcd99ff3f3b27c

def z124 : W := mkw 0x03055e46eb16b8f9 0xa060abc8dd62d71f 0xbf07ff07ff1ffc7f 0x77e0ffe0ffe3ff8f

def z125 : W := mkw 0x2000505760000000 0x04000a0aec000000 0x00000007e0000000 0x00000000fc000000

def z126 : W := mkw 0x0862801910890200 0x410c500322112040 0x40e0003800000000 0x081c000700000000

def z127 : W := mkw 0x24daf1f520000000 0x049b5e3ea4000000 0xe0fefcff80000003 0xbc1fdf9ff0000000

def z128 : W := mkw 0x16f7a4081ffb5f06 0x02def48103ff6be0 0xdffff0001fffff85 0xfbfffe0003fffff0

def z129 : W := mkw 0x082004089b9f9af1 0xc10400811373f35e 0x180000001f9f9ffc 0x0300000003f3f3ff

def z130 : W := mkw 0x079d0ba240000000 0x00f3a17448000000 0xe7ff0fffe0000003 0xfcffe1fffc000000

def z131 : W := mkw 0x102004081de01f06 0x0204008103bc03e0 0x100000001fe01f84 0x0200000003fc03f0

def z132 : W := mkw 0x0842c055800d80e1 0x4108580ab001b01c 0xe8e6ccff801d8063 0xbd1cd99ff003b00c

def z133 : W := mkw 0x000851c420000000 0x00010a3884000000 0x0018f0c000000000 0x80031e1800000000

def z134 : W := mkw 0x15b80fa81de01f06 0x02b701f503bc03e0 0x60f80ff800e01f82 0x8c1f01ff001c03f0

def z135 : W := mkw 0x0042c05500000000 0x0008580aa0000000 0x40e0c0f800000000 0x881c181f00000000

def z136 : W := mkw 0x279d3ba260000000 0x04f3a7744c000000 0x0719330060000000 0x40e326600c000000

def z137 : W := mkw 0x0ef7a4089edfd2e1 0x41def48113dbfa5c 0xdffff0001ffff3e5 0xfbfffe0003fffe7c

def z138 : W := mkw 0x1db80fa89ded9fe7 0x43b701f513bdb3fc 0xfff80ff81ffd9fe6 0xffff01ff03ffb3fc

def z139 : W := mkw 0x030d5fc6eb36bdfd 0xa061abf8dd66d7bf 0xbf1fffc7ffffffff 0xf7e3fff8ffffffff

def z140 : W := mkw 0x05900a2000000000 0x00b2014400000000 0x67e00c3800000000 0x2cfc018700000000

def z141 : W := mkw 0x15b80faadde41f57 0x82b701f55bbc83ea 0xf7f80fffffe01ffe 0xfeff01fffffc03ff

def z142 : W := mkw 0x14b801a814e00706 0x02970035029c00e0 0x40f800f800e00380 0x881f001f001c0070

def z143 : W := mkw 0x15b80fa81de01f06 0x02b701f503bc03e0 0x77f80f381f600c00 0x6eff01e703ec0180

def z144 : W := mkw 0x000851c42020a5ac 0x20010a38840414b5 0x980103c460021fff 0x530020788c0043ff

def z145 : W := mkw 0x234ffbf760000000 0x0469ff7eec000000 0x2007ffffe0000003 0x0400fffffc000000

def z146 : W := mkw 0x06f7e05516db4000 0x00defc0aa2db6800 0xfffffcff9fffe007 0xffffff9ff3fffc00

def z147 : W := mkw 0x15faafa81de95f06 0x02bf55f503bd2be0 0xf7f8fff81fe1ff86 0xfeff1fff03fc3ff0

def z148 : W := mkw 0x2ffffffffedfd2e1 0x45ffffffffdbfa5c 0xfffffffffffff3e7 0xfffffffffffffe7c

def z149 : W := mkw 0x102004089ff61f57 0x8204008113fec3ea 0x180000001ffe1ffc 0x0300000003ffc3ff

def z150 : W := mkw 0x0862c45d988d92e1 0x410c588bb311b25c 0x60e6ccfb989d8380 0xac1cd99f7313b070

def z151 : W := mkw 0x06fff1c436fbe5ac 0x20dffe3886df7cb5 0xdffff0c01fffe385 0xfbfffe1803fffc70

def z152 : W := mkw 0x27dffbf763120810 0x84fbff7eec624102 0xf7ffffffe7020c1b 0xfefffffffce04183

def z153 : W := mkw 0x27fffbf776db4000 0x04ffff7eeedb6800 0xffffffffffffe007 0xfffffffffffffc00

def z154 : W := mkw 0x27dfbbb360000000 0x04fbf7766c000000 0x67ff3f3be0000000 0x6cffe7e77c000000

def z155 : W := mkw 0x0062800010890000 0x000c500002112000 0xd8fff00018ffe005 0xfb1ffe00031ffc00

def z156 : W := mkw 0x279d3ba260000000 0x04f3a7744c000000 0xa71f3f07e0000003 0x74e3e7e0fc000000

def z157 : W := mkw 0x03050a0240000000 0x0060a14048000000 0xbf070f07e0021c7f 0x77e0e1e0fc00438f

def z158 : W := mkw 0x0862c05d108982a0 0x410c580ba2113054 0x40e0c0f800818380 0x881c181f00103070

def z159 : W := mkw 0x06f7a4009fdf5851 0x80def48013fbeb0a 0xdffff0001ffffc7d 0xfbfffe0003ffff8f

def z160 : W := mkw 0x07d7ae02cb161851 0x80faf5c05962c30a 0xffffff07ff1e1c7f 0xffffffe0ffe3c38f

def z161 : W := mkw 0x15980fa809201f06 0x02b301f5012403e0 0xe7f80ff800001f82 0xfcff01ff000003f0

def z162 : W := mkw 0x06d7a00006524000 0x00daf40000ca4800 0xd7fff00007626001 0xfafffe0000ec4c00

def z163 : W := mkw 0x279d3fa2eb161851 0x84f3a7f45d62c30a 0xbf1f3f07ff1e1c7f 0x77e3e7e0ffe3c38f

def z164 : W := mkw 0x08200408988d1241 0x410400811311a248 0x00000000181c0000 0x0000000003038000

def z165 : W := mkw 0x0842c055800d80e1 0x4108580ab001b01c 0x0806c007801d8061 0x0100d800f003b00c

def z166 : W := mkw 0x000851c42020a5ac 0x20010a38840414b5 0x000003c460001ffa 0x000000788c0003ff

def z167 : W := mkw 0x00004044000080a0 0x0000080880001014 0x000000c4000013e2 0x000000188000027c

def z168 : W := mkw 0x2ffffffff88d1241 0x45ffffffff11a248 0xe7fffffff81c0003 0xfcffffffff038000

def z169 : W := mkw 0x0347ca5740000000 0x0068f94ae8000000 0xe7e7cfffe0000003 0xfcfcf9fffc000000

def z170 : W := mkw 0x0000000082160051 0x800000001042c00a 0x08000000001e0078 0x010000000003c00f

def z171 : W := mkw 0x26d7f05760000000 0x04dafe0aec000000 0xc7fff007e0000001 0xf8fffe00fc000000

def z172 : W := mkw 0x15b00e281dc01a02 0x02b601c503b80340 0xe7e00cf81f801386 0xbcfc019f03f00270

def z173 : W := mkw 0x1fffcfffdfff9ff7 0xc3fff9fffbfff3fe 0xffffcfffffff9fff 0xfffff9fffffff3ff

def z174 : W := mkw 0x079d0fa2cb161851 0x80f3a1f45962c30a 0xffff0fffff1e1c7f 0xffffe1ffffe3c38f

def z175 : W := mkw 0x03050e02cb161851 0x8060a1c05962c30a 0x37070f03ff1e0c18 0x66e0e1e07fe3c183

def z176 : W := mkw 0x0020444c188092a0 0x0004088983101254 0xe8e0ccfc188193e7 0xbd1c199f8310327c

def z177 : W := mkw 0x0a47c057c21f80f1 0xc148f80af843f01e 0x0807c007e01f8079 0x0100f800fc03f00f

def z178 : W := mkw 0x08200008108982a0 0x4104000102113054 0x0000000000818380 0x0000000000103070

def z179 : W := mkw 0x24daf1f52020a5ac 0x249b5e3ea40414b5 0x40f8f0f800e1e380 0x881f1e1f001c3c70

def z180 : W := mkw 0x0820444c988d92e1 0x410408899311b25c 0x8800c0c4189d93e7 0x910018188313b27c

def z181 : W := mkw 0x0dfacffd988d92e1 0x41bf59ffb311b25c 0xeffecfff989d93e7 0xfdffd9fff313b27c

def z182 : W := mkw 0x0ef7e45d9edfd2e1 0x41defc8bb3dbfa5c 0xefe6ccff9f9d93e7 0xbdfcd99ff3f3b27c

def z183 : W := mkw 0x0042c055000080a0 0x0008580aa0001014 0xe8e6ccff808193e7 0xbd1cd99ff010327c

def z184 : W := mkw 0x020d51c42232a5ac 0x2041aa38844654b5 0x9f1ff3c47fffffff 0xf3e3fe788fffffff

def z185 : W := mkw 0x020504008a161041 0x0040a0801142c208 0xbf070c079f1e1067 0x77e0e180f3e3c20c

def z186 : W := mkw 0x000811802020250c 0x20010230040404a1 0x0000030060000c18 0x000000600c000183

def z187 : W := mkw 0x0247a000021b4000 0x0048f40000436800 0x00060000001c0000 0x0000c00000038000

def z188 : W := mkw 0x2ff7ee7fd88d92e1 0x45fefdcffb11b25c 0xefe6ccff989d93e7 0xbdfcd99ff313b27c

def z189 : W := mkw 0x000811802020250c 0x20010230040404a1 0x9819330460627c7f 0x530326608c0c4f8f

def z190 : W := mkw 0x2247f05760000000 0x0448fe0aec000000 0x0007f007e0000001 0x0000fe00fc000000

def z191 : W := mkw 0x0000404400000000 0x0000080880000000 0x8000c0c400000003 0x9000181880000000

def z192 : W := mkw 0x030d5fc6eb161851 0x8061abf8dd62c30a 0xbf1fffc7ff1e1c7f 0xf7e3fff8ffe3c38f

def z193 : W := mkw 0x27dffbf762120000 0x04fbff7eec424000 0xffffffffff1e0007 0xffffffffffe3c000

def z194 : W := mkw 0x09004e5fc9049af1 0xc12009cbf920935e 0x20000fffe0001ffa 0x040001fffc0003ff

def z195 : W := mkw 0x07f7aa0257db4810 0x80fef5404afb6902 0xdffff3007fffec1d 0xfbfffe600ffffd83

def z196 : W := mkw 0x01000e0089041841 0x002001c011208308 0xbf060f079f1c1c67 0x77e0c1e0f3e3838c

def z197 : W := mkw 0x0862c05d108982a0 0x410c580ba2113054 0xc8e0c0fc008193e7 0x991c181f8010327c

def z198 : W := mkw 0x004ad1d520000000 0x00095a3aa4000000 0xe0ffffffe0000003 0xfc1ffffffc000000

def z199 : W := mkw 0x37ffffff7de01f06 0x06ffffffefbc03e0 0xf7ffffffffe01f87 0xfefffffffffc03f0

def z200 : W := mkw 0x030d1f82eb363d5d 0xa061a3f05d66c7ab 0xbf1f3f07ff7e7c7f 0x77e3e7e0ffefcf8f

def z201 : W := mkw 0x1cfac5fd9ced97e7 0x439f58bfb39db2fc 0xe8feccff98fd93e7 0xbd1fd99ff31fb27c

def z202 : W := mkw 0x17bd0fa81ff21f06 0x02f7a1f503fe43e0 0xffff0ff81ffe1f87 0xffffe1ff03ffc3f0

def z203 : W := mkw 0x000811802020a5ac 0x20010230040414b5 0x1819330060e3fffc 0x430326600c1c7fff

def z204 : W := mkw 0x0020040818801200 0x0004008103100240 0x0000000018801384 0x0000000003100270

def z205 : W := mkw 0x00004044000080a0 0x0000080880001014 0x0000c0c000818380 0x8000181800103070

def z206 : W := mkw 0x21000a3340000000 0x0420014668000000 0x20000c3b80000000 0x0400018770000000

def z207 : W := mkw 0x00004044000080a0 0x0000080880001014 0x9819f0c400e3f3e7 0xd3033e18801c7e7c

def z208 : W := mkw 0x27dffbf76020a5ac 0x24fbff7eec0414b5 0xe7ffffffe0001ffb 0xfcfffffffc0003ff

def z209 : W := mkw 0x03050e02c9041851 0x8060a1c05920830a 0xa7070f07e0001c7b 0x74e0e1e0fc00038f

def z210 : W := mkw 0x37ffffff7de0bfae 0x26ffffffefbc17f5 0xffffffffffe3ffff 0xfffffffffffc7fff

def z211 : W := mkw 0x08000408880492e1 0x410000811100925c 0x00000000000013e0 0x000000000000027c

def z212 : W := mkw 0x00000000021b4000 0x0000000000436800 0x08000000001fe000 0x010000000003fc00

def z213 : W := mkw 0x000851c42020250c 0x20010a38840404a1 0x9019f3c460626c1b 0xd2033e788c0c4d83

def z214 : W := mkw 0x07f7ae001fdb5800 0x00fef5c003fb6b00 0xffffff001ffffc07 0xffffffe003ffff80

def z215 : W := mkw 0x0042800000000000 0x0008500000000000 0xc0e6c00000000001 0xb81cd80000000000

def z216 : W := mkw 0x15b00e281dc01a02 0x02b601c503b80340 0xf7e00f381f001c06 0x7efc01e703e00380

def z217 : W := mkw 0x0000040088041041 0x0000008011008208 0xb8070f07f81e1c7f 0x7700e1e0ff03c38f

def z218 : W := mkw 0x03050e02cb161851 0x8060a1c05962c30a 0x2f070c07ff1e0079 0x25e0e180ffe3c00f

def z219 : W := mkw 0x37fffffffff61f57 0x86fffffffffec3ea 0xfffffffffffe1fff 0xffffffffffffc3ff

def z220 : W := mkw 0x27dffbf7600080a0 0x04fbff7eec001014 0xefffffffe08193e7 0xfdfffffffc10327c

def z221 : W := mkw 0x020d51c6e236a5fd 0xa041aa38dc46d4bf 0x981ff3c7e0ffffff 0xd303fe78fc1fffff

def z222 : W := mkw 0x06f7a00014c94000 0x00def40002992800 0xc7fff00000e1e001 0xf8fffe00001c3c00

def z223 : W := mkw 0x0a67e45d9a9fd2e1 0x414cfc8bb353fa5c 0xe8e7fcff989ff3e7 0xbd1cff9ff313fe7c

def z224 : W := mkw 0x0247a000021b4000 0x0048f40000436800 0x981ff00000ffe005 0xd303fe00001ffc00

def z225 : W := mkw 0x000811802020250c 0x20010230040404a1 0x9819f30060e3ec1d 0xd3033e600c1c7d83

def z226 : W := mkw 0x06d7a00000000000 0x00daf40000000000 0xc7fff00000000001 0xf8fffe0000000000

def z227 : W := mkw 0x06b5200016d24000 0x00d6a40002da4800 0xd7f930001fe26004 0xfaff260003fc4c00

def z228 : W := mkw 0x0020000016db4000 0x0004000002db6800 0x000000001f1c0000 0x0000000003e38000

def z229 : W := mkw 0x0862c45d988d92e1 0x410c588bb311b25c 0x68e6cc3f981d8061 0x2d1cd987f303b00c

def z230 : W := mkw 0x24daf1f52020a5ac 0x249b5e3ea40414b5 0xd8f9f3fc60e3ffff 0xdb1f3e7f8c1c7fff

def z231 : W := mkw 0x27dffbf766524000 0x04fbff7eecca4800 0xf7ffffffe7626003 0xfefffffffcec4c00

def z232 : W := mkw 0x080855dda824b7ed 0x61010abbb50496fd 0x20000fffe0001ffa 0x040001fffc0003ff

def z233 : W := mkw 0x17b50e2adfd61a53 0x82f6a1c55bfac34a 0x67e60c3b9f1c0000 0x2cfcc18773e38000

def z234 : W := mkw 0x0062800016db4000 0x000c500002db6800 0xd8e6c0001fffe005 0xbb1cd80003fffc00

def z235 : W := mkw 0x25985bf760000000 0x04b30b7eec000000 0xe7f80fffe0000002 0xfcff01fffc000000

def z236 : W := mkw 0x03050a02c3160851 0x8060a1405862c10a 0x1f070307e71e0c79 0x43e0e060fce3c18f

def z237 : W := mkw 0x0205000000000000 0x0040a00000000000 0x8707000000000001 0x70e0e00000000000

def z238 : W := mkw 0x15b80fa89de41f47 0x02b701f513bc83e8 0xfffe0fff9ffc1fe7 0xffffc1fff3ff83fc

def z239 : W := mkw 0x07ffffc6fffffdfd 0xa0fffff8dfffffbf 0xffffffc7ffffffff 0xfffffff8ffffffff

def z240 : W := mkw 0x1df2ce7d9dcd9ae3 0x43be59cfb3b9b35c 0xefe6ccff9f9d93e7 0xbdfcd99ff3f3b27c

def z241 : W := mkw 0x0862c45d988d92e1 0x410c588bb311b25c 0x60e60cff981c13e2 0x2c1cc19ff303827c

def z242 : W := mkw 0x230d5ff7eb161851 0x8461abfefd62c30a 0xbf070fffff1e1c7f 0x77e0e1ffffe3c38f

def z243 : W := mkw 0x0000000000000000 0x0000000000000000 0x0018f00000e1e000 0x80031e00001c3c00

def z244 : W := mkw 0x03050a0243120810 0x8060a14048624102 0x1701030067020c18 0x42e020600ce04183

def z245 : W := mkw 0x000855c4ab36bdfd 0xa0010ab89566d7bf 0x9819f3c47fffffff 0xd3033e788fffffff

def z246 : W := mkw 0x0000000006524000 0x0000000000ca4800 0x1000000007626000 0x0200000000ec4c00

def z247 : W := mkw 0x05980ba000000000 0x00b3017400000000 0x0718030000000000 0x40e3006000000000

def z248 : W := mkw 0x27952a2240000000 0x04f2a54448000000 0x0700000000000000 0x00e0000000000000

def z249 : W := mkw 0x0000040088041041 0x0000008011008208 0x20060c03981c0000 0x2400c18073038000

def z250 : W := mkw 0x000000000020a5ac 0x20000000000414b5 0x9801030460e3ffff 0x530020608c1c7fff

def z251 : W := mkw 0x04b0000016db4000 0x0096000002db6800 0xdff800001fffe004 0xfbff000003fffc00

def z252 : W := mkw 0x06f7a00016db4000 0x00def40002db6800 0xd7fe00001ffc0004 0xfaffc00003ff8000

def z253 : W := mkw 0x04f2a00014c94000 0x009e540002992800 0xc8fef00018fde005 0xb91fde00031fbc00

def z254 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z255 : W := mkw 0x15900a2005400802 0x02b2014400a80100 0x0700000007000000 0x00e0000000e00000

def z256 : W := mkw 0x06f7a00016db4000 0x00def40002db6800 0x57f9f00007e3e000 0xcaff3e0000fc7c00

def z257 : W := mkw 0x102855cc3de0bfae 0x22050ab987bc17f5 0x9819f3c47fe3ffff 0xd3033e788ffc7fff

def z258 : W := mkw 0x03050e02cb161851 0x8060a1c05962c30a 0xbf1fff07fffffc7f 0xf7e3ffe0ffffff8f

def z259 : W := mkw 0x16ffa1a816fb4706 0x02dff43502df68e0 0xdffff0f81fffe385 0xfbfffe1f03fffc70

def z260 : W := mkw 0x03050a0242120000 0x0060a14048424000 0xbf070f07ff1e0007 0x77e0e1e0ffe3c000

def z261 : W := mkw 0x000050442000a0a8 0x20000a0884001415 0x0000000460000078 0x000000008c00000f

def z262 : W := mkw 0x27dffbf7621b4000 0x04fbff7eec436800 0xefffffffe01fe003 0xfdfffffffc03fc00

def z263 : W := mkw 0x2cfaf1fd308982a0 0x459f5e3fa6113054 0x40f8f0f800818380 0x881f1e1f00103070

def z264 : W := mkw 0x08628419988d92e1 0x410c50833311b25c 0x68e60c3b989d93e4 0x2d1cc1877313b27c

def z265 : W := mkw 0x049801a000000000 0x0093003400000000 0x40f800f800000000 0x881f001f00000000

def z266 : W := mkw 0x082855ccb8adb7ed 0x61050ab99715b6fd 0x9819f3c478ffffff 0xd3033e788f1fffff

def z267 : W := mkw 0x27dffff7eb36bdfd 0xa4fbfffefd66d7bf 0xffffffffffffffff 0xffffffffffffffff

def z268 : W := mkw 0x2ffffffff8adb7ed 0x65ffffffff15b6fd 0xfffffffff8ffffff 0xffffffffff1fffff

def z269 : W := mkw 0x01000e0009001800 0x002001c001200300 0xbf010f047f021c7f 0x77e021e08fe0438f

def z270 : W := mkw 0x0008018000200504 0x00010030000400a0 0x000003c000001f82 0x00000078000003f0

def z271 : W := mkw 0x01000a0240000000 0x0020014048000000 0x20000f07e0000002 0x040001e0fc000000

def z272 : W := mkw 0x0205000240000000 0x0040a00048000000 0x00070007e0000001 0x0000e000fc000000

def z273 : W := mkw 0x14faa1a814e94706 0x029f5435029d28e0 0x40f8f0f800e1e380 0x881f1e1f001c3c70

def z274 : W := mkw 0x000851c420200504 0x00010a38840400a0 0x9019f3c460e01f87 0xd2033e788c1c03f0

def z275 : W := mkw 0x27d7aa3340000000 0x04faf54668000000 0xe7e70f3fe0000003 0x7cfce1e7fc000000

def z276 : W := mkw 0x17b50e2adfd61a53 0x82f6a1c55bfac34a 0xffe70f3fff1e1c7f 0x7ffce1e7ffe3c38f

def z277 : W := mkw 0x102004081ffb5f06 0x0204008103ff6be0 0x180000001fffff84 0x0300000003fffff0

def z278 : W := mkw 0x17ffaba017fb4d06 0x02fff57402ff69a0 0xdffff3001fffec05 0xfbfffe6003fffd80

def z279 : W := mkw 0x01000e0009001800 0x002001c001200300 0x27000c001f000000 0x24e0018003e00000

def z280 : W := mkw 0x0247f044221be0a8 0x2048fe0884437c15 0x0807f004601fe079 0x0100fe008c03fc0f

def z281 : W := mkw 0x15980ba005600d06 0x02b3017400ac01a0 0x971803c007e01f86 0xd2e3007800fc03f0

def z282 : W := mkw 0x27d7ae33cb161851 0x84faf5c67962c30a 0x67e60c3b9f1c0000 0x2cfcc18773e38000

def z283 : W := mkw 0x086ad1dd30a9a7ac 0x610d5a3ba61534f5 0x40f8f0f800e1e380 0x881f1e1f001c3c70

def z284 : W := mkw 0x06f7f04436dbe0a8 0x20defe0886db7c15 0xdffff0047fffe07d 0xfbfffe008ffffc0f

def z285 : W := mkw 0x0000000080040041 0x0000000010008008 0x08060007801c0061 0x0100c000f003800c

def z286 : W := mkw 0x000851c420000000 0x00010a3884000000 0x9819f3c460021c7f 0xd3033e788c00438f

def z287 : W := mkw 0x000040440020a5ac 0x20000808800414b5 0x9800c0c400e3ffff 0x93001818801c7fff

def z288 : W := mkw 0x0000000000000000 0x0000000000000000 0x0801f0000003e001 0x01003e0000007c00

def z289 : W := mkw 0x0000040088041041 0x0000008011008208 0x20000c0780001062 0x04000180f000020c

def z290 : W := mkw 0x0490000000000000 0x0092000000000000 0xc7f8000000000000 0xf8ff000000000000

def z291 : W := mkw 0x000004008b161851 0x800000801162c30a 0x000000001f1c0000 0x0000000003e38000

def z292 : W := mkw 0x27f7aa3356db4000 0x04fef5466adb6800 0xfffffc3b9fffe005 0xffffff8773fffc00

def z293 : W := mkw 0x0205000002120000 0x0040a00000424000 0x1701000007020000 0x42e0200000e04000

def z294 : W := mkw 0x11000e2809001a02 0x022001c501200340 0x20000c3800000000 0x0400018700000000

def z295 : W := mkw 0x2ffffffffb9f9af1 0xc5ffffffff73f35e 0xffffffffff9f9fff 0xfffffffffff3f3ff

def z296 : W := mkw 0x01200e0819801a00 0x002401c103300340 0xf7e00ff81f801f86 0xfefc01ff03f003f0

def z297 : W := mkw 0x01000a0001000800 0x0020014000200100 0x1700030007000c00 0x42e0006000e00180

def z298 : W := mkw 0x37fffbff74e00706 0x06ffff7fee9c00e0 0xe7ffffffe0e00383 0xfcfffffffc1c0070

def z299 : W := mkw 0x030d5bc660000000 0x0061ab78cc000000 0xa71fffc7e0000003 0xf4e3fff8fc000000

def z300 : W := mkw 0x17bd0faadff61f57 0x82f7a1f55bfec3ea 0xf7fe0ffb9ffc1f86 0xfeffc1ff73ff83f0

def z301 : W := mkw 0x06f7e04416dbc0a0 0x00defc0882db7814 0xdffff0c41ffff3e7 0xfbfffe1883fffe7c

def z302 : W := mkw 0x04f2a00016db4000 0x009e540002db6800 0x58f8f0001fffe004 0x8b1f1e0003fffc00

def z303 : W := mkw 0x03050e02cb161851 0x8060a1c05962c30a 0x28070f07e01e1c7b 0x0500e1e0fc03c38f

def z304 : W := mkw 0x0b47ce57cb1f98f1 0xc168f9caf963f31e 0xbf07cf07ff1f9c7f 0x77e0f9e0ffe3f38f

def z305 : W := mkw 0x05985be42020a5ac 0x20b30b7c840414b5 0xfff9fffc60e3ffff 0xffff3fff8c1c7fff

def z306 : W := mkw 0x03050e02cb161851 0x8060a1c05962c30a 0xbf070c039f1e0005 0x77e0e18073e3c000

def z307 : W := mkw 0x11085fec2920bfae 0x22210bfd852417f5 0x20000ffc60001ffa 0x040001ff8c0003ff

def z308 : W := mkw 0x0862c45d988d1241 0x410c588bb311a248 0xe0e6ccff981c0003 0xbc1cd99ff3038000

def z309 : W := mkw 0x0862c05d108982a0 0x410c580ba2113054 0xe0e6ccff80818383 0xbc1cd99ff0103070

def z310 : W := mkw 0x07b50e02dfd61851 0x80f6a1c05bfac30a 0xffff0f07fffe1c7f 0xffffe1e0ffffc38f

def z311 : W := mkw 0x27d7aa3340000000 0x04faf54668000000 0xe7fffc3b80000001 0xfcffff8770000000

def z312 : W := mkw 0x01000e02c9041851 0x802001c05920830a 0xb8010f07e0021c7f 0x570021e0fc00438f

def z313 : W := mkw 0x37ffafbb5de01f06 0x06fff5f76bbc03e0 0xf7fe0ffb9fe01f86 0xfeffc1ff73fc03f0

def z314 : W := mkw 0x0800405d000082a0 0x4100080ba0001054 0x000000f800000380 0x0000001f00000070

def z315 : W := mkw 0x000851c42020a5ac 0x20010a38840414b5 0x1819f3046063ec79 0x43033e608c0c7d8f

def z316 : W := mkw 0x15b80fa81de01f06 0x02b701f503bc03e0 0x171803001fe01f84 0x42e3006003fc03f0

def z317 : W := mkw 0x06f7a00016db4000 0x00def40002db6800 0xc7fff0001f1c0001 0xf8fffe0003e38000

def z318 : W := mkw 0x0008018000200504 0x00010030000400a0 0x9819f3c000e3ff87 0xd3033e78001c7ff0

def z319 : W := mkw 0x11080fa809201f06 0x022101f5012403e0 0xb0180ff800e01f86 0xd60301ff001c03f0

def z320 : W := mkw 0x17f7ae281fdb5a02 0x02fef5c503fb6b40 0x67e60c381f1c0000 0x2cfcc18703e38000

def z321 : W := mkw 0x01000e02c9041851 0x802001c05920830a 0x20000c0380000000 0x0400018070000000

def z322 : W := mkw 0x27d7ea7740000000 0x04fafd4ee8000000 0xe7e6ccff80000003 0xbcfcd99ff0000000

def z323 : W := mkw 0x21085bf76020a5ac 0x24210b7eec0414b5 0x20000fffe0001ffa 0x040001fffc0003ff

def z324 : W := mkw 0x15980fa00d601d06 0x02b301f401ac03a0 0xb7180f001f601c06 0x76e301e003ec0380

def z325 : W := mkw 0x182004089ded9fe7 0x4304008113bdb3fc 0x180000001ffd9fe4 0x0300000003ffb3fc

def z326 : W := mkw 0x03050e02cb161851 0x8060a1c05962c30a 0x3f060c039f1e1c7c 0x27e0c18073e3c38f

def z327 : W := mkw 0x27d7ae33cb161851 0x84faf5c67962c30a 0xffe70f3fff1e1c7f 0x7ffce1e7ffe3c38f

def z328 : W := mkw 0x0000000000000000 0x0000000000000000 0x88060000181c0005 0x3100c00003038000

def z329 : W := mkw 0x0205000002120000 0x0040a00000424000 0x08070000001e0001 0x0100e0000003c000

def z330 : W := mkw 0x214adbf760000000 0x04295b7eec000000 0xe0e6cfffe0000003 0xbc1cd9fffc000000

def z331 : W := mkw 0x17ffafa81de01f06 0x02fff5f503bc03e0 0xf7fffff81fe01f87 0xfeffffff03fc03f0

def z332 : W := mkw 0x0695200006524000 0x00d2a40000ca4800 0x9f19f00007e3e005 0xd3e33e0000fc7c00

def z333 : W := mkw 0x04b0000014c00000 0x0096000002980000 0xdff9f0001fe3e005 0xfbff3e0003fc7c00

def z334 : W := mkw 0x04d2a00000000000 0x009a540000000000 0x40f8f00000000000 0x881f1e0000000000

def z335 : W := mkw 0x0000040008001000 0x0000008001000200 0xa0000c0018001006 0x3400018003000200

def z336 : W := mkw 0x084ad1d5a02da5ed 0x61095a3ab405b4bd 0x981ff3c7e0ffffff 0xd303fe78fc1fffff

def z337 : W := mkw 0x07f7ae02dfdf5851 0x80fef5c05bfbeb0a 0x67e60c039f1c0000 0x2cfcc18073e38000

def z338 : W := mkw 0x08628408988d92e1 0x410c50811311b25c 0xc8e6c000189d93e5 0xb91cd8000313b27c

def z339 : W := mkw 0x06f7a00014c00000 0x00def40002980000 0xd7fff0001fe00005 0xfafffe0003fc0000

def z340 : W := mkw 0x0842c055000980a0 0x4108580aa0013014 0x0000c00000018000 0x0000180000003000

def z341 : W := mkw 0x2347fa5760000000 0x0468ff4aec000000 0xa707ff07e0000003 0x74e0ffe0fc000000

def z342 : W := mkw 0x27dffbf760000000 0x04fbff7eec000000 0x67fefcfb80000000 0xacffdf9f70000000

def z343 : W := mkw 0x06f7a00016fbe5ac 0x20def40002df7cb5 0xdffff0001ffffffd 0xfbfffe0003ffffff

def z344 : W := mkw 0x000851c420000000 0x00010a3884000000 0x9819f3c460e3e007 0xd3033e788c1c7c00

def z345 : W := mkw 0x000851c42020a5ac 0x20010a38840414b5 0x8019f3c460001ffb 0xd0033e788c0003ff

def z346 : W := mkw 0x0842c45d880492e1 0x4108588bb100925c 0xe0e6ccff800013e3 0xbc1cd99ff000027c

def z347 : W := mkw 0x06b5200016db4000 0x00d6a40002db6800 0x1f1930001fffe004 0x43e3260003fffc00

def z348 : W := mkw 0x0020000010890000 0x0004000002112000 0x08000000189d8004 0x010000000313b000

def z349 : W := mkw 0x24daf1f520000000 0x049b5e3ea4000000 0xc0f9f3fc60000003 0xd81f3e7f8c000000

def z350 : W := mkw 0x0062c05510890000 0x000c580aa2112000 0xe8e6ccff989d8007 0xbd1cd99ff313b000

def z351 : W := mkw 0x2347fe57eb161851 0x8468ffcafd62c30a 0xbf07ff07ff1e1c7f 0x77e0ffe0ffe3c38f

def z352 : W := mkw 0x0000000000000000 0x0000000000000000 0x8001030460000003 0x500020608c000000

def z353 : W := mkw 0x102805881de01f06 0x020500b103bc03e0 0x901803c01fe01f86 0xd203007803fc03f0

def z354 : W := mkw 0x082004089edfd2e1 0x4104008113dbfa5c 0x180000001ffff3e4 0x0300000003fffe7c

def z355 : W := mkw 0x14b004081de01f06 0x0296008103bc03e0 0xd7f800001fe01f84 0xfaff000003fc03f0

def z356 : W := mkw 0x000855c4a824b5ed 0x20010ab8950496bd 0xb81fffc7f8ffffff 0xf703fff8ff1fffff

def z357 : W := mkw 0x0020040898841241 0x0004008113108248 0xe8e60cff989c13e7 0xbd1cc19ff313827c

def z358 : W := mkw 0x17bd2fa81ff25f06 0x02f7a5f503fe4be0 0xf7f93ff81fe27f86 0xfeff27ff03fc4ff0

def z359 : W := mkw 0x27dffbf76020a5ac 0x24fbff7eec0414b5 0xe7ffffffe0e1e383 0xfcfffffffc1c3c70

def z360 : W := mkw 0x00004044000080a0 0x0000080880001014 0x9801c3c460839fff 0xd30038788c1073ff

def z361 : W := mkw 0x0008018000200504 0x00010030000400a0 0x981903c460e21fff 0xd30320788c1c43ff

def z362 : W := mkw 0x03050e000b121800 0x0060a1c001624300 0xbf070f001f1e1c07 0x77e0e1e003e3c380

def z363 : W := mkw 0x0000000000000000 0x0000000000000000 0x9000030000001c06 0x5200006000000380

def z364 : W := mkw 0x27dffbf76000a0a8 0x24fbff7eec001415 0xefffffffe003e07b 0xfdfffffffc007c0f

def z365 : W := mkw 0x100801a800200706 0x02010035000400e0 0x000000f800000380 0x0000001f00000070

def z366 : W := mkw 0x0000000000000000 0x0000000000000000 0x8800000400001067 0x110000008000020c

def z367 : W := mkw 0x07952e02cf565851 0x80f2a5c059eacb0a 0xbf1f3f07ff7e7c7f 0x77e3e7e0ffefcf8f

def z368 : W := mkw 0x03050a02c2160051 0x8060a1405842c00a 0xaf070f07e01e007b 0x75e0e1e0fc03c00f

def z369 : W := mkw 0x006ad1c430a9a5ac 0x200d5a38861534b5 0xd8fff3c478ffffff 0xfb1ffe788f1fffff

def z370 : W := mkw 0x0820445d988d92e1 0x4104088bb311b25c 0x28000cff989d93e6 0x0500019ff313b27c

def z371 : W := mkw 0x0000000000000000 0x0000000000000000 0x1019300000626000 0x42032600000c4c00

def z372 : W := mkw 0x01000e0009001800 0x002001c001200300 0x20000f0000001c02 0x040001e000000380

def z373 : W := mkw 0x030d5bc66332adbc 0xa061ab78cc6655b7 0x9f19f3c467e3ffff 0xd3e33e788cfc7fff

def z374 : W := mkw 0x04f2800014c90000 0x009e500002992000 0xdffec0001ffd8005 0xfbffd80003ffb000

def z375 : W := mkw 0x27fffbf776db4000 0x04ffff7eeedb6800 0xe7ffffffff1c0003 0xfcffffffffe38000

def z376 : W := mkw 0x279d7be660000000 0x04f3af7ccc000000 0x8719f3c460000003 0xd0e33e788c000000

def z377 : W := mkw 0x27dffbf760000000 0x04fbff7eec000000 0x47f9f3f860000000 0xc8ff3e7f0c000000

def z378 : W := mkw 0x14b805a81de01f06 0x029700b503bc03e0 0x50f800f81fe01f84 0x8a1f001f03fc03f0

def z379 : W := mkw 0x03050e02c8041041 0x0060a1c059008208 0xaf070f07f81c1067 0x75e0e1e0ff03820c

def z380 : W := mkw 0x0cf2e45d9ccdd2e1 0x419e5c8bb399ba5c 0xe8fefcff98fdf3e7 0xbd1fdf9ff31fbe7c

def z381 : W := mkw 0x102004081de0bfae 0x2204008103bc17f5 0x180000001fe3fffc 0x0300000003fc7fff

def z382 : W := mkw 0x01085fc6e924bdfd 0xa0210bf8dd2497bf 0xb819ffc7e0e3ffff 0xd7033ff8fc1c7fff

def z383 : W := mkw 0x0b054e5fcb169af1 0xc160a9cbf962d35e 0xbf070fffff1e1fff 0x77e0e1ffffe3c3ff

def z384 : W := mkw 0x0000040088041041 0x0000008011008208 0x08000000181c1064 0x010000000303820c

def z385 : W := mkw 0x00000000000080a0 0x0000000000001014 0x08000000008193e4 0x010000000010327c

def z386 : W := mkw 0x2ffffbff708982a0 0x45ffff7fee113054 0xe7ffffffe0818383 0xfcfffffffc103070

def z387 : W := mkw 0x15b80ba814e00706 0x02b70175029c00e0 0xe7f80ff800e00382 0xfcff01ff001c0070

def z388 : W := mkw 0x21085bf760000000 0x04210b7eec000000 0xa019ffffe0000003 0xd4033ffffc000000

def z389 : W := mkw 0x17ffafa81ffb5f06 0x02fff5f503ff6be0 0xf7fe0ff81ffc1f86 0xfeffc1ff03ff83f0

def z390 : W := mkw 0x0267a000129b4000 0x004cf40002536800 0xc8e7f000189fe005 0xb91cfe000313fc00

def z391 : W := mkw 0x08000000800d80e1 0x410000001001b01c 0x08000000001d8060 0x010000000003b00c

def z392 : W := mkw 0x06d7a000021b4000 0x00daf40000436800 0xcffff000001fe001 0xf9fffe000003fc00

def z393 : W := mkw 0x0008018000200504 0x00010030000400a0 0x001800c000e00380 0x80030018001c0070

def z394 : W := mkw 0x15b00e281de01f06 0x02b601c503bc03e0 0x77e00c381fe01f84 0x2efc018703fc03f0

def z395 : W := mkw 0x37dfffff69201f06 0x06fbffffed2403e0 0xe7ffffffe0001f83 0xfcfffffffc0003f0

def z396 : W := mkw 0x0000000000000000 0x0000000000000000 0x8800c00000818005 0x9100180000103000

def z397 : W := mkw 0x15b81fa83de03f0e 0x22b703f507bc07e1 0xf7f93ff87fe27f9e 0xfeff27ff0ffc4ff3

def z398 : W := mkw 0x0000000000000000 0x0000000000000000 0x9819f30460e3fc7f 0xd3033e608c1c7f8f

def z399 : W := mkw 0x17bd0faa5de01f06 0x02f7a1f54bbc03e0 0xf7ff0fffffe01f87 0xfeffe1fffffc03f0

def z400 : W := mkw 0x000851c42020a5ac 0x20010a38840414b5 0x8019f3c460e1e383 0xd0033e788c1c3c70

def z401 : W := mkw 0x0042801100000000 0x0008500220000000 0x60e60c3b80000000 0x2c1cc18770000000

def z402 : W := mkw 0x0490200004404000 0x0092040000880800 0x0018300000606000 0x00030600000c0c00

def z403 : W := mkw 0x000851c42020a5ac 0x20010a38840414b5 0x180003c460e3fffe 0x030000788c1c7fff

def z404 : W := mkw 0x0000000000000000 0x0000000000000000 0xe0e00cf800000002 0xbc1c019f00000000

def z405 : W := mkw 0x0000040808001200 0x0000008101000240 0x20000cf800001382 0x0400019f00000270

def z406 : W := mkw 0x102004081de01f06 0x0204008103bc03e0 0xf0e00cf81fe01f86 0xbe1c019f03fc03f0

def z407 : W := mkw 0x000851c42000a0a8 0x20010a3884001415 0x8819f3c46003e07b 0xd1033e788c007c0f

def z408 : W := mkw 0x27dffbf760000000 0x04fbff7eec000000 0xffffffffe0021c7f 0xfffffffffc00438f

def z409 : W := mkw 0x086ac5dd98ad97e5 0x410d58bbb315b2fc 0xf8fecfff98fd9fe7 0xff1fd9fff31fb3fc

def z410 : W := mkw 0x04f2a00014c94000 0x009e540002992800 0xd8f9f00000e3e005 0xdb1f3e00001c7c00

def z411 : W := mkw 0x06d7a00000000000 0x00daf40000000000 0xdffff00000e3e005 0xfbfffe00001c7c00

def z412 : W := mkw 0x0b6fdfdffbbfbffd 0xe16dfbfbff77f7ff 0xffffffffffffffff 0xffffffffffffffff

def z413 : W := mkw 0x03050e02cb161851 0x8060a1c05962c30a 0xa7070f07ff1c0003 0x74e0e1e0ffe38000

def z414 : W := mkw 0x05980fa009001800 0x00b301f401200300 0xf7f80ff81f001c06 0xfeff01ff03e00380

def z415 : W := mkw 0x230d5bf760000000 0x0461ab7eec000000 0xa7070fffe0000003 0x74e0e1fffc000000

def z416 : W := mkw 0x01000a0000000000 0x0020014000000000 0xa7000f0000000002 0x74e001e000000000

def z417 : W := mkw 0x179d2ba007724d06 0x02f3a57400ee49a0 0x1719330007626c00 0x42e3266000ec4d80

def z418 : W := mkw 0x06f7a4081edb5200 0x00def48103db6a40 0xfffffcf81ffff387 0xffffff9f03fffe70

def z419 : W := mkw 0x000004008b161851 0x800000801162c30a 0xb8060c079f1e1c7f 0x3700c180f3e3c38f

def z420 : W := mkw 0x08428011800d0041 0x410850023001a008 0x00060003801c0000 0x0000c00070038000

def z421 : W := mkw 0x01080f8009201d04 0x002101f0012403a0 0xb7180fc01fe01f86 0xf6e301f803fc03f0

def z422 : W := mkw 0x024ff1c4223be5ac 0x2049fe3884477cb5 0x981ff3c460ffffff 0xd303fe788c1fffff

def z423 : W := mkw 0x0862c45d988d92e1 0x410c588bb311b25c 0xf8e7cffff89f9fff 0xff1cf9ffff13f3ff

def z424 : W := mkw 0x07f7ae02dfdf5851 0x80fef5c05bfbeb0a 0xffe70f07ff1e1c7f 0x7ffce1e0ffe3c38f

def z425 : W := mkw 0x0862c05d108982a0 0x410c580ba2113054 0xc8e6c0f8189d8385 0xb91cd81f0313b070

def z426 : W := mkw 0x11200e081de01f06 0x022401c103bc03e0 0xb7000f001fe01f86 0x76e001e003fc03f0

def z427 : W := mkw 0x0000504420000000 0x00000a0884000000 0x0001f00460000001 0x00003e008c000000

def z428 : W := mkw 0x0000000000000000 0x0000000000000000 0xa0060c0780000003 0x3400c180f0000000

def z429 : W := mkw 0x000811802020250c 0x20010230040404a1 0x901933c060e27f9e 0xd20326780c1c4ff3

def z430 : W := mkw 0x279d7be66020a5ac 0x24f3af7ccc0414b5 0x9f19f3c460e3ffff 0xd3e33e788c1c7fff

def z431 : W := mkw 0x03050e02cb161851 0x8060a1c05962c30a 0x27060f07ff1c1c7a 0x24e0c1e0ffe3838f

def z432 : W := mkw 0x0225000016db4000 0x0044a00002db6800 0x9f0700001fffe005 0x73e0e00003fffc00

def z433 : W := mkw 0x000050442000a0a8 0x20000a0884001415 0x8801f0c46083f3ff 0x91003e188c107e7f

def z434 : W := mkw 0x13250e0adff61f57 0x8264a1c15bfec3ea 0xbf070f07fffe1fff 0x77e0e1e0ffffc3ff

def z435 : W := mkw 0x03054e46cb1698f1 0x8060a9c8d962d31e 0xbf07cfc7ff9f9fff 0xf7e0f9f8fff3f3ff

def z436 : W := mkw 0x000000000020250c 0x20000000000404a1 0x1000000000626c18 0x02000000000c4d83

def z437 : W := mkw 0x05980ba000200504 0x00b30174000400a0 0xf7f80ff800e01f86 0xfeff01ff001c03f0

def z438 : W := mkw 0x0347ae02cb1f5851 0x8068f5c05963eb0a 0xbf07ff07ff1ffc7f 0x77e0ffe0ffe3ff8f

def z439 : W := mkw 0x0862c45d188992a0 0x410c588ba3113254 0xe0e0ccf818819386 0xbc1c199f03103270

def z440 : W := mkw 0x05b80fa818801200 0x00b701f503100240 0xe7f80ff818801386 0xfcff01ff03100270

def z441 : W := mkw 0x224ff1d760000000 0x0449fe3aec000000 0x801ff3c7e0000003 0xd003fe78fc000000

def z442 : W := mkw 0x2247f0576000a0a8 0x2448fe0aec001415 0x0807f007e003e079 0x0100fe00fc007c0f

def z443 : W := mkw 0x1dfacffd1de99fa6 0x43bf59ffa3bd33f4 0xf7f8cff81fe19f86 0xfeff19ff03fc33f0

def z444 : W := mkw 0x06d7e05500000000 0x00dafc0aa0000000 0xe7fffcff80000003 0xfcffff9ff0000000

def z445 : W := mkw 0x01000e02c9041851 0x802001c05920830a 0xb7000f07ff001c7e 0x76e001e0ffe0038f

def z446 : W := mkw 0x21085bf76020a5ac 0x24210b7eec0414b5 0xb819ffffe0e3ffff 0xd7033ffffc1c7fff

def z447 : W := mkw 0x0020040818801200 0x0004008103100240 0x60e00c3818000000 0x2c1c018703000000

def z448 : W := mkw 0x0020000014c94000 0x0004000002992800 0x0000000000e1e000 0x00000000001c3c00

def z449 : W := mkw 0x11280fa81de01f06 0x022501f503bc03e0 0x30000ff81fe01f86 0x060001ff03fc03f0

def z450 : W := mkw 0x279d3ba260000000 0x04f3a7744c000000 0xe7f93ff860000002 0xfcff27ff0c000000

def z451 : W := mkw 0x04b0000014c00000 0x0096000002980000 0x40f8000000e00000 0x881f0000001c0000

def z452 : W := mkw 0x27ffffff78801200 0x04ffffffef100240 0xe7fffffff8801387 0xfcffffffff100270

def z453 : W := mkw 0x0ef7a4199edf5241 0x41def48333dbea48 0xfffffc3b9fffe005 0xffffff8773fffc00

def z454 : W := mkw 0x0020000810800200 0x0004000102100040 0x40e000f800800380 0x881c001f00100070

def z455 : W := mkw 0x2fdffbf7e00d80e1 0x45fbff7efc01b01c 0xefffffffe01d8063 0xfdfffffffc03b00c

def z456 : W := mkw 0x086ad5ddb8adb7ed 0x610d5abbb715b6fd 0xe8e6cffff89d9fff 0xbd1cd9ffff13b3ff

def z457 : W := mkw 0x0a67c45d9a9f92e1 0x414cf88bb353f25c 0xffe7ccff9f9f93e7 0xfffcf99ff3f3f27c

def z458 : W := mkw 0x00628400988d1041 0x000c50801311a208 0xe8e6cc07989d9067 0xbd1cd980f313b20c

def z459 : W := mkw 0x15facffd1de01f06 0x02bf59ffa3bc03e0 0xf7fecfff9fe01f87 0xfeffd9fff3fc03f0

def z460 : W := mkw 0x04b004081cc01200 0x0096008103980240 0xf7f80cf81fe01386 0xfeff019f03fc0270

def z461 : W := mkw 0x296adffff88d92e1 0x452d5bffff11b25c 0xe8e6cffff89d93e7 0xbd1cd9ffff13b27c

def z462 : W := mkw 0x27fffbf770890000 0x04ffff7eee112000 0xeffffffff89d8007 0xfdffffffff13b000

def z463 : W := mkw 0x0efff5ddbefff7ed 0x61dffebbb7dffefd 0xffffffffffffffff 0xffffffffffffffff

def z464 : W := mkw 0x27fffbf776fbe5ac 0x24ffff7eeedf7cb5 0xffffffffffffffff 0xffffffffffffffff

def z465 : W := mkw 0x21085ff7e9041851 0x84210bfefd20830a 0x20000fffe0001c7a 0x040001fffc00038f

def z466 : W := mkw 0x002851c436fbe5ac 0x20050a3886df7cb5 0x9819f3c47fffffff 0xd3033e788fffffff

def z467 : W := mkw 0x0000000000000000 0x0000000000000000 0x9018000000e00004 0xd2030000001c0000

def z468 : W := mkw 0x03050e02cb161851 0x8060a1c05962c30a 0x1f0103007f1e1c7c 0x43e020600fe3c38f

def z469 : W := mkw 0x01085fc6e924bdfd 0xa0210bf8dd2497bf 0x20000fc7e0001ffa 0x040001f8fc0003ff

def z470 : W := mkw 0x03050a0240000000 0x0060a14048000000 0x0701030060000000 0x40e020600c000000

def z471 : W := mkw 0x08004055800480e1 0x4100080ab000901c 0x0000000780000060 0x00000000f000000c

def z472 : W := mkw 0x179d0fa2cf761d57 0x82f3a1f459eec3aa 0xbf1f0f07ff7e1c7f 0x77e3e1e0ffefc38f

def z473 : W := mkw 0x0347ce57cb161851 0x8068f9caf962c30a 0xffe7cfffff1e1c7f 0xfffcf9ffffe3c38f

def z474 : W := mkw 0x0020000014c00000 0x0004000002980000 0x100000001fe00004 0x0200000003fc0000

def z475 : W := mkw 0x15b80fa81de01f06 0x02b701f503bc03e0 0x67e00ff81f001f82 0x2cfc01ff03e003f0

def z476 : W := mkw 0x06dff1c420000000 0x00dbfe3884000000 0xc7fff3c460000003 0xf8fffe788c000000

def z477 : W := mkw 0x0862d45db88db2e9 0x610c5a8bb711b65d 0xe8e7fcfff89ff3ff 0xbd1cff9fff13fe7f

def z478 : W := mkw 0x0842c055800d80e1 0x4108580ab001b01c 0x8806c0c7809d93e7 0x9100d818f013b27c

def z479 : W := mkw 0x0042c45588041041 0x0008588ab1008208 0xe8e6ccff981c1067 0xbd1cd99ff303820c

def z480 : W := mkw 0x1000000005600d06 0x0200000000ac01a0 0x1000000007600c00 0x0200000000ec0180

def z481 : W := mkw 0x000851c420000000 0x00010a3884000000 0x000003c460000002 0x000000788c000000

def z482 : W := mkw 0x11080faac9241f57 0x822101f5592483ea 0x20000fffe0001ffa 0x040001fffc0003ff

def z483 : W := mkw 0x379d3ba265600d06 0x06f3a7744cac01a0 0x1719330067600c00 0x42e326600cec0180

def z484 : W := mkw 0x086ad5ddb8adb7ed 0x610d5abbb715b6fd 0xe8fefcff98fdf3e7 0xbd1fdf9ff31fbe7c

def z485 : W := mkw 0x04b0000014c00000 0x0096000002980000 0x47e000001f000000 0x28fc000003e00000

def z486 : W := mkw 0x030d5bc66020a5ac 0x2061ab78cc0414b5 0xbf1fffc7e0e3ffff 0xf7e3fff8fc1c7fff

def z487 : W := mkw 0x15b80ba015e00d06 0x02b7017402bc01a0 0xd7f803001fe00c04 0xfaff006003fc0180

def z488 : W := mkw 0x07dfaba000000000 0x00fbf57400000000 0xe7fffff800000003 0xfcffffff00000000

def z489 : W := mkw 0x2a47f057e00d80e1 0x4548fe0afc01b01c 0x0807f007e01d8061 0x0100fe00fc03b00c

def z490 : W := mkw 0x030d5fc6eb36bdfd 0xa061abf8dd66d7bf 0xbf070fc7ff1e1fff 0x77e0e1f8ffe3c3ff

def z491 : W := mkw 0x14b851ec34e0a7ae 0x22970a3d869c14f5 0xd8f9f3fc60e3ffff 0xdb1f3e7f8c1c7fff

def z492 : W := mkw 0x004ad1d52020a5ac 0x20095a3aa40414b5 0xf8ffffffe0e3ffff 0xff1ffffffc1c7fff

def z493 : W := mkw 0x17ffffec3ffbffae 0x22fffffd87ff7ff5 0xfffffffc7fffffff 0xffffffff8fffffff

def z494 : W := mkw 0x06f7a00016db4000 0x00def40002db6800 0x57ff30001f7e6000 0x6affe60003efcc00

def z495 : W := mkw 0x2247f057e2160051 0x8448fe0afc42c00a 0x0807f007e01e0079 0x0100fe00fc03c00f

def z496 : W := mkw 0x03678e02db9f1851 0x806cf1c05b73e30a 0xffe7cf07ff9f9c7f 0xfffcf9e0fff3f38f

def z497 : W := mkw 0x020504008b161851 0x8040a0801162c30a 0x9f0700001f1e1c7d 0x73e0e00003e3c38f

def z498 : W := mkw 0x27dffff7e9041851 0x84fbfffefd20830a 0xe7ffffffe0001c7b 0xfcfffffffc00038f

def z499 : W := mkw 0x06d7a00002120000 0x00daf40000424000 0xdffff0001f1e0005 0xfbfffe0003e3c000

def z500 : W := mkw 0x0490000004400000 0x0092000000880000 0x1718000007600000 0x42e3000000ec0000

def z501 : W := mkw 0x080855dda824b7ed 0x61010abbb50496fd 0xb819ffffe0e3ffff 0xd7033ffffc1c7fff

def z502 : W := mkw 0x0842d055a00da0e9 0x61085a0ab401b41d 0x0807f007e01fe079 0x0100fe00fc03fc0f

def z503 : W := mkw 0x07d7aa0240000000 0x00faf54048000000 0xe7ffff07e0000003 0xfcffffe0fc000000

def z504 : W := mkw 0x26dff1f760000000 0x04dbfe3eec000000 0x40fff0ffe0000001 0x881ffe1ffc000000

def z505 : W := mkw 0x000841c4002085a4 0x00010838800410b4 0x9818c3c400e19fe7 0xd3031878801c33fc

def z506 : W := mkw 0x030d0f82cb361d55 0x8061a1f05966c3aa 0xbf1f0fc7fffe1fff 0xf7e3e1f8ffffc3ff

def z507 : W := mkw 0x0000000000000000 0x0000000000000000 0x9801000000020005 0x5300200000004000

def z508 : W := mkw 0x0000000000000000 0x0000000000000000 0x1001030060020c18 0x420020600c004183

def z509 : W := mkw 0x0000000000000000 0x0000000000000000 0x0801000460020079 0x010020008c00400f

def z510 : W := mkw 0x06d7a00000000000 0x00daf40000000000 0x47e6000000000000 0x28fcc00000000000

def z511 : W := mkw 0x26fff1f536db4000 0x04dffe3ea6db6800 0xdffff0f81fffe005 0xfbfffe1f03fffc00

def z512 : W := mkw 0x0042800000090000 0x0008500000012000 0x0806c000001d8001 0x0100d8000003b000

def z513 : W := mkw 0x0062840818891200 0x000c508103112240 0xe8e6ccf8189d9387 0xbd1cd99f0313b270

def z514 : W := mkw 0x15b80fa81de0bfae 0x22b701f503bc17f5 0xfff80ff81fe3fffe 0xffff01ff03fc7fff

def z515 : W := mkw 0x01080ba000000000 0x0021017400000000 0x20000ff800000002 0x040001ff00000000

def z516 : W := mkw 0x224ff1d76020a5ac 0x2449fe3aec0414b5 0x981ff3c7e0e3ffff 0xd303fe78fc1c7fff

def z517 : W := mkw 0x086ad5ddb88d92e1 0x410d5abbb711b25c 0xe8fffffff89d93e7 0xfd1fffffff13b27c

def z518 : W := mkw 0x01085fc42920bdac 0x20210bf8852417b5 0xbf19ffc47fe3ffff 0xf7e33ff88ffc7fff

def z519 : W := mkw 0x069d31802672650c 0x20d3a63004ce4ca1 0x1719330067626c18 0x42e326600cec4d83

def z520 : W := mkw 0x03050e02cb161851 0x8060a1c05962c30a 0xb7060f039f1c1c06 0x76e0c1e073e38380

def z521 : W := mkw 0x000050442020a5ac 0x20000a08840414b5 0x1801f00460e3fffd 0x03003e008c1c7fff

def z522 : W := mkw 0x05b80ba014c00000 0x00b7017402980000 0xf7f80ff81fe00006 0xfeff01ff03fc0000

def z523 : W := mkw 0x27dffbf760000000 0x04fbff7eec000000 0x67e60fffe0000002 0x2cfcc1fffc000000

def z524 : W := mkw 0x0000040009001800 0x0000008001200300 0x100000001f001c04 0x0200000003e00380

def z525 : W := mkw 0x0042c05500000000 0x0008580aa0000000 0x0006c00780000001 0x0000d800f0000000

def z526 : W := mkw 0x0062c45d18801200 0x000c588ba3100240 0xe0e6ccff98801387 0xbc1cd99ff3100270

def z527 : W := mkw 0x06f7a00016db4000 0x00def40002db6800 0xcfe6c0001f9d8005 0xb9fcd80003f3b000

def z528 : W := mkw 0x27d7fa7760000000 0x04faff4eec000000 0x67e7fc3fe0000001 0x2cfcff87fc000000

def z529 : W := mkw 0x27dffff7e8041041 0x04fbfffefd008208 0xeffffffff81c1067 0xfdffffffff03820c

def z530 : W := mkw 0x01000e02cb161851 0x802001c05962c30a 0x38000f07ff1e1c7e 0x070001e0ffe3c38f

def z531 : W := mkw 0x02050402cb161851 0x8040a0805962c30a 0x18070007ff1e1c7d 0x0300e000ffe3c38f

def z532 : W := mkw 0x279d7bf760000000 0x04f3af7eec000000 0x27193fffe0000002 0x44e327fffc000000

def z533 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000030460001c7a 0x000000608c00038f

def z534 : W := mkw 0x24faf1f534c94000 0x049f5e3ea6992800 0x40f8f0f800e1e000 0x881f1e1f001c3c00

def z535 : W := mkw 0x0062c044108980a0 0x000c580882113014 0xc8e6c0c4189d93e7 0xb91cd8188313b27c

def z536 : W := mkw 0x000851c42020a5ac 0x20010a38840414b5 0x9819f0c000e3e385 0xd3033e18001c7c70

def z537 : W := mkw 0x02678000129b0000 0x004cf00002536000 0xdfe7c0001f9f8005 0xfbfcf80003f3f000

def z538 : W := mkw 0x06f7a00016db4000 0x00def40002db6800 0x48fff00000ffe001 0x891ffe00001ffc00

def z539 : W := mkw 0x06f7a00010890000 0x00def40002112000 0xcffff000189d8005 0xf9fffe000313b000

def z540 : W := mkw 0x06f7a002d6df4051 0x80def4005adbe80a 0xdffff007ffffe07d 0xfbfffe00fffffc0f

def z541 : W := mkw 0x03050e02cb161851 0x8060a1c05962c30a 0xaf060c079f1c1067 0x35e0c180f3e3820c

def z542 : W := mkw 0x31085fff69201f06 0x06210bffed2403e0 0x20000fffe0001f82 0x040001fffc0003f0

def z543 : W := mkw 0x04f2a00014c94000 0x009e540002992800 0x40e0000000000000 0x081c000000000000

def z544 : W := mkw 0x0062800010890000 0x000c500002112000 0x40e0c00000818000 0x881c180000103000

def z545 : W := mkw 0x0695200006524000 0x00d2a40000ca4800 0x9f1f30001f7e6005 0x73e3e60003efcc00

def z546 : W := mkw 0x15b80fa89ff61f57 0x82b701f513fec3ea 0xfff80ff81ffe1ffe 0xffff01ff03ffc3ff

def z547 : W := mkw 0x102004081dc01a02 0x0204008103b80340 0x000000001f000000 0x0000000003e00000

def z548 : W := mkw 0x279d3ba263120810 0x84f3a7744c624102 0x1719330067020c18 0x42e326600ce04183

def z549 : W := mkw 0x37f7ae3b5dc01a02 0x06fef5c76bb80340 0x67e60c3b9f000000 0x2cfcc18773e00000

def z550 : W := mkw 0x0862c45d988d92e1 0x410c588bb311b25c 0x0806c007989d93e5 0x0100d800f313b27c

def z551 : W := mkw 0x0000000000000000 0x0000000000000000 0x970000001f000004 0x72e0000003e00000

def z552 : W := mkw 0x0820445d988492e1 0x4104088bb310925c 0xe0e00cff988013e6 0xbc1c019ff310027c

def z553 : W := mkw 0x17ffafaadfff5f57 0x82fff5f55bffebea 0xffffffffffffffff 0xffffffffffffffff

def z554 : W := mkw 0x0205000242120010 0x8040a00048424002 0x0001000060020018 0x000020000c004003

def z555 : W := mkw 0x0862c45d98adb7ed 0x610c588bb315b6fd 0xf8e6ccff98ffffff 0xbf1cd99ff31fffff

def z556 : W := mkw 0x06f7a4009edf5041 0x00def48013dbea08 0xfffffc079ffff067 0xffffff80f3fffe0c

def z557 : W := mkw 0x000851c42020a5ac 0x20010a38840414b5 0x9018f3c000e1ff86 0xd2031e78001c3ff0

def z558 : W := mkw 0x000851c42020a5ac 0x20010a38840414b5 0x0018f3c460e1fffa 0x80031e788c1c3fff

def z559 : W := mkw 0x249831a020000000 0x0493063404000000 0x0018300000000000 0x0003060000000000

def z560 : W := mkw 0x000851c42020a5ac 0x20010a38840414b5 0x8818f0c400e1f3e7 0x91031e18801c3e7c

def z561 : W := mkw 0x06f7a00016db4000 0x00def40002db6800 0x4fe7f0001f1fe001 0x29fcfe0003e3fc00

def z562 : W := mkw 0x069d71c42672e5ac 0x20d3ae3884ce5cb5 0x9f19f3c467e3ffff 0xd3e33e788cfc7fff

def z563 : W := mkw 0x04b851c434e0a5ac 0x20970a38869c14b5 0xdff9f3c47fe3ffff 0xfbff3e788ffc7fff

def z564 : W := mkw 0x02055046e216a0f9 0xa040aa08dc42d41f 0x0807f007e01fe079 0x0100fe00fc03fc0f

def z565 : W := mkw 0x0800041988041241 0x4100008331008248 0x20000c3b80000000 0x0400018770000000

def z566 : W := mkw 0x0028058818a01704 0x000500b1031402e0 0xf0f80ff818e01f86 0xfe1f01ff031c03f0

def z567 : W := mkw 0x0000100020002008 0x2000020004000401 0x0001300060026018 0x000026000c004c03

def z568 : W := mkw 0x02050002c2160051 0x8040a0005842c00a 0x9f070007ff1e007d 0x73e0e000ffe3c00f

def z569 : W := mkw 0x0862c055908d80e1 0x410c580ab211b01c 0xc8e6c007989d8065 0xb91cd800f313b00c

def z570 : W := mkw 0x17bd5feefff6bfff 0xa2f7abfddffed7ff 0xffffffffffffffff 0xffffffffffffffff

def z571 : W := mkw 0x0800445d880492e1 0x4100088bb100925c 0xa8060cff981c13e7 0x3500c19ff303827c

def z572 : W := mkw 0x1cfac1fd14e987a6 0x439f583fa29d30f4 0x40f8c0f800e18380 0x881f181f001c3070

def z573 : W := mkw 0x07f7ae02dfdf5851 0x80fef5c05bfbeb0a 0xfffffc039fffe005 0xffffff8073fffc00

def z574 : W := mkw 0x14b851ec34e0a7ae 0x22970a3d869c14f5 0x40f8f0f800e1e380 0x881f1e1f001c3c70

def z575 : W := mkw 0x06d7a000065b4000 0x00daf40000cb6800 0x1f1ff000077fe001 0x43e3fe0000effc00

def z576 : W := mkw 0x08628419988d1241 0x410c50833311a248 0xe8e60c3f981c1067 0x3d1cc187f303820c

def z577 : W := mkw 0x1fffeffd9fffdfe7 0x43fffdffb3fffbfc 0xffffffff9fffffe7 0xfffffffff3fffffc

def z578 : W := mkw 0x0cf2c45d9ccd92e1 0x419e588bb399b25c 0xfffeccff9ffd93e7 0xffffd99ff3ffb27c

def z579 : W := mkw 0x03050e024b121810 0x8060a1c049624302 0xb7010f007f021c1e 0x76e021e00fe04383

def z580 : W := mkw 0x0b678e1bdb9f1a51 0xc16cf1c37b73e34a 0xffe70f3fff1e1c7f 0x7ffce1e7ffe3c38f

def z581 : W := mkw 0x000000000020a5ac 0x20000000000414b5 0x9819f00000e3fffd 0xd3033e00001c7fff

def z582 : W := mkw 0x0a67c45fda9f92f1 0xc14cf88bfb53f25e 0xe8e7ccfff89f93ff 0xbd1cf99fff13f27f

def z583 : W := mkw 0x37ffffff7ffb5f06 0x06ffffffefff6be0 0xffffffffffffff87 0xfffffffffffffff0

def z584 : W := mkw 0x0247a00000000000 0x0048f40000000000 0x0007f00000000001 0x0000fe0000000000

def z585 : W := mkw 0x0000040089041851 0x800000801120830a 0x0000000000001c78 0x000000000000038f

def z586 : W := mkw 0x00004444880490e1 0x000008889100921c 0xa806ccc7989d93e7 0xb500d998f313b27c

def z587 : W := mkw 0x0862c45d9b9f9af1 0xc10c588bb373f35e 0xf8e6ccff9f9f9fff 0xbf1cd99ff3f3f3ff

def z588 : W := mkw 0x1000040809201f06 0x02000081012403e0 0x0000000000001f80 0x00000000000003f0

def z589 : W := mkw 0x0205000002120000 0x0040a00000424000 0x9f1ff0001fffe005 0xf3e3fe0003fffc00

def z590 : W := mkw 0x0862c45d988d92e1 0x410c588bb311b25c 0x60e0ccff808193e2 0x8c1c199ff010327c

def z591 : W := mkw 0x17bd0faa5ff21f16 0x82f7a1f54bfe43e2 0xf7f90ff87fe21f9e 0xfeff21ff0ffc43f3

def z592 : W := mkw 0x196acffd99ad9fe7 0x432d59ffb335b3fc 0xe8e6cfff989d9fe7 0xbd1cd9fff313b3fc

def z593 : W := mkw 0x06b5000016d20000 0x00d6a00002da4000 0xdfff00001ffe0005 0xfbffe00003ffc000

def z594 : W := mkw 0x0247a000021b4000 0x0048f40000436800 0x9f07f0001f1fe005 0x73e0fe0003e3fc00

def z595 : W := mkw 0x000851c42020a5ac 0x20010a38840414b5 0x0801f3c46003fffb 0x01003e788c007fff

def z596 : W := mkw 0x0862c45d988d92e1 0x410c588bb311b25c 0xf8fffcff98fff3e7 0xff1fff9ff31ffe7c

def z597 : W := mkw 0x37ffffff7dc01a02 0x06ffffffefb80340 0xe7ffffffff000003 0xfcffffffffe00000

def z598 : W := mkw 0x03050e02cb36bdfd 0xa060a1c05966d7bf 0xbf070f07ffffffff 0x77e0e1e0ffffffff

def z599 : W := mkw 0x2fdfffffe80492e1 0x45fbfffffd00925c 0xe7ffffffe00013e3 0xfcfffffffc00027c

def z600 : W := mkw 0x0267a00016db4000 0x004cf40002db6800 0x1807f0001fffe005 0x0300fe0003fffc00

def z601 : W := mkw 0x2ff7ae3bd88d1241 0x45fef5c77b11a248 0x67e60c3b981c0000 0x2cfcc18773038000

def z602 : W := mkw 0x15980ba005600d06 0x02b3017400ac01a0 0xf7f80ff807600c02 0xfeff01ff00ec0180

def z603 : W := mkw 0x14b805a81ce01706 0x029700b5039c02e0 0xe0f80cf818e01386 0xbc1f019f031c0270

def z604 : W := mkw 0x1df28e399dcd1a43 0x43be51c733b9a348 0x67e60c3b9f1c0000 0x2cfcc18773e38000

def z605 : W := mkw 0x0042a00000094000 0x0008540000012800 0x0000f0000001e000 0x00001e0000003c00

def z606 : W := mkw 0x0205200002124000 0x0040a40000424800 0x0001300000026000 0x0000260000004c00

def z607 : W := mkw 0x0205000002120000 0x0040a00000424000 0x9f0703047f1e1c7f 0x73e0e0608fe3c38f

def z608 : W := mkw 0x27fffbf774c00000 0x04ffff7eee980000 0xf7ffffffffe00007 0xfefffffffffc0000

def z609 : W := mkw 0x0205000002120000 0x0040a00000424000 0x070600001f1c0000 0x20e0c00003e38000

def z610 : W := mkw 0x0962ce5d998d9ae1 0x412c59cbb331b35c 0xffe6cfff9f9d9fe7 0xfffcd9fff3f3b3fc

def z611 : W := mkw 0x04faf1c434e9e5ac 0x209f5e38869d3cb5 0x40f8f0c000e1e380 0x881f1e18001c3c70

def z612 : W := mkw 0x08200408988d92e1 0x410400811311b25c 0xa8060c07989d93e7 0x3500c180f313b27c

def z613 : W := mkw 0x0800445d880492e1 0x4100088bb100925c 0xa800ccff808193e7 0x9500199ff010327c

def z614 : W := mkw 0x2247f057621b4000 0x0448fe0aec436800 0x0807f007e01fe001 0x0100fe00fc03fc00

def z615 : W := mkw 0x15985be42560adae 0x22b30b7c84ac15b5 0x9f19f3c467e3ffff 0xd3e33e788cfc7fff

def z616 : W := mkw 0x000851c4200080a0 0x00010a3884001014 0x8819f3c4608193e7 0xd1033e788c10327c

def z617 : W := mkw 0x0008018000200504 0x00010030000400a0 0x1018030000600c00 0x42030060000c0180

def z618 : W := mkw 0x11080fa809201f06 0x022101f5012403e0 0xb7000ff81f001f86 0x76e001ff03e003f0

def z619 : W := mkw 0x27dffbf7e2160051 0x84fbff7efc42c00a 0xefffffffe01e007b 0xfdfffffffc03c00f

def z620 : W := mkw 0x02050402ca161051 0x8040a0805942c20a 0xa8070c07f81e107f 0x3500e180ff03c20f

def z621 : W := mkw 0x00004044000080a0 0x0000080880001014 0x0800c00400018061 0x010018008000300c

def z622 : W := mkw 0x03050a0243120810 0x8060a14048624102 0x9f01030467021c7f 0x53e020608ce0438f

def z623 : W := mkw 0x000801800020a5ac 0x20010030000414b5 0x981803c000e3fffe 0xd3030078001c7fff

def z624 : W := mkw 0x01000e02c9041851 0x802001c05920830a 0xa8060f07f81c1c7f 0x3500c1e0ff03838f

def z625 : W := mkw 0x15b80fa81de01f06 0x02b701f503bc03e0 0xfff9fff81fe3ff87 0xffff3fff03fc7ff0

def z626 : W := mkw 0x200851f520000000 0x04010a3ea4000000 0x000000f800000000 0x0000001f00000000

def z627 : W := mkw 0x04faf1c434e9e5ac 0x209f5e38869d3cb5 0xd8f9f3c460e3ffff 0xdb1f3e788c1c7fff

def z628 : W := mkw 0x04f2a00014c94000 0x009e540002992800 0xd7f8f0001fe1e004 0xfaff1e0003fc3c00

def z629 : W := mkw 0x130d0faacb361f57 0x8261a1f55966c3ea 0xbf070fffff1e1fff 0x77e0e1ffffe3c3ff

def z630 : W := mkw 0x03050a0243120810 0x8060a14048624102 0x0700000007000000 0x00e0000000e00000

def z631 : W := mkw 0x06dff1c42020a5ac 0x20dbfe38840414b5 0xdffff3c460e3ffff 0xfbfffe788c1c7fff

def z632 : W := mkw 0x15b85fec3de0bfae 0x22b70bfd87bc17f5 0xf7f80ffc7fe01ffe 0xfeff01ff8ffc03ff

def z633 : W := mkw 0x0695200006524000 0x00d2a40000ca4800 0x0700000007000000 0x00e0000000e00000

def z634 : W := mkw 0x02050002c2160051 0x8040a0005842c00a 0x98070307e01e1c7f 0x5300e060fc03c38f

def z635 : W := mkw 0x11280fa819a01f06 0x022501f5033403e0 0xe0e00ff818801f86 0xbc1c01ff031003f0

def z636 : W := mkw 0x26f7f05776db4000 0x04defe0aeedb6800 0xdffff007ffffe005 0xfbfffe00fffffc00

def z637 : W := mkw 0x0ef7e05d16dbc2a0 0x41defc0ba2db7854 0xdffff0f81fffe385 0xfbfffe1f03fffc70

def z638 : W := mkw 0x15b85fec3de0bfae 0x22b70bfd87bc17f5 0xf7f8fff81fe1ff86 0xfeff1fff03fc3ff0

def z639 : W := mkw 0x0cf2e05d14c9c2a0 0x419e5c0ba2993854 0x40f8f0f800e1e380 0x881f1e1f001c3c70

def z640 : W := mkw 0x01000e008b161851 0x802001c01162c30a 0xbf000f001f1e1c7e 0x77e001e003e3c38f

def z641 : W := mkw 0x02050002c2160051 0x8040a0005842c00a 0x00060003801c0000 0x0000c00070038000

def z642 : W := mkw 0x27dfbba260000000 0x04fbf7744c000000 0xc7fff30060000001 0xf8fffe600c000000

def z643 : W := mkw 0x002855cc38a0b7ac 0x20050ab9871416f5 0xf8f9fffc78e3ffff 0xff1f3fff8f1c7fff

def z644 : W := mkw 0x27dffff7eb161851 0x84fbfffefd62c30a 0xe7ffffffff1c0003 0xfcffffffffe38000

def z645 : W := mkw 0x11085fec2920bfae 0x22210bfd852417f5 0xb819fffc60e3ffff 0xd7033fff8c1c7fff

def z646 : W := mkw 0x06fff1c436db4000 0x00dffe3886db6800 0xdffff3c47fffe007 0xfbfffe788ffffc00

def z647 : W := mkw 0x24d2a03100000000 0x049a540620000000 0x40e0003800000000 0x081c000700000000

def z648 : W := mkw 0x086ad1dd30a9a7ac 0x610d5a3ba61534f5 0xd8f9f3fc60e3ffff 0xdb1f3e7f8c1c7fff

def z649 : W := mkw 0x0695200000000000 0x00d2a40000000000 0x0719300000000000 0x40e3260000000000

def z650 : W := mkw 0x0000000000200504 0x00000000000400a0 0x1000000000e01f84 0x02000000001c03f0

def z651 : W := mkw 0x25dafbf520000000 0x04bb5f7ea4000000 0xe7f8fff800000002 0xfcff1fff00000000

def z652 : W := mkw 0x0000000000000000 0x0000000000000000 0x8019f00000000001 0xd0033e0000000000

def z653 : W := mkw 0x15fa8fa81de91f06 0x02bf51f503bd23e0 0xfffecff81ffd9f87 0xffffd9ff03ffb3f0

def z654 : W := mkw 0x0ef7e45d988d92e1 0x41defc8bb311b25c 0xeffffcff989d93e7 0xfdffff9ff313b27c

def z655 : W := mkw 0x2205300260000000 0x0440a6004c000000 0x0001300060000000 0x000026000c000000

def z656 : W := mkw 0x0000000000000000 0x0000000000000000 0x1800000000021c7c 0x030000000000438f

def z657 : W := mkw 0x000851c42020a5ac 0x20010a38840414b5 0x000000c000000380 0x0000001800000070

def z658 : W := mkw 0x1dfa8fb99ded1f47 0x43bf51f733bda3e8 0xf7fe0ffb9ffc1f86 0xfeffc1ff73ff83f0

def z659 : W := mkw 0x000851c42020a5ac 0x20010a38840414b5 0x101933c460627ffa 0x420326788c0c4fff

def z660 : W := mkw 0x000050442000a0a8 0x20000a0884001415 0x9801f3046003fc7f 0x53003e608c007f8f

def z661 : W := mkw 0x002004009fdf5851 0x8004008013fbeb0a 0x180000001ffffc7c 0x0300000003ffff8f

def z662 : W := mkw 0x34faf1fd34e00706 0x069f5e3fa69c00e0 0x40f8f0f800e00380 0x881f1e1f001c0070

def z663 : W := mkw 0x03050a0240000000 0x0060a14048000000 0x27060c0380000000 0x24e0c18070000000

def z664 : W := mkw 0x26dff1f520000000 0x04dbfe3ea4000000 0xc7fff0f800000001 0xf8fffe1f00000000

def z665 : W := mkw 0x0000000003120810 0x8000000000624102 0x1000000007020c18 0x0200000000e04183

def z666 : W := mkw 0x08628419988d1241 0x410c50833311a248 0xe8e6cc3b989d8005 0xbd1cd9877313b000

def z667 : W := mkw 0x3ffffffffded9fe7 0x47ffffffffbdb3fc 0xfffffffffffd9fe7 0xffffffffffffb3fc

def z668 : W := mkw 0x0b678e1bdb9f1a51 0xc16cf1c37b73e34a 0x67e60c3b9f1c0000 0x2cfcc18773e38000

def z669 : W := mkw 0x149801a004600506 0x02930034008c00a0 0x0018000000600000 0x00030000000c0000

def z670 : W := mkw 0x06f7a00016db4000 0x00def40002db6800 0x5fe600001fffe004 0x2bfcc00003fffc00

def z671 : W := mkw 0x27fffff7ffdf5851 0x84fffffefffbeb0a 0xfffffffffffffc7f 0xffffffffffffff8f

def z672 : W := mkw 0x15b80fa81ffb5f06 0x02b701f503ff6be0 0xfff80ff81fffff86 0xffff01ff03fffff0

def z673 : W := mkw 0x15b00e281dc01a02 0x02b601c503b80340 0xf7f80c381fe00004 0xfeff018703fc0000

def z674 : W := mkw 0x17f7ae281fdb5a02 0x02fef5c503fb6b40 0xfffffc381fffe005 0xffffff8703fffc00

def z675 : W := mkw 0x0020000016fbe5ac 0x2004000002df7cb5 0x180000001ffffffc 0x0300000003ffffff

def z676 : W := mkw 0x15981ba025602d0e 0x22b3037404ac05a1 0x1719330067626c18 0x42e326600cec4d83

def z677 : W := mkw 0x04b8018014e00504 0x00970030029c00a0 0xd7f803c01fe01f86 0xfaff007803fc03f0

def z678 : W := mkw 0x06ffb18036fb650c 0x20dff63006df6ca1 0xdffff3007fffec1d 0xfbfffe600ffffd83

def z679 : W := mkw 0x35fafffd3de01f06 0x06bf5fffa7bc03e0 0xf7f8fff81fe01f86 0xfeff1fff03fc03f0

def z680 : W := mkw 0x27dffff769001800 0x04fbfffeed200300 0xf7ffffffff001c07 0xfeffffffffe00380

def z681 : W := mkw 0x000851c42020a5ac 0x20010a38840414b5 0x8800c3c460819fff 0x910018788c1033ff

def z682 : W := mkw 0x37bd3faa7de01f06 0x06f7a7f54fbc03e0 0xf7f93ff87fe01f86 0xfeff27ff0ffc03f0

def z683 : W := mkw 0x06f7a00016db4000 0x00def40002db6800 0xdfe700001f1e0005 0x7bfce00003e3c000

def z684 : W := mkw 0x0ef7e05596dfc0e1 0x41defc0ab2dbf81c 0xdffff0079fffe065 0xfbfffe00f3fffc0c

def z685 : W := mkw 0x2a67f45ff88d92e1 0x454cfe8bff11b25c 0xe8e7fcfff89d93e7 0xbd1cff9fff13b27c

def z686 : W := mkw 0x000851c42020a5ac 0x20010a38840414b5 0x1019f3c060e3ef98 0xc2033e780c1c7df3

def z687 : W := mkw 0x000851c42020a5ac 0x20010a38840414b5 0x0819f0c460e3e3f9 0x81033e188c1c7c7f

def z688 : W := mkw 0x000811802020250c 0x20010230040404a1 0x0018300000606000 0x00030600000c0c00

def z689 : W := mkw 0x000050442000a0a8 0x20000a0884001415 0x0000f0000001e000 0x00001e0000003c00

def z690 : W := mkw 0x0862c45d988d92e1 0x410c588bb311b25c 0x48e0c0f8189d93e4 0x891c181f0313b27c

def z691 : W := mkw 0x2cfaf5fdb88d92e1 0x459f5ebfb711b25c 0xe8fefcff989d93e7 0xbd1fdf9ff313b27c

def z692 : W := mkw 0x06ffa18016fb4504 0x00dff43002df68a0 0xdffff3c01fffff87 0xfbfffe7803fffff0

def z693 : W := mkw 0x0020000010800000 0x0004000002100000 0xc0e0000018800004 0xb81c000003100000

def z694 : W := mkw 0x03250e02dfdf5851 0x8064a1c05bfbeb0a 0xbf070f07fffffc7f 0x77e0e1e0ffffff8f

def z695 : W := mkw 0x000851c42020a5ac 0x20010a38840414b5 0x1818f0c000e3fffc 0x83031e18001c7fff

def z696 : W := mkw 0x0008018000000000 0x0001003000000000 0x801803c000000002 0xd003007800000000

def z697 : W := mkw 0x0000000000000000 0x0000000000000000 0x1800000000e3e004 0x03000000001c7c00

def z698 : W := mkw 0x000000000020a5ac 0x20000000000414b5 0x0000000000001ff8 0x00000000000003ff

def z699 : W := mkw 0x0247a002c21f4051 0x8048f4005843e80a 0x0807f007e01fe079 0x0100fe00fc03fc0f

def z700 : W := mkw 0x11080ba001200d06 0x02210174002401a0 0x0000030000000c00 0x0000006000000180

def z701 : W := mkw 0x03050a0243120810 0x8060a14048624102 0x9f0703007f1e0c1d 0x73e0e0600fe3c183

def z702 : W := mkw 0x19084ffd89249fe7 0x432109ffb12493fc 0x20000fff80001fe2 0x040001fff00003fc

def z703 : W := mkw 0x2042f05520000000 0x04085e0aa4000000 0x0000f00000000000 0x00001e0000000000

def z704 : W := mkw 0x07952a0247524810 0x80f2a54048ea4902 0x1719330067626c18 0x42e326600cec4d83

def z705 : W := mkw 0x01000a0241000810 0x8020014048200102 0x0000030060000c18 0x000000600c000183

def z706 : W := mkw 0x0ef7a4199edf5241 0x41def48333dbea48 0x67e60c3b9f1c0000 0x2cfcc18773e38000

def z707 : W := mkw 0x082004089a9f92e1 0x410400811353f25c 0x180000001f9f93e4 0x0300000003f3f27c

def z708 : W := mkw 0x030d5fc6eb36bdfd 0xa061abf8dd66d7bf 0x271efcc39ffde380 0xa4e3df9873ffbc70

def z709 : W := mkw 0x04b0000016db4000 0x0096000002db6800 0xdff9f0001fffe005 0xfbff3e0003fffc00

def z710 : W := mkw 0x179d2ba247724d16 0x82f3a57448ee49a2 0x1719330067626c18 0x42e326600cec4d83

def z711 : W := mkw 0x16bd01aad6f60757 0x82d7a0355adec0ea 0x48ff00ffe0fe03f9 0x891fe01ffc1fc07f

def z712 : W := mkw 0x17bd0faadff61f57 0x82f7a1f55bfec3ea 0x1f1903007ffe1ffc 0x43e320600fffc3ff

def z713 : W := mkw 0x0247a000021b4000 0x0048f40000436800 0x9f1ff0001fffe005 0xf3e3fe0003fffc00

def z714 : W := mkw 0x0862d45db88db2e9 0x610c5a8bb711b65d 0xf8e7fffff89fffff 0xff1cffffff13ffff

def z715 : W := mkw 0x21285bf776db4000 0x04250b7eeedb6800 0x38000fffffffe006 0x070001fffffffc00

def z716 : W := mkw 0x0042c05500000000 0x0008580aa0000000 0xe0e7cfffe0000003 0xfc1cf9fffc000000

def z717 : W := mkw 0x06f7a00016db4000 0x00def40002db6800 0xc7fff0001ffde001 0xf8fffe0003ffbc00

def z718 : W := mkw 0x0042c05500000000 0x0008580aa0000000 0xe0fffcff80000003 0xfc1fff9ff0000000

def z719 : W := mkw 0x27dffbf76020250c 0x24fbff7eec0404a1 0xffffffffe0e3ec1f 0xfffffffffc1c7d83

def z720 : W := mkw 0x27dffbf76000a0a8 0x24fbff7eec001415 0xe7ffffffe001e003 0xfcfffffffc003c00

def z721 : W := mkw 0x05980ba000000000 0x00b3017400000000 0xe7fe0fff80000003 0xfcffc1fff0000000

def z722 : W := mkw 0x1ddacbf5856d8de7 0x43bb597eb0adb1bc 0x1f1ec307877d8c61 0x43e3d860f0efb18c

def z723 : W := mkw 0x082855ccb88d92e1 0x41050ab99711b25c 0x8819f3c4789d93e7 0xd1033e788f13b27c

def z724 : W := mkw 0x27dffbf76020a5ac 0x24fbff7eec0414b5 0xffffffffe0021fff 0xfffffffffc0043ff

def z725 : W := mkw 0x0820445d988492e1 0x4104088bb310925c 0xe8e60cff989c13e7 0xbd1cc19ff313827c

def z726 : W := mkw 0x15b05e6c3dc0baaa 0x22b60bcd87b81755 0x6fe1fc3c7f03e079 0x2dfc3f878fe07c0f

def z727 : W := mkw 0x03050e02cb161851 0x8060a1c05962c30a 0xffe70fffff1e1c7f 0xfffce1ffffe3c38f

def z728 : W := mkw 0x0a47e057c21fc0f1 0xc148fc0af843f81e 0x0807f007e01fe079 0x0100fe00fc03fc0f

def z729 : W := mkw 0x15b80ba815e00f06 0x02b7017502bc01e0 0xf7f80ff807e00f82 0xfeff01ff00fc01f0

def z730 : W := mkw 0x06f7a00016db4000 0x00def40002db6800 0x57fff0001fffe000 0xeafffe0003fffc00

def z731 : W := mkw 0x08200408988d92e1 0x410400811311b25c 0x00000000181c13e0 0x000000000303827c

def z732 : W := mkw 0x27dffbf76020a5ac 0x24fbff7eec0414b5 0xf7ffffffe0e1ff87 0xfefffffffc1c3ff0

def z733 : W := mkw 0x000851c42020a5ac 0x20010a38840414b5 0xf8f9fffc60e3ffff 0xff1f3fff8c1c7fff

def z734 : W := mkw 0x0862c45d988d92e1 0x410c588bb311b25c 0xe8e6ccfb989d8385 0xbd1cd99f7313b070

def z735 : W := mkw 0x27dffbf760000000 0x04fbff7eec000000 0xf7ffffffe0626003 0xfefffffffc0c4c00

def z736 : W := mkw 0x102004089de41f47 0x0204008113bc83e8 0x180000001ffc1fe4 0x0300000003ff83fc

def z737 : W := mkw 0x0b67ca5f539b8ab0 0xc16cf94bea737156 0x57e1c3f867838f98 0xcafc387f0cf071f3

def z738 : W := mkw 0x004ad1d52020250c 0x20095a3aa40404a1 0xf0ffffffe0626c1b 0xfe1ffffffc0c4d83

def z739 : W := mkw 0x06f7a01116db4000 0x00def40222db6800 0xfffffc3b9fffe005 0xffffff8773fffc00

def z740 : W := mkw 0x15b80fa81de01f06 0x02b701f503bc03e0 0xf7f90ffc7fe01f87 0xfeff21ff8ffc03f0

def z741 : W := mkw 0x01000e0089041841 0x002001c011208308 0xbf070f07ff1e1c7f 0x77e0e1e0ffe3c38f

def z742 : W := mkw 0x2247f057621be0a8 0x2448fe0aec437c15 0x0807f007e01fe079 0x0100fe00fc03fc0f

def z743 : W := mkw 0x15b80fa81de01f06 0x02b701f503bc03e0 0xf7fe0fff9fe01f87 0xfeffc1fff3fc03f0

def z744 : W := mkw 0x0042c05500000000 0x0008580aa0000000 0x60e60cff80000002 0x2c1cc19ff0000000

def z745 : W := mkw 0x0820444c988d92e1 0x410408899311b25c 0x080000c4189d93e6 0x010000188313b27c

def z746 : W := mkw 0x15b00e281de01f06 0x02b601c503bc03e0 0xf7e00cf81fe01f86 0xbefc019f03fc03f0

def z747 : W := mkw 0x27d7aa334020a5ac 0x24faf546680414b5 0x7fe60c3b80e3fffc 0x2ffcc187701c7fff

def z748 : W := mkw 0x24daf5f5ab161851 0x849b5ebeb562c30a 0x58f8f0f81f1e1c7c 0x8b1f1e1f03e3c38f

def z749 : W := mkw 0x15b80fa81de01f06 0x02b701f503bc03e0 0xfff80ff81fe3ff86 0xffff01ff03fc7ff0

def z750 : W := mkw 0x06f7a00016db4000 0x00def40002db6800 0x5ffff0001f7fe001 0x6bfffe0003effc00

def z751 : W := mkw 0x1862c45d9dcd9ae3 0x430c588bb3b9b35c 0xe8e6ccff9f9d93e7 0xbd1cd99ff3f3b27c

def z752 : W := mkw 0x15b80fa81de01f06 0x02b701f503bc03e0 0xfff9fffc7fe3ffff 0xffff3fff8ffc7fff

def z753 : W := mkw 0x214adbf76020a5ac 0x24295b7eec0414b5 0xe8e6cfffe0819fff 0xbd1cd9fffc1033ff

def z754 : W := mkw 0x27dffbf760000000 0x04fbff7eec000000 0xf7ffffffe0001c07 0xfefffffffc000380

def z755 : W := mkw 0x0695200006524000 0x00d2a40000ca4800 0x9f1ff0001fffe005 0xf3e3fe0003fffc00

def z756 : W := mkw 0x03050e02cb161851 0x8060a1c05962c30a 0xbf1f0f07fffe1c7f 0xf7e3e1e0ffffc38f

def z757 : W := mkw 0x13050e2acb161a53 0x8260a1c55962c34a 0xbf070f3fff1e1c7f 0x77e0e1e7ffe3c38f

def z758 : W := mkw 0x24daf1f520000000 0x049b5e3ea4000000 0x60f8fcff80000002 0x8c1f1f9ff0000000

def z759 : W := mkw 0x27d7aa33421b4000 0x04faf54668436800 0x67e60c3b801c0000 0x2cfcc18770038000

def z760 : W := mkw 0x000851c42020a5ac 0x20010a38840414b5 0x0819f3c460e3fffb 0x81033e788c1c7fff

def z761 : W := mkw 0x37dffbf764600506 0x06fbff7eec8c00a0 0xe7ffffffe0600003 0xfcfffffffc0c0000

def z762 : W := mkw 0x06f7a00016db4000 0x00def40002db6800 0x5ff9f0001fffe004 0xcbff3e0003fffc00

def z763 : W := mkw 0x2fbd3faaf88d92e1 0x45f7a7f55f11b25c 0x0f193300789d93e4 0x41e326600f13b27c

def z764 : W := mkw 0x27dffbf760000000 0x04fbff7eec000000 0x67feffffe0000002 0xacffdffffc000000

def z765 : W := mkw 0x0862c45d988d92e1 0x410c588bb311b25c 0xe8fefcff98fdf3e7 0xbd1fdf9ff31fbe7c

def z766 : W := mkw 0x0862c45d988d92e1 0x410c588bb311b25c 0xf8e6cfff989d9fe7 0xff1cd9fff313b3fc

def z767 : W := mkw 0x0042c455880490e1 0x0008588ab100921c 0xe8e6ccff989d93e7 0xbd1cd99ff313b27c

def z768 : W := mkw 0x379d3ba267720d16 0x86f3a7744cee41a2 0x1719330067620c18 0x42e326600cec4183

def z769 : W := mkw 0x0a67a4089a9fd2e1 0x414cf4811353fa5c 0x0807f000189ff3e5 0x0100fe000313fe7c

def z770 : W := mkw 0x086a9599b8ad374d 0x610d52b33715a6e9 0x70ff3f3bf87e6c18 0x6e1fe7e77f0fcd83

def z771 : W := mkw 0x102004089fd61a53 0x8204008113fac34a 0x180000001f1e1c7c 0x0300000003e3c38f

def z772 : W := mkw 0x102004089fd61a53 0x8204008113fac34a 0x000000001f1c0000 0x0000000003e38000

def z773 : W := mkw 0x05dacbf5002085a4 0x00bb597ea00410b4 0xfffecfff80e19fe7 0xffffd9fff01c33fc

def z774 : W := mkw 0x1db80fa89ded1f47 0x43b701f513bda3e8 0xf7f80ff81ffc1f86 0xfeff01ff03ff83f0

def z775 : W := mkw 0x03478a1340000000 0x0068f14268000000 0x67e60c3b80000000 0x2cfcc18770000000

def z776 : W := mkw 0x27d7aa3340000000 0x04faf54668000000 0x67e60f3fe0000002 0x2cfcc1e7fc000000

def z777 : W := mkw 0x26f7a01356db4000 0x04def4026adb6800 0xdffff0039fffe005 0xfbfffe0073fffc00

def z778 : W := mkw 0x21085ff7e924bdfd 0xa4210bfefd2497bf 0x20000fffe0001ffa 0x040001fffc0003ff

def z779 : W := mkw 0x27d7aa3343120810 0x84faf54668624102 0x77e70f3be7020c18 0x6efce1e77ce04183

def z780 : W := mkw 0x06d7a00002120000 0x00daf40000424000 0xdffff0001fffe005 0xfbfffe0003fffc00

def z781 : W := mkw 0x3267f45f7de01f06 0x064cfe8befbc03e0 0x1007f007ffe01f85 0x0200fe00fffc03f0

def z782 : W := mkw 0x25dafbf760000000 0x04bb5f7eec000000 0x60e00fffe0000002 0x0c1c01fffc000000

def z783 : W := mkw 0x37d7aa3345400802 0x06faf54668a80100 0x67e60c3b87000000 0x2cfcc18770e00000

def z784 : W := mkw 0x06b5200016db4000 0x00d6a40002db6800 0x9f19f0001fffe005 0xd3e33e0003fffc00

def z785 : W := mkw 0x15980fa80d601f06 0x02b301f501ac03e0 0xf7f80ff807601f82 0xfeff01ff00ec03f0

def z786 : W := mkw 0x2142ca7740000000 0x0428594ee8000000 0xe0e6ccff80000003 0xbc1cd99ff0000000

def z787 : W := mkw 0x07950a2240000000 0x00f2a14448000000 0xe7e70f3fe0000003 0x7cfce1e7fc000000

def z788 : W := mkw 0x27dffbf763120810 0x84fbff7eec624102 0xe7ffffffe7000003 0xfcfffffffce00000

def z789 : W := mkw 0x102805889ff61f57 0x820500b113fec3ea 0x981903c47ffe1fff 0xd30320788fffc3ff

def z790 : W := mkw 0x27dffbf76020a5ac 0x24fbff7eec0414b5 0xefffffffe0e3e3fb 0xfdfffffffc1c7c7f

def z791 : W := mkw 0x079d5be66020a5ac 0x20f3ab7ccc0414b5 0xffffffffe0e3ffff 0xfffffffffc1c7fff

def z792 : W := mkw 0x26d7f05760000000 0x04dafe0aec000000 0xe7fffcffe0000003 0xfcffff9ffc000000

def z793 : W := mkw 0x000811802020a5ac 0x20010230040414b5 0x9819f30060e3fffd 0xd3033e600c1c7fff

def z794 : W := mkw 0x15b80fa81de01f06 0x02b701f503bc03e0 0xfff90ff81fe21f87 0xffff21ff03fc43f0

def z795 : W := mkw 0x0042d05520000000 0x00085a0aa4000000 0xe0e7fcffe0000003 0xbc1cff9ffc000000

def z796 : W := mkw 0x0e95645d8e56d2e1 0x41d2ac8bb1cada5c 0x37193cff876273e2 0x46e3279ff0ec4e7c

def z797 : W := mkw 0x0862c45d9ccd92e1 0x410c588bb399b25c 0xf8e6ccff9ffd93e7 0xbf1cd99ff3ffb27c

def z798 : W := mkw 0x15dacbf505600d06 0x02bb597ea0ac01a0 0xf7fecfff87600c03 0xfeffd9fff0ec0180

def z799 : W := mkw 0x15b80fa81de01f06 0x02b701f503bc03e0 0xf7f8fff81fe1ff86 0xfeff1fff03fc3ff0

def z800 : W := mkw 0x279d3ba26672650c 0x24f3a7744cce4ca1 0x1719330067626c18 0x42e326600cec4d83

def z801 : W := mkw 0x06d7a01100000000 0x00daf40220000000 0xe7fffc3b80000001 0xfcffff8770000000

def z802 : W := mkw 0x0862c45d998d9af1 0xc10c588bb331b35e 0xe8e6ccff989d9fff 0xbd1cd99ff313b3ff

def z803 : W := mkw 0x05f2ae02ddcd5851 0x80be55c05bb9ab0a 0x60f8ff07e0e1fc7a 0x8c1f1fe0fc1c3f8f

def z804 : W := mkw 0x27d7aa3346524000 0x04faf54668ca4800 0x67e60c3b87000000 0x2cfcc18770e00000

def z805 : W := mkw 0x079d5be660000000 0x00f3ab7ccc000000 0xe7ffffffe0000003 0xfcfffffffc000000

def z806 : W := mkw 0x03050e02cb161851 0x8060a1c05962c30a 0xbf07cf07ff9f9c7f 0xf7e0f9e0fff3f38f

def z807 : W := mkw 0x06f7a00016db4000 0x00def40002db6800 0xfffffc079fffe007 0xffffff80f3fffc00

def z808 : W := mkw 0x27d7aa3340000000 0x04faf54668000000 0xe7ffff3fe0000003 0xfcffffe7fc000000

def z809 : W := mkw 0x26f7a03116db4000 0x04def40622db6800 0xdffff0381fffe005 0xfbfffe0703fffc00

def z810 : W := mkw 0x182004089ced97e7 0x43040081139db2fc 0x0800000018fd93e4 0x01000000031fb27c

def z811 : W := mkw 0x05dadbf520000000 0x00bb5b7ea4000000 0xe7ffffffe0000003 0xfcfffffffc000000

def z812 : W := mkw 0x26dff1f520000000 0x04dbfe3ea4000000 0xe7fffcff80000003 0xfcffff9ff0000000

def z813 : W := mkw 0x27dffbf760000000 0x04fbff7eec000000 0x67fffffbe0000000 0xecffffff7c000000

def z814 : W := mkw 0x15980ba005600d06 0x02b3017400ac01a0 0xf7f80ff807e01f86 0xfeff01ff00fc03f0

def z815 : W := mkw 0x25dafbf760000000 0x04bb5f7eec000000 0xe0f9ffffe0000003 0xdc1f3ffffc000000

def z816 : W := mkw 0x27dffbf7621b4000 0x04fbff7eec436800 0xe7ffffffe01c0003 0xfcfffffffc038000

def z817 : W := mkw 0x08200408988db2e9 0x610400811311b65d 0x08000000189ff3fc 0x010000000313fe7f

def z818 : W := mkw 0x03050e02cb161851 0x8060a1c05962c30a 0x3f060f07ff1e1c7e 0x27e0c1e0ffe3c38f

def z819 : W := mkw 0x27dffbf76020a5ac 0x24fbff7eec0414b5 0xffffffffe0e3e387 0xfffffffffc1c7c70

def z820 : W := mkw 0x02050002c2160051 0x8040a0005842c00a 0x9f070307ff1e1c7f 0x73e0e060ffe3c38f

def z821 : W := mkw 0x17f7ae2adfdf5a53 0x82fef5c55bfbeb4a 0x67e60c3b9f1c0000 0x2cfcc18773e38000

def z822 : W := mkw 0x15b80fa81de01f06 0x02b701f503bc03e0 0x77f80ff81fe00f80 0xeeff01ff03fc01f0

def z823 : W := mkw 0x01200e0819801a00 0x002401c103300340 0xe7e00cf81f801386 0xbcfc019f03f00270

def z824 : W := mkw 0x25dafbf76020a5ac 0x24bb5f7eec0414b5 0x60f8ffffe0e1fffa 0x8c1f1ffffc1c3fff

def z825 : W := mkw 0x27d7aa3340000000 0x04faf54668000000 0xe7e60cfb80000002 0xbcfcc19f70000000

def z826 : W := mkw 0x0042c05500000000 0x0008580aa0000000 0x60e6ccfb80000000 0xac1cd99f70000000

def z827 : W := mkw 0x08200408988d92e1 0x410400811311b25c 0x00000000008193e0 0x000000000010327c

def z828 : W := mkw 0x27dffbf7621b4000 0x04fbff7eec436800 0xffffffffff1fe007 0xffffffffffe3fc00

def z829 : W := mkw 0x15b00e281dc01a02 0x02b601c503b80340 0x67e00cf81f001382 0x2cfc019f03e00270

def z830 : W := mkw 0x06f7a00016db4000 0x00def40002db6800 0xdffff3001ffffc07 0xfbfffe6003ffff80

def z831 : W := mkw 0x27dffbf760000000 0x04fbff7eec000000 0xe7ffffffe0e1e003 0xfcfffffffc1c3c00

def z832 : W := mkw 0x102004089de41f57 0x8204008113bc83ea 0x100000001fe01ffc 0x0200000003fc03ff

def z833 : W := mkw 0x102004089ff6bfff 0xa204008113fed7ff 0x180000001ffffffc 0x0300000003ffffff

def z834 : W := mkw 0x27d7ea7740000000 0x04fafd4ee8000000 0xe7e7cfffe0000003 0xfcfcf9fffc000000

def z835 : W := mkw 0x05d2ca7500000000 0x00ba594ea0000000 0xe7e6ccff80000003 0xbcfcd99ff0000000

def z836 : W := mkw 0x08200408988d92e1 0x410400811311b25c 0x1800000018fff3e4 0x03000000031ffe7c

def z837 : W := mkw 0x0820444c9b9f9af1 0xc10408899373f35e 0x9801c3c47f9f9fff 0xd30038788ff3f3ff

def z838 : W := mkw 0x27dffbf760200504 0x04fbff7eec0400a0 0xffffffffe0e21fff 0xfffffffffc1c43ff

def z839 : W := mkw 0x000851c42020a5ac 0x20010a38840414b5 0x1819f30460e3fffd 0x43033e608c1c7fff

def z840 : W := mkw 0x27dffbf7600080a0 0x04fbff7eec001014 0xe7ffffffe00013e3 0xfcfffffffc00027c

def z841 : W := mkw 0x06f7a00816db4200 0x00def40102db6840 0xdffff0f81fffe385 0xfbfffe1f03fffc70

def z842 : W := mkw 0x134fafa80b3b5f06 0x0269f5f501676be0 0x2807fff8001fff83 0x0500ffff0003fff0

def z843 : W := mkw 0x15b80fa81de01f06 0x02b701f503bc03e0 0x67f80ff81fe01f82 0xacff01ff03fc03f0

def z844 : W := mkw 0x15b80fa81de01f06 0x02b701f503bc03e0 0xe7f80ff81fe00382 0xfcff01ff03fc0070

def z845 : W := mkw 0x15b80fa81de01f06 0x02b701f503bc03e0 0x77f80ff81f601f82 0x6eff01ff03ec03f0

def z846 : W := mkw 0x15b80faadde41f57 0x82b701f55bbc83ea 0xfff90fffffe21fff 0xffff21fffffc43ff

def z847 : W := mkw 0x03050e02cb161851 0x8060a1c05962c30a 0x3f070f07ff1e0c79 0x67e0e1e0ffe3c18f

def z848 : W := mkw 0x0862d45db88db2e9 0x610c5a8bb711b65d 0xe8e6fcff989df3e7 0xbd1cdf9ff313be7c

def z849 : W := mkw 0x27d7aa3340000000 0x04faf54668000000 0xfffffc3b80e3e005 0xffffff87701c7c00

def z850 : W := mkw 0x06fff1c436fbe5ac 0x20dffe3886df7cb5 0x47e603c47f1c1ffa 0x28fcc0788fe383ff

def z851 : W := mkw 0x102004089fff5f57 0x8204008113ffebea 0x180000001ffffffc 0x0300000003ffffff

def z852 : W := mkw 0x27dffbf760000000 0x04fbff7eec000000 0xffffffffe0020007 0xfffffffffc004000

def z853 : W := mkw 0x0000405500000000 0x0000080aa0000000 0xe0e00cff80000002 0xbc1c019ff0000000

def z854 : W := mkw 0x37dffbf765600d06 0x06fbff7eecac01a0 0xf7ffffffe7e01f87 0xfefffffffcfc03f0

def z855 : W := mkw 0x25dafbf760000000 0x04bb5f7eec000000 0xe0feffffe0000003 0xbc1fdffffc000000

def z856 : W := mkw 0x27d7aa3342120000 0x04faf54668424000 0x67e60c3b9f1c0000 0x2cfcc18773e38000

def z857 : W := mkw 0x15b81fa83de03f0e 0x22b703f507bc07e1 0xfff9fff87fe3ff9f 0xffff3fff0ffc7ff3

def z858 : W := mkw 0x03050e0acb161a51 0x8060a1c15962c34a 0xbf070fffff1e1fff 0x77e0e1ffffe3c3ff

def z859 : W := mkw 0x082004089bbfbffd 0xe10400811377f7ff 0x180000001ffffffc 0x0300000003ffffff

def z860 : W := mkw 0x03050e02cb161851 0x8060a1c05962c30a 0xbf1f3f07ff7e7c7f 0x77e3e7e0ffefcf8f

def z861 : W := mkw 0x0842c055800d80e1 0x4108580ab001b01c 0xe8e6ccff809d93e7 0xbd1cd99ff013b27c

def z862 : W := mkw 0x27dffbf760000000 0x04fbff7eec000000 0xf7ffffffff000007 0xfeffffffffe00000

def z863 : W := mkw 0x0842c055000980a0 0x4108580aa0013014 0xe0e6ccff80018003 0xbc1cd99ff0003000

def z864 : W := mkw 0x02678000129b0000 0x004cf00002536000 0xdffff0001fffe005 0xfbfffe0003fffc00

def z865 : W := mkw 0x0042801100000000 0x0008500220000000 0xe0e6cc3b80000001 0xbc1cd98770000000

def z866 : W := mkw 0x08200408988d1241 0x410400811311a248 0x00000000189c1384 0x0000000003138270

def z867 : W := mkw 0x0247c05500000000 0x0048f80aa0000000 0xe7e7ccff80000003 0xfcfcf99ff0000000

def z868 : W := mkw 0x06dff1d52020a5ac 0x20dbfe3aa40414b5 0xffffffffe0e3ffff 0xfffffffffc1c7fff

def z869 : W := mkw 0x27d7fa7760000000 0x04faff4eec000000 0xe7e7fcffe0000003 0xbcfcff9ffc000000

def z870 : W := mkw 0x0347ca5743120810 0x8068f94ae8624102 0xf7e7cfffe7020c1b 0xfefcf9fffce04183

def z871 : W := mkw 0x0862c05d908d82e1 0x410c580bb211b05c 0xe8e6ccff809d83e3 0xbd1cd99ff013b07c

def z872 : W := mkw 0x234ffbf760000000 0x0469ff7eec000000 0xe0e7ffffe0000003 0xbc1cfffffc000000

def z873 : W := mkw 0x14b805a81ce01706 0x029700b5039c02e0 0xf7f80cf81fe01386 0xfeff019f03fc0270

def z874 : W := mkw 0x15980fa809201f06 0x02b301f5012403e0 0xf7f80ff81f001f86 0xfeff01ff03e003f0

def z875 : W := mkw 0x27d7aa3340000000 0x04faf54668000000 0xe7e6cc3b80000001 0xbcfcd98770000000

def z876 : W := mkw 0x0a47d057e21fa0f9 0xe148fa0afc43f41f 0x0807f007e01fe079 0x0100fe00fc03fc0f

def z877 : W := mkw 0x07dfaba240000000 0x00fbf57448000000 0xe7ffffffe0000003 0xfcfffffffc000000

def z878 : W := mkw 0x15b81fa83de03f0e 0x22b703f507bc07e1 0xfff93ffc7fe27fff 0xffff27ff8ffc4fff

def z879 : W := mkw 0x15b80fa89de41f47 0x02b701f513bc83e8 0xfff80ff81ffc1fe6 0xffff01ff03ff83fc

def z880 : W := mkw 0x0820040898ad97e5 0x410400811315b2fc 0x1800000018fd9fe4 0x03000000031fb3fc

def z881 : W := mkw 0x182855ccbdedbfef 0x63050ab997bdb7fd 0x9819f3c47fffffff 0xd3033e788fffffff

def z882 : W := mkw 0x004ad1d520000000 0x00095a3aa4000000 0xe0e6cfffe0000003 0xbc1cd9fffc000000

def z883 : W := mkw 0x27dffbf761000800 0x04fbff7eec200100 0xf7ffffffe7000c03 0xfefffffffce00180

def z884 : W := mkw 0x27d7aa3340000000 0x04faf54668000000 0xe7e60f3b80000002 0x7cfcc1e770000000

def z885 : W := mkw 0x0142ca5500000000 0x0028594aa0000000 0xe7e6cfff80000003 0xfcfcd9fff0000000

def z886 : W := mkw 0x27dffbf761000810 0x84fbff7eec200102 0xe7ffffffe0000c1b 0xfcfffffffc000183

def z887 : W := mkw 0x27d7fa776000a0a8 0x24faff4eec001415 0x6fe7fc3fe003e079 0x2dfcff87fc007c0f

def z888 : W := mkw 0x27dffbf76020a5ac 0x24fbff7eec0414b5 0xffffffffe063ec7b 0xfffffffffc0c7d8f

def z889 : W := mkw 0x06f7a00016db4000 0x00def40002db6800 0xdffff3047fffe007 0xfbfffe608ffffc00

def z890 : W := mkw 0x06d7a000065b4000 0x00daf40000cb6800 0x9f1ff0001f7fe005 0x73e3fe0003effc00

def z891 : W := mkw 0x07dfebf500000000 0x00fbfd7ea0000000 0xe7ffffff80000003 0xfcfffffff0000000

def z892 : W := mkw 0x27dffbf760000000 0x04fbff7eec000000 0xe7e6cfffe0000003 0xbcfcd9fffc000000

def z893 : W := mkw 0x27dffbf760200504 0x04fbff7eec0400a0 0xe7ffffffe0001f83 0xfcfffffffc0003f0

def z894 : W := mkw 0x1cfad1fd34e9a7ae 0x639f5a3fa69d34f5 0x40f8f0f800e1e380 0x881f1e1f001c3c70

def z895 : W := mkw 0x27dffbf76332adbc 0xa4fbff7eec6655b7 0xffffffffe7e3ffff 0xfffffffffcfc7fff

def z896 : W := mkw 0x06d7e05506524000 0x00dafc0aa0ca4800 0xf7fffcff87626003 0xfeffff9ff0ec4c00

def z897 : W := mkw 0x224ff1d76020a5ac 0x2449fe3aec0414b5 0xf8ffffffe0e3ffff 0xff1ffffffc1c7fff

def z898 : W := mkw 0x15b80faadde41f57 0x82b701f55bbc83ea 0xf7f80ffb9fe01f86 0xfeff01ff73fc03f0

def z899 : W := mkw 0x2a47f057e21fc0e1 0x4548fe0afc43f81c 0x0807f007e01fe061 0x0100fe00fc03fc0c

def z900 : W := mkw 0x15b81fa83de03f0e 0x22b703f507bc07e1 0xf7f80ff87fe01f9e 0xfeff01ff0ffc03f3

def z901 : W := mkw 0x15b80fa89de41f47 0x02b701f513bc83e8 0xffff0ffffffe1fff 0xffffe1ffffffc3ff

def z902 : W := mkw 0x002004089b961a51 0x800400811372c34a 0x180000001f9e1ffc 0x0300000003f3c3ff

def z903 : W := mkw 0x0020040818801200 0x0004008103100240 0xf7e00cf81f801386 0xfefc019f03f00270

def z904 : W := mkw 0x0020040898841241 0x0004008113108248 0xe0e60cfb989c1386 0xbc1cc19f73138270

def z905 : W := mkw 0x0042c05500000000 0x0008580aa0000000 0xe8e6ccff981c0007 0xbd1cd99ff3038000

def z906 : W := mkw 0x27dffbf76020250c 0x24fbff7eec0404a1 0xffffffffe0627c7f 0xfffffffffc0c4f8f

def z907 : W := mkw 0x0020444c988492e1 0x000408899310925c 0xe8e6ccff989d93e7 0xbd1cd99ff313b27c

def z908 : W := mkw 0x14b801a814e00706 0x02970035029c00e0 0x57f800f807e00380 0xcaff001f00fc0070

def z909 : W := mkw 0x03050e02cb161851 0x8060a1c05962c30a 0xbf07ff07ff1ffc7f 0x77e0ffe0ffe3ff8f

def z910 : W := mkw 0x08200408988492e1 0x410400811310925c 0x00000000188013e4 0x000000000310027c

def z911 : W := mkw 0x27dffbf760000000 0x04fbff7eec000000 0xe7ffffffe0001c7b 0xfcfffffffc00038f

def z912 : W := mkw 0x03050e02cb161851 0x8060a1c05962c30a 0xbf070fc7ff9e1fff 0xf7e0e1f8fff3c3ff

def z913 : W := mkw 0x0042c05500000000 0x0008580aa0000000 0x60e0ccff80000002 0x8c1c199ff0000000

def z914 : W := mkw 0x03050e02cb161851 0x8060a1c05962c30a 0xb7060f07ff1c1c7e 0x76e0c1e0ffe3838f

def z915 : W := mkw 0x082004089a9fd2e1 0x410400811353fa5c 0x08000000189ff3e4 0x010000000313fe7c

def z916 : W := mkw 0x27dffbf760000000 0x04fbff7eec000000 0xeffffffff81c0007 0xfdffffffff038000

def z917 : W := mkw 0x25dafbf76020a5ac 0x24bb5f7eec0414b5 0xf8f9ffffe0e3ffff 0xdf1f3ffffc1c7fff

def z918 : W := mkw 0x27d7aa3340000000 0x04faf54668000000 0xe7fe0c3b80000000 0xfcffc18770000000

def z919 : W := mkw 0x15b81fa83de03f0e 0x22b703f507bc07e1 0xf7f83ff81fe07f86 0xfeff07ff03fc0ff0

def z920 : W := mkw 0x27d7fa7760000000 0x04faff4eec000000 0xe7e7ff3fe0000003 0x7cfcffe7fc000000

def z921 : W := mkw 0x05980ba240000000 0x00b3017448000000 0xe7f80fffe0000002 0xfcff01fffc000000

def z922 : W := mkw 0x27dffbf763120810 0x84fbff7eec624102 0xffffffffe7021c7f 0xfffffffffce0438f

def z923 : W := mkw 0x08628419988d1241 0x410c50833311a248 0xe8e6ccfb989d9387 0xbd1cd99f7313b270

def z924 : W := mkw 0x0062c055108980a0 0x000c580aa2113014 0xe8e6ccff989d93e7 0xbd1cd99ff313b27c

def z925 : W := mkw 0x27dffbf762124000 0x04fbff7eec424800 0xe7ffffffe0026003 0xfcfffffffc004c00

def z926 : W := mkw 0x0862c45d988d92e1 0x410c588bb311b25c 0xe8fffcff989d93e7 0xfd1fff9ff313b27c

def z927 : W := mkw 0x27dffbf76000a0a8 0x24fbff7eec001415 0xefffffffe083f3ff 0xfdfffffffc107e7f

def z928 : W := mkw 0x27d7aa33421b4000 0x04faf54668436800 0x6fe7fc3b801fe001 0x2dfcff877003fc00

def z929 : W := mkw 0x0062c45d18891200 0x000c588ba3112240 0xe8e6ccff989d9387 0xbd1cd99ff313b270

def z930 : W := mkw 0x08628408988d92e1 0x410c50811311b25c 0x0806c000189d93e5 0x0100d8000313b27c

def z931 : W := mkw 0x0225040ada961251 0x8044a0815b52c24a 0xe8e70cfff89e13ff 0xbd1ce19fff13c27f

def z932 : W := mkw 0x15b80fa81de01f06 0x02b701f503bc03e0 0x67e00cf81f000380 0x2cfc019f03e00070

def z933 : W := mkw 0x15b80fa89de41f47 0x02b701f513bc83e8 0xf7fe0ffb9ffc1f86 0xfeffc1ff73ff83f0

def z934 : W := mkw 0x0862c45d988d92e1 0x410c588bb311b25c 0xe8e7fcff989ff3e7 0xbd1cff9ff313fe7c

def z935 : W := mkw 0x27d7ea77400080a0 0x04fafd4ee8001014 0xefe6ccff808193e7 0xbdfcd99ff010327c

def z936 : W := mkw 0x102855ccbff6bfff 0xa2050ab997fed7ff 0x9819f3c47fffffff 0xd3033e788fffffff

def z937 : W := mkw 0x27dfabb340000000 0x04fbf57668000000 0x67e60ffb80000002 0x2cfcc1ff70000000

def z938 : W := mkw 0x05980fa009201d04 0x00b301f4012403a0 0xf7f80ff81fe01f86 0xfeff01ff03fc03f0

def z939 : W := mkw 0x21428a3340000000 0x0428514668000000 0x60e60c3b80000000 0x2c1cc18770000000

def z940 : W := mkw 0x2862f45db88d92e1 0x450c5e8bb711b25c 0xe8e6fcff989d93e7 0xbd1cdf9ff313b27c

def z941 : W := mkw 0x0042c05500000000 0x0008580aa0000000 0x60e6cc3f80000001 0x2c1cd987f0000000

def z942 : W := mkw 0x06d7a01100000000 0x00daf40220000000 0x67e60c3b80000000 0x2cfcc18770000000

def z943 : W := mkw 0x03050e02cb161851 0x8060a1c05962c30a 0xaf060f07ff1c1c7f 0x35e0c1e0ffe3838f

def z944 : W := mkw 0x06f7a00016db4000 0x00def40002db6800 0x1f1ff0001fffe005 0x43e3fe0003fffc00

def z945 : W := mkw 0x0862c05d108982a0 0x410c580ba2113054 0xe8e6ccff989d8387 0xbd1cd99ff313b070

def z946 : W := mkw 0x27dffbf7600080a0 0x04fbff7eec001014 0xffffffffe0839fff 0xfffffffffc1073ff

def z947 : W := mkw 0x16f7a02816db4202 0x02def40502db6840 0xdffff0381fffe005 0xfbfffe0703fffc00

def z948 : W := mkw 0x0862c45d988d92e1 0x410c588bb311b25c 0x68e6ccfb989d93e4 0xad1cd99f7313b27c

def z949 : W := mkw 0x0862c45d988d92e1 0x410c588bb311b25c 0xe8e60cff981c13e7 0x3d1cc19ff303827c

def z950 : W := mkw 0x2347fa5760000000 0x0468ff4aec000000 0xe7e7ffffe0000003 0xfcfcfffffc000000

def z951 : W := mkw 0x27d7aa3340000000 0x04faf54668000000 0x67e7fc3b80000001 0x2cfcff8770000000

def z952 : W := mkw 0x214adbf760000000 0x04295b7eec000000 0x60e60fffe0000002 0x2c1cc1fffc000000

def z953 : W := mkw 0x11200e081de01f06 0x022401c103bc03e0 0xf7e00ff81fe01f86 0xfefc01ff03fc03f0

def z954 : W := mkw 0x25dafbf520000000 0x04bb5f7ea4000000 0xe7feffff80000003 0xfcffdffff0000000

def z955 : W := mkw 0x37dffbf761200d06 0x06fbff7eec2401a0 0xe7ffffffe0000c03 0xfcfffffffc000180

def z956 : W := mkw 0x27dffbf76020a5ac 0x24fbff7eec0414b5 0xefffffffe003fffb 0xfdfffffffc007fff

def z957 : W := mkw 0x279d3ba260000000 0x04f3a7744c000000 0xe7ff3fffe0000003 0xfcffe7fffc000000

def z958 : W := mkw 0x27dfabb340000000 0x04fbf57668000000 0xe7fffffb80000003 0xfcffffff70000000

def z959 : W := mkw 0x0b250e0adb9f9af1 0xc164a1c15b73f35e 0x1f0103007f9f9ffc 0x43e020600ff3f3ff

def z960 : W := mkw 0x08200408988d92e1 0x410400811311b25c 0x08000000181d8060 0x010000000303b00c

def z961 : W := mkw 0x06f7a00256db4000 0x00def4004adb6800 0xdffff007ffffe005 0xfbfffe00fffffc00

def z962 : W := mkw 0x27dfabb340000000 0x04fbf57668000000 0x67fe0cfb80000000 0xacffc19f70000000

def z963 : W := mkw 0x27dffbf760000000 0x04fbff7eec000000 0x67e7ffffe0000003 0x2cfcfffffc000000

def z964 : W := mkw 0x15b00e281dc01a02 0x02b601c503b80340 0x67e00cf81f800380 0xacfc019f03f00070

def z965 : W := mkw 0x0eb524089edfd2e1 0x41d6a48113dbfa5c 0x1f1930001ffff3e4 0x43e3260003fffe7c

def z966 : W := mkw 0x000851d52020a5ac 0x20010a3aa40414b5 0xb819ffffe0e3ffff 0xd7033ffffc1c7fff

def z967 : W := mkw 0x27d7ea7740000000 0x04fafd4ee8000000 0x67e60cff80000002 0x2cfcc19ff0000000

def z968 : W := mkw 0x179d0ba247720d16 0x82f3a17448ee41a2 0x1718030007600c00 0x42e3006000ec0180

def z969 : W := mkw 0x03050a0242120000 0x0060a14048424000 0xbf070f07ff1e1c7f 0x77e0e1e0ffe3c38f

def z970 : W := mkw 0x14b004081de01f06 0x0296008103bc03e0 0xf7f80cf81fe01f86 0xfeff019f03fc03f0

def z971 : W := mkw 0x27dffbf76020a5ac 0x24fbff7eec0414b5 0xefffffffe0819fff 0xfdfffffffc1033ff

def z972 : W := mkw 0x01280f8819a01f04 0x002501f1033403e0 0xf7f80ff81fe01f86 0xfeff01ff03fc03f0

def z973 : W := mkw 0x0820040898adb7ed 0x610400811315b6fd 0x0800000018fdf3e4 0x01000000031fbe7c

def z974 : W := mkw 0x27d7aa3340000000 0x04faf54668000000 0x67e70f3be0000000 0x6cfce1e77c000000

def z975 : W := mkw 0x27dffbf760000000 0x04fbff7eec000000 0xefffffffe002007b 0xfdfffffffc00400f

def z976 : W := mkw 0x15b80fa81de01f06 0x02b701f503bc03e0 0xfff8cff81fe19f87 0xffff19ff03fc33f0

def z977 : W := mkw 0x0828058898ad97e5 0x410500b11315b2fc 0x981803c018fd9fe6 0xd3030078031fb3fc

def z978 : W := mkw 0x2a47f057e21f80f1 0xc548fe0afc43f01e 0x0807f007e01f8079 0x0100fe00fc03f00f

def z979 : W := mkw 0x214adbf760000000 0x04295b7eec000000 0xe0ffffffe0000003 0xfc1ffffffc000000

def z980 : W := mkw 0x05984bf500000000 0x00b3097ea0000000 0xe7f80fff80000002 0xfcff01fff0000000

def z981 : W := mkw 0x0862c45d988d92e1 0x410c588bb311b25c 0xffe6ccff9f9d93e7 0xfffcd99ff3f3b27c

def z982 : W := mkw 0x07dfcbf740000000 0x00fbf97ee8000000 0xe7ffcfffe0000003 0xfcfff9fffc000000

def z983 : W := mkw 0x004ac1d500200504 0x0009583aa00400a0 0xf0fecfff80e01f87 0xfe1fd9fff01c03f0

def z984 : W := mkw 0x15b80ba815e00f06 0x02b7017502bc01e0 0xd7f803f81fe00f84 0xfaff007f03fc01f0

def z985 : W := mkw 0x0862c45d998d9ae1 0x410c588bb331b35c 0xf8e6ccff9f9d9fe7 0xbf1cd99ff3f3b3fc

def z986 : W := mkw 0x27d7aa3340000000 0x04faf54668000000 0x67ff3c3b80000000 0x6cffe78770000000

def z987 : W := mkw 0x21085bf760000000 0x04210b7eec000000 0xe0e00fffe0000002 0xbc1c01fffc000000

def z988 : W := mkw 0x15b80fa81de01f06 0x02b701f503bc03e0 0xfff80ffc1fe01fe7 0xffff01ff83fc03fc

def z989 : W := mkw 0x0a47c057c21f80f1 0xc148f80af843f01e 0x0806c007801d8061 0x0100d800f003b00c

def z990 : W := mkw 0x0042c05500000000 0x0008580aa0000000 0xe0e6ccff80801387 0xbc1cd99ff0100270

def z991 : W := mkw 0x2fdffbf7600980a0 0x45fbff7eec013014 0xe7ffffffe0018003 0xfcfffffffc003000

def z992 : W := mkw 0x37dffbf765400802 0x06fbff7eeca80100 0xe7ffffffe7000003 0xfcfffffffce00000

def z993 : W := mkw 0x0347ca57400080a0 0x0068f94ae8001014 0xffe7cfffe0839fff 0xfffcf9fffc1073ff

def z994 : W := mkw 0x27dffbf760094000 0x04fbff7eec012800 0xe7ffffffe001e003 0xfcfffffffc003c00

def z995 : W := mkw 0x04d2c05500000000 0x009a580aa0000000 0xe7feccff80000003 0xfcffd99ff0000000

def z996 : W := mkw 0x0862d45db88db2e9 0x610c5a8bb711b65d 0xf8fffcfff8fff3ff 0xff1fff9fff1ffe7f

def z997 : W := mkw 0x1820040899ad9fe7 0x430400811335b3fc 0x08000000189d9fe4 0x010000000313b3fc

def z998 : W := mkw 0x27dffbf76000a0a8 0x24fbff7eec001415 0xffffffffe003fc7f 0xfffffffffc007f8f

def z999 : W := mkw 0x082855ccbefff7ed 0x61050ab997dffefd 0x9819f3c47fffffff 0xd3033e788fffffff

def z1000 : W := mkw 0x27dffbf760000000 0x04fbff7eec000000 0x67fffcffe0000001 0xacffff9ffc000000

def z1001 : W := mkw 0x102004089ff61f57 0x8204008113fec3ea 0x100000001ffc1f84 0x0200000003ff83f0

def z1002 : W := mkw 0x27d7ea7740000000 0x04fafd4ee8000000 0xe7fffcff80000003 0xfcffff9ff0000000

def z1003 : W := mkw 0x24daf1f520000000 0x049b5e3ea4000000 0x60fefcfb80000000 0xac1fdf9f70000000

def z1004 : W := mkw 0x179d1ba267722d1e 0xa2f3a3744cee45a3 0x1719330067626c18 0x42e326600cec4d83

def z1005 : W := mkw 0x279d3ba263322d1c 0xa4f3a7744c6645a3 0x1719330067626c18 0x42e326600cec4d83

def z1006 : W := mkw 0x15b80fa81de01f06 0x02b701f503bc03e0 0xf7e00ff81f001f86 0x7efc01ff03e003f0

def z1007 : W := mkw 0x15b80fa81de01f06 0x02b701f503bc03e0 0xe7e00ff81f801f86 0xbcfc01ff03f003f0

def z1008 : W := mkw 0x25dadbf760000000 0x04bb5b7eec000000 0xe7fecfffe0000003 0xfcffd9fffc000000

def z1009 : W := mkw 0x27d7ba3360000000 0x04faf7466c000000 0x67e73c3be0000000 0x2cfce7877c000000

def z1010 : W := mkw 0x082004089b9f9af1 0xc10400811373f35e 0x080000001f9d93e4 0x0100000003f3b27c

def z1011 : W := mkw 0x08628419988d92e1 0x410c50833311b25c 0xe8e60cfb989d93e6 0xbd1cc19f7313b27c

def z1012 : W := mkw 0x27dffbf762120000 0x04fbff7eec424000 0xf7ffffffe7020003 0xfefffffffce04000

def z1013 : W := mkw 0x0042c05500000000 0x0008580aa0000000 0xf8e7cfffe0021c7f 0xff1cf9fffc00438f

def z1014 : W := mkw 0x08200408988d92e1 0x410400811311b25c 0x98010304789f9fff 0x530020608f13f3ff

def z1015 : W := mkw 0x15b80faa5de01f16 0x82b701f54bbc03e2 0xf7f80ff87fe01f9e 0xfeff01ff0ffc03f3

def z1016 : W := mkw 0x27dffbf762120010 0x84fbff7eec424002 0xe7ffffffe002001b 0xfcfffffffc004003

def z1017 : W := mkw 0x27d7ea7740000000 0x04fafd4ee8000000 0x67e6cc3f80000001 0x2cfcd987f0000000

def z1018 : W := mkw 0x27dfabb340000000 0x04fbf57668000000 0x67fe0f3b80000000 0x6cffc1e770000000

def z1019 : W := mkw 0x27dffbf766524000 0x04fbff7eecca4800 0xe7ffffffe7000003 0xfcfffffffce00000

def z1020 : W := mkw 0x000000000020a5ac 0x20000000000414b5 0x9819f30460e3ffff 0xd3033e608c1c7fff

def z1021 : W := mkw 0x000851c42020a5ac 0x20010a38840414b5 0x1819f3c060e3fffc 0xc3033e780c1c7fff

def z1022 : W := mkw 0x15b80fa81de01f06 0x02b701f503bc03e0 0xe7f80cf81fe01386 0xbcff019f03fc0270

def z1023 : W := mkw 0x234fdbf760000000 0x0469fb7eec000000 0xe7e7cfffe0000003 0xfcfcf9fffc000000

def z1024 : W := mkw 0x0247e05500000000 0x0048fc0aa0000000 0xe0e7fcff80000003 0xbc1cff9ff0000000

def z1025 : W := mkw 0x03050e02cb161851 0x8060a1c05962c30a 0x37070f07ff1e1c7a 0x66e0e1e0ffe3c38f

def z1026 : W := mkw 0x0862c45d988d92e1 0x410c588bb311b25c 0x68e6ccff981d93e3 0x2d1cd99ff303b27c

def z1027 : W := mkw 0x0a2504089a9f92e1 0x4144a0811353f25c 0x9f0700001f9f93e5 0x73e0e00003f3f27c

def z1028 : W := mkw 0x0862c45d988d92e1 0x410c588bb311b25c 0x68e6ccff989d83e1 0xad1cd99ff313b07c

def z1029 : W := mkw 0x06f7a00016db4000 0x00def40002db6800 0xdffff0047fffe07d 0xfbfffe008ffffc0f

def z1030 : W := mkw 0x27dffbf76020a5ac 0x24fbff7eec0414b5 0x67fefcfb80e1e380 0xacffdf9f701c3c70

def z1031 : W := mkw 0x09085fdfe924bffd 0xe1210bfbfd2497ff 0x20000fffe0001ffa 0x040001fffc0003ff

def z1032 : W := mkw 0x034fdbd760000000 0x0069fb7aec000000 0xe7ffffffe0000003 0xfcfffffffc000000

def z1033 : W := mkw 0x27dfbbb360000000 0x04fbf7766c000000 0xe7ff3ffbe0000002 0xfcffe7ff7c000000

def z1034 : W := mkw 0x0862c45d988d92e1 0x410c588bb311b25c 0x0800c000189d93e4 0x010018000313b27c

def z1035 : W := mkw 0x15b80faa5de01f06 0x02b701f54bbc03e0 0xf7f80fffffe01f86 0xfeff01fffffc03f0

def z1036 : W := mkw 0x05b80fa819801a00 0x00b701f503300340 0xf7f80ff81f801f86 0xfeff01ff03f003f0

def z1037 : W := mkw 0x27dffbf763322d1c 0xa4fbff7eec6645a3 0xf7ffffffe7626c1b 0xfefffffffcec4d83

def z1038 : W := mkw 0x24d2e07500000000 0x049a5c0ea0000000 0xe0e6ccff80000003 0xbc1cd99ff0000000

def z1039 : W := mkw 0x27dfebf740000000 0x04fbfd7ee8000000 0xe7fecfff80000003 0xfcffd9fff0000000

def z1040 : W := mkw 0x004ac1d500000000 0x0009583aa0000000 0xe0fecfff80000003 0xfc1fd9fff0000000

def z1041 : W := mkw 0x0862c45d988d92e1 0x410c588bb311b25c 0xe0e6ccfb989d9386 0xbc1cd99f7313b270

def z1042 : W := mkw 0x082004089b9f1a51 0xc10400811373e34a 0x000000001f1c0000 0x0000000003e38000

def z1043 : W := mkw 0x27dffbf766524000 0x04fbff7eecca4800 0xffffffffff7e6007 0xffffffffffefcc00

def z1044 : W := mkw 0x27dfbbb360000000 0x04fbf7766c000000 0x67e60f3be0000000 0x2cfcc1e77c000000

def z1045 : W := mkw 0x0a47c055821f80e1 0x4148f80ab043f01c 0x0807c007801f8061 0x0100f800f003f00c

def z1046 : W := mkw 0x06f7a00016db4000 0x00def40002db6800 0xcffef0001ffde005 0xb9ffde0003ffbc00

def z1047 : W := mkw 0x27dfbbb36020250c 0x24fbf7766c0404a1 0x77ff3f3be0626c18 0x6effe7e77c0c4d83

def z1048 : W := mkw 0x0820040898adb7ed 0x610400811315b6fd 0x08000000189d9ffc 0x010000000313b3ff

def z1049 : W := mkw 0x182004089dcd9ae3 0x4304008113b9b35c 0x080000001f9d93e4 0x0100000003f3b27c

def z1050 : W := mkw 0x0042c0550020a5ac 0x2008580aa00414b5 0xf8e6ccff80e3ffff 0xbf1cd99ff01c7fff

def z1051 : W := mkw 0x27dfbbb360000000 0x04fbf7766c000000 0x67fe3c3b80000000 0x2cffc78770000000

def z1052 : W := mkw 0x25dafbf760000000 0x04bb5f7eec000000 0xe7f8ffffe0000002 0xfcff1ffffc000000

def z1053 : W := mkw 0x0042c05500090000 0x0008580aa0012000 0xe8e6ccff801d8003 0xbd1cd99ff003b000

def z1054 : W := mkw 0x0347ca5740000000 0x0068f94ae8000000 0xe7e6ccff80000003 0xbcfcd99ff0000000

def z1055 : W := mkw 0x15b80fa81de01f06 0x02b701f503bc03e0 0xe7f80ff81f001f82 0xfcff01ff03e003f0

def z1056 : W := mkw 0x082004089b9f1a51 0xc10400811373e34a 0x180000001f1e1c7c 0x0300000003e3c38f

def z1057 : W := mkw 0x15b80fa81de01f06 0x02b701f503bc03e0 0xf7f90ff87fe21f9e 0xfeff21ff0ffc43f3

def z1058 : W := mkw 0x27dffbf760000000 0x04fbff7eec000000 0x67ffff3fe0000001 0x6cffffe7fc000000

def z1059 : W := mkw 0x0247c05502120000 0x0048f80aa0424000 0xffe7ccff9f1e0007 0xfffcf99ff3e3c000

def z1060 : W := mkw 0x06f7a00016db4000 0x00def40002db6800 0x5ffef0001fffe004 0xabffde0003fffc00

def z1061 : W := mkw 0x15b00e281dc01a02 0x02b601c503b80340 0xf7e00ff81f801f86 0xfefc01ff03f003f0

def z1062 : W := mkw 0x27dffbf7621be0a8 0x24fbff7eec437c15 0xefffffffe01fe07b 0xfdfffffffc03fc0f

def z1063 : W := mkw 0x24faf1f534e9e5ac 0x249f5e3ea69d3cb5 0x40f8f0f800e1e380 0x881f1e1f001c3c70

def z1064 : W := mkw 0x27dffbf7600080a0 0x04fbff7eec001014 0xffffffffe0e3f3e7 0xfffffffffc1c7e7c

def z1065 : W := mkw 0x27dffbf760000000 0x04fbff7eec000000 0xe7fefcff80000003 0xbcffdf9ff0000000

def z1066 : W := mkw 0x0862c45d988d92e1 0x410c588bb311b25c 0xf8feccff98fd93e7 0xff1fd99ff31fb27c

def z1067 : W := mkw 0x0042801100000000 0x0008500220000000 0xe0e60cfb80000002 0xbc1cc19f70000000

def z1068 : W := mkw 0x06d7e055000080a0 0x00dafc0aa0001014 0xfffffcff80e3f3e7 0xffffff9ff01c7e7c

def z1069 : W := mkw 0x27dffbf762120000 0x04fbff7eec424000 0xefffffffe01e0003 0xfdfffffffc03c000

def z1070 : W := mkw 0x0042c055000080a0 0x0008580aa0001014 0xe0e6ccff80818383 0xbc1cd99ff0103070

def z1071 : W := mkw 0x03050e02cb161851 0x8060a1c05962c30a 0x2f070f07ff1e1c7b 0x25e0e1e0ffe3c38f

def z1072 : W := mkw 0x27dfbbb360000000 0x04fbf7766c000000 0xe7ffff3be0000001 0xfcffffe77c000000

def z1073 : W := mkw 0x15b00e281dc01a02 0x02b601c503b80340 0xf7f80cf81fe01386 0xfeff019f03fc0270

def z1074 : W := mkw 0x27dffbf76020a5ac 0x24fbff7eec0414b5 0xf7ffffffe0e3ef9b 0xfefffffffc1c7df3

def z1075 : W := mkw 0x27dffbf76020a5ac 0x24fbff7eec0414b5 0xe7ffffffe0000383 0xfcfffffffc000070

def z1076 : W := mkw 0x0862c45d988d92e1 0x410c588bb311b25c 0xf8e6ccff98fff3e7 0xbf1cd99ff31ffe7c

def z1077 : W := mkw 0x0042c05500000000 0x0008580aa0000000 0xf8fffcff80e3e007 0xff1fff9ff01c7c00

def z1078 : W := mkw 0x27dffbf760002008 0x24fbff7eec000401 0xe7ffffffe002601b 0xfcfffffffc004c03

def z1079 : W := mkw 0x07950a2240000000 0x00f2a14448000000 0x67e60c3b80000000 0x2cfcc18770000000

def z1080 : W := mkw 0x06f7a00016db4000 0x00def40002db6800 0x4ffff0001fffe001 0xa9fffe0003fffc00

def z1081 : W := mkw 0x27dffbf762120000 0x04fbff7eec424000 0xe7ffffffff1c0003 0xfcffffffffe38000

def z1082 : W := mkw 0x06f7a00016db4000 0x00def40002db6800 0xdffff0c01ffff387 0xfbfffe1803fffe70

def z1083 : W := mkw 0x27dffbf7623be5ac 0x24fbff7eec477cb5 0xffffffffe0ffffff 0xfffffffffc1fffff

def z1084 : W := mkw 0x27dffbf760000000 0x04fbff7eec000000 0x67e60cfb80000000 0x2cfcc19f70000000

def z1085 : W := mkw 0x27d7fa7760000000 0x04faff4eec000000 0x67e60c3fe0000000 0x2cfcc187fc000000

def z1086 : W := mkw 0x08200408988d92e1 0x410400811311b25c 0x9819f00018fff3e5 0xd3033e00031ffe7c

def z1087 : W := mkw 0x079d0ba240200504 0x00f3a174480400a0 0xffff0fffe0e21fff 0xffffe1fffc1c43ff

def z1088 : W := mkw 0x00628408988d1241 0x000c50811311a248 0xe8e6ccff989d93e7 0xbd1cd99ff313b27c

def z1089 : W := mkw 0x214adbf76020a5ac 0x24295b7eec0414b5 0xf8ffffffe0e3ffff 0xff1ffffffc1c7fff

def z1090 : W := mkw 0x000851c42020a5ac 0x20010a38840414b5 0x981ff3c478ffffff 0xf303fe788f1fffff

def z1091 : W := mkw 0x0862c45d988d92e1 0x410c588bb311b25c 0x60e60cfb981c0380 0x2c1cc19f73038070

def z1092 : W := mkw 0x27dffbf76020250c 0x24fbff7eec0404a1 0xf7ffffffe0e27f9f 0xfefffffffc1c4ff3

def z1093 : W := mkw 0x27dffbf760000000 0x04fbff7eec000000 0xefffffffe003e003 0xfdfffffffc007c00

def z1094 : W := mkw 0x27dffbf76000a0a8 0x24fbff7eec001415 0xe7ffffffe000007b 0xfcfffffffc00000f

def z1095 : W := mkw 0x04b004081cc01200 0x0096008103980240 0xe7e00cf81f801386 0xbcfc019f03f00270

def z1096 : W := mkw 0x25900a3340000000 0x04b2014668000000 0x67e00c3b80000000 0x2cfc018770000000

def z1097 : W := mkw 0x000851c42020a5ac 0x20010a38840414b5 0xb81fffc7e0e3ffff 0xf703fff8fc1c7fff

def z1098 : W := mkw 0x04f2a00016db4000 0x009e540002db6800 0xdff8f0001fffe004 0xfbff1e0003fffc00

def z1099 : W := mkw 0x37dffbf767724d06 0x06fbff7eecee49a0 0xf7ffffffe7626c03 0xfefffffffcec4d80

def z1100 : W := mkw 0x03050e02cb161851 0x8060a1c05962c30a 0x1f070307ff1e1c7d 0x43e0e060ffe3c38f

def z1101 : W := mkw 0x27dffbf760000000 0x04fbff7eec000000 0xe7fe0fffe0000002 0xfcffc1fffc000000

def z1102 : W := mkw 0x27dffbf76020a5ac 0x24fbff7eec0414b5 0xefffffffe0e1f3e7 0xfdfffffffc1c3e7c

def z1103 : W := mkw 0x004ad1d52020a5ac 0x20095a3aa40414b5 0xe0e6cfffe0001ffb 0xbc1cd9fffc0003ff

def z1104 : W := mkw 0x37dffbf76560adae 0x26fbff7eecac15b5 0xffffffffe7e3ffff 0xfffffffffcfc7fff

def z1105 : W := mkw 0x27dffbf760000000 0x04fbff7eec000000 0xf7ffffffe0020c1b 0xfefffffffc004183

def z1106 : W := mkw 0x08200408988d1241 0x410400811311a248 0x08000000189d8004 0x010000000313b000

def z1107 : W := mkw 0x08200408988d92e1 0x410400811311b25c 0x88060000189d93e5 0x3100c0000313b27c

def z1108 : W := mkw 0x03050e02cb161851 0x8060a1c05962c30a 0xbf070f07fffffc7f 0x77e0e1e0ffffff8f

def z1109 : W := mkw 0x25980bb340000000 0x04b3017668000000 0xe7f80ffb80000002 0xfcff01ff70000000

def z1110 : W := mkw 0x27d7aa3342120000 0x04faf54668424000 0xffe70c3b9f1e0005 0x7ffce18773e3c000

def z1111 : W := mkw 0x27dffbf760200504 0x04fbff7eec0400a0 0xffffffffe0e3ff87 0xfffffffffc1c7ff0

def z1112 : W := mkw 0x27dffbf76020a5ac 0x24fbff7eec0414b5 0xf7ffffffe0e01fff 0xfefffffffc1c03ff

def z1113 : W := mkw 0x27dffbf760000000 0x04fbff7eec000000 0xe7fffcfb80000001 0xfcffff9f70000000

def z1114 : W := mkw 0x082004089efff7ed 0x6104008113dffefd 0x180000001ffffffc 0x0300000003ffffff

def z1115 : W := mkw 0x27dffbf7600080a0 0x04fbff7eec001014 0xefffffffe0018063 0xfdfffffffc00300c

def z1116 : W := mkw 0x082855ccb8adb7ed 0x61050ab99715b6fd 0x080003c4789d9ffe 0x010000788f13b3ff

def z1117 : W := mkw 0x25985bf760000000 0x04b30b7eec000000 0x67e00fffe0000002 0x2cfc01fffc000000

def z1118 : W := mkw 0x0842c45d880d92e1 0x4108588bb101b25c 0xe8e6ccff801d93e3 0xbd1cd99ff003b27c

def z1119 : W := mkw 0x05dadbf52020a5ac 0x20bb5b7ea40414b5 0xffffffffe0e3ffff 0xfffffffffc1c7fff

def z1120 : W := mkw 0x0862c45d988d92e1 0x410c588bb311b25c 0xe0e6ccff989d8383 0xbc1cd99ff313b070

def z1121 : W := mkw 0x27d7aa3340000000 0x04faf54668000000 0xffe70f3fe0021c7f 0x7ffce1e7fc00438f

def z1122 : W := mkw 0x11085feee924bfff 0xa2210bfddd2497ff 0x20000fffe0001ffa 0x040001fffc0003ff

def z1123 : W := mkw 0x27dffbf760000000 0x04fbff7eec000000 0xefffffffe0818007 0xfdfffffffc103000

def z1124 : W := mkw 0x27d7fa7760000000 0x04faff4eec000000 0xe7fffc3fe0000001 0xfcffff87fc000000

def z1125 : W := mkw 0x0862d45db88db2e9 0x610c5a8bb711b65d 0xe8e6ccfff89d93ff 0xbd1cd99fff13b27f

def z1126 : W := mkw 0x27dffbf76672e5ac 0x24fbff7eecce5cb5 0xffffffffe7e3ffff 0xfffffffffcfc7fff

def z1127 : W := mkw 0x2247f0576000a0a8 0x2448fe0aec001415 0xe8e7fcffe083f3ff 0xbd1cff9ffc107e7f

def z1128 : W := mkw 0x06f7a00016db4000 0x00def40002db6800 0xfffffcf81fffe007 0xffffff9f03fffc00

def z1129 : W := mkw 0x0862c45d988d92e1 0x410c588bb311b25c 0x68e6ccff809d93e3 0x8d1cd99ff013b27c

def z1130 : W := mkw 0x15b80fa89de41f57 0x82b701f513bc83ea 0xf7f80ff81fe01ffe 0xfeff01ff03fc03ff

def z1131 : W := mkw 0x01000e02c9041851 0x802001c05920830a 0xbf060f07ff1c1c7f 0x77e0c1e0ffe3838f

def z1132 : W := mkw 0x0247e055021b4000 0x0048fc0aa0436800 0xe8e7fcff801fe003 0xbd1cff9ff003fc00

def z1133 : W := mkw 0x27dffbf760000000 0x04fbff7eec000000 0xffffffffe0e3fc7f 0xfffffffffc1c7f8f

def z1134 : W := mkw 0x27dffbf7602085a4 0x04fbff7eec0410b4 0xffffffffe0e19fe7 0xfffffffffc1c33fc

def z1135 : W := mkw 0x27dffbf760000000 0x04fbff7eec000000 0xefffffffe0001067 0xfdfffffffc00020c

def z1136 : W := mkw 0x27dffbf76020a5ac 0x24fbff7eec0414b5 0x67e60fffe0001ffa 0x2cfcc1fffc0003ff

def z1137 : W := mkw 0x0862c45d988d92e1 0x410c588bb311b25c 0xf8e6ccff989f9fff 0xbf1cd99ff313f3ff

def z1138 : W := mkw 0x27dffbf76020250c 0x24fbff7eec0404a1 0xe7ffffffe0000c1b 0xfcfffffffc000183

def z1139 : W := mkw 0x05da8bb100000000 0x00bb517620000000 0xe7fe0ffb80000002 0xfcffc1ff70000000

def z1140 : W := mkw 0x182004089fffdfe7 0x4304008113fffbfc 0x180000001fffffe4 0x0300000003fffffc

def z1141 : W := mkw 0x0cfaf1dd34e9e7ac 0x619f5e3ba69d3cf5 0x40f8f0f800e1e380 0x881f1e1f001c3c70

def z1142 : W := mkw 0x15b80fa81de01f06 0x02b701f503bc03e0 0x77f80ff807e01f82 0xceff01ff00fc03f0

def z1143 : W := mkw 0x082004089ccd92e1 0x410400811399b25c 0x180000001ffd93e4 0x0300000003ffb27c

def z1144 : W := mkw 0x25985bf760000000 0x04b30b7eec000000 0x60f80fffe0000002 0x8c1f01fffc000000

def z1145 : W := mkw 0x27dffbf762120000 0x04fbff7eec424000 0xffffffffffffe007 0xfffffffffffffc00

def z1146 : W := mkw 0x0042c055000080a0 0x0008580aa0001014 0xe0e6ccff800013e3 0xbc1cd99ff000027c

def z1147 : W := mkw 0x25985bf760000000 0x04b30b7eec000000 0xe7f9ffffe0000003 0xfcff3ffffc000000

def z1148 : W := mkw 0x08200408998d9af1 0xc10400811331b35e 0x08000000189d9ffc 0x010000000313b3ff

def z1149 : W := mkw 0x214adbf760000000 0x04295b7eec000000 0x60e0cfffe0000002 0x8c1c19fffc000000

def z1150 : W := mkw 0x06f7a00016db4000 0x00def40002db6800 0xdffff0001ffffc7d 0xfbfffe0003ffff8f

def z1151 : W := mkw 0x004ad1d52020a5ac 0x20095a3aa40414b5 0xe0fefcff80e1e383 0xbc1fdf9ff01c3c70

def z1152 : W := mkw 0x082004089a9f92f1 0xc10400811353f25e 0x08000000189f93fc 0x010000000313f27f

def z1153 : W := mkw 0x0a47e055021bc0a0 0x4148fc0aa0437814 0x0807f000001fe001 0x0100fe000003fc00

def z1154 : W := mkw 0x03050e02cb161851 0x8060a1c05962c30a 0xa7070f07ff1c1c7b 0x74e0e1e0ffe3838f

def z1155 : W := mkw 0x35b83fa83de01f06 0x06b707f507bc03e0 0xf7f83ff81fe01f86 0xfeff07ff03fc03f0

def z1156 : W := mkw 0x2042f05520000000 0x04085e0aa4000000 0xe0e6fcff80000003 0xbc1cdf9ff0000000

def z1157 : W := mkw 0x27dffbf760090000 0x04fbff7eec012000 0xefffffffe01d8003 0xfdfffffffc03b000

def z1158 : W := mkw 0x0862c45d988d1241 0x410c588bb311a248 0xe0e6ccff989c1387 0xbc1cd99ff3138270

def z1159 : W := mkw 0x0862c45d9ccdd2e1 0x410c588bb399ba5c 0xe8e6ccff98fdf3e7 0xbd1cd99ff31fbe7c

def z1160 : W := mkw 0x14b801a814e00706 0x02970035029c00e0 0xd7f803f81fe01f86 0xfaff007f03fc03f0

def z1161 : W := mkw 0x0042c05500000000 0x0008580aa0000000 0xe8e6ccff80818007 0xbd1cd99ff0103000

def z1162 : W := mkw 0x082004089edf5241 0x4104008113dbea48 0x180000001fffe004 0x0300000003fffc00

def z1163 : W := mkw 0x0020040898841241 0x0004008113108248 0x08000000189c13e4 0x010000000313827c

def z1164 : W := mkw 0x182004089de49fe7 0x4304008113bc93fc 0x100000001fe01fe4 0x0200000003fc03fc

def z1165 : W := mkw 0x27dffbf76232a5ac 0x24fbff7eec4654b5 0xffffffffffffffff 0xffffffffffffffff

def z1166 : W := mkw 0x179d0ba247720d16 0x82f3a17448ee41a2 0xf7ff0fffe7620c1b 0xfeffe1fffcec4183

def z1167 : W := mkw 0x03050a02c3160851 0x8060a1405862c10a 0x9f070307ff1e0c7d 0x73e0e060ffe3c18f

def z1168 : W := mkw 0x15b80fa81de01f06 0x02b701f503bc03e0 0xf7f80cf81fe00384 0xfeff019f03fc0070

def z1169 : W := mkw 0x15b80fa81de01f06 0x02b701f503bc03e0 0x77f80cf81fe01f84 0xaeff019f03fc03f0

def z1170 : W := mkw 0x082855ccb8adb7ed 0x61050ab99715b6fd 0x0818f0c018fdf3e4 0x81031e18031fbe7c

def z1171 : W := mkw 0x020d51c42232a5ac 0x2041aa38844654b5 0x9f0703c47f1e1fff 0x73e0e0788fe3c3ff

def z1172 : W := mkw 0x0042d0552000a0a8 0x20085a0aa4001415 0xe8e7fcffe003e07b 0xbd1cff9ffc007c0f

def z1173 : W := mkw 0x27dffbf760000000 0x04fbff7eec000000 0x60ffffffe0000003 0x8c1ffffffc000000

def z1174 : W := mkw 0x27dffbf767524810 0x84fbff7eecea4902 0xf7ffffffe7626c1b 0xfefffffffcec4d83

def z1175 : W := mkw 0x15b80ba814e00706 0x02b70175029c00e0 0xf7f80ff81fe00386 0xfeff01ff03fc0070

def z1176 : W := mkw 0x08200408998d9ae1 0x410400811331b35c 0x180000001f9d9fe4 0x0300000003f3b3fc

def z1177 : W := mkw 0x07d7ea5740000000 0x00fafd4ae8000000 0xe7ffffffe0000003 0xfcfffffffc000000

def z1178 : W := mkw 0x00004044000080a0 0x0000080880001014 0x9819f3c460e3ffff 0xd3033e788c1c7fff

def z1179 : W := mkw 0x0842c45d880492e1 0x4108588bb100925c 0xe8e6ccff981c13e7 0xbd1cd99ff303827c

def z1180 : W := mkw 0x0942ce55890d98e1 0x412859cab121b31c 0xbf06cf079f1d9c67 0x77e0d9e0f3e3b38c

def z1181 : W := mkw 0x08200408988d1241 0x410400811311a248 0x08000000181c1064 0x010000000303820c

def z1182 : W := mkw 0x27dffbf760000000 0x04fbff7eec000000 0x67ff3fffe0000002 0x6cffe7fffc000000

def z1183 : W := mkw 0x27d7aa3340000000 0x04faf54668000000 0x67e70c3fe0000001 0x2cfce187fc000000

def z1184 : W := mkw 0x06b5000016d20000 0x00d6a00002da4000 0xdffff0001fffe005 0xfbfffe0003fffc00

def z1185 : W := mkw 0x27dffbf760200504 0x04fbff7eec0400a0 0xe7ffffffe0e00383 0xfcfffffffc1c0070

def z1186 : W := mkw 0x19085ffda924bfef 0x63210bffb52497fd 0x20000fffe0001ffa 0x040001fffc0003ff

def z1187 : W := mkw 0x24d2a03100000000 0x049a540620000000 0x60e60c3b80000000 0x2c1cc18770000000

def z1188 : W := mkw 0x279d5bf760000000 0x04f3ab7eec000000 0xe7ff0fffe0000003 0xfcffe1fffc000000

def z1189 : W := mkw 0x03052e02cb165851 0x8060a5c05962cb0a 0xbf073f07ff1e7c7f 0x77e0e7e0ffe3cf8f

def z1190 : W := mkw 0x08200408988d92e1 0x410400811311b25c 0x8800c000189d93e5 0x910018000313b27c

def z1191 : W := mkw 0x079d0ba240000000 0x00f3a17448000000 0xe7fe0ffb80000002 0xfcffc1ff70000000

def z1192 : W := mkw 0x05d28a3100000000 0x00ba514620000000 0x67e60c3b80000000 0x2cfcc18770000000

def z1193 : W := mkw 0x37dfabb345600d06 0x06fbf57668ac01a0 0x77fe0f3b87600c00 0x6effc1e770ec0180

def z1194 : W := mkw 0x37dffbf767720d16 0x86fbff7eecee41a2 0xf7ffffffe7620c1b 0xfefffffffcec4183

def z1195 : W := mkw 0x0862c45d988d92e1 0x410c588bb311b25c 0xe8e7ccfff89f93ff 0xbd1cf99fff13f27f

def z1196 : W := mkw 0x0862c45d988d92e1 0x410c588bb311b25c 0xe0e6ccff981c13e3 0xbc1cd99ff303827c

def z1197 : W := mkw 0x27dffbf762120000 0x04fbff7eec424000 0xffffffffff1e1c7f 0xffffffffffe3c38f

def z1198 : W := mkw 0x05b80ba014e00504 0x00b70174029c00a0 0xf7f80ff81fe01f86 0xfeff01ff03fc03f0

def z1199 : W := mkw 0x182004089dcd1a43 0x4304008113b9a348 0x000000001f1c0000 0x0000000003e38000

def z1200 : W := mkw 0x15b80fa81de01f06 0x02b701f503bc03e0 0x57f803f81fe01f84 0xcaff007f03fc03f0

def z1201 : W := mkw 0x27dfabb340000000 0x04fbf57668000000 0xe7ff0fffe0000003 0xfcffe1fffc000000

def z1202 : W := mkw 0x03050e02cb161851 0x8060a1c05962c30a 0xbf1fff07ff1e1c7f 0xf7e3ffe0ffe3c38f

def z1203 : W := mkw 0x06dff1d520000000 0x00dbfe3aa4000000 0xe7ffffffe0000003 0xfcfffffffc000000

def z1204 : W := mkw 0x0820544cb88db2e9 0x61040a899711b65d 0x0801f004789ff3fd 0x01003e008f13fe7f

def z1205 : W := mkw 0x27dffbf7621b4000 0x04fbff7eec436800 0xffffffffe0ffe007 0xfffffffffc1ffc00

def z1206 : W := mkw 0x27dffbf760000000 0x04fbff7eec000000 0x67f9ffffe0000002 0xccff3ffffc000000

def z1207 : W := mkw 0x082004089fdfdaf1 0xc104008113fbfb5e 0x180000001ffffffc 0x0300000003ffffff

def z1208 : W := mkw 0x0a47e055821fc0e1 0x4148fc0ab043f81c 0x0806c007801d8061 0x0100d800f003b00c

def z1209 : W := mkw 0x35b81faa7de01f06 0x06b703f54fbc03e0 0xf7f80ff87fe01f86 0xfeff01ff0ffc03f0

def z1210 : W := mkw 0x2042d05760000000 0x04085a0aec000000 0xe0e6ccffe0000003 0xbc1cd99ffc000000

def z1211 : W := mkw 0x0225000016db4000 0x0044a00002db6800 0x9f1ff0001fffe005 0xf3e3fe0003fffc00

def z1212 : W := mkw 0x0862c45d988d92e1 0x410c588bb311b25c 0xe8e6cffff89d9fff 0xbd1cd9ffff13b3ff

def z1213 : W := mkw 0x182004089ded1f47 0x4304008113bda3e8 0x100000001ffc1f84 0x0200000003ff83f0

def z1214 : W := mkw 0x2247a01340000000 0x0448f40268000000 0x60e60c3b80000000 0x2c1cc18770000000

def z1215 : W := mkw 0x27d7aa3343120810 0x84faf54668624102 0x67e60c3b87000000 0x2cfcc18770e00000

def z1216 : W := mkw 0x200851f52020a5ac 0x24010a3ea40414b5 0x9819f3fc60e3ffff 0xd3033e7f8c1c7fff

def z1217 : W := mkw 0x27dffbf764404000 0x04fbff7eec880800 0xe7ffffffe0606003 0xfcfffffffc0c0c00

def z1218 : W := mkw 0x06f7a00016db4000 0x00def40002db6800 0xdffff3007fffec1d 0xfbfffe600ffffd83

def z1219 : W := mkw 0x27d7aa3340000000 0x04faf54668000000 0x67fefc3b80000000 0xacffdf8770000000

def z1220 : W := mkw 0x279d7bf760000000 0x04f3af7eec000000 0xe7f93fffe0000002 0xfcff27fffc000000

def z1221 : W := mkw 0x06d7e05500000000 0x00dafc0aa0000000 0xe7e6ccff80000003 0xbcfcd99ff0000000

def z1222 : W := mkw 0x15b80ba815e00f06 0x02b7017502bc01e0 0x47f800f807e00380 0x88ff001f00fc0070

def z1223 : W := mkw 0x04f2800014c90000 0x009e500002992000 0xdffff0001fffe005 0xfbfffe0003fffc00

def z1224 : W := mkw 0x204ad1f520000000 0x04095a3ea4000000 0xe0e6ccff80000003 0xbc1cd99ff0000000

def z1225 : W := mkw 0x06f7a00256db4010 0x80def4004adb6802 0xdffff0007fffe01d 0xfbfffe000ffffc03

def z1226 : W := mkw 0x0862c45d988d92e1 0x410c588bb311b25c 0xf8e7ccff989f93e7 0xff1cf99ff313f27c

def z1227 : W := mkw 0x2247f057e216a0f9 0xa448fe0afc42d41f 0x0807f007e01fe079 0x0100fe00fc03fc0f

def z1228 : W := mkw 0x25dafbf760000000 0x04bb5f7eec000000 0x60f8fcfb80000000 0x8c1f1f9f70000000

def z1229 : W := mkw 0x2247e05740000000 0x0448fc0ae8000000 0xe0e6ccff80000003 0xbc1cd99ff0000000

def z1230 : W := mkw 0x000851c42020a5ac 0x20010a38840414b5 0x1019f3c460e3fffa 0xc2033e788c1c7fff

def z1231 : W := mkw 0x000851c42020a5ac 0x20010a38840414b5 0x9f19f3c47fe3ffff 0xf3e33e788ffc7fff

def z1232 : W := mkw 0x082855ccbbbfbffd 0xe1050ab99777f7ff 0x9819f3c47fffffff 0xd3033e788fffffff

def z1233 : W := mkw 0x27dffbf760000000 0x04fbff7eec000000 0xf7ffffffe0e00007 0xfefffffffc1c0000

def z1234 : W := mkw 0x0042c05500000000 0x0008580aa0000000 0xe8e6ccff80001067 0xbd1cd99ff000020c

def z1235 : W := mkw 0x03478a1340000000 0x0068f14268000000 0xe7e70f3fe0000003 0x7cfce1e7fc000000

def z1236 : W := mkw 0x25d2aa3340000000 0x04ba554668000000 0x60e00c3b80000000 0x0c1c018770000000

def z1237 : W := mkw 0x25985bf76020a5ac 0x24b30b7eec0414b5 0xfff9ffffe0e3ffff 0xffff3ffffc1c7fff

def z1238 : W := mkw 0x05b00e081dc01a00 0x00b601c103b80340 0xf7f80ff81fe01f86 0xfeff01ff03fc03f0

def z1239 : W := mkw 0x27d7aa3340000000 0x04faf54668000000 0xe7e60c3f80000003 0x3cfcc187f0000000

def z1240 : W := mkw 0x182004089fff9ff7 0xc304008113fff3fe 0x180000001fff9ffc 0x0300000003fff3ff

def z1241 : W := mkw 0x0042801100000000 0x0008500220000000 0xe0e60c3f80000003 0x3c1cc187f0000000

def z1242 : W := mkw 0x24daf1f520000000 0x049b5e3ea4000000 0xe0ffffffe0000003 0xfc1ffffffc000000

def z1243 : W := mkw 0x0a47f055a21fe0e9 0x6148fe0ab443fc1d 0x0807f007e01fe079 0x0100fe00fc03fc0f

def z1244 : W := mkw 0x25985bf76020a5ac 0x24b30b7eec0414b5 0xf7f80fffe0e01ffe 0xfeff01fffc1c03ff

def z1245 : W := mkw 0x0247c05740000000 0x0048f80ae8000000 0xe0e7ccffe0000003 0xbc1cf99ffc000000

def z1246 : W := mkw 0x27dffbf766524000 0x04fbff7eecca4800 0xffffffffe7e3e007 0xfffffffffcfc7c00

def z1247 : W := mkw 0x27dffbf76020250c 0x24fbff7eec0404a1 0xe7ffffffe0606003 0xfcfffffffc0c0c00

def z1248 : W := mkw 0x15b80fa81de01f06 0x02b701f503bc03e0 0xf7f93ff81fe27f86 0xfeff27ff03fc4ff0

def z1249 : W := mkw 0x14b801a814e00706 0x02970035029c00e0 0x47f800f81fe00380 0xa8ff001f03fc0070

def z1250 : W := mkw 0x15b82fa81de05f06 0x02b705f503bc0be0 0xf7f83ff81fe07f86 0xfeff07ff03fc0ff0

def z1251 : W := mkw 0x05b80fa81cc01200 0x00b701f503980240 0xf7f80ff81fe01386 0xfeff01ff03fc0270

def z1252 : W := mkw 0x08281588b8adb7ed 0x610502b11715b6fd 0x1819330078fffffc 0x430326600f1fffff

def z1253 : W := mkw 0x37dffbf765602d0e 0x26fbff7eecac05a1 0xf7ffffffe7626c1b 0xfefffffffcec4d83

def z1254 : W := mkw 0x0862c45d988db2e9 0x610c588bb311b65d 0xe8e6ccff989ff3ff 0xbd1cd99ff313fe7f

def z1255 : W := mkw 0x27d7ea7740000000 0x04fafd4ee8000000 0x67e6ccfb80000000 0xacfcd99f70000000

def z1256 : W := mkw 0x08200408988d92e1 0x410400811311b25c 0xe8e60cff989d93e7 0xbd1cc19ff313b27c

def z1257 : W := mkw 0x2247f05760000000 0x0448fe0aec000000 0x60e7fc3fe0000001 0x2c1cff87fc000000

def z1258 : W := mkw 0x0862e45d988dd2e1 0x410c5c8bb311ba5c 0xe8e6fcff989df3e7 0xbd1cdf9ff313be7c

def z1259 : W := mkw 0x27dffbf76020a5ac 0x24fbff7eec0414b5 0xf7ffffffe0627ffb 0xfefffffffc0c4fff

def z1260 : W := mkw 0x0820444c988d92e1 0x410408899311b25c 0x0800c0c0189d93e4 0x810018180313b27c

def z1261 : W := mkw 0x0142ca5740000000 0x0028594ae8000000 0xe0e6cfffe0000003 0xbc1cd9fffc000000

def z1262 : W := mkw 0x11280fa819a01f06 0x022501f5033403e0 0xf7e00ff81f801f86 0xfefc01ff03f003f0

def z1263 : W := mkw 0x0862c45d988d92e1 0x410c588bb311b25c 0x68e60cff989d93e6 0x2d1cc19ff313b27c

def z1264 : W := mkw 0x04b805881ce01704 0x009700b1039c02e0 0xf7f80ff81fe01f86 0xfeff01ff03fc03f0

def z1265 : W := mkw 0x0000000000000000 0x0000000000000000 0xe0e60cff80000003 0xbc1cc19ff0000000

def z1266 : W := mkw 0x0862c45d988d92e1 0x410c588bb311b25c 0xe0e60cff989c13e6 0xbc1cc19ff313827c

def z1267 : W := mkw 0x0820444c988d92e1 0x410408899311b25c 0x0800c004189d93e5 0x010018008313b27c

def z1268 : W := mkw 0x04d2e05500000000 0x009a5c0aa0000000 0xe0fefcff80000003 0xbc1fdf9ff0000000

def z1269 : W := mkw 0x15b80fa81de95f06 0x02b701f503bd2be0 0xf7f80ff81fe1ff86 0xfeff01ff03fc3ff0

def z1270 : W := mkw 0x014acbf500000000 0x0029597ea0000000 0xe0e6cfff80000003 0xbc1cd9fff0000000

def z1271 : W := mkw 0x15b80fa81de01f06 0x02b701f503bc03e0 0xf7f80ffc7fe01ffe 0xfeff01ff8ffc03ff

def z1272 : W := mkw 0x27dffbf76672650c 0x24fbff7eecce4ca1 0xf7ffffffe7626c1b 0xfefffffffcec4d83

def z1273 : W := mkw 0x224ff1d760000000 0x0449fe3aec000000 0xe0ffffffe0000003 0xfc1ffffffc000000

def z1274 : W := mkw 0x27dfabb340200504 0x04fbf576680400a0 0xf7fe0ffb80e01f86 0xfeffc1ff701c03f0

def z1275 : W := mkw 0x082004089edfd2e1 0x4104008113dbfa5c 0x080000001f9d93e4 0x0100000003f3b27c

def z1276 : W := mkw 0x0062c45d98841241 0x000c588bb3108248 0xe8e6ccff989c13e7 0xbd1cd99ff313827c

def z1277 : W := mkw 0x08628419988d1241 0x410c50833311a248 0x60e60cfb981c1382 0x2c1cc19f73038270

def z1278 : W := mkw 0x0862d45db88d92e1 0x410c5a8bb711b25c 0xe8e7fcfff89d93e7 0xbd1cff9fff13b27c

def z1279 : W := mkw 0x08628419988d1241 0x410c50833311a248 0x60e60cfb989c0380 0xac1cc19f73138070

def z1280 : W := mkw 0x27dffbf760200504 0x04fbff7eec0400a0 0xf7ffffffe0600c03 0xfefffffffc0c0180

def z1281 : W := mkw 0x0862c45d988d92e1 0x410c588bb311b25c 0xf8fffffff8ffffff 0xff1fffffff1fffff

def z1282 : W := mkw 0x04b0000814c00200 0x0096000102980040 0xd7f800f81fe00384 0xfaff001f03fc0070

def z1283 : W := mkw 0x27dfbbb360000000 0x04fbf7766c000000 0xe7ff3f3fe0000003 0x7cffe7e7fc000000

def z1284 : W := mkw 0x15b80fa81de01f06 0x02b701f503bc03e0 0xfffe0ff81ffc1f87 0xffffc1ff03ff83f0

def z1285 : W := mkw 0x0008018000200504 0x00010030000400a0 0x9819f3c460e3ffff 0xd3033e788c1c7fff

def z1286 : W := mkw 0x08200408988d92e1 0x410400811311b25c 0x00000000189d8380 0x000000000313b070

def z1287 : W := mkw 0x15b80fa81de01f06 0x02b701f503bc03e0 0x77e00ff81fe01f86 0x2efc01ff03fc03f0

def z1288 : W := mkw 0x020504008a161041 0x0040a0801142c208 0xbf070f07ff1e1c7f 0x77e0e1e0ffe3c38f

def z1289 : W := mkw 0x15b81fa83de01f06 0x02b703f507bc03e0 0xf7f93ff87fe01f86 0xfeff27ff0ffc03f0

def z1290 : W := mkw 0x0820444c9edfd2e1 0x4104088993dbfa5c 0x9819f0c41ffff3e7 0xd3033e1883fffe7c

def z1291 : W := mkw 0x27d7aa3340000000 0x04faf54668000000 0xe7e70c3b80000001 0x7cfce18770000000

def z1292 : W := mkw 0x0ff7ae1bdfdf5a51 0xc1fef5c37bfbeb4a 0x67e60c3b9f1c0000 0x2cfcc18773e38000

def z1293 : W := mkw 0x04f2a00014c94000 0x009e540002992800 0xdffef0001ffde005 0xfbffde0003ffbc00

def z1294 : W := mkw 0x06f7a00016db4000 0x00def40002db6800 0xdffff0041ffff067 0xfbfffe0083fffe0c

def z1295 : W := mkw 0x01000e02c9041851 0x802001c05920830a 0xb819ff07e0e3fc7f 0xd7033fe0fc1c7f8f

def z1296 : W := mkw 0x27dffbf7665b4000 0x04fbff7eeccb6800 0xffffffffe77fe003 0xfffffffffceffc00

def z1297 : W := mkw 0x082004089edf5241 0x4104008113dbea48 0x000000001f1c0000 0x0000000003e38000

def z1298 : W := mkw 0x04dac1f500000000 0x009b583ea0000000 0xe0feccff80000003 0xbc1fd99ff0000000

def z1299 : W := mkw 0x182004089dedbfef 0x6304008113bdb7fd 0x180000001ffffffc 0x0300000003ffffff

def z1300 : W := mkw 0x03050a0240000000 0x0060a14048000000 0xe7e70fffe0000003 0xfcfce1fffc000000

def z1301 : W := mkw 0x24daf1f52020a5ac 0x249b5e3ea40414b5 0xe8fefcff80e1f3e7 0xbd1fdf9ff01c3e7c

def z1302 : W := mkw 0x27d7aa3346524000 0x04faf54668ca4800 0x77ff3c3b87626000 0x6effe78770ec4c00

def z1303 : W := mkw 0x0ef7a01916db4200 0x41def40322db6840 0xdffff0381fffe005 0xfbfffe0703fffc00

def z1304 : W := mkw 0x27dffbf7600080a0 0x04fbff7eec001014 0xe7ffffffe0818383 0xfcfffffffc103070

def z1305 : W := mkw 0x15b80fa89de41f47 0x02b701f513bc83e8 0xf7f80fff9fe01fe6 0xfeff01fff3fc03fc

def z1306 : W := mkw 0x27dffbf760000000 0x04fbff7eec000000 0xe7e70fffe0000003 0x7cfce1fffc000000

def z1307 : W := mkw 0x0042c055000080a0 0x0008580aa0001014 0xe8e6ccff80018063 0xbd1cd99ff000300c

def z1308 : W := mkw 0x08200408988d92e1 0x410400811311b25c 0x18000000189f9ffc 0x030000000313f3ff

def z1309 : W := mkw 0x08628419988d1241 0x410c50833311a248 0xe8e60cff989c13e7 0xbd1cc19ff313827c

def z1310 : W := mkw 0x182845cc9ded9fe7 0x430508b993bdb3fc 0x9818c3c41ffd9fe7 0xd303187883ffb3fc

def z1311 : W := mkw 0x379d3ba267724d06 0x06f3a7744cee49a0 0x1719330067626c00 0x42e326600cec4d80

def z1312 : W := mkw 0x0862c45d988d92e1 0x410c588bb311b25c 0xe8e7cffff89d93e7 0xfd1cf9ffff13b27c

def z1313 : W := mkw 0x15b80ba815e00f06 0x02b7017502bc01e0 0xd7f803f807e01f86 0xdaff007f00fc03f0

def z1314 : W := mkw 0x15b80fa81de01f06 0x02b701f503bc03e0 0xf7f9fff81fe01f87 0xfeff3fff03fc03f0

def z1315 : W := mkw 0x27dffbf76000a0a8 0x24fbff7eec001415 0xffffffffe0e3e07f 0xfffffffffc1c7c0f

def z1316 : W := mkw 0x1db80fa89ded9fe7 0x43b701f513bdb3fc 0x1f1803001ffd9fe4 0x43e3006003ffb3fc

def z1317 : W := mkw 0x004ad1d520000000 0x00095a3aa4000000 0xe0fefcff80000003 0xbc1fdf9ff0000000

def z1318 : W := mkw 0x08200408988d92e1 0x410400811311b25c 0x880000c0189d93e6 0x910000180313b27c

def z1319 : W := mkw 0x27dffbf764400000 0x04fbff7eec880000 0xf7ffffffe7600003 0xfefffffffcec0000

def z1320 : W := mkw 0x15b80fa81de01f06 0x02b701f503bc03e0 0xfff80ff81fe21ffe 0xffff01ff03fc43ff

def z1321 : W := mkw 0x27dffbf760000000 0x04fbff7eec000000 0xe7ffffffe0801387 0xfcfffffffc100270

def z1322 : W := mkw 0x08200408988d92e1 0x410400811311b25c 0x88000004189d93e7 0x110000008313b27c

def z1323 : W := mkw 0x27d7fa7760000000 0x04faff4eec000000 0x67e6fc3b80000000 0x2cfcdf8770000000

def z1324 : W := mkw 0x15b80faadde41f57 0x82b701f55bbc83ea 0xfffe0ffffffc1fff 0xffffc1ffffff83ff

def z1325 : W := mkw 0x15b80fa81de03f0e 0x22b701f503bc07e1 0xf7f80ff81fe27f9e 0xfeff01ff03fc4ff3

def z1326 : W := mkw 0x0862c45d988d92e1 0x410c588bb311b25c 0x60e6ccff989d93e2 0xac1cd99ff313b27c

def z1327 : W := mkw 0x14b805a81de01f06 0x029700b503bc03e0 0xd7f800f81fe01f84 0xfaff001f03fc03f0

def z1328 : W := mkw 0x034fdbd76020a5ac 0x2069fb7aec0414b5 0xffffffffe0e3ffff 0xfffffffffc1c7fff

def z1329 : W := mkw 0x15b80fa81de91f06 0x02b701f503bd23e0 0xfff80ff81ffd9f86 0xffff01ff03ffb3f0

def z1330 : W := mkw 0x24daf1f52020a5ac 0x249b5e3ea40414b5 0xf8ffffffe0e3ffff 0xff1ffffffc1c7fff

def z1331 : W := mkw 0x082004089ccdd2e1 0x410400811399ba5c 0x0800000018fdf3e4 0x01000000031fbe7c

def z1332 : W := mkw 0x27dffbf760000000 0x04fbff7eec000000 0xe7fefffb80000002 0xfcffdfff70000000

def z1333 : W := mkw 0x27dffbf763120810 0x84fbff7eec624102 0xffffffffff1e0c1f 0xffffffffffe3c183

def z1334 : W := mkw 0x06f7a00016db4000 0x00def40002db6800 0xd7fef0001ffde004 0xfaffde0003ffbc00

def z1335 : W := mkw 0x15b80fa81dc01a02 0x02b701f503b80340 0xe7f80ff81f801386 0xfcff01ff03f00270

def z1336 : W := mkw 0x26dff1f760000000 0x04dbfe3eec000000 0xe0fffcffe0000003 0xbc1fff9ffc000000

def z1337 : W := mkw 0x27dffbf76020a5ac 0x24fbff7eec0414b5 0xe7ffffffe0e1fffb 0xfcfffffffc1c3fff

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z7,z8,z4,z5,z6]),(1,[z2,z7,z4,z5,z9,z10]),(0,[z1,z2,z7,z4,z11,z12,z6]),(0,[z1,z2,z13,z14,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z15,z6])],[(1,[z16,z17,z7,z4,z5,z6]),(0,[z1,z18,z2,z7,z4,z19,z6]),(0,[z1,z20,z2,z7,z4,z5,z9]),(0,[z1,z18,z21,z2,z7,z4,z6]),(0,[z1,z22,z2,z7,z4,z23,z5]),(0,[z1,z2,z7,z24,z4,z5,z6])],[(0,[z1,z2,z8,z25,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z26,z6]),(0,[z1,z2,z7,z4,z5,z27,z6]),(0,[z1,z28,z2,z7,z4,z5,z6]),(0,[z1,z29,z2,z7,z4,z5,z6])],[(0,[z1,z2,z7,z4,z30,z5,z10]),(0,[z1,z20,z2,z7,z4,z5,z31]),(0,[z1,z2,z32,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z33,z5,z6]),(0,[z1,z21,z2,z7,z4,z5,z6]),(0,[z1,z34,z2,z7,z35,z4,z5]),(0,[z1,z2,z7,z4,z5,z36,z6]),(0,[z1,z22,z2,z7,z4,z5,z37])],[(1,[z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z38,z7,z35,z4,z5]),(0,[z39,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z19,z5,z10])],[(0,[z1,z40,z2,z7,z4,z5,z10]),(0,[z1,z18,z2,z7,z4,z5,z9]),(0,[z1,z2,z7,z41,z4,z5,z6])],[(0,[z42,z1,z2,z7,z4,z5,z9]),(0,[z1,z2,z7,z4,z5,z43,z9]),(0,[z44,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z45,z4,z5,z6]),(0,[z1,z2,z7,z4,z23,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z46])],[(0,[z1,z2,z47,z7,z4,z5,z9]),(0,[z1,z48,z49,z7,z4,z5,z6]),(0,[z50,z1,z2,z7,z35,z4,z5]),(0,[z51,z1,z22,z2,z7,z4,z5])]],
   [[(0,[z0,z1,z2,z7,z4,z5,z9]),(0,[z1,z2,z7,z4,z52,z5,z6]),(0,[z53,z1,z2,z7,z4,z5,z6]),(0,[z54,z1,z2,z7,z4,z5,z10]),(0,[z1,z2,z7,z5,z55,z56,z6]),(0,[z1,z2,z7,z4,z57,z5,z58]),(0,[z1,z2,z7,z4,z59,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z60])],[(0,[z1,z2,z7,z61,z4,z5,z10]),(0,[z62,z1,z22,z2,z7,z4,z5]),(0,[z1,z2,z7,z4,z63,z5,z6]),(0,[z64,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z65]),(0,[z1,z2,z66,z7,z4,z5,z6]),(0,[z1,z2,z67,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z68])],[(0,[z69,z1,z22,z2,z7,z4,z5]),(1,[z1,z2,z7,z70,z4,z5]),(1,[z1,z2,z7,z4,z5,z71]),(0,[z72,z1,z2,z7,z4,z5,z6]),(1,[z50,z1,z7,z30,z5,z6]),(1,[z1,z34,z2,z12,z5,z6])],[(0,[z1,z2,z7,z4,z73,z5,z6]),(0,[z74,z1,z2,z7,z4,z5,z75]),(1,[z62,z2,z7,z4,z76,z6]),(0,[z77,z1,z2,z7,z78,z5,z6]),(0,[z1,z79,z2,z7,z4,z5,z9]),(0,[z1,z2,z7,z80,z4,z5,z6]),(0,[z54,z1,z81,z7,z4,z5,z6]),(0,[z1,z2,z7,z35,z4,z5,z82]),(0,[z1,z22,z2,z7,z4,z5,z83])],[(0,[z1,z2,z2,z7,z4,z5,z6]),(0,[z0,z1,z2,z7,z4,z84,z6]),(0,[z1,z2,z7,z4,z5,z6,z85]),(0,[z1,z2,z7,z4,z86,z5,z6]),(0,[z87,z1,z2,z7,z4,z5,z6]),(0,[z1,z88,z2,z7,z4,z5,z6])],[(0,[z89,z1,z2,z7,z4,z5,z6]),(0,[z90,z1,z22,z2,z7,z4,z5]),(0,[z91,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z76,z56,z6]),(0,[z1,z2,z92,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z93,z6])],[(0,[z1,z2,z94,z7,z4,z5,z6]),(0,[z1,z2,z95,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z96,z6]),(0,[z1,z2,z7,z4,z5,z97,z6])],[(0,[z1,z2,z7,z4,z98,z5,z6]),(0,[z1,z2,z7,z4,z99,z5,z6]),(1,[z1,z81,z7,z4,z5,z100]),(0,[z1,z2,z7,z4,z57,z5,z101]),(0,[z1,z102,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z103,z4,z5,z6])]],
   [[(0,[z104,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z105,z4,z5,z6]),(0,[z106,z1,z2,z7,z4,z5,z6])],[(0,[z1,z107,z2,z7,z4,z5,z6]),(0,[z74,z1,z2,z7,z108,z5,z6]),(0,[z72,z109,z2,z7,z4,z5,z6]),(1,[z1,z2,z7,z4,z110,z6]),(0,[z1,z2,z7,z4,z111,z5,z6]),(0,[z1,z112,z2,z7,z4,z113,z6]),(0,[z1,z2,z7,z4,z5,z114,z6])],[(0,[z1,z2,z7,z4,z5,z115,z6]),(0,[z1,z2,z7,z4,z5,z116,z6]),(0,[z1,z2,z7,z4,z117,z5,z6]),(0,[z1,z2,z7,z4,z118,z5,z6]),(0,[z1,z2,z7,z4,z5,z119,z6]),(0,[z1,z2,z7,z4,z5,z6,z120]),(0,[z1,z2,z7,z35,z35,z4,z5])],[(0,[z1,z81,z2,z121,z7,z4,z5]),(0,[z1,z2,z7,z4,z122,z5,z6])],[(0,[z1,z2,z7,z4,z123,z5,z6]),(0,[z1,z2,z124,z7,z4,z5,z6]),(0,[z1,z2,z7,z14,z35,z4,z5]),(0,[z1,z2,z7,z4,z5,z125,z6])],[(0,[z1,z2,z7,z126,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z75]),(0,[z1,z2,z7,z4,z5,z127,z6]),(0,[z1,z2,z7,z4,z5,z128,z6])],[(0,[z69,z1,z2,z7,z108,z5,z6]),(0,[z62,z1,z2,z7,z4,z5,z10]),(0,[z1,z20,z2,z7,z4,z5,z6]),(1,[z1,z2,z7,z129,z4,z5]),(0,[z1,z2,z7,z130,z4,z5,z56]),(0,[z1,z112,z2,z47,z4,z5,z6]),(0,[z1,z2,z121,z7,z4,z5,z82]),(0,[z1,z2,z7,z35,z4,z131,z5]),(0,[z1,z2,z7,z132,z4,z5,z6])],[(0,[z0,z1,z17,z7,z4,z5,z6]),(0,[z133,z1,z2,z7,z4,z5,z6]),(0,[z69,z1,z2,z7,z4,z5,z10]),(0,[z1,z2,z7,z4,z134,z5,z6]),(0,[z1,z112,z2,z4,z23,z5,z6]),(0,[z1,z22,z2,z7,z4,z5,z82]),(0,[z1,z135,z22,z2,z7,z4,z5]),(0,[z1,z2,z7,z4,z5,z136,z6]),(0,[z1,z2,z7,z35,z4,z137,z5]),(0,[z1,z2,z7,z35,z4,z5,z138])]],
   [[(0,[z16,z1,z139,z7,z4,z5,z6]),(0,[z1,z2,z140,z7,z4,z5,z9]),(1,[z1,z2,z7,z4,z141,z6]),(0,[z1,z40,z2,z7,z4,z142,z6]),(0,[z1,z2,z7,z4,z137,z5,z6])],[(0,[z1,z1,z2,z7,z4,z5,z9])],[(0,[z90,z1,z2,z7,z4,z5,z10]),(0,[z1,z2,z7,z4,z143,z5,z6]),(0,[z62,z1,z2,z7,z4,z76,z6]),(0,[z144,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z145,z6]),(0,[z1,z18,z2,z7,z4,z5,z6]),(0,[z1,z22,z2,z7,z146,z4,z5])],[(0,[z42,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z147,z6]),(0,[z1,z2,z7,z4,z5,z6,z148])],[(0,[z1,z2,z7,z4,z149,z5,z56])],[(0,[z0,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z150,z4,z5,z6]),(0,[z1,z2,z7,z151,z4,z5,z6]),(0,[z74,z2,z7,z61,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z152]),(0,[z1,z2,z7,z35,z4,z5,z153]),(0,[z1,z2,z121,z7,z35,z4,z5])],[(0,[z1,z2,z7,z4,z5,z154,z6]),(0,[z1,z155,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z156,z6]),(0,[z1,z2,z47,z7,z4,z113,z6]),(0,[z1,z22,z2,z7,z35,z4,z5])],[(0,[z1,z157,z2,z7,z4,z5,z10]),(0,[z1,z2,z7,z4,z142,z5,z9]),(1,[z1,z20,z25,z4,z5,z6])]],
   [[(0,[z0,z16,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z35,z158,z4,z5]),(0,[z1,z79,z2,z7,z4,z5,z6])],[(0,[z1,z2,z7,z159,z4,z5,z6]),(0,[z1,z2,z7,z160,z4,z5,z6]),(0,[z1,z2,z7,z4,z161,z5,z6]),(0,[z1,z2,z162,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z163,z6])],[(0,[z1,z2,z7,z164,z61,z4,z5]),(0,[z72,z1,z22,z2,z7,z4,z5]),(0,[z1,z112,z2,z7,z165,z4,z6]),(0,[z1,z22,z2,z7,z4,z131,z5])],[(0,[z166,z1,z2,z8,z4,z5,z6]),(0,[z167,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z168])],[(0,[z1,z2,z7,z3,z4,z5,z6]),(0,[z1,z22,z2,z139,z7,z4,z5]),(0,[z1,z48,z2,z7,z4,z141,z6]),(0,[z1,z2,z169,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z55,z6]),(0,[z170,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z171,z6])],[(0,[z90,z1,z20,z2,z4,z5,z6]),(0,[z1,z2,z7,z8,z4,z5,z10]),(0,[z1,z2,z7,z4,z172,z5,z6]),(0,[z1,z2,z7,z4,z5,z173,z6]),(0,[z1,z2,z7,z174,z4,z5,z6])],[(0,[z1,z175,z2,z7,z4,z5,z6]),(0,[z1,z176,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z177,z5,z6]),(0,[z1,z2,z7,z178,z4,z5,z6]),(0,[z1,z40,z2,z7,z35,z4,z5])],[(0,[z1,z2,z7,z4,z5,z179,z6]),(0,[z1,z2,z7,z180,z4,z5,z9]),(0,[z1,z2,z7,z4,z181,z5,z6])]],
   [[(0,[z1,z2,z7,z4,z182,z5,z6]),(0,[z1,z183,z2,z7,z4,z5,z6]),(0,[z1,z184,z2,z7,z4,z5,z6]),(0,[z1,z185,z2,z7,z4,z5,z6])],[(0,[z186,z1,z2,z7,z4,z5,z6]),(0,[z1,z187,z2,z7,z4,z5,z6]),(1,[z1,z2,z7,z4,z5,z10]),(0,[z1,z2,z7,z4,z5,z9,z188]),(0,[z189,z1,z2,z7,z4,z5,z6]),(0,[z54,z1,z2,z7,z35,z4,z5]),(0,[z1,z22,z2,z7,z4,z5,z153]),(1,[z1,z2,z7,z4,z131,z190])],[(0,[z191,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z192,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z57,z5,z10]),(0,[z1,z2,z7,z4,z5,z6,z193]),(0,[z1,z2,z7,z4,z194,z5,z6]),(0,[z1,z2,z7,z195,z4,z5,z6]),(0,[z1,z196,z2,z7,z4,z5,z6])],[(0,[z1,z2,z7,z197,z4,z5,z6]),(0,[z1,z198,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z9,z100]),(0,[z1,z22,z48,z2,z7,z4,z5]),(0,[z1,z2,z7,z35,z4,z5,z199])],[(0,[z1,z2,z200,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z56,z9]),(0,[z1,z22,z2,z7,z158,z4,z5]),(0,[z1,z2,z7,z4,z5,z201,z6])],[(0,[z1,z2,z7,z4,z5,z202,z6]),(0,[z54,z1,z2,z7,z4,z131,z5])],[(0,[z1,z2,z7,z4,z76,z113,z6]),(1,[z1,z2,z7,z5,z55,z6])],[(0,[z72,z1,z2,z7,z4,z5,z10]),(0,[z1,z2,z47,z7,z165,z4,z6]),(0,[z203,z1,z2,z7,z4,z5,z6]),(0,[z1,z204,z2,z7,z35,z4,z5])]],
   [[(0,[z205,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z206,z9]),(0,[z207,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z165,z4,z57,z6]),(0,[z1,z2,z7,z4,z190,z6,z199])],[(0,[z166,z1,z2,z7,z4,z5,z208]),(0,[z1,z209,z2,z7,z4,z5,z6])],[(0,[z1,z2,z7,z4,z5,z6,z210]),(0,[z1,z2,z7,z211,z4,z5,z6]),(0,[z212,z1,z2,z7,z4,z5,z6]),(0,[z213,z1,z2,z7,z35,z4,z5])],[(0,[z1,z2,z7,z4,z5,z97,z10]),(0,[z1,z2,z7,z4,z5,z9,z9]),(0,[z1,z2,z7,z4,z131,z5,z9]),(0,[z50,z1,z2,z7,z158,z5,z6]),(0,[z1,z2,z7,z214,z4,z5,z6]),(0,[z1,z215,z2,z7,z4,z5,z6]),(0,[z1,z22,z22,z2,z7,z4,z5])],[(0,[z1,z2,z7,z4,z216,z5,z6]),(0,[z1,z17,z2,z7,z4,z5,z10]),(0,[z217,z1,z2,z7,z4,z5,z6]),(0,[z1,z218,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z76,z10]),(0,[z1,z2,z7,z4,z5,z6,z219])],[(0,[z1,z2,z7,z4,z5,z6,z220]),(0,[z1,z2,z7,z14,z108,z5,z6]),(0,[z1,z48,z2,z7,z4,z5,z10]),(0,[z1,z20,z2,z25,z4,z5,z6]),(0,[z1,z221,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z35,z4,z142,z5]),(0,[z1,z2,z222,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z223,z5,z6])],[(0,[z16,z1,z17,z7,z4,z5,z6]),(1,[z90,z2,z8,z4,z5,z6]),(0,[z1,z224,z2,z7,z4,z5,z6]),(0,[z1,z7,z4,z142,z5,z56,z6]),(0,[z1,z34,z2,z4,z12,z5,z6]),(0,[z225,z1,z2,z7,z4,z5,z6])],[(0,[z62,z1,z2,z7,z35,z4,z5]),(0,[z1,z2,z7,z4,z5,z116,z10]),(0,[z1,z2,z226,z7,z4,z5,z9]),(0,[z1,z2,z227,z7,z4,z5,z6]),(0,[z1,z22,z2,z7,z4,z5,z199])]],
   [[(0,[z1,z228,z2,z7,z4,z5,z6]),(0,[z69,z1,z2,z7,z35,z4,z5]),(0,[z1,z2,z7,z229,z4,z5,z6]),(1,[z1,z2,z169,z7,z4,z5]),(0,[z1,z2,z7,z4,z5,z230,z6]),(1,[z1,z2,z7,z4,z5,z231])],[(0,[z1,z2,z7,z232,z4,z5,z6]),(0,[z1,z2,z7,z158,z4,z5,z9]),(0,[z1,z2,z7,z4,z5,z233,z6]),(0,[z1,z18,z2,z7,z165,z5,z6]),(0,[z1,z234,z2,z7,z4,z5,z6])],[(0,[z109,z1,z2,z7,z4,z5,z9]),(0,[z1,z2,z7,z4,z5,z82,z97]),(1,[z1,z2,z7,z4,z5,z235]),(0,[z1,z236,z2,z7,z4,z5,z6])],[(0,[z90,z1,z2,z7,z35,z4,z5]),(0,[z1,z20,z2,z7,z4,z5,z10]),(0,[z1,z2,z7,z165,z4,z5,z10]),(0,[z1,z237,z2,z7,z4,z5,z6]),(0,[z50,z1,z2,z7,z4,z238,z6]),(0,[z1,z21,z2,z7,z4,z142,z6])],[(0,[z16,z1,z2,z7,z4,z5,z6]),(0,[z0,z1,z139,z7,z4,z5,z6]),(0,[z1,z2,z7,z239,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z136,z10]),(0,[z1,z2,z7,z180,z4,z5,z6]),(1,[z1,z2,z7,z130,z4,z5]),(0,[z1,z22,z2,z7,z35,z5,z6])],[(0,[z1,z2,z7,z4,z5,z240,z6]),(0,[z1,z112,z2,z7,z4,z5,z9])],[(0,[z90,z1,z2,z7,z241,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z208]),(0,[z54,z1,z22,z2,z7,z4,z5]),(0,[z1,z2,z7,z4,z5,z242,z6]),(0,[z1,z2,z7,z4,z5,z101,z6]),(0,[z1,z22,z2,z121,z7,z4,z5])],[(0,[z243,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z165,z4,z76,z6]),(0,[z1,z18,z2,z7,z4,z5,z10])]],
   [[(0,[z1,z244,z2,z7,z4,z5,z127]),(0,[z1,z245,z2,z7,z4,z5,z6]),(0,[z246,z1,z2,z7,z4,z5,z6]),(0,[z1,z79,z2,z4,z5,z82,z6]),(0,[z1,z2,z247,z7,z4,z5,z6])],[(0,[z1,z2,z7,z4,z5,z248,z6]),(0,[z1,z22,z2,z7,z4,z142,z5])],[(0,[z249,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z35,z4,z5,z56]),(0,[z250,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z251,z7,z4,z5,z6])],[(0,[z1,z18,z2,z7,z4,z76,z6]),(0,[z1,z2,z252,z7,z4,z5,z6]),(0,[z1,z2,z253,z7,z4,z5,z6]),(0,[z1,z81,z2,z7,z4,z5,z97]),(0,[z254,z1,z22,z2,z7,z4,z5])],[(0,[z1,z2,z7,z4,z255,z5,z6]),(0,[z1,z2,z256,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z37,z6]),(0,[z1,z2,z7,z4,z257,z5,z6])],[(0,[z90,z1,z258,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z206,z6]),(0,[z166,z1,z2,z38,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z259,z6]),(0,[z1,z260,z2,z7,z4,z5,z6])],[(0,[z1,z2,z7,z8,z35,z4,z5]),(0,[z261,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z49,z7,z4,z5,z6]),(0,[z1,z112,z2,z7,z4,z5,z262]),(0,[z1,z2,z7,z4,z5,z6,z263])],[(0,[z1,z2,z7,z264,z4,z5,z6]),(0,[z1,z2,z7,z4,z56,z37,z6]),(0,[z1,z2,z265,z7,z4,z5,z6]),(0,[z203,z1,z22,z2,z7,z4,z5]),(0,[z1,z2,z7,z266,z4,z5,z6]),(1,[z1,z2,z7,z35,z5,z136])]],
   [[(0,[z1,z2,z7,z4,z5,z6,z267]),(0,[z1,z2,z7,z4,z5,z6,z268]),(0,[z1,z269,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z9,z6]),(0,[z1,z2,z7,z4,z131,z5,z6])],[(0,[z270,z1,z2,z7,z4,z5,z6]),(0,[z2,z7,z4,z19,z5,z76,z6]),(0,[z1,z271,z2,z7,z4,z5,z6]),(0,[z1,z272,z2,z7,z4,z5,z6]),(0,[z54,z1,z2,z121,z7,z4,z5]),(0,[z1,z2,z7,z4,z273,z5,z6]),(0,[z274,z1,z2,z7,z4,z5,z6])],[(1,[z1,z2,z7,z4,z5,z275]),(0,[z1,z2,z7,z4,z5,z276,z6]),(0,[z1,z2,z7,z4,z277,z5,z6]),(0,[z1,z112,z2,z7,z4,z23,z6]),(0,[z1,z2,z7,z4,z5,z278,z6]),(1,[z1,z2,z7,z4,z5,z58]),(1,[z1,z2,z7,z35,z4,z5])],[(0,[z1,z279,z2,z7,z4,z5,z6]),(0,[z1,z280,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z281,z5,z6]),(0,[z1,z2,z7,z4,z5,z10,z210]),(0,[z1,z2,z7,z25,z4,z5,z9]),(0,[z1,z22,z244,z2,z7,z4,z5]),(0,[z1,z2,z7,z4,z5,z282,z6]),(0,[z1,z215,z22,z2,z7,z4,z5])],[(0,[z1,z2,z7,z4,z108,z5,z9]),(0,[z1,z2,z7,z4,z283,z5,z6]),(0,[z62,z2,z7,z4,z5,z76,z6]),(0,[z1,z2,z7,z284,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z82,z9]),(0,[z285,z1,z2,z7,z4,z5,z6]),(0,[z286,z1,z2,z7,z4,z5,z6]),(0,[z1,z22,z112,z2,z7,z4,z5]),(0,[z1,z2,z226,z7,z4,z5,z6]),(0,[z287,z1,z2,z7,z4,z5,z6])],[(1,[z1,z2,z7,z241,z5,z6]),(0,[z288,z1,z2,z7,z4,z5,z6]),(0,[z90,z1,z2,z7,z4,z5,z85]),(0,[z1,z183,z2,z7,z4,z5,z10]),(0,[z1,z2,z7,z4,z5,z113,z9]),(0,[z289,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z290,z7,z4,z5,z6])],[(0,[z291,z1,z2,z7,z4,z5,z10]),(1,[z72,z2,z7,z4,z5,z9]),(0,[z1,z2,z7,z4,z5,z9,z292]),(0,[z1,z2,z7,z158,z4,z5,z6]),(0,[z1,z2,z7,z4,z110,z5,z6]),(0,[z1,z22,z2,z7,z4,z5,z56])],[(0,[z166,z1,z2,z7,z4,z5,z9]),(0,[z109,z1,z2,z7,z4,z5,z6]),(0,[z1,z293,z2,z7,z4,z5,z6])]],
   [[(0,[z1,z2,z139,z7,z4,z5,z10]),(0,[z1,z2,z7,z4,z294,z5,z6]),(0,[z254,z1,z2,z7,z4,z5,z10]),(0,[z72,z1,z2,z7,z35,z4,z5]),(0,[z50,z1,z7,z4,z30,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z295])],[(0,[z1,z296,z2,z7,z4,z5,z6]),(0,[z1,z297,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z298]),(1,[z1,z2,z7,z4,z5,z101])],[(0,[z0,z1,z2,z7,z150,z5,z6]),(0,[z1,z2,z299,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z300,z6]),(0,[z1,z2,z7,z301,z4,z5,z6]),(0,[z74,z1,z2,z7,z4,z5,z9]),(1,[z1,z2,z7,z164,z4,z5]),(0,[z1,z2,z7,z4,z5,z6,z188]),(0,[z1,z2,z302,z7,z4,z5,z6]),(0,[z1,z303,z2,z7,z4,z5,z6]),(0,[z1,z112,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z304,z5,z6]),(0,[z1,z2,z305,z7,z4,z5,z6])],[(0,[z77,z1,z2,z7,z4,z5,z9])],[(0,[z16,z1,z22,z2,z7,z4,z5]),(1,[z1,z258,z7,z4,z5,z6]),(0,[z1,z306,z2,z7,z4,z5,z6]),(0,[z69,z74,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z307,z5,z6]),(0,[z1,z2,z7,z308,z4,z5,z6]),(1,[z1,z2,z7,z4,z5,z127]),(0,[z1,z2,z7,z4,z5,z6,z100]),(0,[z1,z2,z7,z309,z4,z5,z6]),(0,[z1,z2,z7,z4,z11,z5,z6]),(0,[z1,z2,z7,z310,z4,z5,z6]),(0,[z1,z2,z7,z35,z4,z59,z5]),(0,[z1,z2,z7,z4,z131,z5,z190])],[(0,[z1,z17,z2,z7,z35,z4,z5]),(0,[z1,z2,z7,z4,z5,z311,z6]),(0,[z1,z312,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z9,z313]),(0,[z1,z81,z2,z7,z4,z5,z9]),(0,[z1,z2,z7,z314,z4,z5,z6]),(0,[z315,z1,z2,z7,z4,z5,z6]),(1,[z1,z2,z67,z7,z4,z5]),(0,[z1,z22,z2,z7,z4,z316,z5])],[(0,[z1,z2,z7,z61,z158,z5,z6]),(0,[z1,z2,z317,z7,z4,z5,z6]),(0,[z1,z48,z2,z7,z35,z4,z5]),(0,[z318,z1,z2,z7,z4,z5,z6]),(1,[z1,z112,z2,z4,z23,z6])],[(0,[z1,z2,z7,z4,z319,z5,z6]),(0,[z1,z2,z47,z7,z4,z23,z6]),(0,[z1,z2,z7,z4,z5,z320,z6])]],
   [[(0,[z1,z321,z2,z7,z4,z5,z6]),(0,[z74,z1,z2,z7,z4,z5,z322]),(0,[z1,z244,z2,z7,z4,z5,z10]),(1,[z1,z244,z7,z158,z5,z6]),(0,[z1,z40,z7,z4,z5,z56,z6]),(1,[z1,z18,z2,z7,z37,z6])],[(0,[z77,z1,z2,z7,z4,z5,z27]),(0,[z1,z2,z7,z4,z5,z323,z10])],[(0,[z1,z2,z7,z4,z324,z5,z6]),(0,[z1,z2,z7,z35,z4,z57,z5])],[(1,[z1,z2,z7,z4,z5,z325]),(0,[z1,z2,z7,z4,z5,z138,z6])],[(0,[z1,z2,z258,z7,z4,z5,z6]),(1,[z1,z2,z7,z4,z5,z85]),(0,[z166,z1,z2,z7,z4,z5,z311]),(0,[z1,z326,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z327,z6]),(0,[z328,z1,z2,z7,z4,z5,z6]),(0,[z1,z329,z2,z7,z4,z5,z6]),(0,[z1,z20,z2,z7,z35,z4,z5]),(0,[z1,z2,z13,z7,z4,z5,z330]),(0,[z1,z2,z7,z4,z5,z331,z6])],[(0,[z1,z2,z332,z7,z4,z5,z6]),(0,[z1,z2,z333,z7,z4,z5,z6]),(0,[z1,z228,z2,z7,z4,z5,z10]),(0,[z1,z2,z334,z7,z4,z5,z6]),(0,[z335,z1,z2,z7,z4,z5,z6]),(0,[z1,z18,z112,z2,z7,z4,z6]),(0,[z1,z2,z7,z336,z4,z5,z6])],[(0,[z1,z2,z7,z4,z5,z43,z6]),(0,[z1,z2,z7,z4,z142,z19,z6]),(0,[z1,z2,z13,z7,z4,z5,z9]),(0,[z1,z2,z7,z337,z4,z5,z6]),(1,[z1,z2,z7,z4,z149,z5]),(0,[z1,z2,z7,z338,z4,z5,z6]),(0,[z1,z2,z7,z5,z136,z6,z83]),(0,[z1,z2,z339,z7,z4,z5,z6])],[(0,[z1,z2,z7,z340,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z341,z6]),(0,[z1,z2,z7,z4,z5,z97,z153]),(0,[z1,z2,z47,z7,z4,z5,z6]),(0,[z1,z79,z2,z7,z4,z5,z82]),(1,[z1,z22,z2,z7,z4,z5])]],
   [[(0,[z1,z2,z7,z4,z5,z342,z6]),(0,[z1,z2,z7,z343,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z238,z6]),(0,[z344,z1,z2,z7,z4,z5,z6]),(0,[z345,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z346,z4,z5,z6]),(0,[z1,z18,z2,z7,z35,z4,z5]),(0,[z1,z22,z2,z347,z7,z4,z5])],[(0,[z16,z1,z2,z7,z4,z5,z10]),(0,[z1,z2,z7,z4,z108,z5,z6]),(0,[z1,z2,z7,z4,z5,z10,z267]),(0,[z1,z2,z7,z4,z5,z10,z268]),(0,[z1,z348,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z82,z6])],[(0,[z1,z2,z7,z4,z5,z349,z6]),(0,[z50,z1,z2,z7,z30,z5,z6]),(0,[z1,z2,z7,z35,z4,z5,z97]),(0,[z1,z350,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z351,z6])],[(0,[z352,z1,z2,z7,z4,z5,z6]),(0,[z1,z17,z7,z25,z4,z5,z6]),(0,[z1,z22,z17,z2,z7,z4,z5]),(0,[z1,z2,z7,z4,z353,z5,z9]),(1,[z1,z2,z7,z354,z4,z5]),(0,[z1,z2,z7,z4,z355,z5,z6])],[(0,[z166,z1,z2,z7,z4,z5,z6]),(1,[z1,z2,z7,z78,z5,z6]),(0,[z1,z356,z2,z7,z4,z5,z6]),(0,[z1,z357,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z358,z6]),(0,[z1,z18,z2,z7,z5,z37,z6])],[(0,[z1,z2,z7,z4,z5,z6,z359]),(0,[z1,z2,z7,z4,z12,z5,z10]),(0,[z1,z34,z2,z7,z4,z5,z9]),(0,[z1,z22,z20,z2,z7,z4,z5]),(0,[z1,z22,z2,z7,z25,z4,z5]),(0,[z360,z1,z2,z7,z4,z5,z6]),(0,[z361,z1,z2,z7,z4,z5,z6]),(0,[z1,z362,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z262])],[(0,[z363,z1,z2,z7,z4,z5,z6]),(1,[z1,z2,z7,z4,z5,z364]),(0,[z1,z49,z7,z25,z4,z5,z6]),(0,[z1,z2,z7,z4,z365,z5,z6]),(0,[z1,z22,z2,z7,z4,z57,z5])],[(0,[z366,z1,z2,z7,z4,z5,z6]),(0,[z1,z40,z21,z7,z4,z5,z6]),(0,[z1,z2,z7,z367,z4,z5,z6]),(0,[z1,z2,z162,z7,z35,z4,z5]),(0,[z1,z368,z2,z7,z4,z5,z6])]],
   [[(0,[z1,z369,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z370,z4,z5,z6])],[(0,[z371,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z164,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z37,z10]),(0,[z50,z1,z2,z7,z4,z5,z9]),(0,[z1,z372,z2,z7,z4,z5,z6]),(0,[z1,z2,z373,z7,z4,z5,z6]),(0,[z1,z2,z374,z7,z4,z5,z6])],[(0,[z1,z2,z7,z4,z5,z6,z375]),(0,[z1,z2,z7,z4,z5,z376,z6]),(0,[z1,z2,z7,z4,z5,z377,z6]),(0,[z1,z2,z7,z4,z378,z5,z6]),(0,[z1,z379,z2,z7,z4,z5,z6])],[(0,[z1,z2,z49,z7,z4,z5,z10]),(0,[z1,z21,z2,z7,z4,z5,z10]),(0,[z1,z2,z7,z4,z380,z5,z6])],[(0,[z1,z2,z7,z4,z381,z5,z6]),(0,[z1,z382,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z330,z6]),(0,[z1,z2,z7,z4,z383,z5,z6]),(0,[z384,z1,z2,z7,z35,z4,z5]),(0,[z1,z2,z7,z178,z35,z4,z5])],[(0,[z385,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z9,z10]),(0,[z1,z2,z7,z4,z5,z10,z100]),(0,[z1,z48,z2,z7,z4,z33,z6]),(0,[z1,z2,z7,z4,z5,z6,z386]),(0,[z1,z2,z7,z4,z387,z5,z6]),(1,[z1,z79,z2,z4,z5,z82])],[(0,[z1,z2,z7,z4,z5,z388,z6]),(0,[z1,z2,z7,z35,z4,z5,z76]),(0,[z1,z2,z7,z4,z23,z5,z10]),(0,[z1,z21,z7,z4,z142,z5,z6]),(0,[z1,z22,z2,z7,z4,z5,z97])],[]],
   [[(0,[z1,z2,z7,z4,z5,z389,z6]),(0,[z1,z2,z140,z7,z4,z5,z6]),(0,[z1,z390,z2,z7,z4,z5,z6])],[(0,[z1,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z139,z7,z35,z4,z5]),(0,[z90,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z6]),(0,[z1,z2,z7,z4,z5,z9,z327]),(0,[z1,z79,z2,z7,z4,z5,z153]),(0,[z254,z1,z2,z7,z35,z4,z5]),(0,[z1,z2,z7,z391,z35,z4,z5])],[(0,[z1,z2,z7,z4,z23,z76,z6]),(0,[z1,z2,z392,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z131,z190,z6])],[(0,[z393,z1,z2,z7,z4,z5,z6]),(0,[z69,z1,z2,z7,z4,z5,z220]),(0,[z1,z2,z7,z4,z394,z5,z6]),(1,[z109,z2,z7,z4,z5,z10]),(0,[z1,z2,z7,z4,z5,z6,z395])],[(0,[z396,z1,z2,z7,z4,z5,z6]),(0,[z74,z1,z2,z7,z4,z397,z6]),(0,[z398,z1,z2,z7,z4,z5,z6]),(0,[z50,z1,z18,z2,z7,z5,z6]),(0,[z1,z2,z7,z4,z5,z399,z6]),(0,[z400,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z165,z4,z37,z6]),(0,[z1,z2,z7,z4,z5,z325,z6])],[(0,[z1,z401,z2,z7,z4,z5,z9]),(0,[z1,z2,z7,z4,z5,z190,z9]),(0,[z1,z2,z402,z7,z4,z5,z6]),(0,[z1,z244,z7,z158,z4,z5,z6]),(0,[z403,z1,z2,z7,z4,z5,z6]),(0,[z404,z1,z2,z7,z4,z5,z6]),(0,[z1,z18,z22,z2,z7,z4,z5]),(0,[z1,z2,z7,z4,z316,z5,z6])],[(0,[z405,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z406,z5,z6])],[(0,[z2,z38,z7,z8,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z71]),(0,[z1,z112,z2,z7,z4,z5,z10]),(0,[z1,z2,z7,z4,z142,z5,z6]),(0,[z1,z18,z2,z7,z4,z57,z6]),(0,[z1,z2,z67,z7,z4,z5,z37]),(0,[z407,z1,z2,z7,z4,z5,z6])]],
   [[(1,[z1,z2,z7,z4,z5,z408]),(0,[z0,z1,z22,z2,z7,z4,z5]),(0,[z17,z2,z139,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z409,z5,z6]),(0,[z1,z18,z2,z7,z4,z37,z6]),(0,[z1,z2,z7,z211,z35,z4,z5])],[(0,[z1,z2,z410,z7,z4,z5,z6]),(0,[z1,z244,z2,z7,z35,z4,z5]),(0,[z1,z2,z7,z354,z4,z12,z5])],[(0,[z1,z22,z2,z7,z4,z5,z76]),(0,[z1,z2,z411,z7,z4,z5,z6]),(0,[z1,z34,z2,z7,z4,z5,z6])],[(0,[z1,z2,z7,z4,z412,z5,z6]),(1,[z1,z2,z7,z180,z4,z5]),(0,[z1,z2,z7,z4,z5,z9,z83]),(0,[z1,z79,z22,z2,z7,z4,z5])],[(0,[z1,z413,z2,z7,z4,z5,z6])],[(0,[z1,z2,z7,z4,z19,z56,z6]),(0,[z1,z2,z414,z7,z4,z5,z6])],[(1,[z1,z48,z49,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z415,z6]),(1,[z1,z2,z7,z4,z238,z6]),(0,[z1,z416,z2,z7,z4,z5,z6]),(0,[z1,z40,z2,z7,z4,z56,z6]),(0,[z1,z2,z7,z4,z5,z417,z6]),(0,[z1,z2,z7,z418,z4,z5,z6]),(0,[z419,z1,z2,z7,z4,z5,z6])],[(0,[z1,z2,z7,z35,z4,z108,z5]),(1,[z1,z198,z2,z7,z4,z5]),(0,[z1,z2,z7,z420,z4,z5,z6]),(0,[z1,z2,z121,z7,z4,z5,z9])]],
   [[(0,[z1,z421,z2,z7,z4,z5,z6]),(1,[z74,z2,z7,z61,z5,z6]),(0,[z1,z2,z47,z4,z5,z113,z6]),(0,[z1,z422,z2,z7,z4,z5,z6]),(1,[z1,z2,z7,z165,z57,z6])],[(1,[z1,z2,z94,z4,z5,z6]),(0,[z1,z2,z7,z4,z423,z5,z6]),(0,[z1,z2,z7,z424,z4,z5,z6]),(0,[z1,z18,z2,z7,z108,z5,z6]),(0,[z74,z1,z2,z7,z61,z5,z6]),(0,[z1,z2,z7,z425,z4,z5,z6]),(0,[z1,z2,z7,z4,z426,z5,z6])],[(0,[z16,z1,z2,z7,z4,z5,z275]),(0,[z16,z1,z2,z7,z35,z4,z5]),(0,[z1,z22,z2,z7,z5,z6,z83])],[(0,[z427,z1,z2,z7,z4,z5,z6]),(0,[z428,z1,z2,z7,z4,z5,z6]),(0,[z429,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z430,z6])],[(0,[z1,z431,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z7,z4,z5,z6]),(0,[z90,z2,z7,z8,z4,z5,z6]),(0,[z1,z2,z47,z7,z4,z5,z10]),(0,[z1,z2,z7,z4,z5,z56,z6]),(0,[z1,z432,z2,z7,z4,z5,z6]),(0,[z433,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z434,z5,z6])],[(0,[z0,z1,z2,z7,z4,z5,z10]),(0,[z1,z2,z435,z7,z4,z5,z6]),(0,[z436,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z35,z61,z4,z5]),(0,[z1,z2,z437,z7,z4,z5,z6]),(0,[z1,z48,z2,z49,z4,z5,z6]),(1,[z54,z1,z7,z4,z5,z97]),(0,[z1,z2,z438,z7,z4,z5,z6]),(0,[z191,z1,z22,z2,z7,z4,z5])],[(0,[z1,z2,z7,z4,z108,z5,z10]),(0,[z1,z401,z2,z7,z61,z4,z5]),(0,[z1,z2,z7,z4,z30,z5,z9]),(0,[z1,z2,z7,z129,z4,z30,z5]),(0,[z1,z2,z7,z439,z4,z5,z6]),(0,[z1,z2,z440,z7,z4,z5,z6])],[(0,[z1,z2,z7,z4,z19,z5,z9]),(0,[z1,z2,z7,z4,z5,z441,z6]),(0,[z1,z2,z7,z4,z5,z442,z6]),(0,[z1,z2,z7,z4,z5,z443,z6]),(0,[z1,z2,z7,z4,z5,z82,z100]),(0,[z1,z2,z444,z7,z4,z12,z5]),(1,[z1,z2,z47,z4,z113,z6]),(0,[z1,z445,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z446,z6]),(0,[z1,z2,z7,z4,z131,z5,z82])]],
   [[(0,[z1,z447,z2,z7,z4,z5,z6]),(0,[z1,z79,z2,z7,z4,z5,z10]),(0,[z1,z448,z2,z7,z4,z5,z6]),(0,[z1,z112,z2,z7,z4,z5,z235]),(0,[z1,z2,z7,z4,z449,z5,z6]),(0,[z1,z2,z7,z4,z5,z450,z6])],[(0,[z77,z62,z2,z7,z4,z5,z6]),(0,[z50,z1,z2,z7,z57,z5,z6])],[(0,[z1,z401,z2,z7,z4,z5,z6]),(0,[z1,z2,z451,z7,z4,z5,z6]),(0,[z1,z112,z2,z7,z4,z142,z6]),(0,[z1,z2,z7,z4,z5,z6,z452])],[(1,[z1,z2,z7,z423,z5,z6]),(0,[z1,z22,z2,z7,z4,z108,z5]),(0,[z1,z2,z7,z4,z453,z5,z6]),(0,[z1,z454,z2,z7,z4,z5,z6]),(0,[z1,z2,z226,z7,z4,z5,z82]),(0,[z1,z2,z7,z4,z5,z6,z455])],[(0,[z1,z2,z7,z4,z456,z5,z6]),(0,[z1,z2,z7,z4,z457,z5,z6]),(0,[z1,z458,z2,z7,z4,z5,z6]),(0,[z1,z2,z49,z7,z35,z4,z5]),(0,[z1,z21,z2,z7,z35,z4,z5]),(0,[z1,z2,z7,z4,z5,z459,z6])],[(0,[z1,z2,z7,z4,z177,z30,z6]),(0,[z1,z2,z460,z7,z4,z12,z6]),(0,[z1,z2,z7,z4,z5,z6,z461])],[(0,[z1,z2,z7,z164,z4,z5,z10]),(0,[z1,z2,z7,z4,z5,z6,z462])],[(0,[z1,z2,z7,z4,z463,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z464]),(0,[z1,z2,z7,z4,z5,z179,z10]),(0,[z1,z2,z7,z4,z5,z465,z6]),(0,[z1,z466,z2,z7,z4,z5,z6])]],
   [[(0,[z467,z1,z2,z7,z4,z5,z6]),(0,[z1,z81,z2,z7,z4,z5,z100]),(1,[z1,z2,z7,z4,z11,z6]),(0,[z1,z22,z468,z2,z7,z4,z5])],[(0,[z0,z1,z2,z7,z4,z5,z408]),(0,[z1,z469,z2,z139,z4,z5,z6]),(0,[z1,z22,z2,z7,z61,z4,z5]),(0,[z1,z470,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z142,z57,z6]),(0,[z1,z22,z81,z2,z7,z4,z5]),(0,[z1,z34,z2,z13,z4,z5,z6]),(0,[z1,z2,z14,z4,z12,z5,z6]),(0,[z1,z2,z7,z471,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z472,z6]),(0,[z1,z22,z2,z473,z7,z4,z5])],[(0,[z1,z2,z7,z4,z5,z84,z6]),(0,[z77,z1,z2,z7,z4,z19,z6]),(0,[z1,z474,z2,z7,z4,z5,z6])],[(0,[z90,z1,z2,z38,z4,z5,z6]),(1,[z1,z2,z444,z7,z4,z5])],[(0,[z90,z1,z2,z7,z4,z475,z6]),(0,[z1,z2,z476,z7,z4,z5,z6]),(0,[z1,z2,z7,z70,z4,z108,z5]),(0,[z77,z1,z2,z7,z477,z5,z6])],[(0,[z1,z2,z7,z4,z475,z5,z6]),(1,[z166,z2,z38,z4,z5,z6]),(0,[z62,z1,z2,z7,z4,z19,z6]),(0,[z1,z2,z7,z478,z4,z5,z6]),(0,[z1,z479,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z480,z5,z6]),(0,[z1,z88,z2,z7,z35,z4,z5])],[(0,[z481,z1,z2,z7,z4,z5,z6]),(0,[z1,z1,z2,z7,z4,z5,z10]),(0,[z1,z2,z7,z4,z482,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z483])],[(0,[z1,z2,z7,z4,z484,z5,z6]),(0,[z1,z2,z485,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z31,z6]),(0,[z1,z2,z47,z7,z4,z142,z6]),(0,[z1,z2,z486,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z487,z5,z6]),(0,[z1,z2,z7,z488,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z489])]],
   [[(0,[z1,z2,z490,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z491,z5,z6]),(0,[z1,z112,z2,z7,z35,z4,z5]),(0,[z1,z22,z492,z2,z7,z4,z5]),(1,[z1,z2,z121,z7,z4,z199])],[(0,[z1,z2,z7,z4,z5,z493,z6]),(0,[z62,z1,z2,z7,z4,z5,z9]),(0,[z1,z2,z7,z4,z5,z9,z153]),(0,[z1,z2,z7,z4,z131,z5,z153])],[(0,[z1,z2,z494,z7,z4,z5,z6]),(0,[z69,z1,z2,z7,z4,z5,z9]),(0,[z1,z2,z7,z4,z5,z495,z6]),(0,[z1,z2,z496,z7,z4,z5,z6]),(0,[z1,z497,z2,z7,z4,z5,z6])],[(0,[z1,z2,z7,z4,z5,z322,z6]),(0,[z1,z2,z7,z4,z5,z6,z498]),(0,[z1,z2,z7,z4,z30,z5,z6]),(0,[z1,z2,z499,z7,z4,z5,z6]),(0,[z1,z2,z500,z7,z4,z5,z6]),(0,[z1,z2,z7,z501,z4,z5,z6])],[(0,[z1,z2,z7,z4,z5,z275,z6]),(0,[z1,z2,z7,z502,z4,z5,z6]),(0,[z1,z2,z7,z4,z19,z5,z6]),(0,[z1,z2,z7,z4,z142,z5,z10]),(0,[z1,z2,z7,z503,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z504,z6]),(0,[z1,z2,z7,z354,z4,z5,z6]),(0,[z505,z1,z2,z7,z4,z5,z6])],[(0,[z90,z1,z2,z7,z4,z5,z9]),(0,[z166,z1,z48,z2,z4,z5,z6]),(0,[z1,z2,z506,z7,z4,z5,z6]),(0,[z1,z2,z226,z7,z4,z5,z153])],[(0,[z507,z1,z2,z7,z4,z5,z6]),(0,[z508,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z19,z113,z6])],[(0,[z509,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z411,z7,z4,z5,z10]),(0,[z1,z2,z510,z7,z4,z5,z9]),(0,[z1,z2,z7,z4,z5,z511,z6]),(0,[z1,z512,z2,z7,z4,z5,z6]),(0,[z1,z513,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z325,z37])]],
   [[(0,[z1,z2,z7,z4,z142,z76,z6]),(0,[z1,z2,z7,z4,z5,z514,z6]),(0,[z1,z22,z40,z2,z7,z4,z5]),(0,[z1,z2,z7,z130,z4,z5,z6]),(0,[z1,z515,z2,z7,z4,z5,z6]),(0,[z1,z2,z121,z7,z4,z5,z190]),(0,[z1,z2,z7,z4,z5,z516,z6])],[(0,[z1,z2,z7,z4,z517,z5,z6])],[(0,[z1,z469,z2,z7,z4,z5,z6]),(0,[z1,z518,z2,z7,z4,z5,z6])],[(1,[z1,z2,z7,z4,z475,z6]),(0,[z74,z1,z2,z7,z4,z172,z6]),(0,[z1,z2,z7,z4,z5,z5,z6]),(0,[z1,z2,z7,z25,z4,z5,z6]),(0,[z50,z1,z244,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z57,z56,z6])],[(1,[z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z519,z7,z4,z5,z6]),(0,[z1,z520,z2,z7,z4,z5,z6]),(1,[z1,z2,z7,z4,z33,z6]),(0,[z1,z2,z7,z4,z5,z6,z83])],[(0,[z1,z2,z7,z14,z61,z5,z6]),(0,[z1,z244,z2,z7,z158,z5,z6]),(0,[z1,z2,z47,z7,z35,z4,z5]),(0,[z1,z2,z7,z4,z5,z113,z6]),(0,[z521,z1,z2,z7,z4,z5,z6])],[(0,[z0,z1,z2,z7,z35,z4,z5]),(0,[z1,z2,z7,z108,z30,z5,z6]),(0,[z1,z2,z7,z78,z4,z5,z6]),(0,[z1,z2,z7,z4,z149,z5,z6]),(0,[z1,z2,z522,z7,z4,z5,z6])],[(0,[z1,z2,z7,z4,z5,z523,z6]),(0,[z1,z2,z7,z4,z5,z9,z199]),(0,[z1,z2,z7,z35,z4,z30,z5]),(0,[z524,z1,z2,z7,z4,z5,z6]),(0,[z1,z525,z2,z7,z4,z5,z6]),(0,[z1,z526,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z131,z5,z199])]],
   [[(0,[z1,z2,z527,z7,z4,z5,z6]),(1,[z1,z2,z7,z4,z5,z75]),(0,[z62,z1,z2,z7,z4,z5,z528]),(0,[z1,z2,z7,z4,z5,z10,z464]),(0,[z1,z2,z7,z4,z5,z6,z529]),(0,[z1,z530,z2,z7,z4,z5,z6]),(0,[z1,z531,z2,z7,z4,z5,z6])],[(1,[z1,z2,z7,z4,z5,z342]),(0,[z1,z2,z38,z7,z4,z5,z9]),(0,[z1,z2,z7,z4,z5,z56,z10]),(0,[z1,z2,z7,z4,z5,z532,z6]),(0,[z1,z2,z7,z35,z4,z12,z5]),(0,[z1,z79,z2,z7,z35,z4,z5])],[(0,[z533,z1,z2,z7,z4,z5,z6]),(0,[z74,z1,z2,z7,z4,z5,z6]),(0,[z109,z1,z22,z2,z7,z4,z5]),(0,[z1,z22,z2,z49,z7,z4,z5]),(0,[z1,z2,z444,z7,z4,z5,z6]),(1,[z1,z2,z7,z4,z5,z330]),(0,[z1,z2,z7,z35,z266,z4,z5])],[(0,[z77,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z129,z4,z5,z6]),(0,[z1,z18,z244,z2,z7,z5,z6]),(0,[z1,z357,z2,z7,z5,z56,z6]),(0,[z1,z2,z4,z23,z5,z113,z6]),(0,[z1,z2,z7,z35,z4,z5,z136])],[(0,[z1,z2,z7,z4,z5,z442,z10]),(0,[z51,z1,z2,z7,z4,z5,z6])],[(0,[z1,z2,z7,z4,z57,z5,z9]),(0,[z1,z20,z7,z25,z4,z5,z6]),(0,[z1,z81,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z534,z6])],[(0,[z62,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z35,z4,z4,z5])],[(0,[z1,z535,z2,z7,z4,z5,z6]),(0,[z69,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z10,z10]),(0,[z536,z1,z2,z7,z4,z5,z6]),(0,[z1,z537,z2,z7,z4,z5,z6]),(0,[z1,z2,z538,z7,z4,z5,z6]),(0,[z1,z2,z7,z35,z4,z5,z100]),(0,[z1,z2,z539,z7,z4,z5,z6]),(0,[z1,z2,z7,z164,z35,z4,z5])]],
   [[(0,[z1,z2,z7,z4,z5,z397,z6]),(0,[z1,z2,z7,z4,z131,z5,z10]),(1,[z1,z2,z7,z4,z5,z152]),(0,[z1,z40,z2,z7,z165,z4,z6]),(1,[z1,z22,z2,z7,z5,z83])],[(0,[z1,z18,z40,z2,z7,z4,z6]),(0,[z1,z2,z7,z540,z4,z5,z6])],[(1,[z69,z2,z7,z108,z5,z6]),(0,[z1,z541,z2,z7,z4,z5,z6]),(1,[z1,z2,z7,z4,z5,z322]),(0,[z72,z1,z2,z7,z4,z5,z9]),(0,[z1,z2,z7,z4,z5,z6,z542])],[(0,[z1,z2,z543,z7,z4,z5,z6]),(0,[z1,z544,z2,z7,z4,z5,z6]),(0,[z1,z22,z2,z7,z4,z30,z5]),(0,[z1,z2,z545,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z546,z6])],[(0,[z1,z2,z510,z7,z4,z5,z6]),(0,[z62,z1,z2,z7,z4,z5,z71]),(0,[z1,z2,z7,z4,z547,z5,z6]),(0,[z1,z2,z226,z7,z4,z5,z10]),(0,[z1,z2,z7,z4,z5,z548,z6])],[(1,[z1,z2,z7,z4,z5,z359]),(0,[z1,z22,z2,z7,z4,z12,z5]),(0,[z1,z2,z7,z4,z5,z6,z549])],[(1,[z77,z2,z7,z4,z19,z6]),(0,[z1,z2,z7,z158,z4,z5,z10]),(0,[z1,z2,z13,z7,z4,z5,z6]),(0,[z1,z22,z2,z47,z7,z4,z5])],[(0,[z1,z17,z2,z7,z4,z5,z9]),(0,[z1,z2,z7,z4,z5,z528,z6]),(0,[z1,z2,z7,z4,z5,z76,z9]),(0,[z109,z1,z2,z7,z4,z5,z10]),(0,[z109,z2,z7,z4,z5,z6,z10]),(0,[z1,z2,z7,z35,z4,z5,z9]),(0,[z1,z2,z7,z4,z5,z6,z58]),(0,[z1,z22,z2,z7,z4,z5,z136]),(0,[z1,z2,z7,z550,z4,z5,z6])]],
   [[(0,[z1,z48,z2,z7,z4,z5,z9]),(0,[z551,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z552,z4,z5,z6]),(0,[z1,z2,z7,z57,z5,z37,z6])],[(1,[z1,z2,z7,z4,z5,z311]),(0,[z1,z2,z7,z14,z4,z5,z9]),(0,[z1,z2,z7,z4,z5,z553,z6]),(0,[z1,z554,z2,z7,z4,z5,z6]),(0,[z1,z2,z13,z7,z12,z5,z6])],[(0,[z1,z139,z7,z25,z4,z5,z6]),(0,[z1,z2,z7,z165,z4,z19,z6]),(0,[z1,z2,z7,z4,z555,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z292]),(0,[z1,z2,z7,z556,z4,z5,z6]),(0,[z557,z1,z2,z7,z4,z5,z6]),(0,[z1,z22,z2,z7,z4,z4,z5])],[(0,[z1,z2,z7,z4,z353,z5,z6]),(0,[z558,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z559,z6]),(0,[z560,z1,z2,z7,z4,z5,z6]),(0,[z1,z22,z2,z7,z4,z5,z100]),(0,[z1,z2,z7,z35,z4,z5,z113])],[(0,[z1,z2,z561,z7,z4,z5,z6]),(0,[z1,z135,z2,z7,z4,z5,z6]),(0,[z54,z1,z2,z7,z4,z5,z97]),(0,[z1,z2,z562,z7,z4,z5,z6]),(0,[z1,z2,z563,z7,z4,z5,z6])],[(0,[z1,z564,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z565,z4,z5,z6]),(0,[z1,z566,z2,z7,z4,z5,z6]),(0,[z567,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z10,z83]),(1,[z1,z2,z7,z4,z5,z193]),(0,[z1,z568,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z569,z4,z5,z6])],[(0,[z1,z2,z7,z4,z5,z570,z6]),(0,[z1,z2,z38,z7,z4,z5,z6]),(0,[z1,z2,z7,z165,z4,z5,z9]),(0,[z1,z2,z7,z571,z4,z5,z6])],[(0,[z166,z1,z22,z2,z7,z4,z5]),(0,[z1,z2,z7,z4,z5,z136,z9]),(0,[z1,z2,z7,z4,z5,z572,z6]),(0,[z1,z525,z22,z2,z7,z4,z5])]],
   [[(0,[z1,z2,z7,z573,z4,z5,z6]),(0,[z1,z2,z7,z4,z574,z5,z6]),(0,[z1,z34,z2,z7,z12,z5,z6]),(0,[z1,z2,z575,z7,z4,z5,z6])],[(0,[z1,z2,z7,z576,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z313]),(0,[z50,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z121,z7,z4,z6,z199])],[(0,[z0,z1,z2,z7,z4,z5,z342]),(0,[z90,z1,z431,z7,z4,z5,z6]),(0,[z1,z2,z49,z8,z4,z5,z6]),(0,[z74,z1,z22,z2,z7,z4,z5]),(0,[z1,z2,z7,z4,z5,z577,z6]),(0,[z1,z2,z7,z4,z578,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z153]),(0,[z1,z2,z7,z4,z57,z5,z6]),(0,[z1,z579,z2,z7,z4,z5,z6]),(1,[z1,z22,z2,z7,z35,z5])],[(0,[z1,z2,z7,z4,z580,z5,z6]),(0,[z77,z1,z22,z2,z7,z4,z5]),(0,[z1,z22,z2,z7,z4,z5,z9]),(1,[z1,z21,z7,z4,z142,z6]),(0,[z581,z1,z2,z7,z4,z5,z6])],[(0,[z1,z2,z7,z4,z582,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z583]),(0,[z1,z584,z2,z7,z4,z5,z6]),(1,[z1,z492,z2,z7,z4,z5])],[(0,[z1,z2,z7,z108,z12,z5,z6]),(0,[z585,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z100,z153])],[(0,[z586,z1,z2,z7,z4,z5,z6]),(0,[z54,z1,z2,z7,z4,z5,z100]),(0,[z1,z2,z7,z4,z587,z5,z6]),(0,[z1,z22,z2,z13,z7,z4,z5]),(0,[z1,z2,z7,z4,z588,z5,z6])],[(1,[z1,z589,z2,z4,z5,z6]),(0,[z1,z48,z17,z7,z4,z5,z6]),(0,[z1,z2,z7,z590,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z591,z6]),(0,[z1,z18,z2,z47,z7,z4,z6]),(0,[z1,z22,z2,z7,z4,z5,z113]),(0,[z1,z2,z7,z4,z5,z592,z6])]],
   [[(1,[z1,z2,z7,z4,z5,z220]),(0,[z1,z2,z7,z61,z30,z5,z6]),(0,[z1,z2,z7,z25,z4,z5,z10]),(0,[z1,z2,z593,z7,z4,z5,z6])],[(1,[z0,z139,z7,z4,z5,z6]),(1,[z1,z469,z2,z4,z5,z6]),(0,[z69,z1,z2,z7,z61,z5,z6]),(0,[z1,z2,z7,z4,z5,z82,z10]),(0,[z1,z48,z20,z7,z4,z5,z6]),(0,[z1,z594,z2,z7,z4,z5,z6]),(0,[z595,z1,z2,z7,z4,z5,z6])],[(0,[z90,z1,z2,z7,z596,z5,z6]),(0,[z77,z1,z2,z7,z4,z5,z364]),(0,[z1,z2,z7,z4,z5,z6,z597]),(0,[z1,z2,z7,z4,z5,z113,z10]),(0,[z1,z2,z598,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z599]),(0,[z1,z600,z2,z7,z4,z5,z6])],[(0,[z1,z40,z2,z7,z4,z5,z9]),(0,[z1,z22,z2,z226,z7,z4,z5]),(0,[z1,z2,z7,z4,z5,z6,z601]),(0,[z1,z2,z7,z35,z4,z602,z5])],[(0,[z1,z17,z2,z7,z4,z5,z6]),(0,[z166,z1,z2,z7,z4,z5,z10]),(0,[z1,z2,z7,z4,z5,z76,z6]),(0,[z1,z2,z7,z4,z603,z5,z6]),(0,[z1,z2,z7,z4,z5,z604,z6]),(0,[z1,z2,z7,z35,z4,z5,z6])],[(0,[z1,z589,z2,z139,z4,z5,z6]),(0,[z1,z2,z7,z108,z57,z5,z6]),(0,[z1,z48,z2,z7,z4,z5,z6]),(0,[z1,z605,z2,z7,z4,z5,z6]),(0,[z1,z606,z2,z7,z4,z5,z6]),(0,[z1,z2,z226,z4,z5,z6,z153]),(0,[z1,z2,z7,z35,z165,z4,z5]),(0,[z1,z2,z7,z4,z5,z190,z6])],[(0,[z1,z607,z2,z7,z4,z5,z6]),(1,[z1,z2,z7,z4,z397,z6]),(0,[z54,z1,z2,z7,z4,z5,z9]),(0,[z1,z20,z2,z49,z4,z5,z6]),(0,[z50,z1,z2,z7,z4,z110,z6]),(0,[z1,z2,z7,z14,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z608])],[(0,[z1,z2,z7,z4,z596,z5,z6]),(0,[z74,z1,z2,z7,z4,z5,z10]),(0,[z1,z2,z7,z61,z4,z5,z9]),(0,[z1,z20,z2,z7,z4,z5,z193]),(1,[z1,z357,z2,z7,z5,z6])]],
   [[(0,[z77,z1,z2,z7,z4,z5,z10]),(0,[z404,z1,z22,z2,z7,z4,z5]),(0,[z1,z2,z7,z4,z5,z6,z199])],[(0,[z1,z609,z2,z7,z4,z5,z6]),(1,[z1,z431,z7,z4,z5,z6]),(1,[z1,z2,z7,z4,z5,z208]),(0,[z1,z2,z7,z4,z610,z5,z6])],[(0,[z1,z2,z611,z7,z4,z5,z6]),(0,[z1,z81,z2,z7,z4,z5,z10]),(0,[z1,z2,z7,z612,z4,z5,z6])],[(0,[z1,z2,z139,z7,z4,z5,z9]),(0,[z1,z2,z7,z613,z4,z5,z6]),(0,[z1,z22,z2,z38,z7,z4,z5]),(0,[z1,z2,z7,z4,z5,z6,z364]),(0,[z254,z1,z2,z7,z4,z5,z9]),(0,[z1,z21,z2,z7,z165,z4,z6]),(0,[z1,z2,z7,z4,z5,z614,z6]),(0,[z1,z2,z7,z165,z4,z5,z6])],[(0,[z77,z1,z2,z7,z4,z76,z6]),(0,[z1,z244,z2,z7,z30,z5,z6]),(0,[z1,z2,z7,z4,z615,z5,z6]),(0,[z616,z1,z2,z7,z4,z5,z6])],[(0,[z617,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z618,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z619]),(0,[z1,z2,z7,z4,z142,z37,z6]),(0,[z1,z2,z226,z7,z35,z4,z5]),(0,[z1,z620,z2,z7,z4,z5,z6])],[(0,[z621,z1,z2,z7,z4,z5,z6]),(0,[z1,z622,z2,z7,z4,z5,z6]),(0,[z77,z2,z7,z4,z19,z5,z6]),(0,[z1,z2,z347,z7,z4,z5,z6]),(0,[z623,z1,z2,z7,z4,z5,z6])],[(0,[z0,z2,z139,z7,z4,z5,z6]),(0,[z166,z1,z20,z2,z4,z5,z6]),(0,[z1,z624,z2,z7,z4,z5,z6]),(0,[z1,z2,z13,z7,z14,z5,z6]),(0,[z1,z2,z121,z7,z4,z5,z6])]],
   [[(0,[z1,z2,z7,z4,z5,z625,z6]),(0,[z109,z1,z2,z7,z35,z4,z5]),(0,[z1,z2,z7,z4,z5,z626,z6]),(0,[z1,z2,z627,z7,z4,z5,z6]),(0,[z1,z2,z628,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z629,z5,z6]),(0,[z1,z22,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z35,z4,z5,z190])],[(0,[z1,z630,z2,z7,z4,z5,z6]),(1,[z1,z2,z7,z596,z5,z6]),(0,[z1,z2,z7,z4,z547,z5,z10]),(0,[z1,z2,z7,z4,z5,z6,z10]),(0,[z50,z1,z22,z2,z7,z4,z5]),(1,[z1,z40,z7,z4,z56,z6]),(0,[z1,z2,z631,z7,z4,z5,z6]),(0,[z1,z2,z4,z5,z82,z6,z153]),(0,[z1,z22,z2,z7,z165,z4,z5])],[(0,[z16,z17,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z632,z6]),(0,[z1,z2,z633,z7,z4,z5,z6])],[(0,[z1,z634,z2,z7,z4,z5,z6]),(0,[z1,z2,z13,z7,z4,z5,z10]),(0,[z1,z2,z7,z4,z5,z10,z153]),(0,[z1,z244,z2,z7,z4,z5,z9]),(1,[z1,z296,z2,z7,z4,z6]),(0,[z1,z2,z7,z4,z635,z5,z6]),(0,[z1,z22,z2,z7,z14,z4,z5]),(0,[z1,z2,z7,z4,z5,z636,z6])],[(0,[z1,z2,z7,z4,z637,z5,z6])],[(0,[z0,z1,z2,z94,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z638,z6]),(0,[z1,z2,z38,z25,z4,z5,z6]),(0,[z1,z2,z7,z4,z639,z5,z6]),(0,[z1,z2,z7,z146,z4,z5,z6]),(0,[z1,z640,z2,z7,z4,z5,z6])],[(0,[z1,z589,z2,z7,z4,z5,z6]),(0,[z1,z641,z2,z7,z4,z5,z6]),(0,[z1,z198,z2,z7,z4,z108,z5]),(0,[z1,z34,z2,z7,z14,z5,z6]),(0,[z1,z2,z7,z165,z57,z5,z6]),(0,[z428,z1,z22,z2,z7,z4,z5])],[(0,[z1,z244,z2,z7,z4,z5,z152]),(0,[z1,z2,z7,z4,z5,z642,z6]),(0,[z1,z643,z2,z7,z4,z5,z6])]],
   [[(0,[z1,z2,z7,z4,z5,z6,z644]),(0,[z1,z40,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z645,z5,z6])],[(0,[z1,z2,z7,z70,z4,z5,z6]),(0,[z1,z2,z7,z646,z4,z5,z6]),(0,[z72,z2,z7,z4,z5,z9,z6]),(0,[z1,z2,z7,z4,z5,z647,z9]),(0,[z1,z7,z158,z4,z30,z5,z6]),(0,[z1,z2,z7,z4,z648,z5,z6]),(0,[z1,z2,z460,z7,z4,z5,z6]),(0,[z1,z2,z649,z7,z4,z5,z6]),(0,[z1,z492,z2,z7,z4,z5,z6])],[(1,[z1,z2,z7,z4,z73,z6]),(0,[z69,z2,z7,z4,z108,z5,z6]),(1,[z1,z401,z2,z7,z4,z5]),(0,[z650,z1,z2,z7,z4,z5,z6]),(0,[z1,z34,z2,z7,z4,z5,z10]),(1,[z1,z2,z7,z266,z4,z5])],[(0,[z1,z2,z38,z7,z4,z5,z10]),(0,[z1,z2,z7,z4,z477,z5,z6]),(0,[z384,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z651,z6]),(0,[z54,z1,z2,z7,z4,z5,z6])],[(0,[z16,z1,z2,z7,z4,z5,z9]),(0,[z652,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z49,z38,z4,z5,z6]),(0,[z1,z2,z7,z61,z4,z5,z6]),(0,[z1,z2,z7,z35,z4,z19,z5]),(0,[z1,z21,z2,z7,z4,z56,z6]),(0,[z1,z2,z7,z4,z5,z653,z6]),(0,[z1,z2,z7,z4,z654,z5,z6]),(0,[z1,z2,z7,z4,z5,z655,z6]),(0,[z1,z22,z2,z7,z4,z5,z190])],[(0,[z1,z2,z7,z4,z5,z6,z408]),(0,[z656,z1,z2,z7,z4,z5,z6]),(0,[z657,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z658,z6]),(0,[z54,z1,z7,z4,z5,z97,z6]),(0,[z659,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z121,z7,z4,z5,z153]),(0,[z1,z401,z22,z2,z7,z4,z5])],[(0,[z291,z1,z2,z7,z4,z5,z6]),(0,[z50,z1,z2,z7,z4,z5,z10]),(0,[z660,z1,z2,z7,z4,z5,z6])],[(0,[z0,z1,z2,z7,z423,z5,z6]),(0,[z90,z1,z2,z7,z4,z625,z6]),(0,[z1,z2,z7,z61,z12,z5,z6]),(0,[z1,z661,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z662])]],
   [[(0,[z254,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z139,z7,z4,z5,z6]),(0,[z90,z166,z2,z7,z4,z5,z6]),(0,[z90,z1,z2,z7,z4,z5,z523]),(0,[z1,z663,z2,z7,z4,z5,z9]),(0,[z1,z2,z7,z4,z12,z5,z9]),(0,[z1,z2,z7,z4,z5,z664,z6]),(0,[z665,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z231]),(0,[z1,z2,z7,z391,z4,z5,z6])],[(0,[z1,z2,z7,z666,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z10,z199]),(0,[z1,z2,z7,z4,z5,z248,z9]),(0,[z1,z2,z7,z25,z35,z4,z5]),(0,[z1,z204,z2,z7,z4,z5,z6]),(0,[z1,z22,z2,z7,z4,z5,z459]),(0,[z1,z2,z7,z35,z5,z136,z6])],[(0,[z1,z2,z13,z7,z4,z5,z231]),(0,[z1,z2,z7,z4,z5,z6,z667]),(0,[z1,z348,z2,z7,z35,z4,z5])],[(0,[z90,z1,z48,z2,z4,z5,z6]),(0,[z1,z2,z7,z8,z4,z5,z9]),(0,[z1,z2,z7,z4,z668,z5,z6]),(0,[z1,z2,z7,z4,z669,z5,z6]),(1,[z1,z2,z226,z4,z5,z153])],[(0,[z1,z48,z139,z7,z4,z5,z6]),(0,[z69,z1,z2,z7,z4,z5,z154]),(0,[z2,z7,z61,z4,z108,z5,z6]),(0,[z1,z2,z670,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z37,z9]),(0,[z1,z48,z2,z25,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z671]),(0,[z1,z2,z7,z4,z5,z672,z6]),(0,[z213,z1,z2,z7,z4,z5,z6])],[(0,[z16,z1,z2,z7,z4,z5,z359]),(0,[z1,z2,z7,z4,z673,z5,z6]),(0,[z166,z1,z2,z7,z35,z4,z5]),(1,[z1,z2,z7,z477,z5,z6]),(0,[z1,z2,z7,z4,z5,z674,z6]),(0,[z1,z2,z7,z4,z23,z19,z6]),(0,[z1,z2,z437,z7,z4,z5,z10]),(0,[z1,z28,z2,z7,z4,z5,z9]),(0,[z1,z7,z4,z5,z97,z6,z100])],[(0,[z1,z675,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z676,z5,z6]),(0,[z1,z2,z49,z7,z4,z5,z9]),(0,[z1,z21,z2,z7,z4,z5,z9]),(1,[z1,z2,z460,z7,z4,z6])],[(0,[z1,z2,z677,z7,z4,z5,z6]),(0,[z1,z2,z7,z678,z4,z5,z6]),(0,[z1,z2,z7,z61,z57,z5,z6]),(1,[z1,z2,z7,z4,z5,z9]),(0,[z1,z2,z7,z4,z5,z6,z679])]],
   [[(0,[z74,z1,z2,z7,z35,z4,z5]),(0,[z1,z22,z2,z7,z4,z19,z5]),(0,[z1,z244,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z680]),(0,[z1,z112,z2,z7,z4,z56,z6]),(0,[z1,z22,z21,z2,z7,z4,z5]),(0,[z681,z1,z2,z7,z4,z5,z6]),(0,[z1,z468,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z602,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z682]),(0,[z1,z2,z121,z7,z4,z131,z6])],[(0,[z1,z2,z683,z7,z4,z5,z6]),(0,[z1,z18,z2,z7,z61,z5,z6]),(0,[z77,z1,z2,z7,z35,z4,z5]),(0,[z1,z2,z7,z4,z5,z323,z6]),(0,[z1,z2,z7,z35,z4,z5,z10]),(0,[z1,z2,z7,z4,z23,z5,z9]),(1,[z1,z2,z7,z4,z5,z31]),(0,[z1,z2,z7,z4,z684,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z685])],[(0,[z1,z2,z7,z4,z5,z190,z10]),(0,[z686,z1,z2,z7,z4,z5,z6])],[(1,[z1,z2,z7,z4,z84,z6]),(0,[z1,z2,z7,z14,z4,z5,z10]),(1,[z1,z2,z7,z4,z177,z6]),(0,[z687,z1,z2,z7,z4,z5,z6]),(0,[z1,z81,z2,z7,z35,z4,z5]),(0,[z1,z2,z121,z7,z4,z5,z199])],[(0,[z688,z1,z2,z7,z4,z5,z6]),(0,[z689,z1,z2,z7,z4,z5,z6]),(0,[z166,z2,z38,z7,z4,z5,z6]),(0,[z1,z2,z7,z690,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z691])],[(0,[z90,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z241,z4,z5,z6]),(0,[z1,z2,z7,z692,z4,z5,z6]),(1,[z1,z2,z7,z4,z5,z27]),(0,[z1,z81,z7,z4,z5,z6,z100]),(0,[z1,z693,z2,z7,z4,z5,z6]),(0,[z1,z22,z34,z2,z7,z4,z5]),(0,[z1,z2,z7,z35,z4,z23,z5]),(0,[z1,z2,z694,z7,z4,z5,z6])],[(1,[z1,z2,z7,z150,z5,z6]),(0,[z1,z2,z7,z4,z5,z647,z6]),(1,[z1,z2,z7,z4,z625,z6]),(0,[z1,z22,z2,z7,z8,z4,z5]),(0,[z695,z1,z2,z7,z4,z5,z6]),(0,[z385,z1,z2,z7,z35,z4,z5])],[(1,[z1,z2,z7,z4,z5,z523]),(0,[z696,z1,z2,z7,z4,z5,z6]),(0,[z1,z81,z2,z7,z4,z131,z5]),(0,[z1,z2,z7,z35,z4,z5,z37])]],
   [[(0,[z1,z2,z7,z158,z108,z5,z6]),(1,[z1,z2,z7,z4,z5,z262])],[(0,[z697,z1,z2,z7,z4,z5,z6]),(0,[z698,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z97,z9]),(0,[z1,z699,z2,z7,z4,z5,z6]),(1,[z1,z2,z13,z14,z5,z6]),(0,[z1,z79,z2,z226,z4,z5,z6])],[(0,[z1,z2,z7,z4,z4,z5,z6]),(1,[z1,z183,z2,z7,z4,z5]),(0,[z2,z7,z4,z5,z9,z6,z10]),(0,[z1,z157,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z141,z6]),(0,[z1,z2,z7,z4,z700,z5,z6]),(0,[z1,z701,z2,z7,z4,z5,z6])],[(0,[z0,z1,z2,z7,z4,z73,z6]),(0,[z1,z296,z2,z7,z4,z30,z6]),(0,[z1,z244,z2,z7,z57,z5,z6]),(0,[z1,z2,z7,z4,z5,z235,z6]),(0,[z1,z2,z7,z4,z5,z702,z6])],[(0,[z1,z2,z121,z7,z4,z5,z10]),(0,[z1,z2,z7,z4,z5,z703,z6]),(0,[z1,z2,z13,z7,z35,z4,z5]),(0,[z1,z2,z473,z7,z4,z5,z6])],[(0,[z1,z663,z2,z7,z4,z5,z6]),(1,[z1,z2,z7,z4,z172,z6]),(0,[z1,z22,z2,z7,z4,z5,z10]),(0,[z1,z2,z47,z7,z4,z56,z6]),(0,[z1,z2,z7,z4,z12,z5,z6])],[(1,[z1,z2,z7,z4,z5,z154]),(1,[z1,z2,z7,z4,z5,z528]),(0,[z1,z2,z7,z704,z4,z5,z6]),(0,[z1,z705,z2,z7,z4,z5,z6])],[(0,[z1,z2,z169,z7,z4,z30,z5]),(0,[z1,z2,z7,z4,z706,z5,z6]),(0,[z1,z2,z7,z35,z4,z5,z83])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z1,z2,z7,z596,z5,z6]),(0,[z1,z48,z258,z4,z5,z6]),(0,[z1,z2,z7,z707,z4,z5]),(0,[z1,z22,z2,z7,z4,z33]),(0,[z1,z40,z7,z4,z56,z6])],[(0,[z1,z22,z2,z3,z4,z5]),(0,[z1,z708,z7,z4,z5,z6]),(0,[z144,z2,z38,z4,z5,z6]),(0,[z1,z2,z709,z4,z5,z6]),(0,[z1,z2,z510,z4,z5,z292]),(0,[z1,z2,z7,z5,z710,z6]),(0,[z1,z2,z7,z4,z711,z6]),(0,[z1,z2,z7,z4,z5,z712]),(0,[z1,z2,z7,z4,z131,z614])],[(0,[z1,z713,z2,z4,z5,z6]),(0,[z166,z2,z38,z35,z4,z5]),(0,[z77,z22,z2,z7,z4,z19]),(0,[z1,z224,z2,z4,z23,z6]),(0,[z2,z7,z4,z5,z516,z9]),(0,[z1,z48,z49,z4,z33,z6]),(0,[z1,z2,z7,z714,z5,z6]),(0,[z1,z2,z4,z5,z715,z6])],[(0,[z1,z716,z2,z7,z423,z5]),(0,[z1,z2,z717,z4,z5,z6]),(0,[z1,z22,z431,z7,z4,z5]),(0,[z1,z718,z2,z7,z596,z5]),(0,[z1,z20,z25,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z719]),(0,[z1,z2,z226,z146,z4,z5])],[(0,[z1,z2,z7,z4,z5,z720]),(0,[z16,z708,z7,z4,z5,z6]),(0,[z1,z2,z721,z7,z4,z238])],[(0,[z90,z2,z8,z4,z5,z9]),(0,[z1,z2,z7,z165,z722,z6])],[(0,[z1,z2,z7,z723,z4,z5]),(0,[z1,z2,z7,z4,z5,z724])],[(0,[z1,z2,z7,z725,z5,z6]),(0,[z1,z18,z2,z7,z604,z6]),(0,[z1,z2,z7,z35,z5,z114])]],
   [[(0,[z1,z2,z7,z4,z625,z9]),(0,[z74,z2,z7,z61,z5,z75]),(0,[z2,z7,z4,z726,z76,z6]),(0,[z1,z401,z2,z7,z5,z188]),(0,[z1,z22,z727,z7,z4,z5])],[(0,[z1,z22,z2,z7,z241,z5]),(0,[z1,z2,z7,z4,z728,z6]),(0,[z1,z357,z2,z7,z130,z5]),(0,[z1,z350,z2,z7,z35,z5]),(0,[z1,z2,z7,z35,z4,z729])],[(0,[z1,z2,z730,z4,z5,z6]),(0,[z16,z17,z7,z4,z5,z10]),(0,[z1,z2,z7,z731,z4,z5]),(0,[z1,z2,z7,z35,z4,z475]),(0,[z1,z2,z7,z180,z5,z248]),(0,[z1,z2,z7,z4,z353,z190]),(0,[z1,z2,z7,z4,z5,z732]),(0,[z1,z2,z7,z354,z4,z11]),(0,[z733,z2,z7,z4,z5,z6])],[(0,[z1,z2,z47,z4,z259,z6]),(0,[z1,z2,z7,z35,z309,z5])],[(0,[z1,z2,z7,z734,z5,z6]),(0,[z1,z2,z7,z150,z84,z6]),(0,[z0,z589,z139,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z735]),(0,[z1,z2,z7,z4,z736,z5]),(0,[z1,z7,z737,z30,z5,z6]),(0,[z1,z81,z473,z7,z4,z5])],[(0,[z1,z431,z7,z4,z5,z85]),(0,[z69,z2,z7,z266,z4,z5]),(0,[z1,z738,z2,z7,z4,z5]),(0,[z1,z401,z2,z739,z4,z5]),(0,[z1,z2,z7,z4,z131,z190])],[(0,[z1,z2,z7,z4,z740,z6]),(0,[z1,z741,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z742,z10]),(0,[z1,z2,z7,z4,z743,z6]),(0,[z1,z2,z7,z35,z587,z5])],[(0,[z1,z744,z2,z7,z4,z5]),(0,[z1,z2,z7,z745,z4,z5]),(0,[z1,z2,z7,z4,z746,z6]),(0,[z1,z21,z7,z4,z142,z10])]],
   [[(0,[z1,z2,z7,z4,z625,z523]),(0,[z291,z1,z7,z4,z5,z179]),(0,[z1,z357,z2,z7,z57,z6]),(0,[z1,z2,z4,z5,z715,z153])],[(0,[z1,z2,z3,z35,z4,z5]),(0,[z1,z22,z2,z7,z5,z417])],[(0,[z74,z2,z7,z61,z5,z322]),(0,[z1,z2,z7,z35,z78,z5]),(0,[z2,z7,z4,z5,z9,z747]),(0,[z1,z2,z7,z5,z55,z6])],[(0,[z1,z589,z2,z4,z5,z10]),(0,[z1,z2,z7,z241,z475,z6]),(0,[z1,z7,z4,z5,z748,z100])],[(0,[z1,z2,z7,z4,z749,z6]),(0,[z1,z2,z750,z4,z5,z6]),(0,[z1,z2,z7,z477,z5,z6]),(0,[z1,z2,z7,z5,z751,z6]),(0,[z1,z2,z7,z4,z752,z6])],[(0,[z0,z139,z7,z4,z5,z10]),(0,[z1,z469,z2,z4,z5,z10]),(0,[z398,z2,z8,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z753]),(0,[z1,z22,z513,z2,z7,z5]),(0,[z1,z2,z7,z4,z602,z199])],[(0,[z1,z2,z7,z4,z5,z754]),(0,[z1,z2,z755,z4,z5,z6]),(0,[z1,z756,z7,z4,z5,z6]),(0,[z1,z7,z4,z757,z5,z6]),(0,[z1,z183,z2,z7,z5,z268]),(0,[z1,z2,z7,z4,z5,z758]),(0,[z1,z2,z7,z4,z5,z759])],[(0,[z760,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z761]),(0,[z1,z2,z7,z57,z591,z6]),(0,[z1,z22,z2,z762,z4,z5]),(0,[z1,z2,z7,z5,z136,z763])]],
   [[(0,[z1,z2,z7,z4,z5,z764]),(0,[z1,z2,z7,z765,z5,z6]),(0,[z1,z2,z7,z4,z5,z31]),(0,[z1,z22,z2,z7,z610,z5])],[(0,[z1,z2,z7,z766,z5,z6]),(0,[z1,z258,z38,z4,z5,z6]),(0,[z62,z2,z7,z4,z726,z6]),(0,[z1,z22,z2,z7,z517,z5]),(0,[z1,z767,z2,z7,z5,z10]),(0,[z42,z1,z7,z4,z5,z97]),(0,[z1,z2,z7,z5,z6,z768]),(0,[z1,z2,z7,z4,z769,z5])],[(0,[z1,z2,z7,z4,z84,z6]),(1,[z2,z7,z770,z5,z6]),(0,[z1,z2,z7,z4,z397,z10]),(0,[z1,z2,z7,z4,z771,z5]),(0,[z1,z2,z7,z4,z772,z5]),(0,[z1,z2,z7,z4,z177,z6]),(0,[z1,z357,z40,z2,z7,z6]),(0,[z1,z2,z7,z35,z5,z548]),(0,[z1,z2,z7,z722,z37,z6])],[(0,[z2,z7,z4,z5,z747,z6]),(0,[z50,z1,z183,z2,z7,z5]),(0,[z1,z357,z2,z7,z5,z10]),(0,[z225,z2,z7,z4,z5,z10]),(0,[z1,z2,z773,z7,z4,z5]),(0,[z1,z2,z7,z4,z774,z10]),(0,[z1,z2,z775,z7,z4,z5]),(0,[z1,z2,z7,z4,z5,z776])],[(0,[z1,z2,z94,z4,z5,z408]),(0,[z1,z2,z7,z241,z5,z9]),(0,[z1,z2,z4,z5,z777,z6]),(0,[z1,z2,z4,z5,z778,z10]),(0,[z50,z1,z7,z30,z5,z9]),(0,[z1,z2,z7,z4,z5,z779])],[(0,[z1,z2,z7,z150,z5,z6]),(0,[z1,z2,z780,z4,z5,z6]),(0,[z1,z2,z7,z4,z625,z6]),(0,[z62,z2,z7,z4,z76,z9]),(0,[z1,z2,z739,z4,z5,z9]),(0,[z1,z2,z169,z7,z4,z177]),(0,[z1,z445,z7,z4,z56,z6]),(0,[z1,z18,z2,z7,z35,z37]),(0,[z1,z2,z7,z4,z781,z199])],[(0,[z1,z2,z7,z4,z5,z782]),(0,[z1,z2,z7,z4,z5,z235])],[(0,[z1,z357,z2,z7,z76,z6]),(0,[z245,z2,z7,z4,z5,z10]),(0,[z1,z2,z7,z4,z5,z783]),(0,[z1,z22,z2,z784,z4,z5]),(0,[z1,z2,z7,z35,z4,z785])]],
   [[(0,[z1,z2,z7,z4,z5,z786]),(0,[z1,z18,z2,z7,z658,z6]),(0,[z1,z2,z7,z787,z4,z5]),(0,[z1,z244,z7,z737,z5,z6]),(0,[z1,z2,z13,z14,z5,z6])],[(0,[z0,z139,z7,z4,z5,z408]),(0,[z1,z183,z2,z7,z4,z5]),(0,[z1,z2,z7,z4,z6,z781])],[(0,[z1,z2,z7,z4,z5,z788]),(0,[z1,z22,z258,z7,z4,z5]),(0,[z1,z2,z7,z4,z475,z85]),(0,[z1,z2,z7,z4,z789,z5]),(0,[z1,z2,z7,z4,z5,z790]),(0,[z1,z2,z7,z791,z4,z5]),(0,[z1,z2,z7,z4,z5,z792]),(0,[z793,z22,z2,z7,z4,z5])],[(0,[z1,z2,z7,z4,z794,z6]),(0,[z16,z22,z17,z7,z4,z5]),(0,[z1,z258,z7,z4,z5,z9]),(0,[z1,z795,z2,z7,z4,z5]),(0,[z2,z7,z4,z257,z5,z10]),(0,[z695,z2,z7,z4,z5,z9]),(0,[z50,z1,z7,z177,z30,z6]),(0,[z1,z2,z13,z796,z5,z6]),(0,[z1,z2,z7,z797,z5,z6]),(0,[z1,z2,z7,z4,z5,z798])],[(0,[z1,z22,z469,z2,z4,z5]),(0,[z1,z2,z7,z4,z172,z6]),(0,[z1,z18,z2,z67,z7,z37])],[(0,[z1,z2,z7,z4,z799,z6]),(0,[z1,z2,z7,z596,z5,z10]),(0,[z1,z2,z7,z5,z800,z6]),(0,[z1,z2,z7,z4,z5,z154]),(0,[z1,z2,z801,z7,z4,z5]),(0,[z1,z2,z332,z14,z5,z6]),(0,[z1,z40,z7,z4,z56,z10]),(0,[z345,z2,z7,z4,z5,z10]),(0,[z1,z112,z2,z4,z23,z9]),(0,[z1,z2,z7,z802,z5,z6])],[(0,[z1,z2,z7,z423,z5,z408]),(0,[z2,z7,z266,z4,z5,z10]),(0,[z1,z803,z7,z4,z5,z6]),(0,[z1,z296,z244,z2,z7,z6]),(0,[z1,z2,z7,z4,z5,z804])],[(0,[z1,z2,z7,z805,z4,z5]),(0,[z1,z806,z7,z4,z5,z6]),(0,[z2,z7,z4,z5,z9,z10]),(0,[z1,z244,z7,z158,z5,z9]),(0,[z1,z18,z2,z7,z37,z9]),(0,[z1,z2,z807,z4,z5,z6])]],
   [[(0,[z1,z2,z7,z4,z5,z808]),(0,[z1,z2,z4,z5,z809,z9]),(0,[z1,z2,z7,z4,z5,z810])],[(0,[z1,z2,z811,z7,z4,z5]),(0,[z1,z2,z7,z4,z5,z812]),(1,[z1,z2,z7,z722,z6])],[(0,[z1,z2,z7,z4,z5,z813]),(0,[z536,z17,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z814,z6]),(0,[z2,z7,z4,z5,z282,z10]),(0,[z1,z22,z244,z7,z158,z5])],[(0,[z16,z17,z7,z4,z5,z275]),(0,[z1,z2,z7,z4,z5,z815]),(0,[z1,z2,z7,z4,z5,z816]),(0,[z1,z2,z7,z817,z477,z5]),(0,[z1,z634,z7,z4,z142,z6]),(0,[z1,z22,z2,z7,z5,z240]),(0,[z1,z244,z7,z158,z5,z152]),(0,[z1,z22,z40,z7,z4,z56]),(0,[z1,z2,z460,z444,z7,z4])],[(0,[z62,z2,z7,z4,z76,z528]),(0,[z1,z28,z2,z4,z5,z82]),(0,[z1,z7,z4,z737,z5,z6])],[(0,[z1,z818,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z819])],[(0,[z1,z2,z7,z4,z5,z275]),(0,[z1,z2,z7,z4,z73,z10]),(0,[z1,z820,z7,z4,z5,z6]),(0,[z2,z7,z4,z5,z821,z6]),(0,[z1,z2,z7,z35,z4,z33]),(0,[z50,z1,z66,z7,z5,z6]),(0,[z1,z112,z2,z4,z23,z262]),(0,[z1,z2,z7,z4,z5,z58])],[(0,[z1,z2,z94,z423,z5,z6]),(0,[z1,z2,z7,z4,z822,z6]),(0,[z1,z823,z2,z7,z4,z6]),(0,[z1,z2,z7,z4,z5,z824]),(0,[z1,z2,z7,z35,z4,z177]),(0,[z1,z2,z7,z4,z5,z825])]],
   [[(0,[z1,z826,z2,z7,z150,z5]),(0,[z1,z2,z7,z180,z108,z5]),(0,[z1,z795,z2,z7,z477,z5]),(0,[z77,z2,z7,z35,z4,z19]),(0,[z1,z2,z7,z827,z4,z5]),(0,[z1,z2,z7,z4,z5,z828]),(0,[z1,z7,z4,z5,z748,z6]),(0,[z1,z2,z7,z4,z829,z6])],[(0,[z1,z2,z7,z70,z4,z5]),(0,[z50,z1,z7,z30,z5,z6]),(0,[z1,z2,z7,z35,z165,z57])],[(0,[z1,z2,z830,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z831]),(0,[z90,z2,z8,z596,z5,z6]),(0,[z69,z492,z2,z7,z4,z5]),(0,[z1,z2,z739,z4,z5,z6]),(0,[z62,z2,z7,z4,z76,z6]),(0,[z72,z2,z7,z4,z5,z9]),(0,[z1,z2,z7,z4,z832,z5])],[(0,[z1,z2,z7,z4,z833,z5]),(0,[z1,z2,z7,z4,z5,z834]),(0,[z1,z2,z7,z477,z5,z364]),(0,[z1,z2,z7,z78,z5,z9]),(0,[z1,z2,z835,z7,z4,z5]),(0,[z1,z228,z2,z4,z5,z323]),(0,[z1,z20,z25,z4,z5,z31]),(0,[z1,z21,z7,z35,z4,z142])],[(0,[z1,z826,z2,z7,z4,z5]),(0,[z1,z589,z2,z35,z4,z5]),(0,[z1,z2,z7,z836,z596,z5]),(0,[z74,z22,z2,z7,z61,z5]),(0,[z1,z2,z7,z837,z4,z5]),(0,[z1,z296,z2,z7,z129,z4]),(0,[z1,z2,z7,z4,z5,z838]),(0,[z1,z34,z2,z11,z12,z6]),(0,[z839,z22,z2,z7,z4,z5])],[(0,[z1,z2,z7,z4,z5,z840]),(0,[z109,z492,z2,z7,z4,z5]),(0,[z1,z2,z841,z4,z5,z6]),(0,[z1,z2,z4,z842,z5,z6]),(0,[z1,z2,z7,z4,z5,z101])],[(0,[z0,z139,z7,z35,z4,z5]),(0,[z1,z469,z2,z35,z4,z5]),(0,[z1,z2,z7,z164,z4,z5]),(0,[z1,z81,z7,z4,z5,z100]),(0,[z51,z1,z2,z347,z4,z5])],[(0,[z1,z2,z7,z4,z843,z6]),(0,[z1,z2,z7,z4,z844,z6]),(0,[z1,z2,z7,z4,z845,z6]),(0,[z1,z2,z7,z35,z241,z5]),(0,[z1,z2,z7,z4,z846,z6]),(0,[z1,z847,z7,z4,z5,z6]),(0,[z1,z7,z4,z711,z56,z6]),(0,[z1,z357,z40,z7,z56,z6])]],
   [[(0,[z1,z2,z7,z848,z5,z6]),(0,[z1,z2,z7,z4,z5,z849]),(0,[z166,z2,z850,z4,z5,z6]),(0,[z62,z2,z7,z4,z76,z71]),(0,[z1,z2,z411,z4,z5,z464]),(0,[z1,z2,z7,z4,z851,z5]),(0,[z1,z2,z7,z4,z110,z6]),(0,[z1,z2,z7,z4,z5,z127]),(0,[z50,z1,z296,z7,z30,z6]),(0,[z1,z40,z7,z4,z711,z6]),(1,[z1,z7,z4,z5,z748]),(0,[z1,z22,z2,z7,z370,z5])],[(0,[z1,z2,z7,z4,z5,z852]),(0,[z1,z2,z7,z477,z5,z10]),(0,[z1,z2,z7,z78,z5,z27]),(0,[z1,z2,z7,z5,z751,z10]),(0,[z1,z81,z7,z4,z5,z327]),(0,[z853,z1,z2,z7,z4,z5]),(0,[z1,z2,z67,z7,z4,z5])],[(0,[z1,z2,z7,z4,z73,z408]),(0,[z1,z20,z258,z4,z5,z6]),(0,[z207,z2,z7,z108,z5,z6]),(0,[z1,z2,z7,z4,z5,z854]),(0,[z1,z2,z7,z4,z5,z855]),(0,[z1,z2,z7,z4,z736,z238]),(0,[z1,z112,z2,z4,z23,z6]),(0,[z1,z2,z7,z4,z190,z781])],[(0,[z1,z2,z7,z4,z726,z6]),(0,[z1,z2,z7,z35,z477,z5]),(0,[z1,z183,z2,z7,z165,z5]),(0,[z2,z631,z7,z4,z5,z9]),(0,[z1,z2,z7,z4,z5,z856]),(0,[z1,z357,z2,z7,z35,z5]),(0,[z1,z2,z7,z4,z857,z6]),(0,[z1,z858,z7,z4,z5,z6])],[(0,[z1,z2,z7,z859,z4,z5]),(0,[z1,z860,z7,z4,z5,z6]),(0,[z1,z2,z7,z861,z5,z6]),(0,[z2,z486,z7,z4,z5,z9]),(0,[z1,z22,z2,z7,z180,z5]),(0,[z1,z2,z7,z4,z5,z862]),(0,[z1,z2,z7,z863,z4,z5]),(0,[z1,z22,z2,z7,z690,z5]),(0,[z1,z112,z2,z4,z842,z6]),(0,[z1,z18,z2,z7,z37,z6])],[(0,[z1,z864,z2,z4,z5,z6]),(0,[z1,z2,z4,z5,z809,z6]),(0,[z1,z865,z2,z7,z4,z5]),(0,[z492,z2,z7,z4,z5,z76]),(0,[z1,z2,z7,z866,z4,z5]),(0,[z2,z7,z337,z4,z5,z10]),(0,[z1,z867,z2,z7,z4,z5]),(0,[z1,z2,z7,z129,z4,z5]),(0,[z1,z2,z7,z4,z785,z6]),(0,[z1,z2,z868,z7,z4,z5])],[(0,[z1,z2,z7,z4,z5,z869]),(0,[z50,z1,z7,z30,z110,z6]),(0,[z1,z2,z7,z737,z5,z6]),(0,[z1,z2,z870,z7,z4,z5]),(0,[z1,z2,z7,z871,z5,z6]),(0,[z1,z2,z7,z4,z5,z872])],[(0,[z1,z2,z3,z4,z5,z408]),(0,[z1,z22,z2,z7,z150,z5]),(0,[z1,z2,z7,z4,z84,z10]),(0,[z1,z2,z7,z4,z177,z10]),(0,[z1,z2,z7,z4,z141,z6]),(0,[z1,z2,z7,z4,z873,z6]),(0,[z1,z2,z7,z4,z874,z6]),(0,[z1,z2,z7,z4,z5,z875]),(0,[z1,z2,z7,z4,z5,z325]),(0,[z1,z2,z7,z35,z132,z5])]],
   [[(0,[z1,z2,z7,z4,z876,z6]),(0,[z2,z7,z4,z5,z747,z10]),(0,[z1,z2,z7,z877,z4,z5]),(0,[z1,z2,z7,z4,z878,z6]),(0,[z1,z2,z7,z4,z316,z190]),(0,[z1,z2,z7,z35,z4,z879])],[(0,[z1,z431,z7,z241,z5,z6]),(0,[z1,z2,z7,z880,z4,z5]),(0,[z1,z2,z7,z4,z5,z881])],[(0,[z1,z2,z7,z150,z5,z10]),(0,[z1,z2,z7,z4,z625,z10]),(0,[z1,z882,z2,z7,z4,z5]),(0,[z109,z2,z7,z4,z5,z747]),(0,[z1,z2,z780,z4,z5,z10]),(0,[z1,z2,z7,z4,z5,z883]),(0,[z1,z2,z7,z4,z5,z884]),(0,[z1,z885,z2,z7,z4,z5]),(0,[z1,z260,z7,z4,z5,z100])],[(0,[z1,z22,z2,z7,z4,z5]),(0,[z356,z2,z7,z4,z5,z10]),(0,[z1,z2,z7,z4,z5,z886]),(0,[z1,z204,z2,z7,z4,z138])],[(0,[z1,z2,z7,z4,z5,z887]),(0,[z1,z22,z2,z7,z4,z177]),(0,[z1,z2,z392,z4,z5,z153]),(0,[z1,z2,z7,z4,z5,z888])],[(0,[z1,z2,z889,z4,z5,z6]),(0,[z1,z2,z850,z4,z5,z6]),(0,[z1,z2,z13,z14,z5,z10]),(0,[z407,z2,z7,z4,z5,z10]),(0,[z1,z803,z25,z4,z5,z6])],[(0,[z1,z296,z2,z169,z7,z4]),(0,[z1,z2,z890,z4,z5,z6]),(0,[z1,z497,z7,z4,z5,z97]),(0,[z1,z2,z7,z891,z4,z5]),(0,[z1,z22,z2,z7,z165,z57])],[(0,[z1,z2,z7,z4,z5,z892]),(0,[z1,z2,z7,z4,z5,z893]),(0,[z1,z7,z4,z5,z894,z6]),(0,[z401,z492,z2,z7,z4,z5]),(0,[z1,z2,z7,z4,z5,z895]),(0,[z1,z2,z896,z7,z4,z5]),(0,[z1,z2,z7,z4,z5,z897]),(1,[z1,z2,z7,z4,z781])]],
   [[(0,[z1,z2,z7,z4,z898,z6]),(0,[z217,z1,z7,z30,z5,z6]),(0,[z429,z2,z7,z4,z76,z6]),(0,[z1,z2,z7,z4,z6,z899]),(0,[z1,z22,z2,z7,z654,z5])],[(0,[z1,z2,z7,z4,z900,z6]),(0,[z69,z2,z7,z70,z108,z5]),(0,[z1,z2,z7,z4,z901,z6]),(0,[z1,z18,z2,z7,z96,z6]),(0,[z1,z2,z7,z4,z172,z10]),(0,[z1,z902,z2,z7,z4,z5]),(0,[z428,z1,z473,z7,z4,z5])],[(0,[z189,z2,z7,z61,z5,z6]),(0,[z1,z2,z7,z4,z5,z364]),(0,[z1,z903,z2,z7,z4,z6])],[(0,[z1,z2,z7,z4,z84,z408]),(0,[z1,z904,z2,z7,z5,z6]),(0,[z1,z905,z2,z7,z4,z5]),(0,[z1,z2,z7,z4,z5,z906])],[(0,[z1,z907,z2,z7,z5,z6]),(0,[z1,z357,z112,z2,z7,z6]),(0,[z1,z2,z7,z4,z908,z6])],[(0,[z1,z2,z94,z4,z5,z342]),(0,[z1,z909,z7,z4,z5,z6]),(0,[z1,z2,z7,z502,z57,z6]),(0,[z1,z48,z49,z4,z5,z9]),(0,[z1,z2,z7,z910,z4,z5])],[(0,[z1,z2,z7,z4,z5,z911]),(0,[z1,z2,z7,z150,z5,z408]),(0,[z1,z912,z7,z4,z5,z6]),(0,[z1,z296,z2,z7,z61,z6]),(0,[z1,z913,z2,z7,z4,z5])],[(0,[z90,z2,z8,z4,z625,z6]),(0,[z1,z914,z7,z4,z5,z6]),(0,[z74,z2,z7,z61,z5,z9]),(0,[z1,z2,z7,z4,z814,z10]),(0,[z1,z2,z7,z165,z57,z9]),(0,[z1,z2,z7,z796,z5,z6]),(0,[z1,z2,z7,z915,z4,z5])]],
   [[(0,[z1,z2,z7,z4,z5,z10]),(0,[z1,z22,z2,z7,z423,z5]),(0,[z1,z258,z7,z596,z5,z6]),(0,[z90,z2,z8,z4,z5,z523]),(0,[z1,z22,z2,z7,z477,z5]),(0,[z1,z2,z7,z4,z5,z916]),(0,[z1,z2,z7,z4,z5,z917]),(0,[z1,z22,z2,z7,z41,z5]),(0,[z1,z357,z2,z7,z149,z5]),(0,[z1,z2,z7,z4,z5,z918])],[(0,[z0,z469,z139,z4,z5,z6]),(0,[z1,z2,z7,z4,z919,z6]),(0,[z1,z2,z7,z4,z5,z920]),(0,[z1,z2,z921,z7,z4,z141]),(0,[z1,z2,z226,z4,z5,z715]),(0,[z1,z18,z22,z2,z7,z37])],[(0,[z1,z2,z3,z423,z5,z6]),(0,[z0,z139,z7,z4,z5,z342]),(0,[z50,z1,z296,z2,z7,z6]),(0,[z1,z34,z2,z796,z5,z6])],[(0,[z2,z850,z8,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z922]),(0,[z1,z2,z7,z4,z547,z442]),(0,[z1,z2,z7,z35,z308,z5]),(1,[z1,z803,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z781])],[(0,[z1,z431,z7,z4,z475,z6]),(0,[z1,z2,z7,z923,z5,z6]),(0,[z492,z2,z7,z61,z4,z5]),(0,[z1,z924,z2,z7,z5,z10]),(0,[z1,z22,z20,z25,z4,z5]),(0,[z1,z357,z2,z7,z37,z6]),(0,[z1,z2,z7,z4,z5,z925]),(0,[z1,z2,z13,z14,z5,z231]),(0,[z1,z22,z112,z2,z4,z23])],[],[(0,[z1,z2,z7,z926,z5,z6]),(0,[z50,z1,z7,z30,z5,z10]),(0,[z1,z34,z2,z12,z5,z10]),(0,[z1,z2,z47,z4,z113,z9]),(0,[z1,z2,z7,z4,z5,z927])],[(0,[z1,z2,z7,z423,z5,z342]),(0,[z62,z2,z7,z4,z76,z10]),(0,[z109,z2,z7,z4,z5,z10]),(0,[z1,z2,z7,z4,z5,z928]),(0,[z581,z2,z7,z4,z5,z9]),(0,[z1,z929,z2,z7,z5,z6]),(0,[z1,z2,z7,z930,z4,z5])]],
   [[(0,[z1,z2,z7,z596,z5,z85]),(0,[z2,z7,z850,z4,z5,z6]),(0,[z1,z18,z2,z7,z238,z6]),(0,[z50,z1,z7,z129,z30,z5]),(0,[z1,z931,z2,z7,z4,z6])],[(0,[z1,z2,z7,z4,z932,z6]),(0,[z404,z1,z2,z7,z4,z459])],[(0,[z1,z2,z7,z4,z933,z6]),(0,[z1,z2,z7,z934,z5,z6]),(0,[z69,z2,z7,z108,z5,z220]),(0,[z1,z2,z7,z4,z5,z935]),(1,[z1,z2,z796,z5,z6]),(0,[z1,z22,z2,z7,z103,z5])],[(0,[z69,z22,z2,z7,z108,z5]),(0,[z318,z2,z7,z4,z76,z6]),(0,[z54,z1,z7,z4,z59,z5])],[(0,[z1,z2,z7,z4,z5,z408]),(0,[z1,z2,z7,z596,z475,z6]),(0,[z1,z2,z7,z180,z5,z136]),(0,[z1,z2,z7,z35,z4,z238]),(0,[z1,z2,z7,z4,z729,z6]),(0,[z1,z2,z7,z4,z936,z5]),(0,[z1,z2,z7,z4,z5,z937])],[(0,[z1,z2,z938,z7,z4,z6]),(0,[z90,z2,z8,z4,z5,z6]),(0,[z74,z2,z7,z61,z172,z6]),(0,[z1,z2,z7,z4,z110,z10]),(0,[z54,z1,z7,z4,z5,z179]),(0,[z1,z2,z7,z4,z5,z939]),(0,[z1,z2,z7,z5,z6,z940])],[],[(0,[z1,z2,z7,z180,z4,z5]),(0,[z1,z941,z2,z7,z4,z5]),(0,[z42,z1,z7,z4,z5,z647]),(0,[z1,z2,z7,z4,z11,z9]),(0,[z1,z2,z942,z7,z4,z5]),(0,[z1,z2,z784,z4,z5,z9]),(0,[z1,z2,z169,z7,z4,z5]),(0,[z1,z2,z7,z4,z5,z231])]],
   [[(0,[z1,z943,z7,z4,z5,z6]),(0,[z1,z2,z944,z4,z5,z6])],[(0,[z1,z2,z460,z7,z61,z6]),(0,[z1,z2,z7,z817,z4,z5]),(0,[z1,z2,z7,z861,z5,z10]),(0,[z1,z79,z2,z4,z5,z323]),(0,[z1,z2,z7,z945,z5,z6]),(0,[z1,z2,z7,z4,z5,z946])],[(0,[z1,z2,z4,z5,z947,z6]),(0,[z74,z2,z7,z35,z61,z5]),(0,[z274,z2,z7,z4,z5,z10]),(0,[z1,z48,z49,z4,z5,z6])],[(0,[z1,z2,z7,z948,z5,z6]),(0,[z1,z2,z7,z949,z5,z6]),(0,[z1,z2,z7,z4,z5,z950]),(0,[z1,z2,z7,z130,z4,z5]),(0,[z1,z2,z7,z4,z5,z951])],[(0,[z74,z2,z7,z61,z5,z6]),(0,[z1,z2,z7,z4,z141,z10]),(0,[z1,z2,z762,z4,z5,z6]),(0,[z1,z18,z2,z7,z610,z6]),(0,[z1,z2,z7,z165,z57,z6]),(0,[z1,z135,z468,z7,z4,z5]),(0,[z1,z2,z7,z35,z4,z814]),(0,[z1,z88,z7,z178,z4,z5])],[(0,[z1,z2,z7,z4,z5,z952]),(0,[z1,z2,z13,z14,z35,z5]),(0,[z733,z22,z2,z7,z4,z5])],[(0,[z1,z2,z7,z241,z625,z6]),(0,[z166,z382,z2,z4,z5,z6]),(0,[z2,z7,z4,z19,z726,z6]),(0,[z521,z2,z7,z4,z5,z9]),(0,[z1,z2,z7,z4,z953,z6]),(0,[z1,z2,z7,z4,z5,z954]),(0,[z1,z2,z7,z4,z5,z955]),(0,[z1,z2,z7,z4,z5,z956])],[(0,[z1,z2,z7,z241,z5,z523]),(0,[z1,z2,z7,z4,z5,z957]),(0,[z1,z2,z7,z35,z122,z5])]],
   [[(0,[z72,z2,z7,z266,z4,z5])],[(0,[z1,z2,z7,z4,z5,z958]),(0,[z1,z2,z7,z770,z5,z6]),(0,[z1,z2,z7,z4,z959,z5]),(0,[z1,z21,z7,z4,z304,z6])],[(0,[z74,z2,z7,z164,z61,z5]),(0,[z1,z2,z7,z960,z4,z5]),(0,[z686,z2,z7,z4,z5,z10]),(0,[z1,z183,z2,z7,z5,z37]),(0,[z1,z2,z961,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z962])],[(0,[z1,z2,z7,z4,z73,z342]),(0,[z1,z2,z7,z4,z5,z963]),(0,[z1,z20,z25,z4,z5,z10]),(0,[z1,z2,z411,z4,z5,z153]),(0,[z1,z2,z7,z4,z964,z6]),(0,[z1,z2,z7,z4,z965,z5]),(0,[z1,z2,z47,z4,z113,z6]),(0,[z1,z525,z2,z7,z4,z316])],[(0,[z1,z22,z2,z94,z4,z5]),(0,[z1,z2,z7,z164,z4,z814]),(0,[z1,z2,z7,z35,z555,z5]),(0,[z1,z7,z4,z142,z711,z6]),(0,[z966,z2,z7,z4,z5,z6]),(0,[z1,z2,z162,z211,z4,z5]),(0,[z1,z2,z7,z4,z131,z781])],[(0,[z0,z139,z94,z4,z5,z6]),(0,[z1,z2,z7,z35,z150,z5]),(0,[z1,z258,z7,z4,z625,z6]),(0,[z1,z2,z121,z7,z4,z313]),(0,[z1,z357,z21,z2,z7,z6]),(0,[z1,z2,z7,z4,z5,z967])],[(0,[z16,z17,z7,z35,z4,z5]),(0,[z1,z2,z7,z5,z968,z6]),(0,[z1,z258,z7,z4,z5,z523]),(0,[z1,z969,z7,z4,z5,z6]),(0,[z1,z157,z7,z4,z5,z267]),(0,[z466,z2,z7,z4,z5,z10]),(0,[z1,z40,z66,z7,z4,z6]),(0,[z1,z2,z7,z35,z5,z136])],[(0,[z1,z2,z7,z35,z4,z625]),(0,[z1,z2,z7,z4,z131,z442]),(0,[z1,z357,z22,z2,z7,z5]),(0,[z1,z2,z7,z130,z5,z55]),(0,[z1,z34,z2,z35,z12,z5]),(0,[z1,z2,z7,z4,z970,z6]),(0,[z1,z2,z7,z4,z5,z971])]],
   [[(0,[z1,z2,z3,z4,z5,z342]),(0,[z586,z1,z22,z2,z7,z5]),(0,[z1,z972,z2,z7,z4,z6]),(0,[z1,z2,z7,z973,z4,z5]),(0,[z315,z2,z7,z61,z5,z6]),(0,[z1,z2,z7,z4,z832,z141]),(0,[z1,z357,z2,z7,z238,z6]),(0,[z1,z2,z7,z4,z5,z974]),(0,[z1,z112,z2,z4,z23,z235])],[(0,[z1,z2,z7,z35,z4,z5]),(0,[z1,z2,z7,z4,z5,z975]),(0,[z1,z2,z7,z4,z976,z6]),(0,[z166,z2,z38,z4,z5,z311]),(0,[z74,z2,z7,z61,z397,z6]),(0,[z1,z2,z7,z977,z4,z5]),(0,[z1,z2,z7,z165,z676,z6]),(0,[z1,z22,z2,z7,z4,z238]),(0,[z1,z2,z7,z4,z6,z978]),(0,[z1,z2,z121,z7,z4,z459]),(0,[z1,z2,z7,z5,z6,z763])],[(0,[z1,z2,z7,z4,z475,z9]),(0,[z1,z2,z7,z4,z5,z979]),(0,[z1,z2,z7,z78,z19,z6]),(0,[z660,z2,z7,z4,z19,z6]),(0,[z1,z183,z2,z7,z5,z83]),(0,[z1,z2,z121,z7,z4,z399]),(0,[z1,z2,z980,z7,z4,z5])],[(0,[z1,z2,z7,z4,z33,z9]),(0,[z1,z2,z7,z981,z5,z6]),(0,[z1,z2,z7,z982,z4,z5]),(0,[z1,z22,z2,z7,z5,z763])],[(0,[z1,z2,z7,z241,z5,z6]),(0,[z1,z983,z2,z7,z4,z5]),(0,[z1,z2,z7,z4,z984,z6]),(0,[z1,z2,z7,z985,z5,z6]),(0,[z1,z22,z21,z7,z4,z142]),(0,[z1,z2,z7,z4,z11,z6]),(0,[z1,z2,z7,z4,z5,z986]),(0,[z1,z2,z7,z4,z5,z987])],[(0,[z1,z22,z2,z7,z4,z84]),(0,[z398,z139,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z625,z85])],[(0,[z1,z2,z7,z4,z988,z6]),(0,[z1,z2,z7,z4,z989,z6]),(0,[z1,z990,z2,z7,z4,z5]),(0,[z1,z2,z7,z4,z5,z991]),(0,[z1,z18,z196,z2,z7,z6]),(0,[z1,z22,z2,z7,z181,z5])],[(0,[z0,z139,z7,z423,z5,z6]),(0,[z1,z2,z7,z4,z5,z992]),(0,[z2,z7,z266,z61,z4,z5]),(0,[z1,z2,z993,z7,z4,z5]),(0,[z1,z2,z7,z4,z5,z994]),(0,[z1,z2,z444,z7,z4,z5]),(0,[z1,z2,z995,z7,z4,z5]),(0,[z1,z112,z2,z35,z4,z23]),(0,[z1,z2,z7,z996,z5,z6]),(0,[z1,z2,z7,z4,z5,z997])]],
   [[(0,[z1,z18,z2,z7,z240,z6]),(0,[z1,z2,z7,z4,z5,z998]),(0,[z1,z2,z7,z999,z4,z5]),(0,[z1,z2,z7,z4,z5,z715])],[(0,[z1,z2,z7,z4,z5,z1000]),(0,[z1,z2,z7,z4,z1001,z5]),(0,[z1,z2,z7,z165,z223,z6])],[(0,[z1,z2,z7,z4,z475,z523]),(0,[z1,z2,z7,z4,z5,z1002]),(0,[z1,z2,z7,z4,z5,z1003]),(0,[z1,z2,z7,z5,z55,z10]),(0,[z2,z7,z501,z4,z5,z10]),(0,[z1,z157,z7,z4,z5,z100])],[(0,[z1,z258,z7,z4,z5,z6]),(0,[z1,z2,z7,z5,z1004,z6]),(0,[z1,z2,z7,z5,z1005,z6]),(0,[z1,z2,z7,z4,z1006,z6]),(0,[z1,z2,z7,z4,z1007,z6]),(0,[z1,z2,z7,z4,z5,z1008]),(0,[z1,z2,z7,z4,z5,z1009])],[(0,[z1,z2,z7,z4,z84,z342]),(0,[z1,z2,z7,z1010,z4,z5]),(0,[z1,z2,z7,z1011,z5,z6]),(0,[z1,z2,z7,z4,z5,z1012]),(0,[z1,z2,z121,z7,z4,z199])],[(0,[z1,z1013,z2,z7,z4,z5]),(0,[z1,z2,z7,z1014,z4,z5]),(0,[z1,z2,z333,z4,z113,z6]),(0,[z1,z2,z7,z4,z1015,z6]),(0,[z1,z2,z7,z4,z5,z1016]),(0,[z1,z2,z7,z35,z5,z55]),(0,[z1,z22,z2,z7,z5,z461]),(0,[z1,z2,z7,z4,z5,z1017]),(0,[z1,z2,z7,z4,z5,z1018])],[(0,[z1,z2,z7,z35,z423,z5]),(0,[z1,z2,z7,z4,z5,z1019]),(0,[z106,z2,z7,z4,z19,z6]),(0,[z1020,z2,z7,z4,z5,z6]),(0,[z1021,z2,z7,z4,z5,z6])],[(0,[z1,z2,z7,z4,z1022,z6]),(0,[z1,z2,z7,z150,z5,z342]),(0,[z1,z2,z7,z4,z5,z1023]),(0,[z1,z244,z7,z158,z5,z6]),(0,[z1,z2,z796,z12,z5,z6]),(0,[z1,z1024,z2,z7,z4,z5])]],
   [[(0,[z1,z1025,z7,z4,z5,z6]),(0,[z1,z2,z7,z1026,z5,z6]),(0,[z1,z2,z7,z35,z4,z397]),(0,[z315,z2,z7,z4,z19,z6]),(0,[z287,z2,z7,z4,z5,z9]),(0,[z1,z2,z7,z4,z1027,z5]),(1,[z1,z2,z7,z5,z763])],[(0,[z1,z2,z7,z1028,z5,z6]),(0,[z1,z2,z1029,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z1030]),(0,[z1,z2,z4,z1031,z5,z6]),(0,[z1,z2,z1032,z7,z4,z5]),(0,[z1,z2,z7,z4,z5,z1033]),(0,[z69,z2,z7,z108,z5,z9]),(0,[z1,z22,z2,z7,z63,z5]),(0,[z1,z22,z2,z7,z4,z141]),(0,[z1,z48,z803,z4,z5,z6]),(0,[z1,z2,z7,z1034,z4,z5])],[(0,[z90,z2,z8,z4,z5,z10]),(0,[z1,z269,z7,z4,z56,z6]),(0,[z1,z2,z938,z7,z4,z10]),(0,[z344,z2,z7,z4,z5,z10]),(0,[z1,z2,z7,z4,z1035,z6]),(0,[z1,z2,z1036,z7,z4,z6])],[(0,[z1,z2,z7,z4,z5,z1037]),(0,[z1,z2,z7,z4,z5,z1038]),(0,[z1,z2,z7,z4,z5,z85]),(0,[z1,z2,z7,z4,z5,z1039]),(0,[z1,z1040,z2,z7,z4,z5]),(0,[z77,z2,z7,z477,z19,z6]),(0,[z1,z22,z2,z7,z380,z5]),(0,[z1,z432,z2,z4,z5,z82]),(1,[z1,z2,z4,z5,z715])],[(0,[z1,z2,z7,z1041,z5,z6]),(0,[z1,z22,z2,z7,z4,z625]),(0,[z1,z2,z7,z1042,z4,z5]),(0,[z1,z183,z2,z7,z35,z5]),(0,[z1,z2,z7,z4,z5,z1043]),(0,[z1,z2,z7,z4,z5,z1044])],[(0,[z1,z2,z7,z4,z172,z75]),(0,[z77,z2,z7,z4,z19,z9]),(0,[z1,z2,z140,z7,z4,z313]),(0,[z1,z22,z2,z7,z5,z188]),(0,[z1,z2,z7,z4,z1045,z6]),(0,[z1,z2,z7,z4,z149,z5])],[(0,[z1,z2,z94,z4,z73,z6]),(0,[z1,z2,z1046,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z1047]),(0,[z492,z2,z7,z4,z5,z9])],[(0,[z1,z2,z7,z4,z475,z6]),(0,[z1,z2,z7,z1048,z4,z5])]],
   [[(0,[z1,z2,z7,z4,z5,z1049]),(0,[z1,z183,z244,z2,z7,z5]),(0,[z2,z7,z4,z5,z10,z549]),(0,[z1,z1050,z2,z7,z4,z5]),(0,[z1,z2,z7,z4,z33,z6]),(0,[z1,z2,z7,z4,z5,z1051]),(0,[z1,z21,z7,z4,z711,z6]),(0,[z1,z34,z2,z354,z12,z5]),(0,[z1,z2,z121,z7,z4,z781])],[(0,[z166,z2,z38,z4,z5,z208]),(0,[z69,z2,z7,z35,z108,z5]),(0,[z74,z2,z7,z61,z5,z10]),(0,[z1,z2,z7,z4,z5,z1052])],[(0,[z1,z431,z7,z596,z5,z6]),(0,[z1,z2,z7,z354,z4,z5]),(0,[z1,z1053,z2,z7,z4,z5]),(0,[z1,z22,z2,z739,z4,z5])],[(0,[z0,z139,z7,z4,z73,z6]),(0,[z1,z2,z1054,z7,z4,z5]),(0,[z1,z2,z7,z4,z1055,z6]),(0,[z1,z2,z7,z78,z5,z6]),(0,[z1,z2,z7,z108,z172,z6]),(0,[z1,z2,z7,z1056,z4,z5]),(0,[z77,z2,z7,z4,z19,z27])],[(0,[z1,z2,z7,z4,z1057,z6]),(0,[z1,z2,z7,z4,z5,z75]),(0,[z1,z2,z7,z4,z5,z1058]),(0,[z1,z20,z25,z35,z4,z5]),(0,[z1,z1059,z2,z7,z4,z5]),(0,[z1,z244,z7,z158,z5,z127])],[(0,[z1,z2,z7,z4,z5,z342]),(0,[z1,z2,z1060,z4,z5,z6]),(0,[z1,z2,z7,z4,z1061,z6]),(0,[z1,z2,z7,z4,z5,z1062]),(0,[z1,z7,z4,z5,z1063,z6]),(0,[z1,z2,z7,z5,z800,z10]),(0,[z1,z2,z7,z4,z5,z1064])],[(0,[z1,z2,z7,z4,z5,z1065]),(0,[z1,z2,z7,z1066,z5,z6]),(0,[z1,z1067,z2,z7,z78,z5]),(0,[z1,z303,z7,z4,z142,z6]),(0,[z1,z22,z2,z460,z7,z4])],[(0,[z1,z2,z1068,z7,z4,z5]),(0,[z54,z1,z7,z4,z5,z748]),(0,[z1,z2,z7,z5,z722,z6]),(0,[z1,z22,z2,z7,z550,z5]),(0,[z1,z2,z7,z4,z131,z138])]],
   [[(0,[z0,z139,z3,z4,z5,z6]),(0,[z1,z2,z7,z423,z73,z6]),(0,[z1,z296,z2,z7,z108,z6]),(0,[z1,z2,z7,z4,z238,z9]),(0,[z1,z2,z7,z4,z5,z1069])],[(0,[z1,z1070,z2,z7,z4,z5]),(0,[z1,z1071,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z1072]),(0,[z1,z2,z7,z4,z1073,z6]),(0,[z1,z2,z7,z4,z5,z1074]),(0,[z1,z112,z2,z4,z482,z6])],[(0,[z1,z2,z7,z4,z5,z1075]),(0,[z1,z2,z7,z1076,z5,z6]),(0,[z1,z1077,z2,z7,z4,z5]),(0,[z2,z38,z850,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z1078]),(0,[z62,z22,z2,z7,z4,z76]),(0,[z1,z2,z7,z1079,z4,z5]),(0,[z1,z22,z2,z7,z5,z55])],[(0,[z1,z2,z94,z4,z5,z9]),(0,[z1,z2,z1080,z4,z5,z6]),(0,[z1,z22,z589,z2,z4,z5]),(0,[z1,z2,z7,z4,z5,z1081]),(0,[z1,z2,z1082,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z1083]),(0,[z1,z969,z7,z4,z5,z10]),(0,[z1,z2,z7,z4,z5,z1084]),(0,[z1,z22,z34,z2,z12,z5]),(0,[z1,z600,z2,z4,z5,z82])],[(0,[z1,z2,z7,z4,z5,z152]),(0,[z1,z79,z2,z4,z5,z82]),(0,[z1,z22,z2,z7,z5,z83])],[(0,[z1,z22,z2,z7,z4,z397]),(1,[z1,z7,z4,z711,z6]),(0,[z1,z2,z7,z4,z5,z1085])],[(0,[z1,z589,z2,z4,z5,z9]),(0,[z1,z589,z25,z4,z5,z6]),(0,[z1,z2,z7,z1086,z4,z5]),(0,[z492,z2,z38,z7,z4,z5]),(0,[z69,z2,z7,z108,z5,z6]),(0,[z1,z2,z7,z1087,z4,z5]),(0,[z1,z34,z2,z460,z12,z6])],[(0,[z1,z2,z94,z4,z84,z6]),(0,[z1,z1088,z2,z7,z5,z6]),(0,[z1,z296,z2,z7,z35,z4]),(0,[z1,z2,z7,z4,z5,z1089])]],
   [[(0,[z0,z139,z7,z4,z5,z9]),(0,[z1,z469,z2,z4,z5,z9]),(0,[z1,z2,z437,z7,z4,z199]),(0,[z1090,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z1091,z5,z6]),(0,[z1,z7,z4,z5,z711,z6]),(0,[z1,z2,z4,z5,z82,z715]),(0,[z1,z2,z7,z4,z5,z1092]),(0,[z1,z526,z2,z7,z35,z5])],[(0,[z1,z2,z7,z241,z5,z10]),(0,[z1,z2,z7,z4,z5,z1093]),(0,[z1,z2,z7,z4,z5,z1094]),(0,[z1,z2,z1095,z7,z4,z6]),(0,[z1,z2,z7,z4,z397,z75]),(0,[z1,z2,z7,z4,z5,z1096]),(0,[z1,z2,z14,z796,z5,z6]),(0,[z1,z18,z2,z7,z722,z6])],[(0,[z1,z2,z94,z150,z5,z6]),(0,[z77,z2,z7,z4,z19,z6]),(0,[z361,z2,z7,z4,z76,z6]),(0,[z72,z2,z7,z4,z5,z747]),(0,[z1097,z2,z7,z4,z5,z6]),(0,[z1,z2,z1098,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z1099]),(0,[z1,z1100,z7,z4,z5,z6])],[(0,[z1,z2,z7,z4,z5,z1101]),(0,[z1,z2,z7,z4,z5,z1102])],[(0,[z0,z139,z7,z4,z84,z6]),(0,[z2,z708,z7,z4,z5,z6]),(0,[z1,z1103,z2,z7,z4,z5]),(0,[z1,z2,z7,z4,z5,z1104])],[(0,[z1,z2,z7,z423,z5,z9]),(0,[z1,z2,z7,z4,z5,z1105]),(0,[z1,z2,z7,z1106,z4,z5]),(0,[z1,z2,z7,z1107,z4,z5])],[(0,[z1,z1108,z7,z4,z5,z6]),(0,[z2,z7,z4,z5,z10,z601]),(0,[z1,z357,z2,z7,z5,z9]),(0,[z50,z1,z22,z7,z30,z5])],[(0,[z0,z139,z7,z150,z5,z6]),(0,[z17,z708,z7,z4,z5,z6]),(0,[z1,z22,z2,z7,z596,z5]),(0,[z1,z2,z7,z4,z5,z1109]),(0,[z1,z22,z2,z7,z4,z172]),(0,[z1,z2,z7,z4,z5,z1110]),(0,[z623,z2,z7,z4,z5,z9]),(0,[z1,z22,z2,z7,z118,z5]),(0,[z1,z2,z7,z4,z5,z1111]),(0,[z1,z2,z7,z4,z5,z1112]),(0,[z1,z2,z162,z4,z5,z153]),(0,[z191,z492,z2,z7,z4,z5])]],
   [[(0,[z1,z2,z7,z4,z5,z1113]),(0,[z1,z258,z7,z4,z5,z10]),(0,[z1,z431,z7,z4,z5,z9]),(0,[z1,z2,z7,z1114,z4,z5]),(0,[z1,z2,z7,z4,z5,z1115]),(0,[z1,z2,z7,z5,z1005,z10]),(0,[z1,z2,z460,z7,z354,z4]),(0,[z1,z79,z2,z4,z137,z5])],[(0,[z1,z2,z7,z423,z84,z6]),(0,[z90,z492,z2,z7,z4,z5]),(0,[z1,z2,z7,z1116,z4,z5]),(0,[z1,z2,z7,z4,z5,z1117]),(0,[z1,z2,z7,z4,z5,z193]),(0,[z1,z2,z7,z1118,z5,z6]),(0,[z1,z2,z1119,z7,z4,z5]),(0,[z1,z2,z7,z35,z5,z763])],[(0,[z1,z2,z7,z1120,z5,z6]),(0,[z1,z2,z7,z4,z5,z1121]),(0,[z1,z2,z4,z1122,z5,z6]),(0,[z1,z2,z7,z4,z5,z1123]),(0,[z1,z2,z7,z4,z5,z1124]),(0,[z1,z2,z7,z1125,z5,z6]),(0,[z1,z401,z2,z784,z4,z5]),(0,[z1,z112,z2,z4,z23,z10]),(0,[z1,z357,z2,z47,z7,z6]),(0,[z1,z2,z7,z35,z5,z93]),(0,[z1,z79,z2,z4,z5,z715]),(0,[z1,z22,z2,z7,z4,z743])],[(0,[z1,z2,z7,z35,z4,z84]),(0,[z90,z2,z8,z35,z4,z5]),(0,[z1,z2,z460,z7,z108,z6]),(0,[z1,z2,z7,z4,z397,z322]),(0,[z1,z2,z7,z4,z5,z1126]),(0,[z1,z2,z7,z4,z5,z1127]),(0,[z50,z1,z7,z737,z5,z6]),(0,[z1,z2,z1128,z4,z5,z6]),(0,[z1,z2,z7,z4,z722,z6])],[(0,[z0,z22,z139,z7,z4,z5]),(0,[z1,z244,z7,z158,z5,z10]),(0,[z1,z18,z2,z7,z37,z10]),(0,[z1,z2,z7,z1129,z5,z6]),(0,[z1,z244,z7,z5,z472,z6]),(0,[z1,z2,z7,z4,z5,z748]),(0,[z1,z34,z2,z444,z12,z5])],[(0,[z1,z2,z7,z4,z1130,z6]),(0,[z1,z2,z7,z4,z238,z6]),(0,[z1,z1131,z7,z4,z5,z6]),(0,[z1,z1132,z2,z7,z4,z5]),(0,[z1,z2,z7,z391,z4,z602])],[(0,[z1,z22,z2,z7,z4,z73]),(0,[z90,z2,z8,z241,z5,z6]),(0,[z1,z198,z2,z7,z4,z5]),(0,[z1,z2,z7,z4,z5,z1133]),(0,[z1,z7,z4,z5,z97,z748]),(0,[z1,z2,z47,z4,z842,z6]),(0,[z1,z2,z7,z4,z5,z1134]),(0,[z1,z22,z2,z7,z35,z5])],[(0,[z1,z2,z7,z4,z5,z1135]),(0,[z0,z708,z7,z4,z5,z6]),(0,[z1,z718,z2,z7,z4,z5]),(0,[z1,z2,z4,z23,z842,z6])]],
   [[(0,[z1,z2,z94,z4,z5,z6]),(0,[z1,z22,z2,z95,z7,z5]),(0,[z1,z431,z7,z4,z5,z523]),(0,[z1,z2,z7,z596,z5,z9]),(0,[z1,z2,z7,z4,z5,z1136]),(0,[z1,z40,z7,z4,z56,z9])],[(0,[z1,z2,z3,z4,z73,z6]),(0,[z1,z2,z7,z1137,z5,z6]),(0,[z1,z183,z2,z7,z164,z5])],[(0,[z166,z22,z2,z38,z4,z5]),(0,[z1,z2,z7,z78,z5,z364]),(0,[z1,z296,z2,z7,z4,z9]),(0,[z1,z2,z460,z7,z35,z4]),(0,[z1,z2,z7,z165,z57,z58])],[(0,[z1,z589,z2,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z1138]),(0,[z1,z2,z1139,z7,z4,z5]),(0,[z1,z2,z7,z4,z5,z1140])],[(0,[z1,z7,z4,z1141,z5,z6]),(0,[z1,z2,z7,z4,z5,z220]),(0,[z433,z2,z7,z108,z5,z6]),(0,[z1,z2,z7,z4,z1142,z6]),(0,[z54,z1,z7,z4,z5,z97]),(0,[z1,z2,z7,z1143,z4,z5])],[(0,[z0,z139,z7,z4,z5,z6]),(0,[z1,z469,z2,z4,z5,z6]),(0,[z90,z258,z8,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z1144])],[(0,[z1,z589,z2,z4,z5,z1145]),(0,[z1,z1146,z2,z7,z4,z5]),(0,[z1,z2,z7,z4,z5,z1147]),(0,[z1,z2,z7,z1148,z4,z5]),(0,[z1,z22,z2,z7,z571,z5]),(0,[z1,z2,z7,z35,z4,z110]),(0,[z1,z2,z7,z57,z722,z6])],[(0,[z1,z2,z7,z35,z4,z141]),(0,[z1,z2,z7,z4,z5,z1149])]],
   [[(0,[z69,z2,z7,z770,z5,z6]),(0,[z1,z183,z2,z7,z61,z5]),(0,[z1,z2,z7,z78,z5,z10]),(0,[z1,z2,z7,z57,z238,z6]),(0,[z1,z2,z47,z35,z4,z113]),(0,[z1,z2,z7,z35,z346,z5])],[(0,[z1,z2,z7,z4,z73,z9]),(0,[z1,z2,z1150,z4,z5,z6]),(0,[z1,z1151,z2,z7,z4,z5]),(0,[z1,z2,z7,z1152,z4,z5]),(0,[z1,z22,z2,z7,z338,z5]),(0,[z1,z2,z7,z165,z57,z101])],[(0,[z1,z2,z7,z423,z5,z6]),(1,[z708,z7,z4,z5,z6]),(0,[z1,z22,z2,z7,z478,z5]),(0,[z1,z7,z4,z5,z1063,z10]),(0,[z1,z2,z7,z4,z1153,z6]),(0,[z1,z2,z121,z7,z4,z46])],[(0,[z1,z1154,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z6,z1155]),(0,[z1,z2,z7,z4,z5,z1156]),(0,[z1,z2,z7,z4,z5,z1157])],[(0,[z1,z2,z4,z5,z778,z6]),(0,[z1,z2,z7,z78,z76,z6]),(0,[z1,z2,z7,z1158,z5,z6]),(0,[z1,z2,z7,z35,z5,z483])],[(0,[z1,z431,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z208]),(0,[z90,z2,z8,z4,z5,z85]),(0,[z1,z2,z7,z1159,z5,z6]),(0,[z1,z22,z2,z944,z4,z5])],[(0,[z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z7,z4,z1160,z6]),(0,[z1,z1161,z2,z7,z4,z5]),(0,[z1,z2,z7,z1162,z4,z5]),(0,[z77,z492,z2,z7,z4,z5]),(0,[z1,z183,z34,z2,z7,z5]),(0,[z1,z1163,z2,z7,z4,z5])],[(0,[z1,z2,z784,z4,z5,z6]),(0,[z1,z2,z437,z7,z4,z210]),(0,[z1,z2,z499,z4,z5,z153]),(0,[z1,z2,z7,z4,z5,z1164])]],
   [[(0,[z1,z2,z7,z4,z5,z1165]),(0,[z1,z22,z2,z7,z105,z5])],[(0,[z90,z2,z8,z4,z475,z6]),(0,[z1,z48,z49,z4,z141,z6]),(0,[z1,z2,z7,z4,z5,z1166]),(0,[z1,z1167,z7,z4,z5,z6]),(0,[z384,z1,z7,z4,z59,z5])],[(0,[z1,z2,z3,z4,z84,z6]),(0,[z1,z2,z7,z4,z1168,z6]),(0,[z1,z2,z7,z4,z1169,z6]),(0,[z1,z2,z7,z1170,z4,z5]),(0,[z1,z1171,z2,z4,z5,z6]),(0,[z1,z1172,z2,z7,z4,z5]),(0,[z1,z663,z7,z4,z5,z327]),(0,[z1,z2,z7,z4,z5,z1173]),(0,[z1,z2,z7,z4,z5,z1174]),(0,[z1,z2,z7,z4,z1175,z6]),(0,[z1,z2,z7,z1176,z4,z5]),(0,[z1,z1163,z357,z2,z7,z5])],[(0,[z1,z20,z803,z4,z5,z6]),(0,[z1,z2,z7,z1177,z4,z5]),(0,[z203,z401,z2,z7,z4,z5])],[(0,[z166,z2,z38,z4,z5,z6]),(0,[z1,z22,z2,z519,z7,z5]),(0,[z1,z2,z7,z477,z5,z9]),(0,[z1,z20,z25,z4,z5,z193]),(0,[z1178,z2,z7,z4,z5,z6]),(0,[z1,z22,z2,z47,z4,z113])],[(0,[z1,z2,z3,z150,z5,z6]),(0,[z213,z2,z7,z4,z5,z10]),(0,[z1,z2,z460,z7,z4,z9]),(0,[z50,z1,z169,z7,z30,z5])],[(0,[z69,z198,z2,z7,z108,z5]),(0,[z2,z7,z164,z266,z4,z5]),(0,[z398,z2,z7,z4,z5,z10]),(0,[z643,z2,z7,z4,z5,z10]),(0,[z315,z2,z7,z4,z5,z10]),(0,[z1,z2,z7,z1179,z5,z6]),(0,[z1,z40,z7,z4,z149,z56]),(0,[z1,z2,z7,z4,z1180,z6])],[(0,[z1,z2,z7,z1181,z4,z5]),(0,[z1,z2,z7,z4,z5,z1182]),(0,[z1,z401,z2,z7,z180,z5]),(0,[z77,z2,z7,z4,z19,z10]),(0,[z1,z2,z803,z4,z5,z6]),(0,[z1,z296,z2,z7,z4,z6]),(0,[z1,z2,z7,z4,z5,z1183]),(0,[z385,z2,z7,z266,z4,z5])]],
   [[(0,[z1,z2,z1184,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z1185]),(0,[z90,z184,z2,z4,z5,z6]),(0,[z1,z2,z4,z5,z1186,z6]),(0,[z62,z2,z7,z35,z4,z76]),(0,[z400,z2,z7,z4,z5,z10]),(0,[z1,z2,z7,z4,z5,z1187]),(0,[z1,z2,z7,z4,z5,z1188]),(0,[z1,z1189,z7,z4,z5,z6]),(0,[z1,z22,z2,z7,z578,z5])],[(0,[z1,z258,z7,z35,z4,z5]),(0,[z1,z2,z7,z1190,z4,z5])],[(0,[z1,z2,z7,z4,z84,z9]),(0,[z1,z2,z7,z1191,z4,z5]),(0,[z1,z2,z7,z477,z5,z27]),(0,[z1,z2,z7,z4,z177,z9]),(0,[z1,z2,z7,z4,z879,z6])],[(0,[z77,z2,z7,z4,z726,z6]),(0,[z1,z2,z1192,z7,z4,z5]),(0,[z1,z2,z7,z4,z5,z1193]),(0,[z1,z22,z2,z7,z4,z110]),(0,[z1,z7,z158,z737,z5,z6]),(0,[z1,z2,z7,z4,z5,z1194]),(0,[z1,z22,z2,z7,z4,z11])],[(0,[z1,z2,z7,z1195,z5,z6]),(0,[z1,z258,z7,z241,z5,z6]),(0,[z1,z2,z7,z1196,z5,z6]),(0,[z1,z2,z7,z4,z5,z1197]),(0,[z1,z2,z1198,z7,z4,z6]),(0,[z1,z2,z7,z4,z5,z1199]),(0,[z1,z2,z4,z5,z777,z9]),(0,[z1,z2,z7,z4,z1200,z6])],[(0,[z1,z17,z3,z4,z5,z6]),(0,[z1,z2,z7,z150,z5,z9]),(0,[z1,z2,z7,z4,z5,z1201]),(0,[z1,z1202,z7,z4,z5,z6]),(0,[z1,z2,z1203,z7,z4,z5]),(0,[z1,z183,z2,z13,z7,z5]),(0,[z1,z2,z7,z149,z5,z55]),(0,[z1,z2,z4,z796,z5,z6]),(0,[z1,z22,z1100,z7,z4,z5])],[(0,[z1,z2,z7,z4,z73,z6]),(0,[z1,z401,z2,z7,z4,z5]),(0,[z1,z2,z7,z266,z4,z5]),(0,[z1,z2,z7,z1204,z4,z5]),(0,[z1,z2,z7,z4,z5,z1205]),(0,[z1,z2,z7,z4,z5,z1206]),(0,[z1,z2,z13,z14,z5,z330])],[(0,[z1,z2,z226,z4,z5,z292]),(0,[z1,z2,z7,z1207,z4,z5]),(0,[z793,z2,z7,z4,z5,z6]),(0,[z966,z22,z2,z7,z4,z5])]],
   [[(0,[z1,z2,z7,z4,z1208,z6]),(0,[z1,z2,z13,z14,z5,z9]),(0,[z203,z2,z7,z4,z5,z9]),(0,[z1,z2,z7,z4,z6,z1209]),(0,[z1,z2,z7,z4,z5,z1210])],[(0,[z1,z1211,z2,z4,z5,z9]),(0,[z1,z88,z7,z4,z5,z100]),(0,[z1,z18,z2,z7,z578,z6])],[(0,[z1,z2,z7,z1212,z5,z6]),(0,[z1,z155,z2,z12,z5,z6]),(0,[z1,z2,z7,z4,z5,z1213]),(0,[z1,z48,z49,z4,z5,z10]),(0,[z1,z2,z7,z4,z238,z10]),(0,[z1,z2,z7,z4,z5,z1214]),(0,[z1,z22,z2,z7,z425,z5]),(0,[z1,z2,z7,z4,z5,z1215]),(0,[z1,z215,z2,z146,z4,z5])],[(0,[z1,z2,z3,z4,z5,z6]),(0,[z74,z2,z7,z770,z5,z6]),(0,[z2,z7,z4,z5,z1216,z6]),(0,[z1,z2,z7,z4,z5,z1217]),(0,[z1,z348,z2,z4,z137,z5])],[(0,[z1,z2,z1218,z4,z5,z6]),(0,[z1,z2,z7,z241,z5,z85]),(0,[z1,z2,z7,z4,z172,z9]),(0,[z1,z2,z7,z165,z57,z10]),(0,[z1,z81,z7,z4,z5,z748])],[(0,[z1,z2,z94,z4,z5,z10]),(0,[z1,z589,z258,z4,z5,z6]),(0,[z1,z2,z7,z35,z596,z5]),(0,[z2,z7,z770,z108,z5,z6]),(0,[z1,z2,z7,z35,z4,z172]),(0,[z225,z2,z7,z61,z5,z6]),(0,[z1,z2,z7,z4,z5,z1219])],[(0,[z1,z2,z7,z4,z5,z1220])],[(0,[z1,z2,z1221,z7,z4,z5]),(0,[z1,z2,z7,z4,z1222,z6]),(0,[z1,z2,z1223,z4,z5,z6]),(0,[z1,z2,z7,z35,z5,z116]),(0,[z1,z2,z7,z4,z5,z1224]),(0,[z50,z1,z7,z35,z30,z5]),(0,[z1,z2,z1225,z4,z5,z6]),(0,[z1,z2,z226,z4,z5,z153])]],
   [[(0,[z1,z2,z7,z1226,z5,z6]),(0,[z1,z2,z7,z4,z1227,z6]),(0,[z16,z17,z7,z4,z5,z9]),(0,[z1,z609,z25,z4,z5,z6]),(0,[z1,z2,z7,z731,z241,z5]),(0,[z1,z2,z7,z4,z5,z1228]),(0,[z1,z2,z7,z4,z5,z1229]),(0,[z1,z2,z921,z7,z4,z5])],[(0,[z1230,z2,z7,z4,z5,z6]),(0,[z1231,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z1232,z4,z5]),(0,[z1,z2,z7,z4,z5,z330])],[(0,[z1,z2,z7,z4,z5,z1233]),(0,[z1,z2,z7,z4,z172,z322]),(1,[z1,z7,z737,z5,z6]),(0,[z1,z2,z460,z7,z4,z6])],[(0,[z1,z2,z7,z4,z5,z9]),(0,[z1,z1234,z2,z7,z4,z5]),(0,[z1,z258,z7,z4,z5,z85]),(0,[z69,z2,z7,z108,z5,z154]),(0,[z1,z2,z1235,z7,z4,z5]),(0,[z1,z2,z47,z4,z113,z10]),(0,[z1,z2,z7,z4,z5,z1236]),(0,[z54,z1,z7,z4,z434,z5]),(0,[z1,z2,z7,z4,z5,z1237]),(0,[z1,z2,z7,z35,z4,z774])],[(0,[z1,z2,z7,z35,z4,z73]),(0,[z1,z2,z1238,z7,z4,z6]),(0,[z1,z2,z7,z4,z5,z1239]),(0,[z1,z2,z7,z4,z5,z1240])],[(0,[z1,z1241,z2,z7,z4,z5]),(0,[z1,z2,z7,z4,z5,z1242]),(0,[z1,z744,z2,z7,z241,z5]),(0,[z1,z2,z7,z4,z1243,z6]),(0,[z1,z2,z7,z4,z5,z1244]),(0,[z1,z21,z7,z4,z142,z9]),(0,[z1,z40,z7,z55,z56,z6]),(0,[z1,z196,z7,z4,z56,z6]),(0,[z1,z1245,z2,z7,z4,z5])],[(0,[z1,z607,z25,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z1246]),(0,[z1,z2,z721,z7,z4,z5]),(0,[z1,z112,z2,z4,z684,z6])],[(0,[z1,z2,z7,z423,z5,z10]),(0,[z1,z2,z7,z4,z5,z1247]),(0,[z1,z258,z7,z4,z475,z6]),(0,[z1,z2,z7,z4,z1248,z6]),(0,[z1,z2,z7,z4,z1249,z6]),(0,[z1,z2,z7,z164,z5,z116]),(0,[z1,z2,z7,z4,z1250,z6]),(0,[z1,z2,z1251,z7,z4,z6])]],
   [[(0,[z1,z2,z7,z836,z4,z5]),(0,[z1,z312,z49,z4,z5,z6]),(0,[z1,z2,z7,z1252,z4,z5]),(0,[z1,z2,z7,z4,z5,z1253]),(0,[z1,z2,z7,z1254,z5,z6]),(0,[z1,z2,z7,z4,z5,z1255]),(0,[z1,z2,z7,z1256,z5,z6]),(0,[z1,z2,z347,z4,z5,z82])],[(0,[z16,z17,z7,z4,z5,z359]),(0,[z1,z2,z7,z4,z5,z322]),(0,[z1,z2,z7,z4,z5,z1257]),(0,[z1,z2,z7,z4,z5,z27]),(0,[z1,z34,z2,z12,z5,z9]),(0,[z1,z2,z7,z1258,z5,z6]),(0,[z1,z2,z7,z4,z131,z546]),(0,[z1,z2,z7,z4,z5,z1259]),(0,[z839,z2,z7,z4,z5,z6]),(0,[z1021,z22,z2,z7,z4,z5])],[(0,[z1,z2,z7,z1260,z4,z5]),(0,[z1,z431,z7,z4,z5,z10]),(0,[z1,z1261,z2,z7,z4,z5]),(0,[z1,z2,z7,z4,z1262,z6]),(0,[z1,z18,z2,z7,z325,z37])],[(0,[z1,z2,z7,z4,z5,z523]),(0,[z1,z2,z7,z1263,z5,z6]),(0,[z1,z2,z1264,z7,z4,z6]),(0,[z1,z622,z7,z158,z5,z6]),(0,[z1,z2,z7,z164,z4,z774]),(0,[z1265,z1,z2,z7,z4,z5]),(0,[z1,z22,z2,z13,z14,z5])],[(0,[z1,z2,z7,z4,z5,z359]),(0,[z1,z2,z7,z1266,z5,z6]),(0,[z1,z22,z2,z7,z4,z475]),(0,[z2,z7,z61,z770,z5,z6]),(0,[z1,z2,z7,z4,z11,z10]),(0,[z1,z2,z7,z165,z582,z6]),(0,[z1,z81,z7,z174,z4,z5]),(0,[z1,z2,z7,z4,z5,z262])],[(0,[z1,z2,z7,z1267,z4,z5]),(0,[z1,z357,z2,z7,z19,z6]),(0,[z2,z7,z4,z5,z230,z9]),(0,[z1,z2,z7,z5,z55,z1156]),(0,[z1,z22,z2,z807,z4,z5])],[(0,[z1,z1211,z2,z4,z5,z6]),(0,[z1,z2,z7,z866,z78,z5]),(0,[z1,z2,z1268,z7,z4,z5]),(0,[z1,z2,z7,z4,z1269,z6]),(0,[z1,z1270,z2,z7,z4,z5])],[(0,[z1,z2,z7,z4,z1271,z6]),(0,[z1,z2,z7,z4,z5,z1272]),(0,[z1,z2,z7,z4,z5,z1273]),(0,[z2,z7,z4,z726,z5,z6]),(0,[z1,z2,z7,z4,z5,z1274]),(0,[z1,z40,z7,z130,z4,z56]),(0,[z1265,z1,z357,z2,z7,z5]),(0,[z1,z2,z7,z5,z763,z83])]],
   [[(0,[z1,z2,z7,z4,z5,z311]),(0,[z1,z2,z7,z1275,z4,z5]),(0,[z1,z2,z7,z4,z397,z9]),(0,[z1,z2,z7,z4,z110,z9]),(0,[z1,z1276,z2,z7,z5,z6]),(0,[z1,z2,z7,z1277,z5,z6])],[(0,[z1,z48,z589,z4,z5,z6]),(0,[z1,z589,z2,z4,z5,z782]),(0,[z166,z2,z38,z4,z5,z10]),(0,[z1,z2,z7,z1278,z5,z6]),(0,[z1,z28,z2,z4,z5,z206]),(0,[z1,z18,z554,z2,z7,z6]),(0,[z1,z2,z7,z1279,z5,z6]),(0,[z1,z22,z2,z7,z5,z685])],[(0,[z1,z2,z7,z4,z5,z1280]),(0,[z1,z2,z7,z4,z5,z528]),(0,[z250,z2,z7,z4,z5,z9]),(0,[z1,z2,z7,z1281,z5,z6]),(0,[z1,z2,z1282,z7,z4,z6]),(0,[z1,z2,z7,z4,z842,z6])],[(0,[z1,z2,z7,z4,z5,z1283]),(0,[z1,z2,z7,z4,z1284,z6]),(0,[z1285,z2,z7,z4,z5,z6]),(0,[z1,z22,z2,z1128,z4,z5])],[(0,[z1,z2,z7,z1286,z150,z5]),(0,[z1,z2,z7,z4,z1287,z6]),(0,[z1,z1288,z7,z4,z5,z6]),(0,[z1,z22,z2,z7,z78,z5]),(0,[z1,z296,z2,z7,z4,z10]),(0,[z1,z22,z2,z7,z5,z691]),(0,[z1,z2,z47,z418,z4,z6])],[(0,[z16,z17,z7,z4,z5,z6]),(0,[z1,z48,z410,z4,z5,z6]),(0,[z1,z2,z7,z4,z1289,z6]),(0,[z2,z7,z4,z5,z10,z120]),(0,[z2,z7,z4,z5,z430,z9])],[(0,[z1,z2,z7,z1290,z4,z5]),(0,[z1,z2,z7,z4,z5,z1291]),(0,[z2,z7,z4,z1292,z5,z6]),(0,[z1,z2,z1293,z4,z5,z6]),(0,[z1,z244,z7,z35,z158,z5]),(0,[z213,z2,z7,z164,z4,z5])],[(0,[z1,z2,z1294,z4,z5,z6]),(0,[z492,z2,z139,z7,z4,z5]),(0,[z90,z431,z8,z4,z5,z6]),(0,[z1,z1295,z2,z4,z5,z6]),(0,[z286,z2,z7,z4,z5,z10]),(0,[z1,z2,z7,z4,z141,z9]),(0,[z1,z2,z7,z4,z5,z1296])]],
   [[(0,[z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z1286,z4,z5]),(0,[z1,z2,z7,z1297,z4,z5]),(0,[z1,z2,z1298,z7,z4,z5]),(0,[z1,z468,z7,z4,z5,z97]),(0,[z1,z22,z2,z7,z4,z1200])],[(0,[z1,z22,z535,z2,z7,z5]),(0,[z1,z2,z7,z4,z742,z6]),(0,[z1,z2,z7,z4,z5,z1299]),(0,[z1,z2,z1198,z7,z4,z10]),(0,[z2,z7,z4,z5,z446,z9]),(0,[z1,z22,z296,z2,z7,z4])],[(0,[z1,z139,z3,z4,z5,z6]),(0,[z1,z431,z7,z4,z625,z6]),(0,[z616,z2,z7,z4,z5,z10]),(0,[z1,z21,z7,z4,z142,z6]),(0,[z1,z1300,z2,z7,z4,z5])],[(0,[z1,z2,z7,z4,z5,z1145]),(0,[z1,z492,z2,z7,z4,z5]),(0,[z1,z2,z7,z4,z5,z1301]),(0,[z1,z2,z7,z4,z5,z1302]),(0,[z1,z48,z49,z35,z4,z5]),(0,[z1,z479,z2,z7,z35,z5])],[(0,[z1,z924,z2,z7,z5,z6]),(1,[z2,z7,z4,z726,z6]),(1,[z2,z7,z4,z5,z747]),(0,[z1,z2,z709,z4,z5,z9])],[(0,[z1,z2,z4,z1303,z5,z6]),(0,[z1,z2,z7,z4,z5,z1304]),(0,[z1,z1067,z2,z7,z4,z5]),(0,[z1,z2,z7,z4,z1305,z6]),(0,[z1,z40,z7,z35,z4,z56]),(0,[z1,z2,z7,z5,z55,z1194]),(1,[z1,z2,z4,z842,z6])],[(0,[z1,z2,z94,z35,z4,z5]),(0,[z1,z2,z7,z4,z5,z1306]),(0,[z16,z492,z2,z7,z4,z5]),(0,[z1,z2,z7,z180,z61,z5]),(0,[z1,z2,z7,z4,z5,z71]),(0,[z1,z1307,z2,z7,z4,z5]),(0,[z1,z20,z25,z4,z5,z9]),(0,[z50,z1,z7,z30,z238,z6]),(0,[z1,z34,z2,z12,z5,z6]),(0,[z1,z727,z7,z4,z5,z6])],[(0,[z1,z2,z7,z1308,z4,z5]),(0,[z1,z2,z7,z1309,z5,z6]),(0,[z1,z2,z7,z4,z475,z10]),(0,[z1,z2,z7,z4,z5,z1310])]],
   [[(0,[z1,z2,z3,z4,z5,z10]),(0,[z360,z2,z7,z108,z5,z6]),(0,[z1,z22,z2,z7,z264,z5]),(0,[z1,z2,z7,z4,z33,z10]),(0,[z1,z620,z7,z4,z142,z6]),(0,[z1,z22,z2,z7,z612,z5]),(0,[z1,z2,z7,z5,z6,z1311])],[(0,[z1,z2,z7,z1312,z5,z6]),(0,[z1,z2,z7,z4,z1313,z6]),(0,[z1,z2,z7,z4,z1314,z6]),(0,[z403,z2,z7,z4,z5,z9]),(0,[z1,z2,z7,z35,z4,z11]),(0,[z1,z2,z7,z4,z5,z1315])],[(0,[z1,z2,z7,z596,z625,z6]),(0,[z2,z7,z4,z770,z5,z6]),(0,[z1,z183,z2,z7,z108,z5]),(0,[z1,z2,z7,z4,z5,z1316])],[(0,[z1,z1317,z2,z7,z4,z5]),(0,[z1,z2,z7,z596,z5,z523]),(0,[z1,z2,z7,z1318,z4,z5]),(0,[z1,z2,z7,z4,z5,z1319])],[(0,[z1,z2,z7,z4,z1320,z6]),(0,[z1,z767,z2,z7,z5,z6]),(0,[z1,z2,z7,z4,z5,z1321]),(0,[z1,z2,z4,z842,z113,z6])],[(0,[z1,z2,z7,z4,z397,z6]),(0,[z1,z2,z7,z4,z1227,z10]),(0,[z1,z184,z25,z4,z5,z6]),(0,[z1097,z22,z2,z7,z4,z5])],[(0,[z1,z716,z2,z7,z4,z5]),(0,[z1,z2,z7,z1322,z4,z5]),(1,[z2,z850,z4,z5,z6]),(0,[z1,z2,z7,z4,z774,z6]),(0,[z1,z357,z2,z7,z5,z6]),(0,[z1,z2,z7,z4,z5,z1323])],[(0,[z1,z258,z8,z4,z5,z6]),(0,[z1,z2,z460,z7,z4,z10]),(0,[z2,z305,z7,z4,z5,z9]),(0,[z1,z2,z444,z7,z4,z11]),(0,[z1,z2,z7,z4,z1324,z6])]],
   [[(0,[z1,z2,z7,z4,z1325,z6]),(0,[z1,z2,z7,z4,z5,z747])],[(0,[z1,z2,z7,z1326,z5,z6]),(0,[z1,z2,z7,z4,z1327,z6]),(0,[z1,z49,z803,z4,z5,z6]),(0,[z1,z2,z1328,z7,z4,z5]),(0,[z1,z2,z7,z35,z4,z1329])],[(0,[z74,z401,z2,z7,z61,z5]),(0,[z77,z2,z7,z78,z19,z6]),(0,[z1,z2,z7,z4,z5,z1330]),(0,[z1,z2,z7,z4,z5,z763])],[(0,[z1,z2,z7,z150,z73,z6]),(0,[z1,z431,z7,z35,z4,z5]),(0,[z90,z2,z850,z4,z5,z6]),(0,[z1,z2,z7,z61,z172,z6]),(0,[z1,z2,z7,z4,z353,z43]),(0,[z1,z2,z7,z1331,z4,z5]),(0,[z1,z2,z7,z129,z4,z177])],[(0,[z1,z2,z7,z1308,z423,z5]),(0,[z1,z2,z7,z4,z5,z1332]),(0,[z77,z2,z7,z4,z19,z364]),(0,[z1,z22,z48,z49,z4,z5]),(0,[z1,z2,z7,z80,z57,z6]),(0,[z1,z2,z7,z4,z5,z1333])],[(0,[z1,z2,z1334,z4,z5,z6]),(0,[z90,z22,z2,z8,z4,z5]),(0,[z1,z48,z490,z4,z5,z6]),(0,[z1,z2,z7,z4,z1335,z6]),(0,[z1,z2,z7,z5,z55,z9]),(0,[z1,z2,z7,z4,z5,z1336])],[(0,[z69,z2,z7,z108,z5,z10]),(0,[z1,z2,z7,z4,z1329,z6])],[(0,[z708,z139,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z1337])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 515) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 515).take 515) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1030).take 336) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1366)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [515, 515, 336] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 93).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 93).take 93).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 186).take 70).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [93, 93, 70] = true :=
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

end PEqualNP.Outside.L_meta_38823

theorem PEqualNP.Outside.L_meta_38823 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808928 * 2 ^ 32 + 4209682592) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808928 * 2 ^ 32 + 4209682592) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_38823.solve