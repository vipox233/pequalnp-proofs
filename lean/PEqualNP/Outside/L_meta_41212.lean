import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_41212

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
  Nat.testBit (4276809440 * 2 ^ 32 + 4207460544) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x8005670e36171e65#64 ++ 0x1000ace1c6c2e3cc#64 ++ 0x804fef1e763f3e66#64 ++ 0xf009fde3cec7e7cc#64 : BitVec 256),
   (0x0193036288306aae#64 ++ 0x0032606c51060d55#64 ++ 0xa3b313e38831fffd#64 ++ 0xf476627c71063fff#64 : BitVec 256),
   (0x0c2c1c0156c18550#64 ++ 0x018583802ad830aa#64 ++ 0xdc3c1c03ffc1c7fb#64 ++ 0xfb8783807ff838ff#64 : BitVec 256),
   (0x36c01db40b7a0780#64 ++ 0x06d803b6816f40f0#64 ++ 0xffc01ffc0ffe0787#64 ++ 0xbff803ff81ffc0f0#64 : BitVec 256),
   (0x5bfea0000dadf000#64 ++ 0x0b7fd40001b5be00#64 ++ 0xffffe0000ffff807#64 ++ 0xdffffc0001ffff00#64 : BitVec 256),
   (0x1f7bdadbe0000000#64 ++ 0x23ef7b5b7c000000#64 ++ 0x7ffffffff0000007#64 ++ 0xeffffffffe000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.or, [0, 2]⟩, ⟨.and, [6, 5]⟩, ⟨.or, [1, 8]⟩, ⟨.and, [7, 4]⟩, ⟨.or, [8, 10]⟩, ⟨.or, [2, 10]⟩, ⟨.and, [9, 12]⟩, ⟨.and, [11, 3]⟩, ⟨.or, [13, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0193036288306aae 0x0032606c51060d55 0xa3b313e38831fffd 0xf476627c71063fff

def z1 : W := mkw 0x0c2c1c0156c18550 0x018583802ad830aa 0xdc3c1c03ffc1c7fb 0xfb8783807ff838ff

def z2 : W := mkw 0x1f7bdadbe0000000 0x23ef7b5b7c000000 0x7ffffffff0000007 0xeffffffffe000000

def z3 : W := mkw 0x36401c94034a0500 0x06c80392806940a0 0x7fc01ffc07ce0007 0xaff803ff80f9c000

def z4 : W := mkw 0x5bfea0000dadf000 0x0b7fd40001b5be00 0xffffe0000ffff807 0xdffffc0001ffff00

def z5 : W := mkw 0x8005670e36171e65 0x1000ace1c6c2e3cc 0x804fef1e763f3e66 0xf009fde3cec7e7cc

def z6 : W := mkw 0x0d3f1e43d6c1ed7e 0x01a7e3c87ad83daf 0xdc3f1c03ffc1fffb 0xfb87e3807ff83fff

def z7 : W := mkw 0x36c01db40b7a0780 0x06d803b6816f40f0 0xffc01ffc0ffe0787 0xbff803ff81ffc0f0

def z8 : W := mkw 0x0004040016c18550 0x0000808002d830aa 0x800000000fc1c7f8 0x1000000001f838ff

def z9 : W := mkw 0x8001630e20161a25 0x10002c61c402c344 0x004fef1e703e3806 0xe009fde3ce07c700

def z10 : W := mkw 0x093a8041c0000000 0x2127500838000000 0x0030000180000000 0x0006000030000000

def z11 : W := mkw 0x019200608820608a 0x0032400c11040c11 0xa3b310e18831f99d 0xd476621c31063f33

def z12 : W := mkw 0x1f7bdadbe0000000 0x23ef7b5b7c000000 0x5c7fec1ff0000002 0x4b8ffd83fe000000

def z13 : W := mkw 0x019707629ef1effe 0x0032e0ec53de3dff 0xa3b313e38ff1fffd 0xf476627c71fe3fff

def z14 : W := mkw 0x04001c0152400550 0x008003802a4800aa 0x00001c03f00007f8 0x200003807e0000ff

def z15 : W := mkw 0x082c000004818000 0x0105800000903000 0xdc3c00000fc1c003 0xdb87800001f83800

def z16 : W := mkw 0x24801db40b7a0780 0x049003b6816f40f0 0x80001ffc0ffe0780 0x300003ff81ffc0f0

def z17 : W := mkw 0x493fe24be485f000 0x2927fc497c90be00 0x003fe003f001f800 0x4007fc007e003f00

def z18 : W := mkw 0x5ffffadbedadf000 0x2bffff5b7db5be00 0xfffffffffffff807 0xffffffffffffff00

def z19 : W := mkw 0x0004200004051000 0x000084000080a200 0x804fe000063f3806 0xd009fc0000c7e700

def z20 : W := mkw 0xdbffe70e3fbffe65 0x1b7ffce1c7f7ffcc 0xffffef1e7ffffe67 0xfffffde3cfffffcc

def z21 : W := mkw 0x04041c0156410550 0x008083802ac820aa 0x800c1c03f60107fa 0xf00183807ec020ff

def z22 : W := mkw 0x8005670e36171e65 0x1000ace1c6c2e3cc 0x807fff1ffe3fffff 0xf00fffe3ffc7ffff

def z23 : W := mkw 0x05135adbe0000000 0x20a26b5b7c000000 0x23b31ffff0000005 0xe47663fffe000000

def z24 : W := mkw 0x1f7a98d1c0000000 0x23ef531a38000000 0x7fb010e180000001 0x0ff6021c30000000

def z25 : W := mkw 0x8004250416171e65 0x100084a082c2e3cc 0x80000000063f3e60 0x1000000000c7e7cc

def z26 : W := mkw 0x5bfa800009a8e000 0x0b7f500001351c00 0x7fffe00009c0c007 0xcffffc0001381800

def z27 : W := mkw 0x1f7fdedbf6c18550 0x23effbdb7ed830aa 0xffffffffffc1c7ff 0xfffffffffff838ff

def z28 : W := mkw 0x1ffbdbfbe8306aae 0x23ff7b7f7d060d55 0xfffffffff831ffff 0xffffffffff063fff

def z29 : W := mkw 0x8197676ebe377eef 0x1032ecedd7c6efdd 0xa3fffffffe3fffff 0xf47fffffffc7ffff

def z30 : W := mkw 0x8c2d7f0f76d79f75 0x1185afe1eedaf3ee 0xdc7fff1fffffffff 0xfb8fffe3ffffffff

def z31 : W := mkw 0x32c001b4093a0280 0x0658003681274050 0xffc003fc0ffe0007 0x9ff8007f81ffc000

def z32 : W := mkw 0x0193036288306aae 0x0032606c51060d55 0x23b313e18830f99d 0x0476627c31061f33

def z33 : W := mkw 0x0081036288306aae 0x0010206c51060d55 0x800013e38831fff8 0x3000027c71063fff

def z34 : W := mkw 0x5f7ffadbe58d9000 0x2befff5b7cb1b200 0x7ffffffff7ce0007 0xeffffffffef9c000

def z35 : W := mkw 0x32c001b4093a0280 0x0658003681274050 0x23c003fc003e0004 0x0478007f8007c000

def z36 : W := mkw 0x493ea0000485f000 0x0927d4000090be00 0x003fe0000001f800 0x4007fc0000003f00

def z37 : W := mkw 0x0001024280000000 0x0000204850000000 0x000013e380000000 0x2000027c70000000

def z38 : W := mkw 0x0000050402120600 0x000000a0804240c0 0x80400f1c063e0606 0xb00801e380c7c0c0

def z39 : W := mkw 0xb6c57fbe3f7f1fe5 0x16d8aff7c7efe3fc 0xffcffffe7fff3fe7 0xfff9ffffcfffe7fc

def z40 : W := mkw 0x36c018b009680180 0x06d80316012d0030 0x7f8010e009c00181 0x0ff0021c01380030

def z41 : W := mkw 0xa4015fbe32520fe5 0x14802bf7c64a41fc 0x00001ffe700007e0 0x200003ffce0000fc

def z42 : W := mkw 0x8001630e20161a25 0x10002c61c402c344 0x8043e31e003f3e64 0xf0087c63c007e7cc

def z43 : W := mkw 0x0000000150000050 0x000000002a00000a 0x00000003f0000078 0x000000007e00000f

def z44 : W := mkw 0x7fffffffeffff780 0x2ffffffffdfffef0 0xffffffffffffff87 0xfffffffffffffff0

def z45 : W := mkw 0x0c2c1d0556d38750 0x018583a0aada70ea 0xdc7c1f1fffffc7ff 0xfb8f83e3fffff8ff

def z46 : W := mkw 0x04001c0152400550 0x008003802a4800aa 0x00000c0070000000 0x000001800e000000

def z47 : W := mkw 0x8004240416071441 0x1000848082c0e288 0x00000000060e0000 0x0000000000c1c000

def z48 : W := mkw 0x8004600834051041 0x10008c010680a208 0x000ce00070000000 0x00019c000e000000

def z49 : W := mkw 0x53d2800009286000 0x0a7a500001250c00 0x2380000000000000 0x0470000000000000

def z50 : W := mkw 0x5ffe9c015fe9e550 0x0bffd3802bfd3caa 0xffbc1c03ffc1c7fb 0xfff783807ff838ff

def z51 : W := mkw 0x1353c2daa0000000 0x226a785b54000000 0x23f3f3ff80000005 0xe47e7e7ff0000000

def z52 : W := mkw 0x493ea0000485f000 0x0927d4000090be00 0xdc3fe0000fc1f803 0xdb87fc0001f83f00

def z53 : W := mkw 0x0193436aa8306aae 0x0032686d55060d55 0xa3fffffff831ffff 0xf47fffffff063fff

def z54 : W := mkw 0x0113024280000000 0x0022604850000000 0x23b313e380000005 0xe476627c70000000

def z55 : W := mkw 0x0828000140000000 0x0105000028000000 0x003c0003f0000000 0x400780007e000000

def z56 : W := mkw 0x12c005040b3a0600 0x025800a0816740c0 0xffc00f1c0ffe0607 0xbff801e381ffc0c0

def z57 : W := mkw 0x5bfa800009a8e000 0x0b7f500001351c00 0x7fb0000009c0c001 0x0ff6000001381800

def z58 : W := mkw 0x8001470e32120e65 0x100028e1c64241cc 0x00000f1e70000660 0x200001e3ce0000cc

def z59 : W := mkw 0x8004640c36071441 0x10008c8186c0e288 0x004cec1c760e0002 0x00099d838ec1c000

def z60 : W := mkw 0x09bf03628cb1eaae 0x0137e06c51963d55 0xffbf13e38ff1ffff 0xfff7e27c71fe3fff

def z61 : W := mkw 0x24001db402520780 0x048003b6804a40f0 0x00001ffc00000780 0x200003ff800000f0

def z62 : W := mkw 0x8001670e22161e25 0x10002ce1c442c3c4 0x8043ef1c063e3e06 0xb0087de380c7c7c0

def z63 : W := mkw 0x0c2c180154818050 0x018583002a90300a 0x5c3c1c03f001c07b 0xeb8783807e00380f

def z64 : W := mkw 0x408420000dadf000 0x0810840001b5be00 0x800000000ffff800 0x1000000001ffff00

def z65 : W := mkw 0x0001420a20000000 0x0000284144000000 0x004fef1e70000006 0xe009fde3ce000000

def z66 : W := mkw 0x16401d9402120600 0x02c803b2804240c0 0xffc01ffc063e0607 0xbff803ff80c7c0c0

def z67 : W := mkw 0x0080000008206000 0x0010000001040c00 0x800000000831f800 0x1000000001063f00

def z68 : W := mkw 0x8085672e3e371ee5 0x1010ace5c7c6e3dc 0xa3cffffe7e3f3fe7 0xf479ffffcfc7e7fc

def z69 : W := mkw 0x3ffa98f1c9680180 0x27ff531e392d0030 0x7fb010e189c00181 0x0ff6021c31380030

def z70 : W := mkw 0x04015adbe0000000 0x20802b5b7c000000 0x00001ffff0000000 0x200003fffe000000

def z71 : W := mkw 0x9f7fffdff6171e65 0x33effffbfec2e3cc 0xfffffffff63f3e67 0xfffffffffec7e7cc

def z72 : W := mkw 0x5bffa2428dadf82e 0x0b7ff44851b5bf05 0xffffe0038ffff87f 0xdffffc0071ffff0f

def z73 : W := mkw 0x16415a9a20000000 0x02c82b5344000000 0x7fcffffe70000007 0xeff9ffffce000000

def z74 : W := mkw 0x0c2c180144c18110 0x0185830028983022 0xdc3c10018fc1c19b 0xdb87820031f83833

def z75 : W := mkw 0x3e6c1c9557cb8550 0x07cd8392aaf970aa 0xdc7c1c1fffcfc7fb 0xfb8f8383fff9f8ff

def z76 : W := mkw 0xb2c567be3f3f1ee5 0x1658acf7c7e7e3dc 0xa3cfeffe763f3e66 0xf479fdffcec7e7cc

def z77 : W := mkw 0x1353c2daa0000000 0x226a785b54000000 0x23cfeffe70000006 0xe479fdffce000000

def z78 : W := mkw 0xd3d3e30e293e7a25 0x1a7a7c61c527cf44 0x23c3e31c003e3804 0x04787c638007c700

def z79 : W := mkw 0x36c018b009680180 0x06d80316012d0030 0xffc010e00ffe0187 0x9ff8021c01ffc030

def z80 : W := mkw 0x3ffbdbffe93a0280 0x27ff7b7ffd274050 0x7ffffffff03e0007 0xeffffffffe07c000

def z81 : W := mkw 0x09bbc36be8306aae 0x2137786d7d060d55 0xa3bff3e3f831fffd 0xf477fe7c7f063fff

def z82 : W := mkw 0x5ffa98d1c9a8e000 0x2bff531a39351c00 0x7fb010e189c0c001 0x0ff6021c31381800

def z83 : W := mkw 0x0c28180140000000 0x0185030028000000 0xdc3c1c03f801c7fb 0xfb8783807f0038ff

def z84 : W := mkw 0x17531ad280000000 0x02ea635a50000000 0x7ff31fff80000007 0xeffe63fff0000000

def z85 : W := mkw 0x8005630e24171a25 0x1000ac61c482e344 0x804fe31c063f3806 0xd009fc6380c7e700

def z86 : W := mkw 0x0004040016010440 0x0000808002c02088 0x800c0c0276010662 0xf00181804ec020cc

def z87 : W := mkw 0x0c28180140c08110 0x0185030028181022 0x5c3c1c03f9c0c19b 0xeb8783807f381833

def z88 : W := mkw 0x5bfea0608dadf08a 0x0b7fd40c11b5be11 0xfffff0e18ffff99f 0xdffffe1c31ffff33

def z89 : W := mkw 0x13d3c3faa8306aae 0x227a787f55060d55 0xa3f3f3ff8831fffd 0xf47e7e7ff1063fff

def z90 : W := mkw 0x8c2c7c0d76c79551 0x11858f81aed8f2aa 0x5c4cec1c77ce0002 0x0b899d838ef9c000

def z91 : W := mkw 0x4080000009a8e000 0x0810000001351c00 0x0000000009c0c000 0x0000000001381800

def z92 : W := mkw 0x12c0000009280000 0x0258000001250000 0xffc000000ffe0007 0x9ff8000001ffc000

def z93 : W := mkw 0xffffffbe3fffffe5 0x1ffffff7c7fffffc 0xfffffffe7fffffe7 0xffffffffcffffffc

def z94 : W := mkw 0x0001036280100aae 0x0000206c50020155 0x800313e380313ffc 0xf000627c700627ff

def z95 : W := mkw 0x1ffbdbfbe8306aae 0x23ff7b7f7d060d55 0x7ffffffff0303807 0xeffffffffe060700

def z96 : W := mkw 0xdbffe76ebfbffeef 0x1b7ffcedd7f7ffdd 0xffffffffffffffff 0xffffffffffffffff

def z97 : W := mkw 0x819727669e377eef 0x1032e4ecd3c6efdd 0xa3b313e38e3ffffd 0xf476627c71c7ffff

def z98 : W := mkw 0x0005070216110e64 0x0000a0e042c221cc 0x800f0f0276313e66 0xf001e1e04ec627cc

def z99 : W := mkw 0x37d31ff68b7a6fae 0x06fa63fed16f4df5 0xfff31fff8fffffff 0xfffe63fff1ffffff

def z100 : W := mkw 0x3eec1db55ffb87d0 0x07dd83b6abff70fa 0xfffc1fffffffc7ff 0xffff83fffffff8ff

def z101 : W := mkw 0x0193036288306aae 0x0032606c51060d55 0x238303e000303804 0x0470607c00060700

def z102 : W := mkw 0x0192000008206000 0x0032400001040c00 0xa3b310038831fffd 0xf476620071063fff

def z103 : W := mkw 0x36c41db41f7b07c0 0x06d883b683ef60f8 0xffcc1ffe7fff07e7 0xfff983ffcfffe0fc

def z104 : W := mkw 0xb6c17fbe2b7e1fa5 0x16d82ff7c56fc3f4 0xffc3fffc0ffe3f87 0xbff87fff81ffc7f0

def z105 : W := mkw 0x2cac1d255ffb87d0 0x059583a4abff70fa 0xdc3c1c03ffffc7fb 0xfb8783807ffff8ff

def z106 : W := mkw 0x0113034280100a24 0x0022606850020144 0xa3b313e380313e65 0xf476627c700627cc

def z107 : W := mkw 0x1e68d89960000000 0x23cd1b132c000000 0x7fccfffc70000007 0xaff99fff8e000000

def z108 : W := mkw 0x0001020200000824 0x0000204040000104 0x0003000200013860 0x400060004000270c

def z109 : W := mkw 0x0828000140808010 0x0105000028101002 0x003000018000c018 0x0006000030001803

def z110 : W := mkw 0x9b7fe70e36171e65 0x136ffce1c6c2e3cc 0xffffef1e763f3e67 0xfffffde3cec7e7cc

def z111 : W := mkw 0x0001430a20100a24 0x0000286144020144 0x804fef1e70313e66 0xf009fde3ce0627cc

def z112 : W := mkw 0x0001036280100aae 0x0000206c50020155 0x000013e3800007f8 0x2000027c700000ff

def z113 : W := mkw 0x0192000008206000 0x0032400001040c00 0xa3b300000831f805 0xd476600001063f00

def z114 : W := mkw 0x53d2a000092c7000 0x0a7a540001258e00 0x23c3e000003e3804 0x04787c000007c700

def z115 : W := mkw 0x5bffa3628dbdfaae 0x0b7ff46c51b7bf55 0xfffff3e38fffffff 0xfffffe7c71ffffff

def z116 : W := mkw 0x53d6a0000d2d7000 0x0a7ad40001a5ae00 0xa3cfe000063f3806 0xd479fc0000c7e700

def z117 : W := mkw 0x1240000000000000 0x0248000000000000 0x7fc0000000000007 0x8ff8000000000000

def z118 : W := mkw 0x0113036280106aae 0x0022606c50020d55 0x003313e38001fff8 0x6006627c70003fff

def z119 : W := mkw 0x0c2c1c0156c18550 0x018583802ad830aa 0xdc0c0c0277c10662 0xfb8181804ef820cc

def z120 : W := mkw 0x5bfa800009a8e000 0x0b7f500001351c00 0xfff000000ffec007 0x9ffe000001ffd800

def z121 : W := mkw 0x04001c0002400500 0x00800380004800a0 0xdc301c038fc1c7fb 0xfb86038071f838ff

def z122 : W := mkw 0x17d31bf288306aae 0x02fa637e51060d55 0xfff31fff8831ffff 0xfffe63fff1063fff

def z123 : W := mkw 0x0400589960000000 0x20800b132c000000 0x00000c1c70000000 0x000001838e000000

def z124 : W := mkw 0x0080012008306aae 0x0010002401060d55 0x800000000831fff8 0x1000000001063fff

def z125 : W := mkw 0x1e68d89960000000 0x23cd1b132c000000 0x5c4cec1c70000002 0x0b899d838e000000

def z126 : W := mkw 0x0000000000000000 0x0000000000000000 0x8003000000313804 0xd000600000062700

def z127 : W := mkw 0x0193036288306aae 0x0032606c51060d55 0x238313e380303ffc 0x2470627c700607ff

def z128 : W := mkw 0x093bc24be0000000 0x212778497c000000 0x003fe003f0000000 0x4007fc007e000000

def z129 : W := mkw 0x1640189000000000 0x02c8031200000000 0x7fc01ffc00000007 0xaff803ff80000000

def z130 : W := mkw 0x1ffbdadbe9280000 0x23ff7b5b7d250000 0xfffffffffffe0007 0xffffffffffffc000

def z131 : W := mkw 0x1f7bdadbe0000000 0x23ef7b5b7c000000 0x7fbff0e3f0000001 0x4ff7fe1c7e000000

def z132 : W := mkw 0x1bfa800008206000 0x037f500001040c00 0xffffe0000831f807 0xdffffc0001063f00

def z133 : W := mkw 0x5a6ca000058d9000 0x0b4d940000b1b200 0x5c4ce00007ce0002 0x0b899c0000f9c000

def z134 : W := mkw 0x019200608820608a 0x0032400c11040c11 0x23b010e18800c199 0x0476021c31001833

def z135 : W := mkw 0x8005670e36d79f75 0x1000ace1c6daf3ee 0x804fef1e7ffffffe 0xf009fde3cfffffff

def z136 : W := mkw 0x882d670e36979e65 0x1105ace1c6d2f3cc 0xdc7fef1e7ffffe67 0xfb8ffde3cfffffcc

def z137 : W := mkw 0x36c15fffeb7a0780 0x26d82bfffd6f40f0 0xffc01ffffffe0787 0xbff803ffffffc0f0

def z138 : W := mkw 0x8005660e36071441 0x1000acc1c6c0e288 0x004fef1e760e0006 0xe009fde3cec1c000

def z139 : W := mkw 0x8005670e36171e65 0x1000ace1c6c2e3cc 0x8043e31c063f3e64 0x10087c6380c7e7cc

def z140 : W := mkw 0x8005470e36130e65 0x1000a8e1c6c261cc 0x800c0f1e76010662 0xf00181e3cec020cc

def z141 : W := mkw 0x0400189000000000 0x0080031200000000 0x00001ffc00000000 0x200003ff80000000

def z142 : W := mkw 0x4d3ebc0156c5f550 0x09a7d7802ad8beaa 0xdc3ffc03ffc1fffb 0xfb87ff807ff83fff

def z143 : W := mkw 0x019723628c357aae 0x0032e46c5186af55 0xa3fff3e38e3fffff 0xf47ffe7c71c7ffff

def z144 : W := mkw 0x1640189000000000 0x02c8031200000000 0x5c400c1c00000002 0x0b88018380000000

def z145 : W := mkw 0x32c005240b7a0780 0x065800a4816f40f0 0xffc000000ffe0787 0x9ff8000001ffc0f0

def z146 : W := mkw 0x5b7ea0000485f000 0x0b6fd4000090be00 0x7fffe0000001f807 0xcffffc0000003f00

def z147 : W := mkw 0x8005676eb6171eef 0x1000acedd6c2e3dd 0x804ffffff63f3ffe 0xf009fffffec7e7ff

def z148 : W := mkw 0x8001630e20161a25 0x10002c61c402c344 0x0043e31c003e3804 0x00087c638007c700

def z149 : W := mkw 0x04011f63d2500ffe 0x008023ec7a4a01ff 0x00001fe3f00007f8 0x200003fc7e0000ff

def z150 : W := mkw 0x36c01db40b7a0780 0x06d803b6816f40f0 0xdc400c1c0ffe0782 0x1b88018381ffc0f0

def z151 : W := mkw 0x1f7bdadbe000682e 0x23ef7b5b7c000d05 0x7ffffffff001f87f 0xeffffffffe003f0f

def z152 : W := mkw 0x0112000000006000 0x0022400000000c00 0x003300000001f800 0x4006600000003f00

def z153 : W := mkw 0x408420000dadf000 0x0810840001b5be00 0x804fe0000ffff806 0xd009fc0001ffff00

def z154 : W := mkw 0xda6de70e379f9e65 0x1b4dbce1c6f3f3cc 0xdc4fef1e77ff3e66 0xfb89fde3ceffe7cc

def z155 : W := mkw 0x1f7a98d1c0000000 0x23ef531a38000000 0x7fbc1ce3f0000003 0xeff7839c7e000000

def z156 : W := mkw 0x7ffebdb40ffff780 0x0fffd7b681fffef0 0xfffffffc0fffff87 0xffffffff81fffff0

def z157 : W := mkw 0x0113034280106a2e 0x0022606850020d45 0x803303038031fe7c 0xf006606070063fcf

def z158 : W := mkw 0x3ee818b149e88190 0x07dd0316293d1032 0x7fb010e189c0c199 0x0ff6021c31381833

def z159 : W := mkw 0x082c000154818050 0x010580002a90300a 0x003c0003f001c078 0x400780007e00380f

def z160 : W := mkw 0x36c01db55b7a07d0 0x06d803b6ab6f40fa 0xffc01ffffffe07ff 0xbff803ffffffc0ff

def z161 : W := mkw 0x1b7a800000000000 0x036f500000000000 0x7fb0000000000001 0x0ff6000000000000

def z162 : W := mkw 0x8c2c3d0556d79f75 0x118587a0aadaf3ee 0xdc3c1c03fffffffb 0xfb8783807fffffff

def z163 : W := mkw 0x5bfea0000dadf000 0x0b7fd40001b5be00 0x7fcfe00007fe3806 0x0ff9fc0000ffc700

def z164 : W := mkw 0x011302428000682e 0x0022604850000d05 0x003300038001f878 0x4006600070003f0f

def z165 : W := mkw 0x36401c94034a0500 0x06c80392806940a0 0x5c400c1c07ce0002 0x0b88018380f9c000

def z166 : W := mkw 0x04001c0002400500 0x00800380004800a0 0xdc001c000fc00783 0xbb80038001f800f0

def z167 : W := mkw 0x8005670e36171e65 0x1000ace1c6c2e3cc 0x800fe002763f3e60 0x5001fc004ec7e7cc

def z168 : W := mkw 0x0192000008206000 0x0032400001040c00 0x2383000000303804 0x0470600000060700

def z169 : W := mkw 0x5b7ea000058d9000 0x0b6fd40000b1b200 0x7fffe00007ce0007 0xcffffc0000f9c000

def z170 : W := mkw 0x7fffbff68fffffae 0x0ffff7fed1fffff5 0xffffffff8fffffff 0xfffffffff1ffffff

def z171 : W := mkw 0x12c0012009380280 0x0258002401270050 0xffc013e00ffe0787 0xbff8027c01ffc0f0

def z172 : W := mkw 0x13d2000009286000 0x027a400001250c00 0xfff300000ffff807 0xdffe600001ffff00

def z173 : W := mkw 0x082c000154818050 0x010580002a90300a 0xdc3c0003ffc1c07b 0xdb8780007ff8380f

def z174 : W := mkw 0x0000012000100aae 0x0000002400020155 0x00000000000007f8 0x00000000000000ff

def z175 : W := mkw 0x20800124093a0280 0x0410002481274050 0x00000000003e0000 0x000000000007c000

def z176 : W := mkw 0x0c28180140c08110 0x0185030028181022 0x5c30100189c0c199 0x0b86020031381833

def z177 : W := mkw 0x0001420a20000000 0x0000284144000000 0x000fe00270000000 0x4001fc004e000000

def z178 : W := mkw 0xc93fe20a3485f865 0x1927fc414690bf0c 0x003fe0027001f860 0x4007fc004e003f0c

def z179 : W := mkw 0x33d303f6893a6aae 0x067a607ed1274d55 0xa3f313ff883ffffd 0xf47e627ff107ffff

def z180 : W := mkw 0x1f7bdadbe0c08110 0x23ef7b5b7c181022 0x7ffffffff9c0c19f 0xefffffffff381833

def z181 : W := mkw 0x5ffebc015fedf550 0x0bffd7802bfdbeaa 0xfffffc03ffffffff 0xffffff807fffffff

def z182 : W := mkw 0x893fe74ff6171e65 0x3127fce9fec2e3cc 0x807fef1ff63f3e66 0xf00ffde3fec7e7cc

def z183 : W := mkw 0xdbffe20a3dadf865 0x1b7ffc4147b5bf0c 0xffffe0027ffff867 0xdffffc004fffff0c

def z184 : W := mkw 0x0000000000000000 0x0000000000000000 0x803010038801c7f9 0xf0060200710038ff

def z185 : W := mkw 0x0dbf1f63def1effe 0x01b7e3ec7bde3dff 0xffbf1fe3fff1ffff 0xfff7e3fc7ffe3fff

def z186 : W := mkw 0x0000000000000000 0x0000000000000000 0x8000100008000781 0xb0000200010000f0

def z187 : W := mkw 0x0080012008300280 0x0010002401060050 0x238003e000300004 0x0470007c00060000

def z188 : W := mkw 0x3ffbdfffeb7a0780 0x27ff7bfffd6f40f0 0xfffffffffffe0787 0xffffffffffffc0f0

def z189 : W := mkw 0x8005620a34051865 0x1000ac414680a30c 0x000fe00270013860 0x4001fc004e00270c

def z190 : W := mkw 0x1f7bdbfbe0100aae 0x23ef7b7f7c020155 0x7ffffffff00007ff 0xeffffffffe0000ff

def z191 : W := mkw 0x0c295a0b60000000 0x01852b416c000000 0x5c7fff1ff0000007 0xeb8fffe3fe000000

def z192 : W := mkw 0x5bffa2428dadf000 0x0b7ff44851b5be00 0xfffff3e38ffff807 0xfffffe7c71ffff00

def z193 : W := mkw 0x40802000092c7000 0x0810040001258e00 0x00000000003e3800 0x000000000007c700

def z194 : W := mkw 0x84057f0f76571f75 0x1080afe1eecae3ee 0x804fff1ff63f3ffe 0xf009ffe3fec7e7ff

def z195 : W := mkw 0x000000608000008a 0x0000000c10000011 0x000010e180000198 0x0000021c30000033

def z196 : W := mkw 0x1353c2daa0000000 0x226a785b54000000 0x23c3e3fc00000004 0x04787c7f80000000

def z197 : W := mkw 0x49bea0000dadf000 0x0937d40001b5be00 0x803fe0000ffff800 0x5007fc0001ffff00

def z198 : W := mkw 0x0c2c1c0156c18550 0x018583802ad830aa 0x5c0c0c0077c00002 0x0b8181800ef80000

def z199 : W := mkw 0x135280d080000000 0x226a501a10000000 0x238000e000000000 0x0470001c00000000

def z200 : W := mkw 0x0004040016010440 0x0000808002c02088 0x000c0c0076000002 0x000181800ec00000

def z201 : W := mkw 0x8004200014051865 0x100084000280a30c 0x0000000000013860 0x000000000000270c

def z202 : W := mkw 0x0112004080000000 0x0022400810000000 0x23b010e180000001 0x0476021c30000000

def z203 : W := mkw 0xdbfea5041fbffe65 0x1b7fd4a083f7ffcc 0xffffe0000ffffe67 0xdffffc0001ffffcc

def z204 : W := mkw 0x019200608820608a 0x0032400c11040c11 0x238000e000000000 0x0470001c00000000

def z205 : W := mkw 0x37d218f08968618a 0x06fa431e112d0c31 0x7fb010e189c0c199 0x0ff6021c31381833

def z206 : W := mkw 0x24015fffe2520780 0x24802bfffc4a40f0 0x00001ffff0000780 0x200003fffe0000f0

def z207 : W := mkw 0x0001070602120e24 0x000020e0c04241c4 0x80430f1e063f3e66 0xf00861e3c0c7e7cc

def z208 : W := mkw 0x208005240b7a0780 0x041000a4816f40f0 0x800000000ffe0780 0x1000000001ffc0f0

def z209 : W := mkw 0x208005240b7a0780 0x041000a4816f40f0 0x80400f1c0ffe0786 0xb00801e381ffc0f0

def z210 : W := mkw 0x8005660e36071c65 0x1000acc1c6c0e38c 0x004fec1e760f3862 0x4009fd83cec1e70c

def z211 : W := mkw 0x36c019b4093a0280 0x06d8033681274050 0x7fc01ffc003e0007 0xaff803ff8007c000

def z212 : W := mkw 0x8193636ea8367aaf 0x10326c6dd506cf55 0xa3f3f3ff883ffffd 0xf47e7e7ff107ffff

def z213 : W := mkw 0x1b7bc20a20000000 0x036f784144000000 0x7fffef1e70000007 0xeffffde3ce000000

def z214 : W := mkw 0x04015bfbe0100aae 0x20802b7f7c020155 0x00001ffff00007f8 0x200003fffe0000ff

def z215 : W := mkw 0x5ffef8996dadf000 0x2bffdf132db5be00 0xffffec1c7ffff807 0xdffffd838fffff00

def z216 : W := mkw 0x1f7fdadbe4818000 0x23effb5b7c903000 0xffffffffffc1c007 0xfffffffffff83800

def z217 : W := mkw 0x8005270616171e65 0x1000a4e0c2c2e3cc 0x80030302063f3e64 0xf000606040c7e7cc

def z218 : W := mkw 0x1f7b9ad3c0000000 0x23ef735a78000000 0x7fb313e380000005 0xeff6627c70000000

def z219 : W := mkw 0x12c0000009280000 0x0258000001250000 0x7f80000009c00001 0x0ff0000001380000

def z220 : W := mkw 0x24001db402520780 0x048003b6804a40f0 0x80401ffc063e0786 0xb00803ff80c7c0f0

def z221 : W := mkw 0x1f7bdadbe0000000 0x23ef7b5b7c000000 0x7fcfeffc70000006 0x0ff9fdff8e000000

def z222 : W := mkw 0x8dbf7f6ffef7ffff 0x11b7efedffdeffff 0xffffffffffffffff 0xffffffffffffffff

def z223 : W := mkw 0x0c28180140000000 0x0185030028000000 0x5c3c1c03f0000003 0xeb8783807e000000

def z224 : W := mkw 0x093a800000000000 0x0127500000000000 0x003fe00000000000 0x4007fc0000000000

def z225 : W := mkw 0x0c28180140c08110 0x0185030028181022 0x5c00000001c00000 0x0b80000000380000

def z226 : W := mkw 0x0c28180140c08110 0x0185030028181022 0xdc30100389c1c7f9 0xfb860200713838ff

def z227 : W := mkw 0x1753dadbe0000000 0x22ea7b5b7c000000 0x23c3fffff0000004 0x24787ffffe000000

def z228 : W := mkw 0x1640189000000000 0x02c8031200000000 0x7f8010e000000001 0x0ff0021c00000000

def z229 : W := mkw 0x1bfa800009280000 0x037f500001250000 0xffffe0000ffe0007 0xdffffc0001ffc000

def z230 : W := mkw 0x0001030200100a24 0x0000206040020144 0x8003030200313e64 0xf0006060400627cc

def z231 : W := mkw 0x36c01cb00b680580 0x06d80396016d00b0 0xff801ce00fc00783 0xbff0039c01f800f0

def z232 : W := mkw 0x0193036288306aae 0x0032606c51060d55 0x23b313e380303805 0xe476627c70060700

def z233 : W := mkw 0x7ffebdb55ffff7d0 0x0fffd7b6abfffefa 0xffffffffffffffff 0xffffffffffffffff

def z234 : W := mkw 0x5fffbf63dffdfffe 0x0bfff7ec7bffbfff 0xffffffe3ffffffff 0xfffffffc7fffffff

def z235 : W := mkw 0x1b7bc2dbe0000000 0x236f785b7c000000 0x23ffe3fff0000004 0x447ffc7ffe000000

def z236 : W := mkw 0x01930262882068ae 0x0032604c51040d15 0x23b310e38801f9f9 0x4476621c71003f3f

def z237 : W := mkw 0x1f7fdedbf6010440 0x23effbdb7ec02088 0xfffffffff6010667 0xfffffffffec020cc

def z238 : W := mkw 0x0001420a20000000 0x0000284144000000 0x00000f1e70000000 0x200001e3ce000000

def z239 : W := mkw 0x0c281c0142c08510 0x01850380285810a2 0xdc301c018fc0c79b 0xbb86038031f818f3

def z240 : W := mkw 0x000000000000682e 0x0000000000000d05 0x000000000001f878 0x0000000000003f0f

def z241 : W := mkw 0x082c200004859000 0x010584000090b200 0xdc7fe0000ffff807 0xdb8ffc0001ffff00

def z242 : W := mkw 0x36c15fbe2b7a0780 0x06d82bf7c56f40f0 0xffcffffe7ffe0787 0xfff9ffffcfffc0f0

def z243 : W := mkw 0x0c2c180154c18150 0x018583002a98302a 0x5c3c1003f9c1c1f9 0x4b8782007f38383f

def z244 : W := mkw 0x3eec1cb15fe985d0 0x07dd83962bfd30ba 0xffbc1ce3ffc1c7fb 0xfff7839c7ff838ff

def z245 : W := mkw 0x53d6a0000dadf000 0x0a7ad40001b5be00 0xa3c3e0000ffff804 0x14787c0001ffff00

def z246 : W := mkw 0x3ffbdfffeb7a6fae 0x27ff7bfffd6f4df5 0xffffffffffffffff 0xffffffffffffffff

def z247 : W := mkw 0x1f7a98d1c0c08110 0x23ef531a38181022 0x7fb010e189c0c199 0x0ff6021c31381833

def z248 : W := mkw 0x24001db5525207d0 0x048003b6aa4a40fa 0x00001ffff00007f8 0x200003fffe0000ff

def z249 : W := mkw 0x0192012008306280 0x0032402401060c50 0xa3b313e00831ff85 0xf476627c01063ff0

def z250 : W := mkw 0x0000000000000000 0x0000000000000000 0x00001003800007f8 0x20000200700000ff

def z251 : W := mkw 0x0004000004010000 0x0000800000802000 0x800c000006010002 0xd001800000c02000

def z252 : W := mkw 0x0001470e22120600 0x000028e1c44240c0 0x804fef1e763e0606 0xf009fde3cec7c0c0

def z253 : W := mkw 0x8004250416171e65 0x100084a082c2e3cc 0x80400f1c063f3e66 0xb00801e380c7e7cc

def z254 : W := mkw 0x0c2c1c0156c18550 0x018583802ad830aa 0x5c3c1c01ffc0c19b 0x0b8783803ff81833

def z255 : W := mkw 0x019620000c257000 0x0032c4000184ae00 0xa3ffe0000e3ff807 0xd47ffc0001c7ff00

def z256 : W := mkw 0x5bfa800009a8e000 0x0b7f500001351c00 0xffb3000009f1f805 0xdff66000013e3f00

def z257 : W := mkw 0x5bfea0000dadf000 0x0b7fd40001b5be00 0x23ffe000003ff804 0x447ffc000007ff00

def z258 : W := mkw 0x0113024280000000 0x0022604850000000 0xa3b313e38801c7fd 0xf476627c710038ff

def z259 : W := mkw 0x0193036288306aae 0x0032606c51060d55 0xa38313e008303f85 0xb470627c010607f0

def z260 : W := mkw 0x8005620a34051865 0x1000ac414680a30c 0x004fef1e70013866 0xe009fde3ce00270c

def z261 : W := mkw 0x5aeca0000dad9000 0x0b5d940001b5b200 0xffcce0000ffe0007 0x9ff99c0001ffc000

def z262 : W := mkw 0x05931f63da706ffe 0x00b263ec7b4e0dff 0xa3b31fe3f831fffd 0xf47663fc7f063fff

def z263 : W := mkw 0x5bfaa00009acf000 0x0b7f540001359e00 0x7ff3e00009fef805 0x0ffe7c00013fdf00

def z264 : W := mkw 0x36c01db40b7a0780 0x06d803b6816f40f0 0x7f801ffc09c00781 0x2ff003ff813800f0

def z265 : W := mkw 0xc08425041fbffe65 0x181084a083f7ffcc 0x800000000ffffe60 0x1000000001ffffcc

def z266 : W := mkw 0x8c2d7f0f76d79f75 0x1185afe1eedaf3ee 0xdc4fef1e77ff3e66 0xfb89fde3ceffe7cc

def z267 : W := mkw 0x9e6cfc9d76071441 0x33cd9f93aec0e288 0x5c4cec1c760e0002 0x0b899d838ec1c000

def z268 : W := mkw 0x019302428820682e 0x0032604851040d05 0xa3b300038831f87d 0xd476600071063f0f

def z269 : W := mkw 0x0113424aa0000000 0x0022684954000000 0x23fffffff0000007 0xe47ffffffe000000

def z270 : W := mkw 0x3ee81db54b7a0780 0x07dd03b6a96f40f0 0xfffc1ffffffe0787 0xffff83ffffffc0f0

def z271 : W := mkw 0x37d31bf289786bae 0x06fa637e512f0d75 0xffb313e389f1fffd 0xfff6627c713e3fff

def z272 : W := mkw 0x0000010000100a24 0x0000002000020144 0x8000000000313e60 0x10000000000627cc

def z273 : W := mkw 0x8004250416171e65 0x100084a082c2e3cc 0x800c0c02763f3e62 0xf00181804ec7e7cc

def z274 : W := mkw 0x1b7a800000000000 0x036f500000000000 0x7fffe00000000007 0xcffffc0000000000

def z275 : W := mkw 0x1e68d89960000000 0x23cd1b132c000000 0x5c7cfc1ff0000003 0xeb8f9f83fe000000

def z276 : W := mkw 0x5aeca0000dadf000 0x0b5d940001b5be00 0xdc4ce0000ffff802 0x1b899c0001ffff00

def z277 : W := mkw 0x36c01c940b6a0500 0x06d80392816d40a0 0xffc00c1c0ffe0007 0x9ff8018381ffc000

def z278 : W := mkw 0x5a6ca000058d9000 0x0b4d940000b1b200 0xdc7ce0000fcfc003 0xdb8f9c0001f9f800

def z279 : W := mkw 0x37d21db40b7a6780 0x06fa43b6816f4cf0 0xfff31ffc0fffff87 0xfffe63ff81fffff0

def z280 : W := mkw 0x8197670e3e377e65 0x1032ece1c7c6efcc 0xa3ffef1e7e3ffe67 0xf47ffde3cfc7ffcc

def z281 : W := mkw 0x36c01db40b7a0780 0x06d803b6816f40f0 0xfff01fff8fffc7ff 0xfffe03fff1fff8ff

def z282 : W := mkw 0x0000040402020400 0x0000008080404080 0x00400c1c060e0002 0x0008018380c1c000

def z283 : W := mkw 0x24801d240b7a0780 0x049003a4816f40f0 0xdc001c000ffe0783 0xbb80038001ffc0f0

def z284 : W := mkw 0x5bfea4001fadf440 0x0b7fd48003f5be88 0xffffec027ffffe67 0xfffffd804fffffcc

def z285 : W := mkw 0x0828000000000000 0x0105000000000000 0x5c3c000000000003 0xcb87800000000000

def z286 : W := mkw 0x093f0243d481e87e 0x0127e0487a903d0f 0x003f0003f001f878 0x4007e0007e003f0f

def z287 : W := mkw 0x0004040016c18550 0x0000808002d830aa 0x0000000007c00000 0x0000000000f80000

def z288 : W := mkw 0x5ffbfadbe92c7000 0x2bff7f5b7d258e00 0x7ffffffff03e3807 0xeffffffffe07c700

def z289 : W := mkw 0x96457f9e36171e65 0x12c8aff3c6c2e3cc 0xffcffffe763f3e67 0xfff9ffffcec7e7cc

def z290 : W := mkw 0x0c2c1c0006c18500 0x0185838000d830a0 0xdc3c1c000fc1c783 0xfb87838001f838f0

def z291 : W := mkw 0x0c28180140000000 0x0185030028000000 0x5c0c0c0070000002 0x0b8181800e000000

def z292 : W := mkw 0x36401d94035a0700 0x06c803b2806b40e0 0xdc400f1c07fe0606 0xbb8801e380ffc0c0

def z293 : W := mkw 0xd3d7e70e3f3f7e65 0x1a7afce1c7e7efcc 0xa3cfef1e763f3e66 0xf479fde3cec7e7cc

def z294 : W := mkw 0x1e69da9b60000000 0x23cd3b536c000000 0x5c4fef1e70000006 0xeb89fde3ce000000

def z295 : W := mkw 0x200001b400120280 0x0400003680024050 0x000003fc00000000 0x0000007f80000000

def z296 : W := mkw 0x0004000004818000 0x0000800000903000 0x800000000fc1c000 0x1000000001f83800

def z297 : W := mkw 0x73d2a1b4093e7280 0x0e7a54368127ce50 0x23c3e3fc003e3804 0x04787c7f8007c700

def z298 : W := mkw 0x0113024280000000 0x0022604850000000 0x238303e000000004 0x0470607c00000000

def z299 : W := mkw 0xdfffffdfffbffe65 0x3bfffffbfff7ffcc 0xfffffffffffffe67 0xffffffffffffffcc

def z300 : W := mkw 0x1240c09820000000 0x2248181304000000 0x0040e01c00000000 0x00081c0380000000

def z301 : W := mkw 0x0113024280000000 0x0022604850000000 0x0033000380000000 0x4006600070000000

def z302 : W := mkw 0x36c01db40b7a6fae 0x06d803b6816f4df5 0xffc01ffc0fffffff 0xbff803ff81ffffff

def z303 : W := mkw 0x53d3a362893c7aae 0x0a7a746c51278f55 0x23c3e3e0003e3804 0x04787c7c0007c700

def z304 : W := mkw 0xc085670e3fbffe65 0x1810ace1c7f7ffcc 0x804fef1e7ffffe66 0xf009fde3cfffffcc

def z305 : W := mkw 0x05935bfbe8306aae 0x20b26b7f7d060d55 0xa3b31ffff831fffd 0xf47663ffff063fff

def z306 : W := mkw 0x04001c0002400500 0x00800380004800a0 0x5c000c0007c00002 0x0b80018000f80000

def z307 : W := mkw 0x32c001b4093a0280 0x0658003681274050 0xa3c013fc083e0785 0xb478027f8107c0f0

def z308 : W := mkw 0x53d2a000092c7000 0x0a7a540001258e00 0xffc3e0000ffe3807 0x9ff87c0001ffc700

def z309 : W := mkw 0x84015f0f72520f75 0x10802be1ee4a41ee 0x00001f1ff00007f8 0x200003e3fe0000ff

def z310 : W := mkw 0x0080012008300280 0x0010002401060050 0xa38013e008300785 0xb470027c010600f0

def z311 : W := mkw 0x24011ff682520fae 0x048023fed04a41f5 0x00001fff800007f8 0x200003fff00000ff

def z312 : W := mkw 0x36c019b4097a0380 0x06d80336812f4070 0x7fc013fc09fe0185 0x0ff8027f813fc030

def z313 : W := mkw 0x2080002009680180 0x04100004012d0030 0x0000000009c00180 0x0000000001380030

def z314 : W := mkw 0x04015adbe0000000 0x20802b5b7c000000 0x004ffffff0000006 0xe009fffffe000000

def z315 : W := mkw 0x8004650c36171641 0x10008ca186c2e2c8 0x804cef1c763e0606 0xb0099de38ec7c0c0

def z316 : W := mkw 0x1e69dadbe0000000 0x23cd3b5b7c000000 0x5c4cfffff0000002 0x2b899ffffe000000

def z317 : W := mkw 0x493fa2428485f82e 0x0927f4485090bf05 0x003fe0038001f878 0x4007fc0070003f0f

def z318 : W := mkw 0x5bfa806089a8e08a 0x0b7f500c11351c11 0x7fb010e189c0c199 0x0ff6021c31381833

def z319 : W := mkw 0x0d3fde4bf6c18550 0x21a7fbc97ed830aa 0xdc3ffc03ffc1c7fb 0xfb87ff807ff838ff

def z320 : W := mkw 0x808425241e377eef 0x101084a483c6efdd 0x800000000e3ffff8 0x1000000001c7ffff

def z321 : W := mkw 0x0192016088306aae 0x0032402c11060d55 0xa3b010e18831fff9 0x1476021c31063fff

def z322 : W := mkw 0x8001476eb2120eef 0x100028edd64241dd 0x00001ffff00007f8 0x200003fffe0000ff

def z323 : W := mkw 0x5bfaa000092c7000 0x0b7f540001258e00 0x7fffe000003e3807 0xcffffc000007c700

def z324 : W := mkw 0x3ffbdafbe9680180 0x27ff7b5f7d2d0030 0x7ffffffff9c00187 0xefffffffff380030

def z325 : W := mkw 0x5bfea0000dadf000 0x0b7fd40001b5be00 0xfffff0038fffffff 0xfffffe0071ffffff

def z326 : W := mkw 0xb6c47dbc3f7f17c1 0x16d88fb787efe2f8 0xffccfffc7ffe0787 0xbff99fff8fffc0f0

def z327 : W := mkw 0x0004000014818050 0x000080000290300a 0x000000000001c078 0x000000000000380f

def z328 : W := mkw 0x1f7e9c0156c18550 0x03efd3802ad830aa 0xfffffc03ffc1c7ff 0xffffff807ff838ff

def z329 : W := mkw 0x240018b000400180 0x0480031600080030 0x000010e000000180 0x0000021c00000030

def z330 : W := mkw 0x0000000000000000 0x0000000000000000 0x238013e000000005 0xa470027c00000000

def z331 : W := mkw 0x0080012008306aae 0x0010002401060d55 0x803010038831fff9 0xf006020071063fff

def z332 : W := mkw 0x5e6cf899658d9000 0x2bcd9f132cb1b200 0x5c4cec1c77ce0002 0x0b899d838ef9c000

def z333 : W := mkw 0xa4057fbe36571fe5 0x1480aff7c6cae3fc 0x804ffffe763f3fe6 0xf009ffffcec7e7fc

def z334 : W := mkw 0x36c11ff68b7a0fae 0x06d823fed16f41f5 0xffc01fff8ffe07ff 0xbff803fff1ffc0ff

def z335 : W := mkw 0x8000210400161a25 0x100004208002c344 0x00000000003e3800 0x000000000007c700

def z336 : W := mkw 0x0000000000000000 0x0000000000000000 0x0030100380000001 0xe006020070000000

def z337 : W := mkw 0x0400180140400110 0x0080030028080022 0x0000100180000198 0x0000020030000033

def z338 : W := mkw 0x49bea0000ca5f000 0x0937d4000194be00 0xa3bfe0000831f805 0xd477fc0001063f00

def z339 : W := mkw 0x1f7bdedbe2400500 0x23ef7bdb7c4800a0 0xffffffffffc00787 0xfffffffffff800f0

def z340 : W := mkw 0x9f7bfbdfe0161a25 0x33ef7f7bfc02c344 0x7ffffffff03e3807 0xeffffffffe07c700

def z341 : W := mkw 0x5bfe80000da9e000 0x0b7fd00001b53c00 0xffbc00000fc1c003 0xdff7800001f83800

def z342 : W := mkw 0x0c2d5edbf6c18550 0x2185abdb7ed830aa 0xdc3c1fffffc1c7fb 0xfb8783fffff838ff

def z343 : W := mkw 0x84057fdff6171e65 0x3080affbfec2e3cc 0x804ffffff63f3e66 0xf009fffffec7e7cc

def z344 : W := mkw 0x33d3c3fea93a0280 0x267a787fd5274050 0x23c3e3fc003e0004 0x04787c7f8007c000

def z345 : W := mkw 0x493a80000080e000 0x0927500000101c00 0x003000000000c000 0x0006000000001800

def z346 : W := mkw 0x1fffdffbfef1effe 0x23fffbff7fde3dff 0xfffffffffff1ffff 0xfffffffffffe3fff

def z347 : W := mkw 0x5bfea1200dbdfaae 0x0b7fd42401b7bf55 0xffffe0000fffffff 0xdffffc0001ffffff

def z348 : W := mkw 0x5ffebc000fedf500 0x0bffd78001fdbea0 0xfffffc000fffff87 0xffffff8001fffff0

def z349 : W := mkw 0x0004200004051000 0x000084000080a200 0x80000000063f3800 0x1000000000c7e700

def z350 : W := mkw 0x8193636ea8367aaf 0x10326c6dd506cf55 0x23c3e3fc003e3804 0x04787c7f8007c700

def z351 : W := mkw 0x36c018b009680180 0x06d80316012d0030 0x7fc01ffc09c00187 0xaff803ff81380030

def z352 : W := mkw 0x32400094010a0000 0x0648001280214000 0x0040001c000e0000 0x000800038001c000

def z353 : W := mkw 0x082c040016818440 0x0105808002d03088 0xdc3c0c027fc1c663 0xfb8781804ff838cc

def z354 : W := mkw 0x5ffeb8d1cdadf000 0x2bffd71a39b5be00 0xfffff0e18ffff807 0xdffffe1c31ffff00

def z355 : W := mkw 0x1f7a989000000000 0x03ef531200000000 0x7ffffffc00000007 0xefffffff80000000

def z356 : W := mkw 0x8193476eba326eef 0x103268edd7464ddd 0xa3b31ffff831fffd 0xf47663ffff063fff

def z357 : W := mkw 0x0000040002400500 0x00000080004800a0 0x800000000fc00780 0x1000000001f800f0

def z358 : W := mkw 0x0d3bda4be0000000 0x21a77b497c000000 0x5c3ffc03f0000003 0xeb87ff807e000000

def z359 : W := mkw 0x0c2c1c0156c18550 0x018583802ad830aa 0xdc3010018fc1c7f9 0x1b86020031f838ff

def z360 : W := mkw 0x019302628820608a 0x0032604c51040c11 0x23b313e38800c19d 0xe476627c71001833

def z361 : W := mkw 0x9ffffffffe377eef 0x33ffffffffc6efdd 0xfffffffffe3fffff 0xffffffffffc7ffff

def z362 : W := mkw 0x0c2c1c0156010440 0x018583802ac02088 0xdc3c1c03f6010663 0xfb8783807ec020cc

def z363 : W := mkw 0x0000012000100280 0x0000002400020050 0x000013e000000780 0x2000027c000000f0

def z364 : W := mkw 0x008005240a320680 0x001000a4814640d0 0xa3c01ffc0e3e0787 0xb47803ff81c7c0f0

def z365 : W := mkw 0x2000052402520780 0x040000a4804a40f0 0x0000000000000780 0x00000000000000f0

def z366 : W := mkw 0x0c281c0152c08550 0x018503802a5810aa 0x5c301c03f9c0c7f9 0x2b8603807f3818ff

def z367 : W := mkw 0x8085672e3e377eef 0x1010ace5c7c6efdd 0x804fef1e7e3ffffe 0xf009fde3cfc7ffff

def z368 : W := mkw 0x082c000154818050 0x010580002a90300a 0x803c1003f801c7f9 0xf00782007f0038ff

def z369 : W := mkw 0x882d670f76979e75 0x1105ace1eed2f3ce 0x807fef1ff63ffe7e 0xf00ffde3fec7ffcf

def z370 : W := mkw 0x0c281c0142400500 0x01850380284800a0 0xdc3c1c03ffc00783 0xfb8783807ff800f0

def z371 : W := mkw 0x1f7a98d1c0000000 0x23ef531a38000000 0x7ffff0e180000007 0xcffffe1c30000000

def z372 : W := mkw 0x8004650c36171e65 0x10008ca186c2e3cc 0x804cec1c763f3e62 0x10099d838ec7e7cc

def z373 : W := mkw 0x5a68800001888000 0x0b4d100000311000 0x5c00000001c00000 0x0b80000000380000

def z374 : W := mkw 0x5ffeb8900dadf000 0x0bffd71201b5be00 0xfffffffc0ffff807 0xffffffff81ffff00

def z375 : W := mkw 0x0004050416130640 0x000080a082c260c8 0x804c0f1e763f0666 0xf00981e3cec7e0cc

def z376 : W := mkw 0x16415adbe0000000 0x22c82b5b7c000000 0x7fc01ffff0000007 0xaff803fffe000000

def z377 : W := mkw 0x0000400820000000 0x0000080104000000 0x004cec1c70000002 0x00099d838e000000

def z378 : W := mkw 0x000102428000082e 0x0000204850000105 0x0000000380000078 0x000000007000000f

def z379 : W := mkw 0x3e6c1c9557cb8550 0x07cd8392aaf970aa 0x5c4c0c1c77ce0002 0x0b8981838ef9c000

def z380 : W := mkw 0x3fff1ff7dffbeffe 0x07ffe3fefbff7dff 0xffff1fffffffffff 0xffffe3ffffffffff

def z381 : W := mkw 0x0000050402120600 0x000000a0804240c0 0x80000000063e0600 0x1000000000c7c0c0

def z382 : W := mkw 0x8005630a34151a65 0x1000ac614682a34c 0x800fe30270313e64 0xf001fc604e0627cc

def z383 : W := mkw 0x5bffa3020dbdfa24 0x0b7ff46041b7bf44 0xffffe3020ffffe67 0xfffffc6041ffffcc

def z384 : W := mkw 0x0000040012400550 0x00000080024800aa 0x00000000000007f8 0x00000000000000ff

def z385 : W := mkw 0x0081032208300aa4 0x0010206441060154 0xa38313e208313fe5 0xf470627c410627fc

def z386 : W := mkw 0x1f7fdedbf6c18550 0x23effbdb7ed830aa 0x7ffffffff7c00007 0xeffffffffef80000

def z387 : W := mkw 0x5bfea5040fbff600 0x0b7fd4a081f7fec0 0xffffef1c0ffffe07 0xfffffde381ffffc0

def z388 : W := mkw 0x3eec1db40ffb8780 0x07dd83b681ff70f0 0xfffc1ffc0fffc787 0xffff83ff81fff8f0

def z389 : W := mkw 0x0000000000000000 0x0000000000000000 0x800000000801c7f8 0x10000000010038ff

def z390 : W := mkw 0x53d2a000092c7000 0x0a7a540001258e00 0xa3f3e000083ff805 0xd47e7c000107ff00

def z391 : W := mkw 0x1f7ad8d9e0000000 0x23ef5b1b3c000000 0x7ffcfcfdf0000003 0x0fff9f9fbe000000

def z392 : W := mkw 0x208405241ffb87d0 0x041080a483ff70fa 0x800000000fffc7f8 0x1000000001fff8ff

def z393 : W := mkw 0x493ea0015485f050 0x0927d4002a90be0a 0x003fe003f001f878 0x4007fc007e003f0f

def z394 : W := mkw 0x36c43db40f7f1780 0x06d887b681efe2f0 0xffcffffc0fff3f87 0xfff9ffff81ffe7f0

def z395 : W := mkw 0x5bffe2daadadf000 0x2b7ffc5b55b5be00 0xffffe3fc0ffff807 0xdffffc7f81ffff00

def z396 : W := mkw 0x04041c0156c18550 0x008083802ad830aa 0x80001c03ffc1c7f8 0x300003807ff838ff

def z397 : W := mkw 0x36401db402520780 0x06c803b6804a40f0 0x7fc01ffc00000787 0xaff803ff800000f0

def z398 : W := mkw 0x13d3036289386aae 0x027a606c51270d55 0xfff313e38fffffff 0xfffe627c71ffffff

def z399 : W := mkw 0x7ffa98b009e8e180 0x0fff5316013d1c30 0x7fb010e009c0c181 0x0ff6021c01381830

def z400 : W := mkw 0x1e6cdc9976c18550 0x23cd9b932ed830aa 0xdc7cfc1fffc1c7fb 0xfb8f9f83fff838ff

def z401 : W := mkw 0x9e6dff9f76171e65 0x33cdbff3eec2e3cc 0xdc4fef1e763f3e66 0xfb89fde3cec7e7cc

def z402 : W := mkw 0x0c2c1c0156c18550 0x018583802ad830aa 0x5c3c0c03f7c1c07a 0x4b8781807ef8380f

def z403 : W := mkw 0xa08425241f7f1fe5 0x141084a483efe3fc 0x800000000fff3fe0 0x1000000001ffe7fc

def z404 : W := mkw 0x1ffbdbfbe8300280 0x23ff7b7f7d060050 0xfffffffff8300787 0xffffffffff0600f0

def z405 : W := mkw 0x0000000000000000 0x0000000000000000 0x004fe00000000006 0xc009fc0000000000

def z406 : W := mkw 0x7eecbdb40fff9780 0x0fdd97b681fff2f0 0xffccfffc0ffe0787 0xbff99fff81ffc0f0

def z407 : W := mkw 0x0000010400120200 0x0000002080024040 0x0040031c003e0004 0x000800638007c000

def z408 : W := mkw 0x011200408000600a 0x0022400810000c01 0x003000018000c018 0x0006000030001803

def z409 : W := mkw 0x9f7fffdff6d79f75 0x33effffbfedaf3ee 0xffffffffffffffff 0xffffffffffffffff

def z410 : W := mkw 0x0000000000000000 0x0000000000000000 0xdc0000000fc00003 0x9b80000001f80000

def z411 : W := mkw 0x12c420000d2d1000 0x0258840001a5a200 0xffcfe0000fff3807 0xdff9fc0001ffe700

def z412 : W := mkw 0x1f7bdadbe0000000 0x23ef7b5b7c000000 0x7fb01ffff0000001 0x2ff603fffe000000

def z413 : W := mkw 0x04041c0016c18550 0x0080838002d830aa 0xdc001c000fc1c7fb 0xbb80038001f838ff

def z414 : W := mkw 0x16c0189009280000 0x02d8031201250000 0xffc01ffc0ffe0007 0xbff803ff81ffc000

def z415 : W := mkw 0x1ffbdadbe8206000 0x23ff7b5b7d040c00 0xfffffffff831f807 0xffffffffff063f00

def z416 : W := mkw 0x2c2c1db556d387d0 0x058583b6aada70fa 0xdc3c1fffffc1c7fb 0xfb8783fffff838ff

def z417 : W := mkw 0x5f7ffadbe485f000 0x2befff5b7c90be00 0x7ffffffff001f807 0xeffffffffe003f00

def z418 : W := mkw 0x8001670e32161e65 0x10002ce1c642c3cc 0x0043ef1e703e3e64 0x20087de3ce07c7cc

def z419 : W := mkw 0x1e68989140000000 0x23cd131228000000 0x5c00000000000000 0x0b80000000000000

def z420 : W := mkw 0xdbffe30e2dbffa25 0x1b7ffc61c5b7ff44 0xffffe31c0ffff807 0xdffffc6381ffff00

def z421 : W := mkw 0x1ffb9bf3c8306aae 0x23ff737e79060d55 0xffb313e38831fffd 0xfff6627c71063fff

def z422 : W := mkw 0x0081032208306aae 0x0010206441060d55 0x800303020831fffc 0xf000606041063fff

def z423 : W := mkw 0x5ffffbfbedbdfaae 0x2bffff7f7db7bf55 0xffffffffffffffff 0xffffffffffffffff

def z424 : W := mkw 0x5bfea1200dbdf280 0x0b7fd42401b7be50 0xfffff3e00fffff87 0xfffffe7c01fffff0

def z425 : W := mkw 0x3f7bdedfe34a0500 0x27ef7bdbfc6940a0 0x7ffffffff7ce0007 0xeffffffffef9c000

def z426 : W := mkw 0x0001020200000000 0x0000204040000000 0x0003030200000004 0xe000606040000000

def z427 : W := mkw 0x9f7bdfdff2120e65 0x33ef7bfbfe4241cc 0x7ffffffff0000667 0xeffffffffe0000cc

def z428 : W := mkw 0x48ac20000dadf000 0x0915840001b5be00 0xdc3c00000ffff803 0xdb87800001ffff00

def z429 : W := mkw 0x0193030208306a24 0x0032606041060d44 0xa3b303020831fe65 0xf476606041063fcc

def z430 : W := mkw 0x0828000000808000 0x0105000000101000 0x5c30000009c0c001 0x0b86000001381800

def z431 : W := mkw 0x0c2c180144818000 0x0185830028903000 0xdc3c1c03ffc1c003 0xfb8783807ff83800

def z432 : W := mkw 0x7ffebc940feff500 0x0fffd79281fdfea0 0xffffec1c0ffff807 0xdffffd8381ffff00

def z433 : W := mkw 0x16401c9002400500 0x02c80392004800a0 0xffc01ffc0fc00787 0xbff803ff81f800f0

def z434 : W := mkw 0x0193036288306aae 0x0032606c51060d55 0x23b303e38031f87c 0x4476607c70063f0f

def z435 : W := mkw 0x0000040002000400 0x0000008000400080 0x80000c0006000602 0xb000018000c000c0

def z436 : W := mkw 0x0c2c3c0156c59550 0x018587802ad8b2aa 0xdc7ffc03ffffffff 0xfb8fff807fffffff

def z437 : W := mkw 0xbfffffffff7f1fe5 0x37ffffffffefe3fc 0xffffffffffff3fe7 0xffffffffffffe7fc

def z438 : W := mkw 0x8000050412120e65 0x100000a0824241cc 0x0000000000000660 0x00000000000000cc

def z439 : W := mkw 0x1e68189140000000 0x03cd031228000000 0x7ffc1ffff0000007 0xefff83fffe000000

def z440 : W := mkw 0x1aec00000da98000 0x035d800001b53000 0xfffc00000fffc007 0xdfff800001fff800

def z441 : W := mkw 0xa085672e3f7f1fe5 0x1410ace5c7efe3fc 0x804fef1e7fff3fe6 0xf009fde3cfffe7fc

def z442 : W := mkw 0x7ffa9db40bfae780 0x0fff53b6817f5cf0 0xfff01ffc0ffec787 0xbffe03ff81ffd8f0

def z443 : W := mkw 0x008405201ef1effe 0x001080a403de3dff 0x800000000ff1fff8 0x1000000001fe3fff

def z444 : W := mkw 0x8000600c20061001 0x10000c018400c200 0x0040e01c000e0000 0x00081c038001c000

def z445 : W := mkw 0x0080000009280000 0x0010000001250000 0x800000000ffe0000 0x1000000001ffc000

def z446 : W := mkw 0x36401c94034a0500 0x06c80392806940a0 0xdc401c1c0fce0783 0xbb88038381f9c0f0

def z447 : W := mkw 0x1753dadaa0000000 0x22ea7b5b54000000 0x7fc3fffc00000007 0xaff87fff80000000

def z448 : W := mkw 0x0001036280100aae 0x0000206c50020155 0x803013e38801c7f9 0xf006027c710038ff

def z449 : W := mkw 0x482ca00004859000 0x090594000090b200 0x000ce00000000000 0x00019c0000000000

def z450 : W := mkw 0xbeed7fbf7fff9ff5 0x17ddaff7effff3fe 0xffffffffffffffff 0xffffffffffffffff

def z451 : W := mkw 0x0080002008200080 0x0010000401040010 0x238010e008000181 0x0470021c01000030

def z452 : W := mkw 0x0000000000000000 0x0000000000000000 0x00400f1c00000006 0xa00801e380000000

def z453 : W := mkw 0x0193036288306aae 0x0032606c51060d55 0xa38303e00831fffc 0x1470607c01063fff

def z454 : W := mkw 0x1b7bc2daa0000000 0x236f785b54000000 0x7fffe3fc00000007 0xcffffc7f80000000

def z455 : W := mkw 0x37d31ff68b7a0780 0x06fa63fed16f40f0 0xfff31fff8ffe0787 0xfffe63fff1ffc0f0

def z456 : W := mkw 0x0004240016051440 0x0000848002c0a288 0x804fec02763f3e66 0xf009fd804ec7e7cc

def z457 : W := mkw 0x0193036288306aae 0x0032606c51060d55 0x803300038831fff8 0x5006600071063fff

def z458 : W := mkw 0x13d3c3faa8306aae 0x227a787f55060d55 0x23c3e3fc00303804 0x04787c7f80060700

def z459 : W := mkw 0x093bc24be0000000 0x212778497c000000 0x007fef1ff0000006 0xe00ffde3fe000000

def z460 : W := mkw 0x3fffdffffffb87d0 0x27fffbffffff70fa 0xffffffffffffc7ff 0xfffffffffffff8ff

def z461 : W := mkw 0x1b7e800004818000 0x036fd00000903000 0xffffe0000fc1c007 0xdffffc0001f83800

def z462 : W := mkw 0x0004000014010040 0x0000800002802008 0x000c000270010060 0x400180004e00200c

def z463 : W := mkw 0x7ffeb8b00dedf180 0x0fffd71601bdbe30 0xfffff0e00ffff987 0xdffffe1c01ffff30

def z464 : W := mkw 0x8005670e36171e65 0x1000ace1c6c2e3cc 0x004fef1c763e3806 0x0009fde38ec7c700

def z465 : W := mkw 0x8004640c36071441 0x10008c8186c0e288 0x804fec1c763f3806 0xd009fd838ec7e700

def z466 : W := mkw 0x05931f628a706fae 0x00b263ec514e0df5 0xffb31fe38ff1ffff 0xfff663fc71fe3fff

def z467 : W := mkw 0x3f7bdfffe2520780 0x27ef7bfffc4a40f0 0x7ffffffff0000787 0xeffffffffe0000f0

def z468 : W := mkw 0x0000000000000000 0x0000000000000000 0x803000000801c001 0xd006000001003800

def z469 : W := mkw 0x1240009000000000 0x0248001200000000 0x23c003fc00000004 0x0478007f80000000

def z470 : W := mkw 0x52c420000dadf000 0x0a58840001b5be00 0xffc000000ffff807 0x9ff8000001ffff00

def z471 : W := mkw 0x8197636abc357aef 0x1032ec6d5786af5d 0xa3bff3e3f831fffd 0xf477fe7c7f063fff

def z472 : W := mkw 0x1f7bdadbe0000000 0x23ef7b5b7c000000 0xfffffffff801c7ff 0xffffffffff0038ff

def z473 : W := mkw 0xb6c15fbe3b7a0fe5 0x16d82bf7c76f41fc 0xffc01ffe7ffe07e7 0xbff803ffcfffc0fc

def z474 : W := mkw 0x0cac1d215ef187d0 0x019583a42bde30fa 0xffbc1fe3fff1c7ff 0xfff783fc7ffe38ff

def z475 : W := mkw 0x4cac3c015fedf550 0x099587802bfdbeaa 0xdc3c1c03fffffffb 0xfb8783807fffffff

def z476 : W := mkw 0x84015fdff2120e65 0x30802bfbfe4241cc 0x00001ffff0000660 0x200003fffe0000cc

def z477 : W := mkw 0x25931ff68a726fae 0x04b263fed14e4df5 0xa3b31fff8831fffd 0xf47663fff1063fff

def z478 : W := mkw 0x5ffeb8014dadf000 0x0bffd70029b5be00 0xfffffc03fffff807 0xffffff807fffff00

def z479 : W := mkw 0xb6447c9c374f1541 0x16c88f9386e9e2a8 0x5c4cec1c77ce0002 0x0b899d838ef9c000

def z480 : W := mkw 0x0000040012000440 0x0000008002400088 0x00000c0270000660 0x200001804e0000cc

def z481 : W := mkw 0x0080012008306aae 0x0010002401060d55 0xa38013e00831fffd 0xb470027c01063fff

def z482 : W := mkw 0x019201608830628a 0x0032402c11060c51 0xa3b013e18830c79d 0xb476027c310618f3

def z483 : W := mkw 0x36c01cb40b6a0580 0x06d80396816d40b0 0x7fc01cfc0fce0183 0x0ff8039f81f9c030

def z484 : W := mkw 0x37d31ff68b7a6fae 0x06fa63fed16f4df5 0xffc31ffc0ffe3f87 0xbff863ff81ffc7f0

def z485 : W := mkw 0x008000200820608a 0x0010000401040c11 0x000000000800c198 0x0000000001001833

def z486 : W := mkw 0x8117674eb6177e6f 0x1022ece9d6c2efcd 0x807fef1ff63ffe7e 0xf00ffde3fec7ffcf

def z487 : W := mkw 0x0000200000041000 0x0000040000008200 0x0043e000003e3804 0x00087c000007c700

def z488 : W := mkw 0x32c005b40b3a0680 0x065800b6816740d0 0xa3c00ffc063e0606 0xb47801ff80c7c0c0

def z489 : W := mkw 0x893fe24bf4051865 0x3127fc497e80a30c 0x003fe003f0013860 0x4007fc007e00270c

def z490 : W := mkw 0x36c01db40b7a0780 0x06d803b6816f40f0 0x7fc00ffc07fe0006 0x0ff801ff80ffc000

def z491 : W := mkw 0x5ffebc015fedf550 0x0bffd7802bfdbeaa 0xffffec007ffff807 0xdffffd800fffff00

def z492 : W := mkw 0x0005620a24051000 0x0000ac414480a200 0x804fef1e763f3806 0xf009fde3cec7e700

def z493 : W := mkw 0x5ffbdadbe9a8e000 0x2bff7b5b7d351c00 0x7ffffffff9c0c007 0xefffffffff381800

def z494 : W := mkw 0x1f7bdbdbe0100a24 0x23ef7b7b7c020144 0xfffffffff0313e67 0xfffffffffe0627cc

def z495 : W := mkw 0x5bfea4001fedf550 0x0b7fd48003fdbeaa 0xffffe0000fffffff 0xdffffc0001ffffff

def z496 : W := mkw 0x04001c0002400500 0x00800380004800a0 0x00001c0000000780 0x20000380000000f0

def z497 : W := mkw 0x0004200004051000 0x000084000080a200 0x000fe00000013800 0x4001fc0000002700

def z498 : W := mkw 0x36401db4035a0780 0x06c803b6806b40f0 0x5c401ffc07ce0782 0x2b8803ff80f9c0f0

def z499 : W := mkw 0x5bfea0000dadf000 0x0b7fd40001b5be00 0x7ffce0000fcec003 0x0fff9c0001f9d800

def z500 : W := mkw 0x4112a00000047000 0x0822540000008e00 0x0003e00000003800 0x00007c0000000700

def z501 : W := mkw 0x5bffe24bedadf000 0x2b7ffc497db5be00 0xffffe003fffff807 0xdffffc007fffff00

def z502 : W := mkw 0x8005670e36171e65 0x1000ace1c6c2e3cc 0x004cef1e760e0662 0x20099de3cec1c0cc

def z503 : W := mkw 0x408421200dbdfaae 0x0810842401b7bf55 0x800000000ffffff8 0x1000000001ffffff

def z504 : W := mkw 0x5bfea0000dadf000 0x0b7fd40001b5be00 0xffb000000ffff801 0x1ff6000001ffff00

def z505 : W := mkw 0x093bc24be000682e 0x212778497c000d05 0x003fe003f001f878 0x4007fc007e003f0f

def z506 : W := mkw 0x8004250416171e65 0x100084a082c2e3cc 0x804fe000063f3e66 0xd009fc0000c7e7cc

def z507 : W := mkw 0x0113036280100aae 0x0022606c50020155 0x23b313e3800007fd 0xe476627c700000ff

def z508 : W := mkw 0x0c2c1c0156c18550 0x018583802ad830aa 0x5c0c1c03f7c007fa 0x2b8183807ef800ff

def z509 : W := mkw 0x1b7b824280000000 0x036f704850000000 0x7ffff3e380000007 0xeffffe7c70000000

def z510 : W := mkw 0x8197676ebe377eef 0x1032ecedd7c6efdd 0xa3cfeffe763f3e66 0xf479fdffcec7e7cc

def z511 : W := mkw 0x0005230204151a24 0x0000a4604082a344 0x804fe302063f3e66 0xf009fc6040c7e7cc

def z512 : W := mkw 0x36c019b009780380 0x06d80336012f0070 0xff8013e009f00785 0xbff0027c013e00f0

def z513 : W := mkw 0x1f7ffadbe4051000 0x23efff5b7c80a200 0xfffffffff63f3807 0xfffffffffec7e700

def z514 : W := mkw 0x0c2c1c0156c18550 0x018583802ad830aa 0x5c3c1c03f7c00003 0xeb8783807ef80000

def z515 : W := mkw 0x0d3bdadbe0000000 0x21a77b5b7c000000 0x003ffffff0000000 0x6007fffffe000000

def z516 : W := mkw 0x0d3b1a43c0000000 0x01a7634878000000 0x7fbf1fe3f0000007 0xeff7e3fc7e000000

def z517 : W := mkw 0x0001424be0000000 0x200028497c000000 0x00000003f0000000 0x000000007e000000

def z518 : W := mkw 0x5bffe20a2dadf000 0x0b7ffc4145b5be00 0xffffef1e7ffff807 0xfffffde3cfffff00

def z519 : W := mkw 0x36c41db41ffb87d0 0x06d883b683ff70fa 0xffc01ffc0fffc7ff 0xbff803ff81fff8ff

def z520 : W := mkw 0x8001620a20041825 0x10002c4144008304 0x0003e00000003800 0x00007c0000000700

def z521 : W := mkw 0x09bf0363dcb1eafe 0x0137e06c7b963d5f 0xa3bf13e3f831fffd 0xf477e27c7f063fff

def z522 : W := mkw 0x9353e3dea0161a25 0x326a7c7bd402c344 0x23c3e3fc003e3804 0x04787c7f8007c700

def z523 : W := mkw 0x093bc24be0000000 0x212778497c000000 0x23bff3e3f0000005 0xe477fe7c7e000000

def z524 : W := mkw 0x1f7fdadbf4818050 0x23effb5b7e90300a 0x7ffffffff001c07f 0xeffffffffe00380f

def z525 : W := mkw 0x77d2bdb40b7e7780 0x0efa57b6816fcef0 0xffc3fffc0ffe3f87 0xbff87fff81ffc7f0

def z526 : W := mkw 0x0000000000000000 0x0000000000000000 0x003000038001c078 0x400600007000380f

def z527 : W := mkw 0x0080012008306aae 0x0010002401060d55 0x0000000000303800 0x0000000000060700

def z528 : W := mkw 0x082c000154818050 0x010580002a90300a 0x000c000070000000 0x000180000e000000

def z529 : W := mkw 0x208005240b7a6fae 0x041000a4816f4df5 0x800000000ffffff8 0x1000000001ffffff

def z530 : W := mkw 0x0112000000000000 0x0022400000000000 0x23b3000000000005 0xc476600000000000

def z531 : W := mkw 0x1f7ad89960000000 0x23ef5b132c000000 0x7fffec1c70000007 0xcffffd838e000000

def z532 : W := mkw 0x1bfb836288306aae 0x037f706c51060d55 0xfffff3e38831ffff 0xfffffe7c71063fff

def z533 : W := mkw 0x0cac1d215ef1effe 0x019583a42bde3dff 0xdc3c1c03fff1fffb 0xfb8783807ffe3fff

def z534 : W := mkw 0xdbfee40c3faff441 0x1b7fdc8187f5fe88 0xffffec1c7ffff807 0xdffffd838fffff00

def z535 : W := mkw 0x0193036288306aae 0x0032606c51060d55 0xa3b303e00831f805 0xd476607c01063f00

def z536 : W := mkw 0x04041c0016410540 0x0080838002c820a8 0xdc0c1c027fc107e3 0xfb8183804ff820fc

def z537 : W := mkw 0x493ea0000485f000 0x0927d4000090be00 0x807fe000063ff806 0xd00ffc0000c7ff00

def z538 : W := mkw 0x5bfb836289b8eaae 0x0b7f706c51371d55 0xffb313e389f1fffd 0xfff6627c713e3fff

def z539 : W := mkw 0x0001030200100a24 0x0000206040020144 0x0000030200000660 0x20000060400000cc

def z540 : W := mkw 0x408424001fedf550 0x0810848003fdbeaa 0x800000000ffffff8 0x1000000001ffffff

def z541 : W := mkw 0x33d303f6893a6aae 0x067a607ed1274d55 0x23c303fc003e3804 0x0478607f8007c700

def z542 : W := mkw 0x7e6cbc9407cf9500 0x0fcd979280f9f2a0 0x5c4cec1c07ce0002 0x0b899d8380f9c000

def z543 : W := mkw 0x3ee8ddbd6b7a0780 0x27dd1bb7ad6f40f0 0xffccfffc7ffe0787 0xbff99fff8fffc0f0

def z544 : W := mkw 0x1a68800000000000 0x034d100000000000 0x5c4ce00000000002 0x0b899c0000000000

def z545 : W := mkw 0x0dbb1b63c8306aae 0x01b7636c79060d55 0xffbf1fe3f831ffff 0xfff7e3fc7f063fff

def z546 : W := mkw 0x36c01db40b7a0780 0x06d803b6816f40f0 0x23c01ffc003e0784 0x247803ff8007c0f0

def z547 : W := mkw 0x0193036288300280 0x0032606c51060050 0xa3b313e388300785 0xf476627c710600f0

def z548 : W := mkw 0x04801d200a700780 0x009003a4014e00f0 0xff801fe00ff00787 0xbff003fc01fe00f0

def z549 : W := mkw 0x8004640c36071441 0x10008c8186c0e288 0x804cec1e760f0662 0xf0099d83cec1e0cc

def z550 : W := mkw 0x0000010000100200 0x0000002000020040 0x8000030000300604 0xb0000060000600c0

def z551 : W := mkw 0x608425240ffff780 0x0c1084a481fffef0 0x800000000fffff80 0x1000000001fffff0

def z552 : W := mkw 0x16c019b008300280 0x02d8033601060050 0xffc01ffc08300787 0xbff803ff810600f0

def z553 : W := mkw 0x3640189001480100 0x06c8031200290020 0x5c00000001c00000 0x0b80000000380000

def z554 : W := mkw 0x093fc24bf4818050 0x2127f8497e90300a 0x003fe003f001c078 0x4007fc007e00380f

def z555 : W := mkw 0x16c01c000b680500 0x02d80380016d00a0 0xffc01c000ffe0787 0xbff8038001ffc0f0

def z556 : W := mkw 0x76c43db40ffff780 0x0ed887b681fffef0 0xffc01ffc0fffff87 0xbff803ff81fffff0

def z557 : W := mkw 0x24001db402520780 0x048003b6804a40f0 0xdc001ffc0fc00783 0xbb8003ff81f800f0

def z558 : W := mkw 0x040018d1c0000000 0x2080031a38000000 0x000010e180000000 0x0000021c30000000

def z559 : W := mkw 0x419620000dadf000 0x0832c40001b5be00 0xa3b300000ffff805 0xd476600001ffff00

def z560 : W := mkw 0x0c2d1f0356d18f74 0x0185a3e06ada31ee 0xdc3f1f03fff1ffff 0xfb87e3e07ffe3fff

def z561 : W := mkw 0x04001c0152400550 0x008003802a4800aa 0x80301c03f801c7f9 0xf00603807f0038ff

def z562 : W := mkw 0x0005460a36010440 0x0000a8c146c02088 0x804fef1e76010666 0xf009fde3cec020cc

def z563 : W := mkw 0x8c2d7f0f76171e65 0x1185afe1eec2e3cc 0xdc7fff1ff63f3e67 0xfb8fffe3fec7e7cc

def z564 : W := mkw 0x1e6c1c9156c18550 0x03cd83922ad830aa 0xfffc1fffffc1c7ff 0xffff83fffff838ff

def z565 : W := mkw 0x011302428000682e 0x0022604850000d05 0x23b313e38001f87d 0xe476627c70003f0f

def z566 : W := mkw 0x92c5670e3f3f1e65 0x1258ace1c7e7e3cc 0xffcfef1e7fff3e67 0xfff9fde3cfffe7cc

def z567 : W := mkw 0x1240000001080000 0x0248000000210000 0x5c40000007ce0002 0x0b88000000f9c000

def z568 : W := mkw 0x0c2d1f63d6d18ffe 0x0185a3ec7ada31ff 0xdc3c1fe3ffc1c7fb 0xfb8783fc7ff838ff

def z569 : W := mkw 0x1ffbdafbe820608a 0x23ff7b5f7d040c11 0x7ffffffff800c19f 0xefffffffff001833

def z570 : W := mkw 0x1e6cdc9976c18550 0x23cd9b932ed830aa 0x5c4cec1c77c00002 0x0b899d838ef80000

def z571 : W := mkw 0x0004250406171600 0x000084a080c2e2c0 0x804fef1c063f3e06 0xf009fde380c7e7c0

def z572 : W := mkw 0x8001420a30000865 0x100028414600010c 0x0000000270000060 0x000000004e00000c

def z573 : W := mkw 0xb7d77ffebf7f7fef 0x16faefffd7efeffd 0xffffffffffffffff 0xffffffffffffffff

def z574 : W := mkw 0x5a6ca000058d9000 0x0b4d940000b1b200 0xdc4fe00007ff3806 0xdb89fc0000ffe700

def z575 : W := mkw 0x8005670e36171e65 0x1000ace1c6c2e3cc 0x000fef1e70013e60 0x6001fde3ce0027cc

def z576 : W := mkw 0xb2c163be293e1aa5 0x16582c77c527c354 0x23c3e3fc003e3804 0x04787c7f8007c700

def z577 : W := mkw 0x082c000004818000 0x0105800000903000 0x5c0c000007c00002 0x0b81800000f80000

def z578 : W := mkw 0x20000404034a0500 0x04000080806940a0 0x0000000007ce0000 0x0000000000f9c000

def z579 : W := mkw 0x082c000004818000 0x0105800000903000 0xdc3c10038fc1c7fb 0xfb87820071f838ff

def z580 : W := mkw 0x8000440c32020441 0x1000088186404088 0x00000c1c70000000 0x000001838e000000

def z581 : W := mkw 0x5ffffedbffedf550 0x2bffffdb7ffdbeaa 0xffffffffffffffff 0xffffffffffffffff

def z582 : W := mkw 0x37d3dffeab7a0780 0x26fa7bffd56f40f0 0xffc3fffc0ffe0787 0xbff87fff81ffc0f0

def z583 : W := mkw 0x219307668b7a6fae 0x043260ecd16f4df5 0xa3b313e38ffffffd 0xf476627c71ffffff

def z584 : W := mkw 0x0dba1861c8e0e19a 0x01b7430c391c1c33 0x7fb010e189c0c199 0x0ff6021c31381833

def z585 : W := mkw 0x0001030200100a24 0x0000206040020144 0x803313038831fffd 0xf006626071063fff

def z586 : W := mkw 0x0c2c1c0156c18550 0x018583802ad830aa 0x003c1c03f001c7f8 0x600783807e0038ff

def z587 : W := mkw 0x0113c24aa0000000 0x2022784954000000 0x0003e00000000000 0x00007c0000000000

def z588 : W := mkw 0x1f7a980140000000 0x03ef530028000000 0x7ffffc03f0000007 0xefffff807e000000

def z589 : W := mkw 0x0c2d5e0b76c18550 0x0185abc16ed830aa 0xdc7fff1fffc1c7ff 0xfb8fffe3fff838ff

def z590 : W := mkw 0x0004040016c18550 0x0000808002d830aa 0x800c0c027fc1c7fa 0xf00181804ff838ff

def z591 : W := mkw 0x0828c00960000000 0x210518012c000000 0x000ce00070000000 0x00019c000e000000

def z592 : W := mkw 0x0004200004051000 0x000084000080a200 0x004ce000060e0002 0x00099c0000c1c000

def z593 : W := mkw 0x32c005b40b7a0780 0x065800b6816f40f0 0xa3c003fc0ffe0784 0x1478007f81ffc0f0

def z594 : W := mkw 0x0001420a20000000 0x0000284144000000 0x0043e31c00000004 0x00087c6380000000

def z595 : W := mkw 0x8005630e34171a65 0x1000ac61c682e34c 0x004fe31e703f3864 0x4009fc63ce07e70c

def z596 : W := mkw 0x32c000b009280080 0x0658001601250010 0x238000e000000000 0x0470001c00000000

def z597 : W := mkw 0x0000050402120600 0x000000a0804240c0 0x00000f1c00000600 0x200001e3800000c0

def z598 : W := mkw 0x04015edbf2400550 0x20802bdb7e4800aa 0x00001ffff00007f8 0x200003fffe0000ff

def z599 : W := mkw 0x12c0000009280000 0x0258000001250000 0x23c00000003e0004 0x047800000007c000

def z600 : W := mkw 0x011302428000682e 0x0022604850000d05 0x803310038801fff9 0xf006620071003fff

def z601 : W := mkw 0x0193036288306aae 0x0032606c51060d55 0xa38303e200313e64 0xf470607c400627cc

def z602 : W := mkw 0xb6c43db41f7f1fe5 0x16d887b683efe3fc 0xffc01ffc0fff3fe7 0xbff803ff81ffe7fc

def z603 : W := mkw 0x0c28180140000000 0x0185030028000000 0x5c30100180000001 0x0b86020030000000

def z604 : W := mkw 0x5e6cbc0157cd9550 0x0bcd97802af9b2aa 0x5c4cec0077ce0002 0x0b899d800ef9c000

def z605 : W := mkw 0x3ffa9df5cb7a0780 0x27ff53beb96f40f0 0xfff01ffd8ffe0787 0xbffe03ffb1ffc0f0

def z606 : W := mkw 0x24801db40a720780 0x049003b6814e40f0 0xa3801ffc08300785 0xb47003ff810600f0

def z607 : W := mkw 0x1f7bdadbe0000000 0x23ef7b5b7c000000 0x7ff3f3fd80000005 0x0ffe7e7fb0000000

def z608 : W := mkw 0x5bfea0015dadf050 0x0b7fd4002bb5be0a 0xffffe003fffff87f 0xdffffc007fffff0f

def z609 : W := mkw 0x0193024288206000 0x0032604851040c00 0xa3b313e38831f805 0xf476627c71063f00

def z610 : W := mkw 0x84057f0e36571f65 0x1080afe1c6cae3ec 0xdc4fff1e7fff3fe7 0xfb89ffe3cfffe7fc

def z611 : W := mkw 0x0080012008300280 0x0010002401060050 0xa3b013e38831c7fd 0xf476027c710638ff

def z612 : W := mkw 0x019707629e316eee 0x0032e0ec53c62ddd 0xa3bf1fe3fe31ffff 0xf477e3fc7fc63fff

def z613 : W := mkw 0x5bfea0000dadf000 0x0b7fd40001b5be00 0x7fbfe00009c1f801 0x4ff7fc0001383f00

def z614 : W := mkw 0xb6457f9e375f1f65 0x16c8aff3c6ebe3ec 0xdc4fef1e77ff3e66 0xfb89fde3ceffe7cc

def z615 : W := mkw 0x0000000000c08110 0x0000000000181022 0x0000000009c0c198 0x0000000001381833

def z616 : W := mkw 0x0dbe1c015ee1e550 0x01b7c3802bdc3caa 0xffbf1c03fff1ffff 0xfff7e3807ffe3fff

def z617 : W := mkw 0x49bfa3628cb5faae 0x0937f46c5196bf55 0xa3bff3e38831fffd 0xf477fe7c71063fff

def z618 : W := mkw 0x1352800000000000 0x026a500000000000 0x23c3e00000000004 0x04787c0000000000

def z619 : W := mkw 0x0400180000400100 0x0080030000080020 0x5c00100009c00181 0x0b80020001380030

def z620 : W := mkw 0x8004250416d79f75 0x100084a082daf3ee 0x800000000ffffff8 0x1000000001ffffff

def z621 : W := mkw 0x0001030200100a24 0x0000206040020144 0x0003030000303804 0x0000606000060700

def z622 : W := mkw 0x8c2c7c0d76c79551 0x11858f81aed8f2aa 0xdc7cfc1fffcfc7fb 0xfb8f9f83fff9f8ff

def z623 : W := mkw 0x0081036288300aae 0x0010206c51060155 0xa38013e3883007fd 0xb470027c710600ff

def z624 : W := mkw 0x8001470e32120e65 0x100028e1c64241cc 0x80400f1e763e0666 0xb00801e3cec7c0cc

def z625 : W := mkw 0x1f7a98d1c0000000 0x23ef531a38000000 0x7ff01ffd80000007 0xaffe03ffb0000000

def z626 : W := mkw 0x0004040016010440 0x0000808002c02088 0x803c1c03fe01c7fb 0xf00783807fc038ff

def z627 : W := mkw 0xdfffff0f7fffff75 0x1bffffe1efffffee 0xffffff1fffffffff 0xffffffe3ffffffff

def z628 : W := mkw 0x5ffa980149e8e110 0x0bff5300293d1c22 0x7fb0100189c0c199 0x0ff6020031381833

def z629 : W := mkw 0x1ffa98f1c820608a 0x23ff531e39040c11 0x7fb010e18800c199 0x0ff6021c31001833

def z630 : W := mkw 0x0dbe1c61dee1e5da 0x01b7c38c3bdc3cbb 0xffbc1ce3ffc1c7fb 0xfff7839c7ff838ff

def z631 : W := mkw 0x0c2c1c0156c18550 0x018583802ad830aa 0xdc0c1c007fc00783 0xbb8183800ff800f0

def z632 : W := mkw 0x8117624ab405786f 0x1022ec495680af0d 0x003fe003f001f878 0x4007fc007e003f0f

def z633 : W := mkw 0x0c295adbe0000000 0x21852b5b7c000000 0x5c3c1ffff0000003 0xeb8783fffe000000

def z634 : W := mkw 0x019200608820608a 0x0032400c11040c11 0xa3b010e38801c7f9 0xf476021c710038ff

def z635 : W := mkw 0x8005660a36051c65 0x1000acc146c0a38c 0x800fec0276013e62 0xf001fd804ec027cc

def z636 : W := mkw 0x1f7e9cd1d6c18550 0x23efd39a3ad830aa 0xffbc1ce3ffc1c7fb 0xfff7839c7ff838ff

def z637 : W := mkw 0x53d3e2daa92c7000 0x2a7a7c5b55258e00 0x23c3e3fc003e3804 0x04787c7f8007c700

def z638 : W := mkw 0x0193036288306aae 0x0032606c51060d55 0x23b013e38800c7f9 0x2476027c710018ff

def z639 : W := mkw 0x8c2d5f0f76d38f75 0x1185abe1eeda71ee 0xdc3c1f1fffc1c7fb 0xfb8783e3fff838ff

def z640 : W := mkw 0x011302428000682e 0x0022604850000d05 0x0003000000003800 0x0000600000000700

def z641 : W := mkw 0x24001c9402420500 0x04800392804840a0 0x00000c1c00000000 0x0000018380000000

def z642 : W := mkw 0x0400180140000000 0x0080030028000000 0x00001c03f0000000 0x200003807e000000

def z643 : W := mkw 0x0080000008200000 0x0010000001040000 0xa380000008300005 0x9470000001060000

def z644 : W := mkw 0x1f7bdedbf2400550 0x23ef7bdb7e4800aa 0x7ffffffff00007ff 0xeffffffffe0000ff

def z645 : W := mkw 0x7bfea5240ffff780 0x0f7fd4a481fffef0 0xffffe0000fffff87 0xdffffc0001fffff0

def z646 : W := mkw 0x8005620a34051865 0x1000ac414680a30c 0x804fe002763f3866 0xd009fc004ec7e70c

def z647 : W := mkw 0x0d3f1e43d6c18550 0x01a7e3c87ad830aa 0xffbf1fe3ffc1c7ff 0xfff7e3fc7ff838ff

def z648 : W := mkw 0x0000000000000000 0x0000000000000000 0x003010018800c199 0x0006020031001833

def z649 : W := mkw 0x5e6cbc0157cd9550 0x0bcd97802af9b2aa 0xdc7cfc03ffcfc7fb 0xfb8f9f807ff9f8ff

def z650 : W := mkw 0x082c000004818000 0x0105800000903000 0x003c00000001c000 0x4007800000003800

def z651 : W := mkw 0x082c040156c18550 0x010580802ad830aa 0x803c0003ffc1c7f8 0x500780007ff838ff

def z652 : W := mkw 0x0001036280100aae 0x0000206c50020155 0x000003e000000000 0x0000007c00000000

def z653 : W := mkw 0x5b7ea000058df000 0x0b6fd40000b1be00 0x5c7fe00007cff802 0x4b8ffc0000f9ff00

def z654 : W := mkw 0x0400180000000000 0x0080030000000000 0x5c001c0000000003 0xab80038000000000

def z655 : W := mkw 0x8001470e32120e65 0x100028e1c64241cc 0x004fef1e70000666 0xe009fde3ce0000cc

def z656 : W := mkw 0x04001c0152400550 0x008003802a4800aa 0xdc001c03ffc007fb 0xbb8003807ff800ff

def z657 : W := mkw 0x000142daa0000000 0x2000285b54000000 0x000003fc00000000 0x0000007f80000000

def z658 : W := mkw 0x3ee81db54bfa8790 0x07dd03b6a97f50f2 0xfff01ffd8ffec79f 0xbffe03ffb1ffd8f3

def z659 : W := mkw 0x1b7ea00004051000 0x036fd4000080a200 0xffffe000063f3807 0xdffffc0000c7e700

def z660 : W := mkw 0x0192000008206000 0x0032400001040c00 0x23b000000800c001 0x0476000001001800

def z661 : W := mkw 0x36c01db40b7a0780 0x06d803b6816f40f0 0xff8010e00ffe0781 0x1ff0021c01ffc0f0

def z662 : W := mkw 0xda6ce40c378f9441 0x1b4d9c8186f1f288 0x5c4cec1c77ce0002 0x0b899d838ef9c000

def z663 : W := mkw 0x400420000485f000 0x080084000090be00 0x000000000001f800 0x0000000000003f00

def z664 : W := mkw 0x082c040016c18550 0x0105808002d830aa 0xdc3c00000fc1c7fb 0xdb87800001f838ff

def z665 : W := mkw 0x1f7bdfdfe2120600 0x23ef7bfbfc4240c0 0xfffffffff63e0607 0xfffffffffec7c0c0

def z666 : W := mkw 0x04001d0402520700 0x008003a0804a40e0 0xdc401f1c0ffe0787 0xbb8803e381ffc0f0

def z667 : W := mkw 0x0c2c1c0156c18550 0x018583802ad830aa 0xdc0c0c007fc1c7fa 0x1b8181800ff838ff

def z668 : W := mkw 0xc93fe70e3697fe65 0x1927fce1c6d2ffcc 0x807fef1e763ffe66 0xf00ffde3cec7ffcc

def z669 : W := mkw 0x09be00000ca1e000 0x0137c00001943c00 0xffbf00000ff1f807 0xdff7e00001fe3f00

def z670 : W := mkw 0x882d620b74859875 0x1105ac416e90b30e 0x003fe003f001f878 0x4007fc007e003f0f

def z671 : W := mkw 0x5240a000010c1000 0x0a48140000218200 0x0040e000000e0000 0x00081c000001c000

def z672 : W := mkw 0x0000000000000000 0x0000000000000000 0x000c0c0270000002 0xe00181804e000000

def z673 : W := mkw 0x7bfea1b40dbff280 0x0f7fd43681b7fe50 0xffffe3fc0ffff807 0xdffffc7f81ffff00

def z674 : W := mkw 0x53d3a362893c7aae 0x0a7a746c51278f55 0xa3f3f3e3883ffffd 0xf47e7e7c7107ffff

def z675 : W := mkw 0x5bffa3628dbdfaae 0x0b7ff46c51b7bf55 0xffffe3e00ffff807 0xdffffc7c01ffff00

def z676 : W := mkw 0x3eec1db55ffb87d0 0x07dd83b6abff70fa 0xffcc1ffc7ffe0787 0xbff983ff8fffc0f0

def z677 : W := mkw 0x40042000058d9000 0x0800840000b1b200 0x0000000007ce0000 0x0000000000f9c000

def z678 : W := mkw 0x0c2c1c0156c18550 0x018583802ad830aa 0xdc3c0c007fc1c003 0xdb8781800ff83800

def z679 : W := mkw 0x8001430e20120a25 0x10002861c4024144 0x0000031c00000000 0x0000006380000000

def z680 : W := mkw 0x419723628dbdfaae 0x0832e46c51b7bf55 0xa3b313e38ffffffd 0xf476627c71ffffff

def z681 : W := mkw 0x0c281c0152400550 0x018503802a4800aa 0x5c3c1c03f00007fb 0xeb8783807e0000ff

def z682 : W := mkw 0x0080012008300280 0x0010002401060050 0x8000000008300780 0x10000000010600f0

def z683 : W := mkw 0x082c040156818450 0x010580802ad0308a 0x803c0c03f601c67a 0xf00781807ec038cf

def z684 : W := mkw 0x1eec1c015fe98550 0x03dd83802bfd30aa 0xfffc1c03ffffc7ff 0xffff83807ffff8ff

def z685 : W := mkw 0x0004040016010440 0x0000808002c02088 0x8000000006010660 0x1000000000c020cc

def z686 : W := mkw 0x3ffa9db40b7a0780 0x07ff53b6816f40f0 0xfffffffc0ffe0787 0xffffffff81ffc0f0

def z687 : W := mkw 0x8001470e32120e65 0x100028e1c64241cc 0x80030f1e70313e64 0xf00061e3ce0627cc

def z688 : W := mkw 0x0192012008306aae 0x0032402401060d55 0xa3b300000831fffd 0xd476600001063fff

def z689 : W := mkw 0x8c2d7e0b76c59d75 0x1185afc16ed8b3ae 0xdc3ffc03ffc1fffb 0xfb87ff807ff83fff

def z690 : W := mkw 0x9f7ffadbf4051865 0x33efff5b7e80a30c 0x7ffffffff0013867 0xeffffffffe00270c

def z691 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z692 : W := mkw 0x37d21df48b7a678a 0x06fa43be916f4cf1 0xfff01ffd8ffec79f 0xbffe03ffb1ffd8f3

def z693 : W := mkw 0x1b7bc24be0000000 0x236f78497c000000 0x7fffe003f0000007 0xcffffc007e000000

def z694 : W := mkw 0x0000000000000000 0x0000000000000000 0x8000000200010660 0xf0000000400020cc

def z695 : W := mkw 0x9357e7deb6171e65 0x326afcfbd6c2e3cc 0xa3cfeffe763f3e66 0xf479fdffcec7e7cc

def z696 : W := mkw 0x5ffeb8014dedf110 0x0bffd70029bdbe22 0xfffff0018ffff99f 0xdffffe0031ffff33

def z697 : W := mkw 0x36c11fb60b7a0fa4 0x06d823f6c16f41f4 0xffc31ffe0fff3fe7 0xfff863ffc1ffe7fc

def z698 : W := mkw 0x9f7ffedff6071441 0x33efffdbfec0e288 0x7ffffffff60e0007 0xeffffffffec1c000

def z699 : W := mkw 0x8117674eb6171e65 0x1022ece9d6c2e3cc 0xa3fffffff63f3e67 0xf47ffffffec7e7cc

def z700 : W := mkw 0x019307668a326eae 0x003260ecd1464dd5 0xa3f31fff8e3fffff 0xf47e63fff1c7ffff

def z701 : W := mkw 0x208005240b7a0780 0x041000a4816f40f0 0xa38013e00ffe0785 0xb470027c01ffc0f0

def z702 : W := mkw 0x0000000000000000 0x0000000000000000 0x80400000063e0006 0x9008000000c7c000

def z703 : W := mkw 0x0004040016c18550 0x0000808002d830aa 0x803010038fc1c7f9 0xf006020071f838ff

def z704 : W := mkw 0x0dbb1b63c8f0ebbe 0x01b7636c791e1d77 0xffb313e389f1fffd 0xfff6627c713e3fff

def z705 : W := mkw 0x3e68dc9d634a0500 0x27cd1b93ac6940a0 0x5c4cec1c77ce0002 0x0b899d838ef9c000

def z706 : W := mkw 0x8005670e36171e65 0x1000ace1c6c2e3cc 0x80000f1e763f3e60 0x300001e3cec7e7cc

def z707 : W := mkw 0x5bfea0000dadf000 0x0b7fd40001b5be00 0xfffff3e00ffff807 0xfffffe7c01ffff00

def z708 : W := mkw 0x093bc24be0000000 0x212778497c000000 0x23fffffff0000007 0xe47ffffffe000000

def z709 : W := mkw 0x0193036288306aae 0x0032606c51060d55 0xa3b313e18831fffd 0x1476627c31063fff

def z710 : W := mkw 0xa08425241f3f1ee5 0x141084a483e7e3dc 0x80000000063f3e60 0x1000000000c7e7cc

def z711 : W := mkw 0x44857adbedadf000 0x2890af5b7db5be00 0x80001ffffffff800 0x300003ffffffff00

def z712 : W := mkw 0x0113034280100a24 0x0022606850020144 0xa3b313e38831fffd 0xf476627c71063fff

def z713 : W := mkw 0x082c040156c18550 0x010580802ad830aa 0xdc3c0003ffc1c7fb 0xdb8780007ff838ff

def z714 : W := mkw 0x36c018b009680180 0x06d80316012d0030 0xffc01ffc0ffe0187 0xbff803ff81ffc030

def z715 : W := mkw 0x04801d240a720780 0x009003a4814e40f0 0xffc01ffc0ffe0787 0xbff803ff81ffc0f0

def z716 : W := mkw 0x36c01db40b7a0fa4 0x06d803b6816f41f4 0xffc01ffc0fff3fe7 0xbff803ff81ffe7fc

def z717 : W := mkw 0x57d2bc015b6c7550 0x0afa57802b6d8eaa 0x23c3fc03f03e3ffc 0x24787f807e07c7ff

def z718 : W := mkw 0x0c2c3c0156c59550 0x018587802ad8b2aa 0xdc3c1c03fffffffb 0xfb8783807fffffff

def z719 : W := mkw 0x1f7bdadbe0000000 0x23ef7b5b7c000000 0x7fcffffc70000007 0xaff9ffff8e000000

def z720 : W := mkw 0x8196646cbe2774cb 0x1032cc8d97c4ee99 0x23fcfcfdfe0ec19b 0x047f9f9fbfc1d833

def z721 : W := mkw 0x0192016088306aae 0x0032402c11060d55 0xa3b310e18831fffd 0xd476621c31063fff

def z722 : W := mkw 0x1f7bdadbe0000000 0x23ef7b5b7c000000 0x7fffeffff0000006 0x4ffffdfffe000000

def z723 : W := mkw 0x5bfea0000dadf000 0x0b7fd40001b5be00 0xfffff0000fffff87 0xfffffe0001fffff0

def z724 : W := mkw 0x5bfea0015dadf050 0x0b7fd4002bb5be0a 0xffffe0007ffff807 0xdffffc000fffff00

def z725 : W := mkw 0x1ee8d9b968306aae 0x23dd1b372d060d55 0xdc4cec1c7831fffa 0x1b899d838f063fff

def z726 : W := mkw 0x8005670e36171e65 0x1000ace1c6c2e3cc 0x004fef1e763e3806 0xe009fde3cec7c700

def z727 : W := mkw 0x37531ed6834a6d2e 0x06ea63dad0694da5 0x5c730c1f87cff87a 0x4b8e6183f0f9ff0f

def z728 : W := mkw 0x36c01db55b7a07d0 0x06d803b6ab6f40fa 0xfff01fffffffc7ff 0xfffe03fffffff8ff

def z729 : W := mkw 0x1f7a989140000000 0x03ef531228000000 0x7ffffffff0000007 0xeffffffffe000000

def z730 : W := mkw 0x1f7bdadbe0000000 0x23ef7b5b7c000000 0x7fbffffff0000001 0x6ff7fffffe000000

def z731 : W := mkw 0x36c01db40b7a6780 0x06d803b6816f4cf0 0xffc01ffc0fffff87 0xbff803ff81fffff0

def z732 : W := mkw 0x1357c6dab6c18550 0x226af8db56d830aa 0xa3c3e3fc0fc1c7fc 0x14787c7f81f838ff

def z733 : W := mkw 0x8c297b0f60d69b35 0x11852f61ec1ad366 0x5c73f31d89fef99d 0x0b8e7e63b13fdf33

def z734 : W := mkw 0xa4015fbe22520fa5 0x14802bf7c44a41f4 0x00001ffc00000780 0x200003ff800000f0

def z735 : W := mkw 0x0c2c1c0156c18550 0x018583802ad830aa 0x5c3c1c03f9c1c7f9 0x6b8783807f3838ff

def z736 : W := mkw 0x5bfea0015dadf050 0x0b7fd4002bb5be0a 0xfffff003ffffffff 0xfffffe007fffffff

def z737 : W := mkw 0x808425241e377eef 0x101084a483c6efdd 0x80000000063f3e60 0x1000000000c7e7cc

def z738 : W := mkw 0x53d2a000092c7000 0x0a7a540001258e00 0xfff3e0000ffff807 0xdffe7c0001ffff00

def z739 : W := mkw 0x0c281c0152c08550 0x018503802a5810aa 0xdc301c03ffc0c7fb 0xbb8603807ff818ff

def z740 : W := mkw 0x0dbf1f63def1effe 0x01b7e3ec7bde3dff 0x7f8f0fe077f03806 0x0ff1e1fc0efe0700

def z741 : W := mkw 0x1b7bc24aa0000000 0x036f784954000000 0x7ffffffff0000007 0xeffffffffe000000

def z742 : W := mkw 0x8001670e32161e65 0x10002ce1c642c3cc 0x004fef1e703e3e66 0xe009fde3ce07c7cc

def z743 : W := mkw 0xbe6c7c9d77cf9551 0x17cd8f93aef9f2aa 0x5c4cec1c77ce0002 0x0b899d838ef9c000

def z744 : W := mkw 0xdbfbc70e3bbaee65 0x1b7f78e1c7775dcc 0x7fb00f1e79c0c661 0x2ff601e3cf3818cc

def z745 : W := mkw 0x5bfea0000dadf000 0x0b7fd40001b5be00 0xfffff0038ffff807 0xfffffe0071ffff00

def z746 : W := mkw 0x84015f0f72520f75 0x10802be1ee4a41ee 0x00000f1e70000660 0x200001e3ce0000cc

def z747 : W := mkw 0x12442000050d1000 0x0248840000a1a200 0xdc4fe00007ff3806 0xdb89fc0000ffe700

def z748 : W := mkw 0x29bbc76feb7a0780 0x253778edfd6f40f0 0x803fe003fffe0780 0x5007fc007fffc0f0

def z749 : W := mkw 0x0193036288306aae 0x0032606c51060d55 0xa3b013e38831fff9 0x3476027c71063fff

def z750 : W := mkw 0x0193036288306aae 0x0032606c51060d55 0x23b313e38801fff9 0x6476627c71003fff

def z751 : W := mkw 0x082c040016818440 0x0105808002d03088 0xdc3c1c03ffc1c7fb 0xfb8783807ff838ff

def z752 : W := mkw 0x7ffa98f1c9e8e180 0x2fff531e393d1c30 0x7fb010e189c0c181 0x0ff6021c31381830

def z753 : W := mkw 0x0193036288306aae 0x0032606c51060d55 0xffb313e38ff1ffff 0xfff6627c71fe3fff

def z754 : W := mkw 0x0192016088306aae 0x0032402c11060d55 0xa3b010e38831fff9 0xf476021c71063fff

def z755 : W := mkw 0x5bfea0000dadf000 0x0b7fd40001b5be00 0xfffff0018ffff99f 0xdffffe0031ffff33

def z756 : W := mkw 0x5bfea0000dadf000 0x0b7fd40001b5be00 0xfff3e0000ffff805 0x1ffe7c0001ffff00

def z757 : W := mkw 0x5bfea0000dadf000 0x0b7fd40001b5be00 0xdc7fe0000ffff802 0x5b8ffc0001ffff00

def z758 : W := mkw 0x8001630e20161a25 0x10002c61c402c344 0x004fef1c703e3806 0x0009fde38e07c700

def z759 : W := mkw 0x84015f0e32520f65 0x10802be1c64a41ec 0x00001f1e700007e0 0x200003e3ce0000fc

def z760 : W := mkw 0x0c2c1c0156c18550 0x018583802ad830aa 0xdc7ffc03ffc1c7ff 0xfb8fff807ff838ff

def z761 : W := mkw 0x36c01db40b7a0fae 0x06d803b6816f41f5 0xffc01ffc0ffe07ff 0xbff803ff81ffc0ff

def z762 : W := mkw 0x8005670e36571f65 0x1000ace1c6cae3ec 0x804fef1e7fff3fe6 0xf009fde3cfffe7fc

def z763 : W := mkw 0x0193436aa8306aae 0x0032686d55060d55 0xa3b31ffff831fffd 0xf47663ffff063fff

def z764 : W := mkw 0x893f624bf485f87f 0x1127ec497e90bf0f 0x003fe003f001f878 0x4007fc007e003f0f

def z765 : W := mkw 0x0004250416171640 0x000084a082c2e2c8 0x804fef1e763f3e66 0xf009fde3cec7e7cc

def z766 : W := mkw 0xa005672e36571fe5 0x1400ace5c6cae3fc 0x804fef1e763f3fe6 0xf009fde3cec7e7fc

def z767 : W := mkw 0x8005670e36d79f75 0x1000ace1c6daf3ee 0x807fff1fffffffff 0xf00fffe3ffffffff

def z768 : W := mkw 0x8005630e24171a25 0x1000ac61c482e344 0x804fef1e763f3806 0xf009fde3cec7e700

def z769 : W := mkw 0x3aec01b55dbb82d0 0x075d8036abb7705a 0x23fc03fff03fc07c 0x447f807ffe07f80f

def z770 : W := mkw 0x0192016088306aae 0x0032402c11060d55 0xa3b013e18831fffd 0xb476027c31063fff

def z771 : W := mkw 0x1f7bdadbe0000000 0x23ef7b5b7c000000 0xfffffffff8000787 0xffffffffff0000f0

def z772 : W := mkw 0x36c01db40b7a0780 0x06d803b6816f40f0 0xffc01fff8ffe07ff 0xbff803fff1ffc0ff

def z773 : W := mkw 0x0c28180140c08110 0x0185030028181022 0xdc3c1c03f9c1c7fb 0xfb8783807f3838ff

def z774 : W := mkw 0xb3d363fea93e7aaf 0x167a6c7fd527cf55 0x23c3e3fc003e3804 0x04787c7f8007c700

def z775 : W := mkw 0x8005670e36171e65 0x1000ace1c6c2e3cc 0x004fef1e763f3866 0x4009fde3cec7e70c

def z776 : W := mkw 0x808425241e371ee5 0x101084a483c6e3dc 0x800000000e3f3fe0 0x1000000001c7e7fc

def z777 : W := mkw 0xa4015f9e32520f65 0x14802bf3c64a41ec 0x00000f1e70000660 0x200001e3ce0000cc

def z778 : W := mkw 0x12c005240b3a0680 0x025800a4816740d0 0xffc01ffc0ffe0787 0xbff803ff81ffc0f0

def z779 : W := mkw 0x8005670e36979e65 0x1000ace1c6d2f3cc 0x804fef1e7ffffe66 0xf009fde3cfffffcc

def z780 : W := mkw 0x0080012008306aae 0x0010002401060d55 0xa3b013e38831fffd 0xf476027c71063fff

def z781 : W := mkw 0x8005670e36171e65 0x1000ace1c6c2e3cc 0xdc4fef1e7fff3e67 0xfb89fde3cfffe7cc

def z782 : W := mkw 0x9f7ebdd5d6171e65 0x33efd7babac2e3cc 0xffb010e1863f3e61 0x1ff6021c30c7e7cc

def z783 : W := mkw 0x8004640c36071441 0x10008c8186c0e288 0x804fec1e763f3e66 0xf009fd83cec7e7cc

def z784 : W := mkw 0x082c200004859000 0x010584000090b200 0xdc4fe00007ff3806 0xdb89fc0000ffe700

def z785 : W := mkw 0x5a6da362859d9aae 0x0b4db46c50b3b355 0x5c4cf3e387ce07fa 0x2b899e7c70f9c0ff

def z786 : W := mkw 0x5f7bdadbe1888000 0x2bef7b5b7c311000 0x7ffffffff1c00007 0xeffffffffe380000

def z787 : W := mkw 0x0193036288306aae 0x0032606c51060d55 0xa3fff3e38831ffff 0xf47ffe7c71063fff

def z788 : W := mkw 0xb6c57aba3d6d19e5 0x16d8af5747ada33c 0x7f8ff0e279c139e1 0x4ff1fe1c4f38273c

def z789 : W := mkw 0x0c281c0152c08550 0x018503802a5810aa 0x5c3c1c03f9c0c7fb 0xeb8783807f3818ff

def z790 : W := mkw 0x493fe24aa485f000 0x2927fc495490be00 0x003fe0000001f800 0x4007fc0000003f00

def z791 : W := mkw 0x5ffa98d1c9e8e110 0x2bff531a393d1c22 0x7fb010e189c0c199 0x0ff6021c31381833

def z792 : W := mkw 0x16c01d940b3a0600 0x02d803b2816740c0 0xffc01ffc0ffe0607 0xbff803ff81ffc0c0

def z793 : W := mkw 0x0c2c1c0156c18550 0x018583802ad830aa 0xdc7c1c03ffffc7ff 0xfb8f83807ffff8ff

def z794 : W := mkw 0x0192012008306280 0x0032402401060c50 0xa3b313e38831fffd 0xf476627c71063fff

def z795 : W := mkw 0x5bfea0001dadf050 0x0b7fd40003b5be0a 0xffffe0000ffff87f 0xdffffc0001ffff0f

def z796 : W := mkw 0x0113036280106aae 0x0022606c50020d55 0x23b313e38001fffd 0xe476627c70003fff

def z797 : W := mkw 0x8004650c36171e65 0x10008ca186c2e3cc 0x804fec1c763f3e66 0xd009fd838ec7e7cc

def z798 : W := mkw 0x0c2c1c0156c18550 0x018583802ad830aa 0xdc3f1c03fff1ffff 0xfb87e3807ffe3fff

def z799 : W := mkw 0x5bfea0000dadf000 0x0b7fd40001b5be00 0xffbfe0000ffff801 0x5ff7fc0001ffff00

def z800 : W := mkw 0x5f7bdadbe080e000 0x2bef7b5b7c101c00 0x7ffffffff000c007 0xeffffffffe001800

def z801 : W := mkw 0x16401d9402520700 0x02c803b2804a40e0 0xffc01ffc0ffe0787 0xbff803ff81ffc0f0

def z802 : W := mkw 0x1f7bdadbe000682e 0x23ef7b5b7c000d05 0xfffffffff801ffff 0xffffffffff003fff

def z803 : W := mkw 0x36c01db40b7a0780 0x06d803b6816f40f0 0xffc01ffc0fffc7ff 0xbff803ff81fff8ff

def z804 : W := mkw 0x36c01db40b7a0780 0x06d803b6816f40f0 0x7fc01ffc07fe0007 0xaff803ff80ffc000

def z805 : W := mkw 0x1f7bdadbe0808000 0x23ef7b5b7c101000 0x7ffffffff9c0c007 0xefffffffff381800

def z806 : W := mkw 0x0c2c180154c18150 0x018583002a98302a 0xdc3c1003f9c1c7f9 0xfb8782007f3838ff

def z807 : W := mkw 0x8005670e36571f75 0x1000ace1c6cae3ee 0x804fef1e763f3ffe 0xf009fde3cec7e7ff

def z808 : W := mkw 0x493ea0000485f000 0x0927d4000090be00 0xdc7fe0000ffff807 0xdb8ffc0001ffff00

def z809 : W := mkw 0x0193036289386aae 0x0032606c51270d55 0xa3b313e38ffffffd 0xf476627c71ffffff

def z810 : W := mkw 0x5bfea0608dadf08a 0x0b7fd40c11b5be11 0xffffe0e00ffff807 0xdffffc1c01ffff00

def z811 : W := mkw 0x5aeca0000dadf000 0x0b5d940001b5be00 0xdc4fe0000ffff806 0xdb89fc0001ffff00

def z812 : W := mkw 0x53d3e3faa93c7aae 0x2a7a7c7f55278f55 0x23c3e3fc003e3804 0x04787c7f8007c700

def z813 : W := mkw 0x0005630a24151a24 0x0000ac614482a344 0x804fef1e763f3e66 0xf009fde3cec7e7cc

def z814 : W := mkw 0x8005676eb6171eef 0x1000acedd6c2e3dd 0x807ffffffe3fffff 0xf00fffffffc7ffff

def z815 : W := mkw 0x6d3ebdb406d7f780 0x0da7d7b680dafef0 0x003ffffc0001ff80 0x6007ffff80003ff0

def z816 : W := mkw 0x1f7ad8d9e0000000 0x23ef5b1b3c000000 0x7ffcfffdf0000007 0xafff9fffbe000000

def z817 : W := mkw 0x36c01db40b7a0780 0x06d803b6816f40f0 0xffc31ffc0fff3f87 0xfff863ff81ffe7f0

def z818 : W := mkw 0x8005620a34051865 0x1000ac414680a30c 0x804fef1e763f3866 0xf009fde3cec7e70c

def z819 : W := mkw 0x8005670e36171e65 0x1000ace1c6c2e3cc 0x804fef1c763f3806 0xd009fde38ec7e700

def z820 : W := mkw 0x5bfea0608dadf08a 0x0b7fd40c11b5be11 0xfffff0e38fffffff 0xfffffe1c71ffffff

def z821 : W := mkw 0x0001470e22120e24 0x000028e1c44241c4 0x804fef1e763f3e66 0xf009fde3cec7e7cc

def z822 : W := mkw 0x3ffa98f1c968618a 0x27ff531e392d0c31 0x7fb010e189c0c199 0x0ff6021c31381833

def z823 : W := mkw 0x5bfea0000dadf000 0x0b7fd40001b5be00 0xffcfe00007ff3806 0xdff9fc0000ffe700

def z824 : W := mkw 0x09be20000ca5f000 0x0137c4000194be00 0xffffe0000ffff807 0xdffffc0001ffff00

def z825 : W := mkw 0x8005670e36979e75 0x1000ace1c6d2f3ce 0x804fef1e763ffe7e 0xf009fde3cec7ffcf

def z826 : W := mkw 0x36c01db40b7a0780 0x06d803b6816f40f0 0xffcffffc0ffe0787 0xfff9ffff81ffc0f0

def z827 : W := mkw 0x16415adbe0000000 0x22c82b5b7c000000 0x7fcffffff0000007 0xeff9fffffe000000

def z828 : W := mkw 0x493fe24bf485f050 0x2927fc497e90be0a 0x003fe003f001f878 0x4007fc007e003f0f

def z829 : W := mkw 0x1b7bc2dbe0000000 0x236f785b7c000000 0x23ffeffff0000006 0xe47ffdfffe000000

def z830 : W := mkw 0x36c01db41b7a07c0 0x06d803b6836f40f8 0xffc01ffe7ffe07e7 0xbff803ffcfffc0fc

def z831 : W := mkw 0x52c420000dadf000 0x0a58840001b5be00 0xffcfe0000ffff807 0xdff9fc0001ffff00

def z832 : W := mkw 0x5aeca0000dad9000 0x0b5d940001b5b200 0xffcfe0000fff3807 0xdff9fc0001ffe700

def z833 : W := mkw 0x5bfea0900dadf000 0x0b7fd41201b5be00 0xffffe3fc0ffff807 0xdffffc7f81ffff00

def z834 : W := mkw 0x36c01db40b7a0780 0x06d803b6816f40f0 0xfff01fff8ffe0787 0xfffe03fff1ffc0f0

def z835 : W := mkw 0x4c2cbc0156c59550 0x098597802ad8b2aa 0xdc3cfc03ffc1c7fb 0xfb879f807ff838ff

def z836 : W := mkw 0x0c2c1c0556c38550 0x01858380aad870aa 0xdc7c1c1fffcfc7fb 0xfb8f8383fff9f8ff

def z837 : W := mkw 0x0c2c1c9156c18550 0x018583922ad830aa 0xdc3c1fffffc1c7fb 0xfb8783fffff838ff

def z838 : W := mkw 0x3f7bdadbe1480100 0x27ef7b5b7c290020 0x7ffffffff1c00007 0xeffffffffe380000

def z839 : W := mkw 0x36c01db40b7a0780 0x06d803b6816f40f0 0x7fc01ffc0fce0783 0x2ff803ff81f9c0f0

def z840 : W := mkw 0x1753dadbe0000000 0x22ea7b5b7c000000 0x23cffffff0000006 0xe479fffffe000000

def z841 : W := mkw 0xc93fe24ab485f86f 0x1927fc495690bf0d 0x003fe003f001f878 0x4007fc007e003f0f

def z842 : W := mkw 0x5bfea0000dadf000 0x0b7fd40001b5be00 0xffffe0000fffffff 0xdffffc0001ffffff

def z843 : W := mkw 0x36401d94035a0700 0x06c803b2806b40e0 0xffc01ffc07fe0607 0xbff803ff80ffc0c0

def z844 : W := mkw 0x1f7bdadbe0006000 0x23ef7b5b7c000c00 0x7ffffffff001f807 0xeffffffffe003f00

def z845 : W := mkw 0x5e6cfc9977cd9550 0x2bcd9f932ef9b2aa 0x5c4cec1c77ce0002 0x0b899d838ef9c000

def z846 : W := mkw 0x0193036288306aae 0x0032606c51060d55 0xa3f31fff8831ffff 0xf47e63fff1063fff

def z847 : W := mkw 0x36c01db40b7a0780 0x06d803b6816f40f0 0xffc013fc0ffe0785 0x1ff8027f81ffc0f0

def z848 : W := mkw 0x0005660a36051440 0x0000acc146c0a288 0x804fef1e763f3e66 0xf009fde3cec7e7cc

def z849 : W := mkw 0x1f7bdadbe0808010 0x23ef7b5b7c101002 0x7ffffffff000c01f 0xeffffffffe001803

def z850 : W := mkw 0x5bfea041cdadf000 0x2b7fd40839b5be00 0xffffe0018ffff807 0xdffffc0031ffff00

def z851 : W := mkw 0x1f7bdadbe0000000 0x23ef7b5b7c000000 0xfffffffff63e0007 0xfffffffffec7c000

def z852 : W := mkw 0x53d6a0000d2d7000 0x0a7ad40001a5ae00 0xffcfe0000fff3807 0xdff9fc0001ffe700

def z853 : W := mkw 0x5bfea0001dadf040 0x0b7fd40003b5be08 0xffffe0027ffff867 0xdffffc004fffff0c

def z854 : W := mkw 0x32c001b4093a0280 0x0658003681274050 0xffc013fc0ffe0787 0xbff8027f81ffc0f0

def z855 : W := mkw 0x0c2c3c0156c59550 0x018587802ad8b2aa 0xdc7cfc03ffcfc7fb 0xfb8f9f807ff9f8ff

def z856 : W := mkw 0x019200608820608a 0x0032400c11040c11 0xa3b310e38831fffd 0xf476621c71063fff

def z857 : W := mkw 0x0001620a20041000 0x00002c4144008200 0x004fef1e703e3806 0xe009fde3ce07c700

def z858 : W := mkw 0x1f7bdadbe0000000 0x23ef7b5b7c000000 0xfffffffff0010667 0xfffffffffe0020cc

def z859 : W := mkw 0x0c2c1c0156c18550 0x018583802ad830aa 0xdc3c0c03ffc1c7fa 0x5b8781807ff838ff

def z860 : W := mkw 0x36c01db40b7a6fae 0x06d803b6816f4df5 0xffc01ffc0ffe3f87 0xbff803ff81ffc7f0

def z861 : W := mkw 0x5bfea0408dadf000 0x0b7fd40811b5be00 0xfffff0e18ffff807 0xdffffe1c31ffff00

def z862 : W := mkw 0x5bfea0200dadf08a 0x0b7fd40401b5be11 0xffffe0000ffff99f 0xdffffc0001ffff33

def z863 : W := mkw 0x1e69dadbe0000000 0x23cd3b5b7c000000 0x7fccfffff0000007 0xaff99ffffe000000

def z864 : W := mkw 0x36c01db54b7a0780 0x06d803b6a96f40f0 0xffc01ffffffe0787 0xbff803ffffffc0f0

def z865 : W := mkw 0x0005670e26171600 0x0000ace1c4c2e2c0 0x804fef1e763f3e06 0xf009fde3cec7e7c0

def z866 : W := mkw 0x17535adaa0000000 0x02ea6b5b54000000 0x7ffffffff0000007 0xeffffffffe000000

def z867 : W := mkw 0x1f7bdadbe0000000 0x23ef7b5b7c000000 0xfffffffff0313807 0xfffffffffe062700

def z868 : W := mkw 0x12c02000092c1000 0x0258040001258200 0xffc3e0000ffe3807 0x9ff87c0001ffc700

def z869 : W := mkw 0x5bfea0000dadf000 0x0b7fd40001b5be00 0xffffef1c0ffff807 0xfffffde381ffff00

def z870 : W := mkw 0x5bfea0000dadf000 0x0b7fd40001b5be00 0xffcfe0000ffff806 0x1ff9fc0001ffff00

def z871 : W := mkw 0x8005670e36171e65 0x1000ace1c6c2e3cc 0x004fef1e703f3e64 0x6009fde3ce07e7cc

def z872 : W := mkw 0x1f7bdadbe0400100 0x23ef7b5b7c080020 0x7ffffffff9c00187 0xefffffffff380030

def z873 : W := mkw 0x0081032208300aa4 0x0010206441060154 0xa3b313e38831fffd 0xf476627c71063fff

def z874 : W := mkw 0x8005670e36171e65 0x1000ace1c6c2e3cc 0x807fef1ff63ffe7e 0xf00ffde3fec7ffcf

def z875 : W := mkw 0x0d3b5a4be0000000 0x01a76b497c000000 0x7ffffffff0000007 0xeffffffffe000000

def z876 : W := mkw 0x33d3c3fea93a6aae 0x267a787fd5274d55 0x23c3e3fc003e3804 0x04787c7f8007c700

def z877 : W := mkw 0xc08425241fbffeef 0x181084a483f7ffdd 0x800000000ffffff8 0x1000000001ffffff

def z878 : W := mkw 0x0c281c0152c08550 0x018503802a5810aa 0xdc301c03f9c1c7f9 0xfb8603807f3838ff

def z879 : W := mkw 0x36401c94034a0500 0x06c80392806940a0 0x7fc00ffc07ce0006 0x0ff801ff80f9c000

def z880 : W := mkw 0x5bfaa00009acf000 0x0b7f540001359e00 0xfff3e0000ffef807 0x9ffe7c0001ffdf00

def z881 : W := mkw 0x0193036288306aae 0x0032606c51060d55 0xa3b310e38831fff9 0x5476621c71063fff

def z882 : W := mkw 0x49bea0000dadf000 0x0937d40001b5be00 0xdc3fe0000ffff803 0xdb87fc0001ffff00

def z883 : W := mkw 0x5a6ca000058d9000 0x0b4d940000b1b200 0x5c4fe00007fe3806 0x0b89fc0000ffc700

def z884 : W := mkw 0x36c01db40b7a0780 0x06d803b6816f40f0 0xfff01ffd8ffec79f 0xbffe03ffb1ffd8f3

def z885 : W := mkw 0x53d6a0000dadf000 0x0a7ad40001b5be00 0xffc3e0000ffff807 0x9ff87c0001ffff00

def z886 : W := mkw 0x5bfea0d08dadf000 0x2b7fd41a11b5be00 0xffffe0e00ffff807 0xdffffc1c01ffff00

def z887 : W := mkw 0x1b7bc2daa0000000 0x236f785b54000000 0x7fffeffe70000007 0xeffffdffce000000

def z888 : W := mkw 0x16c019b009380280 0x02d8033601270050 0xffc01ffc0ffe0787 0xbff803ff81ffc0f0

def z889 : W := mkw 0x0c2c1c0156c18550 0x018583802ad830aa 0xdc7c1f1fffc1c7ff 0xfb8f83e3fff838ff

def z890 : W := mkw 0x1241429a20000000 0x0248285344000000 0x23cfeffe70000006 0xe479fdffce000000

def z891 : W := mkw 0x1bfea0000d2d1000 0x037fd40001a5a200 0xffffe0000fff3807 0xdffffc0001ffe700

def z892 : W := mkw 0x0193036288306aae 0x0032606c51060d55 0xa3f313e38e3fffff 0xf47e627c71c7ffff

def z893 : W := mkw 0x8005670e36171e65 0x1000ace1c6c2e3cc 0x807fef1e7e3ffe67 0xf00ffde3cfc7ffcc

def z894 : W := mkw 0x1753dadaa0000000 0x22ea7b5b54000000 0x7fcffffe70000007 0xeff9ffffce000000

def z895 : W := mkw 0x5bfea0014dadf010 0x0b7fd40029b5be02 0xffffe0018ffff81f 0xdffffc0031ffff03

def z896 : W := mkw 0x8c2c3c0556c79551 0x11858780aad8f2aa 0xdc3c1c03ffcfc7fb 0xfb8783807ff9f8ff

def z897 : W := mkw 0x5bfea0200dadf080 0x0b7fd40401b5be10 0xfffff0e00ffff987 0xdffffe1c01ffff30

def z898 : W := mkw 0x1f7bdadbe000600a 0x23ef7b5b7c000c01 0x7ffffffff000c01f 0xeffffffffe001803

def z899 : W := mkw 0x1e68d89960000000 0x23cd1b132c000000 0x7fcceffc70000006 0x0ff99dff8e000000

def z900 : W := mkw 0x8005670e36171e65 0x1000ace1c6c2e3cc 0x004fef1e763e3e66 0x2009fde3cec7c7cc

def z901 : W := mkw 0x8005630e34171a65 0x1000ac61c682e34c 0x004fef1e703f3866 0xe009fde3ce07e70c

def z902 : W := mkw 0xa08425241fff9ff5 0x141084a483fff3fe 0x800000000ffffff8 0x1000000001ffffff

def z903 : W := mkw 0x1f7bdadbe0000000 0x23ef7b5b7c000000 0x7fffeffc70000007 0xcffffdff8e000000

def z904 : W := mkw 0x1f7bdadbe1080000 0x23ef7b5b7c210000 0x7ffffffff7ce0007 0xeffffffffef9c000

def z905 : W := mkw 0x1aec20000dad9000 0x035d840001b5b200 0xffffe0000ffff807 0xdffffc0001ffff00

def z906 : W := mkw 0x011302428000682e 0x0022604850000d05 0xa3b313e38801fffd 0xf476627c71003fff

def z907 : W := mkw 0x0193436aa8306aae 0x0032686d55060d55 0xa3f3f3ff8831fffd 0xf47e7e7ff1063fff

def z908 : W := mkw 0x1f7bdadbe0000000 0x23ef7b5b7c000000 0x23fffffff0000004 0x647ffffffe000000

def z909 : W := mkw 0x1e695a9b60000000 0x03cd2b536c000000 0x7ffffffff0000007 0xeffffffffe000000

def z910 : W := mkw 0x32c005b40b3a0680 0x065800b6816740d0 0xffc00ffc0ffe0607 0xbff801ff81ffc0c0

def z911 : W := mkw 0xc93fe24bf485f865 0x3927fc497e90bf0c 0x003fe003f001f860 0x4007fc007e003f0c

def z912 : W := mkw 0x1353c2daa0000000 0x226a785b54000000 0x23cfeffc70000006 0x0479fdff8e000000

def z913 : W := mkw 0x16c01c900b680500 0x02d80392016d00a0 0xffc01ffc0ffe0787 0xbff803ff81ffc0f0

def z914 : W := mkw 0x04001c0152400550 0x008003802a4800aa 0xdc301c03ffc1c7fb 0xfb8603807ff838ff

def z915 : W := mkw 0x36c01db41b7a07d0 0x06d803b6836f40fa 0xffc01ffc0ffe07ff 0xbff803ff81ffc0ff

def z916 : W := mkw 0x5b7ea000058df000 0x0b6fd40000b1be00 0xdc7fe00007fff806 0xdb8ffc0000ffff00

def z917 : W := mkw 0x0193036288306aae 0x0032606c51060d55 0x23b313e38031fffc 0x6476627c70063fff

def z918 : W := mkw 0x1f7bdadbe0400110 0x23ef7b5b7c080022 0x7ffffffff000019f 0xeffffffffe000033

def z919 : W := mkw 0x8005670e36171e65 0x1000ace1c6c2e3cc 0x807fff1ff63f3e67 0xf00fffe3fec7e7cc

def z920 : W := mkw 0x36c01db40b7a0780 0x06d803b6816f40f0 0xffc01ffe0fff07e7 0xfff803ffc1ffe0fc

def z921 : W := mkw 0x36401db4035a0780 0x06c803b6806b40f0 0x7fc01ffc07ce0787 0xaff803ff80f9c0f0

def z922 : W := mkw 0x8004640c36071441 0x10008c8186c0e288 0x004fec1c763e3806 0x0009fd838ec7c700

def z923 : W := mkw 0x808425241ef7ffff 0x101084a483deffff 0x800000000ffffff8 0x1000000001ffffff

def z924 : W := mkw 0x493fe24be4859000 0x2927fc497c90b200 0x003fe003f0000000 0x4007fc007e000000

def z925 : W := mkw 0x5a6ca000058d9000 0x0b4d940000b1b200 0xdc7fe0000ffff807 0xdb8ffc0001ffff00

def z926 : W := mkw 0x0001420a20000000 0x0000284144000000 0x23cffffe70000007 0xe479ffffce000000

def z927 : W := mkw 0x1f7bdadbe000082e 0x23ef7b5b7c000105 0x7ffffffff000007f 0xeffffffffe00000f

def z928 : W := mkw 0x8193436ea8326aaf 0x1032686dd5064d55 0xa3b313ff8831fffd 0xf476627ff1063fff

def z929 : W := mkw 0x1f7bdadbe0000000 0x23ef7b5b7c000000 0x7ffffffdf0000007 0x0fffffffbe000000

def z930 : W := mkw 0x8004650c36171641 0x10008ca186c2e2c8 0x804fef1c763f3e06 0xf009fde38ec7e7c0

def z931 : W := mkw 0x36c01db40b7a6fae 0x06d803b6816f4df5 0xfff01fff8fffffff 0xfffe03fff1ffffff

def z932 : W := mkw 0x8005670e36d79f75 0x1000ace1c6daf3ee 0x804fef1e77ff3e66 0xf009fde3ceffe7cc

def z933 : W := mkw 0x0c2c1c0156c18550 0x018583802ad830aa 0x5c3c1c03ffc0c7fb 0x2b8783807ff818ff

def z934 : W := mkw 0x5ffa98f1c9a8e08a 0x2bff531e39351c11 0x7fb010e189c0c199 0x0ff6021c31381833

def z935 : W := mkw 0x1e69da9b60000000 0x23cd3b536c000000 0x7fcffffe70000007 0xeff9ffffce000000

def z936 : W := mkw 0x36c01db40b7a0780 0x06d803b6816f40f0 0xffc00ffc0ffe0786 0x1ff801ff81ffc0f0

def z937 : W := mkw 0xb6c01db41b7a0fe5 0x16d803b6836f41fc 0xffc01ffc0ffe07e7 0xbff803ff81ffc0fc

def z938 : W := mkw 0x1f7bdadbe0000000 0x23ef7b5b7c000000 0x7ffffffff00007ff 0xeffffffffe0000ff

def z939 : W := mkw 0x36c01c940b6a0500 0x06d80392816d40a0 0xffc01ffc0ffe0007 0xbff803ff81ffc000

def z940 : W := mkw 0x5b7ea000058d9000 0x0b6fd40000b1b200 0xffffe00007ff3807 0xdffffc0000ffe700

def z941 : W := mkw 0x082c000154818050 0x010580002a90300a 0xdc3c1003ffc1c7fb 0xfb8782007ff838ff

def z942 : W := mkw 0xa4015ffff2520fe5 0x34802bfffe4a41fc 0x00001ffff00007e0 0x200003fffe0000fc

def z943 : W := mkw 0x8005670e36171e65 0x1000ace1c6c2e3cc 0x804fef1c763e3e06 0xb009fde38ec7c7c0

def z944 : W := mkw 0x0004600824051000 0x00008c010480a200 0x804fec1c763f3806 0xd009fd838ec7e700

def z945 : W := mkw 0x8001670e22161e25 0x10002ce1c442c3c4 0x804fef1e763e3e06 0xf009fde3cec7c7c0

def z946 : W := mkw 0x12c0009009280000 0x0258001201250000 0xffc003fc0ffe0007 0x9ff8007f81ffc000

def z947 : W := mkw 0x36c01db54b7a0790 0x06d803b6a96f40f2 0xffc01ffd8ffe079f 0xbff803ffb1ffc0f3

def z948 : W := mkw 0x5ffa98d1c9286000 0x2bff531a39250c00 0x7fb010e180000001 0x0ff6021c30000000

def z949 : W := mkw 0x8005672e36171eef 0x1000ace5c6c2e3dd 0x804fef1e763f3ffe 0xf009fde3cec7e7ff

def z950 : W := mkw 0x36c01db40b7a678a 0x06d803b6816f4cf1 0xffc01ffc0ffec79f 0xbff803ff81ffd8f3

def z951 : W := mkw 0x5bfea0014dadf000 0x0b7fd40029b5be00 0xffffe003fffff807 0xdffffc007fffff00

def z952 : W := mkw 0x21930366893a6aae 0x0432606cd1274d55 0xa3b313e3883ffffd 0xf476627c7107ffff

def z953 : W := mkw 0x8005672e36171ee5 0x1000ace5c6c2e3dc 0x804ffffe763f3fe6 0xf009ffffcec7e7fc

def z954 : W := mkw 0x9e6cfc9d76c79551 0x33cd9f93aed8f2aa 0x5c4cec1c77ce0002 0x0b899d838ef9c000

def z955 : W := mkw 0x0113424aa0000000 0x0022684954000000 0x23cfeffe70000006 0xe479fdffce000000

def z956 : W := mkw 0x893fe24bf4859875 0x3127fc497e90b30e 0x003fe003f001f878 0x4007fc007e003f0f

def z957 : W := mkw 0x8001630e20161a25 0x10002c61c402c344 0x804fef1e703f3e66 0xf009fde3ce07e7cc

def z958 : W := mkw 0x0c2c1c0156c18550 0x018583802ad830aa 0xffbc1fe3ffc1c7ff 0xfff783fc7ff838ff

def z959 : W := mkw 0x8005660e36071441 0x1000acc1c6c0e288 0x804fef1e763f3806 0xf009fde3cec7e700

def z960 : W := mkw 0x48ac20000dadf000 0x0915840001b5be00 0xdc7fe0000ffff807 0xdb8ffc0001ffff00

def z961 : W := mkw 0x1f7bdadbe0000000 0x23ef7b5b7c000000 0xfffffffff801c007 0xffffffffff003800

def z962 : W := mkw 0x1f7bdadbe0000000 0x23ef7b5b7c000000 0x7ffcfffff0000003 0x2fff9ffffe000000

def z963 : W := mkw 0x24015fffe2520fae 0x24802bfffc4a41f5 0x00001ffff00007f8 0x200003fffe0000ff

def z964 : W := mkw 0x1f7bdadbe0000000 0x23ef7b5b7c000000 0x7ffffffff001c07f 0xeffffffffe00380f

def z965 : W := mkw 0x1640189001080000 0x02c8031200210000 0x7fc01ffc07ce0007 0xaff803ff80f9c000

def z966 : W := mkw 0x1bfa800009286000 0x037f500001250c00 0xffffe0000ffff807 0xdffffc0001ffff00

def z967 : W := mkw 0x8005676eb6171eef 0x1000acedd6c2e3dd 0x804feffe763f3e66 0xf009fdffcec7e7cc

def z968 : W := mkw 0x0193036288306aae 0x0032606c51060d55 0xa3bf1fe3f831ffff 0xf477e3fc7f063fff

def z969 : W := mkw 0x1f7bda9a20000000 0x03ef7b5344000000 0x7ffffffe70000007 0xefffffffce000000

def z970 : W := mkw 0xd3d3e36ea93e7aaf 0x1a7a7c6dd527cf55 0x23c3e3fc003e3804 0x04787c7f8007c700

def z971 : W := mkw 0x0004200004051000 0x000084000080a200 0xdc4fe0000fff3807 0xdb89fc0001ffe700

def z972 : W := mkw 0x1f7bdadbe000682e 0x23ef7b5b7c000d05 0x7ffffffff0003807 0xeffffffffe000700

def z973 : W := mkw 0x0d3bdadbe0000000 0x21a77b5b7c000000 0x23bffffff0000005 0xe477fffffe000000

def z974 : W := mkw 0x84015fdff2520f75 0x30802bfbfe4a41ee 0x00001ffff00007f8 0x200003fffe0000ff

def z975 : W := mkw 0x7ffa98b149e8e190 0x0fff5316293d1c32 0x7fb010e189c0c199 0x0ff6021c31381833

def z976 : W := mkw 0x7bfea0b00dadf080 0x0f7fd41601b5be10 0xffffe0e00ffff807 0xdffffc1c01ffff00

def z977 : W := mkw 0x8005670e36171e65 0x1000ace1c6c2e3cc 0x804fec1e763f3e62 0x5009fd83cec7e7cc

def z978 : W := mkw 0x0c281c0142400500 0x01850380284800a0 0xdc3c1c03ffc1c7fb 0xfb8783807ff838ff

def z979 : W := mkw 0x8005670e36171e65 0x1000ace1c6c2e3cc 0x804fef1c763f3e66 0x1009fde38ec7e7cc

def z980 : W := mkw 0x5bfea0000dadf000 0x0b7fd40001b5be00 0xffcfe0000ffe3807 0x9ff9fc0001ffc700

def z981 : W := mkw 0x5bfea0000dadf000 0x0b7fd40001b5be00 0xffffe0020ffffe67 0xfffffc0041ffffcc

def z982 : W := mkw 0x04041c0016410540 0x0080838002c820a8 0xdc3c1c03ffc1c7fb 0xfb8783807ff838ff

def z983 : W := mkw 0x1b7ea00004859000 0x036fd4000090b200 0xffffe0000ffff807 0xdffffc0001ffff00

def z984 : W := mkw 0x36c019b4097a0380 0x06d80336812f4070 0xffc013fc0ffe0187 0x9ff8027f81ffc030

def z985 : W := mkw 0x8005670e36171e65 0x1000ace1c6c2e3cc 0x804fef1e7e3ffffe 0xf009fde3cfc7ffff

def z986 : W := mkw 0x5bfea0000dadf000 0x0b7fd40001b5be00 0x7fffe00007fe3807 0xcffffc0000ffc700

def z987 : W := mkw 0xa4015fbf72520ff5 0x14802bf7ee4a41fe 0x00001ffff00007f8 0x200003fffe0000ff

def z988 : W := mkw 0x84015f6ff2520fff 0x10802bedfe4a41ff 0x00001ffff00007f8 0x200003fffe0000ff

def z989 : W := mkw 0x36c01db55b7a07d0 0x06d803b6ab6f40fa 0xffc01ffc7ffe0787 0xbff803ff8fffc0f0

def z990 : W := mkw 0x1f7bdadbe0c08110 0x23ef7b5b7c181022 0xfffffffff9c1c7ff 0xffffffffff3838ff

def z991 : W := mkw 0x8005660e36071c65 0x1000acc1c6c0e38c 0x804fec1e763f3866 0xd009fd83cec7e70c

def z992 : W := mkw 0x5bfea0408dadf00a 0x0b7fd40811b5be01 0xffffe0018ffff81f 0xdffffc0031ffff03

def z993 : W := mkw 0x32c005b40b7a0780 0x065800b6816f40f0 0xffc003fc0ffe0787 0x9ff8007f81ffc0f0

def z994 : W := mkw 0x493fe24be485f82e 0x2927fc497c90bf05 0x003fe003f001f878 0x4007fc007e003f0f

def z995 : W := mkw 0x36c01cb40b6a0580 0x06d80396816d40b0 0x7fc01ffc0fce0187 0xaff803ff81f9c030

def z996 : W := mkw 0x5ffa989149a8e000 0x2bff531229351c00 0x7fb0000009c0c001 0x0ff6000001381800

def z997 : W := mkw 0x13d620000d2d7000 0x027ac40001a5ae00 0xffffe0000ffff807 0xdffffc0001ffff00

def z998 : W := mkw 0x0193c36aa8306aae 0x2032786d55060d55 0xa3b3f3e38831fffd 0xf4767e7c71063fff

def z999 : W := mkw 0x5bfea0000dadf000 0x0b7fd40001b5be00 0xffffe0038ffff87f 0xdffffc0071ffff0f

def z1000 : W := mkw 0x8005670e36171e65 0x1000ace1c6c2e3cc 0x804fff1ff63f3ffe 0xf009ffe3fec7e7ff

def z1001 : W := mkw 0x1f7bdadbe0c08110 0x23ef7b5b7c181022 0x7ffffffff1c00007 0xeffffffffe380000

def z1002 : W := mkw 0x32c001b4093a0280 0x0658003681274050 0x7fc003fc07fe0006 0x0ff8007f80ffc000

def z1003 : W := mkw 0x0c2c1c0156c18550 0x018583802ad830aa 0xdc301c03ffc1c7f9 0x3b8603807ff838ff

def z1004 : W := mkw 0x1f7bdadbe0000000 0x23ef7b5b7c000000 0x7fcfeffe70000006 0xeff9fdffce000000

def z1005 : W := mkw 0x1e68d89960000000 0x23cd1b132c000000 0x7ffcfffff0000007 0xefff9ffffe000000

def z1006 : W := mkw 0x36c01db40b7a0780 0x06d803b6816f40f0 0xffcc1ffe7ffe0787 0xfff983ffcfffc0f0

def z1007 : W := mkw 0x5bfea0000dadf000 0x0b7fd40001b5be00 0xffffec027ffff807 0xfffffd804fffff00

def z1008 : W := mkw 0x5bfaa000092c7000 0x0b7f540001258e00 0xffffe0000ffe3807 0xdffffc0001ffc700

def z1009 : W := mkw 0x8005670e36171e65 0x1000ace1c6c2e3cc 0xa3cffffe763f3e67 0xf479ffffcec7e7cc

def z1010 : W := mkw 0x2c2c1c9556c38550 0x05858392aad870aa 0xdc3c1c1fffc1c7fb 0xfb878383fff838ff

def z1011 : W := mkw 0x0c2c3c0156c59550 0x018587802ad8b2aa 0xdc3ffc03ffc1fffb 0xfb87ff807ff83fff

def z1012 : W := mkw 0x36c01db40b7a0780 0x06d803b6816f40f0 0xff801ffc0ffe0781 0x3ff003ff81ffc0f0

def z1013 : W := mkw 0x36c01db40b7a0780 0x06d803b6816f40f0 0xfff01ffc0fffc787 0xfffe03ff81fff8f0

def z1014 : W := mkw 0x36c01db40b7a0780 0x06d803b6816f40f0 0xffc00ffc07fe0606 0xbff801ff80ffc0c0

def z1015 : W := mkw 0x0c2c180144818000 0x0185830028903000 0xdc3c1c03ffc1c7fb 0xfb8783807ff838ff

def z1016 : W := mkw 0x53d2a000092c7000 0x0a7a540001258e00 0x7fc3e00007fe3806 0x0ff87c0000ffc700

def z1017 : W := mkw 0xe08425241fffffe5 0x1c1084a483fffffc 0x800000000fffffe0 0x1000000001fffffc

def z1018 : W := mkw 0xa08425241f7f7fef 0x141084a483efeffd 0x800000000ffffff8 0x1000000001ffffff

def z1019 : W := mkw 0xa4015ffeb2520fef 0x14802bffd64a41fd 0x00001ffff00007f8 0x200003fffe0000ff

def z1020 : W := mkw 0xa08425241f7f17c1 0x141084a483efe2f8 0x800000000ffe0780 0x1000000001ffc0f0

def z1021 : W := mkw 0x8005670e36171e65 0x1000ace1c6c2e3cc 0x804fff1e7e3f3fe7 0xf009ffe3cfc7e7fc

def z1022 : W := mkw 0x1353c2daa0000000 0x226a785b54000000 0x23fffffff0000007 0xe47ffffffe000000

def z1023 : W := mkw 0x1640589820000000 0x02c80b1304000000 0x7fccfffc70000007 0xaff99fff8e000000

def z1024 : W := mkw 0x0c2c1c0156c18550 0x018583802ad830aa 0xdc3c1003ffc1c7f9 0x5b8782007ff838ff

def z1025 : W := mkw 0x0193436aa8306aae 0x0032686d55060d55 0xa3bff3e3f831fffd 0xf477fe7c7f063fff

def z1026 : W := mkw 0x36c01db40b7a0780 0x06d803b6816f40f0 0x7fc01ffc07fe0786 0x2ff803ff80ffc0f0

def z1027 : W := mkw 0x01930262882068ae 0x0032604c51040d15 0xa3b310e38801fff9 0xf476621c71003fff

def z1028 : W := mkw 0x5bfea0000dadf000 0x0b7fd40001b5be00 0x7fffe00007fff806 0x4ffffc0000ffff00

def z1029 : W := mkw 0x36c01db40b7a0780 0x06d803b6816f40f0 0xffc00ffc0ffe0007 0x9ff801ff81ffc000

def z1030 : W := mkw 0x1f7bdadbe0000000 0x23ef7b5b7c000000 0x7ffffffff800c19f 0xefffffffff001833

def z1031 : W := mkw 0x05135adbe0000000 0x20a26b5b7c000000 0x23fffffff0000007 0xe47ffffffe000000

def z1032 : W := mkw 0x0193024288206000 0x0032604851040c00 0xa3b313e38831fffd 0xf476627c71063fff

def z1033 : W := mkw 0x1f7ad89960000000 0x23ef5b132c000000 0x7ffffffc70000007 0xefffffff8e000000

def z1034 : W := mkw 0x8005674eb6171e6f 0x1000ace9d6c2e3cd 0x804fef1ff63f3e7e 0xf009fde3fec7e7cf

def z1035 : W := mkw 0x608425241ffff7d0 0x0c1084a483fffefa 0x800000000ffffff8 0x1000000001ffffff

def z1036 : W := mkw 0x1f7bdadbe0000000 0x23ef7b5b7c000000 0x7fcffffff0000006 0x2ff9fffffe000000

def z1037 : W := mkw 0x5bfea0000dadf000 0x0b7fd40001b5be00 0x7fffe0000ffef807 0x0ffffc0001ffdf00

def z1038 : W := mkw 0x8005674eb6171e65 0x1000ace9d6c2e3cc 0x804ffffff63f3e66 0xf009fffffec7e7cc

def z1039 : W := mkw 0x0193036688326aae 0x0032606cd1064d55 0xa3f313ff883ffffd 0xf47e627ff107ffff

def z1040 : W := mkw 0x36c01db40b7a0780 0x06d803b6816f40f0 0x7fc01ffc0ffe0187 0x0ff803ff81ffc030

def z1041 : W := mkw 0x36c019b4093a0280 0x06d8033681274050 0xffc01ffc0ffe0007 0xbff803ff81ffc000

def z1042 : W := mkw 0x36401c94034a0500 0x06c80392806940a0 0xffc01ffc0fce0787 0xbff803ff81f9c0f0

def z1043 : W := mkw 0x1f7bdadbe0000824 0x23ef7b5b7c000104 0x7ffffffff0013867 0xeffffffffe00270c

def z1044 : W := mkw 0x1f7bdadbe0000000 0x23ef7b5b7c000000 0xffffffffffc00007 0xfffffffffff80000

def z1045 : W := mkw 0x7e6cbc9557cf9550 0x0fcd9792aaf9f2aa 0x5c4cec1c77ce0002 0x0b899d838ef9c000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(1,[z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z6,z2,z7,z4,z5]),(0,[z8,z0,z1,z2,z7,z4,z9]),(0,[z0,z10,z1,z2,z7,z4,z5]),(0,[z11,z0,z1,z2,z7,z4,z5])],[(0,[z0,z1,z12,z2,z7,z4,z5]),(0,[z0,z13,z1,z2,z7,z4,z5]),(0,[z0,z14,z15,z2,z7,z4,z5]),(0,[z0,z1,z2,z16,z7,z4,z5]),(0,[z0,z1,z2,z17,z4,z18,z5]),(0,[z19,z0,z1,z2,z7,z5,z20]),(0,[z0,z21,z1,z2,z7,z4,z5])],[(0,[z0,z1,z2,z7,z4,z5,z22]),(0,[z0,z23,z1,z2,z7,z4,z5]),(0,[z0,z1,z24,z2,z7,z4,z25]),(0,[z0,z1,z2,z7,z26,z4,z5])],[(0,[z0,z1,z27,z28,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z29,z30]),(0,[z0,z1,z2,z31,z7,z4,z5]),(0,[z32,z0,z1,z2,z7,z4,z5]),(0,[z33,z0,z1,z2,z7,z4,z5])],[(0,[z0,z1,z2,z7,z4,z34,z5]),(0,[z0,z1,z2,z35,z36,z4,z5])],[(0,[z37,z0,z1,z2,z7,z4,z5]),(0,[z38,z0,z1,z2,z4,z5,z39]),(0,[z0,z1,z2,z40,z7,z4,z39]),(0,[z0,z1,z2,z7,z5,z41,z39])],[(0,[z0,z1,z2,z7,z4,z42,z5]),(0,[z43,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z44,z5]),(0,[z0,z1,z45,z2,z7,z4,z5])],[(0,[z0,z46,z1,z2,z7,z4,z5])]],
   [[(0,[z0,z1,z2,z7,z4,z47,z5]),(0,[z0,z1,z2,z7,z4,z48,z5]),(0,[z0,z1,z2,z7,z49,z4,z5]),(0,[z0,z1,z2,z7,z4,z50,z5])],[(0,[z0,z1,z51,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z52,z4,z5]),(1,[z53,z1,z2,z7,z4,z5])],[(0,[z54,z0,z1,z7,z4,z25,z5]),(0,[z0,z55,z1,z2,z7,z4,z5]),(0,[z0,z1,z56,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z57,z4,z58])],[(0,[z1,z2,z7,z4,z59,z5,z29]),(0,[z0,z60,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z5,z30]),(0,[z0,z1,z2,z61,z7,z4,z5])],[(0,[z0,z1,z2,z7,z4,z62,z5]),(0,[z0,z63,z1,z2,z7,z4,z5]),(0,[z0,z1,z7,z64,z4,z18,z5]),(0,[z65,z19,z0,z1,z2,z7,z4]),(0,[z0,z1,z66,z2,z7,z4,z5])],[(0,[z67,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z5,z68]),(0,[z0,z1,z2,z7,z69,z4,z5]),(0,[z0,z70,z1,z2,z7,z4,z5]),(0,[z0,z1,z7,z4,z25,z5,z71])],[(0,[z0,z1,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z72,z5]),(0,[z0,z1,z73,z7,z4,z5,z39]),(0,[z0,z74,z1,z2,z7,z4,z5])],[(0,[z0,z1,z2,z7,z75,z4,z5]),(0,[z0,z1,z2,z7,z4,z5,z76]),(1,[z0,z1,z2,z31,z4,z5]),(1,[z0,z1,z77,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z5,z78]),(0,[z0,z1,z2,z79,z7,z4,z5])]],
   [[(0,[z0,z1,z2,z7,z80,z4,z5]),(0,[z0,z81,z1,z2,z7,z4,z5]),(1,[z0,z1,z2,z7,z4,z82])],[(0,[z0,z83,z1,z2,z7,z4,z5]),(0,[z0,z1,z84,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z59,z5]),(0,[z0,z1,z2,z7,z4,z85,z5]),(1,[z86,z0,z2,z7,z4,z30]),(0,[z0,z87,z1,z2,z7,z4,z5])],[(1,[z0,z1,z2,z7,z88,z5]),(0,[z0,z1,z89,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z5,z90]),(0,[z0,z1,z2,z7,z91,z4,z5]),(0,[z0,z1,z92,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z5,z93]),(0,[z94,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z57,z58,z5])],[(0,[z0,z1,z2,z95,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z5,z96]),(0,[z0,z1,z2,z7,z4,z5,z97])],[(0,[z98,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z99,z100,z4,z5])],[(0,[z101,z0,z1,z2,z7,z4,z5]),(0,[z65,z54,z0,z1,z7,z4,z5]),(0,[z102,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z103,z4,z5]),(0,[z0,z1,z2,z7,z4,z5,z104]),(0,[z0,z1,z2,z105,z7,z4,z5]),(0,[z0,z1,z24,z2,z7,z4,z5]),(0,[z106,z0,z1,z2,z7,z4,z5])],[(1,[z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z107,z2,z7,z4,z5])],[(0,[z108,z0,z1,z2,z7,z4,z5]),(0,[z0,z109,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z5,z110])]],
   [[(0,[z111,z0,z1,z2,z7,z4,z5]),(0,[z112,z113,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z114,z115,z5]),(0,[z0,z1,z2,z7,z116,z4,z5]),(0,[z0,z1,z117,z2,z7,z4,z5]),(0,[z118,z0,z1,z2,z7,z4,z5])],[(0,[z0,z119,z1,z2,z7,z4,z5]),(0,[z0,z70,z1,z7,z64,z4,z5]),(0,[z0,z1,z2,z7,z120,z4,z5])],[(0,[z0,z121,z1,z2,z7,z4,z5]),(0,[z0,z1,z122,z2,z7,z4,z5])],[(0,[z0,z123,z1,z2,z7,z4,z5])],[(1,[z124,z1,z125,z7,z4,z5]),(0,[z126,z0,z1,z2,z7,z4,z5]),(0,[z65,z0,z1,z27,z7,z4,z5]),(0,[z127,z0,z1,z2,z7,z4,z5]),(0,[z0,z128,z1,z129,z7,z4,z5]),(0,[z0,z1,z2,z130,z7,z4,z5]),(0,[z0,z1,z131,z2,z7,z4,z5])],[(0,[z0,z1,z132,z2,z7,z4,z5]),(1,[z112,z1,z2,z7,z133,z5]),(0,[z112,z0,z1,z2,z7,z133,z5]),(0,[z134,z0,z1,z2,z7,z88,z5]),(0,[z8,z0,z1,z2,z7,z4,z135]),(0,[z0,z1,z2,z7,z4,z5,z136]),(0,[z0,z1,z2,z7,z137,z4,z5])],[(0,[z0,z1,z2,z7,z4,z138,z5]),(0,[z19,z0,z1,z2,z7,z133,z5]),(0,[z0,z1,z2,z7,z4,z88,z5]),(0,[z0,z1,z2,z7,z4,z139,z5]),(0,[z0,z1,z2,z7,z4,z140,z5]),(0,[z0,z141,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z142,z4,z5]),(0,[z0,z143,z1,z2,z7,z4,z5])],[(0,[z0,z1,z144,z2,z7,z4,z5]),(0,[z0,z14,z2,z7,z4,z5,z30]),(0,[z0,z1,z2,z145,z7,z4,z5])]],
   [[(0,[z0,z1,z2,z7,z146,z4,z5]),(0,[z65,z0,z1,z7,z4,z5,z71])],[(0,[z0,z1,z2,z7,z4,z5,z147]),(0,[z134,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z148,z59])],[(0,[z0,z149,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z150,z7,z4,z5]),(1,[z0,z1,z151,z7,z4,z5]),(0,[z152,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z153,z4,z5])],[(0,[z0,z1,z2,z7,z4,z5,z154]),(0,[z0,z1,z155,z2,z7,z4,z5]),(0,[z0,z1,z2,z61,z7,z156,z5]),(0,[z157,z0,z1,z2,z7,z4,z5])],[(0,[z0,z1,z2,z7,z158,z4,z5]),(0,[z0,z159,z2,z35,z7,z4,z5]),(1,[z0,z1,z2,z160,z4,z5]),(0,[z0,z1,z161,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z5,z162])],[(0,[z0,z1,z2,z7,z163,z4,z5]),(0,[z124,z0,z1,z2,z3,z4,z5]),(0,[z164,z0,z1,z2,z165,z4,z5]),(0,[z0,z166,z2,z7,z100,z4,z5]),(0,[z0,z1,z2,z7,z4,z167,z5])],[(0,[z168,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z169,z4,z5]),(0,[z164,z0,z1,z2,z99,z4,z5]),(0,[z0,z1,z2,z7,z4,z170,z5]),(0,[z0,z1,z171,z2,z7,z4,z5])],[(0,[z0,z1,z172,z2,z7,z4,z5]),(0,[z0,z173,z1,z2,z7,z4,z5])]],
   [[(0,[z174,z0,z1,z2,z7,z4,z5]),(0,[z124,z0,z1,z125,z7,z4,z5]),(0,[z0,z1,z2,z175,z7,z4,z5]),(0,[z0,z176,z1,z77,z7,z4,z5]),(0,[z0,z128,z1,z2,z7,z4,z5]),(0,[z177,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z5,z178])],[(0,[z0,z1,z2,z179,z7,z4,z5]),(0,[z0,z176,z1,z180,z7,z4,z5])],[(0,[z0,z1,z2,z7,z4,z181,z5]),(0,[z0,z1,z2,z7,z4,z5,z182]),(0,[z0,z70,z1,z2,z7,z64,z5]),(0,[z0,z1,z2,z7,z4,z25,z5]),(0,[z0,z1,z92,z2,z7,z156,z5]),(0,[z0,z1,z2,z7,z4,z5,z183])],[(0,[z184,z0,z185,z2,z7,z4,z5])],[(0,[z184,z101,z1,z2,z7,z4,z5]),(0,[z186,z0,z1,z2,z7,z4,z5]),(0,[z187,z0,z1,z2,z7,z4,z5]),(0,[z0,z176,z1,z2,z7,z4,z148]),(0,[z0,z1,z129,z2,z188,z4,z5]),(0,[z0,z1,z2,z7,z4,z189,z5]),(0,[z19,z0,z1,z2,z7,z4,z58])],[(0,[z0,z1,z2,z190,z7,z4,z5]),(0,[z8,z0,z1,z27,z7,z4,z5]),(0,[z0,z191,z1,z2,z7,z4,z5]),(0,[z0,z70,z1,z2,z7,z18,z5])],[(0,[z0,z1,z2,z7,z4,z192,z5]),(0,[z134,z1,z2,z7,z4,z59,z5]),(0,[z0,z1,z2,z7,z193,z4,z5]),(0,[z0,z1,z2,z7,z4,z5,z194])],[(0,[z195,z0,z1,z2,z7,z4,z5]),(0,[z65,z0,z1,z196,z7,z4,z5]),(0,[z0,z176,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z197,z4,z5])]],
   [[(0,[z184,z0,z198,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z5,z29]),(0,[z0,z1,z199,z2,z7,z4,z5])],[(0,[z200,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z129,z125,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z201,z5])],[(0,[z202,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z5,z203]),(0,[z0,z1,z2,z7,z4,z5,z20])],[(0,[z204,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z205,z4,z5]),(0,[z0,z1,z2,z206,z7,z4,z5]),(1,[z0,z1,z2,z17,z4,z5]),(1,[z0,z1,z2,z7,z57,z58])],[(0,[z0,z1,z125,z2,z7,z4,z5]),(0,[z207,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z100,z36,z4,z5]),(0,[z0,z128,z1,z2,z208,z4,z5]),(0,[z0,z1,z2,z209,z7,z4,z5])],[(0,[z0,z1,z2,z7,z4,z210,z5]),(0,[z0,z1,z2,z211,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z5,z212]),(0,[z0,z1,z213,z2,z7,z4,z5])],[(0,[z0,z214,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z215,z5]),(0,[z0,z1,z2,z216,z7,z4,z5])],[(0,[z0,z1,z2,z7,z4,z217,z5]),(0,[z0,z1,z218,z2,z7,z4,z5]),(0,[z0,z1,z196,z7,z4,z25,z5])]],
   [[(0,[z0,z2,z7,z4,z181,z5,z30]),(0,[z0,z1,z219,z2,z7,z4,z5]),(0,[z0,z1,z2,z220,z7,z4,z5])],[(0,[z184,z0,z1,z221,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z5,z222]),(1,[z0,z223,z27,z7,z4,z5]),(0,[z0,z1,z2,z27,z7,z4,z5]),(0,[z0,z224,z1,z2,z7,z4,z5])],[(0,[z0,z225,z1,z2,z7,z4,z5]),(0,[z0,z226,z1,z2,z7,z4,z5]),(0,[z0,z1,z227,z2,z7,z4,z5]),(0,[z0,z1,z228,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z156,z5]),(0,[z38,z0,z1,z2,z7,z4,z39])],[(0,[z124,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z229,z2,z7,z4,z5])],[(1,[z230,z1,z2,z7,z4,z29]),(0,[z0,z1,z2,z231,z7,z4,z5])],[(0,[z232,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z233,z5]),(0,[z0,z1,z2,z7,z4,z5,z71])],[(0,[z0,z1,z2,z7,z4,z234,z5]),(0,[z0,z1,z2,z7,z99,z4,z5]),(0,[z0,z1,z235,z2,z7,z4,z5]),(1,[z0,z1,z2,z61,z36,z5]),(0,[z236,z0,z1,z2,z7,z4,z5])],[(1,[z0,z1,z2,z7,z4,z9]),(0,[z0,z1,z2,z237,z7,z4,z5]),(0,[z238,z0,z1,z2,z7,z4,z5]),(0,[z0,z239,z1,z2,z7,z4,z5])]],
   [[(0,[z240,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z5,z5]),(0,[z8,z0,z1,z196,z7,z4,z5]),(0,[z0,z241,z1,z2,z7,z5,z30]),(1,[z0,z70,z1,z7,z64,z5])],[(0,[z0,z1,z77,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z242,z4,z5]),(0,[z65,z0,z1,z2,z7,z57,z4]),(0,[z0,z243,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z244,z4,z5])],[(0,[z0,z1,z2,z7,z245,z4,z5]),(0,[z0,z1,z2,z7,z4,z18,z5])],[(0,[z0,z1,z2,z7,z246,z4,z5]),(0,[z0,z1,z247,z2,z7,z4,z5]),(0,[z0,z1,z2,z248,z7,z4,z5]),(1,[z0,z159,z2,z35,z4,z5]),(0,[z249,z0,z1,z2,z7,z4,z5])],[(0,[z250,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z129,z2,z7,z4,z5])],[(0,[z19,z0,z1,z2,z7,z115,z5]),(0,[z251,z0,z1,z2,z7,z4,z5]),(0,[z252,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z253,z5])],[(0,[z0,z254,z1,z2,z7,z4,z5]),(0,[z0,z255,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z256,z4,z5]),(0,[z0,z1,z2,z7,z257,z4,z5]),(0,[z0,z159,z1,z2,z35,z4,z5])],[(0,[z258,z0,z1,z2,z7,z4,z5]),(0,[z259,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z260,z5])]],
   [[(0,[z0,z1,z2,z7,z261,z4,z5]),(0,[z0,z1,z2,z7,z4,z148,z29]),(0,[z0,z262,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z263,z4,z5]),(0,[z0,z1,z2,z264,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z5,z265])],[(0,[z0,z1,z2,z7,z4,z5,z266]),(0,[z0,z1,z2,z7,z4,z5,z267]),(0,[z268,z0,z1,z2,z7,z4,z5])],[],[(0,[z1,z2,z28,z7,z4,z5,z29]),(0,[z269,z0,z1,z7,z4,z5,z29]),(0,[z0,z1,z2,z7,z270,z4,z5]),(0,[z0,z166,z1,z2,z35,z4,z5]),(0,[z0,z2,z7,z4,z148,z5,z30]),(0,[z0,z1,z73,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z271,z4,z5])],[(0,[z272,z0,z1,z2,z7,z4,z5]),(0,[z230,z1,z2,z7,z4,z5,z29]),(0,[z0,z1,z2,z7,z4,z273,z5]),(0,[z0,z1,z2,z35,z7,z4,z5]),(0,[z0,z70,z1,z274,z7,z4,z5])],[(0,[z0,z1,z275,z2,z7,z4,z5])],[(0,[z0,z1,z2,z7,z276,z4,z5]),(0,[z0,z1,z2,z277,z7,z4,z5]),(0,[z65,z0,z1,z2,z7,z4,z30]),(0,[z0,z1,z2,z61,z7,z58,z5])],[(0,[z0,z1,z2,z7,z278,z4,z5]),(0,[z0,z1,z2,z7,z279,z4,z5]),(0,[z0,z1,z2,z7,z4,z5,z280]),(0,[z0,z1,z2,z7,z4,z82,z5])]],
   [[(0,[z0,z1,z2,z7,z281,z4,z5]),(0,[z0,z1,z185,z2,z7,z4,z5]),(0,[z0,z1,z129,z2,z208,z4,z5]),(0,[z38,z0,z1,z2,z40,z4,z5]),(0,[z38,z0,z1,z2,z7,z4,z189])],[(0,[z0,z198,z1,z2,z7,z4,z5]),(0,[z282,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z283,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z284,z5]),(0,[z0,z1,z2,z7,z4,z82,z18])],[(0,[z0,z1,z2,z7,z133,z4,z5]),(0,[z0,z285,z1,z2,z7,z4,z5]),(0,[z0,z14,z176,z2,z7,z4,z5])],[(0,[z0,z286,z1,z2,z7,z4,z5]),(0,[z287,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z288,z5]),(0,[z0,z1,z2,z7,z4,z5,z289]),(0,[z0,z290,z1,z2,z7,z4,z5])],[(0,[z0,z291,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z292,z7,z4,z5])],[(0,[z0,z1,z2,z7,z4,z5,z293]),(0,[z0,z1,z92,z2,z7,z58,z5])],[(1,[z0,z1,z107,z7,z4,z5]),(0,[z0,z1,z294,z2,z7,z4,z5]),(0,[z0,z1,z2,z295,z7,z4,z5]),(0,[z0,z1,z2,z61,z7,z181,z5]),(0,[z0,z1,z2,z40,z4,z189,z5])],[(0,[z101,z0,z185,z2,z7,z4,z5]),(0,[z0,z1,z2,z165,z100,z4,z5]),(0,[z296,z0,z1,z2,z7,z4,z5]),(0,[z0,z241,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z297,z5])]],
   [[(0,[z184,z0,z1,z2,z7,z163,z5]),(0,[z298,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z148,z5]),(0,[z0,z1,z2,z7,z4,z5,z299]),(1,[z38,z0,z1,z2,z4,z39])],[],[(0,[z0,z1,z300,z2,z7,z4,z5]),(0,[z301,z0,z1,z2,z7,z4,z5])],[(0,[z0,z1,z2,z7,z302,z4,z5]),(0,[z0,z1,z2,z7,z303,z4,z5]),(0,[z0,z1,z2,z7,z4,z5,z304])],[(0,[z101,z0,z198,z2,z7,z4,z5]),(1,[z0,z1,z2,z7,z4,z135]),(0,[z0,z305,z1,z2,z7,z4,z5]),(0,[z0,z1,z24,z7,z4,z25,z5])],[(0,[z0,z306,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z307,z7,z4,z5]),(0,[z0,z1,z27,z7,z4,z25,z5]),(0,[z0,z1,z2,z7,z308,z4,z5]),(0,[z0,z1,z92,z2,z7,z181,z5]),(1,[z0,z1,z2,z7,z5,z309])],[(0,[z310,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z311,z7,z4,z5]),(0,[z0,z14,z1,z2,z31,z4,z5]),(0,[z0,z1,z2,z312,z7,z4,z5]),(0,[z0,z1,z2,z313,z7,z4,z5]),(0,[z0,z1,z274,z2,z7,z64,z5]),(0,[z0,z1,z2,z40,z7,z4,z189]),(0,[z0,z314,z1,z2,z7,z4,z5])],[(0,[z0,z1,z2,z7,z4,z315,z5]),(0,[z0,z1,z316,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z317,z4,z5]),(0,[z0,z1,z2,z7,z318,z4,z5]),(0,[z0,z1,z319,z2,z7,z4,z5])]],
   [[(0,[z0,z1,z2,z7,z4,z5,z320]),(0,[z0,z128,z1,z92,z2,z4,z5]),(0,[z65,z321,z1,z2,z7,z4,z5]),(0,[z0,z1,z92,z2,z61,z4,z5])],[(0,[z0,z1,z2,z7,z4,z322,z5]),(0,[z0,z1,z2,z7,z323,z4,z5]),(0,[z0,z1,z2,z7,z324,z4,z5])],[(0,[z0,z1,z2,z7,z4,z325,z5]),(0,[z113,z0,z1,z2,z7,z115,z5]),(0,[z0,z1,z2,z7,z4,z5,z326]),(0,[z327,z0,z1,z2,z7,z4,z5]),(0,[z0,z159,z1,z2,z7,z308,z5]),(0,[z0,z1,z2,z328,z7,z4,z5]),(0,[z0,z1,z2,z329,z7,z4,z5])],[(0,[z330,z0,z1,z2,z7,z4,z5]),(0,[z164,z1,z2,z165,z7,z4,z5]),(0,[z331,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z332,z5]),(0,[z0,z1,z2,z7,z4,z5,z333])],[(0,[z0,z1,z2,z7,z334,z4,z5]),(0,[z0,z1,z2,z7,z4,z335,z5])],[(0,[z336,z0,z1,z2,z7,z4,z5]),(0,[z0,z14,z1,z2,z7,z4,z5]),(0,[z0,z337,z1,z2,z7,z4,z5]),(0,[z0,z1,z208,z7,z188,z4,z5]),(0,[z0,z1,z2,z7,z4,z58,z5])],[(1,[z0,z1,z221,z7,z4,z5]),(1,[z54,z1,z28,z7,z4,z5]),(0,[z0,z1,z2,z7,z338,z4,z5]),(0,[z230,z134,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z339,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z5,z340]),(0,[z0,z1,z2,z7,z341,z4,z5]),(0,[z0,z1,z342,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z5,z343]),(1,[z0,z1,z92,z2,z156,z5])],[(0,[z1,z2,z7,z133,z4,z115,z5]),(0,[z0,z1,z2,z344,z7,z4,z5]),(0,[z0,z1,z2,z7,z345,z4,z5])]],
   [[(0,[z184,z0,z1,z2,z7,z4,z22]),(1,[z134,z1,z2,z7,z4,z59])],[(0,[z0,z1,z2,z346,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z5,z309])],[(0,[z0,z1,z2,z7,z4,z347,z5]),(0,[z0,z128,z1,z2,z165,z4,z5]),(0,[z0,z1,z2,z7,z4,z348,z5]),(0,[z349,z0,z1,z2,z7,z4,z5]),(1,[z0,z1,z73,z7,z4,z5])],[(0,[z124,z1,z125,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z5,z350]),(1,[z8,z0,z196,z7,z4,z5]),(0,[z0,z1,z2,z351,z7,z4,z5])],[(0,[z184,z0,z1,z2,z7,z325,z5]),(0,[z0,z1,z2,z352,z7,z4,z5]),(0,[z0,z15,z1,z2,z7,z4,z5]),(0,[z0,z353,z1,z2,z7,z4,z5])],[(0,[z54,z0,z1,z28,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z354,z5]),(0,[z0,z1,z355,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z5,z356])],[],[(0,[z357,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z358,z2,z7,z4,z5]),(0,[z0,z359,z1,z2,z7,z4,z5]),(0,[z360,z0,z1,z2,z7,z4,z5])]],
   [[(0,[z0,z1,z2,z7,z4,z5,z361]),(0,[z0,z1,z2,z61,z7,z114,z5]),(0,[z0,z362,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z36,z4,z5])],[],[(0,[z363,z0,z1,z2,z7,z4,z5]),(0,[z364,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z92,z2,z35,z4,z5]),(0,[z0,z1,z2,z365,z7,z4,z5]),(0,[z0,z366,z1,z2,z7,z4,z5]),(1,[z19,z0,z1,z2,z7,z20])],[(0,[z0,z1,z2,z7,z4,z5,z367]),(0,[z0,z223,z1,z2,z7,z4,z5]),(0,[z0,z14,z1,z2,z160,z4,z5]),(0,[z321,z0,z1,z2,z7,z4,z5])],[(0,[z0,z368,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z5,z369])],[(0,[z0,z370,z1,z2,z7,z4,z5]),(1,[z0,z1,z274,z7,z18,z5]),(0,[z0,z1,z371,z2,z7,z4,z5])],[(0,[z0,z1,z2,z7,z4,z372,z5]),(0,[z0,z1,z2,z7,z4,z115,z5]),(0,[z0,z1,z2,z7,z373,z4,z5]),(0,[z0,z1,z2,z7,z4,z374,z5])],[(0,[z19,z0,z1,z2,z7,z4,z59]),(0,[z375,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z92,z2,z7,z114,z5]),(0,[z86,z0,z1,z2,z7,z4,z30]),(0,[z0,z1,z376,z2,z7,z4,z5])]],
   [[(0,[z184,z1,z185,z2,z7,z4,z5]),(0,[z377,z0,z1,z2,z7,z4,z5]),(0,[z378,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z379,z4,z5])],[(0,[z0,z1,z2,z7,z380,z4,z5]),(0,[z0,z176,z2,z7,z4,z148,z5]),(0,[z381,z0,z1,z2,z7,z4,z5])],[(0,[z0,z1,z2,z7,z4,z382,z5]),(0,[z0,z1,z2,z7,z4,z383,z5]),(0,[z384,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z9,z5])],[(0,[z385,z0,z1,z2,z7,z4,z5])],[(0,[z0,z1,z2,z386,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z387,z5])],[(0,[z198,z1,z185,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z388,z4,z5])],[(0,[z389,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z390,z4,z5]),(0,[z0,z1,z391,z2,z7,z4,z5]),(0,[z0,z1,z2,z392,z7,z4,z5]),(0,[z0,z1,z2,z7,z393,z4,z5]),(0,[z19,z0,z14,z1,z2,z7,z5]),(0,[z0,z1,z2,z7,z394,z4,z5]),(0,[z0,z1,z2,z7,z57,z4,z20])],[(0,[z0,z196,z2,z27,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z395,z5]),(0,[z0,z396,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z397,z7,z4,z5]),(0,[z0,z1,z398,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z399,z5])]],
   [[(0,[z0,z1,z400,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z5,z401]),(0,[z0,z402,z1,z2,z7,z4,z5]),(0,[z113,z1,z2,z7,z4,z115,z5]),(0,[z65,z0,z1,z2,z7,z4,z148]),(0,[z65,z0,z1,z2,z7,z4,z71]),(0,[z0,z1,z2,z7,z4,z5,z403])],[(0,[z184,z0,z1,z2,z281,z4,z5]),(0,[z0,z1,z2,z404,z7,z4,z5]),(0,[z112,z1,z2,z7,z133,z4,z5]),(0,[z0,z1,z2,z7,z114,z4,z5]),(0,[z405,z0,z1,z2,z7,z4,z5])],[(0,[z124,z0,z1,z7,z4,z25,z5]),(0,[z0,z1,z2,z7,z4,z406,z5]),(0,[z407,z0,z1,z2,z7,z4,z5])],[(0,[z408,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z5,z409]),(0,[z410,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z411,z2,z7,z5,z39]),(0,[z0,z1,z412,z2,z7,z4,z5])],[(0,[z0,z1,z2,z165,z7,z4,z5]),(0,[z0,z413,z1,z2,z7,z4,z5]),(0,[z0,z1,z274,z2,z7,z4,z5])],[(1,[z0,z1,z2,z7,z163,z5]),(0,[z0,z2,z7,z114,z4,z181,z5]),(0,[z0,z1,z414,z2,z4,z18,z5])],[(0,[z0,z1,z2,z415,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z5,z135]),(0,[z0,z1,z2,z416,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z417,z5])],[(0,[z112,z0,z1,z2,z7,z115,z5]),(0,[z0,z1,z2,z7,z4,z418,z5])]],
   [[(0,[z0,z1,z419,z2,z7,z4,z5]),(0,[z0,z15,z2,z7,z4,z181,z5]),(0,[z0,z1,z2,z7,z4,z5,z420]),(0,[z0,z1,z2,z421,z7,z4,z5]),(1,[z0,z1,z2,z40,z4,z189])],[(0,[z422,z0,z1,z2,z7,z4,z5])],[(0,[z0,z1,z2,z7,z4,z423,z5]),(0,[z0,z1,z125,z27,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z424,z5]),(0,[z0,z1,z2,z7,z425,z4,z5])],[(0,[z426,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z100,z4,z5]),(0,[z0,z1,z129,z7,z4,z25,z5]),(0,[z0,z1,z2,z7,z4,z5,z427])],[(0,[z1,z2,z165,z7,z99,z4,z5]),(0,[z0,z1,z2,z7,z428,z4,z5]),(0,[z429,z0,z1,z2,z7,z4,z5])],[(0,[z0,z430,z1,z2,z7,z4,z5]),(0,[z0,z431,z1,z2,z7,z4,z5])],[(0,[z0,z176,z2,z7,z4,z181,z5]),(0,[z65,z0,z1,z208,z7,z4,z5])],[(0,[z54,z1,z2,z28,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z432,z5]),(0,[z0,z1,z433,z2,z7,z4,z5]),(0,[z434,z0,z1,z2,z7,z4,z5]),(0,[z435,z0,z1,z2,z7,z4,z5]),(0,[z19,z0,z436,z2,z7,z4,z5])]],
   [[(0,[z0,z1,z2,z7,z4,z5,z437]),(0,[z0,z1,z2,z7,z4,z438,z5]),(0,[z0,z1,z24,z2,z7,z57,z4])],[],[(1,[z113,z1,z2,z7,z115,z5]),(0,[z0,z1,z439,z2,z7,z4,z5]),(1,[z0,z1,z2,z7,z308,z5]),(1,[z0,z1,z2,z7,z5,z41])],[(1,[z0,z1,z7,z4,z5,z320]),(0,[z0,z1,z440,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z5,z441]),(0,[z0,z1,z2,z7,z4,z442,z5])],[(0,[z443,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z444,z5]),(0,[z445,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z92,z2,z4,z156,z5])],[(1,[z0,z1,z2,z7,z4,z22]),(0,[z0,z1,z2,z446,z7,z4,z5]),(0,[z0,z1,z2,z7,z133,z58,z5]),(0,[z0,z1,z447,z2,z7,z4,z5]),(0,[z448,z0,z1,z2,z7,z4,z5])],[(0,[z0,z1,z2,z7,z449,z4,z5]),(0,[z0,z1,z2,z7,z115,z58,z5])],[(0,[z0,z1,z2,z7,z4,z5,z450])]],
   [[(0,[z451,z0,z1,z2,z7,z4,z5]),(0,[z310,z1,z2,z7,z99,z4,z5]),(0,[z0,z1,z2,z7,z57,z4,z59]),(0,[z452,z0,z1,z2,z7,z4,z5])],[(1,[z0,z1,z2,z7,z325,z5]),(0,[z0,z1,z2,z7,z4,z59,z30]),(0,[z453,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z454,z2,z7,z4,z5])],[(0,[z65,z0,z1,z24,z7,z4,z5])],[(0,[z0,z1,z2,z7,z455,z4,z5]),(1,[z269,z0,z1,z7,z4,z5]),(0,[z456,z0,z1,z2,z7,z4,z5]),(0,[z457,z0,z1,z2,z7,z4,z5])],[(0,[z0,z1,z458,z2,z7,z4,z5]),(0,[z0,z459,z1,z2,z7,z4,z5])],[(0,[z0,z1,z2,z7,z133,z181,z5]),(0,[z0,z1,z2,z7,z460,z4,z5]),(0,[z0,z1,z461,z2,z7,z4,z5]),(0,[z462,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z24,z2,z7,z4,z30]),(0,[z0,z1,z2,z7,z4,z463,z5])],[(0,[z184,z0,z1,z2,z7,z4,z464]),(0,[z124,z54,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z115,z181,z5]),(1,[z0,z1,z2,z7,z4,z465]),(0,[z19,z0,z1,z2,z7,z4,z29]),(0,[z0,z223,z2,z27,z7,z4,z5]),(0,[z0,z466,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z467,z4,z5]),(0,[z0,z1,z2,z7,z4,z5,z41])],[(0,[z468,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z469,z2,z7,z4,z5]),(1,[z0,z241,z1,z2,z7,z5]),(0,[z0,z1,z2,z7,z470,z4,z5]),(0,[z0,z1,z2,z7,z4,z5,z471])]],
   [[(0,[z0,z1,z2,z472,z7,z4,z5]),(1,[z101,z198,z2,z7,z4,z5]),(0,[z164,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z188,z4,z5]),(0,[z0,z1,z274,z7,z4,z18,z5]),(0,[z19,z0,z1,z2,z7,z4,z20]),(0,[z0,z1,z2,z7,z4,z5,z473])],[(0,[z0,z1,z474,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z475,z4,z5]),(0,[z0,z1,z2,z7,z4,z5,z476]),(0,[z0,z1,z2,z477,z7,z4,z5])],[(0,[z0,z1,z7,z4,z5,z320,z29]),(0,[z0,z1,z2,z7,z4,z478,z5]),(0,[z0,z1,z2,z7,z4,z5,z479])],[],[(0,[z8,z0,z223,z2,z7,z4,z5]),(0,[z480,z0,z1,z2,z7,z4,z5]),(0,[z481,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z274,z2,z7,z18,z5]),(0,[z482,z0,z1,z2,z7,z4,z5])],[(0,[z101,z198,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z483,z7,z4,z5])],[(0,[z184,z0,z1,z472,z7,z4,z5]),(0,[z0,z1,z2,z7,z484,z4,z5]),(0,[z485,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z5,z486]),(0,[z230,z0,z1,z2,z7,z4,z59]),(0,[z487,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z488,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z5,z489]),(0,[z0,z1,z2,z7,z4,z5,z39])],[(0,[z184,z0,z1,z2,z490,z4,z5]),(0,[z0,z1,z2,z490,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z491,z5]),(0,[z134,z0,z1,z2,z7,z4,z59]),(1,[z492,z0,z1,z2,z7,z4])]],
   [[(0,[z0,z14,z1,z2,z7,z58,z5]),(0,[z0,z1,z2,z7,z4,z493,z5])],[(0,[z0,z1,z2,z494,z7,z4,z5]),(0,[z0,z1,z92,z2,z7,z36,z5])],[(0,[z124,z1,z2,z7,z4,z5,z29]),(0,[z0,z1,z2,z7,z4,z495,z5]),(0,[z0,z496,z1,z2,z7,z4,z5]),(0,[z0,z1,z92,z129,z2,z4,z5]),(0,[z497,z0,z1,z2,z7,z4,z5])],[(0,[z0,z1,z2,z498,z7,z4,z5]),(0,[z0,z1,z2,z7,z499,z4,z5]),(0,[z0,z1,z2,z7,z500,z4,z5]),(0,[z0,z1,z2,z208,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z501,z5])],[(0,[z164,z0,z1,z151,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z502,z5]),(0,[z0,z1,z2,z7,z503,z4,z5]),(0,[z0,z1,z2,z7,z504,z4,z5]),(0,[z0,z1,z436,z2,z7,z4,z5])],[(0,[z0,z128,z1,z208,z7,z4,z5])],[(1,[z0,z1,z2,z281,z4,z5]),(0,[z0,z505,z1,z2,z7,z4,z5]),(0,[z0,z128,z1,z2,z99,z4,z5]),(0,[z0,z1,z2,z7,z114,z133,z5]),(0,[z0,z1,z2,z7,z4,z506,z5]),(0,[z507,z0,z1,z2,z7,z4,z5])],[(0,[z0,z508,z1,z2,z7,z4,z5]),(0,[z0,z1,z509,z2,z7,z4,z5]),(0,[z0,z15,z1,z2,z7,z58,z5])]],
   [[(0,[z54,z0,z1,z125,z7,z4,z5]),(0,[z0,z14,z1,z2,z7,z181,z5]),(1,[z321,z1,z2,z7,z4,z5])],[(0,[z0,z1,z2,z7,z4,z5,z510])],[(0,[z511,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z512,z7,z4,z5]),(0,[z0,z2,z35,z7,z100,z4,z5]),(0,[z0,z1,z2,z513,z7,z4,z5])],[(0,[z0,z514,z1,z2,z7,z4,z5]),(1,[z0,z166,z2,z100,z4,z5]),(0,[z65,z0,z1,z2,z7,z4,z25]),(0,[z0,z1,z515,z2,z7,z4,z5]),(1,[z0,z1,z7,z4,z5,z403])],[(0,[z0,z1,z516,z2,z7,z4,z5]),(0,[z0,z1,z28,z208,z7,z4,z5]),(0,[z517,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z518,z5]),(1,[z0,z436,z2,z7,z4,z5])],[(0,[z0,z1,z2,z7,z519,z4,z5]),(0,[z0,z1,z2,z7,z4,z520,z5]),(0,[z0,z521,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z5,z522]),(0,[z0,z1,z7,z4,z5,z403,z39])],[(0,[z0,z523,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z524,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z525,z5])],[(0,[z526,z0,z1,z2,z7,z4,z5]),(0,[z527,z0,z1,z2,z7,z4,z5]),(0,[z0,z528,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z529,z7,z4,z5]),(0,[z0,z15,z1,z2,z7,z181,z5])]],
   [[(0,[z530,z0,z1,z2,z7,z4,z5]),(0,[z1,z125,z2,z28,z7,z4,z5]),(0,[z0,z1,z2,z7,z7,z4,z5]),(0,[z0,z1,z531,z2,z7,z4,z5]),(0,[z0,z1,z532,z2,z7,z4,z5])],[(1,[z0,z1,z2,z302,z4,z5]),(0,[z0,z1,z125,z208,z7,z4,z5]),(0,[z8,z0,z196,z2,z7,z4,z5]),(0,[z0,z159,z1,z2,z100,z4,z5]),(1,[z0,z14,z2,z7,z114,z5])],[(0,[z0,z1,z533,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z5,z534]),(0,[z535,z0,z1,z2,z7,z4,z5]),(0,[z65,z0,z1,z129,z7,z4,z5]),(0,[z0,z536,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z537,z4,z5]),(0,[z0,z1,z2,z7,z538,z4,z5])],[(0,[z539,z0,z1,z2,z7,z4,z5]),(0,[z112,z0,z1,z2,z7,z4,z465]),(0,[z0,z1,z2,z7,z540,z4,z5])],[(0,[z0,z1,z2,z541,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z542,z5])],[(0,[z0,z1,z2,z7,z543,z4,z5]),(0,[z0,z1,z544,z2,z7,z4,z5]),(1,[z310,z1,z2,z99,z4,z5]),(0,[z0,z1,z545,z2,z7,z4,z5]),(1,[z0,z176,z2,z7,z4,z148]),(0,[z19,z0,z1,z92,z2,z7,z5])],[(0,[z0,z166,z1,z2,z100,z4,z5]),(0,[z0,z1,z2,z546,z7,z4,z5]),(0,[z0,z1,z129,z7,z188,z4,z5]),(0,[z547,z0,z1,z2,z7,z4,z5])],[(0,[z0,z548,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z549,z5]),(0,[z0,z1,z2,z7,z57,z4,z29])]],
   [[(0,[z550,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z551,z5])],[(0,[z0,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z552,z2,z7,z4,z5]),(0,[z0,z1,z2,z553,z7,z4,z5]),(0,[z0,z554,z1,z2,z7,z4,z5]),(0,[z0,z1,z555,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z556,z5])],[(0,[z0,z1,z2,z557,z7,z4,z5]),(0,[z0,z558,z1,z2,z7,z4,z5])],[(0,[z54,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z559,z4,z5]),(0,[z0,z1,z560,z2,z7,z4,z5]),(0,[z0,z1,z2,z61,z36,z4,z5])],[(0,[z124,z134,z1,z2,z7,z4,z5]),(0,[z0,z561,z1,z2,z7,z4,z5]),(0,[z562,z0,z1,z2,z7,z4,z5])],[(0,[z0,z1,z2,z7,z4,z5,z563]),(0,[z0,z1,z564,z2,z7,z4,z5])],[(0,[z0,z1,z2,z7,z160,z4,z5]),(0,[z565,z0,z1,z2,z7,z4,z5]),(0,[z65,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z5,z566])],[(0,[z0,z1,z567,z2,z7,z4,z5]),(0,[z0,z1,z568,z2,z7,z4,z5]),(0,[z0,z1,z2,z569,z7,z4,z5]),(0,[z0,z1,z570,z2,z7,z4,z5]),(0,[z571,z0,z1,z2,z7,z4,z5])]],
   [[(0,[z0,z1,z2,z7,z5,z309,z30]),(0,[z0,z1,z2,z7,z4,z572,z5]),(0,[z19,z0,z366,z2,z7,z4,z5])],[(0,[z0,z1,z2,z7,z4,z5,z573]),(0,[z0,z1,z129,z2,z165,z4,z5]),(0,[z0,z1,z2,z7,z574,z4,z5]),(0,[z0,z223,z1,z27,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z575,z5]),(0,[z0,z1,z2,z7,z4,z5,z576]),(1,[z0,z1,z411,z2,z7,z5])],[(0,[z0,z1,z221,z2,z7,z4,z5]),(0,[z0,z577,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z578,z7,z4,z5]),(0,[z0,z1,z129,z2,z99,z4,z5]),(0,[z0,z579,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z580,z5]),(0,[z0,z1,z2,z7,z4,z581,z5]),(0,[z0,z1,z2,z7,z582,z4,z5]),(0,[z0,z14,z1,z2,z7,z114,z5]),(0,[z0,z1,z2,z583,z7,z4,z5])],[(1,[z0,z1,z2,z7,z4,z464]),(0,[z0,z1,z584,z2,z7,z4,z5]),(0,[z65,z124,z0,z1,z7,z4,z5]),(0,[z113,z0,z1,z2,z7,z4,z5]),(0,[z585,z0,z1,z2,z7,z4,z5])],[],[(0,[z230,z0,z1,z2,z7,z4,z29]),(1,[z0,z1,z180,z7,z4,z5]),(0,[z0,z128,z1,z2,z188,z4,z5]),(0,[z0,z586,z1,z2,z7,z4,z5])],[(0,[z134,z0,z1,z2,z7,z4,z29]),(0,[z587,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z588,z2,z7,z4,z5]),(0,[z0,z1,z589,z2,z7,z4,z5]),(0,[z590,z0,z1,z2,z7,z4,z5])],[(0,[z0,z591,z1,z2,z7,z4,z5]),(0,[z592,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z593,z7,z4,z5]),(0,[z594,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z595,z5]),(0,[z0,z1,z24,z2,z7,z4,z148]),(0,[z0,z1,z24,z2,z7,z4,z71]),(0,[z0,z1,z2,z7,z57,z4,z5])]],
   [[(0,[z0,z1,z2,z28,z7,z4,z5]),(0,[z0,z1,z2,z596,z7,z4,z5]),(0,[z597,z0,z1,z2,z7,z4,z5])],[(0,[z0,z1,z2,z35,z165,z4,z5]),(0,[z112,z0,z1,z2,z7,z4,z147]),(0,[z0,z598,z1,z2,z7,z4,z5]),(0,[z0,z1,z599,z2,z7,z4,z5]),(0,[z0,z15,z1,z2,z7,z114,z5]),(0,[z0,z1,z2,z36,z4,z156,z5])],[(0,[z0,z1,z2,z35,z99,z4,z5]),(0,[z600,z0,z1,z2,z7,z4,z5])],[(1,[z0,z1,z472,z7,z4,z5]),(0,[z601,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z5,z602]),(0,[z19,z0,z1,z2,z61,z7,z5]),(0,[z19,z0,z1,z2,z7,z57,z5])],[(1,[z0,z1,z2,z490,z4,z5]),(1,[z184,z185,z2,z7,z4,z5]),(0,[z0,z603,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z604,z5]),(1,[z65,z0,z1,z7,z4,z71]),(0,[z0,z1,z2,z7,z605,z4,z5]),(0,[z38,z0,z1,z2,z7,z4,z5])],[(0,[z0,z1,z2,z7,z4,z464,z5]),(0,[z0,z1,z2,z606,z7,z4,z5]),(0,[z0,z1,z607,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z17,z4,z5])],[(1,[z0,z1,z2,z7,z608,z5]),(0,[z609,z0,z1,z2,z7,z4,z5])],[(0,[z0,z1,z2,z3,z7,z4,z5]),(1,[z0,z1,z2,z7,z574,z5]),(0,[z8,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z5,z610]),(1,[z0,z1,z24,z7,z4,z25])]],
   [[(0,[z611,z0,z1,z2,z7,z4,z5]),(0,[z0,z14,z2,z7,z114,z4,z5]),(0,[z0,z612,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z613,z4,z5])],[(0,[z0,z1,z2,z7,z4,z5,z614]),(0,[z615,z0,z1,z2,z7,z4,z5]),(0,[z19,z0,z1,z24,z2,z7,z4])],[(0,[z0,z1,z616,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z617,z4,z5])],[(0,[z0,z1,z618,z2,z7,z4,z5]),(0,[z0,z619,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z620,z5])],[(0,[z621,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z5,z622]),(0,[z0,z223,z1,z196,z7,z4,z5]),(0,[z19,z0,z15,z1,z2,z7,z5]),(0,[z86,z0,z176,z2,z7,z4,z5]),(0,[z623,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z624,z5]),(0,[z0,z1,z625,z2,z7,z4,z5])],[(0,[z0,z1,z196,z28,z7,z4,z5]),(0,[z0,z1,z196,z125,z7,z4,z5]),(0,[z230,z0,z1,z2,z7,z4,z5]),(0,[z626,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z5,z627]),(0,[z0,z1,z2,z7,z4,z628,z5]),(0,[z0,z1,z2,z180,z7,z4,z5])],[(0,[z0,z1,z2,z629,z7,z4,z5]),(0,[z124,z0,z1,z2,z302,z4,z5]),(0,[z0,z1,z630,z2,z7,z4,z5])],[(0,[z0,z631,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z4,z5]),(0,[z0,z1,z2,z7,z4,z5,z632]),(0,[z0,z633,z1,z2,z7,z4,z5]),(0,[z634,z0,z1,z2,z7,z4,z5])]],
   [[(0,[z164,z0,z1,z107,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z635,z5]),(0,[z0,z128,z1,z2,z36,z4,z5]),(0,[z0,z1,z2,z636,z7,z4,z5])],[(0,[z0,z1,z2,z7,z637,z4,z5]),(0,[z0,z1,z2,z7,z58,z5,z20])],[(0,[z134,z0,z1,z2,z7,z574,z5]),(0,[z0,z1,z2,z7,z4,z608,z5]),(0,[z0,z1,z2,z40,z7,z4,z5]),(0,[z0,z1,z2,z4,z189,z5,z39]),(0,[z638,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z5,z639])],[(0,[z640,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z2,z7,z4,z5]),(0,[z310,z0,z1,z2,z165,z4,z5])],[(0,[z310,z0,z1,z2,z99,z4,z5]),(0,[z0,z1,z2,z641,z7,z4,z5]),(0,[z0,z642,z1,z2,z7,z4,z5])],[(0,[z124,z0,z1,z28,z7,z4,z5]),(0,[z0,z1,z92,z2,z100,z4,z5]),(0,[z0,z1,z2,z61,z7,z36,z5])],[(0,[z643,z0,z1,z2,z7,z4,z5]),(0,[z0,z159,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z644,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z645,z5]),(0,[z0,z1,z2,z7,z4,z646,z5])],[(0,[z0,z1,z647,z2,z7,z4,z5]),(1,[z0,z1,z414,z2,z4,z5])]],
   [[(0,[z648,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z465,z5]),(0,[z0,z1,z2,z7,z4,z649,z5]),(0,[z0,z650,z1,z2,z7,z4,z5]),(0,[z0,z651,z1,z2,z7,z4,z5])],[(0,[z184,z0,z1,z2,z7,z4,z5]),(0,[z652,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z653,z4,z5]),(0,[z0,z654,z1,z2,z7,z4,z5]),(0,[z0,z159,z1,z2,z7,z608,z5]),(0,[z0,z1,z2,z7,z4,z655,z5]),(0,[z0,z656,z1,z2,z7,z4,z5])],[(0,[z657,z0,z1,z2,z7,z4,z5])],[(0,[z0,z166,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z658,z4,z5]),(0,[z0,z1,z659,z2,z7,z4,z5])],[(0,[z660,z0,z1,z2,z7,z4,z5]),(0,[z86,z0,z1,z2,z7,z4,z148]),(0,[z86,z0,z2,z7,z4,z5,z30]),(0,[z0,z1,z2,z661,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z5,z662])],[(0,[z134,z1,z2,z28,z7,z4,z5]),(0,[z0,z1,z2,z7,z663,z4,z5]),(0,[z0,z664,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z665,z7,z4,z5]),(1,[z0,z366,z2,z7,z4,z5])],[(0,[z0,z1,z129,z28,z7,z4,z5]),(0,[z0,z666,z1,z2,z7,z4,z5])],[(0,[z0,z667,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z151,z7,z4,z5]),(0,[z86,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z208,z7,z4,z25,z5]),(0,[z0,z1,z2,z7,z64,z4,z5]),(0,[z0,z1,z2,z7,z4,z5,z668])]],
   [[(0,[z0,z669,z1,z2,z7,z4,z5]),(0,[z112,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z196,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z5,z670])],[(0,[z0,z1,z2,z7,z671,z4,z5]),(0,[z672,z0,z1,z2,z7,z4,z5]),(0,[z19,z0,z1,z2,z7,z4,z5])],[(0,[z0,z1,z2,z7,z4,z673,z5]),(0,[z0,z1,z2,z7,z674,z4,z5]),(1,[z0,z1,z129,z188,z4,z5])],[(0,[z0,z1,z2,z7,z4,z675,z5]),(0,[z0,z1,z2,z7,z676,z4,z5]),(0,[z0,z1,z2,z7,z677,z4,z5]),(0,[z0,z678,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z679,z5]),(0,[z492,z0,z1,z2,z7,z4,z5])],[(0,[z0,z1,z2,z7,z680,z4,z5]),(0,[z0,z681,z1,z2,z7,z4,z5])],[(0,[z682,z0,z1,z2,z7,z4,z5]),(1,[z0,z128,z1,z208,z4,z5]),(0,[z492,z0,z1,z2,z7,z4,z18])],[(1,[z164,z1,z2,z165,z4,z5]),(0,[z0,z683,z1,z2,z7,z4,z5])],[(1,[z0,z1,z2,z7,z4,z147]),(0,[z0,z53,z1,z2,z7,z4,z5]),(0,[z0,z1,z684,z2,z7,z4,z5])]],
   [[(0,[z113,z0,z1,z2,z7,z133,z5]),(0,[z685,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z686,z4,z5])],[(0,[z0,z1,z2,z7,z4,z687,z5]),(0,[z688,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z5,z689]),(0,[z0,z1,z2,z7,z4,z5,z690])],[(0,[z691,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z692,z4,z5]),(0,[z0,z176,z1,z2,z7,z4,z30]),(0,[z0,z1,z693,z2,z7,z4,z5])],[(0,[z694,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z5,z695]),(0,[z0,z166,z159,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z696,z5]),(0,[z0,z1,z414,z2,z7,z4,z5])],[(0,[z310,z164,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z697,z4,z5]),(0,[z0,z1,z2,z7,z4,z5,z698]),(0,[z0,z1,z129,z2,z36,z4,z5]),(0,[z65,z53,z1,z2,z7,z4,z5])],[(0,[z0,z1,z2,z7,z4,z5,z699]),(1,[z0,z15,z2,z7,z181,z5]),(0,[z0,z700,z1,z2,z7,z4,z5])],[(0,[z0,z1,z2,z701,z7,z4,z5]),(0,[z269,z0,z1,z2,z7,z4,z5]),(0,[z702,z0,z1,z2,z7,z4,z5])],[(0,[z703,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z704,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z705,z4,z5]),(0,[z0,z1,z2,z7,z4,z706,z5]),(0,[z0,z1,z411,z2,z7,z4,z5])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z7,z707,z5]),(0,[z269,z1,z28,z7,z4,z5]),(0,[z0,z708,z1,z7,z4,z5]),(0,[z709,z1,z2,z7,z4,z5]),(0,[z0,z1,z7,z4,z5,z710]),(0,[z0,z1,z7,z64,z711,z5]),(0,[z0,z436,z24,z2,z7,z4]),(0,[z38,z0,z1,z2,z41,z39])],[(0,[z0,z1,z2,z281,z163,z5]),(0,[z112,z1,z2,z7,z133,z5]),(0,[z712,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z31,z181,z5]),(0,[z0,z1,z24,z7,z4,z620]),(0,[z0,z713,z2,z7,z4,z5]),(0,[z0,z1,z2,z714,z4,z5])],[(0,[z0,z715,z1,z2,z4,z5]),(0,[z0,z1,z2,z716,z4,z5]),(0,[z0,z1,z107,z165,z4,z5]),(0,[z0,z1,z92,z2,z673,z5]),(0,[z0,z2,z7,z717,z4,z5]),(0,[z0,z718,z2,z7,z4,z5])],[(0,[z0,z1,z719,z7,z4,z5]),(0,[z0,z1,z107,z99,z4,z5]),(0,[z1,z2,z7,z4,z59,z720]),(0,[z0,z241,z1,z2,z7,z5]),(0,[z0,z241,z1,z24,z2,z7]),(0,[z721,z1,z2,z7,z4,z5])]],
   [[(0,[z101,z198,z2,z7,z4,z5]),(0,[z0,z1,z722,z7,z4,z5]),(0,[z0,z1,z2,z7,z723,z5]),(0,[z0,z1,z2,z7,z724,z5]),(0,[z1,z125,z725,z7,z4,z5]),(0,[z0,z1,z2,z7,z5,z309])],[(0,[z0,z1,z2,z7,z4,z726]),(0,[z0,z1,z2,z727,z4,z5]),(0,[z0,z1,z2,z728,z4,z5]),(0,[z0,z1,z729,z7,z4,z5]),(0,[z0,z1,z414,z274,z18,z5]),(0,[z0,z1,z730,z7,z4,z5])],[(0,[z0,z1,z151,z7,z4,z5]),(0,[z0,z1,z2,z731,z4,z5]),(0,[z124,z1,z7,z4,z5,z97]),(0,[z0,z223,z732,z7,z4,z5]),(0,[z53,z1,z27,z7,z4,z5]),(0,[z0,z2,z7,z4,z148,z733]),(0,[z0,z1,z2,z7,z5,z734]),(0,[z0,z735,z2,z7,z4,z5])],[(0,[z0,z1,z2,z7,z736,z5]),(0,[z269,z0,z1,z7,z4,z30]),(0,[z0,z70,z1,z7,z711,z5]),(0,[z19,z0,z366,z2,z7,z20])]],
   [[(0,[z184,z185,z221,z7,z4,z5]),(0,[z0,z1,z7,z4,z5,z737]),(0,[z0,z1,z2,z7,z738,z5]),(0,[z0,z436,z2,z7,z4,z29]),(0,[z0,z1,z2,z160,z4,z5]),(0,[z0,z739,z2,z7,z4,z5])],[(0,[z101,z740,z2,z7,z4,z5]),(0,[z0,z1,z741,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z742]),(0,[z1,z2,z7,z4,z5,z743]),(1,[z0,z2,z7,z717,z5]),(0,[z0,z1,z92,z2,z525,z5]),(0,[z0,z1,z2,z61,z5,z473]),(0,[z0,z1,z2,z7,z57,z744])],[(0,[z0,z1,z2,z7,z745,z5])],[(0,[z0,z1,z2,z7,z5,z746]),(0,[z0,z1,z747,z2,z7,z5]),(0,[z0,z241,z436,z2,z7,z5]),(0,[z0,z1,z748,z7,z4,z5]),(0,[z749,z1,z2,z7,z4,z5]),(0,[z750,z1,z2,z7,z4,z5])]],
   [[(0,[z0,z1,z221,z7,z4,z22]),(0,[z0,z751,z2,z7,z4,z5]),(0,[z0,z1,z196,z7,z4,z9]),(0,[z0,z1,z2,z7,z4,z752]),(0,[z0,z1,z7,z711,z18,z5])],[(1,[z740,z2,z7,z4,z5]),(0,[z753,z1,z2,z7,z4,z5]),(0,[z0,z1,z92,z2,z156,z5]),(0,[z0,z1,z73,z7,z5,z41])],[(0,[z0,z87,z27,z7,z4,z5]),(0,[z754,z1,z2,z7,z4,z5])],[(0,[z0,z1,z2,z7,z755,z5]),(1,[z1,z2,z727,z4,z5]),(0,[z1,z2,z727,z99,z4,z5]),(0,[z0,z1,z2,z7,z756,z5]),(0,[z0,z732,z2,z7,z4,z5]),(0,[z0,z14,z436,z2,z7,z5])]],
   [[(0,[z0,z1,z2,z7,z757,z5]),(0,[z0,z1,z2,z7,z4,z758]),(0,[z0,z1,z2,z7,z5,z759]),(0,[z0,z760,z2,z7,z4,z5]),(0,[z19,z0,z1,z2,z7,z662])],[(0,[z0,z1,z2,z761,z4,z5]),(0,[z0,z1,z2,z7,z4,z762]),(0,[z65,z0,z1,z7,z4,z289]),(0,[z0,z1,z73,z7,z4,z5]),(0,[z763,z1,z2,z7,z4,z5]),(0,[z38,z0,z1,z4,z403,z39]),(0,[z0,z1,z411,z73,z7,z5]),(0,[z19,z0,z1,z2,z7,z744])],[(0,[z0,z1,z2,z281,z4,z5]),(0,[z0,z1,z2,z4,z5,z764]),(0,[z8,z0,z196,z7,z4,z5]),(0,[z0,z359,z196,z7,z4,z5]),(0,[z765,z0,z1,z2,z7,z4]),(0,[z0,z1,z2,z7,z4,z766]),(1,[z0,z1,z2,z7,z744])],[(0,[z1,z740,z2,z7,z4,z5]),(0,[z565,z1,z28,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z767]),(0,[z611,z1,z2,z99,z4,z5]),(0,[z0,z1,z2,z7,z318,z58]),(0,[z590,z0,z2,z7,z4,z30])]],
   [[(0,[z321,z1,z2,z7,z4,z5]),(0,[z0,z1,z125,z3,z4,z5]),(0,[z634,z1,z2,z7,z4,z59]),(0,[z0,z1,z2,z7,z4,z768]),(0,[z0,z2,z7,z769,z4,z5]),(0,[z0,z1,z129,z130,z4,z5]),(0,[z770,z1,z2,z7,z4,z5]),(0,[z0,z1,z7,z4,z25,z441])],[(0,[z0,z1,z771,z7,z4,z5]),(0,[z0,z1,z2,z281,z325,z5]),(0,[z0,z1,z2,z772,z4,z5]),(0,[z0,z773,z2,z7,z4,z5]),(0,[z0,z2,z7,z4,z5,z774]),(0,[z585,z1,z2,z7,z4,z29])],[(0,[z0,z1,z2,z7,z4,z775]),(0,[z0,z1,z7,z4,z5,z776]),(0,[z0,z173,z2,z7,z181,z5]),(0,[z65,z321,z1,z7,z4,z71]),(0,[z0,z1,z411,z7,z5,z403])],[(0,[z0,z1,z2,z7,z5,z777]),(0,[z0,z1,z778,z2,z4,z5]),(0,[z0,z1,z2,z7,z4,z779]),(0,[z780,z1,z2,z7,z4,z5]),(0,[z0,z166,z2,z100,z4,z5]),(0,[z0,z1,z2,z7,z4,z781]),(0,[z0,z1,z7,z4,z5,z403]),(1,[z0,z1,z7,z4,z782]),(0,[z0,z1,z2,z7,z57,z58])]],
   [[(0,[z0,z1,z2,z7,z4,z783]),(0,[z0,z784,z1,z2,z7,z5]),(0,[z112,z1,z2,z7,z785,z5]),(0,[z0,z436,z2,z7,z4,z5])],[(0,[z0,z1,z2,z7,z115,z465]),(0,[z0,z1,z7,z4,z786,z5]),(0,[z638,z1,z2,z7,z4,z59]),(0,[z53,z1,z196,z7,z4,z5]),(0,[z0,z586,z2,z35,z4,z5]),(0,[z0,z14,z2,z7,z116,z5]),(0,[z787,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z788])],[(0,[z0,z176,z77,z7,z4,z148])],[(0,[z0,z196,z732,z7,z4,z5]),(0,[z0,z1,z2,z31,z114,z5]),(1,[z0,z2,z7,z4,z733]),(0,[z0,z176,z180,z7,z4,z148]),(0,[z0,z128,z1,z4,z417,z5]),(0,[z0,z789,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z57,z354]),(0,[z19,z0,z436,z2,z7,z20])]],
   [[(0,[z457,z1,z125,z7,z4,z5]),(0,[z0,z1,z2,z790,z4,z5])],[(0,[z0,z1,z2,z302,z4,z5]),(0,[z164,z1,z2,z165,z4,z5]),(0,[z0,z223,z27,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z791]),(0,[z0,z2,z7,z114,z717,z5]),(0,[z492,z0,z1,z2,z17,z4]),(0,[z0,z1,z792,z2,z4,z5]),(0,[z0,z793,z2,z7,z4,z5])],[(0,[z794,z1,z2,z7,z4,z5])],[(0,[z0,z1,z2,z7,z795,z5]),(0,[z796,z1,z2,z7,z4,z5])]],
   [[(0,[z0,z1,z2,z7,z4,z797]),(0,[z1,z725,z28,z7,z4,z5]),(0,[z0,z798,z2,z7,z4,z5]),(0,[z230,z1,z2,z7,z4,z29]),(0,[z0,z1,z2,z7,z799,z5]),(0,[z0,z1,z7,z4,z800,z5]),(0,[z38,z0,z1,z73,z4,z39])],[(0,[z19,z0,z1,z2,z7,z534]),(0,[z0,z1,z801,z2,z4,z5]),(0,[z0,z1,z802,z7,z4,z5]),(0,[z0,z176,z2,z7,z4,z148]),(0,[z0,z1,z2,z7,z4,z782])],[(0,[z0,z1,z2,z803,z4,z5]),(0,[z0,z1,z2,z804,z4,z5]),(0,[z124,z269,z1,z7,z4,z5]),(0,[z0,z1,z805,z7,z4,z5]),(0,[z0,z14,z241,z2,z7,z5]),(0,[z0,z1,z2,z61,z36,z5]),(0,[z0,z1,z7,z5,z403,z41])],[(0,[z0,z1,z3,z4,z25,z5]),(0,[z164,z1,z2,z727,z4,z5]),(0,[z0,z806,z2,z7,z4,z5]),(0,[z113,z1,z2,z7,z785,z5]),(0,[z448,z1,z2,z7,z133,z5]),(0,[z0,z1,z2,z7,z4,z9]),(0,[z0,z1,z2,z7,z4,z807]),(0,[z0,z1,z2,z7,z808,z5]),(0,[z809,z1,z2,z7,z4,z5])]],
   [[(0,[z0,z1,z2,z7,z810,z5]),(0,[z0,z1,z2,z7,z811,z5]),(0,[z0,z2,z7,z812,z4,z5]),(0,[z813,z0,z1,z2,z7,z4]),(0,[z0,z1,z2,z7,z4,z814]),(0,[z65,z0,z1,z7,z4,z340]),(0,[z53,z1,z129,z7,z4,z5]),(0,[z0,z1,z92,z2,z815,z5]),(0,[z0,z1,z2,z36,z815,z5])],[(0,[z0,z1,z816,z7,z4,z5]),(0,[z0,z1,z2,z817,z4,z5]),(0,[z0,z1,z2,z61,z393,z5]),(0,[z0,z1,z129,z748,z4,z5])],[(0,[z0,z1,z472,z7,z163,z5]),(0,[z310,z1,z2,z727,z4,z5]),(0,[z0,z359,z2,z7,z4,z148]),(0,[z0,z1,z2,z7,z4,z818])],[(0,[z0,z1,z2,z7,z4,z819]),(0,[z124,z1,z294,z7,z4,z5]),(0,[z0,z1,z2,z7,z820,z5]),(0,[z65,z53,z1,z7,z4,z71]),(0,[z0,z436,z92,z2,z7,z5])]],
   [[(0,[z821,z0,z1,z2,z7,z4]),(0,[z0,z1,z2,z7,z822,z4])],[(0,[z0,z1,z2,z7,z823,z5]),(0,[z0,z824,z1,z2,z7,z5]),(0,[z164,z1,z151,z165,z4,z5]),(0,[z0,z1,z2,z7,z4,z825]),(0,[z0,z176,z2,z7,z4,z733]),(0,[z0,z1,z2,z826,z4,z5]),(0,[z0,z1,z827,z7,z4,z5])],[(0,[z0,z1,z2,z828,z4,z5]),(0,[z0,z1,z829,z7,z4,z5]),(0,[z0,z15,z436,z2,z7,z5]),(0,[z0,z1,z92,z2,z297,z5])],[(0,[z0,z1,z2,z7,z163,z22]),(0,[z65,z0,z1,z3,z4,z5]),(0,[z124,z53,z1,z7,z4,z5]),(0,[z600,z1,z2,z165,z4,z5]),(0,[z269,z53,z1,z7,z4,z5]),(0,[z0,z1,z2,z830,z4,z5]),(0,[z0,z1,z2,z7,z58,z194]),(0,[z0,z14,z2,z7,z717,z5]),(0,[z0,z1,z2,z7,z831,z5]),(0,[z53,z1,z2,z7,z57,z4]),(0,[z0,z1,z7,z4,z782,z71])]],
   [[(0,[z0,z1,z2,z7,z832,z5]),(0,[z0,z1,z2,z7,z833,z5])],[(0,[z0,z1,z2,z834,z4,z5]),(0,[z124,z1,z125,z3,z4,z5]),(0,[z0,z2,z7,z835,z4,z5]),(0,[z0,z836,z2,z7,z4,z5]),(0,[z0,z1,z2,z769,z4,z5]),(0,[z0,z1,z77,z7,z4,z148]),(0,[z0,z837,z2,z7,z4,z5])],[(0,[z0,z1,z7,z838,z4,z5]),(0,[z0,z1,z2,z839,z4,z5]),(0,[z0,z1,z840,z7,z4,z5])],[(0,[z0,z1,z472,z7,z4,z464]),(0,[z0,z436,z2,z7,z115,z5]),(0,[z0,z1,z2,z4,z5,z841]),(0,[z86,z0,z2,z7,z4,z733]),(0,[z0,z1,z2,z40,z4,z189])]],
   [[(0,[z0,z1,z2,z7,z842,z5]),(0,[z0,z1,z2,z490,z4,z464]),(0,[z184,z185,z2,z7,z4,z464]),(0,[z53,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z843,z4,z5]),(0,[z124,z1,z725,z7,z4,z5]),(0,[z0,z1,z2,z248,z36,z5])],[(0,[z703,z0,z196,z7,z4,z5]),(0,[z0,z1,z844,z7,z4,z5]),(0,[z1,z2,z7,z4,z845,z5]),(0,[z846,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z748,z4,z5])],[(0,[z1,z2,z7,z4,z720,z29]),(0,[z1,z2,z7,z4,z5,z720]),(0,[z0,z1,z2,z847,z4,z5]),(0,[z848,z0,z1,z2,z7,z4]),(0,[z0,z1,z849,z7,z4,z5]),(0,[z0,z1,z2,z7,z850,z5]),(0,[z65,z0,z1,z513,z7,z4]),(0,[z0,z1,z851,z7,z4,z5])],[(0,[z1,z725,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z720]),(0,[z0,z1,z2,z7,z852,z5]),(1,[z0,z1,z2,z4,z788])]],
   [[(0,[z0,z1,z2,z7,z853,z5])],[(0,[z0,z1,z2,z854,z4,z5]),(0,[z0,z855,z2,z7,z4,z5]),(0,[z0,z1,z247,z7,z4,z25]),(0,[z856,z1,z2,z7,z4,z5]),(0,[z857,z0,z1,z2,z7,z4]),(0,[z53,z1,z208,z7,z4,z5])],[(0,[z0,z1,z858,z7,z4,z5]),(0,[z0,z1,z2,z31,z4,z5]),(0,[z0,z1,z208,z748,z4,z5])],[(0,[z0,z1,z472,z7,z4,z5]),(0,[z0,z859,z2,z7,z4,z5]),(0,[z19,z0,z1,z2,z7,z96]),(0,[z0,z1,z2,z7,z711,z5]),(0,[z38,z0,z1,z411,z2,z39])]],
   [[(0,[z0,z1,z472,z490,z4,z5]),(0,[z184,z185,z472,z7,z4,z5]),(0,[z0,z1,z2,z860,z4,z5]),(0,[z0,z1,z2,z7,z861,z5]),(0,[z0,z1,z2,z7,z862,z5]),(0,[z0,z1,z863,z7,z4,z5]),(0,[z0,z1,z2,z864,z4,z5]),(0,[z53,z1,z2,z7,z4,z30]),(0,[z865,z0,z1,z2,z7,z4]),(0,[z0,z1,z24,z7,z4,z782])],[(0,[z0,z1,z221,z7,z163,z5]),(0,[z184,z185,z2,z490,z4,z5]),(0,[z0,z1,z866,z7,z4,z5]),(0,[z269,z0,z1,z7,z4,z148]),(0,[z0,z1,z732,z7,z4,z5]),(0,[z65,z0,z1,z7,z4,z695]),(0,[z0,z1,z274,z17,z18,z5])],[(0,[z0,z1,z472,z7,z325,z5]),(0,[z0,z1,z867,z7,z4,z5])],[(0,[z65,z0,z1,z7,z4,z699]),(0,[z8,z0,z196,z7,z4,z9]),(0,[z0,z14,z2,z7,z5,z639]),(0,[z0,z1,z868,z2,z7,z5]),(0,[z0,z1,z2,z7,z869,z5]),(0,[z0,z1,z24,z7,z4,z25]),(0,[z0,z1,z2,z7,z744,z20])]],
   [[(0,[z0,z1,z2,z7,z4,z22]),(0,[z0,z1,z2,z7,z870,z5]),(0,[z134,z1,z2,z7,z4,z720]),(0,[z0,z1,z2,z7,z4,z871]),(0,[z0,z1,z872,z7,z4,z5]),(0,[z873,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z733])],[(0,[z0,z1,z2,z7,z4,z874]),(0,[z0,z1,z875,z7,z4,z5]),(0,[z0,z83,z27,z7,z4,z5]),(0,[z0,z2,z876,z7,z4,z5]),(0,[z0,z1,z7,z4,z5,z877]),(0,[z0,z878,z2,z7,z4,z5]),(0,[z269,z0,z1,z7,z57,z4]),(0,[z0,z1,z2,z879,z4,z5]),(0,[z0,z1,z2,z7,z880,z5]),(0,[z0,z159,z2,z769,z4,z5]),(0,[z0,z176,z2,z7,z4,z85]),(0,[z881,z1,z2,z7,z4,z5]),(0,[z0,z436,z2,z61,z7,z5])],[(0,[z0,z1,z2,z7,z785,z5]),(0,[z0,z1,z2,z7,z882,z5]),(0,[z0,z1,z2,z7,z883,z5])],[(0,[z0,z1,z2,z7,z325,z22]),(0,[z0,z1,z2,z884,z4,z5]),(0,[z0,z1,z2,z7,z885,z5]),(0,[z0,z1,z2,z7,z886,z5]),(0,[z0,z1,z887,z7,z4,z5])]],
   [[(0,[z0,z1,z888,z2,z4,z5]),(0,[z0,z1,z129,z425,z4,z5]),(0,[z0,z1,z2,z7,z4,z135]),(0,[z0,z889,z2,z7,z4,z5]),(0,[z19,z0,z1,z2,z7,z518])],[(0,[z0,z121,z2,z100,z4,z5]),(0,[z65,z0,z1,z7,z4,z409]),(0,[z0,z1,z890,z7,z4,z5]),(0,[z19,z0,z1,z2,z7,z136]),(0,[z0,z1,z891,z2,z7,z5]),(0,[z0,z128,z1,z748,z4,z5]),(0,[z0,z1,z7,z4,z5,z782]),(0,[z892,z1,z2,z7,z4,z5])],[(0,[z184,z740,z2,z7,z4,z5]),(0,[z134,z1,z2,z7,z4,z138])],[(0,[z0,z1,z2,z7,z4,z893]),(0,[z124,z1,z125,z7,z4,z5]),(0,[z0,z579,z2,z7,z181,z5]),(0,[z0,z1,z894,z7,z4,z5]),(0,[z0,z1,z2,z7,z895,z5]),(1,[z0,z1,z2,z815,z5])]],
   [[(0,[z0,z2,z7,z4,z5,z896]),(0,[z0,z1,z2,z7,z897,z5]),(0,[z0,z1,z898,z7,z4,z5]),(0,[z11,z1,z2,z7,z115,z5]),(0,[z0,z1,z899,z7,z4,z5]),(0,[z0,z2,z7,z4,z733,z30])],[(0,[z0,z1,z2,z7,z4,z900]),(0,[z0,z1,z2,z7,z4,z465]),(0,[z0,z436,z2,z7,z133,z5]),(0,[z0,z1,z414,z2,z4,z82]),(0,[z0,z1,z2,z7,z5,z744])],[(0,[z0,z740,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z901]),(0,[z0,z1,z7,z4,z5,z902]),(0,[z0,z15,z2,z7,z717,z5])],[(0,[z0,z1,z2,z281,z4,z464]),(0,[z0,z1,z903,z7,z4,z5]),(0,[z0,z1,z904,z7,z4,z5]),(0,[z19,z0,z1,z2,z7,z154]),(0,[z0,z1,z2,z7,z574,z59]),(0,[z0,z1,z905,z2,z7,z5])]],
   [[(0,[z1,z2,z165,z727,z4,z5]),(1,[z1,z2,z7,z785,z5]),(0,[z134,z1,z2,z7,z88,z59]),(0,[z906,z1,z2,z7,z4,z5]),(0,[z907,z1,z2,z7,z4,z5]),(0,[z0,z1,z908,z7,z4,z5]),(0,[z0,z1,z909,z7,z4,z5]),(0,[z0,z1,z2,z910,z4,z5]),(0,[z0,z1,z2,z4,z5,z911])],[(0,[z0,z1,z912,z7,z4,z5]),(0,[z0,z1,z913,z2,z4,z5]),(1,[z0,z2,z769,z4,z5]),(0,[z0,z1,z2,z100,z308,z5]),(0,[z0,z1,z92,z2,z374,z5])],[(0,[z0,z1,z221,z7,z4,z5]),(0,[z54,z1,z28,z7,z4,z5]),(0,[z0,z914,z2,z7,z4,z5]),(0,[z19,z269,z0,z1,z7,z4]),(0,[z0,z1,z2,z915,z4,z5])],[(0,[z0,z1,z221,z490,z4,z5]),(0,[z230,z1,z7,z4,z320,z29]),(0,[z0,z1,z414,z2,z4,z5]),(0,[z492,z0,z1,z274,z7,z18])]],
   [[(0,[z0,z1,z2,z7,z916,z5]),(0,[z112,z1,z2,z7,z133,z465]),(0,[z134,z1,z2,z7,z4,z59]),(0,[z0,z241,z1,z2,z7,z59]),(0,[z917,z1,z2,z7,z4,z5]),(0,[z0,z656,z2,z100,z4,z5]),(0,[z0,z1,z918,z7,z4,z5])],[(0,[z0,z1,z2,z7,z4,z919]),(0,[z0,z1,z221,z7,z325,z5]),(0,[z0,z1,z2,z920,z4,z5]),(0,[z0,z1,z2,z921,z4,z5]),(0,[z0,z1,z92,z2,z233,z5]),(0,[z0,z2,z7,z717,z181,z5]),(0,[z0,z1,z2,z7,z4,z922])],[(0,[z0,z1,z7,z4,z5,z923]),(0,[z0,z1,z2,z924,z4,z5]),(0,[z492,z0,z1,z2,z7,z4])],[(0,[z0,z1,z472,z281,z4,z5]),(0,[z0,z1,z2,z7,z925,z5]),(0,[z926,z0,z1,z7,z4,z5]),(0,[z0,z1,z927,z7,z4,z5]),(0,[z1,z2,z7,z133,z785,z5]),(0,[z0,z2,z769,z100,z4,z5]),(0,[z1,z2,z7,z4,z5,z928])]],
   [[(0,[z184,z185,z2,z281,z4,z5]),(0,[z0,z1,z929,z7,z4,z5]),(0,[z740,z185,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z930]),(0,[z134,z1,z2,z7,z574,z59]),(0,[z0,z1,z2,z931,z4,z5]),(0,[z0,z1,z2,z815,z156,z5]),(0,[z0,z1,z2,z4,z189,z788])],[(0,[z0,z1,z2,z7,z4,z932]),(0,[z0,z1,z28,z3,z4,z5]),(0,[z0,z933,z2,z7,z4,z5]),(0,[z0,z366,z2,z7,z4,z5])],[(0,[z0,z1,z2,z7,z4,z934]),(0,[z0,z1,z935,z7,z4,z5]),(0,[z0,z1,z2,z40,z4,z788])],[(0,[z0,z1,z2,z936,z4,z5]),(0,[z1,z2,z7,z785,z115,z5]),(0,[z0,z1,z2,z4,z5,z937])]],
   [[(0,[z0,z1,z2,z281,z4,z22]),(0,[z0,z1,z938,z7,z4,z5]),(0,[z0,z1,z725,z7,z4,z5]),(0,[z0,z1,z2,z939,z4,z5]),(0,[z0,z1,z2,z7,z940,z5]),(0,[z0,z941,z2,z7,z4,z5]),(0,[z102,z1,z2,z7,z115,z5]),(0,[z86,z0,z2,z7,z309,z30]),(0,[z0,z1,z2,z7,z5,z942]),(0,[z0,z1,z2,z17,z4,z82])],[(1,[z0,z732,z7,z4,z5])],[(0,[z0,z1,z2,z7,z4,z943]),(0,[z198,z740,z2,z7,z4,z5]),(0,[z111,z1,z2,z7,z4,z29]),(0,[z0,z1,z2,z35,z308,z5]),(0,[z0,z1,z129,z188,z4,z5]),(0,[z0,z1,z2,z4,z815,z5]),(0,[z19,z0,z1,z2,z7,z20])],[(0,[z944,z0,z1,z2,z7,z4]),(0,[z0,z1,z2,z7,z4,z945]),(0,[z0,z1,z946,z2,z4,z5]),(0,[z0,z1,z2,z947,z4,z5]),(0,[z0,z1,z2,z7,z4,z948]),(0,[z65,z0,z436,z2,z7,z4])]],
   [[(0,[z0,z1,z2,z7,z4,z949]),(0,[z0,z1,z2,z950,z4,z5]),(0,[z0,z1,z2,z7,z951,z5]),(0,[z1,z2,z952,z7,z4,z5]),(0,[z8,z0,z196,z7,z4,z135])],[(0,[z0,z1,z2,z7,z4,z953]),(0,[z1,z2,z7,z4,z5,z954]),(0,[z0,z14,z2,z31,z114,z5]),(0,[z0,z128,z1,z208,z4,z5]),(0,[z0,z1,z274,z7,z18,z5])],[(0,[z955,z0,z1,z7,z4,z5]),(0,[z0,z1,z2,z4,z5,z956]),(0,[z0,z1,z2,z17,z4,z5])],[(0,[z0,z1,z2,z7,z4,z957]),(0,[z0,z1,z2,z7,z4,z147]),(0,[z0,z1,z24,z7,z4,z493])]],
   [[(0,[z0,z958,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z959]),(0,[z0,z1,z2,z7,z960,z5])],[(0,[z0,z1,z961,z7,z4,z5]),(0,[z164,z1,z107,z165,z4,z5]),(0,[z0,z1,z962,z7,z4,z5]),(0,[z0,z1,z208,z4,z5,z602])],[(1,[z1,z725,z7,z4,z5]),(0,[z0,z1,z2,z963,z7,z5])],[(0,[z0,z1,z964,z7,z4,z5]),(0,[z0,z1,z965,z2,z4,z5]),(0,[z19,z0,z1,z2,z31,z5]),(0,[z86,z0,z241,z2,z7,z30])]],
   [[(0,[z0,z14,z2,z7,z114,z5]),(0,[z456,z0,z2,z7,z4,z30]),(0,[z0,z1,z2,z7,z58,z333])],[(0,[z0,z1,z2,z7,z163,z464]),(0,[z0,z1,z966,z2,z7,z5]),(0,[z0,z436,z2,z7,z4,z59]),(0,[z0,z15,z2,z7,z181,z5]),(0,[z0,z586,z2,z7,z114,z5])],[(0,[z0,z1,z221,z281,z4,z5]),(0,[z0,z1,z2,z7,z4,z967]),(0,[z331,z1,z125,z7,z4,z5]),(0,[z112,z1,z2,z7,z133,z147]),(0,[z968,z1,z2,z7,z4,z5]),(0,[z0,z1,z969,z7,z4,z5])],[(0,[z0,z2,z7,z4,z5,z970]),(0,[z0,z226,z2,z7,z4,z148]),(0,[z971,z0,z1,z2,z7,z5])]],
   [[(0,[z0,z1,z972,z7,z4,z5]),(0,[z0,z1,z2,z3,z4,z5]),(0,[z310,z1,z2,z99,z4,z5]),(0,[z0,z1,z973,z7,z4,z5]),(1,[z0,z1,z748,z4,z5]),(0,[z0,z1,z2,z4,z5,z788]),(0,[z0,z1,z2,z7,z4,z744])],[(0,[z0,z505,z1,z208,z4,z5]),(0,[z0,z732,z27,z7,z4,z5]),(0,[z0,z1,z2,z7,z5,z974]),(0,[z0,z1,z2,z7,z4,z975]),(0,[z0,z1,z2,z7,z976,z5])],[(0,[z0,z1,z2,z7,z4,z977]),(0,[z0,z978,z2,z7,z4,z5]),(0,[z124,z1,z125,z302,z4,z5]),(0,[z0,z159,z2,z35,z308,z5])],[(0,[z0,z1,z2,z7,z4,z979]),(0,[z0,z70,z1,z7,z64,z5])]],
   [[(0,[z0,z1,z2,z7,z980,z5]),(0,[z0,z1,z2,z7,z981,z5]),(0,[z258,z1,z28,z7,z4,z5]),(0,[z0,z982,z2,z7,z4,z5]),(0,[z0,z1,z983,z2,z7,z5]),(0,[z8,z0,z732,z7,z4,z5]),(0,[z0,z1,z2,z984,z4,z5]),(0,[z0,z1,z274,z7,z82,z18]),(0,[z65,z0,z1,z7,z4,z782]),(0,[z0,z1,z7,z4,z25,z782])],[(0,[z0,z1,z2,z7,z163,z5]),(0,[z0,z1,z2,z7,z4,z985]),(0,[z230,z1,z2,z7,z4,z720])],[(0,[z0,z1,z2,z7,z986,z5]),(0,[z0,z1,z2,z490,z163,z5]),(0,[z184,z185,z2,z7,z163,z5]),(0,[z481,z1,z2,z99,z4,z5]),(0,[z626,z0,z2,z7,z4,z30]),(0,[z0,z159,z2,z35,z4,z5]),(0,[z0,z1,z2,z7,z5,z987]),(0,[z53,z1,z2,z7,z4,z148]),(1,[z0,z1,z7,z711,z5]),(0,[z492,z0,z1,z414,z2,z4]),(0,[z19,z0,z1,z2,z7,z566]),(0,[z0,z1,z2,z7,z58,z744])],[(0,[z0,z2,z35,z769,z4,z5])]],
   [[(0,[z0,z1,z2,z7,z5,z988]),(0,[z230,z269,z1,z7,z4,z29]),(0,[z0,z1,z7,z711,z4,z5]),(0,[z19,z53,z1,z2,z7,z4]),(0,[z0,z1,z2,z7,z815,z5])],[(0,[z0,z1,z2,z989,z4,z5]),(0,[z0,z1,z990,z7,z4,z5]),(0,[z0,z159,z2,z35,z608,z5]),(0,[z0,z1,z2,z7,z717,z5]),(0,[z0,z1,z92,z2,z394,z5])],[(0,[z0,z1,z2,z7,z574,z29]),(0,[z94,z1,z2,z7,z4,z29]),(0,[z0,z14,z2,z160,z114,z5]),(0,[z0,z2,z7,z4,z5,z733])],[(0,[z0,z1,z2,z7,z4,z991]),(0,[z0,z1,z2,z7,z992,z5]),(0,[z0,z1,z2,z993,z4,z5])]],
   [[(0,[z0,z1,z411,z2,z7,z5])],[(0,[z0,z1,z2,z994,z4,z5]),(0,[z0,z1,z2,z995,z4,z5]),(0,[z0,z1,z2,z7,z4,z996]),(0,[z0,z1,z997,z2,z7,z5]),(0,[z457,z1,z2,z165,z4,z5])],[(0,[z0,z1,z2,z7,z4,z464]),(0,[z0,z1,z2,z7,z133,z465]),(0,[z998,z1,z2,z7,z4,z5])],[(0,[z0,z1,z2,z7,z999,z5]),(0,[z0,z1,z2,z7,z4,z1000]),(0,[z0,z1,z1001,z7,z4,z5]),(0,[z0,z1,z129,z543,z4,z5]),(0,[z0,z1,z2,z1002,z4,z5]),(0,[z0,z241,z1,z2,z7,z29]),(0,[z0,z1,z77,z7,z4,z5]),(0,[z0,z1,z748,z188,z4,z5]),(0,[z0,z1003,z2,z7,z4,z5]),(0,[z65,z0,z1,z7,z4,z522])]],
   [[(0,[z0,z1,z1004,z7,z4,z5]),(0,[z0,z1,z1005,z7,z4,z5]),(0,[z0,z1,z7,z4,z25,z367]),(0,[z0,z561,z2,z7,z114,z5]),(0,[z0,z1,z2,z1006,z4,z5]),(0,[z0,z1,z2,z7,z1007,z5]),(0,[z0,z1,z180,z7,z4,z5]),(0,[z0,z1,z2,z7,z1008,z5]),(0,[z0,z1,z2,z7,z4,z82])],[(0,[z0,z1,z2,z7,z325,z464]),(0,[z0,z1,z2,z7,z4,z1009]),(0,[z54,z53,z1,z7,z4,z5]),(0,[z0,z2,z1010,z7,z4,z5]),(0,[z86,z0,z2,z7,z4,z30]),(0,[z0,z1011,z2,z7,z4,z5])],[(0,[z113,z1,z2,z7,z115,z5]),(0,[z0,z1,z2,z7,z88,z5]),(0,[z0,z1,z2,z7,z308,z5]),(0,[z0,z1,z2,z1012,z4,z5]),(0,[z0,z1,z274,z7,z711,z5]),(0,[z0,z1,z2,z7,z5,z41])],[(0,[z0,z1,z2,z1013,z4,z5]),(0,[z0,z1,z2,z1014,z4,z5]),(0,[z0,z1015,z2,z7,z4,z5]),(0,[z0,z1,z7,z4,z5,z320]),(0,[z0,z1,z2,z7,z1016,z5]),(0,[z0,z166,z2,z769,z4,z5]),(0,[z0,z1,z129,z242,z4,z5]),(0,[z0,z1,z7,z4,z5,z1017])]],
   [[(0,[z0,z1,z7,z4,z5,z1018]),(0,[z0,z1,z2,z7,z5,z1019]),(0,[z0,z1,z2,z7,z57,z322]),(0,[z0,z1,z7,z4,z5,z1020]),(0,[z0,z1,z129,z705,z4,z5])],[(0,[z0,z1,z472,z7,z4,z22]),(0,[z0,z1,z2,z7,z4,z1021]),(0,[z0,z1,z1022,z7,z4,z5]),(0,[z0,z1,z129,z246,z4,z5]),(0,[z0,z368,z2,z35,z4,z5]),(0,[z0,z1,z1023,z7,z4,z5]),(0,[z0,z1,z27,z7,z4,z9]),(0,[z0,z1,z2,z31,z58,z5]),(0,[z0,z1024,z2,z7,z4,z5]),(0,[z1025,z1,z2,z7,z4,z5])],[(0,[z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z490,z4,z22]),(0,[z0,z1,z2,z1026,z4,z5]),(0,[z184,z185,z2,z7,z4,z22]),(0,[z54,z1,z725,z7,z4,z5]),(1,[z1,z2,z7,z4,z720]),(0,[z1027,z1,z2,z7,z4,z5])],[(0,[z0,z1,z2,z490,z4,z5]),(0,[z184,z185,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z1028,z5]),(0,[z0,z1,z2,z1029,z4,z5]),(0,[z0,z1,z1030,z7,z4,z5]),(0,[z0,z1031,z1,z7,z4,z5]),(0,[z1032,z1,z2,z7,z4,z5]),(0,[z0,z1,z77,z7,z4,z30]),(0,[z65,z0,z1,z7,z4,z71]),(0,[z38,z0,z1,z2,z4,z788])]],
   [[(0,[z1,z2,z7,z727,z4,z5]),(0,[z0,z128,z1,z529,z4,z5]),(0,[z0,z1,z1033,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z1034]),(0,[z0,z1,z7,z4,z1035,z5])],[(0,[z0,z1,z2,z7,z325,z5]),(0,[z0,z1,z1036,z7,z4,z5]),(0,[z0,z1,z2,z7,z1037,z5]),(0,[z0,z1,z107,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z1038]),(0,[z638,z1,z2,z7,z133,z5]),(0,[z0,z1,z2,z7,z608,z5]),(0,[z1039,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z61,z815,z5])],[(0,[z0,z1,z2,z490,z325,z5]),(0,[z184,z185,z2,z7,z325,z5]),(0,[z0,z1,z2,z1040,z4,z5]),(0,[z0,z1,z2,z7,z574,z5]),(0,[z0,z1,z2,z1041,z4,z5]),(0,[z0,z1,z2,z36,z501,z5]),(0,[z0,z1,z2,z4,z788,z39])],[(0,[z0,z1,z221,z7,z4,z464]),(0,[z0,z1,z2,z1042,z4,z5]),(0,[z269,z0,z1,z7,z4,z5]),(0,[z0,z1,z1043,z7,z4,z5]),(0,[z1,z2,z7,z785,z4,z5]),(0,[z0,z1,z1044,z7,z4,z5]),(0,[z1,z2,z7,z4,z1045,z5]),(0,[z0,z241,z2,z7,z181,z5]),(0,[z65,z0,z241,z1,z2,z7]),(0,[z38,z0,z1,z2,z4,z39])]]]

def SA : ℕ × List W → Bool := fun c => !inB2 8 256 bkA c

def SB : ℕ × List W → Bool := fun c => !inB2 4 128 bkB c

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 556) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 556).take 462) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1018)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [556, 462] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_nil pbend))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 101).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 101).take 27).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 128)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [101, 27] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_nil pcend))

theorem reject : search 8 rows = false :=
  search_false_C2 (dp := 0) (J := 5) (d := 2) (g1 := 8) (nb1 := 256) (g2 := 4) (nb2 := 128) (by norm_num) gf windowsC windowsB windowsA

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

end PEqualNP.Outside.L_meta_41212

theorem PEqualNP.Outside.L_meta_41212 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809440 * 2 ^ 32 + 4207460544) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809440 * 2 ^ 32 + 4207460544) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_41212.solve