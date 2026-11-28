import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_36312

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
  Nat.testBit (4277075690 * 2 ^ 32 + 4276923048) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x042002000404604a#64 ++ 0x8210010002023025#64 ++ 0xffd0a6023c0ce7ff#64 ++ 0xffe853011e0673ff#64 : BitVec 256),
   (0x13c0090cd2110d24#64 ++ 0x09e0048669088692#64 ++ 0x77b9591dd2333d27#64 ++ 0xbbdcac8ee9199e93#64 : BitVec 256),
   (0x0282616162c38631#64 ++ 0x014130b0b161c318#64 ++ 0xed7e61e1e3c3c639#64 ++ 0x76bf30f0f1e1e31c#64 : BitVec 256),
   (0xab0581b603780780#64 ++ 0x5582c0db01bc03c0#64 ++ 0xdcf781fe03fc07c0#64 ++ 0xee7bc0ff01fe03e0#64 : BitVec 256),
   (0xcc07f60001aef000#64 ++ 0x6603fb0000d77800#64 ++ 0xc3fffe0003fff801#64 ++ 0xe1ffff0001fffc00#64 : BitVec 256),
   (0xf007fcdbb8000000#64 ++ 0x7803fe6ddc000000#64 ++ 0x3ff7fffffc000000#64 ++ 0x1ffbfffffe000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 4]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [0, 7]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [9, 5]⟩, ⟨.or, [10, 6]⟩, ⟨.or, [9, 5]⟩, ⟨.and, [8, 12]⟩, ⟨.or, [1, 13]⟩, ⟨.and, [14, 11]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0282616162c38631 0x014130b0b161c318 0xed7e61e1e3c3c639 0x76bf30f0f1e1e31c

def z1 : W := mkw 0x042002000404604a 0x8210010002023025 0xffd0a6023c0ce7ff 0xffe853011e0673ff

def z2 : W := mkw 0x13c0090cd2110d24 0x09e0048669088692 0x77b9591dd2333d27 0xbbdcac8ee9199e93

def z3 : W := mkw 0x8a05812003680600 0x4502c09001b40300 0xccf781e003fc0600 0xe67bc0f001fe0300

def z4 : W := mkw 0xab0581b603780780 0x5582c0db01bc03c0 0xdcf781fe03fc07c0 0xee7bc0ff01fe03e0

def z5 : W := mkw 0xcc07f60001aef000 0x6603fb0000d77800 0xc3fffe0003fff801 0xe1ffff0001fffc00

def z6 : W := mkw 0xf007fcdbb8000000 0x7803fe6ddc000000 0x3ff7fffffc000000 0x1ffbfffffe000000

def z7 : W := mkw 0x042002000404604a 0x8210010002023025 0x8840a6022c0cc2d8 0x442053011606616c

def z8 : W := mkw 0xf007fcdbb8000000 0x7803fe6ddc000000 0x37b759fdd0000000 0x1bdbacfee8000000

def z9 : W := mkw 0x0400020000046000 0x0200010000023000 0xc3d0a600000ce001 0xe1e8530000067000

def z10 : W := mkw 0xcc27f60005aef04a 0xe613fb0002d77825 0xfffffe023fffffff 0xffffff011fffffff

def z11 : W := mkw 0x0000000000000000 0x0000000000000000 0x3fd0a6023c000000 0x1fe853011e000000

def z12 : W := mkw 0xcc07f60001aef000 0x6603fb0000d77800 0xc02f580003fff801 0xe017ac0001fffc00

def z13 : W := mkw 0x50027c49b8000000 0x28013e24dc000000 0x23007e01fc000000 0x11803f00fe000000

def z14 : W := mkw 0xf007fcdbb8000000 0x7803fe6ddc000000 0x002759fdc0000000 0x0013acfee0000000

def z15 : W := mkw 0x13c0090cd2110d24 0x09e0048669088692 0x12a9591dd2333906 0x8954ac8ee9199c83

def z16 : W := mkw 0x0280016162410631 0x014000b0b1208318 0x2c0001e1e0000638 0x160000f0f000031c

def z17 : W := mkw 0xcc059600012c7000 0x6602cb0000963800 0x02819e00003c3800 0x8140cf00001e1c00

def z18 : W := mkw 0x0000000000000000 0x0000000000000000 0x4000000000002527 0xa000000000001293

def z19 : W := mkw 0x0282616162c38631 0x014130b0b161c318 0x212e61e1e3c3c039 0x109730f0f1e1e01c

def z20 : W := mkw 0x10c00808d0010824 0x0860040468008412 0x23085801d0033827 0x11842c00e8019c13

def z21 : W := mkw 0xa80580b201680280 0x5402c05900b40140 0x884680e201cc02c0 0x4423407100e60160

def z22 : W := mkw 0x0000000000000000 0x0000000000000000 0x43b9580002333801 0xa1dcac0001199c00

def z23 : W := mkw 0xf007fcdbb8000000 0x7803fe6ddc000000 0x3c46a7fffc000000 0x1e2353fffe000000

def z24 : W := mkw 0x0002604120000000 0x0001302090000000 0x2d7661e1e0000000 0x16bb30f0f0000000

def z25 : W := mkw 0xf287fdfbfac38631 0x7943fefdfd61c318 0xffffffffffc3c639 0x7fffffffffe1e31c

def z26 : W := mkw 0xf007fcdbb8000000 0x7803fe6ddc000000 0x2b46fee3fc000000 0x15a37f71fe000000

def z27 : W := mkw 0x230001b602500780 0x118000db012803c0 0x1c0001fe000007c0 0x0e0000ff000003e0

def z28 : W := mkw 0x0280012042c38631 0x014000902161c318 0xe5384101c3c3c639 0x729c2080e1e1e31c

def z29 : W := mkw 0xf407fedbb886f000 0x7a03ff6ddc437800 0x3ffffffffc03f801 0x1ffffffffe01fc00

def z30 : W := mkw 0xbb0589ffbb780780 0x5d82c4ffddbc03c0 0xfcf781fffffc07c0 0xfe7bc0fffffe03e0

def z31 : W := mkw 0x042002000404604a 0x8210010002023025 0x3fd0a6023c0c21c6 0x9fe853011e0610e3

def z32 : W := mkw 0xc807f40001aa9000 0x6403fa0000d54800 0x43bf580003f33801 0xa1dfac0001f99c00

def z33 : W := mkw 0x13c0090cd2110d24 0x09e0048669088692 0x2329591dd2333827 0x1194ac8ee9199c13

def z34 : W := mkw 0xc807f40001aa9000 0x6403fa0000d54800 0x002f580003f31800 0x0017ac0001f98c00

def z35 : W := mkw 0x03c0010442110d24 0x01e0008221088692 0x4008000002333d27 0xa004000001199e93

def z36 : W := mkw 0xa80580b201680280 0x5402c05900b40140 0x9cf781fe01cc02c0 0x4e7bc0ff00e60160

def z37 : W := mkw 0x4002740000000000 0x20013a0000000000 0x03007e0000000000 0x01803f0000000000

def z38 : W := mkw 0x50001c0898000000 0x28000e044c000000 0x02001e001c000000 0x01000f000e000000

def z39 : W := mkw 0x002000000400004a 0x8010000002000025 0x3c0000023c0007fe 0x1e0000011e0003ff

def z40 : W := mkw 0x0082604160838031 0x00413020b041c018 0x21086001e003c039 0x10843000f001e01c

def z41 : W := mkw 0xab87e1f763fb87b1 0x55c3f0fbb1fdc3d8 0xfdffe1ffe3ffc7f9 0xfefff0fff1ffe3fc

def z42 : W := mkw 0x002000000400004a 0x8010000002000025 0x7f9000023c0027ff 0xbfc800011e0013ff

def z43 : W := mkw 0x0280010042010420 0x0140008021008210 0x65384101c2030421 0x329c2080e1018210

def z44 : W := mkw 0x13c2696df2d38f35 0x09e134b6f969c79a 0xffff79fdf3f3ff3f 0xffffbcfef9f9ff9f

def z45 : W := mkw 0xcc07f60001aef000 0x6603fb0000d77800 0xc0f7a60003fcc000 0xe07bd30001fe6000

def z46 : W := mkw 0x0000000000000000 0x0000000000000000 0xed5020002000c639 0x76a810001000631c

def z47 : W := mkw 0x13c0090cd2110d24 0x09e0048669088692 0xfff9791df233ff3f 0xfffcbc8ef919ff9f

def z48 : W := mkw 0xbbc7e9fff3fb8fb5 0x5de3f4fff9fdc7da 0xfffff9fff3ffffff 0xfffffcfff9ffffff

def z49 : W := mkw 0xc807f40001aa9000 0x6403fa0000d54800 0xc0ffd80003ff1800 0xe07fec0001ff8c00

def z50 : W := mkw 0x0280016162410631 0x014000b0b1208318 0x6d3841e1e2030639 0x369c20f0f101831c

def z51 : W := mkw 0x0300010402100500 0x0180008201080280 0xdcf1811e023c07c0 0xee78c08f011e03e0

def z52 : W := mkw 0x03c0010442110d24 0x01e0008221088692 0x0008000002331800 0x0004000001198c00

def z53 : W := mkw 0xc807f40001aa9000 0x6403fa0000d54800 0x03fffe0003f31800 0x01ffff0001f98c00

def z54 : W := mkw 0x06a2636166c7e67b 0x835131b0b363f33d 0xfffee7e3ffcfe7ff 0xffff73f1ffe7f3ff

def z55 : W := mkw 0x0002606120c28211 0x0001303090614108 0x884620e021c0c218 0x4423107010e0610c

def z56 : W := mkw 0x0c000200012c7000 0x0600010000963800 0x00000000003c3800 0x80000000001e1c00

def z57 : W := mkw 0x0bc0012443790fa4 0x05e0009221bc87d2 0xc008000003ff3fe7 0xe004000001ff9ff3

def z58 : W := mkw 0x13c0090cd2110d24 0x09e0048669088692 0x37b1591dd0000526 0x1bd8ac8ee8000293

def z59 : W := mkw 0x042002000404604a 0x8210010002023025 0x128086021c0c21c6 0x894043010e0610e3

def z60 : W := mkw 0xcc27f60005aef04a 0xe613fb0002d77825 0xd3fffe021ffff9c7 0xe9ffff010ffffce3

def z61 : W := mkw 0x440276000086f000 0x22013b0000437800 0x43b97e000233f801 0xa1dcbf000119fc00

def z62 : W := mkw 0x57c27f0cd297fd24 0x2be13f86694bfe92 0x77b97f1dd233fd27 0xbbdcbf8ee919fe93

def z63 : W := mkw 0x0000004120000000 0x0000002090000000 0x2c0001e1e0000000 0x160000f0f0000000

def z64 : W := mkw 0x17e00b0cd6156d6e 0x8bf005866b0ab6b7 0xfff9ff1ffe3fffff 0xfffcff8fff1fffff

def z65 : W := mkw 0x442276000486f04a 0xa2113b0002437825 0x23087e003c03f83f 0x11843f001e01fc1f

def z66 : W := mkw 0x0002606120c28211 0x0001303090614108 0xc97e60e023c3c219 0x64bf307011e1e10c

def z67 : W := mkw 0xa005809200000000 0x5002c04900000000 0x1cf781fe00000000 0x0e7bc0ff00000000

def z68 : W := mkw 0xaa0581b203680680 0x5502c0d901b40340 0xcc7681e203cc06c0 0x663b40f101e60360

def z69 : W := mkw 0xf3c7fddffa110d24 0x79e3feeffd088692 0x7ffffffffe333d27 0xbfffffffff199e93

def z70 : W := mkw 0x13c0090cd2110d24 0x09e0048669088692 0x3400011dd0000526 0x1a00008ee8000293

def z71 : W := mkw 0xfc07fedbb9aef000 0x7e03ff6ddcd77800 0xfffffffffffff801 0xfffffffffffffc00

def z72 : W := mkw 0xc007f40000000000 0x6003fa0000000000 0x43fffe0002333801 0xa1ffff0001199c00

def z73 : W := mkw 0xec07f6d329aef000 0x7603fb6994d77800 0xcbfffee22ffff801 0xe5ffff7117fffc00

def z74 : W := mkw 0xdc07fe49b9aef000 0x6e03ff24dcd77800 0xe3fffe01fffff801 0xf1ffff00fffffc00

def z75 : W := mkw 0x0282616162c38631 0x014130b0b161c318 0xac4621e1e1c0c638 0x562310f0f0e0631c

def z76 : W := mkw 0x0400020000046000 0x0200010000023000 0xf7d0a600100ce527 0xfbe8530008067293

def z77 : W := mkw 0xe807f4f329680280 0x7403fa7994b40140 0x8846a6e22dcc02c0 0x4423537116e60160

def z78 : W := mkw 0x042002000404604a 0x8210010002023025 0xfc0000023c0ce7ff 0xfe0000011e0673ff

def z79 : W := mkw 0x0b00012403780780 0x0580009201bc03c0 0xc000000003fc07c0 0xe000000001fe03e0

def z80 : W := mkw 0xaf2583b6077c67ca 0xd792c1db03be33e5 0xfff7a7fe3ffce7ff 0xfffbd3ff1ffe73ff

def z81 : W := mkw 0x0000000000000000 0x0000000000000000 0x230026003c000000 0x118013001e000000

def z82 : W := mkw 0xbbc589bed3790fa4 0x5de2c4df69bc87d2 0xfcf781ffd3fc07e6 0xfe7bc0ffe9fe03f3

def z83 : W := mkw 0xfc07fedbb9aef000 0x7e03ff6ddcd77800 0xbff7fffffdccc000 0x5ffbfffffee66000

def z84 : W := mkw 0xef07f7b603fef780 0x7783fbdb01ff7bc0 0xdffffffe03ffffc1 0xefffffff01ffffe0

def z85 : W := mkw 0x040262000086e000 0x0201310000437000 0xc3fee60003cfe001 0xe1ff730001e7f000

def z86 : W := mkw 0xe007f4d328000000 0x7003fa6994000000 0x2d76e7e3ec000000 0x16bb73f1f6000000

def z87 : W := mkw 0x0200012002400600 0x0100009001200300 0xcc7601e003c00600 0x663b00f001e00300

def z88 : W := mkw 0x13c0090cd2110d24 0x09e0048669088692 0x54b9591dc2331d00 0xaa5cac8ee1198e80

def z89 : W := mkw 0x0c00020001aef000 0x0600010000d77800 0xc3b9580003fff801 0xe1dcac0001fffc00

def z90 : W := mkw 0xe007f4d328000000 0x7003fa6994000000 0x0846a6e22c000000 0x0423537116000000

def z91 : W := mkw 0x4682776162c7f631 0x23413bb0b163fb18 0xef7e7fe1e3c3fe39 0x77bf3ff0f1e1ff1c

def z92 : W := mkw 0xab0581b603780780 0x5582c0db01bc03c0 0xfdf7a1fe23fcc7f9 0xfefbd0ff11fe63fc

def z93 : W := mkw 0xcc059600012c7000 0x6602cb0000963800 0x43b9de00023f3801 0xa1dcef00011f9c00

def z94 : W := mkw 0xfb07fdffbb780780 0x7d83feffddbc03c0 0xfff7fffffffc07c0 0xfffbfffffffe03e0

def z95 : W := mkw 0xbbc589bed3790fa4 0x5de2c4df69bc87d2 0xffffd9ffd3ff3fe7 0xffffecffe9ff9ff3

def z96 : W := mkw 0xb3c5899ed2110d24 0x59e2c4cf69088692 0x7fffd9ffd2333d27 0xbfffecffe9199e93

def z97 : W := mkw 0xf0059c9a98000000 0x7802ce4d4c000000 0x3fd1be1e3c000000 0x1fe8df0f1e000000

def z98 : W := mkw 0xcc07f60001aef000 0x6603fb0000d77800 0x0389fe00003ff801 0x81c4ff00001ffc00

def z99 : W := mkw 0xad258296053c61ca 0xd692c14b029e30e5 0x1281861e1c3c21c6 0x8940c30f0e1e10e3

def z100 : W := mkw 0x13c0090cd2110d24 0x09e0048669088692 0x7408011dd2333d27 0xba04008ee9199e93

def z101 : W := mkw 0xab0581b603780780 0x5582c0db01bc03c0 0xcc7701fc03f00600 0x663b80fe01f80300

def z102 : W := mkw 0x13c0096df2510f35 0x09e004b6f928879a 0x3c0001fdf000073e 0x1e0000fef800039f

def z103 : W := mkw 0x042002000404604a 0x8210010002023025 0x000026002c00c018 0x000013001600600c

def z104 : W := mkw 0xc007f40000000000 0x6003fa0000000000 0x03f7fe0000000000 0x01fbff0000000000

def z105 : W := mkw 0xdfe7ff0cd7bffd6e 0xeff3ff866bdffeb7 0xffffff1fffffffff 0xffffff8fffffffff

def z106 : W := mkw 0xfc07fedbb9aef000 0x7e03ff6ddcd77800 0xc3fffffdc3fff801 0xe1fffffee1fffc00

def z107 : W := mkw 0x0282616162c38631 0x014130b0b161c318 0xefff79e1e3f3fe39 0xf7ffbcf0f1f9ff1c

def z108 : W := mkw 0x1140080c90100904 0x08a0040648080482 0x1281181c10303906 0x89408c0e08181c83

def z109 : W := mkw 0x13c0092cd2510f24 0x09e0049669288792 0xffff59fdd3f33f27 0xffffacfee9f99f93

def z110 : W := mkw 0xf907fcdfb9380180 0x7c83fe6fdc9c00c0 0x3ff7fffffc3c01c0 0x9ffbfffffe1e00e0

def z111 : W := mkw 0xcc07f60001aef000 0x6603fb0000d77800 0x806ffe0003ffd800 0x4037ff0001ffec00

def z112 : W := mkw 0x300008dbb8000000 0x1800046ddc000000 0x3c0001fffc000000 0x1e0000fffe000000

def z113 : W := mkw 0xf427fedbbc04604a 0xfa13ff6dde023025 0xfff7fffffc0ce7ff 0xfffbfffffe0673ff

def z114 : W := mkw 0xdc07fe0891aef000 0x6e03ff0448d77800 0xf7ffff1dd3fff801 0xfbffff8ee9fffc00

def z115 : W := mkw 0xec07f69201aef000 0x7603fb4900d77800 0xdffffffe03fff801 0xefffffff01fffc00

def z116 : W := mkw 0xf007fcdbb8000000 0x7803fe6ddc000000 0x12a7dfffdc000000 0x0953efffee000000

def z117 : W := mkw 0xcc259600052c704a 0xe612cb0002963825 0x12819e021c3c39c6 0x8940cf010e1e1ce3

def z118 : W := mkw 0x0b00012403780780 0x0580009201bc03c0 0xd4b1011c03fc07c0 0xea58808e01fe03e0

def z119 : W := mkw 0xfc07fedbb92c7000 0x7e03ff6ddc963800 0x3ff7fffffc3c3800 0x9ffbfffffe1e1c00

def z120 : W := mkw 0xab0581b603780780 0x5582c0db01bc03c0 0xc02701fc03fc07c0 0xe01380fe01fe03e0

def z121 : W := mkw 0xcea7f76167eff67b 0xe753fbb0b3f7fb3d 0xffffffe3ffffffff 0xfffffff1ffffffff

def z122 : W := mkw 0xc007f44120000000 0x6003fa2090000000 0x2ff7ffe1e0000000 0x17fbfff0f0000000

def z123 : W := mkw 0x0282616162c38631 0x014130b0b161c318 0x653e41e1c3c30421 0x329f20f0e1e18210

def z124 : W := mkw 0x0000000000000000 0x0000000000000000 0xdcd08002000c07c0 0xee684001000603e0

def z125 : W := mkw 0xcc07f60001aef000 0x6603fb0000d77800 0xdffffe0203ffffc1 0xefffff0101ffffe0

def z126 : W := mkw 0xcc07f60001aef000 0x6603fb0000d77800 0x032f7e0003f3f801 0x0197bf0001f9fc00

def z127 : W := mkw 0xa42582920404604a 0xd212c14902023025 0xfff7a7fe3c0ce7ff 0xfffbd3ff1e0673ff

def z128 : W := mkw 0xc005940000000000 0x6002ca0000000000 0x02819e0000000000 0x0140cf0000000000

def z129 : W := mkw 0x042002000404604a 0x8210010002023025 0xd28086021c0ce7ff 0xe94043010e0673ff

def z130 : W := mkw 0xab0581b603780780 0x5582c0db01bc03c0 0xfff781fe13fc27e7 0xfffbc0ff09fe13f3

def z131 : W := mkw 0x1000080890000000 0x0800040448000000 0x0021591dc0000000 0x0010ac8ee0000000

def z132 : W := mkw 0x0282614162838431 0x014130a0b141c218 0x65386101e203c439 0x329c3080f101e21c

def z133 : W := mkw 0x1140080c90100904 0x08a0040648080482 0x0001181c00301800 0x00008c0e00180c00

def z134 : W := mkw 0x302008dbbc00004a 0x9810046dde000025 0x3c0001fffc0007fe 0x1e0000fffe0003ff

def z135 : W := mkw 0x1bc0092cd3790fa4 0x0de0049669bc87d2 0xf7b9591dd3ff3fe7 0xfbdcac8ee9ff9ff3

def z136 : W := mkw 0xe005949208000000 0x7002ca4904000000 0x000086020c000000 0x0000430106000000

def z137 : W := mkw 0xab0581b603780780 0x5582c0db01bc03c0 0xfff7a7fe3ffc07c0 0xfffbd3ff1ffe03e0

def z138 : W := mkw 0xcf07f70403bef500 0x6783fb8201df7a80 0xd7ffff1c03fffd01 0xebffff8e01fffe80

def z139 : W := mkw 0x0202616122c28611 0x010130b091614308 0xcc7621e023c0c618 0x663b10f011e0630c

def z140 : W := mkw 0x03c0010442110d24 0x01e0008221088692 0x65384101c2333d27 0xb29c2080e1199e93

def z141 : W := mkw 0x1140080c90100904 0x08a0040648080482 0x7791181c10303d27 0xbbc88c0e08181e93

def z142 : W := mkw 0x1140080c90100904 0x08a0040648080482 0x1000001c10000106 0x0800000e08000083

def z143 : W := mkw 0x042262000486e04a 0x8211310002437025 0xfffee6023fcfe7ff 0xffff73011fe7f3ff

def z144 : W := mkw 0xe287f5f36ac38631 0x7143faf9b561c318 0xed7ee7e3efc3c639 0x76bf73f1f7e1e31c

def z145 : W := mkw 0xb00588dbb8000000 0x5802c46ddc000000 0x3cf781fffc000000 0x1e7bc0fffe000000

def z146 : W := mkw 0x0282616162c38631 0x014130b0b161c318 0x002e41e1c3c30000 0x001720f0e1e18000

def z147 : W := mkw 0xf807fcdbb9aa9000 0x7c03fe6ddcd54800 0x3ffffffffff31800 0x1ffffffffff98c00

def z148 : W := mkw 0x0280016162410631 0x014000b0b1208318 0xed5021e1e000c639 0x76a810f0f000631c

def z149 : W := mkw 0x440276000086f000 0x22013b0000437800 0x03087e000003f801 0x01843f000001fc00

def z150 : W := mkw 0xaf0583b603fef780 0x5782c1db01ff7bc0 0xdcff81fe03ffffc1 0xee7fc0ff01ffffe0

def z151 : W := mkw 0xa905809601380180 0x5482c04b009c00c0 0x1081801e003c01c0 0x8840c00f001e00e0

def z152 : W := mkw 0xa005809200000000 0x5002c04900000000 0x002701fc00000000 0x001380fe00000000

def z153 : W := mkw 0xfc27fedbbdaef04a 0xfe13ff6dded77825 0xffffffffffffffff 0xffffffffffffffff

def z154 : W := mkw 0x0002606120c28211 0x0001303090614108 0xad7661e1e1c0c218 0x56bb30f0f0e0610c

def z155 : W := mkw 0xf0059c9a98000000 0x7802ce4d4c000000 0x12819e1e1c000000 0x0940cf0f0e000000

def z156 : W := mkw 0x0000000000000000 0x0000000000000000 0x7790000010002527 0xbbc8000008001293

def z157 : W := mkw 0xab0581b603780780 0x5582c0db01bc03c0 0x886781fe03fc02c0 0x4433c0ff01fe0160

def z158 : W := mkw 0x042002000404604a 0x8210010002023025 0xe3d0a6003c0ce03f 0xf1e853001e06701f

def z159 : W := mkw 0x042002000404604a 0x8210010002023025 0x9ac0a6023c0ce3de 0xcd6053011e0671ef

def z160 : W := mkw 0x12c26969f2c38e35 0x096134b4f961c71a 0xef7e79e1f3c3fe3f 0x77bf3cf0f9e1ff1f

def z161 : W := mkw 0xcc07f60001aef000 0x6603fb0000d77800 0x8046a60001ccc000 0x4023530000e66000

def z162 : W := mkw 0x03c2616562d38f35 0x01e130b2b169c79a 0xed7e61e1e3f3ff3f 0xf6bf30f0f1f9ff9f

def z163 : W := mkw 0xd3c7fd0cd2110d24 0x69e3fe8669088692 0x77ffff1dd2333d27 0xbbffff8ee9199e93

def z164 : W := mkw 0x0282616162c38631 0x014130b0b161c318 0xfffee7e3ffc3c639 0x7fff73f1ffe1e31c

def z165 : W := mkw 0x8805800001280000 0x4402c00000940000 0x8046800001cc0000 0x4023400000e60000

def z166 : W := mkw 0x0c00020001aef000 0x0600010000d77800 0xc008000003fff801 0xe004000001fffc00

def z167 : W := mkw 0x300268dbb8000000 0x1801346ddc000000 0x3d7661fffc000000 0x1ebb30fffe000000

def z168 : W := mkw 0x06a2636166c7e67b 0x835131b0b363f33d 0xed7e61e1e3cfe7ff 0xf6bf30f0f1e7f3ff

def z169 : W := mkw 0xdcc7fe08d1aff824 0x6e63ff0468d7fc12 0xe3fffe01d3fff827 0xf1ffff00e9fffc13

def z170 : W := mkw 0x0f200324077c67ca 0x8790019203be33e5 0xffd0a6023ffce7ff 0xffe853011ffe73ff

def z171 : W := mkw 0xce07f72003eef600 0x6703fb9001f77b00 0xcfffffe003fffe01 0xe7fffff001ffff00

def z172 : W := mkw 0x0002604120000000 0x0001302090000000 0x21006001e0000000 0x10803000f0000000

def z173 : W := mkw 0xca87f56163eb9631 0x6543fab0b1f5cb18 0x002f59e1c3f31800 0x0017acf0e1f98c00

def z174 : W := mkw 0x0280012042c38631 0x014000902161c318 0xed58200023c3c639 0x76ac100011e1e31c

def z175 : W := mkw 0x8805800001280000 0x4402c00000940000 0xc3ffd80003ff3801 0xe1ffec0001ff9c00

def z176 : W := mkw 0xf427fedbbc04604a 0xfa13ff6dde023025 0x3ff7fffffc0c21c6 0x9ffbfffffe0610e3

def z177 : W := mkw 0xc807f40001aa9000 0x6403fa0000d54800 0x0006000001c00000 0x0003000000e00000

def z178 : W := mkw 0x07e0030446156d6e 0x83f00182230ab6b7 0xffd8a6023e3fffff 0xffec53011f1fffff

def z179 : W := mkw 0xa905809601380180 0x5482c04b009c00c0 0xd0f7801e03fc01c0 0xe87bc00f01fe00e0

def z180 : W := mkw 0x0282616162c38631 0x014130b0b161c318 0x886e61e1e3c3c218 0x443730f0f1e1e10c

def z181 : W := mkw 0x0000000000000000 0x0000000000000000 0x14b1011c00000000 0x0a58808e00000000

def z182 : W := mkw 0x0280010042010420 0x0140008021008210 0x67b95901c2333c21 0xb3dcac80e1199e10

def z183 : W := mkw 0x0f00032403fef780 0x0780019201ff7bc0 0xc008000003ffffc1 0xe004000001ffffe0

def z184 : W := mkw 0x13c0090cd2110d24 0x09e0048669088692 0x0029591dc2331800 0x0014ac8ee1198c00

def z185 : W := mkw 0xa005809200000000 0x5002c04900000000 0x3ff7a7fe3c000000 0x1ffbd3ff1e000000

def z186 : W := mkw 0x0282612042c38631 0x014130902161c318 0xc17e600003c3c639 0x60bf300001e1e31c

def z187 : W := mkw 0x06a2636166c7e67b 0x835131b0b363f33d 0xef7e67e1ffc3e63f 0x77bf33f0ffe1f31f

def z188 : W := mkw 0x230001b602500780 0x118000db012803c0 0xdcd081fe000c07c0 0xee6840ff000603e0

def z189 : W := mkw 0x8c05820001aef000 0x4602c10000d77800 0xc0ff800003fff801 0xe07fc00001fffc00

def z190 : W := mkw 0x0000000000000000 0x0000000000000000 0x128086021c000000 0x094043010e000000

def z191 : W := mkw 0x0900000401380180 0x04800002009c00c0 0x00000000003c01c0 0x80000000001e00e0

def z192 : W := mkw 0x3000089a98000000 0x1800044d4c000000 0x1000001e1c000000 0x0800000f0e000000

def z193 : W := mkw 0x230001b602500780 0x118000db012803c0 0x000001fc00000000 0x000000fe00000000

def z194 : W := mkw 0xca87f56163eb9631 0x6543fab0b1f5cb18 0xed7f79e1e3f3de39 0x76bfbcf0f1f9ef1c

def z195 : W := mkw 0xcfc7f70443bffd24 0x67e3fb8221dffe92 0xc3fffe0003fffd27 0xe1ffff0001fffe93

def z196 : W := mkw 0xf307fdffba500780 0x7983feffdd2803c0 0x3ff7fffffc0007c0 0x1ffbfffffe0003e0

def z197 : W := mkw 0xf287fddbfa010420 0x7943feedfd008210 0x7ffffffffe030421 0x3fffffffff018210

def z198 : W := mkw 0x0002600000828000 0x0001300000414000 0xc3ff780003f3f801 0xe1ffbc0001f9fc00

def z199 : W := mkw 0x0080000040838031 0x004000002041c018 0x000800000003c039 0x000400000001e01c

def z200 : W := mkw 0xfc07fe9a99aef000 0x7e03ff4d4cd77800 0xd3fffe1e1ffff801 0xe9ffff0f0ffffc00

def z201 : W := mkw 0x0000000000000000 0x0000000000000000 0x77b9580012333d27 0xbbdcac0009199e93

def z202 : W := mkw 0x10c00808d0010824 0x0860040468008412 0x37b9591dd0033827 0x1bdcac8ee8019c13

def z203 : W := mkw 0xc807f40001aa9000 0x6403fa0000d54800 0xc17f780003f3d801 0x60bfbc0001f9ec00

def z204 : W := mkw 0x0002600000828000 0x0001300000414000 0xc17e600003c3c001 0x60bf300001e1e000

def z205 : W := mkw 0xce87f76163eff631 0x6743fbb0b1f7fb18 0xefffffe1e3fffe39 0xf7fffff0f1ffff1c

def z206 : W := mkw 0xcc07f60001aef000 0x6603fb0000d77800 0xf7fffe0013fffd27 0xfbffff0009fffe93

def z207 : W := mkw 0x13c0090cd2110d24 0x09e0048669088692 0x0000011dc0000000 0x0000008ee0000000

def z208 : W := mkw 0xf007fcdbb8000000 0x7803fe6ddc000000 0x7ff7fffffc002527 0xbffbfffffe001293

def z209 : W := mkw 0x33c009dffa110d24 0x19e004effd088692 0x3c0001fffc000526 0x1e0000fffe000293

def z210 : W := mkw 0x8805800001280000 0x4402c00000940000 0xdcf7800203fc07c0 0xee7bc00101fe03e0

def z211 : W := mkw 0x17e00b0cd6156d6e 0x8bf005866b0ab6b7 0xffd0a71ffc0ce7ff 0xffe8538ffe0673ff

def z212 : W := mkw 0xa287e1f362c38631 0x5143f0f9b161c318 0xfdffe1ffe3c3c639 0x7efff0fff1e1e31c

def z213 : W := mkw 0xab87e1f763fb87b1 0x55c3f0fbb1fdc3d8 0xdcffc1ffc3ff07c0 0xee7fe0ffe1ff83e0

def z214 : W := mkw 0xab87e1f763fb87b1 0x55c3f0fbb1fdc3d8 0x002f41fdc3f30000 0x0017a0fee1f98000

def z215 : W := mkw 0xab0581b603780780 0x5582c0db01bc03c0 0x002701fc03f00000 0x001380fe01f80000

def z216 : W := mkw 0xcc27f60005aef04a 0xe613fb0002d77825 0xc3fffe0003ffffff 0xe1ffff0001ffffff

def z217 : W := mkw 0xf3c7fddffa110d24 0x79e3feeffd088692 0x3ff7fffffc000526 0x1ffbfffffe000293

def z218 : W := mkw 0x042002000404604a 0x8210010002023025 0xf7900000100ce7ff 0xfbc80000080673ff

def z219 : W := mkw 0x70027cdbb8000000 0x38013e6ddc000000 0x3f007ffffc000000 0x1f803ffffe000000

def z220 : W := mkw 0xf287fdfbfac38631 0x7943fefdfd61c318 0x3fffffffffc30000 0x1fffffffffe18000

def z221 : W := mkw 0x13c2696df2d38f35 0x09e134b6f969c79a 0xed7f79fde3f3de39 0x76bfbcfef1f9ef1c

def z222 : W := mkw 0x0c00020001aef000 0x0600010000d77800 0x8000000001ccc000 0x4000000000e66000

def z223 : W := mkw 0x0002604120828000 0x0001302090414000 0xed7e61e1e3c3c001 0x76bf30f0f1e1e000

def z224 : W := mkw 0xcc059600012c7000 0x6602cb0000963800 0x00008600000c0000 0x0000430000060000

def z225 : W := mkw 0xfbc7fdfffb790fa4 0x7de3fefffdbc87d2 0xffffffffffff3fe7 0xffffffffffff9ff3

def z226 : W := mkw 0xfb07fdffbb780780 0x7d83feffddbc03c0 0xdcf7d9ffc3fc07c0 0xee7becffe1fe03e0

def z227 : W := mkw 0x33c009bed2510fa4 0x19e004df692887d2 0x3c0001ffd00007e6 0x1e0000ffe80003f3

def z228 : W := mkw 0x0000000000000000 0x0000000000000000 0x0308580000033801 0x01842c0000019c00

def z229 : W := mkw 0xf007fcdbb8000000 0x7803fe6ddc000000 0x7ffffffffe333801 0xbfffffffff199c00

def z230 : W := mkw 0x0400020000046000 0x0200010000023000 0x02808600000c2000 0x8140430000061000

def z231 : W := mkw 0xfb07fdffbb780780 0x7d83feffddbc03c0 0x002759fdc3f00000 0x0013acfee1f80000

def z232 : W := mkw 0xdfc59f0cd33d7d24 0x6fe2cf86699ebe92 0x77b9df1dd23f3d27 0xbbdcef8ee91f9e93

def z233 : W := mkw 0x10c00808d0010824 0x0860040468008412 0x00085801c0031800 0x00042c00e0018c00

def z234 : W := mkw 0x042002000404604a 0x8210010002023025 0xc0000000000ce7ff 0xe0000000000673ff

def z235 : W := mkw 0x52827d69fac38631 0x29413eb4fd61c318 0xef7e7fe1ffc3c639 0x77bf3ff0ffe1e31c

def z236 : W := mkw 0xdfc7ff0cd3bffd24 0x6fe3ff8669dffe92 0xf7ffff1dd3fffd27 0xfbffff8ee9fffe93

def z237 : W := mkw 0xab0581b603780780 0x5582c0db01bc03c0 0xc84680e203fc07c0 0xe423407101fe03e0

def z238 : W := mkw 0x042002000404604a 0x8210010002023025 0xbfd0a6023c0cc2d8 0x5fe853011e06616c

def z239 : W := mkw 0x0100000400100100 0x0080000200080080 0x1081001c00300100 0x8840800e00180080

def z240 : W := mkw 0x062003200644664a 0x8310019003223325 0xfff6a7e23fcce7ff 0xfffb53f11fe673ff

def z241 : W := mkw 0x33c009bed2510fa4 0x19e004df692887d2 0x7fb959ffd2333fe7 0xbfdcacffe9199ff3

def z242 : W := mkw 0x330009ffba500780 0x198004ffdd2803c0 0x3c0001fffc0007c0 0x1e0000fffe0003e0

def z243 : W := mkw 0x10c00808d0010824 0x0860040468008412 0x77985801d0033d27 0xbbcc2c00e8019e93

def z244 : W := mkw 0x1000080890000000 0x0800040448000000 0x37b1591dd0000000 0x1bd8ac8ee8000000

def z245 : W := mkw 0x272003b6065467ca 0x939001db032a33e5 0xffd0a7fe3c0ce7ff 0xffe853ff1e0673ff

def z246 : W := mkw 0x042002000404604a 0x8210010002023025 0x3fd0a6023c00e03f 0x1fe853011e00701f

def z247 : W := mkw 0x1340090c92100d04 0x09a0048649080682 0x56b1191c12303d06 0xab588c8e09181e83

def z248 : W := mkw 0xed07f69601bef180 0x7683fb4b00df78c0 0xd3fffe1e03fff9c1 0xe9ffff0f01fffce0

def z249 : W := mkw 0x0400020000046000 0x0200010000023000 0xc3f9fe00023ff801 0xe1fcff00011ffc00

def z250 : W := mkw 0x02a2616166c3867b 0x815130b0b361c33d 0xfd7e61e3ffc3c7ff 0x7ebf30f1ffe1e3ff

def z251 : W := mkw 0xcc07f60001aef000 0x6603fb0000d77800 0xfffffe023ffff801 0xffffff011ffffc00

def z252 : W := mkw 0xa90580b601780380 0x5482c05b00bc01c0 0x98c780fe01fc03c0 0xcc63c07f00fe01e0

def z253 : W := mkw 0xcc07f66121eef211 0x6603fb3090f77908 0xcbfffee023fffa19 0xe5ffff7011fffd0c

def z254 : W := mkw 0x0282616162c38631 0x014130b0b161c318 0xfdfee1e3e3cfc7f9 0xfeff70f1f1e7e3fc

def z255 : W := mkw 0x0200012002400600 0x0100009001200300 0x002601e003c00000 0x001300f001e00000

def z256 : W := mkw 0xcc27f60005aef04a 0xe613fb0002d77825 0xcbfffe022ffffad9 0xe5ffff0117fffd6c

def z257 : W := mkw 0x0280012042c38631 0x014000902161c318 0xc008000003c3c639 0x6004000001e1e31c

def z258 : W := mkw 0x0280010042010420 0x0140008021008210 0xed786101e203c639 0x76bc3080f101e31c

def z259 : W := mkw 0x440276000086f000 0x22013b0000437800 0xc3d8fe00000ff801 0xe1ec7f000007fc00

def z260 : W := mkw 0x042002000404604a 0x8210010002023025 0xfff9fe023e3fffff 0xfffcff011f1fffff

def z261 : W := mkw 0x0000000000000000 0x0000000000000000 0x4008000002333801 0xa004000001199c00

def z262 : W := mkw 0xbb0589be93780780 0x5d82c4df49bc03c0 0xfff7d9ffd3fc07c0 0xfffbecffe9fe03e0

def z263 : W := mkw 0xcc07f60001aef000 0x6603fb0000d77800 0xeffffe0023fffe39 0xf7ffff0011ffff1c

def z264 : W := mkw 0x00c0000040010824 0x0060000020008412 0x0008000000033827 0x0004000000019c13

def z265 : W := mkw 0xa005809200000000 0x5002c04900000000 0x084680e200000000 0x0423407100000000

def z266 : W := mkw 0x0682636162c7e631 0x034131b0b163f318 0xeffee7e1e3cfe639 0xf7ff73f0f1e7f31c

def z267 : W := mkw 0xed059696013c7180 0x7682cb4b009e38c0 0x12819e1e003c39c0 0x8940cf0f001e1ce0

def z268 : W := mkw 0x042002000404604a 0x8210010002023025 0xded086021c0c27c6 0xef6843010e0613e3

def z269 : W := mkw 0x0280012042410631 0x0140009021208318 0x0000000000000638 0x000000000000031c

def z270 : W := mkw 0x0400020000046000 0x0200010000023000 0x030026000000e001 0x0180130000007000

def z271 : W := mkw 0xf427fedbbc04604a 0xfa13ff6dde023025 0x3ff7fffffc00e03f 0x1ffbfffffe00701f

def z272 : W := mkw 0x0300010402100500 0x0180008201080280 0x54b1011c02300500 0xaa58808e01180280

def z273 : W := mkw 0xec07f6b201eef280 0x7603fb5900f77940 0xcbfffee203fffac1 0xe5ffff7101fffd60

def z274 : W := mkw 0x042002000404604a 0x8210010002023025 0xc840a6022c0ce7ff 0xe4205301160673ff

def z275 : W := mkw 0x13c0090cd2110d24 0x09e0048669088692 0x63085801d2333d27 0xb1842c00e9199e93

def z276 : W := mkw 0xef87f7f763fff7b1 0x77c3fbfbb1fffbd8 0xffffffffe3fffff9 0xfffffffff1fffffc

def z277 : W := mkw 0x15600a0c9414694e 0x8ab005064a0a34a7 0x12819e1e1c3c39c6 0x8940cf0f0e1e1ce3

def z278 : W := mkw 0x8805800001280000 0x4402c00000940000 0xc0f7800003fc0000 0xe07bc00001fe0000

def z279 : W := mkw 0xf007fcfbb8c28211 0x7803fe7ddc614108 0xbff7fffffdc0c218 0x5ffbfffffee0610c

def z280 : W := mkw 0x448276416087f031 0x22413b20b043f818 0x23087e01e003f839 0x11843f00f001fc1c

def z281 : W := mkw 0x13c0090cd2110d24 0x09e0048669088692 0xfff9d91fd23f3fe7 0xfffcec8fe91f9ff3

def z282 : W := mkw 0xa30581b602500780 0x5182c0db012803c0 0x1cf781fe000007c0 0x0e7bc0ff000003e0

def z283 : W := mkw 0xf007fcdbb8000000 0x7803fe6ddc000000 0xfff7fffffc00c639 0x7ffbfffffe00631c

def z284 : W := mkw 0x0000000000000000 0x0000000000000000 0x4138400002030001 0x209c200001018000

def z285 : W := mkw 0x0000000000000000 0x0000000000000000 0x0281180000303800 0x81408c0000181c00

def z286 : W := mkw 0x1000080890000000 0x0800040448000000 0x1281181c10000000 0x09408c0e08000000

def z287 : W := mkw 0x14e00a08d405686e 0x8a7005046a02b437 0x23087e01fc03f83f 0x11843f00fe01fc1f

def z288 : W := mkw 0x13c0090cd2110d24 0x09e0048669088692 0x7790011dd0002527 0xbbc8008ee8001293

def z289 : W := mkw 0xab07e1f723fa8791 0x5583f0fb91fd43c8 0xdcf7a1fe23fcc7d8 0xee7bd0ff11fe63ec

def z290 : W := mkw 0xf007fcdbb8828000 0x7803fe6ddc414000 0xffffffffffc3c001 0x7fffffffffe1e000

def z291 : W := mkw 0xe007f4d328000000 0x7003fa6994000000 0x3fd6a6e23c000000 0x1feb53711e000000

def z292 : W := mkw 0xac2582b2056c62ca 0xd612c15902b63165 0x8846a6e22dccc2d8 0x4423537116e6616c

def z293 : W := mkw 0x53c27d4dfa110d24 0x29e13ea6fd088692 0x77b97f1dfe333d27 0xbbdcbf8eff199e93

def z294 : W := mkw 0xa905809601380180 0x5482c04b009c00c0 0x0001001c00300000 0x0000800e00180000

def z295 : W := mkw 0x10026849b0000000 0x08013424d8000000 0x3ff779fdf0000000 0x1ffbbcfef8000000

def z296 : W := mkw 0xbbc589bed3790fa4 0x5de2c4df69bc87d2 0xdcffd9ffc3ff1fc0 0xee7fecffe1ff8fe0

def z297 : W := mkw 0x17c00b0cd2156d24 0x0be00586690ab692 0xf7f9ff1dd23ffd27 0xfbfcff8ee91ffe93

def z298 : W := mkw 0xbbc589bed3790fa4 0x5de2c4df69bc87d2 0x002f59fdc3f31800 0x0017acfee1f98c00

def z299 : W := mkw 0xc407f6000086f000 0x6203fb0000437800 0x03fffe000003f801 0x01ffff000001fc00

def z300 : W := mkw 0xf007fc9a98000000 0x7803fe4d4c000000 0x13f7fe1e1c000000 0x09fbff0f0e000000

def z301 : W := mkw 0x06a0032046c7e67b 0x835001902363f33d 0xffd8a6023fcfe7ff 0xffec53011fe7f3ff

def z302 : W := mkw 0xab0581b603780780 0x5582c0db01bc03c0 0x1cf781fe03f00000 0x0e7bc0ff01f80000

def z303 : W := mkw 0x0202616122400600 0x010130b091200300 0xed7661e1e3c00600 0x76bb30f0f1e00300

def z304 : W := mkw 0xcf07f72403fef780 0x6783fb9201ff7bc0 0xc3fffe0003ffffc1 0xe1ffff0001ffffe0

def z305 : W := mkw 0x13c0090cd2110d24 0x09e0048669088692 0x3681191dd0303d26 0x9b408c8ee8181e93

def z306 : W := mkw 0x1140080c90100904 0x08a0040648080482 0x53b9581c12333907 0xa9dcac0e09199c83

def z307 : W := mkw 0xf027fcdbbc00004a 0xf813fe6dde000025 0x3ff7fffffc0007fe 0x1ffbfffffe0003ff

def z308 : W := mkw 0x042002000404604a 0x8210010002023025 0x779026003c00e53f 0xbbc813001e00729f

def z309 : W := mkw 0x042002000404604a 0x8210010002023025 0x230026003c00e03f 0x118013001e00701f

def z310 : W := mkw 0xef07f7b603fef780 0x7783fbdb01ff7bc0 0xdcf7a7fe03fcc7c0 0xee7bd3ff01fe63e0

def z311 : W := mkw 0x042002000404604a 0x8210010002023025 0xef5026003c00e63f 0x77a813001e00731f

def z312 : W := mkw 0xcc05960001aef000 0x6602cb0000d77800 0xc2899e0003fff801 0xe144cf0001fffc00

def z313 : W := mkw 0xac2582b2056c62ca 0xd612c15902b63165 0xffd6a6e23dcce7ff 0xffeb53711ee673ff

def z314 : W := mkw 0x0000000000000000 0x0000000000000000 0x03b1580000000000 0x01d8ac0000000000

def z315 : W := mkw 0x0c20020005aef04a 0x8610010002d77825 0xffd8a6023fffffff 0xffec53011fffffff

def z316 : W := mkw 0xab0581b603780780 0x5582c0db01bc03c0 0x10a781fe03fc01c0 0x8853c0ff01fe00e0

def z317 : W := mkw 0x002000000400004a 0x8010000002000025 0x200000003c00003e 0x100000001e00001f

def z318 : W := mkw 0xbbc589bed3790fa4 0x5de2c4df69bc87d2 0x77bf59fdd3f33d27 0xbbdfacfee9f99e93

def z319 : W := mkw 0x230001b602500780 0x118000db012803c0 0x5cb101fe023007c0 0xae5880ff011803e0

def z320 : W := mkw 0xf007fcdbb8000000 0x7803fe6ddc000000 0x1ac7befe3c000000 0x0d63df7f1e000000

def z321 : W := mkw 0xf0059c9a98000000 0x7802ce4d4c000000 0x37b1df1fdc000000 0x1bd8ef8fee000000

def z322 : W := mkw 0xe007f4f328c28211 0x7003fa7994614108 0x8846a6e22dc0c218 0x4423537116e0610c

def z323 : W := mkw 0x13c0090cd2110d24 0x09e0048669088692 0x7ff9ff1ffe333d27 0xbffcff8fff199e93

def z324 : W := mkw 0x0002604120000000 0x0001302090000000 0x002641e1c0000000 0x001320f0e0000000

def z325 : W := mkw 0x0000000000000000 0x0000000000000000 0x88408002000c02c0 0x4420400100060160

def z326 : W := mkw 0x0000000000000000 0x0000000000000000 0xc0d08000000c0000 0xe068400000060000

def z327 : W := mkw 0x042002000404604a 0x8210010002023025 0xbc40a6023c0cc7fe 0x5e2053011e0663ff

def z328 : W := mkw 0x0280012042c38631 0x014000902161c318 0xcc7e01e003c3c639 0x663f00f001e1e31c

def z329 : W := mkw 0xaf0583b6037c6780 0x5782c1db01be33c0 0xdff7a7fe03fce7c1 0xeffbd3ff01fe73e0

def z330 : W := mkw 0x13c2690cd2938d24 0x09e134866949c692 0xf7ff791dd3f3fd27 0xfbffbc8ee9f9fe93

def z331 : W := mkw 0xa80580b201680280 0x5402c05900b40140 0x000600e001c00000 0x0003007000e00000

def z332 : W := mkw 0xf3c7fddffa110d24 0x79e3feeffd088692 0x3ffffffffe331800 0x1fffffffff198c00

def z333 : W := mkw 0x4002740000829000 0x20013a0000414800 0x0008580000031800 0x00042c0000018c00

def z334 : W := mkw 0xf307fddfba100500 0x7983feefdd080280 0x7ff7fffffe300500 0xbffbffffff180280

def z335 : W := mkw 0xab0581b603780780 0x5582c0db01bc03c0 0xdfffd9fe03ff3fc1 0xefffecff01ff9fe0

def z336 : W := mkw 0x002000000400004a 0x8010000002000025 0x100000021c0001c6 0x080000010e0000e3

def z337 : W := mkw 0x0280016162410631 0x014000b0b1208318 0x000001e1c0000000 0x000000f0e0000000

def z338 : W := mkw 0x0280010042010420 0x0140008021008210 0x4008000002030421 0x2004000001018210

def z339 : W := mkw 0x12c00908d2010c24 0x0960048469008612 0x67385901d2033c27 0x339c2c80e9019e13

def z340 : W := mkw 0x1fc00b0cd3bffd24 0x0fe0058669dffe92 0xf7b9591dd3fffd27 0xfbdcac8ee9fffe93

def z341 : W := mkw 0x0002600000828000 0x0001300000414000 0x002e400003c30000 0x0017200001e18000

def z342 : W := mkw 0xeb07f5b603fa9780 0x7583fadb01fd4bc0 0xdcffd9fe03ff1fc0 0xee7fecff01ff8fe0

def z343 : W := mkw 0xeb07f5b603fa9780 0x7583fadb01fd4bc0 0x002f59fc03f31800 0x0017acfe01f98c00

def z344 : W := mkw 0xf807fcdbb9aa9000 0x7c03fe6ddcd54800 0x002f59fdc3f31800 0x0017acfee1f98c00

def z345 : W := mkw 0xf007fcdbb8000000 0x7803fe6ddc000000 0x0867ffffec000000 0x0433fffff6000000

def z346 : W := mkw 0xef27f7b607fef7ca 0xf793fbdb03ff7be5 0xfffffffe3fffffff 0xffffffff1fffffff

def z347 : W := mkw 0x0000000000000000 0x0000000000000000 0x40b1000002300000 0xa058800001180000

def z348 : W := mkw 0x042002000404604a 0x8210010002023025 0xed50a6022c0cc6f9 0x76a853011606637c

def z349 : W := mkw 0x0080000040010020 0x0040000020008010 0x21084001c0030021 0x10842000e0018010

def z350 : W := mkw 0xad258296053c61ca 0xd692c14b029e30e5 0xffd1a61e3c3ce7ff 0xffe8d30f1e1e73ff

def z351 : W := mkw 0x0000000000000000 0x0000000000000000 0xc0000000000c07c0 0xe0000000000603e0

def z352 : W := mkw 0xb005889a90000000 0x5802c44d48000000 0x3ff7d9ffd0000000 0x1ffbecffe8000000

def z353 : W := mkw 0x0800000001280000 0x0400000000940000 0xc000000003fc0000 0xe000000001fe0000

def z354 : W := mkw 0x0000002000400200 0x0000001000200100 0x884600e001c00200 0x4423007000e00100

def z355 : W := mkw 0x11c0080cd0110924 0x08e0040668088492 0x3389581dd0333927 0x99c4ac0ee8199c93

def z356 : W := mkw 0xab07e1b603fa8780 0x5583f0db01fd43c0 0xddffe1fe03ffc7c1 0xeefff0ff01ffe3e0

def z357 : W := mkw 0x042002000404604a 0x8210010002023025 0xed502000200ce7ff 0xf6a81000100673ff

def z358 : W := mkw 0x13e0090cd6110d6e 0x89f004866b0886b7 0x3c00011ffc0007fe 0x1e00008ffe0003ff

def z359 : W := mkw 0xf7e7ffdffe156d6e 0xfbf3ffefff0ab6b7 0xfffffffffe3fffff 0xffffffffff1fffff

def z360 : W := mkw 0xffc7ffbed3ffffa4 0x7fe3ffdf69ffffd2 0xffffffffd3ffffe7 0xffffffffe9fffff3

def z361 : W := mkw 0xf807fcdbb9280000 0x7c03fe6ddc940000 0xfff7fffffffc0000 0xfffbfffffffe0000

def z362 : W := mkw 0x0000000000000000 0x0000000000000000 0x884020002000c218 0x442010001000610c

def z363 : W := mkw 0x0000000000000000 0x0000000000000000 0xc15020000000c001 0x60a8100000006000

def z364 : W := mkw 0x0000000000000000 0x0000000000000000 0x7fd0a6023c002527 0xbfe853011e001293

def z365 : W := mkw 0xf147fcdfb8100904 0x78a3fe6fdc080482 0x3ff7fffffc303906 0x9ffbfffffe181c83

def z366 : W := mkw 0x0282616162c38631 0x014130b0b161c318 0xfffe61e1f3c3e73f 0xffff30f0f9e1f39f

def z367 : W := mkw 0xf007fcdbb8000000 0x7803fe6ddc000000 0x23277ffdfc000000 0x1193bffefe000000

def z368 : W := mkw 0x300008dbb8000000 0x1800046ddc000000 0x3fd0a7fffc000000 0x1fe853fffe000000

def z369 : W := mkw 0x02a001616641067b 0x815000b0b320833d 0x3c0001e3fc0007fe 0x1e0000f1fe0003ff

def z370 : W := mkw 0x0002606120c28211 0x0001303090614108 0xed5620e021c0c639 0x76ab107010e0631c

def z371 : W := mkw 0xa005809200000000 0x5002c04900000000 0xdcf781fe000c07c0 0xee7bc0ff000603e0

def z372 : W := mkw 0x0300012402500780 0x01800092012803c0 0x00000000000007c0 0x00000000000003e0

def z373 : W := mkw 0x13c0090cd2110d24 0x09e0048669088692 0x74b1011dd2300526 0xba58808ee9180293

def z374 : W := mkw 0x4c02760001aef000 0x26013b0000d77800 0xc3087e0003fff801 0xe1843f0001fffc00

def z375 : W := mkw 0xcc07f64121aef000 0x6603fb2090d77800 0xefffffe1e3fff801 0xf7fffff0f1fffc00

def z376 : W := mkw 0xf007fcdbb8000000 0x7803fe6ddc000000 0xfff7fffffc0c07c0 0xfffbfffffe0603e0

def z377 : W := mkw 0xafa7e3f767ffe7fb 0xd7d3f1fbb3fff3fd 0xffffe7ffffffe7ff 0xfffff3fffffff3ff

def z378 : W := mkw 0x042002000404604a 0x8210010002023025 0xd3d0a6021c0ce1c7 0xe9e853010e0670e3

def z379 : W := mkw 0xa805809201280000 0x5402c04900940000 0xdcf781fe03fc0000 0xee7bc0ff01fe0000

def z380 : W := mkw 0x0280010042010420 0x0140008021008210 0x77b84101d2032527 0xbbdc2080e9019293

def z381 : W := mkw 0x0000000000000000 0x0000000000000000 0x3790000010000000 0x1bc8000008000000

def z382 : W := mkw 0x0082606160c38231 0x00413030b061c118 0xa94e60e1e1c3c239 0x54a73070f0e1e11c

def z383 : W := mkw 0xa80580b201680280 0x5402c05900b40140 0xc8f780e203fc02c0 0xe47bc07101fe0160

def z384 : W := mkw 0x042002000404604a 0x8210010002023025 0xc3d0a600000ce7ff 0xe1e85300000673ff

def z385 : W := mkw 0xbb4589be93780f84 0x5da2c4df49bc07c2 0xdef799fe13fc3fc6 0xef7bccff09fe1fe3

def z386 : W := mkw 0xdd459e0c913c7904 0x6ea2cf06489e3c82 0x12819e1c103c3906 0x8940cf0e081e1c83

def z387 : W := mkw 0xab0581b603780780 0x5582c0db01bc03c0 0x1c2701fe03f007c0 0x0e1380ff01f803e0

def z388 : W := mkw 0x0280010042010420 0x0140008021008210 0x24000101c0000420 0x12000080e0000210

def z389 : W := mkw 0x002000000400004a 0x8010000002000025 0x080000022c0002d8 0x040000011600016c

def z390 : W := mkw 0x0002600000828000 0x0001300000414000 0xed7e600023c3c639 0x76bf300011e1e31c

def z391 : W := mkw 0xc007f40000000000 0x6003fa0000000000 0x0027580000000000 0x0013ac0000000000

def z392 : W := mkw 0xf4259e9a9c04604a 0xfa12cf4d4e023025 0xffd1be1e3c0ce7ff 0xffe8df0f1e0673ff

def z393 : W := mkw 0x03c0010442110d24 0x01e0008221088692 0x0000000000000526 0x0000000000000293

def z394 : W := mkw 0x0082604160838031 0x00413020b041c018 0x2d7e61e1e003c039 0x16bf30f0f001e01c

def z395 : W := mkw 0x0280016162c38631 0x014000b0b161c318 0xec0801e1e3c3c639 0x760400f0f1e1e31c

def z396 : W := mkw 0xcc07f60001aef000 0x6603fb0000d77800 0x02afde0003ff3800 0x8157ef0001ff9c00

def z397 : W := mkw 0x0300012402500700 0x0180009201280380 0xdcf701fc03f00700 0xee7b80fe01f80380

def z398 : W := mkw 0xfe87fffbfbeff631 0x7f43fffdfdf7fb18 0xfffffffffffffe39 0xffffffffffffff1c

def z399 : W := mkw 0xc287f56162c38631 0x6143fab0b161c318 0xefffffe1e3c3c639 0x77fffff0f1e1e31c

def z400 : W := mkw 0x0002600000828000 0x0001300000414000 0x8046200001c0c000 0x4023100000e06000

def z401 : W := mkw 0x042262412404604a 0x8211312092023025 0xfff6e7e3fc0ce7ff 0xfffb73f1fe0673ff

def z402 : W := mkw 0xef07f7b603fef780 0x7783fbdb01ff7bc0 0xc3fffffc03fff801 0xe1fffffe01fffc00

def z403 : W := mkw 0xabc581b643790fa4 0x55e2c0db21bc87d2 0xdcff81fe03ff3fe7 0xee7fc0ff01ff9ff3

def z404 : W := mkw 0x33c009dffa110d24 0x19e004effd088692 0x7fb959fffe333d27 0xbfdcacffff199e93

def z405 : W := mkw 0xce87f76163eff631 0x6743fbb0b1f7fb18 0xc3ffffe1c3fff801 0xe1fffff0e1fffc00

def z406 : W := mkw 0x2100009600100180 0x1080004b000800c0 0x1000001e000001c0 0x0800000f000000e0

def z407 : W := mkw 0xce87f72043eff631 0x6743fb9021f7fb18 0xc3fffe0003fffe39 0xe1ffff0001ffff1c

def z408 : W := mkw 0x17e00b0cd6156d6e 0x8bf005866b0ab6b7 0x77b9df1fde3f3de7 0xbbdcef8fef1f9ef3

def z409 : W := mkw 0x10c26849f0838835 0x08613424f841c41a 0x23087801f003f83f 0x11843c00f801fc1f

def z410 : W := mkw 0x0002604120000000 0x0001302090000000 0x084620e020000000 0x0423107010000000

def z411 : W := mkw 0x0000000000000000 0x0000000000000000 0xcc50000000000600 0x6628000000000300

def z412 : W := mkw 0x07e0030446156d6e 0x83f00182230ab6b7 0xc0080000023fffff 0xe0040000011fffff

def z413 : W := mkw 0x13c2694df2938d35 0x09e134a6f949c69a 0x77b9791df233fd3f 0xbbdcbc8ef919fe9f

def z414 : W := mkw 0xcc07f60001aef000 0x6603fb0000d77800 0xc04ea60003fff801 0xe027530001fffc00

def z415 : W := mkw 0x0000000000000000 0x0000000000000000 0xffd0a6023c0c07c0 0xffe853011e0603e0

def z416 : W := mkw 0x17e26b6df6d7ef7f 0x8bf135b6fb6bf7bf 0xffffffffffffffff 0xffffffffffffffff

def z417 : W := mkw 0x0300010402100500 0x0180008201080280 0x0021011c02300000 0x0010808e01180000

def z418 : W := mkw 0xdbc7fd0cd3bb9d24 0x6de3fe8669ddce92 0x77bf591dd3f33d27 0xbbdfac8ee9f99e93

def z419 : W := mkw 0x8805800001280000 0x4402c00000940000 0x00818000003c0000 0x8040c000001e0000

def z420 : W := mkw 0xab87e1f763fb87b1 0x55c3f0fbb1fdc3d8 0xed7f61fde3f3c639 0x76bfb0fef1f9e31c

def z421 : W := mkw 0xc805940001281000 0x6402ca0000940800 0x0001180000301800 0x00008c0000180c00

def z422 : W := mkw 0xf0c7fcdbf8010824 0x7863fe6dfc008412 0x3ffffffffc033827 0x1ffffffffe019c13

def z423 : W := mkw 0xcc07f60001aef000 0x6603fb0000d77800 0x83f7fe0001ccc000 0x41fbff0000e66000

def z424 : W := mkw 0x0282616162c38631 0x014130b0b161c318 0x2d0861e1e003c639 0x168430f0f001e31c

def z425 : W := mkw 0x0082604160838031 0x00413020b041c018 0xe17e6001e3c3c039 0x70bf3000f1e1e01c

def z426 : W := mkw 0xf207fdfbba400600 0x7903fefddd200300 0xfff7ffffffc00600 0x7ffbffffffe00300

def z427 : W := mkw 0xab8581b643fb87b1 0x55c2c0db21fdc3d8 0xdcff81fe03ffc7f9 0xee7fc0ff01ffe3fc

def z428 : W := mkw 0x04a262416487e07b 0x82513120b243f03d 0x23086601fc03e03f 0x11843300fe01f01f

def z429 : W := mkw 0xf6a7fffbfec7e67b 0xfb53fffdff63f33d 0xffffffffffcfe7ff 0xffffffffffe7f3ff

def z430 : W := mkw 0xcc259600052c704a 0xe612cb0002963825 0xffd1be023c3cffff 0xffe8df011e1e7fff

def z431 : W := mkw 0xc407f60000046000 0x6203fb0000023000 0xc3f7fe00000ce001 0xe1fbff0000067000

def z432 : W := mkw 0x0000000000000000 0x0000000000000000 0xc00000000000c639 0x600000000000631c

def z433 : W := mkw 0xf807fcfbb9680280 0x7c03fe7ddcb40140 0xbff7fffffdcc02c0 0x5ffbfffffee60160

def z434 : W := mkw 0xf9059c9e99380180 0x7c82ce4f4c9c00c0 0x12819e1e1c3c01c0 0x8940cf0f0e1e00e0

def z435 : W := mkw 0x03c0010442110d24 0x01e0008221088692 0x54b9011c02333d27 0xaa5c808e01199e93

def z436 : W := mkw 0x13c2696df2d38f35 0x09e134b6f969c79a 0x002f59fdc3f31800 0x0017acfee1f98c00

def z437 : W := mkw 0x0000000000000000 0x0000000000000000 0x2300000010002027 0x1180000008001013

def z438 : W := mkw 0xbfe58bbed77d6fee 0xdff2c5df6bbeb7f7 0xffffffffffffffff 0xffffffffffffffff

def z439 : W := mkw 0x0280012042410620 0x0140009021208310 0xed7e41e1c3c30621 0x76bf20f0e1e18310

def z440 : W := mkw 0x0800002001680280 0x0400001000b40140 0x8000000001cc02c0 0x4000000000e60160

def z441 : W := mkw 0xfc059e9a992c7000 0x7e02cf4d4c963800 0x12819e1e1c3c3800 0x8940cf0f0e1e1c00

def z442 : W := mkw 0x0000000000000000 0x0000000000000000 0x10808002000c01c0 0x88404001000600e0

def z443 : W := mkw 0x04a262416487e07b 0x82513120b243f03d 0xffd8e603fc0fe7ff 0xffec7301fe07f3ff

def z444 : W := mkw 0x0e80032043eff631 0x0740019021f7fb18 0xc008000003fffe39 0xe004000001ffff1c

def z445 : W := mkw 0xa20581b202400600 0x5102c0d901200300 0xdcf781fe03c00600 0x6e7bc0ff01e00300

def z446 : W := mkw 0x0382616562d38731 0x01c130b2b169c398 0xfdff61fde3f3c739 0xfeffb0fef1f9e39c

def z447 : W := mkw 0x440276000086f000 0x22013b0000437800 0x000026000000c000 0x0000130000006000

def z448 : W := mkw 0x0e82636163eff631 0x074131b0b1f7fb18 0xed7e61e1e3fffe39 0xf6bf30f0f1ffff1c

def z449 : W := mkw 0x0082604160838031 0x00413020b041c018 0x00084001c0030000 0x00042000e0018000

def z450 : W := mkw 0xa805809201280080 0x5402c04900940040 0x00008002000c00c0 0x0000400100060060

def z451 : W := mkw 0x1000080890000000 0x0800040448000000 0x3ff1ff1ffc000000 0x1ff8ff8ffe000000

def z452 : W := mkw 0x54227e49bc04604a 0xaa113f24de023025 0x23007e01fc00e03f 0x11803f00fe00701f

def z453 : W := mkw 0x0282616162410631 0x014130b0b1208318 0x2d7661e1e0000638 0x16bb30f0f000031c

def z454 : W := mkw 0xf007fcdbb8000000 0x7803fe6ddc000000 0x2d7779fde0000000 0x16bbbcfef0000000

def z455 : W := mkw 0x328009fbfa410631 0x194004fdfd208318 0x3c0001fffc000638 0x1e0000fffe00031c

def z456 : W := mkw 0x0c20020005aef04a 0x8610010002d77825 0xc008000003ffffff 0xe004000001ffffff

def z457 : W := mkw 0x13c0090cd2110d24 0x09e0048669088692 0x4029591dc2333d27 0xa014ac8ee1199e93

def z458 : W := mkw 0xf3c7fddffa110d24 0x79e3feeffd088692 0x77bf59fdd2333d27 0xbbdfacfee9199e93

def z459 : W := mkw 0xce87f76163eff631 0x6743fbb0b1f7fb18 0xed7ee7e1e3cfc639 0x76bf73f0f1e7e31c

def z460 : W := mkw 0x0000000000000000 0x0000000000000000 0x210020002000c039 0x108010001000601c

def z461 : W := mkw 0x0000000000000000 0x0000000000000000 0x1280000010002106 0x8940000008001083

def z462 : W := mkw 0x06a2636166c7e67b 0x835131b0b363f33d 0xed7ee7e3efcfc6f9 0x76bf73f1f7e7e37c

def z463 : W := mkw 0xab2581b6077807ca 0xd592c0db03bc03e5 0xfcf781fe3ffc07fe 0xfe7bc0ff1ffe03ff

def z464 : W := mkw 0x0282616162c38631 0x014130b0b161c318 0xe1086001e3c3c639 0x70843000f1e1e31c

def z465 : W := mkw 0xec07f6d329aef000 0x7603fb6994d77800 0x8846a6e22dccc000 0x4423537116e66000

def z466 : W := mkw 0xab8581b6437907a0 0x55c2c0db21bc83d0 0xfdffc1ffc3ff07e1 0xfeffe0ffe1ff83f0

def z467 : W := mkw 0xa807e0f321ea8291 0x5403f07990f54148 0x8846a0e221ccc2d8 0x4423507110e6616c

def z468 : W := mkw 0xcc27f60005aef04a 0xe613fb0002d77825 0xe3fffe003ffff83f 0xf1ffff001ffffc1f

def z469 : W := mkw 0x14e00a08d405686e 0x8a7005046a02b437 0xffd8fe03fc0fffff 0xffec7f01fe07ffff

def z470 : W := mkw 0x1000080890000000 0x0800040448000000 0x3400011dd0000000 0x1a00008ee8000000

def z471 : W := mkw 0x042002000404604a 0x8210010002023025 0xdcd08002000ce7ff 0xee684001000673ff

def z472 : W := mkw 0xcc059600012c7000 0x6602cb0000963800 0xc3d1be00003cf801 0xe1e8df00001e7c00

def z473 : W := mkw 0x238001f7625107b1 0x11c000fbb12883d8 0x3c0001ffe00007f8 0x1e0000fff00003fc

def z474 : W := mkw 0xf3c59d9eda110d24 0x79e2cecf6d088692 0x77b9df1fde333d27 0xbbdcef8fef199e93

def z475 : W := mkw 0x10c00808d0010824 0x0860040468008412 0x20000001d0000026 0x10000000e8000013

def z476 : W := mkw 0x0400020000046000 0x0200010000023000 0xefd0a600200ce639 0xf7e853001006731c

def z477 : W := mkw 0xa905809601380180 0x5482c04b009c00c0 0xdcd1801e003c07c0 0xee68c00f001e03e0

def z478 : W := mkw 0x0300010402100500 0x0180008201080280 0x1400011c00000500 0x0a00008e00000280

def z479 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z480 : W := mkw 0x0400020000046000 0x0200010000023000 0xc0000000000ce001 0xe000000000067000

def z481 : W := mkw 0xf4259e9a9c04604a 0xfa12cf4d4e023025 0x12819e1e1c0c21c6 0x8940cf0f0e0610e3

def z482 : W := mkw 0x8805800001280000 0x4402c00000940000 0x0027000003f00000 0x0013800001f80000

def z483 : W := mkw 0xdbc7fd0cd3bb9d24 0x6de3fe8669ddce92 0x002f591dc3f31800 0x0017ac8ee1f98c00

def z484 : W := mkw 0xf407fedbb8046000 0x7a03ff6ddc023000 0xfff7fffffc0ce001 0xfffbfffffe067000

def z485 : W := mkw 0xf007fcdbb8000000 0x7803fe6ddc000000 0x03f7fffdc0000000 0x01fbfffee0000000

def z486 : W := mkw 0xaf2583b6077c67ca 0xd792c1db03be33e5 0xdcf781fe03fce7ff 0xee7bc0ff01fe73ff

def z487 : W := mkw 0xf0059c9a98000000 0x7802ce4d4c000000 0x0001181c00000000 0x00008c0e00000000

def z488 : W := mkw 0x8807e00001aa8000 0x4403f00000d54000 0xc1ffe00003ffc001 0xe0fff00001ffe000

def z489 : W := mkw 0x0000000000000000 0x0000000000000000 0x0029580002331800 0x0014ac0001198c00

def z490 : W := mkw 0xf287fdfbfac38631 0x7943fefdfd61c318 0xed7f79fde3c3c639 0x76bfbcfef1e1e31c

def z491 : W := mkw 0x0282610042838420 0x014130802141c210 0xe57e6101c3c3c421 0x72bf3080e1e1e210

def z492 : W := mkw 0x1300090c92100500 0x0980048649080280 0x77b1591dd2300500 0xbbd8ac8ee9180280

def z493 : W := mkw 0x042002000404604a 0x8210010002023025 0x3380a6023c0ce1ff 0x99c053011e0670ff

def z494 : W := mkw 0xf3c7fddffa110d24 0x79e3feeffd088692 0x002f59fdc2331800 0x0017acfee1198c00

def z495 : W := mkw 0x0080004160010031 0x00400020b0008018 0x20000001e0000038 0x10000000f000001c

def z496 : W := mkw 0x0140000400100904 0x00a0000200080482 0x0000000000303906 0x8000000000181c83

def z497 : W := mkw 0xa80580b201680280 0x5402c05900b40140 0xdcd680e201cc07c0 0xee6b407100e603e0

def z498 : W := mkw 0x0000000000000000 0x0000000000000000 0x03d0a60000000000 0x01e8530000000000

def z499 : W := mkw 0x0000000000000000 0x0000000000000000 0x3c0000023c000000 0x1e0000011e000000

def z500 : W := mkw 0x17e00b0cd6156d6e 0x8bf005866b0ab6b7 0xf7b9591dd23fffff 0xfbdcac8ee91fffff

def z501 : W := mkw 0x4400160000047000 0x22000b0000023800 0x02001e0000003800 0x01000f0000001c00

def z502 : W := mkw 0xf0059cdbb8000000 0x7802ce6ddc000000 0x3e819ffffc000000 0x1f40cffffe000000

def z503 : W := mkw 0x0282614162010420 0x014130a0b1008210 0x6d7e61e1e2030421 0x36bf30f0f1018210

def z504 : W := mkw 0xa305819602100500 0x5182c0cb01080280 0x5cf781fe02300500 0xae7bc0ff01180280

def z505 : W := mkw 0xeb07f5f72b780780 0x7583fafb95bc03c0 0xdcf7a7fe2ffc07c0 0xee7bd3ff17fe03e0

def z506 : W := mkw 0x0000000000000000 0x0000000000000000 0xffd0a6023c00c639 0x7fe853011e00631c

def z507 : W := mkw 0x0200010002000400 0x0100008001000200 0x4430010002000400 0x2218008001000200

def z508 : W := mkw 0xce87f70043aff420 0x6743fb8021d7fa10 0xe7ffff01c3fffc21 0xf3ffff80e1fffe10

def z509 : W := mkw 0x300008dbb8000000 0x1800046ddc000000 0x000001fdc0000000 0x000000fee0000000

def z510 : W := mkw 0x0800000001aa9000 0x0400000000d54800 0x0008000003f31800 0x0004000001f98c00

def z511 : W := mkw 0xd007fc49b8000000 0x6803fe24dc000000 0x23f7fe01fc000000 0x11fbff00fe000000

def z512 : W := mkw 0x06a003616645667b 0x835001b0b322b33d 0xffd0a7e3fc0ce7ff 0xffe853f1fe0673ff

def z513 : W := mkw 0x0000000000000000 0x0000000000000000 0x2c00000020000638 0x160000001000031c

def z514 : W := mkw 0x0000000000000000 0x0000000000000000 0x25304101c0000000 0x12982080e0000000

def z515 : W := mkw 0x0000000000000000 0x0000000000000000 0x4390000000002001 0xa1c8000000001000

def z516 : W := mkw 0x002000000400004a 0x8010000002000025 0x00000000000007fe 0x00000000000003ff

def z517 : W := mkw 0xe007f4d328000000 0x7003fa6994000000 0x1cf7a7fe2c000000 0x0e7bd3ff16000000

def z518 : W := mkw 0xab0581b603780780 0x5582c0db01bc03c0 0x9c4681fe01cc07c0 0x4e2340ff00e603e0

def z519 : W := mkw 0x10000849b8000000 0x08000424dc000000 0x20000001fc000000 0x10000000fe000000

def z520 : W := mkw 0x328269fbfac38631 0x194134fdfd61c318 0xfd7e61ffffc3c639 0x7ebf30ffffe1e31c

def z521 : W := mkw 0x0282616162c38631 0x014130b0b161c318 0xc02e41e1c3c3c639 0x601720f0e1e1e31c

def z522 : W := mkw 0x042002000404604a 0x8210010002023025 0xdcd0a6022c0cc7d8 0xee685301160663ec

def z523 : W := mkw 0x0c00020001aef000 0x0600010000d77800 0xc3d8a60003fff801 0xe1ec530001fffc00

def z524 : W := mkw 0x0b80012443fb87b1 0x05c0009221fdc3d8 0xc008000003ffc7f9 0xe004000001ffe3fc

def z525 : W := mkw 0xdd47fe0c91bef904 0x6ea3ff0648df7c82 0xd3fffe1c13fff907 0xe9ffff0e09fffc83

def z526 : W := mkw 0x0300010402100500 0x0180008201080280 0x4000000002300500 0xa000000001180280

def z527 : W := mkw 0xd007fc0890000000 0x6803fe0448000000 0x37f7ff1dd0000000 0x1bfbff8ee8000000

def z528 : W := mkw 0x238261f762d387b1 0x11c130fbb169c3d8 0xfd7e61ffe3c3c7f9 0x7ebf30fff1e1e3fc

def z529 : W := mkw 0x1040080890000804 0x0820040448000402 0x0200180010003806 0x01000c0008001c03

def z530 : W := mkw 0x0000000000000000 0x0000000000000000 0x1c000002000007c0 0x0e000001000003e0

def z531 : W := mkw 0xf427fedbbc04604a 0xfa13ff6dde023025 0xbff7fffffc0cc2d8 0x5ffbfffffe06616c

def z532 : W := mkw 0x9bc5890cd3390d24 0x4de2c486699c8692 0xf7ffd91dd3ff3d27 0xfbffec8ee9ff9e93

def z533 : W := mkw 0x442276000486f04a 0xa2113b0002437825 0xffd8fe023c0fffff 0xffec7f011e07ffff

def z534 : W := mkw 0x042002000404604a 0x8210010002023025 0xe30026003c0ce7ff 0xf18013001e0673ff

def z535 : W := mkw 0x232001b6065007ca 0x919000db032803e5 0x3c0001fe3c0007fe 0x1e0000ff1e0003ff

def z536 : W := mkw 0x2b0001b603780780 0x158000db01bc03c0 0xdc0001fe03fc07c0 0xee0000ff01fe03e0

def z537 : W := mkw 0x0282616162c38631 0x014130b0b161c318 0xcc7e41e1c3c30600 0x663f20f0e1e18300

def z538 : W := mkw 0xab0581b603780780 0x5582c0db01bc03c0 0x54b701fc03f00500 0xaa5b80fe01f80280

def z539 : W := mkw 0x8a87e16163eb8631 0x4543f0b0b1f5c318 0xedffe1e1e3ffc639 0xf6fff0f0f1ffe31c

def z540 : W := mkw 0x0200012002400600 0x0100009001200300 0xed7621e023c0c639 0x76bb10f011e0631c

def z541 : W := mkw 0x50c27c49f8010824 0x28613e24fc008412 0x23087e01fc033827 0x11843f00fe019c13

def z542 : W := mkw 0xdfc7ff6df3ffff35 0x6fe3ffb6f9ffff9a 0xfffffffdf3ffff3f 0xfffffffef9ffff9f

def z543 : W := mkw 0xcc07f600012c7000 0x6603fb0000963800 0x03f7fe00003c3800 0x81fbff00001e1c00

def z544 : W := mkw 0x0002604120000000 0x0001302090000000 0x3ff6e7e3fc000000 0x1ffb73f1fe000000

def z545 : W := mkw 0xfb87fdfffbfb87b1 0x7dc3fefffdfdc3d8 0xffffffffffffc7f9 0xffffffffffffe3fc

def z546 : W := mkw 0x14200a089404604a 0x8a1005044a023025 0xfff1ff1ffc0ce7ff 0xfff8ff8ffe0673ff

def z547 : W := mkw 0x50827c49f8838031 0x28413e24fc41c018 0x23087e01fc03c039 0x11843f00fe01e01c

def z548 : W := mkw 0xb945889e91380984 0x5ca2c44f489c04c2 0x1281981e103c39c6 0x8940cc0f081e1ce3

def z549 : W := mkw 0x0300010402100500 0x0180008201080280 0x77b1011c12302527 0xbbd8808e09181293

def z550 : W := mkw 0x54c27e08d087f824 0x2a613f046843fc12 0x23087e01d003f827 0x11843f00e801fc13

def z551 : W := mkw 0xcc87f64161aff031 0x6643fb20b0d7f818 0xe3fffe01e3fff839 0xf1ffff00f1fffc1c

def z552 : W := mkw 0xf087fcdbf8838031 0x7843fe6dfc41c018 0x3ffffffffc03c039 0x1ffffffffe01e01c

def z553 : W := mkw 0xfb07fdffbb780780 0x7d83feffddbc03c0 0x3ff7fffffff00000 0x1ffbfffffff80000

def z554 : W := mkw 0x2000009200000000 0x1000004900000000 0x1c0001fe00000000 0x0e0000ff00000000

def z555 : W := mkw 0x042002000404604a 0x8210010002023025 0x3e8086023c0c27fe 0x9f4043011e0613ff

def z556 : W := mkw 0x200000b200400280 0x1000005900200140 0x080000e2000002c0 0x0400007100000160

def z557 : W := mkw 0x042002000404604a 0x8210010002023025 0x020006001c002006 0x010003000e001003

def z558 : W := mkw 0xab0581b603780780 0x5582c0db01bc03c0 0x1c8181fe003c07c0 0x8e40c0ff001e03e0

def z559 : W := mkw 0x0c02620001aef000 0x0601310000d77800 0xc17e600003fff801 0xe0bf300001fffc00

def z560 : W := mkw 0x0280012042c38631 0x014000902161c318 0x0008000003c30000 0x0004000001e18000

def z561 : W := mkw 0xf287fdfbfac38631 0x7943fefdfd61c318 0x002f59fdc3c30000 0x0017acfee1e18000

def z562 : W := mkw 0x13c0090cd2110d24 0x09e0048669088692 0x43b9591dc2333801 0xa1dcac8ee1199c00

def z563 : W := mkw 0x0f200324077c67ca 0x8790019203be33e5 0xc000000003fce7ff 0xe000000001fe73ff

def z564 : W := mkw 0x13c0090cd2110d24 0x09e0048669088692 0x3708591dd0033d27 0x1b842c8ee8019e93

def z565 : W := mkw 0x002000000400004a 0x8010000002000025 0xfcd080023c0c07fe 0xfe6840011e0603ff

def z566 : W := mkw 0x1000080890000000 0x0800040448000000 0x77b9591dd2333801 0xbbdcac8ee9199c00

def z567 : W := mkw 0xaa87e1f363eb86b1 0x5543f0f9b1f5c358 0xed7ee1e3e3cfc6f9 0x76bf70f1f1e7e37c

def z568 : W := mkw 0x50027c49b8000000 0x28013e24dc000000 0x37b17f1dfc000000 0x1bd8bf8efe000000

def z569 : W := mkw 0xcc07f66121eef211 0x6603fb3090f77908 0x8846a6e021ccc218 0x4423537010e6610c

def z570 : W := mkw 0x0002600000828000 0x0001300000414000 0x010860000003c001 0x008430000001e000

def z571 : W := mkw 0x0fc0030443bffd24 0x07e0018221dffe92 0xc008000003fffd27 0xe004000001fffe93

def z572 : W := mkw 0x002000000400004a 0x8010000002000025 0x3fd0a6023c0007fe 0x1fe853011e0003ff

def z573 : W := mkw 0x1000080890000000 0x0800040448000000 0x23005801d0000000 0x11802c00e8000000

def z574 : W := mkw 0xff07ffffbbfef780 0x7f83ffffddff7bc0 0xffffffffffffffc1 0xffffffffffffffe0

def z575 : W := mkw 0x0280016162410631 0x014000b0b1208318 0xec7601e1e3c00638 0x763b00f0f1e0031c

def z576 : W := mkw 0x8b05810403380500 0x4582c082019c0280 0xd4f7811c03fc0500 0xea7bc08e01fe0280

def z577 : W := mkw 0x8b05812403780780 0x4582c09201bc03c0 0xc0f7800003fc07c0 0xe07bc00001fe03e0

def z578 : W := mkw 0x8c058200012c6000 0x4602c10000963000 0xc3f7a60003fce001 0xe1fbd30001fe7000

def z579 : W := mkw 0x042002000404604a 0x8210010002023025 0x000086020c0c00c0 0x0000430106060060

def z580 : W := mkw 0x0002604120000000 0x0001302090000000 0xed7661e1e000c639 0x76bb30f0f000631c

def z581 : W := mkw 0xec07f6b201eef280 0x7603fb5900f77940 0x8846a6e201ccc2c0 0x4423537100e66160

def z582 : W := mkw 0x0000000000000000 0x0000000000000000 0x2d50200020000000 0x16a8100010000000

def z583 : W := mkw 0x042002000404604a 0x8210010002023025 0x3f0026023c00e7ff 0x1f8013011e0073ff

def z584 : W := mkw 0xaf2583b6077c67ca 0xd792c1db03be33e5 0xdcf7a7fe2ffcc7d8 0xee7bd3ff17fe63ec

def z585 : W := mkw 0xffc7ffdffbbffd24 0x7fe3ffeffddffe92 0xfffffffffffffd27 0xfffffffffffffe93

def z586 : W := mkw 0x12826969f2c38631 0x094134b4f961c318 0xffff79fdf3c3c639 0x7fffbcfef9e1e31c

def z587 : W := mkw 0x042002000404604a 0x8210010002023025 0x00000000000c21c6 0x80000000000610e3

def z588 : W := mkw 0x4002744128000000 0x20013a2094000000 0x000026002c000000 0x0000130016000000

def z589 : W := mkw 0x002000000400004a 0x8010000002000025 0xfd5020023c00c7ff 0x7ea810011e0063ff

def z590 : W := mkw 0x072003040614654a 0x83900182030a32a5 0xfff1a71e3e3ce7ff 0xfff8d38f1f1e73ff

def z591 : W := mkw 0x0200012002400600 0x0100009001200300 0xc000000003c00600 0x6000000001e00300

def z592 : W := mkw 0x0002600000000000 0x0001300000000000 0x0176600000000000 0x00bb300000000000

def z593 : W := mkw 0x13c2694df2110d24 0x09e134a6f9088692 0x7fff79fdf2333d27 0xbfffbcfef9199e93

def z594 : W := mkw 0xab07e1f723780780 0x5583f0fb91bc03c0 0xfdf7e1ffe3fc07c0 0xfefbf0fff1fe03e0

def z595 : W := mkw 0xf007fcdbb8000000 0x7803fe6ddc000000 0x3c2759fffc000000 0x1e13acfffe000000

def z596 : W := mkw 0xef0597b6037c7780 0x7782cbdb01be3bc0 0xdef79ffe03fc3fc0 0xef7bcfff01fe1fe0

def z597 : W := mkw 0x0000000000000000 0x0000000000000000 0x0840a6022c000000 0x0420530116000000

def z598 : W := mkw 0xcc27f60005aef04a 0xe613fb0002d77825 0xffd6a6023dcce7ff 0xffeb53011ee673ff

def z599 : W := mkw 0x8005800000000000 0x4002c00000000000 0x00f7800000000000 0x007bc00000000000

def z600 : W := mkw 0x1140080c90100904 0x08a0040648080482 0x37b1591dd0303906 0x9bd8ac8ee8181c83

def z601 : W := mkw 0x54227e49bc04604a 0xaa113f24de023025 0xffd0fe03fc0ce7ff 0xffe87f01fe0673ff

def z602 : W := mkw 0x13c0092cd2d38f35 0x09e004966969c79a 0xf7b9591dd3f3ff3f 0xfbdcac8ee9f9ff9f

def z603 : W := mkw 0xf1459c9e98100904 0x78a2ce4f4c080482 0x12819e1e1c303906 0x8940cf0f0e181c83

def z604 : W := mkw 0xaf2583b6077c67ca 0xd792c1db03be33e5 0xdef787fe1ffc27c6 0xef7bc3ff0ffe13e3

def z605 : W := mkw 0x0000000000000000 0x0000000000000000 0x3400000010000526 0x1a00000008000293

def z606 : W := mkw 0xe007f4d328000000 0x7003fa6994000000 0x000600e000000000 0x0003007000000000

def z607 : W := mkw 0x13c0090cd2110d24 0x09e0048669088692 0x6539591dc2331c21 0x329cac8ee1198e10

def z608 : W := mkw 0xe427f6d32c04604a 0xf213fb6996023025 0xffd6a6e23c0ce7ff 0xffeb53711e0673ff

def z609 : W := mkw 0x0b00012403780780 0x0580009201bc03c0 0x0000000003f00000 0x0000000001f80000

def z610 : W := mkw 0x0400020000046000 0x0200010000023000 0xffd0a6023c0ce001 0xffe853011e067000

def z611 : W := mkw 0x13c0090cd2110d24 0x09e0048669088692 0x7538411dd2030527 0x3a9c208ee9018293

def z612 : W := mkw 0x13c0090cd2110d24 0x09e0048669088692 0x5289181c12333d27 0xa9448c0e09199e93

def z613 : W := mkw 0x13c2696df2d38f35 0x09e134b6f969c79a 0xfd7e61fdf3c3c73f 0x7ebf30fef9e1e39f

def z614 : W := mkw 0x0280010042010420 0x0140008021008210 0x00284101c2030000 0x00142080e1018000

def z615 : W := mkw 0x50027c49b8000000 0x28013e24dc000000 0x00005801c0000000 0x00002c00e0000000

def z616 : W := mkw 0x0b00012403780780 0x0580009201bc03c0 0xdcd0800203fc07c0 0xee68400101fe03e0

def z617 : W := mkw 0x13c0090cd2110d24 0x09e0048669088692 0x3429591dd2331d26 0x1a14ac8ee9198e93

def z618 : W := mkw 0x0400020000046000 0x0200010000023000 0xdfd0a602000ce7c1 0xefe85301000673e0

def z619 : W := mkw 0x0400020000046000 0x0200010000023000 0x8040a600000cc000 0x4020530000066000

def z620 : W := mkw 0x0282616162c38631 0x014130b0b161c318 0x2c2e41e1e3c30638 0x161720f0f1e1831c

def z621 : W := mkw 0x03c0010442110d24 0x01e0008221088692 0x43b9580002333d27 0xa1dcac0001199e93

def z622 : W := mkw 0x0422626124c6e25b 0x821131309263712d 0x8846a6e22dccc2d8 0x4423537116e6616c

def z623 : W := mkw 0xc007f40000828000 0x6003fa0000414000 0xc3fffe0003c3c001 0x61ffff0001e1e000

def z624 : W := mkw 0x13c2696df2d38f35 0x09e134b6f969c79a 0x77bf59fdd3f33d27 0xbbdfacfee9f99e93

def z625 : W := mkw 0x0b00012403780780 0x0580009201bc03c0 0xcc7601e003fc07c0 0xe63b00f001fe03e0

def z626 : W := mkw 0x0282616162c38631 0x014130b0b161c318 0xc17e61e1c3c3c001 0x60bf30f0e1e1e000

def z627 : W := mkw 0x0282616162c38631 0x014130b0b161c318 0xc84e20e023c3c639 0x6427107011e1e31c

def z628 : W := mkw 0xfb059dbe9b780780 0x7d82cedf4dbc03c0 0xdef79ffe1ffc07c0 0xef7bcfff0ffe03e0

def z629 : W := mkw 0x1000080890000000 0x0800040448000000 0x77b1591dd0002527 0xbbd8ac8ee8001293

def z630 : W := mkw 0x0422626124c6e25b 0x821131309263712d 0xffd6a6e23dcce7ff 0xffeb53711ee673ff

def z631 : W := mkw 0x50027c49b8000000 0x28013e24dc000000 0x3fd0fe03fc000000 0x1fe87f01fe000000

def z632 : W := mkw 0x042002000404604a 0x8210010002023025 0xab40a6023c0ce2ff 0x55a053011e06717f

def z633 : W := mkw 0xcc07f60001aef000 0x6603fb0000d77800 0xc3d6a60001cce001 0xe1eb530000e67000

def z634 : W := mkw 0x06a0032046c7e67b 0x835001902363f33d 0xc008000003cfe7ff 0xe004000001e7f3ff

def z635 : W := mkw 0xab05819603380580 0x5582c0cb019c02c0 0x54b1811e023c05c0 0xaa58c08f011e02e0

def z636 : W := mkw 0x0000002000c28211 0x0000001000614108 0x8000000001c0c218 0x4000000000e0610c

def z637 : W := mkw 0xf287fdfbfa410631 0x7943fefdfd208318 0x3ff7fffffc000638 0x1ffbfffffe00031c

def z638 : W := mkw 0x0000000000000000 0x0000000000000000 0x1cd0800200000000 0x0e68400100000000

def z639 : W := mkw 0xe007f4d328000000 0x7003fa6994000000 0x0bf7fee22c000000 0x05fbff7116000000

def z640 : W := mkw 0x06a003004605646a 0x835001802302b235 0xfff8e703fe0fe7ff 0xfffc7381ff07f3ff

def z641 : W := mkw 0xcc27f60005aef04a 0xe613fb0002d77825 0x8846a6022dccc2d8 0x4423530116e6616c

def z642 : W := mkw 0x300008dbb8000000 0x1800046ddc000000 0x3fb159fffc000000 0x1fd8acfffe000000

def z643 : W := mkw 0x0202612002c28600 0x0101309001614300 0xcd7e61e003c3c601 0x66bf30f001e1e300

def z644 : W := mkw 0xeb07f5b603780780 0x7583fadb01bc03c0 0xdff7fffe03fc07c0 0xeffbffff01fe03e0

def z645 : W := mkw 0x0000000000000000 0x0000000000000000 0x6510000000000421 0x3288000000000210

def z646 : W := mkw 0x17e00b0cd6156d6e 0x8bf005866b0ab6b7 0x77b97f1dfe33fd3f 0xbbdcbf8eff19fe9f

def z647 : W := mkw 0x13e0090cd6110d6e 0x89f004866b0886b7 0x7fb9591ffe333fff 0xbfdcac8fff199fff

def z648 : W := mkw 0x0000006120400211 0x0000003090200108 0x080000e020000218 0x040000701000010c

def z649 : W := mkw 0xf0059c9a98000000 0x7802ce4d4c000000 0x1ef79ffe1c000000 0x0f7bcfff0e000000

def z650 : W := mkw 0xab8581f7637907b1 0x55c2c0fbb1bc83d8 0xfcf781ffe3fc07f8 0xfe7bc0fff1fe03fc

def z651 : W := mkw 0xe427f6d32c04604a 0xf213fb6996023025 0x8846a6e22c0cc2d8 0x442353711606616c

def z652 : W := mkw 0x8c258200052c604a 0xc612c10002963025 0xfff7a6023ffce7ff 0xfffbd3011ffe73ff

def z653 : W := mkw 0x03c0012442d38f35 0x01e000922169c79a 0xc008000003f3ff3f 0xe004000001f9ff9f

def z654 : W := mkw 0xc007f40000000000 0x6003fa0000000000 0x3ff7fe023c000000 0x1ffbff011e000000

def z655 : W := mkw 0x042002000404604a 0x8210010002023025 0xcbd0a6022c0ce2d9 0xe5e853011606716c

def z656 : W := mkw 0xa905809601380180 0x5482c04b009c00c0 0x1cf781fe003c01c0 0x8e7bc0ff001e00e0

def z657 : W := mkw 0x13c0090cd2110d24 0x09e0048669088692 0x37b9591dd2331800 0x1bdcac8ee9198c00

def z658 : W := mkw 0xe007f49200000000 0x7003fa4900000000 0x1ff7fffe00000000 0x0ffbffff00000000

def z659 : W := mkw 0x0000000000000000 0x0000000000000000 0x5490000000000500 0xaa48000000000280

def z660 : W := mkw 0x0000000000000000 0x0000000000000000 0xffd08002100c27e7 0xffe84001080613f3

def z661 : W := mkw 0x0b82616563fb87b1 0x05c130b2b1fdc3d8 0xed7e61e1e3ffc7f9 0xf6bf30f0f1ffe3fc

def z662 : W := mkw 0x0200012002400600 0x0100009001200300 0xdcf681e203cc07c0 0xee7b40f101e603e0

def z663 : W := mkw 0xcc07f60001aef000 0x6603fb0000d77800 0x834efe0001cff801 0x41a77f0000e7fc00

def z664 : W := mkw 0x200000d328000000 0x1000006994000000 0x080000e22c000000 0x0400007116000000

def z665 : W := mkw 0xc007f40000000000 0x6003fa0000000000 0x0046a60000000000 0x0023530000000000

def z666 : W := mkw 0xdfc7ff0cd3bffd24 0x6fe3ff8669dffe92 0xc3ffff1dc3fff801 0xe1ffff8ee1fffc00

def z667 : W := mkw 0x34200adbbc04604a 0x9a10056dde023025 0xffd0a7fffc0ce7ff 0xffe853fffe0673ff

def z668 : W := mkw 0x0000000000000000 0x0000000000000000 0x0c7601e000000000 0x063b00f000000000

def z669 : W := mkw 0x0000000000000000 0x0000000000000000 0xfdd0a002200cc7f9 0xfee85001100663fc

def z670 : W := mkw 0x0000000000828000 0x0000000000414000 0xc008000003c3c001 0x6004000001e1e000

def z671 : W := mkw 0xcc07f60001aef000 0x6603fb0000d77800 0xc17ee60003cfc001 0x60bf730001e7e000

def z672 : W := mkw 0x040002000086f000 0x0200010000437800 0x000800000003f801 0x000400000001fc00

def z673 : W := mkw 0x0002606120c28211 0x0001303090614108 0x000600e001c00000 0x0003007000e00000

def z674 : W := mkw 0xab0581b603780780 0x5582c0db01bc03c0 0xd081801e03fc07c0 0xe840c00f01fe03e0

def z675 : W := mkw 0x0300010402100500 0x0180008201080280 0x57b9591c02333d01 0xabdcac8e01199e80

def z676 : W := mkw 0x54027e49b886f000 0x2a013f24dc437800 0x23087e01fc03f801 0x11843f00fe01fc00

def z677 : W := mkw 0x0082604160838031 0x00413020b041c018 0xed586001e003c639 0x76ac3000f001e31c

def z678 : W := mkw 0x0002604120828011 0x0001302090414008 0x000020002000c018 0x000010001000600c

def z679 : W := mkw 0xa007e0d320000000 0x5003f06990000000 0x3df7e1ffe0000000 0x1efbf0fff0000000

def z680 : W := mkw 0x440276000086f000 0x22013b0000437800 0xc37e7e0003c3f801 0x61bf3f0001e1fc00

def z681 : W := mkw 0x0000000000000000 0x0000000000000000 0xffd020003000e73f 0xffe810001800739f

def z682 : W := mkw 0x0380010442110520 0x01c0008221088290 0x75b9411dc2330521 0xbadca08ee1198290

def z683 : W := mkw 0xab0581b603780780 0x5582c0db01bc03c0 0xc0f781fc03fc0000 0xe07bc0fe01fe0000

def z684 : W := mkw 0x15600a0c9414694e 0x8ab005064a0a34a7 0xffd1be1e3c3cffff 0xffe8df0f1e1e7fff

def z685 : W := mkw 0x13c0096df2510f35 0x09e004b6f928879a 0x7fb959fdf2333f3f 0xbfdcacfef9199f9f

def z686 : W := mkw 0x230001b602500780 0x118000db012803c0 0xdc7601fe03c007c0 0x6e3b00ff01e003e0

def z687 : W := mkw 0x12800908d2010420 0x0940048469008210 0x77b9591dd2030421 0x3bdcac8ee9018210

def z688 : W := mkw 0xf007fcdbb8000000 0x7803fe6ddc000000 0x1cf7d9ffc0000000 0x0e7becffe0000000

def z689 : W := mkw 0x0282616162c38631 0x014130b0b161c318 0x2d7e61e1e3c30000 0x16bf30f0f1e18000

def z690 : W := mkw 0x042002000404604a 0x8210010002023025 0x80000000000cc2d8 0x400000000006616c

def z691 : W := mkw 0xc807f40001280000 0x6403fa0000940000 0xc3f7fe0003fc0000 0xe1fbff0001fe0000

def z692 : W := mkw 0x042002000404604a 0x8210010002023025 0x779086021c0c25e7 0xbbc843010e0612f3

def z693 : W := mkw 0xf3c7fdfffad38f35 0x79e3fefffd69c79a 0xfffffffffff3ff3f 0xfffffffffff9ff9f

def z694 : W := mkw 0x042002000404604a 0x8210010002023025 0x000000000000e03f 0x000000000000701f

def z695 : W := mkw 0x0000000000000000 0x0000000000000000 0xc076000003c00000 0x603b000001e00000

def z696 : W := mkw 0x0200012002400600 0x0100009001200300 0x0c0001e000000600 0x060000f000000300

def z697 : W := mkw 0x10c00808d0010824 0x0860040468008412 0x63b95801d2333827 0xb1dcac00e9199c13

def z698 : W := mkw 0xa005809200000000 0x5002c04900000000 0x1081801e00000000 0x0840c00f00000000

def z699 : W := mkw 0x50027c49b8000000 0x28013e24dc000000 0x2f767fe1fc000000 0x17bb3ff0fe000000

def z700 : W := mkw 0xcc059600012c7000 0x6602cb0000963800 0xc2f79e0003fc3800 0xe17bcf0001fe1c00

def z701 : W := mkw 0xbbc5899ed3390da4 0x5de2c4cf699c86d2 0x77b9d91fd23f3de7 0xbbdcec8fe91f9ef3

def z702 : W := mkw 0xff27ffffbf7c67ca 0xff93ffffdfbe33e5 0xfff7fffffffce7ff 0xfffbfffffffe73ff

def z703 : W := mkw 0x03c0010442110d24 0x01e0008221088692 0x7798000012333d27 0xbbcc000009199e93

def z704 : W := mkw 0xcc07f60001aef000 0x6603fb0000d77800 0x82c7be0001fcf800 0xc163df0000fe7c00

def z705 : W := mkw 0xf007fcdbb8000000 0x7803fe6ddc000000 0x3381fe1ffc000000 0x19c0ff0ffe000000

def z706 : W := mkw 0xc427f6000404604a 0xe213fb0002023025 0xfff7fe023c0ce7ff 0xfffbff011e0673ff

def z707 : W := mkw 0x042002000404604a 0x8210010002023025 0xffd8a6023e3fffff 0xffec53011f1fffff

def z708 : W := mkw 0xdfc7ff0cd3bffd24 0x6fe3ff8669dffe92 0xb446a71dd1ccc526 0x5a23538ee8e66293

def z709 : W := mkw 0x0282616162c38631 0x014130b0b161c318 0xeffe61e1e3c3e639 0xf7ff30f0f1e1f31c

def z710 : W := mkw 0xec07f69201aef000 0x7603fb4900d77800 0xcbfffee203fff801 0xe5ffff7101fffc00

def z711 : W := mkw 0xab0581b603780780 0x5582c0db01bc03c0 0xd0a781fe03fc07c0 0xe853c0ff01fe03e0

def z712 : W := mkw 0x13c0090cd2110d24 0x09e0048669088692 0x0229591dd2333806 0x0114ac8ee9199c03

def z713 : W := mkw 0xc807f40001aa9000 0x6403fa0000d54800 0x806fd80003ff1800 0x4037ec0001ff8c00

def z714 : W := mkw 0xf007fcdbb8000000 0x7803fe6ddc000000 0x37b7dfffdc000000 0x1bdbefffee000000

def z715 : W := mkw 0xa905809601380180 0x5482c04b009c00c0 0xdcf781fe03fc01c0 0xee7bc0ff01fe00e0

def z716 : W := mkw 0xfc259e9a9d2c704a 0xfe12cf4d4e963825 0x12819e1e1c3c39c6 0x8940cf0f0e1e1ce3

def z717 : W := mkw 0xab0581b603780780 0x5582c0db01bc03c0 0xfcf781fe3ffc07c0 0xfe7bc0ff1ffe03e0

def z718 : W := mkw 0xf427fedbbc04604a 0xfa13ff6dde023025 0xc02759fdc00ce7ff 0xe013acfee00673ff

def z719 : W := mkw 0xc807f40001aa9000 0x6403fa0000d54800 0xc02f580003ff1800 0xe017ac0001ff8c00

def z720 : W := mkw 0xf007fcdbb8000000 0x7803fe6ddc000000 0x2f777ffdfc000000 0x17bbbffefe000000

def z721 : W := mkw 0xf007fcdbb8000000 0x7803fe6ddc000000 0xbff7fffffc0c02c0 0x5ffbfffffe060160

def z722 : W := mkw 0x0282616162c38631 0x014130b0b161c318 0xffff79e1f3f3ff3f 0xffffbcf0f9f9ff9f

def z723 : W := mkw 0xf007fcdbb8828000 0x7803fe6ddc414000 0xffffffffffc3c639 0x7fffffffffe1e31c

def z724 : W := mkw 0xf807fcdbb9280000 0x7c03fe6ddc940000 0xbff7fffffdcc0000 0x5ffbfffffee60000

def z725 : W := mkw 0xf007fcdbb8000000 0x7803fe6ddc000000 0x7ffffffffe030001 0x3fffffffff018000

def z726 : W := mkw 0xeb0595b603780780 0x7582cadb01bc03c0 0xdef79ffe03fc07c0 0xef7bcfff01fe03e0

def z727 : W := mkw 0xf007fcdbb8000000 0x7803fe6ddc000000 0x3fd6a7fffc000000 0x1feb53fffe000000

def z728 : W := mkw 0xc827f40005aa904a 0xe413fa0002d54825 0x3c2f58023ff31ffe 0x1e17ac011ff98fff

def z729 : W := mkw 0xf807fcdbb9aa9000 0x7c03fe6ddcd54800 0xfffffffffff3d801 0x7ffffffffff9ec00

def z730 : W := mkw 0xf007fcdbb8000000 0x7803fe6ddc000000 0x2b67fffffc000000 0x15b3fffffe000000

def z731 : W := mkw 0xc807f40001aa9000 0x6403fa0000d54800 0xc3fffe0003ff1800 0xe1ffff0001ff8c00

def z732 : W := mkw 0x06a2636166c7e67b 0x835131b0b363f33d 0x12aec7e3dfcf21c6 0x895763f1efe790e3

def z733 : W := mkw 0xcc07f60001aef000 0x6603fb0000d77800 0xe3fffe0013fff827 0xf1ffff0009fffc13

def z734 : W := mkw 0x70027cdbb8000000 0x38013e6ddc000000 0x23007ffdfc000000 0x11803ffefe000000

def z735 : W := mkw 0x1000080890000000 0x0800040448000000 0x77b9591dd2333d27 0xbbdcac8ee9199e93

def z736 : W := mkw 0xc807f40001aa9000 0x6403fa0000d54800 0x3ffffe023ff31800 0x1fffff011ff98c00

def z737 : W := mkw 0x03c2616562d38f35 0x01e130b2b169c79a 0xfffe61e1f3f3ff3f 0xffff30f0f9f9ff9f

def z738 : W := mkw 0x11c0080cd0110924 0x08e0040668088492 0x7799581dd0333d27 0xbbccac0ee8199e93

def z739 : W := mkw 0xcc27f60005aef04a 0xe613fb0002d77825 0xeffffe022ffffef9 0xf7ffff0117ffff7c

def z740 : W := mkw 0x042002000404604a 0x8210010002023025 0xfff1fe023c0ce7ff 0xfff8ff011e0673ff

def z741 : W := mkw 0xf007fcdbb8828000 0x7803fe6ddc414000 0xbff7fffffdc0c000 0x5ffbfffffee06000

def z742 : W := mkw 0xc807f40001aa9000 0x6403fa0000d54800 0x02afde0003f31800 0x0157ef0001f98c00

def z743 : W := mkw 0x13c0096df2510f35 0x09e004b6f928879a 0x2c0001fde0000638 0x160000fef000031c

def z744 : W := mkw 0xf807fcdbb9280000 0x7c03fe6ddc940000 0x3ff7fffffff00000 0x1ffbfffffff80000

def z745 : W := mkw 0xc807f40001aa9000 0x6403fa0000d54800 0x00ffd80003f31800 0x007fec0001f98c00

def z746 : W := mkw 0xa987e0d761bb81b1 0x54c3f06bb0ddc0d8 0x3189e01fe03fc1f9 0x98c4f00ff01fe0fc

def z747 : W := mkw 0xcc05960001aef000 0x6602cb0000d77800 0x02899e0003ff3800 0x8144cf0001ff9c00

def z748 : W := mkw 0xc807f40001aa9000 0x6403fa0000d54800 0x40bf580003f31800 0xa05fac0001f98c00

def z749 : W := mkw 0x0002606120c28211 0x0001303090614108 0xa94660e1e1c0c218 0x54a33070f0e0610c

def z750 : W := mkw 0xf007fcdbb8000000 0x7803fe6ddc000000 0x3ec7bffffc000000 0x1f63dffffe000000

def z751 : W := mkw 0xce859761636d7631 0x6742cbb0b1b6bb18 0x2e819fe1e03c3e38 0x9740cff0f01e1f1c

def z752 : W := mkw 0xcc27f60005aef04a 0xe613fb0002d77825 0xc02f580003ffffff 0xe017ac0001ffffff

def z753 : W := mkw 0x0280012042c38631 0x014000902161c318 0xed7e41e1c3c3c639 0x76bf20f0e1e1e31c

def z754 : W := mkw 0xc807f40001aa9000 0x6403fa0000d54800 0x017f780003f31800 0x00bfbc0001f98c00

def z755 : W := mkw 0x0282616162c38631 0x014130b0b161c318 0xeffee7e1e3c3c639 0x77ff73f0f1e1e31c

def z756 : W := mkw 0xc807f40001aa9000 0x6403fa0000d54800 0x032f7e0003f31800 0x0197bf0001f98c00

def z757 : W := mkw 0xf007fcdbb8000000 0x7803fe6ddc000000 0x3ff7fffffc0c01c0 0x9ffbfffffe0600e0

def z758 : W := mkw 0xcc07f60001aef000 0x6603fb0000d77800 0xfffffe0213ffffe7 0xffffff0109fffff3

def z759 : W := mkw 0x670277b602d6f780 0x33813bdb016b7bc0 0x1f087ffe0003ffc1 0x0f843fff0001ffe0

def z760 : W := mkw 0x3c000adbb9aef000 0x1e00056ddcd77800 0xfc0801fffffff801 0xfe0400fffffffc00

def z761 : W := mkw 0x300008dbb8000000 0x1800046ddc000000 0x3e8087fffc000000 0x1f4043fffe000000

def z762 : W := mkw 0x0000000000000000 0x0000000000000000 0xc3ff580003f33801 0xe1ffac0001f99c00

def z763 : W := mkw 0x0002604120828000 0x0001302090414000 0xed7e61e1e3c3c639 0x76bf30f0f1e1e31c

def z764 : W := mkw 0xab0581b603780780 0x5582c0db01bc03c0 0xfff7a7fe3ffc27e7 0xfffbd3ff1ffe13f3

def z765 : W := mkw 0x13c0090cd2110d24 0x09e0048669088692 0xf7f9791dd233fd27 0xfbfcbc8ee919fe93

def z766 : W := mkw 0xc807f40001aa9000 0x6403fa0000d54800 0xc3ff780003f3f801 0xe1ffbc0001f9fc00

def z767 : W := mkw 0x0c20020005aef04a 0x8610010002d77825 0xfff9fe023fffffff 0xfffcff011fffffff

def z768 : W := mkw 0xf007fcdbb8000000 0x7803fe6ddc000000 0x3ff7fffffc303800 0x9ffbfffffe181c00

def z769 : W := mkw 0xf007fcdbb8828000 0x7803fe6ddc414000 0x3fffffffffc30000 0x1fffffffffe18000

def z770 : W := mkw 0xaf2583b6077c67ca 0xd792c1db03be33e5 0x232727fc3ff0e03f 0x119393fe1ff8701f

def z771 : W := mkw 0x8805800001280000 0x4402c00000940000 0xc0ffd80003ff1800 0xe07fec0001ff8c00

def z772 : W := mkw 0xcc07f60001aef000 0x6603fb0000d77800 0x03affe0003fff801 0x81d7ff0001fffc00

def z773 : W := mkw 0x13c0090cd2110d24 0x09e0048669088692 0x7ff9791df2333d27 0xbffcbc8ef9199e93

def z774 : W := mkw 0xc807f40001aa9000 0x6403fa0000d54800 0xc07f580003f31800 0x603fac0001f98c00

def z775 : W := mkw 0x13c0090cd2110d24 0x09e0048669088692 0x7fff59fdd2333d27 0xbfffacfee9199e93

def z776 : W := mkw 0xcc27f60005aef04a 0xe613fb0002d77825 0xd3fffe021fffffff 0xe9ffff010fffffff

def z777 : W := mkw 0x0282616162c38631 0x014130b0b161c318 0xac6e61e1e3c3c638 0x563730f0f1e1e31c

def z778 : W := mkw 0x0282616162c38631 0x014130b0b161c318 0x802e41e1c3c3c218 0x401720f0e1e1e10c

def z779 : W := mkw 0x13c0090cd2110d24 0x09e0048669088692 0xf7b9591dd23f3fe7 0xfbdcac8ee91f9ff3

def z780 : W := mkw 0xf007fcdbb8000000 0x7803fe6ddc000000 0x3d76e7fffc000000 0x1ebb73fffe000000

def z781 : W := mkw 0x0282616162c38631 0x014130b0b161c318 0xfdfee1e3e3c3c639 0x7eff70f1f1e1e31c

def z782 : W := mkw 0x4282756162c39631 0x21413ab0b161cb18 0xed7e79e1e3c3de39 0x76bf3cf0f1e1ef1c

def z783 : W := mkw 0x0082606160c38231 0x00413030b061c118 0xe97e60e1e3c3c239 0x74bf3070f1e1e11c

def z784 : W := mkw 0x13c0090cd2110d24 0x09e0048669088692 0x52a9591dd2333d27 0xa954ac8ee9199e93

def z785 : W := mkw 0x50027c49b8000000 0x28013e24dc000000 0x3ff77ffdfc000000 0x1ffbbffefe000000

def z786 : W := mkw 0xab0581b603780780 0x5582c0db01bc03c0 0xdef799fe03fc3fc0 0xef7bccff01fe1fe0

def z787 : W := mkw 0x0800000001aa9000 0x0400000000d54800 0x0029580003f31800 0x0014ac0001f98c00

def z788 : W := mkw 0xcc07f60001aef000 0x6603fb0000d77800 0x43bfde0003ff3801 0xa1dfef0001ff9c00

def z789 : W := mkw 0xcc07f60001aef000 0x6603fb0000d77800 0xe3fffe0023fff839 0xf1ffff0011fffc1c

def z790 : W := mkw 0xcc07f60001aef000 0x6603fb0000d77800 0xc2afde0003fff801 0xe157ef0001fffc00

def z791 : W := mkw 0xcc07f64121aef000 0x6603fb2090d77800 0xcbfffee023fff801 0xe5ffff7011fffc00

def z792 : W := mkw 0x13c0090cd2110d24 0x09e0048669088692 0x77f9ff1dd2333d27 0xbbfcff8ee9199e93

def z793 : W := mkw 0xf807fcdbb9280000 0x7c03fe6ddc940000 0xfff7fffffffc07c0 0xfffbfffffffe03e0

def z794 : W := mkw 0xab8581b6437907b1 0x55c2c0db21bc83d8 0xdcf781fe03fc07f8 0xee7bc0ff01fe03fc

def z795 : W := mkw 0xcc07f60001aef000 0x6603fb0000d77800 0x836ffe0003fff801 0x41b7ff0001fffc00

def z796 : W := mkw 0x17e00b0cd6156d6e 0x8bf005866b0ab6b7 0x8869ff1fee3fdad8 0x4434ff8ff71fed6c

def z797 : W := mkw 0xf007fcdbb8000000 0x7803fe6ddc000000 0x7ff7fffffe300000 0xbffbffffff180000

def z798 : W := mkw 0x13c0090cd2110d24 0x09e0048669088692 0x77b9d91fd23f3de7 0xbbdcec8fe91f9ef3

def z799 : W := mkw 0x0082606160c38231 0x00413030b061c118 0x884e60e1e1c3c218 0x44273070f0e1e10c

def z800 : W := mkw 0x0082606160c38231 0x00413030b061c118 0xa84620e1e1c0c238 0x54231070f0e0611c

def z801 : W := mkw 0xcc07f60001aef000 0x6603fb0000d77800 0xc32f7e0003fff801 0xe197bf0001fffc00

def z802 : W := mkw 0xcc27f60005aef04a 0xe613fb0002d77825 0x12afde021fff39c6 0x8957ef010fff9ce3

def z803 : W := mkw 0x13c0096df2510f35 0x09e004b6f928879a 0x000001fdc0000000 0x000000fee0000000

def z804 : W := mkw 0x0002600000828000 0x0001300000414000 0xffff780033f3ff3f 0xffffbc0019f9ff9f

def z805 : W := mkw 0x33c009bed2510fa4 0x19e004df692887d2 0x1c0001ffc00007c0 0x0e0000ffe00003e0

def z806 : W := mkw 0xf807fcdbb9281000 0x7c03fe6ddc940800 0x3ff7fffffc301800 0x1ffbfffffe180c00

def z807 : W := mkw 0x042002000404604a 0x8210010002023025 0xfff1a71e3c0ce7ff 0xfff8d38f1e0673ff

def z808 : W := mkw 0xab0581b603780780 0x5582c0db01bc03c0 0x802701fc03fc02c0 0x401380fe01fe0160

def z809 : W := mkw 0x13c0090cd2110d24 0x09e0048669088692 0x53b9591dd2333907 0xa9dcac8ee9199c83

def z810 : W := mkw 0x0282616162c38631 0x014130b0b161c318 0xe94e60e1e3c3c639 0x74a73070f1e1e31c

def z811 : W := mkw 0xab0581b603780780 0x5582c0db01bc03c0 0xdc7681fe03cc07c0 0x6e3b40ff01e603e0

def z812 : W := mkw 0xcc07f60001aef000 0x6603fb0000d77800 0xfffffe0223fffff9 0xffffff0111fffffc

def z813 : W := mkw 0xf2859dbadac38631 0x7942cedd6d61c318 0xd2899e1e1fc3c639 0x6944cf0f0fe1e31c

def z814 : W := mkw 0x0282616162c38631 0x014130b0b161c318 0xedfee1e1e3cfc639 0xf6ff70f0f1e7e31c

def z815 : W := mkw 0x0282616162c38631 0x014130b0b161c318 0xad7661e1e1c0c638 0x56bb30f0f0e0631c

def z816 : W := mkw 0xcc07f64121aef000 0x6603fb2090d77800 0xffffffe3fffff801 0xfffffff1fffffc00

def z817 : W := mkw 0xab0581b603780780 0x5582c0db01bc03c0 0xcc7701fc03fc07c0 0xe63b80fe01fe03e0

def z818 : W := mkw 0xcc07f60001aef000 0x6603fb0000d77800 0xfffffe023ffffe39 0xffffff011fffff1c

def z819 : W := mkw 0x8805800001280000 0x4402c00000940000 0xffffd80213ff3fe7 0xffffec0109ff9ff3

def z820 : W := mkw 0x0382616562d38731 0x01c130b2b169c398 0xed7e61e1e3f3c739 0xf6bf30f0f1f9e39c

def z821 : W := mkw 0xcc07f60001aef000 0x6603fb0000d77800 0xfffffe023ffffd27 0xffffff011ffffe93

def z822 : W := mkw 0xcc07f60001aef000 0x6603fb0000d77800 0x002f580003f3f801 0x0017ac0001f9fc00

def z823 : W := mkw 0x300008dbb8000000 0x1800046ddc000000 0x3c40a7fffc000000 0x1e2053fffe000000

def z824 : W := mkw 0xc807f40001aa9000 0x6403fa0000d54800 0x02af580003f33800 0x8157ac0001f99c00

def z825 : W := mkw 0xf807fcdbb9aa8000 0x7c03fe6ddcd54000 0xffffffffffffc001 0xffffffffffffe000

def z826 : W := mkw 0x03c2616562d38f35 0x01e130b2b169c79a 0xed7e61e1e3f3de39 0x76bf30f0f1f9ef1c

def z827 : W := mkw 0xe3c7f5d76a110d24 0x71e3faebb5088692 0x484ea6e22e333d27 0xa427537117199e93

def z828 : W := mkw 0xec07f69201aef000 0x7603fb4900d77800 0xc3fffffc03fff801 0xe1fffffe01fffc00

def z829 : W := mkw 0xf0059cdbb8000000 0x7802ce6ddc000000 0x12819fffdc000000 0x0940cfffee000000

def z830 : W := mkw 0xcc27f60005aef04a 0xe613fb0002d77825 0xcbfffe022fffffff 0xe5ffff0117ffffff

def z831 : W := mkw 0xcc07f60001aef000 0x6603fb0000d77800 0xe7ffff01c3fff801 0xf3ffff80e1fffc00

def z832 : W := mkw 0xec07f69201aef000 0x7603fb4900d77800 0xd3fffe1e03fff801 0xe9ffff0f01fffc00

def z833 : W := mkw 0x1142686db0d28b15 0x08a13436d869458a 0x9ac738fc31f0fb1e 0xcd639c7e18f87d8f

def z834 : W := mkw 0xaa0581b203680680 0x5502c0d901b40340 0xdcf781fe03cc06c0 0x6e7bc0ff01e60360

def z835 : W := mkw 0x33c009bed2510fa4 0x19e004df692887d2 0x340001fdd0000526 0x1a0000fee8000293

def z836 : W := mkw 0x13c0090cd2110d24 0x09e0048669088692 0xfff9591dd2333f27 0xfffcac8ee9199f93

def z837 : W := mkw 0xf007fcdbb8000000 0x7803fe6ddc000000 0x3ff7fffffc00c039 0x1ffbfffffe00601c

def z838 : W := mkw 0x70027cdbb8000000 0x38013e6ddc000000 0x3f767ffffc000000 0x1fbb3ffffe000000

def z839 : W := mkw 0xf007fcdbb8829000 0x7803fe6ddc414800 0x3ffffffffc031800 0x1ffffffffe018c00

def z840 : W := mkw 0x0282616162c38631 0x014130b0b161c318 0xec7621e1e3c0c638 0x763b10f0f1e0631c

def z841 : W := mkw 0xf007fcdbb8000000 0x7803fe6ddc000000 0x3cf7a7fffc000000 0x1e7bd3fffe000000

def z842 : W := mkw 0x5b027d6dbb780780 0x2d813eb6ddbc03c0 0xe3007e01fffc07c0 0xf1803f00fffe03e0

def z843 : W := mkw 0x13c0090cd2110d24 0x09e0048669088692 0xf7ff591dd3f33d27 0xfbffac8ee9f99e93

def z844 : W := mkw 0x37e00bbed6556fee 0x9bf005df6b2ab7f7 0xffd0a7fffc0ce7ff 0xffe853fffe0673ff

def z845 : W := mkw 0x4c02760001aef000 0x26013b0000d77800 0xc3b97e0003fff801 0xe1dcbf0001fffc00

def z846 : W := mkw 0x4c22760005aef04a 0xa6113b0002d77825 0xffd8fe023fffffff 0xffec7f011fffffff

def z847 : W := mkw 0xeb0595b603781780 0x7582cadb01bc0bc0 0xdcf799fe03fc1fc0 0xee7bccff01fe0fe0

def z848 : W := mkw 0x042002000404604a 0x8210010002023025 0xffd8fe023c0fffff 0xffec7f011e07ffff

def z849 : W := mkw 0xab0581b603780780 0x5582c0db01bc03c0 0xfff781fe13fc07c0 0xfffbc0ff09fe03e0

def z850 : W := mkw 0xcc07f60001aef000 0x6603fb0000d77800 0xe3fffe003ffff801 0xf1ffff001ffffc00

def z851 : W := mkw 0xcc07f60001aef000 0x6603fb0000d77800 0x802f580003ffd800 0x4017ac0001ffec00

def z852 : W := mkw 0xcc27f60005aef04a 0xe613fb0002d77825 0xc3fffe0003fff83f 0xe1ffff0001fffc1f

def z853 : W := mkw 0xa90580b601780380 0x5482c05b00bc01c0 0x108780fe01fc01c0 0x8843c07f00fe00e0

def z854 : W := mkw 0xf007fcdbb8000000 0x7803fe6ddc000000 0xbff7fffffc00c218 0x5ffbfffffe00610c

def z855 : W := mkw 0x13c0090cd2110d24 0x09e0048669088692 0x7ff9d91fd2333d27 0xbffcec8fe9199e93

def z856 : W := mkw 0x13c0090cd2110d24 0x09e0048669088692 0x7fb9591ffe333d27 0xbfdcac8fff199e93

def z857 : W := mkw 0x8c058200012c6000 0x4602c10000963000 0xc3fffe0003fff801 0xe1ffff0001fffc00

def z858 : W := mkw 0x0082606160c38231 0x00413030b061c118 0xed5e60e1e1c3c639 0x76af3070f0e1e31c

def z859 : W := mkw 0x0002606120c28211 0x0001303090614108 0xed7661e1e1c0c639 0x76bb30f0f0e0631c

def z860 : W := mkw 0xf007fcdbb8000000 0x7803fe6ddc000000 0x3f277ffffc000000 0x1f93bffffe000000

def z861 : W := mkw 0xf007fcdbb8000000 0x7803fe6ddc000000 0x7ffffffffe333d27 0xbfffffffff199e93

def z862 : W := mkw 0xe807f49201aa9000 0x7403fa4900d54800 0x1cffd9fe03f31800 0x0e7fecff01f98c00

def z863 : W := mkw 0x042002000404604a 0x8210010002023025 0x3f80a6023c0ce7ff 0x9fc053011e0673ff

def z864 : W := mkw 0x0282616162c38631 0x014130b0b161c318 0x002e41e1c3c3c039 0x001720f0e1e1e01c

def z865 : W := mkw 0x0282616162c38631 0x014130b0b161c318 0xed7f79e1e3f3de39 0x76bfbcf0f1f9ef1c

def z866 : W := mkw 0xab0581b603780780 0x5582c0db01bc03c0 0xdcf781fe03fc27e7 0xee7bc0ff01fe13f3

def z867 : W := mkw 0xb8c588bad1690aa4 0x5c62c45d68b48552 0xab4ed8e3d1cf3ae7 0x55a76c71e8e79d73

def z868 : W := mkw 0xa80580b201680280 0x5402c05900b40140 0xdcf781fe03fc02c0 0xee7bc0ff01fe0160

def z869 : W := mkw 0xcc07f60001aef000 0x6603fb0000d77800 0xfffffe023fffffc1 0xffffff011fffffe0

def z870 : W := mkw 0xf007fcdbb8000000 0x7803fe6ddc000000 0xfff7fffffc00c001 0x7ffbfffffe006000

def z871 : W := mkw 0xcc27f60005aef04a 0xe613fb0002d77825 0xdffffe0203ffffff 0xefffff0101ffffff

def z872 : W := mkw 0xa90580b601780380 0x5482c05b00bc01c0 0x884780fe01fc02c0 0x4423c07f00fe0160

def z873 : W := mkw 0x042002000404604a 0x8210010002023025 0xfff6a6023fcce7ff 0xfffb53011fe673ff

def z874 : W := mkw 0x13c0090cd2110d24 0x09e0048669088692 0x77b9df1fde333d27 0xbbdcef8fef199e93

def z875 : W := mkw 0x8805800001280000 0x4402c00000940000 0x002f580003f31800 0x0017ac0001f98c00

def z876 : W := mkw 0xf007fcdbb8000000 0x7803fe6ddc000000 0x1cf7ffffec000000 0x0e7bfffff6000000

def z877 : W := mkw 0xab0581b603780780 0x5582c0db01bc03c0 0xd4b701fc03fc07c0 0xea5b80fe01fe03e0

def z878 : W := mkw 0xa80580b201680280 0x5402c05900b40140 0xdcf781fe01cc07c0 0xee7bc0ff00e603e0

def z879 : W := mkw 0xa80580b201680280 0x5402c05900b40140 0x9c4681fe01cc02c0 0x4e2340ff00e60160

def z880 : W := mkw 0xf007fcdbb8000000 0x7803fe6ddc000000 0x1ef7dfffdc000000 0x0f7befffee000000

def z881 : W := mkw 0xf007fcdbb8828000 0x7803fe6ddc414000 0xfffffffffff3f801 0xfffffffffff9fc00

def z882 : W := mkw 0xf007fcdbb8000000 0x7803fe6ddc000000 0xfff7fffffc0cc7f9 0xfffbfffffe0663fc

def z883 : W := mkw 0x0382616562d38731 0x01c130b2b169c398 0xffff79fde3f3ff39 0xffffbcfef1f9ff9c

def z884 : W := mkw 0x8807e00001aa8000 0x4403f00000d54000 0xc3fff80003fff801 0xe1fffc0001fffc00

def z885 : W := mkw 0x0282616162c38631 0x014130b0b161c318 0xa96e61e1e3c3c239 0x54b730f0f1e1e11c

def z886 : W := mkw 0xa805809201280000 0x5402c04900940000 0xdcf781fe03fc07c0 0xee7bc0ff01fe03e0

def z887 : W := mkw 0xcc27f60005aef04a 0xe613fb0002d77825 0xf3fffe023ffff9ff 0xf9ffff011ffffcff

def z888 : W := mkw 0x33c009fffa510f35 0x19e004fffd28879a 0x3c0001fffc00073e 0x1e0000fffe00039f

def z889 : W := mkw 0x042002000404604a 0x8210010002023025 0xffd1be023c3cffff 0xffe8df011e1e7fff

def z890 : W := mkw 0x0c20020005aef04a 0x8610010002d77825 0xf7b9580013ffffff 0xfbdcac0009ffffff

def z891 : W := mkw 0x0280016162410631 0x014000b0b1208318 0xed7621e1e3c0c639 0x76bb10f0f1e0631c

def z892 : W := mkw 0xcc07f60001aef000 0x6603fb0000d77800 0xc17ffe0003ffd801 0x60bfff0001ffec00

def z893 : W := mkw 0xcc07f60001aef000 0x6603fb0000d77800 0xf7fffe0013fff801 0xfbffff0009fffc00

def z894 : W := mkw 0xab0581b603780780 0x5582c0db01bc03c0 0xdc4681fe03fc07c0 0xee2340ff01fe03e0

def z895 : W := mkw 0x11c0080cd0110924 0x08e0040668088492 0x1289581dd0333906 0x8944ac0ee8199c83

def z896 : W := mkw 0xcc27f60005aef04a 0xe613fb0002d77825 0xc3fffe0003fff9c7 0xe1ffff0001fffce3

def z897 : W := mkw 0xcc27f60005aef04a 0xe613fb0002d77825 0xc3fffe0003fffad9 0xe1ffff0001fffd6c

def z898 : W := mkw 0x11c0080cd0110924 0x08e0040668088492 0x2309581dd0333827 0x1184ac0ee8199c13

def z899 : W := mkw 0x0282616162c38631 0x014130b0b161c318 0x884621e1e1c0c218 0x442310f0f0e0610c

def z900 : W := mkw 0x0282616162c38631 0x014130b0b161c318 0xef7e79e1e3c3fe39 0x77bf3cf0f1e1ff1c

def z901 : W := mkw 0x13c0090cd2110d24 0x09e0048669088692 0x33a9591dd2333927 0x99d4ac8ee9199c93

def z902 : W := mkw 0xcc27f60005aef04a 0xe613fb0002d77825 0xc3fffe001ffff807 0xe1ffff000ffffc03

def z903 : W := mkw 0x13c0090cd2110d24 0x09e0048669088692 0x77b9791df233fd3f 0xbbdcbc8ef919fe9f

def z904 : W := mkw 0x042002000404604a 0x8210010002023025 0xfd50a6023c0cc7ff 0x7ea853011e0663ff

def z905 : W := mkw 0xf007fcdbb8000000 0x7803fe6ddc000000 0x13f7ffffdc000000 0x09fbffffee000000

def z906 : W := mkw 0xec27f6d32daef04a 0xf613fb6996d77825 0x8846a6e22dccc2d8 0x4423537116e6616c

def z907 : W := mkw 0xec07f6d329aef000 0x7603fb6994d77800 0xefffffe3effff801 0xf7fffff1f7fffc00

def z908 : W := mkw 0x13c0096df2510f35 0x09e004b6f928879a 0xffd021fdf000e73f 0xffe810fef800739f

def z909 : W := mkw 0xc807f40001aa9000 0x6403fa0000d54800 0x806f780003f3d800 0x4037bc0001f9ec00

def z910 : W := mkw 0xcc27f60005aef04a 0xe613fb0002d77825 0xdffffe021fffffc7 0xefffff010fffffe3

def z911 : W := mkw 0xcc05960001aef000 0x6602cb0000d77800 0xc2ff9e0003fff801 0xe17fcf0001fffc00

def z912 : W := mkw 0x8805800001280000 0x4402c00000940000 0x43bf580003f33801 0xa1dfac0001f99c00

def z913 : W := mkw 0xab0581b603780780 0x5582c0db01bc03c0 0x884681fe01cc02c0 0x442340ff00e60160

def z914 : W := mkw 0xf0059cdbb8000000 0x7802ce6ddc000000 0x3fb1dffffc000000 0x1fd8effffe000000

def z915 : W := mkw 0x0282616162c38631 0x014130b0b161c318 0xfd7e61e3ffc3c639 0x7ebf30f1ffe1e31c

def z916 : W := mkw 0xf007fcdbb8000000 0x7803fe6ddc000000 0x00277ffdec000000 0x0013bffef6000000

def z917 : W := mkw 0x042002000404604a 0x8210010002023025 0xfc40a6023c0ce7ff 0xfe2053011e0673ff

def z918 : W := mkw 0x13c0096df2510f35 0x09e004b6f928879a 0x340001fdd0000526 0x1a0000fee8000293

def z919 : W := mkw 0xf007fcdbb8000000 0x7803fe6ddc000000 0x02275ffddc000000 0x0113affeee000000

def z920 : W := mkw 0xbd658a9e953c69ce 0xdeb2c54f4a9e34e7 0x12819e1e1c3c39c6 0x8940cf0f0e1e1ce3

def z921 : W := mkw 0xf807fcdbb9aa9000 0x7c03fe6ddcd54800 0x7ffffffffff33801 0xbffffffffff99c00

def z922 : W := mkw 0x0282616162c38631 0x014130b0b161c318 0xfdff61fde3c3c639 0x7effb0fef1e1e31c

def z923 : W := mkw 0x54a27e49fc87e07b 0xaa513f24fe43f03d 0x23087e01fc03e03f 0x11843f00fe01f01f

def z924 : W := mkw 0xcc07f60001aef000 0x6603fb0000d77800 0xeffffe0023fff801 0xf7ffff0011fffc00

def z925 : W := mkw 0x0282616162c38631 0x014130b0b161c318 0xc97e61e1e3c3c219 0x64bf30f0f1e1e10c

def z926 : W := mkw 0x0000000000828000 0x0000000000414000 0xc3b9580003f3f801 0xe1dcac0001f9fc00

def z927 : W := mkw 0x13c0092cd2510f24 0x09e0049669288792 0x3c0001fdd0000726 0x1e0000fee8000393

def z928 : W := mkw 0xf007fcdbb8000000 0x7803fe6ddc000000 0x3ff7fffffc002027 0x1ffbfffffe001013

def z929 : W := mkw 0xcc07f60001aef000 0x6603fb0000d77800 0x002fde0003ff1800 0x0017ef0001ff8c00

def z930 : W := mkw 0x0c00020001aef000 0x0600010000d77800 0xc029580003fff801 0xe014ac0001fffc00

def z931 : W := mkw 0xab0581b603780780 0x5582c0db01bc03c0 0xc0f781fc03fc07c0 0xe07bc0fe01fe03e0

def z932 : W := mkw 0x70027cdbb8000000 0x38013e6ddc000000 0x3c0027fffc000000 0x1e0013fffe000000

def z933 : W := mkw 0x0282616162c38631 0x014130b0b161c318 0xed5621e1e1c0c639 0x76ab10f0f0e0631c

def z934 : W := mkw 0xf007fcdbb8828011 0x7803fe6ddc414008 0x3ff7fffffc00c018 0x1ffbfffffe00600c

def z935 : W := mkw 0xe007f4d328000000 0x7003fa6994000000 0x3df7e7ffec000000 0x1efbf3fff6000000

def z936 : W := mkw 0xcc27f60005aef04a 0xe613fb0002d77825 0xc3fffe002ffff819 0xe1ffff0017fffc0c

def z937 : W := mkw 0xec07f69201aef000 0x7603fb4900d77800 0xfffffffe3ffff801 0xffffffff1ffffc00

def z938 : W := mkw 0xcc07f60001aef000 0x6603fb0000d77800 0xc0ffd80003fff801 0xe07fec0001fffc00

def z939 : W := mkw 0xab0581b603780780 0x5582c0db01bc03c0 0x1cf781fe03fc01c0 0x8e7bc0ff01fe00e0

def z940 : W := mkw 0x300008dbb8000000 0x1800046ddc000000 0x3f0027fffc000000 0x1f8013fffe000000

def z941 : W := mkw 0x13c0090cd2110d24 0x09e0048669088692 0x77b97f1dfe333d27 0xbbdcbf8eff199e93

def z942 : W := mkw 0x70027cdbb8000000 0x38013e6ddc000000 0x3fb17ffffc000000 0x1fd8bffffe000000

def z943 : W := mkw 0x13c0090cd2110d24 0x09e0048669088692 0xf7b9591dd233ff3f 0xfbdcac8ee919ff9f

def z944 : W := mkw 0x13c0090cd2110d24 0x09e0048669088692 0x3729591dd2333d27 0x1b94ac8ee9199e93

def z945 : W := mkw 0xab0581b603780780 0x5582c0db01bc03c0 0x98e781fe03fc03c0 0xcc73c0ff01fe01e0

def z946 : W := mkw 0xf0059c9a98000000 0x7802ce4d4c000000 0x3ff7dfffdc000000 0x1ffbefffee000000

def z947 : W := mkw 0xf007fcdbb8000000 0x7803fe6ddc000000 0x23f7fffdfc000000 0x11fbfffefe000000

def z948 : W := mkw 0xab0581b603780780 0x5582c0db01bc03c0 0xffffd9fe13ff3fe7 0xffffecff09ff9ff3

def z949 : W := mkw 0xcc07f60001aef000 0x6603fb0000d77800 0xc17f780003fff801 0xe0bfbc0001fffc00

def z950 : W := mkw 0xcc07f64121aef011 0x6603fb2090d77808 0xc3fffe0023fff819 0xe1ffff0011fffc0c

def z951 : W := mkw 0xf807fcdbb9aa9000 0x7c03fe6ddcd54800 0xffffffffffff1800 0xffffffffffff8c00

def z952 : W := mkw 0xabc581b643790fa4 0x55e2c0db21bc87d2 0xdfffd9fe03ff3fe7 0xefffecff01ff9ff3

def z953 : W := mkw 0xc807f40001aa9000 0x6403fa0000d54800 0x413f580003f31801 0x209fac0001f98c00

def z954 : W := mkw 0xab0581b603780780 0x5582c0db01bc03c0 0x9cc781fe01fc07c0 0xce63c0ff00fe03e0

def z955 : W := mkw 0xf007fcdbb8000000 0x7803fe6ddc000000 0x0bf7ffffec000000 0x05fbfffff6000000

def z956 : W := mkw 0x13c0090cd2110d24 0x09e0048669088692 0x7fb9591df2333f3f 0xbfdcac8ef9199f9f

def z957 : W := mkw 0xcc07f60001aef000 0x6603fb0000d77800 0xd3fffe0013fff907 0xe9ffff0009fffc83

def z958 : W := mkw 0xab0581b603780780 0x5582c0db01bc03c0 0xc8f781fe03fc02c0 0xe47bc0ff01fe0160

def z959 : W := mkw 0x13c0092cd2510fa4 0x09e00496692887d2 0x77b9591dd2333fe7 0xbbdcac8ee9199ff3

def z960 : W := mkw 0xf007fcdbb8000000 0x7803fe6ddc000000 0x0846a7ffec000000 0x042353fff6000000

def z961 : W := mkw 0x0800000001aa9000 0x0400000000d54800 0x43b9580003f33801 0xa1dcac0001f99c00

def z962 : W := mkw 0xf007fcdbb8000000 0x7803fe6ddc000000 0x2d77ffffec000000 0x16bbfffff6000000

def z963 : W := mkw 0x230001b602500780 0x118000db012803c0 0xdcf681fe03cc07c0 0xee7b40ff01e603e0

def z964 : W := mkw 0xcc27f60005aef04a 0xe613fb0002d77825 0xdffffe022fffffd9 0xefffff0117ffffec

def z965 : W := mkw 0xec07f6d329aef000 0x7603fb6994d77800 0xfffffee23ffff801 0xffffff711ffffc00

def z966 : W := mkw 0xec07f69201aef080 0x7603fb4900d77840 0xc3fffe0203fff8c1 0xe1ffff0101fffc60

def z967 : W := mkw 0xab0581b603780780 0x5582c0db01bc03c0 0xdcf7a7fe2ffc07c0 0xee7bd3ff17fe03e0

def z968 : W := mkw 0x13c0090cd2110d24 0x09e0048669088692 0xf7f9d91dd23f3d27 0xfbfcec8ee91f9e93

def z969 : W := mkw 0xf807fcdbb9aa9000 0x7c03fe6ddcd54800 0x3ff7fffffdc00000 0x1ffbfffffee00000

def z970 : W := mkw 0xc807f40001aa9000 0x6403fa0000d54800 0x77bf580013f33d27 0xbbdfac0009f99e93

def z971 : W := mkw 0xcc07f60001aef000 0x6603fb0000d77800 0x03fffe0003f3f801 0x01ffff0001f9fc00

def z972 : W := mkw 0xec27f6d32daef04a 0xf613fb6996d77825 0xcbfffee22ffffad9 0xe5ffff7117fffd6c

def z973 : W := mkw 0xab0581b603780780 0x5582c0db01bc03c0 0xfcf781fe23fc07f8 0xfe7bc0ff11fe03fc

def z974 : W := mkw 0xcc07f64121aef000 0x6603fb2090d77800 0xefffffe1e3fffe39 0xf7fffff0f1ffff1c

def z975 : W := mkw 0x2b0001b603780780 0x158000db01bc03c0 0xdc7601fe03fc07c0 0xee3b00ff01fe03e0

def z976 : W := mkw 0xcc07f60001aef000 0x6603fb0000d77800 0x43bf7e0003f3f801 0xa1dfbf0001f9fc00

def z977 : W := mkw 0xab0581b603780780 0x5582c0db01bc03c0 0xdcd681fe01cc07c0 0xee6b40ff00e603e0

def z978 : W := mkw 0xf007fcdbb8000000 0x7803fe6ddc000000 0x3ffffffffe331800 0x1fffffffff198c00

def z979 : W := mkw 0xf007fcdbb8000000 0x7803fe6ddc000000 0xfff7fffffc0c27e7 0xfffbfffffe0613f3

def z980 : W := mkw 0xf007fcdbb8000000 0x7803fe6ddc000000 0x3ff7fffffc002106 0x9ffbfffffe001083

def z981 : W := mkw 0x13c0090cd2110d24 0x09e0048669088692 0x0029591dc2333906 0x8014ac8ee1199c83

def z982 : W := mkw 0xabc581b643790fa4 0x55e2c0db21bc87d2 0xfdffc1ffc3ff3fe7 0xfeffe0ffe1ff9ff3

def z983 : W := mkw 0x0282616162c38631 0x014130b0b161c318 0xe53e41e1c3c3c639 0x729f20f0e1e1e31c

def z984 : W := mkw 0xab8581b6437907a0 0x55c2c0db21bc83d0 0xffffc1ffd3ff27e7 0xffffe0ffe9ff93f3

def z985 : W := mkw 0x0002600000828000 0x0001300000414000 0xc17f780003f3d801 0x60bfbc0001f9ec00

def z986 : W := mkw 0x13c0090cd2110d24 0x09e0048669088692 0x54b9591dc2333d27 0xaa5cac8ee1199e93

def z987 : W := mkw 0x13c0092cd2510f24 0x09e0049669288792 0xffffd9ffd3ff3fe7 0xffffecffe9ff9ff3

def z988 : W := mkw 0x03c2616562d38f35 0x01e130b2b169c79a 0xfdff61fde3f3ff3f 0xfeffb0fef1f9ff9f

def z989 : W := mkw 0x13c0090cd2110d24 0x09e0048669088692 0x6539591dc2333d27 0xb29cac8ee1199e93

def z990 : W := mkw 0x4c00160001aef000 0x26000b0000d77800 0xc2081e0003fff801 0xe1040f0001fffc00

def z991 : W := mkw 0x1140080c90100904 0x08a0040648080482 0x77b9591dd2333907 0xbbdcac8ee9199c83

def z992 : W := mkw 0x0282616162c38631 0x014130b0b161c318 0xe17e61e1e3c3c039 0x70bf30f0f1e1e01c

def z993 : W := mkw 0x0282616162c38631 0x014130b0b161c318 0xed7ee7e3efc3c639 0x76bf73f1f7e1e31c

def z994 : W := mkw 0x0282616162c38631 0x014130b0b161c318 0xefff79e1e3c3c639 0x77ffbcf0f1e1e31c

def z995 : W := mkw 0x0282616162c38631 0x014130b0b161c318 0xfffee7e3ffcfc7f9 0xffff73f1ffe7e3fc

def z996 : W := mkw 0xcc07f60001aef000 0x6603fb0000d77800 0xcbfffe0023fffa19 0xe5ffff0011fffd0c

def z997 : W := mkw 0xcc07f60001aef000 0x6603fb0000d77800 0xc37f7e0003f3f801 0x61bfbf0001f9fc00

def z998 : W := mkw 0x11c0080cd0110924 0x08e0040668088492 0x37b9591dd0333927 0x9bdcac8ee8199c93

def z999 : W := mkw 0x0282616162c38631 0x014130b0b161c318 0xad7e61e1e3c3c218 0x56bf30f0f1e1e10c

def z1000 : W := mkw 0xcc07f60001aef000 0x6603fb0000d77800 0x83fffe0003ffd800 0x41ffff0001ffec00

def z1001 : W := mkw 0x33e009bed6510fee 0x99f004df6b2887f7 0x3c0001fffc0007fe 0x1e0000fffe0003ff

def z1002 : W := mkw 0xc807f40001aa9000 0x6403fa0000d54800 0xc3ffd80003ff3801 0xe1ffec0001ff9c00

def z1003 : W := mkw 0x13c0090cd2110d24 0x09e0048669088692 0x56b9591dd2333d06 0xab5cac8ee9199e83

def z1004 : W := mkw 0x0300012402500700 0x0180009201280380 0xdcf781fe03fc07c0 0xee7bc0ff01fe03e0

def z1005 : W := mkw 0xf007fcdbb8000000 0x7803fe6ddc000000 0x0027dfffcc000000 0x0013efffe6000000

def z1006 : W := mkw 0x0282616162c38631 0x014130b0b161c318 0xed7e61e1e3c3e73f 0xf6bf30f0f1e1f39f

def z1007 : W := mkw 0xf0059cdbb8000000 0x7802ce6ddc000000 0x3fd1bffffc000000 0x1fe8dffffe000000

def z1008 : W := mkw 0xab0581b603780780 0x5582c0db01bc03c0 0xdcffd9fe03ff1fc0 0xee7fecff01ff8fe0

def z1009 : W := mkw 0xf007fcdbb8000000 0x7803fe6ddc000000 0x3ff7fffffc000638 0x1ffbfffffe00031c

def z1010 : W := mkw 0xcc07f64121aef000 0x6603fb2090d77800 0xe3fffe01e3fff801 0xf1ffff00f1fffc00

def z1011 : W := mkw 0xcc07f60001aef000 0x6603fb0000d77800 0x002f580003ff3800 0x8017ac0001ff9c00

def z1012 : W := mkw 0x0fe00324477d6fee 0x87f0019223beb7f7 0xc008000003ffffff 0xe004000001ffffff

def z1013 : W := mkw 0x02c2616162c38e35 0x016130b0b161c71a 0xed7e61e1e3c3fe3f 0x76bf30f0f1e1ff1f

def z1014 : W := mkw 0x042002000404604a 0x8210010002023025 0xfff0e703fc0ce7ff 0xfff87381fe0673ff

def z1015 : W := mkw 0xc807f40001aa9000 0x6403fa0000d54800 0x006ffe0003f31800 0x0037ff0001f98c00

def z1016 : W := mkw 0xab0581b603780780 0x5582c0db01bc03c0 0xfdf7c1ffc3fc07c0 0xfefbe0ffe1fe03e0

def z1017 : W := mkw 0xcc07f60001aef000 0x6603fb0000d77800 0x03fffe0003ff3800 0x81ffff0001ff9c00

def z1018 : W := mkw 0xcc27f60005aef04a 0xe613fb0002d77825 0xfffffe023ffff9c7 0xffffff011ffffce3

def z1019 : W := mkw 0x428275616ac38631 0x21413ab0b561c318 0xed7e67e1efc3c639 0x76bf33f0f7e1e31c

def z1020 : W := mkw 0xf007fcdbb8000000 0x7803fe6ddc000000 0xfff7ffffffc00000 0x7ffbffffffe00000

def z1021 : W := mkw 0xab0581b603780780 0x5582c0db01bc03c0 0xfdf781fe03fc07e1 0xfefbc0ff01fe03f0

def z1022 : W := mkw 0x042002000404604a 0x8210010002023025 0xbfd0a6023c0cc7fe 0x5fe853011e0663ff

def z1023 : W := mkw 0xf007fcdbb8000000 0x7803fe6ddc000000 0x7ff7fffffc000421 0x3ffbfffffe000210

def z1024 : W := mkw 0xcc27f60005aef04a 0xe613fb0002d77825 0xebfffe023ffffaff 0xf5ffff011ffffd7f

def z1025 : W := mkw 0xc807f40001aa9000 0x6403fa0000d54800 0x032f580003f33801 0x0197ac0001f99c00

def z1026 : W := mkw 0xab0581b603780780 0x5582c0db01bc03c0 0x9cf781fe03fc02c0 0x4e7bc0ff01fe0160

def z1027 : W := mkw 0xabc581b643790fa4 0x55e2c0db21bc87d2 0xdcf781fe03fc07e6 0xee7bc0ff01fe03f3

def z1028 : W := mkw 0x0282616162c38631 0x014130b0b161c318 0xc17e61e1c3c3c639 0x60bf30f0e1e1e31c

def z1029 : W := mkw 0xf007fcdbb8000000 0x7803fe6ddc000000 0x3f81fffffc000000 0x1fc0fffffe000000

def z1030 : W := mkw 0x042002000404604a 0x8210010002023025 0xdac0a6023c0ce7ff 0xed6053011e0673ff

def z1031 : W := mkw 0xcc07f60001aef000 0x6603fb0000d77800 0xc2ffde0003ff3800 0xe17fef0001ff9c00

def z1032 : W := mkw 0xab0581b603780780 0x5582c0db01bc03c0 0x9cf781fe01cc07c0 0x4e7bc0ff00e603e0

def z1033 : W := mkw 0x0fa0032447ffe7fb 0x87d0019223fff3fd 0xc008000003ffe7ff 0xe004000001fff3ff

def z1034 : W := mkw 0x440276000086f000 0x22013b0000437800 0xc3ff7e0003f3f801 0xe1ffbf0001f9fc00

def z1035 : W := mkw 0x0282616162c38631 0x014130b0b161c318 0xe12e61e1e3c3c639 0x709730f0f1e1e31c

def z1036 : W := mkw 0xcc27f60005aef04a 0xe613fb0002d77825 0xc3fffe020ffff8c1 0xe1ffff0107fffc60

def z1037 : W := mkw 0x042002000404604a 0x8210010002023025 0xbec0a6023c0ce7fe 0xdf6053011e0673ff

def z1038 : W := mkw 0xc807f40001aa9000 0x6403fa0000d54800 0xdcffd80203ff1fc0 0xee7fec0101ff8fe0

def z1039 : W := mkw 0x0282616162c38631 0x014130b0b161c318 0x002e61e1e3c3c018 0x001730f0f1e1e00c

def z1040 : W := mkw 0xcc27f60005aef04a 0xe613fb0002d77825 0x232f7e003ff3f83f 0x1197bf001ff9fc1f

def z1041 : W := mkw 0xf007fcdbb8000000 0x7803fe6ddc000000 0xfff7fffffc000600 0x7ffbfffffe000300

def z1042 : W := mkw 0xf007fcdbb8000000 0x7803fe6ddc000000 0x3ea7dffffc000000 0x1f53effffe000000

def z1043 : W := mkw 0x0002606120c28211 0x0001303090614108 0xed7e61e1e3c3c219 0x76bf30f0f1e1e10c

def z1044 : W := mkw 0xab8581b6437907a0 0x55c2c0db21bc83d0 0xdcff81fe03ff07e1 0xee7fc0ff01ff83f0

def z1045 : W := mkw 0xf007fcdbb8828000 0x7803fe6ddc414000 0x3ffffffffc03c001 0x1ffffffffe01e000

def z1046 : W := mkw 0xc807f44121aa9000 0x6403fa2090d54800 0x2d7f79e1e3f31800 0x16bfbcf0f1f98c00

def z1047 : W := mkw 0x0282616162c38631 0x014130b0b161c318 0xef7e67e1ffc3c639 0x77bf33f0ffe1e31c

def z1048 : W := mkw 0xf007fcdbb8000000 0x7803fe6ddc000000 0x7ff7fffffc002001 0xbffbfffffe001000

def z1049 : W := mkw 0x0282616162c38631 0x014130b0b161c318 0xfd7e61e3e3c3c7f9 0x7ebf30f1f1e1e3fc

def z1050 : W := mkw 0xc007f40000828000 0x6003fa0000414000 0xc3fffe0003f3f801 0xe1ffff0001f9fc00

def z1051 : W := mkw 0xab0581b603780780 0x5582c0db01bc03c0 0xddffc1fe03ff07c1 0xeeffe0ff01ff83e0

def z1052 : W := mkw 0xcc07f60001aef000 0x6603fb0000d77800 0x022f5e0003f33800 0x0117af0001f99c00

def z1053 : W := mkw 0x0002600000828000 0x0001300000414000 0x43bf580003f33801 0xa1dfac0001f99c00

def z1054 : W := mkw 0xcc07f60001aef000 0x6603fb0000d77800 0xc06ffe0003fff801 0xe037ff0001fffc00

def z1055 : W := mkw 0xf807fcdbb9280000 0x7c03fe6ddc940000 0xffffffffffff3801 0xffffffffffff9c00

def z1056 : W := mkw 0x0002606120c28211 0x0001303090614108 0xac4621e1e1c0c218 0x562310f0f0e0610c

def z1057 : W := mkw 0xc807f44121aa9000 0x6403fa2090d54800 0x002f59e1c3f31800 0x0017acf0e1f98c00

def z1058 : W := mkw 0x03c2616562d38f35 0x01e130b2b169c79a 0xefff79e1e3f3ff3f 0xf7ffbcf0f1f9ff9f

def z1059 : W := mkw 0xab0581b603780780 0x5582c0db01bc03c0 0x1ca781fe03fc07c0 0x8e53c0ff01fe03e0

def z1060 : W := mkw 0xcc27f64125aef04a 0xe613fb2092d77825 0xffffffe3ffffffff 0xfffffff1ffffffff

def z1061 : W := mkw 0xb005889a90000000 0x5802c44d48000000 0x3ff7fffffc000000 0x1ffbfffffe000000

def z1062 : W := mkw 0xe807f4d329aa9000 0x7403fa6994d54800 0x002f58e003f31800 0x0017ac7001f98c00

def z1063 : W := mkw 0xf007fcdbb8000000 0x7803fe6ddc000000 0x37b77ffdfc000000 0x1bdbbffefe000000

def z1064 : W := mkw 0xa90580b601780380 0x5482c05b00bc01c0 0x9cf781fe01fc03c0 0xce7bc0ff00fe01e0

def z1065 : W := mkw 0xf007fcdbb8000000 0x7803fe6ddc000000 0x7ff7fffffc000500 0xbffbfffffe000280

def z1066 : W := mkw 0x0082606160c38231 0x00413030b061c118 0xad7e61e1e1c3c239 0x56bf30f0f0e1e11c

def z1067 : W := mkw 0xf007fcdbb8000000 0x7803fe6ddc000000 0x33a7fffffc000000 0x19d3fffffe000000

def z1068 : W := mkw 0xf807fcdbb9280080 0x7c03fe6ddc940040 0x3ff7fffffc0c00c0 0x1ffbfffffe060060

def z1069 : W := mkw 0xc805940001aa9000 0x6402ca0000d54800 0x0009180003f31800 0x00048c0001f98c00

def z1070 : W := mkw 0xab0581b603780780 0x5582c0db01bc03c0 0xfcf781fe13fc07e6 0xfe7bc0ff09fe03f3

def z1071 : W := mkw 0xc807f40001aa9000 0x6403fa0000d54800 0x03bf580003f31800 0x01dfac0001f98c00

def z1072 : W := mkw 0x0282616162c38631 0x014130b0b161c318 0xfffee7e3ffc3e73f 0xffff73f1ffe1f39f

def z1073 : W := mkw 0xf0059cdbb8000000 0x7802ce6ddc000000 0x3c0087fffc000000 0x1e0043fffe000000

def z1074 : W := mkw 0xa90580b601780380 0x5482c05b00bc01c0 0xd8f780fe03fc03c0 0xec7bc07f01fe01e0

def z1075 : W := mkw 0x0282616162c38631 0x014130b0b161c318 0xed7e61e1e3cfc7f9 0xf6bf30f0f1e7e3fc

def z1076 : W := mkw 0x07e0032446d7ef7f 0x83f00192236bf7bf 0xc008000003ffffff 0xe004000001ffffff

def z1077 : W := mkw 0xab0581b603780780 0x5582c0db01bc03c0 0x002781fe03fc00c0 0x0013c0ff01fe0060

def z1078 : W := mkw 0x17e00b6df6556f7f 0x8bf005b6fb2ab7bf 0xffd0a7fffc0ce7ff 0xffe853fffe0673ff

def z1079 : W := mkw 0x0282616162c38631 0x014130b0b161c318 0x2d7e61e1e3c3c039 0x16bf30f0f1e1e01c

def z1080 : W := mkw 0xa90580b601780380 0x5482c05b00bc01c0 0xdcd780fe01fc07c0 0xee6bc07f00fe03e0

def z1081 : W := mkw 0x70027cdbb8000000 0x38013e6ddc000000 0x3fd0fffffc000000 0x1fe87ffffe000000

def z1082 : W := mkw 0xab0581b603780780 0x5582c0db01bc03c0 0xdff7a7fe03fc07c0 0xeffbd3ff01fe03e0

def z1083 : W := mkw 0x33c009bed2510fa4 0x19e004df692887d2 0xffd081ffd00c27e7 0xffe840ffe80613f3

def z1084 : W := mkw 0x10c00808d0010824 0x0860040468008412 0x77b9591dd2333827 0xbbdcac8ee9199c13

def z1085 : W := mkw 0x13c0092cd2510f24 0x09e0049669288792 0xffff79fdf3f3ff3f 0xffffbcfef9f9ff9f

def z1086 : W := mkw 0x11c0080cd0110924 0x08e0040668088492 0x73b9581dd2333927 0xb9dcac0ee9199c93

def z1087 : W := mkw 0xa90580b601780380 0x5482c05b00bc01c0 0x984680fe01cc03c0 0x4c23407f00e601e0

def z1088 : W := mkw 0xcc27f60005aef04a 0xe613fb0002d77825 0xdbfffe023ffffbdf 0xedffff011ffffdef

def z1089 : W := mkw 0x0282616162c38631 0x014130b0b161c318 0x653e61e1e3c3c439 0x329f30f0f1e1e21c

def z1090 : W := mkw 0x13c0092cd2510fa4 0x09e00496692887d2 0x3400011dd00007e6 0x1a00008ee80003f3

def z1091 : W := mkw 0x13c0090cd2110d24 0x09e0048669088692 0x36a9591dd2333d26 0x9b54ac8ee9199e93

def z1092 : W := mkw 0xf807fcdbb9280000 0x7c03fe6ddc940000 0x3ff7fffffc3c0000 0x9ffbfffffe1e0000

def z1093 : W := mkw 0xcc27f60005aef04a 0xe613fb0002d77825 0xe3fffe003fffffff 0xf1ffff001fffffff

def z1094 : W := mkw 0xf007fcdbb8000000 0x7803fe6ddc000000 0xfff7fffffc00e73f 0xfffbfffffe00739f

def z1095 : W := mkw 0xcc25960005aef04a 0xe612cb0002d77825 0xd2899e021fffffff 0xe944cf010fffffff

def z1096 : W := mkw 0xcc07f60001aef000 0x6603fb0000d77800 0xcbfffe0203fffac1 0xe5ffff0101fffd60

def z1097 : W := mkw 0xe807f4d329aa9000 0x7403fa6994d54800 0x086ffee22ff31800 0x0437ff7117f98c00

def z1098 : W := mkw 0x13c0090cd2110d24 0x09e0048669088692 0xfff9ff1ffe3f3fe7 0xfffcff8fff1f9ff3

def z1099 : W := mkw 0xc807f40001aa9000 0x6403fa0000d54800 0x012f780003f3d801 0x0097bc0001f9ec00

def z1100 : W := mkw 0xcc27f60005aef04a 0xe613fb0002d77825 0x886ffe022fffdad8 0x4437ff0117ffed6c

def z1101 : W := mkw 0x0282616162c38631 0x014130b0b161c318 0xad4e61e1e1c3c639 0x56a730f0f0e1e31c

def z1102 : W := mkw 0xcc05960001aef000 0x6602cb0000d77800 0xc3b9de0003fff801 0xe1dcef0001fffc00

def z1103 : W := mkw 0x0202616122400600 0x010130b091200300 0xed7661e1e3c0c639 0x76bb30f0f1e0631c

def z1104 : W := mkw 0xcc07f60001aef000 0x6603fb0000d77800 0xd3fffe0203fff9c1 0xe9ffff0101fffce0

def z1105 : W := mkw 0x0082604160838031 0x00413020b041c018 0xed7e61e1e3c3c039 0x76bf30f0f1e1e01c

def z1106 : W := mkw 0x70001cdbb8000000 0x38000e6ddc000000 0x3e001ffffc000000 0x1f000ffffe000000

def z1107 : W := mkw 0xa80580b201680280 0x5402c05900b40140 0x98c780fe01cc02c0 0x4c63c07f00e60160

def z1108 : W := mkw 0xcc07f60001aef000 0x6603fb0000d77800 0xd3fffe021ffff801 0xe9ffff010ffffc00

def z1109 : W := mkw 0x042262000486e04a 0x8211310002437025 0xfffffe023fffffff 0xffffff011fffffff

def z1110 : W := mkw 0x0b00012403780780 0x0580009201bc03c0 0xdcf701fc03fc07c0 0xee7b80fe01fe03e0

def z1111 : W := mkw 0xf007fcdbb8000000 0x7803fe6ddc000000 0x3ff7fffffc000526 0x1ffbfffffe000293

def z1112 : W := mkw 0x13c0090cd2110d24 0x09e0048669088692 0x63b9591dd2333827 0xb1dcac8ee9199c13

def z1113 : W := mkw 0x040262000086e000 0x0201310000437000 0xc3fffe0003fff801 0xe1ffff0001fffc00

def z1114 : W := mkw 0xab4581b603780f84 0x55a2c0db01bc07c2 0xdcf781fe03fc3fc6 0xee7bc0ff01fe1fe3

def z1115 : W := mkw 0xec07f6d321aef000 0x7603fb6990d77800 0xffffffffe3fff801 0xfffffffff1fffc00

def z1116 : W := mkw 0x0c00020001aef000 0x0600010000d77800 0xc3f9fe0003fff801 0xe1fcff0001fffc00

def z1117 : W := mkw 0x0002600000828000 0x0001300000414000 0x002f580003f31800 0x0017ac0001f98c00

def z1118 : W := mkw 0x0282616162c38631 0x014130b0b161c318 0xfd7e61e1f3c3c73f 0x7ebf30f0f9e1e39f

def z1119 : W := mkw 0x13c0090cd2110d24 0x09e0048669088692 0x37b9591dd2333906 0x9bdcac8ee9199c83

def z1120 : W := mkw 0xc807f40001aa9000 0x6403fa0000d54800 0xc02f580003f3d801 0x6017ac0001f9ec00

def z1121 : W := mkw 0x0282616162c38631 0x014130b0b161c318 0xec4e21e1e3c3c639 0x762710f0f1e1e31c

def z1122 : W := mkw 0xab0581b603780780 0x5582c0db01bc03c0 0xd8c780fe03fc07c0 0xec63c07f01fe03e0

def z1123 : W := mkw 0xcc07f60001aef000 0x6603fb0000d77800 0xc3fffe0003fffd27 0xe1ffff0001fffe93

def z1124 : W := mkw 0xab8581b6437907a0 0x55c2c0db21bc83d0 0xfdffe1ffe3ffc7f9 0xfefff0fff1ffe3fc

def z1125 : W := mkw 0x33c009fffa510fa4 0x19e004fffd2887d2 0x3c0001fffc0007e6 0x1e0000fffe0003f3

def z1126 : W := mkw 0xcc07f64129aef000 0x6603fb2094d77800 0xc3fffe002ffff801 0xe1ffff0017fffc00

def z1127 : W := mkw 0xcc27f60005aef04a 0xe613fb0002d77825 0xfffffe023ffff83f 0xffffff011ffffc1f

def z1128 : W := mkw 0x0282616162c38631 0x014130b0b161c318 0x2d2e61e1e3c3c639 0x169730f0f1e1e31c

def z1129 : W := mkw 0x4c02760001aef000 0x26013b0000d77800 0xc3d8fe0003fff801 0xe1ec7f0001fffc00

def z1130 : W := mkw 0x0282616162c38631 0x014130b0b161c318 0xfffee1e3f3cfe7ff 0xffff70f1f9e7f3ff

def z1131 : W := mkw 0xab0581b603780780 0x5582c0db01bc03c0 0xfdf7a1fe23fc07c0 0xfefbd0ff11fe03e0

def z1132 : W := mkw 0xcc07f60001aef000 0x6603fb0000d77800 0xc2cfbe0003fff801 0xe167df0001fffc00

def z1133 : W := mkw 0xcc07f60001aef000 0x6603fb0000d77800 0x002f7e0003f3d800 0x0017bf0001f9ec00

def z1134 : W := mkw 0x0800000001280000 0x0400000000940000 0xc3b9580003ff3801 0xe1dcac0001ff9c00

def z1135 : W := mkw 0x13c0090cd2110d24 0x09e0048669088692 0x3789591dd0333d27 0x9bc4ac8ee8199e93

def z1136 : W := mkw 0x13c0090cd2110d24 0x09e0048669088692 0x0029591dc2333827 0x0014ac8ee1199c13

def z1137 : W := mkw 0x14e26a49f487e87f 0x8a713524fa43f43f 0x23087e01fc03f83f 0x11843f00fe01fc1f

def z1138 : W := mkw 0xcc27f60005aef04a 0xe613fb0002d77825 0xf7fffe0013ffffff 0xfbffff0009ffffff

def z1139 : W := mkw 0xab0581b603780780 0x5582c0db01bc03c0 0xdff7d9fe03fc07c0 0xeffbecff01fe03e0

def z1140 : W := mkw 0xcc07f60001aef000 0x6603fb0000d77800 0xd7ffff1c03fff801 0xebffff8e01fffc00

def z1141 : W := mkw 0x8c258200052c604a 0xc612c10002963025 0xfffffe023fffffff 0xffffff011fffffff

def z1142 : W := mkw 0xab0581b603780780 0x5582c0db01bc03c0 0x54b781fe03fc05c0 0xaa5bc0ff01fe02e0

def z1143 : W := mkw 0xcc07f60001aef000 0x6603fb0000d77800 0xcbfffe022ffff801 0xe5ffff0117fffc00

def z1144 : W := mkw 0x0382616562d38731 0x01c130b2b169c398 0xffff61fdf3f3e73f 0xffffb0fef9f9f39f

def z1145 : W := mkw 0x13c0090cd2110d24 0x09e0048669088692 0x43b9591dc2333d27 0xa1dcac8ee1199e93

def z1146 : W := mkw 0xab8581b6437907a0 0x55c2c0db21bc83d0 0xfcf781ffc3fc07e0 0xfe7bc0ffe1fe03f0

def z1147 : W := mkw 0xab0581b603780780 0x5582c0db01bc03c0 0x002701fc03fc01c0 0x801380fe01fe00e0

def z1148 : W := mkw 0xf007fcdbb8000000 0x7803fe6ddc000000 0xfff7fffffc0c0000 0xfffbfffffe060000

def z1149 : W := mkw 0xcc07f60001aef000 0x6603fb0000d77800 0xc389fe0003fff801 0xe1c4ff0001fffc00

def z1150 : W := mkw 0x13c0090cd2110d24 0x09e0048669088692 0x6739591dd2333c27 0x339cac8ee9199e13

def z1151 : W := mkw 0xab0581b603780780 0x5582c0db01bc03c0 0x9c6781fe03fc07c0 0x4e33c0ff01fe03e0

def z1152 : W := mkw 0x10026849b0000000 0x08013424d8000000 0x3ff7fffffc000000 0x1ffbfffffe000000

def z1153 : W := mkw 0x042002000404604a 0x8210010002023025 0xfff8e6023e0fe7ff 0xfffc73011f07f3ff

def z1154 : W := mkw 0x0282616162c38631 0x014130b0b161c318 0xed7e61e1e3f3fe39 0xf6bf30f0f1f9ff1c

def z1155 : W := mkw 0xcc059600012c7000 0x6602cb0000963800 0xc3ffde0003ff3801 0xe1ffef0001ff9c00

def z1156 : W := mkw 0xcc07f60001aef000 0x6603fb0000d77800 0xc3fffe0003ffffc1 0xe1ffff0001ffffe0

def z1157 : W := mkw 0xab0581b603780780 0x5582c0db01bc03c0 0xcc7781fe03fc06c0 0x663bc0ff01fe0360

def z1158 : W := mkw 0x13c0092cd2510f24 0x09e0049669288792 0xf7b9591dd3f33f27 0xfbdcac8ee9f99f93

def z1159 : W := mkw 0xcc27f60005aef04a 0xe613fb0002d77825 0xfffffe023ffffad9 0xffffff011ffffd6c

def z1160 : W := mkw 0xb00588dbb8000000 0x5802c46ddc000000 0x3ff7a7fffc000000 0x1ffbd3fffe000000

def z1161 : W := mkw 0x0282616162c38631 0x014130b0b161c318 0xef7e61e1f3c3e63f 0x77bf30f0f9e1f31f

def z1162 : W := mkw 0xfd259e9e9d3c61ca 0xfe92cf4f4e9e30e5 0x12819e1e1c3c21c6 0x8940cf0f0e1e10e3

def z1163 : W := mkw 0x042002000404604a 0x8210010002023025 0xbf40a6023c0ce7ff 0x5fa053011e0673ff

def z1164 : W := mkw 0xcc07f60001aef000 0x6603fb0000d77800 0x82effe0003fff800 0xc177ff0001fffc00

def z1165 : W := mkw 0xab0581b603780780 0x5582c0db01bc03c0 0xdc2701fe03fc07c0 0xee1380ff01fe03e0

def z1166 : W := mkw 0xcc27f60005aef04a 0xe613fb0002d77825 0xeffffe0023ffffff 0xf7ffff0011ffffff

def z1167 : W := mkw 0x0382616562d38731 0x01c130b2b169c398 0xfdffe1ffe3ffc7f9 0xfefff0fff1ffe3fc

def z1168 : W := mkw 0xcc27f60005aef04a 0xe613fb0002d77825 0xeffffe003ffffe3f 0xf7ffff001fffff1f

def z1169 : W := mkw 0xab0581b603780780 0x5582c0db01bc03c0 0xd0f781fe03fc01c0 0xe87bc0ff01fe00e0

def z1170 : W := mkw 0xab8581b6437907a0 0x55c2c0db21bc83d0 0xdcffc1ffc3ff07c0 0xee7fe0ffe1ff83e0

def z1171 : W := mkw 0xab0581b603780780 0x5582c0db01bc03c0 0xfff7a1fe33fce7ff 0xfffbd0ff19fe73ff

def z1172 : W := mkw 0xcc07f60001aef000 0x6603fb0000d77800 0xcfffffe003fff801 0xe7fffff001fffc00

def z1173 : W := mkw 0xcc27f60005aef04a 0xe613fb0002d77825 0xf7fffe003ffffd3f 0xfbffff001ffffe9f

def z1174 : W := mkw 0xa007e0d320000000 0x5003f06990000000 0x3ff7e7fffc000000 0x1ffbf3fffe000000

def z1175 : W := mkw 0xab0581b603780780 0x5582c0db01bc03c0 0xfff7a7fe3ffcc7f9 0xfffbd3ff1ffe63fc

def z1176 : W := mkw 0xcc07f60001aef000 0x6603fb0000d77800 0xdffffe0203fff801 0xefffff0101fffc00

def z1177 : W := mkw 0xcc07f60001aef000 0x6603fb0000d77800 0xe7fffe0003fffc21 0xf3ffff0001fffe10

def z1178 : W := mkw 0x13c0092cd2510f35 0x09e004966928879a 0x77b9591dd2333f3f 0xbbdcac8ee9199f9f

def z1179 : W := mkw 0x4c22760005aef04a 0xa6113b0002d77825 0xe3087e003fffffff 0xf1843f001fffffff

def z1180 : W := mkw 0x042002000404604a 0x8210010002023025 0xfcd0a6023c0cc7fe 0xfe6853011e0663ff

def z1181 : W := mkw 0xe807f49201aa9000 0x7403fa4900d54800 0x002f59fc03f31800 0x0017acfe01f98c00

def z1182 : W := mkw 0x13c0090cd2110d24 0x09e0048669088692 0xfff9f91ff23fffff 0xfffcfc8ff91fffff

def z1183 : W := mkw 0xec27f69205aef04a 0xf613fb4902d77825 0xfffffffe3fffffff 0xffffffff1fffffff

def z1184 : W := mkw 0xec07f69209aef000 0x7603fb4904d77800 0xc3fffe020ffff801 0xe1ffff0107fffc00

def z1185 : W := mkw 0x0282616162c38631 0x014130b0b161c318 0xed7ee1e3e3cfc6f9 0x76bf70f1f1e7e37c

def z1186 : W := mkw 0x54227e49bc86f04a 0xaa113f24de437825 0x23087e01fc03f83f 0x11843f00fe01fc1f

def z1187 : W := mkw 0x13c0090cd2110d24 0x09e0048669088692 0x7429591dd2333d27 0xba14ac8ee9199e93

def z1188 : W := mkw 0x0382616562d38731 0x01c130b2b169c398 0xfd7e61fde3c3c739 0x7ebf30fef1e1e39c

def z1189 : W := mkw 0x042002000404604a 0x8210010002023025 0xfff1a6023e3ce7ff 0xfff8d3011f1e73ff

def z1190 : W := mkw 0xab0581b603780780 0x5582c0db01bc03c0 0xdff781fe03fc27c1 0xeffbc0ff01fe13e0

def z1191 : W := mkw 0x0202616122c28611 0x010130b091614308 0xed7661e1e3c0c618 0x76bb30f0f1e0630c

def z1192 : W := mkw 0x0082606160c38231 0x00413030b061c118 0x210e60e1e1c3c039 0x10873070f0e1e01c

def z1193 : W := mkw 0x4c02760001aef000 0x26013b0000d77800 0xc008580003fff801 0xe0042c0001fffc00

def z1194 : W := mkw 0xeb0595b60b780780 0x7582cadb05bc03c0 0xdcf787fe0ffc07c0 0xee7bc3ff07fe03e0

def z1195 : W := mkw 0x13c0090cd2110d24 0x09e0048669088692 0x6329591dd2333d27 0xb194ac8ee9199e93

def z1196 : W := mkw 0x4c02760001aef000 0x26013b0000d77800 0x03087e0003f3f801 0x01843f0001f9fc00

def z1197 : W := mkw 0x13c0090cd2110d24 0x09e0048669088692 0x7389581dd2333d27 0xb9c4ac0ee9199e93

def z1198 : W := mkw 0xec27f6d32daef04a 0xf613fb6996d77825 0xfffffee23fffffff 0xffffff711fffffff

def z1199 : W := mkw 0xf007fcdbb8000000 0x7803fe6ddc000000 0x1ae7fffffc000000 0x0d73fffffe000000

def z1200 : W := mkw 0x300008dbb8000000 0x1800046ddc000000 0x3ff1fffffc000000 0x1ff8fffffe000000

def z1201 : W := mkw 0x0280016162c38631 0x014000b0b161c318 0xec7e01e1e3c3c639 0x763f00f0f1e1e31c

def z1202 : W := mkw 0xf0059cdbb8000000 0x7802ce6ddc000000 0x3ef79ffffc000000 0x1f7bcffffe000000

def z1203 : W := mkw 0xec07f6d329aef000 0x7603fb6994d77800 0xdffffffe2ffff801 0xefffffff17fffc00

def z1204 : W := mkw 0x0382616562d38731 0x01c130b2b169c398 0xed7f61fde3f3c639 0x76bfb0fef1f9e31c

def z1205 : W := mkw 0xf007fcdbb8000000 0x7803fe6ddc000000 0x3ff7fffffc0007c0 0x1ffbfffffe0003e0

def z1206 : W := mkw 0xc807f40001aa9000 0x6403fa0000d54800 0xc1fff80003ffd801 0xe0fffc0001ffec00

def z1207 : W := mkw 0xcc25960005aef04a 0xe612cb0002d77825 0xffd9be023fffffff 0xffecdf011fffffff

def z1208 : W := mkw 0x0282616162c38631 0x014130b0b161c318 0xcc7e41e1c3c3c639 0x663f20f0e1e1e31c

def z1209 : W := mkw 0x0002606120c28211 0x0001303090614108 0x886661e1e1c0c218 0x443330f0f0e0610c

def z1210 : W := mkw 0xf007fcdbb8000000 0x7803fe6ddc000000 0x3c67fffffc000000 0x1e33fffffe000000

def z1211 : W := mkw 0xa80580b201680280 0x5402c05900b40140 0x886781fe01cc02c0 0x4433c0ff00e60160

def z1212 : W := mkw 0xab8581b6437907a0 0x55c2c0db21bc83d0 0xffffd9ffc3ff3fe1 0xffffecffe1ff9ff0

def z1213 : W := mkw 0x13c0090cd2110d24 0x09e0048669088692 0x7fb9591fd2333fe7 0xbfdcac8fe9199ff3

def z1214 : W := mkw 0x0282616162c38631 0x014130b0b161c318 0xec2e41e1e3c3c639 0x761720f0f1e1e31c

def z1215 : W := mkw 0xabc581b643790fa4 0x55e2c0db21bc87d2 0xffff81fe13ff3fe7 0xffffc0ff09ff9ff3

def z1216 : W := mkw 0xc807f40001280000 0x6403fa0000940000 0xc3fffe0003ff3801 0xe1ffff0001ff9c00

def z1217 : W := mkw 0x8c05820001aef000 0x4602c10000d77800 0xc3ffd80003fff801 0xe1ffec0001fffc00

def z1218 : W := mkw 0x03c2616562d38f35 0x01e130b2b169c79a 0xed7e61e1e3c3c73f 0x76bf30f0f1e1e39f

def z1219 : W := mkw 0x0282616162c38631 0x014130b0b161c318 0xfdfe61e1e3c3c739 0xfeff30f0f1e1e39c

def z1220 : W := mkw 0x042002000404604a 0x8210010002023025 0xeb40a6023c0ce7ff 0xf5a053011e0673ff

def z1221 : W := mkw 0xab0581b603780780 0x5582c0db01bc03c0 0xdcf7a1fe23fcc7d8 0xee7bd0ff11fe63ec

def z1222 : W := mkw 0x300268dbb8000000 0x1801346ddc000000 0x3ff6e7fffc000000 0x1ffb73fffe000000

def z1223 : W := mkw 0xf047fcdbb8000804 0x7823fe6ddc000402 0x3ff7fffffc003806 0x1ffbfffffe001c03

def z1224 : W := mkw 0xa20581b202400600 0x5102c0d901200300 0xdcf781fe03cc07c0 0xee7bc0ff01e603e0

def z1225 : W := mkw 0xcc07f60001aef000 0x6603fb0000d77800 0xfffffe0033ffff3f 0xffffff0019ffff9f

def z1226 : W := mkw 0x0c02620001aef000 0x0601310000d77800 0xc3ff780003fff801 0xe1ffbc0001fffc00

def z1227 : W := mkw 0xab0581b603780780 0x5582c0db01bc03c0 0xc86781fe03fc07c0 0xe433c0ff01fe03e0

def z1228 : W := mkw 0x4282756162c38631 0x21413ab0b161c318 0xef7e7fe1e3c3c639 0x77bf3ff0f1e1e31c

def z1229 : W := mkw 0x13e0096df6510f7f 0x89f004b6fb2887bf 0x3c0001fffc0007fe 0x1e0000fffe0003ff

def z1230 : W := mkw 0x0280012042410620 0x0140009021208310 0xed7e61e1e3c3c639 0x76bf30f0f1e1e31c

def z1231 : W := mkw 0xcc07f60001aef000 0x6603fb0000d77800 0xcffffe0003fffe01 0xe7ffff0001ffff00

def z1232 : W := mkw 0x0282616162c38631 0x014130b0b161c318 0xcc7e61e1e3c3c618 0x663f30f0f1e1e30c

def z1233 : W := mkw 0x0282616162c38631 0x014130b0b161c318 0xfffe61e1f3c3c639 0x7fff30f0f9e1e31c

def z1234 : W := mkw 0xcc07f60001aef000 0x6603fb0000d77800 0xc0fffe0003ffd800 0xe07fff0001ffec00

def z1235 : W := mkw 0xab0581b603780780 0x5582c0db01bc03c0 0xdef781fe13fc27c6 0xef7bc0ff09fe13e3

def z1236 : W := mkw 0x13c0092cd2510f24 0x09e0049669288792 0x7fb959fdd2333f27 0xbfdcacfee9199f93

def z1237 : W := mkw 0xcc07f60001aef000 0x6603fb0000d77800 0xd7fffe0003fffd01 0xebffff0001fffe80

def z1238 : W := mkw 0xab0581b603780780 0x5582c0db01bc03c0 0xdef787fe1ffc07c0 0xef7bc3ff0ffe03e0

def z1239 : W := mkw 0x13c0090cd2110d24 0x09e0048669088692 0xfff9ff1ffe33ff3f 0xfffcff8fff19ff9f

def z1240 : W := mkw 0x0c00020001aef000 0x0600010000d77800 0xc289180003fff801 0xe1448c0001fffc00

def z1241 : W := mkw 0x13c0090cd2110d24 0x09e0048669088692 0x37b9591dd2333827 0x1bdcac8ee9199c13

def z1242 : W := mkw 0x0282616162c38631 0x014130b0b161c318 0xedff61e1e3f3c639 0xf6ffb0f0f1f9e31c

def z1243 : W := mkw 0xcc07f60001aef000 0x6603fb0000d77800 0xc34efe0003fff801 0xe1a77f0001fffc00

def z1244 : W := mkw 0xcc07f60001aef000 0x6603fb0000d77800 0xc3fffe0003fffe39 0xe1ffff0001ffff1c

def z1245 : W := mkw 0x13c0092cd2510f24 0x09e0049669288792 0x77bf59fdd3f33d27 0xbbdfacfee9f99e93

def z1246 : W := mkw 0xcc07f64121aef000 0x6603fb2090d77800 0xc3ffffe1c3fff801 0xe1fffff0e1fffc00

def z1247 : W := mkw 0xec07f69201aef000 0x7603fb4900d77800 0xdffffffe03ffffc1 0xefffffff01ffffe0

def z1248 : W := mkw 0xcc05960001aef000 0x6602cb0000d77800 0xc009180003fff801 0xe0048c0001fffc00

def z1249 : W := mkw 0x042002000404604a 0x8210010002023025 0xf380a6023c0ce7ff 0xf9c053011e0673ff

def z1250 : W := mkw 0xec07f6d329aef000 0x7603fb6994d77800 0xc3fffee003fff801 0xe1ffff7001fffc00

def z1251 : W := mkw 0xcc07f60001aef000 0x6603fb0000d77800 0xc3bf580003fff801 0xe1dfac0001fffc00

def z1252 : W := mkw 0xc807f40001aa9000 0x6403fa0000d54800 0xed7f780023f3de39 0x76bfbc0011f9ef1c

def z1253 : W := mkw 0x042002000404604a 0x8210010002023025 0xfff6a7e23c0ce7ff 0xfffb53f11e0673ff

def z1254 : W := mkw 0x0382616562d387b1 0x01c130b2b169c3d8 0xed7e61e1e3c3c7f9 0x76bf30f0f1e1e3fc

def z1255 : W := mkw 0xc807f40001aa9000 0x6403fa0000d54800 0xc3fffe0003f3d801 0x61ffff0001f9ec00

def z1256 : W := mkw 0x13c0092cd2510f35 0x09e004966928879a 0x3400011dd000073e 0x1a00008ee800039f

def z1257 : W := mkw 0xcc05960001aef000 0x6602cb0000d77800 0xc3d9be0003fff801 0xe1ecdf0001fffc00

def z1258 : W := mkw 0xc807f40001aa9000 0x6403fa0000d54800 0x00afd80003ff1800 0x8057ec0001ff8c00

def z1259 : W := mkw 0xab0581b603780780 0x5582c0db01bc03c0 0xdcff81fe03ff3fc1 0xee7fc0ff01ff9fe0

def z1260 : W := mkw 0xc807f40001aa9000 0x6403fa0000d54800 0x402f580003f33801 0xa017ac0001f99c00

def z1261 : W := mkw 0x33c009fff2510fb5 0x19e004fff92887da 0x3c0001fff00007fe 0x1e0000fff80003ff

def z1262 : W := mkw 0xcc27f60005aef04a 0xe613fb0002d77825 0xf7fffe021ffffde7 0xfbffff010ffffef3

def z1263 : W := mkw 0x0282616162c38631 0x014130b0b161c318 0xc86e61e1e3c3c639 0x643730f0f1e1e31c

def z1264 : W := mkw 0xf007fcdbb8000000 0x7803fe6ddc000000 0x3ffffffffc033801 0x1ffffffffe019c00

def z1265 : W := mkw 0xab0581b603780780 0x5582c0db01bc03c0 0xddf7a1fe03fcc7c1 0xeefbd0ff01fe63e0

def z1266 : W := mkw 0xf007fcdbb8000000 0x7803fe6ddc000000 0x3f46fffffc000000 0x1fa37ffffe000000

def z1267 : W := mkw 0xab0581b603780780 0x5582c0db01bc03c0 0xdcf781fe03fcc7f9 0xee7bc0ff01fe63fc

def z1268 : W := mkw 0xc807f40001aa9000 0x6403fa0000d54800 0x43fffe0003f33801 0xa1ffff0001f99c00

def z1269 : W := mkw 0x33c009bed2510fa4 0x19e004df692887d2 0x000001fdc0000000 0x000000fee0000000

def z1270 : W := mkw 0x4802740001aa9000 0x24013a0000d54800 0x0008580003f31800 0x00042c0001f98c00

def z1271 : W := mkw 0x0c00020001aef000 0x0600010000d77800 0xc308580003fff801 0xe1842c0001fffc00

def z1272 : W := mkw 0xabc581b643790fa4 0x55e2c0db21bc87d2 0xdcff81fe03ff1fc0 0xee7fc0ff01ff8fe0

def z1273 : W := mkw 0x4c02760001aef000 0x26013b0000d77800 0xc37e7e0003fff801 0xe1bf3f0001fffc00

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z0,z7,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z8,z6]),(1,[z0,z9,z2,z4,z10,z6]),(0,[z11,z0,z1,z2,z4,z12,z6]),(0,[z0,z1,z2,z13,z4,z5,z14])],[(1,[z0,z1,z15,z4,z5,z6]),(0,[z16,z1,z2,z4,z17,z5,z6]),(0,[z18,z0,z1,z2,z4,z5,z6]),(0,[z19,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z20,z21,z4,z5,z6]),(0,[z22,z0,z1,z2,z4,z5,z23])],[(0,[z24,z1,z2,z4,z5,z6,z25]),(0,[z0,z1,z2,z4,z5,z26,z6]),(0,[z0,z1,z2,z27,z21,z5,z6]),(0,[z28,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z29]),(0,[z0,z1,z2,z4,z30,z5,z6])],[(0,[z0,z31,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z32,z5,z6]),(1,[z0,z1,z33,z4,z5,z6]),(0,[z0,z2,z4,z34,z5,z10,z6]),(0,[z0,z1,z2,z13,z21,z5,z6]),(0,[z0,z35,z1,z2,z36,z5,z6]),(0,[z0,z1,z2,z37,z4,z5,z6])],[(0,[z0,z1,z2,z38,z4,z5,z6]),(0,[z39,z0,z2,z4,z34,z5,z6]),(0,[z11,z0,z1,z2,z4,z5,z6])],[(0,[z40,z0,z1,z2,z41,z5,z6]),(0,[z42,z0,z1,z2,z4,z5,z6])],[(0,[z43,z1,z2,z44,z4,z5,z6]),(0,[z0,z1,z2,z4,z45,z5,z6])],[(0,[z46,z0,z1,z47,z4,z5,z6]),(0,[z0,z1,z2,z4,z48,z5,z6]),(0,[z0,z1,z2,z4,z49,z5,z6]),(0,[z50,z0,z1,z2,z4,z5,z6])]],
   [[(0,[z0,z51,z1,z2,z4,z5,z6]),(0,[z0,z52,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z53,z5,z6])],[(0,[z46,z1,z54,z2,z4,z5,z6]),(0,[z55,z40,z1,z2,z4,z5,z6]),(0,[z0,z1,z56,z2,z4,z5,z6]),(0,[z0,z1,z57,z2,z4,z5,z6]),(0,[z0,z35,z1,z2,z4,z5,z6]),(0,[z0,z1,z58,z2,z4,z5,z6])],[(0,[z0,z59,z1,z2,z4,z60,z6]),(0,[z0,z1,z2,z61,z4,z5,z6]),(0,[z0,z1,z2,z62,z4,z5,z6])],[(0,[z63,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z64,z4,z34,z6]),(0,[z0,z1,z2,z65,z4,z10,z6]),(0,[z66,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z13,z67,z4,z5])],[(0,[z0,z1,z2,z68,z4,z5,z6]),(0,[z0,z1,z2,z64,z4,z10,z6]),(0,[z39,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z34,z6,z69]),(0,[z0,z1,z70,z2,z4,z6,z71]),(0,[z0,z1,z2,z4,z72,z5,z6]),(0,[z0,z1,z2,z4,z5,z73,z6]),(0,[z0,z1,z2,z4,z5,z74,z6])],[(0,[z43,z0,z1,z2,z4,z5,z6]),(0,[z40,z0,z1,z2,z4,z34,z6]),(1,[z75,z1,z2,z4,z5,z6]),(0,[z0,z76,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z77,z6]),(0,[z0,z78,z1,z2,z4,z5,z6])],[(0,[z40,z0,z1,z2,z4,z10,z6]),(0,[z0,z1,z79,z2,z80,z5,z6]),(0,[z81,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z82,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z83]),(0,[z0,z1,z2,z27,z4,z84,z6])],[(0,[z0,z85,z1,z2,z4,z5,z6]),(0,[z55,z0,z1,z2,z4,z34,z6]),(0,[z0,z1,z2,z4,z5,z86,z6]),(0,[z87,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z88,z2,z4,z5,z6]),(0,[z0,z9,z2,z4,z5,z10,z6]),(0,[z0,z1,z89,z2,z4,z90,z6]),(0,[z0,z1,z2,z91,z4,z5,z6])]],
   [[(0,[z0,z1,z2,z21,z80,z5,z6]),(0,[z0,z1,z2,z4,z10,z14,z6]),(0,[z0,z1,z2,z4,z12,z5,z6])],[(0,[z0,z1,z2,z4,z92,z5,z6]),(0,[z43,z0,z1,z44,z4,z5,z6]),(0,[z0,z1,z2,z4,z93,z5,z6]),(0,[z0,z1,z2,z4,z41,z5,z6]),(0,[z0,z1,z2,z4,z34,z6,z94]),(0,[z0,z1,z21,z4,z95,z5,z6]),(0,[z0,z1,z2,z4,z96,z5,z6])],[(0,[z0,z1,z2,z4,z5,z97,z6]),(0,[z0,z1,z2,z4,z98,z5,z6]),(0,[z0,z1,z2,z4,z99,z5,z6]),(1,[z0,z1,z79,z2,z13,z5]),(0,[z0,z1,z100,z2,z4,z5,z6])],[(0,[z0,z1,z2,z101,z4,z5,z6]),(1,[z0,z1,z2,z102,z4,z6]),(0,[z0,z103,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z13,z5,z6,z94]),(0,[z0,z1,z2,z4,z104,z6,z71])],[(0,[z0,z1,z2,z4,z10,z105,z6]),(0,[z0,z1,z2,z4,z5,z6,z106]),(0,[z22,z107,z1,z2,z4,z5,z6])],[(0,[z0,z1,z108,z2,z4,z5,z6]),(1,[z0,z1,z109,z4,z5,z6]),(0,[z0,z1,z2,z41,z80,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z110]),(0,[z0,z1,z2,z4,z111,z5,z6]),(0,[z0,z1,z2,z112,z4,z34,z6]),(0,[z0,z1,z2,z4,z5,z6,z113]),(0,[z0,z1,z2,z4,z5,z114,z6]),(0,[z0,z1,z2,z4,z5,z115,z6])],[(1,[z0,z1,z2,z4,z5,z116]),(0,[z0,z1,z64,z4,z5,z6,z69]),(0,[z0,z1,z2,z4,z10,z90,z6]),(0,[z0,z1,z2,z4,z5,z117,z6]),(0,[z0,z1,z2,z112,z4,z10,z6]),(0,[z0,z1,z118,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z119]),(0,[z0,z1,z2,z120,z4,z5,z6])]],
   [[(0,[z0,z1,z2,z4,z5,z121,z6]),(0,[z0,z1,z2,z4,z122,z5,z6]),(0,[z123,z0,z1,z2,z4,z5,z6]),(0,[z124,z0,z1,z2,z4,z125,z6]),(0,[z124,z0,z1,z2,z4,z126,z6]),(0,[z0,z1,z2,z4,z5,z90,z14]),(0,[z0,z1,z2,z127,z4,z5,z6])],[(0,[z0,z1,z2,z109,z4,z5,z6]),(0,[z0,z1,z2,z4,z128,z5,z6]),(0,[z0,z129,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z130,z5,z6]),(0,[z0,z1,z131,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z34,z10,z6]),(0,[z132,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z133,z2,z4,z5,z6]),(0,[z0,z1,z2,z134,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z69,z71]),(0,[z0,z35,z1,z4,z5,z90,z6]),(0,[z0,z1,z2,z135,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z136,z6]),(0,[z11,z0,z1,z2,z137,z5,z6]),(0,[z0,z1,z2,z4,z5,z138,z6]),(0,[z139,z0,z1,z2,z4,z5,z6])],[(0,[z0,z140,z1,z2,z4,z5,z6])],[(0,[z0,z1,z141,z2,z4,z5,z6]),(0,[z0,z1,z142,z2,z4,z5,z6]),(0,[z0,z1,z143,z2,z4,z5,z6]),(1,[z19,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z5,z23]),(0,[z0,z1,z2,z4,z5,z144,z6]),(0,[z0,z1,z2,z4,z145,z5,z6])],[(0,[z146,z0,z1,z2,z4,z5,z6]),(0,[z16,z0,z1,z70,z2,z4,z6]),(0,[z0,z1,z2,z4,z10,z6,z71]),(0,[z0,z1,z2,z4,z34,z6,z147]),(0,[z148,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z149,z4,z34,z6]),(0,[z0,z1,z2,z4,z150,z5,z6])]],
   [[(0,[z0,z1,z2,z21,z151,z5,z6]),(0,[z0,z1,z2,z152,z4,z5,z6]),(0,[z0,z1,z2,z149,z4,z10,z6]),(0,[z0,z1,z2,z4,z5,z6,z153]),(0,[z22,z0,z1,z70,z4,z5,z6]),(0,[z154,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z34,z155,z6]),(0,[z156,z0,z1,z2,z157,z5,z6]),(0,[z156,z0,z1,z64,z4,z5,z6]),(0,[z0,z1,z2,z27,z4,z34,z6]),(0,[z0,z158,z1,z2,z4,z5,z6])],[(0,[z0,z159,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z155,z113]),(0,[z0,z1,z1,z2,z4,z10,z6]),(0,[z0,z1,z160,z2,z4,z5,z6]),(0,[z22,z0,z1,z2,z4,z161,z6]),(0,[z35,z162,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z163,z6])],[(0,[z59,z1,z54,z2,z4,z5,z6]),(0,[z0,z1,z2,z64,z4,z5,z6]),(0,[z0,z1,z2,z67,z4,z10,z6]),(0,[z11,z164,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z165,z4,z5,z6]),(0,[z0,z1,z166,z70,z2,z4,z6])],[(0,[z0,z1,z2,z167,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z25,z113]),(0,[z0,z1,z168,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z169,z6]),(0,[z0,z1,z170,z2,z4,z5,z6])],[(0,[z146,z0,z54,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z171,z6]),(0,[z172,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z173,z5,z6]),(1,[z0,z1,z2,z4,z32,z6]),(0,[z174,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z175,z4,z6]),(0,[z0,z1,z2,z112,z4,z5,z69])],[(0,[z0,z1,z2,z4,z5,z6,z176]),(0,[z156,z0,z1,z2,z130,z5,z6]),(0,[z156,z0,z1,z2,z4,z34,z6]),(0,[z0,z1,z2,z4,z177,z5,z6]),(0,[z0,z1,z178,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z104,z71])],[(0,[z0,z1,z54,z2,z4,z34,z6]),(0,[z0,z1,z2,z179,z4,z5,z6]),(0,[z156,z180,z1,z2,z4,z5,z6]),(0,[z156,z0,z1,z2,z4,z10,z6]),(0,[z181,z0,z1,z2,z4,z5,z6])]],
   [[(0,[z0,z1,z54,z2,z4,z10,z6]),(0,[z182,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z183,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z17,z5,z6]),(0,[z156,z0,z1,z184,z4,z5,z6]),(0,[z0,z1,z2,z185,z4,z5,z6]),(0,[z186,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z187,z2,z4,z5,z6]),(0,[z0,z1,z2,z188,z4,z34,z6]),(0,[z0,z1,z2,z112,z4,z5,z94]),(0,[z0,z1,z2,z189,z4,z5,z6])],[(0,[z190,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z191,z2,z4,z5,z6]),(0,[z0,z1,z2,z192,z4,z5,z6]),(0,[z24,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z193,z4,z10,z6]),(0,[z0,z1,z2,z4,z194,z5,z6]),(0,[z0,z1,z2,z4,z5,z195,z6]),(0,[z0,z1,z2,z4,z5,z6,z196])],[(1,[z0,z1,z2,z4,z60,z6]),(0,[z0,z1,z2,z4,z5,z6,z197]),(0,[z198,z0,z1,z2,z4,z5,z6]),(0,[z199,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z200]),(0,[z201,z0,z1,z2,z4,z10,z6]),(0,[z0,z1,z202,z2,z4,z5,z6]),(0,[z0,z1,z2,z112,z4,z5,z6])],[(0,[z0,z59,z1,z2,z4,z203,z6]),(1,[z204,z1,z2,z4,z205,z6]),(1,[z0,z1,z2,z4,z206,z6]),(0,[z0,z1,z207,z2,z4,z10,z6])],[(1,[z0,z1,z2,z4,z5,z208]),(0,[z0,z1,z2,z209,z4,z5,z6])]],
   [[(0,[z0,z1,z2,z210,z4,z5,z6]),(0,[z75,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z211,z4,z5,z6]),(0,[z0,z1,z2,z212,z4,z5,z6]),(0,[z0,z1,z2,z4,z104,z5,z71])],[(0,[z0,z1,z2,z4,z213,z5,z6]),(0,[z0,z1,z44,z64,z4,z5,z6]),(0,[z0,z1,z2,z4,z4,z5,z6]),(0,[z0,z1,z2,z4,z214,z5,z6]),(0,[z204,z1,z2,z4,z5,z205,z6]),(0,[z0,z1,z2,z215,z4,z5,z6]),(0,[z0,z1,z2,z4,z34,z5,z6]),(1,[z0,z1,z2,z4,z216,z6])],[(0,[z0,z1,z2,z4,z5,z6,z217]),(0,[z0,z218,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z219,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z220]),(0,[z0,z1,z2,z221,z4,z5,z6]),(0,[z0,z1,z222,z2,z4,z5,z6]),(0,[z223,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z224,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z225])],[(0,[z0,z1,z2,z4,z5,z6,z226]),(0,[z0,z1,z2,z227,z4,z95,z6]),(0,[z228,z0,z1,z2,z4,z5,z6]),(0,[z22,z0,z1,z2,z4,z5,z229])],[(0,[z0,z230,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z205,z6,z71]),(0,[z0,z1,z2,z4,z5,z6,z231])],[(0,[z0,z1,z2,z4,z5,z232,z6]),(0,[z0,z1,z2,z4,z5,z6,z208]),(0,[z0,z1,z233,z2,z4,z5,z6]),(0,[z0,z234,z1,z2,z112,z4,z5]),(0,[z0,z1,z2,z67,z4,z5,z94]),(0,[z0,z1,z2,z235,z4,z5,z6])]],
   [[(0,[z46,z0,z1,z2,z92,z5,z6]),(1,[z43,z1,z44,z4,z5,z6]),(0,[z22,z0,z1,z4,z5,z236,z6]),(0,[z0,z1,z2,z237,z4,z5,z6]),(0,[z0,z238,z1,z2,z4,z5,z6]),(1,[z0,z35,z1,z4,z5,z90])],[(0,[z0,z1,z1,z2,z4,z5,z6]),(0,[z239,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z240,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z34,z17,z6]),(0,[z39,z0,z2,z64,z4,z5,z6]),(0,[z0,z1,z2,z241,z4,z5,z6]),(0,[z0,z1,z2,z242,z4,z5,z6])],[(0,[z0,z1,z243,z2,z4,z5,z6]),(0,[z0,z1,z2,z27,z95,z5,z6]),(0,[z0,z1,z244,z4,z5,z6,z69]),(0,[z0,z1,z2,z245,z4,z5,z6]),(0,[z0,z1,z2,z67,z4,z5,z6]),(0,[z0,z246,z1,z2,z4,z5,z6])],[(0,[z55,z0,z1,z108,z4,z5,z6]),(0,[z0,z1,z247,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z248,z6]),(0,[z0,z1,z2,z4,z34,z205,z6]),(0,[z0,z249,z1,z2,z4,z5,z6]),(0,[z0,z250,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z13,z95,z5,z6])],[(1,[z0,z1,z2,z4,z251,z6])],[(1,[z0,z1,z2,z252,z5,z6]),(0,[z0,z1,z2,z4,z5,z253,z6]),(0,[z124,z254,z1,z2,z4,z5,z6]),(0,[z0,z1,z70,z2,z4,z34,z6])],[(0,[z0,z1,z108,z4,z95,z5,z6]),(0,[z0,z1,z70,z2,z4,z10,z6]),(0,[z0,z1,z244,z2,z4,z5,z6]),(0,[z0,z1,z166,z2,z4,z5,z71])],[(0,[z255,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z256,z6]),(0,[z0,z1,z166,z2,z4,z84,z6])]],
   [[(0,[z257,z1,z54,z2,z4,z5,z6]),(0,[z258,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z259,z4,z5,z6]),(1,[z0,z260,z2,z4,z5,z6]),(0,[z261,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z262,z5,z6])],[(1,[z0,z1,z2,z4,z263,z6]),(0,[z11,z0,z1,z2,z112,z4,z5]),(0,[z264,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z265,z4,z5,z6]),(0,[z22,z0,z1,z2,z27,z4,z6])],[(0,[z1,z54,z2,z4,z41,z5,z6]),(0,[z1,z108,z2,z44,z4,z5,z6]),(0,[z0,z1,z2,z193,z4,z5,z6])],[(0,[z0,z1,z64,z4,z95,z5,z6]),(0,[z0,z1,z266,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z10,z6,z69]),(0,[z0,z1,z2,z4,z5,z267,z6])],[(0,[z0,z268,z1,z2,z4,z5,z6]),(0,[z269,z0,z1,z2,z4,z5,z6]),(0,[z0,z270,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z271]),(0,[z0,z1,z2,z4,z104,z34,z6]),(0,[z0,z1,z2,z4,z5,z14,z69]),(0,[z0,z272,z1,z4,z95,z5,z6]),(0,[z0,z1,z2,z4,z5,z273,z6]),(0,[z0,z274,z1,z2,z4,z5,z6]),(0,[z0,z1,z275,z2,z4,z5,z6])],[(0,[z43,z0,z1,z2,z252,z5,z6]),(0,[z0,z1,z2,z4,z5,z276,z6]),(0,[z0,z1,z2,z277,z4,z5,z6]),(0,[z0,z1,z2,z4,z104,z10,z6]),(0,[z0,z234,z1,z2,z4,z5,z113]),(0,[z0,z1,z2,z278,z4,z84,z6])],[(0,[z1,z2,z44,z4,z5,z155,z6]),(0,[z0,z1,z2,z4,z5,z6,z279]),(0,[z0,z1,z2,z280,z4,z5,z6]),(1,[z0,z1,z281,z4,z5,z6]),(0,[z0,z1,z2,z282,z4,z5,z6])],[(0,[z46,z0,z1,z2,z4,z5,z283]),(0,[z284,z0,z1,z2,z4,z5,z6]),(0,[z285,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z286,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z111,z6]),(0,[z0,z1,z2,z287,z4,z5,z6])]],
   [[(0,[z0,z1,z2,z4,z10,z6,z94]),(0,[z0,z1,z288,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z289,z5,z6]),(1,[z87,z1,z2,z41,z5,z6]),(1,[z0,z1,z2,z4,z5,z290]),(1,[z156,z0,z64,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z291,z6]),(0,[z0,z1,z2,z4,z292,z5,z6]),(0,[z0,z1,z2,z4,z137,z5,z6]),(0,[z0,z1,z2,z4,z5,z14,z94]),(0,[z0,z1,z2,z293,z4,z5,z6])],[(0,[z0,z1,z2,z294,z4,z5,z6]),(0,[z0,z1,z295,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z296,z5,z6]),(0,[z0,z1,z2,z281,z4,z5,z6]),(0,[z0,z1,z2,z297,z4,z5,z6]),(0,[z22,z0,z1,z2,z4,z34,z6]),(0,[z0,z1,z2,z4,z5,z113,z94]),(0,[z0,z1,z2,z4,z298,z5,z6]),(0,[z0,z1,z2,z4,z299,z5,z6])],[(0,[z0,z1,z2,z4,z5,z300,z6]),(0,[z0,z1,z301,z2,z4,z5,z6]),(0,[z22,z0,z1,z2,z4,z10,z6]),(0,[z0,z1,z2,z302,z4,z5,z6]),(0,[z303,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z304,z6])],[(0,[z0,z1,z305,z2,z4,z5,z6]),(0,[z0,z1,z306,z2,z4,z5,z6]),(0,[z257,z0,z1,z2,z4,z5,z6]),(0,[z39,z0,z7,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z307]),(0,[z0,z308,z1,z2,z4,z5,z6])],[(0,[z124,z0,z309,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z310,z6])],[(0,[z0,z311,z1,z2,z4,z5,z6]),(0,[z16,z0,z1,z2,z4,z34,z6]),(1,[z0,z1,z2,z4,z312,z6]),(0,[z0,z1,z2,z4,z313,z5,z6]),(0,[z314,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z89,z2,z4,z6]),(0,[z0,z1,z315,z2,z4,z5,z6])],[(0,[z0,z1,z2,z316,z4,z5,z6]),(0,[z16,z0,z1,z2,z4,z10,z6]),(0,[z317,z0,z1,z2,z4,z5,z6]),(0,[z0,z309,z1,z2,z4,z34,z6]),(0,[z0,z1,z2,z4,z318,z5,z6]),(0,[z11,z0,z1,z2,z4,z5,z113]),(0,[z0,z1,z2,z319,z4,z5,z6])]],
   [[(1,[z0,z1,z2,z4,z203,z6]),(0,[z0,z1,z2,z4,z5,z320,z6]),(0,[z0,z1,z2,z151,z4,z34,z6]),(0,[z0,z1,z2,z4,z80,z34,z6]),(0,[z0,z309,z1,z2,z4,z10,z6]),(0,[z0,z234,z2,z4,z5,z14,z6])],[(0,[z0,z1,z2,z4,z5,z60,z6]),(0,[z0,z1,z2,z4,z5,z321,z6]),(0,[z0,z1,z2,z151,z4,z10,z6]),(0,[z0,z1,z2,z4,z5,z6,z290]),(0,[z0,z1,z2,z4,z5,z322,z6]),(0,[z0,z1,z2,z4,z80,z10,z6]),(0,[z0,z1,z2,z4,z10,z10,z6]),(0,[z0,z1,z2,z323,z4,z5,z6]),(0,[z0,z1,z2,z13,z4,z5,z71])],[(0,[z324,z0,z1,z2,z4,z5,z6]),(0,[z40,z87,z1,z2,z4,z5,z6]),(0,[z325,z0,z1,z2,z4,z5,z6]),(0,[z124,z0,z1,z2,z4,z5,z6]),(0,[z124,z0,z1,z2,z215,z5,z6]),(0,[z326,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z166,z2,z4,z34,z6]),(0,[z0,z327,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z5,z229]),(0,[z328,z0,z1,z2,z4,z5,z6])],[(0,[z55,z0,z1,z2,z4,z10,z6]),(0,[z0,z1,z2,z4,z5,z206,z6]),(0,[z0,z1,z166,z2,z4,z10,z6])],[(0,[z46,z0,z1,z15,z4,z5,z6]),(0,[z1,z2,z4,z5,z155,z6,z25]),(0,[z0,z1,z2,z4,z126,z5,z6]),(0,[z0,z1,z2,z4,z329,z5,z6])],[(0,[z0,z1,z2,z330,z4,z5,z6]),(0,[z204,z0,z1,z2,z4,z5,z290]),(0,[z0,z1,z2,z331,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z332]),(0,[z0,z1,z2,z333,z4,z34,z6]),(0,[z0,z1,z2,z4,z5,z6,z334]),(0,[z0,z1,z70,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z335,z5,z6])],[(0,[z336,z0,z1,z2,z4,z5,z6]),(0,[z87,z0,z1,z2,z151,z5,z6]),(0,[z337,z0,z1,z2,z4,z10,z6]),(0,[z0,z1,z2,z4,z5,z216,z6])],[(0,[z338,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z339,z2,z4,z5,z6]),(0,[z0,z1,z2,z340,z4,z5,z6])]],
   [[(0,[z46,z0,z1,z2,z4,z5,z6]),(0,[z341,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z10,z155,z6]),(0,[z0,z1,z2,z4,z5,z342,z6]),(0,[z0,z1,z2,z4,z5,z343,z6]),(0,[z0,z1,z2,z4,z5,z6,z344])],[(1,[z0,z1,z2,z316,z5,z6]),(0,[z0,z1,z2,z4,z5,z345,z6]),(0,[z0,z1,z2,z4,z5,z346,z6]),(0,[z347,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z236,z6])],[(0,[z0,z348,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z155,z14]),(0,[z0,z1,z2,z112,z4,z104,z5])],[(0,[z146,z1,z2,z44,z4,z5,z6]),(0,[z349,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z350,z5,z6])],[(0,[z40,z1,z54,z2,z4,z5,z6]),(0,[z351,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z352,z5,z6]),(0,[z22,z0,z1,z2,z4,z6,z71]),(0,[z0,z1,z353,z2,z4,z5,z6])],[(0,[z354,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z355,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z356,z5,z6]),(0,[z0,z357,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z358,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z359])],[(0,[z46,z0,z54,z2,z4,z5,z6]),(0,[z55,z1,z54,z2,z4,z5,z6]),(0,[z0,z272,z1,z2,z21,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z360]),(1,[z0,z1,z2,z4,z5,z361])],[(0,[z362,z0,z1,z2,z4,z5,z6]),(0,[z363,z0,z1,z2,z4,z5,z6]),(0,[z0,z309,z2,z215,z4,z5,z6]),(0,[z0,z1,z2,z4,z34,z6,z113]),(0,[z0,z1,z2,z4,z34,z342,z6]),(0,[z364,z0,z1,z2,z4,z5,z6])]],
   [[(0,[z1,z2,z44,z4,z5,z205,z6]),(0,[z0,z1,z2,z4,z5,z6,z365]),(0,[z156,z366,z1,z2,z4,z5,z6]),(0,[z0,z9,z1,z2,z4,z34,z6]),(1,[z0,z2,z4,z34,z10,z6])],[(0,[z0,z1,z2,z4,z312,z5,z6]),(0,[z0,z1,z2,z4,z5,z367,z6]),(0,[z39,z0,z9,z2,z4,z5,z6]),(0,[z0,z9,z1,z2,z4,z10,z6]),(0,[z0,z1,z2,z368,z4,z34,z6]),(1,[z0,z1,z2,z120,z5,z6]),(0,[z0,z1,z2,z4,z5,z251,z6]),(0,[z0,z1,z2,z4,z90,z73,z6]),(0,[z0,z1,z89,z2,z4,z5,z6])],[(0,[z0,z369,z1,z2,z4,z5,z6]),(0,[z87,z0,z1,z109,z4,z5,z6])],[(0,[z0,z7,z1,z2,z4,z32,z6]),(0,[z370,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z371,z4,z5,z6]),(0,[z0,z372,z1,z2,z4,z5,z6]),(0,[z0,z1,z373,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z256,z6])],[(0,[z0,z1,z2,z4,z5,z6,z25]),(0,[z0,z1,z2,z27,z4,z10,z6]),(0,[z0,z1,z2,z65,z4,z5,z6]),(0,[z0,z1,z2,z13,z4,z34,z6]),(0,[z0,z1,z2,z374,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z263,z6]),(0,[z16,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z375,z6]),(0,[z124,z0,z1,z2,z4,z5,z376]),(0,[z0,z1,z2,z13,z4,z10,z6]),(0,[z0,z1,z2,z4,z5,z6,z361]),(0,[z0,z1,z79,z2,z13,z4,z5])],[(0,[z24,z1,z2,z44,z4,z5,z6]),(0,[z24,z257,z1,z2,z4,z5,z6]),(1,[z24,z1,z2,z4,z5,z25]),(1,[z0,z7,z184,z4,z5,z6]),(0,[z124,z0,z1,z2,z4,z5,z367]),(1,[z0,z1,z2,z4,z34,z6])]],
   [[(0,[z0,z1,z2,z4,z377,z5,z6]),(0,[z40,z0,z1,z2,z4,z5,z6]),(0,[z0,z378,z1,z2,z4,z5,z6]),(1,[z257,z1,z2,z4,z5,z155]),(0,[z0,z1,z184,z2,z4,z34,z6]),(0,[z0,z1,z2,z4,z80,z5,z6]),(0,[z0,z1,z2,z67,z4,z115,z6]),(0,[z0,z1,z2,z379,z4,z5,z6])],[(0,[z46,z0,z1,z2,z4,z5,z116]),(0,[z380,z0,z1,z2,z4,z5,z6]),(1,[z198,z0,z1,z2,z4,z6]),(0,[z0,z1,z2,z151,z95,z5,z6]),(0,[z381,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z184,z2,z4,z10,z6]),(0,[z0,z234,z1,z2,z4,z216,z6]),(0,[z382,z272,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z383,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z90,z71]),(0,[z0,z384,z1,z2,z4,z5,z6])],[(0,[z55,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z385,z5,z6]),(0,[z0,z164,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z386,z6])],[(0,[z156,z0,z2,z64,z4,z5,z6]),(0,[z0,z1,z2,z387,z4,z5,z6])],[(0,[z388,z0,z1,z2,z4,z5,z6])],[(0,[z0,z366,z1,z2,z4,z5,z6]),(0,[z389,z0,z1,z2,z4,z5,z6]),(0,[z390,z0,z1,z2,z4,z10,z6]),(0,[z0,z1,z2,z4,z391,z34,z6])],[(0,[z55,z0,z1,z44,z4,z5,z6]),(0,[z16,z0,z1,z2,z4,z17,z6]),(0,[z0,z1,z2,z4,z5,z6,z392]),(0,[z0,z393,z1,z2,z4,z5,z6]),(0,[z394,z0,z1,z2,z4,z5,z6]),(0,[z395,z0,z1,z2,z4,z5,z6])],[(0,[z46,z0,z1,z2,z4,z396,z6]),(0,[z0,z1,z2,z44,z4,z34,z6]),(0,[z0,z397,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z398]),(0,[z0,z1,z2,z4,z399,z5,z6])]],
   [[(0,[z0,z1,z2,z44,z4,z10,z6]),(0,[z400,z0,z1,z2,z4,z5,z6]),(0,[z16,z0,z1,z2,z4,z205,z6]),(0,[z0,z1,z401,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z402,z6])],[(1,[z0,z1,z2,z403,z5,z6]),(0,[z0,z1,z2,z404,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z405,z6]),(0,[z0,z1,z2,z406,z4,z5,z6]),(0,[z0,z1,z2,z4,z10,z205,z6]),(0,[z0,z1,z166,z2,z4,z17,z6]),(0,[z0,z1,z2,z4,z5,z407,z6]),(1,[z0,z1,z2,z4,z34,z147])],[(0,[z198,z0,z1,z2,z44,z4,z6])],[(0,[z146,z59,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z408,z4,z5,z6]),(1,[z0,z272,z1,z95,z5,z6]),(0,[z0,z1,z20,z2,z21,z5,z6]),(1,[z107,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z47,z4,z5,z6]),(0,[z0,z1,z409,z2,z4,z5,z6]),(0,[z410,z0,z1,z2,z4,z5,z6]),(0,[z0,z2,z64,z4,z5,z10,z6])],[(0,[z411,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z21,z41,z5,z6]),(0,[z0,z1,z412,z2,z4,z5,z6]),(0,[z0,z1,z2,z149,z278,z4,z6])],[(0,[z0,z1,z2,z413,z4,z5,z6]),(0,[z0,z1,z2,z4,z414,z5,z6]),(0,[z0,z1,z2,z4,z84,z6,z71]),(0,[z415,z0,z1,z2,z4,z5,z6])]],
   [[(0,[z0,z1,z2,z416,z4,z5,z6])],[(0,[z0,z417,z1,z2,z4,z5,z6]),(0,[z0,z254,z1,z2,z4,z5,z6]),(1,[z124,z0,z2,z80,z5,z6]),(0,[z0,z1,z2,z4,z5,z418,z6]),(0,[z0,z35,z1,z244,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z84,z6])],[(0,[z0,z1,z108,z184,z4,z5,z6]),(0,[z0,z1,z2,z419,z4,z5,z6]),(0,[z0,z1,z33,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z420,z5,z6]),(0,[z0,z1,z2,z4,z421,z34,z6]),(0,[z0,z1,z2,z4,z5,z6,z422]),(0,[z0,z1,z2,z4,z423,z5,z6]),(0,[z0,z1,z2,z149,z4,z5,z6])],[(0,[z424,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z278,z84,z6]),(0,[z425,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z426]),(0,[z0,z1,z2,z4,z427,z5,z6]),(0,[z0,z1,z2,z80,z5,z6,z94]),(0,[z0,z1,z79,z2,z4,z34,z6]),(0,[z0,z1,z2,z27,z4,z5,z6])],[(0,[z0,z1,z428,z2,z4,z5,z6]),(0,[z0,z7,z1,z2,z4,z256,z6]),(0,[z0,z234,z1,z2,z4,z5,z14]),(0,[z22,z0,z1,z166,z2,z4,z6]),(0,[z0,z1,z2,z13,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z429]),(0,[z0,z1,z2,z4,z5,z430,z6]),(0,[z156,z0,z7,z2,z4,z5,z6]),(0,[z0,z184,z2,z64,z4,z5,z6]),(0,[z0,z1,z2,z21,z4,z34,z6]),(0,[z11,z0,z1,z2,z4,z251,z6]),(0,[z0,z1,z2,z4,z431,z5,z6])],[(0,[z432,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z21,z4,z10,z6]),(0,[z0,z1,z2,z4,z5,z6,z433]),(0,[z0,z1,z2,z149,z5,z84,z6]),(0,[z0,z1,z2,z4,z5,z6,z434]),(0,[z0,z435,z1,z2,z4,z5,z6])]],
   [[(0,[z1,z2,z44,z4,z41,z5,z6]),(0,[z0,z1,z2,z436,z4,z5,z6]),(1,[z0,z1,z2,z4,z5,z345]),(0,[z0,z272,z1,z20,z4,z5,z6]),(0,[z0,z1,z166,z2,z4,z104,z6])],[(0,[z156,z0,z1,z2,z4,z5,z6]),(0,[z437,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z438,z5,z6]),(0,[z124,z0,z2,z4,z80,z5,z6]),(0,[z439,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z440,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z441])],[(0,[z0,z1,z54,z2,z4,z5,z6]),(0,[z442,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z443,z2,z4,z5,z6]),(0,[z0,z1,z444,z2,z4,z5,z6])],[(0,[z24,z0,z1,z2,z4,z5,z25]),(0,[z0,z1,z2,z445,z4,z5,z6])],[(1,[z0,z1,z2,z4,z375,z6]),(0,[z0,z1,z2,z215,z5,z6,z94])],[(0,[z0,z1,z2,z4,z396,z5,z6]),(0,[z40,z1,z2,z151,z4,z5,z6]),(0,[z0,z1,z2,z188,z4,z5,z6]),(0,[z0,z446,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z447,z4,z5,z6]),(0,[z0,z1,z448,z2,z4,z5,z6])],[(0,[z449,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z450,z4,z5,z6]),(0,[z0,z1,z451,z2,z4,z5,z6]),(0,[z0,z1,z2,z452,z4,z5,z6]),(0,[z22,z0,z1,z2,z335,z5,z6]),(0,[z453,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z454,z6]),(0,[z204,z0,z1,z70,z2,z4,z6]),(0,[z0,z1,z2,z455,z4,z5,z6]),(0,[z0,z1,z456,z2,z4,z10,z6]),(0,[z201,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z457,z4,z5,z6]),(0,[z11,z0,z1,z2,z4,z5,z14]),(0,[z0,z1,z2,z4,z5,z6,z458]),(0,[z0,z1,z2,z4,z5,z459,z6])]],
   [[(0,[z460,z0,z1,z2,z4,z5,z6]),(0,[z461,z0,z1,z2,z4,z5,z6]),(0,[z0,z59,z1,z2,z4,z34,z6]),(0,[z0,z1,z462,z2,z4,z5,z6]),(0,[z0,z1,z207,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z463,z5,z6]),(0,[z0,z1,z2,z219,z278,z4,z5]),(0,[z464,z0,z1,z2,z4,z5,z6])],[(0,[z0,z59,z1,z2,z4,z10,z6]),(0,[z124,z0,z1,z2,z80,z5,z6]),(0,[z0,z309,z1,z2,z4,z49,z6]),(0,[z0,z1,z4,z161,z5,z236,z6]),(0,[z0,z1,z4,z5,z90,z6,z69]),(0,[z0,z1,z2,z4,z5,z465,z6])],[(1,[z0,z1,z2,z466,z5,z6]),(0,[z0,z1,z2,z467,z4,z5,z6]),(0,[z0,z7,z184,z2,z4,z5,z6]),(0,[z0,z309,z1,z2,z4,z468,z6]),(0,[z0,z1,z2,z469,z4,z5,z6]),(0,[z0,z1,z470,z2,z4,z5,z6]),(0,[z0,z471,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z472,z5,z6]),(0,[z0,z1,z2,z473,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z474]),(0,[z0,z1,z475,z2,z4,z5,z6])],[(0,[z0,z476,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z477,z4,z5,z6]),(0,[z0,z478,z1,z2,z4,z5,z6])],[(0,[z0,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z20,z64,z4,z5,z6]),(0,[z479,z0,z1,z2,z4,z34,z6])],[(1,[z0,z1,z355,z4,z5,z6]),(0,[z0,z480,z1,z2,z4,z5,z6]),(0,[z479,z0,z1,z2,z4,z10,z6]),(0,[z0,z1,z2,z4,z5,z14,z6])]],
   [[(1,[z0,z1,z323,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z481]),(0,[z0,z1,z166,z2,z112,z4,z6])],[(0,[z55,z16,z1,z2,z4,z5,z6])],[(0,[z43,z0,z1,z2,z466,z5,z6]),(0,[z87,z1,z2,z4,z41,z5,z6]),(0,[z0,z1,z2,z482,z4,z34,z6]),(0,[z0,z1,z2,z4,z5,z69,z113]),(0,[z0,z1,z2,z4,z5,z483,z6]),(0,[z0,z1,z2,z278,z4,z5,z361])],[(0,[z0,z1,z2,z4,z203,z5,z6]),(0,[z0,z1,z2,z4,z5,z105,z6]),(0,[z124,z0,z1,z33,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z484]),(0,[z0,z1,z2,z4,z5,z485,z6]),(0,[z0,z1,z20,z2,z4,z34,z6]),(0,[z0,z1,z2,z4,z486,z5,z6])],[(0,[z0,z1,z2,z4,z5,z487,z6]),(0,[z0,z1,z2,z488,z4,z5,z6]),(0,[z0,z1,z20,z2,z4,z10,z6]),(0,[z0,z1,z2,z4,z95,z34,z6]),(0,[z489,z0,z1,z2,z4,z34,z6]),(0,[z0,z1,z2,z4,z5,z6,z490]),(0,[z491,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z70,z2,z278,z4,z6]),(0,[z0,z1,z492,z2,z4,z5,z6])],[(0,[z0,z493,z1,z2,z4,z5,z6]),(0,[z24,z0,z1,z2,z4,z5,z155]),(0,[z257,z1,z2,z4,z5,z155,z6]),(0,[z180,z0,z1,z2,z4,z5,z6]),(1,[z0,z2,z64,z4,z10,z6]),(0,[z0,z1,z2,z4,z5,z90,z6]),(0,[z0,z1,z2,z4,z5,z6,z494])],[(0,[z1,z54,z2,z4,z5,z6,z25]),(0,[z495,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z20,z184,z4,z5,z6]),(0,[z0,z1,z2,z4,z10,z6,z113]),(0,[z0,z1,z2,z4,z34,z14,z6]),(0,[z0,z272,z1,z2,z95,z5,z6])],[(0,[z496,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z112,z4,z5,z155]),(0,[z0,z7,z2,z4,z5,z10,z6]),(0,[z11,z0,z234,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z94,z71])]],
   [[(0,[z0,z1,z2,z497,z4,z5,z6]),(0,[z498,z0,z1,z2,z4,z5,z6]),(0,[z499,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z500,z4,z5,z6]),(0,[z0,z35,z1,z2,z4,z5,z90]),(1,[z0,z1,z2,z67,z5,z94])],[(0,[z87,z0,z1,z355,z4,z5,z6]),(0,[z0,z1,z2,z501,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z502,z6]),(0,[z0,z1,z2,z4,z10,z121,z6]),(0,[z0,z1,z70,z4,z161,z5,z6]),(0,[z503,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z504,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z505,z6]),(0,[z0,z1,z2,z374,z67,z4,z6])],[(0,[z506,z0,z1,z2,z4,z5,z6])],[(0,[z507,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z508,z6]),(0,[z0,z1,z2,z278,z4,z34,z6]),(0,[z154,z35,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z41,z95,z5,z6]),(0,[z0,z1,z2,z509,z4,z10,z6]),(0,[z0,z1,z2,z278,z4,z10,z6]),(0,[z0,z1,z510,z2,z4,z34,z6]),(0,[z0,z1,z2,z4,z5,z511,z6])],[(1,[z0,z1,z2,z4,z5,z502]),(0,[z0,z1,z512,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z229]),(1,[z0,z1,z2,z27,z149,z6])],[(0,[z0,z1,z2,z4,z5,z6,z71])],[(0,[z513,z0,z1,z2,z4,z5,z6]),(0,[z514,z0,z1,z2,z4,z5,z6]),(0,[z515,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z104,z5,z6])]],
   [[(0,[z0,z7,z1,z64,z4,z5,z6]),(0,[z516,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z517,z6]),(1,[z0,z1,z2,z219,z4,z5])],[(1,[z0,z1,z2,z4,z49,z6]),(0,[z0,z1,z2,z4,z10,z6,z153]),(0,[z0,z1,z457,z2,z4,z5,z6]),(0,[z0,z1,z2,z518,z4,z5,z6]),(0,[z0,z1,z519,z2,z4,z5,z6]),(0,[z0,z1,z2,z520,z4,z5,z6])],[(1,[z0,z1,z2,z92,z5,z6]),(0,[z146,z1,z2,z4,z41,z5,z6]),(0,[z16,z1,z2,z44,z4,z5,z6]),(0,[z22,z16,z0,z1,z2,z4,z6]),(1,[z0,z1,z2,z4,z468,z6]),(1,[z521,z1,z2,z4,z5,z6]),(0,[z0,z522,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z34,z236,z6]),(0,[z11,z0,z1,z2,z120,z5,z6]),(0,[z0,z1,z523,z2,z4,z5,z6]),(0,[z0,z1,z2,z27,z278,z5,z6])],[(0,[z40,z1,z2,z44,z4,z5,z6]),(0,[z0,z1,z524,z2,z4,z5,z6]),(0,[z257,z0,z1,z2,z4,z5,z25])],[(0,[z0,z1,z2,z4,z5,z525,z6]),(1,[z0,z1,z2,z157,z5,z6]),(0,[z0,z526,z1,z2,z4,z5,z6]),(0,[z22,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z527,z6]),(0,[z0,z1,z2,z528,z4,z5,z6])],[(0,[z0,z1,z529,z2,z4,z5,z6]),(0,[z530,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z95,z5,z84,z6])],[]],
   [[(1,[z40,z1,z2,z151,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z531]),(0,[z0,z7,z1,z184,z4,z5,z6]),(1,[z0,z7,z2,z4,z10,z6]),(0,[z0,z1,z2,z175,z4,z5,z6]),(0,[z0,z1,z2,z532,z4,z5,z6]),(0,[z0,z1,z2,z533,z4,z5,z6])],[(0,[z146,z0,z59,z2,z4,z5,z6]),(0,[z204,z0,z1,z2,z4,z5,z502]),(0,[z0,z35,z1,z64,z4,z5,z6]),(0,[z22,z0,z1,z2,z518,z5,z6]),(0,[z0,z534,z1,z2,z4,z5,z6])],[(1,[z55,z1,z108,z4,z5,z6]),(0,[z24,z0,z1,z2,z4,z375,z6]),(1,[z0,z1,z2,z130,z5,z6]),(0,[z156,z0,z1,z2,z4,z206,z6]),(0,[z0,z309,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z535,z4,z5,z6]),(0,[z0,z309,z1,z2,z215,z5,z6]),(1,[z154,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z536,z4,z5,z6])],[(0,[z0,z1,z2,z151,z4,z5,z6]),(0,[z0,z1,z2,z151,z215,z5,z6]),(0,[z0,z1,z2,z4,z5,z155,z71]),(1,[z180,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z10,z6]),(0,[z0,z162,z1,z2,z4,z5,z6])],[(0,[z87,z0,z1,z2,z41,z5,z6]),(0,[z537,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z215,z95,z5,z6]),(0,[z0,z1,z2,z4,z117,z10,z6]),(0,[z0,z1,z20,z2,z95,z5,z6])],[(0,[z0,z1,z2,z4,z5,z25,z71]),(0,[z0,z1,z2,z538,z4,z5,z6]),(0,[z22,z75,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z539,z4,z5,z6]),(0,[z0,z1,z166,z2,z4,z5,z6])],[(1,[z16,z1,z2,z4,z17,z6]),(0,[z124,z19,z1,z2,z4,z5,z6]),(0,[z540,z0,z1,z2,z4,z5,z6]),(0,[z0,z35,z1,z2,z4,z34,z6]),(0,[z0,z1,z2,z4,z34,z161,z6]),(1,[z0,z1,z2,z4,z53,z6]),(0,[z0,z1,z2,z541,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z542,z6]),(0,[z40,z0,z1,z2,z151,z5,z6]),(0,[z0,z1,z2,z4,z34,z6,z25]),(0,[z0,z1,z2,z4,z543,z5,z6])]],
   [[(0,[z544,z0,z1,z2,z4,z5,z6]),(0,[z337,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z545]),(0,[z0,z1,z2,z333,z4,z5,z6]),(0,[z0,z1,z2,z4,z161,z10,z6]),(0,[z0,z1,z2,z546,z4,z5,z6])],[(0,[z0,z1,z2,z547,z4,z5,z6]),(0,[z0,z35,z1,z184,z4,z5,z6]),(0,[z0,z1,z2,z4,z548,z5,z6]),(1,[z0,z1,z2,z374,z4,z6])],[(0,[z43,z0,z1,z2,z4,z34,z6]),(0,[z0,z549,z1,z2,z4,z5,z6]),(0,[z22,z0,z327,z2,z4,z5,z6]),(0,[z0,z1,z2,z550,z4,z5,z6])],[(1,[z146,z59,z2,z4,z5,z6]),(0,[z257,z146,z1,z2,z4,z5,z6]),(0,[z43,z0,z1,z2,z4,z10,z6]),(0,[z55,z1,z2,z4,z5,z155,z6]),(0,[z0,z1,z2,z4,z5,z551,z6]),(0,[z0,z1,z2,z4,z5,z6,z552]),(0,[z0,z1,z2,z4,z5,z6,z553]),(0,[z0,z1,z2,z554,z4,z5,z6])],[(1,[z0,z1,z47,z4,z5,z6]),(0,[z87,z0,z1,z2,z4,z34,z6]),(0,[z0,z555,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z556,z4,z5,z6])],[(0,[z0,z557,z1,z2,z4,z5,z6]),(0,[z0,z1,z108,z64,z4,z5,z6]),(0,[z87,z0,z1,z2,z4,z10,z6]),(0,[z0,z1,z2,z558,z4,z5,z6]),(0,[z0,z1,z559,z2,z4,z5,z6]),(0,[z0,z1,z2,z157,z4,z5,z6]),(0,[z521,z0,z1,z2,z4,z5,z6])],[(0,[z560,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z102,z4,z5,z6]),(0,[z0,z1,z2,z4,z41,z34,z6]),(0,[z204,z0,z1,z2,z4,z34,z6]),(0,[z0,z1,z2,z4,z5,z6,z561]),(0,[z257,z0,z1,z2,z4,z5,z155]),(0,[z0,z1,z562,z2,z4,z5,z6]),(0,[z0,z1,z2,z27,z149,z5,z6])],[(0,[z0,z1,z2,z4,z41,z10,z6]),(0,[z204,z0,z1,z2,z4,z10,z6]),(0,[z0,z1,z166,z2,z4,z205,z6]),(0,[z24,z0,z1,z2,z4,z312,z6]),(0,[z0,z1,z563,z2,z4,z5,z6]),(0,[z0,z1,z260,z2,z4,z5,z6])]],
   [[(0,[z0,z35,z1,z2,z403,z5,z6]),(0,[z0,z1,z564,z2,z4,z5,z6]),(0,[z565,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z566,z2,z4,z5,z6])],[(0,[z0,z1,z2,z567,z4,z5,z6]),(0,[z0,z1,z2,z568,z4,z5,z6])],[(0,[z0,z1,z2,z102,z44,z4,z6]),(0,[z0,z1,z108,z2,z4,z34,z6]),(0,[z0,z1,z2,z4,z5,z569,z6])],[(0,[z0,z1,z108,z2,z4,z10,z6]),(0,[z570,z0,z1,z2,z4,z5,z6]),(0,[z0,z9,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z368,z4,z34,z5]),(0,[z0,z1,z571,z2,z4,z5,z6]),(0,[z572,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z368,z4,z5,z6]),(0,[z0,z1,z573,z2,z4,z5,z6]),(1,[z22,z0,z1,z4,z236,z6]),(0,[z0,z1,z2,z112,z4,z5,z90]),(0,[z0,z1,z2,z4,z5,z6,z574]),(0,[z575,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z112,z13,z4,z5])],[(0,[z0,z1,z15,z2,z4,z5,z6]),(0,[z0,z2,z4,z5,z14,z6,z113])],[(1,[z0,z1,z2,z4,z12,z6]),(0,[z0,z1,z2,z576,z4,z5,z6]),(0,[z0,z35,z1,z2,z4,z5,z69])],[(0,[z46,z146,z1,z2,z4,z5,z6]),(0,[z0,z1,z20,z108,z4,z5,z6]),(0,[z1,z2,z151,z4,z41,z5,z6]),(0,[z0,z1,z184,z4,z5,z6,z69]),(0,[z0,z1,z2,z577,z4,z5,z6])]],
   [[(0,[z0,z1,z2,z578,z4,z5,z6]),(0,[z0,z1,z79,z2,z4,z10,z6]),(0,[z0,z272,z1,z2,z4,z34,z6]),(0,[z0,z1,z2,z67,z21,z5,z6])],[(0,[z0,z579,z1,z2,z4,z5,z6]),(0,[z0,z272,z1,z2,z4,z10,z6]),(0,[z580,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z581,z6])],[(1,[z0,z1,z2,z4,z5,z6]),(0,[z582,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z69]),(0,[z0,z583,z1,z2,z4,z5,z6])],[(0,[z0,z1,z184,z2,z4,z5,z6]),(0,[z156,z0,z1,z2,z4,z111,z6]),(0,[z0,z1,z2,z4,z584,z5,z6]),(0,[z0,z1,z2,z4,z34,z418,z6]),(0,[z0,z1,z2,z4,z34,z84,z6]),(0,[z0,z1,z2,z4,z5,z23,z6]),(0,[z0,z1,z2,z4,z5,z6,z585]),(0,[z0,z1,z586,z2,z4,z5,z6])],[(0,[z146,z0,z1,z2,z4,z34,z6]),(0,[z0,z587,z1,z2,z4,z5,z6]),(0,[z148,z0,z1,z2,z4,z34,z6]),(0,[z0,z1,z2,z588,z4,z5,z6])],[(0,[z146,z0,z1,z2,z4,z10,z6]),(0,[z589,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z590,z2,z4,z5,z6])],[(0,[z0,z1,z2,z2,z4,z5,z6]),(0,[z591,z0,z1,z2,z4,z5,z6]),(0,[z592,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z593,z4,z5,z6]),(0,[z0,z1,z2,z4,z594,z5,z6]),(0,[z0,z1,z2,z4,z5,z595,z6]),(1,[z0,z1,z2,z518,z5,z6])],[(0,[z0,z1,z184,z44,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z596,z6]),(0,[z597,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z468,z6]),(0,[z390,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z161,z5,z6]),(0,[z0,z1,z70,z2,z4,z236,z6]),(0,[z0,z1,z2,z4,z5,z6,z94])]],
   [[(0,[z0,z1,z2,z112,z4,z5,z25]),(0,[z0,z1,z2,z4,z391,z5,z6]),(0,[z0,z1,z2,z13,z4,z5,z113]),(0,[z0,z1,z2,z4,z5,z598,z6]),(0,[z0,z1,z2,z599,z4,z5,z6])],[(0,[z0,z1,z600,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z34,z194,z6]),(0,[z11,z0,z1,z457,z4,z5,z6]),(0,[z0,z1,z2,z601,z4,z5,z6])],[(0,[z0,z1,z2,z44,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z6]),(0,[z0,z1,z2,z602,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z603])],[(0,[z0,z1,z2,z4,z604,z5,z6]),(0,[z605,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z606,z6]),(1,[z0,z1,z2,z4,z125,z6]),(1,[z0,z1,z2,z4,z126,z6]),(0,[z0,z1,z2,z4,z177,z34,z6])],[(0,[z0,z1,z607,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z608,z6])],[(0,[z55,z1,z2,z4,z5,z205,z6]),(0,[z0,z1,z609,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z5,z147]),(0,[z0,z1,z244,z2,z4,z5,z90])],[(0,[z0,z1,z2,z215,z41,z5,z6]),(0,[z204,z0,z1,z2,z4,z5,z6]),(0,[z0,z234,z1,z2,z4,z5,z71]),(0,[z0,z1,z2,z27,z149,z4,z6]),(0,[z0,z610,z1,z2,z4,z5,z6])],[(0,[z40,z146,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z17,z10,z6]),(0,[z0,z1,z611,z2,z4,z5,z6]),(0,[z0,z1,z612,z2,z4,z5,z6]),(1,[z0,z327,z2,z4,z5,z6])]],
   [[(0,[z24,z0,z1,z2,z4,z34,z6]),(0,[z0,z1,z2,z4,z5,z10,z6]),(0,[z0,z1,z2,z613,z4,z5,z6]),(0,[z0,z1,z2,z67,z5,z6,z94])],[(0,[z614,z0,z1,z2,z4,z5,z6]),(0,[z55,z146,z1,z2,z4,z5,z6]),(0,[z24,z0,z1,z2,z4,z10,z6]),(0,[z0,z1,z2,z615,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z116,z6]),(0,[z11,z0,z1,z323,z4,z5,z6]),(0,[z0,z1,z616,z2,z4,z5,z6]),(0,[z0,z1,z70,z2,z4,z161,z6]),(0,[z0,z1,z2,z36,z4,z5,z6])],[(0,[z0,z1,z617,z2,z4,z5,z6]),(0,[z0,z618,z1,z2,z4,z5,z6])],[(0,[z0,z619,z1,z2,z4,z5,z6]),(0,[z22,z0,z1,z2,z4,z236,z6]),(0,[z0,z1,z79,z2,z4,z5,z94])],[(0,[z0,z1,z2,z4,z421,z5,z6]),(0,[z620,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z147]),(0,[z0,z621,z1,z2,z4,z5,z6])],[(0,[z204,z0,z1,z2,z4,z17,z6]),(0,[z124,z0,z1,z281,z4,z5,z6]),(1,[z0,z1,z2,z4,z5,z376]),(0,[z0,z1,z2,z215,z4,z34,z6]),(0,[z0,z1,z2,z210,z4,z10,z6]),(1,[z39,z0,z2,z4,z34,z6]),(0,[z0,z1,z2,z4,z34,z34,z6]),(1,[z0,z1,z2,z368,z4,z5])],[(0,[z46,z0,z1,z2,z4,z263,z6]),(0,[z0,z1,z622,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z155,z6]),(0,[z0,z1,z2,z4,z623,z5,z6]),(1,[z0,z1,z2,z4,z5,z367]),(0,[z0,z1,z2,z215,z4,z10,z6]),(0,[z0,z1,z79,z2,z215,z5,z6]),(1,[z0,z1,z2,z368,z4,z34]),(0,[z0,z1,z79,z2,z4,z5,z6])]],
   [[(0,[z0,z1,z2,z624,z4,z5,z6]),(0,[z204,z0,z1,z2,z4,z205,z6]),(0,[z0,z1,z625,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z95,z10,z6]),(0,[z626,z0,z1,z2,z4,z5,z6]),(0,[z11,z0,z1,z2,z4,z5,z71]),(1,[z0,z234,z2,z4,z5,z14]),(0,[z0,z272,z1,z2,z4,z5,z6]),(0,[z627,z0,z1,z2,z4,z5,z6])],[(1,[z0,z1,z2,z4,z396,z6]),(0,[z0,z1,z2,z4,z5,z6,z628]),(0,[z0,z1,z2,z21,z215,z5,z6]),(0,[z0,z1,z629,z2,z4,z5,z6]),(0,[z0,z1,z2,z21,z4,z5,z6])],[(0,[z0,z1,z630,z2,z4,z5,z6]),(0,[z0,z1,z2,z631,z4,z5,z6]),(0,[z0,z1,z2,z4,z10,z346,z6]),(0,[z0,z1,z2,z4,z10,z236,z6]),(1,[z0,z1,z2,z137,z5,z6]),(0,[z0,z632,z1,z2,z4,z5,z6])],[],[(0,[z55,z43,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z633,z5,z6]),(0,[z382,z0,z1,z2,z4,z5,z6])],[(0,[z22,z204,z0,z1,z2,z4,z6])],[(0,[z0,z1,z634,z2,z4,z5,z6]),(0,[z43,z0,z1,z108,z4,z5,z6]),(0,[z0,z1,z2,z635,z4,z5,z6]),(0,[z636,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z637]),(0,[z0,z1,z2,z4,z5,z6,z376]),(0,[z0,z1,z1,z2,z4,z34,z6]),(0,[z0,z1,z2,z21,z5,z84,z6])],[(0,[z638,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z34,z90,z6]),(0,[z0,z1,z2,z67,z4,z34,z6]),(0,[z0,z1,z2,z4,z5,z639,z6]),(1,[z162,z1,z2,z4,z5,z6]),(1,[z0,z1,z166,z2,z112,z4])]],
   [[(0,[z0,z1,z2,z4,z17,z6,z71]),(0,[z11,z0,z2,z4,z5,z6,z113]),(0,[z0,z1,z2,z4,z5,z90,z113]),(0,[z22,z0,z260,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z403,z5,z6])],[(0,[z0,z1,z640,z2,z4,z5,z6]),(0,[z0,z309,z1,z2,z80,z5,z6]),(0,[z0,z1,z2,z4,z5,z641,z6]),(0,[z0,z1,z456,z2,z4,z5,z6]),(1,[z164,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z642,z4,z5,z6]),(0,[z643,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z644,z6])],[(0,[z46,z0,z59,z2,z4,z5,z6]),(0,[z645,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z151,z80,z5,z6]),(0,[z0,z1,z2,z646,z4,z5,z6]),(0,[z0,z1,z2,z647,z4,z5,z6]),(0,[z0,z234,z1,z2,z4,z34,z6]),(0,[z272,z446,z1,z2,z4,z5,z6])],[(0,[z0,z59,z1,z2,z4,z5,z6]),(0,[z648,z0,z1,z2,z4,z5,z6]),(0,[z0,z234,z1,z2,z4,z10,z6]),(0,[z0,z1,z244,z2,z4,z34,z6])],[(1,[z366,z1,z2,z4,z5,z6]),(0,[z0,z1,z244,z2,z4,z10,z6]),(0,[z11,z521,z1,z2,z4,z5,z6]),(0,[z22,z0,z1,z2,z278,z4,z6]),(0,[z0,z1,z2,z112,z4,z6,z71])],[(0,[z0,z1,z2,z4,z5,z649,z6]),(0,[z0,z1,z2,z4,z650,z5,z6]),(0,[z0,z1,z2,z4,z5,z651,z6]),(0,[z0,z1,z2,z652,z4,z5,z6])],[(0,[z0,z1,z2,z4,z10,z6,z25]),(0,[z0,z234,z1,z2,z4,z53,z6]),(0,[z0,z1,z2,z175,z4,z95,z6]),(1,[z0,z1,z2,z335,z5,z6])],[(0,[z0,z653,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z5,z6]),(0,[z0,z1,z2,z4,z5,z14,z25]),(0,[z0,z1,z2,z80,z95,z5,z6]),(0,[z0,z1,z2,z4,z654,z10,z6]),(0,[z0,z655,z1,z2,z4,z5,z6]),(1,[z0,z1,z244,z4,z5,z69]),(1,[z0,z1,z2,z4,z73,z6])]],
   [[(0,[z0,z1,z2,z656,z4,z5,z6]),(0,[z0,z7,z1,z2,z4,z34,z6]),(0,[z0,z1,z2,z4,z34,z6,z71]),(0,[z0,z1,z657,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z658,z6])],[(0,[z479,z0,z1,z2,z4,z5,z6]),(0,[z659,z0,z1,z2,z4,z5,z6]),(0,[z0,z7,z1,z2,z4,z10,z6])],[(1,[z46,z54,z2,z4,z5,z6]),(0,[z660,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z661,z2,z4,z5,z6]),(0,[z0,z1,z166,z2,z112,z4,z5])],[(0,[z662,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z663,z5,z6])],[(0,[z0,z1,z184,z4,z95,z5,z6]),(0,[z11,z0,z1,z2,z4,z34,z6]),(0,[z0,z1,z2,z664,z4,z5,z6]),(0,[z0,z1,z2,z4,z665,z5,z6])],[(0,[z55,z1,z2,z4,z41,z5,z6]),(0,[z1,z2,z4,z17,z5,z205,z6]),(0,[z0,z1,z2,z4,z5,z666,z6]),(0,[z0,z1,z2,z482,z4,z5,z6]),(0,[z11,z0,z1,z2,z4,z10,z6]),(0,[z0,z1,z288,z2,z4,z34,z6])],[(0,[z156,z0,z1,z2,z4,z5,z208]),(0,[z0,z1,z20,z2,z4,z5,z6]),(0,[z0,z1,z2,z149,z4,z6,z71]),(0,[z0,z1,z2,z667,z4,z5,z6])],[(0,[z46,z0,z1,z2,z316,z5,z6]),(0,[z668,z0,z1,z2,z4,z5,z6]),(0,[z489,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z95,z5,z6])]],
   [[(1,[z254,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z125,z6]),(1,[z0,z1,z20,z21,z5,z6]),(1,[z0,z1,z2,z4,z115,z6])],[(0,[z55,z1,z108,z2,z4,z5,z6]),(0,[z669,z0,z1,z2,z4,z5,z6]),(0,[z670,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z205,z6]),(0,[z257,z0,z1,z2,z4,z34,z6]),(0,[z0,z2,z215,z4,z80,z5,z6]),(0,[z0,z1,z70,z2,z27,z4,z6])],[(0,[z0,z1,z20,z44,z4,z5,z6]),(0,[z0,z1,z2,z4,z671,z5,z6]),(0,[z257,z0,z1,z2,z4,z10,z6]),(0,[z0,z35,z1,z2,z4,z10,z6]),(0,[z0,z672,z1,z2,z4,z5,z6])],[(0,[z0,z1,z244,z2,z4,z5,z69]),(0,[z0,z1,z79,z2,z67,z5,z6])],[(1,[z0,z1,z2,z4,z5,z283]),(0,[z673,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z674,z4,z5,z6]),(0,[z39,z0,z1,z2,z4,z34,z6]),(0,[z0,z675,z1,z2,z4,z5,z6]),(0,[z0,z1,z79,z2,z13,z5,z6]),(0,[z0,z1,z2,z676,z4,z5,z6])],[(0,[z204,z16,z1,z2,z4,z5,z6]),(0,[z677,z0,z1,z2,z4,z5,z6]),(0,[z39,z0,z1,z2,z4,z10,z6])],[(0,[z146,z1,z2,z4,z5,z6,z25]),(0,[z678,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z679,z4,z5,z6]),(0,[z0,z1,z2,z680,z4,z5,z6]),(0,[z0,z1,z2,z509,z4,z5,z6]),(0,[z0,z1,z2,z278,z4,z5,z6])],[(0,[z681,z0,z1,z2,z4,z5,z6]),(0,[z0,z682,z1,z2,z4,z5,z6]),(0,[z124,z0,z1,z2,z4,z34,z6]),(0,[z0,z1,z2,z683,z4,z5,z6]),(0,[z0,z1,z510,z2,z4,z5,z6]),(0,[z0,z1,z2,z227,z4,z5,z6])]],
   [[(0,[z0,z1,z2,z684,z4,z5,z6]),(0,[z0,z1,z2,z685,z4,z5,z6]),(0,[z0,z1,z2,z686,z4,z5,z6]),(0,[z0,z1,z687,z2,z4,z5,z6]),(0,[z124,z0,z1,z2,z4,z10,z6]),(0,[z0,z1,z2,z4,z5,z688,z6]),(0,[z689,z0,z1,z2,z4,z5,z6]),(1,[z382,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z67,z95,z5,z6]),(1,[z0,z1,z2,z227,z4,z6])],[(0,[z0,z1,z2,z4,z466,z5,z6]),(0,[z0,z690,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z34,z5,z147]),(0,[z0,z1,z2,z4,z691,z5,z6])],[(0,[z0,z692,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z10,z84,z6]),(0,[z0,z234,z1,z2,z4,z5,z6]),(1,[z11,z0,z2,z4,z5,z113])],[(0,[z1,z54,z2,z44,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z693]),(0,[z0,z694,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z278,z5,z84,z6])],[(0,[z0,z1,z2,z4,z5,z6,z283]),(0,[z695,z0,z1,z2,z4,z5,z6]),(0,[z696,z0,z1,z2,z4,z5,z6]),(0,[z156,z0,z1,z2,z4,z5,z345]),(1,[z446,z1,z2,z4,z5,z6]),(0,[z0,z1,z697,z2,z4,z5,z6])],[(0,[z46,z0,z1,z2,z4,z34,z6]),(0,[z0,z1,z44,z4,z95,z5,z6]),(0,[z0,z1,z2,z698,z4,z5,z6]),(0,[z0,z1,z2,z699,z4,z5,z6]),(0,[z341,z0,z1,z2,z4,z34,z6]),(0,[z0,z107,z1,z2,z4,z5,z6]),(1,[z0,z1,z70,z4,z161,z6])],[(0,[z46,z0,z1,z2,z4,z10,z6]),(0,[z0,z1,z2,z252,z4,z5,z6]),(0,[z0,z1,z2,z4,z700,z5,z6]),(0,[z0,z1,z2,z4,z701,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z702]),(0,[z0,z1,z2,z4,z641,z10,z6]),(0,[z0,z1,z2,z4,z654,z5,z6]),(0,[z0,z703,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z704,z5,z6]),(0,[z24,z55,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z705,z6]),(1,[z0,z1,z2,z36,z5,z6]),(0,[z0,z1,z166,z2,z149,z4,z6]),(0,[z0,z1,z2,z4,z706,z5,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z4,z396,z6]),(0,[z46,z54,z2,z4,z5,z283]),(0,[z521,z1,z2,z4,z251,z6]),(0,[z0,z707,z2,z4,z5,z6]),(0,[z162,z1,z2,z36,z5,z6])],[(0,[z146,z59,z2,z4,z60,z6]),(1,[z0,z1,z4,z708,z6])],[(0,[z709,z1,z2,z4,z5,z6]),(0,[z0,z64,z4,z641,z10,z6]),(0,[z0,z1,z79,z2,z13,z10]),(0,[z164,z1,z2,z112,z4,z5]),(0,[z0,z1,z2,z4,z710,z6])],[(0,[z0,z1,z2,z711,z5,z6]),(1,[z1,z44,z466,z5,z6]),(0,[z0,z1,z712,z4,z5,z6]),(0,[z0,z158,z2,z4,z10,z6]),(0,[z22,z0,z1,z4,z418,z6]),(0,[z0,z1,z2,z149,z4,z147]),(0,[z0,z1,z2,z4,z713,z6])],[(0,[z0,z1,z2,z4,z5,z714]),(0,[z43,z1,z44,z4,z34,z6]),(0,[z55,z1,z247,z4,z5,z6]),(0,[z0,z64,z4,z10,z6,z69]),(0,[z0,z1,z2,z4,z421,z147]),(0,[z0,z260,z2,z4,z177,z6]),(0,[z154,z35,z1,z4,z5,z90])],[(0,[z614,z1,z44,z4,z5,z6]),(0,[z43,z1,z44,z4,z10,z6]),(0,[z0,z1,z2,z715,z5,z6]),(0,[z0,z35,z1,z4,z10,z90]),(0,[z1,z2,z4,z10,z6,z716]),(0,[z0,z1,z2,z717,z5,z6]),(0,[z0,z2,z4,z5,z6,z718]),(0,[z0,z1,z2,z4,z719,z6])],[(0,[z0,z1,z2,z4,z5,z720]),(0,[z162,z1,z2,z4,z5,z6]),(0,[z0,z2,z546,z4,z10,z6]),(0,[z0,z1,z2,z4,z654,z153]),(0,[z0,z1,z70,z4,z465,z6]),(0,[z0,z1,z89,z2,z4,z71]),(0,[z0,z1,z166,z2,z112,z4])],[(0,[z55,z1,z612,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z721]),(0,[z722,z1,z2,z4,z10,z6]),(0,[z0,z1,z2,z4,z5,z723]),(0,[z0,z234,z2,z4,z5,z718]),(0,[z0,z1,z2,z4,z5,z724]),(0,[z0,z1,z2,z13,z577,z5])]],
   [[(0,[z0,z1,z2,z4,z5,z725]),(0,[z0,z1,z2,z5,z726,z6]),(0,[z0,z1,z2,z4,z5,z727]),(0,[z0,z2,z4,z728,z10,z6]),(0,[z22,z0,z1,z2,z4,z361])],[(0,[z0,z1,z2,z4,z5,z729]),(0,[z0,z1,z2,z252,z34,z6]),(0,[z0,z1,z2,z4,z32,z6]),(0,[z0,z1,z2,z4,z5,z730]),(0,[z0,z1,z2,z4,z34,z345]),(0,[z0,z1,z2,z4,z731,z6]),(0,[z0,z1,z2,z137,z5,z113]),(0,[z0,z1,z2,z175,z4,z6])],[(1,[z732,z2,z4,z5,z6]),(0,[z0,z1,z2,z252,z10,z6]),(0,[z0,z1,z2,z4,z733,z6]),(0,[z0,z1,z2,z734,z4,z10]),(0,[z0,z1,z166,z2,z368,z4]),(0,[z0,z1,z457,z120,z5,z6])],[(0,[z0,z7,z184,z4,z256,z6]),(0,[z254,z1,z2,z80,z5,z6]),(0,[z19,z1,z2,z4,z125,z6]),(0,[z19,z1,z2,z4,z126,z6]),(0,[z0,z1,z735,z4,z5,z6])],[(0,[z415,z0,z2,z80,z5,z6]),(0,[z0,z1,z2,z4,z736,z6]),(0,[z737,z1,z2,z4,z5,z6])],[(0,[z46,z54,z15,z4,z5,z6]),(0,[z0,z1,z738,z4,z5,z6]),(0,[z0,z1,z2,z4,z739,z6]),(0,[z24,z1,z2,z4,z375,z25]),(0,[z0,z740,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z741]),(0,[z0,z1,z2,z4,z742,z6]),(0,[z0,z357,z2,z4,z5,z14]),(0,[z0,z1,z2,z157,z111,z6]),(0,[z0,z1,z2,z743,z4,z6]),(0,[z0,z1,z2,z4,z34,z744]),(0,[z0,z1,z2,z4,z73,z6]),(0,[z0,z1,z244,z4,z5,z69]),(0,[z0,z1,z2,z4,z745,z6])],[(0,[z0,z549,z1,z95,z5,z6]),(0,[z107,z1,z2,z4,z6,z71])]],
   [[(0,[z0,z1,z2,z4,z60,z6]),(0,[z0,z1,z2,z746,z5,z6]),(0,[z156,z0,z64,z157,z5,z6]),(0,[z164,z1,z2,z4,z5,z113]),(0,[z0,z1,z2,z4,z747,z6]),(0,[z0,z1,z2,z4,z748,z6]),(0,[z749,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z750]),(0,[z1,z2,z109,z41,z5,z6]),(0,[z1,z2,z4,z5,z751,z6]),(0,[z0,z1,z2,z4,z752,z6]),(0,[z0,z2,z4,z706,z34,z6]),(0,[z753,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z278,z335,z6])],[(0,[z204,z1,z2,z4,z205,z6]),(0,[z0,z1,z2,z4,z754,z6]),(0,[z0,z1,z2,z4,z206,z6]),(0,[z0,z1,z281,z4,z34,z6]),(0,[z755,z1,z2,z4,z5,z6]),(0,[z0,z1,z207,z4,z641,z6]),(0,[z11,z521,z2,z4,z5,z113]),(0,[z0,z1,z2,z4,z756,z6])],[(0,[z0,z1,z2,z4,z5,z757]),(0,[z0,z1,z2,z466,z34,z6]),(0,[z0,z1,z2,z130,z111,z6]),(0,[z0,z1,z281,z4,z10,z6]),(0,[z0,z1,z323,z120,z5,z6]),(0,[z0,z1,z2,z4,z758,z6]),(0,[z0,z1,z2,z4,z23,z71]),(0,[z0,z1,z2,z27,z759,z6])],[(0,[z204,z0,z260,z2,z4,z6]),(0,[z180,z1,z2,z4,z111,z6]),(0,[z0,z1,z2,z760,z4,z6])],[(0,[z0,z1,z2,z761,z4,z203]),(0,[z762,z0,z1,z2,z4,z6]),(0,[z87,z1,z2,z41,z34,z6]),(0,[z0,z1,z2,z4,z34,z290]),(0,[z156,z0,z64,z130,z5,z6]),(0,[z156,z0,z64,z4,z34,z6]),(0,[z254,z1,z33,z4,z5,z6]),(0,[z763,z1,z2,z4,z5,z6]),(0,[z0,z583,z2,z4,z34,z6]),(0,[z75,z1,z2,z335,z5,z6]),(0,[z0,z1,z2,z764,z5,z6])],[(0,[z0,z1,z765,z4,z5,z6]),(0,[z0,z1,z2,z4,z766,z6]),(0,[z87,z1,z2,z41,z10,z6]),(0,[z0,z1,z2,z4,z10,z290]),(0,[z156,z0,z64,z4,z10,z6]),(0,[z0,z327,z2,z4,z32,z6]),(0,[z0,z35,z1,z36,z5,z90]),(0,[z0,z1,z767,z2,z4,z6])],[(0,[z0,z1,z47,z4,z263,z6]),(0,[z0,z1,z15,z4,z5,z283]),(0,[z0,z1,z2,z4,z5,z768]),(0,[z0,z1,z2,z4,z115,z6])]],
   [[(0,[z0,z1,z2,z4,z5,z769]),(0,[z0,z1,z355,z4,z34,z6]),(0,[z0,z2,z4,z770,z5,z6]),(0,[z0,z384,z2,z4,z10,z6])],[(0,[z55,z1,z306,z4,z5,z6]),(0,[z0,z1,z2,z771,z4,z6]),(0,[z0,z1,z323,z4,z34,z6])],[(0,[z0,z1,z2,z4,z772,z6]),(0,[z0,z1,z773,z4,z5,z6]),(0,[z0,z1,z2,z4,z774,z6]),(0,[z204,z1,z2,z4,z751,z6]),(0,[z24,z1,z2,z4,z312,z25])],[(0,[z0,z1,z775,z4,z5,z6]),(0,[z0,z1,z2,z4,z776,z6]),(0,[z777,z1,z2,z4,z5,z6]),(0,[z0,z590,z2,z4,z10,z6]),(0,[z341,z1,z2,z4,z194,z6]),(0,[z0,z1,z2,z27,z61,z6]),(0,[z778,z1,z2,z4,z5,z6])],[(0,[z0,z1,z779,z4,z5,z6]),(0,[z489,z0,z1,z4,z418,z6]),(0,[z0,z35,z1,z4,z5,z90])],[(0,[z0,z1,z2,z4,z5,z780]),(0,[z781,z1,z2,z4,z5,z6]),(0,[z1,z2,z782,z4,z5,z6]),(0,[z11,z0,z2,z4,z12,z113]),(0,[z783,z1,z2,z4,z5,z6]),(0,[z0,z1,z166,z2,z4,z23]),(0,[z0,z1,z2,z219,z278,z84])],[(0,[z0,z1,z784,z4,z5,z6]),(0,[z0,z1,z2,z785,z4,z5]),(0,[z0,z1,z2,z786,z5,z6]),(0,[z722,z1,z2,z4,z5,z6]),(0,[z0,z1,z787,z2,z4,z6]),(0,[z0,z1,z2,z4,z34,z229])],[(0,[z0,z1,z2,z4,z788,z6]),(0,[z1,z44,z4,z466,z5,z6]),(0,[z16,z1,z2,z613,z4,z6]),(0,[z0,z249,z2,z4,z10,z6]),(0,[z0,z1,z2,z4,z10,z229]),(0,[z0,z1,z2,z227,z4,z6])]],
   [[(0,[z0,z1,z2,z4,z789,z6]),(0,[z0,z1,z2,z770,z5,z6]),(0,[z0,z1,z2,z4,z251,z6]),(0,[z415,z0,z2,z4,z5,z113])],[(0,[z0,z1,z2,z252,z5,z6]),(0,[z11,z0,z2,z4,z5,z113])],[(0,[z0,z1,z2,z4,z790,z6]),(0,[z46,z54,z2,z4,z5,z116]),(0,[z0,z1,z2,z4,z791,z6]),(0,[z0,z1,z792,z4,z5,z6]),(0,[z364,z0,z2,z4,z5,z113])],[(0,[z0,z378,z2,z4,z10,z6]),(0,[z1,z401,z2,z4,z5,z25]),(0,[z0,z1,z2,z4,z10,z793])],[(0,[z1,z732,z2,z4,z5,z6]),(0,[z0,z1,z2,z794,z5,z6]),(0,[z0,z1,z2,z4,z795,z6]),(0,[z0,z796,z64,z4,z5,z6]),(0,[z0,z260,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z797])],[(0,[z0,z1,z2,z316,z34,z6]),(0,[z0,z1,z798,z4,z5,z6]),(0,[z799,z1,z2,z4,z5,z6]),(0,[z521,z1,z2,z120,z5,z6]),(0,[z800,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z316,z10,z6]),(0,[z0,z1,z2,z4,z34,z502]),(0,[z390,z1,z2,z4,z205,z6]),(0,[z0,z1,z2,z4,z801,z6]),(0,[z0,z1,z2,z335,z5,z23])],[(0,[z0,z1,z2,z4,z802,z6]),(0,[z0,z1,z2,z803,z4,z6]),(0,[z804,z0,z1,z2,z4,z6]),(0,[z156,z366,z64,z4,z5,z6]),(0,[z0,z1,z2,z805,z4,z6]),(0,[z0,z1,z2,z4,z34,z806]),(0,[z0,z1,z70,z2,z4,z147]),(0,[z0,z807,z2,z4,z5,z6]),(0,[z0,z1,z2,z808,z5,z6])]],
   [[(0,[z0,z1,z809,z4,z5,z6]),(0,[z810,z1,z2,z4,z5,z6]),(0,[z0,z260,z2,z518,z5,z6])],[(0,[z0,z1,z2,z811,z5,z6]),(0,[z0,z1,z2,z4,z812,z6]),(0,[z572,z0,z2,z4,z34,z6])],[(0,[z1,z2,z4,z5,z6,z813]),(0,[z0,z1,z33,z4,z5,z6]),(0,[z814,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z34,z361]),(0,[z815,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z816,z6]),(0,[z324,z1,z2,z4,z5,z25]),(0,[z0,z1,z2,z817,z5,z6]),(0,[z0,z1,z2,z4,z818,z6]),(0,[z0,z1,z2,z4,z111,z6]),(0,[z337,z1,z2,z4,z117,z6]),(0,[z0,z1,z2,z819,z4,z6]),(0,[z0,z1,z2,z4,z10,z361]),(0,[z521,z1,z2,z4,z34,z6]),(0,[z0,z1,z629,z4,z5,z69]),(0,[z0,z234,z2,z4,z216,z14]),(0,[z820,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z821,z6]),(0,[z0,z1,z2,z4,z822,z6])],[(0,[z24,z1,z2,z4,z5,z279]),(0,[z0,z7,z64,z4,z10,z6]),(0,[z0,z1,z2,z823,z4,z5]),(0,[z0,z2,z4,z34,z728,z6]),(0,[z75,z260,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z824,z6]),(0,[z0,z1,z2,z4,z5,z825]),(0,[z826,z1,z2,z4,z5,z6]),(1,[z0,z2,z4,z728,z6]),(0,[z0,z1,z2,z120,z34,z6]),(0,[z0,z1,z4,z5,z827,z69]),(0,[z0,z1,z2,z4,z5,z827])],[(0,[z0,z1,z64,z130,z5,z6]),(0,[z0,z1,z2,z157,z34,z6]),(0,[z0,z7,z796,z4,z5,z6]),(0,[z0,z1,z2,z4,z828,z6]),(0,[z0,z1,z2,z120,z10,z6]),(0,[z0,z1,z2,z4,z5,z829]),(0,[z0,z1,z2,z4,z830,z6])],[(0,[z0,z1,z2,z4,z831,z6]),(0,[z0,z1,z2,z4,z832,z6])]],
   [[(0,[z146,z1,z2,z92,z5,z6]),(0,[z43,z1,z833,z4,z5,z6]),(0,[z0,z1,z2,z834,z5,z6]),(0,[z0,z143,z2,z4,z34,z6]),(0,[z0,z1,z2,z835,z4,z6]),(0,[z0,z308,z2,z215,z5,z6]),(0,[z0,z1,z288,z4,z161,z6])],[(0,[z0,z1,z836,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z837]),(0,[z1,z240,z2,z41,z5,z6]),(0,[z0,z1,z2,z838,z4,z5]),(0,[z0,z1,z2,z4,z5,z839])],[(0,[z0,z1,z2,z4,z396,z283]),(0,[z840,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z841]),(0,[z0,z1,z79,z2,z842,z5])],[(0,[z55,z1,z108,z4,z34,z6]),(0,[z24,z1,z2,z4,z34,z25]),(0,[z0,z1,z2,z130,z34,z6]),(0,[z0,z1,z281,z4,z125,z6]),(0,[z0,z1,z281,z4,z126,z6]),(0,[z0,z1,z33,z4,z125,z6]),(0,[z0,z1,z33,z4,z126,z6]),(0,[z0,z1,z275,z21,z5,z6]),(0,[z0,z1,z166,z2,z760,z4])],[(0,[z0,z1,z843,z4,z5,z6]),(0,[z24,z1,z2,z4,z10,z25]),(0,[z257,z1,z2,z4,z34,z155]),(0,[z366,z1,z2,z4,z206,z6]),(0,[z180,z1,z2,z4,z34,z6]),(0,[z0,z7,z184,z4,z10,z6]),(0,[z0,z1,z20,z497,z5,z6]),(0,[z0,z1,z2,z80,z5,z376]),(0,[z0,z1,z2,z4,z728,z6]),(0,[z0,z2,z368,z4,z34,z10]),(0,[z22,z0,z1,z2,z4,z147]),(0,[z0,z1,z2,z368,z4,z71]),(0,[z0,z1,z2,z844,z4,z6]),(0,[z0,z1,z2,z845,z4,z6]),(0,[z0,z1,z2,z846,z4,z6])],[(0,[z0,z1,z2,z5,z847,z6]),(0,[z0,z1,z2,z4,z17,z290]),(0,[z0,z2,z4,z34,z430,z6]),(0,[z257,z1,z2,z4,z10,z155]),(0,[z366,z1,z2,z4,z5,z208]),(0,[z0,z1,z2,z175,z335,z6])],[(0,[z0,z1,z184,z130,z5,z6]),(0,[z0,z848,z2,z4,z5,z6])],[(0,[z0,z640,z2,z4,z10,z6]),(0,[z0,z1,z2,z4,z205,z290]),(0,[z0,z1,z2,z849,z5,z6]),(0,[z660,z0,z2,z80,z5,z6]),(0,[z0,z1,z2,z4,z850,z6]),(0,[z0,z1,z2,z193,z65,z6]),(0,[z0,z1,z2,z4,z851,z6])]],
   [[(0,[z0,z2,z4,z173,z10,z6]),(0,[z0,z1,z64,z403,z5,z6]),(0,[z0,z1,z2,z4,z852,z6]),(0,[z0,z1,z2,z137,z251,z6])],[(0,[z0,z1,z15,z4,z5,z116]),(0,[z0,z1,z2,z853,z5,z6]),(0,[z0,z178,z2,z4,z10,z6]),(0,[z0,z272,z1,z227,z95,z6]),(0,[z0,z1,z79,z2,z13,z5])],[(0,[z0,z1,z2,z4,z5,z854]),(0,[z0,z1,z2,z102,z4,z6]),(0,[z0,z1,z855,z4,z5,z6]),(0,[z0,z2,z652,z4,z34,z6]),(0,[z0,z1,z79,z2,z13,z34])],[(0,[z257,z1,z2,z4,z5,z97]),(0,[z1,z833,z2,z4,z5,z6]),(0,[z0,z1,z856,z4,z5,z6]),(0,[z272,z446,z1,z95,z5,z6])],[(0,[z0,z1,z109,z4,z5,z6]),(1,[z1,z2,z4,z5,z813]),(0,[z0,z1,z2,z857,z4,z6]),(0,[z858,z1,z2,z4,z5,z6]),(0,[z859,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z860]),(0,[z0,z1,z2,z4,z5,z861]),(0,[z0,z1,z2,z4,z862,z6])],[(0,[z0,z1,z2,z403,z34,z6])],[(0,[z380,z1,z44,z4,z5,z6]),(0,[z0,z863,z2,z4,z5,z6]),(0,[z0,z1,z281,z4,z5,z376]),(0,[z0,z1,z33,z4,z5,z376]),(0,[z0,z1,z2,z403,z10,z6]),(0,[z0,z1,z2,z278,z342,z6]),(0,[z864,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z112,z760,z4])],[(0,[z0,z1,z15,z4,z396,z6]),(0,[z0,z1,z108,z466,z5,z6]),(0,[z1,z833,z44,z4,z5,z6]),(0,[z0,z2,z64,z4,z206,z6]),(0,[z865,z1,z2,z4,z5,z6]),(0,[z0,z1,z33,z4,z5,z367]),(0,[z164,z1,z2,z4,z251,z6]),(1,[z446,z1,z95,z5,z6]),(0,[z22,z0,z1,z4,z236,z23])]],
   [[(0,[z1,z640,z44,z4,z5,z6]),(0,[z453,z1,z2,z4,z17,z6]),(0,[z0,z1,z2,z866,z5,z6]),(0,[z0,z272,z1,z95,z34,z6]),(0,[z0,z1,z21,z867,z5,z6]),(0,[z0,z1,z2,z868,z5,z6]),(0,[z0,z1,z2,z4,z869,z6])],[(0,[z0,z1,z2,z4,z5,z870]),(0,[z0,z272,z1,z95,z10,z6]),(0,[z107,z1,z2,z4,z10,z6]),(0,[z0,z1,z2,z734,z4,z5]),(0,[z0,z1,z2,z137,z5,z14]),(0,[z0,z1,z2,z120,z12,z6]),(0,[z0,z703,z1,z4,z5,z90]),(0,[z0,z1,z2,z4,z871,z6])],[(0,[z146,z1,z47,z4,z5,z6]),(0,[z0,z1,z2,z872,z5,z6]),(0,[z0,z873,z2,z4,z5,z6]),(0,[z22,z0,z1,z330,z4,z6]),(0,[z0,z1,z2,z112,z189,z4])],[(0,[z0,z1,z874,z4,z5,z6]),(0,[z0,z632,z2,z4,z10,z6]),(0,[z0,z2,z211,z4,z10,z6]),(0,[z0,z1,z2,z875,z4,z6]),(0,[z0,z1,z2,z4,z84,z147])],[(0,[z0,z1,z2,z4,z5,z876]),(0,[z0,z1,z2,z877,z5,z6]),(0,[z0,z1,z2,z878,z5,z6]),(0,[z0,z2,z667,z4,z10,z6]),(0,[z0,z1,z2,z879,z5,z6])],[(0,[z19,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z880]),(0,[z198,z0,z1,z2,z4,z881]),(0,[z1,z108,z833,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z882]),(0,[z0,z1,z2,z120,z5,z6]),(0,[z124,z0,z2,z80,z34,z6]),(0,[z0,z1,z2,z4,z5,z23]),(0,[z883,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z884,z4,z6]),(0,[z885,z1,z2,z4,z5,z6]),(0,[z124,z0,z2,z80,z10,z6]),(0,[z0,z2,z4,z10,z343,z6]),(0,[z0,z2,z4,z10,z6,z344]),(0,[z0,z1,z2,z886,z5,z6])],[(0,[z0,z1,z2,z4,z887,z6]),(0,[z0,z1,z2,z157,z5,z345]),(0,[z22,z0,z1,z340,z4,z6])]],
   [[(0,[z0,z1,z2,z92,z263,z6]),(0,[z0,z1,z2,z888,z4,z6]),(0,[z0,z889,z2,z4,z5,z6]),(0,[z0,z1,z890,z2,z4,z6]),(0,[z164,z1,z2,z4,z5,z14]),(0,[z0,z1,z323,z4,z5,z71]),(0,[z0,z260,z2,z335,z5,z6])],[(0,[z762,z0,z1,z109,z4,z6]),(1,[z1,z2,z4,z751,z6]),(0,[z891,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z194,z147]),(0,[z0,z1,z2,z518,z5,z23])],[(0,[z0,z1,z2,z4,z892,z6]),(0,[z0,z1,z339,z21,z5,z6]),(0,[z0,z1,z2,z4,z893,z6]),(0,[z0,z1,z2,z894,z5,z6])],[(0,[z521,z1,z457,z4,z5,z6]),(0,[z0,z1,z2,z759,z84,z6])],[(0,[z0,z1,z2,z130,z5,z345]),(0,[z0,z1,z895,z4,z5,z6]),(0,[z446,z1,z4,z95,z5,z6])],[(0,[z46,z54,z2,z4,z263,z6]),(0,[z0,z1,z2,z4,z896,z6]),(0,[z366,z1,z2,z4,z111,z6]),(0,[z180,z1,z2,z4,z5,z345]),(0,[z0,z1,z2,z4,z10,z345]),(0,[z0,z1,z2,z4,z897,z6]),(0,[z390,z1,z2,z4,z121,z6]),(0,[z489,z0,z1,z2,z4,z147]),(0,[z75,z1,z2,z4,z5,z23]),(0,[z0,z1,z2,z4,z104,z71])],[(0,[z0,z1,z898,z4,z5,z6]),(0,[z0,z2,z684,z4,z10,z6]),(0,[z899,z1,z2,z4,z10,z6]),(0,[z900,z1,z2,z4,z5,z6])],[(0,[z0,z1,z901,z4,z5,z6]),(0,[z0,z1,z2,z4,z902,z6]),(1,[z1,z833,z4,z5,z6]),(0,[z43,z1,z102,z44,z4,z6]),(0,[z0,z417,z1,z95,z5,z6]),(0,[z0,z2,z4,z34,z10,z147]),(0,[z0,z1,z2,z137,z5,z71])]],
   [[(0,[z0,z1,z903,z4,z5,z6]),(0,[z1,z2,z746,z41,z5,z6]),(0,[z0,z476,z2,z4,z10,z6])],[(0,[z0,z904,z2,z4,z5,z6])],[(0,[z349,z1,z44,z4,z5,z6]),(0,[z669,z0,z2,z80,z5,z6]),(0,[z0,z7,z2,z4,z206,z6]),(0,[z0,z327,z2,z4,z5,z23])],[(0,[z0,z1,z2,z4,z5,z905]),(0,[z1,z2,z4,z17,z751,z6]),(0,[z0,z1,z4,z5,z906,z6]),(0,[z0,z1,z457,z4,z34,z6]),(0,[z0,z1,z616,z2,z13,z5]),(0,[z0,z260,z2,z4,z236,z6]),(0,[z0,z1,z70,z4,z708,z6])],[(0,[z0,z1,z2,z4,z396,z116]),(0,[z40,z1,z2,z635,z5,z6]),(0,[z0,z1,z2,z4,z907,z6]),(0,[z0,z51,z1,z95,z5,z6]),(0,[z0,z1,z457,z4,z10,z6]),(0,[z521,z1,z323,z4,z5,z6])],[],[(0,[z682,z1,z44,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z208]),(0,[z0,z1,z2,z4,z34,z147]),(0,[z164,z1,z2,z4,z5,z71]),(1,[z0,z1,z867,z5,z6])],[(0,[z0,z1,z2,z4,z263,z283]),(0,[z0,z1,z2,z466,z10,z6]),(0,[z0,z1,z2,z908,z4,z6]),(0,[z506,z0,z2,z4,z5,z113]),(0,[z0,z1,z2,z188,z149,z6])]],
   [[(0,[z46,z732,z2,z4,z5,z6]),(0,[z107,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z909,z6]),(0,[z0,z1,z2,z4,z910,z6]),(0,[z0,z1,z2,z4,z911,z6]),(0,[z254,z1,z281,z4,z5,z6]),(0,[z0,z1,z2,z912,z4,z6]),(0,[z0,z1,z2,z913,z10,z6]),(0,[z0,z1,z2,z4,z216,z6]),(0,[z11,z0,z2,z4,z251,z113])],[(0,[z0,z1,z2,z4,z5,z914]),(0,[z0,z1,z20,z68,z5,z6]),(0,[z0,z2,z4,z32,z10,z6]),(0,[z19,z1,z2,z4,z5,z376]),(0,[z915,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z916]),(0,[z0,z917,z2,z4,z5,z6])],[(0,[z0,z1,z2,z918,z4,z6]),(0,[z0,z1,z2,z4,z5,z919]),(0,[z148,z1,z2,z4,z17,z6]),(0,[z19,z1,z2,z4,z5,z367]),(0,[z0,z1,z2,z335,z5,z229])],[(0,[z662,z1,z2,z41,z5,z6]),(0,[z1,z2,z4,z920,z5,z6]),(0,[z0,z1,z2,z4,z5,z921]),(0,[z0,z610,z2,z4,z10,z6]),(0,[z922,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z923,z5,z6]),(0,[z0,z1,z355,z4,z10,z6]),(0,[z107,z1,z2,z518,z5,z6]),(0,[z0,z1,z2,z842,z4,z5]),(0,[z0,z1,z2,z379,z5,z94])],[(0,[z0,z1,z2,z4,z924,z6]),(0,[z925,z1,z2,z4,z5,z6]),(0,[z660,z0,z64,z4,z5,z6]),(0,[z124,z0,z2,z80,z5,z6]),(0,[z124,z0,z2,z770,z5,z6]),(0,[z0,z2,z297,z4,z10,z6]),(0,[z0,z1,z323,z4,z10,z6]),(0,[z0,z1,z2,z112,z4,z53])],[(1,[z1,z2,z746,z5,z6]),(0,[z926,z0,z1,z2,z4,z6]),(0,[z0,z1,z2,z152,z5,z94]),(0,[z0,z1,z70,z4,z641,z6]),(0,[z0,z1,z2,z371,z5,z94])],[(0,[z43,z1,z44,z4,z5,z6]),(0,[z0,z1,z2,z927,z4,z6])]],
   [[(0,[z0,z1,z2,z4,z5,z928]),(0,[z0,z35,z64,z4,z10,z6]),(0,[z0,z315,z2,z4,z34,z6]),(0,[z22,z0,z1,z4,z708,z6])],[(0,[z0,z1,z2,z4,z929,z6]),(0,[z0,z1,z2,z27,z65,z6]),(0,[z0,z234,z2,z4,z34,z14])],[(0,[z0,z1,z930,z2,z4,z6]),(0,[z0,z2,z4,z728,z5,z6])],[(0,[z0,z1,z2,z761,z4,z5]),(0,[z354,z1,z2,z41,z5,z6]),(0,[z162,z1,z64,z4,z5,z6]),(0,[z0,z1,z2,z931,z5,z6]),(0,[z0,z1,z2,z137,z34,z6]),(0,[z0,z1,z2,z932,z175,z4]),(0,[z0,z260,z2,z278,z4,z6]),(0,[z0,z1,z2,z149,z282,z6]),(0,[z0,z1,z2,z842,z67,z5])],[(0,[z0,z1,z15,z4,z263,z6]),(0,[z0,z1,z2,z4,z5,z345]),(0,[z933,z1,z2,z4,z34,z6]),(0,[z0,z1,z2,z67,z34,z94]),(0,[z164,z1,z2,z120,z5,z6]),(0,[z0,z1,z697,z21,z5,z6])],[(0,[z46,z54,z2,z316,z5,z6]),(0,[z732,z54,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z934]),(0,[z0,z1,z2,z4,z5,z935]),(0,[z540,z1,z2,z41,z5,z6]),(0,[z0,z1,z2,z4,z936,z6]),(0,[z0,z1,z2,z4,z937,z6]),(0,[z0,z1,z2,z4,z938,z6]),(0,[z0,z1,z2,z67,z10,z94]),(0,[z899,z1,z2,z4,z5,z6]),(0,[z107,z327,z2,z4,z5,z6])],[(0,[z0,z1,z2,z939,z5,z6]),(0,[z0,z1,z2,z4,z256,z6]),(0,[z124,z0,z2,z80,z125,z6]),(0,[z124,z0,z2,z80,z126,z6]),(0,[z0,z1,z2,z940,z4,z49]),(0,[z0,z1,z941,z4,z5,z6]),(0,[z0,z1,z2,z4,z53,z71]),(0,[z446,z1,z2,z21,z5,z6]),(0,[z0,z272,z1,z175,z95,z6]),(0,[z0,z1,z2,z942,z4,z5])],[(0,[z0,z1,z943,z4,z5,z6]),(0,[z397,z1,z2,z41,z5,z6]),(0,[z156,z180,z64,z4,z5,z6]),(0,[z0,z1,z944,z4,z5,z6]),(0,[z0,z1,z457,z4,z12,z6])]],
   [[(0,[z0,z1,z2,z4,z263,z6]),(0,[z0,z1,z2,z945,z5,z6]),(0,[z146,z59,z2,z4,z203,z6]),(0,[z0,z1,z2,z4,z5,z946]),(0,[z0,z1,z2,z4,z375,z6]),(0,[z366,z1,z64,z4,z5,z6]),(0,[z366,z1,z2,z157,z5,z6]),(0,[z0,z1,z2,z4,z5,z947]),(0,[z0,z1,z2,z948,z10,z6])],[(0,[z0,z1,z2,z4,z949,z6]),(0,[z653,z1,z2,z4,z5,z155]),(0,[z0,z1,z2,z4,z950,z6]),(0,[z0,z1,z2,z4,z49,z951]),(0,[z0,z1,z2,z4,z5,z744]),(0,[z22,z75,z1,z4,z236,z6]),(0,[z0,z1,z2,z952,z5,z6])],[(0,[z544,z1,z2,z4,z5,z25]),(0,[z0,z1,z2,z4,z953,z6]),(0,[z0,z1,z2,z954,z5,z6]),(1,[z1,z109,z41,z5,z6]),(0,[z0,z1,z2,z4,z10,z502]),(0,[z0,z1,z2,z4,z5,z955]),(0,[z0,z274,z2,z4,z10,z6]),(0,[z164,z1,z2,z4,z34,z6]),(0,[z0,z1,z57,z2,z13,z5])],[(0,[z0,z1,z956,z4,z5,z6]),(0,[z0,z1,z2,z4,z957,z6]),(0,[z223,z1,z2,z4,z205,z6]),(0,[z0,z1,z2,z958,z5,z6]),(0,[z162,z1,z184,z4,z5,z6]),(0,[z0,z1,z2,z368,z4,z147]),(0,[z0,z1,z959,z4,z5,z6])],[(0,[z40,z1,z2,z746,z5,z6]),(0,[z0,z1,z2,z4,z10,z960])],[(0,[z366,z1,z2,z4,z34,z6]),(0,[z366,z1,z2,z130,z5,z6]),(0,[z0,z1,z281,z4,z5,z6]),(0,[z0,z1,z281,z215,z5,z6]),(0,[z39,z0,z2,z368,z4,z34]),(1,[z0,z2,z4,z5,z718]),(0,[z0,z1,z961,z2,z4,z6])],[(0,[z0,z1,z2,z92,z34,z6]),(0,[z0,z1,z2,z4,z5,z962]),(0,[z0,z1,z2,z466,z5,z6]),(0,[z366,z1,z2,z4,z10,z6]),(0,[z0,z1,z2,z963,z34,z6]),(0,[z0,z1,z2,z4,z964,z6]),(0,[z0,z1,z2,z27,z335,z6]),(0,[z0,z1,z2,z760,z4,z5])],[(0,[z0,z1,z2,z92,z10,z6]),(0,[z0,z1,z2,z4,z965,z6]),(0,[z521,z1,z2,z4,z10,z6]),(0,[z201,z0,z1,z4,z105,z6]),(0,[z0,z1,z2,z913,z5,z6]),(0,[z0,z1,z2,z335,z34,z6])]],
   [[(0,[z0,z1,z2,z4,z966,z6]),(0,[z87,z1,z2,z41,z5,z6]),(0,[z1,z2,z746,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z290]),(0,[z366,z1,z184,z4,z5,z6]),(0,[z156,z0,z64,z4,z5,z6]),(0,[z0,z1,z2,z967,z5,z6]),(0,[z0,z1,z968,z4,z5,z6]),(0,[z0,z618,z2,z4,z10,z6]),(0,[z0,z1,z2,z4,z34,z969]),(0,[z0,z1,z323,z4,z12,z6])],[(0,[z124,z0,z2,z80,z5,z376])],[(0,[z0,z1,z47,z316,z5,z6]),(0,[z0,z1,z44,z466,z5,z6]),(0,[z180,z1,z2,z157,z5,z6]),(0,[z0,z1,z2,z157,z10,z6]),(0,[z0,z7,z2,z4,z970,z6]),(0,[z0,z1,z2,z4,z971,z6]),(0,[z0,z1,z2,z4,z972,z6]),(0,[z0,z1,z2,z4,z639,z71])],[(0,[z0,z1,z2,z973,z5,z6]),(0,[z46,z54,z2,z4,z34,z6]),(0,[z0,z1,z355,z4,z5,z6]),(0,[z677,z1,z2,z151,z5,z6]),(0,[z0,z1,z2,z4,z974,z6]),(0,[z107,z1,z166,z2,z4,z6]),(0,[z22,z0,z1,z4,z236,z229])],[(0,[z40,z1,z2,z151,z34,z6]),(0,[z0,z1,z2,z975,z5,z6]),(0,[z0,z1,z323,z4,z5,z6]),(0,[z0,z1,z2,z4,z976,z6]),(0,[z0,z1,z2,z977,z34,z6]),(0,[z0,z1,z2,z4,z34,z978]),(0,[z565,z0,z2,z4,z34,z6]),(0,[z0,z1,z2,z4,z5,z718]),(0,[z0,z1,z2,z4,z5,z979]),(0,[z0,z1,z4,z708,z236,z6]),(0,[z0,z1,z2,z4,z644,z71])],[(0,[z0,z1,z2,z4,z5,z980]),(0,[z40,z1,z2,z151,z10,z6]),(0,[z0,z1,z2,z4,z312,z6]),(0,[z0,z1,z981,z4,z5,z6]),(0,[z0,z1,z2,z982,z5,z6]),(0,[z0,z1,z2,z4,z970,z6]),(0,[z983,z1,z2,z4,z5,z6]),(0,[z0,z1,z89,z2,z4,z6])],[(0,[z0,z1,z2,z984,z5,z6]),(0,[z0,z1,z288,z2,z4,z147]),(0,[z154,z1,z2,z4,z34,z6]),(0,[z0,z1,z2,z4,z12,z71])],[(0,[z0,z1,z2,z4,z203,z6]),(0,[z55,z1,z108,z4,z10,z6]),(0,[z180,z1,z2,z130,z5,z6]),(0,[z0,z1,z2,z130,z10,z6]),(0,[z364,z0,z64,z4,z5,z6]),(0,[z985,z0,z1,z2,z4,z6]),(0,[z0,z1,z986,z4,z5,z6]),(0,[z154,z1,z2,z4,z10,z6]),(0,[z0,z1,z2,z67,z5,z433])]],
   [[(0,[z0,z1,z47,z92,z5,z6]),(0,[z0,z1,z987,z4,z5,z6]),(0,[z180,z1,z2,z4,z10,z6]),(0,[z39,z0,z2,z4,z32,z6]),(0,[z0,z184,z796,z4,z5,z6]),(0,[z0,z1,z4,z5,z827,z6]),(0,[z988,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z263,z116]),(0,[z0,z732,z2,z4,z5,z6]),(0,[z0,z1,z989,z4,z5,z6]),(0,[z0,z1,z2,z990,z4,z6]),(0,[z0,z1,z991,z4,z5,z6]),(0,[z0,z2,z64,z4,z10,z6]),(0,[z254,z1,z2,z4,z34,z6]),(0,[z0,z1,z2,z4,z5,z229])],[(0,[z1,z54,z2,z92,z5,z6]),(0,[z0,z1,z166,z2,z167,z4]),(0,[z0,z1,z456,z2,z509,z4])],[(0,[z0,z2,z796,z4,z5,z6]),(0,[z992,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z658,z71])],[(0,[z140,z1,z44,z4,z5,z6]),(0,[z0,z2,z4,z177,z10,z6]),(0,[z993,z1,z2,z4,z5,z6]),(0,[z107,z1,z2,z335,z5,z6]),(0,[z994,z1,z2,z4,z5,z6]),(0,[z995,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z793]),(0,[z0,z1,z2,z518,z5,z229])],[(0,[z0,z1,z2,z4,z996,z6]),(0,[z0,z1,z2,z4,z997,z6]),(0,[z0,z1,z998,z4,z5,z6]),(0,[z999,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z1000,z6]),(0,[z0,z1,z2,z1001,z4,z6]),(0,[z0,z1,z2,z4,z1002,z6])],[(0,[z0,z1,z1003,z4,z5,z6]),(0,[z0,z1004,z1,z2,z5,z6]),(0,[z146,z59,z2,z4,z34,z6]),(0,[z0,z1,z2,z4,z5,z1005]),(0,[z55,z1,z2,z4,z375,z6]),(0,[z0,z1,z2,z4,z206,z208]),(0,[z1006,z1,z2,z4,z5,z6]),(0,[z0,z655,z2,z4,z10,z6]),(0,[z0,z1,z2,z4,z34,z1007]),(0,[z0,z1,z2,z34,z847,z6]),(0,[z0,z1,z2,z1008,z34,z6]),(0,[z0,z2,z4,z34,z598,z6]),(0,[z11,z164,z2,z4,z5,z113]),(0,[z0,z1,z2,z27,z82,z6]),(1,[z0,z1,z2,z760,z4])]],
   [[(0,[z0,z1,z2,z316,z5,z6]),(0,[z0,z1,z47,z4,z34,z6]),(0,[z0,z1,z2,z4,z5,z1009]),(0,[z146,z59,z2,z4,z10,z6]),(0,[z0,z1,z2,z4,z1010,z6]),(0,[z0,z1,z2,z4,z1011,z6]),(0,[z0,z1,z1012,z2,z4,z5]),(0,[z0,z1,z2,z4,z391,z147]),(0,[z0,z260,z2,z4,z5,z23]),(0,[z154,z1,z2,z403,z5,z6])],[(0,[z0,z1,z47,z4,z10,z6]),(0,[z0,z1,z2,z4,z5,z502]),(0,[z382,z1,z2,z4,z34,z6]),(0,[z1013,z1,z2,z4,z5,z6]),(0,[z75,z1,z2,z4,z5,z229]),(0,[z0,z1,z2,z335,z6,z71]),(0,[z0,z1,z2,z27,z149,z6])],[(0,[z146,z1,z2,z4,z5,z283]),(0,[z0,z1,z2,z4,z5,z806]),(0,[z0,z1014,z2,z4,z5,z6]),(0,[z589,z0,z2,z4,z34,z6]),(0,[z0,z1,z281,z4,z5,z367]),(0,[z521,z1,z2,z4,z12,z6]),(0,[z0,z1,z2,z4,z1015,z6]),(0,[z0,z1,z2,z759,z278,z6])],[(0,[z0,z1,z2,z1016,z5,z6]),(0,[z0,z1,z109,z151,z5,z6]),(0,[z0,z1,z457,z137,z5,z6]),(0,[z0,z1,z2,z175,z84,z6])],[(0,[z0,z1,z2,z4,z1017,z6]),(0,[z0,z555,z2,z4,z34,z6]),(0,[z0,z1,z2,z4,z1018,z6]),(0,[z0,z1,z2,z4,z654,z71]),(0,[z1,z2,z4,z5,z6,z716]),(0,[z0,z1,z2,z4,z104,z147]),(0,[z1,z2,z1019,z4,z5,z6])],[(0,[z55,z1,z2,z466,z5,z6]),(0,[z0,z1,z2,z4,z5,z1020]),(0,[z0,z1,z2,z4,z49,z6]),(0,[z446,z1,z2,z4,z34,z6]),(0,[z0,z1,z2,z4,z5,z361])],[(0,[z0,z1,z2,z1021,z5,z6]),(0,[z521,z1,z2,z4,z5,z6]),(0,[z0,z159,z2,z4,z10,z6]),(0,[z366,z1,z2,z4,z5,z345]),(0,[z19,z1,z33,z4,z5,z6]),(0,[z0,z327,z2,z4,z5,z229]),(0,[z0,z1022,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z72,z71])],[(0,[z0,z1,z2,z4,z5,z1023]),(0,[z146,z268,z2,z4,z5,z6]),(0,[z0,z44,z64,z4,z10,z6]),(0,[z198,z107,z1,z2,z4,z6]),(0,[z0,z2,z4,z34,z10,z6]),(0,[z0,z1,z2,z4,z1024,z6]),(0,[z0,z1,z2,z4,z1025,z6])]],
   [[(0,[z0,z1,z2,z1026,z5,z6]),(0,[z0,z1,z2,z36,z34,z6]),(0,[z446,z1,z20,z4,z5,z6]),(0,[z0,z1,z2,z1027,z5,z6])],[(0,[z0,z1,z2,z157,z5,z6]),(0,[z0,z9,z2,z4,z728,z6]),(0,[z0,z1,z2,z36,z10,z6]),(0,[z1028,z1,z2,z4,z5,z6])],[(0,[z0,z1,z15,z4,z34,z6]),(0,[z0,z1,z2,z4,z5,z1029]),(0,[z0,z309,z2,z215,z10,z6]),(0,[z164,z1,z457,z4,z5,z6]),(0,[z0,z435,z1,z95,z5,z6])],[(0,[z0,z1030,z2,z4,z5,z6])],[(0,[z1,z54,z47,z4,z5,z6]),(0,[z0,z1,z2,z4,z1031,z6]),(0,[z0,z2,z4,z970,z10,z6]),(0,[z0,z1,z323,z137,z5,z6]),(0,[z0,z1,z2,z1032,z5,z6])],[(0,[z0,z1,z1033,z2,z4,z5]),(0,[z0,z1,z2,z1034,z4,z6]),(0,[z1035,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z34,z6]),(0,[z0,z1,z2,z4,z1036,z6]),(0,[z55,z1,z108,z4,z5,z6]),(0,[z0,z1037,z2,z4,z5,z6]),(0,[z24,z1,z2,z4,z5,z25]),(0,[z0,z1,z2,z130,z5,z6]),(0,[z0,z7,z184,z4,z5,z6]),(0,[z0,z1,z2,z4,z1038,z6]),(0,[z382,z272,z1,z95,z5,z6]),(0,[z1039,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z10,z6]),(0,[z180,z1,z2,z4,z5,z6]),(0,[z0,z240,z2,z4,z10,z6]),(0,[z439,z1,z2,z41,z5,z6]),(0,[z257,z1,z2,z4,z5,z155]),(0,[z0,z1,z2,z4,z1040,z6])]],
   [[(0,[z0,z1,z2,z4,z5,z1041]),(0,[z0,z1,z2,z4,z5,z1042]),(0,[z198,z0,z1,z2,z4,z6]),(0,[z0,z2,z245,z4,z10,z6]),(0,[z0,z1,z2,z219,z4,z10]),(0,[z1043,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z1044,z5,z6]),(0,[z0,z1,z2,z4,z5,z1045]),(0,[z0,z1,z2,z4,z1046,z6]),(0,[z1047,z1,z2,z4,z5,z6])],[(0,[z55,z1,z141,z4,z5,z6]),(0,[z55,z1,z833,z4,z5,z6]),(0,[z0,z1,z2,z4,z53,z6]),(0,[z0,z1,z2,z518,z34,z6]),(0,[z0,z1,z2,z95,z115,z6]),(0,[z0,z1,z20,z867,z5,z6])],[(0,[z0,z1,z2,z4,z5,z1048]),(0,[z1049,z1,z2,z4,z5,z6]),(0,[z0,z1,z243,z21,z5,z6]),(0,[z0,z1,z2,z518,z10,z6]),(0,[z0,z1,z288,z4,z177,z6]),(0,[z164,z1,z323,z4,z5,z6])],[(0,[z0,z1,z2,z4,z1050,z6]),(0,[z0,z1,z2,z185,z5,z94]),(0,[z0,z1,z2,z112,z4,z147]),(0,[z22,z0,z327,z4,z236,z6]),(0,[z0,z1,z2,z149,z4,z361])],[(0,[z0,z1,z2,z1051,z5,z6]),(0,[z0,z1,z2,z4,z1052,z6]),(0,[z0,z1,z2,z4,z708,z6]),(0,[z0,z1,z2,z374,z4,z6]),(0,[z0,z1,z2,z127,z5,z94])],[(0,[z1053,z0,z1,z2,z4,z6]),(0,[z0,z1,z2,z4,z1054,z6]),(0,[z201,z0,z64,z4,z10,z6]),(0,[z75,z1,z2,z4,z34,z6])],[(0,[z0,z1,z2,z316,z396,z6]),(0,[z0,z1,z2,z4,z203,z729]),(0,[z43,z1,z44,z252,z5,z6]),(0,[z0,z348,z184,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1055])]],
   [[(0,[z0,z1,z47,z4,z5,z6]),(0,[z40,z1,z109,z4,z5,z6]),(0,[z0,z1,z2,z4,z111,z208]),(0,[z0,z78,z2,z4,z34,z6]),(0,[z0,z1,z4,z867,z5,z6]),(0,[z0,z1,z2,z403,z5,z6]),(0,[z1056,z1,z2,z4,z5,z6])],[(0,[z132,z1,z2,z151,z5,z6]),(0,[z204,z1,z2,z4,z205,z290]),(0,[z0,z1,z2,z4,z1057,z6]),(0,[z1,z2,z4,z5,z813,z25]),(0,[z156,z0,z64,z4,z206,z6]),(0,[z0,z64,z4,z95,z10,z6]),(0,[z0,z1,z451,z4,z5,z69]),(1,[z0,z1,z4,z5,z827]),(0,[z0,z1,z2,z374,z67,z94]),(0,[z1058,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z1059,z5,z6]),(0,[z16,z107,z1,z2,z4,z6]),(0,[z0,z1,z2,z4,z1060,z6]),(0,[z0,z1,z2,z4,z1061,z5]),(0,[z0,z1,z2,z4,z10,z147]),(0,[z164,z1,z2,z137,z5,z6]),(0,[z0,z1,z2,z4,z1062,z6])],[(0,[z139,z1,z108,z4,z5,z6]),(0,[z0,z1,z927,z109,z4,z6]),(0,[z0,z1,z2,z4,z5,z1063]),(0,[z0,z327,z2,z4,z34,z6]),(0,[z0,z272,z1,z95,z5,z6])],[(0,[z0,z1,z2,z1064,z5,z6]),(0,[z16,z1,z2,z4,z751,z6]),(0,[z0,z1,z2,z4,z5,z1065]),(0,[z0,z327,z2,z4,z10,z6]),(0,[z0,z1,z566,z4,z5,z69]),(0,[z35,z162,z1,z4,z5,z90])],[(0,[z0,z1,z2,z4,z53,z147]),(0,[z1066,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z21,z115,z6]),(0,[z0,z1,z244,z4,z5,z827])],[(0,[z0,z1,z2,z4,z5,z1067]),(0,[z258,z1,z44,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1068]),(0,[z0,z1,z2,z4,z5,z881]),(0,[z0,z1,z2,z4,z1069,z6]),(0,[z0,z1,z2,z1070,z5,z6]),(0,[z521,z1,z2,z137,z5,z6]),(0,[z446,z1,z2,z95,z5,z6]),(0,[z0,z1,z2,z4,z1071,z6]),(0,[z1072,z1,z2,z4,z5,z6])],[(0,[z198,z0,z1,z2,z4,z1073])]],
   [[(0,[z0,z1,z2,z1074,z5,z6]),(0,[z204,z1,z2,z4,z194,z6]),(0,[z1075,z1,z2,z4,z5,z6])],[(0,[z0,z1,z1076,z2,z4,z5]),(0,[z198,z16,z1,z2,z4,z6]),(0,[z0,z1,z2,z1077,z5,z6]),(0,[z0,z1,z2,z1078,z4,z6]),(0,[z0,z35,z1,z4,z5,z291]),(0,[z1079,z1,z2,z4,z5,z6]),(0,[z0,z260,z2,z4,z161,z6])],[(0,[z0,z1,z2,z1080,z5,z6]),(0,[z0,z1,z2,z4,z34,z376]),(0,[z0,z1,z2,z1081,z4,z5]),(0,[z0,z1,z79,z2,z631,z5]),(0,[z0,z1,z2,z1082,z5,z6]),(0,[z0,z1,z2,z4,z12,z6]),(0,[z0,z1,z2,z1083,z4,z6]),(0,[z0,z1,z2,z278,z84,z6]),(0,[z0,z1,z1084,z4,z5,z6])],[(0,[z0,z1,z2,z4,z10,z376]),(0,[z0,z1,z2,z4,z34,z367]),(0,[z0,z1,z1085,z4,z5,z6]),(0,[z39,z0,z2,z4,z728,z6])],[(0,[z1,z2,z44,z4,z375,z6]),(0,[z0,z1,z1086,z4,z5,z6]),(0,[z0,z1,z2,z1087,z5,z6]),(0,[z0,z1,z281,z80,z5,z6]),(0,[z0,z1,z2,z4,z10,z367]),(0,[z11,z0,z2,z4,z5,z718]),(0,[z0,z1,z867,z95,z5,z6]),(0,[z22,z0,z1,z518,z236,z6])],[(0,[z0,z1,z2,z4,z1088,z6]),(0,[z1089,z1,z2,z4,z5,z6]),(0,[z0,z234,z2,z4,z10,z14]),(0,[z0,z1,z2,z1090,z4,z6])],[(0,[z0,z1,z1091,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1092]),(0,[z0,z1,z2,z4,z1093,z6])],[(0,[z0,z1,z2,z4,z5,z1094]),(0,[z0,z1,z2,z4,z1095,z6]),(0,[z0,z1,z2,z4,z1096,z6]),(0,[z0,z1,z2,z137,z10,z6]),(0,[z0,z1,z2,z4,z1097,z6]),(0,[z0,z1,z1098,z4,z5,z6])]],
   [[(0,[z0,z1,z2,z4,z1099,z6]),(0,[z0,z1,z2,z4,z1100,z6]),(0,[z0,z234,z2,z4,z53,z14]),(0,[z1101,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z1102,z6]),(0,[z1103,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z1104,z6]),(0,[z1,z2,z44,z466,z5,z6]),(0,[z204,z1,z2,z4,z205,z502]),(0,[z0,z2,z4,z10,z418,z6]),(0,[z1105,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z1106,z4,z5]),(0,[z0,z1,z2,z4,z5,z813]),(0,[z0,z1,z2,z1107,z5,z6]),(0,[z162,z1,z2,z4,z34,z6]),(0,[z0,z1,z2,z482,z342,z6])],[(0,[z0,z1,z2,z4,z1108,z6]),(0,[z0,z1,z1109,z2,z4,z6]),(0,[z0,z1,z1110,z2,z5,z6]),(0,[z0,z1,z2,z4,z5,z1111]),(0,[z0,z1,z1112,z4,z5,z6]),(0,[z162,z1,z2,z4,z10,z6]),(0,[z0,z1,z2,z210,z346,z6]),(0,[z11,z0,z323,z4,z5,z113])],[(0,[z0,z1113,z1,z2,z4,z6]),(0,[z0,z1,z2,z1114,z5,z6])],[(0,[z46,z54,z2,z92,z5,z6]),(0,[z0,z1,z2,z4,z1115,z6]),(0,[z0,z1,z457,z4,z5,z6]),(0,[z0,z1,z1116,z2,z4,z6]),(0,[z164,z1,z2,z4,z10,z6])],[(0,[z681,z0,z64,z4,z5,z6]),(0,[z1117,z0,z1,z2,z4,z6]),(0,[z174,z1,z2,z4,z5,z155]),(0,[z1118,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z125,z6]),(0,[z0,z1,z2,z4,z126,z6])]],
   [[(0,[z0,z1,z1119,z4,z5,z6]),(0,[z1,z109,z4,z41,z5,z6]),(0,[z0,z1,z2,z4,z1120,z6]),(0,[z1121,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z1122,z5,z6]),(0,[z0,z1,z2,z4,z1123,z6]),(0,[z0,z1,z2,z1124,z5,z6]),(0,[z0,z1,z2,z4,z5,z147]),(0,[z0,z1,z735,z4,z10,z6]),(0,[z0,z1,z456,z2,z112,z4]),(0,[z0,z1,z323,z112,z4,z5])],[(0,[z0,z1,z2,z316,z5,z283]),(0,[z156,z0,z64,z4,z111,z6]),(0,[z0,z1,z2,z1125,z4,z6]),(0,[z0,z1,z2,z4,z1126,z6]),(0,[z0,z1,z2,z4,z1127,z6])],[(0,[z0,z238,z184,z4,z5,z6]),(0,[z1128,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z1129,z4,z6]),(0,[z0,z1,z2,z335,z10,z6]),(0,[z0,z1,z244,z4,z34,z69]),(0,[z0,z1,z590,z95,z5,z6]),(0,[z0,z1,z2,z932,z4,z5])],[(0,[z0,z1,z244,z4,z10,z69]),(0,[z1130,z1,z2,z4,z5,z6]),(0,[z107,z1,z2,z4,z5,z23]),(0,[z0,z260,z2,z4,z5,z229])],[(0,[z0,z1,z2,z1131,z5,z6]),(0,[z0,z1,z2,z4,z1132,z6]),(0,[z0,z1,z2,z4,z5,z1073]),(0,[z24,z1,z2,z4,z5,z813]),(0,[z124,z254,z2,z80,z5,z6]),(0,[z124,z0,z2,z80,z5,z367]),(0,[z162,z1,z2,z403,z5,z6])],[(0,[z0,z1,z2,z4,z1133,z6])],[(0,[z46,z54,z2,z4,z10,z6]),(0,[z87,z1,z2,z746,z5,z6]),(0,[z186,z1,z2,z4,z5,z155]),(0,[z0,z471,z2,z4,z5,z14]),(0,[z0,z1,z2,z175,z4,z1055]),(0,[z0,z1,z1134,z2,z4,z6]),(0,[z0,z1,z2,z13,z842,z5])]],
   [[(0,[z0,z1,z2,z92,z5,z283]),(0,[z0,z1,z1135,z4,z5,z6]),(0,[z0,z1,z2,z4,z751,z6]),(0,[z0,z1,z1136,z4,z5,z6])],[(0,[z0,z1,z2,z1137,z5,z6]),(0,[z0,z1,z2,z4,z17,z147]),(0,[z0,z1,z2,z4,z1138,z6])],[(0,[z0,z1,z559,z2,z112,z4]),(0,[z0,z1,z2,z215,z5,z376]),(0,[z0,z2,z533,z4,z34,z6]),(0,[z0,z1,z2,z137,z12,z6]),(0,[z0,z1,z2,z1139,z5,z6]),(0,[z0,z1,z70,z241,z4,z6]),(0,[z0,z1,z89,z2,z112,z4])],[(0,[z0,z1,z2,z4,z205,z147]),(0,[z0,z1,z184,z4,z5,z208]),(0,[z0,z1,z2,z4,z1140,z6]),(0,[z0,z675,z1,z95,z5,z6])],[(0,[z0,z234,z2,z4,z5,z14])],[(0,[z254,z1,z2,z4,z10,z6]),(0,[z0,z1,z2,z4,z34,z769]),(0,[z0,z1,z2,z1141,z4,z6])],[(0,[z0,z1,z2,z1142,z5,z6]),(0,[z0,z1,z833,z4,z5,z6]),(0,[z0,z1,z2,z4,z32,z921]),(0,[z0,z1,z2,z137,z5,z6])],[(0,[z0,z1,z15,z316,z5,z6]),(0,[z239,z0,z1,z95,z5,z6]),(0,[z0,z1,z2,z4,z1143,z6]),(0,[z933,z1,z2,z4,z5,z6]),(0,[z0,z1,z323,z4,z5,z113]),(0,[z0,z1,z2,z120,z251,z6]),(0,[z0,z1,z2,z67,z5,z94])]],
   [[(0,[z46,z54,z47,z4,z5,z6]),(0,[z0,z1,z2,z4,z34,z283]),(0,[z0,z1,z2,z4,z375,z25]),(0,[z1144,z1,z2,z4,z5,z6]),(0,[z11,z0,z2,z120,z5,z113]),(0,[z0,z260,z2,z27,z4,z6])],[(0,[z0,z1,z2,z4,z10,z283]),(0,[z0,z1,z1145,z4,z5,z6]),(0,[z0,z35,z1,z4,z34,z90]),(0,[z164,z1,z2,z4,z12,z6])],[(0,[z0,z1,z2,z1146,z5,z6]),(0,[z1,z44,z41,z95,z5,z6]),(0,[z0,z1,z2,z1147,z5,z6]),(0,[z0,z1,z2,z4,z5,z1148]),(0,[z0,z1,z2,z948,z5,z6]),(0,[z1,z2,z782,z4,z34,z6])],[(0,[z87,z1,z109,z41,z5,z6]),(0,[z0,z1,z2,z4,z1149,z6]),(0,[z0,z1,z2,z4,z125,z376]),(0,[z0,z1,z2,z4,z126,z376]),(0,[z0,z2,z4,z10,z483,z6])],[(0,[z0,z1,z1150,z4,z5,z6]),(0,[z198,z1,z2,z4,z205,z6]),(0,[z580,z1,z2,z4,z5,z25]),(0,[z0,z1,z2,z1151,z5,z6]),(0,[z0,z1,z2,z4,z125,z367]),(0,[z0,z1,z2,z4,z126,z367]),(0,[z22,z0,z1,z335,z236,z6])],[(0,[z0,z1,z15,z92,z5,z6]),(0,[z164,z1,z2,z4,z5,z6]),(0,[z0,z1,z1152,z2,z4,z5]),(0,[z0,z1153,z2,z4,z5,z6]),(0,[z382,z1,z2,z4,z10,z6]),(0,[z39,z0,z2,z4,z34,z147]),(0,[z1154,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z1155,z6]),(0,[z0,z1,z2,z4,z1156,z6]),(0,[z0,z1,z2,z368,z4,z10]),(0,[z0,z1,z2,z4,z5,z960]),(0,[z11,z0,z2,z4,z34,z113]),(0,[z0,z1,z510,z2,z368,z4])],[(0,[z0,z1,z2,z1157,z5,z6]),(0,[z0,z1,z1158,z4,z5,z6]),(0,[z11,z0,z2,z4,z10,z113]),(0,[z0,z1,z2,z368,z4,z12]),(0,[z0,z234,z2,z4,z5,z344]),(0,[z0,z1,z2,z4,z1159,z6]),(0,[z0,z1,z2,z219,z4,z5])]],
   [[(0,[z366,z1,z2,z4,z5,z6]),(0,[z0,z108,z64,z4,z10,z6]),(0,[z0,z1,z2,z4,z1160,z5]),(0,[z0,z1,z2,z219,z4,z34])],[(0,[z0,z1,z2,z92,z5,z6]),(0,[z0,z1,z2,z963,z5,z6]),(0,[z1161,z1,z2,z4,z5,z6]),(0,[z19,z1,z281,z4,z5,z6]),(0,[z0,z1,z2,z4,z468,z6]),(0,[z1,z2,z4,z5,z6,z1162]),(0,[z446,z1,z2,z4,z10,z6]),(0,[z0,z260,z2,z4,z34,z6]),(0,[z0,z1,z2,z4,z1160,z34]),(0,[z0,z1163,z2,z4,z5,z6]),(0,[z0,z1,z2,z149,z759,z6])],[(0,[z0,z1,z2,z4,z1164,z6]),(0,[z0,z1,z47,z4,z5,z283]),(0,[z0,z260,z2,z4,z10,z6]),(0,[z0,z2,z4,z5,z718,z113]),(0,[z0,z2,z4,z5,z14,z718]),(0,[z0,z1,z2,z335,z5,z6])],[(0,[z0,z1,z2,z4,z5,z969]),(0,[z0,z1,z2,z1165,z5,z6]),(0,[z0,z1,z546,z4,z5,z69]),(0,[z154,z1,z2,z36,z5,z6]),(0,[z0,z35,z1,z403,z5,z90])],[(0,[z1,z54,z2,z4,z5,z283]),(0,[z255,z1,z2,z41,z5,z6]),(0,[z0,z1,z2,z4,z122,z71]),(0,[z0,z1,z2,z4,z1166,z6]),(0,[z1167,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z210,z84,z6])],[(0,[z0,z2,z770,z80,z5,z6]),(0,[z0,z1,z2,z4,z5,z951])],[(0,[z46,z54,z2,z4,z5,z6]),(0,[z0,z1,z15,z4,z10,z6]),(0,[z59,z732,z2,z4,z5,z6]),(0,[z198,z43,z1,z44,z4,z6]),(0,[z182,z1,z44,z4,z5,z6]),(0,[z0,z1,z2,z4,z1168,z6])],[(0,[z0,z1,z2,z1169,z5,z6]),(0,[z40,z1,z2,z151,z5,z6]),(0,[z0,z7,z2,z4,z10,z6]),(0,[z0,z1,z2,z977,z5,z6]),(0,[z0,z1,z2,z4,z5,z978]),(0,[z0,z1,z33,z4,z34,z6])]],
   [[(0,[z0,z1,z2,z4,z206,z345]),(0,[z0,z1,z33,z4,z10,z6]),(0,[z0,z621,z1,z4,z5,z90])],[(0,[z0,z1,z2,z1170,z5,z6]),(0,[z154,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z1171,z5,z6]),(0,[z0,z1,z2,z4,z1172,z6]),(0,[z0,z1,z2,z4,z623,z71]),(0,[z0,z1,z2,z4,z1173,z6]),(0,[z0,z1,z89,z2,z4,z23]),(0,[z0,z35,z1,z4,z5,z827]),(0,[z0,z1,z2,z759,z4,z6]),(0,[z0,z1,z2,z4,z115,z94])],[(0,[z0,z1,z2,z1174,z4,z5]),(0,[z0,z1,z2,z4,z375,z155]),(0,[z0,z1,z2,z1175,z5,z6]),(0,[z0,z1,z2,z4,z1176,z6])],[(0,[z0,z1,z2,z4,z1177,z6]),(0,[z0,z1,z1178,z4,z5,z6]),(0,[z0,z1,z131,z4,z5,z69]),(0,[z0,z1,z2,z1179,z4,z6]),(0,[z0,z1180,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z1181,z6])],[(0,[z0,z1,z2,z316,z5,z116]),(0,[z254,z1,z2,z4,z5,z6]),(0,[z0,z1,z1182,z4,z5,z6]),(0,[z254,z1,z2,z215,z5,z6]),(0,[z0,z1,z2,z4,z10,z829]),(0,[z0,z1,z2,z4,z1183,z6]),(0,[z0,z1,z4,z10,z906,z6]),(0,[z0,z1,z20,z21,z5,z6]),(0,[z0,z1,z2,z4,z84,z361])],[(0,[z0,z1,z2,z4,z1184,z6]),(0,[z16,z1,z2,z4,z17,z6]),(0,[z204,z107,z1,z2,z4,z6]),(0,[z0,z1,z70,z685,z4,z6]),(0,[z156,z0,z796,z4,z5,z6]),(0,[z1185,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z1186,z10,z6])],[(0,[z0,z1,z1187,z4,z5,z6]),(0,[z0,z1,z2,z4,z34,z839]),(0,[z1188,z1,z2,z4,z5,z6]),(0,[z107,z260,z2,z4,z5,z6]),(0,[z22,z0,z260,z4,z236,z6])],[(0,[z0,z1189,z2,z4,z5,z6]),(0,[z0,z327,z2,z335,z5,z6])]],
   [[(0,[z0,z1,z2,z4,z5,z283]),(0,[z0,z348,z2,z4,z10,z6]),(0,[z0,z522,z2,z4,z10,z6])],[(0,[z0,z1,z109,z41,z5,z6]),(0,[z16,z0,z260,z2,z4,z6]),(0,[z0,z1,z2,z4,z128,z71]),(0,[z0,z1,z2,z1190,z5,z6]),(0,[z0,z1,z4,z161,z708,z6])],[(0,[z146,z59,z2,z4,z5,z6]),(0,[z0,z1,z2,z92,z5,z116]),(0,[z0,z1,z2,z4,z5,z1007]),(0,[z0,z1,z2,z1008,z5,z6]),(0,[z0,z522,z184,z4,z5,z6]),(0,[z75,z1,z2,z4,z10,z6]),(0,[z1191,z1,z2,z4,z5,z6]),(0,[z22,z107,z1,z4,z236,z6]),(0,[z0,z35,z1,z89,z4,z90])],[(0,[z1192,z1,z2,z4,z5,z6]),(0,[z0,z260,z2,z4,z6,z71]),(0,[z0,z1,z2,z4,z399,z71])],[(0,[z382,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z1193,z4,z6]),(0,[z0,z1,z2,z27,z175,z6])],[(0,[z0,z1,z2,z5,z1194,z6]),(0,[z156,z0,z64,z4,z5,z208]),(0,[z0,z1,z2,z823,z4,z32]),(0,[z0,z7,z562,z4,z5,z6]),(0,[z254,z1,z2,z4,z125,z6]),(0,[z254,z1,z2,z4,z126,z6]),(0,[z0,z1,z1195,z4,z5,z6]),(0,[z0,z1,z2,z1196,z4,z6]),(0,[z0,z1,z2,z760,z4,z104])],[(0,[z0,z1,z1197,z4,z5,z6]),(0,[z0,z1,z2,z4,z1198,z6]),(0,[z0,z272,z1,z867,z5,z6]),(1,[z0,z1,z2,z759,z6]),(0,[z0,z1,z2,z37,z4,z71])],[(0,[z0,z1,z2,z4,z5,z1199]),(0,[z0,z397,z1,z95,z5,z6]),(0,[z0,z1,z2,z1200,z4,z5]),(0,[z0,z1,z2,z940,z4,z5]),(0,[z0,z246,z2,z215,z5,z6]),(0,[z0,z1,z2,z4,z342,z147]),(0,[z1201,z1,z2,z4,z5,z6])]],
   [[(0,[z0,z1,z2,z92,z396,z6]),(0,[z146,z732,z2,z4,z5,z6]),(0,[z446,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1202]),(0,[z0,z2,z469,z4,z10,z6]),(0,[z0,z1,z2,z1200,z4,z34]),(0,[z0,z1,z2,z333,z4,z147]),(0,[z0,z1,z2,z4,z1203,z6])],[(0,[z0,z1,z109,z4,z34,z6]),(0,[z1204,z1,z2,z4,z5,z6]),(0,[z124,z0,z281,z80,z5,z6]),(0,[z124,z0,z33,z80,z5,z6]),(0,[z0,z1,z2,z4,z5,z1205]),(0,[z0,z218,z2,z4,z5,z14]),(0,[z0,z1,z70,z4,z161,z6])],[(0,[z0,z1,z2,z4,z34,z116]),(0,[z0,z1,z2,z4,z1206,z6]),(0,[z0,z493,z2,z4,z10,z6]),(0,[z0,z1,z109,z4,z10,z6]),(0,[z0,z1,z2,z4,z1207,z6]),(0,[z1208,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z10,z861]),(0,[z1209,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z691,z71])],[(0,[z0,z1,z2,z4,z10,z116]),(0,[z146,z692,z2,z4,z5,z6]),(0,[z0,z682,z1,z95,z5,z6]),(0,[z1,z2,z4,z751,z205,z6]),(0,[z0,z1,z2,z4,z5,z1210]),(0,[z0,z1,z2,z36,z5,z6]),(0,[z22,z0,z1,z4,z236,z6])],[(0,[z43,z1,z44,z466,z5,z6]),(0,[z0,z20,z64,z4,z10,z6]),(0,[z0,z9,z2,z4,z10,z6]),(0,[z865,z1,z2,z4,z34,z6]),(0,[z42,z0,z2,z4,z34,z6]),(0,[z0,z1,z2,z1211,z5,z6]),(0,[z0,z1,z166,z2,z4,z145])],[(0,[z0,z1,z15,z4,z5,z6]),(0,[z46,z54,z2,z4,z396,z6]),(0,[z0,z1,z457,z4,z251,z6])],[(0,[z0,z1,z70,z2,z4,z290]),(0,[z0,z1,z2,z1212,z5,z6]),(0,[z0,z1,z1213,z4,z5,z6]),(0,[z1214,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z1081,z4,z34]),(0,[z11,z0,z457,z4,z5,z113]),(0,[z0,z1,z2,z1215,z5,z6]),(0,[z0,z1,z2,z4,z1216,z6])],[(0,[z257,z1,z2,z4,z5,z813]),(1,[z0,z796,z4,z5,z6]),(0,[z0,z1,z2,z1217,z4,z6]),(0,[z1218,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z842,z5,z94])]],
   [[(0,[z370,z1,z108,z4,z5,z6]),(0,[z1219,z1,z2,z4,z5,z6]),(0,[z254,z1,z2,z4,z5,z376]),(0,[z148,z1,z2,z4,z421,z6]),(0,[z0,z1220,z2,z4,z5,z6]),(0,[z107,z1,z2,z4,z5,z229]),(0,[z0,z1,z2,z760,z4,z71])],[(0,[z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z1221,z5,z6]),(0,[z0,z1,z2,z1222,z4,z5]),(0,[z146,z31,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1223]),(0,[z0,z1,z2,z4,z111,z345]),(0,[z254,z1,z2,z4,z5,z367]),(1,[z0,z1,z2,z842,z5])],[(0,[z0,z1,z2,z1224,z5,z6]),(0,[z0,z1,z2,z4,z1225,z6]),(0,[z0,z1,z1226,z2,z4,z6]),(0,[z1,z2,z151,z746,z5,z6]),(0,[z0,z1,z2,z1227,z5,z6]),(0,[z19,z1,z2,z4,z34,z6]),(0,[z0,z1,z2,z1222,z4,z34]),(0,[z0,z1,z2,z4,z34,z23]),(0,[z0,z1,z2,z867,z5,z6]),(0,[z1,z2,z1228,z4,z5,z6]),(0,[z0,z1,z2,z842,z5,z6])],[(0,[z0,z1,z2,z1229,z4,z6]),(0,[z156,z0,z64,z4,z5,z345]),(0,[z19,z1,z2,z4,z10,z6]),(0,[z0,z1,z2,z4,z10,z23]),(0,[z11,z0,z2,z667,z4,z5])],[(0,[z0,z1,z47,z4,z5,z116]),(0,[z0,z1,z2,z886,z10,z6]),(0,[z0,z1,z2,z1186,z5,z6]),(0,[z22,z0,z1,z532,z4,z6])],[(0,[z506,z54,z2,z4,z5,z6]),(0,[z1230,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z518,z5,z6]),(0,[z0,z1,z166,z2,z335,z6]),(0,[z0,z1,z2,z67,z115,z94])],[(0,[z0,z1,z2,z4,z1231,z6]),(0,[z16,z1,z2,z4,z93,z6]),(0,[z0,z1,z796,z4,z5,z6]),(0,[z891,z1,z2,z4,z34,z6]),(0,[z0,z1,z323,z4,z251,z6])],[(0,[z1232,z1,z2,z4,z5,z6]),(0,[z1233,z1,z2,z4,z5,z6])]],
   [[(0,[z681,z54,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z1234,z6]),(0,[z201,z0,z64,z4,z5,z6]),(0,[z0,z1,z2,z4,z10,z723]),(0,[z0,z1,z2,z4,z34,z727]),(0,[z0,z1,z2,z112,z4,z12])],[(0,[z0,z1,z2,z1235,z5,z6]),(0,[z75,z1,z2,z4,z5,z6]),(0,[z0,z1,z1236,z4,z5,z6]),(0,[z0,z1,z2,z4,z1237,z6]),(0,[z0,z619,z2,z4,z10,z6]),(0,[z0,z7,z184,z4,z32,z6]),(0,[z0,z446,z1,z95,z5,z6]),(0,[z0,z1,z2,z379,z84,z6])],[(0,[z0,z1,z47,z4,z396,z6]),(0,[z0,z1,z2,z1238,z5,z6]),(0,[z0,z1,z1239,z4,z5,z6]),(0,[z201,z0,z1,z4,z236,z6])],[(0,[z0,z1,z1240,z2,z4,z6]),(0,[z22,z0,z1,z2,z4,z290]),(0,[z0,z512,z2,z4,z10,z6]),(0,[z124,z19,z2,z80,z5,z6]),(0,[z0,z1,z1241,z4,z5,z6]),(0,[z0,z1,z2,z188,z333,z6]),(0,[z1242,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z1243,z6])],[(0,[z0,z1,z2,z4,z1244,z6]),(0,[z0,z1,z1245,z4,z5,z6]),(0,[z0,z1,z2,z4,z1246,z6]),(0,[z1,z2,z4,z5,z155,z813]),(0,[z0,z238,z2,z4,z10,z6]),(0,[z0,z76,z2,z4,z10,z6]),(0,[z0,z1,z2,z4,z1247,z6])],[(0,[z0,z1,z2,z4,z1248,z6]),(0,[z40,z1,z2,z477,z5,z6]),(0,[z0,z1249,z2,z4,z5,z6]),(0,[z0,z1,z2,z157,z206,z6]),(0,[z0,z1,z2,z4,z1250,z6]),(0,[z0,z1,z2,z4,z1251,z6]),(0,[z75,z1,z2,z518,z5,z6])],[(0,[z0,z1,z2,z4,z1252,z6]),(0,[z439,z1,z44,z4,z5,z6]),(0,[z0,z1253,z2,z4,z5,z6]),(0,[z0,z1,z2,z157,z5,z208]),(0,[z0,z327,z2,z4,z5,z6]),(0,[z0,z1,z64,z4,z5,z208]),(0,[z11,z0,z2,z137,z5,z113]),(0,[z1254,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z1255,z6]),(0,[z0,z1,z323,z4,z5,z14])]],
   [[(0,[z0,z1,z2,z1256,z4,z6]),(0,[z0,z1,z2,z112,z137,z5])],[(0,[z0,z1,z2,z4,z1257,z6]),(0,[z0,z1,z2,z4,z1258,z6]),(0,[z0,z1,z2,z1259,z5,z6]),(0,[z0,z1,z4,z5,z708,z6]),(0,[z0,z1,z2,z4,z1260,z6])],[(0,[z0,z1,z2,z4,z5,z116]),(0,[z0,z1,z2,z1261,z4,z6]),(0,[z0,z1,z2,z4,z1262,z6]),(0,[z87,z1,z355,z41,z5,z6]),(0,[z0,z1,z2,z130,z206,z6]),(0,[z1263,z1,z2,z4,z5,z6]),(0,[z0,z327,z2,z518,z5,z6])],[(0,[z180,z1,z2,z4,z206,z6]),(0,[z0,z1,z2,z130,z5,z208]),(0,[z0,z1,z2,z4,z34,z208]),(0,[z0,z1,z2,z4,z5,z1264]),(0,[z0,z1,z70,z2,z4,z361]),(0,[z0,z1,z2,z278,z84,z361])],[(0,[z0,z1,z2,z1265,z5,z6]),(0,[z669,z54,z2,z4,z5,z6]),(0,[z16,z1,z2,z4,z117,z6]),(0,[z223,z1,z2,z4,z5,z25]),(0,[z180,z1,z2,z4,z5,z208]),(0,[z0,z1,z2,z4,z10,z208]),(0,[z0,z1,z2,z4,z5,z1266]),(0,[z0,z260,z166,z2,z4,z6]),(0,[z0,z1,z4,z5,z90,z827]),(0,[z0,z1,z2,z759,z5,z6])],[(0,[z0,z1,z2,z1267,z5,z6]),(0,[z0,z1,z2,z4,z1268,z6]),(0,[z0,z1,z184,z403,z5,z6]),(0,[z0,z1,z2,z4,z5,z376]),(0,[z39,z0,z2,z4,z34,z6]),(0,[z0,z1,z2,z368,z4,z5]),(0,[z0,z1,z2,z1269,z4,z6]),(0,[z0,z1,z2,z1270,z4,z6]),(0,[z107,z1,z2,z4,z34,z6]),(0,[z0,z1,z1271,z2,z4,z6])],[(0,[z0,z1,z2,z1272,z5,z6]),(0,[z0,z1,z2,z4,z5,z367]),(0,[z0,z1,z2,z368,z4,z34]),(0,[z763,z1,z2,z4,z10,z6]),(0,[z75,z327,z2,z4,z5,z6])],[(0,[z0,z1,z2,z316,z263,z6]),(0,[z0,z1,z2,z1273,z4,z6]),(0,[z0,z35,z1,z4,z90,z73]),(0,[z0,z1,z2,z13,z4,z115])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 521) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 521).take 518) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1039).take 240) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1279)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [521, 518, 240] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 88).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 88).take 84).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 172).take 84).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [88, 84, 84] = true :=
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

end PEqualNP.Outside.L_meta_36312

theorem PEqualNP.Outside.L_meta_36312 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075690 * 2 ^ 32 + 4276923048) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075690 * 2 ^ 32 + 4276923048) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_36312.solve