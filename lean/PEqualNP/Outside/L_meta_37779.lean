import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_37779

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
  Nat.testBit (4277071598 * 2 ^ 32 + 4209567944) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0xd0001048818d1b10#64 ++ 0x0d0001048818d1b1#64 ++ 0xec0534d9879f3f3f#64 ++ 0xfec0534d9879f3f3#64 : BitVec 256),
   (0x2008410244224460#64 ++ 0x4200841024422446#64 ++ 0xde1acb264463c7fd#64 ++ 0xfde1acb264463c7f#64 : BitVec 256),
   (0x40630c381854a984#64 ++ 0x140630c381854a98#64 ++ 0xb9e30c38787cf9cf#64 ++ 0xab9e30c38787cf9c#64 : BitVec 256),
   (0x81bc0fc06e80f606#64 ++ 0x981bc0fc06e80f60#64 ++ 0x79fc0fc07f80fe0b#64 ++ 0x679fc0fc07f80fe0#64 : BitVec 256),
   (0x02dff000777b0008#64 ++ 0xe02dff000777b000#64 ++ 0xfbfff0007fff0007#64 ++ 0x1fbfff0007fff000#64 : BitVec 256),
   (0x00f7aeb50000000f#64 ++ 0x000f7aeb50000000#64 ++ 0xfeffffff80000000#64 ++ 0xffeffffff8000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.or, [0, 2]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [1, 8]⟩, ⟨.and, [7, 9]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [2, 11]⟩, ⟨.or, [12, 5]⟩, ⟨.and, [6, 13]⟩, ⟨.or, [14, 10]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x00f7aeb50000000f 0x000f7aeb50000000 0xfeffffff80000000 0xffeffffff8000000

def z1 : W := mkw 0x02dff000777b0008 0xe02dff000777b000 0xfbfff0007fff0007 0x1fbfff0007fff000

def z2 : W := mkw 0x2008410244224460 0x4200841024422446 0xde1acb264463c7fd 0xfde1acb264463c7f

def z3 : W := mkw 0x40630c381854a984 0x140630c381854a98 0xb9e30c38787cf9cf 0xab9e30c38787cf9c

def z4 : W := mkw 0xa1bc4fc26ea2f666 0xda1bc4fc26ea2f66 0xfffecfe67fe3ffff 0xffffecfe67fe3fff

def z5 : W := mkw 0xd0001048818d1b10 0x0d0001048818d1b1 0xec0534d9879f3f3f 0xfec0534d9879f3f3

def z6 : W := mkw 0xd2dff048f7ff1b18 0xed2dff048f7ff1b1 0xfffff4d9ffff3f3f 0xffffff4d9ffff3f3

def z7 : W := mkw 0x0000000000000000 0x0000000000000000 0x980208204060c1cd 0xa980208204060c1c

def z8 : W := mkw 0x00f7aeb50000000f 0x000f7aeb50000000 0xfeffffffc060c1cd 0xffeffffffc060c1c

def z9 : W := mkw 0x81bc0fc06e80f606 0x981bc0fc06e80f60 0x79fc0fc07f80fe0b 0x679fc0fc07f80fe0

def z10 : W := mkw 0x02dff100777b4408 0xe02dff100777b440 0xfbfffb007fffc60f 0x7fbfffb007fffc60

def z11 : W := mkw 0x0000000000000000 0x0000000000000000 0xcc0000000403073d 0xfcc0000000403073

def z12 : W := mkw 0x02fffeb5777b000f 0xe02fffeb5777b000 0xffffffffffff0007 0xfffffffffffff000

def z13 : W := mkw 0x40200c380804a984 0x140200c380804a98 0x00000c380000f9c8 0xa00000c380000f9c

def z14 : W := mkw 0x22dff102777b4468 0xe22dff102777b446 0xfffffb267fffc7ff 0xffffffb267fffc7f

def z15 : W := mkw 0x400000081854a980 0x1400000081854a98 0x01000000787cf9cf 0x001000000787cf9c

def z16 : W := mkw 0x40630c381854a984 0x140630c381854a98 0x21e10418381c3802 0x021e10418381c380

def z17 : W := mkw 0x810801406e80f600 0x9810801406e80f60 0x010000007f80fe0b 0x0010000007f80fe0

def z18 : W := mkw 0x81ffaff56e80f60f 0x981ffaff56e80f60 0xffffffffff80fe0b 0xfffffffffff80fe0

def z19 : W := mkw 0x0000000000000000 0x0000000000000000 0xde1acb260403073d 0xfde1acb260403073

def z20 : W := mkw 0x0000000000000000 0x0000000000000000 0x6804000007800003 0x0680400000780000

def z21 : W := mkw 0x0000100001090000 0x0000010000109000 0xe8053000079f0007 0x1e8053000079f000

def z22 : W := mkw 0x02d7b00033590008 0xa02d7b0003359000 0xb9e730007bfc0007 0x0b9e730007bfc000

def z23 : W := mkw 0xd0631c7899ddbb94 0x1d0631c7899ddbb9 0xb9e73cf9fbfcf9cf 0xab9e73cf9fbfcf9c

def z24 : W := mkw 0x00d7a00000000008 0x000d7a0000000000 0xfafff00000000000 0x1fafff0000000000

def z25 : W := mkw 0xf0ffffffc5af5f7f 0x4f0ffffffc5af5f7 0xfeffffffc7ffffff 0xffeffffffc7fffff

def z26 : W := mkw 0x2008410244224460 0x4200841024422446 0x000000004463c7fd 0x0000000004463c7f

def z27 : W := mkw 0x2008410244224460 0x4200841024422446 0x121acb264060c0c0 0x0121acb264060c0c

def z28 : W := mkw 0x81bc0fc06e80f606 0x981bc0fc06e80f60 0x11f80b007f80fe0b 0x011f80b007f80fe0

def z29 : W := mkw 0xd0631c7899ddbb94 0x1d0631c7899ddbb9 0xb9e30c387fffffff 0xab9e30c387ffffff

def z30 : W := mkw 0xd243f04891ff1b18 0x6d243f04891ff1b1 0xee07f4d987ff3f3f 0xfee07f4d987ff3f3

def z31 : W := mkw 0xd0201efd818d1b17 0x0d0201efd818d1b1 0xec053fff879f3f3f 0xfec053fff879f3f3

def z32 : W := mkw 0x00f7aeb50000000f 0x000f7aeb50000000 0x12facb2600000000 0x012facb260000000

def z33 : W := mkw 0xd0001048818d1b10 0x0d0001048818d1b1 0x00000000079f3f3f 0x000000000079f3f3

def z34 : W := mkw 0x0043000010500000 0x0004300001050000 0xb9e30820787cc1cf 0xab9e30820787cc1c

def z35 : W := mkw 0x50001008810d0910 0x050001008810d091 0x84013019801f0134 0x984013019801f013

def z36 : W := mkw 0x0094000022000000 0x8009400002200000 0x21e400003b800002 0x021e400003b80000

def z37 : W := mkw 0x02d7b00033590008 0xa02d7b0003359000 0x21e530003b9c0002 0x021e530003b9c000

def z38 : W := mkw 0x2008400244220060 0x4200840024422006 0xde1ac026446301f5 0x9de1ac026446301f

def z39 : W := mkw 0xd0001048818d1b10 0x0d0001048818d1b1 0xfc073cf9c7ffffff 0xffc073cf9c7fffff

def z40 : W := mkw 0x81bc0fc06e80f606 0x981bc0fc06e80f60 0xfdfc0fc07f83ff3f 0xffdfc0fc07f83ff3

def z41 : W := mkw 0xb0085142c5ab5670 0x4b0085142c5ab567 0x461cf3c787830630 0x5461cf3c78783063

def z42 : W := mkw 0x00200eb500000007 0x000200eb50000000 0x04000fff80000000 0xe04000fff8000000

def z43 : W := mkw 0x606b4d3a5c76ede4 0x5606b4d3a5c76ede 0xfffbcf3e7c7fffff 0xffffbcf3e7c7ffff

def z44 : W := mkw 0x0043000010500000 0x0004300001050000 0xb9e30000787c0007 0x0b9e30000787c000

def z45 : W := mkw 0x9000104081891210 0x0900010408189121 0xcc0430c18783073d 0xfcc0430c18783073

def z46 : W := mkw 0x42dff008777f0908 0xe42dff008777f090 0xfbfff4187fff390f 0xbfbfff4187fff390

def z47 : W := mkw 0x02fffc307f7ba08c 0xf02fffc307f7ba08 0xfbfff8207fffc0c7 0x1fbfff8207fffc0c

def z48 : W := mkw 0x22ffffb7777b446f 0xe22ffffb7777b446 0xffffffffffffc7ff 0xfffffffffffffc7f

def z49 : W := mkw 0x42fffc387f7fa98c 0xf42fffc387f7fa98 0xfbfffc387ffff9cf 0xbfbfffc387ffff9c

def z50 : W := mkw 0x0243f000117b0008 0x60243f000117b000 0x8203f000007f0004 0x18203f000007f000

def z51 : W := mkw 0x2000400200220060 0x4200040020022006 0x8602c026006301f4 0x98602c026006301f

def z52 : W := mkw 0x22dff002777b0068 0xe22dff002777b006 0xfffff0267fff01f7 0x9fffff0267fff01f

def z53 : W := mkw 0x81b40ec02a80b206 0x981b40ec02a80b20 0x69e404c03f803e0b 0x669e404c03f803e0

def z54 : W := mkw 0x0000028500000003 0x0000002850000000 0x040003c780000000 0x4040003c78000000

def z55 : W := mkw 0x819c01406e80f600 0x9819c01406e80f60 0x79fc00007f80fe0b 0x079fc00007f80fe0

def z56 : W := mkw 0x20ffefb74422446f 0x420ffefb74422446 0xfeffffffc463c7fd 0xffeffffffc463c7f

def z57 : W := mkw 0x819c03c066805602 0x8819c03c06680560 0x401c03c007800600 0x4401c03c00780060

def z58 : W := mkw 0x0008010044004400 0x0000801004400440 0x58180b004400c609 0x658180b004400c60

def z59 : W := mkw 0x02d7f000337b0008 0xe02d7f000337b000 0xa3e7f0003bff0006 0x1a3e7f0003bff000

def z60 : W := mkw 0x00200c000800a004 0x100200c000800a00 0x11e008007800c000 0x011e008007800c00

def z61 : W := mkw 0x4043003810540980 0x0404300381054098 0x80030038007c01c4 0x880030038007c01c

def z62 : W := mkw 0xa008414244a25660 0x4a008414244a2566 0xfe1ecfe647e3ffff 0xffe1ecfe647e3fff

def z63 : W := mkw 0xd0001048818d1b10 0x0d0001048818d1b1 0xfe1fffff879f3f3f 0xffe1fffff879f3f3

def z64 : W := mkw 0x0043a03500000009 0x00043a0350000000 0x8603f03f80000000 0x98603f03f8000000

def z65 : W := mkw 0x029c5000777b0000 0xe029c5000777b000 0x79fc00007fff0007 0x079fc00007fff000

def z66 : W := mkw 0x02d7a00032500008 0xa02d7a0003250000 0x01e0000038000000 0x001e000003800000

def z67 : W := mkw 0x02dfe00076720008 0xe02dfe0007672000 0x13fac00078600000 0x013fac0007860000

def z68 : W := mkw 0xd000004880841b10 0x0d000004880841b1 0x040004d980003f38 0xe040004d980003f3

def z69 : W := mkw 0x2008410244224460 0x4200841024422446 0x4618c30604030630 0x54618c3060403063

def z70 : W := mkw 0x81b40ec02a80b206 0x981b40ec02a80b20 0x39e40cc07b80f80b 0x239e40cc07b80f80

def z71 : W := mkw 0x02dfe00076720008 0xe02dfe0007672000 0x7bfec0007fe00003 0x07bfec0007fe0000

def z72 : W := mkw 0x40f7aebd1854a98f 0x140f7aebd1854a98 0xfffffffff87cf9cf 0xffffffffff87cf9c

def z73 : W := mkw 0xd1bc1fc8ef8dff16 0x9d1bc1fc8ef8dff1 0xfdfd3fd9ff9fff3f 0xffdfd3fd9ff9fff3

def z74 : W := mkw 0x00200c000800a004 0x100200c000800a00 0x39e00c007800f80b 0x239e00c007800f80

def z75 : W := mkw 0xc1ff0ff87ed4ff86 0x9c1ff0ff87ed4ff8 0xf9ff0ff87ffcffcf 0xef9ff0ff87ffcffc

def z76 : W := mkw 0x81bc0fc06e80f606 0x981bc0fc06e80f60 0x51fc0bc07f80c600 0x451fc0bc07f80c60

def z77 : W := mkw 0x00630c301850a084 0x100630c301850a08 0x11e208207860c0c0 0x011e208207860c0c

def z78 : W := mkw 0x9000104081891210 0x0900010408189121 0x440430c187830630 0x5440430c18783063

def z79 : W := mkw 0x2008410244224460 0x4200841024422446 0x961acb264063c1f4 0x9961acb264063c1f

def z80 : W := mkw 0x8108014066805600 0x8810801406680560 0x0000000007800600 0x0000000000780060

def z81 : W := mkw 0x50001008810d0910 0x050001008810d091 0x00000000001f0134 0x000000000001f013

def z82 : W := mkw 0x0000000000000000 0x0000000000000000 0xec0534d980000000 0xfec0534d98000000

def z83 : W := mkw 0x2008410244224460 0x4200841024422446 0xfe1fffffc463c7fd 0xffe1fffffc463c7f

def z84 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z85 : W := mkw 0x83bcffc06fabf60e 0xf83bcffc06fabf60 0x7bfcffc07f83fe0b 0x77bfcffc07f83fe0

def z86 : W := mkw 0x4043003810540980 0x0404300381054098 0x00010018001c0000 0x000010018001c000

def z87 : W := mkw 0x8000004000801200 0x0800000400080120 0xec0404c007833f3f 0xfec0404c007833f3

def z88 : W := mkw 0x42dff038777f0988 0xe42dff038777f098 0xfbfff0387fff01c7 0x9fbfff0387fff01c

def z89 : W := mkw 0x819ca3c56680560b 0x8819ca3c56680560 0x461cf3c787800600 0x5461cf3c78780060

def z90 : W := mkw 0xf008514ac5af5f70 0x4f008514ac5af5f7 0xfe1fffffc7ffffff 0xffe1fffffc7fffff

def z91 : W := mkw 0x4000000800040900 0x0400000080004090 0xec010418041f3f3f 0xfec010418041f3f3

def z92 : W := mkw 0xd0001048818d1b10 0x0d0001048818d1b1 0x200534d9839c3802 0x0200534d9839c380

def z93 : W := mkw 0x604b413a54764de0 0x4604b413a54764de 0xde1bcb3e447fc7fd 0xfde1bcb3e447fc7f

def z94 : W := mkw 0x0000000000000000 0x0000000000000000 0xde1acb2600000000 0xfde1acb260000000

def z95 : W := mkw 0x62fffd3a7f7fedec 0xf62fffd3a7f7fede 0xffffff3e7fffffff 0xfffffff3e7ffffff

def z96 : W := mkw 0x22085102777b4460 0xe22085102777b446 0x010000007fffc7ff 0x0010000007fffc7f

def z97 : W := mkw 0x2008410244224460 0x4200841024422446 0x5a1acb264460c6c9 0x65a1acb264460c6c

def z98 : W := mkw 0x02dff000777b0008 0xe02dff000777b000 0x63fdf0003f9f0002 0x163fdf0003f9f000

def z99 : W := mkw 0x400000081854a980 0x1400000081854a98 0x01000000381c3802 0x001000000381c380

def z100 : W := mkw 0x0094a2850000000b 0x00094a2850000000 0x461cf3c780000000 0x5461cf3c78000000

def z101 : W := mkw 0xc1630ff818d4ff86 0x1c1630ff818d4ff8 0xb9e30ff8787cffcf 0xeb9e30ff8787cffc

def z102 : W := mkw 0x00d7a00000000008 0x000d7a0000000000 0xfefffb2600000000 0xffefffb260000000

def z103 : W := mkw 0x0294b00023090008 0xa0294b0002309000 0x0004300003800000 0x0000430000380000

def z104 : W := mkw 0x81200fc00880f606 0x181200fc00880f60 0x00000fc00000fe08 0x600000fc00000fe0

def z105 : W := mkw 0xa3ffffc27ffbf66e 0xfa3ffffc27ffbf66 0xffffffe67fffffff 0xfffffffe67ffffff

def z106 : W := mkw 0x02085000777b0000 0xe02085000777b000 0x010000007fff0007 0x0010000007fff000

def z107 : W := mkw 0x81b40ec02a80b206 0x981b40ec02a80b20 0x21e404c03b803802 0x021e404c03b80380

def z108 : W := mkw 0x0000000000000000 0x0000000000000000 0x200534d980000000 0x0200534d98000000

def z109 : W := mkw 0x01200f800800e406 0x101200f800800e40 0x00000b000000c000 0x000000b000000c00

def z110 : W := mkw 0x40630c381854a984 0x140630c381854a98 0xfde30c387c7fffff 0xffde30c387c7ffff

def z111 : W := mkw 0x00200c3000000004 0x000200c300000000 0x00000c3800000000 0xa00000c380000000

def z112 : W := mkw 0x00630c3000000004 0x000630c300000000 0xb8e30c3800000000 0xab8e30c380000000

def z113 : W := mkw 0x01bc0f806e00e406 0x901bc0f806e00e40 0x11f80b007800c000 0x011f80b007800c00

def z114 : W := mkw 0x40630c381854a984 0x140630c381854a98 0xb9e30c38381c3802 0xab9e30c38381c380

def z115 : W := mkw 0x024b5000777b0000 0xe024b5000777b000 0xb9e300007fff0007 0x0b9e300007fff000

def z116 : W := mkw 0x4000000800040900 0x0400000080004090 0x0000041800003908 0xa000004180000390

def z117 : W := mkw 0x01ff0fb07e50e486 0x901ff0fb07e50e48 0x11fa0b207860c0c0 0x011fa0b207860c0c

def z118 : W := mkw 0x00200eb500000007 0x000200eb50000000 0xde1acfff80000000 0xfde1acfff8000000

def z119 : W := mkw 0x00f7aeb51050000f 0x000f7aeb51050000 0xfffffffff87c0007 0xffffffffff87c000

def z120 : W := mkw 0x00f7aeb50000000f 0x000f7aeb50000000 0x66fdf7df80000000 0x566fdf7df8000000

def z121 : W := mkw 0x0000000000000000 0x0000000000000000 0xfe1fffff80000000 0xffe1fffff8000000

def z122 : W := mkw 0x024bf000777b0008 0xe024bf000777b000 0x8303f0007fff0007 0x18303f0007fff000

def z123 : W := mkw 0x00d7b00001090008 0x000d7b0000109000 0xfafff000079f0007 0x1fafff000079f000

def z124 : W := mkw 0x81200fc00880f606 0x181200fc00880f60 0x39e00fc07800fe0b 0x639e00fc07800fe0

def z125 : W := mkw 0x810000402a80b200 0x9810000402a80b20 0x010000003b803802 0x0010000003b80380

def z126 : W := mkw 0x000000001850a080 0x1000000001850a08 0x010000007860c0c0 0x0010000007860c0c

def z127 : W := mkw 0x009c010066004400 0x8009c01006600440 0x79fc0b007f80c60b 0x679fc0b007f80c60

def z128 : W := mkw 0xc1f70ef83ad4bb86 0x9c1f70ef83ad4bb8 0x21e504d83b9c3802 0x021e504d83b9c380

def z129 : W := mkw 0x019c038066004402 0x8019c03806600440 0x0018030000000000 0x0001803000000000

def z130 : W := mkw 0x50631c38995da994 0x150631c38995da99 0xbde33c39f87ff9ff 0xbbde33c39f87ff9f

def z131 : W := mkw 0x2000010200004460 0x0200001020000446 0x000000000000c7f8 0x0000000000000c7f

def z132 : W := mkw 0x029cf000672b0008 0xe029cf000672b000 0x7bfcf0007f830003 0x17bfcf0007f83000

def z133 : W := mkw 0x20284fb744224467 0x420284fb74422446 0xde1acfffc463c7fd 0xfde1acfffc463c7f

def z134 : W := mkw 0x606b4d3a5c76ede4 0x5606b4d3a5c76ede 0xb9e30c387c7fffff 0xab9e30c387c7ffff

def z135 : W := mkw 0xd000104899ddbb90 0x1d000104899ddbb9 0xed0534d9ffffffff 0xfed0534d9fffffff

def z136 : W := mkw 0x8000004000801200 0x0800000400080120 0x200404c003803802 0x0200404c00380380

def z137 : W := mkw 0x60ffefbf5c76edef 0x560ffefbf5c76ede 0xfffffffffc7fffff 0xffffffffffc7ffff

def z138 : W := mkw 0x029cf000777b0008 0xe029cf000777b000 0x431cf0007fff0007 0x1431cf0007fff000

def z139 : W := mkw 0x9094b2c58189121b 0x09094b2c58189121 0x461cf3c787830630 0x5461cf3c78783063

def z140 : W := mkw 0x00630c001850a004 0x100630c001850a00 0xb9e30c00787cf80f 0x2b9e30c00787cf80

def z141 : W := mkw 0xa1200fc20880f666 0x1a1200fc20880f66 0x04000fe60000fff8 0xe04000fe60000fff

def z142 : W := mkw 0x02f7beb53359000f 0xa02f7beb53359000 0x21e534d9bb9c0002 0x021e534d9bb9c000

def z143 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000004060c1cd 0x0000000004060c1c

def z144 : W := mkw 0x81200ec00880b206 0x181200ec00880b20 0x000004c000003800 0x0000004c00000380

def z145 : W := mkw 0x00b40eb500000007 0x000b40eb50000000 0x7cfc0fff80000000 0xe7cfc0fff8000000

def z146 : W := mkw 0x0094a00000000008 0x00094a0000000000 0x421cf00000000000 0x1421cf0000000000

def z147 : W := mkw 0x40200c381854a984 0x140200c381854a98 0x01000c38787cf9cf 0xa01000c38787cf9c

def z148 : W := mkw 0x400000080804a980 0x1400000080804a98 0x000000000000f9c8 0x0000000000000f9c

def z149 : W := mkw 0x81280fc04c80f606 0x181280fc04c80f60 0x58180fc04400fe09 0x658180fc04400fe0

def z150 : W := mkw 0x009c400066220000 0xc009c40006622000 0xfbfec0007fe30007 0x1fbfec0007fe3000

def z151 : W := mkw 0x2008410244224460 0x4200841024422446 0xce18c3060403073d 0xfce18c3060403073

def z152 : W := mkw 0x0043a03500000009 0x00043a0350000000 0xee07f4ff80000000 0xfee07f4ff8000000

def z153 : W := mkw 0x0000000000000000 0x0000000000000000 0xde1acb264060c1cd 0xfde1acb264060c1c

def z154 : W := mkw 0xd1b41ec8ab8dbb16 0x9d1b41ec8ab8dbb1 0xede534d9bf9f3f3f 0xfede534d9bf9f3f3

def z155 : W := mkw 0x0243f000117b0008 0x60243f000117b000 0xbbe3f000787f0007 0x1bbe3f000787f000

def z156 : W := mkw 0xd0f7befd818d1b1f 0x0d0f7befd818d1b1 0xfeffffff879f3f3f 0xffeffffff879f3f3

def z157 : W := mkw 0x02dff000777b0008 0xe02dff000777b000 0xfffff0007fff073f 0xffffff0007fff073

def z158 : W := mkw 0x00f7aeb51850a08f 0x100f7aeb51850a08 0x13facb267860c0c0 0x013facb267860c0c

def z159 : W := mkw 0x40f7aebd1854a98f 0x140f7aebd1854a98 0xbbfbcf3e787cf9cf 0xabbfbcf3e787cf9c

def z160 : W := mkw 0x00d7a2b50000000b 0x000d7a2b50000000 0xc61ff3ff80000000 0xdc61ff3ff8000000

def z161 : W := mkw 0xd000104899ddbb90 0x1d000104899ddbb9 0x010000007fffffff 0x0010000007ffffff

def z162 : W := mkw 0x810003c000805602 0x0810003c00080560 0x000003c000000600 0x4000003c00000060

def z163 : W := mkw 0x81f7aff50880f60f 0x181f7aff50880f60 0xfeffffff8000fe08 0xffeffffff8000fe0

def z164 : W := mkw 0x02dfb00077590008 0xa02dfb0007759000 0x79fd30007f9c0003 0x079fd30007f9c000

def z165 : W := mkw 0x0000000010500000 0x0000000001050000 0x01000000787c0007 0x001000000787c000

def z166 : W := mkw 0xd1081148ef8dff10 0x9d1081148ef8dff1 0xed0534d9ff9fff3f 0xfed0534d9ff9fff3

def z167 : W := mkw 0x6008410a44264d60 0x46008410a44264d6 0xfe1bcf3e447fffff 0xffe1bcf3e447ffff

def z168 : W := mkw 0x50431038915d0990 0x050431038915d099 0x84033039807f01f4 0x984033039807f01f

def z169 : W := mkw 0x00f7aeb50000000f 0x000f7aeb50000000 0x7afecfe600000000 0x67afecfe60000000

def z170 : W := mkw 0x40630c380804a984 0x140630c380804a98 0xb8e30c380000f9c8 0xab8e30c380000f9c

def z171 : W := mkw 0x0008400044220000 0x4000840004422000 0xda1ac00044630005 0x1da1ac0004463000

def z172 : W := mkw 0x2000010200004460 0x0200001020000446 0x04000b260000c7f8 0xe04000b260000c7f

def z173 : W := mkw 0xc1bc0ff86e84ff86 0x9c1bc0ff86e84ff8 0x79fc0ff87f80ffcb 0xe79fc0ff87f80ffc

def z174 : W := mkw 0x009c000066000000 0x8009c00006600000 0x79fc00007f800003 0x079fc00007f80000

def z175 : W := mkw 0x83ffffc07ffbf60e 0xf83ffffc07ffbf60 0xfbffffc07ffffe0f 0x7fbffffc07ffffe0

def z176 : W := mkw 0x819c03c066805602 0x8819c03c06680560 0x681c07c007803e0b 0x6681c07c007803e0

def z177 : W := mkw 0x0000000000000000 0x0000000000000000 0xec0534d98403073d 0xfec0534d98403073

def z178 : W := mkw 0x40630c381854a984 0x140630c381854a98 0x11e20820787cf9cf 0x011e20820787cf9c

def z179 : W := mkw 0x4000000800040900 0x0400000080004090 0xa8010418001c390f 0xaa8010418001c390

def z180 : W := mkw 0x40630c381854a984 0x140630c381854a98 0x91e30838787cc1c4 0x891e30838787cc1c

def z181 : W := mkw 0x81200ff50880f607 0x181200ff50880f60 0x04000fff8000fe08 0xe04000fff8000fe0

def z182 : W := mkw 0xd0001048818d1b10 0x0d0001048818d1b1 0xa40534d9839f3936 0x9a40534d9839f393

def z183 : W := mkw 0x029cf000672b0008 0xe029cf000672b000 0xea1df000079f0007 0x1ea1df000079f000

def z184 : W := mkw 0x81b40ec02a80b206 0x981b40ec02a80b20 0x79fc0fc03b803802 0x679fc0fc03b80380

def z185 : W := mkw 0x0000000000000000 0x0000000000000000 0x440430c180000000 0x5440430c18000000

def z186 : W := mkw 0x40f7aebd0804a98f 0x140f7aebd0804a98 0xfeffffff8000f9c8 0xffeffffff8000f9c

def z187 : W := mkw 0x00200c000800a004 0x100200c000800a00 0x21e0040038003802 0x021e004003800380

def z188 : W := mkw 0x8000004000801200 0x0800000400080120 0x680404c007803e0b 0x6680404c007803e0

def z189 : W := mkw 0x0000000000000000 0x0000000000000000 0x040004d980000000 0xe040004d98000000

def z190 : W := mkw 0xd1ffbffdef8dff1f 0x9d1ffbffdef8dff1 0xffffffffff9fff3f 0xfffffffffff9fff3

def z191 : W := mkw 0x81bc0ff56e80f607 0x981bc0ff56e80f60 0x7dfc0fffff80fe0b 0xe7dfc0fffff80fe0

def z192 : W := mkw 0x00630c3000000004 0x000630c300000000 0x20e1041800000000 0x020e104180000000

def z193 : W := mkw 0x810001400880f600 0x1810001400880f60 0x000000000000fe08 0x0000000000000fe0

def z194 : W := mkw 0x22dfe10276724468 0xe22dfe1027672446 0x13facb267860c0c0 0x013facb267860c0c

def z195 : W := mkw 0x42f7bc383b5da98c 0xb42f7bc383b5da98 0xb9e73c387bfcf9cf 0xab9e73c387bfcf9c

def z196 : W := mkw 0x029cf000672b0008 0xe029cf000672b000 0xda1ef00047e30005 0x1da1ef00047e3000

def z197 : W := mkw 0xc1200ff80884ff86 0x1c1200ff80884ff8 0x00000ff80000ffc8 0xe00000ff80000ffc

def z198 : W := mkw 0x206b4d3244224464 0x4206b4d324422446 0xfefbcf3e4463c7fd 0xffefbcf3e4463c7f

def z199 : W := mkw 0xd0631c7899ddbb94 0x1d0631c7899ddbb9 0xfde73cf9ffffffff 0xffde73cf9fffffff

def z200 : W := mkw 0x40200c380804a984 0x140200c380804a98 0x98020c384060f9cd 0xa98020c384060f9c

def z201 : W := mkw 0x00630c3000000004 0x000630c300000000 0xfefbcf3e00000000 0xffefbcf3e0000000

def z202 : W := mkw 0x80200c400880b204 0x180200c400880b20 0x79e40cc07f80fe0b 0x679e40cc07f80fe0

def z203 : W := mkw 0x83dff1407ffbf608 0xf83dff1407ffbf60 0xfbfff0007ffffe0f 0x1fbfff0007ffffe0

def z204 : W := mkw 0x2000400200220060 0x4200040020022006 0xde1acb26006301f4 0xfde1acb26006301f

def z205 : W := mkw 0x0243b00011590008 0x20243b0001159000 0x00013000001c0000 0x000013000001c000

def z206 : W := mkw 0x206b4d325c72e4e4 0x5206b4d325c72e4e 0x13facb267860c0c0 0x013facb267860c0c

def z207 : W := mkw 0x02dff000777b0008 0xe02dff000777b000 0x93fbf000787f0004 0x193fbf000787f000

def z208 : W := mkw 0x0000000000000000 0x0000000000000000 0x000008200000c1c8 0xa000008200000c1c

def z209 : W := mkw 0x2008410244224460 0x4200841024422446 0x161acb264060c7f8 0xe161acb264060c7f

def z210 : W := mkw 0x20284d024c22e464 0x520284d024c22e46 0xfffacf267c63ffff 0xffffacf267c63fff

def z211 : W := mkw 0x81ff0ff07ed0f686 0x981ff0ff07ed0f68 0x79fe0fe07fe0fecb 0x679fe0fe07fe0fec

def z212 : W := mkw 0x404300381854a980 0x1404300381854a98 0x81030038787cf9cf 0x881030038787cf9c

def z213 : W := mkw 0x0000100001090000 0x0000010000109000 0x20053000039c0002 0x020053000039c000

def z214 : W := mkw 0xf008514ac5af5f70 0x4f008514ac5af5f7 0x0000000047ffffff 0x00000000047fffff

def z215 : W := mkw 0x02d7b00033590008 0xa02d7b0003359000 0xe9e530003f9f0007 0x1e9e530003f9f000

def z216 : W := mkw 0x00d7a00000000008 0x000d7a0000000000 0x20e5300000000000 0x020e530000000000

def z217 : W := mkw 0x0000003500000001 0x0000000350000000 0x0400003f80000000 0x80400003f8000000

def z218 : W := mkw 0x00b40e8000000006 0x000b40e800000000 0x78fc0fc000000000 0x678fc0fc00000000

def z219 : W := mkw 0x81f7aef52a80b20f 0x981f7aef52a80b20 0xffffffffbb803802 0xfffffffffbb80380

def z220 : W := mkw 0xf008414ac4a65f70 0x4f008414ac4a65f7 0xde1acfffc463fffd 0xfde1acfffc463fff

def z221 : W := mkw 0x02dff000777b0008 0xe02dff000777b000 0x33fff0007bfc0002 0x033fff0007bfc000

def z222 : W := mkw 0xd0200c788884bb94 0x1d0200c788884bb9 0x04000cf98000fff8 0xe04000cf98000fff

def z223 : W := mkw 0x0043000010500000 0x0004300001050000 0x11e2000078600000 0x011e200007860000

def z224 : W := mkw 0x029cf000672b0008 0xe029cf000672b000 0x421cf00007830000 0x1421cf0000783000

def z225 : W := mkw 0x00630c301850a084 0x100630c301850a08 0x01e0000038000000 0x001e000003800000

def z226 : W := mkw 0x00f70eb000000006 0x000f70eb00000000 0xf8ff0ff800000000 0xef8ff0ff80000000

def z227 : W := mkw 0x2008410244224460 0x4200841024422446 0x561acb264463c6f0 0x5561acb264463c6f

def z228 : W := mkw 0x00f7aeb50000000f 0x000f7aeb50000000 0x20e534d980000000 0x020e534d98000000

def z229 : W := mkw 0x00f7aeb50000000f 0x000f7aeb50000000 0x16facfff80000000 0xe16facfff8000000

def z230 : W := mkw 0x00f7aeb50000000f 0x000f7aeb50000000 0x32ffffff80000000 0x032ffffff8000000

def z231 : W := mkw 0x8000004000801200 0x0800000400080120 0x400400c007800600 0x4400400c00780060

def z232 : W := mkw 0x00200c0000000004 0x000200c000000000 0x38e00c0000000000 0x238e00c000000000

def z233 : W := mkw 0xd0001048818d1b10 0x0d0001048818d1b1 0xe80534d9879f3807 0x1e80534d9879f380

def z234 : W := mkw 0x4000000800040900 0x0400000080004090 0xb8030c38407cf9cf 0xab8030c38407cf9c

def z235 : W := mkw 0x0043100011590000 0x0004310001159000 0xf9e730007fff0007 0x1f9e730007fff000

def z236 : W := mkw 0x0043a03500000009 0x00043a0350000000 0x0202c02600000000 0x00202c0260000000

def z237 : W := mkw 0x81b40fc02a80f606 0x981b40fc02a80f60 0x21e40fc03b80fe0a 0x621e40fc03b80fe0

def z238 : W := mkw 0x40630c3800040904 0x040630c380004090 0xb8e30c38001c390f 0xab8e30c38001c390

def z239 : W := mkw 0x830851407ffbf600 0xf830851407ffbf60 0x010000007ffffe0f 0x0010000007ffffe0

def z240 : W := mkw 0x2008410244224460 0x4200841024422446 0x58180b004463c7fd 0x658180b004463c7f

def z241 : W := mkw 0x40630c381854a984 0x140630c381854a98 0x80030c38007cf9cc 0xa80030c38007cf9c

def z242 : W := mkw 0xa1bc4fc26ea2f666 0xda1bc4fc26ea2f66 0x79fc0fc07fe3ffff 0x679fc0fc07fe3fff

def z243 : W := mkw 0x81bc4fc06ea2f606 0xd81bc4fc06ea2f60 0xfbfecfc07fe3fe0f 0x7fbfecfc07fe3fe0

def z244 : W := mkw 0xf008514ac5af5f70 0x4f008514ac5af5f7 0xec0534d9c7ffffff 0xfec0534d9c7fffff

def z245 : W := mkw 0xf008514ac5af5f70 0x4f008514ac5af5f7 0xde1acb2647ffffff 0xfde1acb2647fffff

def z246 : W := mkw 0x420850087f7fa980 0xf420850087f7fa98 0x010000007ffff9cf 0x0010000007ffff9c

def z247 : W := mkw 0x40630c381854a984 0x140630c381854a98 0x21e10418787cf9cf 0x021e10418787cf9c

def z248 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000000403073d 0x0000000000403073

def z249 : W := mkw 0x81bcafc56e80f60f 0x981bcafc56e80f60 0x7ffcffc7ff80fe0b 0x77ffcffc7ff80fe0

def z250 : W := mkw 0x81f7aef52a80b20f 0x981f7aef52a80b20 0x21e534d9bb803802 0x021e534d9bb80380

def z251 : W := mkw 0x00630c300800a004 0x100630c300800a00 0xb9e30c387800f80b 0xab9e30c387800f80

def z252 : W := mkw 0x0063ac350000000d 0x00063ac350000000 0xbee3fc3f80000000 0xbbee3fc3f8000000

def z253 : W := mkw 0xd0001048818d1b10 0x0d0001048818d1b1 0x640534d9879f3e32 0x5640534d9879f3e3

def z254 : W := mkw 0x00bc0f8044004406 0x000bc0f804400440 0x78fc0fc04400c609 0x678fc0fc04400c60

def z255 : W := mkw 0x0000000000000000 0x0000000000000000 0xc800000004030005 0x1c80000000403000

def z256 : W := mkw 0x0000000000000000 0x0000000000000000 0x8400000000030134 0x9840000000003013

def z257 : W := mkw 0x40630c381854a984 0x140630c381854a98 0x31e30c38787cf8c2 0x031e30c38787cf8c

def z258 : W := mkw 0x0000100001090000 0x0000010000109000 0xec0534d9879f0007 0xfec0534d9879f000

def z259 : W := mkw 0x22dff102777b4468 0xe22dff102777b446 0xfbfff0007fffc7ff 0x1fbfff0007fffc7f

def z260 : W := mkw 0x819c03c066805602 0x8819c03c06680560 0x581c0bc04780c609 0x6581c0bc04780c60

def z261 : W := mkw 0x41ff0fb87e54ed86 0x941ff0fb87e54ed8 0xb9fb0f38787cf9cf 0xab9fb0f38787cf9c

def z262 : W := mkw 0xd0001048818d1b10 0x0d0001048818d1b1 0xcc000000079f3f3f 0xfcc000000079f3f3

def z263 : W := mkw 0x9000104081891210 0x0900010408189121 0x000430c183800000 0x0000430c18380000

def z264 : W := mkw 0x0000000000000000 0x0000000000000000 0x4400000004030630 0x5440000000403063

def z265 : W := mkw 0x606b4d3a5c76ede4 0x5606b4d3a5c76ede 0xbbfbcf3e787cf9cf 0xabbfbcf3e787cf9c

def z266 : W := mkw 0x40200c380804a984 0x140200c380804a98 0x0000041800003800 0x0000004180000380

def z267 : W := mkw 0x40200c380804a984 0x140200c380804a98 0x39e00c387800f9cb 0xa39e00c387800f9c

def z268 : W := mkw 0x92dff040f7fb1218 0xe92dff040f7fb121 0xfffff0c1ffff0637 0x5fffff0c1ffff063

def z269 : W := mkw 0x40630c381854a984 0x140630c381854a98 0xfffbcf3e787cf9cf 0xffffbcf3e787cf9c

def z270 : W := mkw 0x0000000000000000 0x0000000000000000 0x9802000040600005 0x0980200004060000

def z271 : W := mkw 0x7000500a812f0970 0x47000500a812f097 0x8603f03f807f01f4 0x98603f03f807f01f

def z272 : W := mkw 0xd094b2cd818d1b1b 0x0d094b2cd818d1b1 0xee1df7df879f3f3f 0xfee1df7df879f3f3

def z273 : W := mkw 0x0043000010500000 0x0004300001050000 0x21e10000381c0002 0x021e10000381c000

def z274 : W := mkw 0xd000004880841b10 0x0d000004880841b1 0xcc0004d984033f3d 0xfcc0004d984033f3

def z275 : W := mkw 0xd043104891dd1b10 0x0d043104891dd1b1 0xfde734d9ffff3f3f 0xffde734d9ffff3f3

def z276 : W := mkw 0x02f7beb53359000f 0xa02f7beb53359000 0xffffffffbb9c0002 0xfffffffffbb9c000

def z277 : W := mkw 0x0208400076720000 0xe020840007672000 0x0100000078600000 0x0010000007860000

def z278 : W := mkw 0x0043003000000000 0x0004300300000000 0x8003003800000000 0x8800300380000000

def z279 : W := mkw 0x8000004000801200 0x0800000400080120 0xec0534d987803e0b 0xfec0534d987803e0

def z280 : W := mkw 0x00ffaeb56600000f 0x800ffaeb56600000 0xffffffffff800003 0xfffffffffff80000

def z281 : W := mkw 0xd0001048818d1b10 0x0d0001048818d1b1 0x840134d9801f3f3c 0xf840134d9801f3f3

def z282 : W := mkw 0xd0001048818d1b10 0x0d0001048818d1b1 0xa80534d9839c390f 0xaa80534d9839c390

def z283 : W := mkw 0xe1ff4ffa7ef6ffe6 0xde1ff4ffa7ef6ffe 0xffffcffe7fffffff 0xfffffcffe7ffffff

def z284 : W := mkw 0x50001008810d0910 0x050001008810d091 0x00013019801c0000 0x000013019801c000

def z285 : W := mkw 0x02dff000777b0008 0xe02dff000777b000 0xfffffb267fff0007 0xffffffb267fff000

def z286 : W := mkw 0x4063ac3d1854a98d 0x14063ac3d1854a98 0xbfe3fc3ff87cf9cf 0xbbfe3fc3ff87cf9c

def z287 : W := mkw 0x81bc0fc06e80f606 0x981bc0fc06e80f60 0xfdfd3fd9ff80fe0b 0xffdfd3fd9ff80fe0

def z288 : W := mkw 0x4043000810540900 0x0404300081054090 0xb9e30418787c390f 0xab9e30418787c390

def z289 : W := mkw 0x0008000044000000 0x0000800004400000 0x5818000044000001 0x0581800004400000

def z290 : W := mkw 0x42f7bc383b5da98c 0xb42f7bc383b5da98 0x21e534183b9c3802 0x021e534183b9c380

def z291 : W := mkw 0x02dff000777b0008 0xe02dff000777b000 0xfbfff8207fffc1cf 0xbfbfff8207fffc1c

def z292 : W := mkw 0x22dff102777b4468 0xe22dff102777b446 0xfbfffb267fffc0c7 0x1fbfffb267fffc0c

def z293 : W := mkw 0x4000000800040900 0x0400000080004090 0x20010418001c3802 0x020010418001c380

def z294 : W := mkw 0xf1bc5fcaefafff76 0xdf1bc5fcaefafff7 0xffffffffffffffff 0xffffffffffffffff

def z295 : W := mkw 0xd1ff1ff8ffddff96 0x9d1ff1ff8ffddff9 0xfdff3ff9ffffffff 0xffdff3ff9fffffff

def z296 : W := mkw 0x2008010244004460 0x0200801024400446 0x5c180b264400c7f9 0xe5c180b264400c7f

def z297 : W := mkw 0x5243f008917f0918 0x65243f008917f091 0x8603f019807f0134 0x98603f019807f013

def z298 : W := mkw 0x0000000000000000 0x0000000000000000 0x680404c000000000 0x6680404c00000000

def z299 : W := mkw 0xd000004880841b10 0x0d000004880841b1 0x6c0404d987803f3b 0xe6c0404d987803f3

def z300 : W := mkw 0x809c004066801200 0x8809c00406680120 0x79fc04c07f803e0b 0x679fc04c07f803e0

def z301 : W := mkw 0xa10841426ea2f660 0xda10841426ea2f66 0x010000007fe3ffff 0x0010000007fe3fff

def z302 : W := mkw 0x40630c381854a984 0x140630c381854a98 0x21e10c38381cf9ca 0xa21e10c38381cf9c

def z303 : W := mkw 0xd0085048c5af1b10 0x4d0085048c5af1b1 0xfe1ff4d9c7ff3f3f 0xffe1ff4d9c7ff3f3

def z304 : W := mkw 0xd2d7b048b3dd1b18 0xad2d7b048b3dd1b1 0xede534d9bf9f3f3f 0xfede534d9bf9f3f3

def z305 : W := mkw 0x0043a03500000009 0x00043a0350000000 0x0001301980000000 0x0000130198000000

def z306 : W := mkw 0x80f7aef50080120f 0x080f7aef50080120 0xfeffffff87803e0b 0xffeffffff87803e0

def z307 : W := mkw 0x40f7ac381854a98c 0x140f7ac381854a98 0xfbfffc38787cf9cf 0xbfbfffc38787cf9c

def z308 : W := mkw 0xd0001048818d1b10 0x0d0001048818d1b1 0x240534d9839c3f3a 0xe240534d9839c3f3

def z309 : W := mkw 0x4000003800040980 0x0400000380004098 0x00000038000001c0 0x800000038000001c

def z310 : W := mkw 0x9000104081891210 0x0900010408189121 0xec0530c1879f0637 0x5ec0530c1879f063

def z311 : W := mkw 0xc1ff0ff87ed4ff86 0x9c1ff0ff87ed4ff8 0x79fd0fd87f9cfe0b 0x679fd0fd87f9cfe0

def z312 : W := mkw 0x00b4aeb50000000f 0x000b4aeb50000000 0x461cffff80000000 0xf461cffff8000000

def z313 : W := mkw 0x40ff0c387e54a984 0x940ff0c387e54a98 0xf9ff0c387ffcf9cf 0xaf9ff0c387ffcf9c

def z314 : W := mkw 0x02fffc007f7ba00c 0xf02fffc007f7ba00 0xfbfffc007ffff80f 0x3fbfffc007ffff80

def z315 : W := mkw 0x0000000000000000 0x0000000000000000 0xda1ac00000000000 0x1da1ac0000000000

def z316 : W := mkw 0x0008010044004400 0x0000801004400440 0x000000004400c609 0x0000000004400c60

def z317 : W := mkw 0x02fffe80777b000e 0xe02fffe80777b000 0xfbffffc07fff0007 0x7fbffffc07fff000

def z318 : W := mkw 0x00bc0c006e00a004 0x900bc0c006e00a00 0x79fc0c007f80f80b 0x279fc0c007f80f80

def z319 : W := mkw 0x0000000000000000 0x0000000000000000 0x9802082000000000 0xa980208200000000

def z320 : W := mkw 0x2008410244224460 0x4200841024422446 0xde1acb264060c0c0 0xfde1acb264060c0c

def z321 : W := mkw 0x2008410244224460 0x4200841024422446 0x5e18cb064403c639 0x75e18cb064403c63

def z322 : W := mkw 0xd0631c7899ddbb94 0x1d0631c7899ddbb9 0x21e534d9bb9c3802 0x021e534d9bb9c380

def z323 : W := mkw 0x0008010044004400 0x0000801004400440 0xde1acb264400c609 0xfde1acb264400c60

def z324 : W := mkw 0x20ffefb74422446f 0x420ffefb74422446 0xdefacb264463c7fd 0xfdefacb264463c7f

def z325 : W := mkw 0x2243f002117b0068 0x62243f002117b006 0x8603f026007f01f4 0x98603f026007f01f

def z326 : W := mkw 0x0000000000000000 0x0000000000000000 0xa8010000001c0007 0x0a8010000001c000

def z327 : W := mkw 0x21bc4f826e22e466 0xd21bc4f826e22e46 0x13facb267860c0c0 0x013facb267860c0c

def z328 : W := mkw 0x40f7aebd1854a98f 0x140f7aebd1854a98 0xb9e73cf9f87cf9cf 0xab9e73cf9f87cf9c

def z329 : W := mkw 0x81bc0ec06e80b206 0x981bc0ec06e80b20 0x79fc04c07f803803 0x079fc04c07f80380

def z330 : W := mkw 0xd0f7befd818d1b1f 0x0d0f7befd818d1b1 0xfeffffff839c3802 0xffeffffff839c380

def z331 : W := mkw 0x00df000076500000 0x800df00007650000 0xf9ff00007ffc0007 0x0f9ff00007ffc000

def z332 : W := mkw 0x2000010200004460 0x0200001020000446 0x00000b260000c0c0 0x000000b260000c0c

def z333 : W := mkw 0x00200c000800a004 0x100200c000800a00 0x00000c000000f808 0x200000c000000f80

def z334 : W := mkw 0x00f7beb50109000f 0x000f7beb50109000 0xfeffffff879f0007 0xffeffffff879f000

def z335 : W := mkw 0xd1bc1fc8ef8dff16 0x9d1bc1fc8ef8dff1 0x79fd3fd9ff9cfe0b 0x679fd3fd9ff9cfe0

def z336 : W := mkw 0x0000100001090000 0x0000010000109000 0x00000000079f0007 0x000000000079f000

def z337 : W := mkw 0x02ffec307e72a08c 0xf02ffec307e72a08 0x13fac8207860c0c0 0x013fac8207860c0c

def z338 : W := mkw 0xd29cf048e7af1b18 0xed29cf048e7af1b1 0xee1df4d9879f3f3f 0xfee1df4d9879f3f3

def z339 : W := mkw 0x929cf040e7ab1218 0xe929cf040e7ab121 0x461cf0c187830630 0x5461cf0c18783063

def z340 : W := mkw 0x4263fc38197fa98c 0x74263fc38197fa98 0xbbe3fc38787ff9cf 0xbbbe3fc38787ff9c

def z341 : W := mkw 0x03ffff807f7be40e 0xf03ffff807f7be40 0xfbfffb007fffc007 0x1fbfffb007fffc00

def z342 : W := mkw 0x50001008810d0910 0x050001008810d091 0xac013419801f393f 0xbac013419801f393

def z343 : W := mkw 0x20f7afb70000446f 0x020f7afb70000446 0xfeffffff8000c7f8 0xffeffffff8000c7f

def z344 : W := mkw 0x0008400044220000 0x4000840004422000 0xda1ac8204463c1cd 0xbda1ac8204463c1c

def z345 : W := mkw 0x0200100033590000 0xa020010003359000 0x010000003b9c0002 0x0010000003b9c000

def z346 : W := mkw 0x426b5c387f7fa984 0xf426b5c387f7fa98 0xb9e30c387ffff9cf 0xab9e30c387ffff9c

def z347 : W := mkw 0x83ffbfc07fd9f60e 0xb83ffbfc07fd9f60 0x79fd3fc07f9cfe0b 0x679fd3fc07f9cfe0

def z348 : W := mkw 0x40200c080804a904 0x140200c080804a90 0xb9e10c18781cf90f 0xab9e10c18781cf90

def z349 : W := mkw 0x81bc0fc06e80f606 0x981bc0fc06e80f60 0x21e404c07f80fe0b 0x021e404c07f80fe0

def z350 : W := mkw 0xd0f7befd818d1b1f 0x0d0f7befd818d1b1 0x20e534d9839c3802 0x020e534d9839c380

def z351 : W := mkw 0x209ce3874422446b 0x4209ce3874422446 0xde1efbe7c463c7fd 0xfde1efbe7c463c7f

def z352 : W := mkw 0x02dfe00076720008 0xe02dfe0007672000 0xbbfbc000787c0007 0x0bbfbc000787c000

def z353 : W := mkw 0x40630ebd1854a987 0x140630ebd1854a98 0xbde30ffff87cf9cf 0xebde30ffff87cf9c

def z354 : W := mkw 0x02dff000777b0008 0xe02dff000777b000 0x21e530007fff0007 0x021e530007fff000

def z355 : W := mkw 0x0043000010500000 0x0004300001050000 0x80030000007c0004 0x080030000007c000

def z356 : W := mkw 0xf008514ac5af5f70 0x4f008514ac5af5f7 0xee1df7df879f3f3f 0xfee1df7df879f3f3

def z357 : W := mkw 0x00f7aeb50000000f 0x000f7aeb50000000 0xfeffffff8403073d 0xffeffffff8403073

def z358 : W := mkw 0xc1bc0fc86e84ff06 0x9c1bc0fc86e84ff0 0xf9fd0fd87f9cff0f 0xef9fd0fd87f9cff0

def z359 : W := mkw 0x00dfe00044220008 0x400dfe0004422000 0xfafff00044630005 0x1fafff0004463000

def z360 : W := mkw 0x50001008810d0910 0x050001008810d091 0xec0534d9801f0134 0xfec0534d9801f013

def z361 : W := mkw 0x4243f038117f0988 0x64243f038117f098 0x8203f038007f01c4 0x98203f038007f01c

def z362 : W := mkw 0xd0001048818d1b10 0x0d0001048818d1b1 0xec0534d9839c3802 0xfec0534d9839c380

def z363 : W := mkw 0xd0001048818d1b10 0x0d0001048818d1b1 0x680534d9879c3e0b 0x6680534d9879c3e0

def z364 : W := mkw 0x919c13c0e7895612 0x8919c13c0e789561 0x441c33c187830630 0x5441c33c18783063

def z365 : W := mkw 0x009c000066000000 0x8009c00006600000 0x401c000007800000 0x0401c00000780000

def z366 : W := mkw 0x90f7bef58189121f 0x090f7bef58189121 0xfeffffff87830630 0xffeffffff8783063

def z367 : W := mkw 0xd1081148ef8dff10 0x9d1081148ef8dff1 0x010000007f9fff3f 0x0010000007f9fff3

def z368 : W := mkw 0xc10801487ed4ff80 0x9c10801487ed4ff8 0x010000007ffcffcf 0x0010000007ffcffc

def z369 : W := mkw 0x0000000000000000 0x0000000000000000 0x39e0000078000003 0x039e000007800000

def z370 : W := mkw 0x81bc0fc06e80f606 0x981bc0fc06e80f60 0x401c0fc00780fe08 0x6401c0fc00780fe0

def z371 : W := mkw 0xd0001048818d1b10 0x0d0001048818d1b1 0x200534d9879f3f3f 0x0200534d9879f3f3

def z372 : W := mkw 0x81bc0fc06e80f606 0x981bc0fc06e80f60 0x31fc0fc07b80f802 0x031fc0fc07b80f80

def z373 : W := mkw 0x40f70eb81854a986 0x140f70eb81854a98 0xf9ff0ff8787cf9cf 0xef9ff0ff8787cf9c

def z374 : W := mkw 0x00f7aeb50000000f 0x000f7aeb50000000 0x24e53fff80000000 0xe24e53fff8000000

def z375 : W := mkw 0x0043000000000000 0x0004300000000000 0xb8e3000000000000 0x0b8e300000000000

def z376 : W := mkw 0x50f7bebd810d091f 0x050f7bebd810d091 0xfeffffff801f0134 0xffeffffff801f013

def z377 : W := mkw 0x2043e03700220069 0x42043e0370022006 0x8603f03f806301f4 0x98603f03f806301f

def z378 : W := mkw 0x2008410244224460 0x4200841024422446 0xde1ac30644630635 0x5de1ac3064463063

def z379 : W := mkw 0x0008410044224400 0x4000841004422440 0xda1acb004463c60d 0x7da1acb004463c60

def z380 : W := mkw 0x02fffeb5672b000f 0xe02fffeb5672b000 0xfeffffff87830000 0xffeffffff8783000

def z381 : W := mkw 0x81bc0fc06e80f606 0x981bc0fc06e80f60 0xfffecfe67f80fe0b 0xffffecfe67f80fe0

def z382 : W := mkw 0x229cf102672b4468 0xe229cf102672b446 0xde1efb2647e3c7fd 0xfde1efb2647e3c7f

def z383 : W := mkw 0x4000000800040900 0x0400000080004090 0x00000000001c390f 0x000000000001c390

def z384 : W := mkw 0xa1bc4fc26ea2f666 0xda1bc4fc26ea2f66 0x7ffccfc67f83fe3b 0x77ffccfc67f83fe3

def z385 : W := mkw 0xd0001048818d1b10 0x0d0001048818d1b1 0xc40530d9879f0734 0xdc40530d9879f073

def z386 : W := mkw 0x4000000800040900 0x0400000080004090 0x80010018001c0104 0x880010018001c010

def z387 : W := mkw 0x00f7aeb50000000f 0x000f7aeb50000000 0x96fbfb3f80000000 0x996fbfb3f8000000

def z388 : W := mkw 0x2008410244224460 0x4200841024422446 0x8602c0264463c7fd 0x98602c0264463c7f

def z389 : W := mkw 0x02085000777b0000 0xe02085000777b000 0xe90530007fff0007 0x1e90530007fff000

def z390 : W := mkw 0x01bc0f806e00e406 0x901bc0f806e00e40 0x79fc0b007f80c003 0x079fc0b007f80c00

def z391 : W := mkw 0x2000400200220060 0x4200040020022006 0x0202c026006000c0 0x00202c026006000c

def z392 : W := mkw 0x91bc1fc0ef89f616 0x991bc1fc0ef89f61 0x7dfc3fc1ff83fe3b 0x77dfc3fc1ff83fe3

def z393 : W := mkw 0x20dfe10244224468 0x420dfe1024422446 0xfefffb264463c7fd 0xffefffb264463c7f

def z394 : W := mkw 0x81bc0fc06e80f606 0x981bc0fc06e80f60 0xf9fe0fe07fe0ffcf 0xef9fe0fe07fe0ffc

def z395 : W := mkw 0x52dff008f77f0918 0xe52dff008f77f091 0xfffff019ffff0137 0x9fffff019ffff013

def z396 : W := mkw 0x029cf285672b000b 0xe029cf285672b000 0x461cf3c787830000 0x5461cf3c78783000

def z397 : W := mkw 0x2008410244224460 0x4200841024422446 0xde1acb2604030630 0xfde1acb260403063

def z398 : W := mkw 0xd0b41ec8818d1b16 0x0d0b41ec8818d1b1 0xfcfd3fd9879f3f3f 0xffcfd3fd9879f3f3

def z399 : W := mkw 0x2000000200000060 0x0200000020000006 0x04000026000001f0 0x804000026000001f

def z400 : W := mkw 0xc0630c7818d4bb84 0x1c0630c7818d4bb8 0xf9e70cf87ffcffcf 0xef9e70cf87ffcffc

def z401 : W := mkw 0x00b40e800800a006 0x100b40e800800a00 0x79fc0fc07800f80b 0x679fc0fc07800f80

def z402 : W := mkw 0x81280d406e80f604 0x981280d406e80f60 0x39e00c007f80fe0b 0x239e00c007f80fe0

def z403 : W := mkw 0x02fffeb5777b000f 0xe02fffeb5777b000 0xfbfffb267fff0007 0x1fbfffb267fff000

def z404 : W := mkw 0xc3fffff87fffff8e 0xfc3fffff87fffff8 0xfbfffff87fffffcf 0xffbfffff87fffffc

def z405 : W := mkw 0x024bf000557b0008 0x6024bf000557b000 0xda1bf000447f0005 0x1da1bf000447f000

def z406 : W := mkw 0x00b4ae850000000f 0x000b4ae850000000 0x7efcffc780000000 0x77efcffc78000000

def z407 : W := mkw 0x02dff285777b000b 0xe02dff285777b000 0xfffff3c7ffff0007 0x5fffff3c7ffff000

def z408 : W := mkw 0x0000000000000000 0x0000000000000000 0x4618c30600000000 0x54618c3060000000

def z409 : W := mkw 0x204be13744224469 0x4204be1374422446 0xde1bfb3fc463c7fd 0xfde1bfb3fc463c7f

def z410 : W := mkw 0x004b400054720000 0x4004b40005472000 0xfbfbc0007c7f0007 0x1fbfbc0007c7f000

def z411 : W := mkw 0x0000000000000000 0x0000000000000000 0x04000b2600000000 0xe04000b260000000

def z412 : W := mkw 0x209ce3874422446b 0x4209ce3874422446 0x461cf3c784030630 0x5461cf3c78403063

def z413 : W := mkw 0x810801406e80f600 0x9810801406e80f60 0x690404c07f80fe0b 0x6690404c07f80fe0

def z414 : W := mkw 0xd0081148c58d5f10 0x0d0081148c58d5f1 0xfc1d3fd9c79fff3f 0xffc1d3fd9c79fff3

def z415 : W := mkw 0x83fffec07ffbb20e 0xf83fffec07ffbb20 0xfbfff4c07fff3807 0x1fbfff4c07fff380

def z416 : W := mkw 0x00f7aeb50800a00f 0x100f7aeb50800a00 0xfffffffff800f80b 0xffffffffff800f80

def z417 : W := mkw 0xd0631c78818d1b14 0x0d0631c78818d1b1 0xfce73cf9879f3f3f 0xffce73cf9879f3f3

def z418 : W := mkw 0xd0001048818d1b10 0x0d0001048818d1b1 0x84013019879f3f3f 0x984013019879f3f3

def z419 : W := mkw 0x40630c381854a984 0x140630c381854a98 0xb9e30418787c3807 0x0b9e30418787c380

def z420 : W := mkw 0x0008010044004400 0x0000801004400440 0xd81a0b204460c7cd 0xed81a0b204460c7c

def z421 : W := mkw 0x81ffaff56e80f60f 0x981ffaff56e80f60 0x79fd3fd9ff80fe0b 0x679fd3fd9ff80fe0

def z422 : W := mkw 0xd0001048818d1b10 0x0d0001048818d1b1 0x440430c1879f3f3f 0x5440430c1879f3f3

def z423 : W := mkw 0x40001008010d0900 0x040001008010d090 0xe8053418079f390f 0xbe8053418079f390

def z424 : W := mkw 0x2000010200004460 0x0200001020000446 0xcc000b260403c7fd 0xfcc000b260403c7f

def z425 : W := mkw 0x4000000800040900 0x0400000080004090 0xec0534d9801c390f 0xfec0534d9801c390

def z426 : W := mkw 0x81ffaff56680560f 0x881ffaff56680560 0xfeffffff87800600 0xffeffffff8780060

def z427 : W := mkw 0x02fffc30777b000c 0xe02fffc30777b000 0xfbfffc387fff0007 0xbfbfffc387fff000

def z428 : W := mkw 0x819c03c06e80f602 0x9819c03c06e80f60 0x411c03c07f80fe0b 0x4411c03c07f80fe0

def z429 : W := mkw 0x22dff102777b4468 0xe22dff102777b446 0xfffff3067fff0637 0x5fffff3067fff063

def z430 : W := mkw 0x2000400200220060 0x4200040020022006 0x0600c00600030030 0x10600c0060003003

def z431 : W := mkw 0x40f7aebd1854a98f 0x140f7aebd1854a98 0x21e534d9b81c3802 0x021e534d9b81c380

def z432 : W := mkw 0x02dff000777b0008 0xe02dff000777b000 0xfffff4d9ffff0007 0xffffff4d9ffff000

def z433 : W := mkw 0x20085102452b4460 0x420085102452b446 0xfe1ffb2647ffc7ff 0xffe1ffb2647ffc7f

def z434 : W := mkw 0x00630c301850a084 0x100630c301850a08 0xb9e30820787cc0c7 0x0b9e30820787cc0c

def z435 : W := mkw 0x20ffefb74422446f 0x420ffefb74422446 0xfeffffff84030630 0xffeffffff8403063

def z436 : W := mkw 0x40200c081854a984 0x140200c081854a98 0x39e00c00787cf9cf 0x239e00c00787cf9c

def z437 : W := mkw 0x80b40ec000801206 0x080b40ec00080120 0x78fc0fc007803e0b 0x678fc0fc007803e0

def z438 : W := mkw 0x406b0d385c54ed84 0x1406b0d385c54ed8 0xf9fb0f387c7cffcf 0xef9fb0f387c7cffc

def z439 : W := mkw 0x0094028000000002 0x0009402800000000 0x401c03c000000000 0x4401c03c00000000

def z440 : W := mkw 0x02dff000777b0008 0xe02dff000777b000 0x13fac0007fff0007 0x013fac0007fff000

def z441 : W := mkw 0x00ffeeb54422000f 0x400ffeeb54422000 0xfeffffffc4630005 0xffeffffffc463000

def z442 : W := mkw 0x5000000880040910 0x0500000088004091 0x0400001980000130 0x8040000198000013

def z443 : W := mkw 0x81bc0fc06e80f606 0x981bc0fc06e80f60 0x11f80fc07800fe08 0x611f80fc07800fe0

def z444 : W := mkw 0x010801006e00e400 0x9010801006e00e40 0x010000007800c000 0x0010000007800c00

def z445 : W := mkw 0xd000004880841b10 0x0d000004880841b1 0x000004d980003800 0x0000004d98000380

def z446 : W := mkw 0x9000104081891210 0x0900010408189121 0x6c0434c187833e3b 0x76c0434c187833e3

def z447 : W := mkw 0x02dfe00076720008 0xe02dfe0007672000 0xfbfff00078600000 0x1fbfff0007860000

def z448 : W := mkw 0x00f7aeb50000000f 0x000f7aeb50000000 0xfafff4d980000000 0x1fafff4d98000000

def z449 : W := mkw 0x00f7aeb50000000f 0x000f7aeb50000000 0xb8e73cf980000000 0xab8e73cf98000000

def z450 : W := mkw 0x00b40e8000000006 0x000b40e800000000 0x20e404c000000000 0x020e404c00000000

def z451 : W := mkw 0x40630c381854a984 0x140630c381854a98 0xfde73cf9f87cf9cf 0xffde73cf9f87cf9c

def z452 : W := mkw 0x229cf102672b4468 0xe229cf102672b446 0x461cf30607830630 0x5461cf3060783063

def z453 : W := mkw 0xf2dff14af7ff5f78 0xef2dff14af7ff5f7 0xffffffffffffffff 0xffffffffffffffff

def z454 : W := mkw 0xf000014a80845f70 0x0f000014a80845f7 0x04000fff8000fff8 0xe04000fff8000fff

def z455 : W := mkw 0xd1200fc88884ff16 0x1d1200fc88884ff1 0x04000fd98000ff38 0xe04000fd98000ff3

def z456 : W := mkw 0x01b40e802a00a006 0x901b40e802a00a00 0x01e0000038000000 0x001e000003800000

def z457 : W := mkw 0xd043b07d818d1b19 0x0d043b07d818d1b1 0xee07f4ff879f3f3f 0xfee07f4ff879f3f3

def z458 : W := mkw 0x406b4c385c76a984 0x5406b4c385c76a98 0xfbfbcc387c7ff9cf 0xbfbfbcc387c7ff9c

def z459 : W := mkw 0xd0201c78898dbb94 0x1d0201c78898dbb9 0xec053cf9879fffff 0xfec053cf9879ffff

def z460 : W := mkw 0x00b40e8000000006 0x000b40e800000000 0xfcfd3fd980000000 0xffcfd3fd98000000

def z461 : W := mkw 0x400000081854a980 0x1400000081854a98 0xa9010418787cf9cf 0xaa9010418787cf9c

def z462 : W := mkw 0x4043003810540980 0x0404300381054098 0xb9e30038787c01c7 0x8b9e30038787c01c

def z463 : W := mkw 0x00200eb500000007 0x000200eb50000000 0x000004d980000000 0x0000004d98000000

def z464 : W := mkw 0x404300081854a980 0x1404300081854a98 0xb9e30000787cf9cf 0x0b9e30000787cf9c

def z465 : W := mkw 0xd3ffffc8ffffff1e 0xfd3ffffc8ffffff1 0xffffffd9ffffff3f 0xfffffffd9ffffff3

def z466 : W := mkw 0x81bc0fc06e80f606 0x981bc0fc06e80f60 0x61fc07c03f803e02 0x461fc07c03f803e0

def z467 : W := mkw 0x40630c381854a984 0x140630c381854a98 0xa9e10418381c390f 0xaa9e10418381c390

def z468 : W := mkw 0x00f7aeb51850a08f 0x100f7aeb51850a08 0xfffffffff860c0c0 0xffffffffff860c0c

def z469 : W := mkw 0xd0001048818d1b10 0x0d0001048818d1b1 0xe8053000079f3f3f 0x1e8053000079f3f3

def z470 : W := mkw 0x0000a00500000009 0x00000a0050000000 0x0600f00780000000 0x10600f0078000000

def z471 : W := mkw 0x000000000800a000 0x1000000000800a00 0x010000007800f80b 0x0010000007800f80

def z472 : W := mkw 0x00280d004c00e404 0x100280d004c00e40 0x79f80f007c00fe0b 0x679f80f007c00fe0

def z473 : W := mkw 0xd2dff048f7ff1b18 0xed2dff048f7ff1b1 0xfbfff4d9ffff3807 0x1fbfff4d9ffff380

def z474 : W := mkw 0x02dff035777b0009 0xe02dff035777b000 0xfffff03fffff0007 0x9fffff03fffff000

def z475 : W := mkw 0x0000100001090000 0x0000010000109000 0x4004300007830000 0x1400430000783000

def z476 : W := mkw 0x00f7ae800000000e 0x000f7ae800000000 0xfaffffc000000000 0x7faffffc00000000

def z477 : W := mkw 0x4000000810540980 0x0400000081054098 0x00000000007c01c4 0x000000000007c01c

def z478 : W := mkw 0x20f7eeb70022006f 0x420f7eeb70022006 0xfeffffff806301f4 0xffeffffff806301f

def z479 : W := mkw 0x2008410244224460 0x4200841024422446 0xda1ac0004463c7fd 0x1da1ac0004463c7f

def z480 : W := mkw 0x02dfe00076720008 0xe02dfe0007672000 0xdbfac0007c630005 0x1dbfac0007c63000

def z481 : W := mkw 0x2000400200220060 0x4200040020022006 0xce02c026046307fd 0xfce02c026046307f

def z482 : W := mkw 0x6008410a5c76ede0 0x56008410a5c76ede 0xdf1acb267c7fffff 0xfdf1acb267c7ffff

def z483 : W := mkw 0x50001008810d0910 0x050001008810d091 0xec053019879f0137 0x9ec053019879f013

def z484 : W := mkw 0xa1bc0fc26e80f666 0x9a1bc0fc26e80f66 0x7dfc0fe67f80fffb 0xe7dfc0fe67f80fff

def z485 : W := mkw 0x02fffeb5777b000f 0xe02fffeb5777b000 0xfbfff4d9ffff0007 0x1fbfff4d9ffff000

def z486 : W := mkw 0x0243f035117b0009 0x60243f035117b000 0x8603f03f807f0004 0x98603f03f807f000

def z487 : W := mkw 0x0243e00010720008 0x60243e0001072000 0x0202c00000600000 0x00202c0000060000

def z488 : W := mkw 0x0094a2850000000b 0x00094a2850000000 0x000430c180000000 0x0000430c18000000

def z489 : W := mkw 0x40630c3810540984 0x040630c381054098 0xb8e30c38007c01c4 0xab8e30c38007c01c

def z490 : W := mkw 0x60284d3a4c26ede4 0x560284d3a4c26ede 0xde1acf3e4463fffd 0xfde1acf3e4463fff

def z491 : W := mkw 0x2000410200224460 0x4200041020022446 0x8602cb260063c7fc 0xf8602cb260063c7f

def z492 : W := mkw 0x206b4d325c72e4e4 0x5206b4d325c72e4e 0xdffacb267c63c7fd 0xfdffacb267c63c7f

def z493 : W := mkw 0x60630d3a1854ede4 0x160630d3a1854ede 0xbde30f3e787cffff 0xebde30f3e787cfff

def z494 : W := mkw 0x0008010044004400 0x0000801004400440 0x10180b004000c000 0x010180b004000c00

def z495 : W := mkw 0x02005000117b0000 0x602005000117b000 0x00000000007f0004 0x000000000007f000

def z496 : W := mkw 0x01bc0f806e00e406 0x901bc0f806e00e40 0x39f80f007800f80b 0x239f80f007800f80

def z497 : W := mkw 0xd2fffefdf7ff1b1f 0xed2fffefdf7ff1b1 0xffffffffffff3f3f 0xfffffffffffff3f3

def z498 : W := mkw 0xd0001048818d1b10 0x0d0001048818d1b1 0x680404c0079f3f3f 0x6680404c0079f3f3

def z499 : W := mkw 0xd0200efd80841b17 0x0d0200efd80841b1 0x04000fff80003f38 0xe04000fff80003f3

def z500 : W := mkw 0x0094a2850000000b 0x00094a2850000000 0xde1efbe780000000 0xfde1efbe78000000

def z501 : W := mkw 0x02d7b00033590008 0xa02d7b0003359000 0xfbfff0003b9c0002 0x1fbfff0003b9c000

def z502 : W := mkw 0x81bc0fc066805606 0x881bc0fc06680560 0x78fc0fc007800600 0x678fc0fc00780060

def z503 : W := mkw 0x209c410266224460 0xc209c41026622446 0xfffecb267fe3c7ff 0xffffecb267fe3c7f

def z504 : W := mkw 0x00f7aeb50000000f 0x000f7aeb50000000 0xfafffb2600000000 0x1fafffb260000000

def z505 : W := mkw 0xc1f70ef83ad4bb86 0x9c1f70ef83ad4bb8 0xb9e70cf87bfcf9cf 0xab9e70cf87bfcf9c

def z506 : W := mkw 0x00f7aeb50000000f 0x000f7aeb50000000 0xbafbcf3e00000000 0xabafbcf3e0000000

def z507 : W := mkw 0x20ffefb74422446f 0x420ffefb74422446 0x12facb264060c0c0 0x012facb264060c0c

def z508 : W := mkw 0x2000400200220060 0x4200040020022006 0x00000000006301f4 0x000000000006301f

def z509 : W := mkw 0x0000000000000000 0x0000000000000000 0x180008004000c009 0x2180008004000c00

def z510 : W := mkw 0x0000000000000000 0x0000000000000000 0x880000000000010d 0xa880000000000010

def z511 : W := mkw 0x42fffebd7f7fa98f 0xf42fffebd7f7fa98 0xfffffffffffff9cf 0xffffffffffffff9c

def z512 : W := mkw 0x83bc5fc07ffbf606 0xf83bc5fc07ffbf60 0x79fc0fc07ffffe0f 0x679fc0fc07ffffe0

def z513 : W := mkw 0x81ffaff56e80f60f 0x981ffaff56e80f60 0x7bfecfe67f80fe0b 0x67bfecfe67f80fe0

def z514 : W := mkw 0x0000000000000000 0x0000000000000000 0x0400000000000738 0xe040000000000073

def z515 : W := mkw 0xd0001048818d1b10 0x0d0001048818d1b1 0x440434d987833f38 0xf440434d987833f3

def z516 : W := mkw 0xd09c1048e78d1b10 0x8d09c1048e78d1b1 0xfdfd34d9ff9f3f3f 0xffdfd34d9ff9f3f3

def z517 : W := mkw 0x22085102777b4460 0xe22085102777b446 0xdf1acb267fffc7ff 0xfdf1acb267fffc7f

def z518 : W := mkw 0x0000000000000000 0x0000000000000000 0x8401301980000000 0x9840130198000000

def z519 : W := mkw 0x60634c3a1876a9e4 0x560634c3a1876a9e 0xbfe3cc3e787ff9ff 0xbbfe3cc3e787ff9f

def z520 : W := mkw 0x4043003810540980 0x0404300381054098 0x98030838407cc1cd 0xa98030838407cc1c

def z521 : W := mkw 0x810801406e80f600 0x9810801406e80f60 0x59180b007f80fe0b 0x659180b007f80fe0

def z522 : W := mkw 0x4043003810540980 0x0404300381054098 0xa8030438007c39cf 0xaa8030438007c39c

def z523 : W := mkw 0x42dff0087f7fa988 0xf42dff0087f7fa98 0xfbfff0007ffff9cf 0x1fbfff0007ffff9c

def z524 : W := mkw 0x819402c022801202 0x8819402c02280120 0x000400c003800000 0x0000400c00380000

def z525 : W := mkw 0x2008410244224460 0x4200841024422446 0x121acb264463c7fd 0x0121acb264463c7f

def z526 : W := mkw 0x8008014044805600 0x0800801404480560 0x781c0fc04780fe0b 0x6781c0fc04780fe0

def z527 : W := mkw 0x2000400200220060 0x4200040020022006 0x9e02c8264063c1fd 0xb9e02c8264063c1f

def z528 : W := mkw 0x00b40e8000000006 0x000b40e800000000 0x10f80b0000000000 0x010f80b000000000

def z529 : W := mkw 0x00dfa00066000008 0x800dfa0006600000 0xfbfff0007f800003 0x1fbfff0007f80000

def z530 : W := mkw 0x00630eb500000007 0x000630eb50000000 0xbce30fff80000000 0xebce30fff8000000

def z531 : W := mkw 0x0200f000012b0008 0x60200f000012b000 0x0200f00000030000 0x10200f0000003000

def z532 : W := mkw 0x6008410a5c76ede0 0x56008410a5c76ede 0x010000007c7fffff 0x0010000007c7ffff

def z533 : W := mkw 0x0043a00000000008 0x00043a0000000000 0x8203f00000000000 0x18203f0000000000

def z534 : W := mkw 0x4043a03d10540989 0x04043a03d1054098 0x8603f03f807c01c4 0x98603f03f807c01c

def z535 : W := mkw 0xa1bc4fc26ea2f666 0xda1bc4fc26ea2f66 0x7bfecfe67fe0fecb 0x67bfecfe67fe0fec

def z536 : W := mkw 0x00ffafb54400440f 0x000ffafb54400440 0xfeffffffc400c609 0xffeffffffc400c60

def z537 : W := mkw 0x01ffafb56e00e40f 0x901ffafb56e00e40 0x13facb267800c000 0x013facb267800c00

def z538 : W := mkw 0x0008400044220000 0x4000840004422000 0x0000000044630005 0x0000000004463000

def z539 : W := mkw 0xd000004880841b10 0x0d000004880841b1 0xac0104d9801c3f3f 0xeac0104d9801c3f3

def z540 : W := mkw 0x0008010044004400 0x0000801004400440 0xdc180b004403c73d 0xfdc180b004403c73

def z541 : W := mkw 0x2008410244224460 0x4200841024422446 0x0000000004030630 0x0000000000403063

def z542 : W := mkw 0x81ff0fc07ed0f606 0x981ff0fc07ed0f60 0xf9ff0fc07ffcfe0f 0x6f9ff0fc07ffcfe0

def z543 : W := mkw 0x02f7feb5117b000f 0x602f7feb5117b000 0xfeffffff807f0004 0xffeffffff807f000

def z544 : W := mkw 0x6043403a107609e0 0x46043403a107609e 0x8603c03e007f01f4 0x98603c03e007f01f

def z545 : W := mkw 0x83f7bec03bd9b20e 0xb83f7bec03bd9b20 0x21e534c03b9c3802 0x021e534c03b9c380

def z546 : W := mkw 0x40f7aebd1854a98f 0x140f7aebd1854a98 0xffffffffb81c3802 0xfffffffffb81c380

def z547 : W := mkw 0x0008400044220000 0x4000840004422000 0xde1acb2644630005 0xfde1acb264463000

def z548 : W := mkw 0xd0f7aefd80841b1f 0x0d0f7aefd80841b1 0xfeffffff80003f38 0xffeffffff80003f3

def z549 : W := mkw 0x0043a03500000009 0x00043a0350000000 0xde1bfb3f80000000 0xfde1bfb3f8000000

def z550 : W := mkw 0x50001008810d0910 0x050001008810d091 0xcc013019841f073d 0xfcc013019841f073

def z551 : W := mkw 0x81ff0ff06e80f606 0x981ff0ff06e80f60 0xf9ff0ff87f80fe0b 0xef9ff0ff87f80fe0

def z552 : W := mkw 0x8000004000801200 0x0800000400080120 0x000004c000003e08 0x6000004c000003e0

def z553 : W := mkw 0x00d7a2850000000b 0x000d7a2850000000 0xfefff3c780000000 0x5fefff3c78000000

def z554 : W := mkw 0x00f7aeb50000000f 0x000f7aeb50000000 0xdefacb2600000000 0xfdefacb260000000

def z555 : W := mkw 0x819c03c066805602 0x8819c03c06680560 0x79fc03c07f800603 0x479fc03c07f80060

def z556 : W := mkw 0xd1b41ec8ab8dbb16 0x9d1b41ec8ab8dbb1 0x21e534d9bb9c3802 0x021e534d9bb9c380

def z557 : W := mkw 0xd0631c7899ddbb94 0x1d0631c7899ddbb9 0xede534d9bf9f3f3f 0xfede534d9bf9f3f3

def z558 : W := mkw 0x81280fc06e80f606 0x981280fc06e80f60 0x01000fc07f80fe0b 0x601000fc07f80fe0

def z559 : W := mkw 0xc16b0d787ed4ff84 0x9c16b0d787ed4ff8 0xb9e30c387ffcffcf 0xab9e30c387ffcffc

def z560 : W := mkw 0x0000400000220000 0x4000040000022000 0x8202c00000630004 0x18202c0000063000

def z561 : W := mkw 0x03ffef807e72e40e 0xf03ffef807e72e40 0x13facb007860c000 0x013facb007860c00

def z562 : W := mkw 0xc000004800841b00 0x0c000004800841b0 0xe80504d8079c3f0f 0xee80504d8079c3f0

def z563 : W := mkw 0xd043107891dd1b90 0x0d043107891dd1b9 0xec0734f987ff3fff 0xfec0734f987ff3ff

def z564 : W := mkw 0x00630c301850a084 0x100630c301850a08 0xb9e30c387860c0c0 0xab9e30c387860c0c

def z565 : W := mkw 0x40630c381854a984 0x140630c381854a98 0x11e20c387860f9c8 0xa11e20c387860f9c

def z566 : W := mkw 0x40200c380804a984 0x140200c380804a98 0xa8010c38001cf9cf 0xaa8010c38001cf9c

def z567 : W := mkw 0x9000104081891210 0x0900010408189121 0xec0534d987830630 0xfec0534d98783063

def z568 : W := mkw 0x224bf102557b4468 0x6224bf102557b446 0xde1bfb26447fc7fd 0xfde1bfb26447fc7f

def z569 : W := mkw 0x00200c000800a004 0x100200c000800a00 0xb9e20c207860f9cf 0xab9e20c207860f9c

def z570 : W := mkw 0xd19c13c8e78d5f12 0x8d19c13c8e78d5f1 0xec1d37d9879f3f3f 0xfec1d37d9879f3f3

def z571 : W := mkw 0x0094a2850000000b 0x00094a2850000000 0xee1df7df80000000 0xfee1df7df8000000

def z572 : W := mkw 0x00630c3000000004 0x000630c300000000 0xb8e30c384060c1cd 0xab8e30c384060c1c

def z573 : W := mkw 0xf000504a81af1b70 0x4f000504a81af1b7 0xee07f4ff87ff3fff 0xfee07f4ff87ff3ff

def z574 : W := mkw 0x81b40fc00880f606 0x181b40fc00880f60 0x78fc0fc00000fe08 0x678fc0fc00000fe0

def z575 : W := mkw 0xa19c43c266a25662 0xca19c43c266a2566 0x461cc3c607830630 0x5461cc3c60783063

def z576 : W := mkw 0x00f7ac300000000c 0x000f7ac300000000 0xfafffc3800000000 0xbfafffc380000000

def z577 : W := mkw 0x01bc0f806e00e406 0x901bc0f806e00e40 0x59f80b007c00c609 0x659f80b007c00c60

def z578 : W := mkw 0x83fffff57ffbf60f 0xf83fffff57ffbf60 0xfffffffffffffe0f 0xffffffffffffffe0

def z579 : W := mkw 0xd0f7befd818d1b1f 0x0d0f7befd818d1b1 0xece534d9879f3f3f 0xfece534d9879f3f3

def z580 : W := mkw 0x0000100001090000 0x0000010000109000 0xec053000079f073f 0xfec053000079f073

def z581 : W := mkw 0x0008400044220000 0x4000840004422000 0x4218c00004030000 0x14218c0000403000

def z582 : W := mkw 0x0000000000000000 0x0000000000000000 0x280004000000380b 0x2280004000000380

def z583 : W := mkw 0xd0001048818d1b10 0x0d0001048818d1b1 0x00000000039c3802 0x000000000039c380

def z584 : W := mkw 0xd0d7b048818d1b18 0x0d0d7b048818d1b1 0xfefff4d9879f3f3f 0xffefff4d9879f3f3

def z585 : W := mkw 0x00630c3010500004 0x000630c301050000 0xb9e30c38787c0007 0xab9e30c38787c000

def z586 : W := mkw 0x8000104001891200 0x0800010400189120 0xe80534c0079f3e0f 0x7e80534c0079f3e0

def z587 : W := mkw 0x0243f000117b0008 0x60243f000117b000 0xea07f00007ff0007 0x1ea07f00007ff000

def z588 : W := mkw 0x20bc4f8244224466 0x420bc4f824422446 0xfefecfe64463c7fd 0xffefecfe64463c7f

def z589 : W := mkw 0x0008400044220000 0x4000840004422000 0x121ac00040600000 0x0121ac0004060000

def z590 : W := mkw 0x02dff000777b0008 0xe02dff000777b000 0x53fef0007fe30000 0x153fef0007fe3000

def z591 : W := mkw 0x00200c300800a084 0x100200c300800a08 0x000008200000c0c0 0x0000008200000c0c

def z592 : W := mkw 0x0000000000000000 0x0000000000000000 0x80020020006001c4 0x880020020006001c

def z593 : W := mkw 0x0000000000000000 0x0000000000000000 0x100208204060c0c0 0x0100208204060c0c

def z594 : W := mkw 0x1000100081090010 0x0100010008109001 0x0400300180030030 0x1040030018003003

def z595 : W := mkw 0x009c100067090000 0x8009c10006709000 0xf9fd30007f9f0007 0x1f9fd30007f9f000

def z596 : W := mkw 0xd000004880841b10 0x0d000004880841b1 0xec0534d980003f38 0xfec0534d980003f3

def z597 : W := mkw 0x00630c3000000004 0x000630c300000000 0xfce73cf980000000 0xffce73cf98000000

def z598 : W := mkw 0x00630c301850a084 0x100630c301850a08 0x99e208207860c1cd 0xa99e208207860c1c

def z599 : W := mkw 0x81ffafc06e80f60e 0x981ffafc06e80f60 0xfbffffc07f80fe0b 0x7fbffffc07f80fe0

def z600 : W := mkw 0x21bc4f826e22e466 0xd21bc4f826e22e46 0xdffacb267c63c7fd 0xfdffacb267c63c7f

def z601 : W := mkw 0xd0001048818d1b10 0x0d0001048818d1b1 0x040004d9879f3f3f 0xe040004d9879f3f3

def z602 : W := mkw 0xa19c43c266a25662 0xca19c43c266a2566 0xde1ecbe647e3c7fd 0xfde1ecbe647e3c7f

def z603 : W := mkw 0x2008410244224460 0x4200841024422446 0x04000b264463c7fd 0xe04000b264463c7f

def z604 : W := mkw 0x2008410244224460 0x4200841024422446 0x4618c3064463c7fd 0x54618c3064463c7f

def z605 : W := mkw 0x00200eb500000007 0x000200eb50000000 0xec053fff80000000 0xfec053fff8000000

def z606 : W := mkw 0x00b40e8000000006 0x000b40e800000000 0xfefecfe600000000 0xffefecfe60000000

def z607 : W := mkw 0x00d7a00010500008 0x000d7a0001050000 0xfbfff000787c0007 0x1fbfff000787c000

def z608 : W := mkw 0x2000010200004460 0x0200001020000446 0x9c020b264060c7fd 0xe9c020b264060c7f

def z609 : W := mkw 0x5043b03d810d0919 0x05043b03d810d091 0x8603f03f801f0134 0x98603f03f801f013

def z610 : W := mkw 0x40200ebd0804a987 0x140200ebd0804a98 0x04000fff8000f9c8 0xe04000fff8000f9c

def z611 : W := mkw 0x2008410244224460 0x4200841024422446 0x000000004060c0c0 0x0000000004060c0c

def z612 : W := mkw 0x009c000066000000 0x8009c00006600000 0x11f8000078000000 0x011f800007800000

def z613 : W := mkw 0x0000000000000000 0x0000000000000000 0xe805300000000000 0x1e80530000000000

def z614 : W := mkw 0x02dff000672b0008 0xe02dff000672b000 0xfafff00007830000 0x1fafff0000783000

def z615 : W := mkw 0x40631c38195da984 0x140631c38195da98 0xf9e73c387ffff9cf 0xbf9e73c387ffff9c

def z616 : W := mkw 0x0000000000000000 0x0000000000000000 0xa801041800000000 0xaa80104180000000

def z617 : W := mkw 0xd0f7befd99ddbb9f 0x1d0f7befd99ddbb9 0xffffffffffffffff 0xffffffffffffffff

def z618 : W := mkw 0x00d7a00000000008 0x000d7a0000000000 0xfefff4d980000000 0xffefff4d98000000

def z619 : W := mkw 0x00f7aeb50000000f 0x000f7aeb50000000 0xa6e7f4ff80000000 0x9a6e7f4ff8000000

def z620 : W := mkw 0x02dff000777b0008 0xe02dff000777b000 0xc21ff00007ff0004 0x1c21ff00007ff000

def z621 : W := mkw 0x02ffeeb57672000f 0xe02ffeeb57672000 0x13facb2678600000 0x013facb267860000

def z622 : W := mkw 0x02085000672b0000 0xe02085000672b000 0x0000000007830000 0x0000000000783000

def z623 : W := mkw 0xd0201c48898dbb14 0x1d0201c48898dbb1 0xfde53cd9ff9fff3f 0xffde53cd9ff9fff3

def z624 : W := mkw 0x0094000000000000 0x0009400000000000 0x78fc000000000000 0x078fc00000000000

def z625 : W := mkw 0xc1bc0fc87ed4ff86 0x9c1bc0fc87ed4ff8 0x79fc0fc07ffcffcf 0x679fc0fc07ffcffc

def z626 : W := mkw 0x2008410244224460 0x4200841024422446 0x4618cb260403c7f8 0xf4618cb260403c7f

def z627 : W := mkw 0x83ffefc07ef2f60e 0xf83ffefc07ef2f60 0x7bfecfc07fe0fe0b 0x67bfecfc07fe0fe0

def z628 : W := mkw 0xa1ffeff76ea2f66f 0xda1ffeff76ea2f66 0xffffffffffe3ffff 0xfffffffffffe3fff

def z629 : W := mkw 0x2000010200004460 0x0200001020000446 0xde1acb260000c7f8 0xfde1acb260000c7f

def z630 : W := mkw 0x9000104081891210 0x0900010408189121 0x0000000007830630 0x0000000000783063

def z631 : W := mkw 0xa10841426ea2f660 0xda10841426ea2f66 0xdf1acb267fe3ffff 0xfdf1acb267fe3fff

def z632 : W := mkw 0xa1284fc24ca2f666 0x5a1284fc24ca2f66 0xde1acfe64463fffd 0xfde1acfe64463fff

def z633 : W := mkw 0xd0630c7898d4bb94 0x1d0630c7898d4bb9 0xbde30cf9f87cffff 0xebde30cf9f87cfff

def z634 : W := mkw 0x00f7aeb50000000f 0x000f7aeb50000000 0xece534d980000000 0xfece534d98000000

def z635 : W := mkw 0x2008410244224460 0x4200841024422446 0x9a1acb264060c1cd 0xa9a1acb264060c1c

def z636 : W := mkw 0x2008410244224460 0x4200841024422446 0x980208204463c7fd 0xa980208204463c7f

def z637 : W := mkw 0x7008510ac52f4d70 0x47008510ac52f4d7 0xde1bfb3fc47fc7fd 0xfde1bfb3fc47fc7f

def z638 : W := mkw 0x0008400044220000 0x4000840004422000 0xde1ac0004463073d 0xfde1ac0004463073

def z639 : W := mkw 0x22dfe10276724468 0xe22dfe1027672446 0xdffacb267c63c7fd 0xfdffacb267c63c7f

def z640 : W := mkw 0x00f7aeb50000000f 0x000f7aeb50000000 0x78fd3fd980000000 0x678fd3fd98000000

def z641 : W := mkw 0x83dff3c077fb560a 0xe83dff3c077fb560 0xfbfff3c07fff0607 0x5fbfff3c07fff060

def z642 : W := mkw 0xd2085048f7ff1b10 0xed2085048f7ff1b1 0xed0534d9ffff3f3f 0xfed0534d9ffff3f3

def z643 : W := mkw 0x0000000000000000 0x0000000000000000 0xdc0208204463c7fd 0xfdc0208204463c7f

def z644 : W := mkw 0x20200fb700004467 0x020200fb70000446 0x04000fff8000c7f8 0xe04000fff8000c7f

def z645 : W := mkw 0x81bc1fc06f89f606 0x981bc1fc06f89f60 0xf9fd3fc07f9ffe0f 0x7f9fd3fc07f9ffe0

def z646 : W := mkw 0x02ffeeb57672000f 0xe02ffeeb57672000 0xfffffffff8600000 0xffffffffff860000

def z647 : W := mkw 0x40630c381854a984 0x140630c381854a98 0xa1e30438387c39c6 0x8a1e30438387c39c

def z648 : W := mkw 0x02d7f000117b0008 0x602d7f000117b000 0xfafff000007f0004 0x1fafff000007f000

def z649 : W := mkw 0x42ffec387e76a98c 0xf42ffec387e76a98 0xbbfbcc38787cf9cf 0xabbfbcc38787cf9c

def z650 : W := mkw 0x82dff04077fb1208 0xe82dff04077fb120 0xfbfff4c07fff3e0f 0x7fbfff4c07fff3e0

def z651 : W := mkw 0x00bc0e8066000006 0x800bc0e806600000 0x79fc0fc07f800003 0x679fc0fc07f80000

def z652 : W := mkw 0x00200e8000000006 0x000200e800000000 0x00000fc000000000 0x600000fc00000000

def z653 : W := mkw 0x2008410244224460 0x4200841024422446 0xda1acb264463c0c5 0x1da1acb264463c0c

def z654 : W := mkw 0xd0001048818d1b10 0x0d0001048818d1b1 0xa8010418079f3f3f 0xaa8010418079f3f3

def z655 : W := mkw 0xd1bc1fc8ef8dff16 0x9d1bc1fc8ef8dff1 0x79fc0fc07f9fff3f 0x679fc0fc07f9fff3

def z656 : W := mkw 0xb0085142c5ab5670 0x4b0085142c5ab567 0xde1efbe7c7e3c7fd 0xfde1efbe7c7e3c7f

def z657 : W := mkw 0x00d7a03500000009 0x000d7a0350000000 0xfefff03f80000000 0x9fefff03f8000000

def z658 : W := mkw 0x0008010044004400 0x0000801004400440 0x4018030004000600 0x4401803000400060

def z659 : W := mkw 0xd2085048f7ff1b10 0xed2085048f7ff1b1 0x010000007fff3f3f 0x0010000007fff3f3

def z660 : W := mkw 0x01ffafb56e00e40f 0x901ffafb56e00e40 0xfffffffff800c000 0xffffffffff800c00

def z661 : W := mkw 0x00085000452b0000 0x400085000452b000 0xfa1ff00047ff0007 0x1fa1ff00047ff000

def z662 : W := mkw 0xd000004880841b10 0x0d000004880841b1 0x0000000000003f38 0x00000000000003f3

def z663 : W := mkw 0x01bc0f806e00e406 0x901bc0f806e00e40 0x79fc0fc07800c000 0x679fc0fc07800c00

def z664 : W := mkw 0x0000000000000000 0x0000000000000000 0x8602c02600000000 0x98602c0260000000

def z665 : W := mkw 0x00630c3000000004 0x000630c300000000 0x10e2082000000000 0x010e208200000000

def z666 : W := mkw 0x8000004000801200 0x0800000400080120 0x0000000007803e0b 0x00000000007803e0

def z667 : W := mkw 0x0000000000000000 0x0000000000000000 0x4800000004000609 0x6480000000400060

def z668 : W := mkw 0x0000000000000000 0x0000000000000000 0x121acb2600000000 0x0121acb260000000

def z669 : W := mkw 0x0000000000000000 0x0000000000000000 0xcc00000000000000 0xfcc0000000000000

def z670 : W := mkw 0x2000010200004460 0x0200001020000446 0x0400030600000630 0x4040003060000063

def z671 : W := mkw 0x0063aeb50000000f 0x00063aeb50000000 0x8603ffff80000000 0xf8603ffff8000000

def z672 : W := mkw 0xf000114a818d5f70 0x0f000114a818d5f7 0xec053fff879fffff 0xfec053fff879ffff

def z673 : W := mkw 0x9000004080801210 0x0900000408080121 0x040000c180000630 0x4040000c18000063

def z674 : W := mkw 0x00200eb500000007 0x000200eb50000000 0x00000b2600000000 0x000000b260000000

def z675 : W := mkw 0x0000000000000000 0x0000000000000000 0x58180b0000000000 0x658180b000000000

def z676 : W := mkw 0x204b410254724460 0x4204b41025472446 0xfffbcb267c7fc7ff 0xffffbcb267c7fc7f

def z677 : W := mkw 0xd2fffc78ffffbb9c 0xfd2fffc78ffffbb9 0xfffffcf9ffffffff 0xffffffcf9fffffff

def z678 : W := mkw 0x00630c301850a084 0x100630c301850a08 0x39e20c207860f8cb 0x239e20c207860f8c

def z679 : W := mkw 0x400000081854a980 0x1400000081854a98 0x99020820787cf9cf 0xa99020820787cf9c

def z680 : W := mkw 0x00f7aeb50000000f 0x000f7aeb50000000 0x56fefbe780000000 0x556fefbe78000000

def z681 : W := mkw 0x60200d3a0804ede4 0x160200d3a0804ede 0x04000f3e0000fff8 0xe04000f3e0000fff

def z682 : W := mkw 0xd1201fc8898dff16 0x1d1201fc8898dff1 0xec053fd9879fff3f 0xfec053fd9879fff3

def z683 : W := mkw 0xd2d7b048b3dd1b18 0xad2d7b048b3dd1b1 0x21e534d9bb9c3802 0x021e534d9bb9c380

def z684 : W := mkw 0x2008410244224460 0x4200841024422446 0xc61ac326046307f4 0xdc61ac326046307f

def z685 : W := mkw 0x40f7aebd1054098f 0x040f7aebd1054098 0xfeffffff807c01c4 0xffeffffff807c01c

def z686 : W := mkw 0x0000100001090000 0x0000010000109000 0x80013000001f0004 0x180013000001f000

def z687 : W := mkw 0x40f7aebd0004090f 0x040f7aebd0004090 0xfeffffff801c390f 0xffeffffff801c390

def z688 : W := mkw 0x40630c381854a984 0x140630c381854a98 0x39e10c18781cf80b 0x239e10c18781cf80

def z689 : W := mkw 0x00d7a00000000008 0x000d7a0000000000 0x12fac00000000000 0x012fac0000000000

def z690 : W := mkw 0xf06b5d7addfffff4 0x5f06b5d7addfffff 0xffffffffffffffff 0xffffffffffffffff

def z691 : W := mkw 0x2008410244224460 0x4200841024422446 0x0218c30600000000 0x00218c3060000000

def z692 : W := mkw 0x20ffefb74422446f 0x420ffefb74422446 0xfeffffffc060c0c0 0xffeffffffc060c0c

def z693 : W := mkw 0x81200fc00880f606 0x181200fc00880f60 0x68040fc00780fe0b 0x668040fc00780fe0

def z694 : W := mkw 0x02085000777b0000 0xe02085000777b000 0xdb1ac0007fff0007 0x1db1ac0007fff000

def z695 : W := mkw 0xc1ffaffd7ed4ff8f 0x9c1ffaffd7ed4ff8 0xfffffffffffcffcf 0xffffffffffffcffc

def z696 : W := mkw 0x029ce00066220008 0xe029ce0006622000 0x0218c00000000000 0x00218c0000000000

def z697 : W := mkw 0x00f7aeb50000000f 0x000f7aeb50000000 0x00e0000000000000 0x000e000000000000

def z698 : W := mkw 0x0000010000004400 0x0000001000000440 0x00000b000000c608 0x600000b000000c60

def z699 : W := mkw 0x839cf3c067ab560a 0xe839cf3c067ab560 0x421cf3c007830600 0x5421cf3c00783060

def z700 : W := mkw 0x0008000066000000 0x8000800006600000 0x010000007f800003 0x0010000007f80000

def z701 : W := mkw 0x0094a2850000000b 0x00094a2850000000 0x0218c30600000000 0x00218c3060000000

def z702 : W := mkw 0x2008410244224460 0x4200841024422446 0xcc0000004463c7fd 0xfcc0000004463c7f

def z703 : W := mkw 0xd2dff048f7ff1b18 0xed2dff048f7ff1b1 0xfbfff0007fff3f3f 0x1fbfff0007fff3f3

def z704 : W := mkw 0x0043003010500080 0x0004300301050008 0x00020020006000c0 0x000020020006000c

def z705 : W := mkw 0xd1bc0fc8ee84ff16 0x9d1bc0fc8ee84ff1 0x7dfc0fd9ff80ff3b 0xe7dfc0fd9ff80ff3

def z706 : W := mkw 0x42fffc387f7fa98c 0xf42fffc387f7fa98 0xfbfff4187fff3807 0x1fbfff4187fff380

def z707 : W := mkw 0xa1bc4fc26ea2f666 0xda1bc4fc26ea2f66 0xfdfc0fc07fe3ffff 0xffdfc0fc07fe3fff

def z708 : W := mkw 0x42bcfc386f2fa98c 0xf42bcfc386f2fa98 0x421cfc380783f9c8 0xb421cfc380783f9c

def z709 : W := mkw 0x009c5000672b0000 0xc009c5000672b000 0xfbfff0007fff0007 0x1fbfff0007fff000

def z710 : W := mkw 0x22dff102777b4468 0xe22dff102777b446 0xfffffb267fffc1f7 0x9fffffb267fffc1f

def z711 : W := mkw 0xd0001048818d1b10 0x0d0001048818d1b1 0xfe1ff4d9879f3f3f 0xffe1ff4d9879f3f3

def z712 : W := mkw 0x814ba1756e80f609 0x9814ba1756e80f60 0x8703f03fff80fe0b 0x98703f03fff80fe0

def z713 : W := mkw 0x40630c381854a984 0x140630c381854a98 0x21e10c38787cf9cf 0xa21e10c38787cf9c

def z714 : W := mkw 0x2008410244224460 0x4200841024422446 0xc61acb260463c7fc 0xfc61acb260463c7f

def z715 : W := mkw 0x02dff000777b0008 0xe02dff000777b000 0xffffffffffff0007 0xfffffffffffff000

def z716 : W := mkw 0x40630c381854a984 0x140630c381854a98 0xbfe3cc3e787cf9cf 0xbbfe3cc3e787cf9c

def z717 : W := mkw 0x02dff000777b0008 0xe02dff000777b000 0xfbfff4d9ffff0007 0x1fbfff4d9ffff000

def z718 : W := mkw 0x02d7b00033590008 0xa02d7b0003359000 0x79fd30003b9c0002 0x079fd30003b9c000

def z719 : W := mkw 0x02dff000777b0008 0xe02dff000777b000 0x33fff0007fff0007 0x033fff0007fff000

def z720 : W := mkw 0x02d7b00033590008 0xa02d7b0003359000 0xede534d9bb9c0002 0xfede534d9bb9c000

def z721 : W := mkw 0x02dff035777b0009 0xe02dff035777b000 0xfffff4ffffff0007 0xffffff4ffffff000

def z722 : W := mkw 0x404300081854a980 0x1404300081854a98 0x21e10000787cf9cf 0x021e10000787cf9c

def z723 : W := mkw 0x00f7aeb51050000f 0x000f7aeb51050000 0xfffffffff87cc1cf 0xffffffffff87cc1c

def z724 : W := mkw 0x00df000076500000 0x800df00007650000 0x79fd00007f9c0003 0x079fd00007f9c000

def z725 : W := mkw 0x02dff000777b0008 0xe02dff000777b000 0xfffff0c1ffff0007 0x5fffff0c1ffff000

def z726 : W := mkw 0x81b40ec02a80b206 0x981b40ec02a80b20 0xede534d9bb803802 0xfede534d9bb80380

def z727 : W := mkw 0x81bc0fc06e80f606 0x981bc0fc06e80f60 0x7dfc0fe67f80fe0b 0xe7dfc0fe67f80fe0

def z728 : W := mkw 0x204b5102557b4460 0x4204b5102557b446 0xfffffb267fffc7ff 0xffffffb267fffc7f

def z729 : W := mkw 0x90631c7099d9b294 0x190631c7099d9b29 0x55e638e1ffe3c6f0 0x555e638e1ffe3c6f

def z730 : W := mkw 0x02d7b03533590009 0xa02d7b0353359000 0x21e53019bb9c0002 0x021e53019bb9c000

def z731 : W := mkw 0xa1bc4fc26ea2f666 0xda1bc4fc26ea2f66 0x7bfecfe67fe3ffff 0x67bfecfe67fe3fff

def z732 : W := mkw 0x00f7aeb51850a08f 0x100f7aeb51850a08 0xfffffffff87cc0c7 0xffffffffff87cc0c

def z733 : W := mkw 0x40630c381854a984 0x140630c381854a98 0xb9e30c387c7fffff 0xab9e30c387c7ffff

def z734 : W := mkw 0x8363ffc019fbf60e 0x78363ffc019fbf60 0x8203ffc0007ffe0c 0x78203ffc0007ffe0

def z735 : W := mkw 0x02dff000777b0008 0xe02dff000777b000 0x7bfff0007ffc0003 0x07bfff0007ffc000

def z736 : W := mkw 0x02dfb00077590008 0xa02dfb0007759000 0xf9ff30007ffc0007 0x0f9ff30007ffc000

def z737 : W := mkw 0x00f7aeb50000000f 0x000f7aeb50000000 0x96fbffff80000000 0xf96fbffff8000000

def z738 : W := mkw 0x404300081854a980 0x1404300081854a98 0xb9e30820787cf9cf 0xab9e30820787cf9c

def z739 : W := mkw 0x02285eb5777b0007 0xe02285eb5777b000 0x05000fffffff0007 0xe05000fffffff000

def z740 : W := mkw 0x81b40fc02a80f606 0x981b40fc02a80f60 0x21e407c03b803e02 0x421e407c03b803e0

def z741 : W := mkw 0xf208514af7ff5f70 0xef208514af7ff5f7 0x010000007fffffff 0x0010000007ffffff

def z742 : W := mkw 0x02dff000777b0008 0xe02dff000777b000 0xfffff4d9ffff073f 0xffffff4d9ffff073

def z743 : W := mkw 0x02dff100777b4408 0xe02dff100777b440 0xfffffb267fffc60f 0xffffffb267fffc60

def z744 : W := mkw 0x2008410244224460 0x4200841024422446 0xfe1ecfe64463c7fd 0xffe1ecfe64463c7f

def z745 : W := mkw 0x81b40ec02a80b206 0x981b40ec02a80b20 0x79e40cc07f80fe0b 0x679e40cc07f80fe0

def z746 : W := mkw 0x00f7aeb51850a08f 0x100f7aeb51850a08 0xfffffffff860c1cd 0xffffffffff860c1c

def z747 : W := mkw 0x009c100067090000 0x8009c10006709000 0x79fc00007f9f0007 0x079fc00007f9f000

def z748 : W := mkw 0x00f7aeb51050008f 0x000f7aeb51050008 0xfeffffff806000c0 0xffeffffff806000c

def z749 : W := mkw 0xa1bc4fc26ea2f666 0xda1bc4fc26ea2f66 0xffffffffffe3ffff 0xfffffffffffe3fff

def z750 : W := mkw 0x22dff102777b4468 0xe22dff102777b446 0x67fdf3063f9f0632 0x567fdf3063f9f063

def z751 : W := mkw 0xa19c41426ea2f660 0xda19c41426ea2f66 0xfbfec0007fe3ffff 0x1fbfec0007fe3fff

def z752 : W := mkw 0x02d7b00033590008 0xa02d7b0003359000 0xfbfff0007bfc0007 0x1fbfff0007bfc000

def z753 : W := mkw 0x00dfb00067090008 0x800dfb0006709000 0xfbfff0007f9f0007 0x1fbfff0007f9f000

def z754 : W := mkw 0xd2dfe048f6f61b18 0xed2dfe048f6f61b1 0x17fac4d9f8603f38 0xe17fac4d9f8603f3

def z755 : W := mkw 0x02dff000777b0008 0xe02dff000777b000 0x79fd30007fff0007 0x079fd30007fff000

def z756 : W := mkw 0xa1bc4fc26ea2f666 0xda1bc4fc26ea2f66 0xfbfecfc07fe3ffff 0x7fbfecfc07fe3fff

def z757 : W := mkw 0x02dff000777b0008 0xe02dff000777b000 0xfffff0267fff0007 0x9fffff0267fff000

def z758 : W := mkw 0x2008410244224460 0x4200841024422446 0x961acb264063c7fc 0xf961acb264063c7f

def z759 : W := mkw 0x00f7aeb50000000f 0x000f7aeb50000000 0xfeffffffc000c009 0xffeffffffc000c00

def z760 : W := mkw 0xf008514ac5af5f70 0x4f008514ac5af5f7 0x00000000079f3f3f 0x000000000079f3f3

def z761 : W := mkw 0x00f7aeb50800a00f 0x100f7aeb50800a00 0xfffffffff860f9cf 0xffffffffff860f9c

def z762 : W := mkw 0x22dff102777b4468 0xe22dff102777b446 0x13facb267fffc7ff 0x013facb267fffc7f

def z763 : W := mkw 0x00bc0d006e00e404 0x900bc0d006e00e40 0x79fc0f007f80fe0b 0x679fc0f007f80fe0

def z764 : W := mkw 0x80200c400880b204 0x180200c400880b20 0xfde60ce07fe3ffff 0xffde60ce07fe3fff

def z765 : W := mkw 0x819c01406e80f600 0x9819c01406e80f60 0x21e400007f80fe0b 0x021e400007f80fe0

def z766 : W := mkw 0x81bc0fc06e80f606 0x981bc0fc06e80f60 0x11f80b007b80f802 0x011f80b007b80f80

def z767 : W := mkw 0x819c01406e80f600 0x9819c01406e80f60 0x79fc0b007f80fe0b 0x679fc0b007f80fe0

def z768 : W := mkw 0x02dff100777b4408 0xe02dff100777b440 0xfbfff3007fff0607 0x5fbfff3007fff060

def z769 : W := mkw 0x02d7b00033590008 0xa02d7b0003359000 0xfffffb263b9c0002 0xffffffb263b9c000

def z770 : W := mkw 0x02d7b00033590008 0xa02d7b0003359000 0xa3e7f0003b9c0002 0x1a3e7f0003b9c000

def z771 : W := mkw 0xd1200ff88884ff96 0x1d1200ff88884ff9 0x04000ff98000fff8 0xe04000ff98000fff

def z772 : W := mkw 0x02dff000777b0008 0xe02dff000777b000 0x21e530003f9f0002 0x021e530003f9f000

def z773 : W := mkw 0x81bc0fc06e80f606 0x981bc0fc06e80f60 0x69e404c07f80fe0b 0x669e404c07f80fe0

def z774 : W := mkw 0xf008514ac5af5f70 0x4f008514ac5af5f7 0x321fffffc3fcf8c2 0x0321fffffc3fcf8c

def z775 : W := mkw 0xa1bc4fc26ea2f666 0xda1bc4fc26ea2f66 0xfbfecfe67fe0ffcf 0xefbfecfe67fe0ffc

def z776 : W := mkw 0x02d7b00033590008 0xa02d7b0003359000 0xe9e530003b9c0002 0x1e9e530003b9c000

def z777 : W := mkw 0xd0001048818d1b10 0x0d0001048818d1b1 0xfc053cd9c79fff3f 0xffc053cd9c79fff3

def z778 : W := mkw 0x81b40ec02a80b206 0x981b40ec02a80b20 0xfffecfe63b803802 0xffffecfe63b80380

def z779 : W := mkw 0xd0001048818d1b10 0x0d0001048818d1b1 0xfde534d9ff9f3f3f 0xffde534d9ff9f3f3

def z780 : W := mkw 0x4243b038115d0988 0x24243b038115d098 0x00013018001c0000 0x000013018001c000

def z781 : W := mkw 0x00f7aeb50000000f 0x000f7aeb50000000 0x66fdffff80000000 0xf66fdffff8000000

def z782 : W := mkw 0x22dff102777b4468 0xe22dff102777b446 0xfffff3067fff073f 0xffffff3067fff073

def z783 : W := mkw 0x81bc0fc06e80f606 0x981bc0fc06e80f60 0x51fc0fc07f80fe08 0x651fc0fc07f80fe0

def z784 : W := mkw 0x81b40ec02a80b206 0x981b40ec02a80b20 0x69e404c03b803802 0x669e404c03b80380

def z785 : W := mkw 0xa09c414266a25660 0xca09c414266a2566 0xfffecfe67fe3ffff 0xffffecfe67fe3fff

def z786 : W := mkw 0x00d7000032500000 0x800d700003250000 0xb9e700007bfc0007 0x0b9e700007bfc000

def z787 : W := mkw 0x5243f038917f0998 0x65243f038917f099 0x8603f039807f01f4 0x98603f039807f01f

def z788 : W := mkw 0x20df410276724460 0xc20df41027672446 0xffffcb267fffc7ff 0xfffffcb267fffc7f

def z789 : W := mkw 0x009c000076500000 0x8009c00007650000 0x79fc00007ffc0007 0x079fc00007ffc000

def z790 : W := mkw 0x40630c381854a984 0x140630c381854a98 0x91e30838787cf9cf 0x891e30838787cf9c

def z791 : W := mkw 0x81bc0fc06e80f606 0x981bc0fc06e80f60 0x7dfc0fc07f80ff3b 0xe7dfc0fc07f80ff3

def z792 : W := mkw 0x5243b008915d0918 0x25243b008915d091 0x00013019801c0000 0x000013019801c000

def z793 : W := mkw 0xd0001048818d1b10 0x0d0001048818d1b1 0xa80534d9879f3f3f 0xaa80534d9879f3f3

def z794 : W := mkw 0xa1284d426ea2f664 0xda1284d426ea2f66 0xfffacf267fe3ffff 0xffffacf267fe3fff

def z795 : W := mkw 0x00b40c002a00a004 0x900b40c002a00a00 0x39e40c007b80f80b 0x239e40c007b80f80

def z796 : W := mkw 0x00200eb500000007 0x000200eb50000000 0xfe1fffff80000000 0xffe1fffff8000000

def z797 : W := mkw 0x22dff002777b0068 0xe22dff002777b006 0xfffff0067fff0037 0x1fffff0067fff003

def z798 : W := mkw 0x22dff102777b4468 0xe22dff102777b446 0xfbfffb267fffc6cf 0x7fbfffb267fffc6c

def z799 : W := mkw 0x0094100023090000 0x8009410002309000 0xe9e530003f9f0007 0x1e9e530003f9f000

def z800 : W := mkw 0x02d7f000337b0008 0xe02d7f000337b000 0x23e5f0003b9f0002 0x123e5f0003b9f000

def z801 : W := mkw 0x02d7b00033590008 0xa02d7b0003359000 0xa1e530003b9f0006 0x1a1e530003b9f000

def z802 : W := mkw 0x22dff102777b4468 0xe22dff102777b446 0xdffacb267fffc7ff 0xfdffacb267fffc7f

def z803 : W := mkw 0xc1200ef80884bb86 0x1c1200ef80884bb8 0x00000cf80000f9c8 0xa00000cf80000f9c

def z804 : W := mkw 0x01f7aeb52a00a00f 0x901f7aeb52a00a00 0xffffffffb8000000 0xfffffffffb800000

def z805 : W := mkw 0xa1bc4fc26ea2f666 0xda1bc4fc26ea2f66 0x7dfc0fe67fe3ffff 0xe7dfc0fe67fe3fff

def z806 : W := mkw 0x81bc0fc06e80f606 0x981bc0fc06e80f60 0x51fc0bc07f80fe0b 0x451fc0bc07f80fe0

def z807 : W := mkw 0xa1b44ec22aa2b266 0xda1b44ec22aa2b26 0xa7e6c4e63be339f6 0x9a7e6c4e63be339f

def z808 : W := mkw 0x12dff000f77b0018 0xe12dff000f77b001 0xfffff001ffff0037 0x1fffff001ffff003

def z809 : W := mkw 0xd0001048818d1b10 0x0d0001048818d1b1 0x640534d9879f3f3f 0x5640534d9879f3f3

def z810 : W := mkw 0xa1bc0fc26e80f666 0x9a1bc0fc26e80f66 0xfdfe0fe67fe0ffff 0xefdfe0fe67fe0fff

def z811 : W := mkw 0x81bc0fc06e80f606 0x981bc0fc06e80f60 0x31fc0fc07f80fe0b 0x031fc0fc07f80fe0

def z812 : W := mkw 0x22dff002777b0068 0xe22dff002777b006 0xfffff0267fff07ff 0xffffff0267fff07f

def z813 : W := mkw 0x22dff102777b4468 0xe22dff102777b446 0xfbfffb267fffc7ff 0x1fbfffb267fffc7f

def z814 : W := mkw 0x40200c081854a984 0x140200c081854a98 0xb9e20c20787cf9cf 0xab9e20c20787cf9c

def z815 : W := mkw 0x40630ebd1854a987 0x140630ebd1854a98 0xb9e30cf9f87cf9cf 0xab9e30cf9f87cf9c

def z816 : W := mkw 0xa0284d424ca2f664 0x5a0284d424ca2f66 0xfffecfe67fe3ffff 0xffffecfe67fe3fff

def z817 : W := mkw 0x22dff002777b0068 0xe22dff002777b006 0xfbfff0007fff01f7 0x1fbfff0007fff01f

def z818 : W := mkw 0x02d7b00033590008 0xa02d7b0003359000 0xb9e738207bfcc1cf 0xab9e738207bfcc1c

def z819 : W := mkw 0x6243f03a117f09e8 0x66243f03a117f09e 0x8603f03e007f01f4 0x98603f03e007f01f

def z820 : W := mkw 0x22d7b10233594468 0xa22d7b1023359446 0x25e53b263b9cc7fa 0xe25e53b263b9cc7f

def z821 : W := mkw 0x40630c381854a984 0x140630c381854a98 0xfffbcf3e7c7fffff 0xffffbcf3e7c7ffff

def z822 : W := mkw 0x02dff000777b0008 0xe02dff000777b000 0xfbfffb007fff0007 0x7fbfffb007fff000

def z823 : W := mkw 0x22dff102777b4468 0xe22dff102777b446 0xfffffb267fff0637 0xffffffb267fff063

def z824 : W := mkw 0xc1df03f876d45f82 0x8c1df03f876d45f8 0xc01f03f807fc07c4 0xcc01f03f807fc07c

def z825 : W := mkw 0x7243f00a917f0978 0x67243f00a917f097 0x8603f03f807f01f4 0x98603f03f807f01f

def z826 : W := mkw 0x0063aeb50000000f 0x00063aeb50000000 0xde1bffff80000000 0xfde1bffff8000000

def z827 : W := mkw 0xc1200d780884ff84 0x1c1200d780884ff8 0x00000c380000ffc8 0xa00000c380000ffc

def z828 : W := mkw 0x00f7aeb50000000f 0x000f7aeb50000000 0xfeffffff80030134 0xffeffffff8003013

def z829 : W := mkw 0x00d7a00000000008 0x000d7a0000000000 0xfeffffff80000000 0xffeffffff8000000

def z830 : W := mkw 0xd0001048818d1b10 0x0d0001048818d1b1 0xec0534d9879f3e37 0x5ec0534d9879f3e3

def z831 : W := mkw 0xd0001048818d1b10 0x0d0001048818d1b1 0xde1acb26079f3f3f 0xfde1acb26079f3f3

def z832 : W := mkw 0x4243b038115d0988 0x24243b038115d098 0x80033038007c01c4 0x880033038007c01c

def z833 : W := mkw 0x029c5000777b0000 0xe029c5000777b000 0x21e400007fff0007 0x021e400007fff000

def z834 : W := mkw 0x81b40ec02a80b206 0x981b40ec02a80b20 0x79fc0fc07b80f80b 0x679fc0fc07b80f80

def z835 : W := mkw 0x00f7aeb50000000f 0x000f7aeb50000000 0xfeffffff801c0007 0xffeffffff801c000

def z836 : W := mkw 0x00f7aeb50000000f 0x000f7aeb50000000 0xeefdf7df80000000 0xfeefdf7df8000000

def z837 : W := mkw 0x00200c000800a004 0x100200c000800a00 0x79e40c007f80f80b 0x279e40c007f80f80

def z838 : W := mkw 0x22dff102777b4468 0xe22dff102777b446 0xfffff0267fffc7ff 0x9fffff0267fffc7f

def z839 : W := mkw 0x00f7aeb50000000f 0x000f7aeb50000000 0xfeffffff84030005 0xffeffffff8403000

def z840 : W := mkw 0x00f7aeb52200000f 0x800f7aeb52200000 0xffffffffbb800002 0xfffffffffbb80000

def z841 : W := mkw 0x00f7aeb50000000f 0x000f7aeb50000000 0xfaffffff80000000 0x1faffffff8000000

def z842 : W := mkw 0xd0200c788884bb94 0x1d0200c788884bb9 0x040004d980003f38 0xe040004d980003f3

def z843 : W := mkw 0x4063ac381854a98c 0x14063ac381854a98 0xbbe3fc38787cf9cf 0xbbbe3fc38787cf9c

def z844 : W := mkw 0x81bc0ff56e80f607 0x981bc0ff56e80f60 0x79fc0fd9ff80fe0b 0x679fc0fd9ff80fe0

def z845 : W := mkw 0x024b5000777b0000 0xe024b5000777b000 0xf9e730007fff0007 0x1f9e730007fff000

def z846 : W := mkw 0x22dff102777b4468 0xe22dff102777b446 0xfffff0007fffc7ff 0xffffff0007fffc7f

def z847 : W := mkw 0x00f7aeb51850a00f 0x100f7aeb51850a00 0xfffffffff87cf80f 0xffffffffff87cf80

def z848 : W := mkw 0xd0f7befd818d1b1f 0x0d0f7befd818d1b1 0x12facb26079f3f3f 0x012facb26079f3f3

def z849 : W := mkw 0x009c000066000000 0x8009c00006600000 0x79fc04007f80380b 0x279fc04007f80380

def z850 : W := mkw 0x02dff000777b0008 0xe02dff000777b000 0xfbfff8207fffc0c7 0x1fbfff8207fffc0c

def z851 : W := mkw 0x4243f008117f0988 0x64243f008117f098 0x8203f000007f01c4 0x18203f000007f01c

def z852 : W := mkw 0x81b40ec02a80b206 0x981b40ec02a80b20 0x31fc0fc03b803802 0x031fc0fc03b80380

def z853 : W := mkw 0x02dff2b5777b000b 0xe02dff2b5777b000 0xfffff3ffffff0007 0xdfffff3ffffff000

def z854 : W := mkw 0xc1280ff84c84ff86 0x1c1280ff84c84ff8 0xd81a0ff84460ffcd 0xed81a0ff84460ffc

def z855 : W := mkw 0x81bc0ff06e80f686 0x981bc0ff06e80f68 0x79fc0fe07f80fecb 0x679fc0fe07f80fec

def z856 : W := mkw 0x81bc0fc06e80f606 0x981bc0fc06e80f60 0x79fc0fe07f80ffcb 0xe79fc0fe07f80ffc

def z857 : W := mkw 0x02dff000777b0008 0xe02dff000777b000 0xfbfff4c07fff0007 0x7fbfff4c07fff000

def z858 : W := mkw 0x00f7aeb50000000f 0x000f7aeb50000000 0xfeffffff8000010d 0xffeffffff8000010

def z859 : W := mkw 0x81b40ec02a80b206 0x981b40ec02a80b20 0xede404c03f833f3f 0xfede404c03f833f3

def z860 : W := mkw 0x40630c381854a984 0x140630c381854a98 0xb9e30418787cf9cf 0x0b9e30418787cf9c

def z861 : W := mkw 0x81b40ef52a80b207 0x981b40ef52a80b20 0x25e40fffbb803802 0xe25e40fffbb80380

def z862 : W := mkw 0x404300081854a980 0x1404300081854a98 0xb9e30418787cf9cf 0xab9e30418787cf9c

def z863 : W := mkw 0x00f7aeb50000000f 0x000f7aeb50000000 0x7affffff80000000 0x67affffff8000000

def z864 : W := mkw 0x02dfe00076720008 0xe02dfe0007672000 0xfbffc0007ffc0007 0x0fbffc0007ffc000

def z865 : W := mkw 0x606b4d3a5c76ede4 0x5606b4d3a5c76ede 0x67f9c71e3c1f3e32 0x567f9c71e3c1f3e3

def z866 : W := mkw 0x00f7aeb50000000f 0x000f7aeb50000000 0xfeffffffc463c7fd 0xffeffffffc463c7f

def z867 : W := mkw 0x00280c006e00a004 0x900280c006e00a00 0x39e00c007f80f80b 0x239e00c007f80f80

def z868 : W := mkw 0x0243100033590000 0xa024310003359000 0xb9e300007bfc0007 0x0b9e300007bfc000

def z869 : W := mkw 0x81bcafc56e80f60f 0x981bcafc56e80f60 0xfffeffe7ff80fe0b 0xffffeffe7ff80fe0

def z870 : W := mkw 0x81bc0fc06e80f606 0x981bc0fc06e80f60 0x7dfc3fc1ff80fe0b 0x77dfc3fc1ff80fe0

def z871 : W := mkw 0x0000100001090000 0x0000010000109000 0xf9e530007f9f0007 0x1f9e530007f9f000

def z872 : W := mkw 0x81bc4fc06ea2f606 0xd81bc4fc06ea2f60 0x7bfecfc07fe0fe0b 0x67bfecfc07fe0fe0

def z873 : W := mkw 0x81bc0fc06e80f606 0x981bc0fc06e80f60 0x79fe0fe07fe0fecb 0x679fe0fe07fe0fec

def z874 : W := mkw 0x02dff000777b0008 0xe02dff000777b000 0x23fdf0003b9c0002 0x023fdf0003b9c000

def z875 : W := mkw 0x81bc0fc06e80f606 0x981bc0fc06e80f60 0x21fc07c03b803802 0x021fc07c03b80380

def z876 : W := mkw 0x00f7aeb50000000f 0x000f7aeb50000000 0xfeffffffc0600005 0xffeffffffc060000

def z877 : W := mkw 0x5043b03d915d0999 0x05043b03d915d099 0x8603f03f807f01f4 0x98603f03f807f01f

def z878 : W := mkw 0x22dff102777b4468 0xe22dff102777b446 0xffffffffffffc7ff 0xfffffffffffffc7f

def z879 : W := mkw 0x81bc0fc06e80f606 0x981bc0fc06e80f60 0x21e404c03f803e02 0x021e404c03f803e0

def z880 : W := mkw 0x2008410244224460 0x4200841024422446 0x5a1acb264463c7fd 0x65a1acb264463c7f

def z881 : W := mkw 0x02d7b00033590008 0xa02d7b0003359000 0x61e530003f9f0002 0x161e530003f9f000

def z882 : W := mkw 0x81bc0d406e80f604 0x981bc0d406e80f60 0x79fc0c007f80fe0b 0x279fc0c007f80fe0

def z883 : W := mkw 0x02d7b2853359000b 0xa02d7b2853359000 0x67fdf3c7bb9c0002 0x567fdf3c7bb9c000

def z884 : W := mkw 0x81280d406e80f604 0x981280d406e80f60 0x21e004007f80fe0b 0x021e004007f80fe0

def z885 : W := mkw 0x2008410244224460 0x4200841024422446 0xd61acb264463c7f4 0xdd61acb264463c7f

def z886 : W := mkw 0x40200c081854a984 0x140200c081854a98 0x21e00400787cf9cf 0x021e00400787cf9c

def z887 : W := mkw 0x00dfa00076500008 0x800dfa0007650000 0xfbfff0007ffc0007 0x1fbfff0007ffc000

def z888 : W := mkw 0xb29cf142e7ab5678 0xeb29cf142e7ab567 0x461cf3c787830630 0x5461cf3c78783063

def z889 : W := mkw 0x81bcafc06e80f60e 0x981bcafc06e80f60 0x7bfcffc07f80fe0b 0x77bfcffc07f80fe0

def z890 : W := mkw 0x4063ac3d1854a98d 0x14063ac3d1854a98 0xb9e33c39f87cf9cf 0xab9e33c39f87cf9c

def z891 : W := mkw 0x00df010076504400 0x800df01007650440 0xf9ff0b207ffcc7cf 0xef9ff0b207ffcc7c

def z892 : W := mkw 0xa1bc4fc26ea2f666 0xda1bc4fc26ea2f66 0x7bfccfc67f80fe0b 0x67bfccfc67f80fe0

def z893 : W := mkw 0x02d7b00033590008 0xa02d7b0003359000 0x21e534d9bb9c0002 0x021e534d9bb9c000

def z894 : W := mkw 0xa1bc0fc26e80f666 0x9a1bc0fc26e80f66 0x79fc0fe67f80fecb 0x679fc0fe67f80fec

def z895 : W := mkw 0x91bc0fc0ee80f616 0x991bc0fc0ee80f61 0x7dfc0fc1ff80fe3b 0x67dfc0fc1ff80fe3

def z896 : W := mkw 0x40630c381854a984 0x140630c381854a98 0xf9e70c387ffcf9cf 0xaf9e70c387ffcf9c

def z897 : W := mkw 0x0094a2850000000b 0x00094a2850000000 0x661df7df80000000 0x5661df7df8000000

def z898 : W := mkw 0x00df400076720000 0xc00df40007672000 0xfbffc0007fff0007 0x1fbffc0007fff000

def z899 : W := mkw 0x02d7f000337b0008 0xe02d7f000337b000 0xebe7f0003fff0007 0x1ebe7f0003fff000

def z900 : W := mkw 0x00f7aeb50000000f 0x000f7aeb50000000 0x22fdf7df80000000 0x022fdf7df8000000

def z901 : W := mkw 0x02dff000777b0008 0xe02dff000777b000 0xdbfac0007fff0007 0x1dbfac0007fff000

def z902 : W := mkw 0xc1200fc80884ff86 0x1c1200fc80884ff8 0x00000fc00000ffc8 0x600000fc00000ffc

def z903 : W := mkw 0x81bc0ff56e80f607 0x981bc0ff56e80f60 0xfffecfffff80fe0b 0xffffecfffff80fe0

def z904 : W := mkw 0x81b40ec02a80b206 0x981b40ec02a80b20 0x21e534d9bb803802 0x021e534d9bb80380

def z905 : W := mkw 0xa1bc4fc26ea2f666 0xda1bc4fc26ea2f66 0x33fecfe67be0f8c2 0x033fecfe67be0f8c

def z906 : W := mkw 0x81bcafc56e80f60f 0x981bcafc56e80f60 0x79fc3fc1ff80fe0b 0x679fc3fc1ff80fe0

def z907 : W := mkw 0x02dff035777b0009 0xe02dff035777b000 0xfbfff0267fff0007 0x1fbfff0267fff000

def z908 : W := mkw 0x02dff000777b0008 0xe02dff000777b000 0xa3e7f0007fff0007 0x1a3e7f0007fff000

def z909 : W := mkw 0x4043000810540900 0x0404300081054090 0xb9e30c38787cf9cf 0xab9e30c38787cf9c

def z910 : W := mkw 0x40630c381854a984 0x140630c381854a98 0x39e10c18787cf9cf 0x239e10c18787cf9c

def z911 : W := mkw 0x40630c381854a984 0x140630c381854a98 0xbde33c39f87cf9cf 0xbbde33c39f87cf9c

def z912 : W := mkw 0xa39cf3c267ab566a 0xea39cf3c267ab566 0x461cf3c607830630 0x5461cf3c60783063

def z913 : W := mkw 0x81bcafc56e80f60f 0x981bcafc56e80f60 0xfffdffdfff80fe0b 0xffffdffdfff80fe0

def z914 : W := mkw 0x00d7a2b50000000b 0x000d7a2b50000000 0xde1ffbff80000000 0xfde1ffbff8000000

def z915 : W := mkw 0x029c5000777b0000 0xe029c5000777b000 0x11f800007fff0007 0x011f800007fff000

def z916 : W := mkw 0xd1200ffd8884ff17 0x1d1200ffd8884ff1 0x04000fff8000ff38 0xe04000fff8000ff3

def z917 : W := mkw 0x50431008915d0910 0x050431008915d091 0x84033019807f0134 0x984033019807f013

def z918 : W := mkw 0x40630c381854a984 0x140630c381854a98 0xf9fb0f38787cf9cf 0xef9fb0f38787cf9c

def z919 : W := mkw 0x00f7aeb51050000f 0x000f7aeb51050000 0xffffffffb81c0002 0xfffffffffb81c000

def z920 : W := mkw 0x024b5000777b0000 0xe024b5000777b000 0xfbfbc0007fff0007 0x1fbfbc0007fff000

def z921 : W := mkw 0x00f7aeb50800a00f 0x100f7aeb50800a00 0xffffffffb8003802 0xfffffffffb800380

def z922 : W := mkw 0x40630c381854a984 0x140630c381854a98 0xa9e10418787cf9cf 0xaa9e10418787cf9c

def z923 : W := mkw 0x22dff002777b0068 0xe22dff002777b006 0xfffff8267fffc1ff 0xbfffff8267fffc1f

def z924 : W := mkw 0xa1bc0fc26e80f666 0x9a1bc0fc26e80f66 0x7dfc0fc67f80fe3b 0x67dfc0fc67f80fe3

def z925 : W := mkw 0x81200c402a80b204 0x981200c402a80b20 0x21e004003b803802 0x021e004003b80380

def z926 : W := mkw 0x81280d406e80f604 0x981280d406e80f60 0x79e40cc07f80fe0b 0x679e40cc07f80fe0

def z927 : W := mkw 0x2008410244224460 0x4200841024422446 0x561acb264463c7fd 0x5561acb264463c7f

def z928 : W := mkw 0xd0f7befd99ddbb9f 0x1d0f7befd99ddbb9 0x21e534d9bb9c3802 0x021e534d9bb9c380

def z929 : W := mkw 0x5243f008917f0918 0x65243f008917f091 0x8203f000007f0134 0x18203f000007f013

def z930 : W := mkw 0x2008410244224460 0x4200841024422446 0xfe1ecb2647e3c7ff 0xffe1ecb2647e3c7f

def z931 : W := mkw 0xd0001048818d1b10 0x0d0001048818d1b1 0xec053cf9879fffff 0xfec053cf9879ffff

def z932 : W := mkw 0x02dff000777b0008 0xe02dff000777b000 0xfbfff0007fff073f 0x1fbfff0007fff073

def z933 : W := mkw 0x40630c381854a984 0x140630c381854a98 0xfffffffff87cf9cf 0xffffffffff87cf9c

def z934 : W := mkw 0xd0001048818d1b10 0x0d0001048818d1b1 0x240534d9879f3f3f 0xe240534d9879f3f3

def z935 : W := mkw 0x00b4ae850000000f 0x000b4ae850000000 0xfefdffdf80000000 0xffefdffdf8000000

def z936 : W := mkw 0x02dff285777b000b 0xe02dff285777b000 0xfbfff0c1ffff0007 0x1fbfff0c1ffff000

def z937 : W := mkw 0x02dff000777b0008 0xe02dff000777b000 0xfbfffb267fff0007 0x1fbfffb267fff000

def z938 : W := mkw 0x00b40c002a00a004 0x900b40c002a00a00 0x21e404003b803802 0x021e404003b80380

def z939 : W := mkw 0x02dff000777b0008 0xe02dff000777b000 0xe9e530007fff0007 0x1e9e530007fff000

def z940 : W := mkw 0x00f7aeb51850a08f 0x100f7aeb51850a08 0xffffffffb8000000 0xfffffffffb800000

def z941 : W := mkw 0x81b40ec02a80b206 0x981b40ec02a80b20 0x29e404c03b80380b 0x229e404c03b80380

def z942 : W := mkw 0x024bf000777b0008 0xe024bf000777b000 0xbbe3f0007fff0007 0x1bbe3f0007fff000

def z943 : W := mkw 0x229c5102777b4460 0xe229c5102777b446 0x79fc0b007fffc7ff 0x679fc0b007fffc7f

def z944 : W := mkw 0x80200c400880b204 0x180200c400880b20 0x21e404c03b803802 0x021e404c03b80380

def z945 : W := mkw 0xf1284fcacca6ff76 0x5f1284fcacca6ff7 0xde1acfffc463fffd 0xfde1acfffc463fff

def z946 : W := mkw 0x404300381854a980 0x1404300381854a98 0xb9e30038787cf9cf 0x8b9e30038787cf9c

def z947 : W := mkw 0x81bc0fc06e80f606 0x981bc0fc06e80f60 0x59f80b007f80fe0b 0x659f80b007f80fe0

def z948 : W := mkw 0xa1284d426ea2f664 0xda1284d426ea2f66 0xb9e20c207fe3ffff 0xab9e20c207fe3fff

def z949 : W := mkw 0x22dff102777b4468 0xe22dff102777b446 0xfffffb267fffc0c7 0xffffffb267fffc0c

def z950 : W := mkw 0x02dff035777b0009 0xe02dff035777b000 0xfffffb3fffff0007 0xffffffb3fffff000

def z951 : W := mkw 0x2008410244224460 0x4200841024422446 0xfe1ffb264463c7fd 0xffe1ffb264463c7f

def z952 : W := mkw 0x2008410244224460 0x4200841024422446 0xda1acb264463c7fd 0x1da1acb264463c7f

def z953 : W := mkw 0x81bc0fc06e80f606 0x981bc0fc06e80f60 0x39f80f007f80fe0b 0x239f80f007f80fe0

def z954 : W := mkw 0xd0001048818d1b10 0x0d0001048818d1b1 0xfc0734d9c7ff3f3f 0xffc0734d9c7ff3f3

def z955 : W := mkw 0x02dff100777b4408 0xe02dff100777b440 0xfbfffb207fffc7cf 0xffbfffb207fffc7c

def z956 : W := mkw 0x02dfb00077590008 0xa02dfb0007759000 0x61fd30003f9c0002 0x061fd30003f9c000

def z957 : W := mkw 0x22dff102777b4468 0xe22dff102777b446 0xfbfff0007fff0637 0x1fbfff0007fff063

def z958 : W := mkw 0x40630c081854a984 0x140630c081854a98 0xb9e30c00787cf9cf 0x2b9e30c00787cf9c

def z959 : W := mkw 0x02dff000777b0008 0xe02dff000777b000 0xb3fff0007bff0006 0x1b3fff0007bff000

def z960 : W := mkw 0x02d7b00033590008 0xa02d7b0003359000 0x39e530007b9c0003 0x039e530007b9c000

def z961 : W := mkw 0xd1200fc88884ff16 0x1d1200fc88884ff1 0x00000fc00000ff38 0x600000fc00000ff3

def z962 : W := mkw 0x2008410244224460 0x4200841024422446 0xec0534d9c463c7fd 0xfec0534d9c463c7f

def z963 : W := mkw 0x81b40ec02a80b206 0x981b40ec02a80b20 0x21e404c07b80f80b 0x021e404c07b80f80

def z964 : W := mkw 0x2008410244224460 0x4200841024422446 0xde1efbe7c463c7fd 0xfde1efbe7c463c7f

def z965 : W := mkw 0x02d7b00033590008 0xa02d7b0003359000 0xfbfff0003f9f0007 0x1fbfff0003f9f000

def z966 : W := mkw 0xd0001048818d1b10 0x0d0001048818d1b1 0xfe1fffffc7ffffff 0xffe1fffffc7fffff

def z967 : W := mkw 0x0094a2850000000b 0x00094a2850000000 0xc61df3df80000000 0xdc61df3df8000000

def z968 : W := mkw 0x81bc0ec06e80b206 0x981bc0ec06e80b20 0x79fc0fc07f803803 0x679fc0fc07f80380

def z969 : W := mkw 0x00b4aeb50000000f 0x000b4aeb50000000 0x461cf7df80000000 0x5461cf7df8000000

def z970 : W := mkw 0x02dff000777b0008 0xe02dff000777b000 0xfffff8207fffc7ff 0xffffff8207fffc7f

def z971 : W := mkw 0x02dff000777b0008 0xe02dff000777b000 0xfbfff0207fff01c7 0x9fbfff0207fff01c

def z972 : W := mkw 0x40630c381854a984 0x140630c381854a98 0xb1e30c38787cf9c6 0x8b1e30c38787cf9c

def z973 : W := mkw 0x81bc0ec06e80b206 0x981bc0ec06e80b20 0x79fc0cc07f80f80b 0x279fc0cc07f80f80

def z974 : W := mkw 0x009c000066000000 0x8009c00006600000 0xf9fd00007f9c0007 0x0f9fd00007f9c000

def z975 : W := mkw 0xa1bc4ff76ea2f667 0xda1bc4ff76ea2f66 0xfffecfffffe3ffff 0xffffecfffffe3fff

def z976 : W := mkw 0x02dff000777b0008 0xe02dff000777b000 0xfbfff0007bfc0002 0x1fbfff0007bfc000

def z977 : W := mkw 0x02dff000777b0008 0xe02dff000777b000 0x01e000007fff0007 0x001e000007fff000

def z978 : W := mkw 0x81bc0fc06e80f606 0x981bc0fc06e80f60 0xf9fe0fe07f80fe0b 0xef9fe0fe07f80fe0

def z979 : W := mkw 0xa1bc4fc26ea2f666 0xda1bc4fc26ea2f66 0x21e404c07fe3ffff 0x021e404c07fe3fff

def z980 : W := mkw 0x22dff137777b4469 0xe22dff137777b446 0xfffffb3fffffc7ff 0xffffffb3fffffc7f

def z981 : W := mkw 0x4094a28d1854a98b 0x14094a28d1854a98 0x471cf3c7f87cf9cf 0x5471cf3c7f87cf9c

def z982 : W := mkw 0x0043100011590000 0x0004310001159000 0xb9e300007fff0007 0x0b9e300007fff000

def z983 : W := mkw 0x50630c389854a994 0x150630c389854a99 0xbde30c39f87cf9ff 0xabde30c39f87cf9f

def z984 : W := mkw 0x00bc0c006e00a004 0x900bc0c006e00a00 0x79fc04007f803803 0x079fc04007f80380

def z985 : W := mkw 0x40630c381854a984 0x140630c381854a98 0x39e30c38787cf8cb 0x239e30c38787cf8c

def z986 : W := mkw 0x029c5000777b0000 0xe029c5000777b000 0xfbfec0007fff0007 0x1fbfec0007fff000

def z987 : W := mkw 0x40630c381854a984 0x140630c381854a98 0xb9e73cf9f87cf9cf 0xab9e73cf9f87cf9c

def z988 : W := mkw 0x02dff280777b000a 0xe02dff280777b000 0xfbfff3c07fff0007 0x5fbfff3c07fff000

def z989 : W := mkw 0x00f7aeb51850a08f 0x100f7aeb51850a08 0xfffffffff860f8cb 0xffffffffff860f8c

def z990 : W := mkw 0x81bc0fc06e80f606 0x981bc0fc06e80f60 0x79fc04c07f80fe0b 0x079fc04c07f80fe0

def z991 : W := mkw 0xd0200efd8884bb97 0x1d0200efd8884bb9 0x04000fff8000fff8 0xe04000fff8000fff

def z992 : W := mkw 0x00b4aeb50000000f 0x000b4aeb50000000 0x7efcffff80000000 0xf7efcffff8000000

def z993 : W := mkw 0x50431038915d0990 0x050431038915d099 0x84013019801f0134 0x984013019801f013

def z994 : W := mkw 0x50431038915d0990 0x050431038915d099 0xdc033839c47fc7fd 0xfdc033839c47fc7f

def z995 : W := mkw 0x524bf008d57f0918 0x6524bf008d57f091 0xde1bf019c47f073d 0xfde1bf019c47f073

def z996 : W := mkw 0x50431038915d0990 0x050431038915d099 0x80030038007f01f4 0x880030038007f01f

def z997 : W := mkw 0x02dfb00077590008 0xa02dfb0007759000 0xfbfff0007f9c0003 0x1fbfff0007f9c000

def z998 : W := mkw 0x81b40ec02a80b206 0x981b40ec02a80b20 0x21e404c03b803e0a 0x621e404c03b803e0

def z999 : W := mkw 0x40630ebd1854a987 0x140630ebd1854a98 0xfffbcffff87cf9cf 0xffffbcffff87cf9c

def z1000 : W := mkw 0x00f7aeb50000000f 0x000f7aeb50000000 0x76ffffff80000000 0x576ffffff8000000

def z1001 : W := mkw 0x00b40e8000000006 0x000b40e800000000 0xfeffffff80000000 0xffeffffff8000000

def z1002 : W := mkw 0x22dff102777b4468 0xe22dff102777b446 0xfbfff8207fffc7ff 0xbfbfff8207fffc7f

def z1003 : W := mkw 0x02d7b00033590008 0xa02d7b0003359000 0x31e730007bfc0002 0x031e730007bfc000

def z1004 : W := mkw 0x02dff000777b0008 0xe02dff000777b000 0x53fef0007fff0007 0x153fef0007fff000

def z1005 : W := mkw 0x02dff005777b0009 0xe02dff005777b000 0xfffff007ffff0007 0x1fffff007ffff000

def z1006 : W := mkw 0x81bc0fc06e80f606 0x981bc0fc06e80f60 0xf9fd3fc07f80fe0b 0x7f9fd3fc07f80fe0

def z1007 : W := mkw 0x22dff102777b4468 0xe22dff102777b446 0xfbfff0007fffc0c7 0x1fbfff0007fffc0c

def z1008 : W := mkw 0x819c03c066805602 0x8819c03c06680560 0x79fc07c07f803e0b 0x679fc07c07f803e0

def z1009 : W := mkw 0xa1bc4fc26ea2f666 0xda1bc4fc26ea2f66 0x7ffccfe67f83fffb 0xf7ffccfe67f83fff

def z1010 : W := mkw 0x81b4aec52a80b20f 0x981b4aec52a80b20 0x67fcf7c7bb803802 0x567fcf7c7bb80380

def z1011 : W := mkw 0x024b5000777b0000 0xe024b5000777b000 0x11e200007fff0007 0x011e200007fff000

def z1012 : W := mkw 0x00f7aeb50000000f 0x000f7aeb50000000 0xfeffffff8000c1c8 0xffeffffff8000c1c

def z1013 : W := mkw 0xa1bc0fc26e80f666 0x9a1bc0fc26e80f66 0xfffecfe67f80fffb 0xffffecfe67f80fff

def z1014 : W := mkw 0x810801406e80f600 0x9810801406e80f60 0x39e000007f80fe0b 0x039e000007f80fe0

def z1015 : W := mkw 0x8094004022801200 0x8809400402280120 0x21e404c03b803802 0x021e404c03b80380

def z1016 : W := mkw 0x224b5102777b4460 0xe224b5102777b446 0xfffbcb267fffc7ff 0xffffbcb267fffc7f

def z1017 : W := mkw 0x81bc0fc06e80f606 0x981bc0fc06e80f60 0xf9fc0fc07f83fe0f 0x7f9fc0fc07f83fe0

def z1018 : W := mkw 0x02dff000777b0008 0xe02dff000777b000 0x7bfdf0007f9f0003 0x17bfdf0007f9f000

def z1019 : W := mkw 0x40200c081854a984 0x140200c081854a98 0x11e00800787cf9cf 0x011e00800787cf9c

def z1020 : W := mkw 0x02dfb00077590008 0xa02dfb0007759000 0xf9fd30007f9f0007 0x1f9fd30007f9f000

def z1021 : W := mkw 0x00f7aeb50800a08f 0x100f7aeb50800a08 0xfeffffff8000c0c0 0xffeffffff8000c0c

def z1022 : W := mkw 0x0094a2b50000000b 0x00094a2b50000000 0x461cf3ff80000000 0xd461cf3ff8000000

def z1023 : W := mkw 0x81b40fc02a80f606 0x981b40fc02a80f60 0x21e40fc03b80f802 0x021e40fc03b80f80

def z1024 : W := mkw 0x81bcaff56e80f60f 0x981bcaff56e80f60 0x7ffcffffff80fe0b 0xf7ffcffffff80fe0

def z1025 : W := mkw 0x40431038115d0980 0x040431038115d098 0x80033038007f01c4 0x980033038007f01c

def z1026 : W := mkw 0xa1bc4fc26ea2f666 0xda1bc4fc26ea2f66 0x7ffecfe67fe3fefb 0x77ffecfe67fe3fef

def z1027 : W := mkw 0x2008410266224460 0xc200841026622446 0xdf1acb267fe3c7ff 0xfdf1acb267fe3c7f

def z1028 : W := mkw 0x22dff102777b4468 0xe22dff102777b446 0xfbfff3067fff0007 0x1fbfff3067fff000

def z1029 : W := mkw 0x81b40ec02a80b206 0x981b40ec02a80b20 0x79fc0fc03f803e0b 0x679fc0fc03f803e0

def z1030 : W := mkw 0x00f7aeb50000000f 0x000f7aeb50000000 0xfeffffffc060c0c0 0xffeffffffc060c0c

def z1031 : W := mkw 0x704b513ad57f4df0 0x4704b513ad57f4df 0xde1bfb3fc47fc7fd 0xfde1bfb3fc47fc7f

def z1032 : W := mkw 0x22dff387777b446b 0xe22dff387777b446 0xfffff3c7ffff0637 0x5fffff3c7ffff063

def z1033 : W := mkw 0xa1bcefc76ea2f66f 0xda1bcefc76ea2f66 0xfffeffe7ffe3ffff 0xffffeffe7ffe3fff

def z1034 : W := mkw 0xa1bc4fc26ea2f666 0xda1bc4fc26ea2f66 0xfffecfe67fe0fecb 0xffffecfe67fe0fec

def z1035 : W := mkw 0x02dff000777b0008 0xe02dff000777b000 0xfbfff0007fff060f 0x7fbfff0007fff060

def z1036 : W := mkw 0x02dff000777b0008 0xe02dff000777b000 0xfffff3067fff0007 0x5fffff3067fff000

def z1037 : W := mkw 0x81bc0fc06e80f606 0x981bc0fc06e80f60 0xfffecfe67fe0ffcf 0xffffecfe67fe0ffc

def z1038 : W := mkw 0x02dff030777b0008 0xe02dff030777b000 0xfbfff0387fff0007 0x9fbfff0387fff000

def z1039 : W := mkw 0x81bc0fc06e80f606 0x981bc0fc06e80f60 0xf9fd0fc07f9cfe0f 0x6f9fd0fc07f9cfe0

def z1040 : W := mkw 0x81bc0fc06e80f606 0x981bc0fc06e80f60 0x01e000007f80fe0b 0x001e000007f80fe0

def z1041 : W := mkw 0x00d7a2b50000000b 0x000d7a2b50000000 0xee1ff7ff80000000 0xfee1ff7ff8000000

def z1042 : W := mkw 0x0043a03500000009 0x00043a0350000000 0xfe1fffff80000000 0xffe1fffff8000000

def z1043 : W := mkw 0x51bc1f88ef0ded16 0x951bc1f88ef0ded1 0x95f93b19f81fc134 0x995f93b19f81fc13

def z1044 : W := mkw 0xa1bc0fc26e80f666 0x9a1bc0fc26e80f66 0x79fc0fc07f80fffb 0x679fc0fc07f80fff

def z1045 : W := mkw 0x02d7f000337b0008 0xe02d7f000337b000 0xfbfff0003bff0006 0x1fbfff0003bff000

def z1046 : W := mkw 0x00f7aeb50000000f 0x000f7aeb50000000 0xfefff7df80000000 0x5fefff7df8000000

def z1047 : W := mkw 0x809c014066805600 0x8809c01406680560 0x79fc0fc07f80fe0b 0x679fc0fc07f80fe0

def z1048 : W := mkw 0x00f7aeb51050000f 0x000f7aeb51050000 0xfffffffff8600000 0xffffffffff860000

def z1049 : W := mkw 0x81b40ec02a80b206 0x981b40ec02a80b20 0x39e404c07b803803 0x039e404c07b80380

def z1050 : W := mkw 0x81bc0fc06e80f606 0x981bc0fc06e80f60 0x69fc07c03f803e0b 0x669fc07c03f803e0

def z1051 : W := mkw 0x819c01406e80f600 0x9819c01406e80f60 0x11f800007f80fe0b 0x011f800007f80fe0

def z1052 : W := mkw 0xa1bcefc76ea2f66f 0xda1bcefc76ea2f66 0x7ffcffc7ff83fe3b 0x77ffcffc7ff83fe3

def z1053 : W := mkw 0x02d7b00033590008 0xa02d7b0003359000 0x01e000003b9c0002 0x001e000003b9c000

def z1054 : W := mkw 0x819c00406e80b200 0x9819c00406e80b20 0x79fc00007f803803 0x079fc00007f80380

def z1055 : W := mkw 0x22dff002777b0068 0xe22dff002777b006 0xfbfff0267fff00c7 0x1fbfff0267fff00c

def z1056 : W := mkw 0x81bc0fc06e80f606 0x981bc0fc06e80f60 0x11f80fc07f80fe0b 0x611f80fc07f80fe0

def z1057 : W := mkw 0x4243f03d117f0989 0x64243f03d117f098 0x8603f03f807f01c4 0x98603f03f807f01c

def z1058 : W := mkw 0x81bc0fc06e80f606 0x981bc0fc06e80f60 0x7ffccfc67f80fe0b 0x77ffccfc67f80fe0

def z1059 : W := mkw 0x80bc0c406e80b204 0x980bc0c406e80b20 0x79fc0cc07f80fe0b 0x679fc0cc07f80fe0

def z1060 : W := mkw 0x02d7b00033590008 0xa02d7b0003359000 0x21e530007bfc0007 0x021e530007bfc000

def z1061 : W := mkw 0x02dff000777b0008 0xe02dff000777b000 0xfffffb267fff073f 0xffffffb267fff073

def z1062 : W := mkw 0x01bc0f806e00e406 0x901bc0f806e00e40 0x79fc0f007f80f80b 0x279fc0f007f80f80

def z1063 : W := mkw 0x40630c381854a984 0x140630c381854a98 0xfbfbcc38787cf9cf 0xbfbfbcc38787cf9c

def z1064 : W := mkw 0x22dff102777b4468 0xe22dff102777b446 0xfbfffb267fffc1cf 0xbfbfffb267fffc1c

def z1065 : W := mkw 0x40630c381854a984 0x140630c381854a98 0x39e20c20787cf9cf 0x239e20c20787cf9c

def z1066 : W := mkw 0xd0001048818d1b10 0x0d0001048818d1b1 0xc40534d9879f3f3c 0xfc40534d9879f3f3

def z1067 : W := mkw 0x00f7aeb50000000f 0x000f7aeb50000000 0xd6fffbff80000000 0xdd6fffbff8000000

def z1068 : W := mkw 0x02dff285777b000b 0xe02dff285777b000 0xfffff7dfffff0007 0xffffff7dfffff000

def z1069 : W := mkw 0x0043100011590000 0x0004310001159000 0xfde738207fffc7ff 0xffde738207fffc7f

def z1070 : W := mkw 0x00f7aeb50000000f 0x000f7aeb50000000 0xfeffffff80000738 0xffeffffff8000073

def z1071 : W := mkw 0x22dff387777b446b 0xe22dff387777b446 0xfffffbe7ffffc7ff 0xffffffbe7ffffc7f

def z1072 : W := mkw 0x02dff285777b000b 0xe02dff285777b000 0xfffffbe7ffff0007 0xffffffbe7ffff000

def z1073 : W := mkw 0x4063ac3d1854a98d 0x14063ac3d1854a98 0xfffbff3ff87cf9cf 0xffffbff3ff87cf9c

def z1074 : W := mkw 0xa1bc4fc26ea2f666 0xda1bc4fc26ea2f66 0x79fc0fc07fe0fecb 0x679fc0fc07fe0fec

def z1075 : W := mkw 0x81bc0fc06e80f606 0x981bc0fc06e80f60 0x79fc07c07f803e03 0x479fc07c07f803e0

def z1076 : W := mkw 0x20bc4d026e22e464 0xd20bc4d026e22e46 0xfffecf267fe3ffff 0xffffecf267fe3fff

def z1077 : W := mkw 0xf1200fca8884ff76 0x1f1200fca8884ff7 0x04000fff8000fff8 0xe04000fff8000fff

def z1078 : W := mkw 0x81bc0fc56e80f607 0x981bc0fc56e80f60 0x7dfc0fc7ff80fe0b 0x67dfc0fc7ff80fe0

def z1079 : W := mkw 0x81bc0fc06e80f606 0x981bc0fc06e80f60 0x79fc0fc07fe0ffcf 0x679fc0fc07fe0ffc

def z1080 : W := mkw 0x02d7b00033590008 0xa02d7b0003359000 0x63fdf0003b9c0002 0x163fdf0003b9c000

def z1081 : W := mkw 0x8000004000801200 0x0800000400080120 0x79e404c07f803e0b 0x679e404c07f803e0

def z1082 : W := mkw 0x81bc0fc06e80f606 0x981bc0fc06e80f60 0x61fc07c07f80fe0b 0x461fc07c07f80fe0

def z1083 : W := mkw 0xb19c53c2e7ab5672 0xcb19c53c2e7ab567 0x461cf3c787830630 0x5461cf3c78783063

def z1084 : W := mkw 0x40630c381854a984 0x140630c381854a98 0x11e20820787cf8c2 0x011e20820787cf8c

def z1085 : W := mkw 0x40630c381854a984 0x140630c381854a98 0xf9e70cf8787cf9cf 0xef9e70cf8787cf9c

def z1086 : W := mkw 0x81b40ec02a80b206 0x981b40ec02a80b20 0x69e404c03f803803 0x069e404c03f80380

def z1087 : W := mkw 0x81bc0fc06e80f606 0x981bc0fc06e80f60 0x7dfc0fd9ff80fe0b 0xe7dfc0fd9ff80fe0

def z1088 : W := mkw 0x81bc0fc06e80f606 0x981bc0fc06e80f60 0xfdfd3fd9ff83ff3f 0xffdfd3fd9ff83ff3

def z1089 : W := mkw 0x81bc4ec06ea2b206 0xd81bc4ec06ea2b20 0xfbfec4c07fe33807 0x1fbfec4c07fe3380

def z1090 : W := mkw 0x00f7aeb50000000f 0x000f7aeb50000000 0xfeffffff84000609 0xffeffffff8400060

def z1091 : W := mkw 0x0094100023090000 0x8009410002309000 0x21e530003b9c0002 0x021e530003b9c000

def z1092 : W := mkw 0x00f7aeb50000000f 0x000f7aeb50000000 0xfeffffff8000380b 0xffeffffff8000380

def z1093 : W := mkw 0x2008410244224460 0x4200841024422446 0x161acb264463c7fd 0xe161acb264463c7f

def z1094 : W := mkw 0xa1bc4fc26ea2f666 0xda1bc4fc26ea2f66 0xdffacb267fe3ffff 0xfdffacb267fe3fff

def z1095 : W := mkw 0x40630c381854a984 0x140630c381854a98 0xbde30c38787ff9ff 0xbbde30c38787ff9f

def z1096 : W := mkw 0x2000410200224460 0x4200041020022446 0xde1acb260063c7fc 0xfde1acb260063c7f

def z1097 : W := mkw 0x81bc0fc06e80f606 0x981bc0fc06e80f60 0x79fc0fc07b80f802 0x679fc0fc07b80f80

def z1098 : W := mkw 0x81b40fc02a80f606 0x981b40fc02a80f60 0x39e40fc07b80fe0b 0x639e40fc07b80fe0

def z1099 : W := mkw 0xd0001048818d1b10 0x0d0001048818d1b1 0xa40534d9879f3f3f 0x9a40534d9879f3f3

def z1100 : W := mkw 0x224b5102777b4460 0xe224b5102777b446 0xb9e308207fffc7ff 0xab9e308207fffc7f

def z1101 : W := mkw 0x0243f000117b0008 0x60243f000117b000 0xfbe7f0007fff0007 0x1fbe7f0007fff000

def z1102 : W := mkw 0x0243100033590000 0xa024310003359000 0x21e100003b9c0002 0x021e100003b9c000

def z1103 : W := mkw 0xd1200ec88884bb16 0x1d1200ec88884bb1 0x000004d980003800 0x0000004d98000380

def z1104 : W := mkw 0x02dff000777b0008 0xe02dff000777b000 0x7bfec0007fff0007 0x07bfec0007fff000

def z1105 : W := mkw 0x81280fc06e80f606 0x981280fc06e80f60 0x39e00fc07f80fe0b 0x639e00fc07f80fe0

def z1106 : W := mkw 0x02dff000777b0008 0xe02dff000777b000 0xfbfff0007fffc1cf 0x1fbfff0007fffc1c

def z1107 : W := mkw 0x81bcafc56e80f60f 0x981bcafc56e80f60 0x7bfccfc67f80fe0b 0x67bfccfc67f80fe0

def z1108 : W := mkw 0x83bcefc06ea2f60e 0xf83bcefc06ea2f60 0x7bfccfc07f80fe0b 0x67bfccfc07f80fe0

def z1109 : W := mkw 0x00d7a2b50000000b 0x000d7a2b50000000 0xfefff3ff80000000 0xdfefff3ff8000000

def z1110 : W := mkw 0xd0200c488884bb14 0x1d0200c488884bb1 0x04000cd98000ff38 0xe04000cd98000ff3

def z1111 : W := mkw 0x8094004022801200 0x8809400402280120 0x69e404c03f803e0b 0x669e404c03f803e0

def z1112 : W := mkw 0xc0200c780884bb84 0x1c0200c780884bb8 0x00000cf80000ffc8 0xe00000cf80000ffc

def z1113 : W := mkw 0x40630c381854a984 0x140630c381854a98 0xfde30c38787cf9cf 0xffde30c38787cf9c

def z1114 : W := mkw 0x0043100011590000 0x0004310001159000 0x21e530003b9c0002 0x021e530003b9c000

def z1115 : W := mkw 0x209c5102672b4460 0xc209c5102672b446 0xfffffb267fffc7ff 0xffffffb267fffc7f

def z1116 : W := mkw 0x00f7aeb50000000f 0x000f7aeb50000000 0xc61fffff80000000 0xfc61fffff8000000

def z1117 : W := mkw 0x22dff102777b4468 0xe22dff102777b446 0xfffff3067fffc7ff 0x5fffff3067fffc7f

def z1118 : W := mkw 0x02d7b2853359000b 0xa02d7b2853359000 0x21e530c1bb9c0002 0x021e530c1bb9c000

def z1119 : W := mkw 0x00bc4c006e22a004 0xd00bc4c006e22a00 0xfbfecc207fe3f9cf 0xbfbfecc207fe3f9c

def z1120 : W := mkw 0xc1200ffd0884ff87 0x1c1200ffd0884ff8 0x04000fff8000ffc8 0xe04000fff8000ffc

def z1121 : W := mkw 0x00630c001850a004 0x100630c001850a00 0xb9e30c20787cf9cf 0xab9e30c20787cf9c

def z1122 : W := mkw 0x40630c381854a984 0x140630c381854a98 0xbde30c38787cffff 0xebde30c38787cfff

def z1123 : W := mkw 0xd0001048818d1b10 0x0d0001048818d1b1 0xec0734f987ff3fff 0xfec0734f987ff3ff

def z1124 : W := mkw 0x02dff000777b0008 0xe02dff000777b000 0x63fdf0007fff0007 0x163fdf0007fff000

def z1125 : W := mkw 0xd0001048818d1b10 0x0d0001048818d1b1 0xec0534d9879f3e32 0xfec0534d9879f3e3

def z1126 : W := mkw 0x2008410244224460 0x4200841024422446 0x9a1acb264463c7fd 0xa9a1acb264463c7f

def z1127 : W := mkw 0x81b40ec02a80b206 0x981b40ec02a80b20 0x79fc04c03b803802 0x079fc04c03b80380

def z1128 : W := mkw 0xa1bc4fc26ea2f666 0xda1bc4fc26ea2f66 0x67fcc7c63f833e32 0x567fcc7c63f833e3

def z1129 : W := mkw 0x22dff102777b4468 0xe22dff102777b446 0x21e530007fffc7ff 0x021e530007fffc7f

def z1130 : W := mkw 0x81b40ec02a80b206 0x981b40ec02a80b20 0x61fc07c03b803802 0x461fc07c03b80380

def z1131 : W := mkw 0x4243f008117f0908 0x64243f008117f090 0x8203f018007f0104 0x98203f018007f010

def z1132 : W := mkw 0x00f7aeb50000000f 0x000f7aeb50000000 0xfeffffff806001c4 0xffeffffff806001c

def z1133 : W := mkw 0x02dff100777b4408 0xe02dff100777b440 0xfbfffb007fffc007 0x1fbfffb007fffc00

def z1134 : W := mkw 0x009c100067090000 0x8009c10006709000 0x79fd30007f9c0003 0x079fd30007f9c000

def z1135 : W := mkw 0x02f7aeb53250000f 0xa02f7aeb53250000 0xffffffffb8000000 0xfffffffffb800000

def z1136 : W := mkw 0x00bc0e806e00a006 0x900bc0e806e00a00 0x79fc0fc07f80f80b 0x679fc0fc07f80f80

def z1137 : W := mkw 0xd1200ec88884bb16 0x1d1200ec88884bb1 0x040004d980003f38 0xe040004d980003f3

def z1138 : W := mkw 0x80200c400880b204 0x180200c400880b20 0x39e00c007f80fe0b 0x239e00c007f80fe0

def z1139 : W := mkw 0xe1284ffa4ca6ffe6 0x5e1284ffa4ca6ffe 0xde1acffe4463fffd 0xfde1acffe4463fff

def z1140 : W := mkw 0x00f7aeb50800a00f 0x100f7aeb50800a00 0xfeffffff8000f808 0xffeffffff8000f80

def z1141 : W := mkw 0x81b40ec02a80b206 0x981b40ec02a80b20 0x61e404c03f803e02 0x461e404c03f803e0

def z1142 : W := mkw 0x80200c400880b204 0x180200c400880b20 0x69e404c03f803e0b 0x669e404c03f803e0

def z1143 : W := mkw 0xa1bc4fc26ea2f666 0xda1bc4fc26ea2f66 0xfffecfe67f83fe3b 0xffffecfe67f83fe3

def z1144 : W := mkw 0x02d7b00033590008 0xa02d7b0003359000 0xb9e730003b9c0002 0x0b9e730003b9c000

def z1145 : W := mkw 0x02dff000777b0008 0xe02dff000777b000 0xfffff019ffff0007 0x9fffff019ffff000

def z1146 : W := mkw 0x81bc0fc06e80f606 0x981bc0fc06e80f60 0xfffecfe67f83ff3f 0xffffecfe67f83ff3

def z1147 : W := mkw 0xc1200ef80884bb86 0x1c1200ef80884bb8 0x000004d800003800 0x0000004d80000380

def z1148 : W := mkw 0x5243f03d917f0919 0x65243f03d917f091 0x8603f03f807f0134 0x98603f03f807f013

def z1149 : W := mkw 0x02dff000777b0008 0xe02dff000777b000 0x73fff0007fff0002 0x173fff0007fff000

def z1150 : W := mkw 0x50431038915d0990 0x050431038915d099 0x80033039807c01c4 0x880033039807c01c

def z1151 : W := mkw 0xa1bc4fc26ea2f666 0xda1bc4fc26ea2f66 0xf9fe0fe07fe3ffff 0xef9fe0fe07fe3fff

def z1152 : W := mkw 0x81b40fc02a80f606 0x981b40fc02a80f60 0x79fc0fc03b80fe0a 0x679fc0fc03b80fe0

def z1153 : W := mkw 0x229c5102777b4460 0xe229c5102777b446 0xfffecb267fffc7ff 0xffffecb267fffc7f

def z1154 : W := mkw 0x00f7aeb50000000f 0x000f7aeb50000000 0xfeffffff87800003 0xffeffffff8780000

def z1155 : W := mkw 0xf108514aefafff70 0xdf108514aefafff7 0x010000007fffffff 0x0010000007ffffff

def z1156 : W := mkw 0x40630c381854a984 0x140630c381854a98 0xb9e30820787cf9cf 0x0b9e30820787cf9c

def z1157 : W := mkw 0x22dff037777b0069 0xe22dff037777b006 0xfffff03fffff01f7 0x9fffff03fffff01f

def z1158 : W := mkw 0x00f7aeb50000000f 0x000f7aeb50000000 0xfeffffff84030630 0xffeffffff8403063

def z1159 : W := mkw 0x02dff100777b4408 0xe02dff100777b440 0xfffffb007fffc73f 0xffffffb007fffc73

def z1160 : W := mkw 0x02dfb10077594408 0xa02dfb1007759440 0x79fd3b007f9cc60b 0x679fd3b007f9cc60

def z1161 : W := mkw 0x0294100033590000 0xa029410003359000 0x21e400003b9c0002 0x021e400003b9c000

def z1162 : W := mkw 0x22dff102777b4468 0xe22dff102777b446 0xfffffb267fffc6f7 0x5fffffb267fffc6f

def z1163 : W := mkw 0x40630c381854a984 0x140630c381854a98 0xbbfbcf3e787cf9cf 0xabbfbcf3e787cf9c

def z1164 : W := mkw 0xd0001048818d1b10 0x0d0001048818d1b1 0xee07f4ff879f3f3f 0xfee07f4ff879f3f3

def z1165 : W := mkw 0x2008410244224460 0x4200841024422446 0x961acb264463c7fd 0x9961acb264463c7f

def z1166 : W := mkw 0x81bc4fc06ea2f606 0xd81bc4fc06ea2f60 0xfffecfe67fe3fe0f 0xffffecfe67fe3fe0

def z1167 : W := mkw 0x02dff000777b0008 0xe02dff000777b000 0xfffff0007fff0137 0x9fffff0007fff013

def z1168 : W := mkw 0xd0200c788884bb94 0x1d0200c788884bb9 0xdc020cf9c463fffd 0xfdc020cf9c463fff

def z1169 : W := mkw 0xa1bc4fc26ea2f666 0xda1bc4fc26ea2f66 0x79fc0fc07f83fe3b 0x679fc0fc07f83fe3

def z1170 : W := mkw 0x81b4aec52a80b20f 0x981b4aec52a80b20 0x21e434c1bb803802 0x021e434c1bb80380

def z1171 : W := mkw 0xc1200fc80884ff06 0x1c1200fc80884ff0 0x00000fd80000ff08 0xe00000fd80000ff0

def z1172 : W := mkw 0x42435038117f0980 0x642435038117f098 0x80030038007f01c4 0x880030038007f01c

def z1173 : W := mkw 0x81bc0fc06e80f606 0x981bc0fc06e80f60 0x79fc0fc07f83ff3f 0x679fc0fc07f83ff3

def z1174 : W := mkw 0xf0284d7acca6fff4 0x5f0284d7acca6fff 0xde1acfffc463fffd 0xfde1acfffc463fff

def z1175 : W := mkw 0xd1280fc8cc84ff16 0x1d1280fc8cc84ff1 0xdc180fd9c403ff3d 0xfdc180fd9c403ff3

def z1176 : W := mkw 0x22dff102777b4468 0xe22dff102777b446 0x33fffb267bfcc0c2 0x033fffb267bfcc0c

def z1177 : W := mkw 0x400000081854a980 0x1400000081854a98 0x39e00000787cf9cf 0x039e00000787cf9c

def z1178 : W := mkw 0x81bc0fc06e80f606 0x981bc0fc06e80f60 0xf9fc0fc07f80ff0f 0xef9fc0fc07f80ff0

def z1179 : W := mkw 0x81200fc00880f606 0x181200fc00880f60 0x79e40fc07f80fe0b 0x679e40fc07f80fe0

def z1180 : W := mkw 0x81bc0fc06e80f606 0x981bc0fc06e80f60 0xffffffffff80fe0b 0xfffffffffff80fe0

def z1181 : W := mkw 0x40630c381854a984 0x140630c381854a98 0x01e00000787cf9cf 0x001e00000787cf9c

def z1182 : W := mkw 0x02dff000777b0008 0xe02dff000777b000 0xfbfff0003f9f0002 0x1fbfff0003f9f000

def z1183 : W := mkw 0xd0001048818d1b10 0x0d0001048818d1b1 0x640534d9879f3f3a 0xf640534d9879f3f3

def z1184 : W := mkw 0x2008410244224460 0x4200841024422446 0xfe1bcf3e4463c7fd 0xffe1bcf3e4463c7f

def z1185 : W := mkw 0x40630c381854a984 0x140630c381854a98 0xbde30f3e787cf9cf 0xebde30f3e787cf9c

def z1186 : W := mkw 0xd0001048818d1b10 0x0d0001048818d1b1 0xec0534d9c7ffffff 0xfec0534d9c7fffff

def z1187 : W := mkw 0x81bc0ec06e80b206 0x981bc0ec06e80b20 0x21e404c07f803803 0x021e404c07f80380

def z1188 : W := mkw 0xa1bc4fc26ea2f666 0xda1bc4fc26ea2f66 0x7ffecfe67fe0fffb 0xe7ffecfe67fe0fff

def z1189 : W := mkw 0x2008410244224460 0x4200841024422446 0xde1acfffc463c7fd 0xfde1acfffc463c7f

def z1190 : W := mkw 0x81bc4fc06ea2f606 0xd81bc4fc06ea2f60 0x79fc0fc07fe3fe0f 0x679fc0fc07fe3fe0

def z1191 : W := mkw 0x20ffefb74422446f 0x420ffefb74422446 0x20e534d9c463c7fd 0x020e534d9c463c7f

def z1192 : W := mkw 0x0043100011590000 0x0004310001159000 0xb9e730007bfc0007 0x0b9e730007bfc000

def z1193 : W := mkw 0x02dff030777b0088 0xe02dff030777b008 0xfbfff0207fff00c7 0x1fbfff0207fff00c

def z1194 : W := mkw 0x02d7b00033590008 0xa02d7b0003359000 0xa9e530003b9c0007 0x0a9e530003b9c000

def z1195 : W := mkw 0x81b40ef52a80b207 0x981b40ef52a80b20 0x21e404d9bb803802 0x021e404d9bb80380

def z1196 : W := mkw 0x81bc0fc06e80f606 0x981bc0fc06e80f60 0xf9fe0fc07fe0fe0f 0x6f9fe0fc07fe0fe0

def z1197 : W := mkw 0x81b40fc02a80f606 0x981b40fc02a80f60 0x69e40fc03f80fe0b 0x669e40fc03f80fe0

def z1198 : W := mkw 0x40630c381854a984 0x140630c381854a98 0x99e20820787cf9cf 0xa99e20820787cf9c

def z1199 : W := mkw 0x0043000010500000 0x0004300001050000 0xf9e700007ffc0007 0x0f9e700007ffc000

def z1200 : W := mkw 0x81bc0ff56e80f607 0x981bc0ff56e80f60 0x79fc0fe67f80fe0b 0x679fc0fe67f80fe0

def z1201 : W := mkw 0x809c404066a21200 0xc809c404066a2120 0xfffec4c07fe33f3f 0xffffec4c07fe33f3

def z1202 : W := mkw 0x81bc0fc06e80f606 0x981bc0fc06e80f60 0xf9fd0fd87f80fe0b 0xef9fd0fd87f80fe0

def z1203 : W := mkw 0x4243f038117f0988 0x64243f038117f098 0x8203f018007f0004 0x18203f018007f000

def z1204 : W := mkw 0x81bc0ff56e80f607 0x981bc0ff56e80f60 0xfdfd3fffff80fe0b 0xffdfd3fffff80fe0

def z1205 : W := mkw 0x81bc0ff06e80f606 0x981bc0ff06e80f60 0x79fc0ff87f80fe0b 0xe79fc0ff87f80fe0

def z1206 : W := mkw 0x029cf000777b0008 0xe029cf000777b000 0x7bfcf0007fff0007 0x17bfcf0007fff000

def z1207 : W := mkw 0x81b40ec02a80b206 0x981b40ec02a80b20 0x01e000003b803802 0x001e000003b80380

def z1208 : W := mkw 0x00b4aeb50000000f 0x000b4aeb50000000 0xde1effff80000000 0xfde1effff8000000

def z1209 : W := mkw 0xa19c41426ea2f660 0xda19c41426ea2f66 0xfffecb267fe3ffff 0xffffecb267fe3fff

def z1210 : W := mkw 0x81bc4fc06ea2f606 0xd81bc4fc06ea2f60 0xfffecfc07fe3ff3f 0xffffecfc07fe3ff3

def z1211 : W := mkw 0x5243f008917f0918 0x65243f008917f091 0x8203f019807f0004 0x18203f019807f000

def z1212 : W := mkw 0x00f7aeb50800a00f 0x100f7aeb50800a00 0xfffffffff800c000 0xffffffffff800c00

def z1213 : W := mkw 0x81bc0fc06e80f606 0x981bc0fc06e80f60 0x39e40cc07f80fe0b 0x239e40cc07f80fe0

def z1214 : W := mkw 0x024b5000777b0000 0xe024b5000777b000 0x21e100007fff0007 0x021e100007fff000

def z1215 : W := mkw 0x80b40ec00880b206 0x180b40ec00880b20 0x79fc0fc07f80fe0b 0x679fc0fc07f80fe0

def z1216 : W := mkw 0xd0001048818d1b10 0x0d0001048818d1b1 0x680534d9879f3f3f 0x6680534d9879f3f3

def z1217 : W := mkw 0x02dff000777b0008 0xe02dff000777b000 0xfffffb267fffc1cf 0xffffffb267fffc1c

def z1218 : W := mkw 0x02dff000777b0008 0xe02dff000777b000 0xfbfff4007fff380f 0x3fbfff4007fff380

def z1219 : W := mkw 0x81280d406e80f604 0x981280d406e80f60 0x11e008007f80fe0b 0x011e008007f80fe0

def z1220 : W := mkw 0xa1bc4fc26ea2f666 0xda1bc4fc26ea2f66 0x7ffccfc67fe3ffff 0x77ffccfc67fe3fff

def z1221 : W := mkw 0x81bc0ec06e80b206 0x981bc0ec06e80b20 0x31fc04c07b803802 0x031fc04c07b80380

def z1222 : W := mkw 0x5243b008915d0918 0x25243b008915d091 0x84013019801f0134 0x984013019801f013

def z1223 : W := mkw 0x02d7f000337b0008 0xe02d7f000337b000 0x23e7f0003bfc0002 0x023e7f0003bfc000

def z1224 : W := mkw 0x004b000076500000 0x8004b00007650000 0xb9e300007ffc0007 0x0b9e300007ffc000

def z1225 : W := mkw 0x02d7b00033590008 0xa02d7b0003359000 0xa1e730003bfc0006 0x0a1e730003bfc000

def z1226 : W := mkw 0xd0001048818d1b10 0x0d0001048818d1b1 0xec053fff879f3f3f 0xfec053fff879f3f3

def z1227 : W := mkw 0x4063ac3d1854a98d 0x14063ac3d1854a98 0xffe7fcfff87cf9cf 0xfffe7fcfff87cf9c

def z1228 : W := mkw 0x40630eb81854a986 0x140630eb81854a98 0xb9e30ff8787cf9cf 0xeb9e30ff8787cf9c

def z1229 : W := mkw 0x02dff000777b0008 0xe02dff000777b000 0x13fac0007bfc0002 0x013fac0007bfc000

def z1230 : W := mkw 0x40200c081854a984 0x140200c081854a98 0xb9e10c18787cf9cf 0xab9e10c18787cf9c

def z1231 : W := mkw 0x0094a2850000000b 0x00094a2850000000 0xfe1fffff80000000 0xffe1fffff8000000

def z1232 : W := mkw 0x02df5000777b0000 0xe02df5000777b000 0xf9ff00007fff0007 0x0f9ff00007fff000

def z1233 : W := mkw 0x40630ebd1854a987 0x140630ebd1854a98 0xfde73ffff87cf9cf 0xffde73ffff87cf9c

def z1234 : W := mkw 0x00f7aeb50000000f 0x000f7aeb50000000 0xbaffffff80000000 0xabaffffff8000000

def z1235 : W := mkw 0x02dff000777b0008 0xe02dff000777b000 0x93fbf0007fff0007 0x193fbf0007fff000

def z1236 : W := mkw 0xd1200fc88884ff16 0x1d1200fc88884ff1 0x00000fd98000fe08 0x600000fd98000fe0

def z1237 : W := mkw 0xd0001048818d1b10 0x0d0001048818d1b1 0xee1df7df879f3f3f 0xfee1df7df879f3f3

def z1238 : W := mkw 0x02dff285777b000b 0xe02dff285777b000 0xfbfff3067fff0007 0x1fbfff3067fff000

def z1239 : W := mkw 0x02dff000777b0008 0xe02dff000777b000 0xebfdf0003f9f0007 0x1ebfdf0003f9f000

def z1240 : W := mkw 0xd0001048818d1b10 0x0d0001048818d1b1 0xe40534d9879f3f36 0xde40534d9879f3f3

def z1241 : W := mkw 0x00f7aeb50000000f 0x000f7aeb50000000 0x7efdffdf80000000 0x77efdffdf8000000

def z1242 : W := mkw 0x81b40ec02a80b206 0x981b40ec02a80b20 0x21e404c03f803e0b 0x021e404c03f803e0

def z1243 : W := mkw 0x81bc0ec06e80b206 0x981bc0ec06e80b20 0x61fc04c03f803802 0x061fc04c03f80380

def z1244 : W := mkw 0x02d7f000337b0008 0xe02d7f000337b000 0x21e530003bff0006 0x021e530003bff000

def z1245 : W := mkw 0xa1bc0ff76e80f667 0x9a1bc0ff76e80f66 0x7dfc0fffff80fffb 0xe7dfc0fffff80fff

def z1246 : W := mkw 0x50431038915d0990 0x050431038915d099 0x00013019801c0000 0x000013019801c000

def z1247 : W := mkw 0xa1bc4fc26ea2f666 0xda1bc4fc26ea2f66 0x13facb267fe3ffff 0x013facb267fe3fff

def z1248 : W := mkw 0x81bc0fc06e80f606 0x981bc0fc06e80f60 0x31fc0fc07b80fe0a 0x631fc0fc07b80fe0

def z1249 : W := mkw 0x02d7b00033590008 0xa02d7b0003359000 0xede530003f9f073f 0xfede530003f9f073

def z1250 : W := mkw 0x02dff000777b0008 0xe02dff000777b000 0xfbfff8207fff0007 0xbfbfff8207fff000

def z1251 : W := mkw 0x02dff000777b0008 0xe02dff000777b000 0xfbfff4187fff0007 0xbfbfff4187fff000

def z1252 : W := mkw 0x0000000000000000 0x0000000000000000 0xde1acb264463c7fd 0xfde1acb264463c7f

def z1253 : W := mkw 0xc1200ff80884ff86 0x1c1200ff80884ff8 0x00000fd80000fe08 0x600000fd80000fe0

def z1254 : W := mkw 0x02dff000777b0008 0xe02dff000777b000 0xb9e730007fff0007 0x0b9e730007fff000

def z1255 : W := mkw 0x0043100011590000 0x0004310001159000 0xe9e530003f9f0007 0x1e9e530003f9f000

def z1256 : W := mkw 0x02dff000777b0008 0xe02dff000777b000 0xfffff0007fff0007 0xffffff0007fff000

def z1257 : W := mkw 0x624bf13a557f4de8 0x6624bf13a557f4de 0xde1bfb3e447fc7fd 0xfde1bfb3e447fc7f

def z1258 : W := mkw 0x81b40ec02a80b206 0x981b40ec02a80b20 0x21e40cc03b80f80a 0x221e40cc03b80f80

def z1259 : W := mkw 0x0094a2850000000b 0x00094a2850000000 0x461cf7df80000000 0xf461cf7df8000000

def z1260 : W := mkw 0x00f7aeb50000000f 0x000f7aeb50000000 0xfffffffff8000003 0xffffffffff800000

def z1261 : W := mkw 0x02d7b00033590008 0xa02d7b0003359000 0x21e530003f9f0007 0x021e530003f9f000

def z1262 : W := mkw 0x00df100077590000 0x800df10007759000 0xf9ff30007fff0007 0x1f9ff30007fff000

def z1263 : W := mkw 0x02dff035777b0009 0xe02dff035777b000 0xfbfff019ffff0007 0x1fbfff019ffff000

def z1264 : W := mkw 0x724bf10ad57f4d78 0x6724bf10ad57f4d7 0xde1bfb3fc47fc7fd 0xfde1bfb3fc47fc7f

def z1265 : W := mkw 0x02dff000777b0008 0xe02dff000777b000 0x21e530007bfc0002 0x021e530007bfc000

def z1266 : W := mkw 0xf008514addfffff0 0x5f008514addfffff 0x010000007fffffff 0x0010000007ffffff

def z1267 : W := mkw 0x819c03c06e80f602 0x9819c03c06e80f60 0x79fc03c07f80fe0b 0x479fc03c07f80fe0

def z1268 : W := mkw 0x40630c381854a984 0x140630c381854a98 0xa1e30438787cf9cf 0x8a1e30438787cf9c

def z1269 : W := mkw 0x81bc4fc06ea2f606 0xd81bc4fc06ea2f60 0xfbfecfe07fe3ffcf 0xffbfecfe07fe3ffc

def z1270 : W := mkw 0x00d7a2b50000000b 0x000d7a2b50000000 0x461df3df80000000 0x5461df3df8000000

def z1271 : W := mkw 0x02d7b00033590008 0xa02d7b0003359000 0x69e530003f9c0003 0x069e530003f9c000

def z1272 : W := mkw 0x02d7f000337b0008 0xe02d7f000337b000 0xbbe7f0007bff0007 0x1bbe7f0007bff000

def z1273 : W := mkw 0x00f7aeb50000000f 0x000f7aeb50000000 0xe6fff7ff80000000 0xde6fff7ff8000000

def z1274 : W := mkw 0x02dfb00077590008 0xa02dfb0007759000 0x21e530007f9c0003 0x021e530007f9c000

def z1275 : W := mkw 0x7043503a917f09f0 0x47043503a917f09f 0x8603f03f807f01f4 0x98603f03f807f01f

def z1276 : W := mkw 0x40630c381854a984 0x140630c381854a98 0xbde30cf9f87cf9cf 0xebde30cf9f87cf9c

def z1277 : W := mkw 0x2008410244224460 0x4200841024422446 0xfffacb267c63c7ff 0xffffacb267c63c7f

def z1278 : W := mkw 0xf0200d7a8884fff4 0x1f0200d7a8884fff 0x04000fff8000fff8 0xe04000fff8000fff

def z1279 : W := mkw 0x40630c381854a984 0x140630c381854a98 0xb9e30c38787cf8c2 0xab9e30c38787cf8c

def z1280 : W := mkw 0x40200c080804a904 0x140200c080804a90 0xb9e30c38787cf9cf 0xab9e30c38787cf9c

def z1281 : W := mkw 0x81bc4fc06ea2f606 0xd81bc4fc06ea2f60 0x7bfccfc07f83fe0b 0x77bfccfc07f83fe0

def z1282 : W := mkw 0x81bc0fc06e80f606 0x981bc0fc06e80f60 0x39fc0fc07b80f80b 0x239fc0fc07b80f80

def z1283 : W := mkw 0x81bc0fc06e80f606 0x981bc0fc06e80f60 0x21e404c07b80f802 0x021e404c07b80f80

def z1284 : W := mkw 0x00630c301850a084 0x100630c301850a08 0xb9e30c20787cf8cf 0x2b9e30c20787cf8c

def z1285 : W := mkw 0x004b5000557b0000 0x4004b5000557b000 0xfbfff0007fff0007 0x1fbfff0007fff000

def z1286 : W := mkw 0xd0200c788884bb94 0x1d0200c788884bb9 0x000004d980003800 0x0000004d98000380

def z1287 : W := mkw 0x40630c381854a984 0x140630c381854a98 0xb9e30c38787cf8c7 0x0b9e30c38787cf8c

def z1288 : W := mkw 0x80bc0ec066801206 0x880bc0ec06680120 0x79fc0fc07f803e0b 0x679fc0fc07f803e0

def z1289 : W := mkw 0x424bf038557f0988 0x6424bf038557f098 0xda1bf838447fc1cd 0xbda1bf838447fc1c

def z1290 : W := mkw 0x81bc0fc06e80f606 0x981bc0fc06e80f60 0xfdfe0fe07fe3ffff 0xffdfe0fe07fe3fff

def z1291 : W := mkw 0x81bc0fc06e80f606 0x981bc0fc06e80f60 0x21e40fc07f80fe0b 0x621e40fc07f80fe0

def z1292 : W := mkw 0x81bc0ec06e80b206 0x981bc0ec06e80b20 0x79fc04c07f803e0b 0x679fc04c07f803e0

def z1293 : W := mkw 0x0000000000000000 0x0000000000000000 0xee1df7df80000000 0xfee1df7df8000000

def z1294 : W := mkw 0x4063ac3d1854a98d 0x14063ac3d1854a98 0xbbe3cc3e787cf9cf 0xabbe3cc3e787cf9c

def z1295 : W := mkw 0x02085000777b0000 0xe02085000777b000 0x39e000007fff0007 0x039e000007fff000

def z1296 : W := mkw 0x40630ebd1854a987 0x140630ebd1854a98 0xb9e30f3e787cf9cf 0xab9e30f3e787cf9c

def z1297 : W := mkw 0x00f7aeb51050000f 0x000f7aeb51050000 0xfeffffff807c0004 0xffeffffff807c000

def z1298 : W := mkw 0x03dff380777b440a 0xe03dff380777b440 0xfbfff3007fff0007 0x1fbfff3007fff000

def z1299 : W := mkw 0x02dff100777b4408 0xe02dff100777b440 0xfbfff0007fffc60f 0x1fbfff0007fffc60

def z1300 : W := mkw 0xa1bc4fc26ea2f666 0xda1bc4fc26ea2f66 0xfffccfc67f83ff3f 0xffffccfc67f83ff3

def z1301 : W := mkw 0xa1bc0fc26e80f666 0x9a1bc0fc26e80f66 0xfdfc0fe67f83ffff 0xffdfc0fe67f83fff

def z1302 : W := mkw 0x22dff102777b4468 0xe22dff102777b446 0xfffffb067fffc63f 0x7fffffb067fffc63

def z1303 : W := mkw 0x809c004066801200 0x8809c00406680120 0x79fc04c07f803803 0x079fc04c07f80380

def z1304 : W := mkw 0x009c00006e00a000 0x9009c00006e00a00 0x79fc00007f80f80b 0x079fc00007f80f80

def z1305 : W := mkw 0x40630c381854a984 0x140630c381854a98 0x91e30c38787cf9cc 0xa91e30c38787cf9c

def z1306 : W := mkw 0x81bc0fc06e80f606 0x981bc0fc06e80f60 0x7dfc0fc07f83fe3b 0x77dfc0fc07f83fe3

def z1307 : W := mkw 0x40200c381854a984 0x140200c381854a98 0x39e00c38787cf9cf 0xa39e00c38787cf9c

def z1308 : W := mkw 0x02dff000777b0008 0xe02dff000777b000 0xbbfbc0007fff0007 0x0bbfbc0007fff000

def z1309 : W := mkw 0xe1200ffa0884ffe6 0x1e1200ffa0884ffe 0x04000ffe0000fff8 0xe04000ffe0000fff

def z1310 : W := mkw 0x40630c381854a984 0x140630c381854a98 0xf9e30c387c7ff9cf 0xbf9e30c387c7ff9c

def z1311 : W := mkw 0x00b4aeb50000000f 0x000b4aeb50000000 0xee1dffff80000000 0xfee1dffff8000000

def z1312 : W := mkw 0x00d7a2850000000b 0x000d7a2850000000 0xfefff7df80000000 0xffefff7df8000000

def z1313 : W := mkw 0x81bc0fc06e80f606 0x981bc0fc06e80f60 0xfdfc0fc07f80fe0b 0xffdfc0fc07f80fe0

def z1314 : W := mkw 0x00d7b00011590008 0x000d7b0001159000 0xfbfff0007fff0007 0x1fbfff0007fff000

def z1315 : W := mkw 0x81bc0fc06e80f606 0x981bc0fc06e80f60 0x79fc0fc07f80f803 0x079fc0fc07f80f80

def z1316 : W := mkw 0xd0001048818d1b10 0x0d0001048818d1b1 0x200534d9879f3e32 0x0200534d9879f3e3

def z1317 : W := mkw 0x404300081854a980 0x1404300081854a98 0x11e20000787cf9cf 0x011e20000787cf9c

def z1318 : W := mkw 0x02dfb00077590008 0xa02dfb0007759000 0x31fd30007b9c0002 0x031fd30007b9c000

def z1319 : W := mkw 0x819400402a80b200 0x9819400402a80b20 0x21e400003b803802 0x021e400003b80380

def z1320 : W := mkw 0x81bc0fc06e80f606 0x981bc0fc06e80f60 0x79fd3fd9ff80fe0b 0x679fd3fd9ff80fe0

def z1321 : W := mkw 0x40630c381854a984 0x140630c381854a98 0x31e30c38787cf9ca 0xa31e30c38787cf9c

def z1322 : W := mkw 0xa1bc4fc26ea2f666 0xda1bc4fc26ea2f66 0xfffecfc67fe3fe3f 0x7fffecfc67fe3fe3

def z1323 : W := mkw 0x81b40ec02a80b206 0x981b40ec02a80b20 0xb9e60ce07be0f9cf 0xab9e60ce07be0f9c

def z1324 : W := mkw 0x81b40ec02a80b206 0x981b40ec02a80b20 0x39e40cc03b803802 0x239e40cc03b80380

def z1325 : W := mkw 0x02d7b03533590009 0xa02d7b0353359000 0xa7e7f03fbb9c0002 0x9a7e7f03fbb9c000

def z1326 : W := mkw 0x81b40ec02a80b206 0x981b40ec02a80b20 0x21e40fc03b803802 0x621e40fc03b80380

def z1327 : W := mkw 0x81200c402a80b204 0x981200c402a80b20 0x39e00c007b80f80b 0x239e00c007b80f80

def z1328 : W := mkw 0x22dff102777b4468 0xe22dff102777b446 0xfbfffb007fffc7ff 0x7fbfffb007fffc7f

def z1329 : W := mkw 0x40630c381854a984 0x140630c381854a98 0xfde73cf9fc7fffff 0xffde73cf9fc7ffff

def z1330 : W := mkw 0x40630c381854a984 0x140630c381854a98 0x31e30c38787cf9cf 0x031e30c38787cf9c

def z1331 : W := mkw 0x029c5000777b0000 0xe029c5000777b000 0xf9fd30007fff0007 0x1f9fd30007fff000

def z1332 : W := mkw 0x02dff000777b0008 0xe02dff000777b000 0xbbfff0007bfc0007 0x0bbfff0007bfc000

def z1333 : W := mkw 0x00f7aeb50000000f 0x000f7aeb50000000 0x56feffff80000000 0xf56feffff8000000

def z1334 : W := mkw 0x2008410244224460 0x4200841024422446 0x561acb264463c7f8 0xf561acb264463c7f

def z1335 : W := mkw 0x81b40fc02a80f606 0x981b40fc02a80f60 0x21e404c03b80fe0a 0x021e404c03b80fe0

def z1336 : W := mkw 0x819c01406e80f600 0x9819c01406e80f60 0x79fc04c07f80fe0b 0x679fc04c07f80fe0

def z1337 : W := mkw 0x029c100077590000 0xa029c10007759000 0x79fc00007f9c0003 0x079fc00007f9c000

def z1338 : W := mkw 0x00f7aeb50000000f 0x000f7aeb50000000 0xb6ffffff80000000 0x9b6ffffff8000000

def z1339 : W := mkw 0x40630c381854a984 0x140630c381854a98 0xf9e30c387c7cffcf 0xef9e30c387c7cffc

def z1340 : W := mkw 0x81bc0fc06e80f606 0x981bc0fc06e80f60 0x79fc0fc03f803e02 0x679fc0fc03f803e0

def z1341 : W := mkw 0x02d7b00033590008 0xa02d7b0003359000 0xf9e730007fff0007 0x1f9e730007fff000

def z1342 : W := mkw 0x81280d406e80f604 0x981280d406e80f60 0x79f80f007f80fe0b 0x679f80f007f80fe0

def z1343 : W := mkw 0xd0001048818d1b10 0x0d0001048818d1b1 0xe80534d9879f3f3f 0x1e80534d9879f3f3

def z1344 : W := mkw 0x81bc0fc06e80f606 0x981bc0fc06e80f60 0x61fc0fc03f80fe0a 0x661fc0fc03f80fe0

def z1345 : W := mkw 0x02dff000777b0008 0xe02dff000777b000 0xe3fff0003fff0006 0x1e3fff0003fff000

def z1346 : W := mkw 0x81b40ec02a80b206 0x981b40ec02a80b20 0x31e40cc07b80f802 0x031e40cc07b80f80

def z1347 : W := mkw 0x80200c400880b204 0x180200c400880b20 0x39e40cc07b80f80b 0x239e40cc07b80f80

def z1348 : W := mkw 0xd0001048818d1b10 0x0d0001048818d1b1 0x6c0534d9879f3e3b 0x76c0534d9879f3e3

def z1349 : W := mkw 0x02dff000777b0008 0xe02dff000777b000 0xfbfff8007fffc00f 0x3fbfff8007fffc00

def z1350 : W := mkw 0x40630c3d1854a985 0x140630c3d1854a98 0xbde30c3ff87cf9cf 0xabde30c3ff87cf9c

def z1351 : W := mkw 0x009c110067094400 0x8009c11006709440 0xfdfd3b007f9fc73f 0xffdfd3b007f9fc73

def z1352 : W := mkw 0xa1b40fc22a80f666 0x9a1b40fc22a80f66 0x25e40fe63b80fffa 0xe25e40fe63b80fff

def z1353 : W := mkw 0x00f7aeb50000000f 0x000f7aeb50000000 0x36ffffff80000000 0xe36ffffff8000000

def z1354 : W := mkw 0x4063aebd1854a98f 0x14063aebd1854a98 0xbfe3fffff87cf9cf 0xfbfe3fffff87cf9c

def z1355 : W := mkw 0x029cf000672b0008 0xe029cf000672b000 0xfbfdf0007f9f0007 0x1fbfdf0007f9f000

def z1356 : W := mkw 0x22dff002777b0068 0xe22dff002777b006 0xfffffb267fff01f7 0xffffffb267fff01f

def z1357 : W := mkw 0x81bc0fc06e80f606 0x981bc0fc06e80f60 0x71fc0fc07f80fe02 0x471fc0fc07f80fe0

def z1358 : W := mkw 0x02d7b00033590008 0xa02d7b0003359000 0x33fff0003b9c0002 0x033fff0003b9c000

def z1359 : W := mkw 0x80280d404c80f604 0x180280d404c80f60 0x79fc0fc07f80fe0b 0x679fc0fc07f80fe0

def z1360 : W := mkw 0xd0200c788884bb94 0x1d0200c788884bb9 0x00000c380000fff8 0xa00000c380000fff

def z1361 : W := mkw 0x00d7000032500000 0x800d700003250000 0x21e500003b9c0002 0x021e500003b9c000

def z1362 : W := mkw 0x81bc0fc06e80f606 0x981bc0fc06e80f60 0xfbfecfc07f80fe0b 0x7fbfecfc07f80fe0

def z1363 : W := mkw 0x2008410244224460 0x4200841024422446 0xde1bfb3fc463c7fd 0xfde1bfb3fc463c7f

def z1364 : W := mkw 0x809c004066801200 0x8809c00406680120 0x79fc00007f803e0b 0x079fc00007f803e0

def z1365 : W := mkw 0x02dff000777b0008 0xe02dff000777b000 0xfffff0007fff0637 0x5fffff0007fff063

def z1366 : W := mkw 0x40630c381854a984 0x140630c381854a98 0xf9e73c38787cf9cf 0xbf9e73c38787cf9c

def z1367 : W := mkw 0x22dff102777b4468 0xe22dff102777b446 0xfffff3267fff07f7 0xdfffff3267fff07f

def z1368 : W := mkw 0x81bc0fc06e80f606 0x981bc0fc06e80f60 0x7bfecfe67f80fe0b 0x67bfecfe67f80fe0

def z1369 : W := mkw 0xd0001048818d1b10 0x0d0001048818d1b1 0xfc1d3fd9879f3f3f 0xffc1d3fd9879f3f3

def z1370 : W := mkw 0x2008410244224460 0x4200841024422446 0xfe1bcb26447fc7ff 0xffe1bcb26447fc7f

def z1371 : W := mkw 0xd0200c788884bb94 0x1d0200c788884bb9 0x00000cf98000f9c8 0xa00000cf98000f9c

def z1372 : W := mkw 0x2008410244224460 0x4200841024422446 0xfe1acf264463ffff 0xffe1acf264463fff

def z1373 : W := mkw 0xd0001048818d1b10 0x0d0001048818d1b1 0xfc073cf9879f3f3f 0xffc073cf9879f3f3

def z1374 : W := mkw 0x40630c381854a984 0x140630c381854a98 0x21e10418787cf8c2 0x021e10418787cf8c

def z1375 : W := mkw 0x81bc0fc06e80f606 0x981bc0fc06e80f60 0x79fc0b007f80fe0b 0x079fc0b007f80fe0

def z1376 : W := mkw 0x22d7f002337b0068 0xe22d7f002337b006 0xa7e7f0263bff01f6 0x9a7e7f0263bff01f

def z1377 : W := mkw 0x02dff000777b0008 0xe02dff000777b000 0xfbfff0007fff010f 0xbfbfff0007fff010

def z1378 : W := mkw 0xa1bc4fc26ea2f666 0xda1bc4fc26ea2f66 0xfbfecfe67fe3fecf 0x7fbfecfe67fe3fec

def z1379 : W := mkw 0x40630c381854a984 0x140630c381854a98 0x11e20c38787cf9cf 0xa11e20c38787cf9c

def z1380 : W := mkw 0x00630c3000000004 0x000630c300000000 0xfeffffff80000000 0xffeffffff8000000

def z1381 : W := mkw 0x02dff000777b0008 0xe02dff000777b000 0xd3fff0007fff0004 0x1d3fff0007fff000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z7,z8,z1,z2,z3,z9,z5]),(1,[z0,z10,z2,z3,z9,z5]),(0,[z11,z0,z1,z2,z3,z9,z5])],[(0,[z0,z12,z2,z13,z3,z9,z5]),(0,[z0,z2,z14,z15,z3,z9,z5]),(0,[z0,z1,z2,z15,z16,z9,z5]),(0,[z1,z2,z3,z17,z9,z18,z5]),(0,[z19,z0,z1,z2,z3,z9,z5]),(0,[z20,z0,z1,z2,z3,z9,z5]),(0,[z21,z0,z2,z3,z9,z5,z6]),(0,[z0,z22,z1,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z9,z5,z23])],[(0,[z24,z1,z12,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z9,z5,z25]),(0,[z0,z1,z26,z27,z3,z9,z5]),(0,[z0,z1,z2,z3,z28,z9,z5]),(0,[z0,z1,z2,z3,z9,z5,z29]),(0,[z0,z1,z2,z3,z9,z5,z30])],[(0,[z0,z1,z2,z3,z9,z5,z31]),(0,[z32,z0,z1,z2,z3,z9,z33]),(0,[z34,z0,z2,z14,z3,z9,z5]),(0,[z0,z2,z14,z3,z35,z9,z5]),(0,[z36,z0,z37,z2,z3,z9,z5]),(0,[z0,z1,z38,z2,z3,z9,z5]),(0,[z7,z0,z1,z2,z3,z9,z39]),(1,[z0,z1,z2,z3,z40,z5]),(0,[z0,z1,z2,z3,z9,z41,z5])],[(0,[z42,z0,z2,z14,z3,z9,z5]),(0,[z7,z0,z37,z2,z3,z9,z5]),(0,[z0,z37,z2,z3,z43,z9,z5]),(0,[z44,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z9,z45,z5]),(0,[z0,z1,z2,z3,z46,z9,z5]),(0,[z0,z1,z47,z2,z3,z9,z5])],[(0,[z0,z1,z2,z48,z3,z9,z5]),(0,[z0,z2,z14,z3,z49,z9,z5]),(0,[z0,z50,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z9,z5,z6]),(0,[z0,z51,z2,z52,z3,z9,z5]),(1,[z0,z1,z2,z3,z53,z5])],[(0,[z54,z0,z1,z2,z3,z9,z5]),(1,[z0,z1,z2,z3,z55,z5]),(0,[z0,z2,z56,z14,z3,z9,z5]),(0,[z0,z37,z2,z3,z57,z9,z5]),(0,[z58,z0,z59,z2,z3,z9,z5]),(0,[z60,z0,z1,z2,z3,z9,z5]),(1,[z0,z1,z2,z61,z57,z5]),(0,[z0,z1,z2,z3,z9,z62,z5])],[(0,[z0,z1,z2,z3,z9,z5,z63]),(0,[z64,z0,z65,z2,z3,z9,z5]),(0,[z0,z66,z1,z2,z3,z9,z5]),(1,[z0,z67,z2,z3,z9,z68]),(0,[z0,z22,z69,z2,z3,z9,z5]),(0,[z0,z1,z69,z2,z3,z70,z5]),(0,[z0,z71,z1,z2,z3,z9,z5])]],
   [[(0,[z0,z2,z14,z3,z72,z9,z5]),(0,[z0,z1,z2,z3,z18,z5,z73]),(0,[z74,z0,z1,z2,z9,z75,z5]),(0,[z0,z1,z2,z3,z76,z9,z5]),(0,[z77,z0,z1,z2,z3,z9,z78]),(0,[z0,z1,z79,z2,z3,z9,z5])],[(1,[z0,z1,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z80,z9,z5]),(0,[z0,z1,z2,z3,z81,z9,z5]),(0,[z82,z0,z1,z83,z3,z9,z5]),(0,[z84,z0,z2,z14,z3,z9,z5]),(0,[z0,z1,z2,z3,z9,z85,z5]),(0,[z0,z1,z2,z86,z3,z9,z5]),(0,[z0,z1,z2,z3,z87,z9,z5]),(0,[z0,z1,z2,z3,z88,z9,z5])],[(0,[z0,z1,z2,z3,z89,z9,z5]),(0,[z0,z65,z1,z2,z3,z9,z5]),(0,[z0,z2,z14,z3,z9,z5,z90]),(0,[z0,z37,z2,z3,z9,z78,z5]),(0,[z21,z0,z1,z2,z3,z9,z5]),(0,[z0,z1,z2,z91,z3,z9,z5]),(0,[z0,z1,z3,z9,z92,z5,z90]),(0,[z0,z1,z2,z3,z93,z9,z5])],[(0,[z94,z0,z1,z2,z3,z4,z5]),(0,[z0,z2,z14,z3,z95,z9,z5]),(0,[z0,z1,z2,z96,z3,z9,z5]),(0,[z0,z1,z97,z2,z3,z9,z5])],[(0,[z64,z1,z2,z3,z17,z9,z5]),(0,[z0,z98,z1,z2,z3,z9,z5])],[(0,[z94,z0,z1,z26,z3,z9,z5]),(0,[z0,z1,z2,z99,z3,z9,z5]),(0,[z0,z37,z2,z13,z3,z9,z5])],[(0,[z100,z0,z2,z14,z3,z9,z5]),(0,[z0,z1,z2,z61,z3,z18,z5]),(0,[z0,z1,z2,z3,z9,z101,z5])],[(0,[z102,z0,z2,z14,z3,z9,z5]),(0,[z0,z103,z37,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z104,z4,z5])]],
   [[(0,[z0,z2,z14,z3,z9,z92,z5]),(0,[z0,z1,z2,z3,z4,z105,z5])],[(0,[z0,z106,z1,z2,z3,z9,z5]),(0,[z0,z1,z2,z56,z3,z107,z5]),(0,[z108,z0,z1,z2,z3,z9,z5]),(0,[z0,z109,z1,z2,z3,z9,z5]),(0,[z11,z0,z1,z2,z110,z9,z5])],[(0,[z111,z0,z1,z2,z3,z9,z5]),(0,[z112,z0,z37,z2,z3,z9,z5]),(0,[z64,z0,z1,z2,z3,z4,z5]),(0,[z0,z113,z37,z2,z3,z9,z5])],[(0,[z0,z1,z2,z114,z3,z9,z5]),(1,[z0,z115,z2,z3,z9,z5]),(0,[z0,z1,z2,z116,z3,z9,z5]),(0,[z0,z67,z2,z3,z9,z68,z5]),(0,[z0,z8,z1,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z43,z107,z5]),(0,[z0,z117,z1,z2,z3,z9,z5])],[(0,[z82,z1,z2,z3,z72,z9,z5]),(0,[z118,z0,z37,z2,z3,z9,z5]),(0,[z0,z119,z1,z2,z3,z9,z5]),(1,[z120,z1,z2,z3,z9,z5]),(0,[z0,z1,z69,z2,z3,z9,z5]),(0,[z0,z1,z69,z16,z3,z9,z5]),(0,[z121,z0,z1,z2,z3,z9,z5])],[(0,[z0,z67,z12,z2,z3,z9,z5]),(0,[z82,z100,z1,z2,z3,z9,z5]),(0,[z0,z122,z1,z2,z3,z9,z5]),(0,[z123,z0,z1,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z9,z105,z5]),(0,[z0,z1,z2,z3,z124,z9,z5]),(0,[z0,z1,z2,z3,z125,z107,z5]),(0,[z0,z1,z27,z2,z3,z53,z5])],[(0,[z126,z0,z1,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z107,z18,z5]),(0,[z0,z2,z14,z3,z9,z4,z5]),(0,[z127,z0,z2,z14,z3,z9,z5]),(0,[z0,z1,z2,z3,z9,z128,z5]),(0,[z0,z129,z1,z2,z3,z9,z5]),(0,[z77,z0,z1,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z130,z9,z5])],[(0,[z0,z1,z131,z2,z3,z9,z5]),(0,[z77,z0,z1,z2,z72,z9,z5]),(0,[z32,z0,z1,z2,z3,z4,z5]),(0,[z0,z132,z1,z2,z3,z9,z5])]],
   [[(0,[z0,z1,z2,z133,z3,z9,z5]),(0,[z0,z1,z2,z3,z134,z9,z5]),(0,[z0,z1,z2,z3,z9,z5,z135]),(0,[z0,z37,z2,z3,z9,z18,z5]),(0,[z0,z1,z2,z3,z136,z107,z5])],[(0,[z0,z1,z2,z3,z137,z9,z5]),(0,[z0,z138,z1,z2,z3,z9,z5]),(0,[z100,z1,z2,z3,z9,z33,z5]),(1,[z0,z65,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z9,z139,z5]),(0,[z0,z2,z14,z61,z3,z9,z5]),(0,[z0,z37,z67,z2,z3,z9,z5]),(0,[z140,z0,z1,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z141,z4,z5]),(0,[z0,z1,z27,z2,z3,z9,z5]),(0,[z0,z1,z2,z57,z9,z75,z5])],[(0,[z42,z0,z12,z2,z3,z9,z5]),(0,[z0,z1,z142,z2,z3,z9,z5]),(0,[z143,z0,z1,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z144,z9,z5]),(0,[z0,z2,z3,z9,z68,z5,z6]),(1,[z0,z1,z2,z110,z9,z5])],[(0,[z0,z1,z26,z3,z9,z5,z90]),(0,[z145,z0,z1,z2,z3,z9,z5]),(0,[z0,z113,z1,z2,z3,z35,z5])],[(0,[z146,z0,z1,z2,z3,z9,z5]),(0,[z0,z1,z2,z147,z3,z9,z5]),(0,[z24,z0,z37,z2,z3,z9,z5]),(0,[z0,z1,z2,z148,z3,z9,z5]),(0,[z0,z2,z14,z3,z17,z9,z5]),(0,[z11,z0,z2,z14,z3,z9,z5]),(0,[z0,z2,z14,z3,z104,z9,z5]),(0,[z0,z37,z2,z3,z149,z9,z5]),(0,[z150,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z151,z2,z3,z9,z5]),(0,[z152,z0,z1,z2,z3,z9,z5])],[(0,[z153,z0,z1,z2,z3,z9,z5]),(0,[z58,z0,z37,z2,z3,z9,z5]),(1,[z58,z0,z1,z3,z4,z5]),(0,[z0,z1,z2,z3,z9,z5,z154]),(0,[z0,z155,z1,z2,z3,z9,z5])],[(0,[z1,z2,z3,z9,z33,z5,z156]),(1,[z0,z157,z2,z3,z9,z5])],[(0,[z0,z158,z1,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z159,z9,z5]),(0,[z0,z27,z2,z14,z3,z9,z5]),(1,[z160,z1,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z9,z5,z161])]],
   [[(0,[z0,z1,z2,z3,z162,z9,z5]),(0,[z0,z1,z2,z3,z9,z163,z5]),(1,[z0,z164,z2,z3,z9,z5])],[(0,[z165,z0,z1,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z9,z5,z166]),(0,[z44,z0,z37,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z167,z9,z5]),(0,[z0,z1,z2,z3,z168,z9,z5]),(0,[z169,z0,z1,z2,z3,z9,z5])],[(0,[z0,z1,z2,z170,z3,z9,z5]),(0,[z0,z2,z14,z16,z3,z9,z5]),(1,[z11,z0,z1,z3,z9,z90])],[(0,[z171,z0,z1,z2,z3,z9,z5]),(0,[z0,z2,z14,z3,z9,z68,z5]),(0,[z0,z37,z172,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z9,z173,z5]),(1,[z174,z0,z2,z3,z175,z5]),(1,[z0,z1,z3,z107,z4,z5]),(0,[z0,z1,z2,z3,z176,z9,z5])],[(0,[z177,z0,z1,z2,z3,z9,z5]),(0,[z0,z26,z2,z14,z3,z9,z5]),(0,[z0,z1,z2,z178,z3,z9,z5]),(1,[z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z87,z4,z5]),(0,[z0,z1,z51,z2,z3,z107,z5]),(0,[z0,z1,z2,z179,z3,z9,z78]),(0,[z0,z1,z2,z180,z3,z9,z5])],[(0,[z0,z1,z2,z3,z181,z9,z5]),(0,[z0,z1,z2,z3,z9,z182,z5]),(0,[z0,z183,z1,z2,z3,z9,z5])],[(1,[z0,z1,z2,z3,z184,z5]),(0,[z185,z0,z1,z2,z3,z9,z5]),(0,[z21,z0,z2,z14,z3,z9,z5]),(0,[z0,z1,z2,z3,z186,z9,z5]),(0,[z0,z67,z1,z2,z3,z9,z5]),(0,[z187,z0,z1,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z188,z5,z73])],[(0,[z189,z0,z1,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z9,z5,z190])]],
   [[(0,[z0,z1,z2,z3,z9,z191,z5]),(0,[z42,z0,z1,z2,z3,z55,z5]),(0,[z192,z0,z1,z2,z3,z9,z5])],[(0,[z0,z1,z2,z3,z193,z9,z5]),(0,[z0,z1,z2,z194,z3,z9,z5]),(0,[z0,z37,z2,z3,z188,z9,z5]),(0,[z0,z1,z2,z3,z195,z9,z5]),(0,[z0,z196,z1,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z9,z197,z5])],[(0,[z0,z1,z2,z198,z3,z9,z5]),(0,[z0,z1,z2,z14,z3,z9,z5])],[(0,[z42,z0,z1,z2,z3,z9,z5]),(0,[z0,z1,z2,z72,z9,z5,z199]),(0,[z0,z1,z2,z200,z3,z9,z5]),(0,[z201,z0,z1,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z202,z9,z5]),(1,[z0,z1,z2,z3,z168,z5])],[(0,[z42,z1,z2,z3,z72,z9,z5]),(0,[z0,z106,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z9,z203,z5]),(0,[z0,z1,z204,z2,z3,z9,z5])],[(0,[z42,z100,z1,z2,z3,z9,z5]),(0,[z0,z2,z14,z48,z3,z9,z5]),(0,[z0,z205,z1,z2,z3,z9,z5]),(0,[z0,z1,z2,z206,z3,z9,z5]),(0,[z0,z207,z1,z2,z3,z9,z5])],[(0,[z74,z0,z1,z2,z3,z17,z5]),(0,[z82,z0,z1,z2,z3,z4,z5]),(0,[z0,z37,z2,z3,z9,z33,z5]),(0,[z208,z0,z1,z2,z3,z9,z5]),(0,[z0,z1,z209,z2,z3,z9,z5]),(0,[z0,z1,z2,z210,z3,z9,z5]),(0,[z0,z1,z2,z3,z9,z211,z5])],[(0,[z100,z1,z2,z15,z3,z9,z5]),(0,[z0,z1,z2,z212,z3,z9,z5]),(0,[z213,z0,z37,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z9,z175,z5])]],
   [[(0,[z0,z1,z27,z56,z3,z9,z5]),(0,[z171,z0,z1,z172,z3,z9,z5]),(0,[z1,z2,z3,z9,z5,z214,z90])],[(0,[z0,z1,z2,z15,z9,z5,z199]),(0,[z82,z0,z1,z2,z178,z9,z5]),(0,[z77,z0,z1,z2,z3,z4,z5])],[(0,[z174,z0,z50,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z4,z5,z199]),(0,[z0,z215,z1,z2,z3,z9,z5]),(0,[z0,z1,z2,z179,z3,z9,z5])],[(0,[z216,z0,z1,z2,z3,z9,z5]),(0,[z217,z0,z1,z2,z3,z9,z5]),(0,[z0,z1,z26,z2,z3,z107,z5]),(0,[z218,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z83,z3,z9,z5]),(0,[z0,z1,z2,z3,z107,z219,z5])],[(0,[z0,z1,z2,z3,z9,z5,z220]),(0,[z0,z1,z27,z2,z3,z4,z5]),(0,[z11,z0,z221,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z9,z5,z222])],[(0,[z100,z0,z1,z2,z3,z9,z5]),(0,[z223,z0,z1,z2,z3,z9,z5]),(0,[z0,z224,z2,z13,z3,z9,z5]),(0,[z74,z174,z0,z1,z2,z3,z5]),(0,[z225,z0,z1,z2,z3,z9,z5]),(0,[z226,z0,z1,z2,z3,z9,z5]),(0,[z0,z1,z227,z2,z3,z9,z5])],[(0,[z228,z0,z1,z56,z3,z9,z5]),(0,[z100,z0,z1,z2,z72,z9,z5]),(0,[z102,z0,z1,z2,z3,z9,z5]),(0,[z229,z0,z1,z2,z3,z9,z5]),(0,[z0,z59,z1,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z4,z5,z73]),(1,[z230,z1,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z231,z9,z5])],[(0,[z232,z0,z1,z2,z3,z9,z5]),(0,[z0,z1,z2,z15,z3,z4,z5]),(0,[z0,z50,z1,z2,z3,z17,z5]),(0,[z0,z37,z37,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z9,z5,z199])]],
   [[(0,[z0,z1,z2,z3,z9,z233,z5]),(0,[z0,z1,z2,z234,z3,z9,z5]),(0,[z235,z0,z2,z3,z9,z5,z199])],[(0,[z236,z0,z1,z2,z3,z9,z5]),(0,[z171,z0,z1,z2,z3,z237,z5])],[(0,[z228,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z238,z3,z9,z5]),(0,[z0,z1,z2,z3,z9,z239,z5])],[(0,[z0,z1,z240,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z49,z4,z5]),(0,[z0,z1,z2,z241,z3,z9,z5]),(0,[z11,z0,z1,z2,z3,z9,z90]),(0,[z0,z1,z2,z3,z9,z5,z73])],[(0,[z228,z0,z1,z26,z3,z9,z5]),(0,[z0,z1,z69,z2,z16,z9,z5]),(0,[z0,z1,z2,z3,z107,z9,z5])],[(0,[z0,z1,z2,z2,z3,z9,z5]),(0,[z0,z2,z14,z3,z9,z105,z5]),(0,[z174,z0,z2,z13,z3,z9,z5]),(0,[z0,z50,z1,z2,z61,z3,z5]),(1,[z8,z1,z2,z3,z9,z5]),(0,[z11,z0,z1,z2,z3,z40,z5])],[(0,[z24,z0,z106,z2,z3,z9,z5]),(1,[z0,z1,z2,z3,z242,z5]),(0,[z0,z1,z2,z3,z72,z4,z5]),(1,[z0,z1,z2,z3,z243,z5]),(1,[z119,z1,z2,z3,z9,z5]),(0,[z77,z0,z1,z2,z16,z9,z5]),(0,[z0,z1,z2,z3,z9,z78,z92]),(1,[z0,z1,z2,z3,z202,z5])],[(0,[z0,z1,z2,z3,z9,z5,z244]),(0,[z100,z0,z115,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z9,z5,z245]),(0,[z171,z0,z2,z14,z3,z9,z5])]],
   [[(1,[z0,z2,z14,z3,z4,z5]),(0,[z0,z1,z2,z3,z246,z9,z5]),(1,[z0,z1,z2,z3,z9,z39])],[(0,[z94,z0,z1,z2,z247,z9,z5]),(0,[z248,z0,z1,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z9,z249,z5]),(0,[z0,z1,z2,z3,z9,z250,z5]),(0,[z251,z0,z1,z2,z3,z9,z5]),(1,[z0,z37,z2,z3,z107,z5]),(0,[z0,z67,z1,z2,z3,z4,z5]),(0,[z252,z0,z1,z2,z3,z9,z5])],[(0,[z0,z2,z14,z3,z144,z9,z5]),(0,[z0,z1,z2,z3,z9,z253,z5]),(0,[z0,z113,z1,z2,z3,z35,z9])],[(0,[z44,z0,z106,z2,z3,z9,z5]),(0,[z254,z0,z1,z2,z3,z9,z5]),(0,[z255,z0,z1,z2,z3,z9,z5]),(0,[z174,z0,z1,z2,z3,z188,z5]),(0,[z7,z0,z1,z2,z43,z9,z5]),(0,[z256,z0,z1,z2,z3,z9,z5]),(0,[z0,z1,z2,z257,z3,z9,z5]),(0,[z0,z1,z2,z3,z35,z5,z73])],[(0,[z258,z0,z1,z2,z3,z9,z5]),(0,[z0,z26,z2,z259,z3,z9,z5]),(0,[z0,z37,z2,z15,z3,z9,z5]),(0,[z0,z1,z2,z3,z260,z9,z5]),(0,[z0,z1,z2,z3,z4,z75,z5]),(0,[z0,z1,z2,z3,z261,z9,z5])],[(0,[z0,z1,z2,z3,z9,z262,z5]),(1,[z0,z2,z259,z3,z9,z5]),(0,[z0,z1,z2,z3,z9,z263,z5]),(0,[z264,z0,z1,z2,z3,z9,z5]),(0,[z36,z0,z1,z2,z3,z107,z5]),(0,[z0,z1,z2,z3,z265,z9,z5])],[(0,[z42,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z266,z3,z9,z5]),(0,[z0,z37,z2,z3,z35,z9,z5]),(0,[z0,z50,z1,z2,z3,z175,z5]),(0,[z0,z1,z2,z267,z3,z9,z5]),(0,[z7,z0,z1,z2,z3,z107,z5]),(0,[z0,z1,z2,z3,z9,z5,z214]),(0,[z0,z2,z3,z9,z5,z222,z199]),(0,[z0,z1,z2,z3,z9,z268,z5])],[(1,[z0,z1,z2,z269,z9,z5]),(0,[z0,z2,z3,z104,z9,z175,z5])]],
   [[(0,[z270,z0,z1,z2,z3,z9,z5]),(0,[z0,z37,z2,z3,z49,z9,z5]),(0,[z174,z0,z1,z2,z3,z175,z5]),(0,[z0,z1,z10,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z271,z9,z5]),(0,[z0,z1,z2,z61,z3,z188,z5])],[(0,[z0,z115,z1,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z9,z75,z5])],[(0,[z94,z0,z1,z56,z3,z9,z5]),(0,[z174,z0,z1,z2,z3,z4,z5])],[(0,[z0,z37,z2,z3,z72,z9,z5]),(0,[z0,z1,z2,z3,z9,z5,z272]),(0,[z273,z0,z1,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z9,z274,z5]),(0,[z0,z1,z2,z3,z9,z5,z275]),(0,[z84,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z107,z5,z90]),(0,[z0,z1,z2,z3,z107,z78,z5])],[(0,[z0,z37,z276,z2,z3,z9,z5]),(1,[z0,z1,z69,z16,z9,z5])],[(0,[z0,z277,z1,z2,z3,z9,z5]),(0,[z278,z0,z1,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z279,z9,z5]),(0,[z0,z37,z2,z3,z9,z5,z90]),(0,[z0,z280,z1,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z9,z281,z5]),(0,[z0,z1,z2,z3,z9,z282,z5]),(0,[z0,z1,z2,z3,z4,z5,z283]),(0,[z0,z1,z2,z179,z3,z4,z5]),(0,[z0,z1,z2,z3,z284,z9,z5])],[(0,[z94,z0,z285,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z286,z9,z5]),(1,[z0,z37,z172,z3,z9,z5])],[(0,[z0,z1,z2,z61,z3,z4,z5])]],
   [[(0,[z94,z0,z1,z2,z3,z9,z63]),(0,[z100,z0,z1,z2,z3,z4,z5]),(0,[z218,z0,z37,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z9,z287,z5]),(0,[z0,z1,z2,z288,z3,z9,z5]),(1,[z0,z215,z2,z3,z9,z5])],[(0,[z0,z1,z1,z2,z3,z9,z5]),(0,[z289,z0,z1,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z290,z9,z5])],[(0,[z0,z1,z2,z3,z17,z4,z5]),(0,[z0,z2,z14,z14,z3,z9,z5]),(0,[z0,z69,z2,z14,z3,z9,z5]),(0,[z7,z0,z291,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z9,z5,z283]),(0,[z0,z1,z2,z16,z9,z5,z199]),(0,[z58,z0,z1,z51,z3,z9,z5]),(1,[z0,z2,z292,z3,z9,z5]),(0,[z235,z0,z1,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z188,z9,z73])],[(0,[z100,z1,z12,z2,z3,z9,z5]),(0,[z0,z12,z2,z3,z104,z9,z5]),(0,[z171,z0,z1,z14,z3,z9,z5]),(0,[z0,z37,z2,z3,z9,z92,z5]),(0,[z0,z1,z2,z293,z3,z9,z5]),(0,[z58,z0,z1,z3,z9,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z294]),(0,[z0,z1,z2,z3,z9,z5,z295])],[(0,[z0,z1,z2,z56,z3,z9,z5]),(0,[z112,z0,z1,z2,z3,z107,z5]),(0,[z0,z1,z296,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z297,z5,z6]),(0,[z0,z113,z1,z2,z3,z107,z5]),(0,[z0,z1,z27,z2,z3,z9,z90]),(0,[z0,z113,z1,z2,z3,z9,z5])],[(0,[z298,z0,z1,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z9,z299,z5]),(1,[z0,z50,z2,z3,z104,z5]),(0,[z0,z1,z2,z3,z300,z9,z5]),(0,[z0,z1,z2,z3,z9,z301,z5])],[(0,[z0,z1,z2,z302,z3,z9,z5]),(0,[z0,z1,z2,z3,z9,z5,z303]),(0,[z0,z1,z2,z3,z9,z5,z304]),(0,[z0,z2,z3,z104,z9,z68,z5]),(0,[z0,z1,z2,z3,z43,z9,z5]),(0,[z305,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z306,z9,z5])],[(0,[z0,z1,z2,z3,z307,z9,z5]),(0,[z228,z0,z37,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z9,z308,z5]),(0,[z0,z2,z14,z3,z9,z175,z5]),(0,[z0,z1,z2,z3,z107,z4,z5]),(0,[z74,z0,z1,z2,z3,z75,z5])]],
   [[(0,[z0,z1,z2,z3,z125,z9,z5]),(0,[z171,z0,z1,z2,z3,z243,z5]),(0,[z0,z1,z2,z309,z3,z9,z5]),(0,[z0,z1,z2,z16,z3,z4,z5]),(0,[z0,z1,z2,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z9,z5,z294]),(0,[z0,z1,z2,z3,z57,z107,z5]),(0,[z11,z0,z157,z2,z3,z9,z5])],[(0,[z82,z32,z1,z2,z3,z9,z5]),(0,[z0,z37,z2,z3,z9,z4,z5]),(0,[z0,z1,z2,z3,z9,z310,z5]),(0,[z0,z1,z2,z3,z9,z311,z5]),(0,[z0,z1,z2,z3,z35,z188,z9])],[(1,[z0,z1,z2,z247,z9,z5]),(0,[z0,z2,z14,z179,z3,z9,z5]),(0,[z312,z0,z1,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z313,z9,z5]),(0,[z0,z1,z314,z2,z3,z9,z5])],[(0,[z315,z0,z1,z2,z3,z9,z5]),(0,[z0,z1,z12,z2,z3,z4,z5]),(0,[z316,z0,z1,z2,z3,z9,z5]),(0,[z0,z1,z317,z2,z3,z9,z5]),(0,[z82,z1,z2,z3,z9,z5,z156]),(0,[z318,z0,z1,z2,z3,z49,z5]),(0,[z21,z0,z2,z13,z3,z9,z5]),(0,[z0,z1,z2,z3,z136,z9,z5])],[(0,[z319,z0,z1,z2,z3,z9,z5]),(0,[z0,z1,z320,z2,z3,z9,z5]),(0,[z74,z0,z37,z2,z3,z9,z5]),(0,[z0,z37,z2,z61,z3,z9,z5]),(0,[z0,z1,z2,z3,z53,z9,z5]),(0,[z0,z1,z321,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z9,z5,z322])],[(0,[z42,z106,z1,z2,z3,z9,z5]),(1,[z0,z2,z52,z3,z9,z5])],[(0,[z24,z0,z1,z2,z3,z107,z5]),(0,[z1,z2,z3,z72,z9,z18,z5]),(0,[z323,z0,z1,z2,z3,z9,z5]),(0,[z0,z1,z2,z324,z3,z9,z5]),(0,[z0,z2,z325,z14,z3,z9,z5]),(0,[z326,z0,z1,z2,z3,z9,z5]),(0,[z7,z0,z1,z2,z3,z9,z253]),(0,[z11,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z327,z3,z9,z5])],[(0,[z0,z1,z2,z3,z328,z9,z5]),(0,[z0,z37,z2,z3,z17,z9,z5]),(0,[z0,z2,z14,z3,z9,z5,z199]),(0,[z0,z224,z37,z2,z3,z9,z5]),(0,[z0,z37,z2,z3,z104,z9,z5]),(0,[z0,z1,z172,z2,z3,z329,z5]),(0,[z318,z0,z1,z2,z3,z9,z5]),(0,[z0,z1,z2,z13,z3,z107,z5]),(0,[z58,z0,z1,z2,z3,z9,z5]),(0,[z58,z0,z1,z2,z3,z107,z5]),(0,[z0,z1,z2,z3,z9,z5,z330]),(0,[z331,z0,z2,z3,z9,z75,z5])]],
   [[(0,[z0,z1,z2,z3,z269,z9,z5]),(0,[z0,z1,z332,z2,z3,z9,z5]),(0,[z333,z0,z1,z2,z3,z9,z5]),(0,[z0,z334,z1,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z9,z5,z335])],[(0,[z336,z0,z1,z2,z3,z9,z5]),(0,[z0,z1,z337,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z9,z5,z338]),(0,[z0,z1,z2,z3,z9,z339,z5])],[(0,[z0,z106,z2,z13,z3,z9,z5]),(0,[z0,z1,z2,z3,z9,z33,z92]),(0,[z0,z1,z2,z3,z340,z9,z5]),(0,[z0,z1,z341,z2,z3,z9,z5])],[(0,[z0,z2,z14,z3,z9,z5,z73]),(0,[z44,z0,z1,z2,z3,z107,z5]),(0,[z0,z1,z2,z3,z342,z9,z5]),(0,[z77,z0,z1,z2,z179,z9,z5])],[(0,[z0,z12,z2,z3,z9,z5,z6]),(0,[z0,z2,z14,z3,z107,z9,z5]),(0,[z0,z1,z2,z343,z3,z9,z5]),(0,[z44,z174,z0,z2,z3,z9,z5]),(0,[z344,z0,z1,z2,z3,z9,z5])],[(0,[z0,z345,z1,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z346,z9,z5]),(0,[z94,z1,z2,z56,z3,z9,z5]),(0,[z218,z0,z1,z2,z3,z17,z5]),(0,[z0,z1,z2,z3,z4,z5,z156]),(0,[z0,z37,z2,z3,z9,z347,z5]),(0,[z0,z37,z2,z16,z3,z9,z5]),(0,[z0,z50,z37,z2,z3,z9,z5]),(0,[z74,z0,z1,z2,z3,z35,z5]),(0,[z0,z1,z2,z348,z3,z9,z5])],[(1,[z42,z106,z2,z3,z9,z5]),(1,[z0,z1,z2,z3,z349,z5]),(0,[z64,z0,z1,z2,z286,z9,z5]),(0,[z0,z1,z2,z3,z9,z5,z350]),(0,[z0,z37,z2,z3,z9,z68,z5]),(0,[z0,z1,z51,z3,z107,z9,z5]),(0,[z0,z1,z157,z2,z3,z9,z5])],[(1,[z0,z285,z2,z3,z9,z5]),(0,[z228,z1,z2,z3,z9,z5,z156]),(0,[z0,z1,z2,z351,z3,z9,z5]),(0,[z174,z0,z37,z2,z3,z9,z5]),(0,[z0,z1,z51,z2,z3,z9,z5]),(0,[z0,z1,z2,z86,z3,z4,z5]),(0,[z331,z0,z1,z2,z3,z9,z5]),(0,[z0,z352,z1,z2,z3,z9,z5])]],
   [[(0,[z0,z1,z2,z3,z353,z9,z5]),(0,[z0,z354,z1,z2,z3,z9,z5]),(0,[z84,z0,z37,z2,z3,z9,z5]),(0,[z355,z0,z1,z2,z3,z9,z5]),(0,[z21,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z9,z5,z356]),(0,[z0,z357,z1,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z9,z358,z5])],[(1,[z0,z1,z2,z3,z9,z63]),(0,[z359,z0,z1,z2,z3,z9,z5]),(1,[z112,z1,z2,z72,z9,z5]),(0,[z0,z1,z2,z3,z360,z9,z5]),(0,[z0,z1,z2,z3,z361,z49,z5])],[(0,[z0,z1,z2,z3,z9,z362,z5]),(0,[z0,z1,z2,z3,z9,z18,z5]),(1,[z0,z1,z2,z178,z9,z5]),(0,[z0,z1,z2,z3,z9,z5,z156]),(0,[z0,z1,z2,z3,z9,z363,z5]),(0,[z0,z1,z2,z3,z9,z364,z5])],[(0,[z94,z0,z37,z2,z3,z9,z5]),(0,[z365,z0,z1,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z9,z366,z5]),(0,[z0,z1,z2,z3,z9,z5,z367])],[(0,[z7,z0,z98,z2,z3,z9,z5]),(1,[z0,z1,z2,z257,z9,z5])],[(0,[z0,z1,z56,z3,z9,z5,z90]),(0,[z0,z1,z2,z3,z361,z9,z5]),(1,[z0,z59,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z9,z368,z5])],[(0,[z0,z106,z67,z2,z3,z9,z5]),(0,[z0,z2,z14,z266,z3,z9,z5]),(0,[z44,z312,z1,z2,z3,z9,z5]),(0,[z369,z0,z1,z2,z3,z9,z5]),(0,[z0,z50,z1,z2,z3,z35,z5]),(1,[z7,z0,z1,z43,z9,z5])],[(0,[z1,z12,z2,z3,z72,z9,z5]),(0,[z0,z1,z2,z3,z107,z33,z5]),(0,[z0,z1,z2,z3,z370,z9,z5])]],
   [[(1,[z0,z1,z2,z3,z9,z371]),(0,[z0,z113,z2,z14,z3,z9,z5]),(0,[z0,z2,z14,z3,z9,z5,z6]),(0,[z174,z0,z1,z2,z3,z35,z5]),(0,[z120,z0,z1,z2,z3,z9,z5]),(0,[z11,z230,z1,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z372,z9,z5]),(1,[z1,z2,z3,z9,z5,z214])],[(0,[z94,z0,z1,z2,z269,z9,z5]),(0,[z32,z1,z2,z56,z3,z9,z5]),(0,[z0,z1,z2,z3,z373,z9,z5]),(0,[z0,z113,z1,z2,z3,z18,z5]),(0,[z374,z0,z1,z2,z3,z9,z5]),(1,[z0,z37,z14,z3,z9,z5]),(0,[z0,z2,z14,z3,z9,z75,z5])],[(0,[z375,z0,z1,z2,z3,z9,z5]),(0,[z112,z0,z1,z2,z15,z9,z5]),(0,[z64,z0,z37,z2,z3,z9,z5]),(0,[z0,z1,z69,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z376,z9,z5])],[],[(0,[z0,z1,z2,z377,z3,z9,z5]),(0,[z0,z1,z378,z2,z3,z9,z5]),(0,[z379,z0,z1,z2,z3,z9,z5]),(1,[z235,z0,z2,z3,z9,z5])],[(0,[z0,z1,z172,z2,z3,z107,z5]),(0,[z44,z0,z2,z3,z49,z9,z5]),(0,[z0,z2,z13,z3,z49,z9,z5]),(0,[z0,z1,z380,z2,z3,z9,z5]),(0,[z0,z1,z2,z61,z3,z35,z5])],[(0,[z0,z1,z26,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z9,z381,z5]),(0,[z1,z2,z56,z3,z9,z5,z156]),(0,[z0,z1,z2,z382,z3,z9,z5])],[(0,[z0,z1,z2,z383,z3,z9,z5]),(0,[z32,z0,z37,z2,z3,z9,z5]),(1,[z0,z1,z2,z3,z384,z5]),(0,[z0,z1,z2,z3,z9,z385,z5]),(0,[z0,z1,z2,z386,z3,z9,z5]),(0,[z387,z0,z1,z2,z3,z9,z5])]],
   [[(0,[z0,z1,z388,z2,z3,z9,z5]),(1,[z0,z1,z2,z286,z9,z5]),(0,[z0,z389,z1,z2,z3,z9,z5]),(0,[z0,z390,z1,z2,z3,z9,z5]),(0,[z0,z1,z391,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z9,z92,z199]),(0,[z0,z1,z2,z3,z9,z392,z5])],[(0,[z0,z1,z2,z393,z3,z9,z5]),(0,[z106,z1,z12,z2,z3,z9,z5]),(0,[z74,z0,z1,z2,z15,z9,z5]),(0,[z0,z37,z1,z2,z3,z107,z5]),(0,[z7,z0,z1,z2,z3,z394,z5])],[],[(0,[z0,z2,z2,z14,z3,z9,z5]),(0,[z58,z0,z2,z14,z3,z9,z5]),(0,[z11,z0,z37,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z188,z107,z5]),(1,[z331,z0,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z395,z9,z5])],[(0,[z0,z224,z1,z2,z15,z9,z5]),(0,[z174,z0,z1,z2,z3,z17,z5])],[(0,[z0,z396,z1,z2,z3,z9,z5]),(0,[z0,z1,z397,z2,z3,z9,z5])],[(0,[z1,z26,z2,z56,z3,z9,z5]),(0,[z0,z1,z2,z3,z9,z5,z398]),(0,[z0,z1,z399,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z9,z400,z5])],[(0,[z401,z0,z1,z2,z3,z9,z5]),(1,[z0,z1,z2,z3,z402,z5]),(0,[z0,z1,z403,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z9,z404,z5]),(0,[z0,z405,z1,z2,z3,z107,z5]),(0,[z406,z0,z1,z2,z3,z9,z5])]],
   [[(1,[z0,z407,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z9,z394,z5])],[(0,[z408,z0,z1,z2,z3,z9,z5]),(0,[z44,z0,z1,z2,z15,z9,z5]),(0,[z0,z1,z2,z409,z3,z9,z5]),(0,[z0,z1,z2,z61,z3,z17,z5]),(0,[z171,z0,z1,z2,z3,z4,z5]),(0,[z410,z0,z1,z2,z3,z9,z5])],[(0,[z411,z0,z1,z2,z3,z9,z5]),(0,[z0,z1,z2,z412,z3,z9,z5]),(0,[z0,z1,z2,z3,z413,z9,z5]),(0,[z0,z66,z37,z2,z3,z9,z5]),(0,[z174,z0,z1,z2,z61,z3,z5]),(0,[z0,z1,z69,z2,z3,z384,z5]),(0,[z0,z1,z2,z3,z9,z5,z414]),(0,[z0,z1,z2,z3,z107,z415,z5]),(0,[z0,z416,z1,z2,z3,z9,z5])],[(0,[z0,z1,z2,z3,z9,z5,z417]),(0,[z0,z1,z2,z3,z9,z418,z5]),(0,[z0,z1,z2,z419,z3,z9,z5]),(0,[z420,z0,z1,z2,z3,z9,z5])],[(0,[z0,z1,z2,z3,z9,z421,z5]),(0,[z0,z1,z2,z3,z9,z422,z5]),(1,[z0,z37,z2,z3,z9,z5]),(0,[z0,z37,z27,z2,z3,z9,z5]),(0,[z0,z1,z2,z423,z3,z9,z5]),(0,[z0,z1,z424,z2,z3,z9,z5]),(0,[z74,z416,z1,z2,z3,z9,z5])],[(0,[z0,z1,z2,z425,z3,z9,z5]),(0,[z21,z0,z37,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z9,z426,z5]),(0,[z0,z1,z2,z3,z168,z5,z199])],[(0,[z0,z1,z427,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z428,z9,z5]),(1,[z0,z2,z429,z3,z9,z5]),(0,[z0,z1,z430,z2,z3,z9,z5])],[(0,[z0,z1,z2,z3,z431,z9,z5]),(0,[z64,z0,z1,z2,z3,z17,z5]),(1,[z0,z432,z2,z3,z9,z5]),(0,[z0,z1,z2,z433,z3,z9,z5]),(0,[z434,z0,z1,z2,z3,z9,z5]),(1,[z0,z1,z2,z3,z372,z5])]],
   [[(0,[z0,z1,z2,z14,z3,z4,z5]),(0,[z36,z0,z1,z2,z3,z9,z5]),(0,[z0,z1,z2,z435,z3,z9,z5]),(0,[z0,z1,z2,z3,z78,z4,z5])],[(0,[z0,z12,z2,z14,z3,z9,z5]),(0,[z174,z0,z106,z2,z3,z9,z5]),(0,[z0,z1,z2,z436,z3,z9,z5]),(0,[z0,z1,z2,z3,z437,z9,z5]),(0,[z7,z0,z1,z2,z3,z9,z5]),(0,[z11,z357,z1,z2,z3,z9,z5])],[(0,[z0,z51,z2,z14,z3,z9,z5]),(0,[z0,z1,z2,z3,z438,z9,z5]),(0,[z0,z1,z2,z179,z9,z5,z199])],[(0,[z439,z0,z1,z2,z3,z9,z5]),(0,[z82,z0,z440,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z9,z156,z90]),(0,[z0,z441,z1,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z442,z9,z5]),(0,[z0,z1,z2,z3,z443,z9,z5]),(0,[z0,z205,z1,z2,z3,z4,z5])],[(0,[z0,z106,z37,z2,z3,z9,z5]),(0,[z0,z444,z1,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z9,z445,z5]),(0,[z44,z0,z2,z3,z104,z9,z5]),(0,[z0,z2,z13,z3,z104,z9,z5]),(0,[z11,z0,z1,z27,z3,z9,z5]),(0,[z0,z1,z2,z3,z9,z446,z5])],[(0,[z0,z1,z2,z259,z3,z9,z5]),(0,[z0,z1,z2,z72,z43,z9,z5]),(0,[z0,z447,z1,z2,z3,z9,z5]),(0,[z448,z0,z1,z2,z3,z9,z5]),(0,[z0,z50,z2,z3,z104,z9,z5]),(0,[z77,z0,z1,z2,z43,z9,z5])],[(0,[z82,z0,z37,z2,z3,z9,z5]),(0,[z449,z0,z1,z2,z3,z9,z5]),(0,[z450,z0,z1,z2,z3,z107,z5])],[(0,[z0,z1,z2,z72,z57,z9,z5]),(1,[z0,z291,z2,z3,z9,z5]),(0,[z0,z1,z2,z9,z78,z5,z199]),(0,[z0,z1,z2,z3,z202,z5,z199])]],
   [[(0,[z24,z0,z12,z2,z3,z9,z5]),(0,[z94,z0,z1,z2,z3,z349,z5]),(0,[z0,z1,z2,z3,z9,z9,z5])],[(0,[z82,z0,z432,z2,z3,z9,z5]),(0,[z82,z0,z1,z2,z451,z9,z5]),(0,[z0,z2,z96,z14,z3,z9,z5]),(0,[z0,z1,z2,z452,z3,z9,z5]),(0,[z0,z1,z2,z3,z9,z5,z453]),(0,[z77,z0,z37,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z9,z5,z454]),(1,[z0,z2,z3,z9,z5,z455])],[(1,[z0,z1,z2,z353,z9,z5]),(0,[z218,z0,z1,z2,z3,z107,z5]),(0,[z0,z2,z14,z3,z9,z5,z156]),(0,[z0,z456,z1,z2,z3,z107,z5]),(1,[z357,z1,z2,z3,z9,z5])],[(0,[z0,z1,z2,z15,z43,z9,z5]),(0,[z0,z1,z2,z3,z9,z5,z457]),(0,[z0,z1,z2,z3,z458,z9,z5]),(0,[z44,z0,z2,z3,z9,z68,z5]),(0,[z0,z2,z13,z3,z9,z68,z5]),(0,[z0,z1,z2,z3,z9,z5,z459]),(0,[z460,z0,z1,z2,z3,z9,z5])],[(0,[z0,z1,z2,z461,z3,z9,z5]),(0,[z0,z2,z452,z14,z3,z9,z5]),(0,[z0,z37,z2,z3,z195,z9,z5]),(0,[z0,z103,z1,z2,z3,z9,z5]),(0,[z0,z164,z1,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z107,z92,z5])],[(0,[z44,z0,z12,z2,z3,z9,z5]),(0,[z0,z1,z2,z15,z57,z9,z5]),(0,[z0,z37,z2,z14,z3,z9,z5]),(0,[z0,z1,z2,z462,z3,z9,z5]),(0,[z160,z0,z1,z2,z3,z9,z5])],[(0,[z463,z0,z1,z2,z3,z9,z5]),(1,[z0,z1,z2,z464,z9,z5]),(0,[z0,z1,z2,z15,z3,z107,z5]),(0,[z0,z37,z2,z200,z3,z9,z5]),(0,[z0,z1,z2,z3,z9,z5,z465]),(0,[z7,z0,z1,z2,z3,z466,z5]),(0,[z0,z1,z2,z467,z3,z9,z5]),(0,[z0,z468,z1,z2,z3,z9,z5])],[(0,[z0,z1,z2,z3,z9,z469,z5]),(0,[z112,z0,z1,z2,z3,z9,z5]),(0,[z470,z0,z1,z2,z3,z9,z5]),(0,[z471,z0,z1,z2,z3,z9,z5])]],
   [[(0,[z0,z1,z2,z3,z107,z175,z5]),(0,[z472,z0,z1,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z35,z107,z5]),(0,[z0,z221,z1,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z9,z5,z473])],[(1,[z24,z12,z2,z3,z9,z5]),(0,[z94,z228,z1,z2,z3,z9,z5]),(0,[z228,z0,z1,z2,z3,z107,z5]),(0,[z64,z0,z474,z2,z3,z9,z5]),(0,[z64,z0,z1,z2,z436,z9,z5]),(1,[z32,z1,z2,z3,z9,z33]),(0,[z118,z0,z1,z2,z3,z9,z5]),(0,[z475,z0,z1,z2,z3,z9,z5]),(0,[z476,z0,z1,z2,z3,z9,z5]),(0,[z58,z0,z10,z2,z3,z9,z5])],[(0,[z94,z0,z1,z2,z3,z9,z371]),(0,[z0,z2,z194,z14,z3,z9,z5]),(0,[z0,z37,z2,z3,z9,z175,z5]),(0,[z0,z1,z2,z3,z49,z107,z5]),(0,[z0,z1,z2,z292,z3,z9,z5])],[(0,[z0,z1,z2,z477,z3,z9,z5]),(1,[z0,z1,z2,z3,z9,z253]),(0,[z0,z1,z2,z478,z3,z9,z5]),(0,[z0,z1,z2,z3,z57,z9,z5])],[(0,[z0,z1,z479,z2,z3,z9,z5]),(0,[z0,z1,z2,z464,z3,z9,z5]),(0,[z0,z480,z1,z2,z3,z9,z5]),(0,[z0,z1,z481,z2,z3,z9,z5])],[(0,[z0,z1,z2,z3,z72,z107,z5]),(0,[z0,z1,z2,z3,z482,z9,z5]),(0,[z0,z37,z2,z179,z3,z9,z5]),(0,[z0,z1,z2,z3,z483,z9,z5]),(1,[z77,z0,z1,z2,z9,z78])],[(0,[z171,z0,z37,z2,z3,z9,z5]),(0,[z0,z1,z172,z2,z3,z484,z5]),(0,[z74,z0,z1,z2,z3,z107,z5])],[(0,[z0,z1,z485,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z17,z5,z73]),(1,[z171,z0,z14,z3,z9,z5]),(1,[z0,z2,z14,z3,z107,z5]),(1,[z0,z37,z2,z3,z4,z5]),(0,[z11,z0,z1,z2,z3,z9,z92]),(0,[z0,z1,z2,z3,z9,z78,z5])]],
   [[(0,[z0,z486,z1,z2,z3,z9,z5]),(1,[z0,z354,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z451,z9,z5]),(0,[z0,z1,z2,z3,z95,z9,z5]),(0,[z0,z487,z1,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z107,z5,z199])],[(0,[z24,z0,z1,z2,z3,z9,z5]),(1,[z0,z1,z2,z3,z191,z5]),(0,[z488,z0,z1,z2,z3,z9,z5]),(0,[z0,z1,z2,z489,z3,z9,z5]),(0,[z0,z224,z1,z2,z3,z107,z5]),(0,[z0,z1,z2,z3,z490,z9,z5]),(0,[z0,z1,z491,z2,z3,z9,z5]),(1,[z0,z22,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z9,z199,z90]),(0,[z0,z1,z2,z492,z3,z9,z5])],[(0,[z0,z37,z2,z3,z9,z5,z199]),(0,[z0,z1,z2,z3,z493,z9,z5]),(0,[z0,z1,z2,z13,z3,z9,z5]),(0,[z494,z0,z1,z2,z3,z9,z5])],[(0,[z0,z495,z1,z2,z3,z9,z5]),(1,[z100,z1,z2,z15,z9,z5]),(0,[z218,z1,z2,z3,z9,z18,z5]),(0,[z0,z496,z1,z2,z3,z9,z5])],[(0,[z0,z1,z2,z3,z9,z5,z497]),(0,[z0,z1,z2,z3,z9,z498,z5]),(1,[z82,z1,z2,z3,z9,z156]),(0,[z0,z1,z2,z3,z9,z5,z499]),(0,[z500,z0,z1,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z107,z5,z73])],[(0,[z32,z228,z1,z2,z3,z9,z5]),(0,[z0,z501,z1,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z502,z9,z5]),(0,[z7,z0,z2,z14,z3,z9,z5]),(0,[z0,z1,z2,z503,z3,z9,z5]),(0,[z504,z0,z1,z2,z3,z9,z5]),(0,[z0,z1,z2,z52,z3,z9,z5]),(0,[z0,z1,z2,z3,z107,z505,z5]),(0,[z11,z0,z1,z3,z9,z5,z90])],[(0,[z42,z0,z37,z2,z3,z9,z5]),(0,[z0,z37,z2,z3,z9,z5,z73]),(0,[z44,z0,z1,z2,z3,z9,z5]),(0,[z11,z0,z1,z2,z257,z9,z5]),(0,[z77,z0,z1,z2,z3,z9,z199]),(0,[z506,z0,z1,z2,z3,z9,z5])],[(0,[z0,z1,z2,z507,z3,z9,z5]),(0,[z0,z440,z1,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z9,z5,z5]),(0,[z0,z37,z2,z3,z107,z9,z5]),(0,[z0,z50,z1,z2,z3,z107,z5]),(0,[z0,z1,z2,z3,z107,z68,z5])]],
   [[(0,[z0,z1,z508,z2,z3,z9,z5]),(0,[z0,z37,z2,z2,z3,z9,z5]),(0,[z0,z205,z37,z2,z3,z9,z5]),(0,[z509,z0,z1,z2,z3,z9,z5]),(0,[z510,z0,z1,z2,z3,z9,z5]),(1,[z121,z1,z2,z3,z9,z5])],[(0,[z0,z1,z2,z3,z511,z9,z5]),(0,[z0,z37,z1,z14,z3,z9,z5]),(0,[z174,z0,z1,z2,z3,z107,z5]),(1,[z0,z98,z2,z3,z9,z5])],[(0,[z0,z1,z2,z3,z9,z512,z5]),(0,[z100,z1,z2,z56,z3,z9,z5]),(0,[z82,z1,z26,z2,z3,z9,z5]),(1,[z0,z501,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z9,z513,z5]),(0,[z514,z0,z1,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z9,z515,z5]),(0,[z0,z1,z2,z3,z9,z5,z516]),(0,[z21,z0,z67,z2,z3,z9,z5]),(0,[z84,z0,z1,z2,z3,z107,z5]),(0,[z0,z1,z2,z61,z3,z75,z5])],[(0,[z0,z37,z12,z2,z3,z9,z5]),(0,[z0,z1,z2,z517,z3,z9,z5]),(0,[z100,z0,z1,z2,z3,z402,z5]),(1,[z0,z474,z2,z3,z9,z5]),(1,[z0,z1,z2,z436,z9,z5]),(0,[z518,z0,z1,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z9,z92,z156]),(0,[z21,z0,z1,z2,z3,z9,z6]),(0,[z0,z1,z2,z3,z284,z4,z5]),(0,[z0,z1,z2,z3,z519,z9,z5]),(0,[z0,z1,z2,z520,z3,z107,z5]),(0,[z0,z113,z1,z2,z3,z188,z5])],[(0,[z0,z1,z2,z3,z521,z9,z5]),(0,[z100,z0,z407,z2,z3,z9,z5]),(1,[z416,z1,z2,z3,z9,z5]),(0,[z0,z1,z2,z522,z3,z9,z5])],[(0,[z94,z0,z1,z2,z3,z107,z5]),(0,[z0,z1,z2,z3,z523,z9,z5]),(0,[z0,z1,z2,z3,z524,z107,z5]),(0,[z0,z1,z2,z61,z57,z9,z5])],[(0,[z77,z0,z1,z2,z15,z9,z5]),(1,[z0,z1,z525,z3,z9,z5]),(0,[z216,z0,z37,z2,z3,z9,z5]),(0,[z0,z1,z2,z61,z3,z107,z5])],[(0,[z0,z1,z285,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z526,z9,z5]),(0,[z0,z1,z527,z2,z3,z9,z5])]],
   [[(0,[z100,z0,z37,z2,z3,z9,z5]),(0,[z528,z0,z1,z2,z3,z9,z5]),(0,[z529,z0,z1,z2,z3,z9,z5]),(1,[z0,z1,z2,z3,z329,z5]),(0,[z530,z0,z1,z2,z3,z9,z5]),(0,[z0,z531,z1,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z532,z9,z5])],[(0,[z533,z0,z1,z2,z3,z9,z5]),(0,[z0,z1,z2,z534,z3,z9,z5]),(0,[z0,z1,z2,z3,z17,z107,z5]),(0,[z0,z1,z2,z3,z149,z9,z5]),(0,[z44,z0,z224,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z104,z107,z5]),(0,[z0,z1,z2,z3,z107,z5,z6]),(0,[z7,z0,z1,z2,z16,z9,z5]),(0,[z0,z1,z2,z3,z9,z535,z5]),(1,[z74,z0,z1,z2,z75,z5]),(1,[z0,z1,z2,z3,z188,z73])],[(0,[z0,z1,z2,z56,z3,z4,z5]),(0,[z463,z0,z2,z14,z3,z9,z5]),(0,[z0,z536,z1,z2,z3,z9,z5]),(0,[z0,z113,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z107,z75,z5])],[(0,[z112,z0,z2,z14,z3,z9,z5]),(0,[z0,z37,z2,z3,z9,z5,z6])],[(0,[z42,z0,z1,z2,z353,z9,z5]),(0,[z0,z106,z2,z3,z104,z9,z5]),(0,[z0,z537,z1,z2,z3,z9,z5]),(0,[z64,z0,z1,z2,z3,z107,z5]),(0,[z0,z2,z14,z3,z9,z445,z5]),(0,[z0,z37,z2,z3,z9,z75,z5]),(0,[z213,z0,z1,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z43,z4,z5])],[(0,[z538,z0,z1,z2,z3,z9,z5]),(0,[z0,z1,z2,z325,z3,z9,z5]),(0,[z0,z1,z2,z3,z9,z539,z5]),(0,[z540,z0,z1,z2,z3,z9,z5])],[(0,[z228,z1,z26,z2,z3,z9,z5]),(0,[z0,z1,z541,z2,z3,z9,z5]),(0,[z0,z37,z2,z3,z9,z274,z5]),(0,[z0,z1,z2,z3,z329,z9,z5]),(0,[z0,z1,z2,z3,z9,z542,z5]),(0,[z0,z1,z543,z2,z3,z9,z5]),(1,[z0,z1,z2,z3,z394,z5]),(0,[z0,z1,z2,z3,z544,z9,z5])],[(0,[z1,z2,z3,z72,z9,z33,z5]),(0,[z64,z218,z1,z2,z3,z9,z5]),(0,[z0,z1,z525,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z9,z347,z5]),(1,[z318,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z9,z545,z5]),(0,[z0,z1,z2,z3,z546,z9,z5]),(0,[z0,z1,z2,z16,z3,z107,z5])]],
   [[(0,[z547,z0,z1,z2,z3,z9,z5]),(0,[z42,z0,z1,z2,z464,z9,z5]),(0,[z1,z2,z15,z3,z72,z9,z5]),(0,[z82,z0,z1,z525,z3,z9,z5]),(0,[z0,z1,z172,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z9,z5,z548]),(0,[z549,z0,z1,z2,z3,z107,z5]),(0,[z0,z1,z2,z3,z550,z107,z5]),(0,[z0,z1,z27,z2,z3,z9,z92])],[(0,[z0,z1,z2,z3,z9,z551,z5]),(0,[z32,z0,z1,z2,z3,z107,z5]),(0,[z0,z2,z14,z3,z9,z5,z453]),(0,[z0,z1,z2,z3,z9,z484,z5]),(0,[z0,z1,z2,z3,z552,z9,z5]),(1,[z0,z1,z2,z3,z70,z5]),(1,[z0,z1,z51,z3,z107,z5])],[(0,[z0,z1,z12,z2,z3,z107,z5]),(1,[z0,z1,z2,z3,z249,z5]),(0,[z74,z0,z2,z14,z3,z9,z5]),(0,[z553,z0,z1,z2,z3,z9,z5])],[(0,[z0,z1,z2,z3,z18,z4,z5]),(0,[z74,z0,z1,z2,z3,z18,z5]),(0,[z554,z0,z1,z2,z3,z9,z5])],[(0,[z0,z37,z1,z2,z3,z9,z5]),(1,[z0,z1,z2,z3,z361,z5]),(0,[z0,z1,z2,z3,z555,z9,z5]),(0,[z0,z1,z2,z327,z3,z4,z5]),(0,[z0,z1,z2,z3,z9,z5,z556])],[(0,[z24,z0,z2,z14,z3,z9,z5]),(0,[z0,z224,z2,z14,z3,z9,z5]),(0,[z0,z1,z2,z13,z3,z4,z5]),(0,[z74,z0,z50,z1,z2,z3,z5]),(1,[z0,z1,z2,z3,z300,z5]),(0,[z0,z1,z2,z3,z9,z5,z557]),(0,[z58,z0,z1,z2,z3,z4,z5]),(0,[z11,z0,z1,z2,z3,z107,z5])],[(0,[z0,z1,z2,z3,z4,z33,z5]),(0,[z150,z0,z1,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z188,z9,z5])],[(0,[z0,z1,z2,z3,z558,z9,z5]),(0,[z0,z37,z2,z56,z3,z9,z5]),(0,[z0,z1,z2,z3,z9,z559,z5]),(0,[z32,z0,z1,z2,z3,z9,z156]),(0,[z560,z0,z1,z2,z3,z9,z5]),(0,[z0,z1,z561,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z9,z141,z5]),(0,[z0,z1,z2,z3,z9,z562,z5]),(0,[z0,z1,z2,z3,z9,z5,z563]),(0,[z0,z2,z3,z9,z5,z455,z73])]],
   [[(0,[z100,z1,z2,z3,z9,z18,z5]),(0,[z564,z0,z1,z2,z3,z9,z5]),(0,[z0,z1,z2,z565,z3,z9,z5]),(1,[z468,z1,z2,z3,z9,z5])],[(0,[z0,z2,z14,z3,z43,z9,z5]),(0,[z0,z37,z2,z3,z9,z5,z304]),(0,[z0,z1,z2,z566,z3,z9,z5]),(0,[z11,z0,z1,z2,z3,z372,z5])],[(0,[z0,z1,z2,z3,z9,z567,z5]),(0,[z44,z0,z2,z14,z3,z9,z5]),(0,[z0,z37,z69,z2,z3,z9,z5]),(0,[z0,z1,z2,z568,z3,z9,z5]),(0,[z569,z0,z1,z2,z3,z9,z5]),(0,[z0,z405,z1,z2,z3,z9,z5]),(0,[z0,z1,z2,z179,z3,z9,z199])],[(0,[z42,z0,z1,z2,z3,z191,z5]),(0,[z0,z1,z2,z3,z9,z33,z5]),(0,[z0,z2,z14,z3,z57,z9,z5]),(0,[z0,z50,z2,z14,z3,z9,z5]),(0,[z0,z1,z2,z3,z9,z5,z570]),(1,[z571,z1,z2,z3,z9,z5])],[(0,[z572,z0,z1,z2,z3,z9,z5]),(0,[z0,z50,z1,z2,z3,z18,z5]),(1,[z0,z440,z2,z3,z9,z5]),(0,[z0,z1,z2,z43,z9,z5,z199]),(0,[z0,z1,z2,z3,z9,z5,z573]),(0,[z0,z1,z27,z3,z9,z92,z5])],[(0,[z0,z1,z2,z3,z55,z9,z5]),(0,[z0,z1,z2,z3,z574,z9,z5]),(0,[z0,z106,z2,z3,z9,z5,z6]),(0,[z0,z1,z2,z3,z9,z242,z5]),(0,[z0,z1,z2,z3,z9,z243,z5]),(0,[z174,z0,z2,z14,z3,z9,z5]),(0,[z0,z1,z2,z3,z575,z4,z5]),(0,[z0,z1,z51,z2,z3,z4,z5])],[(0,[z0,z1,z2,z247,z3,z9,z5]),(0,[z174,z0,z1,z2,z3,z18,z5]),(0,[z273,z0,z37,z2,z3,z9,z5]),(0,[z576,z0,z1,z2,z3,z9,z5]),(1,[z0,z1,z2,z3,z107,z5]),(0,[z0,z577,z1,z2,z3,z9,z5])],[(0,[z0,z1,z2,z3,z9,z578,z5]),(0,[z0,z1,z2,z3,z9,z5,z579]),(0,[z0,z2,z14,z3,z9,z78,z5]),(0,[z580,z0,z1,z2,z3,z9,z5]),(0,[z21,z0,z1,z2,z3,z107,z5]),(0,[z0,z67,z1,z2,z3,z9,z6]),(0,[z0,z67,z1,z2,z3,z9,z68])]],
   [[(0,[z42,z0,z106,z2,z3,z9,z5]),(0,[z94,z82,z1,z2,z3,z9,z5]),(0,[z0,z1,z407,z2,z3,z9,z5]),(0,[z581,z0,z1,z2,z3,z9,z5]),(0,[z21,z174,z0,z2,z3,z9,z5]),(0,[z582,z0,z1,z2,z3,z9,z5])],[(0,[z94,z0,z2,z14,z3,z9,z5]),(0,[z0,z1,z2,z3,z9,z583,z5]),(1,[z0,z1,z2,z3,z287,z5]),(0,[z0,z37,z1,z172,z3,z9,z5]),(0,[z0,z1,z2,z3,z107,z5,z154])],[(0,[z94,z0,z354,z2,z3,z9,z5]),(0,[z0,z501,z26,z2,z3,z9,z5]),(1,[z0,z1,z2,z451,z9,z5]),(0,[z0,z2,z14,z13,z3,z9,z5]),(0,[z174,z0,z2,z3,z9,z175,z5]),(0,[z0,z1,z2,z3,z300,z5,z6]),(0,[z0,z1,z2,z3,z9,z219,z5])],[(0,[z0,z1,z2,z3,z9,z5,z584]),(0,[z585,z0,z1,z2,z3,z9,z5]),(1,[z44,z0,z2,z49,z9,z5]),(0,[z0,z1,z2,z3,z586,z9,z5]),(0,[z0,z587,z1,z2,z3,z9,z5])],[(0,[z42,z24,z1,z2,z3,z9,z5])],[(0,[z100,z0,z1,z2,z15,z9,z5]),(0,[z0,z1,z2,z588,z3,z9,z5]),(0,[z589,z0,z1,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z9,z40,z5]),(0,[z0,z590,z1,z2,z3,z9,z5]),(0,[z77,z468,z1,z2,z3,z9,z5])],[(0,[z0,z106,z1,z2,z3,z107,z5]),(0,[z21,z44,z0,z2,z3,z9,z5]),(0,[z591,z0,z1,z2,z3,z9,z5]),(0,[z592,z0,z1,z2,z3,z9,z5]),(0,[z593,z0,z1,z2,z3,z9,z5]),(0,[z0,z1,z69,z2,z43,z9,z5]),(0,[z0,z1,z2,z429,z3,z9,z5]),(0,[z0,z1,z594,z2,z3,z9,z5]),(1,[z595,z0,z2,z3,z9,z5])],[(0,[z0,z1,z2,z3,z9,z596,z5]),(0,[z0,z1,z432,z2,z3,z9,z5]),(1,[z0,z113,z1,z2,z3,z35])]],
   [[(0,[z64,z0,z2,z14,z3,z9,z5]),(0,[z82,z0,z1,z2,z3,z9,z5]),(0,[z82,z0,z1,z2,z3,z107,z5]),(0,[z597,z0,z1,z2,z3,z9,z5]),(0,[z77,z571,z1,z2,z3,z9,z5])],[(0,[z450,z0,z1,z2,z3,z9,z5]),(0,[z64,z0,z1,z2,z3,z18,z5]),(1,[z312,z1,z2,z3,z9,z5]),(0,[z0,z1,z69,z2,z3,z107,z5]),(0,[z598,z0,z1,z2,z3,z9,z5])],[(0,[z0,z1,z2,z3,z9,z599,z5]),(0,[z0,z37,z51,z2,z3,z9,z5]),(0,[z0,z27,z2,z292,z3,z9,z5]),(0,[z0,z1,z2,z600,z3,z9,z5])],[(0,[z0,z1,z2,z3,z9,z601,z5]),(0,[z82,z0,z1,z2,z3,z287,z5]),(0,[z0,z1,z2,z3,z107,z5,z156]),(0,[z0,z1,z2,z3,z237,z9,z5]),(0,[z0,z1,z172,z2,z3,z4,z5]),(1,[z0,z1,z2,z3,z466,z5]),(0,[z77,z0,z1,z2,z3,z107,z5]),(0,[z74,z0,z1,z2,z3,z57,z5]),(0,[z0,z1,z2,z3,z9,z602,z5])],[(0,[z0,z1,z603,z2,z3,z9,z5]),(0,[z94,z1,z2,z3,z9,z33,z5]),(0,[z0,z1,z26,z2,z3,z4,z5]),(0,[z0,z1,z604,z2,z3,z9,z5]),(0,[z605,z0,z1,z2,z3,z9,z5]),(0,[z606,z0,z1,z2,z3,z9,z5]),(0,[z121,z1,z2,z3,z9,z5,z90])],[(0,[z607,z0,z1,z2,z3,z9,z5]),(0,[z218,z0,z1,z2,z3,z9,z5]),(0,[z0,z2,z14,z3,z9,z18,z5]),(0,[z0,z37,z2,z3,z9,z5,z156]),(0,[z32,z0,z2,z14,z3,z9,z5]),(0,[z0,z1,z608,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z301,z4,z5]),(0,[z0,z456,z1,z2,z3,z9,z5])],[(0,[z94,z0,z1,z2,z3,z381,z5]),(0,[z0,z1,z26,z2,z3,z184,z5]),(0,[z82,z0,z1,z2,z3,z9,z156]),(0,[z0,z1,z2,z3,z609,z9,z5]),(0,[z0,z1,z27,z2,z3,z107,z5]),(0,[z0,z1,z2,z3,z9,z415,z5]),(0,[z77,z0,z1,z2,z9,z78,z5])],[(0,[z0,z1,z2,z610,z3,z9,z5]),(0,[z82,z0,z1,z2,z3,z9,z33]),(0,[z0,z37,z1,z2,z3,z4,z5]),(0,[z7,z120,z1,z2,z3,z9,z5]),(0,[z0,z1,z291,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z144,z107,z5])]],
   [[(0,[z0,z1,z2,z3,z349,z9,z5]),(1,[z94,z1,z56,z3,z9,z5]),(0,[z0,z1,z611,z2,z3,z9,z5]),(0,[z612,z0,z1,z2,z3,z9,z5])],[(0,[z613,z0,z1,z2,z3,z9,z5]),(0,[z0,z1,z2,z15,z3,z9,z5]),(0,[z0,z614,z1,z2,z3,z9,z5]),(0,[z174,z0,z2,z3,z9,z68,z5]),(0,[z0,z1,z2,z3,z615,z9,z5]),(0,[z0,z1,z2,z3,z188,z4,z5]),(0,[z0,z1,z2,z3,z9,z5,z455])],[(0,[z616,z0,z1,z2,z3,z9,z5]),(1,[z0,z1,z2,z3,z297,z5]),(0,[z0,z1,z2,z3,z9,z78,z90])],[(0,[z174,z0,z12,z2,z3,z9,z5]),(0,[z112,z0,z1,z2,z72,z9,z5]),(0,[z112,z1,z2,z3,z72,z9,z5]),(0,[z0,z1,z2,z3,z9,z5,z617]),(0,[z44,z119,z1,z2,z3,z9,z5]),(0,[z618,z0,z1,z2,z3,z9,z5]),(0,[z619,z0,z1,z2,z3,z9,z5]),(0,[z0,z1,z3,z107,z9,z4,z5]),(0,[z0,z620,z1,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z35,z9,z5])],[(0,[z0,z1,z621,z2,z3,z9,z5]),(0,[z0,z622,z1,z2,z3,z9,z5]),(0,[z228,z0,z1,z2,z3,z9,z5]),(0,[z112,z100,z1,z2,z3,z9,z5]),(1,[z0,z1,z2,z3,z237,z5]),(0,[z0,z1,z2,z3,z9,z5,z623])],[(0,[z624,z0,z1,z2,z3,z9,z5]),(0,[z228,z1,z2,z3,z72,z9,z5]),(0,[z0,z1,z2,z3,z9,z625,z5]),(0,[z0,z1,z626,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z49,z9,z5]),(0,[z0,z1,z2,z3,z9,z627,z5]),(0,[z0,z1,z2,z3,z4,z628,z5]),(0,[z0,z1,z2,z3,z4,z5,z90]),(0,[z569,z0,z1,z2,z3,z4,z5]),(0,[z230,z0,z1,z2,z3,z9,z5])],[(0,[z0,z1,z629,z2,z3,z9,z5]),(0,[z100,z228,z1,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z9,z630,z5]),(0,[z0,z1,z2,z3,z9,z631,z5]),(0,[z0,z1,z2,z3,z9,z632,z5]),(0,[z0,z1,z2,z3,z9,z5,z633]),(0,[z0,z1,z2,z3,z9,z5,z39]),(0,[z634,z0,z1,z2,z3,z9,z5]),(0,[z0,z1,z635,z2,z3,z9,z5])],[(0,[z0,z0,z1,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z3,z9,z5]),(0,[z0,z1,z636,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z297,z9,z5]),(0,[z571,z0,z1,z2,z3,z9,z5]),(0,[z595,z0,z2,z3,z9,z5,z73]),(0,[z0,z1,z2,z3,z637,z9,z5])]],
   [[(0,[z0,z1,z2,z3,z72,z9,z5]),(0,[z32,z1,z2,z3,z9,z33,z5]),(0,[z171,z0,z1,z2,z3,z107,z5]),(0,[z0,z345,z37,z2,z3,z9,z5]),(0,[z638,z0,z1,z2,z3,z9,z5]),(0,[z0,z1,z2,z639,z3,z9,z5]),(0,[z640,z0,z1,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z9,z641,z5])],[(0,[z0,z1,z2,z3,z9,z5,z642]),(0,[z0,z37,z26,z2,z3,z9,z5]),(0,[z0,z1,z276,z2,z3,z9,z5]),(0,[z74,z0,z1,z2,z3,z9,z5]),(1,[z0,z2,z3,z9,z197,z5]),(0,[z643,z0,z1,z2,z3,z9,z5])],[(0,[z0,z1,z2,z3,z9,z371,z5]),(0,[z0,z1,z2,z644,z3,z9,z5]),(0,[z0,z1,z2,z3,z9,z628,z5]),(0,[z74,z0,z1,z2,z72,z9,z5]),(1,[z0,z2,z14,z3,z9,z5]),(0,[z0,z224,z1,z2,z49,z9,z5]),(0,[z0,z1,z2,z3,z9,z645,z5]),(0,[z0,z1,z646,z2,z3,z9,z5]),(0,[z0,z1,z2,z647,z3,z9,z5]),(0,[z0,z1,z2,z3,z9,z5,z90])],[(0,[z0,z648,z1,z2,z3,z9,z5]),(0,[z580,z0,z2,z14,z3,z9,z5]),(0,[z0,z1,z2,z3,z649,z9,z5]),(0,[z0,z67,z1,z2,z3,z107,z5]),(0,[z0,z1,z2,z3,z4,z92,z5]),(0,[z187,z0,z1,z2,z3,z107,z5]),(0,[z0,z1,z2,z61,z3,z57,z5]),(0,[z0,z1,z2,z3,z9,z650,z5])],[(0,[z651,z0,z1,z2,z3,z9,z5]),(0,[z0,z113,z1,z2,z3,z17,z5]),(0,[z0,z224,z1,z2,z3,z9,z5]),(0,[z0,z2,z3,z9,z197,z75,z5])],[(0,[z652,z0,z1,z2,z3,z9,z5]),(0,[z0,z224,z1,z2,z72,z9,z5]),(1,[z0,z1,z2,z3,z28,z5]),(0,[z0,z1,z653,z2,z3,z9,z5]),(0,[z7,z0,z1,z3,z43,z9,z5]),(0,[z0,z1,z2,z3,z70,z9,z5])],[(0,[z100,z0,z1,z2,z3,z249,z5]),(0,[z0,z1,z2,z3,z9,z654,z5]),(1,[z218,z1,z2,z3,z18,z5]),(0,[z0,z1,z2,z3,z9,z5,z655]),(0,[z0,z2,z14,z3,z188,z9,z5]),(0,[z0,z172,z2,z14,z3,z9,z5]),(1,[z0,z1,z2,z179,z9,z199]),(0,[z0,z1,z2,z3,z9,z656,z5])],[(0,[z0,z1,z2,z14,z3,z107,z5]),(0,[z34,z0,z1,z2,z3,z9,z5]),(0,[z44,z0,z1,z2,z49,z9,z5]),(0,[z657,z0,z1,z2,z3,z9,z5]),(0,[z7,z0,z1,z69,z3,z9,z5]),(0,[z0,z1,z2,z3,z466,z9,z5]),(0,[z7,z0,z1,z2,z3,z4,z5]),(0,[z658,z0,z1,z2,z3,z9,z5]),(1,[z0,z1,z2,z3,z535,z5])]],
   [[(0,[z42,z0,z1,z2,z3,z107,z5]),(0,[z0,z1,z2,z3,z9,z5,z659]),(0,[z0,z1,z2,z3,z9,z92,z5]),(0,[z0,z113,z1,z2,z3,z9,z73]),(0,[z0,z660,z1,z2,z3,z9,z5])],[(1,[z21,z0,z2,z3,z9,z6]),(0,[z0,z1,z2,z3,z4,z4,z5])],[(0,[z0,z106,z2,z14,z3,z9,z5]),(0,[z44,z0,z1,z2,z72,z9,z5]),(0,[z0,z50,z1,z2,z3,z9,z5]),(0,[z661,z0,z1,z2,z3,z9,z5])],[(0,[z0,z1,z2,z3,z9,z662,z5]),(0,[z0,z2,z14,z3,z9,z33,z5]),(0,[z0,z663,z1,z2,z3,z9,z5])],[(0,[z664,z0,z1,z2,z3,z9,z5]),(0,[z1,z2,z56,z3,z72,z9,z5]),(0,[z82,z0,z2,z14,z3,z9,z5]),(0,[z174,z0,z1,z2,z3,z9,z5]),(0,[z74,z0,z1,z2,z61,z9,z5]),(1,[z0,z2,z3,z9,z5,z222])],[(0,[z84,z0,z1,z2,z3,z9,z5]),(0,[z1,z26,z2,z3,z9,z33,z5]),(0,[z665,z0,z1,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z666,z9,z5]),(0,[z667,z0,z1,z2,z3,z9,z5]),(0,[z0,z164,z51,z2,z3,z9,z5])],[(0,[z668,z0,z1,z2,z3,z9,z5]),(0,[z0,z1,z26,z2,z3,z242,z5]),(0,[z21,z0,z1,z2,z3,z9,z68]),(0,[z0,z1,z2,z3,z9,z4,z5]),(0,[z0,z1,z2,z520,z3,z9,z5])],[(1,[z0,z1,z2,z3,z381,z5]),(0,[z669,z0,z1,z2,z3,z9,z5]),(0,[z82,z0,z1,z2,z3,z28,z5]),(0,[z77,z0,z2,z14,z3,z9,z5]),(0,[z0,z1,z670,z2,z3,z9,z5]),(1,[z0,z1,z2,z3,z484,z5]),(0,[z671,z0,z1,z2,z3,z9,z5]),(0,[z0,z1,z16,z3,z43,z9,z5]),(0,[z606,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z179,z3,z107,z5])]],
   [[(0,[z94,z0,z1,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z9,z5,z672]),(0,[z0,z1,z2,z3,z9,z673,z5]),(0,[z0,z50,z1,z2,z3,z104,z5]),(0,[z21,z0,z2,z3,z104,z9,z5]),(0,[z0,z1,z2,z3,z524,z9,z5]),(0,[z0,z1,z2,z3,z9,z575,z5]),(0,[z0,z1,z2,z3,z110,z9,z5])],[(0,[z674,z0,z1,z2,z3,z9,z5]),(0,[z675,z0,z1,z2,z3,z9,z5]),(0,[z218,z0,z2,z14,z3,z9,z5]),(0,[z0,z1,z2,z676,z3,z9,z5]),(0,[z0,z1,z2,z3,z9,z5,z677]),(1,[z0,z1,z27,z3,z9,z92]),(0,[z0,z1,z2,z61,z3,z9,z5]),(0,[z678,z0,z1,z2,z3,z9,z5])],[(0,[z0,z1,z2,z679,z3,z9,z5]),(0,[z100,z0,z1,z2,z3,z107,z5]),(0,[z218,z0,z1,z2,z3,z18,z5]),(0,[z0,z224,z1,z2,z13,z9,z5]),(0,[z174,z0,z1,z2,z3,z104,z5]),(0,[z680,z0,z1,z2,z3,z9,z5])],[(0,[z0,z1,z474,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z681,z9,z5])],[(0,[z0,z1,z2,z3,z184,z9,z5]),(0,[z0,z1,z2,z3,z17,z9,z5]),(0,[z0,z1,z2,z3,z104,z9,z5])],[(0,[z112,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z9,z5,z682]),(0,[z0,z1,z2,z3,z9,z5,z683]),(0,[z0,z1,z684,z2,z3,z9,z5]),(0,[z74,z0,z1,z2,z3,z188,z5]),(0,[z0,z1,z2,z3,z685,z9,z5]),(0,[z595,z0,z1,z2,z3,z9,z5])],[(0,[z686,z0,z1,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z4,z68,z5]),(0,[z0,z69,z2,z429,z3,z9,z5]),(0,[z0,z1,z2,z3,z35,z4,z5]),(0,[z0,z1,z2,z3,z687,z9,z5])],[(0,[z64,z0,z1,z2,z3,z9,z5]),(1,[z64,z1,z2,z3,z17,z5]),(0,[z44,z0,z1,z2,z13,z9,z5]),(0,[z0,z1,z2,z688,z3,z9,z5]),(0,[z0,z1,z27,z2,z3,z535,z5]),(0,[z74,z160,z1,z2,z3,z9,z5])]],
   [[(0,[z689,z0,z1,z2,z3,z9,z5]),(0,[z305,z0,z1,z2,z3,z9,z5]),(0,[z228,z0,z2,z14,z3,z9,z5]),(0,[z64,z1,z2,z3,z72,z9,z5]),(0,[z0,z1,z2,z3,z9,z5,z690]),(0,[z0,z1,z691,z2,z3,z9,z5]),(0,[z0,z1,z2,z692,z3,z9,z5])],[(0,[z64,z100,z1,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z693,z9,z5]),(0,[z0,z1,z2,z3,z57,z4,z5]),(0,[z0,z1,z2,z3,z107,z107,z5]),(0,[z0,z1,z2,z3,z9,z505,z5])],[(0,[z0,z694,z1,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z9,z695,z5]),(0,[z127,z0,z1,z2,z3,z9,z5]),(0,[z0,z696,z1,z2,z3,z9,z5]),(0,[z0,z1,z2,z16,z3,z9,z5]),(0,[z0,z1,z2,z2,z3,z107,z5]),(1,[z0,z221,z2,z3,z9,z5]),(0,[z0,z215,z27,z2,z3,z9,z5])],[(0,[z697,z0,z1,z2,z3,z9,z5]),(0,[z0,z1,z2,z16,z72,z9,z5]),(0,[z698,z0,z1,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z9,z699,z5]),(0,[z0,z1,z2,z3,z9,z68,z5]),(0,[z549,z0,z1,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z550,z9,z5])],[(0,[z700,z0,z1,z2,z3,z9,z5]),(0,[z701,z0,z1,z2,z3,z9,z5]),(0,[z32,z0,z1,z2,z3,z9,z5]),(0,[z0,z1,z702,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z9,z5,z703]),(0,[z74,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z12,z2,z3,z9,z5]),(0,[z704,z0,z1,z2,z3,z9,z5])],[(0,[z0,z1,z2,z3,z402,z9,z5]),(0,[z0,z1,z2,z3,z9,z33,z90]),(0,[z0,z50,z1,z2,z3,z188,z5]),(0,[z0,z1,z2,z3,z9,z5,z705]),(0,[z0,z1,z2,z3,z9,z384,z5])],[(0,[z24,z0,z1,z2,z3,z4,z5]),(1,[z0,z1,z83,z3,z9,z5]),(0,[z0,z67,z2,z14,z3,z9,z5]),(0,[z0,z224,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z175,z4,z5]),(0,[z0,z1,z2,z3,z706,z9,z5])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z707,z5]),(0,[z0,z27,z14,z3,z4,z5]),(0,[z44,z0,z2,z708,z9,z5]),(0,[z709,z0,z2,z3,z4,z5]),(0,[z331,z0,z2,z3,z4,z5])],[(0,[z0,z227,z14,z3,z9,z5]),(0,[z0,z2,z710,z3,z9,z5])],[(0,[z312,z115,z2,z3,z9,z5]),(0,[z0,z157,z2,z3,z9,z5]),(0,[z468,z1,z2,z3,z4,z5]),(0,[z357,z1,z27,z3,z9,z5])],[(0,[z0,z1,z2,z3,z9,z711]),(0,[z160,z1,z2,z3,z9,z5]),(1,[z1,z2,z3,z712,z5]),(0,[z606,z1,z2,z3,z18,z5]),(0,[z0,z2,z14,z3,z40,z5]),(0,[z0,z2,z3,z4,z197,z5])],[(0,[z0,z1,z2,z713,z9,z5]),(0,[z8,z98,z2,z3,z9,z5])],[(0,[z0,z2,z14,z3,z53,z5]),(0,[z0,z1,z714,z3,z9,z5]),(0,[z120,z1,z2,z3,z466,z5]),(0,[z571,z1,z2,z3,z4,z5])],[(0,[z0,z501,z2,z3,z242,z5])],[(0,[z42,z106,z2,z3,z107,z5]),(0,[z121,z37,z2,z3,z9,z5]),(0,[z0,z98,z2,z3,z9,z39]),(0,[z121,z715,z2,z3,z9,z5])],[(0,[z0,z1,z2,z716,z9,z5]),(0,[z0,z2,z3,z9,z197,z5])],[(0,[z0,z440,z2,z178,z9,z5]),(0,[z595,z0,z2,z3,z188,z5])],[(0,[z0,z717,z2,z3,z9,z5]),(0,[z112,z1,z2,z72,z107,z5]),(0,[z0,z718,z2,z3,z9,z5])],[(0,[z0,z719,z2,z3,z9,z5]),(0,[z0,z37,z2,z3,z9,z63]),(0,[z0,z1,z2,z178,z107,z5]),(0,[z0,z720,z2,z3,z9,z5]),(0,[z0,z721,z2,z3,z9,z5])],[(0,[z0,z432,z2,z3,z4,z5]),(0,[z0,z1,z2,z451,z4,z5]),(0,[z0,z37,z2,z722,z9,z5])],[(0,[z554,z1,z2,z3,z9,z33]),(0,[z0,z14,z3,z107,z4,z5]),(0,[z723,z1,z2,z3,z9,z5]),(0,[z0,z2,z3,z708,z9,z5]),(0,[z724,z0,z2,z3,z9,z5]),(0,[z74,z0,z1,z2,z400,z5])],[(0,[z0,z725,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z726,z5]),(0,[z58,z0,z37,z3,z4,z5]),(0,[z0,z37,z2,z257,z9,z5]),(0,[z0,z59,z2,z3,z107,z5])],[]],
   [[(0,[z0,z1,z2,z3,z727,z5]),(0,[z0,z2,z728,z3,z9,z5])],[(0,[z177,z1,z2,z3,z9,z156]),(0,[z643,z0,z1,z43,z9,z5]),(0,[z77,z0,z1,z2,z9,z729])],[(0,[z0,z730,z2,z3,z9,z5]),(0,[z0,z1,z525,z3,z731,z5]),(0,[z0,z1,z503,z3,z107,z5]),(0,[z7,z8,z1,z43,z9,z5])],[(0,[z312,z1,z2,z3,z4,z5]),(0,[z21,z0,z2,z3,z9,z275]),(0,[z732,z1,z2,z3,z9,z5])],[(0,[z0,z1,z2,z733,z9,z5]),(0,[z120,z2,z14,z3,z9,z5]),(0,[z0,z2,z3,z9,z734,z5]),(0,[z0,z735,z2,z3,z9,z5])],[(0,[z0,z736,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z87,z73]),(0,[z235,z0,z2,z3,z107,z5])],[(0,[z32,z1,z2,z3,z9,z262])],[(0,[z737,z1,z2,z3,z9,z5])],[(0,[z0,z37,z51,z3,z107,z5]),(0,[z0,z1,z27,z3,z9,z92])],[(0,[z0,z37,z517,z3,z9,z5]),(0,[z0,z37,z2,z3,z249,z5]),(0,[z0,z2,z14,z738,z9,z5])],[(0,[z24,z739,z2,z3,z9,z5]),(0,[z0,z65,z2,z3,z18,z5]),(0,[z0,z2,z14,z110,z9,z5])],[(0,[z357,z1,z3,z9,z5,z90]),(0,[z0,z221,z2,z3,z40,z5])],[(0,[z0,z37,z676,z3,z9,z5]),(0,[z0,z1,z2,z3,z740,z5])],[(0,[z2,z14,z3,z9,z5,z741])],[],[(0,[z0,z742,z2,z3,z9,z5]),(0,[z0,z743,z2,z3,z9,z5]),(0,[z0,z1,z2,z436,z17,z5]),(0,[z468,z37,z2,z3,z9,z5])]],
   [[(0,[z0,z1,z744,z3,z9,z5]),(0,[z127,z0,z2,z3,z175,z5]),(0,[z0,z1,z2,z3,z745,z5]),(0,[z0,z1,z79,z3,z107,z5]),(0,[z746,z1,z2,z3,z9,z5])],[(0,[z0,z37,z2,z3,z402,z5]),(0,[z747,z0,z2,z3,z9,z5]),(0,[z8,z1,z2,z3,z107,z5]),(0,[z0,z2,z3,z107,z5,z455]),(0,[z748,z1,z2,z3,z9,z5])],[(0,[z0,z1,z2,z3,z242,z5]),(0,[z571,z37,z2,z3,z9,z5]),(0,[z11,z0,z221,z3,z9,z90])],[(0,[z0,z1,z83,z3,z749,z5]),(0,[z0,z2,z3,z104,z173,z5]),(0,[z140,z174,z0,z2,z3,z5]),(0,[z21,z0,z2,z3,z300,z5])],[(0,[z0,z2,z750,z3,z9,z5]),(0,[z0,z1,z209,z3,z4,z5])],[(0,[z0,z1,z2,z3,z751,z5]),(0,[z0,z752,z2,z3,z9,z5]),(0,[z753,z0,z2,z3,z9,z5]),(0,[z0,z2,z3,z9,z754,z6])],[(0,[z0,z755,z2,z3,z9,z5]),(0,[z0,z1,z83,z3,z9,z5]),(0,[z74,z0,z2,z14,z75,z5]),(0,[z0,z22,z2,z3,z4,z5])],[(0,[z0,z354,z2,z3,z9,z63]),(0,[z0,z10,z2,z3,z9,z5]),(0,[z7,z0,z1,z43,z9,z253])],[(0,[z0,z1,z2,z3,z756,z5]),(0,[z0,z757,z2,z3,z9,z5]),(0,[z0,z37,z2,z3,z287,z5]),(0,[z0,z1,z758,z3,z9,z5]),(0,[z0,z1,z2,z179,z4,z199])],[(0,[z1,z2,z3,z402,z18,z5]),(0,[z0,z37,z2,z451,z9,z5]),(0,[z0,z37,z2,z3,z372,z5]),(0,[z759,z1,z2,z3,z9,z5]),(0,[z1,z2,z3,z9,z5,z760]),(0,[z761,z1,z2,z3,z4,z5])],[(0,[z218,z1,z2,z3,z219,z5]),(0,[z0,z2,z762,z3,z9,z5]),(0,[z763,z0,z2,z14,z3,z5])],[(0,[z0,z2,z14,z3,z168,z5])],[(0,[z44,z0,z2,z313,z9,z5]),(0,[z7,z120,z1,z43,z9,z5]),(0,[z0,z1,z2,z3,z764,z5])],[(0,[z0,z1,z83,z3,z9,z33]),(0,[z0,z1,z2,z3,z749,z5]),(0,[z0,z37,z2,z3,z765,z5])],[(0,[z0,z1,z2,z3,z766,z5]),(0,[z64,z65,z2,z3,z17,z5]),(0,[z0,z2,z14,z3,z767,z5]),(0,[z8,z1,z2,z3,z466,z5]),(0,[z0,z768,z2,z3,z9,z5])],[(0,[z0,z769,z2,z3,z9,z5]),(0,[z0,z770,z2,z3,z9,z5]),(0,[z21,z0,z2,z3,z9,z516]),(0,[z0,z1,z3,z167,z4,z5]),(0,[z0,z1,z3,z107,z602,z5]),(0,[z0,z2,z3,z9,z5,z771])]],
   [[(0,[z0,z772,z2,z3,z9,z5]),(0,[z0,z1,z320,z3,z9,z92]),(0,[z174,z0,z2,z3,z105,z5]),(0,[z312,z37,z2,z3,z9,z5]),(0,[z0,z1,z69,z16,z107,z5])],[(0,[z0,z1,z2,z3,z773,z5]),(0,[z0,z1,z2,z3,z466,z39]),(0,[z0,z1,z3,z9,z5,z774]),(0,[z0,z1,z2,z3,z775,z5])],[(0,[z0,z776,z525,z3,z9,z5]),(0,[z0,z37,z172,z3,z107,z5]),(0,[z0,z1,z2,z3,z9,z777]),(0,[z0,z221,z2,z110,z9,z5])],[(0,[z118,z106,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z778,z5]),(0,[z153,z1,z56,z3,z9,z5]),(0,[z251,z1,z2,z72,z9,z5]),(0,[z174,z119,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z9,z779]),(0,[z0,z1,z2,z3,z780,z5]),(0,[z0,z1,z27,z3,z4,z92]),(0,[z357,z1,z2,z3,z107,z5])],[(0,[z547,z0,z14,z3,z9,z5]),(0,[z0,z37,z2,z353,z9,z5]),(0,[z158,z1,z2,z3,z9,z33]),(0,[z781,z1,z2,z3,z9,z5]),(0,[z0,z215,z2,z3,z107,z5]),(0,[z0,z2,z782,z3,z9,z5])],[(0,[z216,z276,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z783,z5]),(0,[z0,z2,z3,z104,z734,z5])],[(0,[z100,z1,z2,z679,z9,z5]),(0,[z0,z1,z525,z3,z784,z5]),(0,[z0,z22,z2,z3,z384,z5]),(0,[z0,z2,z292,z3,z107,z5])],[(0,[z44,z0,z2,z346,z9,z5]),(0,[z44,z119,z2,z49,z9,z5]),(0,[z0,z1,z2,z3,z785,z5]),(0,[z786,z0,z2,z3,z9,z5])],[(0,[z44,z0,z2,z511,z9,z5]),(0,[z0,z37,z2,z464,z9,z5]),(0,[z0,z210,z14,z3,z9,z5]),(0,[z0,z1,z2,z3,z787,z5]),(0,[z0,z1,z2,z3,z136,z154]),(0,[z331,z0,z2,z61,z3,z5])],[(0,[z228,z1,z2,z3,z9,z63]),(0,[z0,z37,z2,z3,z297,z5]),(0,[z0,z1,z2,z110,z9,z90]),(0,[z0,z2,z788,z3,z9,z5])],[(0,[z0,z115,z2,z3,z9,z5]),(0,[z24,z12,z2,z3,z107,z5]),(0,[z789,z0,z2,z3,z9,z5]),(0,[z0,z1,z2,z790,z9,z5])],[(0,[z0,z115,z2,z72,z9,z5]),(0,[z0,z1,z2,z3,z791,z5]),(0,[z0,z1,z2,z3,z792,z5]),(0,[z0,z1,z2,z110,z40,z5])],[(0,[z0,z1,z2,z3,z9,z793]),(0,[z0,z2,z194,z3,z9,z445])],[(0,[z0,z1,z2,z3,z794,z5]),(0,[z8,z2,z14,z3,z9,z5]),(0,[z795,z0,z37,z2,z3,z5]),(0,[z0,z37,z2,z3,z9,z253]),(0,[z796,z1,z2,z3,z9,z5]),(0,[z0,z2,z13,z9,z5,z633]),(0,[z0,z2,z797,z3,z9,z5])],[(0,[z0,z1,z2,z247,z9,z5]),(0,[z0,z2,z14,z3,z243,z5]),(0,[z119,z2,z14,z3,z9,z5]),(0,[z0,z2,z798,z3,z9,z5])],[(0,[z0,z1,z2,z9,z729,z199])]],
   [[(0,[z100,z1,z2,z15,z402,z5]),(0,[z0,z2,z14,z3,z9,z39]),(0,[z0,z378,z14,z3,z9,z5]),(0,[z799,z0,z2,z3,z107,z5]),(0,[z0,z800,z2,z3,z9,z5])],[(0,[z100,z407,z2,z15,z9,z5]),(0,[z0,z474,z2,z286,z9,z5]),(0,[z0,z1,z83,z3,z4,z5]),(0,[z0,z2,z325,z3,z144,z5]),(0,[z0,z2,z52,z3,z107,z5]),(0,[z0,z801,z2,z3,z9,z5])],[(0,[z595,z0,z2,z3,z17,z5]),(0,[z0,z2,z802,z3,z9,z5]),(0,[z7,z0,z1,z43,z394,z5]),(0,[z0,z10,z2,z3,z4,z5]),(0,[z0,z2,z3,z107,z803,z5]),(0,[z804,z1,z2,z3,z9,z5]),(0,[z0,z1,z2,z179,z202,z199])],[],[(0,[z0,z113,z2,z14,z3,z35])],[(0,[z0,z1,z2,z3,z805,z5]),(0,[z0,z1,z2,z3,z806,z5]),(0,[z218,z37,z2,z3,z18,z5]),(0,[z0,z37,z2,z179,z9,z199]),(0,[z0,z1,z3,z807,z4,z5])],[(0,[z115,z12,z2,z3,z9,z5]),(0,[z82,z1,z2,z269,z9,z5])],[(0,[z160,z1,z2,z72,z9,z5]),(0,[z0,z808,z2,z3,z9,z5])],[(0,[z0,z1,z2,z3,z9,z809]),(0,[z0,z1,z2,z3,z810,z5]),(0,[z0,z291,z2,z3,z9,z253])],[(0,[z0,z1,z2,z3,z811,z5]),(0,[z82,z432,z2,z3,z9,z156]),(0,[z82,z1,z2,z451,z9,z156]),(0,[z121,z1,z2,z3,z107,z5]),(0,[z11,z0,z1,z3,z9,z90]),(0,[z0,z2,z812,z3,z9,z5])],[(0,[z618,z12,z2,z3,z9,z5]),(0,[z0,z525,z813,z3,z9,z5]),(0,[z0,z776,z2,z3,z9,z5]),(0,[z0,z1,z3,z107,z4,z5]),(0,[z0,z1,z2,z814,z4,z5])],[(0,[z0,z1,z2,z3,z4,z5]),(0,[z0,z285,z2,z3,z9,z5]),(0,[z0,z1,z2,z815,z9,z5]),(0,[z0,z501,z2,z3,z107,z5])],[(0,[z94,z56,z14,z3,z9,z5])],[(0,[z0,z1,z2,z3,z184,z5]),(0,[z0,z1,z2,z3,z107,z63]),(0,[z0,z1,z2,z3,z816,z5])],[(0,[z0,z2,z817,z3,z9,z5]),(0,[z0,z1,z2,z3,z784,z5]),(0,[z0,z818,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z819,z5]),(0,[z0,z172,z820,z3,z9,z5])],[(0,[z597,z1,z2,z72,z9,z5]),(0,[z121,z1,z2,z3,z9,z156]),(0,[z357,z2,z14,z3,z9,z5])]],
   [[(0,[z100,z1,z2,z178,z9,z5]),(0,[z0,z37,z525,z3,z9,z5]),(0,[z0,z205,z2,z3,z104,z5]),(0,[z0,z1,z2,z257,z107,z5])],[(0,[z0,z1,z2,z353,z191,z5]),(0,[z0,z2,z179,z9,z222,z199])],[(0,[z312,z106,z2,z3,z9,z5]),(1,[z1,z83,z3,z9,z156]),(0,[z0,z1,z2,z821,z9,z5]),(0,[z0,z37,z2,z3,z329,z5])],[(0,[z0,z822,z2,z3,z9,z5]),(1,[z1,z56,z3,z9,z63]),(0,[z0,z2,z823,z3,z9,z5])],[(0,[z0,z1,z2,z269,z381,z5]),(0,[z0,z1,z2,z57,z824,z5])],[(0,[z0,z1,z2,z464,z191,z5]),(0,[z0,z115,z2,z3,z4,z5]),(0,[z174,z0,z2,z3,z239,z5])],[(0,[z34,z0,z2,z95,z9,z5]),(0,[z0,z1,z2,z3,z825,z5]),(0,[z826,z1,z2,z3,z9,z5])],[(0,[z0,z133,z14,z3,z9,z5]),(0,[z0,z1,z2,z3,z712,z5]),(0,[z0,z2,z3,z9,z827,z5]),(0,[z0,z14,z3,z490,z9,z5]),(0,[z828,z1,z2,z3,z9,z5])],[(0,[z829,z2,z14,z3,z9,z5]),(0,[z0,z37,z2,z3,z394,z5]),(0,[z0,z1,z2,z61,z575,z5])],[(0,[z0,z1,z2,z534,z57,z5]),(0,[z0,z1,z2,z3,z9,z830]),(0,[z549,z1,z2,z3,z125,z5])],[(0,[z0,z106,z2,z464,z9,z5]),(0,[z1,z2,z3,z9,z831,z5])],[(0,[z0,z820,z14,z3,z9,z5]),(0,[z0,z37,z2,z3,z832,z5]),(0,[z0,z37,z2,z3,z70,z5]),(0,[z0,z37,z172,z3,z484,z5]),(0,[z0,z1,z2,z3,z384,z5]),(0,[z0,z1,z3,z93,z4,z5]),(0,[z0,z833,z2,z3,z107,z5])],[(0,[z0,z1,z2,z3,z834,z5]),(0,[z0,z1,z2,z286,z9,z5]),(0,[z835,z1,z2,z3,z9,z5]),(0,[z836,z1,z2,z3,z9,z5])],[(0,[z230,z1,z2,z3,z9,z5])],[(0,[z0,z37,z2,z3,z361,z5]),(0,[z837,z0,z1,z2,z3,z5]),(0,[z468,z1,z2,z43,z9,z5])],[(0,[z94,z1,z56,z3,z9,z63]),(0,[z0,z2,z838,z3,z9,z5]),(0,[z0,z37,z2,z3,z300,z5]),(0,[z331,z0,z2,z3,z107,z5])]],
   [[(0,[z839,z1,z2,z3,z9,z5]),(0,[z840,z37,z2,z3,z9,z5]),(0,[z841,z1,z2,z3,z9,z5]),(0,[z0,z2,z3,z9,z5,z842]),(0,[z0,z157,z2,z3,z4,z5])],[(0,[z0,z1,z2,z843,z9,z5]),(0,[z160,z1,z2,z3,z4,z5]),(0,[z468,z1,z2,z3,z107,z5]),(0,[z0,z2,z3,z168,z5,z222])],[(0,[z0,z1,z2,z3,z844,z5]),(0,[z0,z845,z2,z3,z9,z5]),(0,[z0,z2,z846,z3,z9,z5]),(0,[z847,z1,z2,z3,z9,z5]),(0,[z0,z50,z2,z3,z141,z5]),(0,[z0,z98,z2,z3,z9,z253]),(0,[z0,z1,z3,z107,z62,z5])],[(1,[z1,z2,z3,z9,z848]),(0,[z0,z291,z2,z3,z394,z5]),(0,[z0,z1,z321,z3,z4,z5]),(0,[z849,z0,z1,z2,z3,z5])],[(0,[z0,z407,z2,z3,z107,z5]),(0,[z0,z850,z2,z3,z9,z5]),(0,[z11,z0,z1,z3,z4,z90]),(0,[z571,z1,z2,z3,z107,z5])],[(0,[z0,z37,z603,z3,z9,z5]),(0,[z0,z37,z2,z3,z55,z5]),(0,[z0,z1,z2,z3,z851,z5]),(0,[z121,z2,z14,z3,z9,z5]),(0,[z0,z37,z2,z61,z57,z5]),(0,[z0,z1,z2,z3,z202,z5])],[(0,[z0,z1,z2,z72,z202,z5]),(0,[z0,z1,z2,z3,z852,z5]),(0,[z0,z50,z2,z3,z149,z5]),(0,[z0,z853,z2,z3,z9,z5])],[(0,[z0,z1,z2,z247,z381,z5]),(0,[z0,z2,z3,z9,z854,z5]),(0,[z0,z1,z2,z3,z855,z5]),(0,[z0,z1,z3,z4,z5,z556]),(0,[z357,z221,z2,z3,z9,z5])],[(0,[z0,z37,z2,z3,z9,z5]),(0,[z0,z479,z14,z3,z9,z5]),(0,[z0,z440,z2,z3,z287,z5]),(0,[z0,z1,z2,z3,z856,z5]),(0,[z0,z715,z2,z3,z9,z5])],[(0,[z0,z2,z14,z3,z9,z63]),(0,[z112,z2,z14,z72,z9,z5]),(0,[z0,z857,z2,z3,z9,z5]),(0,[z0,z440,z2,z451,z9,z5]),(0,[z638,z0,z14,z3,z9,z5]),(0,[z0,z66,z2,z3,z9,z274]),(0,[z858,z1,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z859,z5])],[(0,[z0,z1,z2,z860,z9,z5]),(0,[z0,z1,z2,z3,z861,z5]),(0,[z0,z2,z14,z178,z9,z5]),(0,[z0,z14,z3,z43,z4,z5]),(0,[z0,z1,z481,z3,z107,z5])],[(0,[z0,z432,z2,z3,z107,z5]),(0,[z0,z1,z2,z451,z107,z5])],[(0,[z74,z0,z1,z2,z625,z5]),(0,[z0,z2,z14,z257,z9,z5]),(0,[z0,z1,z227,z3,z4,z5])],[(0,[z739,z12,z2,z3,z9,z5]),(0,[z0,z1,z2,z862,z9,z5]),(0,[z0,z1,z2,z3,z731,z5]),(0,[z0,z1,z2,z178,z28,z5]),(0,[z0,z14,z3,z9,z545,z5]),(0,[z863,z1,z2,z3,z9,z5]),(0,[z0,z357,z1,z3,z9,z90])],[(0,[z0,z1,z2,z269,z9,z5]),(0,[z0,z864,z2,z3,z9,z5])],[]],
   [[(0,[z82,z1,z525,z3,z9,z156]),(0,[z174,z0,z2,z309,z3,z5]),(0,[z0,z2,z3,z4,z5,z455])],[(0,[z0,z1,z3,z865,z9,z5]),(0,[z866,z1,z2,z3,z9,z5])],[(0,[z867,z0,z1,z2,z3,z5]),(0,[z0,z868,z2,z3,z9,z5]),(0,[z312,z1,z2,z3,z107,z5]),(0,[z120,z1,z2,z3,z9,z39]),(0,[z230,z157,z2,z3,z9,z5])],[(0,[z0,z1,z2,z3,z869,z5])],[(0,[z0,z285,z2,z3,z381,z5]),(0,[z1,z2,z3,z9,z33,z63]),(0,[z0,z474,z2,z436,z9,z5])],[(0,[z0,z1,z2,z3,z870,z5]),(0,[z0,z2,z3,z9,z5,z455]),(0,[z871,z0,z2,z3,z9,z5])],[(0,[z657,z12,z2,z3,z9,z5]),(0,[z0,z1,z2,z353,z107,z5]),(0,[z248,z0,z1,z3,z9,z90]),(0,[z0,z1,z2,z3,z872,z5])],[(0,[z0,z1,z2,z3,z873,z5]),(0,[z0,z874,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z875,z5])],[],[(0,[z0,z739,z2,z3,z9,z5]),(0,[z876,z1,z2,z3,z9,z5])],[(0,[z0,z1,z2,z464,z107,z5])],[(0,[z0,z1,z2,z3,z877,z5]),(0,[z100,z1,z2,z15,z249,z5]),(0,[z0,z2,z878,z3,z9,z5]),(0,[z606,z1,z2,z3,z628,z5])],[(0,[z0,z2,z3,z107,z5,z222]),(0,[z0,z113,z1,z2,z3,z550])],[(0,[z0,z1,z2,z3,z381,z371]),(0,[z0,z1,z588,z3,z107,z5]),(0,[z32,z1,z2,z3,z9,z33]),(0,[z0,z98,z2,z3,z394,z5])],[(0,[z739,z1,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z879,z5]),(0,[z0,z1,z880,z3,z9,z5]),(0,[z160,z37,z2,z3,z9,z5]),(0,[z0,z881,z2,z3,z9,z5])],[(0,[z0,z1,z2,z3,z882,z5]),(0,[z0,z2,z14,z3,z402,z5]),(0,[z0,z883,z2,z3,z9,z5]),(0,[z44,z0,z2,z523,z9,z5]),(0,[z1,z2,z3,z9,z5,z848]),(0,[z0,z1,z2,z3,z107,z253]),(0,[z0,z1,z2,z3,z884,z5]),(0,[z0,z1,z885,z3,z9,z5])]],
   [[(0,[z1,z2,z3,z9,z848,z156]),(0,[z58,z0,z14,z3,z4,z5]),(0,[z571,z2,z14,z3,z9,z5]),(0,[z0,z1,z2,z886,z9,z5])],[(0,[z0,z106,z2,z3,z300,z5]),(0,[z887,z0,z2,z3,z9,z5]),(0,[z0,z50,z2,z3,z632,z5]),(0,[z77,z0,z1,z2,z9,z78])],[(0,[z585,z1,z2,z72,z9,z5])],[(0,[z171,z0,z14,z3,z107,z5]),(0,[z0,z2,z14,z9,z888,z5])],[(0,[z0,z1,z2,z3,z889,z5]),(0,[z0,z1,z2,z890,z9,z5]),(0,[z671,z1,z2,z3,z17,z5]),(0,[z891,z0,z2,z3,z9,z5]),(0,[z0,z37,z209,z3,z9,z5]),(0,[z0,z1,z2,z3,z892,z5]),(0,[z0,z221,z2,z257,z9,z5])],[(0,[z0,z1,z2,z3,z191,z5]),(0,[z0,z893,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z894,z5]),(0,[z0,z1,z2,z3,z895,z5]),(0,[z0,z22,z2,z3,z107,z5])],[(0,[z1,z2,z3,z72,z191,z5]),(0,[z44,z318,z0,z2,z49,z5]),(0,[z0,z1,z2,z896,z9,z5]),(0,[z58,z0,z10,z3,z4,z5]),(0,[z0,z1,z2,z520,z524,z5]),(0,[z897,z1,z2,z3,z9,z5])],[(0,[z0,z106,z2,z3,z55,z5]),(0,[z0,z2,z14,z451,z9,z5]),(0,[z0,z2,z14,z3,z372,z5]),(0,[z898,z0,z2,z3,z9,z5]),(0,[z0,z899,z2,z3,z9,z5]),(0,[z0,z1,z2,z179,z107,z199]),(0,[z357,z1,z2,z110,z9,z5])],[(0,[z19,z1,z56,z3,z9,z5]),(0,[z1,z26,z3,z9,z33,z90]),(0,[z82,z1,z2,z3,z9,z156])],[(0,[z0,z83,z14,z3,z9,z5]),(0,[z900,z1,z2,z3,z9,z5])],[(0,[z0,z901,z2,z3,z9,z5]),(0,[z0,z2,z3,z9,z902,z5])],[(0,[z82,z1,z2,z3,z287,z156]),(0,[z0,z1,z2,z3,z903,z5]),(0,[z174,z0,z314,z2,z3,z5])],[(0,[z0,z1,z2,z3,z904,z5]),(0,[z0,z1,z2,z3,z466,z253]),(0,[z0,z1,z2,z3,z905,z5])],[(0,[z0,z1,z2,z3,z349,z5]),(0,[z0,z1,z2,z3,z906,z5]),(0,[z0,z65,z2,z3,z17,z5]),(0,[z0,z907,z2,z3,z9,z5]),(0,[z0,z98,z2,z3,z9,z5]),(0,[z0,z1,z2,z257,z40,z5])],[(0,[z0,z908,z2,z3,z9,z5])],[(0,[z0,z1,z2,z436,z9,z5]),(0,[z0,z474,z2,z3,z107,z5]),(0,[z82,z1,z2,z3,z9,z848]),(0,[z0,z2,z14,z909,z9,z5]),(0,[z174,z0,z2,z3,z545,z5])]],
   [[(0,[z0,z1,z2,z910,z9,z5]),(0,[z0,z1,z2,z911,z9,z5]),(0,[z0,z440,z525,z3,z9,z5]),(0,[z0,z2,z14,z9,z912,z5]),(0,[z571,z1,z2,z3,z913,z5])],[(0,[z0,z37,z2,z3,z381,z5])],[(0,[z0,z2,z14,z353,z9,z5]),(0,[z0,z1,z525,z3,z107,z5]),(0,[z0,z1,z2,z3,z734,z5]),(0,[z914,z1,z2,z3,z9,z5]),(0,[z0,z915,z2,z3,z9,z5])],[(0,[z0,z14,z3,z4,z5,z90]),(0,[z34,z0,z2,z49,z9,z5]),(0,[z0,z37,z27,z3,z9,z92]),(0,[z0,z1,z2,z520,z57,z5])],[(0,[z0,z2,z3,z9,z5,z916])],[(0,[z0,z1,z2,z3,z917,z5]),(0,[z7,z0,z1,z43,z9,z5])],[(0,[z0,z2,z14,z464,z9,z5]),(0,[z0,z1,z2,z918,z9,z5]),(0,[z919,z1,z2,z3,z9,z5]),(0,[z0,z2,z3,z9,z803,z5])],[(0,[z0,z1,z2,z3,z9,z371]),(0,[z0,z920,z2,z3,z9,z5]),(0,[z921,z1,z2,z3,z9,z5])],[(0,[z0,z1,z2,z922,z9,z5]),(0,[z1,z2,z436,z72,z9,z5]),(0,[z0,z1,z2,z3,z279,z73]),(0,[z0,z37,z14,z3,z9,z5]),(0,[z0,z215,z2,z3,z535,z5]),(0,[z0,z1,z2,z3,z824,z5])],[(0,[z171,z0,z14,z3,z237,z5]),(0,[z0,z2,z923,z3,z9,z5])],[(0,[z0,z2,z325,z3,z104,z5]),(0,[z0,z1,z527,z3,z107,z5]),(0,[z0,z2,z292,z3,z535,z5])],[(0,[z1,z2,z269,z9,z33,z5]),(0,[z192,z1,z2,z72,z9,z5]),(0,[z0,z2,z14,z3,z9,z253]),(0,[z0,z1,z2,z3,z924,z5]),(0,[z318,z0,z1,z2,z3,z5]),(0,[z8,z1,z2,z3,z9,z39])],[(0,[z0,z1,z2,z247,z4,z5]),(0,[z0,z1,z2,z3,z925,z5]),(0,[z0,z1,z2,z3,z926,z5]),(0,[z379,z0,z14,z3,z9,z5])],[(0,[z0,z1,z2,z110,z9,z92])],[(0,[z0,z1,z927,z3,z9,z5]),(0,[z21,z0,z2,z3,z297,z6])],[(0,[z0,z1,z3,z9,z5,z928]),(0,[z0,z1,z2,z3,z929,z5]),(0,[z0,z1,z930,z3,z9,z5]),(0,[z0,z221,z2,z3,z372,z5])]],
   [[(0,[z0,z1,z2,z3,z9,z931]),(0,[z0,z2,z429,z3,z70,z5])],[(0,[z0,z932,z2,z3,z9,z5]),(0,[z0,z37,z83,z3,z9,z5]),(0,[z121,z1,z2,z933,z9,z5])],[(0,[z74,z0,z37,z2,z75,z5]),(0,[z898,z0,z2,z3,z4,z5]),(0,[z420,z0,z1,z3,z4,z5]),(0,[z840,z1,z2,z3,z107,z5])],[],[(0,[z0,z1,z2,z3,z9,z934])],[(0,[z160,z1,z2,z436,z9,z5]),(0,[z935,z1,z2,z3,z9,z5]),(0,[z0,z2,z3,z188,z455,z73])],[(0,[z0,z936,z2,z3,z9,z5])],[(0,[z0,z1,z56,z3,z9,z63]),(0,[z0,z937,z2,z3,z9,z5])],[(0,[z0,z440,z2,z3,z9,z5]),(0,[z213,z0,z2,z3,z9,z304]),(0,[z938,z0,z1,z2,z3,z5])],[(0,[z0,z285,z2,z3,z4,z5]),(0,[z0,z939,z2,z3,z9,z5]),(0,[z0,z2,z194,z3,z9,z68]),(0,[z940,z1,z2,z3,z9,z5]),(0,[z74,z416,z1,z2,z75,z5]),(0,[z0,z1,z2,z3,z941,z5])],[(0,[z0,z1,z2,z3,z107,z5]),(0,[z0,z942,z2,z3,z9,z5]),(0,[z460,z1,z2,z3,z18,z5]),(0,[z150,z0,z2,z3,z105,z5])],[(0,[z106,z739,z2,z3,z9,z5])],[(0,[z1,z2,z3,z9,z33,z244]),(0,[z82,z1,z2,z3,z9,z272]),(0,[z0,z2,z943,z3,z9,z5]),(0,[z0,z1,z2,z3,z944,z5])],[(0,[z0,z354,z2,z3,z381,z5]),(0,[z0,z2,z429,z3,z9,z5])],[(0,[z7,z0,z291,z43,z9,z5]),(0,[z0,z2,z3,z9,z5,z945])],[(0,[z1,z2,z3,z17,z712,z5]),(0,[z32,z1,z83,z3,z9,z5]),(0,[z44,z0,z2,z49,z9,z5]),(0,[z0,z1,z2,z9,z729,z5])]],
   [[(0,[z0,z1,z2,z946,z9,z5]),(0,[z0,z1,z2,z3,z947,z5]),(0,[z401,z1,z2,z3,z18,z5]),(0,[z100,z432,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z948,z5]),(0,[z0,z2,z14,z3,z329,z5]),(0,[z7,z0,z1,z43,z4,z5])],[(0,[z0,z653,z14,z3,z9,z5]),(0,[z357,z1,z2,z3,z9,z90])],[(0,[z607,z12,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z4,z371]),(0,[z0,z2,z949,z3,z9,z5]),(0,[z595,z0,z2,z3,z9,z5]),(0,[z0,z950,z2,z3,z107,z5]),(0,[z0,z1,z2,z3,z9,z729])],[(0,[z0,z37,z14,z3,z4,z5]),(0,[z357,z1,z2,z3,z40,z5])],[(0,[z0,z1,z951,z3,z9,z5]),(0,[z0,z1,z952,z3,z9,z5]),(0,[z0,z1,z2,z3,z953,z5]),(0,[z0,z1,z2,z3,z9,z954]),(0,[z0,z164,z51,z3,z107,z5]),(0,[z0,z955,z2,z3,z9,z5])],[(0,[z0,z1,z3,z9,z92,z774]),(0,[z0,z956,z2,z3,z9,z5])],[(0,[z0,z2,z957,z3,z9,z5]),(0,[z0,z2,z14,z3,z394,z5]),(0,[z0,z291,z2,z3,z9,z5]),(0,[z0,z215,z2,z3,z53,z5])],[(0,[z0,z1,z2,z958,z9,z5]),(0,[z0,z1,z2,z3,z9,z848]),(0,[z0,z959,z2,z3,z9,z5]),(0,[z0,z960,z2,z3,z9,z5])],[(0,[z0,z2,z3,z9,z5,z961]),(0,[z796,z37,z2,z3,z9,z5]),(0,[z0,z2,z292,z3,z53,z5])],[(0,[z0,z37,z2,z247,z9,z5]),(0,[z1,z2,z962,z3,z9,z5]),(0,[z0,z1,z2,z3,z963,z5]),(0,[z0,z2,z14,z3,z70,z5])],[(0,[z0,z2,z14,z3,z249,z5]),(0,[z0,z1,z964,z3,z9,z5]),(0,[z0,z1,z2,z286,z4,z5]),(0,[z0,z1,z2,z3,z188,z154])],[(0,[z0,z965,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z9,z966]),(0,[z0,z50,z2,z3,z395,z5]),(0,[z230,z1,z2,z3,z4,z5]),(0,[z967,z1,z2,z3,z9,z5])],[(0,[z0,z1,z2,z3,z968,z5]),(0,[z0,z14,z3,z9,z62,z5]),(0,[z0,z2,z14,z3,z361,z5]),(0,[z969,z1,z2,z3,z9,z5]),(0,[z0,z970,z2,z3,z9,z5])],[(0,[z1,z26,z83,z3,z9,z5]),(0,[z0,z2,z14,z3,z300,z5]),(0,[z0,z971,z2,z3,z9,z5]),(0,[z7,z0,z1,z865,z9,z5]),(0,[z0,z1,z2,z972,z9,z5]),(0,[z77,z0,z1,z2,z78,z4]),(0,[z235,z0,z2,z3,z168,z5])],[(0,[z0,z1,z2,z3,z973,z5])],[(0,[z100,z1,z2,z464,z9,z5]),(0,[z2,z14,z3,z9,z5,z214]),(0,[z0,z1,z2,z110,z372,z5]),(0,[z160,z853,z2,z3,z9,z5]),(0,[z974,z0,z2,z3,z9,z5])]],
   [[(0,[z0,z1,z2,z3,z975,z5]),(0,[z0,z976,z2,z3,z9,z5]),(0,[z64,z474,z2,z3,z17,z5]),(0,[z468,z2,z14,z3,z9,z5]),(0,[z0,z113,z37,z2,z3,z35]),(0,[z160,z1,z2,z3,z107,z5]),(0,[z121,z977,z2,z3,z9,z5])],[(0,[z82,z1,z83,z3,z9,z156]),(0,[z0,z684,z14,z3,z9,z5])],[(0,[z0,z1,z2,z3,z978,z5]),(0,[z0,z1,z2,z3,z979,z5]),(0,[z0,z2,z980,z3,z9,z5])],[(0,[z1,z2,z15,z981,z9,z5]),(0,[z145,z1,z2,z3,z18,z5]),(0,[z982,z0,z2,z3,z9,z5]),(0,[z0,z2,z14,z61,z57,z5]),(0,[z0,z1,z2,z983,z9,z5]),(0,[z984,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z985,z9,z5]),(0,[z11,z230,z1,z3,z9,z90])],[(0,[z572,z1,z2,z72,z9,z5]),(0,[z0,z986,z2,z3,z9,z5]),(0,[z0,z1,z2,z987,z9,z5]),(0,[z0,z988,z2,z3,z9,z5]),(0,[z21,z0,z2,z3,z300,z6]),(0,[z989,z1,z2,z3,z9,z5])],[(0,[z0,z1,z2,z3,z990,z5]),(0,[z174,z0,z2,z3,z512,z5]),(0,[z0,z37,z3,z107,z4,z5])],[(0,[z0,z2,z3,z9,z5,z991]),(0,[z0,z37,z2,z3,z4,z5])],[(0,[z0,z354,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z9,z774])],[(0,[z0,z37,z2,z3,z184,z5]),(0,[z992,z1,z2,z3,z9,z5]),(0,[z0,z2,z429,z3,z4,z5]),(0,[z0,z1,z2,z3,z993,z5]),(0,[z0,z1,z2,z3,z994,z5])],[(0,[z1,z26,z3,z9,z5,z245]),(0,[z0,z2,z14,z3,z287,z5]),(0,[z0,z1,z2,z3,z995,z5])],[(0,[z100,z1,z2,z15,z9,z5]),(0,[z0,z1,z2,z3,z996,z5]),(0,[z74,z0,z1,z2,z824,z5])],[(0,[z0,z997,z2,z3,z9,z5]),(0,[z100,z1,z2,z981,z9,z5]),(0,[z0,z1,z2,z3,z998,z5]),(0,[z0,z2,z3,z4,z5,z222])],[(0,[z0,z285,z2,z269,z9,z5]),(0,[z0,z1,z2,z269,z4,z5]),(0,[z0,z1,z2,z999,z9,z5]),(0,[z1000,z1,z2,z3,z9,z5]),(0,[z1001,z1,z2,z3,z9,z5])],[(0,[z0,z432,z2,z3,z28,z5]),(0,[z0,z1,z2,z451,z28,z5]),(0,[z21,z0,z2,z3,z9,z6]),(0,[z120,z1,z2,z3,z9,z253])],[],[(0,[z0,z2,z1002,z3,z9,z5]),(0,[z0,z38,z14,z3,z9,z5]),(0,[z0,z1,z2,z865,z9,z5]),(0,[z0,z1003,z2,z3,z9,z5])]],
   [[(0,[z0,z1004,z2,z3,z9,z5]),(0,[z0,z1005,z2,z3,z9,z5]),(0,[z0,z2,z3,z9,z5,z222]),(0,[z0,z1,z568,z3,z4,z5])],[(0,[z0,z1,z2,z3,z1006,z5]),(0,[z312,z2,z14,z3,z9,z5]),(0,[z826,z37,z2,z3,z9,z5]),(0,[z0,z291,z2,z3,z4,z5])],[(0,[z0,z2,z1007,z3,z9,z5]),(0,[z77,z468,z1,z2,z9,z78])],[(0,[z416,z1,z2,z3,z9,z5]),(0,[z171,z0,z820,z3,z9,z5]),(0,[z0,z1,z2,z3,z1008,z5])],[(0,[z100,z115,z2,z15,z9,z5]),(0,[z100,z474,z2,z3,z9,z5]),(0,[z0,z79,z14,z3,z9,z5])],[(0,[z0,z1,z27,z3,z107,z92]),(0,[z643,z0,z1,z3,z9,z90])],[(0,[z0,z37,z2,z3,z384,z5]),(0,[z0,z1,z2,z3,z1009,z5]),(0,[z36,z0,z2,z3,z415,z5])],[(0,[z0,z1,z2,z3,z1010,z5]),(0,[z0,z37,z2,z286,z9,z5]),(0,[z571,z1011,z2,z3,z9,z5])],[(0,[z230,z37,z2,z3,z9,z5]),(0,[z1012,z1,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z188,z73])],[(0,[z0,z1,z2,z3,z1013,z5]),(0,[z312,z1,z2,z3,z1014,z5]),(0,[z0,z1,z2,z3,z1015,z5])],[(0,[z0,z2,z1016,z3,z9,z5]),(0,[z0,z2,z14,z3,z297,z5])],[(0,[z32,z1,z2,z3,z4,z33]),(0,[z0,z1,z2,z91,z9,z199])],[(0,[z0,z1,z2,z3,z1017,z5]),(0,[z0,z1018,z2,z3,z9,z5]),(0,[z0,z1,z2,z1019,z9,z5])],[(0,[z0,z1020,z2,z3,z9,z5])],[(0,[z0,z1,z2,z247,z349,z5]),(0,[z0,z221,z2,z3,z9,z5]),(0,[z1021,z1,z2,z3,z9,z5]),(0,[z1022,z1,z2,z3,z9,z5])],[(0,[z0,z285,z2,z247,z9,z5]),(0,[z0,z67,z2,z3,z9,z274])]],
   [[(0,[z0,z37,z2,z3,z242,z5]),(0,[z0,z37,z2,z3,z202,z5]),(0,[z0,z37,z491,z3,z9,z5]),(0,[z0,z2,z503,z3,z175,z5]),(0,[z0,z1,z296,z3,z4,z5]),(0,[z0,z50,z2,z3,z88,z5])],[(0,[z0,z440,z83,z3,z9,z5])],[(0,[z0,z1,z3,z250,z4,z5]),(0,[z0,z1,z2,z3,z1023,z5]),(0,[z0,z1,z2,z890,z4,z5])],[(0,[z1,z56,z3,z9,z5,z63]),(0,[z0,z1,z83,z3,z107,z5])],[(0,[z0,z37,z382,z3,z9,z5]),(0,[z312,z1,z2,z3,z1024,z5]),(0,[z0,z1,z2,z1025,z3,z5]),(0,[z0,z10,z2,z3,z107,z5])],[(0,[z94,z1,z56,z3,z381,z5]),(0,[z100,z1,z2,z15,z4,z5]),(0,[z0,z1,z2,z3,z1026,z5])],[(0,[z94,z0,z14,z3,z4,z5]),(0,[z121,z1,z56,z3,z9,z5]),(0,[z530,z1,z2,z72,z9,z5]),(0,[z218,z2,z14,z3,z18,z5]),(0,[z82,z1,z2,z3,z4,z156]),(0,[z723,z2,z14,z3,z9,z5]),(0,[z0,z2,z14,z179,z9,z199])],[(0,[z0,z37,z393,z3,z9,z5]),(0,[z0,z1,z1027,z3,z9,z5]),(0,[z474,z2,z3,z72,z9,z5]),(0,[z0,z1,z820,z3,z9,z5]),(0,[z0,z2,z1028,z3,z9,z5]),(0,[z1001,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z247,z9,z371]),(0,[z0,z1,z2,z3,z1029,z5]),(0,[z120,z1,z2,z3,z394,z5]),(0,[z1030,z1,z2,z3,z9,z5])],[(0,[z0,z37,z2,z269,z9,z5]),(0,[z0,z1,z83,z3,z9,z156]),(0,[z0,z1,z2,z3,z1031,z5])],[(0,[z0,z14,z3,z9,z5,z220])],[(0,[z0,z285,z2,z3,z349,z5]),(0,[z0,z2,z1032,z3,z9,z5]),(0,[z0,z1,z2,z3,z1033,z5]),(0,[z0,z98,z2,z3,z4,z5]),(0,[z540,z0,z1,z3,z4,z5])],[(0,[z121,z1,z2,z3,z9,z63]),(0,[z1,z2,z3,z712,z18,z5]),(0,[z0,z1,z2,z3,z1034,z5]),(0,[z0,z1035,z2,z3,z9,z5])],[(0,[z0,z1,z2,z436,z4,z5])],[(0,[z0,z1036,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z1037,z5]),(0,[z416,z1,z2,z3,z4,z5])],[(0,[z0,z2,z14,z3,z381,z5]),(0,[z0,z1038,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z1039,z5]),(0,[z0,z69,z429,z16,z9,z5]),(0,[z77,z0,z1,z2,z9,z45]),(0,[z121,z1,z2,z3,z1040,z5]),(0,[z1041,z1,z2,z3,z9,z5])]],
   [[(0,[z0,z51,z14,z3,z107,z5]),(0,[z1042,z1,z2,z3,z9,z5])],[(0,[z0,z1,z204,z3,z107,z5]),(1,[z0,z2,z3,z734,z5]),(0,[z174,z0,z2,z3,z415,z5]),(0,[z0,z1,z865,z43,z9,z5]),(0,[z0,z1,z2,z3,z1043,z73])],[(0,[z100,z1,z2,z3,z287,z5])],[(0,[z0,z1,z2,z3,z1044,z5]),(0,[z0,z1045,z2,z3,z9,z5])],[(0,[z0,z1,z525,z3,z28,z5]),(0,[z1046,z1,z2,z3,z9,z5]),(0,[z786,z0,z2,z3,z107,z5]),(0,[z357,z1,z2,z3,z372,z5])],[(0,[z0,z285,z2,z3,z9,z371]),(0,[z0,z2,z14,z3,z1047,z5]),(0,[z1,z2,z3,z9,z5,z741])],[(0,[z1048,z1,z2,z3,z9,z5]),(0,[z8,z1,z2,z3,z9,z253])],[(0,[z153,z0,z1,z43,z9,z5]),(0,[z0,z115,z2,z3,z107,z5])],[(0,[z108,z1,z2,z3,z9,z156]),(0,[z32,z37,z2,z3,z9,z33]),(0,[z0,z1,z3,z9,z774,z90])],[(0,[z0,z1,z2,z3,z1049,z5]),(0,[z0,z1,z2,z3,z1050,z5])],[(0,[z42,z115,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z1051,z5]),(0,[z0,z1,z2,z3,z466,z5])],[(0,[z0,z1,z2,z3,z1052,z5]),(0,[z0,z1053,z83,z3,z9,z5]),(0,[z171,z0,z14,z3,z243,z5])],[(0,[z0,z1,z2,z3,z1054,z5]),(0,[z580,z0,z2,z3,z9,z453]),(0,[z0,z2,z1055,z3,z9,z5])],[(0,[z0,z65,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z1056,z5]),(0,[z0,z1,z2,z3,z1057,z5]),(0,[z0,z37,z296,z3,z9,z5])],[(0,[z0,z1,z2,z3,z1058,z5]),(0,[z432,z2,z3,z72,z9,z5]),(0,[z0,z1,z2,z3,z1059,z5]),(0,[z174,z0,z2,z3,z650,z5]),(0,[z0,z1,z2,z110,z9,z5])],[(0,[z94,z1,z56,z3,z9,z5]),(0,[z0,z1060,z2,z3,z9,z5]),(0,[z0,z1061,z2,z3,z9,z5]),(0,[z44,z312,z2,z49,z9,z5]),(0,[z0,z1062,z1,z2,z3,z5]),(0,[z804,z1,z2,z3,z107,z5]),(0,[z0,z1,z2,z179,z9,z729])]],
   [[(0,[z0,z1,z2,z1063,z9,z5]),(0,[z0,z37,z2,z3,z191,z5]),(0,[z1,z2,z3,z107,z5,z214]),(0,[z187,z0,z1,z2,z505,z5]),(0,[z0,z2,z1064,z3,z9,z5])],[(0,[z0,z1,z2,z1065,z9,z5]),(0,[z0,z1,z2,z3,z9,z1066]),(0,[z58,z0,z1,z3,z4,z5]),(0,[z1067,z1,z2,z3,z9,z5]),(0,[z571,z1068,z2,z3,z9,z5])],[(0,[z1069,z0,z2,z3,z9,z5]),(0,[z37,z2,z3,z9,z5,z214]),(0,[z0,z157,z2,z3,z107,z5]),(0,[z0,z1,z2,z933,z9,z5])],[(0,[z82,z37,z2,z3,z9,z156]),(0,[z0,z1,z2,z3,z237,z5]),(0,[z1070,z1,z2,z3,z9,z5])],[(0,[z564,z1,z2,z72,z9,z5]),(0,[z0,z2,z1071,z3,z9,z5]),(0,[z64,z1,z2,z3,z402,z5]),(0,[z174,z0,z2,z3,z203,z5]),(0,[z0,z164,z2,z3,z9,z5]),(0,[z0,z1072,z2,z3,z9,z5]),(0,[z0,z1,z3,z4,z128,z5])],[(0,[z1,z2,z56,z3,z9,z63]),(0,[z0,z1053,z2,z3,z9,z5]),(0,[z0,z1,z2,z1073,z9,z5])],[(0,[z0,z2,z14,z3,z55,z5]),(0,[z0,z1,z2,z3,z1074,z5]),(0,[z0,z440,z2,z3,z4,z5]),(0,[z127,z0,z2,z3,z105,z5]),(0,[z0,z37,z2,z3,z903,z5]),(0,[z0,z1,z2,z3,z1075,z5]),(0,[z0,z1,z2,z1076,z3,z5]),(0,[z0,z2,z3,z4,z5,z1077]),(0,[z11,z0,z1,z3,z107,z90])],[(0,[z0,z1,z2,z3,z1078,z5]),(0,[z0,z14,z3,z290,z9,z5]),(0,[z174,z0,z2,z3,z175,z5]),(0,[z0,z1,z3,z107,z807,z5])],[(0,[z0,z285,z2,z3,z107,z5]),(0,[z0,z37,z2,z3,z349,z5]),(0,[z0,z1,z2,z3,z1079,z5]),(0,[z0,z1080,z2,z3,z9,z5]),(0,[z571,z1,z2,z178,z9,z5]),(0,[z0,z69,z14,z16,z9,z5]),(0,[z119,z2,z3,z104,z9,z5]),(0,[z0,z1,z2,z3,z1081,z5]),(0,[z0,z1,z2,z3,z807,z5])],[(0,[z0,z2,z14,z3,z9,z5]),(0,[z0,z1,z2,z3,z1082,z5])],[(0,[z0,z37,z2,z436,z9,z5]),(0,[z0,z1,z2,z4,z1083,z5])],[(0,[z0,z1,z2,z1084,z9,z5]),(0,[z0,z1,z2,z1085,z9,z5]),(0,[z0,z37,z639,z3,z9,z5]),(0,[z0,z1,z2,z3,z1086,z5]),(0,[z0,z22,z69,z16,z9,z5]),(0,[z0,z2,z3,z9,z5,z1077])],[(0,[z0,z1,z2,z3,z1087,z5]),(0,[z0,z1,z2,z3,z1088,z5]),(0,[z0,z1,z2,z3,z28,z5]),(0,[z0,z1,z2,z3,z1089,z5]),(0,[z1090,z1,z2,z3,z9,z5]),(0,[z450,z1,z2,z3,z219,z5])],[(0,[z1091,z0,z2,z3,z9,z5]),(0,[z44,z0,z2,z49,z4,z5]),(0,[z1092,z1,z2,z3,z9,z5])],[(0,[z0,z1,z1093,z3,z9,z5]),(0,[z0,z1,z2,z269,z349,z5]),(0,[z0,z1,z2,z178,z287,z5]),(0,[z0,z1,z2,z3,z1094,z5]),(0,[z0,z1,z2,z3,z535,z5]),(0,[z0,z1,z2,z1095,z9,z5])],[(0,[z0,z1,z1096,z3,z9,z5]),(0,[z0,z1,z2,z3,z1097,z5]),(0,[z0,z432,z2,z178,z9,z5]),(0,[z0,z1,z2,z3,z1098,z5]),(0,[z0,z1,z2,z3,z35,z30]),(0,[z0,z1,z151,z16,z9,z5]),(0,[z0,z1,z2,z9,z1083,z5])]],
   [[(0,[z0,z1,z2,z3,z9,z1099]),(0,[z0,z2,z1100,z3,z9,z5]),(0,[z595,z0,z2,z3,z4,z5]),(0,[z0,z1101,z2,z3,z9,z5])],[(0,[z228,z1,z26,z3,z4,z5]),(0,[z919,z37,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z1014,z5]),(0,[z174,z0,z2,z3,z586,z5]),(0,[z8,z1,z2,z3,z394,z5]),(0,[z0,z1,z2,z257,z372,z5])],[(0,[z0,z1,z2,z3,z767,z5]),(0,[z0,z37,z2,z3,z9,z371]),(0,[z0,z1102,z2,z3,z9,z5]),(0,[z77,z0,z2,z14,z9,z78]),(0,[z0,z2,z3,z9,z5,z1103])],[(0,[z0,z1104,z2,z3,z9,z5]),(0,[z11,z0,z37,z3,z9,z90]),(0,[z826,z1,z2,z3,z107,z5])],[(0,[z0,z1,z2,z3,z1105,z5]),(0,[z0,z1,z2,z3,z394,z39])],[(0,[z44,z318,z0,z2,z3,z5]),(0,[z357,z1,z2,z3,z9,z92])],[(0,[z553,z12,z2,z3,z9,z5]),(0,[z42,z106,z2,z353,z9,z5]),(0,[z0,z1106,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z1107,z5]),(0,[z0,z1,z2,z3,z484,z5]),(0,[z0,z1,z2,z3,z1108,z5]),(0,[z1109,z1,z2,z3,z9,z5]),(0,[z0,z2,z3,z9,z5,z1110])],[(0,[z228,z1,z2,z269,z9,z5])],[(0,[z0,z354,z2,z247,z9,z5]),(0,[z0,z1,z2,z269,z9,z371]),(0,[z0,z1,z2,z3,z1111,z5])],[(0,[z0,z1,z2,z286,z107,z5]),(0,[z0,z1,z2,z3,z913,z5]),(0,[z0,z2,z3,z9,z1112,z5])],[(0,[z42,z106,z2,z464,z9,z5]),(0,[z0,z1,z2,z1113,z9,z5]),(0,[z1114,z0,z2,z3,z9,z5]),(0,[z305,z1,z2,z3,z301,z5]),(0,[z230,z1,z2,z3,z107,z5])],[(0,[z0,z2,z429,z3,z384,z5])],[(0,[z0,z37,z172,z3,z329,z5]),(0,[z0,z1,z2,z3,z1024,z5]),(0,[z0,z2,z3,z9,z68,z754]),(0,[z357,z1,z2,z257,z9,z5]),(0,[z0,z2,z1115,z3,z9,z5])],[(0,[z0,z407,z2,z3,z402,z5]),(0,[z1116,z1,z2,z3,z9,z5]),(0,[z0,z1011,z2,z3,z9,z5])],[(0,[z24,z276,z2,z3,z9,z5]),(0,[z0,z486,z2,z3,z104,z5]),(0,[z64,z1,z2,z3,z17,z5]),(0,[z21,z0,z2,z3,z9,z304])],[(0,[z1,z2,z981,z72,z9,z5]),(0,[z160,z2,z14,z3,z9,z5]),(0,[z0,z1,z2,z824,z75,z5])]],
   [[(0,[z0,z2,z1117,z3,z9,z5]),(0,[z160,z1,z2,z3,z18,z5])],[(0,[z0,z1118,z2,z3,z9,z5]),(0,[z1119,z0,z1,z2,z3,z5])],[(0,[z119,z1,z2,z3,z9,z5]),(0,[z0,z2,z3,z9,z1120,z5]),(0,[z0,z1,z2,z3,z243,z5]),(0,[z1121,z0,z1,z2,z9,z5]),(0,[z0,z1,z2,z1122,z9,z5]),(0,[z0,z2,z708,z49,z9,z5]),(0,[z0,z1,z491,z3,z107,z5]),(0,[z0,z1,z2,z3,z9,z1123]),(0,[z0,z986,z2,z3,z4,z5])],[(0,[z0,z50,z2,z3,z144,z5]),(0,[z0,z1,z69,z16,z70,z5]),(0,[z0,z1,z2,z327,z3,z35])],[(0,[z0,z1124,z2,z3,z9,z5]),(0,[z1,z56,z3,z9,z156,z90]),(0,[z0,z1,z2,z3,z9,z1125]),(0,[z0,z1,z1126,z3,z9,z5]),(0,[z0,z2,z14,z815,z9,z5]),(0,[z0,z2,z14,z3,z4,z5]),(0,[z0,z1,z2,z3,z9,z39])],[(0,[z0,z1,z2,z3,z1127,z5]),(0,[z0,z354,z2,z3,z4,z5]),(0,[z0,z37,z2,z3,z107,z5]),(0,[z0,z1,z2,z3,z1128,z5])],[(0,[z0,z2,z1129,z3,z9,z5]),(0,[z0,z2,z14,z3,z184,z5]),(0,[z0,z1,z2,z3,z1130,z5]),(0,[z0,z1,z2,z3,z1131,z5])],[],[(0,[z112,z1,z2,z981,z9,z5]),(0,[z100,z1,z83,z3,z9,z5]),(0,[z1132,z1,z2,z3,z9,z5]),(0,[z0,z1133,z2,z3,z9,z5]),(0,[z1134,z0,z2,z3,z9,z5])],[(0,[z0,z2,z259,z3,z9,z5]),(0,[z37,z1135,z2,z3,z9,z5]),(0,[z0,z1,z2,z86,z575,z5])],[(0,[z1136,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z40,z5])],[(0,[z0,z1,z2,z269,z107,z5]),(0,[z21,z0,z2,z3,z4,z6]),(0,[z0,z2,z3,z107,z5,z1137])],[(0,[z0,z1,z2,z3,z1138,z5]),(0,[z318,z0,z2,z14,z3,z5]),(0,[z0,z1,z2,z3,z53,z5]),(0,[z0,z2,z3,z9,z5,z1139])],[(0,[z1140,z1,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z1141,z5])],[(0,[z0,z67,z2,z3,z9,z68]),(0,[z0,z1,z2,z3,z1142,z5])],[(0,[z36,z0,z2,z3,z175,z5]),(0,[z0,z1,z2,z3,z9,z754]),(0,[z0,z1,z2,z179,z168,z199])]],
   [[(0,[z0,z1,z2,z3,z1143,z5]),(0,[z0,z37,z568,z3,z9,z5]),(0,[z795,z0,z1,z2,z3,z5]),(0,[z0,z1,z69,z16,z9,z5])],[(0,[z0,z1144,z2,z3,z9,z5])],[(1,[z1,z2,z981,z9,z5]),(0,[z0,z1145,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z1146,z5]),(0,[z0,z1,z2,z3,z87,z294]),(0,[z74,z160,z1,z2,z75,z5])],[(0,[z1,z2,z178,z72,z9,z5]),(0,[z235,z0,z2,z15,z9,z5])],[(0,[z0,z2,z14,z3,z384,z5]),(0,[z0,z2,z3,z9,z1147,z5])],[(0,[z235,z0,z2,z179,z9,z199])],[(0,[z0,z1,z525,z178,z9,z5]),(0,[z230,z2,z14,z3,z9,z5]),(0,[z569,z0,z1,z2,z75,z5]),(0,[z595,z0,z2,z3,z35,z5])],[(0,[z0,z1,z2,z3,z1148,z5]),(0,[z0,z1,z2,z3,z349,z371]),(0,[z0,z1149,z2,z3,z9,z5])],[(0,[z0,z1,z2,z3,z1150,z5])],[(0,[z42,z739,z2,z3,z9,z5]),(0,[z1,z2,z198,z72,z9,z5]),(0,[z0,z50,z2,z3,z104,z5]),(0,[z0,z1,z27,z3,z535,z92])],[(0,[z0,z1,z2,z3,z1151,z5]),(0,[z323,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z107,z631,z5]),(0,[z32,z1,z2,z3,z107,z33])],[(0,[z0,z1,z2,z3,z1152,z5]),(0,[z120,z1,z2,z3,z9,z5]),(0,[z0,z2,z1153,z3,z9,z5]),(0,[z44,z0,z2,z361,z49,z5]),(0,[z1154,z1,z2,z3,z9,z5]),(0,[z1,z2,z3,z4,z5,z1155])],[(0,[z463,z2,z96,z3,z9,z5]),(0,[z829,z1,z2,z3,z9,z5]),(0,[z0,z1,z2,z708,z9,z5]),(0,[z0,z221,z2,z3,z4,z5])],[(0,[z0,z1,z2,z1156,z9,z5]),(0,[z0,z2,z1157,z3,z9,z5]),(0,[z1158,z1,z2,z3,z9,z5]),(0,[z1121,z0,z1,z2,z4,z5]),(0,[z0,z1,z2,z886,z107,z5]),(0,[z0,z1159,z2,z3,z9,z5])],[(0,[z0,z1,z2,z247,z107,z5]),(0,[z0,z2,z14,z3,z242,z5]),(0,[z0,z1,z2,z15,z402,z5]),(0,[z0,z69,z14,z3,z4,z5]),(0,[z0,z1160,z2,z3,z9,z5]),(0,[z0,z2,z14,z3,z202,z5]),(0,[z77,z0,z1,z2,z107,z78])],[(0,[z571,z1,z2,z15,z9,z5]),(0,[z0,z1161,z2,z3,z9,z5]),(0,[z569,z0,z1,z2,z5,z283]),(0,[z0,z157,z2,z3,z40,z5]),(0,[z0,z2,z1162,z3,z9,z5])]],
   [[(0,[z0,z1,z2,z738,z9,z5]),(0,[z32,z1,z2,z3,z9,z848]),(0,[z0,z2,z3,z734,z175,z5]),(0,[z1,z2,z3,z9,z5,z1155])],[(0,[z0,z1,z2,z1163,z9,z5]),(0,[z0,z2,z3,z104,z5,z705])],[],[(0,[z0,z1,z2,z3,z9,z1164]),(0,[z82,z440,z2,z3,z9,z156]),(0,[z11,z0,z1,z3,z40,z90])],[(0,[z0,z1,z1165,z3,z9,z5])],[(0,[z0,z1,z2,z3,z1166,z5]),(0,[z100,z37,z2,z15,z9,z5]),(0,[z0,z1,z83,z3,z28,z5]),(0,[z82,z1,z2,z3,z107,z156]),(1,[z0,z1,z2,z824,z5])],[(1,[z0,z820,z3,z9,z5]),(0,[z0,z1167,z2,z3,z9,z5])],[(0,[z42,z106,z2,z3,z55,z5]),(0,[z0,z2,z14,z269,z9,z5]),(0,[z1,z2,z83,z3,z9,z156]),(0,[z0,z37,z2,z999,z9,z5]),(0,[z0,z1,z2,z3,z188,z516]),(0,[z0,z1068,z2,z3,z9,z5]),(0,[z0,z113,z1,z2,z3,z1043])],[(0,[z0,z354,z2,z269,z9,z5]),(0,[z0,z2,z3,z9,z5,z1168]),(0,[z0,z1,z2,z234,z9,z199])],[(0,[z0,z1,z397,z16,z9,z5]),(0,[z0,z67,z2,z3,z4,z68]),(0,[z0,z1,z2,z9,z824,z5])],[(0,[z42,z106,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z1169,z5]),(0,[z0,z1,z2,z3,z1170,z5])],[(0,[z0,z2,z3,z9,z1171,z5])],[(0,[z0,z1,z2,z3,z1172,z5]),(0,[z0,z1,z2,z3,z1173,z5]),(0,[z0,z1,z2,z436,z107,z5]),(0,[z0,z1,z2,z16,z9,z39]),(0,[z0,z2,z3,z9,z5,z1174])],[(0,[z112,z1,z2,z72,z9,z5]),(0,[z312,z1,z2,z15,z9,z5])],[(0,[z0,z1,z2,z178,z9,z5]),(0,[z74,z0,z1,z2,z559,z5]),(0,[z416,z37,z2,z3,z9,z5]),(0,[z0,z2,z3,z9,z5,z1175]),(0,[z230,z221,z2,z3,z9,z5])],[(0,[z1,z2,z3,z4,z5,z214]),(0,[z914,z1,z2,z3,z107,z5])]],
   [[(0,[z94,z1,z56,z247,z9,z5]),(0,[z174,z0,z2,z3,z734,z5]),(0,[z0,z1,z2,z3,z1040,z5])],[(0,[z0,z59,z2,z3,z9,z5])],[(0,[z0,z2,z1176,z3,z9,z5]),(0,[z0,z1,z2,z1177,z9,z5]),(0,[z7,z0,z1,z43,z107,z5]),(0,[z0,z1,z2,z3,z168,z5])],[(0,[z64,z1,z2,z3,z301,z5]),(0,[z0,z37,z2,z3,z188,z73]),(0,[z0,z1,z2,z3,z1178,z5]),(0,[z0,z1,z27,z3,z9,z774])],[(0,[z0,z1,z2,z3,z107,z371]),(0,[z1,z2,z3,z9,z5,z214]),(0,[z0,z1,z2,z3,z1179,z5]),(0,[z921,z1,z2,z3,z107,z5]),(0,[z121,z1,z2,z3,z1180,z5])],[(0,[z0,z37,z14,z3,z107,z5]),(0,[z121,z1,z2,z1181,z9,z5])],[(0,[z0,z1182,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z9,z1183]),(0,[z120,z1,z2,z3,z4,z5]),(0,[z0,z157,z2,z110,z9,z5])],[(0,[z0,z1,z27,z3,z53,z92])],[(0,[z0,z407,z2,z3,z249,z5]),(0,[z235,z0,z2,z3,z9,z5])],[(0,[z0,z1,z1184,z3,z9,z5]),(0,[z77,z571,z1,z2,z9,z78])],[(0,[z0,z2,z14,z247,z9,z5]),(0,[z218,z1,z2,z3,z712,z5]),(0,[z11,z0,z1,z110,z9,z90])],[(0,[z0,z1,z2,z1185,z9,z5]),(0,[z0,z1,z629,z3,z4,z5]),(0,[z0,z1,z2,z3,z9,z1186]),(0,[z0,z65,z2,z3,z4,z5]),(0,[z0,z1,z3,z9,z807,z5])],[(0,[z0,z1,z2,z3,z1187,z5]),(0,[z0,z1,z2,z3,z1188,z5]),(0,[z0,z1,z2,z110,z4,z5])],[(0,[z94,z285,z56,z3,z9,z5]),(0,[z94,z1,z56,z3,z4,z5]),(0,[z0,z1,z2,z3,z1043,z5])],[],[(0,[z0,z1,z1189,z3,z9,z5]),(0,[z0,z1,z2,z3,z1190,z5]),(0,[z94,z1,z1191,z3,z9,z5]),(0,[z7,z0,z37,z43,z9,z5]),(0,[z7,z0,z1,z43,z466,z5]),(0,[z1192,z0,z2,z3,z9,z5]),(1,[z0,z1,z2,z9,z729])]],
   [[],[(0,[z0,z1,z97,z3,z4,z5]),(0,[z0,z1193,z2,z3,z9,z5]),(0,[z0,z1194,z2,z3,z9,z5])],[(0,[z0,z1,z2,z3,z1195,z5]),(0,[z0,z1,z2,z3,z1196,z5]),(0,[z0,z37,z820,z3,z9,z5]),(0,[z0,z164,z2,z3,z4,z5])],[],[(0,[z0,z1,z1191,z3,z9,z5]),(0,[z8,z1,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z1197,z5]),(0,[z0,z977,z2,z3,z9,z5])],[(0,[z0,z1,z2,z1198,z9,z5]),(0,[z0,z440,z2,z3,z107,z5]),(0,[z1199,z0,z2,z3,z9,z5])],[(0,[z0,z1,z2,z3,z1200,z5]),(0,[z0,z2,z14,z3,z349,z5])],[(0,[z0,z354,z2,z3,z349,z5]),(0,[z0,z1,z2,z3,z1201,z5])],[(0,[z82,z1,z2,z3,z9,z63]),(0,[z0,z1,z2,z3,z1202,z5]),(0,[z0,z1,z38,z3,z107,z5]),(0,[z0,z1,z2,z3,z1203,z5])],[(0,[z0,z12,z2,z464,z9,z5]),(0,[z0,z1,z2,z3,z1204,z5])],[(0,[z0,z2,z14,z3,z819,z5]),(0,[z0,z1,z3,z545,z4,z5]),(0,[z0,z2,z429,z3,z107,z5])],[(0,[z0,z1,z2,z3,z1205,z5]),(0,[z0,z2,z3,z9,z68,z682]),(0,[z0,z1,z2,z3,z372,z5]),(0,[z0,z1,z2,z61,z130,z5]),(0,[z0,z2,z3,z202,z5,z222])],[(0,[z0,z65,z2,z286,z9,z5]),(0,[z44,z0,z2,z49,z107,z5])],[(0,[z0,z1206,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z1207,z5])],[(0,[z0,z1,z27,z3,z9,z362]),(0,[z0,z432,z2,z3,z287,z5]),(0,[z0,z1,z2,z451,z287,z5]),(0,[z1208,z1,z2,z3,z9,z5]),(0,[z21,z0,z2,z3,z9,z754]),(0,[z230,z1,z2,z110,z9,z5])],[(0,[z668,z1,z56,z3,z9,z5]),(0,[z0,z432,z2,z451,z9,z5]),(0,[z0,z1,z2,z3,z394,z253]),(0,[z595,z0,z2,z3,z107,z5])]],
   [[(0,[z0,z1,z2,z3,z1209,z5]),(0,[z0,z2,z14,z3,z9,z371]),(0,[z1121,z0,z2,z14,z9,z5]),(0,[z580,z0,z2,z3,z9,z6]),(0,[z0,z1,z2,z3,z1210,z5]),(0,[z0,z1,z2,z293,z9,z199]),(0,[z0,z1,z2,z3,z1211,z5]),(0,[z1212,z1,z2,z3,z9,z5])],[(0,[z0,z354,z2,z3,z9,z371]),(0,[z0,z1,z2,z3,z1213,z5]),(0,[z228,z37,z26,z3,z9,z5]),(0,[z0,z1214,z2,z3,z9,z5]),(0,[z0,z2,z3,z107,z197,z5])],[(0,[z152,z1,z2,z3,z17,z5]),(0,[z0,z2,z14,z3,z825,z5]),(0,[z0,z1,z2,z9,z78,z729])],[(0,[z0,z1,z2,z3,z1215,z5]),(0,[z0,z1,z2,z909,z9,z5]),(0,[z0,z291,z2,z3,z107,z5])],[(0,[z0,z1,z2,z3,z9,z1216]),(0,[z0,z1217,z2,z3,z9,z5]),(0,[z0,z1218,z2,z3,z9,z5])],[(0,[z0,z37,z172,z3,z9,z5]),(0,[z0,z37,z2,z3,z466,z5]),(0,[z571,z1,z2,z3,z1219,z5])],[(0,[z0,z1,z2,z353,z9,z5]),(0,[z0,z1,z2,z3,z381,z63]),(0,[z357,z1,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z1220,z5]),(0,[z0,z1,z2,z3,z1221,z5])],[(0,[z0,z215,z2,z3,z9,z5])],[(0,[z0,z37,z629,z3,z9,z5]),(0,[z0,z2,z14,z286,z9,z5]),(0,[z0,z1,z2,z3,z1222,z5]),(0,[z0,z1223,z2,z3,z9,z5])],[(0,[z252,z1,z2,z72,z9,z5]),(0,[z1224,z0,z2,z3,z9,z5]),(0,[z0,z2,z292,z3,z9,z5]),(0,[z0,z37,z2,z110,z9,z5]),(0,[z58,z0,z59,z3,z4,z5]),(0,[z0,z205,z2,z3,z141,z5]),(0,[z0,z1,z2,z3,z188,z623]),(0,[z0,z1225,z2,z3,z9,z5])],[(0,[z0,z1,z2,z3,z9,z1226]),(0,[z94,z37,z56,z3,z9,z5]),(0,[z0,z1,z2,z1227,z9,z5])],[(0,[z0,z1,z2,z1228,z9,z5]),(0,[z0,z1229,z2,z3,z9,z5]),(0,[z0,z1,z2,z1230,z9,z5]),(0,[z379,z0,z1,z3,z4,z5]),(0,[z1231,z1,z2,z3,z9,z5])],[(0,[z500,z1,z2,z15,z9,z5])],[(0,[z24,z12,z2,z3,z9,z5]),(0,[z0,z1232,z2,z3,z9,z5]),(0,[z0,z205,z2,z3,z149,z5]),(0,[z0,z1,z3,z107,z632,z5]),(0,[z0,z1,z2,z1233,z9,z5])],[(0,[z0,z37,z2,z3,z237,z5]),(0,[z0,z2,z14,z3,z844,z5]),(0,[z1234,z1,z2,z3,z9,z5])],[(0,[z8,z1,z2,z3,z4,z5])]],
   [[(0,[z94,z1,z56,z269,z9,z5]),(0,[z119,z1,z2,z3,z4,z5]),(0,[z0,z291,z2,z3,z466,z5])],[(0,[z150,z0,z2,z3,z175,z5])],[(0,[z0,z1235,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z4,z39]),(0,[z0,z1,z600,z3,z107,z5]),(0,[z0,z2,z3,z9,z5,z1236])],[(0,[z0,z525,z14,z3,z9,z5]),(0,[z799,z0,z2,z3,z9,z5])],[(0,[z0,z354,z2,z3,z107,z5]),(0,[z0,z1,z2,z3,z9,z1237]),(0,[z0,z27,z14,z3,z9,z92]),(0,[z0,z2,z52,z3,z9,z5]),(0,[z0,z1,z2,z3,z1043,z9])],[(0,[z312,z1,z2,z464,z9,z5]),(0,[z11,z0,z14,z3,z9,z90]),(0,[z0,z2,z3,z9,z5,z754])],[(0,[z0,z1238,z2,z3,z9,z5]),(0,[z0,z1239,z2,z3,z9,z5])],[(0,[z0,z2,z259,z3,z4,z5]),(0,[z100,z1,z2,z15,z107,z5]),(0,[z0,z1,z83,z178,z9,z5]),(0,[z0,z37,z2,z3,z28,z5]),(0,[z0,z1,z2,z3,z9,z1240]),(0,[z1241,z1,z2,z3,z9,z5])],[(0,[z77,z0,z1,z2,z9,z567]),(0,[z0,z1,z2,z3,z1242,z5]),(0,[z0,z1,z2,z3,z1243,z5]),(0,[z74,z0,z1,z2,z505,z5])],[(0,[z0,z2,z259,z3,z184,z5]),(0,[z74,z0,z1,z2,z695,z5]),(0,[z0,z37,z2,z3,z535,z5]),(0,[z11,z1,z3,z9,z214,z90])],[(0,[z0,z1244,z2,z3,z9,z5]),(0,[z21,z0,z2,z3,z107,z6])],[(0,[z0,z1,z2,z3,z1245,z5]),(0,[z0,z1,z2,z425,z9,z199]),(0,[z0,z1,z2,z3,z1246,z5]),(0,[z0,z1,z2,z327,z3,z284]),(0,[z357,z157,z2,z3,z9,z5]),(0,[z74,z0,z2,z197,z75,z5])],[(0,[z121,z1,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z1247,z5]),(0,[z0,z1,z2,z3,z1248,z5]),(0,[z0,z1249,z2,z3,z9,z5]),(0,[z0,z67,z2,z3,z9,z754]),(0,[z8,z1,z2,z16,z9,z5]),(0,[z0,z1,z16,z865,z9,z5])],[(0,[z0,z1250,z2,z3,z9,z5]),(0,[z0,z1251,z2,z3,z9,z5]),(0,[z1252,z0,z1,z3,z9,z5]),(0,[z64,z1,z2,z286,z17,z5]),(0,[z0,z98,z2,z3,z107,z5]),(0,[z0,z2,z3,z9,z1253,z5])],[(0,[z0,z501,z2,z3,z9,z5]),(0,[z77,z0,z37,z2,z9,z78]),(1,[z0,z2,z3,z9,z754]),(0,[z0,z1,z69,z16,z4,z5])],[(0,[z0,z474,z2,z3,z9,z5])]],
   [[(0,[z0,z1,z2,z3,z9,z63]),(0,[z0,z1254,z2,z3,z9,z5]),(0,[z1255,z0,z2,z3,z9,z5]),(0,[z416,z1,z2,z3,z107,z5])],[(0,[z671,z106,z2,z3,z9,z5]),(0,[z0,z1256,z2,z3,z9,z5]),(0,[z0,z1,z2,z722,z9,z5]),(0,[z0,z37,z2,z3,z484,z5]),(0,[z0,z1,z2,z3,z1257,z5]),(0,[z0,z1,z2,z3,z1258,z5])],[(0,[z1259,z1,z2,z3,z9,z5])],[(0,[z160,z1,z2,z3,z17,z5]),(0,[z121,z1,z2,z3,z9,z33]),(0,[z0,z37,z2,z3,z1111,z5]),(0,[z1260,z1,z2,z3,z9,z5]),(0,[z0,z1,z2,z257,z9,z5])],[(0,[z0,z14,z3,z9,z631,z5]),(0,[z0,z2,z292,z3,z4,z5]),(1,[z0,z1,z2,z3,z1043])],[(0,[z0,z1,z525,z3,z287,z5]),(0,[z0,z1261,z2,z3,z9,z5]),(0,[z969,z2,z14,z3,z9,z5]),(0,[z0,z1,z433,z3,z4,z5]),(0,[z1262,z0,z2,z3,z9,z5])],[(0,[z0,z432,z525,z3,z9,z5]),(0,[z0,z1,z525,z451,z9,z5]),(0,[z11,z0,z157,z3,z9,z90])],[(0,[z0,z1263,z2,z3,z9,z5])],[(0,[z174,z416,z1,z2,z3,z5])],[(0,[z0,z1,z388,z3,z107,z5]),(0,[z64,z37,z2,z3,z17,z5]),(0,[z32,z2,z14,z3,z9,z33]),(0,[z763,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z1264,z5])],[(0,[z0,z113,z1,z2,z3,z360]),(0,[z0,z1265,z2,z3,z9,z5]),(0,[z0,z98,z2,z3,z466,z5]),(0,[z1,z2,z3,z9,z5,z1266]),(0,[z230,z1,z2,z3,z40,z5])],[(0,[z0,z1,z2,z3,z1267,z5]),(0,[z0,z1,z2,z1268,z9,z5]),(0,[z160,z1,z2,z15,z9,z5]),(0,[z0,z1,z2,z61,z89,z5]),(0,[z0,z1,z210,z3,z107,z5])],[(0,[z235,z0,z2,z72,z9,z5]),(0,[z0,z37,z424,z3,z9,z5]),(1,[z0,z1,z865,z9,z5])],[(0,[z0,z37,z2,z3,z243,z5]),(0,[z119,z37,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z1269,z5]),(0,[z0,z1,z51,z3,z107,z5]),(0,[z1270,z1,z2,z3,z9,z5]),(0,[z595,z0,z2,z3,z188,z73])],[(0,[z0,z1,z2,z3,z249,z5]),(0,[z318,z0,z2,z13,z3,z5]),(0,[z0,z1,z69,z16,z384,z5]),(0,[z0,z833,z2,z3,z9,z5]),(0,[z0,z1271,z2,z3,z9,z5])],[(0,[z174,z0,z2,z3,z578,z5]),(0,[z94,z1,z56,z3,z349,z5]),(0,[z0,z65,z2,z436,z9,z5]),(0,[z0,z37,z2,z3,z9,z39]),(0,[z0,z2,z3,z300,z68,z5]),(0,[z0,z2,z52,z3,z4,z5])]],
   [[(0,[z0,z1272,z2,z3,z9,z5])],[(0,[z0,z2,z14,z3,z191,z5]),(0,[z0,z2,z259,z3,z242,z5]),(0,[z1273,z1,z2,z3,z9,z5])],[(0,[z331,z0,z2,z3,z9,z5]),(0,[z709,z0,z2,z3,z9,z5]),(0,[z0,z215,z27,z3,z9,z92])],[(0,[z100,z2,z14,z15,z9,z5]),(0,[z0,z1,z2,z61,z824,z5])],[(0,[z312,z12,z2,z3,z9,z5]),(0,[z468,z1,z2,z3,z9,z5]),(0,[z82,z2,z14,z3,z9,z156])],[(0,[z0,z1274,z2,z3,z9,z5]),(0,[z0,z37,z2,z3,z40,z5])],[(0,[z0,z1,z2,z3,z402,z5]),(0,[z0,z1,z83,z3,z1207,z5]),(0,[z0,z1,z2,z3,z1275,z5])],[(0,[z0,z407,z2,z3,z9,z5]),(0,[z0,z1,z2,z1276,z9,z5]),(0,[z571,z1,z2,z3,z9,z5]),(0,[z0,z1,z2,z72,z402,z5]),(0,[z82,z1,z2,z3,z28,z156]),(0,[z0,z37,z2,z3,z53,z5]),(0,[z0,z2,z568,z3,z104,z5])],[(0,[z42,z106,z2,z3,z4,z5]),(0,[z571,z1,z2,z72,z9,z5]),(0,[z318,z0,z37,z2,z3,z5]),(0,[z0,z157,z2,z257,z9,z5])],[(0,[z94,z1,z56,z3,z9,z371]),(0,[z0,z1,z1277,z3,z9,z5]),(0,[z0,z2,z3,z9,z5,z1278])],[(0,[z42,z2,z96,z3,z9,z5]),(0,[z0,z1,z2,z1279,z9,z5]),(0,[z344,z0,z14,z3,z9,z5]),(0,[z0,z1,z2,z9,z888,z5])],[(0,[z44,z12,z2,z72,z9,z5]),(0,[z1,z2,z464,z72,z9,z5]),(0,[z0,z1,z2,z3,z4,z63]),(0,[z112,z1,z2,z72,z4,z5]),(0,[z0,z2,z14,z436,z9,z5]),(0,[z0,z14,z3,z9,z5,z683]),(0,[z0,z37,z69,z16,z9,z5]),(0,[z44,z0,z2,z615,z9,z5])],[(0,[z1,z1191,z56,z3,z9,z5]),(0,[z0,z1,z2,z436,z18,z5]),(0,[z0,z1,z2,z178,z4,z5]),(0,[z416,z2,z14,z3,z9,z5]),(0,[z0,z1,z2,z1280,z9,z5]),(0,[z11,z0,z1,z257,z9,z90])],[(0,[z0,z1,z26,z3,z9,z63]),(0,[z0,z1,z2,z3,z287,z5]),(0,[z0,z1,z2,z3,z1281,z5]),(0,[z0,z1,z2,z3,z1282,z5]),(0,[z1042,z1,z2,z3,z107,z5])],[(0,[z0,z432,z2,z3,z9,z5]),(0,[z0,z1,z2,z451,z9,z5]),(0,[z0,z1,z2,z257,z4,z5]),(0,[z0,z51,z52,z3,z107,z5])],[(0,[z0,z1,z2,z3,z1283,z5]),(0,[z1284,z0,z1,z2,z9,z5]),(0,[z416,z50,z1,z2,z3,z5]),(0,[z1285,z0,z2,z3,z9,z5]),(0,[z0,z59,z2,z3,z4,z5])]],
   [[(0,[z0,z115,z2,z3,z402,z5]),(0,[z0,z2,z3,z9,z5,z1286])],[(0,[z1,z83,z3,z72,z9,z5]),(0,[z0,z2,z14,z3,z188,z73]),(0,[z0,z1,z2,z1287,z9,z5])],[(0,[z0,z1,z2,z3,z765,z5]),(0,[z0,z1,z2,z4,z912,z5])],[(0,[z0,z1,z2,z3,z1288,z5]),(0,[z74,z331,z0,z2,z3,z5]),(0,[z0,z113,z1,z2,z3,z35])],[(0,[z0,z1,z2,z3,z1289,z5]),(0,[z0,z1,z635,z3,z9,z92]),(0,[z0,z1,z2,z3,z1290,z5])],[(0,[z0,z1,z2,z3,z1291,z5]),(0,[z312,z1,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z1292,z5])],[(0,[z0,z1,z2,z353,z55,z5]),(0,[z312,z1,z2,z72,z9,z5]),(0,[z273,z0,z2,z195,z9,z5]),(0,[z120,z37,z2,z3,z9,z5]),(0,[z235,z0,z2,z3,z4,z5])],[(0,[z0,z1,z2,z9,z912,z5])],[(0,[z1293,z1,z2,z3,z9,z5])],[(0,[z0,z1,z2,z1294,z9,z5])],[(0,[z0,z1,z2,z464,z55,z5]),(0,[z0,z65,z2,z3,z107,z5]),(0,[z174,z0,z2,z3,z645,z5]),(0,[z0,z1295,z2,z3,z9,z5])],[(0,[z0,z22,z2,z3,z70,z5]),(0,[z0,z1,z2,z110,z107,z5]),(0,[z0,z1,z2,z3,z1219,z5])],[(0,[z0,z1,z2,z1296,z9,z5]),(0,[z94,z1,z56,z3,z107,z5]),(0,[z160,z1,z2,z3,z402,z5]),(0,[z0,z1,z240,z3,z4,z5])],[(0,[z0,z1,z2,z464,z9,z5])],[(0,[z1,z1135,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z297,z5]),(0,[z58,z0,z1,z3,z807,z5])],[(0,[z1297,z1,z2,z3,z9,z5]),(0,[z0,z405,z2,z3,z144,z5]),(0,[z0,z1298,z2,z3,z9,z5]),(0,[z0,z1,z2,z167,z9,z199])]],
   [[(0,[z64,z1,z2,z436,z17,z5]),(0,[z230,z1,z2,z257,z9,z5])],[(0,[z0,z1299,z2,z3,z9,z5]),(0,[z120,z291,z2,z3,z9,z5]),(0,[z0,z164,z2,z3,z107,z5]),(0,[z0,z1,z2,z3,z1300,z5])],[(0,[z1,z2,z1191,z3,z9,z5]),(0,[z0,z407,z2,z3,z4,z5]),(0,[z0,z1,z626,z3,z4,z5]),(0,[z0,z1,z2,z3,z1301,z5]),(0,[z0,z1,z2,z3,z9,z253]),(0,[z0,z1,z2,z1073,z107,z5]),(0,[z0,z2,z3,z9,z5,z1137]),(0,[z0,z2,z1302,z3,z9,z5])],[(0,[z0,z157,z2,z3,z372,z5]),(0,[z0,z1,z2,z3,z1303,z5])],[(0,[z1304,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z1305,z9,z5]),(0,[z0,z1,z2,z3,z1306,z5])],[(0,[z0,z1,z2,z1307,z9,z5]),(0,[z0,z1308,z2,z3,z9,z5]),(0,[z121,z1,z83,z3,z9,z5])],[(0,[z171,z0,z14,z3,z9,z5]),(0,[z0,z2,z14,z3,z107,z5]),(0,[z0,z2,z3,z9,z68,z459])],[(0,[z0,z440,z2,z3,z28,z5]),(0,[z0,z2,z3,z4,z5,z1309]),(0,[z0,z1,z2,z1280,z4,z5]),(0,[z11,z0,z1,z3,z372,z90])],[(0,[z112,z37,z2,z72,z9,z5]),(0,[z0,z22,z2,z3,z9,z5])],[(0,[z0,z1,z2,z981,z9,z5]),(0,[z1,z2,z3,z981,z9,z5]),(0,[z0,z37,z2,z178,z9,z5]),(0,[z0,z1,z2,z1310,z9,z5]),(0,[z7,z0,z98,z43,z9,z5])],[(0,[z100,z1,z2,z3,z191,z5]),(0,[z218,z1,z2,z3,z18,z5]),(0,[z1311,z1,z2,z3,z9,z5]),(0,[z1312,z1,z2,z3,z9,z5]),(0,[z0,z1,z2,z179,z9,z199])],[(0,[z0,z1,z2,z3,z1313,z5]),(0,[z1314,z0,z2,z3,z9,z5]),(0,[z761,z1,z2,z3,z9,z5])],[(0,[z0,z1,z2,z3,z1315,z5]),(0,[z7,z0,z1,z43,z9,z39]),(0,[z0,z2,z3,z9,z5,z1309]),(0,[z468,z1,z2,z16,z9,z5]),(0,[z0,z1,z2,z3,z35,z563])],[(0,[z19,z0,z1,z3,z9,z90]),(0,[z0,z37,z2,z3,z168,z5])],[(0,[z0,z1,z2,z269,z9,z63]),(0,[z0,z1,z2,z3,z9,z1316]),(0,[z0,z1,z2,z1317,z9,z5]),(0,[z0,z1318,z2,z3,z9,z5])],[(0,[z0,z1,z2,z3,z1319,z5]),(0,[z0,z1,z2,z3,z1320,z5]),(0,[z1,z2,z3,z712,z9,z5]),(0,[z595,z0,z2,z3,z18,z5]),(0,[z0,z1,z2,z1321,z9,z5]),(0,[z44,z0,z2,z246,z9,z5])]],
   [[(0,[z0,z2,z813,z3,z9,z5]),(0,[z0,z37,z503,z3,z9,z5]),(0,[z0,z1,z2,z3,z1322,z5]),(0,[z0,z1,z2,z3,z1323,z5]),(0,[z160,z1295,z2,z3,z9,z5]),(0,[z235,z0,z2,z3,z202,z5])],[(0,[z0,z1,z2,z3,z1324,z5]),(0,[z0,z50,z2,z3,z181,z5]),(0,[z0,z1325,z2,z3,z9,z5]),(0,[z7,z0,z14,z43,z9,z5]),(0,[z174,z0,z2,z3,z542,z5])],[(0,[z0,z1,z2,z3,z1326,z5]),(0,[z0,z1,z2,z3,z1327,z5]),(0,[z0,z115,z2,z15,z9,z5]),(0,[z0,z1,z409,z3,z4,z5]),(0,[z174,z0,z2,z3,z347,z5])],[(0,[z0,z12,z2,z3,z300,z5]),(0,[z0,z1,z2,z3,z381,z5]),(0,[z0,z2,z1328,z3,z9,z5]),(0,[z0,z2,z820,z3,z9,z5]),(0,[z0,z2,z14,z3,z466,z5]),(0,[z0,z37,z172,z3,z4,z5])],[(0,[z0,z1,z2,z353,z4,z5]),(0,[z100,z1,z2,z436,z9,z5]),(0,[z118,z345,z2,z3,z9,z5]),(0,[z357,z1,z2,z3,z4,z5])],[(0,[z0,z1,z525,z3,z9,z5]),(0,[z0,z1,z2,z1329,z9,z5]),(0,[z0,z405,z2,z3,z104,z5]),(1,[z0,z1,z3,z807,z5]),(0,[z0,z215,z2,z3,z4,z5])],[(0,[z0,z1,z2,z1330,z9,z5]),(1,[z357,z1,z3,z9,z90])],[(0,[z228,z0,z14,z3,z4,z5]),(0,[z0,z1331,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z329,z5]),(0,[z0,z14,z3,z9,z632,z5]),(0,[z0,z14,z3,z167,z9,z5]),(0,[z0,z1332,z2,z3,z9,z5]),(1,[z0,z1,z3,z9,z774])],[(0,[z0,z1,z2,z464,z4,z5]),(0,[z1333,z1,z2,z3,z9,z5]),(0,[z0,z1,z1334,z3,z9,z5]),(0,[z0,z50,z2,z3,z734,z5]),(0,[z74,z0,z1,z2,z75,z5])],[(0,[z0,z12,z2,z3,z55,z5]),(0,[z94,z354,z56,z3,z9,z5]),(0,[z0,z1,z2,z3,z1047,z5])],[],[(0,[z24,z12,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z1335,z5]),(0,[z0,z1,z2,z3,z1336,z5]),(0,[z0,z67,z2,z3,z9,z596]),(0,[z0,z1337,z2,z3,z9,z5]),(0,[z8,z1,z2,z43,z9,z5]),(0,[z120,z98,z2,z3,z9,z5]),(0,[z0,z456,z1,z2,z3,z550]),(0,[z230,z1,z2,z3,z372,z5]),(0,[z598,z0,z1,z2,z9,z78])],[(0,[z0,z2,z14,z3,z237,z5])],[(0,[z258,z0,z2,z3,z9,z6]),(0,[z174,z0,z2,z3,z442,z5]),(0,[z0,z1,z2,z3,z394,z5]),(0,[z0,z1,z2,z3,z4,z253]),(0,[z1338,z1,z2,z3,z9,z5]),(0,[z0,z1,z2,z1339,z9,z5])],[(0,[z94,z1,z83,z3,z9,z5]),(0,[z0,z1,z2,z3,z1340,z5]),(0,[z1,z2,z3,z9,z33,z848]),(0,[z0,z1,z2,z43,z9,z39]),(0,[z0,z1341,z2,z3,z9,z5]),(0,[z0,z221,z2,z3,z107,z5])],[(0,[z0,z1,z2,z3,z1342,z5]),(0,[z8,z37,z2,z3,z9,z5]),(0,[z0,z37,z626,z3,z9,z5]),(0,[z119,z1,z2,z3,z107,z5])]],
   [[(0,[z0,z1,z2,z3,z9,z1343]),(0,[z0,z1,z2,z3,z832,z5]),(0,[z0,z1,z2,z3,z70,z5]),(0,[z0,z1,z2,z3,z35,z1043])],[(0,[z0,z1,z2,z247,z9,z63]),(0,[z0,z1,z2,z3,z1344,z5]),(0,[z171,z0,z14,z3,z4,z5]),(0,[z0,z1345,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z107,z39]),(0,[z74,z331,z0,z2,z75,z5]),(0,[z0,z1,z2,z3,z1346,z5])],[(1,[z739,z2,z3,z9,z5]),(0,[z42,z106,z2,z3,z191,z5]),(0,[z0,z1,z2,z3,z1347,z5])],[(0,[z1,z2,z56,z269,z9,z5]),(0,[z0,z1,z2,z3,z361,z5])],[(0,[z0,z1,z2,z3,z300,z5])],[(0,[z0,z2,z14,z3,z28,z5]),(0,[z840,z1,z2,z3,z9,z5]),(0,[z74,z0,z1,z2,z313,z5]),(0,[z0,z1,z2,z3,z9,z1348])],[(0,[z0,z142,z14,z3,z9,z5]),(0,[z0,z2,z259,z3,z107,z5]),(0,[z0,z1,z83,z3,z287,z5]),(0,[z0,z1349,z2,z3,z9,z5])],[(0,[z0,z432,z83,z3,z9,z5]),(0,[z0,z1,z83,z451,z9,z5]),(0,[z0,z2,z14,z3,z535,z5]),(0,[z11,z357,z1,z3,z9,z90])],[(0,[z0,z1,z2,z1350,z9,z5]),(0,[z1351,z0,z2,z3,z9,z5]),(0,[z11,z0,z1,z3,z9,z774])],[(0,[z82,z1,z2,z178,z9,z156]),(0,[z0,z1,z2,z3,z1352,z5]),(0,[z1208,z37,z2,z3,z9,z5])],[(0,[z0,z1,z2,z3,z55,z5]),(0,[z1353,z1,z2,z3,z9,z5]),(0,[z0,z1,z2,z1354,z9,z5]),(0,[z8,z291,z2,z3,z9,z5]),(0,[z0,z1,z69,z865,z9,z5]),(0,[z121,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z61,z57,z5]),(0,[z0,z1355,z2,z3,z9,z5])],[(0,[z102,z12,z2,z3,z9,z5]),(0,[z0,z115,z2,z3,z249,z5]),(0,[z0,z2,z1356,z3,z9,z5]),(0,[z0,z67,z2,z3,z107,z68])],[(0,[z0,z1,z2,z814,z9,z5]),(0,[z0,z501,z2,z3,z4,z5]),(0,[z121,z1,z26,z3,z9,z5])],[(0,[z0,z1,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z349,z63]),(0,[z177,z0,z1,z3,z9,z90]),(0,[z0,z474,z2,z3,z4,z5]),(0,[z0,z291,z2,z3,z9,z39]),(0,[z0,z1,z3,z637,z4,z5])],[(0,[z0,z285,z2,z3,z9,z63]),(0,[z0,z501,z2,z3,z184,z5]),(0,[z0,z1,z2,z3,z1357,z5])],[(0,[z0,z1358,z2,z3,z9,z5]),(0,[z0,z2,z14,z3,z484,z5]),(0,[z0,z1,z2,z3,z1359,z5])]],
   [[(0,[z0,z1,z525,z3,z4,z5]),(0,[z0,z2,z3,z9,z5,z1360]),(0,[z0,z1,z684,z3,z107,z5]),(0,[z0,z1,z2,z3,z1043,z188])],[(0,[z1,z2,z3,z72,z287,z5]),(0,[z357,z37,z2,z3,z9,z5])],[(0,[z201,z1,z2,z72,z9,z5]),(0,[z1361,z0,z2,z3,z9,z5])],[(0,[z0,z1,z2,z3,z1362,z5]),(0,[z0,z1,z1363,z3,z9,z5]),(0,[z0,z1,z2,z3,z1364,z5]),(0,[z102,z2,z48,z3,z9,z5]),(0,[z0,z37,z2,z3,z1222,z5]),(0,[z0,z1365,z2,z3,z9,z5])],[(0,[z0,z1,z2,z1366,z9,z5]),(0,[z605,z106,z2,z3,z9,z5]),(0,[z0,z27,z292,z3,z9,z92]),(0,[z0,z2,z1367,z3,z9,z5])],[(0,[z0,z1,z2,z3,z1368,z5]),(0,[z0,z37,z433,z3,z9,z5]),(0,[z0,z1263,z2,z3,z4,z5]),(0,[z0,z950,z2,z3,z9,z5])],[(0,[z406,z1,z2,z3,z18,z5])],[(0,[z0,z1,z2,z3,z9,z1369]),(0,[z64,z2,z14,z3,z17,z5]),(0,[z0,z1,z1370,z3,z9,z5]),(0,[z0,z2,z3,z9,z5,z1371]),(0,[z0,z1,z1372,z3,z9,z5])],[(0,[z64,z1,z2,z3,z712,z5]),(0,[z0,z204,z14,z3,z9,z5]),(0,[z1,z83,z3,z9,z5,z156]),(0,[z120,z1,z2,z3,z107,z5]),(0,[z0,z1,z2,z3,z1180,z5])],[(0,[z0,z1,z2,z3,z9,z1373]),(0,[z74,z1,z2,z72,z18,z5]),(0,[z549,z1,z2,z3,z17,z5]),(0,[z0,z1,z2,z1181,z9,z5])],[(0,[z36,z0,z2,z3,z347,z5])],[(0,[z0,z83,z878,z3,z9,z5]),(0,[z0,z1,z2,z1374,z9,z5]),(0,[z44,z0,z2,z195,z9,z5]),(0,[z1270,z1,z2,z3,z4,z5]),(0,[z0,z1,z51,z3,z807,z5]),(0,[z11,z121,z1,z3,z9,z90])],[(0,[z0,z1,z2,z3,z1375,z5]),(0,[z0,z1,z517,z3,z4,z5]),(0,[z0,z2,z1376,z3,z9,z5]),(0,[z0,z1,z2,z61,z340,z5]),(0,[z0,z1377,z2,z3,z9,z5]),(0,[z74,z0,z1,z2,z368,z5])],[(0,[z0,z1,z2,z15,z202,z5]),(0,[z0,z1,z2,z3,z1378,z5])],[(0,[z0,z1,z2,z1379,z9,z5]),(0,[z0,z37,z608,z3,z9,z5]),(0,[z1380,z1,z2,z3,z9,z5])],[(0,[z0,z1,z676,z3,z4,z5]),(0,[z0,z1381,z2,z3,z9,z5])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 497) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 497).take 509) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1006).take 434) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1440)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [497, 509, 434] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 146).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 146).take 144).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 290).take 152).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 442).take 70).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 512)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [146, 144, 152, 70] = true :=
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

end PEqualNP.Outside.L_meta_37779

theorem PEqualNP.Outside.L_meta_37779 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277071598 * 2 ^ 32 + 4209567944) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277071598 * 2 ^ 32 + 4209567944) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_37779.solve