import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_43964

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
  Nat.testBit (4276813032 * 2 ^ 32 + 4276807872) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x041881b01151bc80#64 ++ 0x20041881b01151bc#64 ++ 0x0cf883f033f3fcdb#64 ++ 0xdc0cf883f033f3fc#64 : BitVec 256),
   (0x11403450c4c4550a#64 ++ 0x4011403450c4c455#64 ++ 0x3340fc71cccc7fbf#64 ++ 0xbd3340fc71cccc7f#64 : BitVec 256),
   (0x42830a860b0a8a14#64 ++ 0x8042830a860b0a8a#64 ++ 0xc38f0f8e0f0f8f7f#64 ++ 0x7ec38f0f8e0f0f8f#64 : BitVec 256),
   (0xac0dd00b700f6027#64 ++ 0x01ac0dd00b700f60#64 ++ 0xfc0ff00ff00ff0f6#64 ++ 0xfbfc0ff00ff00ff0#64 : BitVec 256),
   (0xfbe0000daea00038#64 ++ 0x04fbe0000daea000#64 ++ 0xfff0000ffff000f1#64 ++ 0xf5fff0000ffff000#64 : BitVec 256),
   (0xfffeef60000000c0#64 ++ 0x02fffeef60000000#64 ++ 0xfffffff00000000f#64 ++ 0xf2fffffff0000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [0, 3]⟩, ⟨.or, [6, 5]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [9, 3]⟩, ⟨.or, [0, 10]⟩, ⟨.and, [9, 7]⟩, ⟨.or, [12, 4]⟩, ⟨.and, [11, 13]⟩, ⟨.or, [8, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0000344040044102 0x4000003440400441 0x00007c00000c0304 0x0000007c00000c03

def z1 : W := mkw 0x041881b01151bc80 0x20041881b01151bc 0x0cf883f033f3fcdb 0xdc0cf883f033f3fc

def z2 : W := mkw 0x11403450c4c4550a 0x4011403450c4c455 0x3340fc71cccc7fbf 0xbd3340fc71cccc7f

def z3 : W := mkw 0x42830a860b0a8a14 0x8042830a860b0a8a 0xc38f0f8e0f0f8f7f 0x7ec38f0f8e0f0f8f

def z4 : W := mkw 0xac0dd00b700f6027 0x01ac0dd00b700f60 0xfc0ff00ff00ff0f6 0xfbfc0ff00ff00ff0

def z5 : W := mkw 0xfbe0000daea00038 0x04fbe0000daea000 0xfff0000ffff000f1 0xf5fff0000ffff000

def z6 : W := mkw 0xfffeef60000000c0 0x02fffeef60000000 0xfffffff00000000f 0xf2fffffff0000000

def z7 : W := mkw 0x00010002000a0004 0x0000010002000a00 0xc00f000e000f8076 0x7ac00f000e000f80

def z8 : W := mkw 0x42820a840b008a10 0x8042820a840b008a 0x03800f800f000f09 0x0403800f800f000f

def z9 : W := mkw 0x040880901151bc00 0x20040880901151bc 0x0c08800033f3fcd2 0xdc0c08800033f3fc

def z10 : W := mkw 0xfbe03450c4c4550a 0x40fbe03450c4c455 0xfff0fc71cccc7fbf 0xfdfff0fc71cccc7f

def z11 : W := mkw 0x53c33ec6cf8ecb1e 0xc053c33ec6cf8ecb 0xf38f7f8fcf0f8f7f 0x7ff38f7f8fcf0f8f

def z12 : W := mkw 0x11403450c4c4550a 0x4011403450c4c455 0x3340fc71cccc73a4 0xa13340fc71cccc73

def z13 : W := mkw 0x041eef60000000c0 0x02041eef60000000 0x000ffff00000000e 0x02000ffff0000000

def z14 : W := mkw 0xbd4df45bf4cf752f 0x41bd4df45bf4cf75 0xff4ffc7ffccfffff 0xffff4ffc7ffccfff

def z15 : W := mkw 0x42820a0000000000 0x0042820a00000000 0xc38f0f800000000f 0x72c38f0f80000000

def z16 : W := mkw 0xffffefe60b0a8ad4 0x82ffffefe60b0a8a 0xfffffffe0f0f8f7f 0xfefffffffe0f0f8f

def z17 : W := mkw 0xbd7ce569a4a000e8 0x06bd7ce569a4a000 0x3c70f071f0f00080 0x813c70f071f0f000

def z18 : W := mkw 0x1140245084c01508 0x401140245084c015 0x03400c700cc00f09 0x0403400c700cc00f

def z19 : W := mkw 0x00030a82010a8a04 0x8000030a82010a8a 0xc00f0f8e000f8f7e 0x7ac00f0f8e000f8f

def z20 : W := mkw 0x0001109b715ffc27 0x210001109b715ffc 0x0000000ff3fffcf0 0x0d0000000ff3fffc

def z21 : W := mkw 0xac1dd1bb715ffca7 0x21ac1dd1bb715ffc 0xfcfff3fff3fffcff 0xfffcfff3fff3fffc

def z22 : W := mkw 0xfbe0345deee4553a 0x44fbe0345deee455 0xfff0fc7ffffc7fff 0xfdfff0fc7ffffc7f

def z23 : W := mkw 0x000000840b008a10 0x80000000840b008a 0x000000000f000f00 0x04000000000f000f

def z24 : W := mkw 0x0000008001008800 0x0000000080010088 0x0080038003000c09 0x040080038003000c

def z25 : W := mkw 0xfbe0000daea00038 0x04fbe0000daea000 0xf300000fcc000020 0x21f300000fcc0000

def z26 : W := mkw 0xfffeff70c4c455ca 0x42fffeff70c4c455 0xfffffff1c0c0708f 0xf3fffffff1c0c070

def z27 : W := mkw 0x42830a82010a8a04 0x8042830a82010a8a 0xc38f0f80000f8f0f 0x7ac38f0f80000f8f

def z28 : W := mkw 0x0000008001008800 0x0000000080010088 0x0088038003038c5b 0x5c0088038003038c

def z29 : W := mkw 0x469b8bb61b5bbe94 0xa0469b8bb61b5bbe 0xcfff8ffe3fffffff 0xfecfff8ffe3fffff

def z30 : W := mkw 0x0408800000000000 0x0004088000000000 0x0c08800000000002 0xd00c088000000000

def z31 : W := mkw 0xac0dd00b700f6027 0x01ac0dd00b700f60 0xfcfff00ff3fff0f7 0xfffcfff00ff3fff0

def z32 : W := mkw 0x00030a82010a8a04 0x8000030a82010a8a 0x000f038000038000 0x02000f0380000380

def z33 : W := mkw 0xfffeef6daea000f8 0x06fffeef6daea000 0xfffffffffff000ff 0xf7fffffffffff000

def z34 : W := mkw 0xfffeef6d2a2000f0 0x06fffeef6d2a2000 0xfffffffe3330004f 0xf2fffffffe333000

def z35 : W := mkw 0xfffeefe01111a8c0 0x22fffeefe01111a8 0xfffffff03333804f 0xf2fffffff0333380

def z36 : W := mkw 0xfbf66f60000000c0 0x02fbf66f60000000 0xf3f77ff00000000d 0x22f3f77ff0000000

def z37 : W := mkw 0xffedf45ffeef753f 0x45ffedf45ffeef75 0xfffffc7fffffffff 0xfffffffc7fffffff

def z38 : W := mkw 0x1140000084800008 0x0011400000848000 0x034000000cc00001 0x04034000000cc000

def z39 : W := mkw 0xeebeef60000000c0 0x02eebeef60000000 0xccbffff00000000e 0x42ccbffff0000000

def z40 : W := mkw 0x428000040a000010 0x00428000040a0000 0xc380000e0f000071 0x74c380000e0f0000

def z41 : W := mkw 0xfbe30a8fafaa8a3c 0x84fbe30a8fafaa8a 0xffff0f8fffff8fff 0xffffff0f8fffff8f

def z42 : W := mkw 0xbd6dd00bf4af602f 0x05bd6dd00bf4af60 0xfc7ff00ff0fff0f6 0xfbfc7ff00ff0fff0

def z43 : W := mkw 0x0000345040445502 0x4000003450404455 0x3000fc71c00c7fbe 0xb93000fc71c00c7f

def z44 : W := mkw 0xfbe66e4000000040 0x02fbe66e40000000 0xf3077c0000000004 0x22f3077c00000000

def z45 : W := mkw 0x0000100040044002 0x0000001000400440 0x3000f001c00c70b6 0xb93000f001c00c70

def z46 : W := mkw 0xfffecb20000000c0 0x02fffecb20000000 0xffff038000000001 0xf2ffff0380000000

def z47 : W := mkw 0x041b8bb2115bbe84 0xa0041b8bb2115bbe 0x0cff8ff033ffffdf 0xde0cff8ff033ffff

def z48 : W := mkw 0x0000244000000000 0x0000002440000000 0x0000fc700000000e 0x000000fc70000000

def z49 : W := mkw 0x1558b5f0d5d5fd8a 0x601558b5f0d5d5fd 0x3ff8fff1ffffffff 0xfd3ff8fff1ffffff

def z50 : W := mkw 0x0000000daea00038 0x040000000daea000 0x0cf0000ffff000f1 0xd50cf0000ffff000

def z51 : W := mkw 0xeaa0000000000000 0x00eaa00000000000 0xccb0000000000000 0x40ccb00000000000

def z52 : W := mkw 0xfbe1008fafaa8a3c 0x84fbe1008fafaa8a 0xfff0000fffff8ff1 0xfdfff0000fffff8f

def z53 : W := mkw 0xa800000920000020 0x00a8000009200000 0xfc00000ff00000f0 0xf1fc00000ff00000

def z54 : W := mkw 0xfff881bdbff1bcb8 0x24fff881bdbff1bc 0xfff883fffff3fcfb 0xfdfff883fffff3fc

def z55 : W := mkw 0x0418812000000080 0x0004188120000000 0x0cf883f00000000b 0xd00cf883f0000000

def z56 : W := mkw 0xac0dd00b700f6027 0x01ac0dd00b700f60 0xcc0ff00e300ff046 0x4acc0ff00e300ff0

def z57 : W := mkw 0xb9600009a4a00028 0x04b9600009a4a000 0x3c700001f0f00080 0x813c700001f0f000

def z58 : W := mkw 0xffecc00000000000 0x00ffecc000000000 0xfffff00000000007 0xf2fffff000000000

def z59 : W := mkw 0xfbe0000920000020 0x00fbe00009200000 0xfff0000ff00000f1 0xf1fff0000ff00000

def z60 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000800000007092 0x9800008000000070

def z61 : W := mkw 0x1558b570d4d5758a 0x601558b570d4d575 0x3c70f071f0f07080 0x813c70f071f0f070

def z62 : W := mkw 0xac1dd1ab711fe8a7 0x21ac1dd1ab711fe8 0xfcbff38ff33ff0f6 0xfbfcbff38ff33ff0

def z63 : W := mkw 0x0000345040445502 0x4000003450404455 0x0000fc70000c7f0e 0x080000fc70000c7f

def z64 : W := mkw 0x11403440c484410a 0x4011403440c48441 0x33007c01cc0c0324 0x2133007c01cc0c03

def z65 : W := mkw 0x428000040a000010 0x00428000040a0000 0xc080000e03000040 0x40c080000e030000

def z66 : W := mkw 0xb9600009a4a00028 0x04b9600009a4a000 0x3f700001fcf000b1 0xb53f700001fcf000

def z67 : W := mkw 0xac0dc00b300b2025 0x01ac0dc00b300b20 0xcc0f000e30038040 0x42cc0f000e300380

def z68 : W := mkw 0xac1cc12000000080 0x00ac1cc120000000 0xfcfff3f00000000f 0xf2fcfff3f0000000

def z69 : W := mkw 0xeebecbb01151bcc0 0x22eebecbb01151bc 0xccff83f033f3fcdb 0xdeccff83f033f3fc

def z70 : W := mkw 0x00001010c4c4550a 0x4000001010c4c455 0x00000001cccc7fb0 0x0d00000001cccc7f

def z71 : W := mkw 0x041881b01151bc80 0x20041881b01151bc 0x0cf083f033f07c89 0x840cf083f033f07c

def z72 : W := mkw 0xfffffffb715ffce7 0x23fffffffb715ffc 0xfffffffff3fffcff 0xfffffffffff3fffc

def z73 : W := mkw 0x57faaf60000000c0 0x0257faaf60000000 0x0ff88ff00000000b 0xd00ff88ff0000000

def z74 : W := mkw 0xfffeef60000000c0 0x02fffeef60000000 0xfffffff00c0c0f3f 0xfefffffff00c0c0f

def z75 : W := mkw 0xac1eef60000000c0 0x02ac1eef60000000 0xfc0ffff00000000e 0xf2fc0ffff0000000

def z76 : W := mkw 0x42830a860b0a8a14 0x8042830a860b0a8a 0xc30f0f8e0c0f8f2e 0x2ac30f0f8e0c0f8f

def z77 : W := mkw 0xfbe0000000000000 0x00fbe00000000000 0xf300000000000000 0x20f3000000000000

def z78 : W := mkw 0x1140000daea00038 0x041140000daea000 0x3340000ffff000f1 0xb53340000ffff000

def z79 : W := mkw 0x000100961b5bbe14 0xa0000100961b5bbe 0x0000000e3ffffff0 0x0c0000000e3fffff

def z80 : W := mkw 0x041dd1b2515ffc87 0x21041dd1b2515ffc 0x000ff3f0000ffc0e 0x0a000ff3f0000ffc

def z81 : W := mkw 0x53f22f60000000c0 0x0253f22f60000000 0x03f00ff000000009 0x0003f00ff0000000

def z82 : W := mkw 0x041881b01151bc80 0x20041881b01151bc 0x0ff88ff03fffffff 0xfc0ff88ff03fffff

def z83 : W := mkw 0x42833ed64b4edf16 0xc042833ed64b4edf 0xc38ffffe0f0fff7f 0x7ec38ffffe0f0fff

def z84 : W := mkw 0x428100860b0a8a14 0x80428100860b0a8a 0xc380000e0f0f8f71 0x7cc380000e0f0f8f

def z85 : W := mkw 0x041881a01111a880 0x20041881a01111a8 0x0008038000038000 0x0000080380000380

def z86 : W := mkw 0x0001008fafaa8a3c 0x840001008fafaa8a 0x0000000fffff8ff0 0x0d0000000fffff8f

def z87 : W := mkw 0xb960000daea00038 0x04b960000daea000 0x3c70000ffff000f0 0x853c70000ffff000

def z88 : W := mkw 0x53e0000000000000 0x0053e00000000000 0x03f0000000000001 0x0003f00000000000

def z89 : W := mkw 0x53c33ed6cfcedf1e 0xc053c33ed6cfcedf 0xf3cfffffcfcfffff 0xfff3cfffffcfcfff

def z90 : W := mkw 0xac0dc00b300b2025 0x01ac0dc00b300b20 0xfc0f000ff00380f0 0xf3fc0f000ff00380

def z91 : W := mkw 0x53f23f70c4c455ca 0x4253f23f70c4c455 0x33f0fff1cccc7fbf 0xbd33f0fff1cccc7f

def z92 : W := mkw 0xfbe0101deee4553a 0x44fbe0101deee455 0xfff0000ffffc7ff1 0xfdfff0000ffffc7f

def z93 : W := mkw 0x000000040a000010 0x00000000040a0000 0x0000000e0f000070 0x040000000e0f0000

def z94 : W := mkw 0x0010013000501480 0x2000100130005014 0x0070007000f00000 0x000070007000f000

def z95 : W := mkw 0x53e000048ea00018 0x0453e000048ea000 0x0ff000003ff000d1 0xd40ff000003ff000

def z96 : W := mkw 0x42830a860b0a8a14 0x8042830a860b0a8a 0xcfff0f8e3fff8fff 0xfecfff0f8e3fff8f

def z97 : W := mkw 0x469b8ba60b0a8a94 0x80469b8ba60b0a8a 0xcfff8ffe0f0f8f7f 0xfecfff8ffe0f0f8f

def z98 : W := mkw 0xac0cd00970056023 0x01ac0cd009700560 0x3c00f001f00c70b6 0xb93c00f001f00c70

def z99 : W := mkw 0x53c23ed4cfc4df1a 0xc053c23ed4cfc4df 0x33c0fff1cfcc7fbf 0xbd33c0fff1cfcc7f

def z100 : W := mkw 0xfbe30a0faeaa023c 0x84fbe30a0faeaa02 0xf3070c0fcc0c0324 0x23f3070c0fcc0c03

def z101 : W := mkw 0x000100060a0a0214 0x80000100060a0a02 0x0000000e0c0c0320 0x000000000e0c0c03

def z102 : W := mkw 0xa800000920000020 0x00a8000009200000 0xf000000fc0000020 0x21f000000fc00000

def z103 : W := mkw 0xfffeeff01151bcc0 0x22fffeeff01151bc 0xfffffff00003fc0f 0xfafffffff00003fc

def z104 : W := mkw 0xffffff6b700f60e7 0x03ffffff6b700f60 0xfffffffff00ff0ff 0xfbfffffffff00ff0

def z105 : W := mkw 0x001001a001108880 0x20001001a0011088 0x00b0038003300000 0x0000b00380033000

def z106 : W := mkw 0xfffeef60100120c0 0x02fffeef60100120 0xfffffff03003f0df 0xfafffffff03003f0

def z107 : W := mkw 0xfbe0000daea00038 0x04fbe0000daea000 0xfcf0000ff3f000c0 0xc1fcf0000ff3f000

def z108 : W := mkw 0xfffeef60000000c0 0x02fffeef60000000 0xfcfff3f000000000 0xc2fcfff3f0000000

def z109 : W := mkw 0x0000000000000000 0x0000000000000000 0x03000c000c0c0f3f 0x3c03000c000c0c0f

def z110 : W := mkw 0x00030a860b0a8a14 0x8000030a860b0a8a 0x000f0f8e0f0f8f7e 0x0e000f0f8e0f0f8f

def z111 : W := mkw 0xfffeefe40b008ad0 0x82fffeefe40b008a 0xfffffff00f000f0f 0xf6fffffff00f000f

def z112 : W := mkw 0xee8fda0b700f6027 0x01ee8fda0b700f60 0xff8fff8ff00ff0ff 0xfbff8fff8ff00ff0

def z113 : W := mkw 0xfffeef60000000c0 0x02fffeef60000000 0xffbf7f8000000004 0x62ffbf7f80000000

def z114 : W := mkw 0x040dc002100b2005 0x01040dc002100b20 0x000f000000038000 0x02000f0000000380

def z115 : W := mkw 0xeebfcba60b0a8ad4 0x82eebfcba60b0a8a 0xcfbf0f8e0f0f8f7f 0x7ecfbf0f8e0f0f8f

def z116 : W := mkw 0xa800000daea00038 0x04a800000daea000 0xfc00000ffff000f0 0xf5fc00000ffff000

def z117 : W := mkw 0x0000000daea00038 0x040000000daea000 0x0000000ffff000f0 0x050000000ffff000

def z118 : W := mkw 0xfbe0000000000000 0x00fbe00000000000 0xfff0000000000001 0xf0fff00000000000

def z119 : W := mkw 0x42820a840b008a10 0x8042820a840b008a 0x0080038003000000 0x0000800380030000

def z120 : W := mkw 0xac0cd00970056023 0x01ac0cd009700560 0x3c00f001f0007080 0x813c00f001f00070

def z121 : W := mkw 0xac0dd00b700f6027 0x01ac0dd00b700f60 0x3c0ff001f00ff086 0x8b3c0ff001f00ff0

def z122 : W := mkw 0xbd7ce560000000c0 0x02bd7ce560000000 0x3c70f07000000000 0x803c70f070000000

def z123 : W := mkw 0xee9fdbbf7b5ffeb7 0xa1ee9fdbbf7b5ffe 0xffffffffffffffff 0xffffffffffffffff

def z124 : W := mkw 0x53c33e56cece571e 0xc053c33e56cece57 0xf347fc7fcccc7fbf 0xbff347fc7fcccc7f

def z125 : W := mkw 0x041eeff01151bcc0 0x22041eeff01151bc 0x000ffff00003fc0e 0x0a000ffff00003fc

def z126 : W := mkw 0x1140000084800008 0x0011400000848000 0x33400001ccc000b1 0xb533400001ccc000

def z127 : W := mkw 0xa805500b600e4027 0x01a805500b600e40 0xf007700fc00c0024 0x23f007700fc00c00

def z128 : W := mkw 0xffedd00ffeaf603f 0x05ffedd00ffeaf60 0xfffff00ffffff0f7 0xfffffff00ffffff0

def z129 : W := mkw 0xfbe0000daea00038 0x04fbe0000daea000 0xfff00c0ffffc0fff 0xfdfff00c0ffffc0f

def z130 : W := mkw 0x041881a01111a880 0x20041881a01111a8 0x0cf8038033f380d1 0xd40cf8038033f380

def z131 : W := mkw 0x0001100b700f6027 0x010001100b700f60 0x0000000ff00ff0f0 0x090000000ff00ff0

def z132 : W := mkw 0xfbe0345deee4553a 0x44fbe0345deee455 0xfff0f07ffff070f1 0xf5fff0f07ffff070

def z133 : W := mkw 0x53e024548ee01518 0x4453e024548ee015 0x03f00c700ff00f09 0x0403f00c700ff00f

def z134 : W := mkw 0xfffeff70c4c455ca 0x42fffeff70c4c455 0xfffffff1cccc7fbf 0xfffffffff1cccc7f

def z135 : W := mkw 0xfffeeffdbff1bcf8 0x26fffeeffdbff1bc 0xfffffffffff3fcff 0xfffffffffffff3fc

def z136 : W := mkw 0x040dd002500f6007 0x01040dd002500f60 0x000ff000000ff006 0x0a000ff000000ff0

def z137 : W := mkw 0xee8fca860b0a8a14 0x80ee8fca860b0a8a 0xff8fff8e0f0f8f7f 0xfeff8fff8e0f0f8f

def z138 : W := mkw 0x00010082010a8a04 0x8000010082010a8a 0x00000000000f8f00 0x0800000000000f8f

def z139 : W := mkw 0x041881a01111a880 0x20041881a01111a8 0x0cb8038033338040 0x400cb80380333380

def z140 : W := mkw 0xfbe67e50c4c4554a 0x42fbe67e50c4c455 0xf347fc71cccc7fbf 0xbff347fc71cccc7f

def z141 : W := mkw 0xee8fda8f7b0fea37 0x81ee8fda8f7b0fea 0xff8fff8fff0fffff 0xffff8fff8fff0fff

def z142 : W := mkw 0xfbe30a860b0a8a14 0x80fbe30a860b0a8a 0xffff0f8e0f0f8f7f 0xfeffff0f8e0f0f8f

def z143 : W := mkw 0xffeffe4b700f6067 0x03ffeffe4b700f60 0xff0ffc0ff00ff0f6 0xfbff0ffc0ff00ff0

def z144 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000000c0c0f30 0x0c000000000c0c0f

def z145 : W := mkw 0x11403450c4c4550a 0x4011403450c4c455 0x3340fc71ccc07f89 0x853340fc71ccc07f

def z146 : W := mkw 0xfbe5500feeae403f 0x05fbe5500feeae40 0xf307700fcc0c0024 0x23f307700fcc0c00

def z147 : W := mkw 0x0418812000000080 0x0004188120000000 0x0c70807000000000 0x800c708070000000

def z148 : W := mkw 0x041881b01151bc80 0x20041881b01151bc 0x004883f000c3fc9b 0x9c004883f000c3fc

def z149 : W := mkw 0x1140244000000000 0x0011402440000000 0x3340fc700000000f 0xb03340fc70000000

def z150 : W := mkw 0x0000008001008800 0x0000000080010088 0x0088038003038040 0x4000880380030380

def z151 : W := mkw 0xbd4ce44000000000 0x00bd4ce440000000 0xff4ffc700000000f 0xf2ff4ffc70000000

def z152 : W := mkw 0x000100860b0a8a14 0x80000100860b0a8a 0x0000000e0f0f8f70 0x0c0000000e0f0f8f

def z153 : W := mkw 0xffffefefafaa8afc 0x86ffffefefafaa8a 0xffffffffffff8fff 0xffffffffffffff8f

def z154 : W := mkw 0xfbe66e4daea00078 0x06fbe66e4daea000 0xf3077c0fcc000024 0x23f3077c0fcc0000

def z155 : W := mkw 0x57dbbff6dfdfff9e 0xe057dbbff6dfdfff 0xffffffffffffffff 0xffffffffffffffff

def z156 : W := mkw 0xeebfcba60b0a8ad4 0x82eebfcba60b0a8a 0xccbf038e03038040 0x42ccbf038e030380

def z157 : W := mkw 0xac1881b93151bca0 0x20ac1881b93151bc 0xfcf883fff3f3fcfb 0xfdfcf883fff3f3fc

def z158 : W := mkw 0x469fefe60b0a8ad4 0x82469fefe60b0a8a 0xc38ffffe0f0f8f7f 0x7ec38ffffe0f0f8f

def z159 : W := mkw 0xeeb881ad3b31a8b0 0x24eeb881ad3b31a8 0xccb8038e33338040 0x40ccb8038e333380

def z160 : W := mkw 0xac0dd08f7b0fea37 0x81ac0dd08f7b0fea 0xfc0ff00fff0ffff6 0xfffc0ff00fff0fff

def z161 : W := mkw 0xbd4cf450c4c4550a 0x40bd4cf450c4c455 0xff4ffc71cccc7fbf 0xffff4ffc71cccc7f

def z162 : W := mkw 0x0000001000401400 0x0000000010004014 0x03408c700ccc7fbf 0xbc03408c700ccc7f

def z163 : W := mkw 0x42830a060a0a0214 0x8042830a060a0a02 0xc3070c0e0c0c0f3f 0x3ec3070c0e0c0c0f

def z164 : W := mkw 0xfbe0344deea4413a 0x44fbe0344deea441 0xfff07c0ffffc03f5 0xf5fff07c0ffffc03

def z165 : W := mkw 0x53e20a848fa08a18 0x8453e20a848fa08a 0x03f00f800ff00f09 0x0403f00f800ff00f

def z166 : W := mkw 0x42830a860b0a8a14 0x8042830a860b0a8a 0x038f0f800f0f8f0f 0x0e038f0f800f0f8f

def z167 : W := mkw 0x42831a864b0eca16 0x8042831a864b0eca 0xf38fff8fcf0fffff 0xfff38fff8fcf0fff

def z168 : W := mkw 0x041ce560000000c0 0x02041ce560000000 0x0000f07000000000 0x000000f070000000

def z169 : W := mkw 0x1140244084800008 0x0011402440848000 0x3340fc71ccc000bf 0xb53340fc71ccc000

def z170 : W := mkw 0x1558a56000000080 0x001558a560000000 0x3ff8fff00000000f 0xf03ff8fff0000000

def z171 : W := mkw 0xfbe0000000000000 0x00fbe00000000000 0xfff0000033f000d1 0xf4fff0000033f000

def z172 : W := mkw 0xfbe20a0daea00038 0x04fbe20a0daea000 0xffff0f8ffff000ff 0xf7ffff0f8ffff000

def z173 : W := mkw 0xfffeef69200000e0 0x02fffeef69200000 0xfffffffff00000ff 0xf3fffffffff00000

def z174 : W := mkw 0x53f22f648ea000d8 0x0653f22f648ea000 0x03f00ff00ff00009 0x0403f00ff00ff000

def z175 : W := mkw 0x0000000000000000 0x0000000000000000 0x00f0000003f00001 0x0400f0000003f000

def z176 : W := mkw 0x1140245084c01508 0x401140245084c015 0x0040007000c00000 0x000040007000c000

def z177 : W := mkw 0x041881a01111a880 0x20041881a01111a8 0x0cf883f03333804b 0xd00cf883f0333380

def z178 : W := mkw 0x469b8ba61b1baa94 0xa0469b8ba61b1baa 0xcfbf0f8e3f3f8f7f 0x7ecfbf0f8e3f3f8f

def z179 : W := mkw 0x00010002000a0004 0x0000010002000a00 0xc007000e000c0024 0x22c007000e000c00

def z180 : W := mkw 0x11403450c4c4550a 0x4011403450c4c455 0x3300fc71cc0c7f2e 0x293300fc71cc0c7f

def z181 : W := mkw 0xfffeef6daea000f8 0x06fffeef6daea000 0xffffffffcc00002f 0xf3ffffffffcc0000

def z182 : W := mkw 0x041881b01151bc80 0x20041881b01151bc 0x0cf883f033f3f0c0 0xc00cf883f033f3f0

def z183 : W := mkw 0x1140000084800008 0x0011400000848000 0x30400001c0c00080 0x8130400001c0c000

def z184 : W := mkw 0x0000001010513400 0x2000000010105134 0x0000000030f07080 0x000000000030f070

def z185 : W := mkw 0xfbe66e4000000040 0x02fbe66e40000000 0xf38f7f800000000f 0x72f38f7f80000000

def z186 : W := mkw 0xa800000920000020 0x00a8000009200000 0xcc00000e30000040 0x40cc00000e300000

def z187 : W := mkw 0x1558a5f01151bc80 0x201558a5f01151bc 0x3ff8fff033f3fcdf 0xfc3ff8fff033f3fc

def z188 : W := mkw 0xac0dd00b700f6027 0x01ac0dd00b700f60 0xcc0f000ff00ff0f0 0x4bcc0f000ff00ff0

def z189 : W := mkw 0x041881b01151bc80 0x20041881b01151bc 0x000883f033f3fcda 0x0c000883f033f3fc

def z190 : W := mkw 0xfffeeff01151bcc0 0x22fffeeff01151bc 0xfffffff033f3fcdf 0xfefffffff033f3fc

def z191 : W := mkw 0x53e0000daea00038 0x0453e0000daea000 0x03f0000ffff000f1 0x0503f0000ffff000

def z192 : W := mkw 0x42830a060a0a0214 0x8042830a060a0a02 0xc3070c0e0c0c0324 0x22c3070c0e0c0c03

def z193 : W := mkw 0xa804400000000000 0x00a8044000000000 0xf007700000000004 0x22f0077000000000

def z194 : W := mkw 0x1140244000000000 0x0011402440000000 0x3340fc700c0c0f3f 0xbc3340fc700c0c0f

def z195 : W := mkw 0x11403440c484410a 0x4011403440c48441 0x33407c01cccc03b5 0xb533407c01cccc03

def z196 : W := mkw 0x428100060a0a0014 0x00428100060a0a00 0xc38f000e0f0f8077 0x7ec38f000e0f0f80

def z197 : W := mkw 0xbd4cf459f4c5752b 0x41bd4cf459f4c575 0x3f40fc71fccc7fbf 0xbd3f40fc71fccc7f

def z198 : W := mkw 0x0418812000000080 0x0004188120000000 0x000883f00000000a 0x00000883f0000000

def z199 : W := mkw 0x42830a860b0a8a14 0x8042830a860b0a8a 0xc08f038e03038040 0x42c08f038e030380

def z200 : W := mkw 0x53f22f60000000c0 0x0253f22f60000000 0x33f0fff00000000f 0xb033f0fff0000000

def z201 : W := mkw 0xea80000d2a000030 0x00ea80000d2a0000 0xff80000fff0000f1 0xf5ff80000fff0000

def z202 : W := mkw 0xa801100b700f6027 0x01a801100b700f60 0xfc00000ff00ff0f0 0xf9fc00000ff00ff0

def z203 : W := mkw 0xbd7ce560000000c0 0x02bd7ce560000000 0x3f70fc700000000f 0xb03f70fc70000000

def z204 : W := mkw 0x00020a0000000000 0x0000020a00000000 0x000f0f800000000e 0x02000f0f80000000

def z205 : W := mkw 0x0000000000000000 0x0000000000000000 0x008803800000000b 0x5000880380000000

def z206 : W := mkw 0xfbe76e460a0a0254 0x82fbe76e460a0a02 0xf3077c0e0c0c0324 0x22f3077c0e0c0c03

def z207 : W := mkw 0x041881bdbff1bcb8 0x24041881bdbff1bc 0x0cf883fffff3fcfb 0xdd0cf883fffff3fc

def z208 : W := mkw 0xbd7cf570c4c455ca 0x42bd7cf570c4c455 0x3f70fc71cccc7fbf 0xbd3f70fc71cccc7f

def z209 : W := mkw 0xeebecb2d2a2000f0 0x06eebecb2d2a2000 0xccbf038e33300040 0x42ccbf038e333000

def z210 : W := mkw 0xbd5df5fbf5dffdaf 0x61bd5df5fbf5dffd 0xffffffffffffffff 0xffffffffffffffff

def z211 : W := mkw 0x041eef60000000c0 0x02041eef60000000 0x0cfffff00000000f 0xd20cfffff0000000

def z212 : W := mkw 0x53e000048ea00018 0x0453e000048ea000 0x03f000000ff00001 0x0403f000000ff000

def z213 : W := mkw 0xfbe0000daea00038 0x04fbe0000daea000 0x3ff00001fff00081 0x853ff00001fff000

def z214 : W := mkw 0xfbe000040a000010 0x00fbe000040a0000 0xfff0000e0f000071 0xf4fff0000e0f0000

def z215 : W := mkw 0xfbe0000daea00038 0x04fbe0000daea000 0xf3f0000fcff00021 0x25f3f0000fcff000

def z216 : W := mkw 0x115035f0c5d4dd8a 0x60115035f0c5d4dd 0x33f0fff1cffc7fbf 0xbd33f0fff1cffc7f

def z217 : W := mkw 0xac0cc00010012000 0x00ac0cc000100120 0xfc0ff0003003f0d6 0xfafc0ff0003003f0

def z218 : W := mkw 0xfbe1000faeaa003c 0x04fbe1000faeaa00 0xffff000fffff80f7 0xffffff000fffff80

def z219 : W := mkw 0x0408800010012000 0x0004088000100120 0x0c00800030007080 0x800c008000300070

def z220 : W := mkw 0x1558b570c4c4558a 0x401558b570c4c455 0x3ff8fff1cccc7fbf 0xfd3ff8fff1cccc7f

def z221 : W := mkw 0x0000345040445502 0x4000003450404455 0x0000f07000007000 0x000000f070000070

def z222 : W := mkw 0x11403450c4c4550a 0x4011403450c4c455 0x3340fc71c0c0708f 0xb13340fc71c0c070

def z223 : W := mkw 0x57faaff01151bcc0 0x2257faaff01151bc 0x0ff88ff033f3fcdb 0xdc0ff88ff033f3fc

def z224 : W := mkw 0xbd7ce560000000c0 0x02bd7ce560000000 0x3cf8f3f00000000b 0xd03cf8f3f0000000

def z225 : W := mkw 0x428000840b008810 0x00428000840b0088 0xc388038e0f038c7b 0x7cc388038e0f038c

def z226 : W := mkw 0xbd4cf459f4c5752b 0x41bd4cf459f4c575 0x3c40f071f0c07080 0x813c40f071f0c070

def z227 : W := mkw 0xeaa0000d2a200030 0x04eaa0000d2a2000 0xccb0000e33300040 0x40ccb0000e333000

def z228 : W := mkw 0xee8dd00f7a0f6037 0x01ee8dd00f7a0f60 0xff8ff00fff0ff0f7 0xffff8ff00fff0ff0

def z229 : W := mkw 0x001001b001509c80 0x20001001b001509c 0x00f003f003f00c09 0x0400f003f003f00c

def z230 : W := mkw 0x00033ed2414edf06 0xc000033ed2414edf 0x000ffff0000fff0e 0x0a000ffff0000fff

def z231 : W := mkw 0xa800000920000020 0x00a8000009200000 0x3c000001f0000080 0x813c000001f00000

def z232 : W := mkw 0x0418813010513480 0x2004188130105134 0x0cf883f030f0708b 0xd00cf883f030f070

def z233 : W := mkw 0xfffeef648ea000d8 0x06fffeef648ea000 0xfffffff00ff0000f 0xf6fffffff00ff000

def z234 : W := mkw 0xfbe66e4daea00078 0x06fbe66e4daea000 0xfff77c0ffff000f5 0xf7fff77c0ffff000

def z235 : W := mkw 0x53c22ed48fc09f18 0xc053c22ed48fc09f 0x03c00ff00fc00f09 0x0403c00ff00fc00f

def z236 : W := mkw 0xfbf001bdaff09cb8 0x24fbf001bdaff09c 0xfff003fffff00cf9 0xf5fff003fffff00c

def z237 : W := mkw 0xbd7cf570c4c455ca 0x42bd7cf570c4c455 0x3c70f071c0c07080 0x813c70f071c0c070

def z238 : W := mkw 0x1140345040445502 0x4011403450404455 0x3340fc70000c7f0f 0xb83340fc70000c7f

def z239 : W := mkw 0x0000101deee4553a 0x440000101deee455 0x0000000ffffc7ff0 0x0d0000000ffffc7f

def z240 : W := mkw 0xac0cd00970056023 0x01ac0cd009700560 0xfc0ff001f0007086 0xf3fc0ff001f00070

def z241 : W := mkw 0xeeadc00f3a2b2035 0x05eeadc00f3a2b20 0xccbf000e33338040 0x42ccbf000e333380

def z242 : W := mkw 0x041881b01151bc80 0x20041881b01151bc 0x000883f00003fc0a 0x08000883f00003fc

def z243 : W := mkw 0x53c32ec60b0a8a14 0x8053c32ec60b0a8a 0xf3cffffe0f0f8f7f 0xfef3cffffe0f0f8f

def z244 : W := mkw 0x00001000c484410a 0x4000001000c48441 0x00000001cc0c0320 0x0100000001cc0c03

def z245 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000c00000c0f0e 0x0800000c00000c0f

def z246 : W := mkw 0xeebecb20000000c0 0x02eebecb20000000 0xccbf038000000000 0x42ccbf0380000000

def z247 : W := mkw 0x0418813010513480 0x2004188130105134 0x0c70807030f07080 0x800c70807030f070

def z248 : W := mkw 0xfbf22f60000000c0 0x02fbf22f60000000 0xfff00ff000000009 0xf0fff00ff0000000

def z249 : W := mkw 0x0000101040445502 0x4000001010404455 0x00000000000c7f00 0x0800000000000c7f

def z250 : W := mkw 0xa800000000000000 0x00a8000000000000 0xfc00000000000000 0xf0fc000000000000

def z251 : W := mkw 0xfbe0244000000000 0x00fbe02440000000 0xfff0fc700000000f 0xf0fff0fc70000000

def z252 : W := mkw 0xac0df45b704f7527 0x41ac0df45b704f75 0xfc0ffc7ff00ffffe 0xfbfc0ffc7ff00fff

def z253 : W := mkw 0xa801000b200a0024 0x00a801000b200a00 0xfc0f000ff00f80f6 0xfbfc0f000ff00f80

def z254 : W := mkw 0x42820a0000000000 0x0042820a00000000 0xc3070c0000000004 0x22c3070c00000000

def z255 : W := mkw 0xa804500960044023 0x01a8045009600440 0x30007001c0000000 0x0130007001c00000

def z256 : W := mkw 0x0408800010012000 0x0004088000100120 0x0c0880003003f0d2 0xd80c0880003003f0

def z257 : W := mkw 0x0000000000000000 0x0000000000000000 0xc00f000000000006 0x72c00f0000000000

def z258 : W := mkw 0x00122f60000000c0 0x0200122f60000000 0x00000ff000000008 0x0000000ff0000000

def z259 : W := mkw 0x1140000084800008 0x0011400000848000 0x3ff00001fff000f1 0xf53ff00001fff000

def z260 : W := mkw 0xb9600009a4a00028 0x04b9600009a4a000 0x30000001c0000000 0x0130000001c00000

def z261 : W := mkw 0x42830a860b0a8a14 0x8042830a860b0a8a 0xc3870f8e0f0c0f2d 0x26c3870f8e0f0c0f

def z262 : W := mkw 0xffefda8fffafea3f 0x85ffefda8fffafea 0xffffff8fffffffff 0xffffffff8fffffff

def z263 : W := mkw 0xac0fda8b710fea27 0x81ac0fda8b710fea 0xfc0fff8ff00ffffe 0xfbfc0fff8ff00fff

def z264 : W := mkw 0x469eef60000000c0 0x02469eef60000000 0xc38ffff00000000f 0x72c38ffff0000000

def z265 : W := mkw 0x0000001000401400 0x0000000010004014 0x0040007000c00c09 0x040040007000c00c

def z266 : W := mkw 0x00001010c4c4550a 0x4000001010c4c455 0x03000c01cccc7fbf 0x3d03000c01cccc7f

def z267 : W := mkw 0xeaa30a8f2b2a8a34 0x84eaa30a8f2b2a8a 0xcfbf0f8e3f3f8f7f 0x7ecfbf0f8e3f3f8f

def z268 : W := mkw 0xac0cc00000000000 0x00ac0cc000000000 0x3c00f00000000000 0x803c00f000000000

def z269 : W := mkw 0xb964644000000040 0x02b9646440000000 0x3000700000000000 0x0030007000000000

def z270 : W := mkw 0x041881a01111a880 0x20041881a01111a8 0x0cb883803333f0d2 0xd80cb883803333f0

def z271 : W := mkw 0x040dd00b700f6027 0x01040dd00b700f60 0x000ff00ff00ff0f6 0x0b000ff00ff00ff0

def z272 : W := mkw 0x0001100b600e4027 0x010001100b600e40 0x0000000fc00c0020 0x010000000fc00c00

def z273 : W := mkw 0xfffecb2daea000f8 0x06fffecb2daea000 0xffff038ffff000f1 0xf7ffff038ffff000

def z274 : W := mkw 0x155eff70c4c455ca 0x42155eff70c4c455 0x334ffff1cccc7fbf 0xbf334ffff1cccc7f

def z275 : W := mkw 0xac0dd00b700f6027 0x01ac0dd00b700f60 0xfc0f700ff00f8064 0x63fc0f700ff00f80

def z276 : W := mkw 0xa805500b700f6027 0x01a805500b700f60 0xf007700ff00ff0f4 0x2bf007700ff00ff0

def z277 : W := mkw 0x040df452504f7507 0x41040df452504f75 0x000ffc70000fff0e 0x0a000ffc70000fff

def z278 : W := mkw 0xfbe0000084800008 0x00fbe00000848000 0xfff00001ccc000b1 0xf5fff00001ccc000

def z279 : W := mkw 0x0000000920000020 0x0000000009200000 0x0000000ff00000f0 0x010000000ff00000

def z280 : W := mkw 0xffe8800dbea12038 0x04ffe8800dbea120 0xfff8800ffff3f0f3 0xfdfff8800ffff3f0

def z281 : W := mkw 0x000100860b0a8a14 0x80000100860b0a8a 0x0000000e03038040 0x000000000e030380

def z282 : W := mkw 0x040cc00000000000 0x00040cc000000000 0x000ff00000000006 0x02000ff000000000

def z283 : W := mkw 0xffecc00daea00038 0x04ffecc00daea000 0xfffff00ffff000f7 0xf7fffff00ffff000

def z284 : W := mkw 0x0000001000401400 0x0000000010004014 0x0040807000c07c9b 0x9c0040807000c07c

def z285 : W := mkw 0xfffeef60000000c0 0x02fffeef60000000 0xff77fc7000000004 0xa2ff77fc70000000

def z286 : W := mkw 0xa805500b600e4027 0x01a805500b600e40 0xf00f700fc00f8076 0x7bf00f700fc00f80

def z287 : W := mkw 0xac0cd00970056023 0x01ac0cd009700560 0x3c08f001f003f0d2 0xd93c08f001f003f0

def z288 : W := mkw 0x00001010c4c4550a 0x4000001010c4c455 0x00408071cccc7fbb 0x9d00408071cccc7f

def z289 : W := mkw 0x0000000000000000 0x0000000000000000 0x0cf0000033f000d1 0xd40cf0000033f000

def z290 : W := mkw 0x42b20b20000000c0 0x0242b20b20000000 0x00b0038000000000 0x0000b00380000000

def z291 : W := mkw 0xffecd00dfea5603b 0x05ffecd00dfea560 0xfff0f00ffff070f1 0xf5fff0f00ffff070

def z292 : W := mkw 0x041b8bb2115bbe84 0xa0041b8bb2115bbe 0x000f8ff0000fff0e 0x0a000f8ff0000fff

def z293 : W := mkw 0xac0dd00b700f6027 0x01ac0dd00b700f60 0xff0ffc0ffc0fffff 0xffff0ffc0ffc0fff

def z294 : W := mkw 0x0000100040044002 0x0000001000400440 0x3000f001c0007080 0x813000f001c00070

def z295 : W := mkw 0xac0dc002000a0004 0x00ac0dc002000a00 0xfc0ff00e000f8076 0xfafc0ff00e000f80

def z296 : W := mkw 0x53f22fe40b008ad0 0x8253f22fe40b008a 0x03f00ff00f000f09 0x0403f00ff00f000f

def z297 : W := mkw 0x1558b570d4d5758a 0x601558b570d4d575 0x3f70fc71fcfc7fbf 0xbd3f70fc71fcfc7f

def z298 : W := mkw 0x428000040a000010 0x00428000040a0000 0xc3800c0e0f0c0f7f 0x7cc3800c0e0f0c0f

def z299 : W := mkw 0xeaa30a8f2b2a8a34 0x84eaa30a8f2b2a8a 0xccbf038e33338040 0x42ccbf038e333380

def z300 : W := mkw 0xffffff6b600e40e7 0x03ffffff6b600e40 0xffffffffc00c002f 0xf3ffffffffc00c00

def z301 : W := mkw 0xfff8812000000080 0x00fff88120000000 0xfff883f00000000b 0xf0fff883f0000000

def z302 : W := mkw 0x0000009dbff1bc38 0x240000009dbff1bc 0x0000000ffff3fcf0 0x0d0000000ffff3fc

def z303 : W := mkw 0xeebecba01111a8c0 0x22eebecba01111a8 0xccbf038033338040 0x42ccbf0380333380

def z304 : W := mkw 0xfff881b01151bc80 0x20fff881b01151bc 0xfff883f033f3fcdb 0xfcfff883f033f3fc

def z305 : W := mkw 0x42830a860b0a8a14 0x8042830a860b0a8a 0xc3070c0e0f0f8f74 0x2ec3070c0e0f0f8f

def z306 : W := mkw 0xac1dd12b700f60a7 0x01ac1dd12b700f60 0xfcfff3fff00ff0ff 0xfbfcfff3fff00ff0

def z307 : W := mkw 0xac0dd01bf4cf752f 0x41ac0dd01bf4cf75 0xfc0ff00ffccffff6 0xfffc0ff00ffccfff

def z308 : W := mkw 0x11403440c484410a 0x4011403440c48441 0x33007c01cc0c0f3f 0x3d33007c01cc0c0f

def z309 : W := mkw 0x0000000000000000 0x0000000000000000 0x03000c000c000f09 0x0403000c000c000f

def z310 : W := mkw 0xac1dc1bb315bbca5 0x21ac1dc1bb315bbc 0xccff83fe33f3fcdb 0xdeccff83fe33f3fc

def z311 : W := mkw 0x53c03454cec4551a 0x4053c03454cec455 0xf3c0fc7fcfcc7fff 0xfdf3c0fc7fcfcc7f

def z312 : W := mkw 0x11401000c484400a 0x0011401000c48440 0x3340f001cccc70b7 0xbd3340f001cccc70

def z313 : W := mkw 0xac0dd00b700f6027 0x01ac0dd00b700f60 0xfc07f00ff00c70a4 0xa3fc07f00ff00c70

def z314 : W := mkw 0x0000008001008800 0x0000000080010088 0x0000000003038c50 0x0c0000000003038c

def z315 : W := mkw 0xfffeef60000000c0 0x02fffeef60000000 0xf30ffff00000000e 0x22f30ffff0000000

def z316 : W := mkw 0x11403450c4c4550a 0x4011403450c4c455 0x3340f071ccc070b1 0xb53340f071ccc070

def z317 : W := mkw 0xac0cc00000000000 0x00ac0cc000000000 0xfc0ff00000000006 0xf2fc0ff000000000

def z318 : W := mkw 0x0000000daea00038 0x040000000daea000 0x0000000fcc000020 0x010000000fcc0000

def z319 : W := mkw 0xee8fca8f3b0baa35 0x81ee8fca8f3b0baa 0xcf8f0f8e3f0f8f7f 0x7ecf8f0f8e3f0f8f

def z320 : W := mkw 0x00030a82010a8a04 0x8000030a82010a8a 0x000f0f80000f8f0e 0x0a000f0f80000f8f

def z321 : W := mkw 0xa805500b600e4027 0x01a805500b600e40 0xf007f00fc00c70b6 0xbbf007f00fc00c70

def z322 : W := mkw 0x0000000000000000 0x0000000000000000 0x03000c000c0c0324 0x2003000c000c0c03

def z323 : W := mkw 0xac0dd00b600e4027 0x01ac0dd00b600e40 0xfc0ff00fc00c0026 0xf3fc0ff00fc00c00

def z324 : W := mkw 0xee8fda0f7a0f6237 0x81ee8fda0f7a0f62 0xff0ffc0ffc0ff3f6 0xfbff0ffc0ffc0ff3

def z325 : W := mkw 0xac1cd139705574a3 0x21ac1cd139705574 0x3c70f071f0f07080 0x813c70f071f0f070

def z326 : W := mkw 0x11702560000000c0 0x0211702560000000 0x0070007000000000 0x0000700070000000

def z327 : W := mkw 0x001001b001509c80 0x20001001b001509c 0x00f803f003f38c5b 0x5c00f803f003f38c

def z328 : W := mkw 0x53f32fe60b0a8ad4 0x8253f32fe60b0a8a 0xc3ff0ffe0f0f8f7f 0x7ec3ff0ffe0f0f8f

def z329 : W := mkw 0x0000008001008800 0x0000000080010088 0x03880f800f0f8f7f 0x7c03880f800f0f8f

def z330 : W := mkw 0x000100860b0a8a14 0x80000100860b0a8a 0x0088038e0f0f8f7b 0x5c0088038e0f0f8f

def z331 : W := mkw 0xac0dd00b700f6027 0x01ac0dd00b700f60 0xfc0ff00ff003f0c0 0xc3fc0ff00ff003f0

def z332 : W := mkw 0xfffeef60848000c8 0x02fffeef60848000 0xfffffff1ccc000bf 0xf7fffffff1ccc000

def z333 : W := mkw 0x4280000daea00038 0x044280000daea000 0xc380000ffff000f1 0x75c380000ffff000

def z334 : W := mkw 0x155eef60000000c0 0x02155eef60000000 0x334ffff00000000f 0xb2334ffff0000000

def z335 : W := mkw 0x04098002100b2004 0x0004098002100b20 0xcc0f800e300ff0f6 0xfacc0f800e300ff0

def z336 : W := mkw 0xb9600009a4a00028 0x04b9600009a4a000 0x3cf00001f3f000d1 0xd53cf00001f3f000

def z337 : W := mkw 0xfffeef60000000c0 0x02fffeef60000000 0xcfff0ff000000009 0x42cfff0ff0000000

def z338 : W := mkw 0x1140000000000000 0x0011400000000000 0x3340000000000001 0xb033400000000000

def z339 : W := mkw 0x42830a860b0a8a14 0x8042830a860b0a8a 0xc08f038e0f0f8f70 0x4ec08f038e0f0f8f

def z340 : W := mkw 0xfbe0244daea00038 0x04fbe0244daea000 0xfff0fc7ffff000ff 0xf5fff0fc7ffff000

def z341 : W := mkw 0x154df452d4cf750f 0x41154df452d4cf75 0x334ffc71cccfffbf 0xbf334ffc71cccfff

def z342 : W := mkw 0x041881b01151bc80 0x20041881b01151bc 0x0c70807033f3fcd0 0x8c0c70807033f3fc

def z343 : W := mkw 0x000000901151bc00 0x20000000901151bc 0x000000000003fc00 0x08000000000003fc

def z344 : W := mkw 0xfbe66e4000000040 0x02fbe66e40000000 0xf347fc700000000f 0xb2f347fc70000000

def z345 : W := mkw 0x469b8ba61b1baa94 0xa0469b8ba61b1baa 0xccbf038e33338040 0x42ccbf038e333380

def z346 : W := mkw 0x42820a840b008a10 0x8042820a840b008a 0x03800f800f0c0f3f 0x3c03800f800f0c0f

def z347 : W := mkw 0xfbe0000d2a200030 0x04fbe0000d2a2000 0xfff0000e33300041 0xf0fff0000e333000

def z348 : W := mkw 0xbd7cf569700560e3 0x03bd7cf569700560 0x3c70f071f0007080 0x813c70f071f00070

def z349 : W := mkw 0x041fff62500f60c7 0x03041fff62500f60 0x000ffff0000ff00e 0x0a000ffff0000ff0

def z350 : W := mkw 0x00001010c4c4550a 0x4000001010c4c455 0x3000f001cccc7fb6 0xbd3000f001cccc7f

def z351 : W := mkw 0x000000901151bc00 0x20000000901151bc 0x0cf0000033f3fcd1 0xdc0cf0000033f3fc

def z352 : W := mkw 0xac08800930012020 0x00ac088009300120 0xfc08800ff003f0f2 0xf9fc08800ff003f0

def z353 : W := mkw 0xeaa0000d2a200030 0x04eaa0000d2a2000 0xfcb0000ff33000f0 0xf1fcb0000ff33000

def z354 : W := mkw 0xee8fca8f3b0baa35 0x81ee8fca8f3b0baa 0xcc8f038e33038040 0x42cc8f038e330380

def z355 : W := mkw 0xb9603459e4e4552a 0x44b9603459e4e455 0x3f70fc71fcfc7fbf 0xbd3f70fc71fcfc7f

def z356 : W := mkw 0x1140245084c01508 0x401140245084c015 0x33400c71ccc00fb9 0xb533400c71ccc00f

def z357 : W := mkw 0xac0dd01b704f7427 0x01ac0dd01b704f74 0xfc4ff07ff0cffcff 0xfffc4ff07ff0cffc

def z358 : W := mkw 0xffcffedfffcfff3f 0xc1ffcffedfffcfff 0xffcfffffffcfffff 0xffffcfffffffcfff

def z359 : W := mkw 0x42831a8f7b0fea37 0x8142831a8f7b0fea 0xc38f0f8fff0fffff 0x7fc38f0f8fff0fff

def z360 : W := mkw 0xeaa0000daea00038 0x04eaa0000daea000 0xccb0000ffff000f0 0x45ccb0000ffff000

def z361 : W := mkw 0x0000000000000000 0x0000000000000000 0x0cf0000000000001 0xd00cf00000000000

def z362 : W := mkw 0x53c000048e800018 0x0053c000048e8000 0xf3c0000fcfc000f1 0xf5f3c0000fcfc000

def z363 : W := mkw 0xfffeff69700560e3 0x03fffeff69700560 0xfffffff1f000708f 0xf3fffffff1f00070

def z364 : W := mkw 0xfffce560000000c0 0x02fffce560000000 0xfff0f07000000001 0xf0fff0f070000000

def z365 : W := mkw 0x041881a001008880 0x00041881a0010088 0x0cf883f003038c5b 0xdc0cf883f003038c

def z366 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000c1b 0x1c0000000000000c

def z367 : W := mkw 0x468b8a861b0baa14 0x80468b8a861b0baa 0xcf8f8f8e3f0fffff 0xfecf8f8f8e3f0fff

def z368 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z369 : W := mkw 0x0000001000401400 0x0000000010004014 0x0000000000c07c90 0x0c0000000000c07c

def z370 : W := mkw 0xac1dd1bb715ffca7 0x21ac1dd1bb715ffc 0xfc0ff3fff00ffcfe 0xfbfc0ff3fff00ffc

def z371 : W := mkw 0x00010002000a0004 0x0000010002000a00 0x0000000e000f8070 0x080000000e000f80

def z372 : W := mkw 0x041881b01151bc80 0x20041881b01151bc 0x0c0883f03003fcda 0xd80c0883f03003fc

def z373 : W := mkw 0xffeeee4000000040 0x02ffeeee40000000 0xff0ffc0000000006 0xf2ff0ffc00000000

def z374 : W := mkw 0x00010002000a0004 0x0000010002000a00 0x000f0000000f8006 0x0a000f0000000f80

def z375 : W := mkw 0x1140245084c01508 0x401140245084c015 0x3340fc700cc00f0f 0xb43340fc700cc00f

def z376 : W := mkw 0x041eeff01151bcc0 0x22041eeff01151bc 0x0cfffff033f3fcdf 0xde0cfffff033f3fc

def z377 : W := mkw 0x00055002400e4007 0x0100055002400e40 0x00077000000c0004 0x0200077000000c00

def z378 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000000000c0036 0x3800000000000c00

def z379 : W := mkw 0x1140244000000000 0x0011402440000000 0x03400c7000000009 0x0003400c70000000

def z380 : W := mkw 0xbd788139b4f134a8 0x24bd788139b4f134 0x3c708071f0f07080 0x813c708071f0f070

def z381 : W := mkw 0x0001100ffeaf603f 0x050001100ffeaf60 0x0000000ffffff0f0 0x0d0000000ffffff0

def z382 : W := mkw 0x42820a040a000010 0x0042820a040a0000 0xc38f0f8e0f00007f 0x76c38f0f8e0f0000

def z383 : W := mkw 0x42920bb40b509e90 0xa042920bb40b509e 0x03f00ff00ff00f09 0x0403f00ff00ff00f

def z384 : W := mkw 0xa805500b600e4027 0x01a805500b600e40 0xfc07700ff00c00f4 0xf3fc07700ff00c00

def z385 : W := mkw 0xbd4df45bf4cf752f 0x41bd4df45bf4cf75 0xfc4ff07ff0cff0f6 0xfbfc4ff07ff0cff0

def z386 : W := mkw 0xffffef6b300b20e5 0x03ffffef6b300b20 0xfffffffe3003804f 0xf2fffffffe300380

def z387 : W := mkw 0xb9603459e4e4552a 0x44b9603459e4e455 0x3c70f071f0f07080 0x813c70f071f0f070

def z388 : W := mkw 0x041991bb715ffca7 0x21041991bb715ffc 0x0cf883fff3fffcfb 0xdd0cf883fff3fffc

def z389 : W := mkw 0x000000901151bc00 0x20000000901151bc 0x0000000033f3fcd0 0x0c0000000033f3fc

def z390 : W := mkw 0xac0cc00920000020 0x00ac0cc009200000 0xfc0ff00ff00000f6 0xf3fc0ff00ff00000

def z391 : W := mkw 0x42820a0000000000 0x0042820a00000000 0x03800f8000000009 0x0003800f80000000

def z392 : W := mkw 0x041dd1b2515ffc87 0x21041dd1b2515ffc 0x0cfff3f033fffcdf 0xde0cfff3f033fffc

def z393 : W := mkw 0x000100860b0a8a14 0x80000100860b0a8a 0xc00f000e0f0f8f76 0x7ec00f000e0f0f8f

def z394 : W := mkw 0x00010082010a8804 0x0000010082010a88 0xc08f038e030f8c7f 0x7ec08f038e030f8c

def z395 : W := mkw 0xbd7ce570105134c0 0x22bd7ce570105134 0x3c70f07030f07080 0x803c70f07030f070

def z396 : W := mkw 0x0418813010513480 0x2004188130105134 0x0c70807030f07c9b 0x9c0c70807030f07c

def z397 : W := mkw 0x0000000000000000 0x0000000000000000 0x0cb0000033300040 0x400cb00000333000

def z398 : W := mkw 0x11403450c4c4550a 0x4011403450c4c455 0x3ff0fc71fffc7fff 0xfd3ff0fc71fffc7f

def z399 : W := mkw 0x041981b61b5bbe94 0xa0041981b61b5bbe 0x0cf883fe3ffffffb 0xdc0cf883fe3fffff

def z400 : W := mkw 0x000000901151bc00 0x20000000901151bc 0x0088038033f3fcdb 0x5c0088038033f3fc

def z401 : W := mkw 0xfbe30a0faeaa023c 0x84fbe30a0faeaa02 0xfff70c0ffffc03f5 0xf7fff70c0ffffc03

def z402 : W := mkw 0x00030a02000a0204 0x8000030a02000a02 0x00070c00000c0304 0x0200070c00000c03

def z403 : W := mkw 0x468fda865b0fea17 0x81468fda865b0fea 0xc38fff8e0f0fff7f 0x7ec38fff8e0f0fff

def z404 : W := mkw 0xfbe30a8fafaa8a3c 0x84fbe30a8fafaa8a 0xffff038ffff380f1 0xf7ffff038ffff380

def z405 : W := mkw 0x041eff70404455c2 0x42041eff70404455 0x000ffff0000c7f0e 0x0a000ffff0000c7f

def z406 : W := mkw 0xffffef62000a00c4 0x02ffffef62000a00 0xfffffffe000f807f 0xfafffffffe000f80

def z407 : W := mkw 0x1141345bf4cf752f 0x411141345bf4cf75 0x3340fc7ffccfffff 0xbd3340fc7ffccfff

def z408 : W := mkw 0x42830a060a0a0214 0x8042830a060a0a02 0xc38f0f8e0c0c032f 0x72c38f0f8e0c0c03

def z409 : W := mkw 0x0001100b700f6027 0x010001100b700f60 0x3000f00ff00ff0f6 0xb93000f00ff00ff0

def z410 : W := mkw 0x114134d6cfcedf1e 0xc0114134d6cfcedf 0x3340fc7fcfcfffff 0xbd3340fc7fcfcfff

def z411 : W := mkw 0x0000001000401400 0x0000000010004014 0x0000807000007c0a 0x080000807000007c

def z412 : W := mkw 0x1140244000000000 0x0011402440000000 0x33007c0000000004 0x2033007c00000000

def z413 : W := mkw 0x42930bb60b5a9e94 0xa042930bb60b5a9e 0xc3ff0ffe0fff8f7f 0x7ec3ff0ffe0fff8f

def z414 : W := mkw 0x11403450c4c4550a 0x4011403450c4c455 0x3040f071c0c07080 0x813040f071c0c070

def z415 : W := mkw 0x469a8bb41b51be90 0xa0469a8bb41b51be 0x0ff88ff03ff3ffdb 0xdc0ff88ff03ff3ff

def z416 : W := mkw 0x11401010c4c4550a 0x4011401010c4c455 0x33400001cccc7fb1 0xbd33400001cccc7f

def z417 : W := mkw 0x42831a96cfcedf1e 0xc042831a96cfcedf 0xc38f0f8fcfcfffff 0x7fc38f0f8fcfcfff

def z418 : W := mkw 0x00011002400e4006 0x0000011002400e40 0xf00ff00fc00ff0f6 0xfbf00ff00fc00ff0

def z419 : W := mkw 0xfbe00009a4a00028 0x04fbe00009a4a000 0xfff00001f0f00081 0xf1fff00001f0f000

def z420 : W := mkw 0xeebfcb2b300b20e5 0x03eebfcb2b300b20 0xccbf038e30038040 0x42ccbf038e300380

def z421 : W := mkw 0x00011002500f6007 0x0100011002500f60 0x00000000000ff000 0x0800000000000ff0

def z422 : W := mkw 0xa800000920000020 0x00a8000009200000 0xfcf0000ff3f000f1 0xf5fcf0000ff3f000

def z423 : W := mkw 0xac1fff6b700f60e7 0x03ac1fff6b700f60 0xfc0ffffff00ff0fe 0xfbfc0ffffff00ff0

def z424 : W := mkw 0x53c23e50c4c4550a 0x4053c23e50c4c455 0xf3cffff1cccc7fbf 0xfff3cffff1cccc7f

def z425 : W := mkw 0x1140245084c01508 0x401140245084c015 0x03408c700cc07f9b 0x9c03408c700cc07f

def z426 : W := mkw 0x0408801010413400 0x0004088010104134 0x0c48807030c3fcdb 0xdc0c48807030c3fc

def z427 : W := mkw 0xeebecb20000000c0 0x02eebecb20000000 0xccff83f00000000b 0xd2ccff83f0000000

def z428 : W := mkw 0xfffb8bbfbffbbebc 0xa4fffb8bbfbffbbe 0xffff8fffffffffff 0xffffff8fffffffff

def z429 : W := mkw 0xfbe5500feeae403f 0x05fbe5500feeae40 0xfff7700ffffc00f5 0xf7fff7700ffffc00

def z430 : W := mkw 0x53c22e4000000000 0x0053c22e40000000 0xf3cffff00000000f 0xf2f3cffff0000000

def z431 : W := mkw 0xffffefe60b0a8ad4 0x82ffffefe60b0a8a 0xfffffffe0303804f 0xf2fffffffe030380

def z432 : W := mkw 0x00010002000a0004 0x0000010002000a00 0xc30f0c0e0c0f8f7f 0x7ec30f0c0e0c0f8f

def z433 : W := mkw 0x040880801101a800 0x00040880801101a8 0x0c8883803303fcdb 0xdc0c8883803303fc

def z434 : W := mkw 0xfbe1100ffeaf603f 0x05fbe1100ffeaf60 0xfff0000ffffff0f1 0xfdfff0000ffffff0

def z435 : W := mkw 0x4280000000000000 0x0042800000000000 0xc380000000000001 0x70c3800000000000

def z436 : W := mkw 0x00001090d5d5fd0a 0x6000001090d5d5fd 0x00000001fffffff0 0x0d00000001ffffff

def z437 : W := mkw 0x1140244084800108 0x4011402440848001 0x03000c000c000300 0x0003000c000c0003

def z438 : W := mkw 0x42830a860b0a8a14 0x8042830a860b0a8a 0x03800f8e0f0f8f79 0x0c03800f8e0f0f8f

def z439 : W := mkw 0x0000001000401400 0x0000000010004014 0x0cf0807033f07cdb 0xdc0cf0807033f07c

def z440 : W := mkw 0xfffeff7deee455fa 0x46fffeff7deee455 0xfffffffffffc7fff 0xfffffffffffffc7f

def z441 : W := mkw 0xffedd00b700f6027 0x01ffedd00b700f60 0xfffff00ff00ff0f7 0xfbfffff00ff00ff0

def z442 : W := mkw 0xfffefff0d5d5fdca 0x62fffefff0d5d5fd 0xfffffff1ffffffff 0xfffffffff1ffffff

def z443 : W := mkw 0x0000000000000000 0x0000000000000000 0x030000000c000031 0x34030000000c0000

def z444 : W := mkw 0xfffeff60c48441ca 0x42fffeff60c48441 0xfffffff1cc0c032f 0xf3fffffff1cc0c03

def z445 : W := mkw 0x42830a060a0a0214 0x8042830a060a0a02 0xc30f0c0e0c0f8376 0x7ac30f0c0e0c0f83

def z446 : W := mkw 0x0000000000000000 0x0000000000000000 0x0008000000038052 0x5800080000000380

def z447 : W := mkw 0x00030a82010a8a04 0x8000030a82010a8a 0x030f0f800c0f8f3f 0x3e030f0f800c0f8f

def z448 : W := mkw 0x53f22f7084c015c8 0x4253f22f7084c015 0x03f00ff00cc00f09 0x0403f00ff00cc00f

def z449 : W := mkw 0xfbe0000daea00038 0x04fbe0000daea000 0xffb0000fff300060 0x61ffb0000fff3000

def z450 : W := mkw 0xac0cc00930012021 0x01ac0cc009300120 0x0c00000030000000 0x000c000000300000

def z451 : W := mkw 0x041881b01151bc80 0x20041881b01151bc 0x0cf803f033f38c49 0x440cf803f033f38c

def z452 : W := mkw 0xfffeef60000000c0 0x02fffeef60000000 0xfffffff033f000df 0xf6fffffff033f000

def z453 : W := mkw 0x428000040a000010 0x00428000040a0000 0xc300000e0c000020 0x20c300000e0c0000

def z454 : W := mkw 0xfffdd1bffffffcbf 0x25fffdd1bffffffc 0xfffff3fffffffcff 0xfffffff3fffffffc

def z455 : W := mkw 0xeebecb20000000c0 0x02eebecb20000000 0xfcbff38000000006 0xf2fcbff380000000

def z456 : W := mkw 0xfbe0345deee4553a 0x44fbe0345deee455 0xf340fc7fcccc7fbf 0xbdf340fc7fcccc7f

def z457 : W := mkw 0x1140001084c01408 0x001140001084c014 0x33408071ccc07cbb 0xbd33408071ccc07c

def z458 : W := mkw 0xb9400009a4800028 0x00b9400009a48000 0xff40000ffcc000f1 0xf5ff40000ffcc000

def z459 : W := mkw 0x001001b01151bc80 0x20001001b01151bc 0x00f003f033f3fcd9 0x0c00f003f033f3fc

def z460 : W := mkw 0x0418813010513480 0x2004188130105134 0x0c78807030f3f0d2 0xd80c78807030f3f0

def z461 : W := mkw 0xac0cd00970056023 0x01ac0cd009700560 0xfc00f00ff00070f0 0xf1fc00f00ff00070

def z462 : W := mkw 0x11403450c4c4550a 0x4011403450c4c455 0x33407c71cccc0f2d 0x2533407c71cccc0f

def z463 : W := mkw 0xac1dd13b705f74a7 0x21ac1dd13b705f74 0xfc7ff07ff0fff0f6 0xfbfc7ff07ff0fff0

def z464 : W := mkw 0x1140000084800008 0x0011400000848000 0x33000001cc000020 0x2133000001cc0000

def z465 : W := mkw 0xac0dc00b300b2025 0x01ac0dc00b300b20 0xcc0f000e300f8076 0x7acc0f000e300f80

def z466 : W := mkw 0x53c32ed68fca9f1c 0xc053c32ed68fca9f 0xc3cf0ffe0fcf8f7f 0x7ec3cf0ffe0fcf8f

def z467 : W := mkw 0x0010012000000080 0x0000100120000000 0x00f003f000000009 0x0000f003f0000000

def z468 : W := mkw 0x0418b5f05155fd82 0x600418b5f05155fd 0x0cf8fff033ffffdf 0xdc0cf8fff033ffff

def z469 : W := mkw 0xbd7eef60000000c0 0x02bd7eef60000000 0x3c7ffff00000000e 0x823c7ffff0000000

def z470 : W := mkw 0x040dd002500f6007 0x01040dd002500f60 0x300ff001c00ff0b6 0xbb300ff001c00ff0

def z471 : W := mkw 0x42830a860b0a8a14 0x8042830a860b0a8a 0xc08f038e03038c5b 0x5ec08f038e03038c

def z472 : W := mkw 0xfbe0000daea00038 0x04fbe0000daea000 0xf380000fcf000071 0x75f380000fcf0000

def z473 : W := mkw 0x42820a0000000000 0x0042820a00000000 0xc08f038000000000 0x42c08f0380000000

def z474 : W := mkw 0x0000245000401500 0x4000002450004015 0x00000c7000000f08 0x0000000c7000000f

def z475 : W := mkw 0xfbe77e4b600e4067 0x03fbe77e4b600e40 0xf3077c0fc00c0024 0x23f3077c0fc00c00

def z476 : W := mkw 0xac0dd00b700f6027 0x01ac0dd00b700f60 0xf00ff00fc00ff026 0x2bf00ff00fc00ff0

def z477 : W := mkw 0xbd4dd00bf48f602f 0x01bd4dd00bf48f60 0xff4ff00ffccff0f7 0xffff4ff00ffccff0

def z478 : W := mkw 0x1160000084a00008 0x041160000084a000 0x0070000000f00000 0x000070000000f000

def z479 : W := mkw 0x041fefe2010a8ac4 0x82041fefe2010a8a 0x000ffff0000f8f0e 0x0a000ffff0000f8f

def z480 : W := mkw 0xfffeef70004014c0 0x02fffeef70004014 0xfffffff000c07c9f 0xfefffffff000c07c

def z481 : W := mkw 0x0418b5f05155fd82 0x600418b5f05155fd 0x0008fff0000fff0e 0x080008fff0000fff

def z482 : W := mkw 0xbd7df56b700f60e7 0x03bd7df56b700f60 0xfc7ff07ff00ff0f6 0xfbfc7ff07ff00ff0

def z483 : W := mkw 0x57feef60000000c0 0x0257feef60000000 0x03fffff00000000f 0x0203fffff0000000

def z484 : W := mkw 0x0408800010012000 0x0004088000100120 0x000880000003f002 0x08000880000003f0

def z485 : W := mkw 0xfff8812daea000b8 0x04fff8812daea000 0xfff883fffff000fb 0xf5fff883fffff000

def z486 : W := mkw 0x42830a860b0a8a14 0x8042830a860b0a8a 0xc08f0f8e030f8f4e 0x4ac08f0f8e030f8f

def z487 : W := mkw 0x041981b2115bbc84 0x20041981b2115bbc 0xccff83fe33fffcff 0xfeccff83fe33fffc

def z488 : W := mkw 0x040cd00050056003 0x01040cd000500560 0x0000f00000007000 0x000000f000000070

def z489 : W := mkw 0x00011096cfcedf1e 0xc000011096cfcedf 0x0000000fcfcffff0 0x0d0000000fcfcfff

def z490 : W := mkw 0x0000000d2a200030 0x040000000d2a2000 0x0000000e33300040 0x000000000e333000

def z491 : W := mkw 0xffffffef7b0feaf7 0x83ffffffef7b0fea 0xffffffffff0fffff 0xffffffffffff0fff

def z492 : W := mkw 0x11403440c484410a 0x4011403440c48441 0x30007001c0000000 0x0130007001c00000

def z493 : W := mkw 0xfbe0000daea00038 0x04fbe0000daea000 0xcff0000e3ff00041 0x44cff0000e3ff000

def z494 : W := mkw 0xfffeef640a0000d0 0x02fffeef640a0000 0xfffffffe0f00007f 0xf6fffffffe0f0000

def z495 : W := mkw 0xfffeef69a4a000e8 0x06fffeef69a4a000 0xfffffff1f0f0008f 0xf3fffffff1f0f000

def z496 : W := mkw 0x040fda82510fea07 0x81040fda82510fea 0x000fff80000fff0e 0x0a000fff80000fff

def z497 : W := mkw 0x00003450c4c4550a 0x4000003450c4c455 0x0000fc71cccc7fbe 0x0d0000fc71cccc7f

def z498 : W := mkw 0x0000000000000000 0x0000000000000000 0x0c70000030f00080 0x800c70000030f000

def z499 : W := mkw 0x0000000000000000 0x0000000000000000 0x0040000000c00091 0x940040000000c000

def z500 : W := mkw 0x53e000048ea00018 0x0453e000048ea000 0x030000000c000000 0x00030000000c0000

def z501 : W := mkw 0xac3cc120000000c0 0x02ac3cc120000000 0x0c30000000000000 0x000c300000000000

def z502 : W := mkw 0xea875a0f6a0e4237 0x81ea875a0f6a0e42 0xf3077c0fcc0c0324 0x23f3077c0fcc0c03

def z503 : W := mkw 0xac1dc1ab311ba8a5 0x21ac1dc1ab311ba8 0xccbf038e33338040 0x42ccbf038e333380

def z504 : W := mkw 0xac0cd00040044002 0x00ac0cd000400440 0xfc0ff001c00c70b6 0xfbfc0ff001c00c70

def z505 : W := mkw 0x040dd002500f6007 0x01040dd002500f60 0x0c0ff000300ff0d6 0xda0c0ff000300ff0

def z506 : W := mkw 0x428000040a000010 0x00428000040a0000 0x038000000f000001 0x04038000000f0000

def z507 : W := mkw 0x11403450c4c4550a 0x4011403450c4c455 0x03400c71cccc7fb9 0x0d03400c71cccc7f

def z508 : W := mkw 0xffffeff61b5bbed4 0xa2ffffeff61b5bbe 0xfffffffe3fffffff 0xfefffffffe3fffff

def z509 : W := mkw 0x42830a860b0a8a14 0x8042830a860b0a8a 0xc38f038e0f038071 0x76c38f038e0f0380

def z510 : W := mkw 0x041891b05155fc82 0x20041891b05155fc 0x3cf8f3f1f3fffcff 0xfd3cf8f3f1f3fffc

def z511 : W := mkw 0x0408800010012000 0x0004088000100120 0x0cf8800033f3f0d3 0xdc0cf8800033f3f0

def z512 : W := mkw 0xac1cc1b01151bc80 0x20ac1cc1b01151bc 0xfcfff3f033f3fcdf 0xfefcfff3f033f3fc

def z513 : W := mkw 0xfbe0000daea00038 0x04fbe0000daea000 0xf300000ffff000f0 0x25f300000ffff000

def z514 : W := mkw 0x0000000000000000 0x0000000000000000 0x03000c000000000f 0x3003000c00000000

def z515 : W := mkw 0xeaa0000d2a200030 0x04eaa0000d2a2000 0xc000000e00000000 0x00c000000e000000

def z516 : W := mkw 0xfbe000048ea00018 0x04fbe000048ea000 0xfff000000ff00001 0xf4fff000000ff000

def z517 : W := mkw 0x115025f085d09d88 0x60115025f085d09d 0x03f00ff00ff00f09 0x0403f00ff00ff00f

def z518 : W := mkw 0x42820a840b008a10 0x8042820a840b008a 0x03880f800f038f5b 0x5c03880f800f038f

def z519 : W := mkw 0x0418812010112080 0x2004188120101120 0x0c30000030300000 0x000c300000303000

def z520 : W := mkw 0xfbe67e40c484414a 0x42fbe67e40c48441 0xf3077c01cc0c0324 0x23f3077c01cc0c03

def z521 : W := mkw 0x0001101bf4cf752f 0x410001101bf4cf75 0x0000000ffccffff0 0x0d0000000ffccfff

def z522 : W := mkw 0x53c30a868f8a8a1c 0x8053c30a868f8a8a 0xf3cf0f8fcfcf8fff 0xfff3cf0f8fcfcf8f

def z523 : W := mkw 0x1140000084800008 0x0011400000848000 0x33400c01cccc0fbf 0xbd33400c01cccc0f

def z524 : W := mkw 0x11403450c4c4550a 0x4011403450c4c455 0x0340fc700ccc7f0f 0x0c0340fc700ccc7f

def z525 : W := mkw 0x00066e4000000040 0x0200066e40000000 0x00077c0000000004 0x0200077c00000000

def z526 : W := mkw 0xea830a8f2b0a8a34 0x80ea830a8f2b0a8a 0xff8f0f8fff0f8fff 0xffff8f0f8fff0f8f

def z527 : W := mkw 0xfbe76ec60b0a8a54 0x82fbe76ec60b0a8a 0xf38f7f8e0f0f8f7f 0x7ef38f7f8e0f0f8f

def z528 : W := mkw 0x0000000000000000 0x0000000000000000 0x004080700000000b 0x9000408070000000

def z529 : W := mkw 0x11403450c4c4550a 0x4011403450c4c455 0x33007c01cccc7fb4 0x2d33007c01cccc7f

def z530 : W := mkw 0xfffeef7084c015c8 0x42fffeef7084c015 0xfffffff00cc00f0f 0xf6fffffff00cc00f

def z531 : W := mkw 0x041891b0d5d5fd8a 0x60041891b0d5d5fd 0x0cf883f1fffffffb 0xdd0cf883f1ffffff

def z532 : W := mkw 0x11413452c4ce550e 0x4011413452c4ce55 0xf34ffc7fcccfffff 0xfff34ffc7fcccfff

def z533 : W := mkw 0xfffce56daea000f8 0x06fffce56daea000 0xfff0f07ffff000f1 0xf5fff0f07ffff000

def z534 : W := mkw 0x0000001000401400 0x0000000010004014 0x0040807000c07080 0x800040807000c070

def z535 : W := mkw 0x0000000084800008 0x0000000000848000 0x00000001ccc000b0 0x0500000001ccc000

def z536 : W := mkw 0x041881b01151bc80 0x20041881b01151bc 0x0cf883f00003fc0b 0xd80cf883f00003fc

def z537 : W := mkw 0xac0dd00b700f6027 0x01ac0dd00b700f60 0x3c00f00ff00ff0f0 0x893c00f00ff00ff0

def z538 : W := mkw 0x0418812000000080 0x0004188120000000 0x0cb8038000000000 0x400cb80380000000

def z539 : W := mkw 0x42830a860b0a8a14 0x8042830a860b0a8a 0xc08f038e030f8076 0x7ac08f038e030f80

def z540 : W := mkw 0x041ecb20000000c0 0x02041ecb20000000 0x000f038000000000 0x02000f0380000000

def z541 : W := mkw 0x53e03454cee4551a 0x4453e03454cee455 0x33f0fc71cffc7fbf 0xbd33f0fc71cffc7f

def z542 : W := mkw 0x42820a840b008a10 0x8042820a840b008a 0xc38f0f800f000f0f 0x76c38f0f800f000f

def z543 : W := mkw 0x0408800010012000 0x0004088000100120 0x0c08000030038040 0x400c080000300380

def z544 : W := mkw 0xffedd00ffeaf603f 0x05ffedd00ffeaf60 0xff0ff00ffc0ff0f6 0xfbff0ff00ffc0ff0

def z545 : W := mkw 0xeeadd00f7a2f6037 0x05eeadd00f7a2f60 0xfcbff00ff33ff0f6 0xfbfcbff00ff33ff0

def z546 : W := mkw 0x0000100040044002 0x0000001000400440 0x30007001c00c0024 0x2130007001c00c00

def z547 : W := mkw 0x469a8b2000000080 0x00469a8b20000000 0xcfff8ff00000000f 0xf2cfff8ff0000000

def z548 : W := mkw 0x041881b01151bc80 0x20041881b01151bc 0x00f883f003f3fc0b 0x0c00f883f003f3fc

def z549 : W := mkw 0xfffeef70105134c0 0x22fffeef70105134 0xfffffff030f0708f 0xf2fffffff030f070

def z550 : W := mkw 0x11403440c484410a 0x4011403440c48441 0x3340fc71cc0c032f 0xb13340fc71cc0c03

def z551 : W := mkw 0xfffeff60400440c2 0x02fffeff60400440 0xfffffff1c00c70bf 0xfbfffffff1c00c70

def z552 : W := mkw 0xb945745be4ce552f 0x41b945745be4ce55 0xf347fc7fcccc7fbf 0xbff347fc7fcccc7f

def z553 : W := mkw 0x53f22f60000000c0 0x0253f22f60000000 0xc3ff0ff00000000f 0x72c3ff0ff0000000

def z554 : W := mkw 0xffffff62500f60c7 0x03ffffff62500f60 0xfffffff0000ff00f 0xfafffffff0000ff0

def z555 : W := mkw 0x000000048ea00018 0x04000000048ea000 0x000000000ff00000 0x04000000000ff000

def z556 : W := mkw 0x42830a960b4a9e14 0x8042830a960b4a9e 0xc3cf8ffe0fcfffff 0xfec3cf8ffe0fcfff

def z557 : W := mkw 0x0418813010513480 0x2004188130105134 0x0000807000007000 0x0000008070000070

def z558 : W := mkw 0x0000000010012000 0x0000000000100120 0x000000003003f0d0 0x08000000003003f0

def z559 : W := mkw 0x1140244000000000 0x0011402440000000 0x3040f07000000000 0x803040f070000000

def z560 : W := mkw 0xeebecb20000000c0 0x02eebecb20000000 0xcfbf0f800000000f 0x72cfbf0f80000000

def z561 : W := mkw 0x0000345040445502 0x4000003450404455 0x0300fc700c0c7f3f 0x3c0300fc700c0c7f

def z562 : W := mkw 0x0000000000000000 0x0000000000000000 0x0080000003000051 0x5400800000030000

def z563 : W := mkw 0x1140245000401400 0x0011402450004014 0x3340fc7000c07c9f 0xbc3340fc7000c07c

def z564 : W := mkw 0xac1cd1b97155fca3 0x21ac1cd1b97155fc 0x3cf8f3f1f3f3fcdb 0xdd3cf8f3f1f3f3fc

def z565 : W := mkw 0xfbe0001daee01438 0x04fbe0001daee014 0xfff0807ffff07cfb 0xfdfff0807ffff07c

def z566 : W := mkw 0xbd4df44bf48f612f 0x41bd4df44bf48f61 0xff0ffc0ffc0ff3f6 0xfbff0ffc0ffc0ff3

def z567 : W := mkw 0x11433ed2c5cedf0e 0xc011433ed2c5cedf 0x334ffff1cccfffbf 0xbf334ffff1cccfff

def z568 : W := mkw 0x00030a82010a8a04 0x8000030a82010a8a 0x008f0f80030f8f5f 0x5e008f0f80030f8f

def z569 : W := mkw 0xee8eca0000000000 0x00ee8eca00000000 0xff8fff800000000f 0xf2ff8fff80000000

def z570 : W := mkw 0x1140344040044002 0x0011403440400440 0x3340fc71c00c70bf 0xb93340fc71c00c70

def z571 : W := mkw 0xeaa0000d2a200030 0x04eaa0000d2a2000 0xccf0000e33f000d1 0xd4ccf0000e33f000

def z572 : W := mkw 0xffffff6ffeaf60ff 0x07ffffff6ffeaf60 0xfffffffffffff0ff 0xfffffffffffffff0

def z573 : W := mkw 0x0000000000000000 0x0000000000000000 0x3000f00000000006 0xb03000f000000000

def z574 : W := mkw 0xfffeff70404455c2 0x42fffeff70404455 0xfffffff0000c7f0f 0xfafffffff0000c7f

def z575 : W := mkw 0x0418813000401480 0x0004188130004014 0x0cf883f000c07c9b 0xdc0cf883f000c07c

def z576 : W := mkw 0x11403450c4c4550a 0x4011403450c4c455 0x3040f071c0cc70b6 0xb93040f071c0cc70

def z577 : W := mkw 0x53e22e4000000040 0x0253e22e40000000 0x03000c0000000000 0x0003000c00000000

def z578 : W := mkw 0x0418813010513480 0x2004188130105134 0x0cf0807033f070d1 0xd40cf0807033f070

def z579 : W := mkw 0x040dd002500f6007 0x01040dd002500f60 0xc00ff00e000ff076 0x7ac00ff00e000ff0

def z580 : W := mkw 0x1558b5f0d5d5fd8a 0x601558b5f0d5d5fd 0x3cf8f3f1f3f3fcdb 0xdd3cf8f3f1f3f3fc

def z581 : W := mkw 0x0000101040445402 0x0000001010404454 0x3040f071c0cc7cbf 0xbd3040f071c0cc7c

def z582 : W := mkw 0xac0dd09b715ffc27 0x21ac0dd09b715ffc 0xfc0ff00ff3fffcf6 0xfffc0ff00ff3fffc

def z583 : W := mkw 0x0001108f7b0fea37 0x810001108f7b0fea 0x0000000fff0ffff0 0x0d0000000fff0fff

def z584 : W := mkw 0xfbe0008dafa08838 0x04fbe0008dafa088 0xfff8038ffff38cfb 0xfdfff8038ffff38c

def z585 : W := mkw 0x0409900b700f6027 0x010409900b700f60 0x0c08800ff00ff0f2 0xd90c08800ff00ff0

def z586 : W := mkw 0x42820a840b008a10 0x8042820a840b008a 0xc3800f8e0f000f79 0x74c3800f8e0f000f

def z587 : W := mkw 0x0418812010012080 0x0004188120100120 0x0cf883f03003f0db 0xd80cf883f03003f0

def z588 : W := mkw 0x1140345deee4553a 0x441140345deee455 0x3340fc7ffffc7fff 0xbd3340fc7ffffc7f

def z589 : W := mkw 0x1558b5f0d5d5fd8a 0x601558b5f0d5d5fd 0x3348fff1cccfffbf 0xbd3348fff1cccfff

def z590 : W := mkw 0xa820000920200020 0x04a8200009202000 0x0c30000030300000 0x000c300000303000

def z591 : W := mkw 0xbd4df44b700f6027 0x01bd4df44b700f60 0xff4ffc7ff00ff0ff 0xfbff4ffc7ff00ff0

def z592 : W := mkw 0x11403450c4c4550a 0x4011403450c4c455 0x3040fc71c0cc7f8e 0x893040fc71c0cc7f

def z593 : W := mkw 0xbd7881b9b5f1bca8 0x24bd7881b9b5f1bc 0x3cf883f1f3f3fcdb 0xdd3cf883f1f3f3fc

def z594 : W := mkw 0xfbf22f6daea000f8 0x06fbf22f6daea000 0xfff00ffffff000f9 0xf5fff00ffffff000

def z595 : W := mkw 0x469b8bb61b5bbe94 0xa0469b8bb61b5bbe 0xc38f8ffe0f0fff7f 0x7ec38f8ffe0f0fff

def z596 : W := mkw 0x42830a961b5bbe14 0xa042830a961b5bbe 0xc38f0f8e3fffffff 0x7ec38f0f8e3fffff

def z597 : W := mkw 0xfbe0000daea00038 0x04fbe0000daea000 0xfff0000fcc000021 0xf1fff0000fcc0000

def z598 : W := mkw 0xa805400b200a0025 0x01a805400b200a00 0xc007000e00000000 0x02c007000e000000

def z599 : W := mkw 0xfff8813dbef134b8 0x24fff8813dbef134 0xfff0807ffff070f1 0xf5fff0807ffff070

def z600 : W := mkw 0xac0cc00000000000 0x00ac0cc000000000 0xcc0f000000000000 0x42cc0f0000000000

def z601 : W := mkw 0x000100860b0a8a14 0x80000100860b0a8a 0x03000c0e0f0f8f7f 0x3c03000c0e0f0f8f

def z602 : W := mkw 0x53f001b48ff09c98 0x2453f001b48ff09c 0x03f003f00ff00c09 0x0403f003f00ff00c

def z603 : W := mkw 0xfbe0344deea4413a 0x44fbe0344deea441 0xf3007c0fcc0c0324 0x21f3007c0fcc0c03

def z604 : W := mkw 0xbd7ce5f01151bcc0 0x22bd7ce5f01151bc 0x3cf8f3f033f3fcdb 0xdc3cf8f3f033f3fc

def z605 : W := mkw 0x00001010c4c4550a 0x4000001010c4c455 0x00000001c0c07080 0x0100000001c0c070

def z606 : W := mkw 0x42830a860b0a8a14 0x8042830a860b0a8a 0xc38f0f8e0f038f49 0x46c38f0f8e0f038f

def z607 : W := mkw 0x11403440c484410a 0x4011403440c48441 0x3300fc01cc0c73b6 0xb93300fc01cc0c73

def z608 : W := mkw 0xfbe30a8fafaa8a3c 0x84fbe30a8fafaa8a 0xf38f0f8fcf0f8f7f 0x7ff38f0f8fcf0f8f

def z609 : W := mkw 0x0000100040044002 0x0000001000400440 0x3300fc01cc0c7fbf 0xbd3300fc01cc0c7f

def z610 : W := mkw 0x0000345040445502 0x4000003450404455 0x0040fc7000cc7f9f 0x9c0040fc7000cc7f

def z611 : W := mkw 0x0000009001509c00 0x200000009001509c 0x0000000003f00c00 0x040000000003f00c

def z612 : W := mkw 0xeaa64a0000000040 0x02eaa64a00000000 0xc007000000000000 0x02c0070000000000

def z613 : W := mkw 0xfbe33edfefeedf3e 0xc4fbe33edfefeedf 0xffffffffffffffff 0xffffffffffffffff

def z614 : W := mkw 0xac0dc00b300b2025 0x01ac0dc00b300b20 0xcc0f800e3003f0d2 0xdacc0f800e3003f0

def z615 : W := mkw 0xeaa0000d2a200030 0x04eaa0000d2a2000 0xcfb0000e3f300071 0x74cfb0000e3f3000

def z616 : W := mkw 0xee8fda8f7b0fea37 0x81ee8fda8f7b0fea 0xfc8ff38ff30ff0f6 0xfbfc8ff38ff30ff0

def z617 : W := mkw 0xfffeeff001509cc0 0x22fffeeff001509c 0xfffffff003f00c0f 0xf6fffffff003f00c

def z618 : W := mkw 0x469b8bb61b5bbe94 0xa0469b8bb61b5bbe 0xccff83fe33f3fcdb 0xdeccff83fe33f3fc

def z619 : W := mkw 0x57f881b49ff1bc98 0x2457f881b49ff1bc 0x0ff883f03ff3fcdb 0xdc0ff883f03ff3fc

def z620 : W := mkw 0xfff881adbfb1a8b8 0x24fff881adbfb1a8 0xfff8038ffff380f1 0xf5fff8038ffff380

def z621 : W := mkw 0x0000008001008800 0x0000000080010088 0x0008038000038c0a 0x080008038000038c

def z622 : W := mkw 0x0000000000000000 0x0000000000000000 0x30000001c00000b0 0xb130000001c00000

def z623 : W := mkw 0x42830a860b0a8a14 0x8042830a860b0a8a 0xc38f0f8e0303804f 0x72c38f0f8e030380

def z624 : W := mkw 0xbd6cd009f4a5602b 0x05bd6cd009f4a560 0x3c70f001f0f07080 0x813c70f001f0f070

def z625 : W := mkw 0xfbe0000daea00038 0x04fbe0000daea000 0xff70000ffcf000a0 0xa1ff70000ffcf000

def z626 : W := mkw 0x000000801111a800 0x20000000801111a8 0x0000000033338040 0x0000000000333380

def z627 : W := mkw 0x11403450c4c4550a 0x4011403450c4c455 0x3040f071c0c07c9b 0x9d3040f071c0c07c

def z628 : W := mkw 0x42820a0000000000 0x0042820a00000000 0xc38f0f800c0c0f3f 0x7ec38f0f800c0c0f

def z629 : W := mkw 0x469a8bb01151bc80 0x20469a8bb01151bc 0xcfff8ff033f3fcdf 0xfecfff8ff033f3fc

def z630 : W := mkw 0x469881b41b51bc90 0x20469881b41b51bc 0xcff883fe3ff3fcfb 0xfccff883fe3ff3fc

def z631 : W := mkw 0xffffefe2010a8ac4 0x82ffffefe2010a8a 0xfffffff0000f8f0f 0xfafffffff0000f8f

def z632 : W := mkw 0x0000100970056023 0x0100001009700560 0x00000001f0007080 0x0100000001f00070

def z633 : W := mkw 0xfbe0100deea4403a 0x04fbe0100deea440 0xfff0f00ffffc70f7 0xfdfff0f00ffffc70

def z634 : W := mkw 0x041881b01151bc80 0x20041881b01151bc 0x0c7883f030f3fc8a 0x880c7883f030f3fc

def z635 : W := mkw 0xeeb881bd3b71bcb0 0x24eeb881bd3b71bc 0xccf883fe33f3fcdb 0xdcccf883fe33f3fc

def z636 : W := mkw 0x00020a8001008a00 0x8000020a8001008a 0x00000f8000000f08 0x0000000f8000000f

def z637 : W := mkw 0x041881b001509c80 0x20041881b001509c 0x0cf883f003f00c0b 0xd40cf883f003f00c

def z638 : W := mkw 0x0000008001008800 0x0000000080010088 0x0cf8038033f38cdb 0xdc0cf8038033f38c

def z639 : W := mkw 0xac0dd002500f6007 0x01ac0dd002500f60 0xfc0ff000000ff006 0xfafc0ff000000ff0

def z640 : W := mkw 0x42830a060a0a0214 0x8042830a060a0a02 0xc007000e00000000 0x02c007000e000000

def z641 : W := mkw 0xb9403459e4c4552a 0x40b9403459e4c455 0xff40fc7ffccc7fff 0xfdff40fc7ffccc7f

def z642 : W := mkw 0x0408900050056002 0x0004089000500560 0x3c08f001f00ff0f6 0xf93c08f001f00ff0

def z643 : W := mkw 0x114034d0c5c4dd0a 0x40114034d0c5c4dd 0x33c8fff1cfcfffff 0xfd33c8fff1cfcfff

def z644 : W := mkw 0xac0dd08b710fe827 0x01ac0dd08b710fe8 0xfc8ff38ff30ffcff 0xfffc8ff38ff30ffc

def z645 : W := mkw 0xffffef660a0a02d4 0x82ffffef660a0a02 0xfffffffe0c0c032f 0xf2fffffffe0c0c03

def z646 : W := mkw 0x0000000000000000 0x0000000000000000 0x0c000000300000d0 0xd00c000000300000

def z647 : W := mkw 0xfbe0000daea00038 0x04fbe0000daea000 0xf340000fccc000b1 0xb5f340000fccc000

def z648 : W := mkw 0x001001b001509c80 0x20001001b001509c 0x00f083f003f07c9b 0x9c00f083f003f07c

def z649 : W := mkw 0xffffff7bf4cf75ef 0x43ffffff7bf4cf75 0xfffffffffccfffff 0xfffffffffffccfff

def z650 : W := mkw 0x42830a860b0a8a14 0x8042830a860b0a8a 0xc38f0f8e0f0f8364 0x62c38f0f8e0f0f83

def z651 : W := mkw 0x428000040a000010 0x00428000040a0000 0xcff0000e3ff000f1 0xf4cff0000e3ff000

def z652 : W := mkw 0x0000100040044002 0x0000001000400440 0x0000f000000c7006 0x080000f000000c70

def z653 : W := mkw 0x000000901151bc00 0x20000000901151bc 0x0040807033f3fcdb 0x9c0040807033f3fc

def z654 : W := mkw 0x1140245084c01508 0x401140245084c015 0x03400c700ccc0f3f 0x3c03400c700ccc0f

def z655 : W := mkw 0xfbe20a0000000000 0x00fbe20a00000000 0xffff0f800000000f 0xf2ffff0f80000000

def z656 : W := mkw 0x11403450c4c4550a 0x4011403450c4c455 0x3040f071cccc7fb0 0x8d3040f071cccc7f

def z657 : W := mkw 0xeebfdb2b700f60e7 0x03eebfdb2b700f60 0xfcbff38ff00ff0f6 0xfbfcbff38ff00ff0

def z658 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000033f000d0 0x040000000033f000

def z659 : W := mkw 0x041881a01111a880 0x20041881a01111a8 0x0cb8038033338c5b 0x5c0cb8038033338c

def z660 : W := mkw 0x041881b01151bc80 0x20041881b01151bc 0x0cb8038033f3fcd0 0x4c0cb8038033f3fc

def z661 : W := mkw 0x00000009a4a00028 0x0400000009a4a000 0x00000001f0f00080 0x0100000001f0f000

def z662 : W := mkw 0x42a000040a200010 0x0442a000040a2000 0x00b0000003300000 0x0000b00000033000

def z663 : W := mkw 0x0000001084c01508 0x400000001084c015 0x000000000cc00f00 0x04000000000cc00f

def z664 : W := mkw 0xb960000000000000 0x00b9600000000000 0x3c70000000000000 0x803c700000000000

def z665 : W := mkw 0x42830a8fafaa8a3c 0x8442830a8fafaa8a 0xc38f0f8fffff8fff 0x7fc38f0f8fffff8f

def z666 : W := mkw 0xac0dd00ffeaf603f 0x05ac0dd00ffeaf60 0xfc0ff00ffffff0f6 0xfffc0ff00ffffff0

def z667 : W := mkw 0x53f22ff001509cc0 0x2253f22ff001509c 0x03f00ff003f00c09 0x0403f00ff003f00c

def z668 : W := mkw 0x53c33e46ce8e431e 0xc053c33e46ce8e43 0xf3077c0fcc0c0324 0x23f3077c0fcc0c03

def z669 : W := mkw 0xfffeefe0010088c0 0x02fffeefe0010088 0xfffffff003038c5f 0xfefffffff003038c

def z670 : W := mkw 0x53e30a868faa8a1c 0x8453e30a868faa8a 0xc3ff0f8e0fff8f7f 0x7ec3ff0f8e0fff8f

def z671 : W := mkw 0xfff8b5fdfff5fdba 0x64fff8b5fdfff5fd 0xfff8ffffffffffff 0xfdfff8ffffffffff

def z672 : W := mkw 0xfbe0000daea00038 0x04fbe0000daea000 0xff00000ffc0000f0 0xf1ff00000ffc0000

def z673 : W := mkw 0x0000009001409c00 0x000000009001409c 0x00c883f003c3fcdb 0xdc00c883f003c3fc

def z674 : W := mkw 0xffedc00fbeab203d 0x05ffedc00fbeab20 0xffff000ffff380f1 0xf7ffff000ffff380

def z675 : W := mkw 0x42820a040a000210 0x8042820a040a0002 0x03000c000c000300 0x0003000c000c0003

def z676 : W := mkw 0xbd7ce560000000c0 0x02bd7ce560000000 0xfc7ff07000000006 0xf2fc7ff070000000

def z677 : W := mkw 0x53e000048ea00018 0x0453e000048ea000 0xc3f0000e0ff00071 0x74c3f0000e0ff000

def z678 : W := mkw 0x001001b001509c80 0x20001001b001509c 0x000003f000000c08 0x00000003f000000c

def z679 : W := mkw 0x155881b095d1bc88 0x20155881b095d1bc 0x3ff883f1fff3fcfb 0xfd3ff883f1fff3fc

def z680 : W := mkw 0xac0dc00b300b2025 0x01ac0dc00b300b20 0xfc0ff00e30038046 0xf2fc0ff00e300380

def z681 : W := mkw 0xfffffff6cfcedfde 0xc2fffffff6cfcedf 0xffffffffcfcfffff 0xffffffffffcfcfff

def z682 : W := mkw 0x42820a8001008800 0x0042820a80010088 0xc38f0f8003038c5f 0x7ec38f0f8003038c

def z683 : W := mkw 0xfbe0009dbff1bc38 0x24fbe0009dbff1bc 0xfff0000ffff3fcf1 0xfdfff0000ffff3fc

def z684 : W := mkw 0xea875a8f6b0eca37 0x81ea875a8f6b0eca 0xf38f7f8fcf0f8f7f 0x7ff38f7f8fcf0f8f

def z685 : W := mkw 0x041881b01151bc80 0x20041881b01151bc 0x0cb883f03333fc4a 0x480cb883f03333fc

def z686 : W := mkw 0xb945744be48e412f 0x41b945744be48e41 0xf3077c0fcc0c0324 0x23f3077c0fcc0c03

def z687 : W := mkw 0x041881b01151bc80 0x20041881b01151bc 0x008883f00303fc5b 0x5c008883f00303fc

def z688 : W := mkw 0x0418812000000080 0x0004188120000000 0x0cf883f033f000db 0xd40cf883f033f000

def z689 : W := mkw 0xfbe66e4000000040 0x02fbe66e40000000 0xfff77c0000000005 0xf2fff77c00000000

def z690 : W := mkw 0x42830a060a0a0214 0x8042830a060a0a02 0xc3870c0e0f0c0375 0x76c3870c0e0f0c03

def z691 : W := mkw 0xfffeef60000000c0 0x02fffeef60000000 0x3ff0fff000000009 0x803ff0fff0000000

def z692 : W := mkw 0xfbe20a8dafa08a38 0x84fbe20a8dafa08a 0xfff00f8ffff00ff9 0xf5fff00f8ffff00f

def z693 : W := mkw 0x001001b001509c80 0x20001001b001509c 0x0cf003f033f00cd9 0xd40cf003f033f00c

def z694 : W := mkw 0x114034d0d5d5fd0a 0x60114034d0d5d5fd 0x3340fc71ffffffff 0xbd3340fc71ffffff

def z695 : W := mkw 0x0001000b300b2025 0x010001000b300b20 0x0000000e30038040 0x000000000e300380

def z696 : W := mkw 0x1548b450d4c5750a 0x401548b450d4c575 0x3f48fc71fccfffff 0xfd3f48fc71fccfff

def z697 : W := mkw 0xa800100960044022 0x00a8001009600440 0xfc00f00ff00c70f6 0xf9fc00f00ff00c70

def z698 : W := mkw 0xb9600009a4a00028 0x04b9600009a4a000 0xfc70000ff0f000f0 0xf1fc70000ff0f000

def z699 : W := mkw 0x0001100b700f6027 0x010001100b700f60 0xc00f000ff00ff0f6 0x7bc00f000ff00ff0

def z700 : W := mkw 0x42830a02000a0004 0x0042830a02000a00 0xc38f0f8e000f807f 0x7ac38f0f8e000f80

def z701 : W := mkw 0x00010002000a0004 0x0000010002000a00 0xc00f000e00038040 0x42c00f000e000380

def z702 : W := mkw 0x53e000048ea00018 0x0453e000048ea000 0x33f00001cff000b1 0xb533f00001cff000

def z703 : W := mkw 0x0000100040044002 0x0000001000400440 0x00000001c00c70b0 0x0900000001c00c70

def z704 : W := mkw 0x1558a5f095d1bd88 0x601558a5f095d1bd 0x0ff88ff03ff3ffdb 0xdc0ff88ff03ff3ff

def z705 : W := mkw 0xfbe0245daee01538 0x44fbe0245daee015 0xfff00c7ffff00ff9 0xf5fff00c7ffff00f

def z706 : W := mkw 0x0000000000000000 0x0000000000000000 0xc000000e00000070 0x70c000000e000000

def z707 : W := mkw 0x469eef640a0000d0 0x02469eef640a0000 0xc38ffffe0f00007f 0x76c38ffffe0f0000

def z708 : W := mkw 0xb9630a8ba5aa8a2c 0x84b9630a8ba5aa8a 0x3c7f0f81f0ff8f8e 0x8b3c7f0f81f0ff8f

def z709 : W := mkw 0x041991b2515ffc87 0x21041991b2515ffc 0x000883f0000ffc0a 0x08000883f0000ffc

def z710 : W := mkw 0x469b8b361a5b3694 0xa0469b8b361a5b36 0xcf778c7e3cfc73a4 0xa2cf778c7e3cfc73

def z711 : W := mkw 0xac1cc129200000a0 0x00ac1cc129200000 0xfcfff3fff3f000ff 0xf7fcfff3fff3f000

def z712 : W := mkw 0xac0dd00b700f6027 0x01ac0dd00b700f60 0xfc0ff00ff3fff0f6 0xfffc0ff00ff3fff0

def z713 : W := mkw 0xfffeef6daea000f8 0x06fffeef6daea000 0xffffffffff30006f 0xf3ffffffffff3000

def z714 : W := mkw 0x42830a02000a0004 0x0042830a02000a00 0xc38f0f8e0c0f8f7f 0x7ec38f0f8e0c0f8f

def z715 : W := mkw 0xbd4de45bb4cb352d 0x41bd4de45bb4cb35 0xcf4f0c7e3cc38f49 0x46cf4f0c7e3cc38f

def z716 : W := mkw 0xfbe0000daea00038 0x04fbe0000daea000 0xffb0000ffff000f0 0x65ffb0000ffff000

def z717 : W := mkw 0x11403450c4c4550a 0x4011403450c4c455 0x3300fc71cccc7fbe 0x2d3300fc71cccc7f

def z718 : W := mkw 0x53c11096cfcedf1e 0xc053c11096cfcedf 0xf3c0000fcfcffff1 0xfdf3c0000fcfcfff

def z719 : W := mkw 0xfbe0000daea00038 0x04fbe0000daea000 0xfff00c0ffff00ff9 0xf5fff00c0ffff00f

def z720 : W := mkw 0xfbe0000daea00038 0x04fbe0000daea000 0xfff0800ffff070f3 0xfdfff0800ffff070

def z721 : W := mkw 0xfffeef6daea000f8 0x06fffeef6daea000 0xfffffffffc0000ff 0xf3fffffffffc0000

def z722 : W := mkw 0x041cc1b01151bc80 0x20041cc1b01151bc 0x0cfff3f033f3fcdf 0xde0cfff3f033f3fc

def z723 : W := mkw 0x0001109fefeedf3e 0xc40001109fefeedf 0x0000000ffffffff0 0x0d0000000fffffff

def z724 : W := mkw 0xfbe20a0daea00038 0x04fbe20a0daea000 0xfff00f8ffff000f9 0xf5fff00f8ffff000

def z725 : W := mkw 0x0001109f7b5ffe37 0xa10001109f7b5ffe 0x0000000ffffffff0 0x0d0000000fffffff

def z726 : W := mkw 0x53e0000daea00038 0x0453e0000daea000 0x0ff0000ffff000f1 0xd50ff0000ffff000

def z727 : W := mkw 0xee9fcbaf3b1baab5 0xa1ee9fcbaf3b1baa 0xccbf038e33338040 0x42ccbf038e333380

def z728 : W := mkw 0x53f22f60000000c0 0x0253f22f60000000 0xf3fffff00000000f 0xf2f3fffff0000000

def z729 : W := mkw 0xb9600009a4a00028 0x04b9600009a4a000 0xfcf0000ff3f000f1 0xf5fcf0000ff3f000

def z730 : W := mkw 0xfffeef648ea000d8 0x06fffeef648ea000 0xfffffff00c00000f 0xf2fffffff00c0000

def z731 : W := mkw 0xfffeef60000000c0 0x02fffeef60000000 0xfffffff0000c0f0f 0xfafffffff0000c0f

def z732 : W := mkw 0x041eef60000000c0 0x02041eef60000000 0x0c7ffff00000000e 0x820c7ffff0000000

def z733 : W := mkw 0xfffeef60000000c0 0x02fffeef60000000 0xfcfffff00000000e 0xc2fcfffff0000000

def z734 : W := mkw 0x041eef6daea000f8 0x06041eef6daea000 0x000ffffffff000fe 0x07000ffffffff000

def z735 : W := mkw 0xfbe33e4feeae433e 0xc4fbe33e4feeae43 0xf3077c0fcc0c0324 0x23f3077c0fcc0c03

def z736 : W := mkw 0xfbe66ed01151bc40 0x22fbe66ed01151bc 0xf3077c0033f3fcd4 0x2ef3077c0033f3fc

def z737 : W := mkw 0xac0dd00b700f6027 0x01ac0dd00b700f60 0xfc0ff00ff003f0c6 0xf3fc0ff00ff003f0

def z738 : W := mkw 0x53c33ed6cfcedf1e 0xc053c33ed6cfcedf 0xf0cff3ffc3c3f0c0 0xc3f0cff3ffc3c3f0

def z739 : W := mkw 0xfbe64a0daea00078 0x06fbe64a0daea000 0xfff7000ffff000f1 0xf7fff7000ffff000

def z740 : W := mkw 0x469eef60000000c0 0x02469eef60000000 0x038ffff00000000f 0x02038ffff0000000

def z741 : W := mkw 0xac0dd00b700f6027 0x01ac0dd00b700f60 0xfcbff00ff33ff0f6 0xfbfcbff00ff33ff0

def z742 : W := mkw 0x155eef60000000c0 0x02155eef60000000 0x034ffff00000000f 0x02034ffff0000000

def z743 : W := mkw 0x42830a860b0a8a14 0x8042830a860b0a8a 0xc38f8f8e0f0fffff 0xfec38f8f8e0f0fff

def z744 : W := mkw 0x155eef60000000c0 0x02155eef60000000 0x330ffff00000000e 0x22330ffff0000000

def z745 : W := mkw 0xa801109b715ffc27 0x21a801109b715ffc 0xfcf0000ff3fffcf1 0xfdfcf0000ff3fffc

def z746 : W := mkw 0x041eef60000000c0 0x02041eef60000000 0x0cfffff033f000df 0xd60cfffff033f000

def z747 : W := mkw 0xfffeef6daea000f8 0x06fffeef6daea000 0xfffffffffffc0fff 0xfffffffffffffc0f

def z748 : W := mkw 0x57feef648ea000d8 0x0657feef648ea000 0x03fffff00ff0000f 0x0603fffff00ff000

def z749 : W := mkw 0xac1dd12b701f60a7 0x21ac1dd12b701f60 0xfc3ff00ff03ff0f6 0xfbfc3ff00ff03ff0

def z750 : W := mkw 0xfbe0000daea00038 0x04fbe0000daea000 0xfff8038ffff000fb 0xf5fff8038ffff000

def z751 : W := mkw 0x041eef60000000c0 0x02041eef60000000 0x00fffff00000000f 0x0200fffff0000000

def z752 : W := mkw 0xfbe22e4daea00038 0x04fbe22e4daea000 0xfffffffffff000ff 0xf7fffffffffff000

def z753 : W := mkw 0x57feef60000000c0 0x0257feef60000000 0xc3fffff00000000f 0x72c3fffff0000000

def z754 : W := mkw 0x0000000920000020 0x0000000009200000 0x0cf0000ff3f000f1 0xd50cf0000ff3f000

def z755 : W := mkw 0x11403450c4c4550a 0x4011403450c4c455 0x3340fc71cccc7fae 0xa93340fc71cccc7f

def z756 : W := mkw 0xfffeef648ea000d8 0x06fffeef648ea000 0xfffffffe0ff0007f 0xf6fffffffe0ff000

def z757 : W := mkw 0x53f33f6b700f60e7 0x0353f33f6b700f60 0x03f00ffff00ff0f9 0x0903f00ffff00ff0

def z758 : W := mkw 0xac1eef60000000c0 0x02ac1eef60000000 0xfcfffff00000000f 0xf2fcfffff0000000

def z759 : W := mkw 0x11403450c4c4550a 0x4011403450c4c455 0x3340fc71fffc7fff 0xbd3340fc71fffc7f

def z760 : W := mkw 0xfbf66f60000000c0 0x02fbf66f60000000 0xfff77ff00000000d 0xf2fff77ff0000000

def z761 : W := mkw 0x42821a10c4c4550a 0x4042821a10c4c455 0xc38f0f81cccc7fbf 0x7fc38f0f81cccc7f

def z762 : W := mkw 0xfbe77e4feeae407f 0x07fbe77e4feeae40 0xf3077c0fcc0c0024 0x23f3077c0fcc0c00

def z763 : W := mkw 0xfbe0000daea00038 0x04fbe0000daea000 0xfff8000ffff380f3 0xfdfff8000ffff380

def z764 : W := mkw 0x42830a860b0a8a14 0x8042830a860b0a8a 0xf38fff8e0f0f8f7f 0xfef38fff8e0f0f8f

def z765 : W := mkw 0x42822e4000000000 0x0042822e40000000 0xc38ffff00000000f 0x72c38ffff0000000

def z766 : W := mkw 0x11422e4000000000 0x0011422e40000000 0x334ffff00000000f 0xb2334ffff0000000

def z767 : W := mkw 0x57deef60000000c0 0x0257deef60000000 0xf3cffff00000000f 0xf2f3cffff0000000

def z768 : W := mkw 0x041881b01151bc80 0x20041881b01151bc 0x3cf883f1f3f3fcfb 0xfd3cf883f1f3f3fc

def z769 : W := mkw 0xeebeef60000000c0 0x02eebeef60000000 0xccbff3f000000000 0x42ccbff3f0000000

def z770 : W := mkw 0xfbe0000daea00038 0x04fbe0000daea000 0xfff0000ffff000e0 0xe1fff0000ffff000

def z771 : W := mkw 0xbd7ce560000000c0 0x02bd7ce560000000 0xfcfff3f00000000f 0xf2fcfff3f0000000

def z772 : W := mkw 0x00166f60000000c0 0x0200166f60000000 0x00077ff00000000c 0x0200077ff0000000

def z773 : W := mkw 0x42830a860b0a8a14 0x8042830a860b0a8a 0xc38f0f8e3fff8fff 0x7ec38f0f8e3fff8f

def z774 : W := mkw 0x041eef60000000c0 0x02041eef60000000 0x000ff3f000000000 0x02000ff3f0000000

def z775 : W := mkw 0xfffeef60848000c8 0x02fffeef60848000 0xfffffff00cc0000f 0xf6fffffff00cc000

def z776 : W := mkw 0x11403450c4c4550a 0x4011403450c4c455 0x3340fc71cccc7fb4 0xad3340fc71cccc7f

def z777 : W := mkw 0x00022e4000000000 0x0000022e40000000 0x000ffff00000000e 0x02000ffff0000000

def z778 : W := mkw 0xfffeef69202000e0 0x06fffeef69202000 0xfffffff03030000f 0xf2fffffff0303000

def z779 : W := mkw 0x1140000daea00038 0x041140000daea000 0x3ff0000ffff000f1 0xf53ff0000ffff000

def z780 : W := mkw 0xfbf66f6daea000f8 0x06fbf66f6daea000 0xfff77ffffff000fd 0xf7fff77ffffff000

def z781 : W := mkw 0xfffeef648ea000d8 0x06fffeef648ea000 0xfffffff03ff000df 0xf6fffffff03ff000

def z782 : W := mkw 0xac0dd00b700f6027 0x01ac0dd00b700f60 0xff0ffc0ff00ff0ff 0xfbff0ffc0ff00ff0

def z783 : W := mkw 0xfffeef6d2a2000f0 0x06fffeef6d2a2000 0xfffffffff33000ff 0xf3fffffffff33000

def z784 : W := mkw 0xfbe0000daea00038 0x04fbe0000daea000 0xfff0000ff3f000c1 0xf1fff0000ff3f000

def z785 : W := mkw 0xa820000daea00038 0x04a820000daea000 0x0c30000ffff000f0 0x050c30000ffff000

def z786 : W := mkw 0x42830a860b0a8a14 0x8042830a860b0a8a 0xc30f0f8e0c0f8f7e 0x7ac30f0f8e0c0f8f

def z787 : W := mkw 0xfffeef60000000c0 0x02fffeef60000000 0xfffffff00000709f 0xfafffffff0000070

def z788 : W := mkw 0xfbe0000daea00038 0x04fbe0000daea000 0xfff0000ffff000a1 0xa5fff0000ffff000

def z789 : W := mkw 0x11403450c4c4550a 0x4011403450c4c455 0x3ff0fc71cccc7fbf 0xfd3ff0fc71cccc7f

def z790 : W := mkw 0x041cc12000000080 0x00041cc120000000 0x000ff3f00000000e 0x02000ff3f0000000

def z791 : W := mkw 0xfffeef60848000c8 0x02fffeef60848000 0xfffffff1cc00002f 0xf3fffffff1cc0000

def z792 : W := mkw 0xfffeef640a2000d0 0x06fffeef640a2000 0xfffffff00330000f 0xf2fffffff0033000

def z793 : W := mkw 0xa81551bb615edca7 0x21a81551bb615edc 0xf0f773ffc3fc0c2d 0x27f0f773ffc3fc0c

def z794 : W := mkw 0xac1eef60000000c0 0x02ac1eef60000000 0xf00ffff00000000e 0x22f00ffff0000000

def z795 : W := mkw 0x041eef60100120c0 0x02041eef60100120 0x0c0ffff03003f0de 0xda0c0ffff03003f0

def z796 : W := mkw 0xac0dd00b700f6027 0x01ac0dd00b700f60 0xfc07f00ff00ff0f4 0xabfc07f00ff00ff0

def z797 : W := mkw 0x041eef60000000c0 0x02041eef60000000 0x300ffff00000000e 0xb2300ffff0000000

def z798 : W := mkw 0x00011092515ffc07 0x2100011092515ffc 0x0000000033fffcd0 0x0c0000000033fffc

def z799 : W := mkw 0xfffeef60000000c0 0x02fffeef60000000 0xfffffff000000004 0xe2fffffff0000000

def z800 : W := mkw 0xfffeef60100120c0 0x02fffeef60100120 0xfffffff03000708f 0xf2fffffff0300070

def z801 : W := mkw 0x469eef60000000c0 0x02469eef60000000 0xc30ffff00000000e 0x22c30ffff0000000

def z802 : W := mkw 0xbd7de5e60b0a8ad4 0x82bd7de5e60b0a8a 0x3c70f07e0f0f8f70 0x8c3c70f07e0f0f8f

def z803 : W := mkw 0xfbe0244daea00038 0x04fbe0244daea000 0xfff00c7ffff000f9 0xf5fff00c7ffff000

def z804 : W := mkw 0xfffcc12daea000b8 0x04fffcc12daea000 0xfffff3fffff000ff 0xf7fffff3fffff000

def z805 : W := mkw 0xfbe66e4daea00078 0x06fbe66e4daea000 0xffff7f8ffff000ff 0xf7ffff7f8ffff000

def z806 : W := mkw 0xfffeef6daea000f8 0x06fffeef6daea000 0xfffffffff3f000cf 0xf3fffffffff3f000

def z807 : W := mkw 0x57feef60000000c0 0x0257feef60000000 0x030ffff00000000e 0x02030ffff0000000

def z808 : W := mkw 0x041881b01151bc80 0x20041881b01151bc 0x0ff88ff033f3fcdf 0xfc0ff88ff033f3fc

def z809 : W := mkw 0xfbf66f6daea000f8 0x06fbf66f6daea000 0xf3f77fffcff0002d 0x27f3f77fffcff000

def z810 : W := mkw 0xee8eda8d7b05ea33 0x81ee8eda8d7b05ea 0x3f80ff81ff007f89 0x853f80ff81ff007f

def z811 : W := mkw 0xfffeef69200000e0 0x02fffeef69200000 0xfffffffff3f000ff 0xf7fffffffff3f000

def z812 : W := mkw 0x57daaf6000000080 0x0057daaf60000000 0xfffffff00000000f 0xf2fffffff0000000

def z813 : W := mkw 0xee9ecb2000000080 0x00ee9ecb20000000 0xfffffff00000000f 0xf2fffffff0000000

def z814 : W := mkw 0x00011096dfdfff1e 0xe000011096dfdfff 0x0000000ffffffff0 0x0d0000000fffffff

def z815 : W := mkw 0xa805500b700f6027 0x01a805500b700f60 0xfc07700ff00ff0f4 0xfbfc07700ff00ff0

def z816 : W := mkw 0xfffeef60848001c8 0x42fffeef60848001 0xfffffff00c00030f 0xf2fffffff00c0003

def z817 : W := mkw 0x041eef60100120c0 0x02041eef60100120 0x000ffff00003f00e 0x0a000ffff00003f0

def z818 : W := mkw 0xfffeef60000000c0 0x02fffeef60000000 0xfffffff00c000f0f 0xf6fffffff00c000f

def z819 : W := mkw 0x041eef60000000c0 0x02041eef60000000 0x008ffff00000000f 0x52008ffff0000000

def z820 : W := mkw 0xfffeef60848000c8 0x02fffeef60848000 0xfffffff1cccc0fbf 0xfffffffff1cccc0f

def z821 : W := mkw 0xfffeef60000000c0 0x02fffeef60000000 0xfffffff003f0000f 0xf6fffffff003f000

def z822 : W := mkw 0x53e22ed48fe09f18 0xc453e22ed48fe09f 0x03f00ff00ff00f09 0x0403f00ff00ff00f

def z823 : W := mkw 0x041eef60000000c0 0x02041eef60000000 0x0cbffff00000000e 0x420cbffff0000000

def z824 : W := mkw 0x11403450c4c4550a 0x4011403450c4c455 0x3340fc71cccc7fb9 0x8d3340fc71cccc7f

def z825 : W := mkw 0x11403450c4c4550a 0x4011403450c4c455 0x3300fc71cc0c7fbe 0xb93300fc71cc0c7f

def z826 : W := mkw 0x041881b01151bc80 0x20041881b01151bc 0x0ff88ff03ff3ffdb 0xdc0ff88ff03ff3ff

def z827 : W := mkw 0xfbe0000daea00038 0x04fbe0000daea000 0xfcf0000ff3f000f0 0xf1fcf0000ff3f000

def z828 : W := mkw 0xa805500b600e4027 0x01a805500b600e40 0xf00ff00fc00ff0f6 0xfbf00ff00fc00ff0

def z829 : W := mkw 0x001001b01151bc80 0x20001001b01151bc 0x0cf003f033f3fcd9 0xdc0cf003f033f3fc

def z830 : W := mkw 0xfffeef60000000c0 0x02fffeef60000000 0xfffffff000c0009f 0xf6fffffff000c000

def z831 : W := mkw 0xffceee4000000000 0x00ffceee40000000 0xffcffff00000000f 0xf2ffcffff0000000

def z832 : W := mkw 0x155eef60848000c8 0x02155eef60848000 0x334ffff1ccc000bf 0xb7334ffff1ccc000

def z833 : W := mkw 0xfffeef6dbea120f8 0x06fffeef6dbea120 0xfffffffffff3f0ff 0xfffffffffffff3f0

def z834 : W := mkw 0x42830a860b0a8a14 0x8042830a860b0a8a 0xc38f0f8e0c0f8f2f 0x7ac38f0f8e0c0f8f

def z835 : W := mkw 0x041881b01151bc80 0x20041881b01151bc 0x0cf883f033f3fcc9 0xc40cf883f033f3fc

def z836 : W := mkw 0x57feef60000000c0 0x0257feef60000000 0x33fffff00000000f 0xb233fffff0000000

def z837 : W := mkw 0xfffeef60000000c0 0x02fffeef60000000 0xfffffff00300005f 0xf6fffffff0030000

def z838 : W := mkw 0xeebedb30c4c455ca 0x42eebedb30c4c455 0xccbf0381cccc7fb0 0x4fccbf0381cccc7f

def z839 : W := mkw 0x041881b01151bc80 0x20041881b01151bc 0xccf883fe33f3fcfb 0xfcccf883fe33f3fc

def z840 : W := mkw 0xfbe0244daea00038 0x04fbe0244daea000 0xfff07c0ffff000f5 0xf5fff07c0ffff000

def z841 : W := mkw 0xbd7eef60000000c0 0x02bd7eef60000000 0x3f7ffff00000000f 0xb23f7ffff0000000

def z842 : W := mkw 0xac0dd00b700f6027 0x01ac0dd00b700f60 0xfc8ff38ff00ff0ff 0xfbfc8ff38ff00ff0

def z843 : W := mkw 0xfffeef60000000c0 0x02fffeef60000000 0xfffffff1c00000bf 0xf3fffffff1c00000

def z844 : W := mkw 0xac0dd00b700f6027 0x01ac0dd00b700f60 0xff0ff00ffc0ff0f7 0xffff0ff00ffc0ff0

def z845 : W := mkw 0x1140344040044002 0x0011403440400440 0x3340fc71cc0c7fbf 0xbd3340fc71cc0c7f

def z846 : W := mkw 0xfffeef6daea000f8 0x06fffeef6daea000 0xfffff3fffff000f1 0xf7fffff3fffff000

def z847 : W := mkw 0xfff881bdbff1bcb8 0x24fff881bdbff1bc 0xf30883ffcc03fc2a 0x29f30883ffcc03fc

def z848 : W := mkw 0x42830a860b0a8a14 0x8042830a860b0a8a 0xc38f0f8e0f0f8f4f 0x4ec38f0f8e0f0f8f

def z849 : W := mkw 0xbd7cf579f4c575eb 0x43bd7cf579f4c575 0x3c70f071f0c07080 0x813c70f071f0c070

def z850 : W := mkw 0xa805500b700f6027 0x01a805500b700f60 0xf007f00ff00ff0f6 0xbbf007f00ff00ff0

def z851 : W := mkw 0xfffeef60000000c0 0x02fffeef60000000 0xfffffff030f0008f 0xf2fffffff030f000

def z852 : W := mkw 0xac0dd002400e4006 0x00ac0dd002400e40 0xfc0ff00fc00ff0f6 0xfbfc0ff00fc00ff0

def z853 : W := mkw 0xfffeef60000000c0 0x02fffeef60000000 0xfffffffe0000007f 0xf2fffffffe000000

def z854 : W := mkw 0x041eef60000000c0 0x02041eef60000000 0x004ffff00000000f 0x92004ffff0000000

def z855 : W := mkw 0xbd5eef60000000c0 0x02bd5eef60000000 0xff4ffff00000000f 0xf2ff4ffff0000000

def z856 : W := mkw 0xfffeef69a4a000e8 0x06fffeef69a4a000 0xfffffff1fcf000bf 0xf7fffffff1fcf000

def z857 : W := mkw 0x0000009001409c00 0x000000009001409c 0x0cf883f033f3fcdb 0xdc0cf883f033f3fc

def z858 : W := mkw 0x041881b01151bc80 0x20041881b01151bc 0xccff83f033f3fcdf 0xfeccff83f033f3fc

def z859 : W := mkw 0xa805500b700f6027 0x01a805500b700f60 0xf007700fc00ff024 0x2bf007700fc00ff0

def z860 : W := mkw 0x42830a860b0a8a14 0x8042830a860b0a8a 0xcfff0f8e0f0f8f7f 0xfecfff0f8e0f0f8f

def z861 : W := mkw 0xfffeef60000000c0 0x02fffeef60000000 0xfffffff03330004f 0xf2fffffff0333000

def z862 : W := mkw 0xfbe0244daea00138 0x44fbe0244daea001 0xfff00c0ffff003f1 0xf5fff00c0ffff003

def z863 : W := mkw 0xac0dd00b700f6027 0x01ac0dd00b700f60 0xfc0ff00ff00ff0c6 0xcbfc0ff00ff00ff0

def z864 : W := mkw 0xeaa0345d6a645532 0x44eaa0345d6a6455 0xccb0fc7e333c7f4e 0x48ccb0fc7e333c7f

def z865 : W := mkw 0x42830a860b0a8a14 0x8042830a860b0a8a 0xc3cf8ffe0f0f8f7f 0xfec3cf8ffe0f0f8f

def z866 : W := mkw 0xfffeef60000000c0 0x02fffeef60000000 0xf34ffff00000000f 0xb2f34ffff0000000

def z867 : W := mkw 0xfbe0000daea00038 0x04fbe0000daea000 0xfff0000ffff000c1 0xc5fff0000ffff000

def z868 : W := mkw 0x041881b01151bc80 0x20041881b01151bc 0x0cf883f033f3fc4b 0x4c0cf883f033f3fc

def z869 : W := mkw 0xfffeef648ea000d8 0x06fffeef648ea000 0xfffffff1cff000bf 0xf7fffffff1cff000

def z870 : W := mkw 0x1558b5e0d595e98a 0x601558b5e0d595e9 0x3fb87f81ff3f8364 0x613fb87f81ff3f83

def z871 : W := mkw 0x00011092414edf06 0xc000011092414edf 0x00000000000fff00 0x0800000000000fff

def z872 : W := mkw 0x11403450c4c4550a 0x4011403450c4c455 0xf340fc7fcccc7fff 0xfdf340fc7fcccc7f

def z873 : W := mkw 0xfbe0244daea00038 0x04fbe0244daea000 0xfff0fc7ffffc0fff 0xfdfff0fc7ffffc0f

def z874 : W := mkw 0xfbe20a0daea00238 0x84fbe20a0daea002 0xfff00c0ffff003f1 0xf5fff00c0ffff003

def z875 : W := mkw 0xeebeef60000000c0 0x02eebeef60000000 0xcfbffff00000000f 0x72cfbffff0000000

def z876 : W := mkw 0xfffeef60000000c0 0x02fffeef60000000 0xfffffff0300000df 0xf2fffffff0300000

def z877 : W := mkw 0xfbe20a0daea00038 0x04fbe20a0daea000 0xffff038ffff000f1 0xf7ffff038ffff000

def z878 : W := mkw 0xac0dd00b700f6027 0x01ac0dd00b700f60 0xfc4ff00ff0cff0f7 0xfffc4ff00ff0cff0

def z879 : W := mkw 0xfbe0000daea00038 0x04fbe0000daea000 0xfff0807ffff000fb 0xf5fff0807ffff000

def z880 : W := mkw 0xfbe0000daea00038 0x04fbe0000daea000 0xfff00c0ffffc03f5 0xf5fff00c0ffffc03

def z881 : W := mkw 0xac1eef60000000c0 0x02ac1eef60000000 0x3c0ffff00000000e 0x823c0ffff0000000

def z882 : W := mkw 0xfbf66f60000000c0 0x02fbf66f60000000 0xf3ff7ff00000000f 0x72f3ff7ff0000000

def z883 : W := mkw 0xb9400009a4800028 0x00b9400009a48000 0xfff0000ffff000f1 0xf5fff0000ffff000

def z884 : W := mkw 0x42a30a860b2a8a14 0x8442a30a860b2a8a 0xc3bf0f8e0f3f8f7f 0x7ec3bf0f8e0f3f8f

def z885 : W := mkw 0xb960000daea00038 0x04b960000daea000 0x3f70000ffff000f1 0xb53f70000ffff000

def z886 : W := mkw 0xfbe0000daea00038 0x04fbe0000daea000 0xcff0000ffff000f1 0x45cff0000ffff000

def z887 : W := mkw 0xfffeef60000000c0 0x02fffeef60000000 0x3ffffff00000000f 0x823ffffff0000000

def z888 : W := mkw 0xfffeef6daea000f8 0x06fffeef6daea000 0xf30fffffcc00002e 0x23f30fffffcc0000

def z889 : W := mkw 0xac0dd00b700f6027 0x01ac0dd00b700f60 0xfc0ff00fc00ff026 0xfbfc0ff00fc00ff0

def z890 : W := mkw 0xac1dd12b700f60a7 0x01ac1dd12b700f60 0xfc0ff3fff00ff0fe 0xfbfc0ff3fff00ff0

def z891 : W := mkw 0x0001100b700f6027 0x010001100b700f60 0xf00ff00ff00ff0f6 0xfbf00ff00ff00ff0

def z892 : W := mkw 0xeebeef60000000c0 0x02eebeef60000000 0xfcbffff00000000e 0xf2fcbffff0000000

def z893 : W := mkw 0x041881b01151bc80 0x20041881b01151bc 0x0cf883f033f3f0cb 0xd00cf883f033f3f0

def z894 : W := mkw 0xfffeef60000000c0 0x02fffeef60000000 0xfcfff3f00000000b 0xd2fcfff3f0000000

def z895 : W := mkw 0x11403450c4c4550a 0x4011403450c4c455 0x3340fc71cccc7fad 0xa53340fc71cccc7f

def z896 : W := mkw 0x11403450c4c4550a 0x4011403450c4c455 0x33c8fff1cccc7fbf 0xfd33c8fff1cccc7f

def z897 : W := mkw 0xfffeef60000000c0 0x02fffeef60000000 0xfff7fff00000000d 0xa2fff7fff0000000

def z898 : W := mkw 0xfffeef60000000c0 0x02fffeef60000000 0xf3fffff00000000f 0x22f3fffff0000000

def z899 : W := mkw 0xfffcc12000000080 0x00fffcc120000000 0xfffff3f00000000f 0xf2fffff3f0000000

def z900 : W := mkw 0xfbe4644daea00078 0x06fbe4644daea000 0xfff0700ffff000f1 0xf5fff0700ffff000

def z901 : W := mkw 0xac0dd00b700f6027 0x01ac0dd00b700f60 0xfcfff00ff00ff0f7 0xfbfcfff00ff00ff0

def z902 : W := mkw 0x155eef60000000c0 0x02155eef60000000 0x3ffffff00000000f 0xf23ffffff0000000

def z903 : W := mkw 0x0001109ffffffc3f 0x250001109ffffffc 0x0000000ffffffcf0 0x0d0000000ffffffc

def z904 : W := mkw 0x57edd006deaf601f 0x0557edd006deaf60 0x03fff0000ffff007 0x0e03fff0000ffff0

def z905 : W := mkw 0xfffeef60100120c0 0x02fffeef60100120 0xfffffff03003804f 0xf2fffffff0300380

def z906 : W := mkw 0xfffeef6d2a0000f0 0x02fffeef6d2a0000 0xffffffffff0000ff 0xf7ffffffffff0000

def z907 : W := mkw 0xfffeef69a4a000e8 0x06fffeef69a4a000 0xfffffff1c000000f 0xf3fffffff1c00000

def z908 : W := mkw 0x041881b01151bc80 0x20041881b01151bc 0x0cf883f033f3fcca 0xc80cf883f033f3fc

def z909 : W := mkw 0xbd5cf579f4d575ab 0x61bd5cf579f4d575 0x3c70f071f0f07080 0x813c70f071f0f070

def z910 : W := mkw 0xfbe0000daea00038 0x04fbe0000daea000 0xfcf0000ffff000f0 0xc5fcf0000ffff000

def z911 : W := mkw 0x42830a860b0a8a14 0x8042830a860b0a8a 0xc38f0f8e0f0f8f79 0x4ec38f0f8e0f0f8f

def z912 : W := mkw 0x041cc12000000080 0x00041cc120000000 0x0cfff3f00000000f 0xd20cfff3f0000000

def z913 : W := mkw 0x0000101040445402 0x0000001010404454 0x3340fc71cccc7fbf 0xbd3340fc71cccc7f

def z914 : W := mkw 0xeaa0000daea00038 0x04eaa0000daea000 0xcfb0000ffff000f1 0x75cfb0000ffff000

def z915 : W := mkw 0xac0cc0901151bc00 0x20ac0cc0901151bc 0xfc0ff00033f3fcd6 0xfefc0ff00033f3fc

def z916 : W := mkw 0x041df5f2515ffd87 0x61041df5f2515ffd 0x000ffff0000fff0e 0x0a000ffff0000fff

def z917 : W := mkw 0xfbe0000daea00038 0x04fbe0000daea000 0xfff0f00ffff000f7 0xf5fff0f00ffff000

def z918 : W := mkw 0xfffeef640a0000d0 0x02fffeef640a0000 0xfffffff00f00000f 0xf6fffffff00f0000

def z919 : W := mkw 0xfbe0000daea00038 0x04fbe0000daea000 0xfcf0000ff3f000d1 0xd5fcf0000ff3f000

def z920 : W := mkw 0x041eef60000000c0 0x02041eef60000000 0x0c0ffff00000000e 0xd20c0ffff0000000

def z921 : W := mkw 0xfbe4400daea00038 0x04fbe4400daea000 0xfff7700ffff000f5 0xf7fff7700ffff000

def z922 : W := mkw 0x157eef60000000c0 0x02157eef60000000 0x007ffff00000000e 0x02007ffff0000000

def z923 : W := mkw 0x53c000048e800018 0x0053c000048e8000 0xfff0000ffff000f1 0xf5fff0000ffff000

def z924 : W := mkw 0xfbe66e4daea00078 0x06fbe66e4daea000 0xfff7fc7ffff000ff 0xf7fff7fc7ffff000

def z925 : W := mkw 0xac0dd00b700f6027 0x01ac0dd00b700f60 0xfc0ff00ff00ff0a6 0xabfc0ff00ff00ff0

def z926 : W := mkw 0xfffeef69300120e0 0x02fffeef69300120 0xfffffffff003f0ff 0xfbfffffffff003f0

def z927 : W := mkw 0xeebecb20000000c0 0x02eebecb20000000 0xfcfff3f00000000f 0xf2fcfff3f0000000

def z928 : W := mkw 0xfffeef640a0000d0 0x02fffeef640a0000 0xfffffffe0c00002f 0xf2fffffffe0c0000

def z929 : W := mkw 0xfffeef60000000c0 0x02fffeef60000000 0xff0ffff00000000e 0xf2ff0ffff0000000

def z930 : W := mkw 0xac2dd00b702f6027 0x05ac2dd00b702f60 0xfc3ff00ff03ff0f6 0xfbfc3ff00ff03ff0

def z931 : W := mkw 0xac0dd00b700f6027 0x01ac0dd00b700f60 0xfc0ff00ff00ff066 0x6bfc0ff00ff00ff0

def z932 : W := mkw 0x0418812010012080 0x0004188120100120 0x0cf883f033f3f0db 0xdc0cf883f033f3f0

def z933 : W := mkw 0xfffeef60100120c0 0x02fffeef60100120 0xfffffff00003f00f 0xfafffffff00003f0

def z934 : W := mkw 0xac0dd00b700f6027 0x01ac0dd00b700f60 0xfc0ff00ff00ff0e4 0xe3fc0ff00ff00ff0

def z935 : W := mkw 0xfffeef60848000c8 0x02fffeef60848000 0xfffffff1fff000ff 0xf7fffffff1fff000

def z936 : W := mkw 0xeaa0000daea00038 0x04eaa0000daea000 0xfcb0000ffff000f0 0xf5fcb0000ffff000

def z937 : W := mkw 0xfbe0000daea00038 0x04fbe0000daea000 0xfff0000ffff00cfb 0xfdfff0000ffff00c

def z938 : W := mkw 0xbd7eef60000000c0 0x02bd7eef60000000 0x3cfffff00000000f 0xd23cfffff0000000

def z939 : W := mkw 0xfbe0000daea00038 0x04fbe0000daea000 0xfff0000ffff00061 0x65fff0000ffff000

def z940 : W := mkw 0x42821a844b04ca12 0x8042821a844b04ca 0x3380ff81cf0c7fbf 0xbd3380ff81cf0c7f

def z941 : W := mkw 0xa800000daea00038 0x04a800000daea000 0xfcf0000ffff000f1 0xf5fcf0000ffff000

def z942 : W := mkw 0x42830a860b0a8a14 0x8042830a860b0a8a 0xc38f0f8e0f0f8f6e 0x6ac38f0f8e0f0f8f

def z943 : W := mkw 0x04099002500f6006 0x0004099002500f60 0xfc0ff00ff00ff0f6 0xfbfc0ff00ff00ff0

def z944 : W := mkw 0xfffeef60000000c0 0x02fffeef60000000 0xff7ffff00000000e 0xa2ff7ffff0000000

def z945 : W := mkw 0xfffeef60000000c0 0x02fffeef60000000 0xfffff3f000000001 0xf2fffff3f0000000

def z946 : W := mkw 0x00011092c5cedf0e 0xc000011092c5cedf 0x00000001cccfffb0 0x0d00000001cccfff

def z947 : W := mkw 0x42830a860b0a8a14 0x8042830a860b0a8a 0xc38f0f8e0f0f8f6d 0x66c38f0f8e0f0f8f

def z948 : W := mkw 0xfffeef60000000c0 0x02fffeef60000000 0xfffffff000000c1f 0xfefffffff000000c

def z949 : W := mkw 0xac1eef69200000e0 0x02ac1eef69200000 0xfc0ffffff00000fe 0xf3fc0ffffff00000

def z950 : W := mkw 0xfffeef6daea000f8 0x06fffeef6daea000 0xfcfff3fff3f000c0 0xc3fcfff3fff3f000

def z951 : W := mkw 0x4280000daea00038 0x044280000daea000 0xcff0000ffff000f1 0xf5cff0000ffff000

def z952 : W := mkw 0x00010082010a8804 0x0000010082010a88 0xc38f0f8e0f0f8f7f 0x7ec38f0f8e0f0f8f

def z953 : W := mkw 0xfffeef640a0000d0 0x02fffeef640a0000 0xfffffffe3ff000ff 0xf6fffffffe3ff000

def z954 : W := mkw 0x11403450c4c4550a 0x4011403450c4c455 0x3f40fc71fccc7fff 0xfd3f40fc71fccc7f

def z955 : W := mkw 0xbd7eef60000000c0 0x02bd7eef60000000 0x300ffff00000000e 0x02300ffff0000000

def z956 : W := mkw 0x041881b01151bc80 0x20041881b01151bc 0x0cf883f033fffcff 0xfc0cf883f033fffc

def z957 : W := mkw 0xfffeef640a0000d0 0x02fffeef640a0000 0xfffffffe0f0c0f7f 0xfefffffffe0f0c0f

def z958 : W := mkw 0xfffeef60000000c0 0x02fffeef60000000 0xfffffff00c0c032f 0xf2fffffff00c0c03

def z959 : W := mkw 0x00011092515ffc07 0x2100011092515ffc 0x00000000000ffc00 0x0800000000000ffc

def z960 : W := mkw 0xfffeef60100120c0 0x02fffeef60100120 0xfffffff033f3f0df 0xfefffffff033f3f0

def z961 : W := mkw 0xac1dd12b700f60a7 0x01ac1dd12b700f60 0xfcfff3fff3fff0ff 0xfffcfff3fff3fff0

def z962 : W := mkw 0x0001109bf5dffd2f 0x610001109bf5dffd 0x0000000ffffffff0 0x0d0000000fffffff

def z963 : W := mkw 0xfbe22e4000000000 0x00fbe22e40000000 0xfffffff00000000f 0xf2fffffff0000000

def z964 : W := mkw 0x041eef60000000c0 0x02041eef60000000 0x000ffff0000c0f0e 0x0a000ffff0000c0f

def z965 : W := mkw 0x041881b01151bc80 0x20041881b01151bc 0x0cf083f033f3fcd9 0x8c0cf083f033f3fc

def z966 : W := mkw 0xbd5ce56000000080 0x00bd5ce560000000 0xfffffff00000000f 0xf2fffffff0000000

def z967 : W := mkw 0x041ffff2515ffcc7 0x23041ffff2515ffc 0x000ffff0000ffc0e 0x0a000ffff0000ffc

def z968 : W := mkw 0xac0dd00b700f6027 0x01ac0dd00b700f60 0xfc0ff00ff003f0d2 0xdbfc0ff00ff003f0

def z969 : W := mkw 0x469eef60000000c0 0x02469eef60000000 0xc08ffff00000000e 0x42c08ffff0000000

def z970 : W := mkw 0x11403450c4c4550a 0x4011403450c4c455 0x3f70fc71fcfc7fbf 0xbd3f70fc71fcfc7f

def z971 : W := mkw 0xb960000daea00038 0x04b960000daea000 0x3cf0000ffff000f1 0xd53cf0000ffff000

def z972 : W := mkw 0xfffeef60848000c8 0x02fffeef60848000 0xfffffff1c0c0008f 0xf3fffffff1c0c000

def z973 : W := mkw 0xeaa0000d2a200030 0x04eaa0000d2a2000 0xfcf0000ff3f000f1 0xf5fcf0000ff3f000

def z974 : W := mkw 0x53f66f60000000c0 0x0253f66f60000000 0x03f77ff00000000d 0x0203f77ff0000000

def z975 : W := mkw 0x041881b01151bc80 0x20041881b01151bc 0x0cf883f03ffffffb 0xdc0cf883f03fffff

def z976 : W := mkw 0x041eef60000000c0 0x02041eef60000000 0x030ffff00c0c0f3f 0x3e030ffff00c0c0f

def z977 : W := mkw 0x11403450c4c4550a 0x4011403450c4c455 0xf34ffc71cccc7fbf 0xfff34ffc71cccc7f

def z978 : W := mkw 0x11403450c4c4550a 0x4011403450c4c455 0x3340fc71cccc7f8f 0x8d3340fc71cccc7f

def z979 : W := mkw 0x11403450c4c4550a 0x4011403450c4c455 0x3340fc71cccc7f2f 0x2d3340fc71cccc7f

def z980 : W := mkw 0xfffeef60000000c0 0x02fffeef60000000 0xf38ffff00000000f 0x72f38ffff0000000

def z981 : W := mkw 0xeebeef6d2a2000f0 0x06eebeef6d2a2000 0xccbffffe3330004e 0x42ccbffffe333000

def z982 : W := mkw 0x041881b01151bc80 0x20041881b01151bc 0x0cf883f033f3f0d1 0xd40cf883f033f3f0

def z983 : W := mkw 0xfffeef60101120c0 0x22fffeef60101120 0xfffffff03030000f 0xf2fffffff0303000

def z984 : W := mkw 0xfffeef6d2a2000f0 0x06fffeef6d2a2000 0xfffffffe3f30007f 0xf6fffffffe3f3000

def z985 : W := mkw 0xfffeef60000000c0 0x02fffeef60000000 0xfcfff3f000000006 0xf2fcfff3f0000000

def z986 : W := mkw 0xac1cc12000000080 0x00ac1cc120000000 0xfc0ff3f00000000e 0xf2fc0ff3f0000000

def z987 : W := mkw 0xfbe0000daea00038 0x04fbe0000daea000 0xfff00c0ffff000ff 0xf5fff00c0ffff000

def z988 : W := mkw 0x42830a860b0a8a14 0x8042830a860b0a8a 0xc3cf0f8e0fcf8fff 0xfec3cf0f8e0fcf8f

def z989 : W := mkw 0xfffeef60000000c0 0x02fffeef60000000 0xfffffff00003805f 0xfafffffff0000380

def z990 : W := mkw 0x0000000daea00038 0x040000000daea000 0x0c70000ffff000f0 0x850c70000ffff000

def z991 : W := mkw 0x469eef60000000c0 0x02469eef60000000 0xcffffff00000000f 0xf2cffffff0000000

def z992 : W := mkw 0xac0dd00b700f6027 0x01ac0dd00b700f60 0xfc7ff00ff0fff0f6 0xfbfc7ff00ff0fff0

def z993 : W := mkw 0x041881b01151bc80 0x20041881b01151bc 0x0cf883f033f3fcd0 0xcc0cf883f033f3fc

def z994 : W := mkw 0x11403450c4c4550a 0x4011403450c4c455 0x33f0fc71cffc7fbf 0xbd33f0fc71cffc7f

def z995 : W := mkw 0xbd7eef60000000c0 0x02bd7eef60000000 0xfc7ffff00000000e 0xf2fc7ffff0000000

def z996 : W := mkw 0xa801100b600e4026 0x00a801100b600e40 0xfc0ff00ff00ff0f6 0xfbfc0ff00ff00ff0

def z997 : W := mkw 0x041881b01151bc80 0x20041881b01151bc 0x3cf8f3f033f3fcdf 0xfc3cf8f3f033f3fc

def z998 : W := mkw 0xfffeef640a0000d0 0x02fffeef640a0000 0xfffffffe0300004f 0xf2fffffffe030000

def z999 : W := mkw 0x57feef60000000c0 0x0257feef60000000 0x0ffffff00000000f 0xd20ffffff0000000

def z1000 : W := mkw 0x53f22ff48fc09fd8 0xc253f22ff48fc09f 0x03f00ff00fc00f09 0x0403f00ff00fc00f

def z1001 : W := mkw 0x42830a860b0a8a14 0x8042830a860b0a8a 0xcf8f0f8e3f0f8fff 0xfecf8f0f8e3f0f8f

def z1002 : W := mkw 0x42830a860b0a8a14 0x8042830a860b0a8a 0xc30f0f8e0f0f8f7e 0x2ec30f0f8e0f0f8f

def z1003 : W := mkw 0x041881b01151bc80 0x20041881b01151bc 0x0cf883f033f3fc8b 0x8c0cf883f033f3fc

def z1004 : W := mkw 0x42830a860b0a8a14 0x8042830a860b0a8a 0xc30f0f8e0c0f8f3f 0x3ec30f0f8e0c0f8f

def z1005 : W := mkw 0xfbe0244daea00038 0x04fbe0244daea000 0xfff0f07ffff000f1 0xf5fff0f07ffff000

def z1006 : W := mkw 0xfbe20a0daea00038 0x04fbe20a0daea000 0xffff0f8ffffc0fff 0xffffff0f8ffffc0f

def z1007 : W := mkw 0xfbe1109fefeedf3e 0xc4fbe1109fefeedf 0xfff0000ffffffff1 0xfdfff0000fffffff

def z1008 : W := mkw 0xfffeef6daea000f8 0x06fffeef6daea000 0xfffffffe3ff0004f 0xf6fffffffe3ff000

def z1009 : W := mkw 0x041881b01151bc80 0x20041881b01151bc 0x0cf88ff033ffffdf 0xdc0cf88ff033ffff

def z1010 : W := mkw 0xb960000daea00038 0x04b960000daea000 0x3c70000ff3f000c0 0x813c70000ff3f000

def z1011 : W := mkw 0x155eef60000000c0 0x02155eef60000000 0x304ffff00000000e 0x82304ffff0000000

def z1012 : W := mkw 0x11403450c4c4550a 0x4011403450c4c455 0x3348fc71cccfffff 0xfd3348fc71cccfff

def z1013 : W := mkw 0xfbe1109ffffffc3f 0x25fbe1109ffffffc 0xfff0000ffffffcf1 0xfdfff0000ffffffc

def z1014 : W := mkw 0x42830a860b0a8a14 0x8042830a860b0a8a 0xc3ff0f8e0fff8f7f 0x7ec3ff0f8e0fff8f

def z1015 : W := mkw 0xac0dd00b700f6027 0x01ac0dd00b700f60 0xfc8ff00ff30ff0f7 0xfffc8ff00ff30ff0

def z1016 : W := mkw 0x11603450c4e4550a 0x4411603450c4e455 0x3370fc71ccfc7fbf 0xbd3370fc71ccfc7f

def z1017 : W := mkw 0x46beef60000000c0 0x0246beef60000000 0x00bffff00000000e 0x0200bffff0000000

def z1018 : W := mkw 0xfffeef6d2a2000f0 0x06fffeef6d2a2000 0xfffffffe0000000f 0xf2fffffffe000000

def z1019 : W := mkw 0xfbe66e4000000040 0x02fbe66e40000000 0xf3cffff00000000f 0xf2f3cffff0000000

def z1020 : W := mkw 0xeebeef60000000c0 0x02eebeef60000000 0xccfffff00000000f 0xd2ccfffff0000000

def z1021 : W := mkw 0xee9eef60000000c0 0x02ee9eef60000000 0xff8ffff00000000f 0xf2ff8ffff0000000

def z1022 : W := mkw 0xfbf66f60000000c0 0x02fbf66f60000000 0xf3077ff00000000c 0x22f3077ff0000000

def z1023 : W := mkw 0x42830a860b0a8a14 0x8042830a860b0a8a 0xcfbf0f8e3f3f8f7f 0x7ecfbf0f8e3f3f8f

def z1024 : W := mkw 0x11403450c4c4550a 0x4011403450c4c455 0x3300fc71cc0c7f3f 0x3d3300fc71cc0c7f

def z1025 : W := mkw 0xac0dd00b700f6027 0x01ac0dd00b700f60 0xfc0ffc0ff00ffffe 0xfbfc0ffc0ff00fff

def z1026 : W := mkw 0xac0dd00b700f6027 0x01ac0dd00b700f60 0xfc0ff00ff003f0f0 0xf3fc0ff00ff003f0

def z1027 : W := mkw 0xfbe0000daea00038 0x04fbe0000daea000 0x3ff0000ffff000f1 0x853ff0000ffff000

def z1028 : W := mkw 0xb960000daea00038 0x04b960000daea000 0xfc70000ffff000f0 0xf5fc70000ffff000

def z1029 : W := mkw 0xfffeef69a4a000e8 0x06fffeef69a4a000 0xfffffff1f3f000df 0xf7fffffff1f3f000

def z1030 : W := mkw 0xac0dd00b700f6027 0x01ac0dd00b700f60 0xfc0ff00ff00ff0f0 0xcbfc0ff00ff00ff0

def z1031 : W := mkw 0xfbe0000920000020 0x00fbe00009200000 0xfff0000ff3f000f1 0xf5fff0000ff3f000

def z1032 : W := mkw 0xeaa0000daea00038 0x04eaa0000daea000 0xccb0000ff3f000c0 0x41ccb0000ff3f000

def z1033 : W := mkw 0xac1dd12b700f60a7 0x01ac1dd12b700f60 0xfc7ff07ff00ff0f6 0xfbfc7ff07ff00ff0

def z1034 : W := mkw 0xbd7eef60000000c0 0x02bd7eef60000000 0x3c7ff3f000000000 0x823c7ff3f0000000

def z1035 : W := mkw 0xfffeef60000000c0 0x02fffeef60000000 0xcffffff00000000f 0x42cffffff0000000

def z1036 : W := mkw 0xbd7eef69a4a000e8 0x06bd7eef69a4a000 0x3c7ffff1f0f0008e 0x833c7ffff1f0f000

def z1037 : W := mkw 0xfffeef60000000c0 0x02fffeef60000000 0xfffffff00c00003f 0xf6fffffff00c0000

def z1038 : W := mkw 0x041881b01151bc80 0x20041881b01151bc 0x0cf883f033f3f0d2 0xd80cf883f033f3f0

def z1039 : W := mkw 0xfffeef69a4a000e8 0x06fffeef69a4a000 0xfffffffff0f000ff 0xf3fffffffff0f000

def z1040 : W := mkw 0x0001109b715ffc27 0x210001109b715ffc 0x0000000ff00ffcf0 0x090000000ff00ffc

def z1041 : W := mkw 0x53f22ff48ff09cd8 0x2653f22ff48ff09c 0x03f00ff00ff00c09 0x0403f00ff00ff00c

def z1042 : W := mkw 0xfffeef60000000c0 0x02fffeef60000000 0xffbffff00000000e 0x62ffbffff0000000

def z1043 : W := mkw 0x42830a860b0a8a14 0x8042830a860b0a8a 0xc38f0f8e0f0f8f2f 0x2ec38f0f8e0f0f8f

def z1044 : W := mkw 0x041881b01151bc80 0x20041881b01151bc 0x0ff883f03ff3fcfb 0xfc0ff883f03ff3fc

def z1045 : W := mkw 0xeebeef60000000c0 0x02eebeef60000000 0xc00ffff00000000e 0x02c00ffff0000000

def z1046 : W := mkw 0x041eef60000000c0 0x02041eef60000000 0x030ffff00000000f 0x32030ffff0000000

def z1047 : W := mkw 0x0001109fffcfff3f 0xc10001109fffcfff 0x0000000fffcffff0 0x0d0000000fffcfff

def z1048 : W := mkw 0x000110964b4edf16 0xc0000110964b4edf 0x0000000e0f0fff70 0x0c0000000e0f0fff

def z1049 : W := mkw 0xfffeef6084a000c8 0x06fffeef6084a000 0xfffffff000f0000f 0xf2fffffff000f000

def z1050 : W := mkw 0x53d22ff48fd09f98 0xe053d22ff48fd09f 0x03f00ff00ff00f09 0x0403f00ff00ff00f

def z1051 : W := mkw 0x42830a860b0a8a14 0x8042830a860b0a8a 0xf38f0f8fcf0f8fff 0xfff38f0f8fcf0f8f

def z1052 : W := mkw 0x0000345040445502 0x4000003450404455 0x3300fc71cc0c7fbf 0xbd3300fc71cc0c7f

def z1053 : W := mkw 0xac0dd00b700f6027 0x01ac0dd00b700f60 0xf00ff00fc00ff0b6 0xbbf00ff00fc00ff0

def z1054 : W := mkw 0xac1dd12b700f60a7 0x01ac1dd12b700f60 0xfcbff38ff00ff0f6 0xfbfcbff38ff00ff0

def z1055 : W := mkw 0xfffeef640a0002d0 0x82fffeef640a0002 0xfffffff00c00030f 0xf2fffffff00c0003

def z1056 : W := mkw 0xfbe0000daea00038 0x04fbe0000daea000 0xfff0000ffffc00f7 0xfdfff0000ffffc00

def z1057 : W := mkw 0xac0dd00b700f6027 0x01ac0dd00b700f60 0xfc0f700ff00ff0f4 0x6bfc0f700ff00ff0

def z1058 : W := mkw 0xfffeef6d2a2000f0 0x06fffeef6d2a2000 0xfffffffe33f000df 0xf6fffffffe33f000

def z1059 : W := mkw 0xfffeef69a48000e8 0x02fffeef69a48000 0xfffffffffcc000ff 0xf7fffffffffcc000

def z1060 : W := mkw 0xac0dd00b700f6027 0x01ac0dd00b700f60 0xf00ff00fc00ff076 0x7bf00ff00fc00ff0

def z1061 : W := mkw 0x11403450c4c4550a 0x4011403450c4c455 0x3340fc71cc0c7f2f 0xb93340fc71cc0c7f

def z1062 : W := mkw 0xfbf66f60000000c0 0x02fbf66f60000000 0xf3f7fff00000000f 0xb2f3f7fff0000000

def z1063 : W := mkw 0xfffeef69300120e1 0x03fffeef69300120 0xfffffff03000000f 0xf2fffffff0300000

def z1064 : W := mkw 0xfffeef69200000e0 0x02fffeef69200000 0xffffffffc000002f 0xf3ffffffffc00000

def z1065 : W := mkw 0xeaa0000daea00038 0x04eaa0000daea000 0xccf0000ffff000f1 0xd5ccf0000ffff000

def z1066 : W := mkw 0xfffeef648e8000d8 0x02fffeef648e8000 0xffffffffcfc000ff 0xf7ffffffffcfc000

def z1067 : W := mkw 0x041881b01151bc80 0x20041881b01151bc 0x0cf803f033f3fcd9 0x4c0cf803f033f3fc

def z1068 : W := mkw 0x42830a860b0a8a14 0x8042830a860b0a8a 0xc38f0f8e0f0f8f74 0x6ec38f0f8e0f0f8f

def z1069 : W := mkw 0x114124c60b0a8a14 0x80114124c60b0a8a 0x3340fc7e0f0f8f7f 0xbc3340fc7e0f0f8f

def z1070 : W := mkw 0xac0dd00b700f6027 0x01ac0dd00b700f60 0xff0ffc0ffc0ff3f6 0xfbff0ffc0ffc0ff3

def z1071 : W := mkw 0xfbe22e4daea00078 0x06fbe22e4daea000 0xfff00c0ffff000f1 0xf5fff00c0ffff000

def z1072 : W := mkw 0x040dd002500f6007 0x01040dd002500f60 0xf00ff00fc00ff0f6 0xfbf00ff00fc00ff0

def z1073 : W := mkw 0xfffeef60000000c0 0x02fffeef60000000 0xfffffff0000c003f 0xfafffffff0000c00

def z1074 : W := mkw 0x11403450c4c4550a 0x4011403450c4c455 0x33c0fc71cfcc7fff 0xfd33c0fc71cfcc7f

def z1075 : W := mkw 0xeebfcbaf3b0baaf5 0x83eebfcbaf3b0baa 0xccbf038e33038040 0x42ccbf038e330380

def z1076 : W := mkw 0xfffeef69200000e0 0x02fffeef69200000 0xfffffff1f000008f 0xf3fffffff1f00000

def z1077 : W := mkw 0xac0cc00930012020 0x00ac0cc009300120 0xfc0ff00ff003f0f6 0xfbfc0ff00ff003f0

def z1078 : W := mkw 0x0419912b700f60a7 0x010419912b700f60 0x0cf883fff00ff0fb 0xd90cf883fff00ff0

def z1079 : W := mkw 0xfffeef6daea000f8 0x06fffeef6daea000 0xffffffffcff0002f 0xf7ffffffffcff000

def z1080 : W := mkw 0x00030a82010a8a04 0x8000030a82010a8a 0xc30f0f8e0c0f8f7f 0x7ec30f0f8e0c0f8f

def z1081 : W := mkw 0xac0dd00b700f6027 0x01ac0dd00b700f60 0xfc0ff00ff00ffcff 0xfffc0ff00ff00ffc

def z1082 : W := mkw 0xfffeef60000000c0 0x02fffeef60000000 0xffff7ff00000000d 0x62ffff7ff0000000

def z1083 : W := mkw 0x041fdbb2515ffe87 0xa1041fdbb2515ffe 0x000ffff0000fff0e 0x0a000ffff0000fff

def z1084 : W := mkw 0xfffeef60000000c0 0x02fffeef60000000 0xfffffff000000009 0xc2fffffff0000000

def z1085 : W := mkw 0xfbe20a0daea00038 0x04fbe20a0daea000 0xfff70c0ffff000f5 0xf7fff70c0ffff000

def z1086 : W := mkw 0xac0dd00b700f6027 0x01ac0dd00b700f60 0xf00ff00ff00ff0f6 0x2bf00ff00ff00ff0

def z1087 : W := mkw 0xfffeef69200000e0 0x02fffeef69200000 0xfffffffe3000004f 0xf2fffffffe300000

def z1088 : W := mkw 0xac0dd00b700f6027 0x01ac0dd00b700f60 0xfc0ff00ffc0ffff6 0xfffc0ff00ffc0fff

def z1089 : W := mkw 0xac3eef60000000c0 0x02ac3eef60000000 0x0c3ffff00000000e 0x020c3ffff0000000

def z1090 : W := mkw 0xfbe0000daea00038 0x04fbe0000daea000 0xfff0000ffffc0ff1 0xfdfff0000ffffc0f

def z1091 : W := mkw 0xfffeef6daea000f8 0x06fffeef6daea000 0xffffffffccc000bf 0xf7ffffffffccc000

def z1092 : W := mkw 0xea80000d2a000030 0x00ea80000d2a0000 0xfff0000ffff000f1 0xf5fff0000ffff000

def z1093 : W := mkw 0x1141245284ca150c 0x401141245284ca15 0xc34f0c7e0ccf8f7f 0x7ec34f0c7e0ccf8f

def z1094 : W := mkw 0xac3dd12b700f60e7 0x03ac3dd12b700f60 0xfc3ff00ff00ff0f6 0xfbfc3ff00ff00ff0

def z1095 : W := mkw 0xfbe0000daea00038 0x04fbe0000daea000 0xff70000ffff000f0 0xa5ff70000ffff000

def z1096 : W := mkw 0x0000000daea00038 0x040000000daea000 0x0cb0000ffff000f0 0x450cb0000ffff000

def z1097 : W := mkw 0x53c22e448e800018 0x0053c22e448e8000 0xf3cfffffcfc000ff 0xf7f3cfffffcfc000

def z1098 : W := mkw 0xfffeef6daea000f8 0x06fffeef6daea000 0xffffffffcf00007f 0xf7ffffffffcf0000

def z1099 : W := mkw 0xac1eef60000000c0 0x02ac1eef60000000 0xcc0ffff00000000e 0x42cc0ffff0000000

def z1100 : W := mkw 0xfffeef6daea000f8 0x06fffeef6daea000 0xfffffff1fff0008f 0xf7fffffff1fff000

def z1101 : W := mkw 0x041bbff2515fff86 0xe0041bbff2515fff 0x000ffff0000fff0e 0x0a000ffff0000fff

def z1102 : W := mkw 0xfbe0000daea00038 0x04fbe0000daea000 0xffff000ffff000f7 0xf7ffff000ffff000

def z1103 : W := mkw 0xac0dd00b700f6027 0x01ac0dd00b700f60 0xfc4ff07ff00ff0ff 0xfbfc4ff07ff00ff0

def z1104 : W := mkw 0x041eef60000000c0 0x02041eef60000000 0xc00ffff00000000e 0x72c00ffff0000000

def z1105 : W := mkw 0xa805500b700f6027 0x01a805500b700f60 0xf00f700ff00ff0f6 0x7bf00f700ff00ff0

def z1106 : W := mkw 0xfffeef6daea000f8 0x06fffeef6daea000 0xfffffffffcf000af 0xf3fffffffffcf000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z7,z1,z2,z8,z4,z5,z6]),(0,[z9,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z10,z6])],[(0,[z1,z2,z3,z11,z4,z5,z6]),(0,[z1,z12,z2,z3,z4,z5,z6]),(0,[z1,z13,z2,z3,z4,z14,z5]),(1,[z1,z2,z15,z4,z5,z16]),(0,[z1,z2,z3,z4,z17,z5,z6])],[(0,[z1,z18,z2,z3,z14,z5,z6]),(0,[z19,z1,z2,z3,z4,z5,z6]),(0,[z1,z13,z2,z3,z4,z5,z5])],[(0,[z20,z1,z2,z3,z4,z21,z5]),(0,[z1,z13,z2,z3,z4,z5,z22]),(0,[z23,z1,z2,z3,z4,z5,z6])],[(0,[z24,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z25,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z26]),(0,[z1,z2,z27,z3,z4,z5,z6])],[(0,[z28,z1,z2,z29,z4,z5,z6]),(0,[z30,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z31,z5,z6]),(0,[z32,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z14,z5,z33]),(0,[z1,z2,z3,z4,z5,z6,z34])],[(0,[z1,z2,z3,z4,z5,z6,z35]),(1,[z1,z2,z3,z4,z5,z36]),(0,[z1,z2,z3,z4,z5,z37,z6]),(0,[z1,z38,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z39,z5]),(0,[z1,z2,z40,z3,z4,z41,z6]),(0,[z1,z2,z3,z4,z42,z5,z6]),(0,[z43,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z44,z6]),(0,[z45,z7,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z4,z5,z46,z6]),(0,[z1,z47,z2,z3,z4,z5,z6]),(0,[z48,z1,z13,z2,z3,z4,z5])]],
   [[(0,[z1,z2,z49,z3,z4,z5,z6]),(0,[z50,z1,z2,z3,z4,z44,z6]),(0,[z1,z2,z3,z4,z51,z5,z6]),(0,[z1,z2,z3,z4,z5,z52,z6]),(0,[z1,z13,z2,z3,z53,z4,z5])],[(0,[z1,z13,z2,z3,z4,z5,z54]),(0,[z55,z1,z13,z2,z3,z4,z5]),(0,[z1,z2,z3,z56,z4,z5,z6]),(0,[z7,z1,z2,z3,z4,z5,z6]),(0,[z1,z13,z2,z3,z4,z57,z5]),(0,[z1,z2,z3,z4,z5,z58,z6]),(0,[z1,z2,z3,z4,z59,z5,z6])],[(0,[z60,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z61,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z62,z5,z6]),(0,[z63,z1,z64,z3,z4,z5,z6]),(0,[z1,z2,z65,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z66,z5,z6]),(0,[z1,z2,z3,z67,z4,z5,z33])],[(0,[z1,z2,z3,z4,z68,z5,z6]),(0,[z1,z2,z3,z4,z69,z5,z6])],[(0,[z1,z2,z3,z4,z25,z5,z33]),(0,[z70,z1,z2,z3,z4,z5,z33]),(0,[z71,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z72]),(0,[z1,z2,z3,z73,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z74]),(1,[z1,z2,z3,z4,z75,z5])],[(0,[z1,z2,z3,z4,z5,z36,z6]),(0,[z1,z2,z76,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z77,z5,z6]),(0,[z1,z78,z2,z3,z4,z5,z6])],[(0,[z79,z1,z2,z3,z4,z5,z6]),(1,[z1,z80,z2,z3,z4,z6]),(0,[z1,z2,z3,z81,z4,z5,z44]),(0,[z1,z2,z3,z4,z5,z44,z33]),(1,[z82,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z83,z4,z5,z6]),(0,[z1,z13,z2,z84,z3,z4,z5])]],
   [[(0,[z85,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z8,z3,z4,z5,z33]),(0,[z86,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z87,z6]),(0,[z1,z2,z3,z88,z4,z5,z6])],[(0,[z1,z13,z2,z3,z89,z4,z5]),(0,[z1,z2,z3,z90,z4,z5,z6]),(0,[z1,z2,z3,z91,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z92,z6]),(0,[z93,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z41,z6])],[(0,[z94,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z95,z4,z5,z6]),(0,[z1,z2,z3,z96,z4,z5,z6]),(0,[z1,z2,z3,z97,z4,z5,z6]),(0,[z1,z2,z3,z98,z4,z5,z6]),(0,[z1,z2,z3,z99,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z100,z6])],[(0,[z101,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z102,z4,z5,z6]),(0,[z2,z3,z4,z25,z5,z54,z6]),(0,[z1,z2,z3,z4,z5,z6,z103]),(0,[z1,z2,z3,z4,z57,z5,z6]),(0,[z1,z2,z3,z81,z5,z6,z104])],[(0,[z105,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z106]),(1,[z1,z2,z3,z4,z107,z6]),(1,[z1,z2,z3,z4,z5,z108]),(0,[z109,z1,z2,z89,z4,z5,z6]),(0,[z110,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z111]),(0,[z1,z2,z3,z4,z112,z5,z6])],[(0,[z1,z2,z3,z4,z5,z113,z6]),(0,[z45,z1,z2,z3,z4,z5,z6]),(0,[z114,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z115,z5,z6]),(0,[z1,z2,z40,z3,z4,z57,z6]),(0,[z1,z2,z3,z116,z4,z5,z6]),(0,[z117,z1,z2,z3,z4,z118,z6])]],
   [[(0,[z1,z2,z119,z3,z4,z5,z6]),(0,[z1,z2,z8,z3,z120,z5,z6]),(0,[z1,z2,z3,z121,z4,z5,z6]),(0,[z1,z2,z40,z3,z4,z5,z33]),(0,[z1,z2,z3,z4,z122,z5,z6])],[(0,[z1,z2,z3,z4,z123,z5,z6]),(0,[z1,z2,z3,z124,z4,z5,z6]),(0,[z1,z125,z2,z3,z4,z5,z6]),(0,[z1,z126,z2,z3,z4,z39,z5])],[(0,[z1,z2,z3,z127,z5,z128,z6]),(1,[z1,z2,z3,z4,z129,z6]),(0,[z130,z1,z2,z3,z4,z5,z6])],[(0,[z131,z1,z2,z3,z21,z5,z6]),(0,[z1,z2,z3,z4,z5,z132,z6]),(0,[z1,z2,z3,z133,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z134,z16]),(0,[z1,z2,z3,z4,z5,z33,z135])],[(0,[z136,z1,z2,z3,z21,z5,z6]),(0,[z109,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z137,z5,z6]),(0,[z138,z1,z2,z3,z4,z5,z33])],[(0,[z139,z64,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z140,z6]),(0,[z50,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z120,z4,z141,z5,z6]),(0,[z1,z2,z3,z4,z5,z142,z6])],[(0,[z1,z2,z3,z4,z5,z143,z6]),(0,[z144,z1,z2,z3,z4,z5,z6]),(0,[z1,z145,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z146,z6])],[(0,[z147,z1,z2,z3,z4,z5,z6]),(0,[z148,z1,z2,z3,z4,z5,z6]),(0,[z1,z13,z149,z2,z3,z4,z5])]],
   [[(0,[z150,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z151,z5,z6]),(0,[z152,z1,z2,z15,z4,z5,z6]),(0,[z1,z2,z15,z3,z4,z87,z6]),(0,[z1,z2,z3,z4,z5,z33,z153]),(0,[z1,z2,z3,z4,z5,z154,z6])],[(0,[z1,z2,z3,z155,z4,z5,z6]),(0,[z1,z13,z2,z3,z120,z4,z5]),(0,[z1,z2,z3,z4,z156,z5,z6]),(0,[z1,z2,z3,z4,z157,z5,z6]),(0,[z1,z2,z3,z158,z4,z5,z6])],[(0,[z1,z2,z3,z4,z159,z5,z6]),(0,[z1,z2,z3,z4,z160,z5,z6]),(0,[z1,z2,z3,z4,z161,z5,z6])],[(0,[z162,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z163,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z164,z6]),(0,[z1,z2,z3,z165,z4,z5,z6]),(0,[z1,z2,z166,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z5,z33])],[(0,[z1,z2,z3,z167,z4,z5,z6]),(1,[z1,z149,z3,z4,z5,z134]),(0,[z1,z168,z2,z3,z4,z5,z6]),(0,[z1,z169,z2,z3,z4,z5,z6])],[(0,[z1,z2,z170,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z171,z5,z6]),(0,[z1,z2,z3,z4,z5,z172,z6]),(0,[z1,z2,z3,z4,z5,z6,z173]),(0,[z1,z2,z3,z174,z4,z5,z33])],[(0,[z175,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z54,z6]),(1,[z50,z1,z2,z3,z4,z6]),(0,[z1,z176,z2,z3,z4,z5,z6]),(0,[z177,z1,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z178,z4,z5,z6]),(0,[z179,z1,z2,z3,z4,z5,z6]),(0,[z1,z180,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z181]),(0,[z182,z1,z2,z3,z4,z5,z6]),(0,[z1,z183,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z33,z134])],[(0,[z184,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z185,z6]),(0,[z1,z2,z3,z186,z4,z5,z6]),(0,[z1,z2,z187,z3,z4,z5,z6]),(0,[z1,z2,z3,z188,z4,z5,z6]),(0,[z189,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z190]),(0,[z1,z13,z2,z3,z4,z5,z190]),(0,[z1,z2,z3,z191,z4,z5,z6])],[(0,[z1,z2,z192,z3,z4,z5,z6]),(0,[z1,z2,z3,z193,z4,z5,z6]),(0,[z1,z194,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z128,z33])],[(0,[z1,z64,z2,z3,z4,z5,z6]),(0,[z1,z195,z2,z3,z4,z5,z6]),(0,[z1,z2,z196,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z197,z5,z6]),(0,[z1,z169,z2,z3,z4,z5,z33])],[(0,[z198,z1,z2,z3,z4,z5,z6]),(0,[z1,z199,z3,z89,z4,z5,z6]),(0,[z45,z1,z13,z2,z3,z4,z5]),(0,[z1,z2,z3,z200,z4,z5,z6]),(0,[z1,z2,z3,z4,z57,z22,z6]),(0,[z1,z2,z3,z4,z201,z5,z6]),(0,[z1,z13,z2,z3,z202,z4,z5])],[(0,[z55,z2,z3,z4,z5,z6,z190]),(0,[z1,z2,z3,z4,z203,z5,z6]),(0,[z70,z152,z1,z2,z3,z4,z5]),(0,[z204,z1,z2,z3,z4,z5,z6])]],
   [[(0,[z205,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z206,z6]),(0,[z1,z207,z2,z3,z4,z5,z6])],[(1,[z1,z2,z40,z4,z41,z6]),(0,[z1,z13,z2,z40,z3,z4,z5]),(0,[z1,z2,z3,z4,z208,z5,z6]),(0,[z1,z2,z3,z4,z209,z5,z33])],[(0,[z1,z2,z3,z4,z210,z5,z6]),(0,[z1,z211,z2,z3,z4,z25,z5]),(0,[z1,z2,z3,z212,z4,z5,z6])],[(0,[z109,z1,z13,z2,z3,z4,z5]),(0,[z48,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z213,z5,z6]),(0,[z1,z2,z3,z4,z214,z5,z6]),(0,[z1,z13,z2,z3,z4,z5,z33]),(0,[z1,z2,z3,z4,z5,z6,z33])],[(0,[z1,z2,z3,z4,z215,z5,z6]),(0,[z1,z2,z216,z3,z4,z5,z6]),(0,[z1,z2,z3,z217,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z218,z6]),(1,[z1,z2,z3,z4,z41,z33])],[(0,[z219,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z220,z3,z4,z5,z6]),(0,[z221,z1,z2,z3,z4,z5,z6]),(0,[z1,z222,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z223,z4,z5,z6])],[(0,[z1,z2,z3,z4,z224,z5,z6]),(0,[z1,z2,z225,z3,z4,z5,z6])],[(0,[z1,z2,z3,z120,z14,z5,z6]),(0,[z1,z2,z3,z4,z226,z5,z6]),(0,[z117,z1,z2,z3,z4,z227,z6]),(0,[z1,z2,z3,z4,z228,z5,z6])]],
   [[(0,[z229,z1,z2,z3,z21,z5,z6]),(0,[z230,z1,z2,z3,z4,z5,z6]),(0,[z70,z1,z149,z3,z4,z5,z6]),(0,[z1,z2,z3,z231,z4,z5,z6]),(0,[z232,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z233])],[(0,[z1,z2,z3,z4,z5,z234,z6]),(1,[z1,z2,z3,z235,z5,z6])],[(0,[z1,z64,z3,z4,z5,z22,z6])],[(0,[z1,z2,z3,z4,z5,z236,z6]),(0,[z1,z2,z3,z4,z237,z5,z6]),(0,[z1,z2,z8,z120,z4,z5,z6]),(0,[z1,z238,z2,z3,z4,z5,z6])],[(0,[z239,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z240,z4,z5,z6]),(0,[z152,z1,z2,z3,z4,z122,z5]),(0,[z1,z2,z3,z4,z241,z5,z6]),(0,[z1,z168,z13,z2,z3,z4,z5])],[(0,[z242,z2,z3,z4,z25,z5,z6]),(0,[z1,z2,z3,z243,z4,z5,z6])],[(0,[z244,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z81,z4,z5,z190]),(0,[z245,z1,z2,z3,z4,z5,z6]),(0,[z1,z3,z4,z227,z5,z22,z6]),(0,[z1,z2,z3,z4,z5,z22,z33]),(0,[z1,z2,z3,z4,z122,z246,z5])],[(0,[z28,z247,z2,z3,z4,z5,z6]),(0,[z45,z1,z2,z3,z14,z5,z6]),(0,[z1,z2,z15,z3,z4,z122,z5]),(0,[z1,z2,z3,z53,z4,z128,z6]),(0,[z1,z2,z3,z4,z5,z248,z6]),(1,[z1,z2,z3,z4,z118,z33])]],
   [[(0,[z1,z82,z2,z3,z4,z5,z6]),(0,[z249,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z250,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z251,z6]),(0,[z1,z2,z3,z4,z252,z5,z6]),(0,[z1,z2,z3,z253,z4,z5,z6]),(0,[z1,z13,z2,z3,z212,z4,z5])],[(0,[z1,z2,z254,z3,z4,z5,z6]),(0,[z1,z13,z2,z3,z4,z6,z33])],[(0,[z1,z2,z3,z255,z4,z5,z6]),(0,[z229,z256,z2,z3,z4,z5,z6]),(0,[z257,z1,z2,z3,z4,z5,z6]),(0,[z258,z1,z2,z3,z4,z5,z6])],[(0,[z1,z259,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z260,z5,z6]),(0,[z1,z2,z261,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z262,z6]),(0,[z1,z2,z3,z4,z263,z5,z6]),(1,[z1,z2,z3,z264,z4,z5])],[(0,[z265,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z67,z4,z5,z6]),(0,[z266,z1,z2,z3,z4,z5,z6]),(0,[z198,z1,z13,z2,z3,z4,z5])],[(0,[z1,z2,z3,z4,z267,z5,z6]),(0,[z1,z2,z3,z268,z4,z5,z6]),(0,[z1,z2,z40,z4,z5,z41,z6]),(0,[z204,z1,z13,z2,z3,z4,z5])],[(0,[z70,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z81,z4,z5,z33])]],
   [[(0,[z1,z2,z3,z4,z269,z5,z6]),(0,[z270,z1,z2,z3,z4,z5,z6]),(0,[z271,z1,z2,z3,z4,z5,z6]),(0,[z249,z1,z2,z3,z4,z5,z33])],[(0,[z272,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z273,z6]),(0,[z1,z2,z274,z3,z4,z5,z6])],[(0,[z1,z2,z3,z275,z4,z5,z6]),(0,[z1,z2,z3,z276,z4,z5,z6]),(0,[z277,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z278,z5,z6]),(0,[z279,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z280,z6]),(0,[z281,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z8,z3,z4,z5,z6]),(0,[z282,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z283,z6])],[(0,[z284,z1,z49,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z285,z6]),(0,[z1,z2,z3,z286,z4,z5,z6]),(0,[z1,z2,z3,z287,z4,z5,z6]),(0,[z1,z2,z15,z4,z5,z6,z16])],[(0,[z288,z1,z2,z3,z4,z5,z6])],[(0,[z289,z1,z180,z3,z4,z5,z6]),(0,[z289,z1,z2,z3,z4,z25,z6]),(0,[z1,z2,z3,z290,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z291,z6])],[(0,[z1,z292,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z293,z5,z6]),(0,[z294,z1,z2,z3,z4,z5,z6]),(0,[z7,z1,z18,z2,z3,z5,z6]),(0,[z117,z1,z2,z3,z4,z41,z6]),(0,[z1,z2,z3,z295,z4,z5,z6]),(0,[z1,z2,z3,z296,z4,z5,z6])]],
   [[(0,[z1,z2,z297,z3,z4,z5,z6]),(0,[z1,z2,z298,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z299,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z300]),(0,[z1,z2,z3,z4,z5,z301,z6]),(0,[z302,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z303,z5,z6]),(0,[z1,z2,z3,z4,z5,z304,z6])],[(0,[z1,z13,z2,z3,z127,z4,z5]),(0,[z1,z2,z305,z3,z4,z5,z6]),(1,[z1,z2,z3,z306,z5,z6]),(1,[z182,z2,z3,z4,z5,z6]),(0,[z109,z1,z2,z199,z4,z5,z6]),(0,[z1,z2,z3,z4,z307,z5,z6]),(0,[z136,z1,z2,z3,z53,z5,z6])],[(0,[z1,z308,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z34]),(0,[z1,z2,z40,z3,z4,z5,z6])],[(0,[z309,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z310,z5,z6]),(0,[z1,z2,z3,z311,z4,z5,z6]),(0,[z1,z312,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z313,z4,z5,z6]),(0,[z314,z1,z2,z3,z4,z5,z6]),(0,[z289,z1,z2,z3,z4,z5,z315]),(0,[z1,z316,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z317,z5,z104])],[(0,[z229,z2,z3,z127,z4,z5,z6]),(0,[z318,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z319,z5,z6]),(0,[z320,z1,z2,z3,z4,z41,z6]),(0,[z1,z2,z3,z264,z4,z57,z5])],[(0,[z1,z2,z3,z321,z4,z5,z6]),(0,[z322,z1,z2,z3,z4,z5,z6]),(0,[z1,z13,z2,z192,z3,z4,z5]),(0,[z256,z1,z2,z3,z127,z5,z6]),(1,[z20,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z323,z4,z5,z6]),(0,[z138,z1,z2,z3,z4,z5,z6]),(1,[z136,z1,z2,z3,z212,z6]),(0,[z136,z1,z2,z3,z212,z4,z6])]],
   [[(0,[z139,z1,z64,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z324,z5,z6]),(0,[z1,z2,z3,z4,z325,z5,z6]),(0,[z1,z2,z326,z3,z4,z5,z6]),(0,[z327,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z328,z4,z5,z6])],[(0,[z329,z1,z2,z3,z4,z5,z6]),(0,[z1,z80,z2,z3,z4,z21,z6]),(0,[z330,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z331,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z332]),(0,[z1,z2,z333,z3,z4,z5,z6]),(0,[z117,z1,z2,z3,z4,z5,z6])],[(1,[z1,z2,z334,z3,z4,z5]),(0,[z131,z1,z2,z3,z4,z5,z6]),(0,[z258,z1,z13,z2,z3,z4,z5])],[(0,[z335,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z21,z5,z33]),(1,[z1,z2,z3,z4,z5,z74]),(0,[z1,z2,z199,z3,z4,z5,z33]),(0,[z136,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z336,z5,z6]),(0,[z1,z2,z3,z4,z5,z337,z6]),(0,[z1,z2,z3,z120,z67,z5,z6]),(0,[z1,z338,z2,z3,z4,z5,z6]),(0,[z1,z2,z339,z3,z4,z5,z6]),(0,[z1,z149,z2,z3,z4,z340,z6]),(0,[z1,z2,z3,z4,z5,z6,z16]),(0,[z1,z13,z2,z3,z4,z5,z16]),(0,[z1,z2,z341,z3,z4,z5,z6]),(0,[z1,z13,z2,z3,z158,z4,z5])],[(0,[z342,z1,z2,z3,z4,z5,z6]),(0,[z343,z1,z2,z3,z4,z5,z33])],[(0,[z1,z2,z3,z4,z5,z344,z6]),(0,[z1,z2,z3,z345,z4,z5,z6]),(0,[z1,z2,z3,z127,z5,z6,z104]),(1,[z55,z2,z3,z4,z5,z190]),(0,[z1,z2,z346,z3,z4,z5,z6]),(0,[z1,z149,z2,z3,z4,z246,z5]),(0,[z1,z2,z3,z4,z347,z5,z6]),(0,[z70,z1,z13,z2,z3,z4,z5])],[(0,[z1,z2,z3,z4,z5,z5,z6]),(1,[z1,z2,z3,z4,z227,z33]),(0,[z1,z2,z3,z4,z246,z5,z33]),(0,[z1,z2,z3,z4,z348,z5,z6]),(0,[z1,z349,z2,z3,z4,z5,z6]),(0,[z350,z1,z2,z3,z4,z5,z6]),(0,[z351,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z202,z4,z5,z6])]],
   [[(0,[z256,z1,z2,z3,z4,z5,z36]),(1,[z1,z180,z3,z4,z5,z6]),(0,[z1,z2,z3,z352,z4,z5,z6]),(0,[z1,z2,z3,z4,z353,z5,z6]),(0,[z1,z2,z3,z4,z354,z5,z6]),(0,[z1,z2,z3,z4,z355,z5,z6]),(0,[z117,z1,z2,z3,z4,z57,z6]),(0,[z1,z356,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z357,z5,z6]),(0,[z1,z2,z192,z4,z5,z41,z6]),(0,[z1,z2,z3,z4,z5,z358,z6]),(0,[z1,z2,z3,z174,z4,z5,z6]),(0,[z117,z1,z2,z3,z4,z5,z33])],[(0,[z1,z2,z3,z359,z4,z5,z6]),(0,[z131,z1,z2,z3,z4,z5,z33]),(0,[z282,z1,z13,z2,z3,z4,z5])],[(1,[z1,z2,z3,z4,z360,z6]),(0,[z1,z2,z3,z4,z141,z5,z6]),(0,[z136,z1,z2,z3,z4,z5,z33])],[(0,[z361,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z362,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z363]),(0,[z1,z2,z3,z4,z5,z364,z6]),(0,[z365,z1,z2,z3,z4,z5,z6])],[(0,[z366,z1,z2,z3,z4,z5,z6]),(0,[z1,z13,z64,z2,z3,z4,z5]),(0,[z1,z2,z3,z367,z4,z5,z6]),(1,[z242,z2,z3,z4,z25,z6]),(0,[z368,z1,z2,z3,z4,z5,z33])],[(0,[z369,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z370,z5,z6]),(0,[z371,z1,z2,z3,z4,z5,z6]),(0,[z1,z13,z2,z8,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z128,z6]),(0,[z372,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z373,z6]),(0,[z289,z1,z2,z76,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z315]),(0,[z374,z1,z2,z3,z4,z5,z6]),(0,[z1,z375,z2,z3,z4,z5,z6]),(0,[z1,z13,z376,z2,z3,z4,z5])]],
   [[(0,[z377,z1,z2,z3,z4,z5,z6]),(0,[z378,z1,z2,z3,z4,z5,z6]),(0,[z1,z379,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z22,z41,z6])],[(0,[z247,z139,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z380,z5,z6]),(0,[z1,z2,z3,z4,z107,z5,z6]),(0,[z381,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z382,z3,z4,z5,z33])],[(0,[z1,z2,z3,z383,z4,z5,z6]),(0,[z1,z2,z3,z384,z4,z5,z6]),(0,[z1,z2,z3,z4,z385,z5,z6]),(0,[z1,z18,z2,z3,z67,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z386]),(0,[z1,z126,z2,z3,z4,z227,z6]),(0,[z1,z2,z3,z4,z387,z5,z6]),(0,[z1,z388,z2,z3,z4,z5,z6])],[(0,[z117,z242,z1,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z306,z5,z6]),(0,[z389,z1,z2,z3,z4,z5,z44]),(0,[z1,z2,z3,z4,z141,z5,z33]),(0,[z1,z2,z3,z390,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z33,z190]),(0,[z45,z1,z2,z8,z3,z5,z6]),(0,[z1,z3,z4,z246,z5,z6,z134]),(0,[z1,z2,z391,z3,z4,z5,z6]),(0,[z1,z392,z2,z3,z4,z5,z6]),(0,[z393,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z209,z5,z6])],[(0,[z247,z1,z2,z3,z4,z5,z33]),(0,[z394,z1,z2,z3,z4,z5,z6]),(0,[z289,z1,z2,z3,z53,z4,z6]),(0,[z136,z242,z1,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z395,z5,z6]),(0,[z396,z1,z2,z3,z4,z5,z6]),(0,[z1,z149,z2,z3,z4,z5,z134]),(0,[z70,z1,z2,z3,z4,z246,z5])],[(0,[z397,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z398,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z6]),(0,[z63,z1,z2,z3,z4,z227,z6]),(0,[z1,z399,z2,z3,z4,z5,z6]),(0,[z400,z1,z2,z3,z4,z5,z6]),(0,[z1,z13,z2,z3,z317,z4,z5]),(0,[z1,z13,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z401,z6]),(0,[z256,z1,z2,z3,z4,z5,z106]),(0,[z289,z1,z2,z3,z4,z5,z33]),(0,[z109,z82,z2,z3,z4,z5,z6])]],
   [[(0,[z284,z139,z2,z3,z4,z5,z6]),(0,[z63,z1,z49,z3,z4,z5,z6]),(0,[z402,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z403,z4,z5,z6]),(0,[z117,z1,z13,z2,z3,z4,z5])],[(0,[z1,z2,z3,z4,z5,z404,z6]),(0,[z1,z405,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z406]),(0,[z1,z2,z407,z3,z4,z5,z6]),(0,[z131,z1,z13,z2,z3,z4,z5])],[(0,[z289,z1,z2,z3,z4,z54,z6]),(0,[z1,z2,z408,z3,z4,z5,z6]),(0,[z409,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z410,z3,z4,z5,z6]),(0,[z136,z1,z13,z2,z3,z4,z5])],[(0,[z411,z1,z2,z3,z4,z5,z6]),(0,[z1,z412,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z413,z4,z5,z6]),(0,[z1,z414,z2,z3,z4,z5,z33]),(0,[z1,z2,z3,z415,z4,z5,z6]),(0,[z1,z2,z3,z390,z4,z5,z33]),(0,[z1,z13,z416,z2,z3,z4,z5])],[(0,[z284,z1,z2,z3,z4,z5,z33]),(0,[z1,z2,z3,z417,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z173])],[(0,[z109,z1,z2,z3,z4,z107,z6]),(0,[z109,z1,z2,z3,z4,z5,z108]),(0,[z418,z1,z2,z3,z89,z5,z6]),(0,[z418,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z419,z5,z6]),(0,[z1,z2,z3,z4,z420,z5,z6]),(0,[z421,z1,z2,z3,z4,z5,z33]),(0,[z1,z2,z3,z4,z5,z33,z33])],[(0,[z1,z2,z3,z422,z4,z21,z6]),(0,[z70,z1,z3,z4,z246,z5,z6]),(0,[z351,z1,z13,z2,z3,z4,z5]),(0,[z1,z13,z2,z3,z4,z423,z5])],[(0,[z1,z2,z3,z424,z4,z5,z6])]],
   [[(0,[z1,z425,z2,z3,z4,z5,z6]),(0,[z426,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z427,z5,z6]),(1,[z1,z2,z76,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z22,z6]),(1,[z117,z1,z13,z2,z3,z4])],[(0,[z1,z2,z3,z4,z5,z428,z6]),(0,[z1,z2,z3,z4,z5,z429,z6]),(0,[z109,z1,z2,z3,z4,z129,z6]),(0,[z1,z2,z3,z430,z89,z4,z5]),(0,[z1,z2,z3,z4,z5,z6,z431]),(0,[z432,z1,z2,z3,z4,z5,z6]),(0,[z152,z1,z149,z2,z3,z4,z5]),(0,[z433,z1,z2,z3,z4,z5,z6]),(0,[z1,z13,z2,z3,z4,z5,z41]),(0,[z1,z2,z3,z4,z5,z434,z6])],[(0,[z1,z2,z435,z3,z4,z5,z6]),(0,[z1,z2,z3,z317,z4,z5,z33])],[(0,[z436,z1,z2,z3,z4,z5,z6]),(0,[z1,z437,z2,z3,z4,z5,z6]),(0,[z256,z2,z3,z4,z21,z5,z6]),(0,[z1,z2,z438,z3,z4,z5,z6])],[(0,[z439,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z440]),(0,[z1,z2,z334,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z441,z6])],[(0,[z1,z2,z3,z4,z5,z6,z442]),(0,[z1,z2,z3,z4,z5,z315,z6]),(0,[z289,z1,z2,z3,z4,z6,z33]),(0,[z443,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z444]),(0,[z229,z1,z2,z3,z4,z5,z33]),(0,[z55,z1,z2,z3,z4,z5,z44])]],
   [[(0,[z1,z2,z445,z3,z4,z5,z6])],[(0,[z446,z1,z2,z3,z4,z5,z6]),(0,[z389,z55,z2,z3,z4,z5,z6]),(0,[z447,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z448,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z33])],[(0,[z1,z2,z3,z4,z449,z5,z6]),(0,[z1,z2,z3,z81,z317,z4,z5]),(0,[z1,z2,z3,z81,z4,z5,z6])],[(0,[z1,z2,z3,z235,z89,z5,z6]),(0,[z1,z2,z3,z235,z4,z5,z6]),(0,[z1,z2,z3,z450,z4,z5,z6]),(0,[z451,z1,z2,z3,z4,z5,z6]),(0,[z45,z1,z18,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z340,z6]),(1,[z1,z2,z3,z4,z172,z6]),(0,[z1,z2,z3,z212,z4,z75,z5])],[(0,[z1,z2,z3,z4,z5,z6,z452])],[(0,[z64,z2,z49,z3,z4,z5,z6]),(0,[z1,z2,z453,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z454,z6]),(0,[z1,z2,z3,z4,z455,z5,z6]),(0,[z63,z1,z3,z4,z227,z5,z6]),(0,[z1,z13,z13,z2,z3,z4,z5])],[(0,[z1,z2,z3,z4,z5,z44,z104]),(0,[z1,z2,z3,z53,z5,z128,z6]),(1,[z1,z2,z3,z4,z5,z233])],[(0,[z284,z2,z49,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z68,z21,z5]),(0,[z20,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z456,z6])]],
   [[(0,[z1,z457,z2,z3,z4,z5,z6]),(0,[z55,z1,z2,z3,z306,z5,z6]),(0,[z1,z2,z3,z4,z458,z5,z6]),(0,[z1,z2,z3,z4,z246,z5,z16]),(1,[z1,z2,z3,z4,z57,z33]),(0,[z459,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z127,z4,z5,z6]),(0,[z289,z117,z1,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z22,z6,z33]),(0,[z460,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z461,z4,z5,z6])],[(0,[z1,z462,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z463,z5,z6]),(0,[z320,z1,z2,z192,z4,z5,z6]),(0,[z136,z1,z2,z3,z212,z5,z6]),(0,[z1,z2,z3,z317,z5,z6,z104]),(0,[z1,z2,z84,z3,z4,z5,z6])],[(0,[z1,z464,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z465,z4,z5,z6]),(0,[z1,z2,z3,z466,z4,z5,z6]),(0,[z1,z126,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z118,z5,z6])],[(0,[z467,z1,z2,z3,z4,z5,z6]),(0,[z1,z468,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z227,z41,z6]),(0,[z1,z2,z40,z3,z4,z469,z5])],[(0,[z1,z2,z3,z422,z4,z5,z6]),(0,[z1,z2,z3,z331,z4,z5,z6]),(0,[z470,z1,z2,z3,z4,z5,z6]),(0,[z152,z1,z2,z3,z4,z5,z33])],[(0,[z1,z2,z471,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z472,z5,z6]),(0,[z1,z2,z473,z3,z4,z5,z6]),(0,[z474,z1,z2,z3,z4,z5,z6]),(0,[z1,z416,z2,z3,z4,z5,z6])]],
   [[(0,[z247,z1,z2,z192,z4,z5,z6]),(0,[z1,z149,z2,z15,z3,z4,z5]),(0,[z1,z2,z3,z4,z122,z5,z134]),(0,[z7,z1,z2,z4,z141,z5,z6]),(0,[z1,z2,z3,z4,z5,z475,z6]),(1,[z1,z13,z2,z3,z4,z5])],[(0,[z1,z2,z3,z127,z4,z5,z33]),(1,[z1,z2,z3,z476,z5,z6]),(0,[z63,z1,z126,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z477,z5,z6]),(0,[z1,z2,z478,z3,z4,z5,z6]),(0,[z1,z2,z15,z3,z4,z5,z33]),(0,[z1,z479,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z480]),(0,[z1,z481,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z482,z5,z6]),(0,[z1,z2,z3,z483,z53,z4,z5])],[(0,[z484,z1,z2,z3,z4,z5,z6]),(1,[z242,z1,z2,z3,z4,z33]),(0,[z1,z2,z3,z4,z5,z485,z6]),(0,[z1,z2,z486,z3,z4,z5,z6]),(0,[z1,z487,z2,z3,z4,z5,z6]),(0,[z1,z2,z15,z3,z4,z172,z6])],[(0,[z1,z13,z2,z3,z29,z4,z5]),(0,[z256,z1,z2,z3,z21,z5,z6]),(0,[z1,z2,z3,z430,z4,z5,z6]),(1,[z1,z126,z3,z4,z22,z6]),(0,[z1,z126,z2,z3,z4,z5,z33]),(0,[z1,z13,z2,z3,z4,z246,z5]),(0,[z488,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z4,z122,z5,z6,z16]),(0,[z1,z2,z3,z4,z118,z5,z33])],[(0,[z1,z2,z3,z21,z5,z128,z6]),(0,[z489,z1,z2,z3,z89,z4,z5]),(0,[z490,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z491])],[(0,[z1,z492,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z21,z5,z6]),(1,[z1,z2,z3,z4,z234,z6]),(0,[z1,z2,z199,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z493,z5,z6]),(0,[z1,z2,z3,z14,z141,z5,z6]),(0,[z1,z2,z40,z3,z4,z5,z494]),(0,[z1,z2,z3,z4,z57,z5,z495]),(0,[z1,z2,z3,z4,z423,z5,z6])],[(0,[z7,z1,z2,z3,z141,z5,z6]),(0,[z496,z1,z2,z3,z4,z5,z6]),(0,[z497,z1,z2,z3,z4,z5,z6])]],
   [[(0,[z498,z1,z2,z3,z4,z5,z6]),(0,[z343,z1,z2,z3,z4,z5,z6]),(0,[z63,z1,z2,z3,z4,z5,z33]),(0,[z131,z1,z2,z3,z81,z4,z5])],[(0,[z499,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z500,z4,z5,z6]),(0,[z1,z2,z3,z4,z501,z5,z6]),(0,[z1,z2,z3,z4,z502,z5,z6])],[(0,[z1,z2,z3,z4,z503,z5,z6]),(0,[z389,z1,z2,z3,z4,z5,z190]),(0,[z1,z2,z3,z89,z4,z5,z33]),(0,[z1,z13,z18,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z246,z5,z6]),(0,[z1,z2,z3,z504,z4,z5,z6])],[(0,[z131,z1,z2,z3,z127,z5,z6]),(0,[z505,z1,z2,z3,z4,z5,z6]),(0,[z389,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z22,z33]),(0,[z1,z2,z506,z3,z4,z5,z6]),(0,[z1,z507,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z508]),(0,[z136,z1,z2,z3,z127,z5,z6]),(0,[z1,z2,z509,z3,z4,z5,z6])],[(0,[z1,z510,z2,z3,z4,z5,z6]),(0,[z152,z1,z13,z2,z3,z4,z5]),(0,[z511,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z512,z5,z6])],[(0,[z289,z1,z2,z96,z4,z5,z6]),(0,[z1,z2,z3,z4,z513,z5,z6]),(0,[z514,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z33,z16])],[(0,[z1,z2,z3,z4,z515,z5,z6]),(0,[z1,z18,z2,z3,z4,z5,z33]),(0,[z70,z1,z2,z15,z3,z4,z5]),(0,[z1,z2,z3,z4,z516,z5,z6])]],
   [[(0,[z368,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z517,z3,z4,z5,z6]),(0,[z1,z2,z518,z3,z4,z5,z6])],[(0,[z519,z1,z2,z3,z4,z5,z6]),(1,[z489,z1,z2,z3,z4,z5]),(0,[z1,z13,z2,z3,z67,z4,z5]),(0,[z1,z2,z3,z4,z5,z520,z6])],[(0,[z1,z2,z3,z4,z44,z234,z6]),(0,[z521,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z522,z4,z5,z6]),(0,[z1,z523,z2,z3,z4,z5,z6]),(0,[z1,z524,z2,z3,z4,z5,z6])],[(0,[z525,z1,z2,z3,z4,z5,z6]),(0,[z389,z1,z2,z3,z4,z5,z33]),(0,[z1,z2,z3,z4,z5,z6,z134]),(0,[z320,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z118,z6,z33])],[(0,[z1,z2,z3,z4,z526,z5,z6]),(0,[z1,z2,z382,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z527,z6]),(0,[z1,z13,z2,z199,z3,z4,z5]),(0,[z136,z1,z2,z3,z4,z128,z6])],[(0,[z528,z1,z2,z3,z4,z5,z6]),(0,[z1,z529,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z530]),(0,[z1,z531,z2,z3,z4,z5,z6]),(0,[z1,z2,z532,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z533,z6]),(0,[z1,z13,z2,z3,z4,z5,z128])],[(0,[z534,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z276,z5,z6]),(0,[z1,z414,z2,z89,z4,z5,z6]),(0,[z45,z1,z2,z3,z67,z5,z6]),(1,[z1,z2,z3,z4,z5,z332]),(0,[z535,z1,z2,z3,z4,z5,z6]),(0,[z536,z1,z2,z3,z4,z5,z6])]],
   [[(0,[z247,z1,z2,z3,z4,z5,z6]),(0,[z320,z1,z2,z40,z4,z5,z6]),(0,[z1,z2,z3,z537,z4,z5,z6])],[(0,[z538,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z539,z3,z4,z5,z6]),(0,[z1,z13,z126,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z41,z6,z33]),(0,[z1,z540,z13,z2,z3,z4,z5])],[(0,[z28,z1,z2,z3,z4,z5,z33]),(0,[z289,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z190,z104]),(0,[z320,z1,z2,z3,z4,z57,z6]),(0,[z1,z2,z3,z4,z5,z6,z104]),(0,[z1,z13,z2,z3,z4,z5,z104])],[(0,[z1,z2,z3,z4,z293,z5,z6]),(0,[z320,z1,z2,z3,z4,z5,z33]),(0,[z1,z2,z3,z541,z4,z5,z6]),(0,[z1,z2,z542,z3,z4,z5,z6])],[(0,[z543,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z544,z6]),(0,[z1,z2,z3,z4,z39,z5,z6]),(0,[z1,z2,z3,z4,z545,z5,z6]),(0,[z1,z13,z2,z3,z81,z4,z5])],[(0,[z546,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z547,z4,z5,z6]),(0,[z289,z1,z398,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z495]),(0,[z548,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z549]),(0,[z55,z1,z2,z3,z4,z5,z190]),(0,[z1,z550,z2,z3,z4,z5,z6]),(0,[z1,z414,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z551])],[(0,[z284,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z422,z4,z6]),(1,[z1,z2,z3,z4,z68,z5]),(0,[z1,z2,z3,z4,z552,z5,z6]),(0,[z289,z242,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z57,z227,z6]),(0,[z1,z2,z3,z553,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z554]),(0,[z555,z1,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z556,z4,z5,z6]),(0,[z557,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z96,z4,z5,z6]),(0,[z421,z1,z2,z3,z4,z5,z6])],[(0,[z558,z1,z2,z3,z4,z5,z6]),(0,[z1,z559,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z560,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z494]),(0,[z561,z1,z2,z3,z4,z5,z6])],[(0,[z562,z1,z2,z3,z4,z5,z6]),(1,[z1,z211,z2,z3,z4,z5]),(0,[z1,z563,z2,z3,z4,z5,z6]),(0,[z389,z1,z13,z2,z3,z4,z5])],[(0,[z1,z2,z3,z4,z25,z5,z181]),(0,[z1,z149,z3,z4,z5,z6,z134]),(0,[z1,z2,z3,z4,z564,z5,z6])],[(0,[z1,z2,z3,z4,z5,z565,z6]),(1,[z139,z64,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z566,z5,z6]),(0,[z1,z80,z2,z3,z4,z5,z6]),(0,[z1,z18,z3,z67,z4,z5,z6]),(0,[z1,z2,z3,z4,z227,z5,z34]),(0,[z1,z2,z567,z3,z4,z5,z6])],[(0,[z568,z1,z2,z3,z4,z5,z6])],[(1,[z109,z1,z89,z4,z5,z6]),(0,[z117,z1,z2,z3,z4,z22,z6]),(0,[z1,z2,z3,z4,z569,z5,z6]),(0,[z1,z2,z3,z317,z4,z5,z6]),(0,[z1,z570,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z571,z5,z6]),(0,[z1,z211,z2,z3,z4,z5,z6]),(0,[z55,z1,z2,z3,z4,z5,z33]),(0,[z2,z3,z4,z5,z44,z6,z190]),(0,[z152,z1,z2,z3,z4,z5,z16]),(0,[z1,z2,z3,z4,z5,z6,z572]),(0,[z131,z1,z2,z3,z317,z5,z6]),(0,[z368,z1,z13,z2,z3,z4,z5])]],
   [[(0,[z573,z1,z2,z3,z4,z5,z6]),(1,[z1,z18,z3,z67,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z574]),(0,[z575,z1,z2,z3,z4,z5,z6]),(0,[z1,z576,z2,z3,z4,z5,z6])],[(1,[z45,z1,z3,z14,z5,z6])],[(0,[z229,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z577,z4,z5,z6]),(0,[z1,z126,z2,z3,z4,z5,z332]),(0,[z578,z1,z2,z3,z4,z5,z6]),(0,[z320,z1,z13,z2,z3,z4,z5]),(0,[z579,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z15,z3,z4,z5,z16]),(1,[z1,z2,z3,z53,z128,z6]),(0,[z525,z1,z13,z2,z3,z4,z5])],[(0,[z289,z136,z1,z2,z3,z4,z6]),(0,[z1,z2,z580,z3,z4,z5,z6]),(0,[z1,z2,z3,z264,z4,z5,z6]),(0,[z1,z2,z3,z4,z87,z5,z6])],[(1,[z1,z2,z3,z4,z5,z6]),(0,[z581,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z582,z5,z6]),(0,[z1,z2,z3,z4,z5,z129,z6]),(0,[z583,z1,z2,z3,z4,z5,z6])],[(0,[z139,z1,z49,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z584,z6]),(0,[z247,z1,z13,z2,z3,z4,z5]),(1,[z1,z398,z3,z4,z5,z6]),(0,[z585,z1,z2,z3,z4,z5,z6]),(0,[z70,z1,z2,z3,z4,z5,z134]),(0,[z1,z2,z3,z4,z5,z33,z440])]],
   [[(0,[z289,z1,z2,z3,z4,z5,z452]),(0,[z1,z2,z586,z3,z4,z5,z6]),(0,[z587,z1,z2,z3,z4,z5,z6]),(0,[z1,z13,z2,z3,z4,z118,z5])],[(0,[z1,z2,z3,z29,z4,z5,z33]),(0,[z289,z1,z13,z2,z3,z4,z5]),(1,[z1,z13,z2,z3,z4,z33]),(0,[z1,z2,z588,z3,z4,z5,z6])],[(0,[z289,z1,z2,z3,z476,z5,z6]),(0,[z1,z2,z589,z3,z4,z5,z6]),(0,[z152,z1,z2,z4,z122,z5,z6])],[(0,[z247,z2,z49,z3,z4,z5,z6]),(0,[z320,z1,z2,z29,z4,z5,z6]),(1,[z256,z2,z3,z21,z5,z6]),(0,[z1,z2,z3,z590,z4,z5,z6]),(0,[z1,z2,z3,z4,z591,z5,z6]),(0,[z1,z2,z3,z212,z5,z128,z6])],[(0,[z1,z592,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z593,z5,z6]),(0,[z1,z2,z3,z4,z5,z594,z6])],[(0,[z1,z2,z3,z595,z4,z5,z6]),(0,[z1,z2,z3,z596,z4,z5,z6]),(0,[z1,z2,z3,z4,z597,z5,z6])],[(0,[z284,z1,z13,z2,z3,z4,z5]),(1,[z389,z2,z3,z4,z5,z44]),(0,[z1,z13,z2,z15,z3,z4,z5]),(0,[z1,z2,z3,z4,z17,z5,z33])],[(0,[z1,z2,z3,z598,z4,z5,z6]),(0,[z1,z2,z29,z4,z5,z41,z6]),(0,[z1,z2,z3,z4,z5,z599,z6]),(0,[z1,z2,z3,z4,z5,z6,z106]),(0,[z1,z2,z3,z600,z4,z5,z6]),(0,[z601,z1,z2,z3,z4,z5,z6])]],
   [[(0,[z247,z1,z2,z29,z4,z5,z6]),(0,[z1,z2,z3,z602,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z603,z6]),(0,[z1,z2,z3,z4,z604,z5,z6])],[(0,[z109,z1,z3,z89,z4,z5,z6]),(0,[z605,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z606,z3,z4,z5,z6]),(0,[z152,z1,z2,z3,z4,z5,z6])],[(0,[z1,z607,z2,z3,z4,z5,z6]),(0,[z242,z1,z2,z3,z4,z25,z6]),(0,[z1,z3,z67,z4,z14,z5,z6])],[(0,[z1,z2,z3,z4,z5,z608,z6]),(0,[z609,z1,z2,z3,z4,z5,z6])],[(0,[z610,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z120,z4,z5,z6]),(0,[z1,z2,z15,z3,z4,z5,z6]),(1,[z131,z1,z2,z3,z81,z5])],[(0,[z1,z2,z49,z3,z4,z5,z33]),(0,[z28,z1,z2,z192,z4,z5,z6]),(0,[z611,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z612,z5,z6]),(0,[z1,z2,z3,z4,z5,z613,z6]),(0,[z7,z1,z2,z3,z4,z5,z33]),(0,[z1,z2,z4,z57,z5,z41,z6])],[(0,[z1,z2,z3,z4,z469,z5,z6])]],
   [[(0,[z1,z2,z3,z614,z4,z5,z6]),(0,[z1,z2,z3,z4,z615,z5,z6]),(0,[z1,z2,z3,z4,z616,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z617]),(0,[z229,z1,z13,z2,z3,z4,z5]),(0,[z1,z2,z3,z618,z4,z5,z6]),(0,[z1,z2,z3,z619,z4,z5,z6]),(0,[z1,z376,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z620,z6]),(1,[z1,z2,z3,z4,z5,z452])],[(0,[z621,z1,z2,z3,z4,z5,z6]),(0,[z256,z1,z2,z3,z4,z5,z6]),(0,[z622,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z67,z141,z5,z6]),(0,[z63,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z623,z3,z4,z5,z6]),(1,[z152,z1,z2,z4,z122,z5]),(0,[z1,z2,z3,z4,z624,z5,z6])],[(0,[z1,z2,z3,z4,z625,z5,z6]),(0,[z1,z2,z3,z120,z4,z5,z33])],[(0,[z626,z1,z2,z3,z4,z5,z6]),(0,[z1,z627,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z4,z5,z6]),(0,[z1,z2,z3,z89,z4,z5,z6]),(0,[z1,z540,z2,z3,z4,z5,z6]),(0,[z1,z2,z628,z3,z4,z5,z6]),(0,[z1,z2,z3,z629,z4,z5,z6])],[(0,[z109,z1,z414,z3,z4,z5,z6]),(1,[z1,z2,z3,z430,z4,z5]),(0,[z7,z1,z2,z3,z120,z5,z6]),(0,[z1,z2,z3,z630,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z631])],[(0,[z1,z49,z3,z4,z5,z22,z6]),(1,[z229,z2,z3,z127,z5,z6]),(0,[z632,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z41,z33])]],
   [[],[(0,[z1,z2,z3,z21,z5,z6,z104]),(0,[z1,z2,z3,z4,z5,z6,z135]),(0,[z1,z414,z199,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z633,z6]),(0,[z1,z2,z8,z3,z141,z5,z6]),(0,[z1,z2,z3,z4,z57,z5,z33]),(0,[z131,z1,z2,z3,z4,z5,z104])],[(0,[z289,z1,z2,z3,z31,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z181]),(0,[z1,z18,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z227,z5,z6]),(0,[z1,z13,z2,z3,z4,z141,z5])],[(0,[z256,z1,z2,z3,z4,z5,z33]),(0,[z1,z2,z3,z4,z360,z5,z6]),(0,[z634,z1,z2,z3,z4,z5,z6]),(0,[z320,z1,z2,z4,z57,z5,z6])],[(0,[z1,z2,z3,z3,z4,z5,z6]),(0,[z45,z1,z2,z3,z4,z5,z33]),(0,[z1,z2,z3,z4,z635,z5,z6]),(1,[z7,z1,z2,z141,z5,z6]),(0,[z636,z1,z2,z3,z4,z5,z6]),(0,[z637,z1,z2,z3,z4,z5,z6]),(0,[z117,z1,z13,z2,z3,z4,z6])],[(0,[z55,z1,z2,z3,z276,z5,z6]),(0,[z1,z126,z3,z4,z5,z22,z6]),(0,[z7,z1,z13,z2,z3,z4,z5]),(0,[z638,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z122,z5,z33]),(1,[z1,z2,z3,z483,z4,z5]),(0,[z1,z2,z3,z639,z4,z5,z6])],[(0,[z139,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z640,z3,z4,z5,z6]),(0,[z389,z1,z2,z3,z317,z4,z5]),(0,[z1,z2,z3,z4,z5,z6,z153]),(0,[z1,z2,z3,z4,z641,z5,z6])],[(0,[z1,z149,z2,z3,z4,z360,z6])]],
   [[(0,[z642,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z643,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z644,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z645]),(0,[z646,z1,z2,z3,z4,z5,z6]),(0,[z1,z13,z2,z3,z4,z227,z5]),(1,[z1,z2,z3,z4,z340,z6])],[(0,[z1,z2,z3,z4,z647,z5,z6]),(0,[z2,z3,z127,z4,z21,z5,z6]),(0,[z131,z55,z1,z2,z3,z4,z5]),(0,[z109,z1,z2,z3,z4,z5,z33]),(0,[z648,z1,z2,z3,z4,z5,z6]),(0,[z1,z13,z2,z3,z4,z122,z5])],[(1,[z289,z2,z3,z4,z54,z6]),(0,[z1,z2,z3,z4,z5,z6,z649]),(0,[z1,z2,z3,z4,z227,z5,z33])],[(0,[z1,z2,z650,z3,z4,z5,z6]),(0,[z242,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z651,z3,z4,z5,z6]),(0,[z289,z2,z3,z4,z5,z54,z6]),(0,[z1,z414,z2,z199,z4,z5,z6]),(0,[z652,z1,z2,z3,z4,z5,z6]),(0,[z653,z1,z2,z3,z4,z5,z6]),(0,[z1,z654,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z655,z6]),(0,[z1,z656,z2,z3,z4,z5,z6])],[(0,[z28,z1,z2,z3,z4,z5,z6]),(1,[z28,z2,z29,z4,z5,z6]),(0,[z1,z2,z3,z4,z657,z5,z6]),(0,[z1,z2,z3,z4,z5,z154,z33])],[(0,[z284,z1,z64,z3,z4,z5,z6]),(0,[z2,z49,z3,z29,z4,z5,z6]),(0,[z139,z1,z2,z3,z4,z5,z33]),(0,[z247,z2,z192,z3,z4,z5,z6]),(0,[z658,z1,z2,z3,z4,z5,z6]),(0,[z659,z1,z2,z3,z4,z5,z6]),(0,[z1,z13,z2,z3,z4,z5,z134])],[(0,[z660,z1,z2,z3,z4,z5,z6]),(0,[z661,z1,z2,z3,z4,z5,z6])]],
   [[(0,[z389,z131,z1,z2,z3,z4,z5]),(0,[z1,z13,z414,z2,z3,z4,z5]),(0,[z1,z2,z3,z662,z4,z5,z6]),(0,[z663,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z664,z5,z6]),(0,[z1,z2,z3,z4,z57,z6,z33]),(0,[z1,z2,z3,z665,z4,z5,z6]),(0,[z1,z2,z3,z4,z666,z5,z6])],[(0,[z242,z1,z2,z3,z53,z4,z6]),(0,[z1,z13,z2,z3,z4,z25,z5]),(0,[z1,z2,z3,z667,z4,z5,z6]),(0,[z1,z2,z3,z668,z4,z5,z6]),(0,[z1,z126,z2,z3,z4,z22,z6])],[(0,[z1,z2,z3,z4,z5,z6,z669]),(0,[z256,z1,z13,z2,z3,z4,z5]),(0,[z1,z13,z2,z3,z4,z21,z5]),(0,[z63,z1,z13,z2,z3,z4,z5]),(0,[z1,z2,z3,z670,z4,z5,z6])],[(0,[z242,z1,z2,z3,z4,z5,z33])],[(0,[z1,z2,z3,z4,z5,z671,z6]),(0,[z1,z2,z3,z4,z672,z5,z6]),(1,[z1,z2,z3,z31,z5,z6]),(1,[z289,z1,z2,z3,z4,z33]),(0,[z1,z2,z3,z4,z5,z54,z33]),(0,[z673,z1,z2,z3,z4,z5,z6]),(0,[z45,z1,z3,z4,z14,z5,z6]),(0,[z1,z18,z2,z8,z3,z5,z6]),(0,[z1,z2,z3,z4,z5,z674,z6]),(0,[z1,z2,z3,z4,z5,z33,z104])],[(0,[z1,z1,z2,z3,z4,z5,z6]),(0,[z139,z2,z3,z29,z4,z5,z6]),(0,[z63,z1,z2,z3,z4,z22,z6])],[(0,[z242,z1,z2,z3,z4,z54,z6])],[(0,[z1,z2,z675,z3,z4,z5,z6]),(0,[z1,z2,z334,z3,z4,z227,z5]),(0,[z1,z2,z3,z4,z676,z5,z6]),(0,[z1,z2,z3,z677,z4,z5,z6]),(1,[z320,z1,z2,z4,z57,z6]),(0,[z1,z13,z2,z274,z3,z4,z5])]],
   [[(0,[z1,z2,z192,z3,z4,z5,z33]),(0,[z678,z1,z2,z3,z4,z5,z6]),(1,[z418,z1,z2,z3,z5,z6]),(0,[z1,z2,z679,z3,z4,z5,z6]),(0,[z1,z2,z3,z53,z4,z5,z173])],[(0,[z1,z64,z2,z3,z4,z5,z33]),(0,[z1,z2,z3,z4,z227,z6,z33]),(0,[z1,z2,z3,z680,z4,z5,z6])],[(0,[z55,z1,z2,z3,z4,z5,z6]),(0,[z55,z1,z2,z3,z317,z4,z5]),(0,[z109,z1,z2,z3,z293,z5,z6]),(0,[z1,z2,z3,z4,z5,z108,z6]),(0,[z1,z2,z3,z4,z5,z6,z681]),(0,[z489,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z317,z4,z5,z104])],[(0,[z1,z13,z2,z49,z3,z4,z5]),(0,[z1,z2,z682,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z683,z6]),(0,[z1,z2,z3,z4,z75,z5,z6])],[(0,[z28,z2,z3,z29,z4,z5,z6]),(0,[z1,z2,z3,z4,z684,z5,z6]),(0,[z1,z2,z3,z476,z4,z5,z6]),(0,[z685,z1,z2,z3,z4,z5,z6])],[(0,[z139,z1,z13,z2,z3,z4,z5]),(0,[z109,z182,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z686,z5,z6]),(0,[z1,z149,z2,z3,z4,z5,z6]),(0,[z687,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z53,z4,z5,z6]),(0,[z1,z2,z3,z212,z53,z4,z6]),(0,[z131,z1,z2,z3,z81,z5,z6]),(0,[z688,z1,z2,z3,z4,z5,z6])],[(1,[z1,z2,z3,z4,z469,z5])],[(0,[z1,z2,z3,z4,z5,z689,z6]),(0,[z1,z2,z3,z212,z4,z5,z33])]],
   [[(0,[z2,z192,z3,z29,z4,z5,z6]),(0,[z389,z2,z3,z4,z5,z44,z6]),(0,[z1,z2,z3,z483,z4,z5,z6])],[(0,[z1,z2,z690,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z691,z6]),(0,[z1,z2,z3,z4,z5,z33,z572])],[(0,[z242,z1,z2,z3,z4,z6,z33]),(0,[z242,z1,z13,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z692,z6]),(0,[z693,z1,z2,z3,z4,z5,z6])],[(1,[z284,z49,z3,z4,z5,z6]),(0,[z229,z1,z2,z3,z127,z5,z6]),(0,[z1,z2,z694,z3,z4,z5,z6]),(0,[z1,z13,z2,z3,z4,z5,z44]),(0,[z695,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z495])],[(0,[z28,z1,z13,z2,z3,z4,z5]),(0,[z1,z2,z3,z29,z4,z5,z6]),(0,[z1,z2,z696,z3,z4,z5,z6]),(0,[z109,z1,z2,z3,z331,z5,z6]),(0,[z1,z2,z3,z697,z4,z5,z6]),(0,[z1,z2,z3,z212,z4,z5,z233])],[(0,[z1,z2,z3,z4,z14,z5,z6]),(0,[z1,z149,z2,z3,z4,z5,z33]),(0,[z1,z2,z3,z4,z698,z5,z6]),(0,[z699,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z53,z4,z5,z33]),(0,[z1,z2,z700,z3,z4,z5,z6]),(0,[z688,z1,z2,z3,z4,z5,z33])],[(1,[z247,z2,z192,z4,z5,z6]),(0,[z109,z1,z2,z3,z4,z5,z74]),(0,[z701,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z702,z4,z5,z6])],[(0,[z703,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z704,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z705,z6]),(0,[z706,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z494])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z1,z2,z192,z4,z41,z33]),(0,[z1,z2,z3,z4,z227,z495]),(0,[z1,z2,z3,z707,z4,z33])],[(0,[z1,z2,z3,z4,z107,z33]),(0,[z1,z2,z4,z708,z41,z6]),(0,[z1,z709,z2,z3,z4,z6])],[(0,[z247,z2,z710,z4,z5,z6]),(0,[z1,z2,z3,z4,z711,z5]),(0,[z1,z2,z3,z712,z5,z6])],[(0,[z7,z1,z2,z141,z5,z6])],[(0,[z1,z2,z3,z4,z5,z713]),(0,[z1,z2,z714,z4,z5,z6]),(0,[z1,z2,z3,z483,z4,z5])],[(0,[z1,z3,z4,z715,z5,z6])],[(0,[z1,z2,z3,z4,z716,z6]),(0,[z1,z717,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z129,z33]),(0,[z1,z2,z3,z718,z4,z5]),(0,[z1,z2,z3,z390,z5,z572])],[(0,[z1,z2,z96,z31,z5,z6]),(0,[z1,z2,z3,z4,z719,z6]),(0,[z1,z18,z3,z715,z5,z6]),(0,[z1,z2,z3,z4,z340,z6]),(0,[z266,z1,z3,z4,z246,z5])]],
   [[(0,[z1,z2,z3,z4,z584,z33])],[(0,[z289,z2,z3,z4,z54,z6]),(0,[z1,z149,z3,z4,z5,z134])],[(0,[z1,z2,z3,z4,z720,z6]),(0,[z1,z2,z3,z4,z5,z721]),(0,[z82,z13,z2,z3,z4,z5]),(0,[z489,z1,z2,z3,z235,z5]),(0,[z136,z1,z13,z2,z3,z212]),(0,[z722,z13,z2,z3,z4,z5])],[(0,[z50,z1,z2,z3,z4,z6]),(0,[z723,z1,z2,z3,z4,z5]),(0,[z117,z1,z2,z334,z3,z4]),(0,[z1,z2,z3,z4,z724,z6])],[(0,[z28,z2,z29,z4,z5,z6]),(0,[z725,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z726,z4,z6]),(0,[z289,z398,z3,z4,z54,z6]),(0,[z182,z2,z3,z293,z5,z6]),(0,[z1,z2,z3,z4,z516,z33])],[(0,[z1,z3,z4,z727,z5,z6])],[(0,[z1,z2,z3,z728,z4,z5]),(0,[z687,z1,z2,z3,z4,z33])],[(0,[z1,z2,z3,z4,z729,z6]),(0,[z1,z2,z3,z4,z5,z730]),(0,[z1,z2,z3,z4,z5,z731])]],
   [[(0,[z1,z732,z2,z3,z4,z5]),(0,[z131,z1,z2,z3,z73,z5]),(0,[z1,z2,z3,z4,z5,z733]),(1,[z1,z734,z2,z3,z4])],[(0,[z1,z2,z3,z422,z128,z6]),(0,[z1,z2,z3,z476,z5,z452]),(0,[z2,z3,z4,z5,z735,z6]),(0,[z1,z13,z2,z3,z53,z128])],[(0,[z1,z2,z3,z68,z5,z104]),(0,[z55,z2,z3,z4,z5,z736]),(0,[z1,z2,z3,z737,z5,z6]),(0,[z1,z2,z738,z4,z5,z6]),(0,[z1,z194,z3,z4,z5,z134])],[(0,[z1,z2,z3,z4,z739,z6]),(0,[z50,z1,z2,z3,z4,z33]),(0,[z109,z1,z738,z4,z5,z6]),(0,[z1,z2,z3,z4,z66,z33]),(0,[z1,z2,z3,z740,z4,z5])],[(0,[z1,z2,z3,z741,z5,z6]),(0,[z1,z80,z13,z2,z3,z4])],[(0,[z1,z2,z3,z293,z5,z74]),(0,[z1,z2,z742,z3,z4,z5]),(0,[z1,z2,z3,z4,z353,z33])],[(0,[z1,z2,z743,z4,z5,z6]),(0,[z1,z2,z744,z3,z4,z5]),(0,[z1,z2,z3,z745,z4,z5]),(0,[z1,z746,z2,z3,z4,z5]),(0,[z182,z2,z3,z331,z5,z6])],[(0,[z1,z2,z3,z4,z5,z747]),(0,[z418,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z4,z613,z33]),(0,[z1,z2,z3,z748,z4,z5])]],
   [[(0,[z1,z2,z3,z749,z5,z6]),(0,[z1,z2,z3,z4,z750,z6]),(0,[z1,z2,z3,z4,z419,z33])],[(0,[z256,z13,z2,z3,z21,z5]),(0,[z1,z751,z2,z3,z4,z5]),(1,[z1,z2,z3,z4,z752]),(0,[z1,z2,z3,z753,z4,z5]),(0,[z754,z1,z2,z3,z4,z6])],[(0,[z1,z755,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z756]),(0,[z1,z2,z3,z757,z5,z104])],[(0,[z1,z2,z3,z4,z758,z5]),(0,[z1,z759,z3,z4,z5,z6]),(0,[z55,z2,z3,z306,z5,z190]),(0,[z1,z13,z2,z3,z4,z533])],[(0,[z1,z2,z40,z4,z708,z6])],[(0,[z1,z2,z3,z4,z5,z760]),(0,[z1,z2,z40,z4,z41,z33])],[(0,[z242,z1,z2,z3,z4,z181]),(0,[z1,z149,z2,z3,z4,z172]),(0,[z1,z2,z761,z3,z4,z5]),(0,[z2,z3,z4,z5,z762,z33])],[(0,[z1,z2,z3,z4,z763,z6]),(0,[z1,z2,z3,z331,z5,z74]),(0,[z1,z2,z764,z4,z5,z6]),(0,[z1,z2,z765,z3,z4,z5])]],
   [[(0,[z1,z2,z766,z3,z4,z5]),(0,[z1,z479,z2,z3,z4,z33])],[(0,[z289,z2,z3,z476,z54,z6]),(0,[z1,z2,z3,z767,z4,z5]),(0,[z768,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z769,z5])],[(0,[z284,z49,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z770,z6]),(0,[z1,z2,z3,z4,z771,z5]),(0,[z772,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z633,z33]),(0,[z1,z2,z3,z4,z5,z495])],[(0,[z1,z2,z773,z4,z5,z6]),(0,[z1,z774,z2,z3,z4,z129]),(0,[z1,z2,z3,z4,z5,z775]),(0,[z1,z2,z3,z4,z118,z33])],[(0,[z1,z776,z3,z4,z5,z6]),(0,[z777,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z778])],[(0,[z1,z779,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z5,z780]),(0,[z1,z2,z3,z4,z5,z781]),(0,[z1,z2,z3,z782,z5,z6]),(0,[z1,z2,z3,z235,z5,z33]),(0,[z1,z2,z3,z4,z5,z783])],[(0,[z1,z2,z3,z217,z5,z104]),(0,[z1,z2,z3,z4,z784,z6]),(0,[z1,z2,z3,z430,z785,z4]),(0,[z1,z2,z3,z4,z5,z494]),(0,[z320,z1,z13,z2,z4,z57])],[(0,[z1,z2,z786,z4,z5,z6]),(0,[z1,z2,z3,z595,z4,z33])]],
   [[(0,[z1,z2,z3,z4,z5,z787]),(0,[z1,z2,z3,z4,z788,z6]),(0,[z1,z789,z3,z4,z5,z6]),(0,[z109,z1,z13,z89,z4,z5]),(0,[z1,z2,z3,z4,z387,z33]),(0,[z1,z2,z3,z264,z4,z5]),(0,[z1,z2,z15,z4,z5,z16]),(0,[z1,z2,z15,z158,z4,z5]),(0,[z1,z169,z3,z4,z5,z440])],[(0,[z1,z790,z80,z2,z3,z4]),(0,[z1,z2,z3,z31,z5,z452])],[(0,[z1,z2,z3,z4,z5,z791]),(0,[z109,z82,z89,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z792])],[(0,[z256,z2,z3,z793,z5,z6]),(0,[z1,z2,z3,z4,z794,z5]),(0,[z1,z13,z2,z3,z4,z340])],[(0,[z2,z3,z793,z21,z5,z6]),(0,[z1,z795,z2,z3,z4,z5]),(0,[z1,z13,z2,z76,z4,z5]),(0,[z1,z2,z3,z4,z5,z736]),(0,[z1,z2,z3,z707,z4,z57])],[(0,[z1,z2,z3,z796,z5,z6]),(0,[z638,z2,z29,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z36]),(0,[z55,z2,z3,z276,z5,z190]),(0,[z1,z797,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z39,z5]),(0,[z1,z540,z2,z3,z4,z33]),(0,[z1,z2,z3,z4,z41,z34]),(0,[z1,z2,z3,z4,z655,z33]),(0,[z798,z1,z2,z3,z4,z5])],[(0,[z1,z2,z3,z4,z5,z799]),(0,[z138,z1,z2,z4,z17,z5])],[(0,[z1,z2,z3,z4,z5,z800]),(0,[z1,z2,z3,z4,z278,z33])]],
   [[(0,[z1,z2,z3,z801,z4,z5]),(0,[z1,z2,z96,z4,z5,z452]),(0,[z1,z2,z4,z802,z5,z16])],[(0,[z1,z2,z3,z4,z803,z6]),(0,[z1,z13,z2,z3,z4,z273])],[(0,[z1,z2,z3,z4,z5,z804]),(1,[z1,z398,z3,z4,z33]),(0,[z1,z180,z3,z4,z5,z315])],[(0,[z1,z169,z3,z4,z22,z6]),(0,[z1,z168,z2,z3,z4,z172])],[(0,[z256,z2,z3,z21,z5,z36]),(0,[z1,z2,z3,z4,z75,z5])],[(0,[z1,z2,z3,z4,z805,z6]),(0,[z1,z2,z3,z306,z5,z190]),(0,[z50,z389,z2,z3,z4,z44]),(0,[z1,z13,z2,z3,z331,z5]),(0,[z1,z2,z3,z4,z5,z806])],[(0,[z1,z80,z2,z3,z4,z6]),(0,[z1,z2,z3,z306,z5,z6]),(0,[z1,z2,z3,z807,z4,z5]),(0,[z351,z2,z3,z4,z5,z44]),(0,[z109,z1,z89,z4,z107,z6]),(0,[z808,z2,z3,z4,z5,z6]),(0,[z198,z376,z2,z3,z4,z5])],[(0,[z1,z2,z3,z4,z5,z809]),(0,[z418,z489,z1,z2,z3,z5]),(0,[z1,z2,z4,z810,z5,z6]),(0,[z1,z2,z3,z4,z87,z6])]],
   [[(0,[z256,z2,z3,z422,z21,z6])],[(0,[z498,z1,z2,z3,z4,z33]),(0,[z1,z2,z3,z4,z5,z811]),(0,[z289,z2,z3,z31,z54,z6])],[(0,[z1,z2,z3,z812,z4,z5]),(0,[z1,z2,z3,z4,z813,z5])],[(0,[z814,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z815,z5,z6]),(0,[z1,z2,z3,z293,z5,z33]),(0,[z109,z1,z89,z4,z129,z6]),(0,[z1,z169,z3,z4,z22,z33]),(0,[z7,z1,z13,z2,z141,z5]),(0,[z136,z1,z2,z3,z212,z6])],[(0,[z1,z2,z3,z4,z5,z816]),(0,[z1,z817,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z683,z33]),(0,[z1,z2,z3,z4,z5,z818]),(0,[z1,z13,z2,z3,z235,z5]),(0,[z1,z18,z3,z99,z5,z6]),(0,[z1,z2,z3,z4,z22,z495])],[(0,[z1,z819,z2,z3,z4,z5]),(0,[z131,z1,z2,z3,z68,z5]),(0,[z1,z13,z2,z3,z4,z129]),(0,[z1,z2,z3,z4,z5,z820])],[(0,[z1,z2,z3,z4,z449,z33]),(0,[z247,z2,z163,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z821]),(0,[z2,z3,z127,z793,z5,z6]),(0,[z1,z2,z3,z306,z5,z33]),(0,[z182,z2,z3,z4,z5,z33]),(0,[z1,z2,z3,z822,z5,z6]),(0,[z1,z2,z3,z4,z57,z34]),(0,[z1,z2,z3,z810,z5,z6])],[(0,[z1,z823,z2,z3,z4,z5]),(0,[z109,z1,z430,z89,z4,z5]),(0,[z1,z2,z3,z430,z235,z5])]],
   [[(0,[z289,z2,z96,z4,z54,z6]),(0,[z1,z2,z3,z4,z689,z33]),(0,[z1,z824,z3,z4,z5,z6])],[(0,[z20,z1,z2,z3,z422,z4]),(0,[z1,z825,z3,z4,z5,z6]),(0,[z826,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z827,z6]),(0,[z48,z1,z274,z3,z4,z5])],[(0,[z1,z2,z3,z828,z5,z6]),(0,[z55,z2,z3,z4,z5,z190]),(0,[z1,z2,z4,z802,z5,z6])],[(0,[z256,z2,z3,z21,z5,z106]),(0,[z1,z2,z3,z4,z227,z33]),(0,[z1,z2,z3,z4,z692,z33]),(0,[z829,z2,z3,z4,z5,z6]),(0,[z136,z1,z2,z3,z212,z33])],[(0,[z1,z180,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z830]),(0,[z1,z180,z76,z4,z5,z6]),(0,[z1,z13,z2,z96,z4,z5]),(0,[z1,z2,z589,z3,z4,z33]),(0,[z1,z2,z3,z4,z5,z831]),(0,[z1,z2,z832,z3,z4,z227])],[(0,[z289,z1,z2,z76,z4,z33]),(0,[z1,z2,z3,z331,z5,z33])],[(0,[z1,z2,z3,z4,z5,z833]),(0,[z229,z13,z2,z3,z127,z5]),(0,[z1,z2,z834,z4,z5,z6]),(0,[z2,z3,z4,z5,z44,z736]),(0,[z1,z738,z89,z4,z5,z6])],[(0,[z1,z2,z3,z4,z360,z6])]],
   [[(0,[z139,z13,z64,z3,z4,z5]),(0,[z835,z2,z3,z4,z5,z6]),(0,[z109,z1,z235,z89,z5,z6]),(0,[z1,z2,z3,z4,z705,z33]),(0,[z1,z2,z3,z836,z4,z5]),(0,[z136,z1,z2,z3,z212,z233]),(0,[z1,z2,z3,z317,z423,z5])],[(0,[z1,z2,z3,z4,z5,z837]),(0,[z242,z2,z3,z4,z25,z6]),(0,[z1,z3,z4,z838,z5,z134]),(0,[z839,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z10,z33])],[(0,[z1,z2,z3,z4,z840,z6]),(0,[z1,z2,z3,z4,z841,z5]),(0,[z45,z1,z13,z3,z14,z5])],[(0,[z1,z2,z3,z842,z5,z6]),(0,[z1,z2,z3,z4,z5,z315]),(0,[z1,z2,z76,z4,z5,z315]),(0,[z1,z2,z3,z4,z5,z843])],[(0,[z1,z2,z651,z4,z41,z6]),(0,[z1,z180,z3,z4,z5,z33]),(0,[z82,z2,z3,z4,z5,z108]),(0,[z1,z2,z3,z844,z5,z6]),(0,[z1,z845,z3,z4,z5,z6])],[],[(0,[z1,z2,z3,z4,z5,z846]),(0,[z1,z2,z4,z708,z5,z6])],[(0,[z117,z1,z2,z96,z4,z6]),(0,[z1,z2,z3,z4,z5,z181]),(0,[z1,z2,z3,z4,z847,z6]),(0,[z1,z2,z848,z4,z5,z6]),(0,[z1,z2,z4,z849,z5,z6]),(0,[z1,z2,z3,z4,z360,z33])]],
   [[(0,[z1,z2,z3,z850,z5,z6]),(0,[z1,z2,z3,z4,z625,z33]),(0,[z1,z2,z3,z4,z5,z851]),(1,[z2,z3,z793,z5,z6]),(0,[z20,z256,z2,z3,z21,z5]),(0,[z1,z2,z3,z276,z5,z33]),(0,[z1,z2,z3,z852,z5,z6]),(0,[z609,z1,z3,z14,z5,z6]),(0,[z1,z2,z3,z4,z5,z853]),(0,[z1,z2,z4,z57,z41,z33])],[(0,[z1,z854,z2,z3,z4,z5]),(0,[z1,z790,z2,z3,z4,z5]),(0,[z242,z2,z3,z4,z25,z33]),(0,[z242,z13,z2,z3,z4,z25]),(0,[z1,z2,z3,z4,z855,z5]),(0,[z1,z2,z3,z4,z52,z33])],[(0,[z1,z259,z2,z3,z4,z33]),(0,[z1,z2,z3,z4,z107,z108]),(0,[z1,z2,z3,z4,z5,z856]),(0,[z1,z734,z2,z3,z4,z5]),(0,[z1,z2,z274,z3,z4,z33])],[(0,[z857,z2,z3,z4,z5,z6]),(0,[z858,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z859,z5,z6])],[(0,[z1,z2,z860,z4,z5,z6]),(0,[z242,z2,z3,z4,z847,z6]),(0,[z45,z1,z532,z3,z5,z6])],[(0,[z1,z2,z3,z4,z5,z861]),(0,[z1,z2,z3,z4,z862,z6]),(0,[z1,z149,z274,z3,z4,z5]),(0,[z320,z1,z2,z4,z57,z495])],[(1,[z2,z710,z4,z5,z6]),(0,[z20,z1,z80,z2,z3,z4]),(0,[z1,z2,z3,z863,z5,z6]),(0,[z1,z126,z3,z4,z864,z6])],[(0,[z1,z2,z865,z4,z5,z6]),(0,[z1,z2,z3,z4,z129,z108]),(0,[z1,z2,z40,z4,z469,z41]),(0,[z1,z13,z2,z3,z4,z87])]],
   [[(0,[z1,z2,z3,z4,z5,z866]),(0,[z637,z2,z3,z127,z5,z6]),(0,[z1,z13,z2,z3,z476,z5]),(0,[z1,z2,z3,z4,z867,z6]),(0,[z868,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z715,z5,z6]),(0,[z1,z2,z3,z4,z5,z869]),(0,[z1,z2,z832,z3,z4,z5]),(0,[z1,z2,z334,z3,z4,z360]),(0,[z1,z2,z40,z4,z41,z6])],[(0,[z284,z870,z3,z4,z5,z6]),(0,[z871,z1,z2,z3,z4,z5]),(0,[z1,z872,z3,z4,z5,z6]),(0,[z1,z2,z3,z264,z4,z33]),(0,[z1,z2,z3,z4,z873,z6]),(0,[z2,z3,z4,z5,z762,z6])],[(0,[z1,z2,z3,z4,z874,z6]),(0,[z1,z774,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z875,z5]),(0,[z1,z2,z3,z4,z708,z6]),(0,[z829,z13,z2,z3,z4,z5])],[(0,[z1,z2,z3,z4,z5,z876]),(0,[z1,z80,z2,z3,z4,z68]),(0,[z182,z2,z3,z4,z5,z74]),(0,[z1,z2,z3,z4,z877,z6]),(0,[z1,z2,z3,z4,z92,z33]),(0,[z1,z2,z3,z4,z41,z33]),(0,[z1,z2,z3,z859,z5,z33])],[(0,[z1,z2,z3,z878,z5,z6]),(0,[z1,z180,z3,z476,z5,z6]),(0,[z1,z2,z810,z141,z5,z6])],[(0,[z1,z2,z3,z4,z879,z6]),(0,[z1,z2,z3,z4,z880,z6]),(0,[z1,z2,z76,z4,z5,z6]),(0,[z289,z1,z2,z96,z4,z33])],[(0,[z1,z2,z3,z4,z881,z5]),(0,[z1,z2,z3,z483,z53,z128])],[(0,[z329,z2,z29,z4,z5,z6]),(0,[z1,z49,z3,z4,z22,z33]),(0,[z1,z2,z3,z96,z4,z33])]],
   [[(0,[z1,z2,z3,z4,z5,z882]),(0,[z1,z2,z3,z53,z31,z6]),(0,[z1,z2,z3,z235,z5,z6]),(0,[z688,z2,z3,z4,z5,z135]),(0,[z1,z13,z2,z3,z815,z5])],[(0,[z284,z13,z49,z3,z4,z5]),(0,[z361,z1,z2,z3,z4,z33])],[(0,[z289,z2,z3,z4,z54,z452]),(0,[z1,z13,z2,z3,z4,z513])],[(0,[z1,z2,z3,z4,z883,z6]),(0,[z1,z2,z3,z476,z5,z315]),(0,[z1,z2,z884,z4,z5,z6]),(0,[z1,z349,z2,z3,z4,z33])],[(0,[z136,z1,z2,z3,z422,z6]),(0,[z1,z2,z3,z4,z132,z33]),(0,[z1,z2,z3,z4,z885,z6]),(0,[z1,z2,z3,z4,z886,z6]),(0,[z1,z2,z3,z4,z5,z887])],[(0,[z1,z2,z3,z4,z5,z33]),(1,[z870,z3,z4,z5,z6]),(0,[z1,z2,z76,z4,z5,z33]),(0,[z289,z1,z2,z3,z4,z888])],[(0,[z2,z3,z4,z25,z847,z6]),(0,[z242,z2,z3,z4,z154,z6]),(0,[z63,z1,z3,z4,z227,z33]),(0,[z1,z13,z2,z3,z116,z4]),(0,[z1,z2,z3,z4,z142,z33])],[(0,[z1,z2,z3,z193,z5,z104]),(0,[z1,z2,z3,z590,z4,z33]),(0,[z1,z2,z3,z4,z172,z6])]],
   [[(0,[z557,z1,z2,z3,z4,z33]),(0,[z1,z2,z3,z889,z5,z6]),(0,[z1,z2,z3,z890,z5,z6]),(0,[z688,z242,z2,z3,z4,z33])],[(0,[z289,z207,z2,z3,z4,z6]),(0,[z891,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z4,z892,z5])],[(0,[z1,z2,z3,z4,z571,z33]),(0,[z893,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z894]),(0,[z1,z895,z3,z4,z5,z6]),(0,[z1,z896,z3,z4,z5,z6]),(0,[z2,z3,z793,z4,z5,z6]),(0,[z1,z125,z2,z3,z4,z33]),(0,[z109,z489,z1,z89,z4,z5])],[(0,[z1,z2,z3,z4,z57,z33])],[(0,[z1,z2,z3,z4,z164,z33]),(0,[z1,z2,z3,z4,z5,z897]),(0,[z1,z2,z3,z4,z5,z898]),(0,[z1,z2,z3,z4,z5,z899]),(0,[z117,z1,z2,z3,z4,z315])],[(0,[z1,z2,z3,z4,z900,z6]),(0,[z1,z2,z3,z901,z5,z6]),(0,[z242,z2,z3,z4,z154,z33])],[(0,[z1,z2,z3,z422,z4,z811]),(0,[z1,z2,z334,z3,z4,z33]),(0,[z1,z405,z2,z3,z4,z33]),(0,[z1,z2,z3,z4,z172,z33])]],
   [[(0,[z1,z2,z902,z3,z4,z5]),(0,[z903,z1,z2,z3,z4,z5]),(0,[z109,z1,z89,z293,z5,z6]),(0,[z45,z1,z3,z715,z5,z6]),(0,[z1,z540,z2,z3,z4,z340]),(0,[z1,z149,z3,z4,z340,z134]),(0,[z1,z2,z3,z4,z355,z33]),(0,[z1,z2,z3,z212,z904,z6])],[(0,[z1,z2,z3,z4,z5,z905]),(0,[z289,z242,z2,z3,z4,z33]),(0,[z1,z13,z2,z3,z31,z5]),(0,[z289,z1,z2,z3,z476,z33]),(0,[z1,z2,z3,z4,z5,z906])],[(0,[z1,z2,z3,z4,z5,z907]),(0,[z908,z2,z3,z4,z5,z6])],[(0,[z1,z2,z4,z909,z5,z6]),(0,[z242,z211,z2,z3,z4,z25]),(0,[z1,z2,z3,z4,z910,z6]),(0,[z1,z2,z911,z4,z5,z6]),(0,[z432,z1,z2,z141,z5,z6]),(0,[z1,z2,z628,z4,z5,z16]),(0,[z1,z912,z2,z3,z4,z5])],[(0,[z913,z1,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z914,z6]),(0,[z1,z3,z4,z227,z22,z33])],[(0,[z162,z49,z3,z4,z5,z6]),(0,[z1,z2,z76,z476,z5,z6]),(0,[z1,z2,z3,z915,z4,z5]),(0,[z1,z2,z3,z4,z129,z747]),(0,[z1,z3,z67,z715,z5,z6]),(0,[z1,z2,z382,z4,z5,z153])],[(0,[z1,z916,z2,z3,z4,z6]),(0,[z1,z2,z3,z293,z5,z6]),(0,[z1,z2,z3,z4,z917,z6]),(0,[z1,z2,z3,z4,z5,z918]),(0,[z152,z1,z2,z4,z802,z5])],[(0,[z1,z2,z3,z4,z919,z6]),(0,[z1,z920,z2,z3,z4,z5]),(0,[z242,z1,z2,z3,z4,z33]),(0,[z289,z1,z2,z3,z4,z181]),(0,[z117,z1,z734,z2,z3,z4])]],
   [[(0,[z139,z870,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z921,z6]),(0,[z1,z126,z3,z4,z22,z6]),(0,[z1,z2,z922,z3,z4,z5]),(0,[z1,z13,z2,z333,z3,z4])],[(0,[z182,z2,z3,z4,z5,z6]),(0,[z578,z2,z192,z4,z5,z6])],[(0,[z1,z2,z3,z923,z4,z6]),(0,[z1,z2,z3,z4,z924,z6]),(0,[z1,z2,z3,z925,z5,z6]),(0,[z1,z13,z2,z3,z422,z4]),(0,[z109,z1,z89,z331,z5,z6]),(0,[z1,z2,z3,z4,z5,z34]),(0,[z447,z1,z2,z4,z57,z6]),(0,[z1,z2,z3,z4,z698,z33])],[(0,[z85,z1,z2,z3,z4,z33]),(0,[z1,z2,z29,z4,z41,z33]),(0,[z1,z180,z96,z4,z5,z6]),(0,[z1,z2,z3,z31,z5,z315]),(0,[z351,z1,z2,z3,z4,z33])],[(0,[z229,z2,z3,z793,z5,z6]),(0,[z1,z2,z3,z4,z5,z926]),(0,[z109,z1,z89,z4,z5,z74]),(0,[z1,z2,z15,z4,z87,z16]),(0,[z1,z2,z3,z317,z5,z104])],[(0,[z1,z2,z3,z4,z927,z5]),(0,[z1,z2,z3,z4,z5,z928]),(0,[z1,z2,z3,z127,z5,z106]),(0,[z1,z2,z3,z476,z5,z33]),(0,[z1,z13,z2,z3,z293,z5]),(0,[z1,z2,z3,z4,z246,z340]),(0,[z1,z2,z3,z4,z218,z33]),(0,[z1,z2,z382,z4,z41,z33])],[(0,[z20,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z929]),(0,[z2,z3,z4,z5,z847,z6]),(0,[z1,z2,z3,z930,z5,z6])],[(0,[z1,z2,z3,z931,z5,z6]),(0,[z55,z376,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z340,z134]),(0,[z932,z2,z3,z4,z5,z33]),(0,[z351,z525,z2,z3,z4,z5])]],
   [[(0,[z1,z2,z3,z68,z306,z5]),(0,[z1,z2,z3,z331,z5,z6]),(0,[z1,z126,z3,z4,z22,z33]),(0,[z1,z2,z4,z17,z41,z33])],[(0,[z1,z2,z3,z4,z336,z33]),(0,[z1,z2,z3,z4,z5,z933]),(0,[z109,z418,z1,z89,z5,z6]),(0,[z1,z2,z334,z3,z4,z5]),(0,[z601,z1,z2,z4,z122,z5]),(0,[z1,z2,z3,z757,z4,z5])],[(0,[z1,z2,z96,z4,z5,z315]),(0,[z1,z2,z3,z4,z234,z33]),(0,[z1,z2,z3,z4,z5,z74])],[(0,[z1,z2,z3,z934,z5,z6]),(0,[z1,z2,z3,z4,z5,z935]),(0,[z1,z3,z738,z4,z5,z6]),(0,[z1,z2,z3,z4,z936,z6]),(0,[z1,z734,z2,z3,z4,z33])],[(0,[z1,z2,z3,z4,z937,z6]),(0,[z1,z2,z3,z4,z938,z5]),(0,[z1,z13,z2,z3,z4,z172])],[(0,[z1,z2,z3,z4,z939,z6]),(0,[z489,z1,z2,z3,z4,z5]),(0,[z1,z2,z940,z3,z5,z6]),(0,[z136,z1,z2,z3,z904,z6])],[(0,[z320,z1,z2,z4,z708,z6])],[(0,[z1,z2,z3,z941,z4,z6]),(0,[z1,z13,z2,z3,z4,z234])]],
   [[(0,[z1,z2,z942,z4,z5,z6]),(0,[z943,z1,z2,z3,z5,z6]),(0,[z289,z2,z3,z4,z157,z6])],[(0,[z1,z2,z3,z4,z5,z944]),(0,[z1,z2,z3,z4,z5,z945]),(0,[z1,z2,z832,z3,z4,z33]),(0,[z946,z1,z2,z3,z4,z5])],[(0,[z289,z1,z2,z3,z31,z33]),(0,[z9,z2,z3,z4,z5,z44]),(0,[z1,z2,z8,z466,z5,z6]),(0,[z1,z2,z3,z4,z251,z33])],[(0,[z1,z2,z947,z4,z5,z6]),(0,[z1,z2,z3,z276,z5,z6])],[(0,[z1,z2,z3,z4,z5,z948]),(0,[z1,z2,z3,z95,z4,z33])],[(0,[z397,z1,z2,z3,z4,z33]),(0,[z587,z2,z3,z21,z5,z6]),(0,[z1,z2,z76,z31,z5,z6]),(0,[z1,z2,z3,z4,z949,z5]),(0,[z1,z734,z2,z3,z4,z118])],[(0,[z1,z2,z3,z4,z107,z806]),(0,[z1,z2,z3,z4,z5,z950]),(0,[z1,z13,z2,z3,z4,z360])],[(0,[z1,z2,z951,z3,z4,z6]),(0,[z1,z2,z3,z4,z171,z33]),(0,[z82,z2,z3,z4,z107,z6]),(0,[z1,z2,z3,z4,z802,z5])]],
   [[(0,[z952,z1,z2,z4,z5,z6]),(0,[z1,z2,z3,z422,z31,z6]),(0,[z585,z1,z2,z3,z81,z5]),(0,[z182,z13,z2,z3,z4,z5])],[(0,[z1,z398,z3,z4,z5,z315]),(0,[z1,z169,z3,z4,z5,z134])],[(0,[z1,z13,z180,z3,z4,z5]),(0,[z1,z2,z4,z57,z708,z6])],[(0,[z1,z2,z3,z4,z5,z953]),(0,[z1,z954,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z493,z33])],[(0,[z1,z2,z3,z4,z955,z5]),(0,[z82,z2,z3,z4,z129,z6])],[(0,[z956,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z957])],[(0,[z1,z2,z3,z4,z5,z958]),(0,[z959,z1,z80,z2,z3,z4])],[(0,[z2,z3,z710,z4,z5,z6]),(0,[z1,z168,z2,z3,z4,z33]),(0,[z1,z2,z3,z4,z5,z960])]],
   [[(0,[z256,z80,z2,z3,z21,z6]),(0,[z1,z13,z18,z3,z67,z5]),(0,[z1,z2,z3,z4,z864,z6]),(0,[z1,z2,z3,z4,z299,z33]),(0,[z1,z2,z3,z4,z172,z16]),(0,[z1,z2,z3,z961,z5,z6])],[(0,[z962,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z963]),(0,[z1,z2,z3,z53,z128,z173])],[(0,[z242,z392,z2,z3,z4,z6]),(0,[z1,z13,z2,z3,z276,z5]),(0,[z1,z964,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z213,z33]),(1,[z1,z2,z4,z802,z5])],[(0,[z1,z2,z3,z422,z4,z33]),(0,[z965,z2,z3,z4,z5,z6]),(0,[z1,z2,z40,z4,z41,z494]),(0,[z1,z2,z3,z4,z5,z173]),(0,[z1,z2,z3,z757,z5,z6])],[(0,[z1,z2,z3,z4,z966,z5]),(0,[z1,z967,z2,z3,z4,z6]),(0,[z1,z2,z96,z4,z5,z33]),(0,[z389,z2,z3,z4,z5,z154]),(0,[z1,z2,z3,z785,z4,z6]),(0,[z1,z18,z3,z67,z5,z6]),(0,[z1,z2,z3,z4,z347,z33])],[(0,[z1,z2,z3,z968,z5,z6]),(0,[z1,z180,z3,z4,z5,z452]),(0,[z1,z2,z3,z4,z888,z33]),(0,[z1,z2,z3,z969,z4,z5]),(0,[z1,z2,z3,z4,z267,z33])],[(0,[z1,z970,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z971,z6]),(0,[z1,z2,z3,z4,z5,z972]),(0,[z1,z2,z3,z53,z128,z6]),(0,[z1,z2,z3,z904,z53,z6])],[(0,[z1,z2,z3,z4,z973,z6]),(0,[z1,z2,z3,z974,z4,z5])]],
   [[(0,[z1,z2,z3,z4,z5,z6]),(0,[z139,z64,z3,z4,z5,z33]),(0,[z975,z2,z3,z4,z5,z6]),(0,[z1,z976,z2,z3,z4,z5]),(0,[z1,z977,z3,z4,z5,z6]),(0,[z117,z1,z13,z2,z3,z4]),(0,[z1,z2,z3,z961,z5,z33])],[(0,[z1,z2,z3,z4,z5,z752]),(0,[z1,z978,z3,z4,z5,z6])],[(0,[z1,z2,z3,z793,z5,z6]),(0,[z109,z1,z89,z4,z5,z33])],[(0,[z1,z398,z3,z4,z5,z6]),(0,[z1,z979,z3,z4,z5,z6]),(0,[z1,z398,z76,z4,z5,z6]),(0,[z1,z2,z398,z3,z4,z33])],[(0,[z1,z18,z3,z67,z5,z33]),(0,[z70,z1,z2,z3,z4,z172]),(0,[z1,z2,z3,z512,z5,z104])],[(0,[z1,z2,z3,z4,z5,z980]),(0,[z45,z1,z3,z14,z5,z33]),(0,[z1,z2,z3,z904,z4,z6])],[(0,[z1,z126,z3,z4,z22,z332]),(0,[z1,z2,z3,z4,z981,z5]),(0,[z1,z2,z3,z53,z128,z33])],[(0,[z982,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z983]),(0,[z1,z2,z710,z4,z5,z6]),(0,[z1,z3,z4,z864,z5,z6]),(1,[z1,z2,z4,z708,z6])],[(0,[z1,z126,z3,z4,z39,z22])],[(0,[z1,z2,z3,z4,z5,z984]),(0,[z1,z13,z2,z3,z191,z4]),(0,[z131,z1,z2,z3,z757,z5])],[(0,[z1,z398,z3,z4,z5,z33]),(0,[z289,z1,z180,z3,z4,z33]),(0,[z1,z2,z96,z4,z6,z33]),(0,[z1,z2,z3,z4,z5,z985]),(0,[z152,z1,z2,z417,z4,z5])],[(0,[z1,z2,z3,z4,z986,z5]),(0,[z1,z2,z3,z4,z987,z6]),(0,[z1,z2,z3,z4,z227,z332]),(0,[z152,z1,z2,z4,z17,z5]),(1,[z1,z2,z3,z757,z5])],[(0,[z1,z2,z988,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z989]),(0,[z990,z1,z2,z3,z4,z6]),(0,[z289,z180,z3,z4,z54,z6]),(1,[z1,z2,z96,z4,z33]),(0,[z289,z2,z3,z4,z847,z6]),(0,[z242,z1,z2,z3,z4,z173]),(0,[z1,z149,z3,z424,z4,z5]),(0,[z1,z2,z3,z4,z5,z233])],[(0,[z1,z2,z3,z991,z4,z5]),(0,[z1,z2,z3,z992,z5,z6]),(0,[z136,z1,z2,z3,z31,z6]),(0,[z198,z1,z2,z3,z4,z234])],[(0,[z256,z2,z3,z21,z5,z33]),(0,[z993,z2,z3,z4,z5,z6]),(0,[z1,z654,z3,z67,z5,z6]),(0,[z1,z2,z15,z3,z4,z340]),(0,[z1,z168,z2,z84,z4,z5])]],
   [[(0,[z1,z994,z3,z4,z5,z6]),(0,[z1,z2,z3,z89,z4,z752]),(0,[z1,z149,z3,z4,z360,z134]),(0,[z1,z2,z3,z4,z995,z5])],[(0,[z320,z1,z2,z264,z4,z57])],[(0,[z1,z2,z3,z996,z5,z6]),(0,[z997,z2,z3,z4,z5,z6]),(0,[z117,z1,z2,z3,z264,z4])],[(0,[z64,z870,z3,z4,z5,z6]),(0,[z2,z710,z29,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z998]),(0,[z1,z2,z3,z4,z214,z33]),(0,[z1,z2,z84,z4,z122,z5])],[(0,[z1,z2,z3,z999,z4,z5]),(0,[z289,z2,z3,z4,z54,z315]),(0,[z1,z2,z3,z1000,z5,z6]),(0,[z136,z1,z2,z3,z212,z75])],[],[(0,[z1,z2,z3,z807,z422,z4]),(0,[z1,z2,z76,z4,z5,z452]),(0,[z50,z1,z2,z3,z4,z315])],[(0,[z1,z13,z2,z3,z4,z5]),(0,[z1,z870,z3,z4,z5,z6]),(0,[z1,z2,z1001,z4,z5,z6]),(0,[z1,z180,z3,z31,z5,z6]),(0,[z1,z2,z1002,z4,z5,z6]),(0,[z389,z388,z2,z3,z4,z5]),(0,[z1003,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z1004,z4,z5,z6]),(0,[z1,z2,z3,z4,z401,z33]),(0,[z1,z2,z3,z476,z5,z6]),(0,[z1,z2,z3,z4,z1005,z6]),(0,[z1,z523,z3,z4,z22,z6]),(0,[z1,z2,z382,z4,z41,z6])],[(0,[z1,z292,z2,z3,z4,z33]),(0,[z2,z3,z4,z5,z736,z190]),(0,[z1,z149,z3,z4,z838,z5]),(0,[z1,z2,z3,z4,z1006,z6]),(0,[z1,z13,z2,z40,z4,z41])],[(0,[z1,z2,z3,z21,z5,z106]),(0,[z1,z398,z3,z4,z6,z33]),(0,[z1,z2,z3,z430,z4,z5]),(0,[z1,z2,z3,z4,z5,z1007]),(0,[z1,z2,z3,z4,z404,z33]),(0,[z1,z2,z3,z4,z5,z1008]),(0,[z148,z1,z2,z3,z4,z33]),(0,[z1,z2,z15,z243,z4,z5]),(0,[z1,z2,z3,z4,z664,z33]),(0,[z932,z2,z3,z4,z5,z6])],[(0,[z1,z398,z3,z476,z5,z6])],[(0,[z55,z2,z3,z4,z512,z5])],[(0,[z1,z2,z3,z4,z234,z6]),(0,[z1009,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z1010,z6])],[(0,[z1,z259,z3,z4,z22,z6]),(0,[z959,z1,z2,z3,z4,z5]),(0,[z1,z13,z2,z3,z306,z5]),(0,[z1,z734,z2,z3,z4,z6])],[(0,[z693,z2,z3,z127,z5,z6]),(0,[z131,z1,z2,z3,z582,z5]),(0,[z1,z2,z1011,z3,z4,z5]),(0,[z1,z2,z3,z4,z59,z33]),(0,[z1,z2,z3,z158,z4,z33])]],
   [[(0,[z1,z1012,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1013]),(0,[z1,z2,z1014,z4,z5,z6]),(0,[z418,z1,z2,z3,z430,z5])],[],[(0,[z1,z2,z3,z1015,z5,z6]),(0,[z1,z2,z3,z4,z752,z6]),(0,[z1,z3,z4,z864,z22,z6]),(0,[z1,z2,z3,z4,z22,z33])],[(0,[z229,z2,z3,z127,z5,z33]),(0,[z1,z2,z3,z4,z429,z33]),(0,[z289,z1,z2,z3,z4,z173]),(0,[z1,z2,z3,z306,z5,z44]),(0,[z1,z3,z4,z209,z22,z33]),(0,[z1,z1016,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z434,z33])],[(0,[z1,z2,z3,z1017,z4,z5])],[(0,[z1,z2,z3,z4,z5,z1018])],[(0,[z1,z2,z3,z4,z5,z1019]),(0,[z289,z2,z76,z4,z54,z6])],[(0,[z1,z2,z3,z4,z1020,z5]),(0,[z1,z2,z3,z4,z315,z33]),(0,[z1,z2,z3,z4,z1021,z5]),(0,[z421,z1,z2,z3,z174,z5])]],
   [[(0,[z1,z13,z126,z3,z4,z22]),(0,[z1,z2,z3,z4,z838,z5]),(0,[z7,z1,z2,z141,z5,z33]),(0,[z1,z2,z3,z264,z4,z87]),(0,[z1,z2,z3,z4,z5,z1022]),(0,[z1,z13,z2,z3,z4,z594])],[(0,[z1,z13,z398,z3,z4,z5]),(0,[z82,z2,z3,z293,z5,z6])],[(0,[z1,z2,z1023,z4,z5,z6]),(0,[z1,z1024,z3,z4,z5,z6]),(0,[z1,z2,z3,z1025,z5,z6]),(0,[z1,z2,z3,z1026,z5,z6]),(0,[z1,z2,z3,z4,z51,z33]),(0,[z1,z2,z3,z4,z1027,z6]),(0,[z1,z2,z3,z4,z1028,z6]),(0,[z1,z2,z3,z757,z317,z5])],[(0,[z1,z2,z651,z3,z4,z33]),(0,[z1,z2,z3,z4,z5,z1029]),(0,[z587,z2,z3,z4,z5,z190]),(0,[z1,z2,z3,z1030,z5,z6]),(0,[z1,z2,z4,z122,z802,z5])],[(0,[z198,z1,z2,z3,z4,z33]),(0,[z439,z1,z2,z3,z4,z33]),(0,[z1,z2,z3,z4,z340,z33])],[(0,[z1,z2,z3,z4,z1031,z6]),(0,[z1,z2,z3,z4,z1032,z6])],[(0,[z1,z2,z3,z1033,z5,z6]),(0,[z289,z2,z3,z4,z54,z33]),(0,[z1,z2,z3,z4,z5,z332]),(0,[z1,z2,z3,z4,z1034,z5])],[(0,[z1,z2,z3,z293,z107,z6]),(0,[z1,z2,z3,z293,z5,z108]),(0,[z1,z2,z3,z4,z5,z1035]),(0,[z1,z2,z3,z4,z1036,z5]),(0,[z1,z2,z3,z707,z4,z5])]],
   [[(0,[z1,z2,z3,z31,z5,z6]),(0,[z289,z1,z2,z3,z4,z33]),(0,[z136,z1,z2,z3,z370,z6]),(0,[z1,z2,z3,z4,z5,z1037]),(0,[z7,z1,z2,z810,z5,z6])],[(0,[z28,z2,z29,z4,z5,z33]),(0,[z389,z1,z2,z3,z4,z234]),(0,[z1038,z2,z3,z4,z5,z6]),(0,[z1,z3,z4,z838,z5,z6])],[(0,[z182,z2,z3,z4,z107,z6]),(0,[z182,z2,z3,z4,z5,z108]),(0,[z1,z2,z298,z4,z41,z6]),(0,[z1,z2,z3,z4,z5,z1039])],[(0,[z1,z398,z3,z31,z5,z6]),(0,[z1040,z1,z2,z3,z4,z5]),(0,[z82,z2,z3,z331,z5,z6]),(0,[z320,z1,z2,z4,z57,z6])],[(0,[z139,z308,z3,z4,z5,z6]),(0,[z117,z1,z398,z3,z4,z6]),(0,[z1,z2,z3,z1041,z5,z6]),(0,[z1,z2,z3,z293,z129,z6])],[(0,[z1,z13,z2,z3,z4,z485]),(0,[z82,z2,z3,z4,z5,z74]),(0,[z1,z3,z715,z14,z5,z6])],[(0,[z1,z2,z3,z4,z5,z1042]),(0,[z1,z2,z1043,z4,z5,z6]),(0,[z1,z2,z3,z422,z4,z6]),(0,[z1,z2,z3,z4,z68,z5]),(0,[z1044,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z1045,z5]),(0,[z1,z2,z96,z4,z5,z6]),(0,[z182,z2,z3,z4,z129,z6]),(0,[z1,z1046,z2,z3,z4,z107]),(0,[z1047,z1,z2,z3,z4,z5]),(0,[z1048,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z1049]),(0,[z1,z13,z2,z3,z4,z283]),(0,[z1,z13,z2,z3,z890,z5])]],
   [[(0,[z1,z2,z3,z1050,z5,z6]),(0,[z1,z2,z3,z31,z5,z33]),(0,[z1,z2,z1051,z4,z5,z6]),(0,[z1052,z1,z3,z4,z5,z6]),(0,[z1,z13,z734,z2,z3,z4])],[(0,[z1,z2,z3,z1053,z5,z6]),(0,[z1,z2,z3,z1054,z5,z6]),(0,[z1,z2,z3,z4,z5,z1055]),(0,[z1,z211,z2,z3,z4,z5]),(0,[z289,z13,z2,z3,z4,z54]),(0,[z1,z2,z3,z331,z107,z6]),(0,[z1,z2,z3,z331,z5,z108]),(0,[z1,z2,z3,z4,z41,z494]),(0,[z1,z2,z3,z904,z5,z6])],[(0,[z870,z49,z3,z4,z5,z6]),(0,[z439,z49,z3,z4,z5,z6]),(0,[z1,z398,z96,z4,z5,z6]),(1,[z2,z3,z4,z5,z736]),(0,[z1,z2,z3,z4,z1056,z6]),(0,[z1,z1046,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z469,z5]),(0,[z204,z1,z2,z158,z4,z5])],[(0,[z139,z64,z3,z4,z5,z6]),(0,[z1,z2,z3,z1057,z5,z6]),(0,[z1,z2,z3,z4,z5,z1058]),(0,[z130,z64,z3,z4,z5,z6]),(0,[z256,z2,z3,z68,z21,z5]),(0,[z1,z2,z3,z4,z107,z74]),(0,[z1,z2,z3,z4,z5,z1059]),(0,[z320,z1,z2,z4,z57,z33])],[(0,[z418,z1,z2,z3,z5,z33]),(0,[z1,z2,z27,z4,z57,z6]),(0,[z131,z1,z2,z3,z174,z5]),(0,[z1,z2,z3,z1041,z5,z33])],[(0,[z136,z1,z2,z3,z95,z6]),(0,[z109,z1,z89,z4,z5,z6])],[(0,[z1,z2,z3,z1060,z5,z6]),(0,[z1,z1061,z3,z4,z5,z6]),(0,[z1,z2,z3,z331,z129,z6]),(0,[z1,z2,z3,z81,z757,z5])],[(0,[z1,z2,z3,z4,z5,z1062]),(0,[z1,z2,z3,z4,z5,z1063]),(0,[z638,z1,z2,z3,z4,z33])]],
   [[(0,[z1,z2,z3,z4,z5,z1064]),(0,[z1,z2,z3,z4,z129,z74]),(0,[z45,z1,z3,z14,z5,z6]),(0,[z7,z1,z2,z167,z5,z6]),(0,[z1,z2,z3,z4,z122,z172]),(0,[z1,z2,z3,z904,z128,z6])],[(0,[z1,z2,z3,z4,z1065,z6]),(0,[z511,z2,z3,z21,z5,z6]),(0,[z1,z2,z3,z4,z5,z1066])],[(0,[z247,z2,z192,z4,z5,z6]),(0,[z289,z1,z398,z3,z4,z33]),(0,[z1067,z2,z3,z4,z5,z6])],[(0,[z1,z2,z1068,z4,z5,z6]),(0,[z1,z2,z1069,z3,z4,z5]),(0,[z258,z1,z2,z3,z202,z5])],[(0,[z109,z182,z89,z4,z5,z6]),(0,[z1,z2,z3,z430,z4,z752])],[(0,[z1,z2,z3,z1070,z5,z6]),(0,[z28,z13,z2,z29,z4,z5]),(0,[z1,z2,z3,z4,z1071,z6]),(0,[z1072,z1,z2,z3,z5,z6])],[(0,[z2,z192,z710,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1073]),(0,[z1,z2,z15,z4,z802,z5]),(0,[z189,z1,z2,z3,z4,z33])],[(0,[z284,z49,z3,z4,z5,z33]),(0,[z2,z3,z4,z847,z54,z6]),(1,[z1,z3,z715,z5,z6])]],
   [[(0,[z1,z481,z2,z3,z4,z33]),(0,[z1,z1074,z3,z4,z5,z6]),(0,[z320,z1,z2,z4,z336,z6]),(0,[z1,z2,z3,z4,z22,z332]),(0,[z1,z13,z2,z3,z4,z33])],[(0,[z50,z1,z13,z2,z3,z4]),(0,[z1,z3,z4,z1075,z5,z6])],[(0,[z247,z2,z192,z4,z5,z33]),(0,[z256,z2,z3,z21,z5,z6]),(0,[z1,z2,z3,z317,z306,z5]),(0,[z1,z2,z3,z4,z615,z33]),(0,[z1,z2,z3,z4,z57,z494]),(0,[z343,z2,z3,z4,z5,z154])],[(0,[z1,z2,z3,z4,z5,z1076])],[(0,[z1,z2,z3,z1077,z5,z6]),(0,[z1,z1078,z2,z3,z4,z5]),(0,[z389,z2,z3,z4,z5,z736]),(0,[z1,z13,z78,z2,z3,z4]),(1,[z1,z2,z3,z904,z6])],[(0,[z1,z2,z3,z4,z5,z1079]),(0,[z389,z2,z3,z4,z5,z44]),(0,[z1080,z1,z2,z4,z5,z6])],[(0,[z1,z2,z3,z1081,z5,z6]),(0,[z1,z2,z3,z4,z5,z1082]),(0,[z1,z1083,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z5,z1084])],[(0,[z1,z2,z3,z4,z1085,z6]),(0,[z1,z2,z96,z476,z5,z6]),(0,[z1,z2,z15,z4,z172,z16])]],
   [[(0,[z1,z2,z3,z1086,z5,z6]),(0,[z1,z2,z3,z4,z5,z1087])],[(0,[z1,z2,z3,z81,z4,z234]),(0,[z1,z2,z3,z1088,z5,z6]),(0,[z1,z2,z3,z4,z1089,z5])],[(0,[z2,z870,z3,z4,z5,z6]),(0,[z389,z2,z3,z4,z44,z234]),(0,[z1,z2,z3,z4,z1090,z6]),(0,[z1,z2,z3,z81,z202,z5])],[(0,[z82,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1091]),(0,[z1,z2,z3,z4,z1092,z6]),(0,[z109,z1,z89,z4,z5,z108]),(0,[z1,z2,z1093,z3,z5,z6]),(0,[z1,z2,z382,z4,z5,z16]),(0,[z722,z2,z3,z4,z5,z6]),(0,[z131,z1,z2,z3,z81,z5])],[(0,[z28,z2,z710,z4,z5,z6]),(0,[z131,z1,z2,z3,z306,z5]),(0,[z688,z2,z3,z4,z5,z190]),(0,[z418,z1,z13,z2,z3,z5]),(0,[z1,z2,z3,z1094,z5,z6]),(0,[z1,z2,z3,z1077,z5,z33])],[],[(0,[z1,z2,z3,z4,z1095,z6])],[(0,[z1096,z1,z2,z3,z4,z6]),(0,[z55,z1,z2,z3,z4,z234]),(0,[z1,z13,z2,z3,z4,z107]),(0,[z1,z2,z3,z1097,z4,z5])]],
   [[(0,[z1,z2,z3,z4,z5,z1098]),(0,[z242,z2,z3,z4,z25,z181]),(0,[z1,z2,z3,z4,z1099,z5]),(0,[z1,z2,z3,z4,z5,z1100])],[(0,[z1,z64,z3,z4,z22,z33]),(0,[z247,z13,z2,z192,z4,z5]),(0,[z1,z2,z3,z4,z5,z106]),(0,[z1,z2,z3,z4,z5,z452]),(0,[z1,z2,z3,z4,z597,z33]),(0,[z1,z2,z3,z4,z234,z104]),(0,[z1,z2,z3,z4,z107,z6]),(0,[z1,z2,z3,z4,z5,z108]),(0,[z1,z2,z3,z390,z5,z104])],[(0,[z1,z2,z3,z4,z5,z888]),(0,[z152,z1,z2,z4,z122,z5])],[(0,[z1,z2,z3,z422,z4,z68]),(0,[z1,z80,z2,z3,z4,z33]),(0,[z82,z2,z3,z4,z5,z33])],[(0,[z1,z1101,z2,z3,z4,z6]),(0,[z1,z398,z3,z4,z5,z452]),(0,[z152,z1,z2,z3,z4,z340]),(0,[z1,z2,z3,z4,z1102,z6]),(0,[z1,z2,z3,z4,z87,z33]),(0,[z282,z1,z2,z3,z423,z5])],[(0,[z1,z2,z3,z4,z565,z33]),(0,[z1,z2,z3,z1103,z5,z6]),(1,[z2,z3,z4,z847,z6]),(0,[z2,z3,z4,z5,z736,z6]),(0,[z1,z1104,z2,z3,z4,z5])],[(0,[z1,z2,z3,z1105,z5,z6]),(0,[z229,z2,z3,z127,z5,z6]),(0,[z1,z2,z3,z4,z129,z6])],[(0,[z1,z2,z3,z4,z5,z1106])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 542) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 542).take 527) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1069).take 105) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1174)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [542, 527, 105] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 124).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 124).take 129).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 253).take 3).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [124, 129, 3] = true :=
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

end PEqualNP.Outside.L_meta_43964

theorem PEqualNP.Outside.L_meta_43964 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276813032 * 2 ^ 32 + 4276807872) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276813032 * 2 ^ 32 + 4276807872) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_43964.solve