import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_36821

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
  Nat.testBit (4276677352 * 2 ^ 32 + 4007717600) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x100045822c862162#64 ++ 0x080022c1164310b1#64 ++ 0xef00cf9e7d8e67e7#64 ++ 0xf78067cf3ec733f3#64 : BitVec 256),
   (0x200312a894b28b28#64 ++ 0x900189544a594594#64 ++ 0xdf8733e99ef39b39#64 ++ 0xefc399f4cf79cd9c#64 : BitVec 256),
   (0x4038285143015414#64 ++ 0x201c1428a180aa0a#64 ++ 0xbe783c71e303fc3f#64 ++ 0xdf3c1e38f181fe1f#64 : BitVec 256),
   (0x805d807c03581e80#64 ++ 0xc02ec03e01ac0f40#64 ++ 0x7dffc07e03fc1fc1#64 ++ 0xbeffe03f01fe0fe0#64 : BitVec 256),
   (0x01eeff8003efe001#64 ++ 0x00f77fc001f7f000#64 ++ 0xf9ffff8003ffe001#64 ++ 0x7cffffc001fff000#64 : BitVec 256),
   (0x02f7ff7ff8000000#64 ++ 0x017bffbffc000000#64 ++ 0xfafffffffc000000#64 ++ 0xfd7ffffffe000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [0, 1]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [0, 4]⟩, ⟨.and, [3, 8]⟩, ⟨.and, [2, 9]⟩, ⟨.or, [6, 10]⟩, ⟨.or, [2, 9]⟩, ⟨.and, [7, 12]⟩, ⟨.and, [11, 5]⟩, ⟨.or, [13, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x01eeff8003efe001 0x00f77fc001f7f000 0xf9ffff8003ffe001 0x7cffffc001fff000

def z1 : W := mkw 0x02f7ff7ff8000000 0x017bffbffc000000 0xfafffffffc000000 0xfd7ffffffe000000

def z2 : W := mkw 0x03efffaebbefe001 0x01f7ffd75df7f000 0xf9ffff8e1fffe001 0x7cffffc70ffff000

def z3 : W := mkw 0x100045822c862162 0x080022c1164310b1 0xef00cf9e7d8e67e7 0xf78067cf3ec733f3

def z4 : W := mkw 0x200312a894b28b28 0x900189544a594594 0xdf8733e99ef39b39 0xefc399f4cf79cd9c

def z5 : W := mkw 0x4038285143015414 0x201c1428a180aa0a 0xbe783c71e303fc3f 0xdf3c1e38f181fe1f

def z6 : W := mkw 0x805d807c03581e80 0xc02ec03e01ac0f40 0x7dffc07e03fc1fc1 0xbeffe03f01fe0fe0

def z7 : W := mkw 0x200312a894b28b28 0x900189544a594594 0x928733e19e739838 0x494399f0cf39cc1c

def z8 : W := mkw 0x02a27f03f8000000 0x01513f81fc000000 0xea00ff9ffc000000 0xf5007fcffe000000

def z9 : W := mkw 0x80ffff7c03581e80 0xc07fffbe01ac0f40 0xfdfffffe03fc1fc1 0xfeffffff01fe0fe0

def z10 : W := mkw 0x4000000140000014 0x20000000a000000a 0x02000001e000003e 0x01000000f000001f

def z11 : W := mkw 0x42ffba7dd3015414 0x217fdd3ee980aa0a 0xbeff3c71e303fc3f 0xdf7f9e38f181fe1f

def z12 : W := mkw 0x4000000000014014 0x200000000000a00a 0x000000000003e03e 0x000000000001f01f

def z13 : W := mkw 0x1108008007efe163 0x0884004003f7f0b1 0x0500000003ffe7e7 0x0280000001fff3f3

def z14 : W := mkw 0x11eeff822fefe163 0x08f77fc117f7f0b1 0xffffff9e7fffe7e7 0xffffffcf3ffff3f3

def z15 : W := mkw 0x8011007c00101e80 0xc008803e00080f40 0x0400007e00001fc0 0x8200003f00000fe0

def z16 : W := mkw 0x100045822c862162 0x080022c1164310b1 0x82000f807c026026 0x410007c03e013013

def z17 : W := mkw 0x805d807c03581e80 0xc02ec03e01ac0f40 0x10ff006002701800 0x087f803001380c00

def z18 : W := mkw 0x004c800003480000 0x0026400001a40000 0x79ffc00003fc0001 0x3cffe00001fe0000

def z19 : W := mkw 0x200312a894b28b28 0x900189544a594594 0x860033e99c039b38 0xc30019f4ce01cd9c

def z20 : W := mkw 0x4008000003015414 0x200400000180aa0a 0x9e0030618303fc3f 0xcf001830c181fe1f

def z21 : W := mkw 0x2003122890308a08 0x9001891448184504 0x1087306182719818 0x08439830c138cc0c

def z22 : W := mkw 0x200312a894b28b28 0x900189544a594594 0x418703881cf00300 0x20c381c40e780180

def z23 : W := mkw 0x805c805403481480 0x402e402a01a40a40 0x3c78c076030c1cc1 0x9e3c603b01860e60

def z24 : W := mkw 0x01a23a000021c001 0x00d11d000010e000 0x0000300000018000 0x000018000000c000

def z25 : W := mkw 0x01eeba000369c001 0x00f75d0001b4e000 0x10ff300002718000 0x087f98000138c000

def z26 : W := mkw 0x4010005140001414 0x20080028a0000a0a 0x06000071e0001c3e 0x83000038f0000e1f

def z27 : W := mkw 0x0003122890000000 0x0001891448000000 0xda8733e99c000000 0xed4399f4ce000000

def z28 : W := mkw 0x000045822c820120 0x000022c116410090 0xef00cf9e7c820321 0xf78067cf3e410190

def z29 : W := mkw 0x1000450228042042 0x0800228114021021 0x6d00cc1e618c67c7 0xb680660f30c633e3

def z30 : W := mkw 0x2002128094a28128 0x100109404a514094 0x820033819c038038 0x410019c0ce01c01c

def z31 : W := mkw 0x805c805403481480 0x402e402a01a40a40 0x2078c016010c04c0 0x103c600b00860260

def z32 : W := mkw 0xc07da87d43595e94 0xe03ed43ea1acaf4a 0x10ff306182719818 0x087f9830c138cc0c

def z33 : W := mkw 0x8045802c00580a80 0xc022c016002c0540 0x4187c00e00fc03c0 0x20c3e007007e01e0

def z34 : W := mkw 0x0028280003014000 0x001414000180a000 0x1078300002018000 0x083c18000100c000

def z35 : W := mkw 0x4038285143015414 0x201c1428a180aa0a 0x9e78306182039839 0xcf3c1830c101cc1c

def z36 : W := mkw 0x01eeba000369c001 0x00f75d0001b4e000 0x79fff00003fd8001 0x3cfff80001fec000

def z37 : W := mkw 0x02f7ba7ff8000000 0x017bdd3ffc000000 0x12ff307ffc000000 0x897f983ffe000000

def z38 : W := mkw 0x0211007ff8000000 0x0108803ffc000000 0x0200007ffc000000 0x8100003ffe000000

def z39 : W := mkw 0x100000822c820162 0x08000041164100b1 0xcf00039e7c8207e7 0xe78001cf3e4103f3

def z40 : W := mkw 0x0028280003014000 0x001414000180a000 0xb8783c000303e001 0x5c3c1e000181f000

def z41 : W := mkw 0x01c6d78000eea001 0x00e36bc000775000 0x4187c38000fc0000 0x20c3e1c0007e0000

def z42 : W := mkw 0x02c7d72eb8000000 0x0163eb975c000000 0x4087c38e1c000000 0x2043e1c70e000000

def z43 : W := mkw 0x4008000003015414 0x200400000180aa0a 0x040000000303fc3f 0x020000000181fe1f

def z44 : W := mkw 0x300357aabcb6ab6a 0x9801abd55e5b55b5 0xff87ffffffffffff 0xffc3ffffffffffff

def z45 : W := mkw 0xa05f92fc97fa9fa8 0xd02fc97e4bfd4fd4 0xfffff3ff9fff9ff9 0xfffff9ffcfffcffc

def z46 : W := mkw 0x0055c57e28000000 0x002ae2bf14000000 0xfaffcffe7c000000 0xfd7fe7ff3e000000

def z47 : W := mkw 0x905dc5fe2fde3fe2 0xc82ee2ff17ef1ff1 0xffffcffe7ffe7fe7 0xffffe7ff3fff3ff3

def z48 : W := mkw 0x82ffff7ffb581e80 0xc17fffbffdac0f40 0xfafffffffe701800 0xfd7fffffff380c00

def z49 : W := mkw 0xa008008007fa9fa8 0xd004004003fd4fd4 0x0500000003ff9ff9 0x0280000001ffcffc

def z50 : W := mkw 0x81eeff8003fffe81 0xc0f77fc001ffff40 0xfdffff8003ffffc1 0x7effffc001ffffe0

def z51 : W := mkw 0xa011007c94101fa8 0xd008803e4a080fd4 0x0600007f9c001ff8 0x8300003fce000ffc

def z52 : W := mkw 0x01aa7f8003a7e001 0x00d53fc001d3f000 0xb8783f800303e001 0x5c3c1fc00181f000

def z53 : W := mkw 0x0000000000000000 0x0000000000000000 0x6900c000018c0001 0x3480600000c60000

def z54 : W := mkw 0x00e6ff0228000000 0x00737f8114000000 0xfaffff9e7c000000 0xfd7fffcf3e000000

def z55 : W := mkw 0x00e7ff2890000000 0x0073ff9448000000 0xfaffffe99c000000 0xfd7ffff4ce000000

def z56 : W := mkw 0x41eeff8003eff415 0x20f77fc001f7fa0a 0xfdffff8003fffc3f 0x7effffc001fffe1f

def z57 : W := mkw 0x12f7ff7ff8042042 0x097bffbffc021021 0xfafffffffd0c64c6 0xfd7ffffffe863263

def z58 : W := mkw 0x02f7ba7dd0000000 0x017bdd3ee8000000 0x78fff07f80000000 0xbc7ff83fc0000000

def z59 : W := mkw 0x01eced00034d6001 0x00f6768001a6b000 0x2078cc00010c6000 0x103c660000863000

def z60 : W := mkw 0x41feffd143eff415 0x20ff7fe8a1f7fa0a 0xfffffff1e3fffc3f 0xfffffff8f1fffe1f

def z61 : W := mkw 0x01a27f8000a7e001 0x00d13fc00053f000 0x80003f800003e000 0x40001fc00001f000

def z62 : W := mkw 0x805d807c03581e80 0xc02ec03e01ac0f40 0x78ffc07e02701800 0xbc7fe03f01380c00

def z63 : W := mkw 0x004cc58003ce2000 0x002662c001e71000 0xf9ffcf8003fe6001 0x7cffe7c001ff3000

def z64 : W := mkw 0x000312a890a28000 0x0001895448514000 0xdb8733e99ef38001 0xedc399f4cf79c000

def z65 : W := mkw 0x0108008003efe001 0x0084004001f7f000 0x0100000003ffe001 0x0080000001fff000

def z66 : W := mkw 0x82ffff7ffb581e80 0xc17fffbffdac0f40 0xfffffffffffc1fc1 0xfffffffffffe0fe0

def z67 : W := mkw 0x0011007c00000000 0x0008803e00000000 0x0000007e00000000 0x8000003f00000000

def z68 : W := mkw 0x0000000000000000 0x0000000000000000 0x6d00c01e018c07c1 0xb680600f00c603e0

def z69 : W := mkw 0x02b37f7ff8000000 0x0159bfbffc000000 0x82003ffffc000000 0xc1001ffffe000000

def z70 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z71 : W := mkw 0x02f7ba7dd0000000 0x017bdd3ee8000000 0x10ff306180000000 0x087f9830c0000000

def z72 : W := mkw 0x1211007ffc000162 0x0908803ffe0000b1 0x0600007ffc0007e6 0x8300003ffe0003f3

def z73 : W := mkw 0x4038285143015414 0x201c1428a180aa0a 0x20780c1061006406 0x103c060830803203

def z74 : W := mkw 0xc011007d40101e94 0xe008803ea0080f4a 0x0600007fe0001ffe 0x8300003ff0000fff

def z75 : W := mkw 0xc07da87d43595e94 0xe03ed43ea1acaf4a 0xfffffc7fe3ffffff 0xfffffe3ff1ffffff

def z76 : W := mkw 0x300312aabcb28b6a 0x980189555e5945b5 0xdf8733fffef39fff 0xefc399ffff79cfff

def z77 : W := mkw 0x0182578000a6a001 0x00c12bc000535000 0x0000038000000000 0x000001c000000000

def z78 : W := mkw 0x100045822c862162 0x080022c1164310b1 0xeb00cf807d8e6027 0x758067c03ec73013

def z79 : W := mkw 0x1000008004862162 0x08000040024310b1 0x05000000018e67e7 0x0280000000c733f3

def z80 : W := mkw 0x2003122890308a08 0x9001891448184504 0xda8733e99e719818 0xed4399f4cf38cc0c

def z81 : W := mkw 0x01eeff8003efe001 0x00f77fc001f7f000 0x61ffcf8001fc6000 0x30ffe7c000fe3000

def z82 : W := mkw 0x8044800400480080 0x4022400200240040 0x0000c006000c00c0 0x0000600300060060

def z83 : W := mkw 0x100045822c862162 0x080022c1164310b1 0xcf000f887c826327 0xe78007c43e413193

def z84 : W := mkw 0x03fffffffbefe001 0x01fffffffdf7f000 0xfbffffffffffe001 0xfdfffffffffff000

def z85 : W := mkw 0x0000450228000000 0x0000228114000000 0xea00cf9e7c000000 0xf50067cf3e000000

def z86 : W := mkw 0x21a27f8094a7e129 0x10d13fc04a53f094 0x82003f819c03e038 0x41001fc0ce01f01c

def z87 : W := mkw 0x200357aabcb28b28 0x9001abd55e594594 0xff87fffffef39b39 0xffc3ffffff79cd9c

def z88 : W := mkw 0x50386dd36f877576 0x281c36e9b7c3babb 0xff78ffffff8fffff 0xffbc7fffffc7ffff

def z89 : W := mkw 0x4038285143015414 0x201c1428a180aa0a 0xb8783c106303e407 0x5c3c1e083181f203

def z90 : W := mkw 0x0030285140000000 0x00181428a0000000 0xba783c71e0000000 0xdd3c1e38f0000000

def z91 : W := mkw 0x11eeff822fefe163 0x08f77fc117f7f0b1 0xf9ffff8e1fffe3c1 0x7cffffc70ffff1e0

def z92 : W := mkw 0x0075a87d40000000 0x003ad43ea0000000 0xfafffc7fe0000000 0xfd7ffe3ff0000000

def z93 : W := mkw 0x004c800003480000 0x0026400001a40000 0x10ff000002700000 0x087f800001380000

def z94 : W := mkw 0x0030285140000000 0x00181428a0000000 0x1078306180000000 0x083c1830c0000000

def z95 : W := mkw 0x501000536c001576 0x28080029b6000abb 0x0600007ffc001ffe 0x8300003ffe000fff

def z96 : W := mkw 0x603b3af9d7b3df3c 0xb01d9d7cebd9ef9e 0xdfff33e99ef39b39 0xefff99f4cf79cd9c

def z97 : W := mkw 0x2002128094a28128 0x100109404a514094 0xcf0033899c838339 0xe78019c4ce41c19c

def z98 : W := mkw 0x603b3af9d7b3df3c 0xb01d9d7cebd9ef9e 0xffff3ff9fff3ff3f 0xffff9ffcfff9ff9f

def z99 : W := mkw 0x01c6d78000eea001 0x00e36bc000775000 0xd987f38002ff8001 0x6cc3f9c0017fc000

def z100 : W := mkw 0x91fffffe2fffffe3 0xc8ffffff17fffff1 0xfffffffe7fffffe7 0xffffffff3ffffff3

def z101 : W := mkw 0x100045822c862162 0x080022c1164310b1 0x4100c38e1c8c03c0 0x208061c70e4601e0

def z102 : W := mkw 0x603828d147b3df3c 0xb01c1468a3d9ef9e 0xbf783c71e3f3ff3f 0xdfbc1e38f1f9ff9f

def z103 : W := mkw 0x21efffa897ffeb29 0x90f7ffd44bfff594 0xffffffe99ffffb39 0xfffffff4cffffd9c

def z104 : W := mkw 0x00eeff0003014000 0x00777f800180a000 0xf8ffff800303e001 0x7c7fffc00181f000

def z105 : W := mkw 0x004c800003480000 0x0026400001a40000 0x7dffc01e03fc07c1 0xbeffe00f01fe03e0

def z106 : W := mkw 0x0028280003014000 0x001414000180a000 0xbe783c106303e427 0xdf3c1e083181f213

def z107 : W := mkw 0x805d807c03581e80 0xc02ec03e01ac0f40 0x2478c07e010c1fc0 0x923c603f00860fe0

def z108 : W := mkw 0x10286d822f876162 0x081436c117c3b0b1 0xff78ff9e7f8fe7e7 0xffbc7fcf3fc7f3f3

def z109 : W := mkw 0x3001002abc100b6a 0x980080155e0805b5 0x0600007ffc001ffe 0x8300003ffe000fff

def z110 : W := mkw 0x8008000003581e80 0xc004000001ac0f40 0x0500000003fc1fc1 0x0280000001fe0fe0

def z111 : W := mkw 0x200100a804b28b28 0x9000805402594594 0x5d87006802f39b39 0xaec380340179cd9c

def z112 : W := mkw 0x11eeff822fefe163 0x08f77fc117f7f0b1 0xfbffff807fffe027 0x7dffffc03ffff013

def z113 : W := mkw 0x81ffba7c0379de81 0xc0ffdd3e01bcef40 0x7dfff07e03fd9fc1 0xbefff83f01fecfe0

def z114 : W := mkw 0x9011007e2c101fe2 0xc808803f16080ff1 0x0600007e7c001fe6 0x8300003f3e000ff3

def z115 : W := mkw 0x01efffa803ffea01 0x80f7ffd401fff500 0xfdffffe803fffb01 0xfefffff401fffd80

def z116 : W := mkw 0x00c6d70000000000 0x00636b8000000000 0x4087c38000000000 0x2043e1c000000000

def z117 : W := mkw 0x11eced022b4d6043 0x08f6768115a6b021 0x2078cc16610c64c6 0x103c660b30863263

def z118 : W := mkw 0x100257822ca6a162 0x08012bc1165350b1 0xff87ff9e7fffe7e7 0xffc3ffcf3ffff3f3

def z119 : W := mkw 0x100000022c000162 0x08000001160000b1 0xae000c1e7d0267e7 0xd700060f3e8133f3

def z120 : W := mkw 0x2000008004b28b28 0x9000004002594594 0x0500000002f39b39 0x028000000179cd9c

def z121 : W := mkw 0x01eeba8003efe001 0x00f75d4001f7f000 0x11ff300003ffe001 0x08ff980001fff000

def z122 : W := mkw 0x1000450228042042 0x0800228114021021 0x2000cc16610c64c6 0x1000660b30863263

def z123 : W := mkw 0x2003122890308a08 0x9001891448184504 0x5d87306982f19b19 0xaec39834c178cd8c

def z124 : W := mkw 0x02f7ff7ff8000000 0x017bffbffc000000 0xfefffffffe039839 0xff7fffffff01cc1c

def z125 : W := mkw 0x0000000000000000 0x0000000000000000 0x1c00006002001801 0x8e00003001000c00

def z126 : W := mkw 0x21efffa897ffeb29 0x90f7ffd44bfff594 0xf9ffff881fffe301 0x7cffffc40ffff180

def z127 : W := mkw 0x0038285143014000 0x001c1428a180a000 0xba783c71e303e001 0xdd3c1e38f181f000

def z128 : W := mkw 0x0000000000000000 0x0000000000000000 0x0600001060000426 0x8300000830000213

def z129 : W := mkw 0x42ffba7dd3015414 0x217fdd3ee980aa0a 0x10ff306182019818 0x087f9830c100cc0c

def z130 : W := mkw 0x0055807c00000000 0x002ac03e00000000 0x78ffc07e00000000 0xbc7fe03f00000000

def z131 : W := mkw 0x0002128000a28000 0x0001094000514000 0xd987338002f38001 0x6cc399c00179c000

def z132 : W := mkw 0x0000450228000000 0x0000228114000000 0x82000f807c000000 0x410007c03e000000

def z133 : W := mkw 0x000100a804920b20 0x8000805402490590 0xdf8703e81ef21b21 0xefc381f40f790d90

def z134 : W := mkw 0x0018005003001400 0x000c002801800a00 0x3c78007003001c01 0x9e3c003801800e00

def z135 : W := mkw 0x01ced78003eea001 0x00e76bc001f75000 0x79ffc38003fc0001 0x3cffe1c001fe0000

def z136 : W := mkw 0x01c6920000688001 0x00e3490000344000 0x0087000000700000 0x0043800000380000

def z137 : W := mkw 0x0002128000a28000 0x0001094000514000 0x4187038000f00000 0x20c381c000780000

def z138 : W := mkw 0x8211007ff8101e80 0xc108803ffc080f40 0x0600007ffc001fc0 0x8300003ffe000fe0

def z139 : W := mkw 0x11eeff822befe043 0x08f77fc115f7f021 0xf9ffff9663ffe4c7 0x7cffffcb31fff263

def z140 : W := mkw 0x0000000000000000 0x0000000000000000 0xae000c1061026427 0xd700060830813213

def z141 : W := mkw 0x2000000094000128 0x100000004a000094 0x020000019c000038 0x01000000ce00001c

def z142 : W := mkw 0xc038285143595e94 0xe01c1428a1acaf4a 0xbf783c71e3ffffff 0xdfbc1e38f1ffffff

def z143 : W := mkw 0x200312a894b28b28 0x900189544a594594 0x518733e99ef19b18 0x28c399f4cf78cd8c

def z144 : W := mkw 0x2001002894100b28 0x900080144a080594 0x060000699c001b38 0x83000034ce000d9c

def z145 : W := mkw 0x0000450228000000 0x0000228114000000 0xee00cf9e7d026427 0xf70067cf3e813213

def z146 : W := mkw 0x02d7d77eb8000000 0x016bebbf5c000000 0x78ffc3fe1c000000 0xbc7fe1ff0e000000

def z147 : W := mkw 0x0010005140000000 0x00080028a0000000 0x02000071e0000000 0x81000038f0000000

def z148 : W := mkw 0x02a06d0368000000 0x01503681b4000000 0x00000c0060000000 0x0000060030000000

def z149 : W := mkw 0x00286d8003876000 0x001436c001c3b000 0xf978ff80038fe001 0x7cbc7fc001c7f000

def z150 : W := mkw 0x905cc5562b4c34c2 0x482e62ab15a61a61 0x2078cc16610c64c6 0x103c660b30863263

def z151 : W := mkw 0x0030285140000000 0x00181428a0000000 0xbe783c71e1026427 0xdf3c1e38f0813213

def z152 : W := mkw 0x02f4ed5768000000 0x017a76abb4000000 0x2078cc1660000000 0x103c660b30000000

def z153 : W := mkw 0x804c800003581e80 0xc026400001ac0f40 0x7dffc00003fc1fc1 0x3effe00001fe0fe0

def z154 : W := mkw 0x2108008007ffeb29 0x9084004003fff594 0x0500000003fffb39 0x0280000001fffd9c

def z155 : W := mkw 0x0000450228000000 0x0000228114000000 0x2000cc1660000000 0x1000660b30000000

def z156 : W := mkw 0x4020280140014014 0x20101400a000a00a 0x82003c01e003e03e 0x41001e00f001f01f

def z157 : W := mkw 0x00e6ff0000000000 0x00737f8000000000 0xf8ffff8000000000 0x7c7fffc000000000

def z158 : W := mkw 0x0000000000000000 0x0000000000000000 0x9800300002038001 0x4c0018000101c000

def z159 : W := mkw 0x02f7ff7ff8000000 0x017bffbffc000000 0x92ff3fe1fc000000 0x497f9ff0fe000000

def z160 : W := mkw 0x101845d22f863562 0x080c22e917c31ab1 0xff78cffe7f8e7fe7 0xffbc67ff3fc73ff3

def z161 : W := mkw 0x12f7fffffc862162 0x097bfffffe4310b1 0xfffffffffd8e67e7 0xfffffffffec733f3

def z162 : W := mkw 0x42ffff7ffb015414 0x217fffbffd80aa0a 0xfeffffffff03fc3f 0xff7fffffff81fe1f

def z163 : W := mkw 0x01eeba000369c001 0x00f75d0001b4e000 0xb8ff3c000373e001 0x5c7f9e0001b9f000

def z164 : W := mkw 0x0000458000862000 0x000022c000431000 0x4100c380008c0000 0x208061c000460000

def z165 : W := mkw 0x807da87d43581e80 0xc03ed43ea1ac0f40 0xfffffc7fe3fc1fc1 0xfffffe3ff1fe0fe0

def z166 : W := mkw 0x00306d5368000000 0x001836a9b4000000 0xfa78fffffc000000 0xfd3c7ffffe000000

def z167 : W := mkw 0x9008008007de3fe2 0xc804004003ef1ff1 0x0500000003fe7fe7 0x0280000001ff3ff3

def z168 : W := mkw 0x200312a894b28b28 0x900189544a594594 0xcf8703881cf20321 0xe7c381c40e790190

def z169 : W := mkw 0x0000458000862000 0x000022c000431000 0xe900cf80018e6001 0x748067c000c73000

def z170 : W := mkw 0x50386d536b057456 0x281c36a9b582ba2b 0xbe78fc77e30ffcff 0xdf3c7e3bf187fe7f

def z171 : W := mkw 0x4038285143015414 0x201c1428a180aa0a 0x1078306182019818 0x083c1830c100cc0c

def z172 : W := mkw 0x42f7ff7ff8014014 0x217bffbffc00a00a 0xfafffffffc03e03e 0xfd7ffffffe01f01f

def z173 : W := mkw 0x0000450228000000 0x0000228114000000 0xef00cf9e7d8c07c1 0xf78067cf3ec603e0

def z174 : W := mkw 0x13ffffffffefe163 0x09fffffffff7f0b1 0xffffffffffffe7e7 0xfffffffffffff3f3

def z175 : W := mkw 0x11c6d7822ceea163 0x08e36bc1167750b1 0x4187c38e1cfc03c0 0x20c3e1c70e7e01e0

def z176 : W := mkw 0x02a27f03f8000000 0x01513f81fc000000 0x82003f81fc000000 0x41001fc0fe000000

def z177 : W := mkw 0x03eeff83fbefe001 0x01f77fc1fdf7f000 0xfbffff81ffffe001 0x7dffffc0fffff000

def z178 : W := mkw 0x02a37f2bf8000000 0x0151bf95fc000000 0xda873fe9fc000000 0xed439ff4fe000000

def z179 : W := mkw 0x01a27f8000a7e001 0x00d13fc00053f000 0xe900ff80018fe001 0x74807fc000c7f000

def z180 : W := mkw 0x03fced576b4d6001 0x01fe76abb5a6b000 0x2078cc16610c6000 0x103c660b30863000

def z181 : W := mkw 0x0001002890000000 0x0000801448000000 0x020000699c000000 0x81000034ce000000

def z182 : W := mkw 0x0044800000000000 0x0022400000000000 0x78ffc00000000000 0x3c7fe00000000000

def z183 : W := mkw 0x82f7ff7ff8101e80 0xc17bffbffc080f40 0xfefffffffc001fc0 0xff7ffffffe000fe0

def z184 : W := mkw 0x00e6ff8000a28000 0x00737fc000514000 0xf9ffff8002f38001 0x7cffffc00179c000

def z185 : W := mkw 0x22f7fffffcb28b28 0x917bfffffe594594 0xfffffffffef39b39 0xffffffffff79cd9c

def z186 : W := mkw 0x42fced576b015414 0x217e76abb580aa0a 0x2078cc1661006406 0x103c660b30803203

def z187 : W := mkw 0x703b7ffbffb7ff7e 0xb81dbffdffdbffbf 0xffffffffffffffff 0xffffffffffffffff

def z188 : W := mkw 0x01eced00034d6001 0x00f6768001a6b000 0xb878fc00030fe001 0x5c3c7e000187f000

def z189 : W := mkw 0x100045822c862162 0x080022c1164310b1 0xc300cf8e7c8e63e6 0x618067c73e4731f3

def z190 : W := mkw 0x0020280000014000 0x001014000000a000 0x80003c000003e000 0x40001e000001f000

def z191 : W := mkw 0x02a23a01d0000000 0x01511d00e8000000 0x0000300180000000 0x00001800c0000000

def z192 : W := mkw 0x02f4ed5768000000 0x017a76abb4000000 0xea78cf9e7c000000 0xf53c67cf3e000000

def z193 : W := mkw 0x0001002800100a00 0x8000801400080500 0x5d87006802f01b01 0xaec3803401780d80

def z194 : W := mkw 0x01eced00034d6001 0x00f6768001a6b000 0x79ffcc0003fc6001 0x3cffe60001fe3000

def z195 : W := mkw 0x0000000000000000 0x0000000000000000 0x9e00306182039839 0xcf001830c101cc1c

def z196 : W := mkw 0x02f7ff7ff8000000 0x017bffbffc000000 0xfffffffffd8c07c1 0xfffffffffec603e0

def z197 : W := mkw 0x00333a79d0000000 0x00199d3ce8000000 0xfaff3ff9fc000000 0xfd7f9ffcfe000000

def z198 : W := mkw 0x23ffffffffffeb29 0x91fffffffffff594 0xfffffffffffffb39 0xfffffffffffffd9c

def z199 : W := mkw 0x100045822c862162 0x080022c1164310b1 0xe900cf8e1d8e63c1 0x748067c70ec731e0

def z200 : W := mkw 0x0128288003efe001 0x0094144001f7f000 0xb9783c0003ffe001 0x5cbc1e0001fff000

def z201 : W := mkw 0x0008000003001400 0x0004000001800a00 0x0400000003001c01 0x0200000001800e00

def z202 : W := mkw 0x02f6ff5768000000 0x017b7fabb4000000 0xf8ffff9660000000 0x7c7fffcb30000000

def z203 : W := mkw 0x42f7ff7ff8001414 0x217bffbffc000a0a 0xfefffffffc001c3e 0xff7ffffffe000e1f

def z204 : W := mkw 0x804d802c03580a80 0xc026c01601ac0540 0x79ffc00e03fc03c1 0x3cffe00701fe01e0

def z205 : W := mkw 0x501045d36c863576 0x280822e9b6431abb 0xef00cffffd8e7fff 0xf78067fffec73fff

def z206 : W := mkw 0x0055807c00100a00 0x802ac03e00080500 0x7dffc07e02f01b01 0xbeffe03f01780d80

def z207 : W := mkw 0xb05fd7febffebfea 0xd82febff5fff5ff5 0xffffffffffffffff 0xffffffffffffffff

def z208 : W := mkw 0x2002128094a28128 0x100109404a514094 0xdb8733819ef38039 0x6dc399c0cf79c01c

def z209 : W := mkw 0x805c805403481480 0x402e402a01a40a40 0x0078000000000000 0x003c000000000000

def z210 : W := mkw 0x02f7ff7ff8000000 0x017bffbffc000000 0xfefffffffd026427 0xff7ffffffe813213

def z211 : W := mkw 0x805d807c03581e80 0xc02ec03e01ac0f40 0xffffcc7e63fe7fe7 0xffffe63f31ff3ff3

def z212 : W := mkw 0x200100a894b28b28 0x900080544a594594 0x070000699ef39b39 0x83800034cf79cd9c

def z213 : W := mkw 0x300145aabc962b6a 0x9800a2d55e4b15b5 0xef00cffffd8e7fff 0xf78067fffec73fff

def z214 : W := mkw 0x02f7fffffc820120 0x017bfffffe410090 0xfffffffffc820321 0xfffffffffe410190

def z215 : W := mkw 0x02ffff7ffb001400 0x017fffbffd800a00 0xfeffffffff001c01 0xff7fffffff800e00

def z216 : W := mkw 0x0100008000eea001 0x0080004000775000 0x0100000000fc0000 0x00800000007e0000

def z217 : W := mkw 0x0000458000862000 0x000022c000431000 0xef00cf90618e6427 0xf78067c830c73213

def z218 : W := mkw 0x32f7fffffcb6ab6a 0x997bfffffe5b55b5 0xffffffffffffffff 0xffffffffffffffff

def z219 : W := mkw 0x2000008004b28b28 0x9000004002594594 0xcf0003881ef39b39 0xe78001c40f79cd9c

def z220 : W := mkw 0x905dc57e2b5c3ec2 0xc82ee2bf15ae1f61 0x7dffcc7e63fc7fc7 0xbeffe63f31fe3fe3

def z221 : W := mkw 0x51feffd36feff577 0x28ff7fe9b7f7fabb 0xffffffffffffffff 0xffffffffffffffff

def z222 : W := mkw 0x12f7ff7ffc000162 0x097bffbffe0000b1 0xfefffffffc0007e6 0xff7ffffffe0003f3

def z223 : W := mkw 0x81fced54034d7481 0x40fe76aa01a6ba40 0x2078cc16010c64c0 0x103c660b00863260

def z224 : W := mkw 0x300357aabcb6ab6a 0x9801abd55e5b55b5 0x4187c38e1cfc03c0 0x20c3e1c70e7e01e0

def z225 : W := mkw 0x0028280003014000 0x001414000180a000 0x20780c0001006000 0x103c060000803000

def z226 : W := mkw 0x100045822c862162 0x080022c1164310b1 0x87000f807d8e67e7 0x438007c03ec733f3

def z227 : W := mkw 0x01eeff00036de001 0x00f77f8001b6f000 0x30fffc00037de000 0x187ffe0001bef000

def z228 : W := mkw 0x0000000000000000 0x0000000000000000 0x8e00000000020021 0xc700000000010010

def z229 : W := mkw 0xa05f927c93789e88 0xd02fc93e49bc4f44 0x7dfff07f83fd9fd9 0xbefff83fc1fecfec

def z230 : W := mkw 0x02f7ba7dd0000000 0x017bdd3ee8000000 0xbaff3c71e0000000 0xdd7f9e38f0000000

def z231 : W := mkw 0x02f7fffff8a28000 0x017bfffffc514000 0xfbfffffffef38001 0xfdffffffff79c000

def z232 : W := mkw 0x0008000003000000 0x0004000001800000 0x3878000003000001 0x1c3c000001800000

def z233 : W := mkw 0x0055807c00000000 0x002ac03e00000000 0x10ff006000000000 0x087f803000000000

def z234 : W := mkw 0x0001002800100a00 0x8000801400080500 0x1087006002701800 0x0843803001380c00

def z235 : W := mkw 0x805d807c03581e80 0xc02ec03e01ac0f40 0x61ffc01e01fc07c0 0x30ffe00f00fe03e0

def z236 : W := mkw 0x0000000000000000 0x0000000000000000 0xef00cc1e618e67e7 0xf780660f30c733f3

def z237 : W := mkw 0x12a27f83fc862162 0x09513fc1fe4310b1 0x82003f81fc026026 0x41001fc0fe013013

def z238 : W := mkw 0x805c805403481480 0x402e402a01a40a40 0x6d78c01e018c07c1 0xb6bc600f00c603e0

def z239 : W := mkw 0x0018005003001400 0x000c002801800a00 0x1078006002001800 0x083c003001000c00

def z240 : W := mkw 0x30025782bca6a16a 0x18012bc15e5350b5 0xef00ff9ffd8fe7ff 0xf7807fcffec7f3ff

def z241 : W := mkw 0x81fffffc03fffe81 0xc0fffffe01ffff40 0xfdfffffe03ffffc1 0xfeffffff01ffffe0

def z242 : W := mkw 0x202b3aa897b3cb28 0x90159d544bd9e594 0xffff3fe99ff3fb39 0xffff9ff4cff9fd9c

def z243 : W := mkw 0x0000008004820120 0x0000004002410090 0x820003801c020020 0x410001c00e010010

def z244 : W := mkw 0x006ca80003494000 0x0036540001a4a000 0xf9fffc0003ffe001 0x7cfffe0001fff000

def z245 : W := mkw 0x02f4a85540000000 0x017a542aa0000000 0x0078000000000000 0x003c000000000000

def z246 : W := mkw 0x0001002800100a00 0x8000801400080500 0xdf87306982f39b39 0xefc39834c179cd9c

def z247 : W := mkw 0x2211007ffc100b28 0x9108803ffe080594 0x0600007ffc001b38 0x8300003ffe000d9c

def z248 : W := mkw 0x0000000000000000 0x0000000000000000 0x1000306182019818 0x08001830c100cc0c

def z249 : W := mkw 0x03feffd76befe001 0x01ff7febb5f7f000 0xf9ffff9663ffe001 0x7cffffcb31fff000

def z250 : W := mkw 0x4211007ff8001414 0x2108803ffc000a0a 0x0600007ffc001c3e 0x8300003ffe000e1f

def z251 : W := mkw 0x4018005143015414 0x200c0028a180aa0a 0x06000071e303fc3f 0x83000038f181fe1f

def z252 : W := mkw 0x0000000228000000 0x0000000114000000 0x0200001e7c000000 0x8100000f3e000000

def z253 : W := mkw 0x02f7ff7dd0000000 0x017bffbee8000000 0xf8ffffe180000000 0x7c7ffff0c0000000

def z254 : W := mkw 0x11a27f822ca7e163 0x08d13fc11653f0b1 0xef00ff9e7d8fe7e7 0xf7807fcf3ec7f3f3

def z255 : W := mkw 0x4008000003015414 0x200400000180aa0a 0x0000000001006406 0x0000000000803203

def z256 : W := mkw 0x01eeff8003efe001 0x00f77fc001f7f000 0xfdffff9e03ffe7c1 0xfeffffcf01fff3e0

def z257 : W := mkw 0x01eeff8003efe001 0x00f77fc001f7f000 0x90ff3f800273e000 0x487f9fc00139f000

def z258 : W := mkw 0x300357aabcb6ab6a 0x9801abd55e5b55b5 0xdf873fe9fef3fb3f 0xefc39ff4ff79fd9f

def z259 : W := mkw 0x4038285143015414 0x201c1428a180aa0a 0x3c780c7063007c07 0x9e3c063831803e03

def z260 : W := mkw 0x0002128004a28120 0x0001094002514090 0xdf8733881ef38321 0xefc399c40f79c190

def z261 : W := mkw 0x0000008004820120 0x0000004002410090 0xcf0003881c820321 0xe78001c40e410190

def z262 : W := mkw 0x4038285143015414 0x201c1428a180aa0a 0x0078000000000000 0x003c000000000000

def z263 : W := mkw 0x02f7ff7ff8100a00 0x817bffbffc080500 0xfffffffffef01b01 0xffffffffff780d80

def z264 : W := mkw 0xa04792ac94fa8ba8 0xd023c9564a7d45d4 0x4187c38e1cfc03c0 0x20c3e1c70e7e01e0

def z265 : W := mkw 0x02825702b8000000 0x01412b815c000000 0x000003801c000000 0x000001c00e000000

def z266 : W := mkw 0x2003122890308a08 0x9001891448184504 0x9e87306182739839 0xcf439830c139cc1c

def z267 : W := mkw 0x02e6ff03f8000000 0x01737f81fc000000 0xfaffff81fc000000 0x7d7fffc0fe000000

def z268 : W := mkw 0x01c6d78000eea001 0x00e36bc000775000 0xe987cf8001fe6001 0x74c3e7c000ff3000

def z269 : W := mkw 0x4038285143015414 0x201c1428a180aa0a 0x30783c71e301fc1e 0x183c1e38f180fe0f

def z270 : W := mkw 0x0019007803101e00 0x800c803c01880f00 0x7dff007803f01f01 0xbeff803c01f80f80

def z271 : W := mkw 0x221312fffcb28b28 0x9109897ffe594594 0xdf8733fffef39b39 0xefc399ffff79cd9c

def z272 : W := mkw 0x02c4c50628000000 0x0162628314000000 0x0000c00600000000 0x0000600300000000

def z273 : W := mkw 0x02f7ba7dd0000000 0x017bdd3ee8000000 0xdaff33e99c000000 0xed7f99f4ce000000

def z274 : W := mkw 0xa05f92fc97fa9fa8 0xd02fc97e4bfd4fd4 0x7dffc3fe1ffc1fc1 0xbeffe1ff0ffe0fe0

def z275 : W := mkw 0x02b27f53f8000000 0x01593fa9fc000000 0xba783ff1fc000000 0xdd3c1ff8fe000000

def z276 : W := mkw 0x40feff5143015414 0x207f7fa8a180aa0a 0xfefffff1e303fc3f 0xff7ffff8f181fe1f

def z277 : W := mkw 0x60392879d7115f3c 0xb01c943ceb88af9e 0xbe783c79ff03ff3f 0xdf3c1e3cff81ff9f

def z278 : W := mkw 0x100045822c862162 0x080022c1164310b1 0x86000f9e7c0267e6 0xc30007cf3e0133f3

def z279 : W := mkw 0x014c808003efe001 0x00a6404001f7f000 0x79ffc00003ffe001 0x3cffe00001fff000

def z280 : W := mkw 0xa1fffffc97ffffa9 0xd0fffffe4bffffd4 0xffffffff9ffffff9 0xffffffffcffffffc

def z281 : W := mkw 0x01eeba8003ebc001 0x00f75d4001f5e000 0xd9ff338002f38001 0x6cff99c00179c000

def z282 : W := mkw 0x004e928003ea8000 0x0027494001f54000 0xf9fff38003ff8001 0x7cfff9c001ffc000

def z283 : W := mkw 0x4010005140001414 0x20080028a0000a0a 0x0000006180001818 0x00000030c0000c0c

def z284 : W := mkw 0x805dc57e2b581e80 0xc02ee2bf15ac0f40 0xffffcffe7ffc1fc1 0xffffe7ff3ffe0fe0

def z285 : W := mkw 0x22a27f83fca28128 0x11513fc1fe514094 0x82003f81fc038038 0x41001fc0fe01c01c

def z286 : W := mkw 0x0018005003001400 0x000c002801800a00 0xbe780c7063027c27 0xdf3c063831813e13

def z287 : W := mkw 0x905cc5d62fce35e2 0x482e62eb17e71af1 0xef78cf9e7d8e67e7 0xf7bc67cf3ec733f3

def z288 : W := mkw 0x81fded7c035d7e81 0xc0fef6be01aebf40 0x7dffcc7e03fc7fc1 0xbeffe63f01fe3fe0

def z289 : W := mkw 0x0044800000480000 0x0022400000240000 0x4187c00000fc0000 0x20c3e000007e0000

def z290 : W := mkw 0x21a37fa894b7eb29 0x90d1bfd44a5bf594 0xdf873fe99ef3fb39 0xefc39ff4cf79fd9c

def z291 : W := mkw 0x901145fe2c963fe2 0xc808a2ff164b1ff1 0xef00cffe7d8e7fe7 0xf78067ff3ec73ff3

def z292 : W := mkw 0x42ba7f53fb015414 0x215d3fa9fd80aa0a 0xbe783ff1ff03fc3f 0xdf3c1ff8ff81fe1f

def z293 : W := mkw 0x82ffff7ffb481480 0x417fffbffda40a40 0xfafffffffd0c04c0 0xfd7ffffffe860260

def z294 : W := mkw 0x0008000003480000 0x0004000001a40000 0x0100000003fc0001 0x0080000001fe0000

def z295 : W := mkw 0x200100a894920b28 0x900080544a490594 0xcf0003e99c821b39 0xe78001f4ce410d9c

def z296 : W := mkw 0x03f7fffff8eea001 0x01fbfffffc775000 0xfbfffffffcfc0000 0xfdfffffffe7e0000

def z297 : W := mkw 0x02e7ff2eb8000000 0x0173ff975c000000 0xf8ffff8e1c000000 0x7c7fffc70e000000

def z298 : W := mkw 0x8055807c00580a80 0xc02ac03e002c0540 0x79ffc07e00fc03c0 0xbcffe03f007e01e0

def z299 : W := mkw 0x0000000000000000 0x0000000000000000 0xbe003c71e303fc3f 0xdf001e38f181fe1f

def z300 : W := mkw 0x805f92fc03fa9e80 0xc02fc97e01fd4f40 0xfdfff3fe03ff9fc1 0xfefff9ff01ffcfe0

def z301 : W := mkw 0x81c7d7ac00feaa81 0xc0e3ebd6007f5540 0x4187c38e00fc03c0 0x20c3e1c7007e01e0

def z302 : W := mkw 0x300045822cb6ab6a 0x980022c1165b55b5 0xef00cf9e7fffffff 0xf78067cf3fffffff

def z303 : W := mkw 0x0010005000000000 0x0008002800000000 0x3878007000000000 0x9c3c003800000000

def z304 : W := mkw 0x02f7fffff8862000 0x017bfffffc431000 0xfbfffffffd8e6001 0xfdfffffffec73000

def z305 : W := mkw 0x4030285140014014 0x20181428a000a00a 0xba783c71e003e03e 0xdd3c1e38f001f01f

def z306 : W := mkw 0x0000450000000000 0x0000228000000000 0xe800cf8000000000 0x740067c000000000

def z307 : W := mkw 0x0054805400000000 0x002a402a00000000 0x2078c01600000000 0x103c600b00000000

def z308 : W := mkw 0x805d807c03581e80 0xc02ec03e01ac0f40 0x51ffc06e02fc1bc0 0x28ffe037017e0de0

def z309 : W := mkw 0x0000000000000000 0x0000000000000000 0x0600006180001838 0x83000030c0000c1c

def z310 : W := mkw 0xa00b12a897fa9fa8 0xd00589544bfd4fd4 0xdf8733e99fff9ff9 0xefc399f4cfffcffc

def z311 : W := mkw 0x4020280140014014 0x20101400a000a00a 0xae003c11e103e43f 0xd7001e08f081f21f

def z312 : W := mkw 0x8045802c00580a80 0xc022c016002c0540 0x5d87c06e02fc1bc1 0xaec3e037017e0de0

def z313 : W := mkw 0x2001002894100b28 0x900080144a080594 0x9e0030699e039b39 0xcf001834cf01cd9c

def z314 : W := mkw 0x81dfd7fc03febe81 0xc0efebfe01ff5f40 0x7dffc3fe03fc1fc1 0xbeffe1ff01fe0fe0

def z315 : W := mkw 0xa01312fc94b29fa8 0xd009897e4a594fd4 0xdf8733ff9ef39ff9 0xefc399ffcf79cffc

def z316 : W := mkw 0x4028280143014014 0x20141400a180a00a 0xba783c01e303e03f 0x5d3c1e00f181f01f

def z317 : W := mkw 0x0003572ab8000000 0x0001ab955c000000 0xfa87fffffc000000 0xfd43fffffe000000

def z318 : W := mkw 0x4020280140014014 0x20101400a000a00a 0x00000c0060006006 0x0000060030003003

def z319 : W := mkw 0x02f7ff7ff8000000 0x017bffbffc000000 0x50fff3ef9c000000 0x287ff9f7ce000000

def z320 : W := mkw 0x0000000000000000 0x0000000000000000 0xa8000c0001026001 0x5400060000813000

def z321 : W := mkw 0x22f7ff7ffc100b28 0x917bffbffe080594 0xfefffffffc001b38 0xff7ffffffe000d9c

def z322 : W := mkw 0xc05d807d43581e94 0xe02ec03ea1ac0f4a 0x7fffc07fe3fc1fff 0xbfffe03ff1fe0fff

def z323 : W := mkw 0x200312a894b28b28 0x900189544a594594 0x5d8703e81ef01b01 0xaec381f40f780d80

def z324 : W := mkw 0x42a27f03f8014014 0x21513f81fc00a00a 0x82003f81fc03e03e 0x41001fc0fe01f01f

def z325 : W := mkw 0x200312a894b28b28 0x900189544a594594 0xff873ff9fff3ff3f 0xffc39ffcfff9ff9f

def z326 : W := mkw 0x100045822c862162 0x080022c1164310b1 0xff00ffffff8fffff 0xff807fffffc7ffff

def z327 : W := mkw 0x4000000000001414 0x2000000000000a0a 0x0400000000001c3e 0x0200000000000e1f

def z328 : W := mkw 0xc039287d43115e94 0xe01c943ea188af4a 0xbe783c7fe303ffff 0xdf3c1e3ff181ffff

def z329 : W := mkw 0x42fced576b015414 0x217e76abb580aa0a 0xbe78fc77e303fc3f 0xdf3c7e3bf181fe1f

def z330 : W := mkw 0x5008008007877576 0x2804004003c3babb 0x05000000038fffff 0x0280000001c7ffff

def z331 : W := mkw 0x200312a894b28b28 0x900189544a594594 0xff87f3ff9fff9ff9 0xffc3f9ffcfffcffc

def z332 : W := mkw 0x0030285140000000 0x00181428a0000000 0xbe783c71e2039839 0xdf3c1e38f101cc1c

def z333 : W := mkw 0x0000458228862000 0x000022c114431000 0xeb00cf9e7d8e6001 0xf58067cf3ec73000

def z334 : W := mkw 0x2001002890100a08 0x9000801448080504 0x0000006180001818 0x00000030c0000c0c

def z335 : W := mkw 0x21efba289379ca09 0x90f7dd1449bce504 0x10ff306182719818 0x087f9830c138cc0c

def z336 : W := mkw 0x8055807c00581e80 0xc02ac03e002c0f40 0x4587c07e00fc1fc0 0xa2c3e03f007e0fe0

def z337 : W := mkw 0x01eeff822befe001 0x00f77fc115f7f000 0xfbffff9e7fffe001 0xfdffffcf3ffff000

def z338 : W := mkw 0x900845822fde3fe2 0xc80422c117ef1ff1 0xef00cf9e7ffe7fe7 0xf78067cf3fff3ff3

def z339 : W := mkw 0x03fffffdd3efe001 0x01fffffee9f7f000 0xf9ffffe183ffe001 0x7cfffff0c1fff000

def z340 : W := mkw 0x503828d147877576 0x281c1468a3c3babb 0xbf783c71e38fffff 0xdfbc1e38f1c7ffff

def z341 : W := mkw 0x0001002800000000 0x0000801400000000 0x5887006800000000 0xac43803400000000

def z342 : W := mkw 0x0000000000000000 0x0000000000000000 0x8200300180038038 0x41001800c001c01c

def z343 : W := mkw 0x01eca80003494001 0x00f6540001a4a000 0x0078000000000000 0x003c000000000000

def z344 : W := mkw 0x0010005000001400 0x0008002800000a00 0x0400007000001c00 0x8200003800000e00

def z345 : W := mkw 0x62ffffffffb3df3c 0xb17fffffffd9ef9e 0xfffffffffff3ff3f 0xfffffffffff9ff9f

def z346 : W := mkw 0x12a27f83fc862162 0x09513fc1fe4310b1 0xef00ff9ffd8e67e7 0xf7807fcffec733f3

def z347 : W := mkw 0x82ffba7dd3581e80 0xc17fdd3ee9ac0f40 0x10ff306182701800 0x087f9830c1380c00

def z348 : W := mkw 0x002a3a8003a3c000 0x00151d4001d1e000 0xf9ff3f8003f3e001 0x7cff9fc001f9f000

def z349 : W := mkw 0x4020280140014014 0x20101400a000a00a 0x9e003c61e203f83f 0xcf001e30f101fc1f

def z350 : W := mkw 0x03c7d7aeb8eea001 0x01e3ebd75c775000 0x4187c38e1cfc0000 0x20c3e1c70e7e0000

def z351 : W := mkw 0x4030285140001414 0x20181428a0000a0a 0xbe783c71e0001c3e 0xdf3c1e38f0000e1f

def z352 : W := mkw 0x52ffffffff877576 0x297fffffffc3babb 0xffffffffff8fffff 0xffffffffffc7ffff

def z353 : W := mkw 0x8008000003481480 0x4004000001a40a40 0x00000000010c04c0 0x0000000000860260

def z354 : W := mkw 0x0045802c00000000 0x0022c01600000000 0x4087c00e00000000 0x2043e00700000000

def z355 : W := mkw 0x100045822c862162 0x080022c1164310b1 0xeb00cf9e7c8c03c0 0xf58067cf3e4601e0

def z356 : W := mkw 0x00eeff0003480000 0x00777f8001a40000 0xf9ffff8003fc0001 0x7cffffc001fe0000

def z357 : W := mkw 0x6008008007b3df3c 0xb004004003d9ef9e 0x0500000003f3ff3f 0x0280000001f9ff9f

def z358 : W := mkw 0x805d807c03581e80 0xc02ec03e01ac0f40 0x14ff007e02701fc0 0x8a7f803f01380fe0

def z359 : W := mkw 0x22f7bafdd4b28b28 0x917bdd7eea594594 0xdfff33e99ef39b39 0xefff99f4cf79cd9c

def z360 : W := mkw 0x403828d147835534 0x201c1468a3c1aa9a 0xff783ff9ff83ff3f 0xffbc1ffcffc1ff9f

def z361 : W := mkw 0x413828d143eff415 0x209c1468a1f7fa0a 0xbf783c71e3fffc3f 0xdfbc1e38f1fffe1f

def z362 : W := mkw 0x1000008004862162 0x08000040024310b1 0x01000000008c03c0 0x00800000004601e0

def z363 : W := mkw 0x8108008003fffe81 0xc084004001ffff40 0x0500000003ffffc1 0x0280000001ffffe0

def z364 : W := mkw 0x01e6ff8000efe001 0x00f37fc00077f000 0xc187ff8000ffe000 0x60c3ffc0007ff000

def z365 : W := mkw 0x43fffffffbeff415 0x21fffffffdf7fa0a 0xfffffffffffffc3f 0xfffffffffffffe1f

def z366 : W := mkw 0x200312a894b28b28 0x900189544a594594 0xdb8733e99cf00300 0xedc399f4ce780180

def z367 : W := mkw 0x0002120000000000 0x0001090000000000 0xd887338000000000 0x6c4399c000000000

def z368 : W := mkw 0x8011007c00101e80 0xc008803e00080f40 0x0000006000001800 0x0000003000000c00

def z369 : W := mkw 0x01eeff000369c001 0x00f77f8001b4e000 0xf8ffff8002718000 0x7c7fffc00138c000

def z370 : W := mkw 0x100000022c000162 0x08000001160000b1 0x0600001e7c0007e6 0x8300000f3e0003f3

def z371 : W := mkw 0x204f92a897fa8b28 0x9027c9544bfd4594 0xfffff3e99fff9b39 0xfffff9f4cfffcd9c

def z372 : W := mkw 0x4038285143015414 0x201c1428a180aa0a 0x92783c61e203f83e 0x493c1e30f101fc1f

def z373 : W := mkw 0x0008000003014000 0x000400000180a000 0x000000000303e001 0x000000000181f000

def z374 : W := mkw 0x905d807e2f581fe2 0xc82ec03f17ac0ff1 0x7fffc07e7ffc1fe7 0xbfffe03f3ffe0ff3

def z375 : W := mkw 0x11eeff8007efe163 0x08f77fc003f7f0b1 0xfdffff8003ffe7e7 0x7effffc001fff3f3

def z376 : W := mkw 0x2002128094a28128 0x100109404a514094 0x9e0033e19e039839 0xcf0019f0cf01cc1c

def z377 : W := mkw 0x805f927c93581e80 0xc02fc93e49ac0f40 0xfffff3ff9ffc1fc1 0xfffff9ffcffe0fe0

def z378 : W := mkw 0x1000450228042042 0x0800228114021021 0xea00cf9e7d0c64c6 0xf50067cf3e863263

def z379 : W := mkw 0x8055807c00101e80 0xc02ac03e00080f40 0x7cffc07e00001fc0 0xbe7fe03f00000fe0

def z380 : W := mkw 0x03f7fffff8a7e001 0x01fbfffffc53f000 0xfafffffffc03e000 0xfd7ffffffe01f000

def z381 : W := mkw 0x02f7ff7ff8000000 0x017bffbffc000000 0x60ffcf9e7c000000 0x307fe7cf3e000000

def z382 : W := mkw 0x50386dd36f877576 0x281c36e9b7c3babb 0xef78cf9e7d8e67e7 0xf7bc67cf3ec733f3

def z383 : W := mkw 0x603a3ad1d7a3d53c 0x301d1d68ebd1ea9e 0xbe783ff1ff03fc3f 0xdf3c1ff8ff81fe1f

def z384 : W := mkw 0x100045822c862162 0x080022c1164310b1 0xae000f907d026427 0xd70007c83e813213

def z385 : W := mkw 0x00e4ed0000000000 0x0072768000000000 0x2078cc0000000000 0x103c660000000000

def z386 : W := mkw 0x1000450228042042 0x0800228114021021 0x0000c006000c00c0 0x0000600300060060

def z387 : W := mkw 0x0000000000000000 0x0000000000000000 0xca0003881c000000 0xe50001c40e000000

def z388 : W := mkw 0x21eeff8007ffeb29 0x90f77fc003fff594 0xfdffff8003fffb39 0x7effffc001fffd9c

def z389 : W := mkw 0x4038285143015414 0x201c1428a180aa0a 0xff78fc7fe38fffff 0xffbc7e3ff1c7ffff

def z390 : W := mkw 0x2003122894308b28 0x900189144a184594 0x168730699e719b38 0x8b439834cf38cd9c

def z391 : W := mkw 0x01eeff00034d6001 0x00f77f8001a6b000 0xf8ffff80010c6000 0x7c7fffc000863000

def z392 : W := mkw 0x22c7d7aebcb28b28 0x9163ebd75e594594 0xdf87f3ef9ef39b39 0xefc3f9f7cf79cd9c

def z393 : W := mkw 0x600b12a897b3df3c 0xb00589544bd9ef9e 0xdf8733e99ff3ff3f 0xefc399f4cff9ff9f

def z394 : W := mkw 0x01aa7f8003efe001 0x00d53fc001f7f000 0x81003f8003ffe001 0x40801fc001fff000

def z395 : W := mkw 0x0000000000000000 0x0000000000000000 0x0400001e000007c0 0x8200000f000003e0

def z396 : W := mkw 0x81feffd403eff481 0x40ff7fea01f7fa40 0xf9ffff9603ffe4c1 0x7cffffcb01fff260

def z397 : W := mkw 0x100000822c862162 0x08000041164310b1 0x0700001e7d8e67e7 0x8380000f3ec733f3

def z398 : W := mkw 0x0000458000862000 0x000022c000431000 0x80000f8000026000 0x400007c000013000

def z399 : W := mkw 0x0001002800100a00 0x8000801400080500 0x0400006800001b00 0x8200003400000d80

def z400 : W := mkw 0x805d807c03581e80 0xc02ec03e01ac0f40 0x30ffc076037c1cc0 0x187fe03b01be0e60

def z401 : W := mkw 0x31efffaabfffeb6b 0x98f7ffd55ffff5b5 0xffffffffffffffff 0xffffffffffffffff

def z402 : W := mkw 0x004d802803580a00 0x8026c01401ac0500 0x7dffc06803fc1b01 0xbeffe03401fe0d80

def z403 : W := mkw 0x00e6ba0000000000 0x00735d0000000000 0x10ff300000000000 0x087f980000000000

def z404 : W := mkw 0x60223a81d4a3c13c 0x30111d40ea51e09e 0x82003f81fc03e03e 0x41001fc0fe01f01f

def z405 : W := mkw 0x805d807c03581e80 0xc02ec03e01ac0f40 0x5dff006802f01b01 0xaeff803401780d80

def z406 : W := mkw 0x02ffff7ffb014000 0x017fffbffd80a000 0xfaffffffff03e001 0xfd7fffffff81f000

def z407 : W := mkw 0x0002128000a28000 0x0001094000514000 0xdf8733e182f39839 0xefc399f0c179cc1c

def z408 : W := mkw 0x21efffa893ffea09 0x90f7ffd449fff504 0xf9ffffe183fff819 0x7cfffff0c1fffc0c

def z409 : W := mkw 0x82f7ff7ff8580a80 0xc17bffbffc2c0540 0xfbfffffffcfc03c0 0xfdfffffffe7e01e0

def z410 : W := mkw 0x0000008000820000 0x0000004000410000 0xc900038000820001 0x648001c000410000

def z411 : W := mkw 0x4008000003015414 0x200400000180aa0a 0x0000000002019818 0x000000000100cc0c

def z412 : W := mkw 0x12c7d7aebc862162 0x0963ebd75e4310b1 0xef87cf9e7d8e67e7 0xf7c3e7cf3ec733f3

def z413 : W := mkw 0x22f7ff7ff8308a08 0x917bffbffc184504 0xfafffffffe719818 0xfd7fffffff38cc0c

def z414 : W := mkw 0x01eeff8003efe001 0x00f77fc001f7f000 0x51fff38002fd8000 0x28fff9c0017ec000

def z415 : W := mkw 0x1000458004862162 0x080022c0024310b1 0xed00cf80018e67e7 0x768067c000c733f3

def z416 : W := mkw 0x8010005400001480 0x4008002a00000a40 0x00000016000004c0 0x0000000b00000260

def z417 : W := mkw 0x00f7ff7c00000000 0x007bffbe00000000 0xf8fffffe00000000 0xfc7fffff00000000

def z418 : W := mkw 0x503828536f015576 0x281c1429b780aabb 0xbe783c7fff03ffff 0xdf3c1e3fff81ffff

def z419 : W := mkw 0x02ffff7ffb480000 0x017fffbffda40000 0xfbfffffffffc0001 0xfdfffffffffe0000

def z420 : W := mkw 0x01eeff8003efe001 0x00f77fc001f7f000 0xffffffe183fff839 0xfffffff0c1fffc1c

def z421 : W := mkw 0x10e6ff822c862162 0x08737fc1164310b1 0xffffff9e7d8e67e7 0xffffffcf3ec733f3

def z422 : W := mkw 0x21eeff8097efe129 0x10f77fc04bf7f094 0xfbffff819fffe039 0x7dffffc0cffff01c

def z423 : W := mkw 0x9045c5ae2cde2be2 0xc822e2d7166f15f1 0xef87cf9e7dfe67e7 0xf7c3e7cf3eff33f3

def z424 : W := mkw 0x805dc5fc03de3e80 0xc02ee2fe01ef1f40 0xfdffcffe03fe7fc1 0xfeffe7ff01ff3fe0

def z425 : W := mkw 0x4038285143015414 0x201c1428a180aa0a 0xba783c71e2019818 0xdd3c1e38f100cc0c

def z426 : W := mkw 0x100045822c862162 0x080022c1164310b1 0xcf00c38e1c8e03e1 0xe78061c70e4701f0

def z427 : W := mkw 0x200312a894b28b28 0x900189544a594594 0x478703e99cf01b38 0xa3c381f4ce780d9c

def z428 : W := mkw 0x01eeff8003efe001 0x00f77fc001f7f000 0xffffff9063ffe427 0xffffffc831fff213

def z429 : W := mkw 0x0057927c90000000 0x002bc93e48000000 0xfafff3ff9c000000 0xfd7ff9ffce000000

def z430 : W := mkw 0x110845822fefe163 0x088422c117f7f0b1 0xef00cf9e7fffe7e7 0xf78067cf3ffff3f3

def z431 : W := mkw 0x01eced8003cf6001 0x00f676c001e7b000 0xe978cf80018e6001 0x74bc67c000c73000

def z432 : W := mkw 0x60110079d4101f3c 0xb008803cea080f9e 0x06000079fc001f3e 0x8300003cfe000f9f

def z433 : W := mkw 0x41feba514369d415 0x20ff5d28a1b4ea0a 0xbeff3c71e373fc3f 0xdf7f9e38f1b9fe1f

def z434 : W := mkw 0x02f6ff57f8000000 0x017b7fabfc000000 0xa278ff97fc000000 0x513c7fcbfe000000

def z435 : W := mkw 0x22a37fabfcb28b28 0x9151bfd5fe594594 0xdf873fe9fef39b39 0xefc39ff4ff79cd9c

def z436 : W := mkw 0xc008000003595e94 0xe004000001acaf4a 0x0500000003ffffff 0x0280000001ffffff

def z437 : W := mkw 0x01eeff8007efe121 0x00f77fc003f7f090 0xffffff881fffe321 0xffffffc40ffff190

def z438 : W := mkw 0x300312a894b6ab6a 0x980189544a5b55b5 0xdf8733e99fffffff 0xefc399f4cfffffff

def z439 : W := mkw 0x805d807c03581e80 0xc02ec03e01ac0f40 0x79ffc06003fc1801 0x3cffe03001fe0c00

def z440 : W := mkw 0x0020280140000000 0x00101400a0000000 0x82003c01e0000000 0x41001e00f0000000

def z441 : W := mkw 0x0000000000000000 0x0000000000000000 0x2c00001001000401 0x9600000800800200

def z442 : W := mkw 0x100045822c862162 0x080022c1164310b1 0xa200cf967d0e64e6 0x510067cb3e873273

def z443 : W := mkw 0x4039287943115e14 0xa01c943ca188af0a 0xffff3c79e3f3ff3f 0xffff9e3cf1f9ff9f

def z444 : W := mkw 0x000312a800b28a00 0x8001895400594500 0xdd8733e802f39b01 0xeec399f40179cd80

def z445 : W := mkw 0x0055807c00000000 0x002ac03e00000000 0x7dffc07e018c07c1 0xbeffe03f00c603e0

def z446 : W := mkw 0x0001002800100a00 0x8000801400080500 0x7d87c07e03fc1fc1 0xbec3e03f01fe0fe0

def z447 : W := mkw 0x807da87c03595e80 0xc03ed43e01acaf40 0xfdfffc7e03ffffc1 0xfefffe3f01ffffe0

def z448 : W := mkw 0x0255807ff8000000 0x012ac03ffc000000 0x7affc07ffc000000 0xbd7fe03ffe000000

def z449 : W := mkw 0x4038285143015414 0x201c1428a180aa0a 0xba783c71e1006406 0xdd3c1e38f0803203

def z450 : W := mkw 0x82fced576b481480 0x417e76abb5a40a40 0x2078cc16610c04c0 0x103c660b30860260

def z451 : W := mkw 0x0018005003001400 0x000c002801800a00 0x7d78c07e038c1fc1 0xbebc603f01c60fe0

def z452 : W := mkw 0x8001002c00100a80 0xc000801600080540 0x0000000e000003c0 0x00000007000001e0

def z453 : W := mkw 0x4030285140015414 0x20181428a000aa0a 0x86003c71e003fc3e 0xc3001e38f001fe1f

def z454 : W := mkw 0x0000008004820120 0x0000004002410090 0xef00c39e1d8e07e1 0xf78061cf0ec703f0

def z455 : W := mkw 0x4010005140001414 0x20080028a0000a0a 0xae000c71e1027c3f 0xd7000638f0813e1f

def z456 : W := mkw 0x0000000004000120 0x0000000002000090 0x060000081c000320 0x830000040e000190

def z457 : W := mkw 0x4010005140001414 0x20080028a0000a0a 0x9e003071e2039c3f 0xcf001838f101ce1f

def z458 : W := mkw 0x100000022c000162 0x08000001160000b1 0x020000007c000026 0x010000003e000013

def z459 : W := mkw 0x00f6ff5140000000 0x007b7fa8a0000000 0xfafffff1e0000000 0xfd7ffff8f0000000

def z460 : W := mkw 0x601312f9d4b29f3c 0xb009897cea594f9e 0xdf8733f9fef39f3f 0xefc399fcff79cf9f

def z461 : W := mkw 0x0038285003015400 0x001c14280180aa00 0xbc783c700303fc01 0xde3c1e380181fe00

def z462 : W := mkw 0x2000008004a28128 0x1000004002514094 0x0000000000038038 0x000000000001c01c

def z463 : W := mkw 0x100000022c000162 0x08000001160000b1 0x0000000e1c0003c0 0x000000070e0001e0

def z464 : W := mkw 0x100357aabc862162 0x0801abd55e4310b1 0xff87fffffd8e67e7 0xffc3fffffec733f3

def z465 : W := mkw 0xc2ffff7ffb595e94 0xe17fffbffdacaf4a 0xffffffffffffffff 0xffffffffffffffff

def z466 : W := mkw 0x12f7fffffc862162 0x097bfffffe4310b1 0xfbfffffffc8c03c0 0xfdfffffffe4601e0

def z467 : W := mkw 0x50386dd36f877576 0x281c36e9b7c3babb 0xbe783ff1ff03fc3f 0xdf3c1ff8ff81fe1f

def z468 : W := mkw 0x11a27f822ca7e163 0x08d13fc11653f0b1 0x82003f807c03e026 0x41001fc03e01f013

def z469 : W := mkw 0x0028280003014000 0x001414000180a000 0xbe783c618303f839 0xdf3c1e30c181fc1c

def z470 : W := mkw 0x004c800003480000 0x0026400001a40000 0x2078c000010c0000 0x103c600000860000

def z471 : W := mkw 0x2000008004b28b28 0x9000004002594594 0x0100000000f00300 0x0080000000780180

def z472 : W := mkw 0x2002120090208008 0x1001090048104004 0x0000300180018018 0x00001800c000c00c

def z473 : W := mkw 0x22f7fffffca28128 0x117bfffffe514094 0xfafffffffc038038 0xfd7ffffffe01c01c

def z474 : W := mkw 0x100045022c000162 0x08002281160000b1 0xee00cf9e7c0007e6 0xf70067cf3e0003f3

def z475 : W := mkw 0x10306dd36c862162 0x081836e9b64310b1 0xff78fffffd8e67e7 0xffbc7ffffec733f3

def z476 : W := mkw 0x603b3a79d331de1c 0xb01d9d3ce998ef0e 0xbeff3c71e373fc3f 0xdf7f9e38f1b9fe1f

def z477 : W := mkw 0x03a27f83f8a7e001 0x01d13fc1fc53f000 0x82003f81fc03e000 0x41001fc0fe01f000

def z478 : W := mkw 0x0201002eb8000000 0x010080175c000000 0x0000000e1c000000 0x000000070e000000

def z479 : W := mkw 0x0003122890100a00 0x8001891448080500 0xdf8733e99ef01b01 0xefc399f4cf780d80

def z480 : W := mkw 0x0100008000a7e001 0x008000400053f000 0x000000000003e000 0x000000000001f000

def z481 : W := mkw 0x805c805403481480 0x402e402a01a40a40 0x79ffc01603fc04c1 0x3cffe00b01fe0260

def z482 : W := mkw 0x02c7d72eb8000000 0x0163eb975c000000 0xda87f3ef9c000000 0xed43f9f7ce000000

def z483 : W := mkw 0x815d80fc03fffe81 0xc0aec07e01ffff40 0x7dffc07e03ffffc1 0xbeffe03f01ffffe0

def z484 : W := mkw 0x21c7d7a894feab29 0x90e3ebd44a7f5594 0xdf87f3e99eff9b39 0xefc3f9f4cf7fcd9c

def z485 : W := mkw 0x805d807c03581e80 0xc02ec03e01ac0f40 0x3cff007003701c01 0x9e7f803801b80e00

def z486 : W := mkw 0xa05f927c93789e88 0xd02fc93e49bc4f44 0x10ff306182719818 0x087f9830c138cc0c

def z487 : W := mkw 0x100045822c862162 0x080022c1164310b1 0x6100cf9e7d8c67c6 0x308067cf3ec633e3

def z488 : W := mkw 0x4038285143015414 0x201c1428a180aa0a 0xb8783c618303f819 0x5c3c1e30c181fc0c

def z489 : W := mkw 0x00e6ff8000862000 0x00737fc000431000 0xf9ffff80018e6001 0x7cffffc000c73000

def z490 : W := mkw 0x0000008004820120 0x0000004002410090 0x0500000000820321 0x0280000000410190

def z491 : W := mkw 0x01a06d0000056001 0x00d036800002b000 0x00000c0000006000 0x0000060000003000

def z492 : W := mkw 0x1000458228862042 0x080022c114431021 0xe900cf96618e64c7 0x748067cb30c73263

def z493 : W := mkw 0x100000022c000162 0x08000001160000b1 0x6f00c01e7d8c07e7 0xb780600f3ec603f3

def z494 : W := mkw 0x50206d836c876176 0x281036c1b643b0bb 0x82003f81fc03e03e 0x41001fc0fe01f01f

def z495 : W := mkw 0x01ced78003efe001 0x00e76bc001f7f000 0x4187c38003ffe001 0x20c3e1c001fff000

def z496 : W := mkw 0x02e7ff2ff8000000 0x0173ff97fc000000 0xc287ff8ffc000000 0x6143ffc7fe000000

def z497 : W := mkw 0x41ba7fd143a7f415 0x20dd3fe8a1d3fa0a 0xbe783ff1e303fc3f 0xdf3c1ff8f181fe1f

def z498 : W := mkw 0x200312a894b28b28 0x900189544a594594 0x1587306182f39b39 0x0ac39830c179cd9c

def z499 : W := mkw 0x4038285143015414 0x201c1428a180aa0a 0x24780c106303fc3f 0x123c06083181fe1f

def z500 : W := mkw 0xa2fffffffffa9fa8 0xd17ffffffffd4fd4 0xffffffffffff9ff9 0xffffffffffffcffc

def z501 : W := mkw 0x01e6ff8000eea001 0x00f37fc000775000 0xf9ffff8000fc0000 0x7cffffc0007e0000

def z502 : W := mkw 0x2002128004b28b28 0x9001094002594594 0xdd87338002f39b39 0x6ec399c00179cd9c

def z503 : W := mkw 0xa05d807c97581fa8 0xd02ec03e4bac0fd4 0x7fffc07f9ffc1ff9 0xbfffe03fcffe0ffc

def z504 : W := mkw 0x0000000000000000 0x0000000000000000 0x5987000002f00001 0x2cc3800001780000

def z505 : W := mkw 0x2003122894100b28 0x900189144a080594 0xde8733e99c001b38 0xef4399f4ce000d9c

def z506 : W := mkw 0x03ffff7ffb69c001 0x01ffffbffdb4e000 0xfafffffffe718000 0xfd7fffffff38c000

def z507 : W := mkw 0x104cc5822fce2162 0x082662c117e710b1 0xffffcf9e7ffe67e7 0xffffe7cf3fff33f3

def z508 : W := mkw 0x8009002803581e80 0xc004801401ac0f40 0x5d87006803fc1fc1 0xaec3803401fe0fe0

def z509 : W := mkw 0x8045802c00580a80 0xc022c016002c0540 0x0087000000700000 0x0043800000380000

def z510 : W := mkw 0x005c805003481400 0x002e402801a40a00 0x7dffc07003fc1c01 0xbeffe03801fe0e00

def z511 : W := mkw 0x50206d836c876176 0x281036c1b643b0bb 0xef00ff9ffd8fe7ff 0xf7807fcffec7f3ff

def z512 : W := mkw 0x100045822c862162 0x080022c1164310b1 0xea00cf9e7c026026 0xf50067cf3e013013

def z513 : W := mkw 0x4038285143015414 0x201c1428a180aa0a 0x3c78307183019c19 0x9e3c1838c180ce0c

def z514 : W := mkw 0x0000000000000000 0x0000000000000000 0x0400000002039839 0x020000000101cc1c

def z515 : W := mkw 0x407da87d43015414 0x203ed43ea180aa0a 0xfefffc7fe303fc3f 0xff7ffe3ff181fe1f

def z516 : W := mkw 0x805d807c03581e80 0xc02ec03e01ac0f40 0xfffff07f83ff9ff9 0xfffff83fc1ffcffc

def z517 : W := mkw 0x1000008004862162 0x08000040024310b1 0x0000000000026026 0x0000000000013013

def z518 : W := mkw 0x200312a894a28128 0x100189544a514094 0xda8733e99c038038 0xed4399f4ce01c01c

def z519 : W := mkw 0x2003122890308a08 0x9001891448184504 0x0087000000700000 0x0043800000380000

def z520 : W := mkw 0x4028280003015414 0x201414000180aa0a 0xbc783c000303fc3f 0x5e3c1e000181fe1f

def z521 : W := mkw 0x0000458004862120 0x000022c002431090 0xef00cf881d8e6321 0xf78067c40ec73190

def z522 : W := mkw 0x41a27f8140a7e015 0x20d13fc0a053f00a 0x82003f81e003e03e 0x41001fc0f001f01f

def z523 : W := mkw 0xd07dedff6fdf7ff6 0xe83ef6ffb7efbffb 0xffffffffffffffff 0xffffffffffffffff

def z524 : W := mkw 0x100045822c862162 0x080022c1164310b1 0x6d00c39e1d8c07c1 0xb68061cf0ec603e0

def z525 : W := mkw 0x8011007c00101e80 0xc008803e00080f40 0x6d00c07e018c1fc1 0xb680603f00c60fe0

def z526 : W := mkw 0x22c7d7aebcb28b28 0x9163ebd75e594594 0x4187c38e1cf00300 0x20c3e1c70e780180

def z527 : W := mkw 0x8045802c00580a80 0xc022c016002c0540 0x6d87c01e01fc07c1 0xb6c3e00f00fe03e0

def z528 : W := mkw 0x0018005003001400 0x000c002801800a00 0x2078001001000400 0x103c000800800200

def z529 : W := mkw 0x41eeff8143efe015 0x20f77fc0a1f7f00a 0xfbffff81e3ffe03f 0x7dffffc0f1fff01f

def z530 : W := mkw 0x210b12a897ffeb29 0x908589544bfff594 0xdf8733e99ffffb39 0xefc399f4cffffd9c

def z531 : W := mkw 0x0002128000a28000 0x0001094000514000 0x8000338000038000 0x400019c00001c000

def z532 : W := mkw 0x0000000000100a00 0x8000000000080500 0x0500000002f01b01 0x0280000001780d80

def z533 : W := mkw 0x403a3ad143a3d414 0x201d1d68a1d1ea0a 0xffff3ff1e3f3fc3f 0xffff9ff8f1f9fe1f

def z534 : W := mkw 0x407ca85143495414 0x203e5428a1a4aa0a 0xfffffc71e3fffc3f 0xfffffe38f1fffe1f

def z535 : W := mkw 0x205792fc94b28b28 0x902bc97e4a594594 0xfffff3ff9ef39b39 0xfffff9ffcf79cd9c

def z536 : W := mkw 0x02c7d72eb8000000 0x0163eb975c000000 0xea87cf9e7c000000 0xf543e7cf3e000000

def z537 : W := mkw 0x603b3a79d331de1c 0xb01d9d3ce998ef0e 0x10ff306182719818 0x087f9830c138cc0c

def z538 : W := mkw 0xc07da87d43595e94 0xe03ed43ea1acaf4a 0x7dfff07f83fd9fd9 0xbefff83fc1fecfec

def z539 : W := mkw 0x02f4ed5768000000 0x017a76abb4000000 0xba78fc77e0000000 0xdd3c7e3bf0000000

def z540 : W := mkw 0x0210005768000000 0x0108002bb4000000 0x0000001660000000 0x0000000b30000000

def z541 : W := mkw 0x02000003f8000000 0x01000001fc000000 0x02000001fc000000 0x01000000fe000000

def z542 : W := mkw 0x2001002894100b28 0x900080144a080594 0x5f8700699ef01b39 0xafc38034cf780d9c

def z543 : W := mkw 0x0211007dd0000000 0x0108803ee8000000 0x0000006180000000 0x00000030c0000000

def z544 : W := mkw 0x1000000000042042 0x0800000000021021 0x00000000010c64c6 0x0000000000863263

def z545 : W := mkw 0x3000008004b6ab6a 0x98000040025b55b5 0x0500000003ffffff 0x0280000001ffffff

def z546 : W := mkw 0x201b12f897b29f28 0x900d897c4bd94f94 0xffff33f99ff39f39 0xffff99fccff9cf9c

def z547 : W := mkw 0x83fffffffbfffe81 0xc1fffffffdffff40 0xffffffffffffffc1 0xffffffffffffffe0

def z548 : W := mkw 0x1000008004862162 0x08000040024310b1 0x6d00c01e018e67e7 0xb680600f00c733f3

def z549 : W := mkw 0x01eeff8003efe001 0x00f77fc001f7f000 0xa078ff80010fe000 0x503c7fc00087f000

def z550 : W := mkw 0x0000000000000000 0x0000000000000000 0x0400000001026427 0x0200000000813213

def z551 : W := mkw 0x100145aa2c962b62 0x8800a2d5164b15b1 0xff87cffe7ffe7fe7 0xffc3e7ff3fff3ff3

def z552 : W := mkw 0x2000000000308a08 0x9000000000184504 0x0000000002719818 0x000000000138cc0c

def z553 : W := mkw 0x8000000000580a80 0xc0000000002c0540 0x0100000000fc03c0 0x00800000007e01e0

def z554 : W := mkw 0x0020280000000000 0x0010140000000000 0xb8783c0000000000 0x5c3c1e0000000000

def z555 : W := mkw 0x8019007c03581e80 0xc00c803e01ac0f40 0x0500007e03fc1fc1 0x8280003f01fe0fe0

def z556 : W := mkw 0x2001002894100b28 0x900080144a080594 0x000000081c000300 0x000000040e000180

def z557 : W := mkw 0x41feba514369d415 0x20ff5d28a1b4ea0a 0x10ff306182719818 0x087f9830c138cc0c

def z558 : W := mkw 0x0231287ff8000000 0x0118943ffc000000 0xba783c7ffc000000 0xdd3c1e3ffe000000

def z559 : W := mkw 0x010800000369c001 0x0084000001b4e000 0x0000000002718000 0x000000000138c000

def z560 : W := mkw 0x0000000000000000 0x0000000000000000 0x6800c01e00000000 0xb400600f00000000

def z561 : W := mkw 0x60233aa9d4b3cb3c 0xb0119d54ea59e59e 0xdf873fe9fef3fb3f 0xefc39ff4ff79fd9f

def z562 : W := mkw 0x4038285143015414 0x201c1428a180aa0a 0x16783071e2019c3e 0x8b3c1838f100ce1f

def z563 : W := mkw 0x8008000003581e80 0xc004000001ac0f40 0x0000000002701800 0x0000000001380c00

def z564 : W := mkw 0x805d807c03481480 0x402ec03e01a40a40 0x78ffc07e010c04c0 0xbc7fe03f00860260

def z565 : W := mkw 0x92ffffffffde3fe2 0xc97fffffffef1ff1 0xfffffffffffe7fe7 0xffffffffffff3ff3

def z566 : W := mkw 0x2002128094b28b28 0x900109404a594594 0x870033819ef39b39 0x438019c0cf79cd9c

def z567 : W := mkw 0x01feffd003eff401 0x00ff7fe801f7fa00 0xfdfffff003fffc01 0xfefffff801fffe00

def z568 : W := mkw 0x100045822c862162 0x080022c1164310b1 0x4500c38e1d8e67e7 0x228061c70ec733f3

def z569 : W := mkw 0xc05d807c03595e94 0xe02ec03e01acaf4a 0x7dffc07e03ffffff 0xbeffe03f01ffffff

def z570 : W := mkw 0x03ffba7dd369c001 0x01ffdd3ee9b4e000 0x10ff306182718000 0x087f9830c138c000

def z571 : W := mkw 0x0211457ff8000000 0x0108a2bffc000000 0xea00cffffc000000 0xf50067fffe000000

def z572 : W := mkw 0x8000000000101e80 0xc000000000080f40 0x0400000000001fc0 0x0200000000000fe0

def z573 : W := mkw 0x500845822f877576 0x280422c117c3babb 0xef00cf9e7f8fffff 0xf78067cf3fc7ffff

def z574 : W := mkw 0x0000000000000000 0x0000000000000000 0x05000000018c07c1 0x0280000000c603e0

def z575 : W := mkw 0x0018005003001400 0x000c002801800a00 0xbe78307183039c39 0xdf3c1838c181ce1c

def z576 : W := mkw 0x81ffba7c0379de81 0xc0ffdd3e01bcef40 0x10ff306002719800 0x087f98300138cc00

def z577 : W := mkw 0x41fced51434d7415 0x20fe76a8a1a6ba0a 0xbe78fc71e30ffc3f 0xdf3c7e38f187fe1f

def z578 : W := mkw 0x01efffa893efe001 0x00f7ffd449f7f000 0xfbffffe99fffe001 0xfdfffff4cffff000

def z579 : W := mkw 0x01fffffc03efe001 0x00fffffe01f7f000 0xf9fffffe03ffe001 0xfcffffff01fff000

def z580 : W := mkw 0x82ffba7dd3581e80 0xc17fdd3ee9ac0f40 0x7dfff07f83fc1fc1 0xbefff83fc1fe0fe0

def z581 : W := mkw 0x8008000003581e80 0xc004000001ac0f40 0x6d00c01e03fc1fc1 0xb680600f01fe0fe0

def z582 : W := mkw 0x01a27f8000a7e001 0x00d13fc00053f000 0xd9873f8002f3e001 0x6cc39fc00179f000

def z583 : W := mkw 0x01080000034d6001 0x0084000001a6b000 0x00000000010c6000 0x0000000000863000

def z584 : W := mkw 0x0000458000862000 0x000022c000431000 0xed00cf9e018e67c1 0xf68067cf00c733e0

def z585 : W := mkw 0x0003122890000000 0x0001891448000000 0x408703881c000000 0x204381c40e000000

def z586 : W := mkw 0x12f4edd76c862162 0x097a76ebb64310b1 0xef78cf9e7d8e67e7 0xf7bc67cf3ec733f3

def z587 : W := mkw 0xa05f92fc97fa9fa8 0xd02fc97e4bfd4fd4 0xdfff33e99ef39b39 0xefff99f4cf79cd9c

def z588 : W := mkw 0x0002120000208000 0x0001090000104000 0x1087300002718000 0x084398000138c000

def z589 : W := mkw 0x0000450000042000 0x0000228000021000 0x2000cc00010c6000 0x1000660000863000

def z590 : W := mkw 0x61fffff9d7ffff3d 0xb0fffffcebffff9e 0xfffffff9ffffff3f 0xfffffffcffffff9f

def z591 : W := mkw 0x0000000000000000 0x0000000000000000 0xaa000c1060000000 0xd500060830000000

def z592 : W := mkw 0x20333af9d4b28b28 0x90199d7cea594594 0xffff3ff9fef39b39 0xffff9ffcff79cd9c

def z593 : W := mkw 0x1000008004862162 0x08000040024310b1 0xcf0003881d8e67e7 0xe78001c40ec733f3

def z594 : W := mkw 0x8011007c00101e80 0xc008803e00080f40 0x5d87007e02f01fc1 0xaec3803f01780fe0

def z595 : W := mkw 0x8019007c03101e80 0xc00c803e01880f40 0x3c78007e03001fc1 0x9e3c003f01800fe0

def z596 : W := mkw 0xa05d80fc07fa9fa8 0xd02ec07e03fd4fd4 0x7dffc07e03ff9ff9 0xbeffe03f01ffcffc

def z597 : W := mkw 0x30025782bca6a16a 0x18012bc15e5350b5 0x82003f81fc03e03e 0x41001fc0fe01f01f

def z598 : W := mkw 0x4010005140001414 0x20080028a0000a0a 0x0000001060000406 0x0000000830000203

def z599 : W := mkw 0x000312a894820120 0x000189544a410090 0xdf8733e99c820321 0xefc399f4ce410190

def z600 : W := mkw 0x41feffd143eff415 0x20ff7fe8a1f7fa0a 0xf9ffff9063ffe407 0x7cffffc831fff203

def z601 : W := mkw 0x21efbaa897fbcb29 0x90f7dd544bfde594 0xdfff33e99ef39b39 0xefff99f4cf79cd9c

def z602 : W := mkw 0x200312a894b28b28 0x900189544a594594 0xd98733881ef38301 0x6cc399c40f79c180

def z603 : W := mkw 0x0000000000000000 0x0000000000000000 0x4d00000800800301 0xa680000400400180

def z604 : W := mkw 0x40386dd143877414 0x201c36e8a1c3ba0a 0xff78fff1e38ffc3f 0xffbc7ff8f1c7fe1f

def z605 : W := mkw 0x2002128094a28128 0x100109404a514094 0x000003801c000000 0x000001c00e000000

def z606 : W := mkw 0x2000000004100b28 0x9000000002080594 0x0400000000001b38 0x0200000000000d9c

def z607 : W := mkw 0x0000008004820120 0x0000004002410090 0x410003881c800300 0x208001c40e400180

def z608 : W := mkw 0x03ffff7ffb4d6001 0x01ffffbffda6b000 0xfafffffffd0c6000 0xfd7ffffffe863000

def z609 : W := mkw 0x21c7d7a894feab29 0x90e3ebd44a7f5594 0x4187c3881cfc0300 0x20c3e1c40e7e0180

def z610 : W := mkw 0x0108458003efe001 0x008422c001f7f000 0xe900cf8003ffe001 0x748067c001fff000

def z611 : W := mkw 0x121145fffc862162 0x0908a2fffe4310b1 0xef00cffffd8e67e7 0xf78067fffec733f3

def z612 : W := mkw 0x4038285143015414 0x201c1428a180aa0a 0x26780c71e1007c3e 0x933c0638f0803e1f

def z613 : W := mkw 0x0000450228000000 0x0000228114000000 0x4000c38e1c000000 0x200061c70e000000

def z614 : W := mkw 0x4038285143015414 0x201c1428a180aa0a 0x147830618303fc3f 0x0a3c1830c181fe1f

def z615 : W := mkw 0x81efffac03ffea81 0xc0f7ffd601fff540 0xf9ffff8e03ffe3c1 0x7cffffc701fff1e0

def z616 : W := mkw 0x0003122890000000 0x0001891448000000 0xde8733e99e039839 0xef4399f4cf01cc1c

def z617 : W := mkw 0x4008000003015414 0x200400000180aa0a 0xae000c106303fc3f 0xd70006083181fe1f

def z618 : W := mkw 0x41feffd143eff415 0x20ff7fe8a1f7fa0a 0xf9ffffe183fff819 0x7cfffff0c1fffc0c

def z619 : W := mkw 0x0000000000000000 0x0000000000000000 0x9a00306180000000 0xcd001830c0000000

def z620 : W := mkw 0x02c7922c90000000 0x0163c91648000000 0x0087000000000000 0x0043800000000000

def z621 : W := mkw 0x01feffd143efe001 0x00ff7fe8a1f7f000 0xfbfffff1e3ffe001 0xfdfffff8f1fff000

def z622 : W := mkw 0x41fced51434d7415 0x20fe76a8a1a6ba0a 0x2078cc10610c6406 0x103c660830863203

def z623 : W := mkw 0x300357aabcb6ab6a 0x9801abd55e5b55b5 0xef87cf9e7dfe67e7 0xf7c3e7cf3eff33f3

def z624 : W := mkw 0x1000000004000162 0x08000000020000b1 0x04000000000007e6 0x02000000000003f3

def z625 : W := mkw 0x805d807c03581e80 0xc02ec03e01ac0f40 0x15ff006003fc1fc1 0x0aff803001fe0fe0

def z626 : W := mkw 0x22f7ba7dd0308a08 0x917bdd3ee8184504 0x10ff306182719818 0x087f9830c138cc0c

def z627 : W := mkw 0xc07da87d43595e94 0xe03ed43ea1acaf4a 0xbeff3c71e373fc3f 0xdf7f9e38f1b9fe1f

def z628 : W := mkw 0x005d807c03480000 0x002ec03e01a40000 0x79ffc07e03fc0001 0xbcffe03f01fe0000

def z629 : W := mkw 0x0000008004820120 0x0000004002410090 0xef000f987d826727 0xf78007cc3ec13393

def z630 : W := mkw 0x403b3a79d3015414 0x201d9d3ce980aa0a 0xfeff3ff9ff03fc3f 0xff7f9ffcff81fe1f

def z631 : W := mkw 0x82c7d72eb8580a80 0xc163eb975c2c0540 0x4187c38e1cfc03c0 0x20c3e1c70e7e01e0

def z632 : W := mkw 0x100045822c862162 0x080022c1164310b1 0x000003801c000000 0x000001c00e000000

def z633 : W := mkw 0x0000008004820120 0x0000004002410090 0xdf0033e99e839b39 0xef8019f4cf41cd9c

def z634 : W := mkw 0x0000008000a28000 0x0000004000514000 0x0100000002f38001 0x008000000179c000

def z635 : W := mkw 0x905d80fc07de3fe2 0xc82ec07e03ef1ff1 0x7dffc07e03fe7fe7 0xbeffe03f01ff3ff3

def z636 : W := mkw 0x82dfd77ebb581e80 0xc16febbf5dac0f40 0x7dffc3fe1ffc1fc1 0xbeffe1ff0ffe0fe0

def z637 : W := mkw 0x4038285143015414 0x201c1428a180aa0a 0xae780c1061026427 0xd73c060830813213

def z638 : W := mkw 0xc07ca85543495494 0x603e542aa1a4aa4a 0xbe78fc77e30ffcff 0xdf3c7e3bf187fe7f

def z639 : W := mkw 0x82fded7f6b581e80 0xc17ef6bfb5ac0f40 0x7dffcc7e63fc1fc1 0xbeffe63f31fe0fe0

def z640 : W := mkw 0x010a128003efe001 0x0085094001f7f000 0xd987338003ffe001 0x6cc399c001fff000

def z641 : W := mkw 0x02f5ed7ff8000000 0x017af6bffc000000 0x2278cc7ffc000000 0x913c663ffe000000

def z642 : W := mkw 0x11eced822fcf6163 0x08f676c117e7b0b1 0xef78cf9e7d8e67e7 0xf7bc67cf3ec733f3

def z643 : W := mkw 0x0003122890000000 0x0001891448000000 0x1087306180000000 0x08439830c0000000

def z644 : W := mkw 0x100045822c862162 0x080022c1164310b1 0x2500cc16618e67e7 0x1280660b30c733f3

def z645 : W := mkw 0x4038285143015414 0x201c1428a180aa0a 0xa2783c11e103e43e 0x513c1e08f081f21f

def z646 : W := mkw 0x02d7d77ff8000000 0x016bebbffc000000 0x4287c3fffc000000 0xa143e1fffe000000

def z647 : W := mkw 0x100045822c862162 0x080022c1164310b1 0x4700c39e7c8c07e6 0xa38061cf3e4603f3

def z648 : W := mkw 0x200312a894b28b28 0x900189544a594594 0x458703881ef39b39 0x22c381c40f79cd9c

def z649 : W := mkw 0x0002578000a6a000 0x00012bc000535000 0xf987ff8003ffe001 0x7cc3ffc001fff000

def z650 : W := mkw 0xc07ca85543495494 0x603e542aa1a4aa4a 0x2078cc16610c64c6 0x103c660b30863263

def z651 : W := mkw 0x0038285143001400 0x001c1428a1800a00 0xbe783c71e3001c01 0xdf3c1e38f1800e00

def z652 : W := mkw 0x0001002800100a00 0x8000801400080500 0x4187000800f00300 0x20c3800400780180

def z653 : W := mkw 0x20e7ffa894b28b28 0x9073ffd44a594594 0xffffffe99ef39b39 0xfffffff4cf79cd9c

def z654 : W := mkw 0x11c6d7822ceea163 0x08e36bc1167750b1 0xef87cf9e7dfe67e7 0xf7c3e7cf3eff33f3

def z655 : W := mkw 0x0000000000000000 0x0000000000000000 0x4100c00e008c03c0 0x20806007004601e0

def z656 : W := mkw 0x0000008000862000 0x0000004000431000 0x01000000018e6001 0x0080000000c73000

def z657 : W := mkw 0x01eced8003efe001 0x00f676c001f7f000 0x2178cc0003ffe001 0x10bc660001fff000

def z658 : W := mkw 0x4239287ffb015414 0x211c943ffd80aa0a 0xbe783c7fff03fc3f 0xdf3c1e3fff81fe1f

def z659 : W := mkw 0x4108008003eff415 0x2084004001f7fa0a 0x0500000003fffc3f 0x0280000001fffe1f

def z660 : W := mkw 0x40386d536b015414 0x201c36a9b580aa0a 0xfe78ffffff03fc3f 0xff3c7fffff81fe1f

def z661 : W := mkw 0x0000000000000000 0x0000000000000000 0x2000c016010c04c0 0x1000600b00860260

def z662 : W := mkw 0x8018005003581e80 0xc00c002801ac0f40 0x3d78007003fc1fc1 0x9ebc003801fe0fe0

def z663 : W := mkw 0x0000000000000000 0x0000000000000000 0x82000c0060026026 0x4100060030013013

def z664 : W := mkw 0x2000008004b28b28 0x9000004002594594 0x9f00306182f39b39 0xcf801830c179cd9c

def z665 : W := mkw 0x81fffffc03fffe81 0xc0fffffe01ffff40 0xf9ffffe003fff801 0x7cfffff001fffc00

def z666 : W := mkw 0x804d802c03581e80 0xc026c01601ac0f40 0x4587c00e03fc1fc1 0x22c3e00701fe0fe0

def z667 : W := mkw 0x1000008004862162 0x08000040024310b1 0xaf000c10618e67e7 0xd780060830c733f3

def z668 : W := mkw 0x00a27f0000000000 0x00513f8000000000 0x80003f8000000000 0x40001fc000000000

def z669 : W := mkw 0x200357a894b6ab28 0x9001abd44a5b5594 0xff87ffe99ffffb39 0xffc3fff4cffffd9c

def z670 : W := mkw 0x01c4c500004c2001 0x00e2628000261000 0x0000c000000c0000 0x0000600000060000

def z671 : W := mkw 0x22f7fffffcb28b28 0x917bfffffe594594 0xfbfffffffcf00300 0xfdfffffffe780180

def z672 : W := mkw 0x1055c5fe2c862162 0x082ae2ff164310b1 0xffffcffe7d8e67e7 0xffffe7ff3ec733f3

def z673 : W := mkw 0x42ffff7ffb015414 0x217fffbffd80aa0a 0xfafffffffe019818 0xfd7fffffff00cc0c

def z674 : W := mkw 0x9045c5ae2cde2be2 0xc822e2d7166f15f1 0x4187c38e1cfc03c0 0x20c3e1c70e7e01e0

def z675 : W := mkw 0x4028280143015414 0x20141400a180aa0a 0x86003c01e303fc3f 0x43001e00f181fe1f

def z676 : W := mkw 0x4018005143001414 0x200c0028a1800a0a 0x3e780071e3001c3f 0x9f3c0038f1800e1f

def z677 : W := mkw 0x4018005003015414 0x200c00280180aa0a 0x3c7800700303fc3f 0x9e3c00380181fe1f

def z678 : W := mkw 0x200312a894b28b28 0x900189544a594594 0xc38733899cf38338 0x61c399c4ce79c19c

def z679 : W := mkw 0x0002120090000000 0x0001090048000000 0x820033819c000000 0x410019c0ce000000

def z680 : W := mkw 0x805d80fc07da1fa0 0xc02ec07e03ed0fd0 0xffffc3fe1ffe1fe1 0xffffe1ff0fff0ff0

def z681 : W := mkw 0x200312a890b28a08 0x9001895448594504 0xd98733e182f39819 0x6cc399f0c179cc0c

def z682 : W := mkw 0x100045022c042162 0x08002281160210b1 0x2600cc1e7d0c67e6 0x9300660f3e8633f3

def z683 : W := mkw 0x805c805403581e80 0xc02e402a01ac0f40 0x2578c01603fc1fc1 0x12bc600b01fe0fe0

def z684 : W := mkw 0x0000000000000000 0x0000000000000000 0x20000c1061006406 0x1000060830803203

def z685 : W := mkw 0x905dc5fe2fde3fe2 0xc82ee2ff17ef1ff1 0x7dffc3fe1ffc1fc1 0xbeffe1ff0ffe0fe0

def z686 : W := mkw 0xe07fbafdd7fbdfbc 0xf03fdd7eebfdefde 0xffffffffffffffff 0xffffffffffffffff

def z687 : W := mkw 0x1000000228000042 0x0800000114000021 0x00000016600004c6 0x0000000b30000263

def z688 : W := mkw 0x12f4ed5768042042 0x097a76abb4021021 0x2078cc16610c64c6 0x103c660b30863263

def z689 : W := mkw 0x4020280140014014 0x20101400a000a00a 0x0000300180018018 0x00001800c000c00c

def z690 : W := mkw 0x12f7fffffc862162 0x097bfffffe4310b1 0xfafffffffc026026 0xfd7ffffffe013013

def z691 : W := mkw 0x1000450228042042 0x0800228114021021 0xae00cc16610e64e7 0xd700660b30873273

def z692 : W := mkw 0x0213127ff8000000 0x0109893ffc000000 0xda8733fffc000000 0xed4399fffe000000

def z693 : W := mkw 0xc07da87d43595e94 0xe03ed43ea1acaf4a 0x7dffcc7e63fc7fc7 0xbeffe63f31fe3fe3

def z694 : W := mkw 0xa04792ac94fa8ba8 0xd023c9564a7d45d4 0xdf87f3ef9eff9bf9 0xefc3f9f7cf7fcdfc

def z695 : W := mkw 0x42ffff7ffb015414 0x217fffbffd80aa0a 0xfafffffffd006406 0xfd7ffffffe803203

def z696 : W := mkw 0x1000450228042042 0x0800228114021021 0x00000c0060006006 0x0000060030003003

def z697 : W := mkw 0x300357aabcb6ab6a 0x9801abd55e5b55b5 0xdf87f3ef9eff9bf9 0xefc3f9f7cf7fcdfc

def z698 : W := mkw 0x12c7d7aebc862162 0x0963ebd75e4310b1 0x4187c38e1c8c03c0 0x20c3e1c70e4601e0

def z699 : W := mkw 0x005d807c03001400 0x002ec03e01800a00 0x7cffc07e03001c01 0xbe7fe03f01800e00

def z700 : W := mkw 0x01e6ff8000a7e001 0x00f37fc00053f000 0xf8ffff800003e000 0x7c7fffc00001f000

def z701 : W := mkw 0x50386d536b057456 0x281c36a9b582ba2b 0x2078cc16610c64c6 0x103c660b30863263

def z702 : W := mkw 0x02f5ed7f68000000 0x017af6bfb4000000 0x78ffcc7e60000000 0xbc7fe63f30000000

def z703 : W := mkw 0x0030285140000000 0x00181428a0000000 0x20780c1060000000 0x103c060830000000

def z704 : W := mkw 0x825d807ffb581e80 0xc12ec03ffdac0f40 0x7fffc07ffffc1fc1 0xbfffe03ffffe0fe0

def z705 : W := mkw 0xc1fffffd43fffe95 0xe0fffffea1ffff4a 0xffffffffe3ffffff 0xfffffffff1ffffff

def z706 : W := mkw 0x02f7ff7ff8000000 0x017bffbffc000000 0x30fffc77e0000000 0x187ffe3bf0000000

def z707 : W := mkw 0x4038285143015414 0x201c1428a180aa0a 0xa6783c71e103fc3e 0xd33c1e38f081fe1f

def z708 : W := mkw 0x02f7ff7ff8000000 0x017bffbffc000000 0x78ffcffe7c000000 0xbc7fe7ff3e000000

def z709 : W := mkw 0x0008000003480000 0x0004000001a40000 0x0500000003fc07c1 0x0280000001fe03e0

def z710 : W := mkw 0x01eeba8003ebc001 0x00f75d4001f5e000 0xf9fff38003ff8001 0x7cfff9c001ffc000

def z711 : W := mkw 0x8011007c00101e80 0xc008803e00080f40 0x0600007e60001fe6 0x8300003f30000ff3

def z712 : W := mkw 0x01ccc500034c2001 0x00e6628001a61000 0x79ffc00003fc0001 0x3cffe00001fe0000

def z713 : W := mkw 0x2003122890308a08 0x9001891448184504 0x508733e99e719818 0x284399f4cf38cc0c

def z714 : W := mkw 0x01eced00034d6001 0x00f6768001a6b000 0xf9fffc0003ffe001 0x7cfffe0001fff000

def z715 : W := mkw 0x02f7ba7dd0000000 0x017bdd3ee8000000 0x92ff33e19c000000 0x497f99f0ce000000

def z716 : W := mkw 0x004c800003480000 0x0026400001a40000 0x7dffc00003fc07c1 0x3effe00001fe03e0

def z717 : W := mkw 0x01e6ff8000efe001 0x00f37fc00077f000 0xf9ffff8000ffe000 0x7cffffc0007ff000

def z718 : W := mkw 0x11eeff822fefe163 0x08f77fc117f7f0b1 0xfbffff9e7fffe027 0xfdffffcf3ffff013

def z719 : W := mkw 0x100045822ca6a162 0x080022c1165350b1 0xef00cf9e7fffe7e7 0xf78067cf3ffff3f3

def z720 : W := mkw 0x100045822c862162 0x080022c1164310b1 0xff87cf9e7ffe67e7 0xffc3e7cf3fff33f3

def z721 : W := mkw 0x11eeff8007efe163 0x08f77fc003f7f0b1 0xffffff881fffe7e7 0xffffffc40ffff3f3

def z722 : W := mkw 0x11eeff822fefe163 0x08f77fc117f7f0b1 0xffffff907fffe427 0xffffffc83ffff213

def z723 : W := mkw 0xc011007d40101e94 0xe008803ea0080f4a 0x0400007e60001fc6 0x8200003f30000fe3

def z724 : W := mkw 0x8055807c00580a80 0xc02ac03e002c0540 0x51ffc06e00fc03c0 0x28ffe037007e01e0

def z725 : W := mkw 0x1108008007efe163 0x0884004003f7f0b1 0x0100000003ffe027 0x0080000001fff013

def z726 : W := mkw 0x21eeff8097efe129 0x10f77fc04bf7f094 0xf9ffff801fffe001 0x7cffffc00ffff000

def z727 : W := mkw 0x02b37f7ff8000000 0x0159bfbffc000000 0xba783ffffc000000 0xdd3c1ffffe000000

def z728 : W := mkw 0x02f7ff7ff8000000 0x017bffbffc000000 0xfefffffffe001801 0xff7fffffff000c00

def z729 : W := mkw 0x01eeba000369c001 0x00f75d0001b4e000 0x90ff3c000273e000 0x487f9e000139f000

def z730 : W := mkw 0x22f7ff7ff8100a08 0x917bffbffc080504 0xfafffffffc001818 0xfd7ffffffe000c0c

def z731 : W := mkw 0x804d802c03580a80 0xc026c01601ac0540 0x51ffc00e02fc03c0 0x28ffe007017e01e0

def z732 : W := mkw 0x02f7ff7ff8000000 0x017bffbffc000000 0xa278fffffc000000 0xd13c7ffffe000000

def z733 : W := mkw 0x012a3a8003efe001 0x00951d4001f7f000 0xf9ff3f8003ffe001 0x7cff9fc001fff000

def z734 : W := mkw 0x00e6ff0000000000 0x00737f8000000000 0xfaffff881c000000 0xfd7fffc40e000000

def z735 : W := mkw 0x805d807c03595e80 0xc02ec03e01acaf40 0x7dffc07e03ffffc1 0xbeffe03f01ffffe0

def z736 : W := mkw 0x41eeba000369d415 0x20f75d0001b4ea0a 0x14ff30000373fc3f 0x0a7f980001b9fe1f

def z737 : W := mkw 0x02f6ff57f8000000 0x017b7fabfc000000 0xba78fff7fc000000 0xdd3c7ffbfe000000

def z738 : W := mkw 0x00f6ff5368000000 0x007b7fa9b4000000 0xfafffffffc000000 0xfd7ffffffe000000

def z739 : W := mkw 0x200312a894b28b28 0x900189544a594594 0xff873ff9fef39b39 0xffc39ffcff79cd9c

def z740 : W := mkw 0x4038285143015414 0x201c1428a180aa0a 0xbe78fc77e30ffcff 0xdf3c7e3bf187fe7f

def z741 : W := mkw 0x200312a894b28b28 0x900189544a594594 0xff87f3e99fff9b39 0xffc3f9f4cfffcd9c

def z742 : W := mkw 0x0044800000480000 0x0022400000240000 0x79ffc00000fc0000 0x3cffe000007e0000

def z743 : W := mkw 0x2108008007ffeb29 0x9084004003fff594 0x0100000003ffe301 0x0080000001fff180

def z744 : W := mkw 0x13eeff83ffefe163 0x09f77fc1fff7f0b1 0xffffff9fffffe7e7 0xffffffcffffff3f3

def z745 : W := mkw 0x31eeff82bfefe16b 0x18f77fc15ff7f0b5 0xffffff9fffffe7ff 0xffffffcffffff3ff

def z746 : W := mkw 0x20110079d4100b28 0x9008803cea080594 0x06000079fc001b38 0x8300003cfe000d9c

def z747 : W := mkw 0x0019007803101e00 0x800c803c01880f00 0x7dffc07e03fc1fc1 0xbeffe03f01fe0fe0

def z748 : W := mkw 0x11eeff822fefe163 0x08f77fc117f7f0b1 0xfdffff9663ffe7e7 0x7effffcb31fff3f3

def z749 : W := mkw 0x01eeff8093efe001 0x00f77fc049f7f000 0xfbffff819fffe001 0x7dffffc0cffff000

def z750 : W := mkw 0x11eeff822fefe163 0x08f77fc117f7f0b1 0xfbffff967fffe4e7 0x7dffffcb3ffff273

def z751 : W := mkw 0x006ca80003480000 0x0036540001a40000 0xf9fffc0003fc0001 0x7cfffe0001fe0000

def z752 : W := mkw 0x805d807c03581e80 0xc02ec03e01ac0f40 0x41ffc00e00fc03c0 0x20ffe007007e01e0

def z753 : W := mkw 0x02f7ff7ff8000000 0x017bffbffc000000 0xfbfffffffef00001 0xfdffffffff780000

def z754 : W := mkw 0x41eeff8143eff415 0x20f77fc0a1f7fa0a 0xffffff81e3fffc3f 0x7fffffc0f1fffe1f

def z755 : W := mkw 0x82f7ff7ff8580a80 0xc17bffbffc2c0540 0xfafffffffc700000 0xfd7ffffffe380000

def z756 : W := mkw 0x00e6ff0000000000 0x00737f8000000000 0xf9ffff8002f00001 0x7cffffc001780000

def z757 : W := mkw 0x00eeff022b480000 0x00777f8115a40000 0xffffff9e7ffc07c1 0xffffffcf3ffe03e0

def z758 : W := mkw 0x8211457ff8101e80 0xc108a2bffc080f40 0xef00cffffd8c1fc1 0xf78067fffec60fe0

def z759 : W := mkw 0x1008008007ce2162 0x0804004003e710b1 0x0500000003fe67e7 0x0280000001ff33f3

def z760 : W := mkw 0x00e6ba0000208000 0x00735d0000104000 0x10ff300002718000 0x087f98000138c000

def z761 : W := mkw 0x02f7ff7ff8000000 0x017bffbffc000000 0xfefffffffc0007c0 0xff7ffffffe0003e0

def z762 : W := mkw 0x00eeff8003ea8000 0x00777fc001f54000 0xf9ffff8003ff8001 0x7cffffc001ffc000

def z763 : W := mkw 0x11eeff022b6de043 0x08f77f8115b6f021 0x30fffc16637de4c6 0x187ffe0b31bef263

def z764 : W := mkw 0x02d7d77eb8000000 0x016bebbf5c000000 0xfafff3ff9c000000 0xfd7ff9ffce000000

def z765 : W := mkw 0x01eeff8003efe001 0x00f77fc001f7f000 0xfdffff9003ffe401 0xfeffffc801fff200

def z766 : W := mkw 0x8211007dd0101e80 0xc108803ee8080f40 0x0400007f80001fc0 0x8200003fc0000fe0

def z767 : W := mkw 0x4011007940101e14 0xa008803ca0080f0a 0x06000079e0001f3e 0x8300003cf0000f9f

def z768 : W := mkw 0x004c800003480000 0x0026400001a40000 0x78ffc00002700000 0x3c7fe00001380000

def z769 : W := mkw 0x8211007ff8101e80 0xc108803ffc080f40 0x0200007ffc001800 0x8100003ffe000c00

def z770 : W := mkw 0xc065a82d40594a94 0xe032d416a02ca54a 0xc387fc0fe0ffe3fe 0x61c3fe07f07ff1ff

def z771 : W := mkw 0xa00312ac94b28ba8 0xd00189564a5945d4 0xdf8733ef9ef39bf9 0xefc399f7cf79cdfc

def z772 : W := mkw 0x01eeff000369c001 0x00f77f8001b4e000 0x50fff38002718000 0x287ff9c00138c000

def z773 : W := mkw 0x221145fffc920b28 0x9108a2fffe490594 0xef00cffffc821b39 0xf78067fffe410d9c

def z774 : W := mkw 0x004c800003480000 0x0026400001a40000 0xf9ffcc0003fe6001 0x7cffe60001ff3000

def z775 : W := mkw 0x905dc5fe2fde3fe2 0xc82ee2ff17ef1ff1 0x92ff0fe07e727826 0x497f87f03f393c13

def z776 : W := mkw 0x11eeff822fefe163 0x08f77fc117f7f0b1 0x61ffcf9e7dfc67c6 0x30ffe7cf3efe33e3

def z777 : W := mkw 0x11eeba022f69c163 0x08f75d0117b4e0b1 0x16ff301e7e7187e6 0x8b7f980f3f38c3f3

def z778 : W := mkw 0x200312a894b28b28 0x900189544a594594 0xd38733e99ef39b38 0x69c399f4cf79cd9c

def z779 : W := mkw 0x200312a894b28b28 0x900189544a594594 0xd98733e99ef39b19 0x6cc399f4cf79cd8c

def z780 : W := mkw 0x1108008007efe163 0x0884004003f7f0b1 0x0100000003ffe3c1 0x0080000001fff1e0

def z781 : W := mkw 0x00e6ff8000a6a000 0x00737fc000535000 0xf9ffff8003ffe001 0x7cffffc001fff000

def z782 : W := mkw 0x11eeff822fefe163 0x08f77fc117f7f0b1 0x51fff38e1efd83c0 0x28fff9c70f7ec1e0

def z783 : W := mkw 0x11eeff8007efe163 0x08f77fc003f7f0b1 0xfdffff9e03ffe7e7 0xfeffffcf01fff3f3

def z784 : W := mkw 0xb011007ebc101fea 0xd808803f5e080ff5 0x0600007ffc001ffe 0x8300003ffe000fff

def z785 : W := mkw 0x31c7d7aabcfeab6b 0x98e3ebd55e7f55b5 0x4187c38e1cfc03c0 0x20c3e1c70e7e01e0

def z786 : W := mkw 0x82f7ff7ff8101e80 0xc17bffbffc080f40 0xfffffffffd8c1fc1 0xfffffffffec60fe0

def z787 : W := mkw 0x1108008007cf6163 0x0884004003e7b0b1 0x05000000018e67e7 0x0280000000c733f3

def z788 : W := mkw 0x005c805003481400 0x002e402801a40a00 0x7dffc07e03fc1fc1 0xbeffe03f01fe0fe0

def z789 : W := mkw 0x11eeff8007efe163 0x08f77fc003f7f0b1 0xffffff9063ffe7e7 0xffffffc831fff3f3

def z790 : W := mkw 0x01eeba8003efe001 0x00f75d4001f7f000 0x10ff30000273e000 0x087f98000139f000

def z791 : W := mkw 0x11eeff822fefe163 0x08f77fc117f7f0b1 0xffffff887fffe327 0xffffffc43ffff193

def z792 : W := mkw 0x60333af9d4b3df3c 0xb0199d7cea59ef9e 0x86003ff9fc03ff3e 0xc3001ffcfe01ff9f

def z793 : W := mkw 0xc05d807d43581e94 0xe02ec03ea1ac0f4a 0xffffcc7fe3fe7fff 0xffffe63ff1ff3fff

def z794 : W := mkw 0x2002128094a28128 0x100109404a514094 0xdf8733e19ef39839 0xefc399f0cf79cc1c

def z795 : W := mkw 0x01ced78003eea001 0x00e76bc001f75000 0x51ffc38002fc0000 0x28ffe1c0017e0000

def z796 : W := mkw 0x2211007ffc100b28 0x9108803ffe080594 0x0200007ffc000300 0x8100003ffe000180

def z797 : W := mkw 0x01ced78003eea001 0x00e76bc001f75000 0x61ffc38001fc0000 0x30ffe1c000fe0000

def z798 : W := mkw 0x82f7ff7ff8101e80 0xc17bffbffc080f40 0xfafffffffc001800 0xfd7ffffffe000c00

def z799 : W := mkw 0x8055807c00580a80 0xc02ac03e002c0540 0x7dffc07e02fc1bc1 0xbeffe03f017e0de0

def z800 : W := mkw 0x02f7ff7ff8000000 0x017bffbffc000000 0xfefffffffc020021 0xff7ffffffe010010

def z801 : W := mkw 0x01eeff8003efe001 0x00f77fc001f7f000 0xd1ffff8002ffe000 0x68ffffc0017ff000

def z802 : W := mkw 0x3003572ab834aa4a 0x9801ab955c1a5525 0x3087fc77e37dfcde 0x1843fe3bf1befe6f

def z803 : W := mkw 0x004c800003480000 0x0026400001a40000 0x2078c016010c04c0 0x103c600b00860260

def z804 : W := mkw 0x42f7ff7ff8001414 0x217bffbffc000a0a 0xfafffffffc000406 0xfd7ffffffe000203

def z805 : W := mkw 0x100045822c862162 0x080022c1164310b1 0xef00cffffd8e7fff 0xf78067fffec73fff

def z806 : W := mkw 0x02f6ff57f8000000 0x017b7fabfc000000 0xfaffff97fc000000 0x7d7fffcbfe000000

def z807 : W := mkw 0x01eeba8003efe001 0x00f75d4001f7f000 0xb9ff3c0003ffe001 0x5cff9e0001fff000

def z808 : W := mkw 0x01eeba000369c001 0x00f75d0001b4e000 0x98ff300002738001 0x4c7f98000139c000

def z809 : W := mkw 0x4038285143015414 0x201c1428a180aa0a 0xbf783c71e38fffff 0xdfbc1e38f1c7ffff

def z810 : W := mkw 0x100045822c862162 0x080022c1164310b1 0x6500cf9e7d8e67e7 0x328067cf3ec733f3

def z811 : W := mkw 0x0047922890000000 0x0023c91448000000 0xfafff3e99c000000 0xfd7ff9f4ce000000

def z812 : W := mkw 0x42f7ff7ff8014014 0x217bffbffc00a00a 0xfefffffffd03e43f 0xff7ffffffe81f21f

def z813 : W := mkw 0x31a27f82bca7e16b 0x18d13fc15e53f0b5 0x82003f81fc03e03e 0x41001fc0fe01f01f

def z814 : W := mkw 0x11eeff822fefe163 0x08f77fc117f7f0b1 0xfdffff8e1fffe7e7 0x7effffc70ffff3f3

def z815 : W := mkw 0xc211007ff8101e94 0xe108803ffc080f4a 0x0600007ffc001ffe 0x8300003ffe000fff

def z816 : W := mkw 0x11eeff822fefe163 0x08f77fc117f7f0b1 0xfbffff8e7fffe3e7 0x7dffffc73ffff1f3

def z817 : W := mkw 0x11eeff822fefe163 0x08f77fc117f7f0b1 0xffffff807fffe7e7 0x7fffffc03ffff3f3

def z818 : W := mkw 0x02f7ff7ff8000000 0x017bffbffc000000 0xfbfffffffc8c03c0 0xfdfffffffe4601e0

def z819 : W := mkw 0x801145fc00963e80 0xc008a2fe004b1f40 0xed00cffe018e7fc1 0xf68067ff00c73fe0

def z820 : W := mkw 0xa05d807c93581e88 0xd02ec03e49ac0f44 0x7dffc07f83fc1fd9 0xbeffe03fc1fe0fec

def z821 : W := mkw 0x0255c57ff8000000 0x012ae2bffc000000 0xfaffcffffc000000 0xfd7fe7fffe000000

def z822 : W := mkw 0x8011007c00101e80 0xc008803e00080f40 0x6c00c07e00001fc0 0xb600603f00000fe0

def z823 : W := mkw 0x13a27f83fca7e163 0x09d13fc1fe53f0b1 0x82003f81fc03e026 0x41001fc0fe01f013

def z824 : W := mkw 0x81b37ffc00b7fe81 0xc0d9bffe005bff40 0x84003ffe0003ffc0 0xc2001fff0001ffe0

def z825 : W := mkw 0xd01145ff6c963ff6 0xe808a2ffb64b1ffb 0xef00cffffd8e7fff 0xf78067fffec73fff

def z826 : W := mkw 0x02e7ff2eb8000000 0x0173ff975c000000 0xfaffff9e7c000000 0xfd7fffcf3e000000

def z827 : W := mkw 0x02f7ba7ff8000000 0x017bdd3ffc000000 0xdaff33fffc000000 0xed7f99fffe000000

def z828 : W := mkw 0x01eeba000369c001 0x00f75d0001b4e000 0xbeff3c106373e427 0xdf7f9e0831b9f213

def z829 : W := mkw 0x804d802c03581e80 0xc026c01601ac0f40 0x7dffc00e03fc1fc1 0x3effe00701fe0fe0

def z830 : W := mkw 0x01eeff8003efe001 0x00f77fc001f7f000 0xfbffffe183ffe001 0xfdfffff0c1fff000

def z831 : W := mkw 0x01e6ff8000eea001 0x00f37fc000775000 0xf9ffff8002ff8001 0x7cffffc0017fc000

def z832 : W := mkw 0x21eded28975d6b29 0x90f6f6944baeb594 0x2678cc699d0c7b38 0x933c6634ce863d9c

def z833 : W := mkw 0x02f7ff7ff8000000 0x017bffbffc000000 0xf8ffff9e7c000000 0x7c7fffcf3e000000

def z834 : W := mkw 0x004c800003494000 0x0026400001a4a000 0x79ffc00003ffe001 0x3cffe00001fff000

def z835 : W := mkw 0x11eeff822befe043 0x08f77fc115f7f021 0xf9ffff8603ffe0c1 0x7cffffc301fff060

def z836 : W := mkw 0x01eeff8003efe001 0x00f77fc001f7f000 0xf9ffff9e03ffe001 0xfcffffcf01fff000

def z837 : W := mkw 0x805c805403481480 0x402e402a01a40a40 0x7dffc01e03fc07c1 0xbeffe00f01fe03e0

def z838 : W := mkw 0x0077ba7dd0000000 0x003bdd3ee8000000 0xfafffffffc000000 0xfd7ffffffe000000

def z839 : W := mkw 0x3108008007ffeb6b 0x9884004003fff5b5 0x0500000003ffffff 0x0280000001ffffff

def z840 : W := mkw 0x01eeba8003efe001 0x00f75d4001f7f000 0x11ff300002fd8000 0x08ff9800017ec000

def z841 : W := mkw 0x01eeff8003efe001 0x00f77fc001f7f000 0x79fff38003fd8001 0x3cfff9c001fec000

def z842 : W := mkw 0x9108008007ffffe3 0xc884004003fffff1 0x0500000003ffffe7 0x0280000001fffff3

def z843 : W := mkw 0x41d6d7d140eeb415 0x20eb6be8a0775a0a 0x4787c3f1e0fc1c3e 0xa3c3e1f8f07e0e1f

def z844 : W := mkw 0x02f7ff7ff8001400 0x017bffbffc000a00 0xfefffffffc001c00 0xff7ffffffe000e00

def z845 : W := mkw 0x02e7ff2ff8000000 0x0173ff97fc000000 0xfaffff8ffc000000 0x7d7fffc7fe000000

def z846 : W := mkw 0x005d807c03480000 0x002ec03e01a40000 0x7dffc07e03fc07c1 0xbeffe03f01fe03e0

def z847 : W := mkw 0x601100f9d4921f3c 0xb008807cea490f9e 0xef000ff9fd827f3f 0xf78007fcfec13f9f

def z848 : W := mkw 0x02c7d72eb8000000 0x0163eb975c000000 0x78ffc38e1c000000 0x3c7fe1c70e000000

def z849 : W := mkw 0x105580fc04862162 0x082ac07e024310b1 0x7dffc07e018e67e7 0xbeffe03f00c733f3

def z850 : W := mkw 0xc011007c00101e94 0xe008803e00080f4a 0x0400007e00001ffe 0x8200003f00000fff

def z851 : W := mkw 0x200312a894b28b28 0x900189544a594594 0xdf8733ff9ef39ff9 0xefc399ffcf79cffc

def z852 : W := mkw 0x014c8000034d6001 0x00a6400001a6b000 0x79ffc00003fc6001 0x3cffe00001fe3000

def z853 : W := mkw 0x01eeff00036de001 0x00f77f8001b6f000 0x10ff3c000271e000 0x087f9e000138f000

def z854 : W := mkw 0x01aa7f8003a7e001 0x00d53fc001d3f000 0xf9ff3f8003f3e001 0x7cff9fc001f9f000

def z855 : W := mkw 0x4038285143015414 0x201c1428a180aa0a 0x96783c71e203fc3e 0xcb3c1e38f101fe1f

def z856 : W := mkw 0x9011457e28143ec2 0xc808a2bf140a1f61 0x2400cc7e610c7fc6 0x9200663f30863fe3

def z857 : W := mkw 0x02f7ff7ff8000000 0x017bffbffc000000 0xdafff3ef9c000000 0xed7ff9f7ce000000

def z858 : W := mkw 0x0028280003014000 0x001414000180a000 0xbe783c71e303fc3f 0xdf3c1e38f181fe1f

def z859 : W := mkw 0x01ced78003efe001 0x00e76bc001f7f000 0x79ffc38003ffe001 0x3cffe1c001fff000

def z860 : W := mkw 0x100045022c042162 0x08002281160210b1 0xee00cf9e7d0c67e6 0xf70067cf3e8633f3

def z861 : W := mkw 0x8019007c03101e80 0xc00c803e01880f40 0x0400007e03001fc1 0x8200003f01800fe0

def z862 : W := mkw 0x50386dd36f877576 0x281c36e9b7c3babb 0x5178f3ef9e8d9bd8 0x28bc79f7cf46cdec

def z863 : W := mkw 0x02e6ff03f8000000 0x01737f81fc000000 0xfaffff9ffc000000 0xfd7fffcffe000000

def z864 : W := mkw 0x0054c55628000000 0x002a62ab14000000 0xea78cf9e7c000000 0xf53c67cf3e000000

def z865 : W := mkw 0x100045822c862162 0x080022c1164310b1 0xff00ff9e7f8fe7e7 0xff807fcf3fc7f3f3

def z866 : W := mkw 0x21eeff8007efe129 0x10f77fc003f7f094 0xf9ffff8003ffe039 0x7cffffc001fff01c

def z867 : W := mkw 0xb01145febc963fea 0xd808a2ff5e4b1ff5 0xef00cffffd8e7fff 0xf78067fffec73fff

def z868 : W := mkw 0x9008008007ce35e2 0x4804004003e71af1 0x05000000018e67e7 0x0280000000c733f3

def z869 : W := mkw 0x8011007c00101e80 0xc008803e00080f40 0x0000006e00001bc0 0x0000003700000de0

def z870 : W := mkw 0x00e6ff8000a28000 0x00737fc000514000 0xf9ffff8000f00000 0x7cffffc000780000

def z871 : W := mkw 0xc031287d40115e94 0xe018943ea008af4a 0x86003c7fe003fffe 0xc3001e3ff001ffff

def z872 : W := mkw 0x01eeba000369c001 0x00f75d0001b4e000 0x7dfff01e03fd87c1 0xbefff80f01fec3e0

def z873 : W := mkw 0x02f6ff53f8000000 0x017b7fa9fc000000 0xfafffff1fc000000 0xfd7ffff8fe000000

def z874 : W := mkw 0x01eced00034d6001 0x00f6768001a6b000 0x30ffcc00037c6000 0x187fe60001be3000

def z875 : W := mkw 0x8011007c00101e80 0xc008803e00080f40 0x0000007600001cc0 0x0000003b00000e60

def z876 : W := mkw 0x02f7ff7ff8000000 0x017bffbffc000000 0xfafffffffd026001 0xfd7ffffffe813000

def z877 : W := mkw 0x3211007ffc100b6a 0x9908803ffe0805b5 0x0600007ffc001ffe 0x8300003ffe000fff

def z878 : W := mkw 0x6211007ffc101f3c 0xb108803ffe080f9e 0x0600007ffc001f3e 0x8300003ffe000f9f

def z879 : W := mkw 0x42cfd72ebb015414 0x2167eb975d80aa0a 0x4487c38e1f03fc3f 0x2243e1c70f81fe1f

def z880 : W := mkw 0x300045822ca6a16a 0x180022c1165350b5 0xef00cf9e7d8fe7ff 0xf78067cf3ec7f3ff

def z881 : W := mkw 0x004e928003ea8000 0x0027494001f54000 0x79ffc38003fc0001 0x3cffe1c001fe0000

def z882 : W := mkw 0x01eeba000369c001 0x00f75d0001b4e000 0x10ff30000373e001 0x087f980001b9f000

def z883 : W := mkw 0x00e4ed0228000000 0x0072768114000000 0xea78cf9e7c000000 0xf53c67cf3e000000

def z884 : W := mkw 0x0044c50228000000 0x0022628114000000 0xfaffcf9e7c000000 0xfd7fe7cf3e000000

def z885 : W := mkw 0x004cc500034c2000 0x0026628001a61000 0x79ffcc0003fc6001 0x3cffe60001fe3000

def z886 : W := mkw 0x006eba8003ebc000 0x00375d4001f5e000 0xf9ffff8003ffe001 0x7cffffc001fff000

def z887 : W := mkw 0x8011007c00101e80 0xc008803e00080f40 0x0000007e00001800 0x8000003f00000c00

def z888 : W := mkw 0x200312a890b28a08 0x9001895448594504 0xdb8733e99ef39819 0xedc399f4cf79cc0c

def z889 : W := mkw 0x01eeff8003efe001 0x00f77fc001f7f000 0xfbffff881fffe001 0xfdffffc40ffff000

def z890 : W := mkw 0x200312a894b28b28 0x900189544a594594 0x558733e99ef39b39 0x2ac399f4cf79cd9c

def z891 : W := mkw 0x000100a804920b20 0x8000805402490590 0xdf8733e99ef39b39 0xefc399f4cf79cd9c

def z892 : W := mkw 0x300312a894b6ab6a 0x980189544a5b55b5 0xff873ff9ffffffff 0xffc39ffcffffffff

def z893 : W := mkw 0x12f7bafdd4862162 0x097bdd7eea4310b1 0x15ff3061818e67e7 0x0aff9830c0c733f3

def z894 : W := mkw 0x4038285143015414 0x201c1428a180aa0a 0xba783c71e203f83e 0xdd3c1e38f101fc1f

def z895 : W := mkw 0x01eeff000369c001 0x00f77f8001b4e000 0x90ff3f8002718000 0x487f9fc00138c000

def z896 : W := mkw 0x004c800003480000 0x0026400001a40000 0x7dffc01003fc0401 0xbeffe00801fe0200

def z897 : W := mkw 0x031900fffbefe001 0x018c807ffdf7f000 0x0300007fffffe001 0x8180003ffffff000

def z898 : W := mkw 0x400845022b015414 0x200422811580aa0a 0xee00cf9e7f03fc3f 0xf70067cf3f81fe1f

def z899 : W := mkw 0x0000008004820120 0x0000004002410090 0xef00cf9e7d8e67e7 0xf78067cf3ec733f3

def z900 : W := mkw 0x00f7ff7e28000000 0x007bffbf14000000 0xfafffffe7c000000 0xfd7fffff3e000000

def z901 : W := mkw 0x4038285143015414 0x201c1428a180aa0a 0xfe78fc7fe303fc3f 0xff3c7e3ff181fe1f

def z902 : W := mkw 0xc2f7ff7ff8101e94 0xe17bffbffc080f4a 0xfefffffffc001ffe 0xff7ffffffe000fff

def z903 : W := mkw 0x0011007800101e00 0x8008803c00080f00 0x0400007800001f00 0x8200003c00000f80

def z904 : W := mkw 0x01eeff00036de001 0x00f77f8001b6f000 0xf8ffff80037de000 0x7c7fffc001bef000

def z905 : W := mkw 0x02f7ff7ff8000000 0x017bffbffc000000 0xfeffffffff03fc3f 0xff7fffffff81fe1f

def z906 : W := mkw 0x8211007ff8100a80 0xc108803ffc080540 0x0200007ffc0003c0 0x8100003ffe0001e0

def z907 : W := mkw 0x8011007c00101e80 0xc008803e00080f40 0x0500007e018c1fc1 0x8280003f00c60fe0

def z908 : W := mkw 0x02f7ff7ff8000000 0x017bffbffc000000 0xbaff3ff1fc000000 0xdd7f9ff8fe000000

def z909 : W := mkw 0x01eeff8003efe001 0x00f77fc001f7f000 0xe1ffff8001ffe000 0x70ffffc000fff000

def z910 : W := mkw 0x0044800000480000 0x0022400000240000 0x4187c00e00fc03c0 0x20c3e007007e01e0

def z911 : W := mkw 0x42f7ff7ff8000014 0x217bffbffc00000a 0xfafffffffc00003e 0xfd7ffffffe00001f

def z912 : W := mkw 0x004c800003480000 0x0026400001a40000 0x79ffc00e03fc03c1 0x3cffe00701fe01e0

def z913 : W := mkw 0x01eeff8003efe001 0x00f77fc001f7f000 0xb8ff3f800373e001 0x5c7f9fc001b9f000

def z914 : W := mkw 0x004c808007ca0120 0x0026404003e50090 0xffffc3881ffe0321 0xffffe1c40fff0190

def z915 : W := mkw 0x02f7ff7ff8000000 0x017bffbffc000000 0xb2fffff7fc000000 0x597ffffbfe000000

def z916 : W := mkw 0x22f7ff7ff8308a08 0x917bffbffc184504 0xfafffffffc700000 0xfd7ffffffe380000

def z917 : W := mkw 0x106ced822fcf6162 0x083676c117e7b0b1 0xffffff9e7fffe7e7 0xffffffcf3ffff3f3

def z918 : W := mkw 0x805d807c03581e80 0xc02ec03e01ac0f40 0x79ffc07e01fc07c0 0xbcffe03f00fe03e0

def z919 : W := mkw 0xc011007d40101e94 0xe008803ea0080f4a 0x06000071e0001c3e 0x83000038f0000e1f

def z920 : W := mkw 0x805d807c03581e80 0xc02ec03e01ac0f40 0x65ffc01e03fc1fc1 0x32ffe00f01fe0fe0

def z921 : W := mkw 0xc011007d40101e94 0xe008803ea0080f4a 0x0400007f80001fd8 0x8200003fc0000fec

def z922 : W := mkw 0x0211007ff8100a00 0x8108803ffc080500 0x0600007ffc001b00 0x8300003ffe000d80

def z923 : W := mkw 0x200312a894b28b28 0x900189544a594594 0xdf8733e99ff3ff3f 0xefc399f4cff9ff9f

def z924 : W := mkw 0x02f7ff7ff8000000 0x017bffbffc000000 0xfafffffffc026026 0xfd7ffffffe013013

def z925 : W := mkw 0x004c800003480000 0x0026400001a40000 0x51ffc00002fc0000 0x28ffe000017e0000

def z926 : W := mkw 0x004c800003480000 0x0026400001a40000 0x61ffc00001fc0000 0x30ffe00000fe0000

def z927 : W := mkw 0x01eeff8003efe001 0x00f77fc001f7f000 0xffffff8003ffe021 0xffffffc001fff010

def z928 : W := mkw 0x11eeff822fefe163 0x08f77fc117f7f0b1 0x92ff3f807e73e026 0x497f9fc03f39f013

def z929 : W := mkw 0x11eeff8007efe163 0x08f77fc003f7f0b1 0xf9ffff8003ffe3c1 0x7cffffc001fff1e0

def z930 : W := mkw 0x8011007c04101fa0 0xc008803e02080fd0 0x0600007e1c001fe0 0x8300003f0e000ff0

def z931 : W := mkw 0x4038285143495414 0x201c1428a1a4aa0a 0xbf783c71e3fffc3f 0xdfbc1e38f1fffe1f

def z932 : W := mkw 0x5108008007eff577 0x2884004003f7fabb 0x0500000003ffffff 0x0280000001ffffff

def z933 : W := mkw 0x02333a7ff8000000 0x01199d3ffc000000 0xfaff3ffffc000000 0xfd7f9ffffe000000

def z934 : W := mkw 0x02e7ff2eb8000000 0x0173ff975c000000 0x50fff38e1c000000 0x287ff9c70e000000

def z935 : W := mkw 0x01eeff8003eff401 0x00f77fc001f7fa00 0xfdffff8003fffc01 0x7effffc001fffe00

def z936 : W := mkw 0x01eeba000369c001 0x00f75d0001b4e000 0x11ff300003fd8001 0x08ff980001fec000

def z937 : W := mkw 0x02eeff03fb480000 0x01777f81fda40000 0xfbffff81fffc0001 0x7dffffc0fffe0000

def z938 : W := mkw 0x004c808003ce2000 0x0026404001e71000 0x79ffc00003fe6001 0x3cffe00001ff3000

def z939 : W := mkw 0x8211007dd0101e80 0xc108803ee8080f40 0x0000006180001800 0x00000030c0000c00

def z940 : W := mkw 0x804c800003481480 0x4026400001a40a40 0x79ffc00003fc04c1 0x3cffe00001fe0260

def z941 : W := mkw 0x01eeff8003efe001 0x00f77fc001f7f000 0xfffffff1e3fffc3f 0xfffffff8f1fffe1f

def z942 : W := mkw 0x00e6ff0000208000 0x00737f8000104000 0xf8ffff8002718000 0x7c7fffc00138c000

def z943 : W := mkw 0x01eeba8003ebc001 0x00f75d4001f5e000 0x90ff338002738000 0x487f99c00139c000

def z944 : W := mkw 0x8011007c00100a80 0xc008803e00080540 0x0000007e000003c0 0x8000003f000001e0

def z945 : W := mkw 0x804c800003581e80 0xc026400001ac0f40 0x7dffc01e03fc1fc1 0xbeffe00f01fe0fe0

def z946 : W := mkw 0x01eeba000369c001 0x00f75d0001b4e000 0x00ff000000700000 0x007f800000380000

def z947 : W := mkw 0x02f7ff7ff8000000 0x017bffbffc000000 0xfefffffffc001838 0xff7ffffffe000c1c

def z948 : W := mkw 0xd008008007df7ff6 0xe804004003efbffb 0x0500000003ffffff 0x0280000001ffffff

def z949 : W := mkw 0x9011007e2c101fe2 0xc808803f16080ff1 0x0400007e1c001fc0 0x8200003f0e000fe0

def z950 : W := mkw 0x01eeba000369c001 0x00f75d0001b4e000 0x30ff3c000371e000 0x187f9e0001b8f000

def z951 : W := mkw 0x200312a894b28b28 0x900189544a594594 0xda8733e99e739838 0xed4399f4cf39cc1c

def z952 : W := mkw 0x01eeff8003efe001 0x00f77fc001f7f000 0xfdffff8803ffe301 0xfeffffc401fff180

def z953 : W := mkw 0xe011007dd4101fbc 0xf008803eea080fde 0x0600007ffc001ffe 0x8300003ffe000fff

def z954 : W := mkw 0x104cc5822fce2162 0x082662c117e710b1 0xfbffcf807ffe6027 0x7dffe7c03fff3013

def z955 : W := mkw 0x51eeff836fefe177 0x28f77fc1b7f7f0bb 0xfbffff81ffffe03f 0x7dffffc0fffff01f

def z956 : W := mkw 0x4038285143015414 0x201c1428a180aa0a 0xff783c79e383ff3f 0xffbc1e3cf1c1ff9f

def z957 : W := mkw 0xc05d807c03595e94 0xe02ec03e01acaf4a 0x7dffc07e03fd9fd9 0xbeffe03f01fecfec

def z958 : W := mkw 0x02f7ff7ff8100a00 0x817bffbffc080500 0xfafffffffe701800 0xfd7fffffff380c00

def z959 : W := mkw 0x004e928003ea8000 0x0027494001f54000 0xd9ff338002f38001 0x6cff99c00179c000

def z960 : W := mkw 0x004c800003480000 0x0026400001a40000 0x79ffc01e03fc0001 0xbcffe00f01fe0000

def z961 : W := mkw 0x8011007c00101e80 0xc008803e00080f40 0x2c00007e01001fc1 0x9600003f00800fe0

def z962 : W := mkw 0x805d807c03581e80 0xc02ec03e01ac0f40 0x7dffc07e03ff9ff9 0xbeffe03f01ffcffc

def z963 : W := mkw 0x03f7ff7ff84c2001 0x01fbffbffc261000 0xfafffffffc0c0000 0xfd7ffffffe060000

def z964 : W := mkw 0x02f7ff7ff8000000 0x017bffbffc000000 0x70fffffffc000000 0x387ffffffe000000

def z965 : W := mkw 0xa011007c90101e88 0xd008803e48080f44 0x0400007f80001fd8 0x8200003fc0000fec

def z966 : W := mkw 0x03f7ff7ff8688001 0x01fbffbffc344000 0xfafffffffc700000 0xfd7ffffffe380000

def z967 : W := mkw 0xa108008007ffffa9 0xd084004003ffffd4 0x0500000003fffff9 0x0280000001fffffc

def z968 : W := mkw 0x02e6ff02b8000000 0x01737f815c000000 0xf8ffff801c000000 0x7c7fffc00e000000

def z969 : W := mkw 0x01eeff8003efe001 0x00f77fc001f7f000 0xe9ffcf8001fe6001 0x74ffe7c000ff3000

def z970 : W := mkw 0x006ca80003494000 0x0036540001a4a000 0x79fff00003fd8001 0x3cfff80001fec000

def z971 : W := mkw 0x21eeff8097efe129 0x10f77fc04bf7f094 0xffffff899fffe339 0xffffffc4cffff19c

def z972 : W := mkw 0x6108008007ffff3d 0xb084004003ffff9e 0x0500000003ffff3f 0x0280000001ffff9f

def z973 : W := mkw 0x01eeff000369c001 0x00f77f8001b4e000 0x30fffc0002718000 0x187ffe000138c000

def z974 : W := mkw 0x22f7ff7ff8308a08 0x917bffbffc184504 0xfffffffffef19b19 0xffffffffff78cd8c

def z975 : W := mkw 0x42f7ff7ff8015414 0x217bffbffc00aa0a 0xfefffffffc03fc3e 0xff7ffffffe01fe1f

def z976 : W := mkw 0x41eeba014369c015 0x20f75d00a1b4e00a 0x10ff300182718018 0x087f9800c138c00c

def z977 : W := mkw 0x000312a890a28000 0x0001895448514000 0xdf8733e99ef39839 0xefc399f4cf79cc1c

def z978 : W := mkw 0xc019007c03115e94 0xe00c803e0188af4a 0x0400007e0303ffff 0x8200003f0181ffff

def z979 : W := mkw 0x02d7d77ff8000000 0x016bebbffc000000 0x7affc3fffc000000 0xbd7fe1fffe000000

def z980 : W := mkw 0x0008000003000000 0x0004000001800000 0x79ff000003f00001 0x3cff800001f80000

def z981 : W := mkw 0x0055c57e28000000 0x002ae2bf14000000 0x78ffc3fe1c000000 0xbc7fe1ff0e000000

def z982 : W := mkw 0x11eeff822fefe163 0x08f77fc117f7f0b1 0xffffff8e1fffe3e1 0xffffffc70ffff1f0

def z983 : W := mkw 0x004c808003ca0000 0x0026404001e50000 0xf9ffc38003fe0001 0x7cffe1c001ff0000

def z984 : W := mkw 0x11eeff822fefe163 0x08f77fc117f7f0b1 0xf9ffff801fffe001 0x7cffffc00ffff000

def z985 : W := mkw 0x0028280003014000 0x001414000180a000 0xf9ff3c0003f3e001 0x7cff9e0001f9f000

def z986 : W := mkw 0x11eeba8007efe163 0x08f75d4003f7f0b1 0x15ff300003ffe7e7 0x0aff980001fff3f3

def z987 : W := mkw 0x0011007c00100a00 0x8008803e00080500 0x0400007e00001b00 0x8200003f00000d80

def z988 : W := mkw 0x0046928000a28000 0x0023494000514000 0xf9fff38002f38001 0x7cfff9c00179c000

def z989 : W := mkw 0x00333a79d0000000 0x00199d3ce8000000 0xdaff33e99c000000 0xed7f99f4ce000000

def z990 : W := mkw 0x02e6ff03f8000000 0x01737f81fc000000 0x92ff3f81fc000000 0x497f9fc0fe000000

def z991 : W := mkw 0x22f7ff7ff8308a08 0x917bffbffc184504 0xfefffffffe739839 0xff7fffffff39cc1c

def z992 : W := mkw 0xa011007c94101fa8 0xd008803e4a080fd4 0x060000699c001b38 0x83000034ce000d9c

def z993 : W := mkw 0x2008008007b29f28 0x9004004003d94f94 0x0500000003f39f39 0x0280000001f9cf9c

def z994 : W := mkw 0x82f7ff7ff8100a80 0xc17bffbffc080540 0xfafffffffc0003c0 0xfd7ffffffe0001e0

def z995 : W := mkw 0x002a3a8003a3c000 0x00151d4001d1e000 0xd9ff338002f38001 0x6cff99c00179c000

def z996 : W := mkw 0x02f7ff7ff8042000 0x017bffbffc021000 0xfafffffffd0c6000 0xfd7ffffffe863000

def z997 : W := mkw 0x901145fe2c963fe2 0xc808a2ff164b1ff1 0x86000ffe7c027fe6 0xc30007ff3e013ff3

def z998 : W := mkw 0x100045822c862162 0x080022c1164310b1 0xef00cf9e7f8fffff 0xf78067cf3fc7ffff

def z999 : W := mkw 0x404c800003495414 0x2026400001a4aa0a 0x7dffc00003fffc3f 0x3effe00001fffe1f

def z1000 : W := mkw 0x8211007f68101e80 0xc108803fb4080f40 0x0400007e60001fc0 0x8200003f30000fe0

def z1001 : W := mkw 0x602a3a81d7a3c13c 0x30151d40ebd1e09e 0xfbff3f81fff3e03f 0x7dff9fc0fff9f01f

def z1002 : W := mkw 0x03eeba01d369c001 0x01f75d00e9b4e000 0x10ff300182718000 0x087f9800c138c000

def z1003 : W := mkw 0x00e6ff0228000000 0x00737f8114000000 0xfaffff807c000000 0x7d7fffc03e000000

def z1004 : W := mkw 0xc05d807c03595e94 0xe02ec03e01acaf4a 0xffffcc7e63ffffff 0xffffe63f31ffffff

def z1005 : W := mkw 0x01eeff8003efe001 0x00f77fc001f7f000 0x71ffff8003fde000 0x38ffffc001fef000

def z1006 : W := mkw 0x01e6ff0000688001 0x00f37f8000344000 0xf8ffff8000700000 0x7c7fffc000380000

def z1007 : W := mkw 0x01eeba000369c001 0x00f75d0001b4e000 0x59ff300002f18001 0x2cff98000178c000

def z1008 : W := mkw 0x01eeff822fefe121 0x00f77fc117f7f090 0xffffff9e7fffe321 0xffffffcf3ffff190

def z1009 : W := mkw 0x21eeba009369c009 0x10f75d0049b4e004 0x10ff300182718018 0x087f9800c138c00c

def z1010 : W := mkw 0x02f7ff7ff8000000 0x017bffbffc000000 0xfefffffffd000401 0xff7ffffffe800200

def z1011 : W := mkw 0x01eeff8003efe001 0x00f77fc001f7f000 0xfdffffe003fff801 0xfefffff001fffc00

def z1012 : W := mkw 0x805d807c03581e80 0xc02ec03e01ac0f40 0xfdffcc7e03fe7fc1 0xfeffe63f01ff3fe0

def z1013 : W := mkw 0x805d807c03581e80 0xc02ec03e01ac0f40 0xffffc3fe1ffc1fc1 0xffffe1ff0ffe0fe0

def z1014 : W := mkw 0x100045822c862162 0x080022c1164310b1 0xeb00cf9e7d8c67c6 0xf58067cf3ec633e3

def z1015 : W := mkw 0xc038285543015494 0x601c142aa180aa4a 0xbe783c77e303fcff 0xdf3c1e3bf181fe7f

def z1016 : W := mkw 0x02b27f53f8000000 0x01593fa9fc000000 0xa2783f91fc000000 0x513c1fc8fe000000

def z1017 : W := mkw 0x41eeff8143efe015 0x20f77fc0a1f7f00a 0xf9ffff8183ffe019 0x7cffffc0c1fff00c

def z1018 : W := mkw 0x100045822c862162 0x080022c1164310b1 0xff00cffe7f8e7fe7 0xff8067ff3fc73ff3

def z1019 : W := mkw 0xc2ffba7dd3595e94 0xe17fdd3ee9acaf4a 0x10ff306182719818 0x087f9830c138cc0c

def z1020 : W := mkw 0x200312a894b28b28 0x900189544a594594 0x108733e19e719818 0x084399f0cf38cc0c

def z1021 : W := mkw 0x1008008007863562 0x0804004003c31ab1 0x05000000038e7fe7 0x0280000001c73ff3

def z1022 : W := mkw 0x01eeff00036de001 0x00f77f8001b6f000 0xb8fffc00037fe001 0x5c7ffe0001bff000

def z1023 : W := mkw 0x321145fffc962b6a 0x9908a2fffe4b15b5 0xef00cffffd8e7fff 0xf78067fffec73fff

def z1024 : W := mkw 0x82aa7f03fb581e80 0xc1553f81fdac0f40 0x87003f81fffc1fc1 0x43801fc0fffe0fe0

def z1025 : W := mkw 0x004c800003480000 0x0026400001a40000 0x38ff000003700001 0x1c7f800001b80000

def z1026 : W := mkw 0x22f4edd76cb28b28 0x917a76ebb6594594 0x2578cc1662f39b39 0x12bc660b3179cd9c

def z1027 : W := mkw 0x42aa7f03fb015414 0x21553f81fd80aa0a 0x86003f81ff03fc3f 0x43001fc0ff81fe1f

def z1028 : W := mkw 0x01eca80003494001 0x00f6540001a4a000 0x79ffc00003fc0001 0x3cffe00001fe0000

def z1029 : W := mkw 0x006ca80003494000 0x0036540001a4a000 0xb8ff3c000373e001 0x5c7f9e0001b9f000

def z1030 : W := mkw 0x004e920003480000 0x0027490001a40000 0xf9fff38003fc0001 0x7cfff9c001fe0000

def z1031 : W := mkw 0x8011007c00101e80 0xc008803e00080f40 0x4d00007e00801fc1 0xa680003f00400fe0

def z1032 : W := mkw 0x200312a894b28b28 0x900189544a594594 0x578733e99ef19b38 0xabc399f4cf78cd9c

def z1033 : W := mkw 0x4038285143015414 0x201c1428a180aa0a 0xba783c61e303f83f 0x5d3c1e30f181fc1f

def z1034 : W := mkw 0x004cc50003480000 0x0026628001a40000 0xf9ffcf8003fc0001 0x7cffe7c001fe0000

def z1035 : W := mkw 0x200312a894b28b28 0x900189544a594594 0xdb8733e99ef19b18 0xedc399f4cf78cd8c

def z1036 : W := mkw 0x01eeff8007efe121 0x00f77fc003f7f090 0xffffffe99ffffb39 0xfffffff4cffffd9c

def z1037 : W := mkw 0x805d807c03581e80 0xc02ec03e01ac0f40 0xffffc07e03fe1fe1 0xffffe03f01ff0ff0

def z1038 : W := mkw 0xb008008007febfea 0xd804004003ff5ff5 0x0500000003ffffff 0x0280000001ffffff

def z1039 : W := mkw 0x200312a894b28b28 0x900189544a594594 0x5d8733e99ef19b19 0xaec399f4cf78cd8c

def z1040 : W := mkw 0x02b27f53f8000000 0x01593fa9fc000000 0xfa78fffffc000000 0xfd3c7ffffe000000

def z1041 : W := mkw 0x2011007894101f28 0x9008803c4a080f94 0x060000799c001f38 0x8300003cce000f9c

def z1042 : W := mkw 0x8055807c00581e80 0xc02ac03e002c0f40 0x0400c07e000c1fc0 0x8200603f00060fe0

def z1043 : W := mkw 0x01eeff8007efe121 0x00f77fc003f7f090 0xffffff987fffe727 0xffffffcc3ffff393

def z1044 : W := mkw 0x8045802c00580a80 0xc022c016002c0540 0x79ffc00e00fc03c0 0x3cffe007007e01e0

def z1045 : W := mkw 0x804d802c03580a80 0xc026c01601ac0540 0x61ffc00e01fc03c0 0x30ffe00700fe01e0

def z1046 : W := mkw 0x104cc5822fce2162 0x082662c117e710b1 0x79ffc38e1ffc03c1 0x3cffe1c70ffe01e0

def z1047 : W := mkw 0x42f7ff7ff8001414 0x217bffbffc000a0a 0xfafffffffc001818 0xfd7ffffffe000c0c

def z1048 : W := mkw 0x01eeff8003efe001 0x00f77fc001f7f000 0x51fff38003ffe001 0x28fff9c001fff000

def z1049 : W := mkw 0x00e6ba8000a28000 0x00735d4000514000 0xd9ff338002f38001 0x6cff99c00179c000

def z1050 : W := mkw 0x01eeff8003efe001 0x00f77fc001f7f000 0x10ff338002718000 0x087f99c00138c000

def z1051 : W := mkw 0x104cc5022b4c2042 0x0826628115a61021 0x79ffcc1663fc64c7 0x3cffe60b31fe3263

def z1052 : W := mkw 0x13eeff83ffefe163 0x09f77fc1fff7f0b1 0xfbffff81ffffe027 0x7dffffc0fffff013

def z1053 : W := mkw 0x02b27f53f8000000 0x01593fa9fc000000 0x92783fe1fc000000 0x493c1ff0fe000000

def z1054 : W := mkw 0x02f7ff7ff8000000 0x017bffbffc000000 0xfefffffffc000426 0xff7ffffffe000213

def z1055 : W := mkw 0x01eeff8003efe001 0x00f77fc001f7f000 0x91ff3f8003ffe001 0x48ff9fc001fff000

def z1056 : W := mkw 0x11eeff822befe043 0x08f77fc115f7f021 0xfbffff9e7fffe4c7 0xfdffffcf3ffff263

def z1057 : W := mkw 0x004c800003481400 0x0026400001a40a00 0x7dffc00003fc1c01 0x3effe00001fe0e00

def z1058 : W := mkw 0x11eeff822befe043 0x08f77fc115f7f021 0xfdffff9e63ffe7c7 0xfeffffcf31fff3e3

def z1059 : W := mkw 0x2008008007b3cb28 0x9004004003d9e594 0x0500000003f3fb39 0x0280000001f9fd9c

def z1060 : W := mkw 0x0000450228000000 0x0000228114000000 0xef00cf9e7d8e67e7 0xf78067cf3ec733f3

def z1061 : W := mkw 0x21eeff8093efe009 0x10f77fc049f7f004 0xf9ffff8183ffe019 0x7cffffc0c1fff00c

def z1062 : W := mkw 0x02f7ff7ff8000000 0x017bffbffc000000 0xfbfffffffd8c0001 0xfdfffffffec60000

def z1063 : W := mkw 0x4030285140015414 0x20181428a000aa0a 0xbe783c71e003fc3e 0xdf3c1e38f001fe1f

def z1064 : W := mkw 0x01eeff8003efe001 0x00f77fc001f7f000 0x79ffcf8003fc6001 0x3cffe7c001fe3000

def z1065 : W := mkw 0x603b3af9d7b3df3c 0xb01d9d7cebd9ef9e 0x61ff0f987df06706 0x30ff87cc3ef83383

def z1066 : W := mkw 0x004e928007ea8120 0x0027494003f54090 0xfffff39e1fff87e1 0xfffff9cf0fffc3f0

def z1067 : W := mkw 0x0030285140000000 0x00181428a0000000 0xfa783ff9fc000000 0xfd3c1ffcfe000000

def z1068 : W := mkw 0x41eeff8143efe015 0x20f77fc0a1f7f00a 0xffffff91e3ffe43f 0xffffffc8f1fff21f

def z1069 : W := mkw 0x00eeba0003480000 0x00775d0001a40000 0x79fff00003fc0001 0x3cfff80001fe0000

def z1070 : W := mkw 0x00eced0003480000 0x0076768001a40000 0x79ffcc0003fc0001 0x3cffe60001fe0000

def z1071 : W := mkw 0x00f7ff79d0000000 0x007bffbce8000000 0xfafffff9fc000000 0xfd7ffffcfe000000

def z1072 : W := mkw 0x004c800003480000 0x0026400001a40000 0x7dffc00803fc0301 0xbeffe00401fe0180

def z1073 : W := mkw 0x2108008007efe129 0x1084004003f7f094 0x0100000003ffe039 0x0080000001fff01c

def z1074 : W := mkw 0x51eeff836fefe177 0x28f77fc1b7f7f0bb 0xffffff9fffffe7ff 0xffffffcffffff3ff

def z1075 : W := mkw 0x82f7ff7ff8001480 0x417bffbffc000a40 0xfafffffffc0004c0 0xfd7ffffffe000260

def z1076 : W := mkw 0x6008008007b3df3c 0xb004004003d9ef9e 0x0500000002f39b39 0x028000000179cd9c

def z1077 : W := mkw 0x03f7ff7ff821c001 0x01fbffbffc10e000 0xfafffffffc018000 0xfd7ffffffe00c000

def z1078 : W := mkw 0x901100fc04963fe2 0xc808807e024b1ff1 0x0500007e018e7fe7 0x8280003f00c73ff3

def z1079 : W := mkw 0xc011007d40101e94 0xe008803ea0080f4a 0x0000006180001818 0x00000030c0000c0c

def z1080 : W := mkw 0x00306d5368000000 0x001836a9b4000000 0xba783ff1fc000000 0xdd3c1ff8fe000000

def z1081 : W := mkw 0x11eeff8007efe163 0x08f77fc003f7f0b1 0xf9ffff8003ffe027 0x7cffffc001fff013

def z1082 : W := mkw 0x014c808003eea001 0x00a6404001f75000 0x79ffc00003fc0001 0x3cffe00001fe0000

def z1083 : W := mkw 0x004cc58003ce2000 0x002662c001e71000 0x79ffc38003fc0001 0x3cffe1c001fe0000

def z1084 : W := mkw 0x02f7ff7ff8000000 0x017bffbffc000000 0xfaffffe1fc000000 0x7d7ffff0fe000000

def z1085 : W := mkw 0x2211007dd4100b28 0x9108803eea080594 0x060000699c001b38 0x83000034ce000d9c

def z1086 : W := mkw 0x016ca88003efe001 0x00b6544001f7f000 0xf9fffc0003ffe001 0x7cfffe0001fff000

def z1087 : W := mkw 0x01eeff822befe001 0x00f77fc115f7f000 0xffffff9e7fffe7c1 0xffffffcf3ffff3e0

def z1088 : W := mkw 0x004c800003480000 0x0026400001a40000 0xfffff06183ff9839 0xfffff830c1ffcc1c

def z1089 : W := mkw 0x800b122893581e80 0xc005891449ac0f40 0xdf8733e99ffc1fc1 0xefc399f4cffe0fe0

def z1090 : W := mkw 0x9008008007de3fe2 0xc804004003ef1ff1 0x0500000003fc1fc1 0x0280000001fe0fe0

def z1091 : W := mkw 0x204e928097ea8128 0x102749404bf54094 0xfbfff3819fff8039 0x7dfff9c0cfffc01c

def z1092 : W := mkw 0x00eeff8003a3c000 0x00777fc001d1e000 0xf9ffff8003f3e001 0x7cffffc001f9f000

def z1093 : W := mkw 0x0018005003001400 0x000c002801800a00 0xbe783c71e303fc3f 0xdf3c1e38f181fe1f

def z1094 : W := mkw 0xc038285143495494 0x601c1428a1a4aa4a 0xbe783c71e30ffcff 0xdf3c1e38f187fe7f

def z1095 : W := mkw 0x200312a894b28b28 0x900189544a594594 0xff8733f99ff39f39 0xffc399fccff9cf9c

def z1096 : W := mkw 0x61eeff81d7efe13d 0x30f77fc0ebf7f09e 0xfbffff81ffffe03f 0x7dffffc0fffff01f

def z1097 : W := mkw 0x01eeff8003efe001 0x00f77fc001f7f000 0x41ffc38000fc0000 0x20ffe1c0007e0000

def z1098 : W := mkw 0x02f7ff7ff8000000 0x017bffbffc000000 0x78fff3ff9c000000 0xbc7ff9ffce000000

def z1099 : W := mkw 0x800845022b581e80 0xc004228115ac0f40 0xef00cf9e7ffc1fc1 0xf78067cf3ffe0fe0

def z1100 : W := mkw 0xe07fba7dd379de9c 0xf03fdd3ee9bcef4e 0x10ff306182719818 0x087f9830c138cc0c

def z1101 : W := mkw 0x51a27f836ca7e177 0x28d13fc1b653f0bb 0x82003f81fc03e03e 0x41001fc0fe01f01f

def z1102 : W := mkw 0x1000450228042042 0x0800228114021021 0xef00cf9e7d8c67c7 0xf78067cf3ec633e3

def z1103 : W := mkw 0x82cfd72ebb581e80 0xc167eb975dac0f40 0x4587c38e1ffc1fc1 0x22c3e1c70ffe0fe0

def z1104 : W := mkw 0x4038285143015414 0x201c1428a180aa0a 0x34783c71e303fc3f 0x1a3c1e38f181fe1f

def z1105 : W := mkw 0x01eeff8003efe001 0x00f77fc001f7f000 0xf9ffff9063ffe407 0x7cffffc831fff203

def z1106 : W := mkw 0xc05d807c03595e94 0xe02ec03e01acaf4a 0xfffff07f83ffffff 0xfffff83fc1ffffff

def z1107 : W := mkw 0x0057d77eb8000000 0x002bebbf5c000000 0xfafffffffc000000 0xfd7ffffffe000000

def z1108 : W := mkw 0x00e6ff0000480000 0x00737f8000240000 0xf9ffff8000fc0000 0x7cffffc0007e0000

def z1109 : W := mkw 0x01eeba000369c001 0x00f75d0001b4e000 0x9eff306182739839 0xcf7f9830c139cc1c

def z1110 : W := mkw 0x205580fc04b28b28 0x902ac07e02594594 0x7dffc07e02f39b39 0xbeffe03f0179cd9c

def z1111 : W := mkw 0x31eeff82bfefe16b 0x18f77fc15ff7f0b5 0xfbffff81ffffe03f 0x7dffffc0fffff01f

def z1112 : W := mkw 0x8011007c00101e80 0xc008803e00080f40 0x0600007f80001ff8 0x8300003fc0000ffc

def z1113 : W := mkw 0x200312a894b28b28 0x900189544a594594 0x968733e99e739b38 0xcb4399f4cf39cd9c

def z1114 : W := mkw 0x8011007c00101e80 0xc008803e00080f40 0x0400006000001fc0 0x0200003000000fe0

def z1115 : W := mkw 0x8211007eb8101e80 0xc108803f5c080f40 0x0400007e1c001fc0 0x8200003f0e000fe0

def z1116 : W := mkw 0x01eeff8003efe001 0x00f77fc001f7f000 0xfbffff8183ffe039 0x7dffffc0c1fff01c

def z1117 : W := mkw 0x0057927c90000000 0x002bc93e48000000 0x78ffc3fe1c000000 0xbc7fe1ff0e000000

def z1118 : W := mkw 0x02f7ff7ff8000000 0x017bffbffc000000 0x10ff33e19c000000 0x087f99f0ce000000

def z1119 : W := mkw 0x203028d144b28b28 0x90181468a2594594 0xbf783c71e2f39b39 0xdfbc1e38f179cd9c

def z1120 : W := mkw 0x12f7ff7ff8042042 0x097bffbffc021021 0xfafffffffc0c00c0 0xfd7ffffffe060060

def z1121 : W := mkw 0x82f7ff7ff8580a80 0xc17bffbffc2c0540 0xfffffffffdfc07c1 0xfffffffffefe03e0

def z1122 : W := mkw 0x82f7ff7ff8581e80 0xc17bffbffc2c0f40 0xfffffffffcfc1fc0 0xfffffffffe7e0fe0

def z1123 : W := mkw 0x01eeff822befe001 0x00f77fc115f7f000 0xffffff9e7fffe427 0xffffffcf3ffff213

def z1124 : W := mkw 0x01eeff8003efe001 0x00f77fc001f7f000 0x31fffc0003ffe001 0x18fffe0001fff000

def z1125 : W := mkw 0x0008000003000000 0x0004000001800000 0x3c78001003000401 0x9e3c000801800200

def z1126 : W := mkw 0xa011007c90101e88 0xd008803e48080f44 0x0000006180001818 0x00000030c0000c0c

def z1127 : W := mkw 0x01eeff8003efe001 0x00f77fc001f7f000 0xd9ff3f8002f3e001 0x6cff9fc00179f000

def z1128 : W := mkw 0x8055807c00580a80 0xc02ac03e002c0540 0x61ffc01e00fc03c0 0x30ffe00f007e01e0

def z1129 : W := mkw 0x8011007c00101e80 0xc008803e00080f40 0x0000001e000007c0 0x0000000f000003e0

def z1130 : W := mkw 0x014c80000369c001 0x00a6400001b4e000 0x79ffc00003fd8001 0x3cffe00001fec000

def z1131 : W := mkw 0x2211007ff8100a08 0x9108803ffc080504 0x0200007ffc001818 0x8100003ffe000c0c

def z1132 : W := mkw 0x03eeff83fbefe001 0x01f77fc1fdf7f000 0xfbffff9fffffe001 0xfdffffcffffff000

def z1133 : W := mkw 0x805d807c03581e80 0xc02ec03e01ac0f40 0x55ffc07e02fc1fc0 0xaaffe03f017e0fe0

def z1134 : W := mkw 0x02f7ff7ff8000000 0x017bffbffc000000 0xfafffffffd006406 0xfd7ffffffe803203

def z1135 : W := mkw 0x00eeff0003480000 0x00777f8001a40000 0xf8ffff8002700000 0x7c7fffc001380000

def z1136 : W := mkw 0x200312a894b28b28 0x900189544a594594 0xdf8733f9fef39f3f 0xefc399fcff79cf9f

def z1137 : W := mkw 0x00e7ff2ab8000000 0x0073ff955c000000 0xfafffffffc000000 0xfd7ffffffe000000

def z1138 : W := mkw 0x004c800003480000 0x0026400001a40000 0x7dffc06003fc1801 0xbeffe03001fe0c00

def z1139 : W := mkw 0x901145fe2c963fe2 0xc808a2ff164b1ff1 0x4500c3fe1c8c1fc0 0xa28061ff0e460fe0

def z1140 : W := mkw 0x12f7ff7ff8000042 0x097bffbffc000021 0xfafffffffc0004c6 0xfd7ffffffe000263

def z1141 : W := mkw 0x03eeff81d3efe001 0x01f77fc0e9f7f000 0xf9ffff8183ffe001 0x7cffffc0c1fff000

def z1142 : W := mkw 0x02f7ff7ff8000000 0x017bffbffc000000 0x92ff3ffffc000000 0xc97f9ffffe000000

def z1143 : W := mkw 0x01eeba00036de001 0x00f75d0001b6f000 0x10ff3000037de000 0x087f980001bef000

def z1144 : W := mkw 0x4038285143015414 0x201c1428a180aa0a 0xff78fc71e38ffc3f 0xffbc7e38f1c7fe1f

def z1145 : W := mkw 0x00e6ff0228000000 0x00737f8114000000 0xf8ffff8e1c000000 0x7c7fffc70e000000

def z1146 : W := mkw 0x82f7ff7ff8480080 0x417bffbffc240040 0xfafffffffc0c00c0 0xfd7ffffffe060060

def z1147 : W := mkw 0x805d807c03581e80 0xc02ec03e01ac0f40 0xffffcc7e63fc1fc1 0xffffe63f31fe0fe0

def z1148 : W := mkw 0x400b122893015414 0x200589144980aa0a 0xde8733e99f03fc3f 0xef4399f4cf81fe1f

def z1149 : W := mkw 0x0013127890000000 0x0009893c48000000 0xfaff33f99c000000 0xfd7f99fcce000000

def z1150 : W := mkw 0x51fced536b4d7457 0x28fe76a9b5a6ba2b 0x2078cc16610c64c6 0x103c660b30863263

def z1151 : W := mkw 0x01eced8003cf6001 0x00f676c001e7b000 0xf9ffcf8003fe6001 0x7cffe7c001ff3000

def z1152 : W := mkw 0x804d802c03580a80 0xc026c01601ac0540 0x7dffc01e03fc07c1 0xbeffe00f01fe03e0

def z1153 : W := mkw 0x8011007d40101e80 0xc008803ea0080f40 0x0600007fe0001fc0 0x8300003ff0000fe0

def z1154 : W := mkw 0x102a7f822fa7e162 0x08153fc117d3f0b1 0xffffff9e7fffe7e7 0xffffffcf3ffff3f3

def z1155 : W := mkw 0x104ed7822feea162 0x08276bc117f750b1 0xffffff9e7fffe7e7 0xffffffcf3ffff3f3

def z1156 : W := mkw 0x02f7ff7ff8000000 0x017bffbffc000000 0x52fff3fffc000000 0xa97ff9fffe000000

def z1157 : W := mkw 0x0002128004a28120 0x0001094002514090 0xdf8733e99ef39b39 0xefc399f4cf79cd9c

def z1158 : W := mkw 0x51eeff8007eff577 0x28f77fc003f7fabb 0xfdffff8003ffffff 0x7effffc001ffffff

def z1159 : W := mkw 0x01eeff00036de001 0x00f77f8001b6f000 0x10fff000027d8000 0x087ff800013ec000

def z1160 : W := mkw 0x200312a894b28b28 0x900189544a594594 0xdb8733e19ef39839 0x6dc399f0cf79cc1c

def z1161 : W := mkw 0x100045822c862162 0x080022c1164310b1 0xe300cf9e7d8e67e6 0x718067cf3ec733f3

def z1162 : W := mkw 0x006ca80003494000 0x0036540001a4a000 0x10ff300002718000 0x087f98000138c000

def z1163 : W := mkw 0x12f7ff7ff8042042 0x097bffbffc021021 0xfffffffffd8c67c7 0xfffffffffec633e3

def z1164 : W := mkw 0x02f7ff7ff8000000 0x017bffbffc000000 0xfffffffffc800301 0xfffffffffe400180

def z1165 : W := mkw 0x004c800003480000 0x0026400001a40000 0x11ff000003fc0001 0x08ff800001fe0000

def z1166 : W := mkw 0x8011007c90101e80 0xc008803e48080f40 0x0600007f9c001fc0 0x8300003fce000fe0

def z1167 : W := mkw 0x2211007dd0100a08 0x9108803ee8080504 0x0000006180001818 0x00000030c0000c0c

def z1168 : W := mkw 0x00223a8000a28000 0x00111d4000514000 0xf9ff3f8002f38001 0x7cff9fc00179c000

def z1169 : W := mkw 0x004c800003480000 0x0026400001a40000 0xf9fff00003ff8001 0x7cfff80001ffc000

def z1170 : W := mkw 0x200312a894b28b28 0x900189544a594594 0xff87f3ff9ef39b39 0xffc3f9ffcf79cd9c

def z1171 : W := mkw 0x2003122890308a08 0x9001891448184504 0x928733e19e719818 0x494399f0cf38cc0c

def z1172 : W := mkw 0x02f4ed5768000000 0x017a76abb4000000 0xa278cf967c000000 0x513c67cb3e000000

def z1173 : W := mkw 0x01eeff822befe001 0x00f77fc115f7f000 0xf9ffff9663ffe001 0x7cffffcb31fff000

def z1174 : W := mkw 0x200312a894b28b28 0x900189544a594594 0xdf8733e99fff9ff9 0xefc399f4cfffcffc

def z1175 : W := mkw 0x805d807c03581e80 0xc02ec03e01ac0f40 0x7dfff07f83fd9fd9 0xbefff83fc1fecfec

def z1176 : W := mkw 0x104c808007ce2162 0x0826404003e710b1 0x7dffc00003fe67e7 0x3effe00001ff33f3

def z1177 : W := mkw 0x805d807c03580a80 0xc02ec03e01ac0540 0x79ffc07e03fc03c1 0xbcffe03f01fe01e0

def z1178 : W := mkw 0x114c808007efe163 0x08a6404003f7f0b1 0x7dffc01e03ffe7e7 0xbeffe00f01fff3f3

def z1179 : W := mkw 0x0003122890100a00 0x8001891448080500 0xdf8733e99ef39b39 0xefc399f4cf79cd9c

def z1180 : W := mkw 0x006ced8003cf6000 0x003676c001e7b000 0xf9ffff8003ffe001 0x7cffffc001fff000

def z1181 : W := mkw 0x01eeba000369c001 0x00f75d0001b4e000 0x10ff306182719818 0x087f9830c138cc0c

def z1182 : W := mkw 0x02b37f7bf8000000 0x0159bfbdfc000000 0xfaff3ff9fc000000 0xfd7f9ffcfe000000

def z1183 : W := mkw 0x805d807c03581e80 0xc02ec03e01ac0f40 0x79ffc07e02fc1bc0 0xbcffe03f017e0de0

def z1184 : W := mkw 0x11eced022b4d6043 0x08f6768115a6b021 0x7dffcc1e63fc67c7 0xbeffe60f31fe33e3

def z1185 : W := mkw 0x03eeff03fb69c001 0x01f77f81fdb4e000 0x92ff3f81fe718000 0x497f9fc0ff38c000

def z1186 : W := mkw 0x114cc5822fefe163 0x08a662c117f7f0b1 0xffffcf9e7fffe7e7 0xffffe7cf3ffff3f3

def z1187 : W := mkw 0x11a27f822ca7e163 0x08d13fc11653f0b1 0x80003f801c03e000 0x40001fc00e01f000

def z1188 : W := mkw 0x00306d5368000000 0x001836a9b4000000 0xea78cf9e7c000000 0xf53c67cf3e000000

def z1189 : W := mkw 0x5008008007877576 0x2804004003c3babb 0x05000000018e67e7 0x0280000000c733f3

def z1190 : W := mkw 0x21eeff8097efe129 0x10f77fc04bf7f094 0xffffffe19ffff839 0xfffffff0cffffc1c

def z1191 : W := mkw 0x805d807c03581e80 0xc02ec03e01ac0f40 0x7dffc07e03fe7fe7 0xbeffe03f01ff3ff3

def z1192 : W := mkw 0x2003122890308a08 0x9001891448184504 0xdf8733e99ef19b19 0xefc399f4cf78cd8c

def z1193 : W := mkw 0xa211007ffc101fa8 0xd108803ffe080fd4 0x0600007ffc001ff8 0x8300003ffe000ffc

def z1194 : W := mkw 0x4038285143015414 0x201c1428a180aa0a 0x96783c61e303fc3f 0x4b3c1e30f181fe1f

def z1195 : W := mkw 0x81eeff8003eff481 0x40f77fc001f7fa40 0xf9ffff8003ffe4c1 0x7cffffc001fff260

def z1196 : W := mkw 0x01eced00034d6001 0x00f6768001a6b000 0x61ffcc0001fc6000 0x30ffe60000fe3000

def z1197 : W := mkw 0x02d7d77eb8000000 0x016bebbf5c000000 0xfaffcffe7c000000 0xfd7fe7ff3e000000

def z1198 : W := mkw 0x805d807c03581e80 0xc02ec03e01ac0f40 0x79ffc01e03fc07c1 0x3cffe00f01fe03e0

def z1199 : W := mkw 0x70227f83fca7e17e 0x38113fc1fe53f0bf 0x82003f81fc03e03e 0x41001fc0fe01f01f

def z1200 : W := mkw 0x104c80022f480162 0x0826400117a400b1 0x7fffc01e7ffc07e7 0xbfffe00f3ffe03f3

def z1201 : W := mkw 0x21eeba8097ebc129 0x10f75d404bf5e094 0x92ff33819e738038 0x497f99c0cf39c01c

def z1202 : W := mkw 0x01eeff00034d6001 0x00f77f8001a6b000 0xf9ffff8003fc6001 0x7cffffc001fe3000

def z1203 : W := mkw 0x401212d140a29414 0x20090968a0514a0a 0xdf8733f1e2f39c3f 0xefc399f8f179ce1f

def z1204 : W := mkw 0x01eeff8003efe001 0x00f77fc001f7f000 0xf9ffffe183fff819 0x7cfffff0c1fffc0c

def z1205 : W := mkw 0x01eeff8003efe001 0x00f77fc001f7f000 0xffffff9e63ffe7e7 0xffffffcf31fff3f3

def z1206 : W := mkw 0x2003122890308a08 0x9001891448184504 0xde8733e99e739839 0xef4399f4cf39cc1c

def z1207 : W := mkw 0x41eeff8143efe015 0x20f77fc0a1f7f00a 0xf9ffff8063ffe007 0x7cffffc031fff003

def z1208 : W := mkw 0x004c808003ea8000 0x0026404001f54000 0x79ffc00003ff8001 0x3cffe00001ffc000

def z1209 : W := mkw 0x00f7ff7c90000000 0x007bffbe48000000 0xfaffffff9c000000 0xfd7fffffce000000

def z1210 : W := mkw 0xc05d807d43581e94 0xe02ec03ea1ac0f4a 0xfffff07fe3ff9fff 0xfffff83ff1ffcfff

def z1211 : W := mkw 0x11eeff822fefe163 0x08f77fc117f7f0b1 0xf9ffff9e7fffe7c7 0x7cffffcf3ffff3e3

def z1212 : W := mkw 0x12f7ff7ff8042042 0x097bffbffc021021 0xfafffffffc006006 0xfd7ffffffe003003

def z1213 : W := mkw 0xa01100fc94921fa8 0xd008807e4a490fd4 0xef00c3ff9d8e1ff9 0xf78061ffcec70ffc

def z1214 : W := mkw 0x01eeba8003ebc001 0x00f75d4001f5e000 0xf9ff3f8003f3e001 0x7cff9fc001f9f000

def z1215 : W := mkw 0x00e7ba2890000000 0x0073dd1448000000 0xdaff33e99c000000 0xed7f99f4ce000000

def z1216 : W := mkw 0x00323a51d0000000 0x00191d28e8000000 0xba783ff1fc000000 0xdd3c1ff8fe000000

def z1217 : W := mkw 0x02f7ff7ff8000000 0x017bffbffc000000 0xfafffffffe038001 0xfd7fffffff01c000

def z1218 : W := mkw 0x01eeba000369c001 0x00f75d0001b4e000 0x78fff00002718000 0x3c7ff8000138c000

def z1219 : W := mkw 0x805d807c03581e80 0xc02ec03e01ac0f40 0xfffffc7fe3ffffff 0xfffffe3ff1ffffff

def z1220 : W := mkw 0x0000000000000000 0x0000000000000000 0x5d87000802f00301 0xaec3800401780180

def z1221 : W := mkw 0xa011007c04101fa8 0xd008803e02080fd4 0x0400007e00001ff8 0x8200003f00000ffc

def z1222 : W := mkw 0x02f6ff57f8000000 0x017b7fabfc000000 0x82783f81fc000000 0x413c1fc0fe000000

def z1223 : W := mkw 0x100045822c862162 0x080022c1164310b1 0x6700cf9e7d8c67e6 0xb38067cf3ec633f3

def z1224 : W := mkw 0x8011007c00101e80 0xc008803e00080f40 0x0400006800001b00 0x8200003400000d80

def z1225 : W := mkw 0x805d807c03581e80 0xc02ec03e01ac0f40 0x5dffc06e02fc1bc1 0xaeffe037017e0de0

def z1226 : W := mkw 0x02f4ed5768000000 0x017a76abb4000000 0x6078cf9e7c000000 0x303c67cf3e000000

def z1227 : W := mkw 0x200312a894b28b28 0x900189544a594594 0x820033e19c039838 0x410019f0ce01cc1c

def z1228 : W := mkw 0x01eeff8007efe121 0x00f77fc003f7f090 0xffffff9e1fffe7e1 0xffffffcf0ffff3f0

def z1229 : W := mkw 0x02ffff7ffb480000 0x017fffbffda40000 0xfffffffffffc07c1 0xfffffffffffe03e0

def z1230 : W := mkw 0x01eca80003494001 0x00f6540001a4a000 0x10ff000002700000 0x087f800001380000

def z1231 : W := mkw 0x804c800403480080 0x4026400201a40040 0x79ffc00603fc00c1 0x3cffe00301fe0060

def z1232 : W := mkw 0x12f7ff7ff8042042 0x097bffbffc021021 0xfefffffffd0e64e7 0xff7ffffffe873273

def z1233 : W := mkw 0x00206d0228000000 0x0010368114000000 0xfa78ff9e7c000000 0xfd3c7fcf3e000000

def z1234 : W := mkw 0x01ced78003eea001 0x00e76bc001f75000 0xf9fff38003ff8001 0x7cfff9c001ffc000

def z1235 : W := mkw 0x01eeff822befe001 0x00f77fc115f7f000 0xfbffff807fffe001 0x7dffffc03ffff000

def z1236 : W := mkw 0x01eeff8003ebc001 0x00f77fc001f5e000 0xf9ffff8002f38001 0x7cffffc00179c000

def z1237 : W := mkw 0x10e6ff822ca6a162 0x08737fc1165350b1 0xffffff9e7fffe7e7 0xffffffcf3ffff3f3

def z1238 : W := mkw 0x4030285140014014 0x20181428a000a00a 0xbe783c71e203f83f 0xdf3c1e38f101fc1f

def z1239 : W := mkw 0x01eeff8003efe001 0x00f77fc001f7f000 0xf9ffff8001fc6000 0x7cffffc000fe3000

def z1240 : W := mkw 0xe008008007fbdfbc 0xf004004003fdefde 0x0500000003ffffff 0x0280000001ffffff

def z1241 : W := mkw 0xc05d807d43595e94 0xe02ec03ea1acaf4a 0x7fffc07fe3ffffff 0xbfffe03ff1ffffff

def z1242 : W := mkw 0x02f7ff7ff8000000 0x017bffbffc000000 0xfffffffffd8e67e7 0xfffffffffec733f3

def z1243 : W := mkw 0x11e6ff822ceea163 0x08f37fc1167750b1 0xfbffff9e7cfc03c0 0xfdffffcf3e7e01e0

def z1244 : W := mkw 0x004c800003480000 0x0026400001a40000 0x59ff000002f00001 0x2cff800001780000

def z1245 : W := mkw 0x22f7ff7ff8208008 0x117bffbffc104004 0xfafffffffc018018 0xfd7ffffffe00c00c

def z1246 : W := mkw 0x300312a894b28b6a 0x980189544a5945b5 0xdf8733e99ef39fff 0xefc399f4cf79cfff

def z1247 : W := mkw 0x02f7ff7ff8000000 0x017bffbffc000000 0xeaffcf9e7c000000 0xf57fe7cf3e000000

def z1248 : W := mkw 0x02f7ff7ff8100a00 0x817bffbffc080500 0xfffffffffef39b39 0xffffffffff79cd9c

def z1249 : W := mkw 0x02e7ff2eb8000000 0x0173ff975c000000 0x60ffcf8e1c000000 0x307fe7c70e000000

def z1250 : W := mkw 0x41eeff8003eff415 0x20f77fc001f7fa0a 0xf9ffff8003ffe407 0x7cffffc001fff203

def z1251 : W := mkw 0xa011007c94101fa8 0xd008803e4a080fd4 0x0400007e1c001fc0 0x8200003f0e000fe0

def z1252 : W := mkw 0x42f7ff7ff8001414 0x217bffbffc000a0a 0xfefffffffd027c3f 0xff7ffffffe813e1f

def z1253 : W := mkw 0x300312a894b6ab6a 0x980189544a5b55b5 0xdf8733e99ef3fb3f 0xefc399f4cf79fd9f

def z1254 : W := mkw 0x02f6ff5768000000 0x017b7fabb4000000 0xfaffff9e7c000000 0xfd7fffcf3e000000

def z1255 : W := mkw 0x01eeff8003efe001 0x00f77fc001f7f000 0xfbffff8063ffe027 0x7dffffc031fff013

def z1256 : W := mkw 0x825d807dd3581e80 0xc12ec03ee9ac0f40 0x7dffc07f83fc1fc1 0xbeffe03fc1fe0fe0

def z1257 : W := mkw 0x01eeba000369c001 0x00f75d0001b4e000 0x30fff000037d8000 0x187ff80001bec000

def z1258 : W := mkw 0x42f7ff7ff8014014 0x217bffbffc00a00a 0xfefffffffe03f83f 0xff7fffffff01fc1f

def z1259 : W := mkw 0x01eeba000369c001 0x00f75d0001b4e000 0xd8ff338002718000 0x6c7f99c00138c000

def z1260 : W := mkw 0x01e6ff8000a7e001 0x00f37fc00053f000 0xf9ffff8002f3e001 0x7cffffc00179f000

def z1261 : W := mkw 0x2011007c94100b28 0x9008803e4a080594 0x0600007f9c001b38 0x8300003fce000d9c

def z1262 : W := mkw 0x805d807c03581e80 0xc02ec03e01ac0f40 0xfffff07f83fc1fc1 0xfffff83fc1fe0fe0

def z1263 : W := mkw 0x002a3a000321c000 0x00151d000190e000 0xb8ff3c000373e001 0x5c7f9e0001b9f000

def z1264 : W := mkw 0x4038285143015414 0x201c1428a180aa0a 0xfe783ff9ff03fc3f 0xff3c1ffcff81fe1f

def z1265 : W := mkw 0x004e920003688000 0x0027490001b44000 0x79fff00003fd8001 0x3cfff80001fec000

def z1266 : W := mkw 0xd07ced576b4d74d6 0x683e76abb5a6ba6b 0x2078cc16610c64c6 0x103c660b30863263

def z1267 : W := mkw 0x00eeba0003480000 0x00775d0001a40000 0x10ff300002700000 0x087f980001380000

def z1268 : W := mkw 0x22e6ff83fca28128 0x11737fc1fe514094 0xfbffff81fef38039 0x7dffffc0ff79c01c

def z1269 : W := mkw 0xc011007d40101e94 0xe008803ea0080f4a 0xef00cc7fe18e7fff 0xf780663ff0c73fff

def z1270 : W := mkw 0x0044800000000000 0x0022400000000000 0x79ffc00002f00001 0x3cffe00001780000

def z1271 : W := mkw 0x11eced822fcf6163 0x08f676c117e7b0b1 0xffffcf9e7ffe67e7 0xffffe7cf3fff33f3

def z1272 : W := mkw 0x103028d144862162 0x08181468a24310b1 0xbf783c71e18e67e7 0xdfbc1e38f0c733f3

def z1273 : W := mkw 0x02f7ff7ff8100a00 0x817bffbffc080500 0xfffffffffffc1fc1 0xfffffffffffe0fe0

def z1274 : W := mkw 0x5008008007877576 0x2804004003c3babb 0x040000000303fc3f 0x020000000181fe1f

def z1275 : W := mkw 0x004d802803580a00 0x8026c01401ac0500 0x7dffc07e03fc1fc1 0xbeffe03f01fe0fe0

def z1276 : W := mkw 0x002a3a8007a3c120 0x00151d4003d1e090 0xffff3f987ff3e727 0xffff9fcc3ff9f393

def z1277 : W := mkw 0x406ca80143494014 0x20365400a1a4a00a 0xfbfffc01e3ffe03f 0x7dfffe00f1fff01f

def z1278 : W := mkw 0x02a27f03f8000000 0x01513f81fc000000 0xba783f81fc000000 0x5d3c1fc0fe000000

def z1279 : W := mkw 0x12f4edd76c862162 0x097a76ebb64310b1 0x2578cc16618e67e7 0x12bc660b30c733f3

def z1280 : W := mkw 0x01eeff8007efe121 0x00f77fc003f7f090 0xfbffff801fffe021 0x7dffffc00ffff010

def z1281 : W := mkw 0x02e6ff03f8000000 0x01737f81fc000000 0xa278ff81fc000000 0x513c7fc0fe000000

def z1282 : W := mkw 0x02316d7ff8000000 0x0118b6bffc000000 0xfa78fffffc000000 0xfd3c7ffffe000000

def z1283 : W := mkw 0x01eeff822befe001 0x00f77fc115f7f000 0xf9ffff8e1fffe001 0x7cffffc70ffff000

def z1284 : W := mkw 0x006ca80003494000 0x0036540001a4a000 0x79ffcc0003fc6001 0x3cffe60001fe3000

def z1285 : W := mkw 0xa01312fc94b29fa8 0xd009897e4a594fd4 0x860033ff9c039ff8 0xc30019ffce01cffc

def z1286 : W := mkw 0x805d807c03581e80 0xc02ec03e01ac0f40 0x71ffc07e03fc1fc0 0x38ffe03f01fe0fe0

def z1287 : W := mkw 0x00eeff8003ce2000 0x00777fc001e71000 0xf9ffff8003fe6001 0x7cffffc001ff3000

def z1288 : W := mkw 0x01e6ff8000eea001 0x00f37fc000775000 0x61ffcf8000fc0000 0x30ffe7c0007e0000

def z1289 : W := mkw 0x42f7ff7ff8014014 0x217bffbffc00a00a 0xfafffffffc018018 0xfd7ffffffe00c00c

def z1290 : W := mkw 0x200312a894b6ab28 0x900189544a5b5594 0xdf8733e99ffffb39 0xefc399f4cffffd9c

def z1291 : W := mkw 0x81eeff8403efe081 0x40f77fc201f7f040 0xf9ffff8603ffe0c1 0x7cffffc301fff060

def z1292 : W := mkw 0xc05d807c03595e94 0xe02ec03e01acaf4a 0x7dffc07e03fc7fc7 0xbeffe03f01fe3fe3

def z1293 : W := mkw 0x0044800000000000 0x0022400000000000 0x78ffc01e00000000 0xbc7fe00f00000000

def z1294 : W := mkw 0x9211007ffc101fe2 0xc908803ffe080ff1 0x0600007ffc001fe6 0x8300003ffe000ff3

def z1295 : W := mkw 0x02f7ff7dd0000000 0x017bffbee8000000 0xfaffffe99c000000 0xfd7ffff4ce000000

def z1296 : W := mkw 0x01eeff8003efe001 0x00f77fc001f7f000 0xfdffff8003fff839 0x7effffc001fffc1c

def z1297 : W := mkw 0x4030285140015414 0x20181428a000aa0a 0x82003c61e003f83e 0x41001e30f001fc1f

def z1298 : W := mkw 0x4038285143015414 0x201c1428a180aa0a 0xffff3c71e3f3fc3f 0xffff9e38f1f9fe1f

def z1299 : W := mkw 0x01eeff8003efe001 0x00f77fc001f7f000 0xf9ffff9603ffe4c1 0x7cffffcb01fff260

def z1300 : W := mkw 0x2008008007fa8b28 0x9004004003fd4594 0x0500000003ff9b39 0x0280000001ffcd9c

def z1301 : W := mkw 0x805d807c03581e80 0xc02ec03e01ac0f40 0x35ffc07603fc1fc1 0x1affe03b01fe0fe0

def z1302 : W := mkw 0x02b37f7ff8000000 0x0159bfbffc000000 0x82003fe1fc000000 0x41001ff0fe000000

def z1303 : W := mkw 0x01eeff8007efe121 0x00f77fc003f7f090 0xf9ffff881fffe301 0x7cffffc40ffff180

def z1304 : W := mkw 0x02d7d77eb8000000 0x016bebbf5c000000 0x50ffc3ee1c000000 0x287fe1f70e000000

def z1305 : W := mkw 0x8011007c00101e80 0xc008803e00080f40 0x1c00007e02001fc1 0x8e00003f01000fe0

def z1306 : W := mkw 0x60110079d0101e1c 0xb008803ce8080f0e 0x0000006180001818 0x00000030c0000c0c

def z1307 : W := mkw 0xa05e92d497ea95a8 0x502f496a4bf54ad4 0xa278f3979d0f84f8 0x513c79cbce87c27c

def z1308 : W := mkw 0x8055807c00580a80 0xc02ac03e002c0540 0x7dffc07e01fc07c1 0xbeffe03f00fe03e0

def z1309 : W := mkw 0x02f6ff57f8000000 0x017b7fabfc000000 0xea78ff9ffc000000 0xf53c7fcffe000000

def z1310 : W := mkw 0x0257927ff8000000 0x012bc93ffc000000 0xfafff3fffc000000 0xfd7ff9fffe000000

def z1311 : W := mkw 0x82f7ff7ff8101e80 0xc17bffbffc080f40 0xfffffffffef01fc1 0xffffffffff780fe0

def z1312 : W := mkw 0x02f7ff7ff8100a00 0x817bffbffc080500 0xfefffffffc001b00 0xff7ffffffe000d80

def z1313 : W := mkw 0x4028280143014014 0x20141400a180a00a 0xbe783c61e303f83f 0xdf3c1e30f181fc1f

def z1314 : W := mkw 0x805d807c03581e80 0xc02ec03e01ac0f40 0x7fffc07e63fc1fe7 0xbfffe03f31fe0ff3

def z1315 : W := mkw 0x02f7ff7eb8000000 0x017bffbf5c000000 0xf8fffffe1c000000 0xfc7fffff0e000000

def z1316 : W := mkw 0x805d807c03581e80 0xc02ec03e01ac0f40 0x55ffc06e03fc1fc1 0x2affe03701fe0fe0

def z1317 : W := mkw 0x03eeff82bbefe001 0x01f77fc15df7f000 0xf9ffff801fffe001 0x7cffffc00ffff000

def z1318 : W := mkw 0x006ca80003494000 0x0036540001a4a000 0xfffffc1e63ffe7e7 0xfffffe0f31fff3f3

def z1319 : W := mkw 0x82b37f7ff8101e80 0xc159bfbffc080f40 0x86003ffffc001fc0 0xc3001ffffe000fe0

def z1320 : W := mkw 0x9011007c04101fe2 0xc808803e02080ff1 0x0400007e00001fe6 0x8200003f00000ff3

def z1321 : W := mkw 0x200312a894b28b28 0x900189544a594594 0xff873fe99ff3fb39 0xffc39ff4cff9fd9c

def z1322 : W := mkw 0x00ced70003480000 0x00676b8001a40000 0x79ffc38003fc0001 0x3cffe1c001fe0000

def z1323 : W := mkw 0x01ce920003688001 0x00e7490001b44000 0x79ffc00003fc0001 0x3cffe00001fe0000

def z1324 : W := mkw 0x01eeba8007ebc121 0x00f75d4003f5e090 0xdfff33881ef38321 0xefff99c40f79c190

def z1325 : W := mkw 0x02f7ff7ff8208000 0x017bffbffc104000 0xfafffffffe718000 0xfd7fffffff38c000

def z1326 : W := mkw 0x014c80000369c001 0x00a6400001b4e000 0x10ff000002718000 0x087f80000138c000

def z1327 : W := mkw 0x801100fc04921fa0 0xc008807e02490fd0 0xcf0003fe1c821fe1 0xe78001ff0e410ff0

def z1328 : W := mkw 0x200312a894b28b28 0x900189544a594594 0x978733e19ef39b39 0x4bc399f0cf79cd9c

def z1329 : W := mkw 0x01eeff8007efe121 0x00f77fc003f7f090 0xfdffff8003ffe321 0x7effffc001fff190

def z1330 : W := mkw 0x41eeba000369d415 0x20f75d0001b4ea0a 0x10ff300002719818 0x087f98000138cc0c

def z1331 : W := mkw 0x01eeba000369c001 0x00f75d0001b4e000 0xf9fffc0003ffe001 0x7cfffe0001fff000

def z1332 : W := mkw 0x02e7ff2eb8000000 0x0173ff975c000000 0xfaffffef9c000000 0xfd7ffff7ce000000

def z1333 : W := mkw 0x01eeba000369c001 0x00f75d0001b4e000 0xb8ff3c0002718000 0x5c7f9e000138c000

def z1334 : W := mkw 0x7008008007b7ff7e 0xb804004003dbffbf 0x0500000003ffffff 0x0280000001ffffff

def z1335 : W := mkw 0x02f7ff7ff8014000 0x017bffbffc00a000 0xfafffffffc03e000 0xfd7ffffffe01f000

def z1336 : W := mkw 0x03f7ff7ff8056001 0x01fbffbffc02b000 0xfafffffffc006000 0xfd7ffffffe003000

def z1337 : W := mkw 0x10eeff822fce2162 0x08777fc117e710b1 0xffffff9e7ffe67e7 0xffffffcf3fff33f3

def z1338 : W := mkw 0x100045822c862162 0x080022c1164310b1 0xa600cf9e7d0e67e6 0xd30067cf3e8733f3

def z1339 : W := mkw 0x41eeff8003efe015 0x20f77fc001f7f00a 0xf9ffff8003ffe03f 0x7cffffc001fff01f

def z1340 : W := mkw 0x2003122894308b28 0x900189144a184594 0xde8733e99e719b38 0xef4399f4cf38cd9c

def z1341 : W := mkw 0x014e928003efe001 0x00a7494001f7f000 0xf9fff38003ffe001 0x7cfff9c001fff000

def z1342 : W := mkw 0x02f5ed7f68000000 0x017af6bfb4000000 0xfaffcffe7c000000 0xfd7fe7ff3e000000

def z1343 : W := mkw 0x014cc58003efe001 0x00a662c001f7f000 0xf9ffcf8003ffe001 0x7cffe7c001fff000

def z1344 : W := mkw 0x42f7ff7ff8014014 0x217bffbffc00a00a 0xfafffffffc006006 0xfd7ffffffe003003

def z1345 : W := mkw 0x4038285143015414 0x201c1428a180aa0a 0xbe783c7fe303ffff 0xdf3c1e3ff181ffff

def z1346 : W := mkw 0x8011007c00101e80 0xc008803e00080f40 0x0400007000001c00 0x8200003800000e00

def z1347 : W := mkw 0xb047d7aebcfeabea 0xd823ebd75e7f55f5 0x4187c38e1cfc03c0 0x20c3e1c70e7e01e0

def z1348 : W := mkw 0x01eeba8003ebc001 0x00f75d4001f5e000 0x51ff338002f18000 0x28ff99c00178c000

def z1349 : W := mkw 0x60110079d0101e1c 0xb008803ce8080f0e 0x06000071e0001c3e 0x83000038f0000e1f

def z1350 : W := mkw 0x1008008007876162 0x0804004003c3b0b1 0x05000000038fe7e7 0x0280000001c7f3f3

def z1351 : W := mkw 0x11e6ff822ceea163 0x08f37fc1167750b1 0xffffff9e7dfe67e7 0xffffffcf3eff33f3

def z1352 : W := mkw 0x22f7bafdd4b28b28 0x917bdd7eea594594 0x15ff306182f39b39 0x0aff9830c179cd9c

def z1353 : W := mkw 0x0030285140000000 0x00181428a0000000 0xbe783c71e303fc3f 0xdf3c1e38f181fe1f

def z1354 : W := mkw 0x11eeff822fefe163 0x08f77fc117f7f0b1 0xefffcf9e7dfe67e7 0xf7ffe7cf3eff33f3

def z1355 : W := mkw 0x200312a894b28b28 0x900189544a594594 0xdf873fe9fef3fb3f 0xefc39ff4ff79fd9f

def z1356 : W := mkw 0x200312a894b28b28 0x900189544a594594 0xdf87f3ef9eff9bf9 0xefc3f9f7cf7fcdfc

def z1357 : W := mkw 0x02f7ff7ff8000000 0x017bffbffc000000 0xfafffffffe019818 0xfd7fffffff00cc0c

def z1358 : W := mkw 0x02f7ff7ff8000000 0x017bffbffc000000 0xe2ffff9ffc000000 0x717fffcffe000000

def z1359 : W := mkw 0x02f7ba7dd0000000 0x017bdd3ee8000000 0xfaff3ff9fc000000 0xfd7f9ffcfe000000

def z1360 : W := mkw 0x11ced7822feea163 0x08e76bc117f750b1 0x7dffc39e1ffc07c1 0xbeffe1cf0ffe03e0

def z1361 : W := mkw 0x02f7ff7ff8000000 0x017bffbffc000000 0x62ffcffffc000000 0xb17fe7fffe000000

def z1362 : W := mkw 0x41eeff8143efe015 0x20f77fc0a1f7f00a 0xffffffe1e3fff83f 0xfffffff0f1fffc1f

def z1363 : W := mkw 0x02d7d77eb8000000 0x016bebbf5c000000 0x60ffc39e1c000000 0x307fe1cf0e000000

def z1364 : W := mkw 0x01eeba8003ebc001 0x00f75d4001f5e000 0x11ff300002f38001 0x08ff98000179c000

def z1365 : W := mkw 0x01eeff8003efe001 0x00f77fc001f7f000 0xb0ffff80037fe000 0x587fffc001bff000

def z1366 : W := mkw 0xc2fced576b495494 0x617e76abb5a4aa4a 0x2078cc16610c64c6 0x103c660b30863263

def z1367 : W := mkw 0x8011007c00101e80 0xc008803e00080f40 0x2400c07e010c1fc0 0x9200603f00860fe0

def z1368 : W := mkw 0x4008008007835534 0x2004004003c1aa9a 0x050000000383ff3f 0x0280000001c1ff9f

def z1369 : W := mkw 0x9011007e28101ec2 0xc808803f14080f61 0x0400007e60001fc6 0x8200003f30000fe3

def z1370 : W := mkw 0x41eeff8003eff415 0x20f77fc001f7fa0a 0xf9ffff8003fff819 0x7cffffc001fffc0c

def z1371 : W := mkw 0x01eced8003efe001 0x00f676c001f7f000 0x79ffcc0003ffe001 0x3cffe60001fff000

def z1372 : W := mkw 0x100045822c862162 0x080022c1164310b1 0xe900cf9e7d8e67c7 0x748067cf3ec733e3

def z1373 : W := mkw 0x805d807c03581e80 0xc02ec03e01ac0f40 0x79ffc06e03fc1bc1 0x3cffe03701fe0de0

def z1374 : W := mkw 0x8011007e28101e80 0xc008803f14080f40 0x0600007e7c001fc0 0x8300003f3e000fe0

def z1375 : W := mkw 0x004ed78003eea000 0x00276bc001f75000 0xf9ffff8003ffe001 0x7cffffc001fff000

def z1376 : W := mkw 0xa008008007fa9fa8 0xd004004003fd4fd4 0x0500000003fc1fc1 0x0280000001fe0fe0

def z1377 : W := mkw 0x11eeff822befe043 0x08f77fc115f7f021 0xffffff9663ffe4e7 0xffffffcb31fff273

def z1378 : W := mkw 0x805d807d43581e80 0xc02ec03ea1ac0f40 0x7fffc07fe3fc1fc1 0xbfffe03ff1fe0fe0

def z1379 : W := mkw 0x11eeff8003efe043 0x08f77fc001f7f021 0xf9ffff8003ffe4c7 0x7cffffc001fff263

def z1380 : W := mkw 0xc05d807c03581e94 0xe02ec03e01ac0f4a 0x7dffc07e03fc1fff 0xbeffe03f01fe0fff

def z1381 : W := mkw 0xc05d807d43581e94 0xe02ec03ea1ac0f4a 0x7dffc07e63fc1fc7 0xbeffe03f31fe0fe3

def z1382 : W := mkw 0xc05d807d43581e94 0xe02ec03ea1ac0f4a 0x7dffc07f83fc1fd9 0xbeffe03fc1fe0fec

def z1383 : W := mkw 0x82f7ff7ff8580a80 0xc17bffbffc2c0540 0xfffffffffefc1bc1 0xffffffffff7e0de0

def z1384 : W := mkw 0x22b37ffffcb28b28 0x9159bffffe594594 0x86003ffffc039b38 0xc3001ffffe01cd9c

def z1385 : W := mkw 0x02f7ff7ff8480000 0x017bffbffc240000 0xfbfffffffcfc0000 0xfdfffffffe7e0000

def z1386 : W := mkw 0x4038285143015414 0x201c1428a180aa0a 0x9e783c61e203f83f 0xcf3c1e30f101fc1f

def z1387 : W := mkw 0x23eeff83ffefe129 0x11f77fc1fff7f094 0xfbffff81ffffe039 0x7dffffc0fffff01c

def z1388 : W := mkw 0x02f7ff7ff8000000 0x017bffbffc000000 0xdaff3fe9fc000000 0xed7f9ff4fe000000

def z1389 : W := mkw 0x002a3a000321c000 0x00151d000190e000 0x10ff300002718000 0x087f98000138c000

def z1390 : W := mkw 0x8011007c00101e80 0xc008803e00080f40 0xae000c7e61027fe7 0xd700063f30813ff3

def z1391 : W := mkw 0x02f7ff7ff8000000 0x017bffbffc000000 0xd2ffffeffc000000 0x697ffff7fe000000

def z1392 : W := mkw 0x805d807c03581e80 0xc02ec03e01ac0f40 0x7dffcc7e63fc7fc7 0xbeffe63f31fe3fe3

def z1393 : W := mkw 0x0055807c00000000 0x002ac03e00000000 0xfaffc3fe1c000000 0xfd7fe1ff0e000000

def z1394 : W := mkw 0x01eeff8003efe001 0x00f77fc001f7f000 0xfdffff8003ffe7c1 0x7effffc001fff3e0

def z1395 : W := mkw 0x00e6ff0090000000 0x00737f8048000000 0xfaffff819c000000 0x7d7fffc0ce000000

def z1396 : W := mkw 0x004c800003480000 0x0026400001a40000 0xffffcc1063fe6427 0xffffe60831ff3213

def z1397 : W := mkw 0x01eeba8003efe001 0x00f75d4001f7f000 0xd9ff338003ffe001 0x6cff99c001fff000

def z1398 : W := mkw 0x02f5ed7ff8000000 0x017af6bffc000000 0xea78cffffc000000 0xf53c67fffe000000

def z1399 : W := mkw 0x41eeff8003eff415 0x20f77fc001f7fa0a 0xffffffe183fffc3f 0xfffffff0c1fffe1f

def z1400 : W := mkw 0x41eeba014369c015 0x20f75d00a1b4e00a 0x92ff3c01e273e03e 0x497f9e00f139f01f

def z1401 : W := mkw 0x2029282897114b28 0x901494144b88a594 0xbe783c699f03fb39 0xdf3c1e34cf81fd9c

def z1402 : W := mkw 0x02f7ff7ff8000000 0x017bffbffc000000 0xfafffffffc038038 0xfd7ffffffe01c01c

def z1403 : W := mkw 0x8055807c00581e80 0xc02ac03e002c0f40 0x7dffc07e00fc1fc0 0xbeffe03f007e0fe0

def z1404 : W := mkw 0x805d807c03581e80 0xc02ec03e01ac0f40 0x65ffc07e01fc1fc0 0xb2ffe03f00fe0fe0

def z1405 : W := mkw 0x002a7f8003a7e000 0x00153fc001d3f000 0xf9ffff8003ffe001 0x7cffffc001fff000

def z1406 : W := mkw 0x004c800003480000 0x0026400001a40000 0x79ffc01603fc04c1 0x3cffe00b01fe0260

def z1407 : W := mkw 0x02f4ed5768000000 0x017a76abb4000000 0xfa78fffffc000000 0xfd3c7ffffe000000

def z1408 : W := mkw 0x300312a894b6ab6a 0x980189544a5b55b5 0xff87f3ff9fffffff 0xffc3f9ffcfffffff

def z1409 : W := mkw 0x41eeff8003eff415 0x20f77fc001f7fa0a 0xffffff9063fffc3f 0xffffffc831fffe1f

def z1410 : W := mkw 0x01c6d78000eea001 0x00e36bc000775000 0x79ffc38000fc0000 0x3cffe1c0007e0000

def z1411 : W := mkw 0x11eeff822fefe163 0x08f77fc117f7f0b1 0xffffffffffffffff 0xffffffffffffffff

def z1412 : W := mkw 0x200312a894b28b28 0x900189544a594594 0xff87ffffffffffff 0xffc3ffffffffffff

def z1413 : W := mkw 0x00e6ff822ca28120 0x00737fc116514090 0xffffff9e7ef38321 0xffffffcf3f79c190

def z1414 : W := mkw 0x01ce920003688001 0x00e7490001b44000 0x10ff000002700000 0x087f800001380000

def z1415 : W := mkw 0x01eeff8003eea001 0x00f77fc001f75000 0xf9ffff8003fc0001 0x7cffffc001fe0000

def z1416 : W := mkw 0x51eeff822feff577 0x28f77fc117f7fabb 0xffffff9e7fffffff 0xffffffcf3fffffff

def z1417 : W := mkw 0x01eeff8003efe001 0x00f77fc001f7f000 0xd9fff38002ff8001 0x6cfff9c0017fc000

def z1418 : W := mkw 0xd011007f6c101ff6 0xe808803fb6080ffb 0x0600007ffc001ffe 0x8300003ffe000fff

def z1419 : W := mkw 0x01eeff000369c001 0x00f77f8001b4e000 0xf8ffff800373e001 0x7c7fffc001b9f000

def z1420 : W := mkw 0x00eeff0003494000 0x00777f8001a4a000 0xf9ffff8003ffe001 0x7cffffc001fff000

def z1421 : W := mkw 0x01eeff00036de001 0x00f77f8001b6f000 0x79fffc0003fde001 0x3cfffe0001fef000

def z1422 : W := mkw 0x00337f7bf8000000 0x0019bfbdfc000000 0xfafffffffc000000 0xfd7ffffffe000000

def z1423 : W := mkw 0x805d807c03581e80 0xc02ec03e01ac0f40 0x6dffc01e01fc07c1 0xb6ffe00f00fe03e0

def z1424 : W := mkw 0x0010455228000000 0x000822a914000000 0xfa78cffe7c000000 0xfd3c67ff3e000000

def z1425 : W := mkw 0x8011457e28101e80 0xc008a2bf14080f40 0xee00cffe7c001fc0 0xf70067ff3e000fe0

def z1426 : W := mkw 0x03eeff862befe001 0x01f77fc315f7f000 0xf9ffff8603ffe001 0x7cffffc301fff000

def z1427 : W := mkw 0x100045822c862162 0x080022c1164310b1 0xef00ff9ffd8fe7ff 0xf7807fcffec7f3ff

def z1428 : W := mkw 0x11eeff822befe043 0x08f77fc115f7f021 0xf9ffff8063ffe007 0x7cffffc031fff003

def z1429 : W := mkw 0x01eeff8003efe001 0x00f77fc001f7f000 0xfdffff8003ffe427 0x7effffc001fff213

def z1430 : W := mkw 0x0108008007efe121 0x0084004003f7f090 0x0500000003ffe321 0x0280000001fff190

def z1431 : W := mkw 0x0057927c90000000 0x002bc93e48000000 0xdaff33e99c000000 0xed7f99f4ce000000

def z1432 : W := mkw 0x02f7ff7ff8000000 0x017bffbffc000000 0xfafffffffd0c04c0 0xfd7ffffffe860260

def z1433 : W := mkw 0x100045822c862162 0x080022c1164310b1 0x6d00cf9e7d8c67c7 0xb68067cf3ec633e3

def z1434 : W := mkw 0x02f7ff7ff8000000 0x017bffbffc000000 0xf8ffffef9c000000 0x7c7ffff7ce000000

def z1435 : W := mkw 0x02e7ff2bf8000000 0x0173ff95fc000000 0xfaffffe9fc000000 0xfd7ffff4fe000000

def z1436 : W := mkw 0x01eeff8003efe001 0x00f77fc001f7f000 0xf8ffff800273e000 0x7c7fffc00139f000

def z1437 : W := mkw 0x8019007c03581e80 0xc00c803e01ac0f40 0x0400007e010c1fc0 0x8200003f00860fe0

def z1438 : W := mkw 0x01ced78003eea001 0x00e76bc001f75000 0xf9ffcf8003fe6001 0x7cffe7c001ff3000

def z1439 : W := mkw 0x01e6ba0000688001 0x00f35d0000344000 0x10ff300000700000 0x087f980000380000

def z1440 : W := mkw 0x8011007c00101e80 0xc008803e00080f40 0x4500c07e008c1fc0 0xa280603f00460fe0

def z1441 : W := mkw 0x03eeff836befe001 0x01f77fc1b5f7f000 0xf9ffff8063ffe001 0x7cffffc031fff000

def z1442 : W := mkw 0x01eeff022b69c001 0x00f77f8115b4e000 0xfaffff9e7e718000 0xfd7fffcf3f38c000

def z1443 : W := mkw 0x32a27f83fca6a16a 0x19513fc1fe5350b5 0x82003f81fc03e03e 0x41001fc0fe01f01f

def z1444 : W := mkw 0x02f7ff7ff8000000 0x017bffbffc000000 0x40ffc38e1c000000 0x207fe1c70e000000

def z1445 : W := mkw 0x02f6ff57f8000000 0x017b7fabfc000000 0x2078cf967c000000 0x103c67cb3e000000

def z1446 : W := mkw 0x407ca85143495414 0x203e5428a1a4aa0a 0xfffffc7fe3ffffff 0xfffffe3ff1ffffff

def z1447 : W := mkw 0x60110079d4101f3c 0xb008803cea080f9e 0x060000699c001b38 0x83000034ce000d9c

def z1448 : W := mkw 0x32c7d7aebcb6ab6a 0x9963ebd75e5b55b5 0x4187c38e1cfc03c0 0x20c3e1c70e7e01e0

def z1449 : W := mkw 0x7011007bfc101f7e 0xb808803dfe080fbf 0x0600007ffc001ffe 0x8300003ffe000fff

def z1450 : W := mkw 0x004e920003688000 0x0027490001b44000 0x10ff300002718000 0x087f98000138c000

def z1451 : W := mkw 0x01e6ff8000eea001 0x00f37fc000775000 0xf9ffff8001fe6001 0x7cffffc000ff3000

def z1452 : W := mkw 0x01eeff8003efe001 0x00f77fc001f7f000 0xf9ffff8e03ffe3c1 0x7cffffc701fff1e0

def z1453 : W := mkw 0x01eeba000369c001 0x00f75d0001b4e000 0x51fff00002fd8000 0x28fff800017ec000

def z1454 : W := mkw 0x2108008007fbcb29 0x9084004003fde594 0x0500000002f39b39 0x028000000179cd9c

def z1455 : W := mkw 0x100045822c862162 0x080022c1164310b1 0xff00fffffd8e67e7 0xff807ffffec733f3

def z1456 : W := mkw 0x921145fffc963fe2 0xc908a2fffe4b1ff1 0xef00cffffd8e7fe7 0xf78067fffec73ff3

def z1457 : W := mkw 0x01eeba000369c001 0x00f75d0001b4e000 0x38ff300003718001 0x1c7f980001b8c000

def z1458 : W := mkw 0x000a128003a28000 0x0005094001d14000 0xf9ff338003f38001 0x7cff99c001f9c000

def z1459 : W := mkw 0x01eeff8143efe001 0x00f77fc0a1f7f000 0xfbffff81e3ffe001 0x7dffffc0f1fff000

def z1460 : W := mkw 0x01eeff8003efe001 0x00f77fc001f7f000 0xfbffff9063ffe001 0xfdffffc831fff000

def z1461 : W := mkw 0x02f7ba7dd0000000 0x017bdd3ee8000000 0x50ff33e99c000000 0x287f99f4ce000000

def z1462 : W := mkw 0x02f7ff7ff8100a00 0x817bffbffc080500 0xfbfffffffcf00300 0xfdfffffffe780180

def z1463 : W := mkw 0x6008008007a3d53c 0x3004004003d1ea9e 0x040000000303fc3f 0x020000000181fe1f

def z1464 : W := mkw 0x11eeff822fefe163 0x08f77fc117f7f0b1 0xfdffff9e1fffe7c1 0xfeffffcf0ffff3e0

def z1465 : W := mkw 0x01eeff000369c001 0x00f77f8001b4e000 0xf9ffff8003fd8001 0x7cffffc001fec000

def z1466 : W := mkw 0x11eeff822fefe163 0x08f77fc117f7f0b1 0xfbffff9e7fffe3c1 0xfdffffcf3ffff1e0

def z1467 : W := mkw 0x8011007c00101e80 0xc008803e00080f40 0x9e00307f82039ff9 0xcf00183fc101cffc

def z1468 : W := mkw 0x01eeff00036de001 0x00f77f8001b6f000 0x20ffcc00017c6000 0x107fe60000be3000

def z1469 : W := mkw 0x01eeba8003efe001 0x00f75d4001f7f000 0x79fff00003ffe001 0x3cfff80001fff000

def z1470 : W := mkw 0x4038285143015414 0x201c1428a180aa0a 0xb2783c71e303fc3e 0x593c1e38f181fe1f

def z1471 : W := mkw 0x0055807c00100a00 0x802ac03e00080500 0x7dffc07e03fc1fc1 0xbeffe03f01fe0fe0

def z1472 : W := mkw 0x805c805403581e80 0xc02e402a01ac0f40 0x7dffc01603fc1fc1 0x3effe00b01fe0fe0

def z1473 : W := mkw 0x0075ed7f68000000 0x003af6bfb4000000 0xfafffffffc000000 0xfd7ffffffe000000

def z1474 : W := mkw 0x014c808003efe001 0x00a6404001f7f000 0x11ff000003ffe001 0x08ff800001fff000

def z1475 : W := mkw 0x01eeff8003efe001 0x00f77fc001f7f000 0xf9ffff8002fd8000 0x7cffffc0017ec000

def z1476 : W := mkw 0x200312a894b28b28 0x900189544a594594 0x9e8733e19e739839 0xcf4399f0cf39cc1c

def z1477 : W := mkw 0x805d807c03581e80 0xc02ec03e01ac0f40 0x7fffc07f83fc1ff9 0xbfffe03fc1fe0ffc

def z1478 : W := mkw 0x00233a2890000000 0x00119d1448000000 0xfaff3fe99c000000 0xfd7f9ff4ce000000

def z1479 : W := mkw 0x004c800003480000 0x0026400001a40000 0x30ffc000037c0000 0x187fe00001be0000

def z1480 : W := mkw 0x204f92a897fa8b28 0x9027c9544bfd4594 0xfffff3ff9fff9ff9 0xfffff9ffcfffcffc

def z1481 : W := mkw 0x42f7ff7ff8001414 0x217bffbffc000a0a 0xfefffffffe039c3f 0xff7fffffff01ce1f

def z1482 : W := mkw 0x004cc5022b480000 0x0026628115a40000 0xfbffcf9e7ffc0001 0xfdffe7cf3ffe0000

def z1483 : W := mkw 0x43eeff83fbefe015 0x21f77fc1fdf7f00a 0xfbffff81ffffe03f 0x7dffffc0fffff01f

def z1484 : W := mkw 0x804d802c03580a80 0xc026c01601ac0540 0x7dffc06e03fc1bc1 0xbeffe03701fe0de0

def z1485 : W := mkw 0x01e6ff8000eea001 0x00f37fc000775000 0x51fff38000fc0000 0x28fff9c0007e0000

def z1486 : W := mkw 0x01eeff8003efe001 0x00f77fc001f7f000 0x61ffcf8003ffe001 0x30ffe7c001fff000

def z1487 : W := mkw 0x805d807c03581e80 0xc02ec03e01ac0f40 0xfdfff07e03ff9fc1 0xfefff83f01ffcfe0

def z1488 : W := mkw 0x8008008007da1fa0 0xc004004003ed0fd0 0x0500000003fe1fe1 0x0280000001ff0ff0

def z1489 : W := mkw 0x805d807c93581e80 0xc02ec03e49ac0f40 0x7fffc07f9ffc1fc1 0xbfffe03fcffe0fe0

def z1490 : W := mkw 0x300312a894b6ab6a 0x980189544a5b55b5 0xdf8733e99eff9bf9 0xefc399f4cf7fcdfc

def z1491 : W := mkw 0x02f7ba7dd0000000 0x017bdd3ee8000000 0xfafff3ff9c000000 0xfd7ff9ffce000000

def z1492 : W := mkw 0xa008008007fa9fa8 0xd004004003fd4fd4 0x0500000002f39b39 0x028000000179cd9c

def z1493 : W := mkw 0x701145fbfc963f7e 0xb808a2fdfe4b1fbf 0xef00cffffd8e7fff 0xf78067fffec73fff

def z1494 : W := mkw 0x11ced7822feea163 0x08e76bc117f750b1 0xffffcf9e7ffe67e7 0xffffe7cf3fff33f3

def z1495 : W := mkw 0x43fced576b4d7415 0x21fe76abb5a6ba0a 0x2078cc16610c6406 0x103c660b30863203

def z1496 : W := mkw 0x00e7ff2890000000 0x0073ff9448000000 0xf8ffff881c000000 0x7c7fffc40e000000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z0,z1,z3,z7,z4,z5,z6]),(0,[z0,z8,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z9]),(0,[z0,z1,z3,z4,z10,z5,z6]),(0,[z0,z1,z3,z4,z5,z11,z6]),(0,[z0,z1,z3,z4,z12,z5,z6])],[(0,[z1,z3,z13,z14,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z15,z6]),(0,[z0,z1,z16,z4,z5,z17,z6])],[(0,[z18,z1,z3,z19,z4,z5,z6]),(0,[z0,z1,z3,z4,z20,z5,z6]),(0,[z0,z1,z3,z21,z22,z5,z6]),(0,[z0,z1,z3,z4,z5,z23,z6])],[(0,[z24,z25,z1,z3,z4,z5,z6]),(0,[z18,z1,z3,z4,z26,z5,z6]),(0,[z27,z1,z3,z4,z5,z15,z6]),(0,[z28,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z16,z3,z4,z5,z17]),(0,[z0,z1,z29,z3,z4,z5,z6]),(0,[z0,z1,z3,z30,z5,z31,z6]),(0,[z0,z1,z3,z4,z5,z6,z32])],[(0,[z25,z1,z3,z4,z5,z33,z6]),(0,[z34,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z35,z5,z6]),(0,[z36,z1,z16,z3,z4,z5,z6])],[(0,[z0,z37,z1,z3,z4,z5,z6])],[(0,[z18,z38,z1,z3,z4,z5,z6]),(0,[z0,z1,z39,z3,z4,z5,z6]),(0,[z40,z0,z1,z3,z4,z5,z6]),(0,[z41,z1,z3,z4,z5,z15,z6]),(0,[z0,z42,z3,z4,z43,z5,z6]),(0,[z0,z1,z3,z44,z5,z6,z45]),(0,[z46,z0,z3,z4,z5,z6,z47]),(0,[z0,z1,z3,z4,z5,z6,z48]),(1,[z0,z3,z4,z5,z6,z49])]],
   [[(0,[z18,z1,z3,z4,z43,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z50]),(1,[z1,z3,z4,z5,z6,z51]),(0,[z52,z0,z1,z3,z4,z5,z6])],[(0,[z53,z0,z1,z3,z4,z5,z6]),(0,[z54,z0,z3,z14,z4,z5,z6]),(1,[z55,z0,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z56,z6]),(0,[z0,z1,z3,z57,z4,z5,z6]),(0,[z0,z58,z1,z3,z4,z5,z6])],[(0,[z59,z1,z3,z4,z5,z60,z6]),(0,[z61,z0,z1,z16,z3,z4,z5]),(0,[z42,z1,z3,z4,z5,z15,z6]),(0,[z0,z1,z3,z4,z5,z62,z6]),(0,[z63,z1,z3,z4,z5,z6,z47])],[(0,[z64,z0,z1,z3,z4,z5,z6]),(0,[z65,z0,z3,z4,z5,z6,z66]),(0,[z67,z0,z1,z3,z4,z5,z6]),(0,[z25,z1,z3,z4,z26,z5,z6]),(1,[z68,z18,z1,z3,z4,z5]),(0,[z0,z69,z1,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z15,z6,z66])],[(0,[z70,z0,z1,z3,z4,z5,z6]),(0,[z71,z1,z3,z4,z5,z15,z6]),(0,[z1,z3,z30,z4,z5,z15,z6]),(0,[z0,z1,z3,z72,z4,z5,z6]),(0,[z0,z1,z3,z22,z73,z5,z6]),(0,[z1,z3,z4,z5,z6,z74,z75])],[(0,[z18,z25,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z76,z5,z6]),(0,[z77,z0,z1,z3,z4,z5,z6]),(0,[z1,z78,z3,z4,z5,z15,z6]),(0,[z0,z1,z79,z3,z80,z5,z6]),(0,[z0,z1,z3,z4,z5,z17,z6]),(1,[z81,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z82,z6]),(0,[z0,z1,z83,z3,z4,z5,z6])],[(0,[z1,z84,z3,z4,z5,z15,z6]),(0,[z25,z38,z1,z3,z4,z5,z6]),(0,[z85,z1,z3,z14,z4,z5,z6]),(0,[z0,z1,z3,z4,z86,z5,z6]),(0,[z0,z1,z3,z4,z87,z5,z6]),(0,[z0,z1,z3,z4,z5,z88,z6]),(0,[z0,z1,z3,z4,z5,z6,z47])],[(0,[z25,z1,z3,z4,z43,z5,z6]),(0,[z0,z1,z3,z4,z89,z5,z6]),(0,[z90,z18,z1,z3,z4,z5,z6]),(1,[z1,z3,z91,z4,z5,z6]),(0,[z92,z0,z1,z3,z4,z5,z6])]],
   [[(0,[z38,z1,z3,z4,z5,z15,z6]),(0,[z93,z25,z1,z3,z4,z5,z6]),(0,[z24,z0,z1,z3,z4,z5,z6]),(0,[z94,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z95,z6]),(0,[z0,z1,z3,z4,z5,z96,z6]),(0,[z0,z1,z3,z97,z4,z5,z6]),(0,[z0,z1,z3,z73,z5,z98,z6]),(0,[z99,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z100]),(1,[z18,z1,z16,z3,z4,z5]),(0,[z1,z101,z3,z91,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z102,z6]),(0,[z1,z3,z4,z5,z6,z51,z45])],[(0,[z25,z1,z3,z3,z4,z5,z6]),(0,[z1,z3,z4,z103,z5,z15,z6]),(0,[z40,z1,z3,z4,z5,z15,z6]),(0,[z104,z0,z1,z3,z4,z5,z6])],[(1,[z105,z1,z3,z4,z5,z6]),(0,[z106,z0,z1,z3,z4,z5,z6]),(0,[z25,z25,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z107,z6]),(0,[z0,z1,z3,z108,z4,z5,z6]),(0,[z53,z18,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z6])],[(0,[z59,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z109,z5,z6])],[(0,[z0,z71,z3,z4,z5,z6,z66]),(0,[z0,z79,z3,z4,z5,z110,z6]),(0,[z0,z1,z3,z111,z4,z5,z6]),(0,[z1,z16,z3,z112,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z113]),(1,[z1,z3,z4,z5,z6,z114]),(0,[z0,z115,z1,z3,z4,z5,z6])]],
   [[(0,[z116,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z117,z4,z5,z6]),(0,[z0,z1,z3,z118,z4,z5,z6]),(0,[z18,z1,z3,z4,z103,z5,z6]),(0,[z0,z1,z119,z3,z4,z5,z6]),(0,[z18,z1,z3,z120,z4,z5,z6]),(0,[z85,z121,z1,z3,z4,z5,z6]),(0,[z0,z1,z122,z3,z4,z5,z6]),(0,[z0,z1,z3,z123,z4,z5,z6]),(0,[z0,z1,z124,z3,z4,z5,z6]),(0,[z125,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z126,z5,z6])],[(0,[z127,z0,z1,z3,z4,z5,z6]),(0,[z128,z0,z1,z3,z4,z5,z6]),(0,[z18,z0,z1,z3,z4,z5,z6]),(0,[z1,z79,z3,z4,z5,z15,z6]),(0,[z0,z1,z3,z4,z5,z129,z6]),(0,[z130,z0,z3,z4,z5,z6,z66]),(0,[z0,z1,z3,z4,z5,z6,z51])],[(0,[z131,z0,z1,z3,z103,z5,z6]),(0,[z132,z0,z1,z3,z4,z5,z6]),(0,[z0,z3,z120,z4,z43,z5,z6]),(0,[z133,z0,z1,z3,z4,z5,z6]),(0,[z134,z0,z1,z3,z4,z5,z75]),(0,[z135,z0,z1,z3,z4,z5,z6])],[(0,[z136,z25,z1,z3,z4,z5,z6]),(0,[z137,z0,z1,z3,z4,z5,z6]),(0,[z131,z1,z3,z4,z26,z5,z6]),(0,[z1,z3,z4,z5,z6,z138,z66]),(1,[z1,z3,z139,z4,z5,z6]),(0,[z140,z0,z1,z3,z4,z5,z6])],[(0,[z65,z1,z3,z14,z4,z5,z6]),(1,[z25,z1,z3,z4,z5,z6]),(0,[z93,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z141,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z142]),(0,[z0,z1,z3,z143,z4,z5,z6])],[(0,[z59,z0,z1,z3,z144,z5,z6]),(0,[z145,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z122,z21,z5,z6]),(0,[z0,z146,z1,z3,z4,z5,z6])],[(0,[z131,z38,z1,z3,z4,z5,z6]),(0,[z147,z0,z1,z3,z4,z5,z6]),(0,[z0,z148,z1,z3,z4,z5,z6]),(0,[z149,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z150]),(0,[z0,z1,z3,z4,z5,z33,z6])],[(0,[z25,z1,z3,z120,z4,z5,z6]),(0,[z25,z1,z3,z4,z103,z5,z6]),(0,[z151,z0,z1,z3,z4,z5,z6]),(0,[z0,z152,z1,z3,z120,z5,z6]),(1,[z0,z1,z3,z7,z5,z6])]],
   [[(0,[z0,z1,z3,z4,z5,z153,z6]),(0,[z25,z0,z1,z3,z4,z5,z6]),(1,[z0,z3,z4,z154,z5,z6]),(0,[z155,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z156,z88,z6]),(0,[z0,z1,z3,z91,z4,z5,z6])],[(0,[z85,z157,z0,z3,z4,z5,z6]),(0,[z158,z0,z1,z3,z4,z5,z6]),(0,[z68,z0,z159,z3,z4,z5,z6]),(0,[z0,z1,z3,z160,z4,z5,z6])],[(0,[z1,z3,z14,z4,z73,z5,z6]),(0,[z18,z130,z1,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z15,z15,z6]),(0,[z0,z3,z161,z4,z5,z162,z6]),(0,[z163,z0,z1,z3,z4,z5,z6])],[(0,[z164,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z19,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z165]),(1,[z166,z0,z3,z4,z5,z6]),(1,[z0,z3,z4,z5,z6,z167])],[(0,[z131,z25,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z26,z5,z6]),(0,[z18,z18,z1,z3,z4,z5,z6]),(0,[z68,z1,z3,z4,z5,z15,z6]),(0,[z0,z152,z79,z3,z4,z5,z6]),(0,[z0,z3,z4,z43,z5,z6,z66]),(0,[z0,z1,z3,z168,z4,z5,z6]),(0,[z81,z0,z1,z3,z4,z5,z6])],[(0,[z169,z0,z1,z3,z4,z5,z6]),(1,[z54,z3,z14,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z170,z6]),(0,[z0,z1,z3,z4,z171,z6,z75]),(1,[z0,z3,z4,z5,z172,z6])],[(0,[z1,z3,z22,z4,z5,z15,z6]),(0,[z85,z0,z1,z161,z4,z5,z6]),(0,[z173,z0,z1,z3,z4,z5,z6])],[(0,[z0,z38,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z174,z4,z5,z6]),(0,[z136,z0,z1,z3,z4,z5,z6]),(0,[z61,z0,z1,z3,z4,z5,z33]),(0,[z0,z1,z3,z5,z31,z6,z45])]],
   [[(1,[z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z175,z4,z5,z6]),(0,[z0,z1,z3,z4,z43,z5,z6]),(0,[z176,z1,z177,z3,z4,z5,z6]),(0,[z0,z178,z1,z3,z4,z5,z6])],[(2,[z105,z1,z3,z4,z5]),(1,[z40,z1,z3,z4,z60,z6]),(0,[z41,z1,z3,z4,z26,z5,z6]),(0,[z18,z42,z1,z3,z4,z5,z6]),(0,[z1,z3,z161,z4,z5,z15,z6]),(1,[z1,z177,z3,z4,z5,z6]),(0,[z179,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z180,z3,z4,z5,z6]),(0,[z181,z0,z1,z3,z4,z5,z6]),(0,[z130,z1,z3,z14,z4,z5,z6]),(0,[z182,z18,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z183]),(0,[z184,z1,z3,z4,z185,z5,z6]),(0,[z0,z1,z3,z4,z5,z186,z6]),(0,[z0,z1,z3,z4,z5,z187,z6]),(0,[z188,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z189,z3,z4,z5,z6])],[(0,[z190,z0,z1,z3,z4,z5,z6]),(0,[z0,z191,z1,z3,z4,z5,z6]),(0,[z0,z192,z3,z21,z4,z5,z6]),(1,[z193,z0,z1,z3,z5,z45]),(0,[z194,z1,z3,z30,z4,z5,z6])],[(0,[z41,z38,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z3,z4,z5,z6]),(0,[z61,z0,z1,z3,z4,z5,z6]),(0,[z195,z1,z3,z4,z5,z15,z6]),(0,[z0,z1,z78,z3,z4,z5,z6]),(1,[z0,z71,z79,z4,z5,z6]),(0,[z0,z1,z3,z139,z4,z5,z6]),(0,[z68,z0,z196,z3,z4,z5,z6]),(0,[z197,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z198,z5,z6]),(0,[z85,z65,z0,z3,z4,z5,z6]),(0,[z0,z1,z199,z3,z4,z5,z6]),(0,[z200,z0,z1,z3,z4,z5,z6]),(0,[z201,z0,z1,z3,z4,z5,z6])],[(0,[z0,z202,z1,z3,z4,z5,z6]),(0,[z0,z3,z4,z26,z5,z203,z6]),(0,[z0,z1,z3,z4,z26,z5,z204]),(1,[z18,z1,z3,z4,z5,z33]),(0,[z1,z3,z4,z5,z15,z6,z47]),(0,[z0,z152,z3,z120,z4,z5,z6])],[(0,[z27,z25,z1,z3,z4,z5,z6]),(0,[z131,z1,z3,z4,z103,z5,z6]),(0,[z0,z1,z3,z4,z5,z205,z6]),(0,[z206,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z207])]],
   [[(0,[z105,z0,z1,z3,z14,z4,z5]),(0,[z25,z42,z1,z3,z4,z5,z6]),(0,[z131,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z208,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z209,z6]),(0,[z140,z0,z210,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z211]),(0,[z0,z1,z3,z4,z156,z33,z6])],[(0,[z0,z1,z3,z212,z4,z5,z6]),(0,[z18,z1,z84,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z213,z5,z6]),(0,[z0,z1,z214,z3,z4,z5,z6]),(0,[z0,z1,z215,z3,z4,z5,z6])],[(0,[z157,z0,z38,z3,z4,z5,z6]),(0,[z216,z0,z1,z3,z4,z5,z6]),(0,[z41,z25,z1,z3,z4,z5,z6]),(0,[z217,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z5,z204]),(0,[z0,z1,z3,z4,z218,z5,z6]),(0,[z0,z1,z3,z219,z4,z5,z6]),(0,[z0,z1,z122,z3,z44,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z220])],[(0,[z1,z3,z14,z4,z5,z110,z6]),(0,[z1,z122,z3,z14,z4,z5,z6]),(0,[z140,z0,z1,z3,z4,z171,z6]),(1,[z134,z0,z1,z3,z4,z75])],[(1,[z3,z13,z14,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z221,z6]),(0,[z0,z1,z3,z222,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z223]),(0,[z1,z3,z4,z156,z5,z15,z6]),(0,[z1,z3,z4,z5,z15,z6,z6]),(0,[z0,z1,z3,z4,z224,z5,z6])],[(0,[z157,z65,z1,z3,z4,z5,z6]),(0,[z225,z0,z1,z3,z4,z5,z6]),(0,[z1,z3,z4,z26,z5,z60,z6]),(0,[z0,z1,z226,z3,z4,z5,z6]),(1,[z227,z1,z3,z4,z5,z6]),(0,[z228,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z229]),(0,[z0,z230,z1,z3,z4,z5,z6]),(0,[z63,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z231,z3,z4,z5,z6]),(0,[z232,z18,z1,z3,z4,z5,z6]),(0,[z233,z0,z1,z3,z4,z5,z6]),(0,[z234,z0,z1,z3,z4,z5,z6]),(0,[z195,z0,z1,z3,z4,z5,z235]),(0,[z236,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z237,z4,z5,z6]),(0,[z0,z152,z1,z3,z44,z5,z6]),(0,[z0,z1,z3,z4,z5,z238,z6]),(0,[z140,z0,z1,z3,z4,z5,z211]),(0,[z239,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z240,z5,z6]),(0,[z0,z146,z3,z4,z156,z5,z6])]],
   [[(0,[z25,z1,z84,z3,z4,z5,z6]),(0,[z1,z3,z14,z4,z5,z6,z241]),(0,[z131,z0,z1,z3,z144,z5,z6]),(0,[z0,z1,z3,z4,z103,z5,z6]),(0,[z0,z1,z3,z4,z242,z5,z6]),(0,[z0,z1,z3,z120,z4,z5,z6]),(0,[z243,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z22,z73,z6]),(0,[z244,z0,z1,z3,z4,z5,z6])],[(0,[z0,z0,z1,z3,z4,z5,z6]),(0,[z1,z3,z14,z30,z4,z5,z6]),(0,[z0,z245,z1,z3,z4,z5,z6]),(1,[z184,z1,z3,z4,z5,z6]),(0,[z0,z159,z1,z3,z4,z5,z6]),(0,[z197,z0,z3,z4,z5,z98,z6]),(0,[z246,z0,z1,z3,z4,z5,z6])],[(0,[z1,z3,z14,z4,z5,z6,z75]),(0,[z85,z0,z3,z4,z43,z5,z6]),(1,[z1,z3,z4,z247,z5,z6]),(0,[z248,z0,z1,z3,z4,z5,z6]),(0,[z68,z0,z1,z16,z4,z5,z6]),(0,[z195,z0,z1,z3,z4,z73,z6])],[(0,[z131,z18,z1,z3,z4,z5,z6]),(0,[z27,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z249,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z250,z6]),(0,[z0,z176,z1,z3,z4,z5,z75]),(0,[z0,z1,z3,z30,z21,z5,z6]),(0,[z0,z1,z101,z3,z4,z88,z6]),(0,[z0,z1,z196,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z251,z5,z6]),(0,[z38,z1,z3,z4,z5,z60,z6]),(0,[z252,z0,z1,z3,z4,z5,z6]),(0,[z0,z253,z1,z3,z4,z5,z6]),(0,[z193,z18,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z254,z4,z5,z6]),(0,[z0,z1,z3,z4,z255,z5,z6]),(0,[z68,z256,z1,z3,z4,z5,z6]),(0,[z257,z0,z1,z3,z4,z5,z6])],[(0,[z41,z1,z3,z4,z103,z5,z6]),(0,[z68,z0,z1,z4,z5,z6,z47]),(0,[z0,z1,z3,z4,z258,z5,z6]),(0,[z0,z1,z3,z4,z259,z5,z6])],[(0,[z260,z1,z3,z14,z4,z5,z6]),(0,[z1,z3,z14,z4,z156,z5,z6]),(0,[z40,z25,z1,z3,z4,z5,z6]),(0,[z1,z3,z144,z4,z5,z15,z6]),(0,[z261,z18,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z262,z5,z6]),(0,[z0,z1,z263,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z264])],[(0,[z1,z3,z4,z103,z5,z60,z6]),(0,[z0,z71,z1,z161,z4,z5,z6]),(0,[z0,z265,z1,z3,z4,z5,z6]),(1,[z130,z0,z3,z4,z5,z66]),(0,[z0,z1,z3,z266,z4,z5,z6])]],
   [[(0,[z134,z1,z3,z14,z4,z5,z6]),(0,[z18,z152,z1,z3,z4,z5,z6]),(0,[z0,z267,z3,z4,z5,z15,z6]),(0,[z261,z227,z1,z3,z4,z5,z6]),(0,[z268,z0,z1,z3,z4,z5,z6])],[(0,[z1,z3,z14,z21,z4,z5,z6]),(0,[z0,z1,z3,z4,z269,z5,z6]),(0,[z270,z0,z1,z3,z4,z5,z6])],[(0,[z1,z3,z14,z14,z4,z5,z6]),(0,[z90,z0,z3,z4,z5,z6,z66])],[(0,[z0,z1,z3,z4,z271,z5,z6]),(0,[z70,z25,z1,z3,z4,z5,z6]),(0,[z0,z272,z1,z3,z4,z5,z6]),(0,[z0,z273,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z274]),(1,[z0,z275,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z276,z6]),(0,[z65,z0,z38,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z277,z6]),(0,[z18,z1,z278,z3,z4,z5,z6]),(0,[z18,z1,z16,z3,z4,z5,z6]),(1,[z279,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z5,z211])],[(0,[z1,z3,z14,z4,z5,z6,z45]),(0,[z0,z3,z13,z14,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z280]),(0,[z85,z1,z3,z4,z5,z15,z6]),(0,[z1,z3,z4,z44,z5,z15,z6]),(0,[z281,z0,z1,z3,z4,z5,z6]),(0,[z282,z1,z3,z4,z5,z6,z45])],[(0,[z0,z1,z3,z4,z283,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z284]),(0,[z0,z1,z3,z4,z285,z5,z6]),(0,[z286,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z287])],[(0,[z25,z152,z1,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z88,z15,z6]),(0,[z130,z0,z1,z3,z4,z5,z75])]],
   [[(0,[z0,z1,z3,z4,z5,z6,z288]),(0,[z289,z18,z1,z3,z4,z5,z6]),(0,[z18,z1,z3,z4,z44,z5,z6]),(0,[z0,z1,z3,z4,z290,z5,z6]),(1,[z1,z3,z4,z5,z6,z291]),(0,[z0,z1,z3,z4,z5,z292,z6]),(0,[z195,z81,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z293])],[(0,[z294,z0,z1,z3,z4,z5,z6]),(0,[z25,z1,z3,z295,z4,z5,z6]),(0,[z0,z1,z296,z3,z4,z5,z6]),(0,[z0,z297,z3,z4,z26,z5,z6]),(1,[z0,z152,z3,z120,z5,z6]),(0,[z0,z42,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z298,z6]),(0,[z299,z0,z1,z3,z4,z5,z6]),(0,[z195,z0,z1,z3,z5,z98,z6])],[(0,[z1,z3,z14,z4,z5,z31,z6]),(0,[z0,z1,z3,z4,z5,z6,z300]),(0,[z0,z1,z3,z4,z5,z6,z301]),(0,[z1,z3,z4,z5,z15,z6,z183]),(0,[z27,z0,z3,z4,z5,z110,z6]),(0,[z0,z1,z3,z4,z302,z5,z6]),(0,[z303,z0,z1,z3,z4,z5,z6]),(0,[z0,z176,z3,z4,z43,z5,z6]),(0,[z0,z1,z3,z21,z5,z6,z45])],[(0,[z0,z1,z304,z3,z4,z5,z6]),(0,[z1,z3,z14,z4,z171,z5,z6]),(0,[z25,z1,z16,z3,z4,z5,z6]),(0,[z40,z1,z3,z144,z4,z5,z6]),(0,[z0,z42,z71,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z247,z5,z6]),(0,[z90,z0,z1,z3,z4,z43,z6]),(0,[z0,z1,z3,z4,z305,z5,z6])],[(0,[z306,z0,z1,z3,z4,z5,z6]),(0,[z59,z25,z1,z3,z4,z5,z6]),(0,[z1,z3,z4,z26,z5,z15,z6]),(0,[z0,z42,z1,z3,z4,z162,z6])],[(0,[z157,z1,z3,z14,z4,z5,z6]),(0,[z1,z3,z14,z161,z4,z5,z6]),(0,[z307,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z308,z6])],[(0,[z0,z1,z3,z4,z4,z5,z6]),(0,[z309,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z310]),(0,[z0,z1,z3,z4,z311,z5,z6]),(0,[z0,z1,z3,z4,z5,z312,z6])],[(0,[z1,z3,z14,z4,z185,z5,z6]),(0,[z25,z1,z3,z4,z44,z5,z6]),(0,[z68,z25,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z313,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z314]),(0,[z0,z1,z3,z4,z5,z6,z315]),(0,[z0,z1,z3,z4,z316,z5,z6]),(0,[z317,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z318,z5,z6])]],
   [[(0,[z0,z3,z4,z185,z5,z6,z66]),(0,[z0,z319,z1,z3,z4,z5,z6])],[(0,[z0,z1,z84,z3,z4,z5,z6]),(0,[z320,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z321,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z322]),(0,[z18,z1,z79,z3,z4,z5,z6]),(0,[z0,z1,z3,z323,z4,z5,z6])],[(0,[z140,z25,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z324,z6]),(1,[z0,z1,z3,z325,z5,z6]),(0,[z68,z0,z1,z3,z7,z5,z6]),(1,[z0,z1,z326,z4,z5,z6])],[(0,[z0,z1,z3,z4,z327,z5,z6]),(0,[z65,z1,z3,z4,z5,z15,z6]),(0,[z90,z1,z3,z14,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z328]),(0,[z0,z1,z3,z4,z5,z329,z6]),(0,[z0,z3,z4,z5,z330,z88,z6]),(1,[z0,z1,z3,z331,z5,z6])],[(0,[z332,z0,z1,z3,z4,z5,z6])],[(0,[z333,z0,z1,z3,z4,z5,z6]),(0,[z1,z3,z14,z334,z4,z5,z6]),(0,[z40,z18,z1,z3,z4,z5,z6]),(0,[z18,z1,z3,z4,z5,z162,z6]),(0,[z27,z0,z1,z3,z44,z5,z6]),(0,[z68,z0,z1,z3,z4,z5,z47])],[(0,[z0,z1,z3,z4,z335,z5,z6]),(0,[z0,z1,z3,z4,z5,z336,z6]),(1,[z337,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z338]),(0,[z0,z1,z3,z326,z4,z5,z6])],[(0,[z1,z3,z117,z14,z4,z5,z6]),(0,[z195,z25,z1,z3,z4,z5,z6]),(0,[z18,z1,z3,z4,z5,z98,z6]),(0,[z0,z1,z339,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z340,z6]),(0,[z341,z0,z1,z3,z4,z5,z6]),(0,[z342,z0,z1,z3,z4,z5,z6])]],
   [[(0,[z65,z0,z3,z120,z4,z5,z6]),(0,[z343,z25,z1,z3,z4,z5,z6]),(0,[z25,z1,z79,z3,z4,z5,z6]),(0,[z344,z1,z3,z4,z5,z15,z6]),(0,[z0,z1,z3,z4,z5,z345,z6]),(0,[z0,z42,z3,z4,z5,z110,z6]),(0,[z0,z1,z3,z346,z4,z5,z6]),(0,[z0,z176,z1,z3,z4,z5,z110])],[(0,[z152,z1,z3,z14,z4,z5,z6]),(0,[z59,z1,z3,z144,z4,z5,z6]),(0,[z68,z61,z0,z1,z3,z4,z5]),(0,[z1,z3,z4,z5,z110,z15,z6]),(0,[z0,z1,z3,z4,z5,z6,z291]),(0,[z0,z1,z3,z4,z5,z6,z347]),(0,[z348,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z349,z5,z6])],[(0,[z0,z1,z350,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z351,z5,z6]),(0,[z1,z3,z175,z14,z4,z5,z6]),(0,[z70,z18,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z352,z6]),(0,[z0,z1,z3,z4,z5,z353,z6]),(0,[z354,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z355,z3,z4,z5,z6]),(1,[z356,z1,z3,z4,z5,z6]),(0,[z279,z0,z1,z3,z4,z5,z6]),(1,[z0,z3,z4,z5,z357,z6])],[(0,[z0,z1,z3,z4,z5,z358,z6]),(0,[z1,z16,z3,z14,z4,z5,z6]),(0,[z0,z1,z3,z4,z359,z5,z6]),(0,[z0,z1,z3,z4,z5,z360,z6]),(0,[z68,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z361,z6]),(1,[z65,z38,z3,z4,z5,z6]),(0,[z169,z25,z1,z3,z4,z5,z6]),(0,[z25,z1,z3,z4,z5,z162,z6]),(0,[z0,z1,z362,z3,z4,z5,z6]),(1,[z0,z3,z4,z5,z330,z6])],[(0,[z18,z1,z3,z144,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z363]),(0,[z0,z1,z122,z101,z4,z5,z6]),(0,[z364,z0,z1,z3,z4,z5,z6])],[(0,[z157,z41,z1,z3,z4,z5,z6]),(0,[z25,z1,z3,z4,z5,z98,z6]),(0,[z0,z1,z3,z4,z5,z203,z6]),(0,[z0,z1,z16,z3,z4,z5,z47])],[(0,[z157,z0,z84,z3,z4,z5,z6]),(0,[z38,z1,z84,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z365,z6]),(0,[z0,z1,z3,z366,z4,z5,z6]),(0,[z194,z0,z1,z3,z4,z5,z6])]],
   [[(0,[z367,z0,z1,z3,z4,z5,z6]),(1,[z1,z3,z4,z5,z368,z6]),(0,[z1,z3,z144,z4,z26,z5,z6]),(0,[z369,z0,z1,z3,z4,z5,z6]),(0,[z0,z152,z1,z3,z4,z5,z6]),(0,[z0,z275,z1,z3,z4,z5,z6])],[(0,[z25,z0,z1,z370,z4,z5,z6]),(0,[z0,z1,z3,z4,z26,z5,z322]),(0,[z18,z1,z3,z4,z371,z5,z6]),(0,[z130,z1,z3,z4,z5,z15,z6]),(1,[z0,z1,z3,z4,z372,z6])],[(0,[z1,z3,z14,z4,z5,z6,z66]),(0,[z1,z3,z14,z4,z5,z60,z6]),(0,[z0,z1,z3,z295,z4,z5,z6]),(0,[z0,z1,z3,z4,z154,z5,z6]),(0,[z0,z3,z4,z156,z5,z172,z6])],[(0,[z61,z25,z1,z3,z4,z5,z6]),(1,[z41,z1,z3,z4,z26,z6]),(0,[z0,z176,z1,z3,z4,z5,z66]),(0,[z195,z0,z1,z3,z4,z5,z6])],[(0,[z373,z0,z1,z3,z4,z5,z6]),(0,[z343,z0,z1,z3,z4,z5,z6]),(0,[z25,z1,z3,z144,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z374]),(0,[z55,z0,z3,z4,z103,z5,z6]),(0,[z0,z1,z278,z3,z4,z5,z6]),(0,[z0,z1,z3,z375,z4,z5,z6]),(0,[z130,z0,z1,z3,z4,z5,z110]),(0,[z0,z1,z16,z3,z4,z5,z6]),(1,[z0,z1,z16,z4,z5,z17]),(0,[z0,z1,z3,z376,z4,z5,z6])],[(1,[z0,z1,z3,z4,z5,z322]),(0,[z1,z3,z208,z4,z5,z15,z6]),(0,[z0,z1,z3,z4,z5,z6,z377]),(0,[z0,z1,z378,z3,z4,z5,z6]),(0,[z0,z1,z4,z44,z5,z88,z6])],[(0,[z0,z1,z3,z4,z5,z379,z6]),(0,[z0,z1,z380,z3,z4,z5,z6]),(0,[z130,z0,z3,z120,z4,z5,z6]),(0,[z0,z381,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z382,z6]),(0,[z0,z1,z3,z4,z5,z383,z6]),(0,[z134,z0,z1,z3,z4,z5,z33]),(0,[z0,z1,z384,z3,z4,z5,z6])],[(0,[z385,z0,z1,z3,z4,z5,z6]),(0,[z0,z337,z1,z3,z4,z5,z6]),(0,[z281,z1,z122,z3,z4,z5,z6]),(0,[z0,z1,z386,z3,z4,z5,z6])]],
   [[(0,[z387,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z388,z5,z6]),(0,[z0,z1,z3,z4,z44,z5,z6]),(1,[z0,z1,z3,z4,z389,z6]),(0,[z195,z0,z1,z3,z4,z98,z6])],[(0,[z0,z1,z3,z390,z4,z5,z6]),(0,[z1,z3,z14,z22,z4,z5,z6]),(0,[z260,z0,z1,z3,z4,z5,z6]),(0,[z140,z18,z1,z3,z4,z5,z6]),(0,[z391,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z392,z5,z6]),(0,[z0,z1,z3,z4,z5,z393,z6]),(0,[z394,z0,z1,z3,z4,z5,z6]),(0,[z261,z0,z1,z3,z21,z5,z6])],[(0,[z0,z1,z1,z3,z4,z5,z6]),(0,[z18,z1,z370,z3,z4,z5,z6]),(0,[z93,z18,z1,z3,z4,z5,z6]),(0,[z1,z122,z3,z4,z5,z15,z6]),(0,[z395,z1,z3,z4,z5,z15,z6]),(0,[z0,z1,z3,z4,z5,z6,z396])],[(0,[z0,z1,z397,z3,z4,z5,z6]),(0,[z398,z0,z1,z3,z4,z5,z6]),(0,[z105,z0,z1,z3,z4,z5,z6]),(1,[z131,z1,z3,z103,z5,z6]),(0,[z0,z152,z3,z4,z5,z162,z6]),(0,[z134,z0,z1,z3,z4,z5,z6])],[(0,[z18,z176,z1,z3,z4,z5,z6]),(0,[z261,z0,z1,z122,z4,z5,z6])],[(0,[z157,z1,z3,z4,z5,z60,z6]),(0,[z399,z1,z3,z4,z5,z15,z6]),(0,[z0,z1,z3,z4,z5,z400,z6]),(0,[z1,z3,z4,z5,z6,z114,z47]),(0,[z0,z1,z3,z4,z5,z45,z75])],[(0,[z1,z3,z14,z4,z401,z5,z6]),(0,[z402,z0,z1,z3,z4,z5,z6]),(0,[z1,z3,z120,z4,z5,z15,z6]),(1,[z1,z3,z4,z5,z6,z138]),(0,[z193,z0,z1,z3,z5,z6,z45])],[(0,[z403,z25,z1,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z15,z6,z315])]],
   [[(0,[z85,z25,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z404,z6])],[(0,[z65,z0,z84,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z368,z6]),(0,[z0,z1,z79,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z405,z6])],[(0,[z0,z1,z406,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z5,z6]),(0,[z407,z0,z1,z3,z4,z5,z6]),(1,[z267,z3,z4,z5,z15,z6]),(0,[z0,z42,z3,z161,z4,z5,z6]),(0,[z0,z1,z21,z4,z44,z5,z6]),(0,[z0,z1,z3,z4,z408,z5,z6])],[(0,[z169,z18,z1,z3,z4,z5,z6]),(0,[z25,z176,z1,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z15,z6,z328]),(0,[z0,z79,z3,z161,z4,z5,z6]),(0,[z0,z1,z3,z4,z33,z6,z75]),(0,[z0,z1,z3,z4,z5,z6,z409])],[(0,[z410,z0,z1,z3,z4,z5,z6]),(0,[z1,z3,z144,z4,z103,z5,z6]),(0,[z0,z1,z3,z4,z411,z5,z6]),(0,[z0,z42,z3,z4,z185,z5,z6]),(0,[z0,z1,z3,z412,z4,z5,z6]),(0,[z0,z1,z3,z4,z413,z5,z6]),(0,[z140,z414,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z5,z308])],[(0,[z0,z1,z415,z3,z4,z5,z6]),(0,[z131,z40,z1,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z416,z15,z6]),(0,[z0,z79,z3,z4,z185,z5,z6]),(0,[z0,z1,z3,z4,z5,z162,z6]),(1,[z1,z3,z112,z4,z5,z6]),(0,[z134,z0,z1,z3,z4,z156,z6])],[(1,[z18,z1,z3,z4,z5,z6]),(1,[z282,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z156,z5,z75])],[(0,[z417,z0,z1,z3,z4,z5,z6]),(0,[z134,z1,z3,z4,z5,z15,z6]),(0,[z0,z1,z3,z4,z5,z98,z6])]],
   [[(1,[z25,z1,z14,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z418,z6]),(0,[z18,z1,z419,z3,z4,z5,z6]),(1,[z244,z1,z3,z4,z5,z6])],[(0,[z1,z101,z3,z14,z4,z5,z6]),(0,[z1,z3,z14,z4,z5,z15,z6]),(0,[z1,z3,z4,z5,z15,z6,z291]),(1,[z420,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z421,z4,z5,z6]),(1,[z1,z3,z4,z422,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z423])],[(0,[z403,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z424]),(0,[z0,z1,z3,z4,z425,z5,z6]),(0,[z27,z130,z0,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z33,z17]),(0,[z0,z1,z426,z3,z4,z5,z6])],[(0,[z25,z0,z1,z14,z4,z5,z6]),(0,[z0,z1,z3,z427,z4,z5,z6]),(1,[z3,z4,z5,z15,z6,z183]),(0,[z85,z0,z1,z3,z4,z5,z6]),(1,[z428,z1,z3,z4,z5,z6]),(0,[z429,z0,z1,z3,z4,z5,z6])],[(1,[z157,z84,z3,z4,z5,z6]),(0,[z0,z1,z3,z430,z4,z5,z6]),(0,[z54,z1,z3,z14,z4,z5,z6]),(0,[z0,z1,z3,z144,z4,z5,z6]),(0,[z431,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z416,z6]),(0,[z85,z0,z1,z79,z4,z5,z6]),(0,[z1,z3,z4,z5,z432,z98,z6])],[(0,[z157,z0,z79,z3,z4,z5,z6]),(0,[z0,z1,z3,z13,z4,z5,z6]),(0,[z25,z1,z3,z4,z5,z433,z6]),(0,[z0,z1,z3,z4,z5,z6,z138]),(0,[z0,z1,z210,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z6,z167,z47]),(0,[z193,z0,z263,z3,z4,z5,z6]),(0,[z193,z0,z434,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z156,z5,z33])]],
   [[(0,[z193,z1,z3,z14,z4,z5,z6]),(0,[z27,z0,z71,z3,z4,z5,z6]),(1,[z369,z1,z3,z4,z5,z6]),(1,[z0,z42,z3,z4,z43,z6]),(0,[z0,z1,z3,z4,z435,z5,z6]),(0,[z166,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z436])],[(0,[z0,z1,z3,z4,z371,z5,z6]),(1,[z121,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z80,z4,z5,z6]),(0,[z261,z437,z1,z3,z4,z5,z6]),(1,[z414,z1,z3,z4,z5,z6])],[(0,[z261,z1,z3,z14,z4,z5,z6]),(1,[z0,z1,z3,z438,z5,z6]),(0,[z0,z1,z3,z4,z5,z31,z75])],[(0,[z157,z0,z3,z4,z5,z162,z6]),(0,[z0,z1,z3,z4,z5,z439,z6]),(0,[z18,z0,z1,z3,z4,z5,z241]),(0,[z440,z0,z1,z3,z4,z5,z6]),(0,[z441,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z442,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z443,z6])],[(0,[z157,z1,z3,z4,z5,z15,z6]),(0,[z1,z3,z14,z4,z5,z17,z6]),(1,[z0,z3,z57,z4,z5,z6])],[(0,[z1,z3,z14,z4,z5,z88,z6]),(0,[z1,z3,z14,z4,z5,z6,z47]),(0,[z444,z0,z1,z3,z4,z5,z6]),(0,[z445,z0,z1,z3,z4,z5,z6]),(0,[z90,z0,z79,z3,z4,z5,z6]),(0,[z446,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z101,z4,z171,z6])],[(0,[z0,z1,z3,z4,z5,z6,z447]),(0,[z0,z448,z1,z3,z4,z5,z6]),(1,[z61,z1,z3,z4,z5,z15]),(0,[z0,z1,z3,z4,z449,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z450]),(0,[z451,z0,z1,z3,z4,z5,z6]),(0,[z68,z0,z1,z3,z331,z5,z6]),(0,[z0,z1,z3,z112,z4,z5,z6])],[(0,[z18,z157,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z452,z6]),(0,[z18,z1,z3,z4,z453,z5,z6]),(0,[z68,z18,z0,z1,z3,z4,z5]),(0,[z0,z176,z1,z3,z4,z5,z33]),(0,[z454,z0,z1,z3,z4,z5,z6])]],
   [[(0,[z1,z3,z14,z4,z5,z6,z100]),(0,[z25,z1,z3,z4,z455,z5,z6]),(0,[z456,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z457,z5,z6]),(0,[z140,z0,z1,z3,z325,z5,z6]),(1,[z68,z0,z1,z4,z5,z47]),(1,[z1,z3,z4,z5,z432,z6])],[(0,[z157,z0,z3,z120,z4,z5,z6]),(0,[z157,z0,z42,z3,z4,z5,z6]),(0,[z27,z18,z1,z3,z4,z5,z6]),(0,[z1,z3,z4,z171,z5,z15,z6])],[(0,[z65,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z458,z3,z4,z5,z6]),(0,[z459,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z460,z6]),(0,[z461,z0,z1,z3,z4,z5,z6]),(0,[z90,z1,z3,z4,z5,z15,z6]),(0,[z0,z1,z3,z462,z4,z5,z6]),(0,[z0,z1,z101,z4,z171,z5,z6]),(0,[z0,z420,z1,z3,z4,z5,z6])],[(0,[z38,z1,z3,z144,z4,z5,z6]),(0,[z0,z1,z463,z3,z4,z5,z6]),(0,[z18,z1,z3,z4,z73,z5,z6]),(0,[z85,z0,z3,z4,z5,z110,z6]),(0,[z0,z1,z3,z464,z4,z5,z6]),(0,[z184,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z465]),(0,[z0,z1,z3,z466,z4,z5,z6]),(0,[z0,z1,z4,z5,z17,z6,z47]),(0,[z0,z1,z3,z4,z5,z467,z6]),(0,[z0,z1,z3,z4,z422,z5,z6])],[(1,[z1,z3,z468,z14,z4,z5]),(0,[z469,z0,z1,z3,z4,z5,z6]),(0,[z470,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z471,z4,z5,z6]),(0,[z0,z176,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z472,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z49]),(0,[z0,z1,z3,z4,z473,z5,z6])],[(0,[z0,z3,z4,z5,z15,z6,z183]),(1,[z261,z0,z1,z44,z5,z6]),(0,[z0,z428,z1,z3,z4,z5,z6]),(0,[z195,z0,z1,z326,z4,z5,z6])],[(0,[z0,z1,z474,z3,z4,z5,z6]),(0,[z0,z1,z3,z475,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z476,z6])],[(0,[z0,z1,z477,z3,z4,z5,z6]),(0,[z0,z478,z1,z3,z4,z5,z6]),(0,[z344,z0,z1,z3,z4,z5,z6]),(0,[z90,z0,z3,z120,z4,z5,z6]),(0,[z90,z0,z42,z3,z4,z5,z6]),(0,[z479,z0,z1,z3,z4,z5,z6])]],
   [[(0,[z480,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z481,z6]),(0,[z152,z1,z3,z4,z5,z15,z6]),(0,[z0,z482,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z483]),(0,[z65,z0,z79,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z484,z5,z6]),(0,[z0,z1,z122,z3,z21,z5,z6]),(0,[z0,z1,z3,z4,z5,z485,z6])],[(0,[z25,z1,z3,z4,z73,z5,z6]),(0,[z1,z16,z3,z4,z5,z15,z6]),(0,[z0,z1,z3,z4,z5,z6,z486])],[(0,[z18,z65,z1,z3,z4,z5,z6]),(0,[z41,z0,z1,z3,z4,z26,z6]),(0,[z130,z0,z1,z3,z4,z5,z33]),(1,[z0,z124,z3,z4,z5,z6]),(0,[z0,z1,z487,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z488,z5,z6]),(0,[z489,z0,z1,z3,z4,z5,z6]),(0,[z490,z0,z1,z3,z4,z5,z6]),(0,[z68,z0,z1,z3,z4,z372,z6])],[(0,[z65,z0,z3,z4,z5,z162,z6]),(0,[z1,z3,z14,z4,z5,z33,z6]),(0,[z491,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z492,z3,z4,z5,z6]),(0,[z0,z1,z493,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z494,z6])],[(0,[z55,z0,z1,z3,z4,z5,z6]),(1,[z1,z3,z375,z4,z5,z6]),(0,[z495,z0,z1,z3,z4,z5,z6]),(0,[z0,z496,z1,z3,z4,z5,z6])],[(0,[z1,z3,z468,z14,z4,z5,z6]),(0,[z294,z18,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z497,z6]),(0,[z0,z1,z3,z498,z4,z5,z6]),(0,[z0,z71,z1,z79,z4,z5,z6]),(0,[z0,z1,z3,z4,z499,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z500]),(1,[z501,z1,z3,z4,z5,z6]),(1,[z36,z1,z3,z4,z5,z6]),(0,[z348,z1,z3,z4,z5,z98,z6])]],
   [[(0,[z0,z1,z3,z502,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z433,z6]),(0,[z0,z1,z3,z4,z5,z6,z503]),(0,[z0,z1,z419,z3,z4,z5,z6]),(0,[z0,z3,z161,z4,z5,z6,z66]),(0,[z369,z1,z79,z3,z4,z5,z6]),(0,[z130,z0,z1,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z6,z49,z45])],[(0,[z504,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z432,z6])],[(0,[z0,z1,z3,z505,z4,z5,z6]),(0,[z25,z1,z506,z3,z4,z5,z6]),(0,[z18,z0,z1,z3,z4,z5,z15])],[(0,[z65,z0,z42,z3,z4,z5,z6]),(0,[z1,z3,z14,z4,z26,z5,z6]),(0,[z18,z1,z3,z507,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z508,z6]),(0,[z0,z176,z3,z4,z5,z110,z6]),(0,[z0,z1,z3,z4,z5,z509,z6])],[(0,[z510,z0,z1,z3,z4,z5,z6]),(0,[z18,z1,z3,z4,z5,z110,z6]),(0,[z0,z71,z79,z3,z4,z5,z6]),(0,[z195,z0,z1,z3,z22,z5,z6]),(0,[z0,z1,z3,z4,z5,z357,z6]),(0,[z0,z1,z3,z4,z5,z511,z6])],[(0,[z0,z1,z3,z468,z14,z4,z5]),(0,[z27,z0,z152,z3,z4,z5,z6])],[(0,[z131,z157,z1,z3,z4,z5,z6]),(0,[z1,z3,z14,z174,z4,z5,z6]),(0,[z70,z1,z3,z14,z4,z5,z6]),(0,[z1,z3,z4,z5,z15,z6,z241]),(0,[z501,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z512,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z513,z5,z6])],[(0,[z1,z3,z14,z4,z43,z5,z6]),(0,[z40,z0,z1,z3,z4,z26,z6]),(0,[z130,z0,z79,z3,z4,z5,z6]),(0,[z514,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z515,z6]),(0,[z0,z1,z3,z4,z5,z6,z516])]],
   [[(1,[z25,z1,z370,z4,z5,z6]),(0,[z0,z1,z517,z3,z4,z5,z6]),(0,[z0,z1,z3,z518,z4,z5,z6]),(0,[z0,z1,z3,z519,z4,z5,z6])],[(0,[z157,z0,z176,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z520,z5,z6]),(0,[z0,z1,z3,z4,z455,z5,z6]),(0,[z395,z0,z1,z3,z4,z5,z6]),(0,[z521,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z522,z6]),(0,[z18,z1,z3,z4,z5,z6,z241]),(0,[z0,z1,z3,z4,z5,z6,z523]),(0,[z0,z1,z3,z4,z5,z235,z6]),(0,[z0,z1,z524,z3,z4,z5,z6])],[(0,[z25,z1,z3,z4,z5,z525,z6]),(0,[z134,z25,z1,z3,z4,z5,z6]),(0,[z18,z1,z3,z30,z4,z5,z6]),(0,[z0,z1,z3,z4,z526,z5,z6]),(0,[z0,z1,z3,z4,z5,z527,z6]),(0,[z528,z0,z1,z3,z4,z5,z6]),(1,[z1,z3,z4,z5,z529,z6])],[(0,[z0,z1,z3,z4,z530,z5,z6]),(0,[z25,z1,z3,z4,z5,z110,z6]),(0,[z531,z0,z1,z3,z4,z5,z6]),(0,[z18,z1,z3,z4,z5,z6,z75]),(0,[z532,z0,z1,z3,z4,z5,z6]),(0,[z130,z0,z3,z4,z5,z162,z6]),(0,[z140,z0,z319,z3,z4,z5,z6]),(0,[z140,z0,z1,z101,z4,z5,z6])],[(0,[z399,z0,z1,z3,z4,z5,z6]),(0,[z504,z18,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z533,z6]),(0,[z1,z3,z4,z73,z5,z15,z6]),(1,[z0,z3,z4,z5,z6,z183])],[(0,[z106,z1,z3,z14,z4,z5,z6]),(0,[z18,z1,z3,z4,z5,z534,z6]),(0,[z0,z71,z3,z120,z4,z5,z6]),(0,[z0,z1,z3,z4,z535,z5,z6]),(0,[z0,z536,z1,z3,z4,z5,z6]),(0,[z46,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z537,z6])],[(0,[z59,z1,z3,z14,z4,z5,z6]),(0,[z18,z1,z3,z4,z156,z5,z6]),(0,[z0,z1,z3,z4,z453,z5,z6]),(0,[z27,z0,z3,z161,z4,z5,z6]),(0,[z0,z152,z1,z3,z185,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z538]),(0,[z0,z539,z1,z3,z4,z5,z6])]],
   [[(0,[z0,z540,z1,z3,z4,z5,z6]),(0,[z0,z541,z1,z3,z4,z5,z6]),(0,[z54,z0,z1,z3,z4,z5,z6]),(0,[z25,z1,z3,z4,z5,z6,z241]),(0,[z18,z59,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z542,z4,z5,z6]),(0,[z1,z3,z4,z5,z98,z15,z6]),(0,[z0,z1,z3,z4,z438,z5,z6]),(0,[z0,z1,z3,z4,z372,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z167]),(0,[z193,z0,z1,z3,z4,z5,z45]),(0,[z135,z1,z3,z4,z156,z5,z6])],[(0,[z169,z0,z1,z370,z4,z5,z6]),(0,[z543,z1,z3,z14,z4,z5,z6]),(0,[z25,z1,z3,z30,z4,z5,z6]),(0,[z68,z18,z1,z3,z4,z5,z6]),(0,[z27,z0,z3,z4,z185,z5,z6]),(0,[z130,z0,z42,z3,z4,z5,z6]),(0,[z0,z1,z4,z171,z5,z88,z6])],[(1,[z1,z3,z4,z5,z525,z6]),(0,[z25,z1,z3,z4,z5,z6,z75]),(0,[z18,z1,z3,z21,z4,z5,z6]),(0,[z85,z337,z1,z3,z4,z5,z6]),(0,[z0,z1,z544,z3,z4,z5,z6]),(0,[z356,z1,z3,z4,z5,z6,z66]),(0,[z0,z1,z3,z4,z545,z5,z6]),(0,[z140,z0,z1,z3,z4,z5,z308]),(0,[z0,z1,z3,z4,z546,z5,z6]),(0,[z0,z1,z3,z4,z5,z172,z6])],[(0,[z0,z1,z3,z4,z5,z6,z547]),(0,[z1,z3,z14,z4,z5,z221,z6]),(0,[z1,z370,z3,z14,z4,z5,z6]),(0,[z18,z1,z3,z14,z4,z5,z6]),(0,[z0,z42,z152,z3,z4,z5,z6]),(0,[z0,z1,z548,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z73,z5,z6])],[(0,[z549,z0,z1,z3,z4,z5,z6])],[(0,[z140,z1,z3,z14,z4,z5,z6]),(0,[z61,z0,z1,z3,z4,z5,z15]),(0,[z550,z0,z1,z3,z4,z5,z6]),(0,[z279,z176,z1,z3,z4,z5,z6]),(1,[z257,z1,z3,z4,z5,z6]),(1,[z0,z381,z3,z4,z5,z6]),(0,[z0,z1,z3,z551,z4,z5,z6])],[(0,[z25,z1,z3,z4,z156,z5,z6]),(0,[z18,z1,z3,z4,z5,z6,z45]),(0,[z0,z1,z3,z552,z4,z5,z6]),(0,[z0,z3,z120,z4,z5,z110,z6]),(1,[z90,z0,z3,z4,z162,z6]),(0,[z0,z3,z4,z43,z5,z162,z6]),(0,[z0,z1,z3,z4,z5,z553,z6]),(0,[z0,z1,z3,z30,z4,z5,z31])],[(0,[z554,z0,z1,z3,z4,z5,z6]),(0,[z157,z25,z1,z3,z4,z5,z6]),(0,[z1,z3,z14,z120,z4,z5,z6]),(0,[z1,z3,z14,z4,z103,z5,z6])]],
   [[(0,[z0,z1,z3,z4,z5,z555,z6]),(0,[z0,z1,z3,z556,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z557,z6]),(0,[z0,z558,z1,z3,z4,z5,z6]),(0,[z1,z101,z3,z4,z5,z15,z6]),(0,[z1,z3,z4,z5,z15,z31,z6]),(1,[z0,z1,z3,z4,z5,z298]),(0,[z0,z1,z3,z4,z43,z5,z298]),(0,[z0,z1,z3,z44,z5,z98,z6]),(1,[z0,z319,z3,z4,z5,z6]),(0,[z282,z0,z1,z3,z4,z5,z6])],[(0,[z559,z0,z1,z3,z4,z5,z6]),(0,[z25,z1,z3,z21,z4,z5,z6]),(0,[z195,z18,z1,z3,z4,z5,z6]),(0,[z560,z0,z1,z3,z4,z5,z6]),(1,[z197,z0,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z561,z6])],[(0,[z0,z1,z3,z4,z562,z5,z6]),(0,[z25,z1,z3,z14,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z563,z6]),(0,[z0,z1,z3,z4,z5,z564,z6]),(0,[z130,z0,z1,z3,z4,z5,z66]),(0,[z140,z428,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z389,z6])],[(0,[z65,z0,z176,z3,z4,z5,z6]),(0,[z0,z1,z506,z3,z4,z5,z6]),(0,[z18,z1,z3,z4,z5,z31,z6]),(0,[z0,z1,z3,z4,z5,z6,z565]),(0,[z0,z1,z3,z566,z4,z5,z6]),(1,[z0,z1,z487,z4,z5,z6]),(1,[z0,z1,z3,z4,z5,z516]),(0,[z0,z567,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z529,z6])],[(0,[z25,z1,z370,z3,z4,z5,z6]),(0,[z18,z1,z3,z4,z171,z5,z6]),(0,[z18,z0,z1,z16,z3,z4,z5]),(0,[z27,z0,z1,z3,z21,z5,z6]),(0,[z0,z1,z568,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z569]),(0,[z195,z420,z1,z3,z4,z5,z6]),(0,[z193,z0,z1,z3,z30,z5,z6])],[(0,[z0,z1,z570,z3,z4,z5,z6]),(0,[z25,z571,z1,z3,z4,z5,z6]),(0,[z90,z25,z1,z3,z4,z5,z6]),(0,[z25,z1,z3,z4,z5,z6,z45]),(0,[z1,z3,z4,z43,z5,z15,z6]),(0,[z1,z3,z4,z5,z572,z15,z6]),(0,[z0,z1,z3,z4,z5,z573,z6]),(0,[z356,z0,z1,z3,z4,z5,z6])],[(0,[z18,z1,z3,z161,z4,z5,z6]),(0,[z574,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z122,z21,z4,z5,z6]),(1,[z0,z196,z3,z4,z5,z6]),(0,[z575,z0,z1,z3,z4,z5,z6])],[(0,[z169,z1,z3,z14,z4,z5,z6]),(0,[z1,z3,z3,z14,z4,z5,z6]),(0,[z41,z0,z1,z3,z4,z60,z6]),(0,[z0,z1,z3,z4,z5,z6,z576]),(0,[z193,z1,z3,z4,z5,z15,z6]),(0,[z0,z1,z122,z4,z5,z88,z6]),(0,[z140,z0,z1,z3,z4,z88,z6])]],
   [[(1,[z93,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z577,z6]),(0,[z18,z71,z1,z3,z4,z5,z6]),(0,[z18,z1,z3,z4,z185,z5,z6]),(0,[z0,z578,z1,z3,z4,z5,z6]),(0,[z0,z579,z1,z3,z4,z5,z6])],[(0,[z176,z1,z3,z14,z4,z5,z6]),(0,[z134,z18,z1,z3,z4,z5,z6]),(0,[z261,z1,z3,z4,z5,z15,z6]),(0,[z0,z1,z3,z4,z5,z6,z580]),(0,[z0,z1,z3,z4,z5,z581,z6]),(1,[z437,z1,z3,z4,z5,z6]),(1,[z0,z263,z3,z4,z5,z6]),(1,[z0,z434,z3,z4,z5,z6]),(0,[z582,z0,z1,z3,z4,z5,z6])],[(0,[z583,z0,z1,z3,z4,z5,z6]),(1,[z1,z3,z14,z4,z5,z6]),(0,[z25,z1,z3,z4,z5,z31,z6]),(0,[z584,z0,z1,z3,z4,z5,z6]),(0,[z585,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z586,z4,z5,z6]),(1,[z0,z273,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z587])],[(0,[z157,z0,z1,z3,z4,z5,z6]),(0,[z65,z38,z1,z3,z4,z5,z6]),(1,[z169,z1,z14,z4,z5,z6]),(0,[z25,z1,z3,z4,z171,z5,z6]),(0,[z0,z1,z3,z4,z5,z525,z6]),(0,[z0,z1,z3,z4,z325,z5,z6])],[(0,[z588,z25,z1,z3,z4,z5,z6]),(0,[z18,z41,z1,z3,z4,z5,z6]),(0,[z85,z130,z0,z3,z4,z5,z6]),(0,[z1,z3,z4,z43,z5,z56,z6]),(0,[z0,z1,z3,z4,z5,z110,z6]),(0,[z0,z1,z3,z4,z331,z5,z6]),(0,[z0,z1,z3,z4,z5,z17,z75]),(0,[z134,z0,z1,z3,z4,z6,z75])],[(0,[z589,z0,z1,z3,z4,z5,z6]),(0,[z1,z3,z14,z4,z283,z5,z6]),(0,[z25,z1,z3,z161,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z590,z6]),(0,[z591,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z592,z5,z6])],[(0,[z61,z1,z3,z14,z4,z5,z6]),(0,[z1,z79,z3,z375,z4,z5,z6]),(0,[z27,z90,z0,z3,z4,z5,z6]),(0,[z0,z1,z593,z3,z4,z5,z6])],[(0,[z25,z71,z1,z3,z4,z5,z6]),(0,[z25,z1,z3,z4,z185,z5,z6]),(0,[z131,z59,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z594,z6]),(1,[z59,z1,z3,z144,z5,z6]),(0,[z0,z1,z3,z30,z4,z5,z45])]],
   [[(0,[z0,z1,z3,z4,z5,z595,z6]),(0,[z267,z1,z3,z4,z5,z15,z6]),(0,[z0,z1,z3,z4,z5,z6,z596]),(0,[z0,z1,z3,z4,z597,z5,z6])],[(0,[z65,z25,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z598,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z241]),(0,[z85,z0,z71,z3,z4,z5,z6]),(0,[z90,z0,z1,z3,z4,z5,z6]),(0,[z130,z0,z176,z3,z4,z5,z6]),(1,[z1,z3,z4,z5,z6,z74])],[(0,[z131,z1,z3,z14,z4,z5,z6]),(0,[z18,z1,z101,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z162,z110,z6]),(0,[z0,z1,z3,z30,z4,z5,z6]),(0,[z244,z1,z3,z4,z5,z6,z75])],[(0,[z40,z0,z1,z3,z4,z60,z6]),(0,[z1,z3,z4,z5,z368,z15,z6]),(0,[z599,z0,z1,z3,z4,z5,z6]),(1,[z163,z1,z3,z4,z5,z6]),(1,[z348,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z600,z6]),(0,[z0,z1,z3,z4,z5,z6,z75])],[(0,[z169,z0,z1,z14,z4,z5,z6]),(0,[z25,z1,z3,z4,z601,z5,z6]),(0,[z0,z1,z3,z602,z4,z5,z6]),(1,[z0,z1,z3,z80,z5,z6]),(0,[z90,z0,z1,z3,z4,z162,z6]),(0,[z603,z0,z1,z3,z4,z5,z6]),(1,[z63,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z604,z6]),(0,[z1,z3,z4,z5,z162,z15,z6]),(0,[z0,z79,z3,z4,z43,z5,z6]),(0,[z27,z0,z1,z3,z185,z5,z6]),(0,[z0,z1,z3,z605,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z534,z6]),(1,[z85,z0,z161,z4,z5,z6]),(0,[z0,z1,z3,z4,z88,z6,z75]),(1,[z256,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z606,z4,z5,z6]),(0,[z607,z0,z1,z3,z4,z5,z6]),(0,[z261,z0,z1,z3,z44,z5,z6]),(0,[z0,z1,z3,z4,z5,z33,z31]),(0,[z0,z1,z3,z4,z156,z5,z6])]],
   [[(0,[z588,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z608,z3,z4,z5,z6]),(0,[z18,z0,z1,z3,z4,z5,z75]),(1,[z0,z1,z3,z4,z5,z569]),(0,[z0,z1,z3,z4,z43,z5,z569]),(0,[z0,z3,z4,z5,z110,z6,z66])],[(0,[z25,z1,z101,z3,z4,z5,z6]),(0,[z0,z1,z3,z22,z44,z5,z6]),(1,[z140,z0,z1,z4,z88,z6]),(1,[z46,z0,z3,z4,z5,z6]),(0,[z0,z1,z3,z22,z4,z73,z6])],[(0,[z0,z1,z3,z4,z609,z5,z6]),(0,[z85,z18,z1,z3,z4,z5,z6]),(0,[z610,z0,z1,z3,z4,z5,z6]),(0,[z0,z3,z120,z4,z185,z5,z6]),(0,[z0,z437,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z21,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z572,z6]),(0,[z0,z1,z3,z611,z4,z5,z6]),(0,[z0,z1,z3,z14,z4,z5,z6]),(0,[z0,z1,z3,z4,z612,z5,z6]),(0,[z18,z1,z3,z4,z5,z60,z6]),(0,[z18,z1,z3,z4,z5,z6,z66]),(0,[z613,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z614,z5,z6]),(0,[z0,z1,z79,z3,z438,z5,z6]),(0,[z0,z192,z1,z3,z4,z5,z6]),(0,[z163,z1,z101,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z615])],[(0,[z90,z0,z3,z4,z5,z162,z6]),(1,[z281,z1,z3,z4,z5,z6])],[(0,[z0,z1,z370,z3,z4,z5,z6]),(0,[z27,z1,z3,z14,z4,z5,z6]),(0,[z41,z59,z1,z3,z4,z5,z6])],[(1,[z0,z1,z3,z468,z4,z5]),(0,[z0,z571,z1,z3,z4,z5,z6]),(1,[z0,z267,z3,z4,z5,z6]),(0,[z616,z0,z1,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z368,z17,z6]),(0,[z195,z0,z124,z3,z4,z5,z6]),(0,[z0,z434,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z45])],[(0,[z130,z25,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z617,z5,z6]),(0,[z0,z1,z3,z4,z5,z618,z6])]],
   [[(0,[z41,z1,z3,z14,z4,z5,z6]),(0,[z619,z0,z1,z3,z4,z5,z6]),(0,[z501,z1,z3,z4,z43,z5,z6])],[(0,[z18,z0,z1,z3,z4,z5,z33]),(0,[z0,z620,z1,z3,z4,z5,z6]),(0,[z0,z176,z71,z3,z4,z5,z6]),(0,[z0,z621,z1,z3,z4,z5,z6]),(0,[z227,z0,z1,z3,z4,z5,z6]),(0,[z0,z275,z3,z4,z5,z33,z6])],[(0,[z25,z1,z3,z4,z5,z6,z66]),(0,[z25,z1,z3,z4,z5,z60,z6]),(0,[z0,z1,z3,z4,z5,z622,z6]),(0,[z0,z297,z1,z3,z4,z5,z6]),(0,[z18,z1,z3,z22,z4,z5,z6]),(0,[z0,z1,z3,z4,z623,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z74])],[(0,[z157,z1,z84,z3,z4,z5,z6]),(0,[z0,z1,z624,z3,z4,z5,z6]),(0,[z42,z1,z3,z14,z4,z5,z6]),(0,[z0,z42,z1,z3,z4,z43,z6]),(0,[z0,z1,z3,z4,z5,z31,z6])],[(0,[z67,z1,z3,z4,z5,z15,z6]),(0,[z0,z1,z3,z4,z5,z625,z6]),(0,[z0,z1,z3,z4,z626,z5,z6]),(0,[z0,z1,z3,z4,z171,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z627])],[(0,[z628,z0,z1,z3,z4,z5,z6]),(0,[z71,z1,z3,z14,z4,z5,z6]),(0,[z70,z1,z3,z4,z5,z15,z6]),(0,[z0,z1,z3,z4,z5,z33,z47])],[(0,[z0,z1,z3,z161,z4,z5,z6]),(1,[z195,z0,z1,z3,z98,z6]),(0,[z629,z0,z1,z3,z4,z5,z6]),(1,[z429,z0,z3,z4,z5,z6])],[(0,[z1,z84,z3,z14,z4,z5,z6]),(1,[z0,z297,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z630,z6]),(0,[z0,z1,z3,z4,z5,z6,z631]),(0,[z1,z122,z3,z139,z4,z5,z6]),(1,[z0,z192,z3,z4,z5,z6]),(0,[z0,z256,z1,z3,z4,z5,z6])]],
   [[(0,[z0,z1,z3,z468,z4,z5,z6]),(0,[z1,z3,z4,z5,z60,z15,z6]),(0,[z0,z71,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z185,z5,z6]),(0,[z0,z1,z3,z4,z5,z33,z45]),(0,[z1,z3,z30,z4,z422,z5,z6])],[(0,[z38,z1,z3,z14,z4,z5,z6]),(1,[z105,z1,z3,z14,z4,z5]),(0,[z25,z1,z3,z22,z4,z5,z6]),(1,[z0,z3,z4,z5,z203,z6]),(0,[z61,z0,z1,z3,z4,z5,z241]),(0,[z0,z152,z1,z3,z21,z5,z6]),(0,[z0,z1,z632,z3,z4,z5,z6])],[(0,[z470,z18,z1,z3,z4,z5,z6]),(0,[z0,z3,z4,z185,z5,z162,z6]),(1,[z0,z176,z3,z4,z5,z110]),(0,[z36,z0,z1,z3,z4,z5,z6]),(0,[z193,z0,z1,z3,z4,z5,z31])],[(0,[z61,z0,z1,z3,z4,z5,z75]),(1,[z27,z0,z3,z185,z5,z6]),(0,[z1,z3,z4,z247,z185,z5,z6]),(0,[z0,z1,z101,z4,z44,z5,z6]),(0,[z633,z0,z1,z3,z4,z5,z6])],[(0,[z182,z0,z1,z3,z4,z5,z6]),(0,[z634,z0,z1,z3,z4,z5,z6]),(0,[z40,z1,z3,z14,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z204,z6]),(0,[z0,z1,z3,z4,z5,z6,z635]),(0,[z0,z1,z3,z4,z5,z6,z636]),(0,[z0,z1,z3,z30,z44,z5,z6]),(0,[z0,z1,z3,z4,z637,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z638])],[(0,[z0,z1,z3,z4,z601,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z639])],[(0,[z0,z1,z3,z334,z4,z5,z6]),(0,[z59,z1,z3,z4,z5,z15,z6]),(0,[z85,z0,z152,z3,z4,z5,z6]),(0,[z640,z0,z1,z3,z4,z5,z6]),(0,[z68,z0,z1,z3,z4,z389,z6])],[(0,[z1,z3,z14,z4,z44,z5,z6]),(0,[z0,z641,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z642,z4,z5,z6]),(0,[z643,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z644,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z156,z171,z6])]],
   [[(0,[z27,z157,z0,z3,z4,z5,z6]),(1,[z18,z1,z3,z4,z5,z241]),(0,[z68,z257,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z645,z5,z6]),(0,[z429,z0,z3,z4,z5,z6,z45])],[(0,[z0,z646,z1,z3,z4,z5,z6]),(0,[z0,z1,z647,z3,z4,z5,z6]),(0,[z1,z3,z4,z185,z5,z15,z6]),(0,[z0,z152,z3,z4,z5,z6,z66]),(0,[z0,z1,z3,z648,z4,z5,z6]),(0,[z649,z0,z1,z3,z4,z5,z6]),(0,[z166,z0,z3,z4,z5,z88,z6]),(0,[z0,z1,z3,z4,z5,z330,z6]),(0,[z0,z1,z3,z4,z5,z6,z650])],[(0,[z1,z79,z3,z14,z4,z5,z6]),(0,[z193,z25,z1,z3,z4,z5,z6]),(0,[z1,z370,z3,z4,z5,z15,z6]),(0,[z18,z1,z3,z4,z5,z15,z6]),(1,[z18,z1,z3,z4,z5,z75]),(0,[z651,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z101,z3,z4,z5,z6]),(0,[z652,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z653,z5,z6]),(0,[z0,z1,z3,z654,z4,z5,z6]),(0,[z1,z3,z4,z5,z15,z6,z75]),(0,[z0,z71,z3,z4,z5,z162,z6]),(1,[z135,z1,z3,z4,z5,z6])],[(0,[z261,z25,z1,z3,z4,z5,z6]),(0,[z140,z1,z3,z4,z5,z15,z6]),(0,[z655,z0,z1,z3,z4,z5,z6])],[(0,[z656,z0,z1,z3,z4,z5,z6]),(0,[z0,z3,z161,z120,z4,z5,z6]),(0,[z657,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z114]),(1,[z194,z1,z3,z4,z5,z6]),(0,[z1,z3,z4,z156,z5,z529,z6])],[(0,[z0,z1,z3,z4,z5,z658,z6]),(0,[z0,z1,z3,z4,z5,z659,z6]),(0,[z0,z1,z3,z4,z5,z660,z6]),(0,[z661,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z662,z6]),(0,[z663,z0,z1,z3,z4,z5,z6])]],
   [[(0,[z1,z3,z14,z4,z5,z368,z6]),(0,[z559,z25,z1,z3,z4,z5,z6]),(0,[z232,z0,z1,z3,z4,z5,z6]),(0,[z1,z3,z4,z316,z5,z15,z6]),(0,[z85,z0,z3,z161,z4,z5,z6]),(0,[z0,z1,z3,z664,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z665]),(0,[z195,z0,z381,z3,z4,z5,z6]),(1,[z0,z146,z3,z4,z5,z6])],[(0,[z25,z1,z3,z4,z5,z15,z6]),(0,[z0,z1,z3,z4,z5,z666,z6]),(0,[z0,z1,z667,z3,z4,z5,z6]),(0,[z261,z0,z1,z4,z44,z5,z6])],[(0,[z1,z3,z4,z5,z15,z17,z6]),(0,[z85,z0,z3,z4,z185,z5,z6]),(0,[z90,z0,z176,z3,z4,z5,z6]),(0,[z140,z0,z1,z3,z143,z5,z6]),(1,[z0,z1,z3,z4,z156,z33])],[(0,[z668,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z60,z6]),(0,[z18,z69,z1,z3,z4,z5,z6]),(0,[z0,z267,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z66]),(0,[z0,z3,z4,z5,z33,z6,z409])],[(0,[z27,z65,z0,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z669,z5,z6]),(0,[z1,z3,z14,z4,z5,z162,z6]),(0,[z670,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z671,z5,z6])],[(0,[z68,z1,z3,z14,z4,z5,z6]),(0,[z40,z41,z1,z3,z4,z5,z6]),(1,[z1,z3,z507,z4,z5,z6]),(0,[z18,z1,z3,z4,z5,z17,z6]),(0,[z0,z1,z3,z672,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z673,z6]),(0,[z0,z1,z3,z4,z5,z6,z674])],[(0,[z169,z1,z3,z4,z5,z15,z6]),(0,[z1,z3,z14,z4,z5,z98,z6]),(0,[z18,z1,z3,z4,z5,z88,z6]),(0,[z18,z1,z3,z4,z5,z6,z47]),(0,[z1,z3,z4,z5,z15,z6,z45]),(0,[z0,z176,z152,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z675,z5,z6]),(1,[z0,z159,z3,z4,z5,z6]),(0,[z195,z0,z1,z487,z4,z5,z6]),(0,[z195,z0,z1,z3,z4,z5,z516]),(0,[z193,z0,z1,z3,z4,z5,z6]),(1,[z0,z3,z4,z5,z6,z409])],[(0,[z0,z1,z3,z4,z676,z5,z6]),(0,[z0,z1,z3,z4,z677,z5,z6]),(1,[z0,z3,z4,z413,z5,z6]),(0,[z0,z1,z3,z678,z4,z5,z6])]],
   [[(0,[z176,z1,z3,z4,z5,z15,z6]),(0,[z679,z0,z1,z3,z4,z5,z6]),(0,[z261,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z680]),(0,[z0,z3,z21,z4,z413,z5,z6]),(0,[z93,z1,z3,z4,z5,z17,z6])],[(0,[z0,z3,z4,z154,z103,z5,z6]),(1,[z1,z3,z4,z5,z15,z6]),(0,[z0,z273,z122,z3,z4,z5,z6])],[(1,[z105,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z681,z4,z5,z6]),(0,[z0,z1,z682,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z683,z6]),(0,[z684,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z685]),(0,[z0,z1,z3,z22,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z686])],[(0,[z0,z1,z687,z3,z4,z5,z6]),(0,[z0,z1,z3,z688,z4,z5,z6]),(0,[z0,z1,z3,z21,z5,z98,z6]),(0,[z0,z1,z3,z4,z689,z5,z6]),(0,[z0,z3,z4,z5,z357,z98,z6])],[(0,[z1,z3,z14,z144,z4,z5,z6]),(0,[z25,z1,z3,z4,z5,z17,z6]),(0,[z18,z1,z3,z4,z5,z6,z6]),(0,[z414,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z690,z4,z5,z6]),(0,[z0,z1,z691,z3,z4,z5,z6])],[(0,[z195,z1,z3,z14,z4,z5,z6]),(0,[z25,z1,z3,z4,z5,z88,z6]),(0,[z25,z1,z3,z4,z5,z6,z47]),(0,[z0,z692,z1,z3,z4,z5,z6]),(0,[z61,z1,z3,z4,z5,z15,z6]),(0,[z0,z1,z3,z4,z5,z6,z693])],[(0,[z18,z61,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z694])],[(0,[z0,z1,z3,z4,z401,z5,z6]),(1,[z18,z1,z3,z4,z5,z15]),(0,[z0,z1,z177,z3,z4,z5,z6]),(0,[z0,z122,z3,z57,z4,z5,z6]),(1,[z0,z1,z3,z143,z5,z6]),(0,[z0,z1,z3,z22,z4,z98,z6]),(0,[z0,z1,z3,z4,z5,z695,z6])]],
   [[(0,[z18,z1,z122,z3,z4,z5,z6]),(0,[z1,z3,z21,z4,z5,z15,z6]),(0,[z0,z176,z3,z161,z4,z5,z6]),(1,[z1,z3,z4,z5,z56,z6])],[(0,[z157,z0,z3,z4,z5,z6,z66]),(0,[z0,z543,z1,z3,z4,z5,z6]),(0,[z34,z25,z1,z3,z4,z5,z6]),(0,[z131,z1,z3,z4,z5,z15,z6]),(0,[z121,z0,z1,z3,z4,z5,z6]),(0,[z27,z0,z3,z4,z43,z5,z6]),(0,[z0,z1,z696,z3,z4,z5,z6])],[(1,[z0,z3,z13,z4,z5,z6]),(0,[z289,z0,z1,z3,z4,z5,z6]),(0,[z27,z0,z1,z3,z120,z5,z6]),(0,[z0,z176,z3,z4,z185,z5,z6]),(1,[z0,z210,z3,z4,z5,z6]),(0,[z0,z1,z101,z3,z4,z171,z6])],[(1,[z54,z0,z3,z4,z5,z6]),(0,[z41,z0,z1,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z15,z33,z6]),(0,[z0,z1,z3,z4,z697,z5,z6]),(0,[z68,z0,z1,z3,z4,z5,z17]),(1,[z0,z1,z3,z4,z5,z235])],[(0,[z40,z1,z3,z4,z5,z60,z6]),(0,[z0,z1,z3,z698,z4,z5,z6]),(0,[z699,z0,z1,z3,z4,z5,z6]),(0,[z700,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z701,z6]),(0,[z0,z702,z1,z3,z4,z5,z6])],[(0,[z105,z1,z3,z14,z4,z5,z6]),(0,[z703,z0,z1,z3,z4,z5,z6]),(0,[z140,z0,z1,z4,z5,z88,z6]),(0,[z0,z1,z3,z4,z5,z47,z75])],[(0,[z0,z1,z3,z4,z5,z6,z704]),(0,[z25,z1,z3,z4,z5,z6,z113]),(0,[z0,z1,z3,z4,z5,z6,z705]),(0,[z18,z1,z3,z4,z5,z33,z6]),(0,[z0,z1,z3,z507,z4,z5,z6])],[(0,[z157,z1,z3,z144,z4,z5,z6]),(0,[z25,z1,z122,z3,z4,z5,z6]),(0,[z59,z0,z1,z3,z103,z5,z6]),(0,[z1,z3,z4,z5,z452,z15,z6]),(0,[z85,z90,z0,z3,z4,z5,z6]),(0,[z0,z706,z1,z3,z4,z5,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z3,z4,z5,z203,z6]),(0,[z18,z1,z3,z4,z707,z6]),(0,[z655,z18,z1,z3,z4,z5]),(0,[z196,z3,z4,z5,z15,z6]),(0,[z27,z0,z3,z4,z5,z298])],[(0,[z0,z1,z122,z21,z5,z6]),(0,[z0,z319,z3,z325,z5,z6]),(0,[z0,z708,z3,z4,z5,z6])],[(0,[z709,z105,z1,z3,z4,z5]),(0,[z710,z1,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z711,z211]),(0,[z195,z420,z1,z3,z98,z6]),(0,[z712,z1,z3,z4,z5,z6])],[(0,[z1,z122,z14,z21,z5,z6]),(0,[z0,z1,z3,z713,z5,z6])],[(0,[z0,z3,z4,z154,z5,z6]),(0,[z25,z71,z79,z4,z5,z6]),(0,[z714,z1,z3,z4,z5,z6]),(0,[z0,z715,z3,z4,z5,z6])],[(0,[z25,z1,z3,z4,z156,z33]),(0,[z716,z1,z3,z4,z5,z6]),(0,[z717,z1,z3,z4,z5,z6]),(0,[z1,z3,z718,z4,z5,z6])],[(0,[z0,z1,z719,z4,z5,z6]),(0,[z297,z3,z14,z4,z5,z6]),(0,[z18,z1,z720,z4,z5,z6]),(0,[z1,z3,z721,z4,z5,z6]),(0,[z348,z197,z3,z4,z5,z6]),(0,[z1,z3,z722,z4,z5,z6])],[(0,[z1,z3,z4,z5,z6,z723])],[(0,[z105,z59,z1,z3,z4,z5]),(0,[z85,z25,z161,z4,z5,z6]),(0,[z267,z3,z4,z5,z368,z6]),(0,[z0,z1,z3,z4,z5,z724]),(0,[z0,z152,z3,z664,z5,z6]),(0,[z0,z1,z3,z325,z5,z308]),(0,[z0,z196,z3,z331,z5,z6])],[(0,[z54,z3,z14,z4,z5,z6]),(0,[z18,z1,z3,z4,z5,z75]),(0,[z3,z725,z112,z4,z5,z6]),(0,[z0,z1,z326,z4,z5,z235]),(0,[z1,z3,z4,z726,z5,z6])],[(0,[z25,z3,z4,z413,z5,z6]),(0,[z18,z727,z3,z4,z5,z6]),(0,[z0,z728,z3,z4,z5,z6]),(0,[z729,z1,z3,z4,z5,z6])],[(0,[z0,z3,z4,z730,z5,z6]),(0,[z46,z25,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z731]),(0,[z1,z3,z4,z5,z60,z204]),(0,[z18,z732,z3,z4,z5,z6]),(0,[z140,z1,z4,z88,z15,z6]),(0,[z420,z124,z3,z4,z5,z6])],[(0,[z733,z1,z3,z4,z5,z6]),(0,[z734,z0,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z735]),(0,[z1,z3,z4,z5,z736,z6]),(0,[z40,z1,z3,z4,z60,z6]),(0,[z0,z737,z3,z4,z5,z6])],[(0,[z738,z3,z14,z4,z5,z6]),(0,[z263,z3,z14,z4,z5,z6]),(0,[z46,z3,z4,z5,z15,z6]),(0,[z0,z1,z3,z739,z5,z6]),(0,[z0,z1,z3,z4,z740,z6])],[(0,[z0,z1,z3,z741,z5,z6]),(0,[z130,z0,z3,z4,z5,z631])]],
   [[(0,[z25,z1,z254,z4,z5,z6]),(0,[z742,z1,z3,z4,z5,z6]),(0,[z0,z71,z79,z4,z5,z6]),(0,[z0,z122,z57,z21,z5,z6]),(0,[z0,z3,z4,z743,z5,z6])],[(0,[z1,z3,z744,z4,z5,z6]),(0,[z1,z3,z4,z745,z5,z6]),(0,[z18,z1,z3,z4,z5,z615]),(0,[z0,z1,z3,z4,z676,z75]),(0,[z1,z3,z4,z746,z5,z6]),(0,[z747,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z156,z33])],[(0,[z261,z25,z1,z44,z5,z6]),(0,[z1,z3,z748,z4,z5,z6]),(0,[z749,z1,z3,z4,z5,z6]),(0,[z1,z3,z750,z4,z5,z6])],[(0,[z34,z1,z3,z4,z433,z6]),(0,[z197,z18,z3,z4,z5,z6])],[(0,[z68,z18,z196,z3,z4,z5]),(0,[z130,z0,z3,z4,z5,z636])],[(0,[z1,z14,z4,z5,z6,z576]),(0,[z25,z210,z3,z4,z5,z6]),(0,[z751,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z752])],[(0,[z25,z1,z3,z4,z5,z235]),(0,[z0,z753,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z204]),(0,[z0,z3,z4,z413,z5,z6]),(0,[z1,z3,z4,z5,z754,z6]),(0,[z0,z3,z4,z5,z6,z755]),(0,[z756,z263,z3,z4,z5,z6])],[(0,[z757,z1,z3,z4,z5,z6]),(0,[z0,z273,z3,z21,z5,z6])],[(0,[z1,z3,z4,z5,z6,z758]),(0,[z18,z3,z759,z4,z5,z6]),(0,[z18,z1,z3,z4,z5,z74])],[(0,[z105,z0,z1,z3,z4,z5]),(0,[z760,z1,z3,z4,z5,z6]),(0,[z0,z761,z3,z4,z5,z6]),(0,[z68,z0,z1,z507,z4,z5]),(0,[z762,z1,z3,z4,z5,z6])],[(0,[z1,z3,z763,z4,z5,z6]),(0,[z1,z3,z14,z4,z372,z6]),(0,[z0,z764,z3,z4,z5,z6])],[(0,[z25,z275,z3,z4,z5,z6]),(0,[z1,z3,z4,z26,z6,z328]),(0,[z501,z1,z3,z4,z5,z569]),(0,[z765,z1,z3,z4,z5,z6])],[(0,[z18,z1,z3,z4,z156,z33]),(0,[z1,z3,z4,z5,z6,z766]),(0,[z1,z16,z4,z5,z368,z17]),(0,[z195,z81,z1,z3,z98,z6]),(0,[z1,z3,z4,z767,z5,z6])],[(0,[z184,z1,z3,z4,z5,z6]),(0,[z768,z1,z3,z4,z5,z6]),(0,[z279,z176,z3,z4,z5,z110]),(0,[z0,z196,z3,z4,z389,z6]),(0,[z1,z3,z4,z5,z6,z769])],[(0,[z1,z3,z4,z247,z5,z6]),(0,[z1,z3,z14,z4,z5,z322]),(0,[z267,z3,z4,z5,z452,z6])],[(0,[z0,z1,z3,z4,z33,z770])]],
   [[(0,[z1,z3,z5,z15,z6,z771]),(0,[z772,z1,z3,z4,z5,z6])],[(0,[z105,z1,z3,z4,z44,z5]),(0,[z1,z3,z4,z773,z5,z6]),(0,[z18,z1,z3,z4,z171,z75]),(0,[z0,z210,z3,z4,z5,z6]),(0,[z774,z1,z3,z4,z5,z6]),(0,[z0,z1,z4,z5,z775,z47])],[(0,[z105,z1,z3,z161,z4,z5]),(0,[z1,z3,z776,z4,z5,z6]),(0,[z1,z326,z4,z5,z15,z6])],[(0,[z169,z1,z777,z4,z5,z6]),(0,[z27,z105,z1,z3,z4,z5]),(0,[z260,z1,z3,z103,z5,z6]),(0,[z25,z1,z777,z4,z5,z6]),(0,[z279,z1,z3,z4,z5,z33]),(0,[z0,z319,z3,z4,z5,z308]),(0,[z0,z1,z3,z778,z5,z6])],[(0,[z25,z1,z278,z4,z5,z6]),(0,[z0,z1,z3,z779,z5,z6]),(0,[z0,z3,z780,z4,z5,z6])],[(0,[z781,z1,z3,z4,z5,z6]),(0,[z420,z381,z3,z4,z5,z6])],[(0,[z25,z1,z397,z4,z5,z6]),(0,[z105,z1,z3,z174,z4,z5]),(0,[z1,z3,z782,z4,z5,z6]),(0,[z1,z3,z783,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z784]),(0,[z256,z1,z3,z4,z372,z6])],[(0,[z0,z1,z3,z4,z785,z6]),(0,[z68,z93,z1,z3,z4,z5]),(0,[z3,z4,z5,z525,z6,z786]),(0,[z0,z3,z787,z4,z5,z6]),(0,[z0,z275,z3,z4,z5,z6])],[(0,[z279,z1,z3,z4,z5,z6]),(0,[z788,z1,z3,z14,z4,z5]),(0,[z184,z3,z4,z5,z162,z6]),(0,[z1,z3,z789,z4,z5,z6]),(0,[z790,z1,z3,z4,z5,z6]),(0,[z1,z3,z791,z4,z5,z6])],[(0,[z18,z1,z3,z143,z5,z6]),(0,[z1,z3,z4,z5,z792,z6])],[(0,[z25,z1,z3,z4,z5,z793]),(0,[z93,z1,z3,z4,z5,z525]),(0,[z0,z1,z3,z794,z5,z6]),(0,[z18,z3,z4,z5,z33,z409]),(0,[z795,z1,z3,z4,z5,z6]),(0,[z1,z3,z4,z796,z5,z6]),(0,[z797,z1,z3,z4,z5,z6])],[(0,[z18,z196,z3,z4,z5,z6]),(0,[z3,z4,z5,z15,z6,z798]),(0,[z0,z1,z3,z4,z5,z799]),(0,[z420,z1,z3,z4,z5,z516])],[(0,[z68,z1,z14,z4,z5,z47]),(0,[z25,z3,z4,z5,z6,z786]),(0,[z0,z800,z3,z4,z5,z6]),(0,[z801,z1,z3,z4,z5,z6])],[(0,[z18,z1,z3,z4,z5,z595]),(0,[z18,z1,z3,z4,z5,z235]),(0,[z261,z0,z1,z802,z5,z6])],[(0,[z803,z105,z1,z3,z4,z5]),(0,[z1,z3,z4,z5,z525,z17]),(0,[z184,z42,z3,z4,z5,z6])],[(0,[z0,z3,z4,z5,z804,z6]),(0,[z1,z3,z4,z5,z6,z51]),(0,[z0,z1,z805,z4,z5,z6]),(0,[z0,z806,z3,z4,z5,z6]),(0,[z807,z1,z3,z4,z5,z6]),(0,[z479,z0,z3,z185,z5,z6]),(0,[z0,z42,z3,z4,z43,z298]),(0,[z0,z3,z4,z43,z6,z631]),(0,[z808,z1,z487,z4,z5,z6])]],
   [[(0,[z1,z3,z4,z520,z60,z6]),(0,[z0,z1,z3,z4,z809,z6]),(0,[z0,z1,z810,z4,z5,z6])],[(0,[z0,z1,z44,z5,z360,z6]),(0,[z1,z16,z112,z4,z5,z17])],[(0,[z811,z18,z3,z4,z5,z6]),(0,[z68,z18,z1,z3,z4,z5]),(0,[z0,z3,z4,z5,z812,z6])],[(0,[z1,z3,z14,z4,z813,z5]),(0,[z1,z3,z208,z5,z416,z6]),(0,[z1,z3,z814,z4,z5,z6])],[(0,[z64,z157,z3,z4,z5,z6]),(0,[z81,z1,z3,z4,z5,z6]),(0,[z41,z1,z3,z4,z453,z6]),(0,[z1,z3,z4,z5,z6,z815]),(0,[z414,z1,z3,z143,z5,z6]),(0,[z1,z3,z816,z4,z5,z6])],[(0,[z1,z3,z817,z4,z5,z6]),(0,[z0,z818,z3,z4,z5,z6])],[(0,[z1,z3,z117,z144,z5,z6])],[(0,[z1,z3,z4,z5,z819,z6]),(0,[z0,z1,z3,z4,z5,z820]),(0,[z25,z821,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z822,z6]),(0,[z261,z227,z1,z44,z5,z6])],[(0,[z105,z1,z3,z4,z5,z100]),(0,[z0,z3,z4,z5,z6,z786]),(0,[z1,z3,z4,z5,z522,z15]),(0,[z18,z1,z16,z3,z4,z5])],[(0,[z434,z3,z4,z5,z15,z6])],[(0,[z157,z3,z4,z5,z6,z183]),(0,[z0,z1,z3,z823,z4,z5]),(0,[z90,z105,z1,z3,z4,z5]),(0,[z105,z1,z3,z3,z4,z5]),(0,[z68,z1,z3,z507,z4,z5]),(0,[z0,z1,z3,z4,z5,z824]),(0,[z1,z3,z4,z5,z6,z825])],[(0,[z93,z105,z1,z3,z4,z5]),(0,[z0,z826,z3,z4,z5,z6]),(0,[z294,z69,z3,z4,z5,z6])],[(0,[z1,z487,z4,z5,z15,z6])],[(0,[z131,z1,z3,z653,z5,z6]),(0,[z0,z827,z3,z4,z5,z6]),(0,[z124,z3,z4,z5,z15,z6]),(0,[z0,z210,z3,z4,z5,z211]),(0,[z774,z1,z3,z4,z5,z211])],[(0,[z356,z1,z3,z4,z5,z6]),(0,[z1,z3,z14,z4,z5,z569]),(0,[z828,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z829]),(0,[z1,z3,z4,z5,z15,z439]),(0,[z830,z1,z3,z4,z5,z6]),(0,[z831,z1,z3,z4,z5,z6])]],
   [[],[(0,[z788,z0,z1,z3,z4,z5]),(0,[z1,z3,z832,z103,z5,z6]),(0,[z0,z833,z3,z4,z5,z6]),(0,[z399,z267,z3,z4,z5,z6]),(0,[z834,z1,z3,z4,z5,z569]),(0,[z1,z3,z835,z4,z5,z6]),(0,[z0,z1,z3,z4,z349,z33])],[(0,[z105,z54,z3,z4,z5,z6]),(0,[z195,z105,z1,z3,z4,z5]),(0,[z1,z3,z139,z4,z5,z6]),(0,[z1,z3,z144,z832,z5,z6]),(0,[z836,z1,z3,z4,z5,z6]),(0,[z27,z0,z3,z359,z5,z6]),(0,[z756,z1,z3,z4,z5,z6])],[(0,[z3,z14,z4,z5,z6,z409]),(0,[z0,z821,z3,z4,z5,z6]),(0,[z369,z1,z3,z80,z5,z6])],[(0,[z1,z4,z5,z368,z6,z291]),(0,[z0,z1,z3,z4,z5,z837]),(0,[z588,z1,z3,z601,z5,z6]),(0,[z18,z1,z3,z4,z5,z705]),(0,[z3,z4,z5,z368,z6,z183]),(0,[z0,z1,z4,z5,z17,z775]),(0,[z838,z0,z3,z4,z5,z6])],[(0,[z1,z3,z144,z271,z5,z6]),(0,[z0,z3,z4,z839,z5,z6]),(0,[z71,z79,z4,z5,z15,z6]),(0,[z395,z1,z4,z5,z6,z291]),(0,[z840,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z372,z6]),(0,[z841,z1,z3,z4,z5,z6]),(0,[z0,z3,z725,z4,z5,z6]),(0,[z0,z124,z3,z4,z5,z516])],[],[(0,[z105,z1,z3,z4,z5,z88]),(0,[z3,z14,z4,z5,z6,z842]),(0,[z41,z1,z3,z4,z26,z6]),(0,[z1,z3,z4,z843,z60,z6]),(0,[z0,z844,z3,z4,z5,z6]),(0,[z0,z845,z3,z4,z5,z6]),(0,[z163,z1,z101,z4,z171,z6])],[],[(0,[z846,z1,z3,z14,z4,z5]),(0,[z1,z3,z4,z5,z847,z6]),(0,[z0,z1,z3,z4,z453,z33]),(0,[z501,z3,z120,z4,z5,z6])],[(0,[z0,z848,z3,z4,z5,z6]),(0,[z0,z3,z849,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z850])],[(0,[z18,z1,z3,z4,z5,z336]),(0,[z1,z3,z851,z5,z15,z6]),(0,[z0,z210,z3,z325,z5,z6])],[(0,[z18,z192,z3,z4,z5,z6])],[(0,[z157,z0,z3,z80,z5,z6]),(0,[z25,z1,z3,z4,z5,z204]),(0,[z852,z1,z3,z4,z5,z6]),(0,[z63,z46,z3,z4,z5,z6]),(0,[z195,z0,z381,z3,z98,z6]),(0,[z853,z1,z3,z4,z5,z6])],[(0,[z85,z0,z421,z4,z5,z6]),(0,[z140,z25,z1,z4,z88,z6]),(0,[z131,z267,z3,z4,z5,z6]),(0,[z18,z3,z4,z5,z203,z6]),(0,[z0,z159,z3,z4,z372,z6])],[(0,[z18,z1,z122,z21,z5,z6]),(0,[z0,z71,z548,z4,z5,z6]),(0,[z0,z1,z29,z21,z5,z6]),(0,[z854,z1,z3,z4,z5,z6])]],
   [[(0,[z0,z1,z3,z4,z855,z6]),(0,[z1,z3,z4,z5,z6,z856]),(0,[z0,z857,z3,z4,z5,z6])],[(0,[z858,z1,z3,z14,z4,z6]),(0,[z59,z1,z3,z19,z5,z6]),(0,[z859,z1,z3,z4,z5,z6])],[(0,[z0,z1,z860,z4,z5,z6]),(0,[z18,z3,z4,z154,z5,z6])],[(0,[z25,z1,z3,z22,z73,z6]),(0,[z90,z18,z3,z4,z162,z6]),(0,[z18,z1,z384,z3,z4,z5]),(0,[z61,z267,z3,z4,z5,z15]),(0,[z1,z3,z4,z5,z861,z6]),(0,[z0,z1,z4,z862,z88,z6])],[(0,[z1,z3,z468,z112,z4,z5]),(0,[z446,z18,z1,z3,z4,z5])],[(0,[z863,z3,z14,z4,z5,z6]),(0,[z510,z1,z3,z4,z5,z15]),(0,[z864,z0,z3,z4,z5,z6])],[(0,[z65,z177,z3,z4,z5,z6]),(0,[z41,z1,z3,z4,z455,z6]),(0,[z0,z1,z865,z4,z5,z6]),(0,[z1,z3,z4,z832,z5,z6]),(0,[z1,z3,z4,z5,z843,z6]),(0,[z267,z3,z4,z5,z15,z6])],[(1,[z105,z3,z13,z4,z5]),(0,[z131,z1,z3,z832,z5,z6]),(0,[z131,z297,z3,z4,z5,z6]),(0,[z0,z71,z644,z4,z5,z6]),(0,[z1,z3,z4,z866,z5,z6]),(0,[z63,z1,z3,z4,z5,z75]),(0,[z1,z3,z4,z5,z6,z867])],[(0,[z0,z3,z4,z5,z6,z868])],[(0,[z1,z3,z4,z5,z15,z503]),(0,[z0,z79,z4,z5,z573,z6]),(0,[z1,z3,z4,z5,z869,z308]),(0,[z870,z1,z3,z4,z5,z6]),(0,[z0,z3,z4,z156,z172,z33])],[(0,[z261,z105,z1,z3,z4,z5]),(0,[z1,z3,z4,z5,z6,z871]),(0,[z61,z1,z3,z4,z5,z824])],[(0,[z3,z13,z14,z4,z5,z6])],[(0,[z227,z1,z3,z4,z5,z6]),(0,[z872,z1,z3,z4,z5,z6]),(0,[z3,z14,z4,z5,z6,z49]),(0,[z105,z54,z0,z3,z4,z5]),(0,[z18,z1,z3,z4,z597,z5]),(0,[z873,z3,z4,z5,z15,z6])],[(0,[z18,z1,z3,z741,z5,z6]),(0,[z1,z3,z4,z5,z15,z298]),(0,[z3,z4,z5,z330,z15,z6]),(0,[z236,z0,z1,z4,z88,z6]),(0,[z874,z1,z3,z4,z5,z6])],[(0,[z18,z71,z79,z4,z5,z6]),(0,[z1,z3,z4,z5,z875,z6]),(0,[z0,z152,z3,z111,z5,z6]),(0,[z81,z1,z326,z4,z5,z6])],[(0,[z0,z876,z3,z4,z5,z6]),(0,[z403,z506,z3,z4,z5,z6]),(0,[z1,z3,z4,z877,z5,z6]),(0,[z1,z3,z4,z5,z878,z6]),(0,[z90,z0,z3,z4,z879,z6]),(0,[z0,z381,z3,z4,z5,z516]),(0,[z0,z1,z326,z5,z98,z6]),(0,[z0,z1,z3,z22,z73,z6])]],
   [[(0,[z27,z25,z3,z185,z5,z6]),(0,[z0,z1,z4,z880,z5,z6])],[(0,[z18,z54,z3,z4,z5,z6])],[(0,[z846,z0,z1,z3,z4,z5]),(0,[z1,z3,z4,z86,z5,z15]),(0,[z267,z3,z4,z5,z572,z6]),(0,[z85,z0,z475,z4,z5,z6]),(0,[z257,z196,z3,z4,z5,z6]),(0,[z881,z1,z3,z4,z5,z6])],[(0,[z18,z1,z3,z237,z4,z5]),(0,[z882,z1,z3,z4,z5,z6]),(0,[z0,z319,z3,z143,z5,z6])],[(0,[z0,z79,z430,z4,z5,z6]),(0,[z25,z152,z3,z120,z5,z6]),(0,[z883,z0,z3,z4,z5,z6]),(0,[z18,z1,z3,z4,z5,z204]),(0,[z18,z753,z3,z4,z5,z6]),(0,[z18,z3,z4,z413,z5,z6]),(0,[z884,z0,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z15,z308]),(0,[z885,z1,z3,z4,z5,z6]),(0,[z886,z1,z3,z4,z5,z6])],[(0,[z166,z25,z3,z4,z5,z6]),(0,[z68,z1,z507,z4,z5,z6]),(0,[z1,z3,z4,z5,z887,z6]),(0,[z90,z0,z3,z4,z292,z6])],[(0,[z286,z0,z1,z3,z4,z75])],[(0,[z0,z1,z3,z888,z5,z6]),(0,[z889,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z890,z5,z6]),(0,[z891,z0,z1,z3,z5,z6])],[(0,[z166,z3,z4,z5,z15,z6]),(0,[z0,z1,z3,z892,z5,z6]),(0,[z140,z166,z0,z4,z88,z6]),(0,[z0,z1,z4,z171,z862,z6])],[(0,[z297,z3,z4,z5,z60,z6]),(0,[z18,z1,z3,z4,z5,z165]),(0,[z85,z0,z893,z4,z5,z6]),(0,[z0,z1,z3,z4,z894,z6]),(0,[z895,z1,z3,z4,z5,z6]),(0,[z896,z1,z3,z4,z5,z6]),(0,[z0,z1,z101,z4,z171,z6]),(0,[z429,z0,z3,z4,z5,z75])],[(0,[z157,z350,z3,z4,z5,z6]),(0,[z65,z897,z3,z4,z5,z6]),(0,[z18,z429,z3,z4,z5,z6]),(0,[z42,z3,z4,z43,z15,z6]),(0,[z0,z3,z4,z898,z5,z6]),(0,[z0,z71,z79,z438,z5,z6]),(0,[z0,z1,z3,z143,z5,z308]),(0,[z0,z1,z487,z4,z5,z235]),(0,[z899,z0,z1,z4,z5,z6])],[(0,[z900,z0,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z901,z6]),(0,[z3,z4,z5,z6,z74,z902])],[(0,[z1,z101,z14,z4,z171,z6]),(0,[z1,z3,z14,z4,z5,z516]),(0,[z3,z14,z4,z5,z357,z6]),(0,[z54,z3,z4,z5,z60,z6]),(0,[z903,z1,z3,z4,z5,z6]),(0,[z904,z1,z3,z4,z5,z6]),(0,[z0,z905,z3,z4,z5,z6]),(0,[z3,z4,z5,z6,z906,z409])],[],[(0,[z105,z61,z1,z3,z4,z5])],[(0,[z1,z3,z468,z4,z5,z15]),(0,[z18,z210,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z907,z6]),(0,[z0,z908,z3,z4,z5,z6]),(0,[z909,z1,z3,z4,z5,z6])]],
   [[(0,[z1,z3,z117,z334,z5,z6]),(0,[z910,z105,z1,z3,z4,z5]),(0,[z0,z3,z4,z5,z911,z6]),(0,[z18,z275,z3,z4,z5,z33]),(0,[z0,z152,z3,z120,z5,z6]),(0,[z912,z1,z101,z3,z4,z5])],[(0,[z25,z1,z468,z14,z4,z5]),(0,[z90,z3,z4,z162,z15,z6]),(0,[z913,z1,z3,z4,z5,z6])],[(0,[z54,z3,z4,z5,z221,z6]),(0,[z914,z1,z3,z4,z5,z6]),(0,[z0,z915,z3,z4,z5,z6])],[(0,[z897,z84,z3,z4,z5,z6]),(0,[z0,z3,z4,z916,z5,z6]),(0,[z1,z3,z917,z4,z5,z6])],[(0,[z395,z18,z1,z3,z4,z5]),(1,[z1,z3,z832,z5,z6]),(0,[z193,z0,z434,z3,z5,z45])],[(0,[z18,z275,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z918]),(0,[z1,z3,z4,z5,z6,z919])],[(0,[z38,z3,z4,z5,z659,z6]),(0,[z67,z3,z4,z5,z6,z183]),(0,[z0,z1,z3,z4,z5,z920]),(0,[z1,z3,z4,z5,z6,z921]),(0,[z922,z263,z3,z4,z5,z6])],[(0,[z25,z3,z4,z5,z330,z6]),(0,[z0,z1,z3,z851,z5,z6]),(0,[z0,z1,z3,z923,z5,z6])],[(0,[z3,z14,z4,z5,z6,z167]),(0,[z0,z79,z4,z626,z5,z6])],[(0,[z0,z924,z3,z4,z5,z6])],[(0,[z3,z14,z4,z5,z172,z6]),(0,[z925,z1,z3,z4,z5,z6]),(0,[z926,z1,z3,z4,z5,z6]),(0,[z1,z3,z4,z316,z452,z6]),(0,[z927,z1,z3,z4,z5,z6]),(0,[z414,z210,z3,z4,z5,z6])],[(0,[z501,z1,z3,z4,z5,z6]),(0,[z105,z1,z370,z3,z4,z5]),(0,[z18,z152,z3,z120,z5,z6]),(0,[z195,z18,z1,z3,z98,z6])],[(0,[z25,z1,z3,z4,z372,z6]),(0,[z0,z79,z893,z4,z5,z6]),(0,[z1,z3,z4,z5,z56,z569]),(0,[z282,z3,z4,z5,z6,z49])],[(0,[z337,z1,z3,z4,z5,z6]),(0,[z1,z3,z14,z80,z5,z6]),(0,[z1,z3,z928,z4,z5,z6]),(0,[z1,z3,z929,z4,z5,z6]),(0,[z1,z3,z4,z5,z930,z6]),(0,[z0,z1,z3,z4,z156,z770])],[(0,[z68,z18,z1,z3,z4,z372]),(0,[z18,z1,z3,z4,z5,z693]),(0,[z267,z3,z4,z5,z6,z183]),(0,[z130,z0,z3,z4,z5,z284])],[(0,[z0,z1,z3,z4,z931,z6]),(0,[z210,z3,z14,z4,z5,z6]),(0,[z0,z3,z4,z5,z932,z6]),(0,[z25,z1,z16,z4,z5,z17]),(0,[z0,z933,z3,z4,z5,z6]),(0,[z0,z1,z3,z7,z372,z6])]],
   [[(0,[z105,z1,z3,z21,z4,z5]),(0,[z0,z934,z3,z4,z5,z6]),(0,[z1,z370,z777,z4,z5,z6]),(0,[z25,z1,z3,z4,z5,z322]),(0,[z1,z3,z507,z4,z5,z75]),(0,[z584,z18,z1,z3,z4,z5]),(0,[z761,z3,z4,z5,z15,z6]),(0,[z0,z71,z667,z4,z5,z6]),(0,[z935,z1,z3,z4,z5,z6]),(0,[z936,z1,z3,z4,z5,z6]),(0,[z140,z0,z319,z4,z88,z6])],[],[(1,[z105,z54,z3,z4,z5]),(0,[z3,z14,z4,z5,z6,z798]),(0,[z937,z1,z3,z4,z5,z6]),(0,[z18,z1,z3,z4,z5,z312]),(0,[z938,z1,z3,z4,z5,z6])],[(0,[z0,z3,z4,z5,z330,z6])],[(0,[z53,z1,z507,z4,z5,z6]),(0,[z289,z1,z3,z4,z453,z6]),(0,[z267,z3,z208,z4,z5,z6]),(0,[z451,z0,z1,z3,z4,z75]),(0,[z0,z1,z524,z4,z171,z6])],[],[(0,[z1,z3,z4,z5,z6,z939]),(0,[z1,z3,z4,z5,z940,z6]),(0,[z501,z3,z4,z5,z162,z6]),(0,[z941,z1,z3,z4,z5,z6]),(0,[z63,z1,z16,z3,z4,z5])],[(0,[z65,z571,z3,z4,z5,z6]),(0,[z1,z777,z14,z4,z5,z6]),(0,[z105,z152,z1,z3,z4,z5]),(0,[z1,z78,z4,z5,z368,z6]),(0,[z942,z3,z4,z413,z5,z6]),(0,[z943,z1,z3,z4,z5,z6])],[(0,[z18,z1,z3,z4,z5,z824]),(0,[z1,z3,z4,z5,z944,z6]),(0,[z146,z3,z4,z5,z15,z6]),(0,[z85,z0,z3,z4,z5,z298])],[(0,[z1,z3,z14,z4,z5,z945]),(0,[z946,z1,z3,z4,z5,z6]),(0,[z0,z947,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z6,z948]),(0,[z1,z3,z4,z5,z6,z949]),(0,[z0,z1,z3,z4,z389,z47]),(0,[z950,z1,z3,z4,z5,z6])],[(0,[z55,z41,z3,z4,z5,z6]),(0,[z0,z1,z3,z951,z5,z6]),(0,[z952,z1,z3,z4,z5,z6])],[(0,[z145,z0,z161,z4,z5,z6]),(0,[z0,z1,z16,z4,z5,z17]),(0,[z1,z3,z4,z5,z6,z953])],[(0,[z0,z1,z3,z4,z5,z322]),(0,[z1,z3,z954,z4,z5,z6]),(0,[z501,z42,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z955,z6])],[(0,[z59,z1,z3,z313,z5,z6]),(0,[z0,z1,z3,z4,z956,z6])],[(0,[z1,z3,z4,z5,z525,z6]),(0,[z93,z1,z3,z4,z5,z75]),(0,[z55,z25,z3,z4,z5,z6]),(0,[z3,z4,z154,z5,z15,z6]),(0,[z85,z0,z586,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z957]),(0,[z261,z437,z1,z44,z5,z6]),(0,[z0,z958,z3,z4,z5,z6]),(0,[z959,z1,z3,z4,z5,z6])],[(0,[z157,z3,z13,z4,z5,z6]),(0,[z1,z14,z4,z213,z5,z6])]],
   [[(0,[z18,z1,z3,z4,z5,z358]),(0,[z105,z1,z3,z4,z5,z98]),(0,[z18,z1,z3,z4,z5,z300]),(0,[z960,z1,z3,z4,z5,z6])],[(0,[z55,z3,z4,z5,z15,z6]),(0,[z1,z3,z4,z5,z961,z6]),(0,[z195,z1,z3,z432,z98,z6])],[(0,[z105,z1,z3,z4,z171,z5]),(0,[z25,z273,z3,z4,z5,z6]),(0,[z131,z1,z3,z103,z5,z6]),(0,[z68,z18,z1,z3,z331,z5]),(0,[z61,z1,z3,z112,z4,z5]),(0,[z173,z0,z161,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z962])],[(0,[z0,z963,z3,z4,z5,z6]),(1,[z1,z3,z4,z843,z6]),(0,[z18,z1,z3,z4,z372,z6]),(0,[z206,z0,z3,z4,z5,z66]),(0,[z0,z964,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z965]),(0,[z195,z0,z1,z326,z98,z6])],[(0,[z25,z966,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z6,z967]),(0,[z1,z3,z4,z5,z824,z241]),(0,[z3,z4,z5,z357,z15,z6]),(0,[z0,z152,z3,z413,z5,z6]),(0,[z0,z176,z3,z4,z5,z409]),(0,[z968,z3,z4,z5,z6,z74])],[(0,[z1,z3,z14,z7,z5,z6]),(0,[z900,z3,z14,z4,z5,z6]),(0,[z969,z1,z3,z4,z5,z6]),(0,[z970,z1,z3,z4,z5,z6]),(0,[z1,z3,z4,z971,z5,z6]),(0,[z0,z1,z3,z4,z311,z33])],[(0,[z0,z3,z4,z5,z972,z6])],[(0,[z18,z1,z3,z4,z5,z322]),(0,[z68,z18,z1,z507,z4,z5]),(0,[z18,z1,z3,z4,z453,z33]),(0,[z61,z3,z4,z5,z15,z183]),(0,[z973,z1,z3,z4,z5,z6])],[(0,[z105,z1,z3,z4,z5,z17]),(0,[z131,z1,z3,z371,z5,z6]),(0,[z41,z3,z4,z26,z203,z6]),(0,[z41,z267,z3,z4,z5,z6]),(0,[z18,z848,z3,z4,z5,z6]),(0,[z742,z1,z3,z4,z5,z298]),(0,[z0,z3,z4,z974,z5,z6]),(0,[z282,z1,z3,z4,z5,z33])],[(0,[z0,z3,z4,z5,z975,z6]),(0,[z1,z3,z4,z5,z976,z6])],[(0,[z977,z0,z1,z3,z5,z6]),(0,[z381,z3,z14,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z978]),(0,[z0,z3,z4,z43,z879,z6])],[(0,[z0,z979,z3,z4,z5,z6]),(0,[z0,z79,z3,z4,z5,z298])],[(0,[z18,z1,z3,z4,z5,z555]),(0,[z157,z296,z3,z4,z5,z6])],[(0,[z628,z1,z3,z4,z5,z15]),(0,[z282,z1,z3,z4,z5,z6]),(0,[z980,z1,z3,z4,z5,z6]),(0,[z0,z434,z3,z4,z5,z6]),(0,[z981,z0,z3,z4,z5,z6]),(0,[z1,z3,z982,z4,z5,z6])],[(0,[z1,z3,z14,z4,z5,z6]),(0,[z18,z1,z3,z4,z855,z6]),(0,[z0,z273,z3,z4,z5,z6]),(0,[z27,z0,z3,z413,z5,z6]),(0,[z983,z1,z3,z4,z5,z6]),(0,[z1,z3,z984,z4,z5,z6])],[(0,[z105,z1,z3,z507,z4,z5]),(0,[z25,z3,z57,z4,z5,z6]),(0,[z806,z3,z4,z5,z15,z6]),(0,[z985,z1,z3,z4,z5,z6])]],
   [[(0,[z1,z3,z986,z4,z5,z6]),(0,[z25,z1,z101,z4,z171,z6]),(0,[z0,z966,z3,z4,z5,z6]),(0,[z420,z1,z3,z4,z5,z6])],[(0,[z25,z1,z474,z4,z5,z6]),(0,[z0,z1,z3,z4,z813,z5]),(0,[z1,z3,z4,z422,z5,z6]),(0,[z41,z297,z3,z4,z5,z6]),(0,[z987,z1,z3,z4,z5,z6]),(0,[z834,z1,z3,z4,z5,z6]),(0,[z988,z1,z3,z4,z5,z6]),(0,[z0,z176,z3,z4,z5,z436]),(0,[z989,z0,z3,z4,z5,z6])],[(0,[z25,z990,z3,z4,z5,z6]),(0,[z0,z3,z4,z991,z5,z6]),(0,[z1,z3,z4,z5,z6,z992]),(0,[z0,z3,z4,z993,z5,z6])],[(0,[z428,z1,z3,z4,z5,z6]),(0,[z25,z1,z493,z4,z5,z6]),(0,[z0,z3,z4,z5,z6,z994]),(0,[z1,z3,z143,z5,z15,z6])],[(0,[z159,z3,z4,z5,z15,z6]),(0,[z85,z337,z161,z4,z5,z6]),(0,[z27,z184,z3,z185,z5,z6]),(0,[z995,z1,z3,z4,z5,z6])],[(0,[z0,z996,z3,z4,z5,z6]),(0,[z105,z1,z3,z4,z5,z241]),(0,[z18,z1,z3,z4,z88,z75]),(0,[z1,z3,z4,z5,z6,z997]),(0,[z0,z1,z998,z4,z5,z6])],[(0,[z1,z3,z4,z5,z999,z6]),(0,[z1,z3,z4,z5,z6,z1000]),(0,[z0,z1,z384,z4,z5,z17])],[(0,[z369,z1,z3,z4,z5,z6]),(0,[z59,z1,z3,z295,z5,z6]),(0,[z1,z3,z4,z5,z452,z204]),(0,[z1,z3,z4,z5,z1001,z6]),(0,[z1,z1002,z3,z4,z5,z6])],[(0,[z54,z3,z174,z4,z5,z6]),(0,[z1,z14,z4,z302,z5,z6]),(0,[z1,z3,z4,z5,z15,z235]),(0,[z0,z1,z3,z80,z5,z6]),(0,[z27,z3,z247,z185,z5,z6]),(0,[z46,z0,z3,z4,z5,z33])],[(0,[z18,z1,z3,z4,z534,z33]),(0,[z1003,z0,z3,z4,z5,z6])],[(0,[z85,z0,z161,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1004])],[(0,[z157,z337,z3,z4,z5,z6]),(0,[z85,z105,z1,z3,z4,z5]),(0,[z0,z3,z57,z4,z5,z6]),(0,[z1005,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z569])],[(0,[z858,z0,z1,z3,z4,z6]),(0,[z18,z1,z3,z22,z73,z6]),(0,[z61,z1,z3,z4,z5,z15]),(0,[z1,z16,z4,z5,z15,z17]),(0,[z46,z0,z3,z4,z5,z6]),(0,[z1006,z3,z4,z5,z330,z6])],[(0,[z25,z124,z3,z4,z5,z6]),(0,[z0,z990,z3,z4,z5,z6]),(0,[z273,z3,z4,z5,z15,z6])],[(0,[z25,z297,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z432,z6]),(0,[z0,z3,z4,z43,z340,z6]),(0,[z197,z0,z3,z44,z5,z6]),(0,[z68,z256,z1,z4,z5,z47]),(0,[z1007,z1,z3,z4,z5,z6])]],
   [[(0,[z193,z25,z1,z3,z5,z45]),(0,[z0,z210,z3,z4,z5,z308])],[],[(0,[z1,z3,z22,z73,z15,z6])],[(0,[z18,z445,z1,z3,z4,z5]),(0,[z27,z501,z3,z4,z5,z6]),(0,[z1008,z1,z3,z4,z5,z6]),(0,[z256,z159,z3,z4,z5,z6]),(0,[z0,z1,z3,z331,z372,z6]),(0,[z946,z1,z326,z4,z5,z6]),(0,[z1,z3,z4,z1009,z5,z6])],[(0,[z0,z1,z3,z4,z5,z945]),(0,[z169,z1,z468,z14,z4,z5]),(0,[z261,z0,z1,z44,z5,z6]),(0,[z0,z1010,z3,z4,z5,z6])],[(0,[z18,z1,z3,z4,z33,z75]),(0,[z0,z893,z161,z4,z5,z6]),(0,[z1011,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z1012]),(0,[z0,z1,z3,z4,z5,z1013]),(0,[z0,z1,z1014,z4,z5,z6]),(0,[z3,z4,z5,z6,z49,z51])],[(0,[z25,z934,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z6,z1015]),(0,[z18,z1,z101,z4,z171,z6]),(0,[z68,z0,z4,z5,z167,z47]),(0,[z195,z0,z3,z357,z98,z6]),(0,[z0,z1016,z3,z4,z5,z6])],[(0,[z134,z25,z1,z3,z4,z75]),(0,[z1,z3,z4,z5,z1017,z6])],[],[(0,[z38,z3,z4,z5,z6,z183]),(0,[z1,z3,z14,z4,z5,z211]),(0,[z0,z71,z893,z4,z5,z6]),(0,[z0,z124,z3,z4,z5,z6]),(0,[z0,z1,z1018,z4,z5,z6])],[(0,[z0,z297,z3,z4,z5,z6]),(0,[z319,z3,z4,z5,z15,z6]),(0,[z0,z1,z4,z5,z6,z1019]),(0,[z236,z0,z1,z4,z5,z47]),(0,[z0,z381,z326,z4,z5,z6]),(0,[z0,z1,z3,z1020,z5,z6])],[(0,[z105,z1,z3,z4,z5,z15]),(0,[z0,z3,z1021,z4,z5,z6])],[(0,[z93,z1,z16,z3,z4,z5]),(0,[z0,z176,z3,z4,z5,z298]),(0,[z1022,z1,z3,z4,z5,z6])],[(0,[z36,z1,z3,z4,z5,z6]),(0,[z1,z3,z4,z1023,z5,z6]),(0,[z0,z3,z4,z5,z110,z1024]),(0,[z0,z1,z101,z325,z5,z6])],[(0,[z1025,z1,z3,z4,z5,z6]),(1,[z0,z3,z1026,z5,z6]),(0,[z0,z3,z4,z5,z1027,z6]),(0,[z1028,z1,z3,z4,z5,z6]),(0,[z428,z1,z3,z4,z5,z211]),(0,[z81,z1,z487,z4,z5,z6])]],
   [[(0,[z25,z3,z4,z5,z6,z183]),(0,[z18,z55,z3,z4,z5,z6]),(0,[z93,z1,z278,z4,z5,z6]),(0,[z18,z1,z3,z112,z4,z5]),(0,[z0,z176,z3,z4,z5,z581])],[(0,[z1,z3,z4,z5,z15,z481]),(0,[z1,z101,z91,z4,z171,z6]),(0,[z1029,z1,z3,z4,z5,z6]),(0,[z0,z1,z326,z4,z5,z516])],[(0,[z1030,z1,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z298,z66]),(0,[z1,z3,z4,z5,z1031,z6])],[(0,[z65,z3,z375,z4,z5,z6]),(0,[z0,z1,z3,z1032,z5,z6]),(0,[z1,z507,z4,z5,z17,z6]),(0,[z1,z3,z4,z1033,z15,z6]),(0,[z1034,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z1035,z5,z6]),(0,[z130,z0,z3,z4,z5,z465]),(0,[z1036,z1,z3,z4,z5,z6])],[(0,[z105,z54,z3,z14,z4,z5]),(0,[z130,z25,z3,z4,z5,z66]),(0,[z182,z419,z3,z4,z5,z6]),(0,[z18,z267,z3,z4,z5,z15]),(0,[z0,z42,z3,z4,z617,z6]),(0,[z0,z1,z3,z4,z5,z1037]),(0,[z0,z3,z4,z5,z6,z1038]),(0,[z0,z1,z3,z1039,z5,z6]),(0,[z0,z1040,z3,z4,z5,z6]),(0,[z68,z63,z1,z4,z5,z47]),(0,[z1,z3,z4,z1041,z5,z6])],[(0,[z18,z3,z4,z5,z15,z183]),(0,[z134,z244,z1,z3,z4,z75])],[(0,[z18,z1,z3,z4,z5,z527]),(0,[z1,z3,z4,z5,z1042,z6]),(0,[z1043,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z1044]),(0,[z157,z578,z3,z4,z5,z6]),(0,[z65,z3,z4,z388,z5,z6]),(0,[z0,z3,z13,z468,z4,z5]),(0,[z0,z1,z3,z4,z5,z1045]),(0,[z1,z3,z1046,z4,z5,z6]),(0,[z130,z3,z4,z5,z15,z66]),(0,[z912,z0,z1,z3,z4,z5]),(0,[z0,z146,z3,z4,z5,z33])],[(0,[z0,z3,z4,z5,z1047,z6]),(0,[z25,z381,z3,z4,z5,z6]),(0,[z1048,z1,z3,z4,z5,z6]),(0,[z140,z0,z4,z330,z88,z6])],[(0,[z196,z3,z14,z4,z5,z6]),(0,[z1,z3,z4,z5,z529,z6]),(0,[z1049,z1,z3,z4,z5,z6]),(0,[z68,z63,z1,z3,z4,z5])],[(0,[z0,z152,z3,z545,z5,z6]),(0,[z257,z1,z3,z4,z372,z6]),(0,[z420,z1,z326,z4,z5,z6]),(0,[z1050,z1,z3,z4,z5,z6]),(0,[z135,z146,z3,z4,z5,z6])],[(0,[z275,z3,z4,z5,z15,z6]),(1,[z0,z1,z3,z4,z770])],[(0,[z0,z3,z4,z5,z6,z183]),(0,[z18,z1,z3,z4,z5,z447]),(0,[z1,z3,z1051,z4,z5,z6]),(0,[z1,z3,z1052,z4,z5,z6]),(1,[z912,z1,z3,z4,z5]),(0,[z195,z0,z1,z487,z98,z6])],[(0,[z1,z370,z4,z5,z6,z291]),(0,[z18,z1,z3,z4,z931,z6]),(0,[z18,z1,z3,z4,z5,z666]),(1,[z18,z1,z3,z4,z389]),(0,[z428,z1,z3,z325,z5,z6]),(0,[z0,z1053,z3,z4,z5,z6])],[(0,[z25,z1,z3,z4,z5,z516]),(0,[z0,z1054,z3,z4,z5,z6]),(0,[z1,z3,z4,z15,z6,z1015]),(0,[z1055,z1,z3,z4,z5,z6]),(0,[z0,z1,z644,z21,z5,z6]),(0,[z1,z3,z1056,z4,z5,z6]),(0,[z1057,z1,z3,z4,z5,z6]),(0,[z1,z3,z1058,z4,z5,z6])],[(0,[z0,z3,z4,z1059,z5,z6]),(0,[z1060,z0,z1,z4,z5,z6]),(0,[z1,z3,z4,z1061,z5,z6]),(0,[z0,z1,z3,z4,z770,z75])]],
   [[(0,[z0,z1062,z3,z4,z5,z6]),(0,[z1,z14,z4,z5,z205,z6]),(0,[z27,z0,z3,z535,z5,z6]),(0,[z195,z0,z1,z3,z98,z235])],[(0,[z0,z1,z3,z4,z1063,z6]),(0,[z990,z3,z4,z5,z525,z6]),(0,[z267,z3,z144,z4,z5,z6]),(0,[z18,z3,z4,z5,z330,z6]),(0,[z1064,z1,z3,z4,z5,z6])],[(0,[z54,z84,z3,z4,z5,z6]),(0,[z169,z1,z507,z4,z5,z6]),(0,[z25,z1,z507,z4,z5,z6]),(0,[z0,z159,z3,z4,z5,z6]),(0,[z0,z1,z3,z1065,z98,z6])],[],[(0,[z1066,z1,z3,z4,z5,z6]),(0,[z25,z263,z3,z4,z5,z6]),(0,[z25,z434,z3,z4,z5,z6]),(0,[z0,z381,z3,z4,z5,z6]),(0,[z1067,z0,z3,z4,z5,z6]),(0,[z429,z0,z3,z44,z5,z6]),(0,[z1,z3,z4,z5,z1068,z6]),(0,[z195,z0,z1,z3,z1065,z6])],[(0,[z1069,z1,z3,z4,z5,z6])],[(0,[z1070,z1,z3,z4,z5,z6])],[(0,[z157,z3,z606,z4,z5,z6]),(0,[z1,z378,z14,z4,z5,z6]),(0,[z46,z3,z14,z4,z5,z6]),(0,[z25,z1,z119,z4,z5,z6]),(0,[z279,z1,z3,z4,z5,z75])],[(0,[z260,z105,z1,z3,z4,z5]),(0,[z1071,z0,z3,z4,z5,z6]),(0,[z0,z176,z3,z4,z5,z1024]),(0,[z1072,z1,z3,z4,z5,z6]),(0,[z273,z3,z139,z4,z5,z6]),(0,[z3,z4,z1073,z422,z5,z6])],[(0,[z1,z3,z468,z4,z5,z368]),(0,[z18,z1,z16,z4,z5,z17])],[(0,[z1,z3,z4,z5,z1074,z6]),(0,[z0,z3,z4,z5,z6,z1075]),(0,[z0,z3,z4,z5,z1076,z6]),(0,[z0,z1,z3,z4,z5,z516])],[(0,[z18,z1,z3,z4,z5,z594]),(0,[z18,z1062,z3,z4,z5,z6]),(0,[z18,z1,z3,z4,z5,z15])],[(0,[z1,z3,z4,z5,z56,z6]),(0,[z826,z3,z14,z4,z5,z6]),(0,[z18,z1,z3,z4,z1063,z6]),(0,[z18,z1,z3,z4,z5,z328])],[(0,[z0,z3,z4,z1073,z5,z6])],[(0,[z0,z3,z13,z4,z5,z6]),(0,[z65,z3,z4,z5,z6,z138]),(1,[z105,z1,z3,z4,z5]),(0,[z1,z16,z3,z507,z4,z5])],[(0,[z0,z3,z4,z5,z379,z66]),(0,[z25,z1077,z3,z4,z5,z6]),(0,[z25,z1,z3,z80,z5,z6]),(0,[z18,z381,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z1078]),(1,[z0,z893,z4,z5,z6])]],
   [[(1,[z897,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z1079]),(0,[z437,z1,z3,z4,z5,z6]),(0,[z0,z263,z3,z4,z5,z6]),(0,[z0,z1,z3,z22,z637,z6]),(0,[z1080,z0,z3,z4,z5,z6])],[(0,[z38,z3,z4,z321,z5,z6]),(0,[z105,z1,z3,z468,z4,z5]),(0,[z1,z3,z1081,z4,z5,z6]),(0,[z1082,z1,z3,z4,z5,z6]),(0,[z1083,z1,z3,z4,z5,z6])],[(0,[z193,z105,z1,z3,z4,z5]),(0,[z884,z18,z3,z4,z5,z6]),(0,[z1084,z3,z4,z5,z15,z6])],[(0,[z1,z477,z3,z4,z5,z15]),(0,[z105,z1,z3,z4,z5,z368]),(0,[z25,z1,z3,z4,z5,z569]),(0,[z1,z3,z4,z1085,z5,z6]),(0,[z1086,z1,z3,z4,z5,z6])],[(0,[z256,z1,z3,z7,z5,z6]),(0,[z0,z124,z326,z4,z5,z6])],[(0,[z18,z1,z3,z4,z5,z516]),(0,[z1087,z1,z3,z4,z5,z6]),(0,[z607,z0,z1,z44,z5,z6]),(0,[z922,z1,z3,z4,z5,z6])],[(0,[z24,z1,z3,z4,z5,z525]),(0,[z232,z1,z3,z4,z534,z6]),(0,[z1088,z1,z3,z4,z5,z6])],[(0,[z1,z415,z14,z4,z5,z6]),(0,[z18,z3,z4,z5,z975,z6]),(0,[z27,z0,z3,z592,z5,z6])],[(0,[z0,z863,z3,z4,z5,z6]),(0,[z40,z1,z3,z4,z534,z6]),(0,[z1,z3,z4,z5,z6,z74]),(0,[z130,z0,z3,z80,z5,z6]),(0,[z0,z3,z4,z5,z1089,z6]),(0,[z281,z1,z122,z21,z5,z6]),(0,[z428,z319,z3,z4,z5,z6]),(0,[z68,z0,z1,z4,z372,z47])],[(0,[z169,z54,z14,z4,z5,z6]),(0,[z25,z1,z3,z468,z4,z5]),(0,[z25,z267,z3,z4,z5,z6]),(0,[z18,z1,z3,z4,z5,z683]),(0,[z0,z3,z4,z5,z6,z1090]),(0,[z0,z275,z3,z4,z156,z33])],[(0,[z163,z1,z3,z4,z5,z6]),(0,[z1,z3,z4,z1091,z5,z6]),(0,[z1092,z1,z3,z4,z5,z6])],[(0,[z1,z326,z14,z4,z5,z6]),(0,[z0,z1077,z3,z4,z5,z6]),(0,[z18,z263,z3,z4,z5,z6]),(0,[z18,z434,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z6,z49])],[(0,[z18,z273,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z871,z75]),(0,[z1,z4,z5,z17,z6,z291]),(0,[z1093,z0,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z389,z17])],[(0,[z256,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z6,z1094]),(0,[z0,z1,z3,z1095,z5,z6]),(0,[z1,z3,z4,z5,z1096,z6])],[(0,[z1097,z1,z3,z4,z5,z6]),(0,[z0,z1098,z3,z4,z5,z6]),(0,[z3,z780,z91,z4,z5,z6])],[(0,[z0,z3,z4,z5,z1099,z6]),(0,[z428,z1,z3,z4,z5,z308]),(0,[z0,z1,z4,z5,z6,z1100])]],
   [[(0,[z0,z210,z3,z143,z5,z6]),(0,[z140,z0,z1,z4,z88,z6])],[(0,[z1,z3,z14,z4,z5,z1101]),(0,[z0,z1,z1102,z4,z5,z6]),(0,[z0,z3,z4,z5,z6,z1103]),(0,[z0,z1,z325,z5,z88,z6])],[(0,[z54,z3,z4,z5,z368,z6]),(0,[z0,z1,z3,z4,z1104,z6]),(0,[z1105,z1,z3,z4,z5,z6])],[(0,[z105,z1,z3,z4,z5,z33]),(0,[z197,z25,z3,z4,z5,z6]),(0,[z0,z192,z122,z21,z5,z6])],[(0,[z131,z1,z3,z601,z5,z6]),(0,[z90,z0,z3,z4,z630,z6]),(0,[z0,z1,z3,z4,z5,z1106]),(1,[z0,z1,z802,z5,z6]),(0,[z1107,z0,z3,z4,z5,z6]),(0,[z1108,z1,z3,z4,z5,z6])],[(0,[z0,z267,z3,z4,z5,z6]),(0,[z105,z1,z3,z4,z5,z45]),(0,[z0,z1,z3,z468,z4,z5]),(0,[z25,z176,z3,z4,z5,z110]),(0,[z1109,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z5,z6,z771]),(0,[z0,z3,z4,z1110,z5,z6]),(0,[z1,z3,z4,z1111,z5,z6]),(0,[z1,z3,z4,z5,z1112,z516])],[(0,[z193,z1,z3,z14,z5,z45]),(0,[z18,z1,z3,z80,z5,z6]),(0,[z197,z3,z4,z5,z15,z6]),(0,[z0,z3,z1026,z185,z5,z6])],[(0,[z0,z1,z3,z1113,z5,z6]),(0,[z1,z14,z4,z335,z5,z6]),(0,[z1,z3,z4,z5,z1114,z6]),(0,[z3,z4,z5,z172,z15,z6]),(0,[z1,z3,z4,z5,z6,z1115]),(0,[z1116,z1,z3,z4,z5,z6]),(0,[z1117,z0,z3,z4,z5,z6]),(0,[z0,z1118,z3,z4,z5,z6])],[(0,[z1,z3,z14,z438,z5,z6])],[(0,[z18,z3,z57,z4,z5,z6]),(0,[z61,z0,z1,z3,z4,z389]),(0,[z0,z3,z4,z1119,z5,z6]),(0,[z1,z3,z4,z5,z850,z569]),(0,[z0,z3,z1120,z4,z5,z6]),(0,[z3,z4,z5,z529,z172,z6])],[(0,[z105,z1,z3,z4,z401,z5]),(0,[z18,z1,z3,z4,z5,z569]),(0,[z0,z3,z4,z5,z6,z1121])],[(0,[z863,z3,z4,z5,z368,z6]),(0,[z1,z3,z4,z5,z6,z114]),(0,[z0,z3,z4,z5,z6,z1122]),(0,[z1123,z1,z3,z4,z5,z6]),(1,[z0,z1,z4,z5,z775])],[(0,[z1124,z1,z3,z4,z5,z6])],[(0,[z1125,z105,z1,z3,z4,z5]),(0,[z1,z3,z4,z5,z6,z1126]),(0,[z0,z3,z80,z43,z5,z6]),(0,[z1127,z1,z3,z4,z5,z6]),(0,[z1108,z3,z4,z5,z6,z409])],[(0,[z134,z1,z3,z14,z4,z75]),(0,[z0,z1,z3,z832,z5,z6]),(0,[z0,z1,z3,z4,z5,z1128])],[(0,[z1,z3,z4,z5,z1129,z6])]],
   [[(0,[z18,z267,z3,z4,z5,z6]),(0,[z1130,z1,z3,z4,z5,z6]),(0,[z3,z4,z1131,z413,z5,z6]),(0,[z1,z1132,z3,z4,z5,z6]),(0,[z193,z0,z263,z3,z5,z45])],[(0,[z0,z1,z3,z4,z5,z1133]),(0,[z3,z13,z4,z5,z368,z6]),(0,[z0,z1,z3,z4,z1033,z6]),(0,[z369,z1,z3,z438,z5,z6]),(0,[z0,z176,z3,z4,z5,z110]),(0,[z0,z1134,z3,z4,z5,z6]),(0,[z1135,z1,z3,z4,z5,z6])],[(0,[z434,z3,z14,z4,z5,z6]),(0,[z0,z1,z3,z1136,z5,z6]),(0,[z27,z0,z3,z185,z5,z6])],[(0,[z85,z14,z161,z4,z5,z6]),(0,[z1137,z0,z3,z4,z5,z6]),(0,[z25,z146,z3,z4,z5,z6]),(0,[z41,z1,z3,z4,z843,z6]),(0,[z1,z3,z4,z5,z15,z824]),(1,[z0,z3,z4,z879,z6]),(0,[z501,z1,z3,z4,z5,z298]),(0,[z0,z1,z3,z7,z5,z6]),(0,[z1138,z1,z3,z4,z5,z6])],[(0,[z18,z1,z3,z4,z5,z424]),(0,[z105,z1,z3,z4,z43,z5]),(0,[z131,z105,z1,z3,z4,z5])],[(0,[z1,z487,z14,z4,z5,z6]),(0,[z41,z1,z3,z4,z457,z6]),(0,[z1,z3,z4,z5,z6,z1139]),(0,[z0,z1,z101,z4,z862,z6]),(0,[z135,z1,z3,z4,z5,z33])],[(0,[z124,z3,z14,z4,z5,z6]),(0,[z0,z3,z1140,z4,z5,z6]),(0,[z3,z4,z5,z203,z15,z6]),(0,[z1,z1141,z3,z4,z5,z6])],[(0,[z42,z3,z14,z4,z43,z6]),(0,[z1,z492,z14,z4,z5,z6]),(0,[z18,z1,z3,z4,z5,z241]),(0,[z166,z0,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z6,z167]),(0,[z81,z1,z3,z4,z5,z235])],[(0,[z0,z1142,z3,z4,z5,z6]),(0,[z1,z3,z4,z26,z843,z6]),(0,[z18,z124,z3,z4,z5,z6]),(0,[z0,z1,z16,z254,z4,z5]),(0,[z1,z3,z80,z5,z15,z6]),(0,[z134,z1,z3,z4,z15,z75]),(0,[z1143,z1,z3,z4,z5,z6]),(0,[z140,z0,z1,z4,z862,z6])],[(0,[z65,z69,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z1144,z6]),(0,[z25,z159,z3,z4,z5,z6]),(0,[z25,z3,z4,z5,z6,z409]),(0,[z18,z297,z3,z4,z5,z6]),(0,[z925,z1,z3,z4,z5,z308]),(0,[z1145,z0,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z6,z1146])],[(0,[z135,z1,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z203,z204]),(0,[z61,z256,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z1147])],[(0,[z105,z176,z1,z3,z4,z5]),(0,[z1,z3,z14,z325,z5,z6]),(0,[z0,z3,z4,z1148,z5,z6]),(0,[z1149,z0,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6]),(0,[z1,z3,z14,z331,z5,z6]),(0,[z55,z3,z144,z4,z5,z6]),(0,[z18,z1,z3,z30,z5,z31]),(0,[z140,z0,z1,z4,z88,z211]),(0,[z0,z159,z3,z7,z5,z6]),(0,[z68,z0,z1,z4,z5,z775]),(0,[z0,z1,z3,z5,z1065,z6])],[(0,[z27,z0,z3,z653,z5,z6]),(0,[z1,z177,z3,z4,z5,z6]),(0,[z105,z3,z13,z4,z5,z6]),(0,[z1,z3,z14,z5,z1150,z6]),(0,[z68,z25,z1,z4,z5,z47]),(0,[z1151,z1,z3,z4,z5,z6])],[(0,[z71,z79,z14,z4,z5,z6]),(0,[z1,z3,z14,z4,z5,z1152]),(0,[z197,z0,z3,z21,z5,z6])],[(0,[z38,z3,z13,z4,z5,z6]),(0,[z3,z4,z5,z368,z6,z798]),(0,[z105,z1,z3,z144,z4,z5]),(0,[z0,z42,z3,z4,z20,z6]),(0,[z1,z3,z4,z5,z1153,z6]),(0,[z0,z146,z3,z4,z5,z6]),(0,[z1,z3,z1154,z4,z5,z6])]],
   [[(0,[z157,z2,z3,z4,z5,z6]),(0,[z333,z1,z14,z4,z5,z6]),(0,[z1,z3,z794,z5,z15,z6]),(0,[z1,z3,z4,z5,z944,z298])],[(0,[z1,z3,z1155,z4,z5,z6])],[(0,[z105,z1,z3,z4,z5,z66]),(0,[z18,z130,z3,z4,z5,z66]),(0,[z134,z0,z1,z3,z4,z770])],[(0,[z18,z1142,z3,z4,z5,z6])],[(0,[z0,z1156,z3,z4,z5,z6]),(0,[z140,z105,z1,z3,z4,z5]),(0,[z18,z1,z78,z3,z4,z5]),(0,[z0,z3,z161,z80,z5,z6])],[(0,[z25,z3,z13,z4,z5,z6]),(0,[z1157,z1,z3,z14,z5,z6]),(0,[z1,z3,z4,z5,z6,z824]),(0,[z0,z3,z4,z5,z6,z409]),(1,[z0,z1,z4,z862,z6])],[(0,[z1,z3,z375,z80,z5,z6]),(0,[z501,z42,z3,z4,z43,z6]),(0,[z1,z3,z4,z5,z1158,z6]),(0,[z0,z196,z3,z4,z372,z6]),(0,[z1159,z1,z3,z4,z5,z6])],[(0,[z134,z0,z1,z3,z4,z75])],[(0,[z105,z1,z84,z3,z4,z5]),(0,[z429,z25,z3,z4,z5,z6]),(0,[z0,z1,z3,z1160,z5,z6]),(0,[z256,z1,z3,z331,z5,z6]),(0,[z0,z1,z1161,z4,z5,z6])],[(0,[z105,z256,z1,z3,z4,z5]),(0,[z0,z3,z4,z5,z6,z842]),(0,[z0,z1084,z3,z4,z5,z6]),(1,[z0,z3,z4,z5,z1024])],[(0,[z18,z1,z3,z4,z5,z483]),(0,[z1162,z1,z3,z4,z5,z6]),(0,[z68,z18,z1,z278,z4,z5]),(0,[z18,z3,z4,z5,z6,z183]),(0,[z140,z0,z1,z325,z88,z6]),(0,[z0,z3,z1163,z4,z5,z6])],[(0,[z157,z897,z3,z4,z5,z6]),(0,[z25,z1,z682,z4,z5,z6]),(0,[z1,z3,z325,z5,z15,z6]),(0,[z429,z3,z4,z5,z15,z6]),(0,[z0,z1164,z3,z4,z5,z6]),(0,[z0,z1,z122,z802,z5,z6]),(0,[z93,z1,z16,z4,z5,z17])],[(0,[z1165,z1,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z1166,z6])],[(0,[z1,z3,z4,z1167,z5,z6]),(0,[z0,z1,z3,z4,z843,z6]),(0,[z1168,z1,z3,z4,z5,z6])],[(0,[z54,z3,z468,z14,z4,z5]),(0,[z1,z507,z4,z44,z5,z6])],[(0,[z267,z3,z14,z4,z5,z6])]],
   [[(0,[z18,z159,z3,z4,z5,z6]),(0,[z1169,z1,z3,z4,z5,z516])],[(0,[z1,z897,z3,z4,z5,z6]),(0,[z1,z3,z14,z4,z389,z6]),(0,[z68,z18,z1,z3,z4,z389]),(0,[z0,z1,z3,z1170,z5,z6]),(0,[z0,z1,z3,z1171,z5,z6]),(0,[z0,z1172,z3,z4,z5,z6])],[(0,[z1,z3,z777,z4,z5,z6]),(0,[z25,z3,z4,z5,z6,z49]),(0,[z1,z3,z4,z5,z15,z204]),(0,[z1173,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z1174,z5,z6]),(0,[z0,z1,z3,z4,z5,z1175])],[(0,[z1,z3,z1176,z4,z5,z6]),(0,[z0,z3,z120,z1026,z5,z6]),(0,[z130,z0,z3,z4,z5,z66])],[(0,[z184,z79,z3,z4,z5,z6])],[(0,[z1,z3,z4,z156,z15,z33])],[(0,[z0,z1,z3,z4,z5,z1177]),(0,[z1,z3,z14,z4,z5,z298]),(0,[z1,z3,z1178,z4,z5,z6]),(0,[z1179,z0,z1,z3,z5,z6]),(0,[z454,z0,z1,z44,z5,z6]),(0,[z1180,z1,z3,z4,z5,z6]),(0,[z1181,z1,z3,z4,z5,z6]),(0,[z0,z1182,z3,z4,z5,z6]),(0,[z0,z968,z3,z4,z5,z6])],[(0,[z105,z71,z1,z3,z4,z5]),(0,[z18,z0,z1,z3,z4,z389]),(0,[z0,z1,z3,z4,z5,z1183]),(0,[z616,z0,z3,z185,z5,z6])],[(0,[z1,z3,z1184,z4,z5,z6]),(0,[z1,z1185,z3,z4,z5,z6]),(0,[z85,z18,z161,z4,z5,z6]),(0,[z1,z3,z1186,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z211]),(0,[z239,z0,z1,z3,z4,z75])],[(0,[z1,z14,z611,z4,z5,z6]),(0,[z130,z3,z4,z5,z138,z66]),(0,[z299,z0,z1,z3,z98,z6]),(0,[z0,z1,z3,z1187,z4,z5]),(0,[z1188,z0,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z1189,z6]),(0,[z1,z3,z4,z1190,z5,z6])],[(0,[z25,z1,z326,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1191]),(0,[z0,z1,z3,z1192,z5,z6]),(0,[z1,z3,z4,z5,z6,z1193])],[(0,[z25,z1,z108,z4,z5,z6]),(0,[z0,z1,z3,z4,z1194,z6]),(0,[z90,z0,z3,z80,z5,z6]),(0,[z420,z1,z487,z4,z5,z6]),(0,[z0,z1,z3,z4,z1065,z6]),(0,[z3,z4,z5,z357,z432,z6])],[(0,[z105,z54,z1,z3,z4,z5]),(0,[z27,z3,z14,z185,z5,z6]),(0,[z18,z3,z13,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z1195]),(0,[z1196,z1,z3,z4,z5,z6])],[(0,[z3,z13,z468,z14,z4,z5]),(0,[z1,z3,z14,z4,z5,z308]),(0,[z1137,z3,z14,z4,z5,z6]),(0,[z0,z1,z101,z4,z35,z6]),(0,[z0,z1197,z3,z4,z5,z6]),(0,[z256,z1,z3,z4,z389,z6])],[(0,[z3,z14,z4,z5,z203,z6]),(0,[z0,z1,z3,z4,z5,z1198])],[(0,[z0,z3,z120,z530,z5,z6]),(0,[z25,z1,z118,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1199])]],
   [[(0,[z55,z0,z3,z4,z5,z6])],[(0,[z261,z1,z14,z44,z5,z6]),(0,[z166,z3,z14,z4,z5,z6]),(0,[z1,z3,z1200,z4,z5,z6]),(0,[z1,z3,z4,z1201,z5,z6]),(0,[z1202,z1,z3,z4,z5,z6]),(0,[z0,z3,z4,z156,z33,z409])],[(0,[z105,z157,z1,z3,z4,z5]),(0,[z68,z105,z1,z3,z4,z5]),(0,[z3,z14,z4,z154,z5,z6]),(0,[z25,z3,z4,z5,z357,z6]),(0,[z1,z3,z4,z1203,z5,z6]),(0,[z261,z18,z1,z44,z5,z6]),(0,[z176,z3,z4,z5,z110,z15]),(0,[z0,z1,z122,z266,z5,z6]),(0,[z1204,z1,z3,z4,z5,z6]),(0,[z1205,z1,z3,z4,z5,z6])],[(0,[z105,z1,z3,z4,z5,z221]),(0,[z90,z25,z3,z4,z162,z6]),(0,[z429,z0,z3,z21,z5,z6])],[(0,[z0,z1,z3,z1206,z5,z6]),(0,[z46,z3,z4,z5,z6,z114]),(0,[z1,z3,z4,z5,z1207,z6])],[(0,[z1208,z1,z3,z4,z5,z6])],[(0,[z217,z1,z14,z4,z5,z6]),(0,[z1,z3,z91,z4,z5,z6]),(0,[z1209,z0,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1210]),(0,[z192,z3,z4,z5,z15,z6]),(0,[z0,z1,z326,z4,z5,z6]),(0,[z1006,z1,z3,z4,z5,z6])],[(0,[z3,z13,z375,z4,z5,z6]),(0,[z0,z3,z893,z4,z5,z6]),(0,[z68,z1,z4,z5,z114,z47]),(0,[z1,z3,z1211,z4,z5,z6])],[(0,[z18,z256,z1,z3,z4,z5]),(0,[z0,z3,z1212,z4,z5,z6])],[(0,[z3,z14,z4,z730,z5,z6]),(0,[z54,z41,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z1213]),(0,[z18,z3,z4,z5,z6,z49]),(0,[z0,z3,z4,z1026,z5,z6]),(0,[z1214,z1,z3,z4,z5,z6]),(0,[z146,z3,z4,z5,z529,z6])],[(0,[z105,z1,z3,z4,z103,z5]),(0,[z1215,z25,z3,z4,z5,z6]),(0,[z25,z1,z3,z7,z5,z6]),(0,[z1216,z0,z3,z4,z5,z6])],[(0,[z105,z1,z3,z4,z5,z6]),(0,[z85,z501,z3,z4,z5,z6]),(0,[z0,z122,z21,z413,z5,z6]),(0,[z140,z0,z210,z4,z88,z6])],[],[(0,[z54,z25,z3,z4,z5,z6]),(0,[z105,z25,z1,z14,z4,z5]),(0,[z0,z1217,z3,z4,z5,z6]),(0,[z297,z3,z4,z5,z15,z6]),(0,[z0,z3,z4,z5,z203,z322]),(0,[z1,z122,z21,z5,z15,z6]),(0,[z0,z79,z4,z5,z6,z338]),(0,[z0,z1,z21,z802,z5,z6]),(0,[z575,z0,z1,z3,z4,z75])],[(0,[z25,z3,z4,z5,z6,z167]),(0,[z236,z18,z1,z3,z4,z5]),(0,[z0,z3,z4,z5,z357,z6]),(0,[z1218,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1219])],[(0,[z1220,z105,z1,z3,z4,z5]),(0,[z501,z79,z3,z4,z5,z6])]],
   [[(0,[z260,z54,z3,z4,z5,z6]),(0,[z105,z1,z3,z22,z4,z5]),(0,[z54,z3,z4,z5,z15,z6]),(0,[z25,z3,z4,z5,z172,z6]),(0,[z1,z3,z4,z5,z6,z1221]),(0,[z0,z1222,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z171,z211]),(0,[z0,z159,z3,z331,z5,z6])],[(0,[z105,z1,z3,z4,z156,z5]),(0,[z0,z1,z1223,z4,z5,z6]),(0,[z1,z3,z4,z5,z1224,z6])],[(0,[z0,z1,z3,z4,z5,z1225]),(0,[z0,z1226,z3,z4,z5,z6])],[(0,[z25,z1,z3,z4,z5,z6]),(0,[z105,z1,z3,z1227,z4,z5]),(0,[z18,z1,z3,z468,z4,z5]),(0,[z1228,z1,z3,z4,z5,z6])],[(0,[z3,z14,z4,z413,z5,z6]),(0,[z105,z1,z1229,z3,z4,z5]),(0,[z1230,z1,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z1231,z6]),(0,[z0,z3,z1232,z4,z5,z6])],[(0,[z1233,z0,z3,z4,z5,z6]),(0,[z18,z1,z3,z1113,z5,z6]),(0,[z263,z3,z4,z5,z15,z6]),(0,[z0,z124,z487,z4,z5,z6]),(0,[z0,z1,z3,z73,z1065,z6]),(0,[z1234,z1,z3,z4,z5,z6]),(0,[z193,z282,z1,z3,z5,z45])],[(0,[z157,z231,z3,z4,z5,z6]),(0,[z90,z0,z3,z4,z660,z6]),(0,[z184,z176,z3,z4,z5,z6])],[(0,[z18,z1,z3,z4,z5,z9]),(0,[z1235,z1,z3,z4,z5,z6]),(0,[z1236,z1,z3,z4,z5,z6]),(0,[z1,z3,z1237,z4,z5,z6]),(0,[z0,z1,z3,z4,z1238,z6]),(0,[z0,z42,z3,z4,z43,z569])],[(0,[z1239,z1,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z6,z1240])],[(0,[z105,z1,z3,z334,z4,z5]),(0,[z1,z3,z1160,z5,z15,z6]),(0,[z844,z3,z4,z5,z15,z6]),(0,[z0,z3,z80,z413,z5,z6])],[(0,[z0,z1,z3,z4,z5,z1241]),(0,[z157,z177,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z298,z409]),(0,[z0,z1242,z3,z4,z5,z6]),(0,[z135,z3,z4,z5,z172,z6])],[(0,[z1,z3,z1243,z4,z5,z6]),(0,[z1244,z1,z3,z4,z5,z6]),(0,[z0,z1,z4,z5,z6,z775])],[(0,[z0,z3,z4,z5,z172,z6]),(0,[z0,z3,z4,z1245,z5,z6]),(0,[z282,z1,z3,z4,z5,z75])],[(0,[z0,z1,z3,z1246,z5,z6]),(0,[z0,z152,z3,z80,z5,z6]),(0,[z0,z1247,z3,z4,z5,z6]),(0,[z68,z46,z0,z4,z5,z47]),(0,[z926,z1,z3,z4,z5,z235]),(0,[z0,z1248,z3,z4,z5,z6])],[(0,[z25,z1,z421,z4,z5,z6]),(0,[z0,z1249,z3,z4,z5,z6]),(0,[z1,z3,z4,z372,z15,z6]),(0,[z445,z0,z3,z4,z5,z66]),(0,[z1,z3,z4,z5,z1250,z6]),(0,[z0,z3,z4,z879,z162,z6]),(0,[z1,z3,z4,z5,z6,z1251])],[(0,[z105,z0,z3,z13,z4,z5]),(0,[z131,z1,z3,z242,z5,z6]),(0,[z18,z176,z3,z4,z5,z110]),(0,[z281,z3,z57,z4,z5,z6])]],
   [[(0,[z0,z3,z4,z5,z1252,z6]),(0,[z0,z1,z3,z1253,z5,z6])],[(0,[z25,z1,z430,z4,z5,z6]),(0,[z1,z14,z4,z5,z557,z6]),(0,[z105,z1,z3,z4,z73,z5]),(0,[z146,z3,z14,z4,z5,z6]),(0,[z0,z1254,z3,z4,z5,z6]),(0,[z1,z3,z144,z5,z6,z315]),(0,[z18,z1,z3,z7,z5,z6]),(0,[z633,z0,z1,z44,z5,z6]),(0,[z1255,z1,z3,z4,z5,z6])],[(0,[z1,z3,z14,z4,z5,z1256]),(0,[z193,z0,z1,z3,z5,z45]),(0,[z1257,z1,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z1258,z6])],[(0,[z152,z3,z14,z120,z5,z6]),(0,[z1259,z1,z3,z4,z5,z6]),(0,[z1260,z1,z3,z4,z5,z6]),(0,[z1,z3,z4,z1261,z5,z6])],[(0,[z0,z3,z4,z5,z6,z798]),(0,[z0,z3,z688,z120,z5,z6]),(0,[z0,z1,z3,z4,z5,z1262])],[(0,[z1,z3,z4,z5,z15,z322]),(0,[z504,z1,z3,z371,z5,z6]),(0,[z18,z1,z3,z4,z5,z33]),(0,[z18,z3,z4,z5,z6,z167]),(0,[z0,z1,z3,z1026,z5,z6]),(0,[z0,z159,z3,z4,z389,z6]),(0,[z195,z197,z0,z3,z98,z6])],[(0,[z0,z3,z4,z5,z1024,z66])],[(0,[z18,z1,z3,z4,z1144,z6]),(0,[z257,z159,z3,z4,z5,z6])],[(0,[z1263,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z6,z770])],[(0,[z65,z0,z3,z80,z5,z6]),(0,[z399,z1,z3,z5,z6,z315]),(0,[z0,z1,z3,z4,z1264,z6]),(0,[z0,z3,z4,z5,z6,z1024]),(0,[z1265,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z5,z6,z1266])],[(0,[z18,z1,z3,z4,z5,z6]),(0,[z55,z3,z14,z4,z5,z6]),(0,[z1267,z1,z3,z4,z5,z6]),(0,[z18,z1,z3,z4,z5,z107]),(0,[z1,z3,z144,z4,z5,z204]),(0,[z1,z3,z4,z1268,z5,z6])],[(0,[z105,z1,z3,z13,z4,z5]),(0,[z195,z25,z1,z3,z98,z6]),(0,[z1,z487,z1211,z4,z5,z6])],[(0,[z1,z3,z4,z5,z6,z1269]),(0,[z244,z1,z3,z4,z5,z6]),(0,[z27,z0,z3,z218,z5,z6]),(0,[z46,z0,z3,z4,z5,z75])],[(0,[z18,z1,z3,z4,z5,z113]),(0,[z18,z146,z3,z4,z5,z6]),(0,[z27,z184,z3,z4,z5,z6])],[(0,[z1270,z1,z3,z4,z5,z6]),(0,[z193,z0,z3,z5,z49,z45]),(0,[z1,z3,z1271,z4,z5,z6])],[(0,[z1,z3,z4,z5,z15,z153]),(0,[z54,z3,z334,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1101]),(0,[z25,z1,z3,z4,z5,z211]),(0,[z0,z3,z1272,z4,z5,z6]),(0,[z0,z1273,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z1274,z6]),(0,[z0,z381,z487,z4,z5,z6])]],
   [[(0,[z1275,z1,z3,z14,z4,z5])],[(0,[z157,z84,z3,z4,z5,z6]),(0,[z1276,z1,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z1277,z6])],[(1,[z1,z777,z4,z5,z6]),(0,[z0,z1278,z3,z4,z5,z6]),(0,[z0,z3,z1279,z4,z5,z6]),(0,[z0,z3,z120,z4,z5,z298]),(0,[z1280,z1,z3,z4,z5,z6])],[(0,[z0,z1281,z3,z4,z5,z6]),(0,[z18,z3,z4,z5,z6,z409]),(0,[z68,z1,z4,z5,z15,z47]),(0,[z68,z0,z1,z7,z5,z47])],[(0,[z25,z1282,z3,z4,z5,z6]),(0,[z1283,z1,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z56,z298]),(0,[z0,z1,z3,z22,z1065,z6]),(0,[z1284,z1,z3,z4,z5,z6])],[(0,[z414,z1,z3,z4,z5,z6]),(0,[z169,z105,z1,z14,z4,z5]),(0,[z1,z3,z4,z5,z6,z1285]),(0,[z0,z1,z3,z4,z5,z1286]),(0,[z0,z1,z487,z4,z5,z516])],[(0,[z0,z1,z3,z438,z5,z6]),(0,[z1287,z1,z3,z4,z5,z6])],[(0,[z1288,z1,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z1289,z6])],[(0,[z0,z1,z3,z1290,z5,z6]),(0,[z134,z105,z1,z3,z4,z5]),(0,[z1,z3,z4,z5,z15,z374]),(0,[z1,z3,z4,z5,z6,z1291])],[(0,[z0,z1,z3,z4,z5,z1292])],[(0,[z1,z570,z14,z4,z5,z6]),(0,[z0,z3,z4,z43,z102,z6]),(0,[z130,z356,z3,z4,z5,z66]),(0,[z1,z3,z4,z5,z1112,z6]),(0,[z193,z1,z3,z5,z51,z45])],[(0,[z1293,z105,z1,z3,z4,z5]),(0,[z0,z3,z4,z5,z6,z902])],[(0,[z1,z3,z4,z5,z6,z1294]),(0,[z68,z0,z1,z4,z5,z47]),(0,[z3,z4,z5,z6,z167,z114]),(0,[z1,z3,z4,z5,z6,z906])],[(0,[z1,z3,z14,z143,z5,z6]),(0,[z140,z1,z14,z4,z88,z6]),(0,[z159,z3,z14,z4,z5,z6]),(0,[z25,z1,z3,z325,z5,z6]),(0,[z0,z1295,z3,z4,z5,z6]),(0,[z3,z4,z413,z5,z15,z6]),(0,[z1296,z1,z3,z4,z5,z6])],[(0,[z105,z1,z3,z4,z1297,z5]),(0,[z93,z1,z507,z4,z5,z6]),(0,[z25,z1,z3,z331,z5,z6]),(0,[z140,z18,z1,z4,z88,z6])],[(0,[z157,z3,z4,z5,z365,z6]),(0,[z65,z267,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z291]),(0,[z0,z1,z3,z4,z1298,z6]),(0,[z1299,z1,z3,z4,z5,z6]),(0,[z0,z1,z326,z22,z5,z6])]],
   [[(0,[z0,z1282,z3,z4,z5,z6]),(0,[z3,z4,z5,z6,z138,z183]),(0,[z0,z1,z3,z4,z677,z75]),(0,[z68,z0,z159,z4,z5,z47])],[(0,[z1,z3,z14,z4,z5,z235]),(0,[z1157,z0,z1,z3,z5,z6]),(0,[z0,z3,z4,z1300,z5,z6]),(0,[z0,z1,z3,z4,z5,z1301]),(0,[z42,z3,z4,z43,z56,z6])],[(0,[z105,z1302,z1,z3,z4,z5]),(0,[z18,z1,z3,z4,z5,z494]),(0,[z0,z176,z3,z4,z5,z508]),(0,[z1303,z1,z3,z4,z5,z6]),(0,[z428,z1,z3,z143,z5,z6]),(0,[z0,z1304,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z1305,z6])],[(0,[z105,z1,z122,z3,z4,z5]),(0,[z3,z14,z4,z839,z5,z6]),(0,[z521,z1,z14,z4,z5,z6]),(0,[z105,z41,z1,z3,z4,z5]),(0,[z151,z0,z3,z4,z162,z6]),(0,[z420,z1,z3,z4,z5,z235])],[],[(0,[z1,z3,z4,z5,z15,z569]),(0,[z0,z1,z893,z4,z5,z6]),(0,[z428,z210,z3,z4,z5,z6]),(0,[z429,z3,z4,z5,z6,z51])],[(0,[z1,z16,z14,z4,z5,z17]),(0,[z18,z1,z3,z4,z5,z211]),(0,[z0,z1,z691,z21,z5,z6])],[(0,[z0,z176,z3,z4,z5,z555]),(0,[z105,z25,z1,z3,z4,z5]),(0,[z273,z3,z14,z4,z5,z6]),(0,[z1,z3,z175,z4,z283,z6]),(0,[z61,z1,z3,z4,z5,z525]),(0,[z0,z873,z3,z4,z5,z6]),(0,[z18,z1,z3,z4,z5,z467])],[(0,[z1,z3,z4,z5,z1306,z6]),(0,[z0,z1,z3,z5,z6,z1307]),(0,[z246,z0,z1,z3,z5,z45])],[(0,[z0,z1,z3,z4,z5,z1308]),(0,[z0,z1,z3,z325,z5,z6]),(0,[z1,z3,z4,z1131,z5,z6])],[(0,[z1,z3,z375,z4,z5,z6]),(0,[z1254,z3,z14,z4,z5,z6]),(0,[z3,z4,z5,z15,z6,z994]),(0,[z0,z1,z3,z331,z5,z6]),(0,[z0,z1309,z3,z4,z5,z6])],[(0,[z0,z1,z3,z5,z1150,z6]),(0,[z18,z1,z3,z4,z5,z229]),(0,[z256,z196,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z1152]),(0,[z0,z1310,z3,z4,z5,z6])],[(0,[z0,z3,z4,z5,z6,z1311]),(0,[z1312,z3,z4,z5,z15,z6]),(0,[z1,z3,z4,z1313,z15,z6]),(0,[z0,z3,z4,z5,z324,z110]),(0,[z942,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z1314])],[(0,[z105,z1,z101,z3,z4,z5]),(0,[z140,z0,z1,z4,z88,z308])]],
   [[(0,[z584,z1,z14,z4,z5,z6]),(0,[z0,z1315,z3,z4,z5,z6]),(0,[z27,z18,z3,z185,z5,z6]),(0,[z0,z1,z3,z4,z5,z1316])],[(0,[z1,z1317,z3,z4,z5,z6]),(0,[z414,z1,z3,z4,z5,z211])],[(0,[z1318,z1,z3,z4,z5,z6]),(0,[z267,z3,z4,z5,z60,z6]),(0,[z1,z3,z4,z5,z6,z1319]),(0,[z1,z3,z4,z389,z15,z6]),(0,[z1,z3,z4,z5,z6,z1320]),(0,[z0,z1,z3,z4,z156,z527])],[(0,[z65,z38,z3,z4,z5,z6]),(0,[z0,z1,z3,z1321,z5,z6]),(0,[z25,z1,z3,z4,z389,z6]),(0,[z1322,z1,z3,z4,z5,z6]),(0,[z1323,z1,z3,z4,z5,z6])],[(0,[z25,z1,z370,z4,z5,z6]),(0,[z1324,z1,z3,z4,z5,z6]),(0,[z319,z3,z14,z4,z5,z6]),(0,[z25,z1325,z3,z4,z5,z6]),(0,[z18,z1,z326,z4,z5,z6])],[(0,[z1326,z1,z3,z4,z5,z6]),(0,[z166,z18,z3,z4,z5,z6]),(0,[z18,z1,z3,z331,z5,z6]),(0,[z1,z3,z4,z5,z1327,z6]),(0,[z0,z1,z3,z1328,z5,z6]),(0,[z1329,z1,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z1330,z6]),(0,[z281,z273,z3,z4,z5,z6]),(0,[z1331,z1,z3,z4,z5,z6]),(0,[z0,z1,z16,z4,z5,z775])],[(0,[z0,z1332,z3,z4,z5,z6]),(0,[z0,z1,z3,z7,z389,z6])],[(0,[z1,z3,z4,z5,z368,z6]),(0,[z106,z105,z1,z3,z4,z5]),(0,[z25,z3,z4,z5,z1252,z6]),(0,[z1,z3,z7,z5,z15,z6]),(0,[z1333,z1,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z1334,z6])],[(0,[z1,z3,z4,z5,z525,z47]),(0,[z25,z1,z3,z4,z5,z298]),(0,[z25,z319,z3,z4,z5,z6]),(0,[z0,z1335,z3,z4,z5,z6]),(0,[z18,z1,z3,z4,z5,z389]),(0,[z257,z1,z3,z7,z5,z6]),(0,[z195,z0,z1,z3,z98,z516])],[(0,[z0,z42,z3,z4,z251,z6]),(0,[z0,z1336,z3,z4,z5,z6])],[(0,[z18,z1,z3,z4,z5,z871]),(0,[z1,z3,z1337,z4,z5,z6])],[(0,[z68,z18,z1,z3,z7,z5])],[(0,[z176,z3,z14,z4,z5,z110]),(0,[z1,z3,z144,z5,z460,z6]),(0,[z18,z3,z4,z5,z357,z6]),(0,[z863,z3,z4,z5,z15,z6])],[(0,[z0,z1,z1338,z4,z5,z6]),(0,[z299,z0,z1,z4,z88,z6]),(0,[z0,z124,z3,z4,z5,z235])],[(0,[z343,z1,z3,z295,z5,z6]),(0,[z18,z1,z3,z4,z5,z288]),(0,[z267,z177,z3,z4,z5,z6]),(0,[z0,z152,z3,z498,z5,z6])],[(0,[z157,z3,z4,z5,z6,z138]),(0,[z105,z3,z13,z14,z4,z5]),(0,[z25,z1,z3,z4,z5,z308]),(0,[z1,z3,z4,z5,z1339,z6]),(0,[z0,z1,z3,z4,z389,z6])]],
   [[(0,[z0,z1,z3,z1340,z5,z6]),(0,[z130,z3,z14,z4,z5,z66]),(0,[z0,z1325,z3,z4,z5,z6]),(0,[z18,z1,z3,z4,z5,z301]),(0,[z1341,z1,z3,z4,z5,z6]),(0,[z0,z1342,z3,z4,z5,z6])],[(0,[z257,z1,z3,z4,z5,z6]),(0,[z105,z1,z3,z175,z4,z5]),(0,[z1343,z1,z3,z4,z5,z6]),(0,[z0,z3,z80,z5,z110,z6]),(0,[z68,z0,z196,z4,z5,z47]),(0,[z0,z3,z4,z5,z1344,z6])],[(0,[z3,z13,z4,z5,z15,z6]),(0,[z0,z1,z3,z4,z1345,z6]),(0,[z18,z1,z3,z4,z5,z238]),(0,[z451,z18,z1,z3,z4,z5]),(0,[z1,z3,z4,z5,z1346,z6]),(0,[z0,z1,z3,z4,z6,z1347]),(0,[z1348,z1,z3,z4,z5,z6])],[(0,[z1,z3,z175,z4,z26,z6]),(0,[z0,z1312,z3,z4,z5,z6]),(0,[z0,z273,z122,z21,z5,z6])],[(0,[z275,z3,z14,z4,z5,z6]),(0,[z41,z1,z3,z4,z26,z204]),(0,[z0,z319,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z298]),(0,[z1,z3,z4,z5,z1349,z6])],[(0,[z1,z3,z4,z5,z6,z138]),(0,[z0,z3,z1350,z4,z5,z6]),(0,[z18,z1,z3,z4,z5,z314]),(0,[z197,z0,z3,z4,z5,z6]),(0,[z0,z1,z3,z325,z5,z211]),(0,[z1169,z1,z3,z4,z5,z6])],[(0,[z1,z3,z1351,z4,z5,z6])],[(0,[z105,z105,z1,z3,z4,z5]),(0,[z0,z3,z4,z1352,z5,z6]),(0,[z1353,z0,z1,z3,z4,z6]),(0,[z0,z1,z487,z4,z5,z6]),(0,[z1,z3,z1354,z4,z5,z6])],[(0,[z18,z1,z458,z3,z4,z5]),(0,[z18,z1,z632,z3,z4,z5]),(0,[z0,z1,z3,z1355,z5,z6])],[(0,[z18,z1,z3,z4,z5,z379]),(0,[z54,z65,z3,z4,z5,z6]),(0,[z0,z1,z3,z1356,z5,z6])],[(0,[z65,z3,z4,z5,z250,z6]),(0,[z18,z3,z4,z5,z172,z6]),(0,[z0,z1357,z3,z4,z5,z6])],[(0,[z38,z897,z3,z4,z5,z6]),(0,[z25,z42,z3,z4,z43,z6]),(0,[z0,z1,z3,z4,z5,z308])],[(0,[z105,z38,z1,z3,z4,z5]),(0,[z1,z3,z112,z4,z5,z6]),(0,[z0,z1358,z3,z4,z5,z6])],[(0,[z25,z1,z3,z438,z5,z6]),(0,[z130,z0,z3,z4,z5,z377]),(0,[z0,z1359,z3,z4,z5,z6])],[(0,[z1,z78,z14,z4,z5,z6]),(0,[z184,z3,z4,z5,z6,z66]),(0,[z3,z4,z5,z330,z1158,z6]),(0,[z193,z429,z0,z3,z5,z45])],[(0,[z25,z1,z14,z4,z5,z6]),(0,[z260,z1,z3,z401,z5,z6]),(0,[z1,z3,z1360,z4,z5,z6]),(0,[z1,z199,z14,z4,z5,z6]),(0,[z0,z1361,z3,z4,z5,z6]),(0,[z131,z3,z154,z103,z5,z6]),(0,[z0,z3,z4,z5,z162,z298]),(0,[z0,z1,z3,z802,z5,z6]),(0,[z81,z124,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z1362,z6]),(0,[z0,z1363,z3,z4,z5,z6]),(0,[z0,z1,z3,z160,z4,z75])]],
   [[(0,[z1364,z1,z3,z4,z5,z6]),(0,[z1365,z1,z3,z4,z5,z6])],[(0,[z41,z1,z3,z4,z251,z6]),(0,[z195,z1,z3,z14,z98,z6]),(0,[z738,z0,z3,z4,z5,z6]),(0,[z469,z1,z3,z4,z60,z6]),(0,[z0,z3,z4,z5,z879,z6]),(0,[z0,z1,z3,z5,z6,z1366]),(0,[z1,z3,z4,z5,z1367,z6])],[(0,[z0,z3,z4,z1368,z5,z6]),(0,[z1,z3,z4,z5,z6,z1369])],[(0,[z1,z3,z14,z4,z156,z33]),(0,[z3,z4,z5,z15,z6,z183]),(0,[z1,z3,z4,z5,z15,z516]),(0,[z63,z1,z3,z4,z5,z33])],[(0,[z106,z1,z3,z4,z60,z6]),(0,[z1,z3,z4,z5,z1370,z6]),(0,[z1371,z1,z3,z4,z5,z6]),(0,[z501,z176,z3,z4,z5,z6]),(0,[z68,z257,z1,z4,z5,z47]),(0,[z808,z1,z3,z4,z5,z6])],[(0,[z267,z84,z3,z4,z5,z6]),(0,[z18,z1,z3,z4,z5,z525]),(0,[z0,z1,z1372,z4,z5,z6]),(0,[z40,z1,z3,z4,z843,z6]),(0,[z0,z42,z3,z4,z5,z298]),(0,[z140,z414,z1,z4,z88,z6])],[(0,[z0,z1,z3,z4,z5,z1373]),(0,[z85,z121,z161,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z775]),(0,[z195,z348,z1,z3,z98,z6])],[(0,[z105,z1,z3,z4,z5,z75]),(0,[z1,z3,z4,z5,z1374,z6]),(0,[z0,z42,z3,z4,z43,z6]),(0,[z1375,z1,z3,z4,z5,z6]),(0,[z1,z122,z139,z21,z5,z6]),(0,[z0,z381,z3,z4,z5,z235])],[(0,[z121,z1,z3,z4,z5,z6]),(0,[z157,z419,z3,z4,z5,z6]),(0,[z0,z176,z3,z4,z5,z666]),(0,[z0,z3,z4,z5,z6,z1376])],[(0,[z54,z3,z175,z4,z5,z6]),(0,[z1,z3,z1377,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z1378]),(0,[z106,z1,z3,z4,z221,z6]),(0,[z0,z1,z3,z4,z1313,z6]),(0,[z1,z3,z1379,z4,z5,z6]),(0,[z0,z42,z3,z4,z879,z6])],[(0,[z0,z1,z3,z4,z5,z1380]),(0,[z0,z1,z3,z4,z5,z1381]),(0,[z18,z1,z3,z4,z5,z377]),(0,[z369,z71,z79,z4,z5,z6]),(0,[z130,z0,z3,z4,z5,z409])],[(0,[z25,z13,z14,z4,z5,z6]),(0,[z1,z3,z14,z4,z5,z1382]),(0,[z25,z1,z39,z4,z5,z6]),(0,[z0,z71,z79,z80,z5,z6]),(0,[z0,z3,z4,z5,z6,z1383])],[(0,[z0,z897,z3,z4,z5,z6]),(0,[z1,z3,z4,z1384,z5,z6]),(0,[z267,z3,z4,z5,z6,z291]),(0,[z0,z3,z80,z185,z5,z6]),(0,[z282,z429,z3,z4,z5,z6])],[(0,[z0,z1385,z3,z4,z5,z6]),(0,[z27,z3,z185,z5,z15,z6]),(0,[z0,z1,z3,z4,z1386,z6])],[(0,[z131,z54,z3,z4,z5,z6]),(0,[z3,z759,z507,z4,z5,z6]),(0,[z1,z3,z4,z1387,z5,z6]),(0,[z0,z1,z3,z4,z5,z1024]),(0,[z0,z1388,z3,z4,z5,z6])]],
   [[(1,[z1,z3,z4,z5,z824]),(0,[z0,z319,z3,z4,z5,z211])],[(0,[z3,z14,z4,z5,z330,z6]),(0,[z1389,z1,z3,z4,z5,z6]),(0,[z3,z4,z5,z15,z6,z1075]),(0,[z193,z1,z3,z5,z15,z45]),(0,[z0,z378,z161,z4,z5,z6])],[(0,[z0,z1,z3,z4,z707,z6]),(0,[z131,z1,z3,z4,z5,z204]),(0,[z1,z3,z4,z5,z1390,z6]),(0,[z0,z1391,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1307])],[(0,[z105,z1,z3,z4,z185,z5]),(0,[z1,z3,z468,z14,z4,z5]),(0,[z105,z1,z3,z4,z283,z5]),(0,[z25,z1,z642,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1392]),(1,[z0,z1,z3,z1065,z6])],[(0,[z18,z1,z3,z438,z5,z6]),(0,[z811,z0,z3,z4,z5,z6])],[(0,[z131,z55,z3,z103,z5,z6]),(0,[z152,z3,z120,z5,z15,z6]),(0,[z429,z0,z3,z4,z5,z33])],[(0,[z210,z3,z4,z5,z15,z6]),(0,[z1393,z0,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z770])],[(0,[z157,z3,z375,z4,z5,z6]),(0,[z65,z337,z3,z4,z5,z6]),(0,[z1,z14,z4,z5,z6,z291]),(0,[z395,z105,z1,z3,z4,z5]),(0,[z25,z1,z654,z4,z5,z6]),(0,[z1394,z1,z3,z4,z5,z6]),(0,[z0,z152,z3,z1026,z5,z6]),(0,[z1395,z0,z3,z4,z5,z6])],[(0,[z0,z1,z720,z4,z5,z6]),(0,[z297,z3,z144,z4,z5,z6]),(0,[z1396,z1,z3,z4,z5,z6]),(0,[z1397,z1,z3,z4,z5,z6]),(0,[z176,z177,z3,z4,z5,z110]),(0,[z0,z273,z3,z44,z5,z6])],[(0,[z1,z3,z14,z4,z785,z6]),(0,[z0,z1398,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z1399,z6]),(0,[z81,z381,z3,z4,z5,z6]),(0,[z135,z1,z3,z4,z5,z75])],[(0,[z1,z3,z4,z5,z1400,z6]),(0,[z40,z1,z3,z4,z433,z6]),(0,[z1,z3,z4,z1401,z5,z6]),(0,[z429,z0,z3,z4,z5,z6]),(0,[z0,z1,z802,z44,z5,z6]),(0,[z0,z1,z3,z331,z389,z6])],[(0,[z54,z3,z144,z4,z5,z6]),(0,[z68,z18,z1,z16,z4,z5]),(0,[z3,z57,z4,z5,z15,z6]),(0,[z195,z1,z3,z98,z15,z6])],[(0,[z1275,z0,z1,z3,z4,z5]),(0,[z0,z727,z3,z4,z5,z6]),(0,[z18,z46,z3,z4,z5,z6]),(0,[z257,z1,z3,z331,z5,z6]),(0,[z0,z1402,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z1403]),(0,[z54,z3,z13,z4,z5,z6]),(0,[z105,z1,z3,z14,z4,z5]),(0,[z0,z1,z3,z4,z5,z1404]),(0,[z0,z732,z3,z4,z5,z6]),(0,[z55,z3,z4,z5,z60,z6]),(0,[z1,z122,z507,z4,z5,z6]),(0,[z18,z1,z3,z4,z1298,z6]),(0,[z1405,z1,z3,z4,z5,z6]),(0,[z1406,z1,z3,z4,z5,z6]),(0,[z0,z1407,z3,z4,z5,z6])],[(0,[z0,z1,z3,z1408,z5,z6]),(0,[z0,z146,z3,z4,z5,z75])],[(0,[z1,z3,z4,z5,z15,z704]),(0,[z197,z3,z14,z4,z5,z6]),(0,[z18,z3,z4,z1300,z5,z6]),(0,[z140,z0,z1,z143,z88,z6]),(0,[z81,z1,z3,z4,z5,z516])]],
   [[(0,[z0,z1,z3,z4,z5,z1256]),(0,[z68,z1,z4,z5,z6,z291]),(0,[z1,z3,z4,z5,z1409,z6]),(0,[z1410,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z862,z6])],[(0,[z1,z3,z1411,z4,z5,z6]),(0,[z884,z3,z507,z4,z5,z6]),(0,[z85,z0,z672,z4,z5,z6]),(0,[z27,z0,z3,z1026,z5,z6]),(0,[z0,z1,z4,z802,z5,z6])],[(0,[z1,z16,z3,z954,z4,z5]),(0,[z3,z4,z5,z6,z183,z291]),(0,[z3,z4,z5,z15,z6,z49])],[(0,[z157,z506,z3,z4,z5,z6]),(0,[z105,z130,z1,z3,z4,z5]),(0,[z0,z1,z4,z5,z862,z6]),(0,[z0,z1,z3,z1412,z5,z6])],[(0,[z1413,z1,z3,z4,z5,z6]),(0,[z105,z1,z3,z4,z5,z110]),(0,[z446,z0,z1,z3,z5,z45]),(0,[z0,z1,z3,z4,z88,z211])],[(0,[z1414,z1,z3,z4,z5,z6]),(0,[z0,z297,z3,z4,z5,z204]),(0,[z1415,z1,z3,z4,z5,z6])],[(0,[z105,z1,z3,z120,z4,z5]),(0,[z1,z3,z4,z5,z1416,z6]),(0,[z1417,z1,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z1418]),(0,[z134,z1,z3,z4,z74,z75])],[(0,[z40,z1,z3,z4,z533,z6]),(0,[z41,z1,z3,z4,z26,z322]),(0,[z18,z1,z3,z325,z5,z6]),(0,[z1,z3,z438,z5,z15,z6]),(0,[z1419,z1,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z110,z596])],[(0,[z54,z0,z3,z468,z4,z5]),(0,[z1420,z1,z3,z4,z5,z6]),(0,[z1421,z1,z3,z4,z5,z6]),(0,[z1422,z0,z3,z4,z5,z6])],[(0,[z1,z3,z14,z4,z5,z820]),(0,[z194,z1,z3,z4,z5,z6]),(0,[z1,z3,z4,z26,z277,z6]),(0,[z0,z1,z3,z4,z5,z1423])],[(0,[z0,z3,z759,z4,z5,z6]),(0,[z261,z1,z44,z5,z15,z6]),(0,[z1,z3,z4,z5,z869,z6]),(0,[z1424,z0,z3,z4,z5,z6])],[(0,[z131,z55,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z1425,z6]),(0,[z1,z1426,z3,z4,z5,z6]),(0,[z1145,z3,z91,z4,z5,z6]),(0,[z1,z326,z1411,z4,z5,z6]),(0,[z0,z1,z1427,z4,z5,z6])],[(0,[z1,z3,z14,z823,z4,z5]),(0,[z1,z3,z507,z4,z5,z33]),(0,[z1,z3,z1428,z4,z5,z6]),(0,[z135,z1,z3,z4,z156,z33])],[(0,[z105,z1,z3,z30,z4,z5]),(0,[z1429,z1,z3,z4,z5,z6]),(0,[z1430,z437,z3,z4,z5,z6]),(0,[z1431,z0,z3,z4,z5,z6])],[(0,[z25,z1,z487,z4,z5,z6]),(0,[z0,z1432,z3,z4,z5,z6]),(0,[z0,z1,z1433,z4,z5,z6])],[(0,[z105,z1,z3,z4,z26,z5]),(0,[z25,z1,z3,z143,z5,z6]),(0,[z0,z1434,z3,z4,z5,z6]),(0,[z1435,z3,z4,z5,z15,z6]),(0,[z845,z3,z4,z5,z15,z6]),(0,[z1436,z1,z3,z4,z5,z6])]],
   [[(0,[z59,z1,z3,z832,z5,z6]),(0,[z1,z3,z4,z5,z74,z322]),(0,[z193,z18,z1,z3,z5,z45]),(0,[z912,z1,z3,z91,z4,z5]),(0,[z197,z3,z4,z5,z432,z6])],[(0,[z1,z3,z507,z4,z5,z6]),(0,[z25,z196,z3,z4,z5,z6]),(0,[z381,z3,z4,z5,z15,z6]),(0,[z1,z3,z4,z5,z1437,z6]),(0,[z1438,z1,z3,z4,z5,z6]),(0,[z257,z1,z3,z4,z389,z6]),(0,[z1003,z3,z112,z4,z5,z6]),(0,[z0,z146,z3,z4,z156,z33])],[(0,[z1439,z1,z3,z4,z5,z6]),(0,[z0,z1435,z3,z4,z5,z6]),(0,[z414,z1,z3,z325,z5,z6]),(0,[z1,z3,z4,z5,z1440,z6]),(0,[z1,z3,z4,z5,z1129,z235])],[(0,[z105,z65,z1,z3,z4,z5])],[(0,[z1,z3,z375,z438,z5,z6]),(0,[z1,z1441,z3,z4,z5,z6]),(0,[z0,z196,z3,z7,z5,z6])],[(0,[z1,z3,z4,z5,z15,z6]),(0,[z1442,z1,z3,z4,z5,z6]),(0,[z344,z1,z3,z4,z6,z328]),(0,[z0,z1,z3,z4,z1443,z5]),(0,[z90,z0,z3,z4,z162,z6]),(0,[z0,z1444,z3,z4,z5,z6]),(0,[z0,z1445,z3,z4,z5,z6])],[(0,[z70,z105,z1,z3,z4,z5]),(0,[z105,z1,z16,z3,z4,z5]),(0,[z1,z3,z14,z4,z5,z837]),(0,[z1,z3,z4,z156,z529,z33])],[(0,[z105,z1,z3,z4,z5,z1446]),(0,[z0,z1,z3,z4,z5,z1382]),(0,[z1,z3,z1187,z91,z4,z5])],[(0,[z134,z18,z1,z3,z4,z75])],[(0,[z3,z14,z57,z4,z5,z6]),(0,[z54,z337,z3,z4,z5,z6]),(0,[z348,z3,z4,z5,z357,z6])],[(0,[z93,z1,z3,z4,z5,z33]),(0,[z0,z3,z120,z5,z6,z310]),(0,[z1,z3,z4,z5,z1447,z6]),(0,[z68,z0,z1,z331,z5,z47])],[(0,[z18,z1,z1338,z4,z5,z6]),(0,[z0,z1,z3,z143,z5,z6])],[(0,[z54,z25,z14,z4,z5,z6]),(0,[z1215,z0,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z879,z6]),(0,[z0,z1,z3,z4,z675,z33])],[(0,[z18,z1,z3,z4,z389,z6]),(0,[z0,z196,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z1448,z6]),(0,[z1,z3,z4,z5,z1449,z6])],[(0,[z1450,z1,z3,z4,z5,z6]),(0,[z1,z3,z4,z316,z60,z6]),(0,[z3,z4,z5,z15,z6,z167]),(0,[z1451,z1,z3,z4,z5,z6]),(0,[z1452,z1,z3,z4,z5,z6]),(0,[z1453,z1,z3,z4,z5,z6])],[(0,[z54,z0,z3,z4,z5,z6]),(0,[z93,z1,z3,z4,z5,z6]),(0,[z559,z571,z3,z4,z5,z6]),(0,[z25,z3,z4,z1454,z5,z6]),(0,[z85,z161,z4,z5,z15,z6]),(0,[z1,z3,z4,z1345,z15,z6]),(0,[z0,z1,z593,z44,z5,z6]),(0,[z0,z1,z3,z4,z5,z235])]],
   [[(0,[z0,z1,z1455,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z1456]),(0,[z629,z0,z1,z44,z5,z6]),(0,[z1457,z1,z3,z4,z5,z6]),(0,[z1458,z1,z3,z4,z5,z6])],[(0,[z543,z3,z13,z4,z5,z6]),(0,[z1459,z1,z3,z4,z5,z6])],[(0,[z169,z1,z14,z4,z5,z6]),(0,[z169,z105,z1,z3,z4,z5]),(0,[z105,z1,z3,z4,z5,z60]),(0,[z93,z1,z3,z4,z5,z113]),(0,[z470,z1,z3,z19,z5,z6]),(0,[z18,z1,z3,z4,z5,z298]),(0,[z18,z319,z3,z4,z5,z6]),(0,[z1460,z1,z3,z4,z5,z6]),(0,[z0,z1461,z3,z4,z5,z6]),(0,[z0,z1462,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z1463,z6])],[(0,[z407,z1,z3,z103,z5,z6]),(0,[z0,z3,z4,z5,z110,z635]),(0,[z1,z3,z1464,z4,z5,z6])],[(0,[z105,z1,z3,z4,z5,z31]),(0,[z429,z3,z14,z4,z5,z6]),(0,[z1465,z1,z3,z4,z5,z6]),(0,[z1,z3,z1466,z4,z5,z6]),(0,[z1395,z3,z4,z422,z5,z6])],[(0,[z105,z543,z1,z3,z4,z5]),(0,[z18,z1,z3,z4,z5,z452]),(0,[z18,z1,z3,z4,z5,z581]),(0,[z18,z1,z3,z954,z4,z5]),(0,[z18,z1,z487,z4,z5,z6]),(0,[z1,z3,z4,z5,z1467,z6]),(0,[z85,z184,z3,z4,z5,z6]),(0,[z1468,z1,z3,z4,z5,z6])],[(0,[z59,z1,z3,z144,z5,z6]),(1,[z68,z1,z507,z4,z5]),(0,[z1469,z1,z3,z4,z5,z6]),(0,[z734,z437,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z1470,z6]),(0,[z1,z3,z4,z5,z711,z6]),(0,[z63,z3,z4,z5,z6,z167])],[],[(0,[z1471,z0,z1,z3,z4,z5])],[(0,[z105,z1,z3,z4,z5,z162]),(0,[z18,z1,z3,z4,z5,z308]),(0,[z912,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z1472]),(0,[z348,z1,z3,z4,z5,z6]),(0,[z68,z18,z1,z4,z5,z47]),(0,[z61,z1,z3,z4,z5,z74]),(0,[z267,z3,z4,z5,z6,z328]),(0,[z71,z79,z375,z4,z5,z6]),(0,[z1473,z0,z3,z4,z5,z6]),(0,[z1474,z1,z3,z4,z5,z6])],[(0,[z63,z1,z3,z4,z5,z6]),(0,[z1,z3,z14,z4,z5,z204]),(0,[z0,z3,z4,z1454,z5,z6]),(0,[z1,z3,z331,z5,z15,z6]),(0,[z184,z3,z120,z4,z5,z6])],[(0,[z0,z1,z777,z4,z5,z6]),(0,[z3,z4,z5,z15,z6,z409]),(0,[z1475,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z1476,z5,z6]),(0,[z195,z0,z124,z3,z98,z6])],[(0,[z1,z3,z208,z103,z5,z6]),(0,[z0,z1,z3,z4,z5,z1477]),(0,[z1478,z0,z3,z4,z5,z6]),(0,[z18,z1,z3,z4,z5,z538]),(0,[z1,z101,z4,z171,z15,z6]),(0,[z0,z71,z3,z80,z5,z6]),(0,[z414,z319,z3,z4,z5,z6])],[(0,[z1479,z1,z3,z4,z5,z6])],[(0,[z169,z13,z14,z4,z5,z6]),(0,[z130,z0,z3,z4,z5,z1024]),(0,[z140,z428,z1,z4,z88,z6]),(0,[z68,z0,z1,z4,z389,z47])]],
   [[(0,[z3,z14,z4,z5,z932,z6]),(0,[z105,z1,z3,z4,z1480,z5]),(0,[z40,z105,z1,z3,z4,z5]),(0,[z25,z1398,z3,z4,z5,z6]),(0,[z25,z1,z647,z4,z5,z6]),(0,[z0,z3,z4,z5,z1481,z6]),(0,[z0,z3,z4,z305,z162,z6])],[(0,[z1,z3,z14,z22,z73,z6]),(0,[z136,z1,z3,z4,z455,z6]),(0,[z1482,z1,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z15,z211]),(0,[z1,z3,z4,z5,z1483,z6])],[(0,[z105,z1,z3,z4,z5,z47]),(0,[z25,z192,z3,z4,z5,z6]),(0,[z0,z42,z3,z4,z675,z6])],[(0,[z281,z1,z3,z4,z5,z6]),(0,[z105,z42,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z793]),(0,[z68,z18,z159,z3,z4,z5]),(0,[z1430,z0,z3,z4,z5,z6])],[(0,[z25,z3,z4,z5,z203,z6]),(0,[z0,z1,z3,z4,z5,z1484]),(0,[z1485,z1,z3,z4,z5,z6]),(0,[z414,z1,z3,z4,z5,z308])],[(0,[z1,z551,z14,z4,z5,z6]),(0,[z1,z442,z14,z4,z5,z6]),(0,[z25,z1,z122,z21,z5,z6]),(0,[z18,z42,z3,z4,z43,z6]),(0,[z0,z3,z120,z5,z393,z6]),(0,[z0,z1,z3,z5,z1307,z45])],[(0,[z3,z14,z4,z5,z1047,z6]),(0,[z41,z297,z3,z4,z26,z6])],[(0,[z0,z1,z3,z143,z5,z211])],[(0,[z25,z3,z4,z154,z5,z6]),(0,[z0,z297,z3,z4,z5,z322]),(0,[z1486,z1,z3,z4,z5,z6])],[(0,[z105,z1,z79,z3,z4,z5]),(0,[z18,z105,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z1487]),(0,[z0,z3,z4,z5,z1488,z6])],[(0,[z3,z14,z4,z5,z6,z183]),(0,[z332,z0,z3,z4,z162,z6]),(0,[z36,z1,z16,z4,z5,z17])],[(0,[z0,z1,z3,z4,z5,z1489]),(0,[z0,z1,z3,z1490,z5,z6]),(0,[z0,z1491,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z6,z1492]),(0,[z193,z0,z1,z3,z5,z1307])],[(0,[z402,z1,z3,z4,z5,z15]),(0,[z41,z1,z3,z4,z5,z204]),(0,[z18,z1385,z3,z4,z5,z6]),(0,[z501,z3,z4,z5,z6,z66]),(0,[z1,z3,z4,z5,z1493,z6]),(0,[z1,z3,z1494,z4,z5,z6])],[(0,[z0,z1,z3,z5,z1495,z6]),(0,[z195,z0,z1,z3,z98,z6]),(0,[z1496,z0,z3,z4,z5,z6])],[(0,[z0,z192,z3,z4,z5,z6]),(0,[z27,z0,z3,z626,z5,z6])],[(0,[z0,z3,z4,z351,z162,z6]),(0,[z90,z3,z14,z4,z162,z6]),(0,[z192,z3,z14,z4,z5,z6]),(0,[z105,z1,z3,z117,z4,z5]),(0,[z25,z1,z3,z4,z5,z731]),(0,[z18,z1,z3,z4,z5,z580]),(0,[z3,z139,z57,z4,z5,z6])]]]

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
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 491).take 494) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 985).take 487) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb3 : chunkB SB 1 ((bkA.flatten.flatten.drop 1472).take 8) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1480)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [491, 494, 487, 8] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_cons pb3 (windowsG_nil pbend))))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 114).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 114).take 112).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 226).take 94).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 320).take 114).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc4 : chunkOK 5 ((bkB.flatten.drop 434).take 78).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 512)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [114, 112, 94, 114, 78] = true :=
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

end PEqualNP.Outside.L_meta_36821

theorem PEqualNP.Outside.L_meta_36821 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276677352 * 2 ^ 32 + 4007717600) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276677352 * 2 ^ 32 + 4007717600) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_36821.solve