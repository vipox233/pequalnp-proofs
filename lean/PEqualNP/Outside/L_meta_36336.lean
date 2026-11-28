import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_36336

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
  Nat.testBit (4277075690 * 2 ^ 32 + 4277067968) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x08000845444c63c0#64 ++ 0x008000845444c63c#64 ++ 0xf41488cfc4dce7cd#64 ++ 0xdf41488cfc4dce7c#64 : BitVec 256),
   (0x90010b1305052850#64 ++ 0x090010b130505285#64 ++ 0xee2b0f33072738fb#64 ++ 0xbee2b0f33072738f#64 : BitVec 256),
   (0x204c302c183815a4#64 ++ 0xd204c302c183815a#64 ++ 0x5fcc703c38383fff#64 ++ 0xf5fcc703c38383ff#64 : BitVec 256),
   (0xc1b05dc02fc03e01#64 ++ 0x1c1b05dc02fc03e0#64 ++ 0x3df07fc03fc03f07#64 ++ 0x73df07fc03fc03f0#64 : BitVec 256),
   (0x00fe800032b28006#64 ++ 0x600fe800032b2800#64 ++ 0xffff80003fffc00f#64 ++ 0x0ffff80003fffc00#64 : BitVec 256),
   (0x00ffe6ba80000007#64 ++ 0x800ffe6ba8000000#64 ++ 0xfcffffffc0000000#64 ++ 0xffcffffffc000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.or, [0, 3]⟩, ⟨.or, [1, 3]⟩, ⟨.and, [2, 8]⟩, ⟨.and, [6, 9]⟩, ⟨.or, [10, 4]⟩, ⟨.or, [6, 9]⟩, ⟨.and, [7, 5]⟩, ⟨.or, [13, 11]⟩, ⟨.and, [12, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x00fe800032b28006 0x600fe800032b2800 0xffff80003fffc00f 0x0ffff80003fffc00

def z1 : W := mkw 0x00ffe6ba80000007 0x800ffe6ba8000000 0xfcffffffc0000000 0xffcffffffc000000

def z2 : W := mkw 0x08000845444c63c0 0x008000845444c63c 0xf41488cfc00027c0 0xdf41488cfc00027c

def z3 : W := mkw 0x08000845444c63c0 0x008000845444c63c 0xf41488cfc4dce7cd 0xdf41488cfc4dce7c

def z4 : W := mkw 0x204c302c183815a4 0xd204c302c183815a 0x5fcc703c38383fff 0xf5fcc703c38383ff

def z5 : W := mkw 0x90010b1305052850 0x090010b130505285 0xee2b0f33072738fb 0xbee2b0f33072738f

def z6 : W := mkw 0xc1b05dc02fc03e01 0x1c1b05dc02fc03e0 0x3df07fc03fc03f07 0x73df07fc03fc03f0

def z7 : W := mkw 0x90010b1305052850 0x090010b130505285 0x00000f33000038f0 0xb00000f33000038f

def z8 : W := mkw 0x0000000000000000 0x0000000000000000 0x2c200f0000000000 0x32c200f000000000

def z9 : W := mkw 0x90011b130d053c50 0x190011b130d053c5 0xffeb7f333f273fff 0xfffeb7f333f273ff

def z10 : W := mkw 0xe1fc75a83bb01c25 0xde1fc75a83bb01c2 0x0be877303b201832 0x20be877303b20183

def z11 : W := mkw 0x0000000032b28000 0x60000000032b2800 0x030000003fffc00f 0x0030000003fffc00

def z12 : W := mkw 0x000166ba80000001 0x8000166ba8000000 0x00007fffc0000000 0xf00007fffc000000

def z13 : W := mkw 0x90010b1305052850 0x090010b130505285 0x0a2b0f33032338f2 0xb0a2b0f33032338f

def z14 : W := mkw 0x0000000000000000 0x0000000000000000 0xee2b00000727000b 0x0ee2b00000727000

def z15 : W := mkw 0x90ff8b1337b7a856 0x690ff8b1337b7a85 0xffff8f333ffff8ff 0xbffff8f333ffff8f

def z16 : W := mkw 0x800019000d003c00 0x1800019000d003c0 0x3de07f003f003f07 0x73de07f003f003f0

def z17 : W := mkw 0xb04d3b3f1d3d3df4 0xdb04d3b3f1d3d3df 0xffef7f3f3f3f3fff 0xfffef7f3f3f3f3ff

def z18 : W := mkw 0x00b0000022800000 0x000b000002280000 0x3df000003fc00007 0x03df000003fc0000

def z19 : W := mkw 0x2000302c080815a0 0x92000302c080815a 0x0000703c00003ff0 0xf0000703c00003ff

def z20 : W := mkw 0xc1b04dc027c02a01 0x0c1b04dc027c02a0 0x20300fc007c00000 0x020300fc007c0000

def z21 : W := mkw 0x9001031201010810 0x0900103120101081 0x0a2b073003231832 0x20a2b07300323183

def z22 : W := mkw 0x20001004183815a0 0x520001004183815a 0x0100000038180704 0x0010000003818070

def z23 : W := mkw 0x00fe800000000006 0x000fe80000000000 0xfcff800000000000 0x0fcff80000000000

def z24 : W := mkw 0x0000000000000000 0x0000000000000000 0xf414800004dcc00d 0x0f414800004dcc00

def z25 : W := mkw 0x08000845444c63c0 0x008000845444c63c 0x000008cfc00027c0 0xd000008cfc00027c

def z26 : W := mkw 0x20feb02c3aba95a6 0xf20feb02c3aba95a 0xfffff03c3fffffff 0xffffff03c3ffffff

def z27 : W := mkw 0x284c386d5c7c77e4 0xd284c386d5c7c77e 0xffdcf8fffcfcffff 0xfffdcf8fffcfcfff

def z28 : W := mkw 0xc1fc7de82fc03e05 0x9c1fc7de82fc03e0 0x7dfc7ffc3fc03f07 0xf7dfc7ffc3fc03f0

def z29 : W := mkw 0x00b3c69280000003 0x000b3c6928000000 0xa0338fc3c0000000 0x0a0338fc3c000000

def z30 : W := mkw 0x20001004183815a0 0x520001004183815a 0x0300000038383fff 0x00300000038383ff

def z31 : W := mkw 0x204c302c183815a4 0xd204c302c183815a 0x5dcc703c38180704 0xf5dcc703c3818070

def z32 : W := mkw 0xc1b04dc027c02a01 0x0c1b04dc027c02a0 0x34300fc007c02705 0x534300fc007c0270

def z33 : W := mkw 0x004e800010328006 0x6004e80001032800 0xdfcf8000383fc00f 0x0dfcf8000383fc00

def z34 : W := mkw 0x204c302c183815a4 0xd204c302c183815a 0x11c4703c38183ff4 0xf11c4703c38183ff

def z35 : W := mkw 0x00fe800032b28006 0x600fe800032b2800 0xffff88cfffffc00f 0xdffff88cfffffc00

def z36 : W := mkw 0x08ffeeffc44c63c7 0x808ffeeffc44c63c 0xfcffffffc4dce7cd 0xffcffffffc4dce7c

def z37 : W := mkw 0x0001021200000000 0x0000102120000000 0x082b073000000000 0x2082b07300000000

def z38 : W := mkw 0x004c202800000004 0x8004c20280000000 0x5ccc703c00000000 0xf5ccc703c0000000

def z39 : W := mkw 0x20fff6be983815a7 0xd20fff6be983815a 0xfffffffff8383fff 0xffffffffff8383ff

def z40 : W := mkw 0x08000845444c63c0 0x008000845444c63c 0xe400080304dce7cd 0x9e400080304dce7c

def z41 : W := mkw 0x0000000000000000 0x0000000000000000 0x4e080030002038fb 0xb4e080030002038f

def z42 : W := mkw 0xc1b05dc02fc03e01 0x1c1b05dc02fc03e0 0x7ff87ff03fe03fff 0xf7ff87ff03fe03ff

def z43 : W := mkw 0x00ffe6bab2b28007 0xe00ffe6bab2b2800 0xffffffffffffc00f 0xfffffffffffffc00

def z44 : W := mkw 0x08fe884576fee3c6 0x608fe884576fee3c 0xffff88cfffffe7cf 0xdffff88cfffffe7c

def z45 : W := mkw 0x204c302c183815a4 0xd204c302c183815a 0xffef703c3f3f3fff 0xfffef703c3f3f3ff

def z46 : W := mkw 0x90010b1305052850 0x090010b130505285 0xa0230f0307070000 0x0a0230f030707000

def z47 : W := mkw 0x00ffe6ba90328007 0xe00ffe6ba9032800 0xfeffffffc03fc008 0xffeffffffc03fc00

def z48 : W := mkw 0x004c302808001404 0x9004c30280800140 0x5dcc703c38003f07 0xf5dcc703c38003f0

def z49 : W := mkw 0x0000080104042040 0x0000008010404204 0xe4000803040420c9 0x9e4000803040420c

def z50 : W := mkw 0x98010b57454d6bd0 0x098010b57454d6bd 0xfe3f8fffc7ffffff 0xffe3f8fffc7fffff

def z51 : W := mkw 0x00fe800032b28006 0x600fe800032b2800 0x5fdc800038f8c00f 0x05fdc800038f8c00

def z52 : W := mkw 0x0000448000000001 0x0000044800000000 0x00007fc000000000 0x700007fc00000000

def z53 : W := mkw 0x00ffe6bab2b28007 0xe00ffe6bab2b2800 0xfffffffffb230002 0xffffffffffb23000

def z54 : W := mkw 0x0000100008001400 0x1000010000800140 0x1dc0700038003f07 0x71dc0700038003f0

def z55 : W := mkw 0x00b0448000000001 0x000b044800000000 0x3cf07fc000000000 0x73cf07fc00000000

def z56 : W := mkw 0xd1b15f932f853c51 0x1d1b15f932f853c5 0xefeb7f333f2738fb 0xbefeb7f333f2738f

def z57 : W := mkw 0xc1b05dc02fc03e01 0x1c1b05dc02fc03e0 0x31f07fc03fc00704 0x431f07fc03fc0070

def z58 : W := mkw 0x080018454c4c77c0 0x1080018454c4c77c 0xfdd4f8cffcdcffcf 0xffdd4f8cffcdcffc

def z59 : W := mkw 0x20001004080815a0 0x120001004080815a 0x0000000000003ff0 0x00000000000003ff

def z60 : W := mkw 0x20feb02c3aba95a6 0xf20feb02c3aba95a 0xfffff00c3fffc70f 0x4fffff00c3fffc70

def z61 : W := mkw 0x204c302c080815a4 0x9204c302c080815a 0x5ccc703c00003ff0 0xf5ccc703c00003ff

def z62 : W := mkw 0x0001469280000001 0x0000146928000000 0x00000fc3c0000000 0x000000fc3c000000

def z63 : W := mkw 0x90016fbb85052851 0x890016fbb8505285 0xee2b7fffc72738fb 0xfee2b7fffc72738f

def z64 : W := mkw 0x004e800010328006 0x6004e80001032800 0x020b000000230000 0x0020b00000023000

def z65 : W := mkw 0x2000302c080815a0 0x92000302c080815a 0x4e08703c00203ffb 0xf4e08703c00203ff

def z66 : W := mkw 0x00ffe6bab2b28007 0xe00ffe6bab2b2800 0xfffff7303fffc00f 0x2fffff7303fffc00

def z67 : W := mkw 0x204c302818301424 0xd204c30281830142 0x01c0700038000000 0x001c070003800000

def z68 : W := mkw 0x204c202c103801a4 0xc204c202c103801a 0x420c003c003800f8 0x8420c003c003800f

def z69 : W := mkw 0xc10019400d403e00 0x1c10019400d403e0 0x0000000000003f00 0x00000000000003f0

def z70 : W := mkw 0xc1b17ffaafc03e01 0x9c1b17ffaafc03e0 0x3df07fffffc03f07 0xf3df07fffffc03f0

def z71 : W := mkw 0xd1fffffbafc53e57 0x9d1fffffbafc53e5 0xffffffffffe73fff 0xfffffffffffe73ff

def z72 : W := mkw 0x80010b1205002800 0x080010b120500280 0xec2b0f3307003803 0xbec2b0f330700380

def z73 : W := mkw 0x0000000000000000 0x0000000000000000 0xf41488cfc0000000 0xdf41488cfc000000

def z74 : W := mkw 0x00ffe6ba80000007 0x800ffe6ba8000000 0xfcffffffc4dcc00d 0xffcffffffc4dcc00

def z75 : W := mkw 0x00ffe6ba80000007 0x800ffe6ba8000000 0x08eb7fffc0000000 0xf08eb7fffc000000

def z76 : W := mkw 0x00fe800032b28006 0x600fe800032b2800 0xb1f780003fdfc004 0x0b1f780003fdfc00

def z77 : W := mkw 0x00ffe6ba80000007 0x800ffe6ba8000000 0xe03f8fffc0000000 0x8e03f8fffc000000

def z78 : W := mkw 0x004c000010300004 0x4004c00001030000 0x5fcc00003838000f 0x05fcc00003838000

def z79 : W := mkw 0x00b010002a801400 0x100b010002a80140 0x3df070003fc03f07 0x73df070003fc03f0

def z80 : W := mkw 0x004e800010328006 0x6004e80001032800 0xc20f8000003fc008 0x0c20f8000003fc00

def z81 : W := mkw 0x0800084144446240 0x0080008414444624 0xa01088c3c4c4c000 0x0a01088c3c4c4c00

def z82 : W := mkw 0x204c302818301424 0xd204c30281830142 0x0bc8703038201832 0x20bc870303820183

def z83 : W := mkw 0x204c302c183815a4 0xd204c302c183815a 0x11c4700c38180704 0x411c4700c3818070

def z84 : W := mkw 0x0000000000000000 0x0000000000000000 0xf414800000000000 0x0f41480000000000

def z85 : W := mkw 0x00fe800032b28006 0x600fe800032b2800 0x11d4800038d8c004 0x011d4800038d8c00

def z86 : W := mkw 0xc10019403ff2be00 0x7c10019403ff2be0 0x030000003fffff0f 0x0030000003fffff0

def z87 : W := mkw 0x0001021200000000 0x0000102120000000 0xee2b0f33002038fb 0xbee2b0f33002038f

def z88 : W := mkw 0xb0ffffbf9d3d3df7 0xdb0ffffbf9d3d3df 0xffffffffff3f3fff 0xfffffffffff3f3ff

def z89 : W := mkw 0x0000000400080180 0x0000000040008018 0x5404000c001827cd 0xd5404000c001827c

def z90 : W := mkw 0xc9b05dc56fcc7fc1 0x1c9b05dc56fcc7fc 0xfdf4ffcfffdcffcf 0xffdf4ffcfffdcffc

def z91 : W := mkw 0xd1b15fd32fc53e51 0x1d1b15fd32fc53e5 0xfffb7ff33fe73fff 0xffffb7ff33fe73ff

def z92 : W := mkw 0x0800084144446240 0x0080008414444624 0xb41088c3c4c4e705 0x5b41088c3c4c4e70

def z93 : W := mkw 0x004ea02880000006 0x8004ea0288000000 0x0004800cc0000000 0x00004800cc000000

def z94 : W := mkw 0x41b054c02ac01601 0x141b054c02ac0160 0x11d070c038c00704 0x411d070c038c0070

def z95 : W := mkw 0xc1b055802b801c01 0x1c1b055802b801c0 0x09e077003b001802 0x209e077003b00180

def z96 : W := mkw 0x00ffe6ba80000007 0x800ffe6ba8000000 0xfeffffffc02038fb 0xffeffffffc02038f

def z97 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000030000038f0 0xb00000030000038f

def z98 : W := mkw 0x00b166ba80000001 0x800b166ba8000000 0x3cf07fffc0000000 0xf3cf07fffc000000

def z99 : W := mkw 0x00b0548008001401 0x100b054800800140 0x3df07fc038003f07 0x73df07fc038003f0

def z100 : W := mkw 0x204c302c183815a4 0xd204c302c183815a 0x0bc8703038383fff 0x20bc8703038383ff

def z101 : W := mkw 0x00fe800022828006 0x200fe80002282800 0xfcff800007c7c000 0x0fcff800007c7c00

def z102 : W := mkw 0x204c302c183815a4 0xd204c302c183815a 0x13c4700c38383fff 0x413c4700c38383ff

def z103 : W := mkw 0x204c302818301424 0xd204c30281830142 0x1fc8703038203f37 0x71fc8703038203f3

def z104 : W := mkw 0x000064a880000001 0x8000064a88000000 0x000070ccc0000000 0x4000070ccc000000

def z105 : W := mkw 0x084c0845547c63c4 0x4084c0845547c63c 0xffdc88cffcfce7cf 0xdffdc88cffcfce7c

def z106 : W := mkw 0x00b3c69280000003 0x000b3c6928000000 0x0023070000000000 0x0002307000000000

def z107 : W := mkw 0x0000084004402200 0x0000008400440220 0x341008c004c02705 0x5341008c004c0270

def z108 : W := mkw 0x28fffeffdc7c77e7 0xd28fffeffdc7c77e 0xfffffffffcfcffff 0xffffffffffcfcfff

def z109 : W := mkw 0x08000845444c63c0 0x008000845444c63c 0xe01488cfc4dcc0c8 0x8e01488cfc4dcc0c

def z110 : W := mkw 0x90ffefbb85052857 0x890ffefbb8505285 0xfeffffffc72738fb 0xffeffffffc72738f

def z111 : W := mkw 0x284c386d5c7c77e4 0xd284c386d5c7c77e 0x5fcc78fff8383fff 0xf5fcc78fff8383ff

def z112 : W := mkw 0x204eb02c183a95a6 0xf204eb02c183a95a 0xdfcff03c383fffff 0xfdfcff03c383ffff

def z113 : W := mkw 0x08000845444c63c0 0x008000845444c63c 0x000008cfc4dce7cd 0xd000008cfc4dce7c

def z114 : W := mkw 0x90010b1305052850 0x090010b130505285 0xfe3f8f3307fff8ff 0xbfe3f8f3307fff8f

def z115 : W := mkw 0xc1005dc00d403e01 0x1c1005dc00d403e0 0x00007fc000003f00 0x700007fc000003f0

def z116 : W := mkw 0x20fff6be983815a7 0xd20fff6be983815a 0xfdfffffff8180704 0xffdfffffff818070

def z117 : W := mkw 0x00fe800032b28006 0x600fe800032b2800 0x0beb00003fffc00f 0x00beb00003fffc00

def z118 : W := mkw 0x0000080104042040 0x0000008010404204 0x00000000040420c9 0x000000000040420c

def z119 : W := mkw 0x00fe800032b28006 0x600fe800032b2800 0x0beb00003b230002 0x00beb00003b23000

def z120 : W := mkw 0x0000000000000000 0x0000000000000000 0xa01088c3c0000000 0x0a01088c3c000000

def z121 : W := mkw 0x90010b1305052850 0x090010b130505285 0xfe3f8fffc72738fb 0xffe3f8fffc72738f

def z122 : W := mkw 0x90ffe7ba81010817 0x890ffe7ba8101081 0xfeffffffc3231832 0xffeffffffc323183

def z123 : W := mkw 0x204c302c183815a4 0xd204c302c183815a 0xffdcf8fff8383fff 0xfffdcf8fff8383ff

def z124 : W := mkw 0x9000090105052850 0x0900009010505285 0x02000000072738fb 0x002000000072738f

def z125 : W := mkw 0x0000100008001400 0x1000010000800140 0x09c0700038001802 0x209c070003800180

def z126 : W := mkw 0x0000100008001400 0x1000010000800140 0x5fc8703038203fff 0xf5fc8703038203ff

def z127 : W := mkw 0x000166ba80000001 0x8000166ba8000000 0xf414ffffc0000000 0xff414ffffc000000

def z128 : W := mkw 0x00fee4a880000007 0x800fee4a88000000 0x10d4f0ccc0000000 0x410d4f0ccc000000

def z129 : W := mkw 0x1001021300050050 0x0100102130005005 0xc20b0033002700f8 0x8c20b0033002700f

def z130 : W := mkw 0xe1fc7dec3ff83fa5 0xde1fc7dec3ff83fa 0x7ffc7ffc3ff83fff 0xf7ffc7ffc3ff83ff

def z131 : W := mkw 0x0000000400080180 0x0000000040008018 0xf414800c04dce7cd 0xdf414800c04dce7c

def z132 : W := mkw 0x00b0000022800000 0x000b000002280000 0xfdf480003fdcc00f 0x0fdf480003fdcc00

def z133 : W := mkw 0x0001021200000000 0x0000102120000000 0x00000f3300000000 0xb00000f330000000

def z134 : W := mkw 0x2000302c080815a0 0x92000302c080815a 0x1dc0703c38003ff7 0xf1dc0703c38003ff

def z135 : W := mkw 0x00fe880136b6a046 0x600fe880136b6a04 0xffff88033fffe0cf 0x9ffff88033fffe0c

def z136 : W := mkw 0x00b0448000000001 0x000b044800000000 0xfcf4ffcfc0000000 0xffcf4ffcfc000000

def z137 : W := mkw 0x9000090105052850 0x0900009010505285 0x00000000000038f0 0x000000000000038f

def z138 : W := mkw 0xc1b019402fc03e00 0x1c1b019402fc03e0 0x3df000003fc03f07 0x03df000003fc03f0

def z139 : W := mkw 0x000166ba80000001 0x8000166ba8000000 0xec2b7fffc0000000 0xfec2b7fffc000000

def z140 : W := mkw 0xc1fed5803bb29c07 0x7c1fed5803bb29c0 0xfffff7003fffd80f 0x2fffff7003fffd80

def z141 : W := mkw 0x0000000000000000 0x0000000000000000 0xa023000007070000 0x0a02300000707000

def z142 : W := mkw 0x104f821310378056 0x6104f82131037805 0xc20f8033003fc0f8 0x8c20f8033003fc0f

def z143 : W := mkw 0x204c202c103801a4 0xc204c202c103801a 0x5fcc003c383800ff 0x85fcc003c383800f

def z144 : W := mkw 0xc1feddc03ff2be07 0x7c1feddc03ff2be0 0xffffffc03fffff0f 0x7ffffffc03fffff0

def z145 : W := mkw 0x90ffefbb85052857 0x890ffefbb8505285 0xfcffffffc00038f0 0xffcffffffc00038f

def z146 : W := mkw 0x0001021200000000 0x0000102120000000 0xec2b0f3300000000 0xbec2b0f330000000

def z147 : W := mkw 0x204c302c3aba95a4 0xf204c302c3aba95a 0x5fcc703c3fffffff 0xf5fcc703c3ffffff

def z148 : W := mkw 0x90ff8b1337b7a856 0x690ff8b1337b7a85 0xefeb0f333f2738fb 0xbefeb0f333f2738f

def z149 : W := mkw 0x00b0000022800000 0x000b000002280000 0x2030000007c00000 0x02030000007c0000

def z150 : W := mkw 0x9000090105052850 0x0900009010505285 0x4e080030072738fb 0xb4e080030072738f

def z151 : W := mkw 0x000018400c403600 0x1000018400c40360 0x3dd078c03cc03f07 0x73dd078c03cc03f0

def z152 : W := mkw 0x08000845444c63c0 0x008000845444c63c 0x0000000004dce7cd 0x00000000004dce7c

def z153 : W := mkw 0x0000000000000000 0x0000000000000000 0xf41488cfc4dcc00d 0xdf41488cfc4dcc00

def z154 : W := mkw 0x0000080104042040 0x0000008010404204 0xf414880304dce0cd 0x9f414880304dce0c

def z155 : W := mkw 0x08000005400c41c0 0x008000005400c41c 0x00000000001cc0c8 0x000000000001cc0c

def z156 : W := mkw 0x280018455c7c77e0 0x5280018455c7c77e 0xf71488cffcfcffff 0xdf71488cffcfcfff

def z157 : W := mkw 0x00ffe6be80080187 0x800ffe6be8008018 0xfcffffffc01827cd 0xffcffffffc01827c

def z158 : W := mkw 0x00b2800032b28002 0x600b2800032b2800 0xa33380003fffc00f 0x0a33380003fffc00

def z159 : W := mkw 0xd1b15fd32fc53e51 0x1d1b15fd32fc53e5 0xbdf37fc33fc73f07 0x7bdf37fc33fc73f0

def z160 : W := mkw 0xc1fecdc037f2aa07 0x6c1fecdc037f2aa0 0xffff8fc03fffc00f 0x0ffff8fc03fffc00

def z161 : W := mkw 0x90ffefbbb7b7a857 0xe90ffefbbb7b7a85 0xfffffffffffff8ff 0xffffffffffffff8f

def z162 : W := mkw 0xc9feddc57ffeffc7 0x7c9feddc57ffeffc 0xffffffcfffffffcf 0xfffffffcfffffffc

def z163 : W := mkw 0x004c000010300004 0x4004c00001030000 0x5fcc0030383838ff 0xb5fcc0030383838f

def z164 : W := mkw 0x90010b1305052850 0x090010b130505285 0x0a2b0730072738fb 0x20a2b0730072738f

def z165 : W := mkw 0x204c382d1c3c35e4 0xd204c382d1c3c35e 0xffcc783f3c3c3fff 0xfffcc783f3c3c3ff

def z166 : W := mkw 0xc1b05dc02fc03e01 0x1c1b05dc02fc03e0 0xfffb7fc03fe73f0f 0x7fffb7fc03fe73f0

def z167 : W := mkw 0xa04c392c1d383da4 0xda04c392c1d383da 0x7fec7f3c3f383fff 0xf7fec7f3c3f383ff

def z168 : W := mkw 0x00b2800022828002 0x200b280002282800 0xa033800007c7c000 0x0a033800007c7c00

def z169 : W := mkw 0x8000090005002800 0x0800009000500280 0x0000000007003803 0x0000000000700380

def z170 : W := mkw 0x08016effc44c63c1 0x808016effc44c63c 0xf414ffffc4dce7cd 0xff414ffffc4dce7c

def z171 : W := mkw 0x00ffe6ba80000007 0x800ffe6ba8000000 0xfeffffffc727000b 0xffeffffffc727000

def z172 : W := mkw 0x08fe884576fee3c6 0x608fe884576fee3c 0xffff80003fffe7cf 0x0ffff80003fffe7c

def z173 : W := mkw 0x9000090105052850 0x0900009010505285 0x2e200f00072738fb 0x32e200f00072738f

def z174 : W := mkw 0x004e800010328006 0x6004e80001032800 0x000480000018c000 0x0000480000018c00

def z175 : W := mkw 0x004c202800000004 0x8004c20280000000 0x10c4700c00000000 0x410c4700c0000000

def z176 : W := mkw 0x00fe800032b28006 0x600fe800032b2800 0xfdff800038d8c004 0x0fdff800038d8c00

def z177 : W := mkw 0x90b14f9305052851 0x090b14f930505285 0xfefb7ff3072738fb 0xffefb7ff3072738f

def z178 : W := mkw 0x98010b57454d6bd0 0x098010b57454d6bd 0x00000fffc0003ff0 0xf00000fffc0003ff

def z179 : W := mkw 0x08ffeefff6fee3c7 0xe08ffeefff6fee3c 0xffffffffffffe7cf 0xfffffffffffffe7c

def z180 : W := mkw 0xe1b05dc43ff83fa1 0x5e1b05dc43ff83fa 0x3ff07fc03ff83fff 0x73ff07fc03ff83ff

def z181 : W := mkw 0x00fff6ba88001407 0x900fff6ba8800140 0xfdfffffff8003f07 0xffdfffffff8003f0

def z182 : W := mkw 0x20fff6ba98301427 0xd20fff6ba9830142 0xfffffffff8201832 0xffffffffff820183

def z183 : W := mkw 0x90ff831233b38816 0x690ff831233b3881 0x0beb07303b231832 0x20beb07303b23183

def z184 : W := mkw 0x00fea02832b28006 0xe00fea02832b2800 0xfffff03c3fffc00f 0xffffff03c3fffc00

def z185 : W := mkw 0x0000000000000000 0x0000000000000000 0x02000000002038fb 0x002000000002038f

def z186 : W := mkw 0x00b3e6ba80000003 0x800b3e6ba8000000 0xa033ffffc0000000 0xfa033ffffc000000

def z187 : W := mkw 0x00ffa23a80000006 0x800ffa23a8000000 0xfcff803fc0000000 0x8fcff803fc000000

def z188 : W := mkw 0x90010b1305052850 0x090010b130505285 0xc20b0033072738fb 0x8c20b0033072738f

def z189 : W := mkw 0x0000000000000000 0x0000000000000000 0x1014800000d8c004 0x01014800000d8c00

def z190 : W := mkw 0x004d66ba80000005 0x8004d66ba8000000 0x5ccc7fffc0000000 0xf5ccc7fffc000000

def z191 : W := mkw 0x00ffe6baa2800007 0x800ffe6baa280000 0xfdffffffffc00007 0xffdffffffffc0000

def z192 : W := mkw 0x00fe800032b28006 0x600fe800032b2800 0xd3df800038ffc00c 0x0d3df800038ffc00

def z193 : W := mkw 0x61fc74ec3af817a5 0xd61fc74ec3af817a 0x5fdc70fc38f83fff 0xf5fdc70fc38f83ff

def z194 : W := mkw 0x204d76be983815a5 0xd204d76be983815a 0x5fcc7ffff8383fff 0xf5fcc7ffff8383ff

def z195 : W := mkw 0x410054c008401601 0x1410054c00840160 0x000070c000000700 0x4000070c00000070

def z196 : W := mkw 0x0000000000000000 0x0000000000000000 0x5404000c00000000 0xd5404000c0000000

def z197 : W := mkw 0x20fef4ac983815a7 0xd20fef4ac983815a 0x11d4f0ccf8180704 0x411d4f0ccf818070

def z198 : W := mkw 0x104fa23b80050056 0x8104fa23b8005005 0xc20f803fc02700f8 0x8c20f803fc02700f

def z199 : W := mkw 0x49b054c46ac85781 0x149b054c46ac8578 0x11d4f0ccf8d8c704 0x411d4f0ccf8d8c70

def z200 : W := mkw 0xd1b14fd327c52a51 0x0d1b14fd327c52a5 0xa0330fc307c70000 0x0a0330fc307c7000

def z201 : W := mkw 0x90010b1305052850 0x090010b130505285 0x4e080f33002038fb 0xb4e080f33002038f

def z202 : W := mkw 0x004c000010300004 0x4004c00001030000 0xffef00003f3f000f 0x0ffef00003f3f000

def z203 : W := mkw 0x08000045404c43c0 0x008000045404c43c 0xd01480cfc0dcc7cc 0xcd01480cfc0dcc7c

def z204 : W := mkw 0x8000090005002800 0x0800009000500280 0x2c200f0007003803 0x32c200f000700380

def z205 : W := mkw 0x00b0000022800000 0x000b000002280000 0x09e000003b000002 0x009e000003b00000

def z206 : W := mkw 0x0000000400080180 0x0000000040008018 0x0000000c000027c0 0xd0000000c000027c

def z207 : W := mkw 0x0000000000000000 0x0000000000000000 0xc004800fc0000000 0x8c004800fc000000

def z208 : W := mkw 0x2000302c183815a0 0xd2000302c183815a 0x0300703c38383fff 0xf0300703c38383ff

def z209 : W := mkw 0x08ffeeffc44c63c7 0x808ffeeffc44c63c 0xfcffffffc00027c0 0xffcffffffc00027c

def z210 : W := mkw 0x8000090005002800 0x0800009000500280 0xee2b0f000727380b 0x3ee2b0f000727380

def z211 : W := mkw 0x90016fbb85052851 0x890016fbb8505285 0x00007fffc00038f0 0xf00007fffc00038f

def z212 : W := mkw 0x08000005400c41c0 0x008000005400c41c 0xf41488cfc01cc0c8 0xdf41488cfc01cc0c

def z213 : W := mkw 0x204c302c183815a4 0xd204c302c183815a 0x55c4700c381827cd 0xd55c4700c381827c

def z214 : W := mkw 0x004c202800000004 0x8004c20280000000 0x08c8703000000000 0x208c870300000000

def z215 : W := mkw 0x00fc000032b00004 0x400fc000032b0000 0x7ffc00003ff8000f 0x07ffc00003ff8000

def z216 : W := mkw 0x8000090005002800 0x0800009000500280 0x6e280f30072038fb 0xb6e280f30072038f

def z217 : W := mkw 0x084e8005503ec1c6 0x6084e8005503ec1c 0xc20f800fc03fc0c8 0x8c20f800fc03fc0c

def z218 : W := mkw 0x90010b1305052850 0x090010b130505285 0xa2230f03072738fb 0x0a2230f03072738f

def z219 : W := mkw 0x000166ba80000001 0x8000166ba8000000 0x0000773000000000 0x2000077300000000

def z220 : W := mkw 0x0000000000000000 0x0000000000000000 0x2c20000007000003 0x02c2000000700000

def z221 : W := mkw 0xc1fff7baab801c07 0x9c1fff7baab801c0 0x09eb77303b001802 0x209eb77303b00180

def z222 : W := mkw 0xb84d3b7f5d7d7ff4 0xdb84d3b7f5d7d7ff 0xffffffffffffffff 0xffffffffffffffff

def z223 : W := mkw 0x8000090005002800 0x0800009000500280 0x00000f0000003800 0x300000f000000380

def z224 : W := mkw 0x00ffe6ba80000007 0x800ffe6ba8000000 0x18fff7fcc0000000 0x618fff7fcc000000

def z225 : W := mkw 0xd10019412fc53e50 0x1d10019412fc53e5 0x030000003fe73fff 0x0030000003fe73ff

def z226 : W := mkw 0x0000000000000000 0x0000000000000000 0x000008cfc0000000 0xd000008cfc000000

def z227 : W := mkw 0xc90019456fcc7fc0 0x1c90019456fcc7fc 0xf51488cfffdcffcf 0xdf51488cfffdcffc

def z228 : W := mkw 0x9001031201010810 0x0900103120101081 0x4e2b0730032338fb 0xb4e2b0730032338f

def z229 : W := mkw 0x00fee4a880000007 0x800fee4a88000000 0xf4d4f8cfc0000000 0xdf4d4f8cfc000000

def z230 : W := mkw 0x304d223f103d01f4 0xc304d223f103d01f 0xc20f003f003f00f8 0x8c20f003f003f00f

def z231 : W := mkw 0x00fe800000000006 0x000fe80000000000 0xfcff800004dcc00d 0x0fcff800004dcc00

def z232 : W := mkw 0x00fee4a8b2b28007 0xe00fee4a8b2b2800 0xfffff0ccffffc00f 0x4fffff0ccffffc00

def z233 : W := mkw 0x98000945454d6bd0 0x098000945454d6bd 0xf61488cfc7ffffff 0xdf61488cfc7fffff

def z234 : W := mkw 0x00b0084026c02200 0x000b0084026c0220 0x3df008c03fc02707 0x53df008c03fc0270

def z235 : W := mkw 0x9001031201010810 0x0900103120101081 0xee2b07300727183b 0x2ee2b07300727183

def z236 : W := mkw 0x08000005400c41c0 0x008000005400c41c 0x0000000fc00000c0 0x80000000fc00000c

def z237 : W := mkw 0x0000000000000000 0x0000000000000000 0x4c08003000000000 0xb4c0800300000000

def z238 : W := mkw 0x0000084004402200 0x0000008400440220 0xf41488cfc4c02705 0xdf41488cfc4c0270

def z239 : W := mkw 0x8000094005402a00 0x08000094005402a0 0x3c300fc007c03f07 0x73c300fc007c03f0

def z240 : W := mkw 0x1001021300050050 0x0100102130005005 0xce0b0033002738fb 0xbce0b0033002738f

def z241 : W := mkw 0x0800004440484380 0x0080000444048438 0xf41488cfc0d8c704 0xdf41488cfc0d8c70

def z242 : W := mkw 0x00fe800022800006 0x000fe80002280000 0xfdff80003fc00007 0x0fdff80003fc0000

def z243 : W := mkw 0x0000080104042040 0x0000008010404204 0xa000080304040000 0x0a00008030404000

def z244 : W := mkw 0x8000090105042840 0x0800009010504284 0xec200f03070438cb 0xbec200f03070438c

def z245 : W := mkw 0x00b3c692a2828003 0x200b3c692a282800 0xa0338fc3c7c7c000 0x0a0338fc3c7c7c00

def z246 : W := mkw 0x410010402ac01600 0x1410010402ac0160 0x0100000038c00704 0x00100000038c0070

def z247 : W := mkw 0x08000005400c41c0 0x008000005400c41c 0xc004800fc01cc0c8 0x8c004800fc01cc0c

def z248 : W := mkw 0x00b0000022800000 0x000b000002280000 0xfffb00003fe7000f 0x0fffb00003fe7000

def z249 : W := mkw 0x0800084144446240 0x0080008414444624 0xe41088c3c4c4e0c9 0x9e41088c3c4c4e0c

def z250 : W := mkw 0x90ff8b1305052856 0x090ff8b130505285 0xfeff8f33072738fb 0xbfeff8f33072738f

def z251 : W := mkw 0x9001031201010810 0x0900103120101081 0x0000073000001830 0x2000007300000183

def z252 : W := mkw 0xf1fd7fff3ffd3ff5 0xdf1fd7fff3ffd3ff 0xffff7fff3fff3fff 0xfffff7fff3fff3ff

def z253 : W := mkw 0x08000845444c63c0 0x008000845444c63c 0xf414800004dce7cd 0x0f414800004dce7c

def z254 : W := mkw 0x904d0b1315352854 0x4904d0b131535285 0xffef0f333f3f38ff 0xbffef0f333f3f38f

def z255 : W := mkw 0x0000000000000000 0x0000000000000000 0xc20b000000270008 0x0c20b00000027000

def z256 : W := mkw 0x00fee4a8b2b28007 0xe00fee4a8b2b2800 0x11d4f0ccf8d8c004 0x411d4f0ccf8d8c00

def z257 : W := mkw 0x204c1004183815a4 0x5204c1004183815a 0x5fcc000038383fff 0x05fcc000038383ff

def z258 : W := mkw 0x0800004440484380 0x0080000444048438 0xf41480ccc4dcc70d 0x4f41480ccc4dcc70

def z259 : W := mkw 0x90010b1305052850 0x090010b130505285 0xc20b0f33002738f8 0xbc20b0f33002738f

def z260 : W := mkw 0x204c302c183815a4 0xd204c302c183815a 0x430c003c38383fff 0x8430c003c38383ff

def z261 : W := mkw 0x0000000400080180 0x0000000040008018 0x1004000c00180704 0x41004000c0018070

def z262 : W := mkw 0xc9005dc54d4c7fc1 0x1c9005dc54d4c7fc 0x00007fcfc0003fc0 0xf00007fcfc0003fc

def z263 : W := mkw 0x08000805440c61c0 0x008000805440c61c 0xe404880fc41ce0c9 0x9e404880fc41ce0c

def z264 : W := mkw 0x20fe90043aba95a6 0x720fe90043aba95a 0xffff80003fffffff 0x0ffff80003ffffff

def z265 : W := mkw 0x0000000032b28000 0x60000000032b2800 0xef2b00003fffc00f 0x0ef2b00003fffc00

def z266 : W := mkw 0x204c302c183815a4 0xd204c302c183815a 0x1dc4700c38183f07 0x71dc4700c38183f0

def z267 : W := mkw 0xc9b05dc56fcc7fc1 0x1c9b05dc56fcc7fc 0x3df07fcfffc03fc7 0xf3df07fcfffc03fc

def z268 : W := mkw 0x004e800032b28006 0x6004e800032b2800 0xc30f80003fffc00f 0x0c30f80003fffc00

def z269 : W := mkw 0xc1b2ddc02fc2be03 0x3c1b2ddc02fc2be0 0xbdf3ffc03fc7ff07 0x7bdf3ffc03fc7ff0

def z270 : W := mkw 0x9000090105052850 0x0900009010505285 0xe6000803072738fb 0x9e6000803072738f

def z271 : W := mkw 0x204c386c1c7837a4 0xd204c386c1c7837a 0x7fdc78fc3cf83fff 0xf7fdc78fc3cf83ff

def z272 : W := mkw 0x08b0084566cc63c0 0x008b0084566cc63c 0xfdf488cfffdce7cf 0xdfdf488cfffdce7c

def z273 : W := mkw 0x304d323f183d15f4 0xd304d323f183d15f 0xdfcf703f383f3fff 0xfdfcf703f383f3ff

def z274 : W := mkw 0x90ffefbb85052857 0x890ffefbb8505285 0xeeeb7f33072738fb 0xbeeeb7f33072738f

def z275 : W := mkw 0x90b3cf9385052853 0x090b3cf938505285 0xa0338fc3c7070000 0x0a0338fc3c707000

def z276 : W := mkw 0x004c000410380184 0x4004c00041038018 0x5fcc000c383827cf 0xd5fcc000c383827c

def z277 : W := mkw 0xc10019402fc03e00 0x1c10019402fc03e0 0x010000003fc03f07 0x0010000003fc03f0

def z278 : W := mkw 0x0000004000400200 0x0000000400040020 0x101000c000c00704 0x4101000c000c0070

def z279 : W := mkw 0xc1b055802b801c01 0x1c1b055802b801c0 0x1de077003b003f07 0x71de077003b003f0

def z280 : W := mkw 0xc1fffffabff2be07 0xfc1fffffabff2be0 0xffffffffffffff0f 0xfffffffffffffff0

def z281 : W := mkw 0x08b2884166c6e242 0x208b2884166c6e24 0xa03388c3c7c7c000 0x0a03388c3c7c7c00

def z282 : W := mkw 0x00ffe6ba80000007 0x800ffe6ba8000000 0x10d4ffffc0000000 0xf10d4ffffc000000

def z283 : W := mkw 0xc1feddc02fc03e07 0x1c1feddc02fc03e0 0xfdffffc03fc03f07 0x7fdffffc03fc03f0

def z284 : W := mkw 0x00fe800010328006 0x600fe80001032800 0xfeff8000003fc008 0x0feff8000003fc00

def z285 : W := mkw 0x284c302d583c55e4 0xd284c302d583c55e 0xdfccf03ff83cffff 0xfdfccf03ff83cfff

def z286 : W := mkw 0xc1fffffaafc03e07 0x9c1fffffaafc03e0 0xfdffffffffc03f07 0xffdffffffffc03f0

def z287 : W := mkw 0x08000845444c63c0 0x008000845444c63c 0x101488cfc0d8e7c4 0xd101488cfc0d8e7c

def z288 : W := mkw 0x0000000000000000 0x0000000000000000 0x1cc0700000000000 0x71cc070000000000

def z289 : W := mkw 0x004fa23a80000006 0x8004fa23a8000000 0xc00f803fc0000000 0x8c00f803fc000000

def z290 : W := mkw 0xe14c396c3ff83fa4 0xde14c396c3ff83fa 0x5fcc703c3ff83fff 0xf5fcc703c3ff83ff

def z291 : W := mkw 0xc1b0458023800801 0x0c1b045802380080 0x0020070003000000 0x0002007000300000

def z292 : W := mkw 0x08000845444c63c0 0x008000845444c63c 0x00000000000027c0 0x000000000000027c

def z293 : W := mkw 0x2000302808001420 0x9200030280800142 0x0000703000001830 0x2000070300000183

def z294 : W := mkw 0x00fe800032b28006 0x600fe800032b2800 0xffff80003b230002 0x0ffff80003b23000

def z295 : W := mkw 0x00ffe6bab2b28007 0xe00ffe6bab2b2800 0xfdfffffff8d8c004 0xffdfffffff8d8c00

def z296 : W := mkw 0xc1005dc00d403e01 0x1c1005dc00d403e0 0x2c207fc007003f03 0x72c207fc007003f0

def z297 : W := mkw 0x41b054c02ac01601 0x141b054c02ac0160 0x3df07fc038c00704 0x73df07fc038c0070

def z298 : W := mkw 0x00ffeebb84042047 0x800ffeebb8404204 0xfcffffffc40420c9 0xffcffffffc40420c

def z299 : W := mkw 0x08000845444c63c0 0x008000845444c63c 0xfe3f88cfc7ffe7cf 0xdfe3f88cfc7ffe7c

def z300 : W := mkw 0x0001021200000000 0x0000102120000000 0xfc3f8fffc0000000 0xffc3f8fffc000000

def z301 : W := mkw 0x00fee4a880000007 0x800fee4a88000000 0x5cdcf0fcc0000000 0xf5cdcf0fcc000000

def z302 : W := mkw 0x9000090105052850 0x0900009010505285 0xee2b0000072738fb 0x0ee2b0000072738f

def z303 : W := mkw 0x904f8b131537a856 0x6904f8b131537a85 0xee2f8f33073ff8fb 0xbee2f8f33073ff8f

def z304 : W := mkw 0xc1b04dc027c02a01 0x0c1b04dc027c02a0 0x3cf07fc007c00000 0x73cf07fc007c0000

def z305 : W := mkw 0x08000845444c63c0 0x008000845444c63c 0x101480ccc4dce7cd 0x4101480ccc4dce7c

def z306 : W := mkw 0x00fe800000000006 0x000fe80000000000 0x08eb000000000000 0x008eb00000000000

def z307 : W := mkw 0xc1b3dfd2afc03e03 0x1c1b3dfd2afc03e0 0xbdf3ffc3ffc03f07 0x7bdf3ffc3ffc03f0

def z308 : W := mkw 0x00fec48032b28007 0x600fec48032b2800 0xffffffc03fffc00f 0x7ffffffc03fffc00

def z309 : W := mkw 0x08ffe6bfc00c41c7 0x808ffe6bfc00c41c 0xfcffffffc01cc0c8 0xffcffffffc01cc0c

def z310 : W := mkw 0x0000100008001400 0x1000010000800140 0x0000700000003f00 0x70000700000003f0

def z311 : W := mkw 0x90ffe7ba81010817 0x890ffe7ba8101081 0x0aeb773003231832 0x20aeb77300323183

def z312 : W := mkw 0x41b044c022c00201 0x041b044c022c0020 0x001000c000c00000 0x0001000c000c0000

def z313 : W := mkw 0xc1b05dc02fc03e01 0x1c1b05dc02fc03e0 0x20307fc007c03f00 0x720307fc007c03f0

def z314 : W := mkw 0xb0011b171d3d3df0 0x5b0011b171d3d3df 0xef2b0f333f3f3fff 0xbef2b0f333f3f3ff

def z315 : W := mkw 0x0000000010300000 0x4000000001030000 0x030000003838000f 0x0030000003838000

def z316 : W := mkw 0x20feb02c3aba95a6 0xf20feb02c3aba95a 0x5fdcf03c38f8ffff 0xf5fdcf03c38f8fff

def z317 : W := mkw 0xc1fffffa8d403e07 0x9c1fffffa8d403e0 0xfcffffffc0003f00 0xffcffffffc0003f0

def z318 : W := mkw 0x98010b5345456a50 0x098010b5345456a5 0xee3b8ff3c7e7f8fb 0xbee3b8ff3c7e7f8f

def z319 : W := mkw 0xc1b05dc02fc03e01 0x1c1b05dc02fc03e0 0xfdf4ffcfffc03f07 0xffdf4ffcfffc03f0

def z320 : W := mkw 0x00ffe6ba80000007 0x800ffe6ba8000000 0x08eb773000000000 0x208eb77300000000

def z321 : W := mkw 0xc1fefde8afc03e07 0x9c1fefde8afc03e0 0x3df4ffccffc03f07 0x73df4ffccffc03f0

def z322 : W := mkw 0xd1b14fd327c52a51 0x0d1b14fd327c52a5 0xee3b0ff307e738fb 0xbee3b0ff307e738f

def z323 : W := mkw 0x20001004183815a0 0x520001004183815a 0x5704000c38383fff 0xd5704000c38383ff

def z324 : W := mkw 0xc9b05dc16fc47e41 0x1c9b05dc16fc47e4 0xbdf0ffc3ffc4ff07 0x7bdf0ffc3ffc4ff0

def z325 : W := mkw 0x204c202810300024 0xc204c20281030002 0x0208003000200030 0x0020800300020003

def z326 : W := mkw 0x0000000000000000 0x0000000000000000 0x4e0800000020000b 0x04e0800000020000

def z327 : W := mkw 0x90b10b1327852850 0x090b10b132785285 0xfffb0f333fe738ff 0xbfffb0f333fe738f

def z328 : W := mkw 0x08000845444c63c0 0x008000845444c63c 0x5404000c04dce7cd 0xd5404000c04dce7c

def z329 : W := mkw 0x204d323e183815a4 0xd204d323e183815a 0xffef7f3f38383fff 0xfffef7f3f38383ff

def z330 : W := mkw 0x0800004440484380 0x0080000444048438 0x101480ccc0d8c704 0x4101480ccc0d8c70

def z331 : W := mkw 0xc90019456fcc7fc0 0x1c90019456fcc7fc 0x010000003fdcffcf 0x0010000003fdcffc

def z332 : W := mkw 0x0800084576fee3c0 0x60800084576fee3c 0xf71488cfffffe7cf 0xdf71488cfffffe7c

def z333 : W := mkw 0x00fe800000000006 0x000fe80000000000 0xfeff80000727000b 0x0feff80000727000

def z334 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z335 : W := mkw 0xc10019402fc03e00 0x1c10019402fc03e0 0x1dc070003fc03f07 0x71dc070003fc03f0

def z336 : W := mkw 0x00b3c69280000003 0x000b3c6928000000 0xf4378fcfc0000000 0xdf4378fcfc000000

def z337 : W := mkw 0x200010043aba95a0 0x7200010043aba95a 0x030000003fffffff 0x0030000003ffffff

def z338 : W := mkw 0x00ffe6baa2828007 0xa00ffe6baa282800 0xfcffffffc7c7c000 0xffcffffffc7c7c00

def z339 : W := mkw 0x90010b1305052850 0x090010b130505285 0xec2b0f33000038f0 0xbec2b0f33000038f

def z340 : W := mkw 0x90fe890137b7a856 0x690fe890137b7a85 0xffff80003ffff8ff 0x0ffff80003ffff8f

def z341 : W := mkw 0xb04d2b3f153d29f4 0xcb04d2b3f153d29f 0xee2f0f3f073f38fb 0xbee2f0f3f073f38f

def z342 : W := mkw 0xe1fefdec3ffabfa7 0xfe1fefdec3ffabfa 0xfffffffc3fffffff 0xffffffffc3ffffff

def z343 : W := mkw 0x41fed4c03af29607 0x741fed4c03af2960 0xfffff0c03fffc70f 0x4fffff0c03fffc70

def z344 : W := mkw 0x0000000000000000 0x0000000000000000 0xc0048000001cc008 0x0c0048000001cc00

def z345 : W := mkw 0x0000080104042040 0x0000008010404204 0xf41488cfc40420c9 0xdf41488cfc40420c

def z346 : W := mkw 0x00b2800000000002 0x000b280000000000 0xa033800000000000 0x0a03380000000000

def z347 : W := mkw 0x00fe800032b28006 0x600fe800032b2800 0xf5d480003cdcc00d 0x0f5d480003cdcc00

def z348 : W := mkw 0xc1b05dc02fc03e01 0x1c1b05dc02fc03e0 0x11d07fc038c03f04 0x711d07fc038c03f0

def z349 : W := mkw 0x90010b5305452a50 0x090010b5305452a5 0xfe3b0ff307e73fff 0xffe3b0ff307e73ff

def z350 : W := mkw 0x41fed4c03af29607 0x741fed4c03af2960 0x11d4f0c038d8c704 0x411d4f0c038d8c70

def z351 : W := mkw 0x20001004183815a0 0x520001004183815a 0x4f08003038383fff 0xb4f08003038383ff

def z352 : W := mkw 0x00ffe6ba80000007 0x800ffe6ba8000000 0xb0f7ffcfc0000000 0x4b0f7ffcfc000000

def z353 : W := mkw 0x0000202800000000 0x8000020280000000 0x0000703c00000000 0xf0000703c0000000

def z354 : W := mkw 0x0000000000000000 0x0000000000000000 0xa010800004c4c000 0x0a010800004c4c00

def z355 : W := mkw 0xc1fe99403ff2be06 0x7c1fe99403ff2be0 0xffff80003fffff0f 0x0ffff80003fffff0

def z356 : W := mkw 0x00b3c69280000003 0x000b3c6928000000 0xec3b8ff3c0000000 0xbec3b8ff3c000000

def z357 : W := mkw 0x80fe890037b2a806 0x680fe890037b2a80 0xffff8f003ffff80f 0x3ffff8f003ffff80

def z358 : W := mkw 0x0800084144446240 0x0080008414444624 0xf41488cfc4c4c000 0xdf41488cfc4c4c00

def z359 : W := mkw 0xc1b05dc42fc83f81 0x1c1b05dc42fc83f8 0x7df47fcc3fd83fcf 0xf7df47fcc3fd83fc

def z360 : W := mkw 0x20fea02c32ba81a6 0xe20fea02c32ba81a 0xffff803c3fffc0ff 0x8ffff803c3fffc0f

def z361 : W := mkw 0x0001223a80000000 0x80001223a8000000 0x0000003fc0000000 0x80000003fc000000

def z362 : W := mkw 0x98010b57454d6bd0 0x098010b57454d6bd 0xee2b0fffc7273ffb 0xfee2b0fffc7273ff

def z363 : W := mkw 0x0000084004402200 0x0000008400440220 0xf41488c004dce70d 0x5f41488c004dce70

def z364 : W := mkw 0xc9b05dc56fcc7fc1 0x1c9b05dc56fcc7fc 0x3df07fc03fdcffcf 0x73df07fc03fdcffc

def z365 : W := mkw 0x90b38b132787a852 0x290b38b132787a85 0xee3b8f3307e7f8fb 0xbee3b8f3307e7f8f

def z366 : W := mkw 0xc1b05d802f803c01 0x1c1b05d802f803c0 0x2de07f003f003803 0x32de07f003f00380

def z367 : W := mkw 0x0000100008001400 0x1000010000800140 0x11c0700038000704 0x411c070003800070

def z368 : W := mkw 0x0000000022828000 0x2000000002282800 0x0000000007c7c000 0x00000000007c7c00

def z369 : W := mkw 0x90010b1337b7a850 0x690010b1337b7a85 0xef2b0f333ffff8ff 0xbef2b0f333ffff8f

def z370 : W := mkw 0x004fe6ba80000007 0x8004fe6ba8000000 0xc00fffffc0000000 0xfc00fffffc000000

def z371 : W := mkw 0x200176be880815a1 0x9200176be880815a 0x00007fffc0003ff0 0xf00007fffc0003ff

def z372 : W := mkw 0x284c306c587857a4 0xd284c306c587857a 0x5fdcf0fcf8f8ffff 0xf5fdcf0fcf8f8fff

def z373 : W := mkw 0x204c302818301424 0xd204c30281830142 0x4fc87030382038fb 0xb4fc87030382038f

def z374 : W := mkw 0x9001031201010810 0x0900103120101081 0xee2b0f3303231832 0xbee2b0f330323183

def z375 : W := mkw 0x00b2800022828002 0x200b280002282800 0xee3b800007e7c00b 0x0ee3b800007e7c00

def z376 : W := mkw 0x00ffe6ba90300007 0xc00ffe6ba9030000 0xfffffffff838000f 0xffffffffff838000

def z377 : W := mkw 0x0800004440484380 0x0080000444048438 0x0000000000d8c704 0x00000000000d8c70

def z378 : W := mkw 0xc1b05dc00d403e01 0x1c1b05dc00d403e0 0x3cf07fc000003f00 0x73cf07fc000003f0

def z379 : W := mkw 0xe1fffffebff83fa7 0xde1fffffebff83fa 0xfffffffffff83fff 0xffffffffffff83ff

def z380 : W := mkw 0x08000845444c63c0 0x008000845444c63c 0xb01488cfc4dcc704 0x4b01488cfc4dcc70

def z381 : W := mkw 0x90010b1305052850 0x090010b130505285 0xe22b0f33072700f8 0x8e22b0f33072700f

def z382 : W := mkw 0x08fe8845444c63c6 0x008fe8845444c63c 0xfcff88cfc4dce7cd 0xdfcff88cfc4dce7c

def z383 : W := mkw 0x00fe800032b28006 0x600fe800032b2800 0x1bff80003bfbc006 0x01bff80003bfbc00

def z384 : W := mkw 0x08b3ced3c4446243 0x008b3ced3c444624 0xa0338fc3c4c4c000 0x0a0338fc3c4c4c00

def z385 : W := mkw 0x0000000000000000 0x0000000000000000 0x44000000000020c9 0x944000000000020c

def z386 : W := mkw 0x0000080104042040 0x0000008010404204 0xee2b0803072720cb 0x9ee2b0803072720c

def z387 : W := mkw 0xc1b05dc02fc03e01 0x1c1b05dc02fc03e0 0x09e077003fc03f07 0x209e077003fc03f0

def z388 : W := mkw 0x284c386d5c7c77e4 0xd284c386d5c7c77e 0x5fcc703c3cfcffff 0xf5fcc703c3cfcfff

def z389 : W := mkw 0x00fec48000000007 0x000fec4800000000 0xfcffffc000000000 0x7fcffffc00000000

def z390 : W := mkw 0xe9fc7ded7ffc7fe5 0xde9fc7ded7ffc7fe 0xfffcfffffffcffff 0xffffcfffffffcfff

def z391 : W := mkw 0x084c286d444c63c4 0x8084c286d444c63c 0xfcdcf8ffc4dce7cd 0xffcdcf8ffc4dce7c

def z392 : W := mkw 0x98010b57454d6bd0 0x098010b57454d6bd 0xf4148fffc4dcfffd 0xff4148fffc4dcfff

def z393 : W := mkw 0x004fa23a80000006 0x8004fa23a8000000 0x000b003000000000 0x0000b00300000000

def z394 : W := mkw 0xc1b05dc02fc03e01 0x1c1b05dc02fc03e0 0x11d070c03fc03f07 0x411d070c03fc03f0

def z395 : W := mkw 0xc9b04dc567cc6bc1 0x0c9b04dc567cc6bc 0xf4348fcfc7dce7cd 0xdf4348fcfc7dce7c

def z396 : W := mkw 0xc1feddc03ff2be07 0x7c1feddc03ff2be0 0x3ffb7fc03fe33f07 0x73ffb7fc03fe33f0

def z397 : W := mkw 0x08000845444c63c0 0x008000845444c63c 0x341008c004dce7cd 0x5341008c004dce7c

def z398 : W := mkw 0x20001004183815a0 0x520001004183815a 0x1fc0700038383fff 0x71fc0700038383ff

def z399 : W := mkw 0x90010b1305052850 0x090010b130505285 0xec2b0f3307070000 0xbec2b0f330707000

def z400 : W := mkw 0xd1b05dc12fc53e51 0x1d1b05dc12fc53e5 0x3ff07fc03fe73fff 0x73ff07fc03fe73ff

def z401 : W := mkw 0x90ff831233b38816 0x690ff831233b3881 0xffff87303fffd83f 0x2ffff87303fffd83

def z402 : W := mkw 0x00fe800032b28006 0x600fe800032b2800 0x01c0000038000000 0x001c000003800000

def z403 : W := mkw 0x204c302c183815a4 0xd204c302c183815a 0xffdcf03c3cfcffff 0xfffdcf03c3cfcfff

def z404 : W := mkw 0x004c000010300004 0x4004c00001030000 0x420c000000380008 0x0420c00000038000

def z405 : W := mkw 0x08fe884576fee3c6 0x608fe884576fee3c 0xf5d488cffcdce7cd 0xdf5d488cffcdce7c

def z406 : W := mkw 0x00ffe6bab2b28007 0xe00ffe6bab2b2800 0x0beb77303b230002 0x20beb77303b23000

def z407 : W := mkw 0x004c202810300004 0xc004c20281030000 0x5fcc703c3838000f 0xf5fcc703c3838000

def z408 : W := mkw 0xc1005dc00d403e01 0x1c1005dc00d403e0 0x34107fc004c03f05 0x734107fc004c03f0

def z409 : W := mkw 0xc10019402fc03e00 0x1c10019402fc03e0 0x2d200f003fc03f07 0x32d200f003fc03f0

def z410 : W := mkw 0x20feb02c183815a6 0xd20feb02c183815a 0xfffff03c38383fff 0xffffff03c38383ff

def z411 : W := mkw 0xc1b05dc02fc03e01 0x1c1b05dc02fc03e0 0xfdf4ffc03fdcff0f 0x7fdf4ffc03fdcff0

def z412 : W := mkw 0x20fff6be880815a7 0x920fff6be880815a 0xfcffffffc0003ff0 0xffcffffffc0003ff

def z413 : W := mkw 0xe1007dec0d483fa1 0x9e1007dec0d483fa 0x00007ffc00003ff0 0xf00007ffc00003ff

def z414 : W := mkw 0x0000000000000000 0x0000000000000000 0xec2b000000000000 0x0ec2b00000000000

def z415 : W := mkw 0x0000000000000000 0x0000000000000000 0x540400000018000d 0x0540400000018000

def z416 : W := mkw 0x20fff6bebaba95a7 0xf20fff6bebaba95a 0xffffffffffffffff 0xffffffffffffffff

def z417 : W := mkw 0x00b0448022800001 0x000b044802280000 0x3df07fc03fc00007 0x73df07fc03fc0000

def z418 : W := mkw 0xc1004dc005402a01 0x0c1004dc005402a0 0x00000fc000000000 0x000000fc00000000

def z419 : W := mkw 0xe1b07dec2fc83fa1 0x9e1b07dec2fc83fa 0x3df07ffc3fc03ff7 0xf3df07ffc3fc03ff

def z420 : W := mkw 0x0000000000000000 0x0000000000000000 0x0c00000000003803 0x30c0000000000380

def z421 : W := mkw 0x00b0000022800000 0x000b000002280000 0x11d0000038c00004 0x011d0000038c0000

def z422 : W := mkw 0x0000000400080180 0x0000000040008018 0x00000000001827cd 0x000000000001827c

def z423 : W := mkw 0x004c202800000004 0x8004c20280000000 0xfcdcf8ffc0000000 0xffcdcf8ffc000000

def z424 : W := mkw 0x8000010001000800 0x0800001000100080 0x0820070003001802 0x2082007000300180

def z425 : W := mkw 0x08000845444c63c0 0x008000845444c63c 0xfe1c88ffc4fcffff 0xffe1c88ffc4fcfff

def z426 : W := mkw 0x0000084004402200 0x0000008400440220 0x000008c000002700 0x5000008c00000270

def z427 : W := mkw 0xc10019402fc03e00 0x1c10019402fc03e0 0x351008c03fc03f07 0x5351008c03fc03f0

def z428 : W := mkw 0x004e800000000006 0x0004e80000000000 0xc00f800000000000 0x0c00f80000000000

def z429 : W := mkw 0x204c302c183815a4 0xd204c302c183815a 0x0bc8703c38203ff2 0xf0bc8703c38203ff

def z430 : W := mkw 0xd1ffdfd33ff7be57 0x7d1ffdfd33ff7be5 0xfffffff33fffffff 0xffffffff33ffffff

def z431 : W := mkw 0x08fe884176f6e246 0x608fe884176f6e24 0xffff88c3ffffc00f 0x0ffff88c3ffffc00

def z432 : W := mkw 0x88000945454c6bc0 0x088000945454c6bc 0xfc348fcfc7dcffcf 0xffc348fcfc7dcffc

def z433 : W := mkw 0x00b1469200000001 0x000b146920000000 0xfcfb7ff300000000 0xffcfb7ff30000000

def z434 : W := mkw 0x0000000000000000 0x0000000000000000 0x3410000004c00005 0x03410000004c0000

def z435 : W := mkw 0xc1b05dc02fc03e01 0x1c1b05dc02fc03e0 0x09e07fc03b003f02 0x709e07fc03b003f0

def z436 : W := mkw 0x0800084144446240 0x0080008414444624 0x000008c3c0000000 0x0000008c3c000000

def z437 : W := mkw 0x00ff821200000006 0x000ff82120000000 0xfcff8f3300000000 0xbfcff8f330000000

def z438 : W := mkw 0x08000845444c63c0 0x008000845444c63c 0xc00488cfc01ce7c8 0xdc00488cfc01ce7c

def z439 : W := mkw 0x20fc302c3ab815a4 0xd20fc302c3ab815a 0x7ffc703c3ff83fff 0xf7ffc703c3ff83ff

def z440 : W := mkw 0x084e8845547ee3c6 0x6084e8845547ee3c 0xf61f88cfc4ffe7cd 0xdf61f88cfc4ffe7c

def z441 : W := mkw 0x08feecedc44c63c7 0x808feecedc44c63c 0xf4d4f8cfc4dce7cd 0xdf4d4f8cfc4dce7c

def z442 : W := mkw 0x90010b1305052850 0x090010b130505285 0xe4230f03070720c9 0x9e4230f03070720c

def z443 : W := mkw 0x904fab3b85052856 0x8904fab3b8505285 0xee2f8f3fc72738fb 0xbee2f8f3fc72738f

def z444 : W := mkw 0xc1005dc00d403e01 0x1c1005dc00d403e0 0x1dc07fc038003f07 0x71dc07fc038003f0

def z445 : W := mkw 0x98010b57454d6bd0 0x098010b57454d6bd 0xee2b0f3307ffffff 0xbee2b0f3307fffff

def z446 : W := mkw 0xb04d333e19391db4 0xdb04d333e19391db 0x5fef773c3b3b3fff 0xf5fef773c3b3b3ff

def z447 : W := mkw 0x08000845444c63c0 0x008000845444c63c 0x540408cfc01827cd 0xd540408cfc01827c

def z448 : W := mkw 0x9000010001010810 0x0900001000101081 0x0200000003231832 0x0020000000323183

def z449 : W := mkw 0x9001031301050850 0x0900103130105085 0xca2b0733032718fa 0xaca2b0733032718f

def z450 : W := mkw 0x204c202c103801a4 0xc204c202c103801a 0x0004000c00180000 0x00004000c0018000

def z451 : W := mkw 0xc1ffeffaa7c02a07 0x8c1ffeffaa7c02a0 0xfcffffffc7c00000 0xffcffffffc7c0000

def z452 : W := mkw 0x0000000000000000 0x0000000000000000 0xee2b0030072738fb 0xbee2b0030072738f

def z453 : W := mkw 0x41b05cc02ec03601 0x141b05cc02ec0360 0x35d078c03cc02705 0x535d078c03cc0270

def z454 : W := mkw 0xe1fc7dec3ff83fa5 0xde1fc7dec3ff83fa 0x3df47fcc3fd83f07 0x73df47fcc3fd83f0

def z455 : W := mkw 0x08000845444c63c0 0x008000845444c63c 0xa01088cfc4c4e7c0 0xda01088cfc4c4e7c

def z456 : W := mkw 0x08000005400c41c0 0x008000005400c41c 0xf414800fc4dcc0cd 0x8f414800fc4dcc0c

def z457 : W := mkw 0xb04d333a19311c34 0xdb04d333a19311c3 0x0beb77303b231832 0x20beb77303b23183

def z458 : W := mkw 0xb0ffbb3f3fbfbdf6 0xfb0ffbb3f3fbfbdf 0xffffff3f3fffffff 0xfffffff3f3ffffff

def z459 : W := mkw 0x00ffa23ab2b28006 0xe00ffa23ab2b2800 0xffff803fffffc00f 0x8ffff803fffffc00

def z460 : W := mkw 0x00fe800032b28006 0x600fe800032b2800 0xe23f800007ffc008 0x0e23f800007ffc00

def z461 : W := mkw 0x98000945454d6bd0 0x098000945454d6bd 0x0200000007ffffff 0x00200000007fffff

def z462 : W := mkw 0x18010217400d41d0 0x018010217400d41d 0xc20f803fc03fc0f8 0x8c20f803fc03fc0f

def z463 : W := mkw 0x00ffe6ba80000007 0x800ffe6ba8000000 0xeceb7f3300000000 0xbeceb7f330000000

def z464 : W := mkw 0x00ffc69280000007 0x000ffc6928000000 0xfcff8fc3c0000000 0x0fcff8fc3c000000

def z465 : W := mkw 0x08000845444c63c0 0x008000845444c63c 0x341008cfc4c027c5 0xd341008cfc4c027c

def z466 : W := mkw 0x00fe800432ba8186 0x600fe800432ba818 0xffff800c3fffe7cf 0xdffff800c3fffe7c

def z467 : W := mkw 0x80ffefba85002807 0x880ffefba8500280 0xfcffffffc7003803 0xffcffffffc700380

def z468 : W := mkw 0x00b2800022828002 0x200b280002282800 0xf437800007dfc00d 0x0f437800007dfc00

def z469 : W := mkw 0xc1b04dc027c02a01 0x0c1b04dc027c02a0 0x3df00fc03fc00007 0x03df00fc03fc0000

def z470 : W := mkw 0x00ffe6ba80000007 0x800ffe6ba8000000 0xa8fbfff3c0000000 0x2a8fbfff3c000000

def z471 : W := mkw 0x004c000010300004 0x4004c00001030000 0x0bc8000038200002 0x00bc800003820000

def z472 : W := mkw 0x9000090105052850 0x0900009010505285 0x0000000007070000 0x0000000000707000

def z473 : W := mkw 0x20ffe6be903801a7 0xc20ffe6be903801a 0xfeffffffc03800f8 0xffeffffffc03800f

def z474 : W := mkw 0x0800084576fee3c0 0x60800084576fee3c 0x030000003fffe7cf 0x0030000003fffe7c

def z475 : W := mkw 0xc1b05dc02fc03e01 0x1c1b05dc02fc03e0 0x21300fc03fc03f07 0x021300fc03fc03f0

def z476 : W := mkw 0x0001021200000000 0x0000102120000000 0xee2b0f330727000b 0xbee2b0f330727000

def z477 : W := mkw 0x0000000000000000 0x0000000000000000 0x1dc0000038000007 0x01dc000003800000

def z478 : W := mkw 0x0000000000000000 0x0000000000000000 0xe400080300000000 0x9e40008030000000

def z479 : W := mkw 0x1001021300050050 0x0100102130005005 0x8003000300070000 0x0800300030007000

def z480 : W := mkw 0x004c202800000004 0x8004c20280000000 0x5ecc703c002038fb 0xf5ecc703c002038f

def z481 : W := mkw 0xc1fff7baab801c07 0x9c1fff7baab801c0 0xfdfffffffb001802 0xffdfffffffb00180

def z482 : W := mkw 0xe1fc75ac3bb81da5 0xde1fc75ac3bb81da 0x5fec773c3b383fff 0xf5fec773c3b383ff

def z483 : W := mkw 0x10ff821332b78056 0x610ff821332b7805 0xffff80333fffc0ff 0x8ffff80333fffc0f

def z484 : W := mkw 0x0800084144446240 0x0080008414444624 0x0000000004c4c000 0x00000000004c4c00

def z485 : W := mkw 0x00ffeefa84402207 0x800ffeefa8440220 0xfcffffffc4c02705 0xffcffffffc4c0270

def z486 : W := mkw 0x20feb0283ab29426 0xf20feb0283ab2942 0x0beb70303b231832 0x20beb70303b23183

def z487 : W := mkw 0x00b0448000000001 0x000b044800000000 0x20300fc000000000 0x020300fc00000000

def z488 : W := mkw 0x284c386d5c7c77e4 0xd284c386d5c7c77e 0xf5d4f8cffcdce7cd 0xdf5d4f8cffcdce7c

def z489 : W := mkw 0x90010b17050d29d0 0x090010b17050d29d 0xfe2f0f3f073f3fff 0xffe2f0f3f073f3ff

def z490 : W := mkw 0xc1b055c02bc01e01 0x1c1b055c02bc01e0 0x19f077c03bc01f06 0x619f077c03bc01f0

def z491 : W := mkw 0xe10019443ff83fa0 0x5e10019443ff83fa 0x030000003ff83fff 0x0030000003ff83ff

def z492 : W := mkw 0x90010b1305052850 0x090010b130505285 0x02000f33072738fb 0xb02000f33072738f

def z493 : W := mkw 0x00fe800000000006 0x000fe80000000000 0xfcff88cfc0000000 0xdfcff88cfc000000

def z494 : W := mkw 0x0000100008001400 0x1000010000800140 0x0100000038003f07 0x00100000038003f0

def z495 : W := mkw 0xd9b15fd76fcd7fd1 0x1d9b15fd76fcd7fd 0xffffffffffffffff 0xffffffffffffffff

def z496 : W := mkw 0xd1015fd30d453e51 0x1d1015fd30d453e5 0x00007ff300003ff0 0xf00007ff300003ff

def z497 : W := mkw 0x00fe800032b28006 0x600fe800032b2800 0xcbef80003b3fc00a 0x0cbef80003b3fc00

def z498 : W := mkw 0xb00019051d3d3df0 0x5b00019051d3d3df 0x030000003f3f3fff 0x0030000003f3f3ff

def z499 : W := mkw 0xd1b15fd32fc53e51 0x1d1b15fd32fc53e5 0x3df07ff33fc03ff7 0xf3df07ff33fc03ff

def z500 : W := mkw 0x2000202c000801a0 0x82000202c000801a 0x0000003c000000f0 0x80000003c000000f

def z501 : W := mkw 0x08016effc44c63c1 0x808016effc44c63c 0x00007fffc00027c0 0xf00007fffc00027c

def z502 : W := mkw 0x0001021200000000 0x0000102120000000 0xa0230f0300000000 0x0a0230f030000000

def z503 : W := mkw 0x00b0000032b28000 0x600b0000032b2800 0x3ff000003fffc00f 0x03ff000003fffc00

def z504 : W := mkw 0x90ffefbb85052857 0x890ffefbb8505285 0xfcffffffc7070000 0xffcffffffc707000

def z505 : W := mkw 0x61fc74ec3af817a5 0xd61fc74ec3af817a 0x11d470cc38d80704 0x411d470cc38d8070

def z506 : W := mkw 0x004e800010328006 0x6004e80001032800 0xee2f8000073fc00b 0x0ee2f8000073fc00

def z507 : W := mkw 0x90010b1305052850 0x090010b130505285 0x00000f0300000000 0x000000f030000000

def z508 : W := mkw 0x00fe800032b28006 0x600fe800032b2800 0x13d480003fffc00f 0x013d480003fffc00

def z509 : W := mkw 0x00fe800032b28006 0x600fe800032b2800 0xabfb80003fe7c002 0x0abfb80003fe7c00

def z510 : W := mkw 0x0000084404482380 0x0000008440448238 0x741408cc04d827cd 0xd741408cc04d827c

def z511 : W := mkw 0x2000302c080815a0 0x92000302c080815a 0x0000700c00000700 0x40000700c0000070

def z512 : W := mkw 0x0800004040404200 0x0080000404040420 0x001080c0c0c0c000 0x0001080c0c0c0c00

def z513 : W := mkw 0xc1b04dc027c02a01 0x0c1b04dc027c02a0 0x2c300fc007c03803 0x32c300fc007c0380

def z514 : W := mkw 0x41b054c02ac01601 0x141b054c02ac0160 0x1dd070c038c03f07 0x71dd070c038c03f0

def z515 : W := mkw 0x41fff6faaac01607 0x941fff6faaac0160 0xfdfffffff8c00704 0xffdfffffff8c0070

def z516 : W := mkw 0x0000080104042040 0x0000008010404204 0xee080833042438fb 0xbee080833042438f

def z517 : W := mkw 0x8000090005002800 0x0800009000500280 0x20200f0007000000 0x020200f000700000

def z518 : W := mkw 0xc1b05dc03ff2be01 0x7c1b05dc03ff2be0 0x3ff07fc03fffff0f 0x73ff07fc03fffff0

def z519 : W := mkw 0x00b2800022828002 0x200b280002282800 0x0023000003030000 0x0002300000303000

def z520 : W := mkw 0x280018455c7c77e0 0x5280018455c7c77e 0x030000003cfcffff 0x0030000003cfcfff

def z521 : W := mkw 0x00b2800022828002 0x200b280002282800 0xbdf380003fc7c007 0x0bdf380003fc7c00

def z522 : W := mkw 0x004c100018301404 0x5004c10001830140 0x5fcc700038383f0f 0x75fcc700038383f0

def z523 : W := mkw 0x0800000440084180 0x0080000044008418 0x0004800cc018c000 0x00004800cc018c00

def z524 : W := mkw 0x0800004440484380 0x0080000444048438 0x541480ccc0d8e7cd 0xd541480ccc0d8e7c

def z525 : W := mkw 0x08fe804472fac386 0x608fe804472fac38 0x11d480ccf8d8c704 0x411d480ccf8d8c70

def z526 : W := mkw 0xc9ffffffefcc7fc7 0x9c9ffffffefcc7fc 0xfdffffffffdcffcf 0xffdffffffffdcffc

def z527 : W := mkw 0x00fe800032b28006 0x600fe800032b2800 0xffff80303ffff8ff 0xbffff80303ffff8f

def z528 : W := mkw 0x10010a1304052050 0x010010a130405205 0xe60b0833042720f9 0x9e60b0833042720f

def z529 : W := mkw 0x98010b57454d6bd0 0x098010b57454d6bd 0xf4378fcfc7dfe7cd 0xdf4378fcfc7dfe7c

def z530 : W := mkw 0x004fa23a80000006 0x8004fa23a8000000 0xec2f8f3fc0000000 0xbec2f8f3fc000000

def z531 : W := mkw 0x0000000400080180 0x0000000040008018 0x5e0c003c00383fff 0xf5e0c003c00383ff

def z532 : W := mkw 0xc9005dc54d4c7fc1 0x1c9005dc54d4c7fc 0xf414ffcfc4dcffcd 0xff414ffcfc4dcffc

def z533 : W := mkw 0xc1fc5dc03ff03e05 0x5c1fc5dc03ff03e0 0x7ffc7fc03ff83f0f 0x77ffc7fc03ff83f0

def z534 : W := mkw 0x1001021300050050 0x0100102130005005 0x00000033000000f0 0x800000033000000f

def z535 : W := mkw 0xc1fed5803bb29c07 0x7c1fed5803bb29c0 0x0beb77003b231802 0x20beb77003b23180

def z536 : W := mkw 0x08fe800572bec1c6 0x608fe800572bec1c 0xffff800fffffc0cf 0x8ffff800fffffc0c

def z537 : W := mkw 0x204fa23e903801a6 0xc204fa23e903801a 0xc20f803fc03800f8 0x8c20f803fc03800f

def z538 : W := mkw 0x0000000000000000 0x0000000000000000 0x101480ccc0000000 0x4101480ccc000000

def z539 : W := mkw 0x98010b5345456a50 0x098010b5345456a5 0xa0338fc3c7c7c000 0x0a0338fc3c7c7c00

def z540 : W := mkw 0x20fff6ba98301427 0xd20fff6ba9830142 0x0beb773038201832 0x20beb77303820183

def z541 : W := mkw 0x08ffeefbc4446247 0x808ffeefbc444624 0xfcffffffc4c4c000 0xffcffffffc4c4c00

def z542 : W := mkw 0x10ffe6bb80050057 0x810ffe6bb8005005 0xfeffffffc02700f8 0xffeffffffc02700f

def z543 : W := mkw 0x0000000000000000 0x0000000000000000 0xe400000004040009 0x0e40000000404000

def z544 : W := mkw 0x08fee4ecc0484387 0x808fee4ecc048438 0x10d4f0ccc0d8c704 0x410d4f0ccc0d8c70

def z545 : W := mkw 0x98010b17450d69d0 0x098010b17450d69d 0xee2f8f3fc73ff8fb 0xbee2f8f3fc73ff8f

def z546 : W := mkw 0x00ffe6ba80000007 0x800ffe6ba8000000 0xd0dff0ffc0000000 0xcd0dff0ffc000000

def z547 : W := mkw 0x004c000010300004 0x4004c00001030000 0x11c4000038180004 0x011c400003818000

def z548 : W := mkw 0x08b2884566cee3c2 0x208b2884566cee3c 0xf43788cfc7dfe7cd 0xdf43788cfc7dfe7c

def z549 : W := mkw 0x08000845444c63c0 0x008000845444c63c 0xa01088c3c4dce7cd 0x0a01088c3c4dce7c

def z550 : W := mkw 0x00fe800010300006 0x400fe80001030000 0xffff80003838000f 0x0ffff80003838000

def z551 : W := mkw 0xb04c392d1d3d3df4 0xdb04c392d1d3d3df 0x5fcc703c3f3f3fff 0xf5fcc703c3f3f3ff

def z552 : W := mkw 0x0800000140044040 0x0080000014004404 0x80008003c004c000 0x080008003c004c00

def z553 : W := mkw 0x2000302c080815a0 0x92000302c080815a 0x5404703c00183ffd 0xf5404703c00183ff

def z554 : W := mkw 0x90010b1305052850 0x090010b130505285 0x2c200f33070038f3 0xb2c200f33070038f

def z555 : W := mkw 0x08b04cc5444c63c1 0x008b04cc5444c63c 0xfcf4ffcfc4dce7cd 0xffcf4ffcfc4dce7c

def z556 : W := mkw 0x20feb0283ab29426 0xf20feb0283ab2942 0xfffff0303fffd83f 0x2fffff0303fffd83

def z557 : W := mkw 0x00b3c69280000003 0x000b3c6928000000 0xbcf3ffc3c0000000 0x7bcf3ffc3c000000

def z558 : W := mkw 0x08000005400c41c0 0x008000005400c41c 0xd404800fc01ce7cd 0xdd404800fc01ce7c

def z559 : W := mkw 0x00fee4a880000007 0x800fee4a88000000 0x3cf4ffccc0000000 0x73cf4ffccc000000

def z560 : W := mkw 0x0800084444486380 0x0080008444448638 0x341488ccc4d8e705 0x5341488ccc4d8e70

def z561 : W := mkw 0x00fe800032b28006 0x600fe800032b2800 0x5fef00003b3b000f 0x05fef00003b3b000

def z562 : W := mkw 0xc1b05dc12fc43e41 0x1c1b05dc12fc43e4 0xfdf07fc33fc43fcf 0xffdf07fc33fc43fc

def z563 : W := mkw 0x20000004103801a0 0x420000004103801a 0x02000000003800f8 0x002000000003800f

def z564 : W := mkw 0x20fef4ac983815a7 0xd20fef4ac983815a 0x5fdcf0fcf8383fff 0xf5fdcf0fcf8383ff

def z565 : W := mkw 0x004c000010300004 0x4004c00001030000 0xffdc80003cfcc00f 0x0ffdc80003cfcc00

def z566 : W := mkw 0x0000080004002000 0x0000008000400200 0x2400080004002001 0x1240008000400200

def z567 : W := mkw 0x1000000100050050 0x0100000010005005 0x02000000002700f8 0x002000000002700f

def z568 : W := mkw 0x204c202c103801a4 0xc204c202c103801a 0x5ecc703c003800f8 0xf5ecc703c003800f

def z569 : W := mkw 0x08ffe6fec0484387 0x808ffe6fec048438 0xfcffffffc0d8c704 0xffcffffffc0d8c70

def z570 : W := mkw 0x9000090137b7a850 0x69000090137b7a85 0x030000003ffff8ff 0x0030000003ffff8f

def z571 : W := mkw 0x00fc64a800000005 0x800fc64a80000000 0x7cfc7ffc00000000 0xf7cfc7ffc0000000

def z572 : W := mkw 0x004fa23a80000006 0x8004fa23a8000000 0xf41f88ffc0000000 0xdf41f88ffc000000

def z573 : W := mkw 0x0000000000000000 0x0000000000000000 0x0a2b000003230002 0x00a2b00000323000

def z574 : W := mkw 0x004c000032b28004 0x6004c000032b2800 0x5fcc00003fffc00f 0x05fcc00003fffc00

def z575 : W := mkw 0x41fef4e8aac01607 0x941fef4e8aac0160 0x11d4f0ccf8c00704 0x411d4f0ccf8c0070

def z576 : W := mkw 0xb04d3b3b1d353c74 0xdb04d3b3b1d353c7 0xefeb7f333f2738fb 0xbefeb7f333f2738f

def z577 : W := mkw 0x00fe800032b28006 0x600fe800032b2800 0x3ffb00003fe30007 0x03ffb00003fe3000

def z578 : W := mkw 0xc100558009001c01 0x1c100558009001c0 0x0000770000001800 0x2000077000000180

def z579 : W := mkw 0x204ea02c103a81a6 0xe204ea02c103a81a 0xc20f803c003fc0f8 0x8c20f803c003fc0f

def z580 : W := mkw 0x90b38b132787a852 0x290b38b132787a85 0xa0338f0307c7c000 0x0a0338f0307c7c00

def z581 : W := mkw 0x204c202c103801a4 0xc204c202c103801a 0x560c003c003827fd 0xd560c003c003827f

def z582 : W := mkw 0x904d2b3b05052854 0x8904d2b3b0505285 0xfeef7f3f072738fb 0xffeef7f3f072738f

def z583 : W := mkw 0xe1fc7de83ff03e25 0xde1fc7de83ff03e2 0x3ff87ff03fe03f37 0x73ff87ff03fe03f3

def z584 : W := mkw 0x0000000032b28000 0x60000000032b2800 0x0100000038d8c004 0x00100000038d8c00

def z585 : W := mkw 0x004d223a00000004 0x8004d223a0000000 0xfcef7f3f00000000 0xffcef7f3f0000000

def z586 : W := mkw 0x204c302818301424 0xd204c30281830142 0x5fcc70303838183f 0x25fcc70303838183

def z587 : W := mkw 0x20feb02c3aba95a6 0xf20feb02c3aba95a 0x11d4f00c38d8c704 0x411d4f00c38d8c70

def z588 : W := mkw 0x08000845444c63c0 0x008000845444c63c 0xe40008cfc40427c9 0xde40008cfc40427c

def z589 : W := mkw 0x1001021300050050 0x0100102130005005 0xee2b0f33002700f8 0xbee2b0f33002700f

def z590 : W := mkw 0x9001031201010810 0x0900103120101081 0x0023070003030000 0x0002307000303000

def z591 : W := mkw 0x90010b1305052850 0x090010b130505285 0xa0230f33070738f0 0xba0230f33070738f

def z592 : W := mkw 0xc10011002b801c00 0x1c10011002b801c0 0x010000003b001802 0x0010000003b00180

def z593 : W := mkw 0x00b2c48080000003 0x000b2c4808000000 0x001080c0c0000000 0x0001080c0c000000

def z594 : W := mkw 0x2800386d4c4c77e0 0x92800386d4c4c77e 0x000078ffc0003ff0 0xf000078ffc0003ff

def z595 : W := mkw 0xc1b2cdc027c2aa03 0x2c1b2cdc027c2aa0 0xa0338fc007c7c000 0x0a0338fc007c7c00

def z596 : W := mkw 0x0000000400080180 0x0000000040008018 0xf41488cfc01827cd 0xdf41488cfc01827c

def z597 : W := mkw 0xd1011b532fc53e50 0x1d1011b532fc53e5 0xef2b0f333fe73fff 0xbef2b0f333fe73ff

def z598 : W := mkw 0x00fe90003ab29406 0x700fe90003ab2940 0xfffff0003fffff0f 0x7fffff0003fffff0

def z599 : W := mkw 0xb04d3b3f1d3d3df4 0xdb04d3b3f1d3d3df 0x5fcc7f3f38383fff 0xf5fcc7f3f38383ff

def z600 : W := mkw 0x00fee4a880000007 0x800fee4a88000000 0x00c0700000000000 0x000c070000000000

def z601 : W := mkw 0x0000100408081580 0x1000010040808158 0x5dc4700c38183fcf 0xf5dc4700c38183fc

def z602 : W := mkw 0x08010a57444c63c0 0x008010a57444c63c 0xfc3f8fffc4dce7cd 0xffc3f8fffc4dce7c

def z603 : W := mkw 0xc1feddc03ff2be07 0x7c1feddc03ff2be0 0x3df4ffc03fd8ff07 0x73df4ffc03fd8ff0

def z604 : W := mkw 0x084fa23fc00c41c6 0x8084fa23fc00c41c 0xc00f803fc01cc0c8 0x8c00f803fc01cc0c

def z605 : W := mkw 0x80b04d8005002801 0x080b04d800500280 0x3cf07fc007003803 0x73cf07fc00700380

def z606 : W := mkw 0xc1017ffa8d403e01 0x9c1017ffa8d403e0 0x00007fffc0003f00 0xf00007fffc0003f0

def z607 : W := mkw 0x00fea02800000006 0x800fea0280000000 0xfcfff03c00000000 0xffcfff03c0000000

def z608 : W := mkw 0xd1015fd30d453e51 0x1d1015fd30d453e5 0xee2b7ff307273ffb 0xfee2b7ff307273ff

def z609 : W := mkw 0x0000000000000000 0x0000000000000000 0x1400000000002705 0x5140000000000270

def z610 : W := mkw 0x00b0448000000001 0x000b044800000000 0x08e0770000000000 0x208e077000000000

def z611 : W := mkw 0x41b054802a801401 0x141b054802a80140 0x01c0700038000000 0x001c070003800000

def z612 : W := mkw 0x0000000000000000 0x0000000000000000 0x341008c000000000 0x5341008c00000000

def z613 : W := mkw 0x0000000032b28000 0x60000000032b2800 0xf71480003fffc00f 0x0f71480003fffc00

def z614 : W := mkw 0x0003821280000002 0x0000382128000000 0x80038003c0000000 0x080038003c000000

def z615 : W := mkw 0x204c302c183815a4 0xd204c302c183815a 0x53cc703c383807fc 0xc53cc703c383807f

def z616 : W := mkw 0x41b054c02ac01601 0x141b054c02ac0160 0x3df070c03fc00707 0x43df070c03fc0070

def z617 : W := mkw 0xc1005dc02fc03e01 0x1c1005dc02fc03e0 0x01007fc03fc03f07 0x701007fc03fc03f0

def z618 : W := mkw 0xe14c7dec1d783fa5 0xde14c7dec1d783fa 0x5fcc7ffc38383fff 0xf5fcc7ffc38383ff

def z619 : W := mkw 0x004fa23a90328006 0xe004fa23a9032800 0xc20f803fc03fc008 0x8c20f803fc03fc00

def z620 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000004dcc00d 0x00000000004dcc00

def z621 : W := mkw 0x0800084144446240 0x0080008414444624 0xf41488c3c4dcc00d 0x0f41488c3c4dcc00

def z622 : W := mkw 0x004c202800000004 0x8004c20280000000 0x400c003c00000000 0x8400c003c0000000

def z623 : W := mkw 0x98ff8b5777ffebd6 0x698ff8b5777ffebd 0xffff8fffffffffff 0xfffff8ffffffffff

def z624 : W := mkw 0xc1b055802b801c01 0x1c1b055802b801c0 0x3df077003fc01807 0x23df077003fc0180

def z625 : W := mkw 0x20fc74ac183815a5 0xd20fc74ac183815a 0x7ffc7ffc38383fff 0xf7ffc7ffc38383ff

def z626 : W := mkw 0x0000000022800000 0x0000000002280000 0x010000003fc00007 0x0010000003fc0000

def z627 : W := mkw 0x00b04cc004402201 0x000b04cc00440220 0x3cf07fc004c02705 0x73cf07fc004c0270

def z628 : W := mkw 0xc1b3cfd2a7c02a03 0x0c1b3cfd2a7c02a0 0xa0338fc3c7c00000 0x0a0338fc3c7c0000

def z629 : W := mkw 0x08fe804472fac386 0x608fe804472fac38 0xffff80ccffffc70f 0x4ffff80ccffffc70

def z630 : W := mkw 0x80b0090027802800 0x080b009002780280 0x3df00f003fc03807 0x33df00f003fc0380

def z631 : W := mkw 0x00fee4a880000007 0x800fee4a88000000 0xfcfff0ccc0000000 0x4fcfff0ccc000000

def z632 : W := mkw 0x084faa7fc44c63c6 0x8084faa7fc44c63c 0xf41f88ffc4dce7cd 0xdf41f88ffc4dce7c

def z633 : W := mkw 0xb0013b3f0d0d3df0 0x9b0013b3f0d0d3df 0xee2b7f3f07273ffb 0xfee2b7f3f07273ff

def z634 : W := mkw 0x1001021200010010 0x0100102120001001 0x020b003000230030 0x0020b00300023003

def z635 : W := mkw 0x0001021200000000 0x0000102120000000 0xc00b003300000000 0x8c00b00330000000

def z636 : W := mkw 0x00ffe6ba80000007 0x800ffe6ba8000000 0xc8eff73fc0000000 0xac8eff73fc000000

def z637 : W := mkw 0x00b0000000000000 0x000b000000000000 0x3cf0000000000000 0x03cf000000000000

def z638 : W := mkw 0x1001021300050050 0x0100102130005005 0xee2b0033072700fb 0x8ee2b0033072700f

def z639 : W := mkw 0x08b3ced7c44c63c3 0x008b3ced7c44c63c 0xf4378fcfc4dce7cd 0xdf4378fcfc4dce7c

def z640 : W := mkw 0x08000845444c63c0 0x008000845444c63c 0xc004800fc4dce7cd 0x8c004800fc4dce7c

def z641 : W := mkw 0x284c306c587857a4 0xd284c306c587857a 0x11d4f0ccf8d8c704 0x411d4f0ccf8d8c70

def z642 : W := mkw 0x18010a57444d63d0 0x018010a57444d63d 0xf61f88ffc4ffe7fd 0xdf61f88ffc4ffe7f

def z643 : W := mkw 0xc9b04dc167c46a41 0x0c9b04dc167c46a4 0xa0308fc3c7c4c000 0x0a0308fc3c7c4c00

def z644 : W := mkw 0x20feb02c3aba95a6 0xf20feb02c3aba95a 0x5fef703c3b3b3fff 0xf5fef703c3b3b3ff

def z645 : W := mkw 0x204c302c183815a4 0xd204c302c183815a 0x5fcc700c3838070f 0x45fcc700c3838070

def z646 : W := mkw 0x204c302c183815a4 0xd204c302c183815a 0x1bcc703c38381f36 0x61bcc703c38381f3

def z647 : W := mkw 0x0000000400080180 0x0000000040008018 0x4004000c001800c8 0x84004000c001800c

def z648 : W := mkw 0xb0013b3f0d0d3df0 0x9b0013b3f0d0d3df 0x00007f3f00003ff0 0xf00007f3f00003ff

def z649 : W := mkw 0x00fe800000000006 0x000fe80000000000 0x10d4800000000000 0x010d480000000000

def z650 : W := mkw 0x204c302c183815a4 0xd204c302c183815a 0x420c703c00383ff8 0xf420c703c00383ff

def z651 : W := mkw 0xc1b05dc02fc03e01 0x1c1b05dc02fc03e0 0x29f07fc03fc01802 0x229f07fc03fc0180

def z652 : W := mkw 0x90010b1305052850 0x090010b130505285 0xee2b0f030727000b 0x0ee2b0f030727000

def z653 : W := mkw 0x00ff821232b28006 0x600ff821232b2800 0xffff8f333fffc00f 0xbffff8f333fffc00

def z654 : W := mkw 0x00fe800032b28006 0x600fe800032b2800 0x3df480003fd8c007 0x03df480003fd8c00

def z655 : W := mkw 0x00b0448000000001 0x000b044800000000 0x10d070c000000000 0x410d070c00000000

def z656 : W := mkw 0x90010b1305052850 0x090010b130505285 0xaa2b0f3307271832 0x2aa2b0f330727183

def z657 : W := mkw 0xd1b157922b811c11 0x1d1b157922b811c1 0x0beb77303b231832 0x20beb77303b23183

def z658 : W := mkw 0x0000000010328000 0x6000000001032800 0x02000000003fc008 0x002000000003fc00

def z659 : W := mkw 0x004c202c00080184 0x8004c202c0008018 0x5ccc703c001827cd 0xf5ccc703c001827c

def z660 : W := mkw 0x0000000032b28000 0x60000000032b2800 0x030000003b230002 0x0030000003b23000

def z661 : W := mkw 0x2000100018301420 0x5200010001830142 0x0300000038201832 0x0030000003820183

def z662 : W := mkw 0x90b3cf9385052853 0x090b3cf938505285 0xee3b8ff3c72738fb 0xbee3b8ff3c72738f

def z663 : W := mkw 0xc9b05dc46fc87f81 0x1c9b05dc46fc87f8 0x3df4ffccffd8ff07 0x73df4ffccffd8ff0

def z664 : W := mkw 0x00ffe6ba80000007 0x800ffe6ba8000000 0x3cfb7ff000000000 0x73cfb7ff00000000

def z665 : W := mkw 0x0000000000000000 0x0000000000000000 0x42080030002000f8 0x842080030002000f

def z666 : W := mkw 0x2800386d4c4c77e0 0x92800386d4c4c77e 0xf414f8ffc4dcfffd 0xff414f8ffc4dcfff

def z667 : W := mkw 0x204c302818301424 0xd204c30281830142 0x5fcc703c38201832 0xf5fcc703c3820183

def z668 : W := mkw 0xc1b055802b801c01 0x1c1b055802b801c0 0x3df07fc03b001802 0x73df07fc03b00180

def z669 : W := mkw 0x204c202c103801a4 0xc204c202c103801a 0x4e0c003c003838fb 0xb4e0c003c003838f

def z670 : W := mkw 0xc100094027c02a00 0x0c100094027c02a0 0x0000000007c00000 0x00000000007c0000

def z671 : W := mkw 0x0000000000000000 0x0000000000000000 0xfe3f800007ffc00f 0x0fe3f800007ffc00

def z672 : W := mkw 0x49b05cc56ecc77c1 0x149b05cc56ecc77c 0xf5d4f8cffcdce7cd 0xdf5d4f8cffcdce7c

def z673 : W := mkw 0x0000000100040040 0x0000000010004004 0xc0000003000400c8 0x8c0000003000400c

def z674 : W := mkw 0x0800004440484380 0x0080000444048438 0x000000ccc0000700 0x4000000ccc000070

def z675 : W := mkw 0x0002800000028002 0x2000280000002800 0x800380000007c000 0x0800380000007c00

def z676 : W := mkw 0x00ffc692b2b28007 0x600ffc692b2b2800 0xffff8fc3ffffc00f 0x0ffff8fc3ffffc00

def z677 : W := mkw 0x0000084004402200 0x0000008400440220 0x0000000004c02705 0x00000000004c0270

def z678 : W := mkw 0xd1b15fd22fc13e11 0x1d1b15fd22fc13e1 0x3ffb7ff03fe33f37 0x73ffb7ff03fe33f3

def z679 : W := mkw 0x00000805040c21c0 0x000000805040c21c 0xf404080f041c27cd 0xdf404080f041c27c

def z680 : W := mkw 0x004e800010328006 0x6004e80001032800 0xf61f800004ffc00d 0x0f61f800004ffc00

def z681 : W := mkw 0x00b2800022828002 0x200b280002282800 0x0010800000c0c000 0x00010800000c0c00

def z682 : W := mkw 0x00ffe6ba80000007 0x800ffe6ba8000000 0x5cef773c00000000 0xf5cef773c0000000

def z683 : W := mkw 0x0000084004402200 0x0000008400440220 0x201008c004c00000 0x0201008c004c0000

def z684 : W := mkw 0x00fe800032b28006 0x600fe800032b2800 0xefeb00003f27000b 0x0efeb00003f27000

def z685 : W := mkw 0x00fe884036f2a206 0x600fe884036f2a20 0xffff88c03fffe70f 0x5ffff88c03fffe70

def z686 : W := mkw 0x90ff8b1337b7a856 0x690ff8b1337b7a85 0xffff8f033fffc00f 0x0ffff8f033fffc00

def z687 : W := mkw 0x284c286d547c63e4 0xc284c286d547c63e 0xf61c88ffc4fce7fd 0xdf61c88ffc4fce7f

def z688 : W := mkw 0x00010a1304042040 0x000010a130404204 0xec2b0f33040420c9 0xbec2b0f33040420c

def z689 : W := mkw 0x90010b1205012810 0x090010b120501281 0x2e2b0f3007233833 0x32e2b0f300723383

def z690 : W := mkw 0x0000084104442240 0x0000008410444224 0xf41008c304c427cd 0xdf41008c304c427c

def z691 : W := mkw 0x0000080104042040 0x0000008010404204 0x00000803000020c0 0x900000803000020c

def z692 : W := mkw 0x284c202d503c41e4 0xc284c202d503c41e 0xc20c803fc03cc0f8 0x8c20c803fc03cc0f

def z693 : W := mkw 0x204c302c183815a4 0xd204c302c183815a 0x4bcc703c383818fa 0xa4bcc703c383818f

def z694 : W := mkw 0x004fa23a80000006 0x8004fa23a8000000 0xdccff03fc0000000 0xfdccff03fc000000

def z695 : W := mkw 0x0000000000000000 0x0000000000000000 0x020000000727000b 0x0020000000727000

def z696 : W := mkw 0x28feb86d7efef7e6 0xf28feb86d7efef7e 0xfffff8ffffffffff 0xffffff8fffffffff

def z697 : W := mkw 0x0000000000000000 0x0000000000000000 0x0a08003000201832 0x20a0800300020183

def z698 : W := mkw 0x20fff6be983815a7 0xd20fff6be983815a 0x5fef773c38383fff 0xf5fef773c38383ff

def z699 : W := mkw 0x90010b1305052850 0x090010b130505285 0xe4000f33040438f9 0xbe4000f33040438f

def z700 : W := mkw 0x204fb23e983815a6 0xd204fb23e983815a 0xdfcff03ff8383fff 0xfdfcff03ff8383ff

def z701 : W := mkw 0x98ffefffc54d6bd7 0x898ffefffc54d6bd 0xfeffffffc7ffffff 0xffeffffffc7fffff

def z702 : W := mkw 0x90010b1305052850 0x090010b130505285 0xac230f0307073803 0x3ac230f030707380

def z703 : W := mkw 0x004c000000000004 0x0004c00000000000 0x5ccc000000000000 0x05ccc00000000000

def z704 : W := mkw 0x00ffe6ba80000007 0x800ffe6ba8000000 0xfcfff73000000000 0x2fcfff7300000000

def z705 : W := mkw 0xc1fffffaafc03e07 0x9c1fffffaafc03e0 0x3dfb7ff03fc03f07 0x73dfb7ff03fc03f0

def z706 : W := mkw 0xc1b15fd22fc03e01 0x1c1b15fd22fc03e0 0xfdfb7ff33fc03f07 0xffdfb7ff33fc03f0

def z707 : W := mkw 0x00ffe6ba80000007 0x800ffe6ba8000000 0xfcffffffc7000003 0xffcffffffc700000

def z708 : W := mkw 0xe1fc6dec37f82ba5 0xce1fc6dec37f82ba 0x623c0ffc07f800f8 0x8623c0ffc07f800f

def z709 : W := mkw 0x08000845444c63c0 0x008000845444c63c 0xfdd488cffcdce7cf 0xdfdd488cffcdce7c

def z710 : W := mkw 0x20fff6babab29427 0xf20fff6babab2942 0x0beb77303b231832 0x20beb77303b23183

def z711 : W := mkw 0x90010b1305052850 0x090010b130505285 0xee3b8ff3c72738fb 0xbee3b8ff3c72738f

def z712 : W := mkw 0xc1b05d802f803c01 0x1c1b05d802f803c0 0x3de07f003f003f07 0x73de07f003f003f0

def z713 : W := mkw 0x00b2800032b28002 0x600b2800032b2800 0x032300003fffc00f 0x0032300003fffc00

def z714 : W := mkw 0x004fe6ba90328007 0xe004fe6ba9032800 0xc20fffffc03fc008 0xfc20fffffc03fc00

def z715 : W := mkw 0x204c302c183815a4 0xd204c302c183815a 0x5fcc703038383fff 0x25fcc703038383ff

def z716 : W := mkw 0x304fa23f903d01f6 0xc304fa23f903d01f 0xc20f803fc03f00f8 0x8c20f803fc03f00f

def z717 : W := mkw 0x004e800032b28006 0x6004e800032b2800 0x030b00003fffc00f 0x0030b00003fffc00

def z718 : W := mkw 0x00b0548008001401 0x100b054800800140 0x3df07fc038000704 0x73df07fc03800070

def z719 : W := mkw 0xc1b05dc02fc03e01 0x1c1b05dc02fc03e0 0x09e077003b003f02 0x209e077003b003f0

def z720 : W := mkw 0x08ffeeffc44c63c7 0x808ffeeffc44c63c 0x08eb773004dce7cd 0x208eb773004dce7c

def z721 : W := mkw 0x00b2800032b28002 0x600b2800032b2800 0xef3b80003fffc00f 0x0ef3b80003fffc00

def z722 : W := mkw 0xc1b05dc12fc43e41 0x1c1b05dc12fc43e4 0xfffb7fc33fe73fcf 0xffffb7fc33fe73fc

def z723 : W := mkw 0x00ffe6ba80000007 0x800ffe6ba8000000 0xfeffffffc0270008 0xffeffffffc027000

def z724 : W := mkw 0x90ff8b1337b7a856 0x690ff8b1337b7a85 0x11d48f3338d8f8f4 0xb11d48f3338d8f8f

def z725 : W := mkw 0x98000945454d6bd0 0x098000945454d6bd 0xfe348fcfc7ffffff 0xffe348fcfc7fffff

def z726 : W := mkw 0xd1b05dc12fc53e51 0x1d1b05dc12fc53e5 0x3df07fc03fc03ff7 0x73df07fc03fc03ff

def z727 : W := mkw 0xc1b05dc02fc03e01 0x1c1b05dc02fc03e0 0x35f07fc03fc02705 0x535f07fc03fc0270

def z728 : W := mkw 0xc1b05dc02fc03e01 0x1c1b05dc02fc03e0 0x01c07fc038003f00 0x701c07fc038003f0

def z729 : W := mkw 0xb04d3b3f1d3d3df4 0xdb04d3b3f1d3d3df 0xb1e77f0f3f1f0704 0x4b1e77f0f3f1f070

def z730 : W := mkw 0xc1b05dc02fc03e01 0x1c1b05dc02fc03e0 0x3ff07fc03fe73f0f 0x73ff07fc03fe73f0

def z731 : W := mkw 0xc9b055856b8c5dc1 0x1c9b055856b8c5dc 0xc9e4f70ffb1cd8ca 0xac9e4f70ffb1cd8c

def z732 : W := mkw 0x00fec48032b28007 0x600fec48032b2800 0xffffffcfffffc00f 0xfffffffcfffffc00

def z733 : W := mkw 0x204d223e903801a4 0xc204d223e903801a 0x420c003fc03800f8 0x8420c003fc03800f

def z734 : W := mkw 0x00ffe6bab2b28007 0xe00ffe6bab2b2800 0xfdffffffffd8c007 0xffdffffffffd8c00

def z735 : W := mkw 0x00ffe6ba80000007 0x800ffe6ba8000000 0xfcffffffc4c00005 0xffcffffffc4c0000

def z736 : W := mkw 0xc1b2ddc02fc2be03 0x3c1b2ddc02fc2be0 0xfdf7ffc03fdfff0f 0x7fdf7ffc03fdfff0

def z737 : W := mkw 0x00ffe6ba80000007 0x800ffe6ba8000000 0xfcffffffc00020c9 0xffcffffffc00020c

def z738 : W := mkw 0x204fa23e903a81a6 0xe204fa23e903a81a 0xc20f803fc03fc0f8 0x8c20f803fc03fc0f

def z739 : W := mkw 0xd90019456fcd7fd0 0x1d90019456fcd7fd 0x030000003fffffff 0x0030000003ffffff

def z740 : W := mkw 0x0000100008001400 0x1000010000800140 0x3de07f0038003f07 0x73de07f0038003f0

def z741 : W := mkw 0xc14eddc01d72be07 0x7c14eddc01d72be0 0xc20fffc0003fff08 0x7c20fffc0003fff0

def z742 : W := mkw 0x51b156d32ac51651 0x151b156d32ac5165 0xd3db70f338e707fc 0xcd3db70f338e707f

def z743 : W := mkw 0x0000448000000001 0x0000044800000000 0xf414ffcfc0000000 0xff414ffcfc000000

def z744 : W := mkw 0xc1b05dc02fc03e01 0x1c1b05dc02fc03e0 0x31f07fc03fc03f07 0x431f07fc03fc03f0

def z745 : W := mkw 0xc9b05dc16fc47e41 0x1c9b05dc16fc47e4 0xfdf4ffcfffc4ff07 0xffdf4ffcfffc4ff0

def z746 : W := mkw 0x00b04cc026c02201 0x000b04cc026c0220 0x3df07fc03fc02707 0x73df07fc03fc0270

def z747 : W := mkw 0xd1b05dc12fc53e51 0x1d1b05dc12fc53e5 0x3df07fc03fc73f07 0x73df07fc03fc73f0

def z748 : W := mkw 0x41b054c02ac01601 0x141b054c02ac0160 0x3df07fc038c03f07 0x73df07fc038c03f0

def z749 : W := mkw 0xd9015fd74d4d7fd1 0x1d9015fd74d4d7fd 0x00007fffc0003ff0 0xf00007fffc0003ff

def z750 : W := mkw 0x9801035641494b90 0x09801035641494b9 0x1a3f87fcc3fbdf36 0x61a3f87fcc3fbdf3

def z751 : W := mkw 0x90feeda985052857 0x890feeda98505285 0x12d4f0ccc72738fb 0x412d4f0ccc72738f

def z752 : W := mkw 0x0800084444486380 0x0080008444448638 0xf41488cfc4d8e705 0xdf41488cfc4d8e70

def z753 : W := mkw 0x00ffe6baa2828007 0xa00ffe6baa282800 0xfcffffffc7dfc00d 0xffcffffffc7dfc00

def z754 : W := mkw 0x90010b1305052850 0x090010b130505285 0x4e2b0730072738fb 0xb4e2b0730072738f

def z755 : W := mkw 0xa04c292c153829a4 0xca04c292c153829a 0x6e2c0f3c073838fb 0xb6e2c0f3c073838f

def z756 : W := mkw 0x00b166ba80000001 0x800b166ba8000000 0x20307fffc0000000 0xf20307fffc000000

def z757 : W := mkw 0x204c302818301424 0xd204c30281830142 0x5fc8703038203fff 0xf5fc8703038203ff

def z758 : W := mkw 0x2000302c183815a0 0xd2000302c183815a 0x1fc0703c38383fff 0xf1fc0703c38383ff

def z759 : W := mkw 0xc1b055802b801c01 0x1c1b055802b801c0 0x3df077003fc03f07 0x73df077003fc03f0

def z760 : W := mkw 0x00ffe6bab2b28007 0xe00ffe6bab2b2800 0xffffffffffe7c002 0xfffffffffffe7c00

def z761 : W := mkw 0xc1b05dc02fc03e01 0x1c1b05dc02fc03e0 0x7df47fcc3fc03f07 0xf7df47fcc3fc03f0

def z762 : W := mkw 0xc9b05dc16fc47e41 0x1c9b05dc16fc47e4 0x3df07fc03fc4ff07 0x73df07fc03fc4ff0

def z763 : W := mkw 0x0800004440484380 0x0080000444048438 0xb01488cfc0d8c704 0x4b01488cfc0d8c70

def z764 : W := mkw 0x00ffe6ba80000007 0x800ffe6ba8000000 0xfcffffffc0002705 0xffcffffffc000270

def z765 : W := mkw 0xc1b05dc02fc03e01 0x1c1b05dc02fc03e0 0x3df07ff03fc03ff7 0xf3df07ff03fc03ff

def z766 : W := mkw 0x800019000d003c00 0x1800019000d003c0 0x1dc07f0038003f07 0x71dc07f0038003f0

def z767 : W := mkw 0x08000845444c63c0 0x008000845444c63c 0xf41488cfc4dcc704 0xdf41488cfc4dcc70

def z768 : W := mkw 0x284c38695c747664 0xd284c38695c74766 0xabd8f8f3fce4d832 0x2abd8f8f3fce4d83

def z769 : W := mkw 0x0800004440484380 0x0080000444048438 0xf41488cfc4dcc70d 0xdf41488cfc4dcc70

def z770 : W := mkw 0x000166ba80000001 0x8000166ba8000000 0x1cc07fffc0000000 0xf1cc07fffc000000

def z771 : W := mkw 0xc90019456fcc7fc0 0x1c90019456fcc7fc 0x010000003fc03fc7 0x0010000003fc03fc

def z772 : W := mkw 0x000166bab2b28001 0xe000166bab2b2800 0x03007fffffffc00f 0xf03007fffffffc00

def z773 : W := mkw 0x00fea02832b28006 0xe00fea02832b2800 0xfffff00c3fffc00f 0x4fffff00c3fffc00

def z774 : W := mkw 0x20b3d696983815a3 0x520b3d696983815a 0xa3338fc3f8383fff 0x0a3338fc3f8383ff

def z775 : W := mkw 0x00b2800032b28002 0x600b2800032b2800 0xf73780003fffc00f 0x0f73780003fffc00

def z776 : W := mkw 0x00ffe6ba90300007 0xc00ffe6ba9030000 0xffffffffff3f000f 0xfffffffffff3f000

def z777 : W := mkw 0x00ffe6ba80000007 0x800ffe6ba8000000 0xfcffffffc018000d 0xffcffffffc018000

def z778 : W := mkw 0x004e800032b28006 0x6004e800032b2800 0xf71f80003fffc00f 0x0f71f80003fffc00

def z779 : W := mkw 0x00ffe6bab2b28007 0xe00ffe6bab2b2800 0x11d4fffff8d8c004 0xf11d4fffff8d8c00

def z780 : W := mkw 0xc1fff7babbb29c07 0xfc1fff7babbb29c0 0x0beb77303b231802 0x20beb77303b23180

def z781 : W := mkw 0xc14fbb7aafc03e06 0x9c14fbb7aafc03e0 0xc10f803fffc03f07 0x8c10f803fffc03f0

def z782 : W := mkw 0x204eb02c983815a6 0xd204eb02c983815a 0x5fccf03cf8383fff 0xf5fccf03cf8383ff

def z783 : W := mkw 0x08fe884576fee3c6 0x608fe884576fee3c 0x0beb08cffb2327c2 0xd0beb08cffb2327c

def z784 : W := mkw 0x41b054c02ac01601 0x141b054c02ac0160 0x3df07fc03fc00707 0x73df07fc03fc0070

def z785 : W := mkw 0x00ffe6ba90300007 0xc00ffe6ba9030000 0xfffffffff8200002 0xffffffffff820000

def z786 : W := mkw 0x88000945454c6bc0 0x088000945454c6bc 0xf4148fcfc4dcffcd 0xff4148fcfc4dcffc

def z787 : W := mkw 0x90010b1305052850 0x090010b130505285 0xfe3b0f3307e738ff 0xbfe3b0f3307e738f

def z788 : W := mkw 0xc1b05dc02fc03e01 0x1c1b05dc02fc03e0 0x3df07fcfffc03f07 0xf3df07fcfffc03f0

def z789 : W := mkw 0x00ffe6ba80000007 0x800ffe6ba8000000 0xf0ffffffc0000000 0xcf0ffffffc000000

def z790 : W := mkw 0x08000845444c63c0 0x008000845444c63c 0xf41488ffc4dcfffd 0xff41488ffc4dcfff

def z791 : W := mkw 0xc90019454d4c7fc0 0x1c90019454d4c7fc 0x0000000004dcffcd 0x00000000004dcffc

def z792 : W := mkw 0xc1b05dc02fc03e01 0x1c1b05dc02fc03e0 0x11d07fc03fc03f07 0x711d07fc03fc03f0

def z793 : W := mkw 0x90010b1305052850 0x090010b130505285 0xe22b0f33072738f8 0xbe22b0f33072738f

def z794 : W := mkw 0x00ffe6bab2b28007 0xe00ffe6bab2b2800 0xfffffffffb3fc00a 0xffffffffffb3fc00

def z795 : W := mkw 0x0800004440484380 0x0080000444048438 0xd01480cfc0d8c704 0xcd01480cfc0d8c70

def z796 : W := mkw 0x0000000032b28000 0x60000000032b2800 0xc30b00003fffc00f 0x0c30b00003fffc00

def z797 : W := mkw 0x00ffe6ba90328007 0xe00ffe6ba9032800 0xfeffffffc73fc00b 0xffeffffffc73fc00

def z798 : W := mkw 0x204c302c183815a4 0xd204c302c183815a 0x4fc8703c38203ffb 0xf4fc8703c38203ff

def z799 : W := mkw 0x08000845444c63c0 0x008000845444c63c 0xd01480cfc4dce7cd 0xcd01480cfc4dce7c

def z800 : W := mkw 0xc1b05dc12fc43e41 0x1c1b05dc12fc43e4 0x3df07fc33fc03fc7 0xf3df07fc33fc03fc

def z801 : W := mkw 0x98000945454d6bd0 0x098000945454d6bd 0xf41488cfc4dcfffd 0xdf41488cfc4dcfff

def z802 : W := mkw 0x00ffe6baa2800007 0x800ffe6baa280000 0xfdffffffffdcc00f 0xffdffffffffdcc00

def z803 : W := mkw 0x08000045404c43c0 0x008000045404c43c 0xf41480cfc4dcc7cd 0xcf41480cfc4dcc7c

def z804 : W := mkw 0xc1b055802b801c01 0x1c1b055802b801c0 0x19e077003b001f06 0x619e077003b001f0

def z805 : W := mkw 0x90010b1305052850 0x090010b130505285 0x2e2b0f30072738fb 0x32e2b0f30072738f

def z806 : W := mkw 0x00ffe6ba80000007 0x800ffe6ba8000000 0x10d4ffcfc0000000 0x410d4ffcfc000000

def z807 : W := mkw 0x18000845444d63d0 0x018000845444d63d 0xf61488cfc4ffe7fd 0xdf61488cfc4ffe7f

def z808 : W := mkw 0x004d66ba80000005 0x8004d66ba8000000 0xfcef7fffc0000000 0xffcef7fffc000000

def z809 : W := mkw 0xd1b3cfd327c7aa53 0x2d1b3cfd327c7aa5 0xa0338fc307c7c000 0x0a0338fc307c7c00

def z810 : W := mkw 0xc1b05dc02fc03e01 0x1c1b05dc02fc03e0 0x11d07fc038c00704 0x411d07fc038c0070

def z811 : W := mkw 0xc1b055c02bc01e01 0x1c1b055c02bc01e0 0x11f077c03bc00704 0x411f077c03bc0070

def z812 : W := mkw 0xc9b05dc16fc47e41 0x1c9b05dc16fc47e4 0x3df07fc3ffc03f07 0x73df07fc3ffc03f0

def z813 : W := mkw 0x90010b1305052850 0x090010b130505285 0xca2b0f33032738fa 0xbca2b0f33032738f

def z814 : W := mkw 0x00fe800032b28006 0x600fe800032b2800 0x5fef00003fffc00f 0x05fef00003fffc00

def z815 : W := mkw 0x00fea028b2b28006 0xe00fea028b2b2800 0xffff800cffffc00f 0x0ffff800cffffc00

def z816 : W := mkw 0x0000548008001401 0x1000054800800140 0x1dc07fc038003f07 0x71dc07fc038003f0

def z817 : W := mkw 0x00ffe6baa2828007 0xa00ffe6baa282800 0xfdffffffffc7c007 0xffdffffffffc7c00

def z818 : W := mkw 0x00ffe6ba80000007 0x800ffe6ba8000000 0xfeffffffc02000f8 0xffeffffffc02000f

def z819 : W := mkw 0x00fe800032b28006 0x600fe800032b2800 0xebff80003fffc00a 0x0ebff80003fffc00

def z820 : W := mkw 0x00b166baa2800001 0x800b166baa280000 0x3df07fffffc00007 0xf3df07fffffc0000

def z821 : W := mkw 0x00ffe6bab2b28007 0xe00ffe6bab2b2800 0xfffffffff8ffc00c 0xffffffffff8ffc00

def z822 : W := mkw 0x00fee4a880000007 0x800fee4a88000000 0xfcf4ffcfc0000000 0xffcf4ffcfc000000

def z823 : W := mkw 0x00ffe6ba90328007 0xe00ffe6ba9032800 0xfeffffffc4ffc00d 0xffeffffffc4ffc00

def z824 : W := mkw 0x00fe800032b28006 0x600fe800032b2800 0x1bff80003fffc00f 0x01bff80003fffc00

def z825 : W := mkw 0x90010b1305052850 0x090010b130505285 0x0a2b0730032338f2 0x20a2b0730032338f

def z826 : W := mkw 0x90010b1305052850 0x090010b130505285 0xee2b0730072738fb 0x2ee2b0730072738f

def z827 : W := mkw 0x00ffe6ba80000007 0x800ffe6ba8000000 0xfcffffffc0d8c004 0xffcffffffc0d8c00

def z828 : W := mkw 0x08000845444c63c0 0x008000845444c63c 0xe01488cfc4dce7c8 0xde01488cfc4dce7c

def z829 : W := mkw 0x9001031201010810 0x0900103120101081 0xee2b0730072738fb 0xbee2b0730072738f

def z830 : W := mkw 0x00fea02832b28006 0xe00fea02832b2800 0xfffff03c3ffff8ff 0xffffff03c3ffff8f

def z831 : W := mkw 0x204eb02c183a95a6 0xf204eb02c183a95a 0xffeff03c3f3fffff 0xfffeff03c3f3ffff

def z832 : W := mkw 0xc1b05dc02fc03e01 0x1c1b05dc02fc03e0 0xfdf4ffc03fc03f07 0x7fdf4ffc03fc03f0

def z833 : W := mkw 0xc1b05dc02fc03e01 0x1c1b05dc02fc03e0 0xfdfb7fc03fc03f07 0x7fdfb7fc03fc03f0

def z834 : W := mkw 0x00ffe6ba80000007 0x800ffe6ba8000000 0xd0dfffffc0000000 0xfd0dfffffc000000

def z835 : W := mkw 0x08000845444c63c0 0x008000845444c63c 0xf61488cfc4fcffff 0xdf61488cfc4fcfff

def z836 : W := mkw 0x0000000400080180 0x0000000040008018 0xf41488cfc4dce7cd 0xdf41488cfc4dce7c

def z837 : W := mkw 0x90010b5305452a50 0x090010b5305452a5 0xee2b0f3307e73fff 0xbee2b0f3307e73ff

def z838 : W := mkw 0x98000945454d6bd0 0x098000945454d6bd 0xfe3f88cfc7ffffff 0xdfe3f88cfc7fffff

def z839 : W := mkw 0x00fe800032b28006 0x600fe800032b2800 0xefeb00003fffc00f 0x0efeb00003fffc00

def z840 : W := mkw 0x00ffe6ba80000007 0x800ffe6ba8000000 0x00c07fffc0000000 0xf00c07fffc000000

def z841 : W := mkw 0x00b054802a801401 0x100b054802a80140 0x3df07fc03fc03f07 0x73df07fc03fc03f0

def z842 : W := mkw 0xc1b05dc12fc43e41 0x1c1b05dc12fc43e4 0xbdf07fc33fc43f07 0x7bdf07fc33fc43f0

def z843 : W := mkw 0x00ffe6ba80000007 0x800ffe6ba8000000 0xfdfffffff8000007 0xffdfffffff800000

def z844 : W := mkw 0xc1b05dc02fc03e01 0x1c1b05dc02fc03e0 0x3df07fc03fc00704 0x73df07fc03fc0070

def z845 : W := mkw 0x00b166ba80000001 0x800b166ba8000000 0xfcfb7fffc0000000 0xffcfb7fffc000000

def z846 : W := mkw 0x00fe800032b28006 0x600fe800032b2800 0xabfb80003fffc00f 0x0abfb80003fffc00

def z847 : W := mkw 0x08000845444c63c0 0x008000845444c63c 0xb01488cfc4dce7cd 0x4b01488cfc4dce7c

def z848 : W := mkw 0x00fe800032b28006 0x600fe800032b2800 0xffff80303fffc00f 0xbffff80303fffc00

def z849 : W := mkw 0x00ffe6ba80000007 0x800ffe6ba8000000 0x5cdcffffc0000000 0xf5cdcffffc000000

def z850 : W := mkw 0x90010b1305052850 0x090010b130505285 0xfe3f8fffc7fff8ff 0xffe3f8fffc7fff8f

def z851 : W := mkw 0x00ffe6ba80000007 0x800ffe6ba8000000 0x3cfb7fffc0000000 0xf3cfb7fffc000000

def z852 : W := mkw 0x08000845444c63c0 0x008000845444c63c 0x341488cfc4d8e7c5 0xd341488cfc4d8e7c

def z853 : W := mkw 0xc1b05dc02fc03e01 0x1c1b05dc02fc03e0 0xfdf4ffcfffdcff0f 0xffdf4ffcfffdcff0

def z854 : W := mkw 0x00fd66ba80000005 0x800fd66ba8000000 0x7cfc7fffc0000000 0xf7cfc7fffc000000

def z855 : W := mkw 0x204c302c183815a4 0xd204c302c183815a 0xffdcf03c38383fff 0xfffdcf03c38383ff

def z856 : W := mkw 0xc1b05dc02fc03e01 0x1c1b05dc02fc03e0 0x2de07fc03f003f03 0x72de07fc03f003f0

def z857 : W := mkw 0x204d223e103801a4 0xc204d223e103801a 0xc20f003f003800f8 0x8c20f003f003800f

def z858 : W := mkw 0xc1b05dc02fc03e01 0x1c1b05dc02fc03e0 0x39f07fc03fc01f06 0x639f07fc03fc01f0

def z859 : W := mkw 0xc9b05dc06fc07e01 0x1c9b05dc06fc07e0 0x3df0ffc0ffc0ff07 0x73df0ffc0ffc0ff0

def z860 : W := mkw 0x0002800032b28002 0x60002800032b2800 0x830380003fffc00f 0x0830380003fffc00

def z861 : W := mkw 0x004d223a00000004 0x8004d223a0000000 0xfcffffffc0000000 0xffcffffffc000000

def z862 : W := mkw 0x41b054c02ac01601 0x141b054c02ac0160 0x11d07fc038c00704 0x711d07fc038c0070

def z863 : W := mkw 0x204c302c183815a4 0xd204c302c183815a 0x0bc8703038203ff2 0x20bc8703038203ff

def z864 : W := mkw 0x98000945454d6bd0 0x098000945454d6bd 0xf41488cfc7dfe7cd 0xdf41488cfc7dfe7c

def z865 : W := mkw 0x000166ba80000001 0x8000166ba8000000 0x54047fffc0000000 0xf54047fffc000000

def z866 : W := mkw 0x41b05cc02ec03601 0x141b05cc02ec0360 0x3df07fc03cc02705 0x73df07fc03cc0270

def z867 : W := mkw 0x88000945454c6bc0 0x088000945454c6bc 0xfe3c8fffc7fcffff 0xffe3c8fffc7fcfff

def z868 : W := mkw 0x90010b1305052850 0x090010b130505285 0xee3b8f3307e7f8fb 0xbee3b8f3307e7f8f

def z869 : W := mkw 0x20fef4acbaba95a7 0xf20fef4acbaba95a 0x11d4f0ccf8d8c704 0x411d4f0ccf8d8c70

def z870 : W := mkw 0x20001004183815a0 0x520001004183815a 0x5fc8703038383fff 0xf5fc8703038383ff

def z871 : W := mkw 0x000166ba80000001 0x8000166ba8000000 0x1014ffffc0000000 0xf1014ffffc000000

def z872 : W := mkw 0x90010b1305052850 0x090010b130505285 0xfe3b0ff3072738fb 0xffe3b0ff3072738f

def z873 : W := mkw 0x204c302c183815a4 0xd204c302c183815a 0xdfccf03ff8383fff 0xfdfccf03ff8383ff

def z874 : W := mkw 0x98000945454d6bd0 0x098000945454d6bd 0xfe1c88ffc7ffffff 0xffe1c88ffc7fffff

def z875 : W := mkw 0xc1b05dc02fc03e01 0x1c1b05dc02fc03e0 0xbdf0ffc03fc4ff07 0x7bdf0ffc03fc4ff0

def z876 : W := mkw 0x08000045404c43c0 0x008000045404c43c 0xf41488cfc0dcc7cc 0xdf41488cfc0dcc7c

def z877 : W := mkw 0x90010b1305052850 0x090010b130505285 0xea2b0f33072718fa 0xaea2b0f33072718f

def z878 : W := mkw 0x00ffe6bab2b00007 0xc00ffe6bab2b0000 0xfffffffffff8000f 0xffffffffffff8000

def z879 : W := mkw 0x08000845444c63c0 0x008000845444c63c 0xf61f88cfc4ffe7cd 0xdf61f88cfc4ffe7c

def z880 : W := mkw 0x9001031301050850 0x0900103130105085 0x0a2b0730032718fa 0x20a2b0730032718f

def z881 : W := mkw 0x00fee4a8b2b28007 0xe00fee4a8b2b2800 0xfffff0003fffc00f 0x0fffff0003fffc00

def z882 : W := mkw 0xc1b05dc02fc03e01 0x1c1b05dc02fc03e0 0x3ffb7fc03fe33f07 0x73ffb7fc03fe33f0

def z883 : W := mkw 0x204eb02c183a95a6 0xf204eb02c183a95a 0x5fccf03c3838ffff 0xf5fccf03c3838fff

def z884 : W := mkw 0x08000045404c43c0 0x008000045404c43c 0x101480cfc0d8c7c4 0xc101480cfc0d8c7c

def z885 : W := mkw 0x08000845444c63c0 0x008000845444c63c 0xfc1c88ffc4dce7cd 0xffc1c88ffc4dce7c

def z886 : W := mkw 0x00fe800032b28006 0x600fe800032b2800 0xbbff80003fffc006 0x0bbff80003fffc00

def z887 : W := mkw 0x00fe800032b28006 0x600fe800032b2800 0xb3f780003fffc00f 0x0b3f780003fffc00

def z888 : W := mkw 0xb8013b7f4d4d7ff0 0x9b8013b7f4d4d7ff 0x00007fffc0003ff0 0xf00007fffc0003ff

def z889 : W := mkw 0x000166ba80000001 0x8000166ba8000000 0xf414ffffc4dcc00d 0xff414ffffc4dcc00

def z890 : W := mkw 0x000166ba80000001 0x8000166ba8000000 0x4c087fffc0000000 0xf4c087fffc000000

def z891 : W := mkw 0x204c302c183815a4 0xd204c302c183815a 0xffdcf8fffcfcffff 0xfffdcf8fffcfcfff

def z892 : W := mkw 0x90010b1305052850 0x090010b130505285 0xfe3f8f33072738fb 0xbfe3f8f33072738f

def z893 : W := mkw 0xc1b05dc02fc03e01 0x1c1b05dc02fc03e0 0x1de07fc03b003f07 0x71de07fc03b003f0

def z894 : W := mkw 0xc1b2ddc02fc2be03 0x3c1b2ddc02fc2be0 0xfffbffc03fe7ff0f 0x7fffbffc03fe7ff0

def z895 : W := mkw 0xc1b05dc02fc03e01 0x1c1b05dc02fc03e0 0x3df077003fc03f07 0x23df077003fc03f0

def z896 : W := mkw 0xc1b05dc02fc03e01 0x1c1b05dc02fc03e0 0x09e07fc03fc03f07 0x709e07fc03fc03f0

def z897 : W := mkw 0x00ffe6bab2b28007 0xe00ffe6bab2b2800 0xffffffffffe30007 0xfffffffffffe3000

def z898 : W := mkw 0xc1b05dc02fc03e01 0x1c1b05dc02fc03e0 0x35d07fc03cc03f05 0x735d07fc03cc03f0

def z899 : W := mkw 0xd1b05dc12fc53e51 0x1d1b05dc12fc53e5 0xfff07fc33fe73fff 0xffff07fc33fe73ff

def z900 : W := mkw 0x304d223f103d01f4 0xc304d223f103d01f 0x420c003f003800f8 0x8420c003f003800f

def z901 : W := mkw 0x9001031201010810 0x0900103120101081 0x0a2b0730032338f2 0xb0a2b0730032338f

def z902 : W := mkw 0x00ffe6bab2b28007 0xe00ffe6bab2b2800 0xfdffffffffdfc004 0xffdffffffffdfc00

def z903 : W := mkw 0x00fec48000000007 0x000fec4800000000 0xfcffffcfc0000000 0xffcffffcfc000000

def z904 : W := mkw 0x00ffe6bab2b28007 0xe00ffe6bab2b2800 0xfdfffffff8000000 0xffdfffffff800000

def z905 : W := mkw 0x20b2b02c2a8a95a2 0xb20b2b02c2a8a95a 0xa033f03c07c7fff0 0xfa033f03c07c7fff

def z906 : W := mkw 0x9001031301050850 0x0900103130105085 0xce2b0733032738fb 0xbce2b0733032738f

def z907 : W := mkw 0x204c302c183815a4 0xd204c302c183815a 0x4bcc703c38383ffa 0xf4bcc703c38383ff

def z908 : W := mkw 0xc1b05dc02fc03e01 0x1c1b05dc02fc03e0 0xbdf37fc03fc73f07 0x7bdf37fc03fc73f0

def z909 : W := mkw 0xc9b019456fcc7fc0 0x1c9b019456fcc7fc 0xfdf480003fdcffcf 0x0fdf480003fdcffc

def z910 : W := mkw 0x08000845444c63c0 0x008000845444c63c 0xfcd4f8cfc4dce7cd 0xffcd4f8cfc4dce7c

def z911 : W := mkw 0x00b0448022800001 0x000b044802280000 0xfdf4ffcfffdcc00f 0xffdf4ffcfffdcc00

def z912 : W := mkw 0x90010b1205012810 0x090010b120501281 0x6e2b0f30072338fb 0xb6e2b0f30072338f

def z913 : W := mkw 0x00ffe6ba80000007 0x800ffe6ba8000000 0xfcffffffc0003803 0xffcffffffc000380

def z914 : W := mkw 0x0000000032b28000 0x60000000032b2800 0x0b2b00003fffc00f 0x00b2b00003fffc00

def z915 : W := mkw 0x204c302c183815a4 0xd204c302c183815a 0x55c4703c38183ffd 0xf55c4703c38183ff

def z916 : W := mkw 0x00fe800032b28006 0x600fe800032b2800 0xffff80003ffff8ff 0x0ffff80003ffff8f

def z917 : W := mkw 0x00fee4a832b28007 0xe00fee4a832b2800 0xfffffffc3fffc00f 0xffffffffc3fffc00

def z918 : W := mkw 0x204eb02c183815a6 0xd204eb02c183815a 0xdfcff03c38383fff 0xfdfcff03c38383ff

def z919 : W := mkw 0x90010b5305452a50 0x090010b5305452a5 0xee2b0ff307273ffb 0xfee2b0ff307273ff

def z920 : W := mkw 0xd1b3cfd3a7c52a53 0x0d1b3cfd3a7c52a5 0xa0338fc3c7c70000 0x0a0338fc3c7c7000

def z921 : W := mkw 0x204eb02c183a95a6 0xf204eb02c183a95a 0xffdff03c3cffffff 0xfffdff03c3cfffff

def z922 : W := mkw 0x204c302c183815a4 0xd204c302c183815a 0x5fcc703c38203ff2 0xf5fcc703c38203ff

def z923 : W := mkw 0x08000845444c63c0 0x008000845444c63c 0xfe1c88cfc4fce7cf 0xdfe1c88cfc4fce7c

def z924 : W := mkw 0x2000302c080815a0 0x92000302c080815a 0x09c0703c38003ff2 0xf09c0703c38003ff

def z925 : W := mkw 0xc1b05dc02fc03e01 0x1c1b05dc02fc03e0 0xbdf0ffc3ffc03f07 0x7bdf0ffc3ffc03f0

def z926 : W := mkw 0xc1005dc02fc03e01 0x1c1005dc02fc03e0 0x1dc07fc03fc03f07 0x71dc07fc03fc03f0

def z927 : W := mkw 0x00ffe6bab2b28007 0xe00ffe6bab2b2800 0xfffffffffb3b000f 0xffffffffffb3b000

def z928 : W := mkw 0x004d66ba90300005 0xc004d66ba9030000 0x5fcc7ffff838000f 0xf5fcc7ffff838000

def z929 : W := mkw 0x00b166ba80000001 0x800b166ba8000000 0x08e07fffc0000000 0xf08e07fffc000000

def z930 : W := mkw 0x004d66ba80000005 0x8004d66ba8000000 0x08c87fffc0000000 0xf08c87fffc000000

def z931 : W := mkw 0x90010b1305052850 0x090010b130505285 0xee2b0fffc72738fb 0xfee2b0fffc72738f

def z932 : W := mkw 0x98010b5345456a50 0x098010b5345456a5 0xee2b0ff3c72738fb 0xbee2b0ff3c72738f

def z933 : W := mkw 0x00fe800032b28006 0x600fe800032b2800 0xffff88c03fffc00f 0x5ffff88c03fffc00

def z934 : W := mkw 0xc1b05dc02fc03e01 0x1c1b05dc02fc03e0 0x1dd07fc038c03f07 0x71dd07fc038c03f0

def z935 : W := mkw 0x00fe800032b28006 0x600fe800032b2800 0xe33f80003fffc00f 0x0e33f80003fffc00

def z936 : W := mkw 0x00fea02832b28006 0xe00fea02832b2800 0xfffff8ffffffc00f 0xffffff8ffffffc00

def z937 : W := mkw 0xc1b055c02bc01e01 0x1c1b055c02bc01e0 0x1df077c03bc03f07 0x71df077c03bc03f0

def z938 : W := mkw 0xc1b05dc02fc2be01 0x3c1b05dc02fc2be0 0x3df07fc03fc7ff07 0x73df07fc03fc7ff0

def z939 : W := mkw 0x000166ba80000001 0x8000166ba8000000 0x00007fcfc0000000 0x400007fcfc000000

def z940 : W := mkw 0x204c302c183815a4 0xd204c302c183815a 0xffcc703c3c3c3fff 0xfffcc703c3c3c3ff

def z941 : W := mkw 0xc1b05dc02fc03e01 0x1c1b05dc02fc03e0 0x3df07fc03fc00707 0x43df07fc03fc0070

def z942 : W := mkw 0x204c302c183815a4 0xd204c302c183815a 0x7fec703c3f383fff 0xf7fec703c3f383ff

def z943 : W := mkw 0x0800004440484380 0x0080000444048438 0xf41488cfc0d8e7cd 0xdf41488cfc0d8e7c

def z944 : W := mkw 0xc1b055c02bc01e01 0x1c1b055c02bc01e0 0x09e077c03b001f02 0x609e077c03b001f0

def z945 : W := mkw 0xc1005dc00d403e01 0x1c1005dc00d403e0 0x09c07fc038003f02 0x709c07fc038003f0

def z946 : W := mkw 0x00ffe6ba90300007 0xc00ffe6ba9030000 0xfffffffffcfcc00f 0xffffffffffcfcc00

def z947 : W := mkw 0xc1005dc00d403e01 0x1c1005dc00d403e0 0x11c07fc038003f04 0x711c07fc038003f0

def z948 : W := mkw 0x800019400d403e00 0x1800019400d403e0 0x3df07fc03fc03f07 0x73df07fc03fc03f0

def z949 : W := mkw 0xc1b05dc12fc43e41 0x1c1b05dc12fc43e4 0xfdf4ffcfffc43fcf 0xffdf4ffcfffc43fc

def z950 : W := mkw 0x004c000010300004 0x4004c00001030000 0xffff80003fffc00f 0x0ffff80003fffc00

def z951 : W := mkw 0x00fe800032b28006 0x600fe800032b2800 0xf3ff80003fffc00c 0x0f3ff80003fffc00

def z952 : W := mkw 0x08000845444c63c0 0x008000845444c63c 0xd01488cfc0dce7cc 0xdd01488cfc0dce7c

def z953 : W := mkw 0x00fe800032b28006 0x600fe800032b2800 0xffff80003fffe70f 0x5ffff80003fffe70

def z954 : W := mkw 0x41b054c02ac01601 0x141b054c02ac0160 0x19f077c038c00704 0x619f077c038c0070

def z955 : W := mkw 0x00fe800032b28006 0x600fe800032b2800 0xffff80ccffffc00f 0x4ffff80ccffffc00

def z956 : W := mkw 0x004e800032b28006 0x6004e800032b2800 0xdfcf80003fffc00f 0x0dfcf80003fffc00

def z957 : W := mkw 0x00fe800032b28006 0x600fe800032b2800 0xffff800c3fffc00f 0xdffff800c3fffc00

def z958 : W := mkw 0x00b3c69280000003 0x000b3c6928000000 0xfcf7ffcfc0000000 0xffcf7ffcfc000000

def z959 : W := mkw 0x00b1469200000001 0x000b146920000000 0xfcffffffc0000000 0xffcffffffc000000

def z960 : W := mkw 0x90010b5305452a50 0x090010b5305452a5 0xfe3f8fffc7e73fff 0xffe3f8fffc7e73ff

def z961 : W := mkw 0x90010b1305052850 0x090010b130505285 0xee2f8f3fc72738fb 0xbee2f8f3fc72738f

def z962 : W := mkw 0x00ffe6ba80000007 0x800ffe6ba8000000 0xbcf7ffcfc0000000 0x7bcf7ffcfc000000

def z963 : W := mkw 0x000166ba80000001 0x8000166ba8000000 0xe4007fffc0000000 0xfe4007fffc000000

def z964 : W := mkw 0xc90019454d4c7fc0 0x1c90019454d4c7fc 0x0000000000003fc0 0x00000000000003fc

def z965 : W := mkw 0x00ffe6ba80000007 0x800ffe6ba8000000 0xfeffffffc3230002 0xffeffffffc323000

def z966 : W := mkw 0x10ffe6ba80010017 0x810ffe6ba8001001 0xfeffffffc0230030 0xffeffffffc023003

def z967 : W := mkw 0x00ffe6baa2800007 0x800ffe6baa280000 0xffffffffffe7000f 0xfffffffffffe7000

def z968 : W := mkw 0x08000845444c63c0 0x008000845444c63c 0xf61488cfc7ffe7cf 0xdf61488cfc7ffe7c

def z969 : W := mkw 0xc10019402fc03e00 0x1c10019402fc03e0 0x3de07f003fc03f07 0x73de07f003fc03f0

def z970 : W := mkw 0x20fea02832b28026 0xe20fea02832b2802 0xffff80303fffc03f 0x0ffff80303fffc03

def z971 : W := mkw 0x204c302c080815a4 0x9204c302c080815a 0x5dcc703c38003ff7 0xf5dcc703c38003ff

def z972 : W := mkw 0xc1b05dc12fc43e41 0x1c1b05dc12fc43e4 0x3df07fc03fc43fcf 0x73df07fc03fc43fc

def z973 : W := mkw 0x000166ba80000001 0x8000166ba8000000 0xa010ffffc0000000 0xfa010ffffc000000

def z974 : W := mkw 0x90010b1305052850 0x090010b130505285 0x2e2b0f33072338f3 0xb2e2b0f33072338f

def z975 : W := mkw 0x084fa23fd03ec1c6 0xe084fa23fd03ec1c 0xc20f803fc03fc0c8 0x8c20f803fc03fc0c

def z976 : W := mkw 0x00ffe6ba80000007 0x800ffe6ba8000000 0x18ffffffc0000000 0xf18ffffffc000000

def z977 : W := mkw 0x00ffe6bab2b28007 0xe00ffe6bab2b2800 0xffffffcfffffc00f 0x4ffffffcfffffc00

def z978 : W := mkw 0xc1b2ddc02fc2be03 0x3c1b2ddc02fc2be0 0x3df0ffc03fc0ff07 0x73df0ffc03fc0ff0

def z979 : W := mkw 0x0000000032b28000 0x60000000032b2800 0xff3f80003fffc00f 0x0ff3f80003fffc00

def z980 : W := mkw 0x90010b1305052850 0x090010b130505285 0xee2b0f3307fff8ff 0xbee2b0f3307fff8f

def z981 : W := mkw 0x00fee4a8b2b28007 0xe00fee4a8b2b2800 0xfffff0fcffffc00f 0xffffff0fcffffc00

def z982 : W := mkw 0x00ffe6ba80000007 0x800ffe6ba8000000 0xf4d4ffffc0000000 0xff4d4ffffc000000

def z983 : W := mkw 0x9001031301050850 0x0900103130105085 0xee2b0733072718fb 0xaee2b0733072718f

def z984 : W := mkw 0x00b3e6ba80000003 0x800b3e6ba8000000 0xbcf3ffffc0000000 0xfbcf3ffffc000000

def z985 : W := mkw 0x08000845444c63c0 0x008000845444c63c 0xf41488cfc4dcc70d 0x4f41488cfc4dcc70

def z986 : W := mkw 0x00ffe6ba80000007 0x800ffe6ba8000000 0xa8fbffffc0000000 0xfa8fbffffc000000

def z987 : W := mkw 0x304fa23f103f81f6 0xe304fa23f103f81f 0xc20f803f003fc0f8 0x8c20f803f003fc0f

def z988 : W := mkw 0x00ffe6ba80000007 0x800ffe6ba8000000 0xe8ffffffc0000000 0xae8ffffffc000000

def z989 : W := mkw 0xc9b2ddc16fc6fe43 0x3c9b2ddc16fc6fe4 0xbdf3ffc3ffc7ff07 0x7bdf3ffc3ffc7ff0

def z990 : W := mkw 0x00ffe6bab2b28007 0xe00ffe6bab2b2800 0xfffffffffbfbc006 0xffffffffffbfbc00

def z991 : W := mkw 0xc1b055c02bc01e01 0x1c1b055c02bc01e0 0x11d077c038c01f04 0x611d077c038c01f0

def z992 : W := mkw 0x004d66ba80000005 0x8004d66ba8000000 0x10c47fffc0000000 0xf10c47fffc000000

def z993 : W := mkw 0x0000000032b28000 0x60000000032b2800 0xa32300003fffc00f 0x0a32300003fffc00

def z994 : W := mkw 0x304d223e103901b4 0xc304d223e103901b 0x420f003c003b00f8 0x8420f003c003b00f

def z995 : W := mkw 0x204c302c183815a4 0xd204c302c183815a 0x13c4703c38383fff 0xf13c4703c38383ff

def z996 : W := mkw 0x00b166ba80000001 0x800b166ba8000000 0xfcf4ffffc0000000 0xffcf4ffffc000000

def z997 : W := mkw 0x00fe800032b28006 0x600fe800032b2800 0xffff8f003fffc00f 0x3ffff8f003fffc00

def z998 : W := mkw 0x004d66ba80000005 0x8004d66ba8000000 0xfcdcffffc0000000 0xffcdcffffc000000

def z999 : W := mkw 0x004c302808001404 0x9004c30280800140 0x5fcc703c38203fff 0xf5fcc703c38203ff

def z1000 : W := mkw 0x00fe800032b28006 0x600fe800032b2800 0xfffff0003fffc00f 0x7fffff0003fffc00

def z1001 : W := mkw 0x204c302c183815a4 0xd204c302c183815a 0xfffff03c3fffffff 0xffffff03c3ffffff

def z1002 : W := mkw 0x000166ba80000001 0x8000166ba8000000 0xee2b7fffc727000b 0xfee2b7fffc727000

def z1003 : W := mkw 0x90010b1305052850 0x090010b130505285 0xfe2f0f33073f38ff 0xbfe2f0f33073f38f

def z1004 : W := mkw 0x00ffe6ba80000007 0x800ffe6ba8000000 0xfeffffffc0201832 0xffeffffffc020183

def z1005 : W := mkw 0x9001031201010810 0x0900103120101081 0x4a2b0730032318fa 0xa4a2b0730032318f

def z1006 : W := mkw 0x00ffe6ba90328007 0xe00ffe6ba9032800 0xfffffffff83fc00f 0xffffffffff83fc00

def z1007 : W := mkw 0x000166ba80000001 0x8000166ba8000000 0x00007fffc00038f0 0xf00007fffc00038f

def z1008 : W := mkw 0x90010b1305052850 0x090010b130505285 0x4e2b0f33032338fb 0xb4e2b0f33032338f

def z1009 : W := mkw 0x204fa23e903801a6 0xc204fa23e903801a 0x420f003c003800f8 0x8420f003c003800f

def z1010 : W := mkw 0x00ffe6ba80000007 0x800ffe6ba8000000 0xfcffffffc7070000 0xffcffffffc707000

def z1011 : W := mkw 0x00b0448000000001 0x000b044800000000 0x3cf07fcfc0000000 0xf3cf07fcfc000000

def z1012 : W := mkw 0x90010b1305052850 0x090010b130505285 0xfeeb7f33072738fb 0xffeeb7f33072738f

def z1013 : W := mkw 0x88000945454c6bc0 0x088000945454c6bc 0xf41488cfc7dcffcf 0xdf41488cfc7dcffc

def z1014 : W := mkw 0x204c302c183815a4 0xd204c302c183815a 0x7fdc78fc38383fff 0xf7fdc78fc38383ff

def z1015 : W := mkw 0xc1b2ddc02fc03e03 0x1c1b2ddc02fc03e0 0xbdf3ffc03fc03f07 0x7bdf3ffc03fc03f0

def z1016 : W := mkw 0x00b166ba80000001 0x800b166ba8000000 0x10d07fffc0000000 0xf10d07fffc000000

def z1017 : W := mkw 0x204c302c183815a4 0xd204c302c183815a 0x53cc703c38383ffc 0xf53cc703c38383ff

def z1018 : W := mkw 0x00fec48032b28007 0x600fec48032b2800 0xffff8fc03fffc00f 0x0ffff8fc03fffc00

def z1019 : W := mkw 0x80b05d800d003c01 0x180b05d800d003c0 0x3df07fc03f003f07 0x73df07fc03f003f0

def z1020 : W := mkw 0x98010b5345456a50 0x098010b5345456a5 0xfe3f8ff3c7fff8ff 0xbfe3f8ff3c7fff8f

def z1021 : W := mkw 0x00b3e6ba80000003 0x800b3e6ba8000000 0x00237fffc0000000 0xf00237fffc000000

def z1022 : W := mkw 0x00fec48032b28007 0x600fec48032b2800 0xfffff0c03fffc00f 0x4fffff0c03fffc00

def z1023 : W := mkw 0x00b3e6ba80000003 0x800b3e6ba8000000 0xec3bffffc0000000 0xfec3bffffc000000

def z1024 : W := mkw 0x004c100018301404 0x5004c10001830140 0x5fcc703038383fff 0xf5fcc703038383ff

def z1025 : W := mkw 0x88000945454c6bc0 0x088000945454c6bc 0xf4348fcfc7dce7cd 0xdf4348fcfc7dce7c

def z1026 : W := mkw 0x00fc64a800000005 0x800fc64a80000000 0xfcfcffffc0000000 0xffcfcffffc000000

def z1027 : W := mkw 0x00ffe6ba80000007 0x800ffe6ba8000000 0xfeffffffc72738fb 0xffeffffffc72738f

def z1028 : W := mkw 0x204c302c183815a4 0xd204c302c183815a 0xdfccf03c383cffff 0xfdfccf03c383cfff

def z1029 : W := mkw 0x00fe800032b28006 0x600fe800032b2800 0xffff80303fffd83f 0x2ffff80303fffd83

def z1030 : W := mkw 0x2000302c080815a0 0x92000302c080815a 0x11c0703c38003ff4 0xf11c0703c38003ff

def z1031 : W := mkw 0x204c302c183815a4 0xd204c302c183815a 0x7fdc703c3cf83fff 0xf7fdc703c3cf83ff

def z1032 : W := mkw 0x00ffe6baa2800007 0x800ffe6baa280000 0xfcffffffc7c00000 0xffcffffffc7c0000

def z1033 : W := mkw 0x00fe800032b28006 0x600fe800032b2800 0xffff88033fffc00f 0x9ffff88033fffc00

def z1034 : W := mkw 0x00ffe6ba90300007 0xc00ffe6ba9030000 0xfdfffffff8180004 0xffdfffffff818000

def z1035 : W := mkw 0x00ffe6ba80000007 0x800ffe6ba8000000 0xfcffffffc4040009 0xffcffffffc404000

def z1036 : W := mkw 0xc9b05dc16fc47e41 0x1c9b05dc16fc47e4 0xfdf4ffc3ffdcff0f 0x7fdf4ffc3ffdcff0

def z1037 : W := mkw 0x9001031301050850 0x0900103130105085 0x0a2b0733032318f2 0xa0a2b0733032318f

def z1038 : W := mkw 0x00ffe6bab2b28007 0xe00ffe6bab2b2800 0xfffffffffffff8ff 0xffffffffffffff8f

def z1039 : W := mkw 0x204c302c183815a4 0xd204c302c183815a 0x5fcc703c3f3f3fff 0xf5fcc703c3f3f3ff

def z1040 : W := mkw 0x08000845444c63c0 0x008000845444c63c 0x101488cfc0d8c704 0x4101488cfc0d8c70

def z1041 : W := mkw 0x08000845444c63c0 0x008000845444c63c 0xf01488cfc4dcc7cc 0xcf01488cfc4dcc7c

def z1042 : W := mkw 0x00ffe6bab2b28007 0xe00ffe6bab2b2800 0xb1f7ffcfffdfc004 0x4b1f7ffcfffdfc00

def z1043 : W := mkw 0xc100558009001c01 0x1c100558009001c0 0x1dc0770038003f07 0x71dc0770038003f0

def z1044 : W := mkw 0xd1b05dc02fc13e11 0x1d1b05dc02fc13e1 0x3ff07fc03fe33f37 0x73ff07fc03fe33f3

def z1045 : W := mkw 0x00ffe6baa2828007 0xa00ffe6baa282800 0xfeffffffc7e7c00b 0xffeffffffc7e7c00

def z1046 : W := mkw 0x00fec480b2b28007 0x600fec480b2b2800 0xffff80c0ffffc00f 0x0ffff80c0ffffc00

def z1047 : W := mkw 0x004fe6ba80000007 0x8004fe6ba8000000 0xec2fffffc0000000 0xfec2fffffc000000

def z1048 : W := mkw 0x00ffe6ba90328007 0xe00ffe6ba9032800 0xfcffffffc018c000 0xffcffffffc018c00

def z1049 : W := mkw 0x9001031201010810 0x0900103120101081 0xee2b0f33032338fb 0xbee2b0f33032338f

def z1050 : W := mkw 0x00ffe6bab2b28007 0xe00ffe6bab2b2800 0xfdfffffffcdcc00d 0xffdfffffffcdcc00

def z1051 : W := mkw 0x00ffe6ba90300007 0xc00ffe6ba9030000 0xfffffffff83838ff 0xffffffffff83838f

def z1052 : W := mkw 0x88000945454c6bc0 0x088000945454c6bc 0xfe3f8fcfc7ffffcf 0xffe3f8fcfc7ffffc

def z1053 : W := mkw 0x90010b1305052850 0x090010b130505285 0xaa2b0f33072738fb 0x2aa2b0f33072738f

def z1054 : W := mkw 0x284c302c583855a4 0xd284c302c583855a 0x5fccf03cf838ffff 0xf5fccf03cf838fff

def z1055 : W := mkw 0x00b3e6ba80000003 0x800b3e6ba8000000 0xf437ffffc0000000 0xff437ffffc000000

def z1056 : W := mkw 0x00b0548008001401 0x100b054800800140 0x1de0770038003f07 0x71de0770038003f0

def z1057 : W := mkw 0x00fec48032b28007 0x600fec48032b2800 0xfffff7003fffc00f 0x2fffff7003fffc00

def z1058 : W := mkw 0xc1005dc00d403e01 0x1c1005dc00d403e0 0x3de07fc03f003f07 0x73de07fc03f003f0

def z1059 : W := mkw 0x20ffe6ba90300027 0xc20ffe6ba9030002 0xfeffffffc0200030 0xffeffffffc020003

def z1060 : W := mkw 0x08000845444c63c0 0x008000845444c63c 0xfc348fcfc4dce7cd 0xffc348fcfc4dce7c

def z1061 : W := mkw 0x90010b1305052850 0x090010b130505285 0x0a2b0f33072738fb 0xb0a2b0f33072738f

def z1062 : W := mkw 0x0000084004402200 0x0000008400440220 0xf41488cfc4dce70d 0xdf41488cfc4dce70

def z1063 : W := mkw 0xc1b2ddc02fc2be03 0x3c1b2ddc02fc2be0 0x3df37fc03fc33f07 0x73df37fc03fc33f0

def z1064 : W := mkw 0xc1b055802b801c01 0x1c1b055802b801c0 0x3df07fc03b003f07 0x73df07fc03b003f0

def z1065 : W := mkw 0x90010b5305452a50 0x090010b5305452a5 0xfe3f8ff307ffffff 0xffe3f8ff307fffff

def z1066 : W := mkw 0x004c000032b28004 0x6004c000032b2800 0xffef00003fffc00f 0x0ffef00003fffc00

def z1067 : W := mkw 0xc1b05dc00d403e01 0x1c1b05dc00d403e0 0x3df07fc038003f07 0x73df07fc038003f0

def z1068 : W := mkw 0x00ffe6ba80000007 0x800ffe6ba8000000 0xfeffffffc020000b 0xffeffffffc020000

def z1069 : W := mkw 0x00fe800032b28006 0x600fe800032b2800 0xffff80303fffc0ff 0x8ffff80303fffc0f

def z1070 : W := mkw 0x000166ba80000001 0x8000166ba8000000 0x2c207fffc0000000 0xf2c207fffc000000

def z1071 : W := mkw 0x90010b1305052850 0x090010b130505285 0xee2f8f33073ff8fb 0xbee2f8f33073ff8f

def z1072 : W := mkw 0x1001121308051450 0x1100112130805145 0xdfcb703338273fff 0xfdfcb703338273ff

def z1073 : W := mkw 0x00ffe6ba80000007 0x800ffe6ba8000000 0x5cef7fffc0000000 0xf5cef7fffc000000

def z1074 : W := mkw 0x00ffe6baa2828007 0xa00ffe6baa282800 0xfcffffffc3030000 0xffcffffffc303000

def z1075 : W := mkw 0x08000045404c43c0 0x008000045404c43c 0x901480cfc0dcc704 0x4901480cfc0dcc70

def z1076 : W := mkw 0x2000302c080815a0 0x92000302c080815a 0x5fc8703c38203fff 0xf5fc8703c38203ff

def z1077 : W := mkw 0x98010b5345456a50 0x098010b5345456a5 0xee2b0f3307e7f8fb 0xbee2b0f3307e7f8f

def z1078 : W := mkw 0x204c302c183815a4 0xd204c302c183815a 0x7fec7f3c38383fff 0xf7fec7f3c38383ff

def z1079 : W := mkw 0xc1b05dc02fc03e01 0x1c1b05dc02fc03e0 0x2de07f003fc03f07 0x32de07f003fc03f0

def z1080 : W := mkw 0x004fe6ba80000007 0x8004fe6ba8000000 0x000b7fffc0000000 0xf000b7fffc000000

def z1081 : W := mkw 0x000166ba80000001 0x8000166ba8000000 0xc00b7fffc0000000 0xfc00b7fffc000000

def z1082 : W := mkw 0x90010b1305052850 0x090010b130505285 0xca2b0733072738fb 0xaca2b0733072738f

def z1083 : W := mkw 0xc1b055c02bc01e01 0x1c1b055c02bc01e0 0x3df07fc03bc01f06 0x73df07fc03bc01f0

def z1084 : W := mkw 0x00ffe6ba80000007 0x800ffe6ba8000000 0xb0f7ffffc0000000 0xfb0f7ffffc000000

def z1085 : W := mkw 0xd1b05dc12fc53e51 0x1d1b05dc12fc53e5 0x7ff87ff03fe73fff 0xf7ff87ff03fe73ff

def z1086 : W := mkw 0x0800004440484380 0x0080000444048438 0x101488cfc0d8c704 0xd101488cfc0d8c70

def z1087 : W := mkw 0x90010b1305052850 0x090010b130505285 0xfe2b0f3307273fff 0xffe2b0f3307273ff

def z1088 : W := mkw 0x00ffe6bab2b28007 0xe00ffe6bab2b2800 0xfffffffff8f8c00f 0xffffffffff8f8c00

def z1089 : W := mkw 0x204c302c183815a4 0xd204c302c183815a 0x0bc8703c38383fff 0xf0bc8703c38383ff

def z1090 : W := mkw 0x08000845444c63c0 0x008000845444c63c 0x101488cfc4dce7cd 0xd101488cfc4dce7c

def z1091 : W := mkw 0x204c302c183815a4 0xd204c302c183815a 0x4bcc703c38383fff 0xa4bcc703c38383ff

def z1092 : W := mkw 0x204c302c183815a4 0xd204c302c183815a 0x5fcc78fff8383fff 0xf5fcc78fff8383ff

def z1093 : W := mkw 0xc1b05dc12fc43e41 0x1c1b05dc12fc43e4 0xfdf4ffc33fdcffcf 0xffdf4ffc33fdcffc

def z1094 : W := mkw 0x00fe800032b28006 0x600fe800032b2800 0xffff88c3ffffc00f 0x0ffff88c3ffffc00

def z1095 : W := mkw 0x004d66ba80000005 0x8004d66ba8000000 0x400c7fffc0000000 0xf400c7fffc000000

def z1096 : W := mkw 0xc1b05dc02fc03e01 0x1c1b05dc02fc03e0 0x3df4ffccffc03f07 0x73df4ffccffc03f0

def z1097 : W := mkw 0x00fe800032b28006 0x600fe800032b2800 0x3ffb00003fffc00f 0x03ffb00003fffc00

def z1098 : W := mkw 0x00b0000032b28000 0x600b0000032b2800 0xfffb00003fffc00f 0x0fffb00003fffc00

def z1099 : W := mkw 0xc1b05dc12fc43e41 0x1c1b05dc12fc43e4 0xfff87ff33fe43fff 0xffff87ff33fe43ff

def z1100 : W := mkw 0x08000845444c63c0 0x008000845444c63c 0xf61c88ffc4fce7fd 0xdf61c88ffc4fce7f

def z1101 : W := mkw 0x00ffe6ba80000007 0x800ffe6ba8000000 0x3cf4ffffc0000000 0xf3cf4ffffc000000

def z1102 : W := mkw 0xc1b055c02bc01e01 0x1c1b055c02bc01e0 0x3df077c03fc01f07 0x63df077c03fc01f0

def z1103 : W := mkw 0xc1b05dc02fc03e01 0x1c1b05dc02fc03e0 0x3df07fc03fdcff0f 0x73df07fc03fdcff0

def z1104 : W := mkw 0xc1005dc00d403e01 0x1c1005dc00d403e0 0x3dd07fc03cc03f07 0x73dd07fc03cc03f0

def z1105 : W := mkw 0x00fee4a8b2b28007 0xe00fee4a8b2b2800 0xffffffccffffc00f 0x7ffffffccffffc00

def z1106 : W := mkw 0x90010b1305052850 0x090010b130505285 0xfe2f0f3f072738fb 0xffe2f0f3f072738f

def z1107 : W := mkw 0x00ffe6ba80000007 0x800ffe6ba8000000 0xb8ffffffc0000000 0x6b8ffffffc000000

def z1108 : W := mkw 0x000166ba80000001 0x8000166ba8000000 0x4e087fffc02038fb 0xf4e087fffc02038f

def z1109 : W := mkw 0x00fe800032b28006 0x600fe800032b2800 0xcbef80003fffc00f 0x0cbef80003fffc00

def z1110 : W := mkw 0x0001021200000000 0x0000102120000000 0xee2b0f33072738fb 0xbee2b0f33072738f

def z1111 : W := mkw 0x204c302c183815a4 0xd204c302c183815a 0x1fc8703c38203ff7 0xf1fc8703c38203ff

def z1112 : W := mkw 0x08000845444c63c0 0x008000845444c63c 0xb41488cfc4dce705 0x5b41488cfc4dce70

def z1113 : W := mkw 0x204c302c183815a4 0xd204c302c183815a 0x5fdcf03c38f8ffff 0xf5fdcf03c38f8fff

def z1114 : W := mkw 0x00fe800032b28006 0x600fe800032b2800 0xffff800fffffc00f 0x8ffff800fffffc00

def z1115 : W := mkw 0x0000100408081580 0x1000010040808158 0x5fcc703c38383fff 0xf5fcc703c38383ff

def z1116 : W := mkw 0xc90019457ffeffc0 0x7c90019457ffeffc 0x030000003fffffcf 0x0030000003fffffc

def z1117 : W := mkw 0x98010b5345456a50 0x098010b5345456a5 0xfe3b8ff3c7e7ffff 0xffe3b8ff3c7e7fff

def z1118 : W := mkw 0x98010b1345056850 0x098010b134505685 0xee2b8f33c727f8fb 0xbee2b8f33c727f8f

def z1119 : W := mkw 0x08000845444c63c0 0x008000845444c63c 0xe01488cfc4dce7cd 0x8e01488cfc4dce7c

def z1120 : W := mkw 0x204c302c183815a4 0xd204c302c183815a 0x1bcc703c38383fff 0x61bcc703c38383ff

def z1121 : W := mkw 0xd1b14fd327c52a51 0x0d1b14fd327c52a5 0x20300fc307c00000 0x020300fc307c0000

def z1122 : W := mkw 0x204eb02c183a95a6 0xf204eb02c183a95a 0x5fcf703c383b3fff 0xf5fcf703c383b3ff

def z1123 : W := mkw 0xc1b05dc02fc03e01 0x1c1b05dc02fc03e0 0x7df47fc03fd83f0f 0x77df47fc03fd83f0

def z1124 : W := mkw 0x98010b5345456a50 0x098010b5345456a5 0xfe3f8fffc7e7f8fb 0xffe3f8fffc7e7f8f

def z1125 : W := mkw 0x00ffe6ba80000007 0x800ffe6ba8000000 0xfcffffcfc0000000 0x4fcffffcfc000000

def z1126 : W := mkw 0x00b3e6ba80000003 0x800b3e6ba8000000 0xa033ffcfc0000000 0x4a033ffcfc000000

def z1127 : W := mkw 0x004fe6ba80000007 0x8004fe6ba8000000 0xf41fffffc0000000 0xff41fffffc000000

def z1128 : W := mkw 0xc1b05dc02fc03e01 0x1c1b05dc02fc03e0 0x1de077003fc03f07 0x71de077003fc03f0

def z1129 : W := mkw 0x00ffe6ba80028007 0xa00ffe6ba8002800 0xfcffffffc007c000 0xffcffffffc007c00

def z1130 : W := mkw 0x204c302c183815a4 0xd204c302c183815a 0x53cc703c38383fff 0xc53cc703c38383ff

def z1131 : W := mkw 0xc1b05dc02fc03e01 0x1c1b05dc02fc03e0 0xfdf07fc33fc03f07 0xffdf07fc33fc03f0

def z1132 : W := mkw 0x0003e6ba80000003 0x80003e6ba8000000 0x8003ffffc0000000 0xf8003ffffc000000

def z1133 : W := mkw 0x00fea02832b28006 0xe00fea02832b2800 0xfffff0303fffc00f 0x2fffff0303fffc00

def z1134 : W := mkw 0xc1b055802b801c01 0x1c1b055802b801c0 0x09e077003b003f02 0x709e077003b003f0

def z1135 : W := mkw 0xc1b2ddc0afc03e03 0x1c1b2ddc0afc03e0 0x3df0ffc0ffc03f07 0x73df0ffc0ffc03f0

def z1136 : W := mkw 0x08000845444c63c0 0x008000845444c63c 0x541488cfc0d8e7cd 0xd541488cfc0d8e7c

def z1137 : W := mkw 0x000166ba80000001 0x8000166ba8000000 0x34107fffc0000000 0xf34107fffc000000

def z1138 : W := mkw 0x204c302c183815a4 0xd204c302c183815a 0x5dcc703c38183ff4 0xf5dcc703c38183ff

def z1139 : W := mkw 0xc1b055802b801c01 0x1c1b055802b801c0 0x09e077003b003f07 0x209e077003b003f0

def z1140 : W := mkw 0x00fee4a8b2b28007 0xe00fee4a8b2b2800 0xfffff8cfffffc00f 0xdfffff8cfffffc00

def z1141 : W := mkw 0x08000845444c63c0 0x008000845444c63c 0xfc3f88cfc4dce7cd 0xdfc3f88cfc4dce7c

def z1142 : W := mkw 0x204c302c183815a4 0xd204c302c183815a 0xffef703c38383fff 0xfffef703c38383ff

def z1143 : W := mkw 0x204fa23e903801a6 0xc204fa23e903801a 0xc00f803fc0180000 0x8c00f803fc018000

def z1144 : W := mkw 0x004fe6ba80000007 0x8004fe6ba8000000 0x0004ffffc0000000 0xf0004ffffc000000

def z1145 : W := mkw 0x8000090005002800 0x0800009000500280 0xee2b0f30072738fb 0xbee2b0f30072738f

def z1146 : W := mkw 0x00ffe6ba80000007 0x800ffe6ba8000000 0xeceb7fffc0000000 0xfeceb7fffc000000

def z1147 : W := mkw 0x00ffe6ba80000007 0x800ffe6ba8000000 0xfcffffffc4c4c000 0xffcffffffc4c4c00

def z1148 : W := mkw 0x00b2800032b28002 0x600b2800032b2800 0xa13380003fdfc004 0x0a13380003fdfc00

def z1149 : W := mkw 0x90010b5305452a50 0x090010b5305452a5 0xee3b0ff307e738fb 0xbee3b0ff307e738f

def z1150 : W := mkw 0x08000845444c63c0 0x008000845444c63c 0xfc1488cfc4dcffcf 0xffc1488cfc4dcffc

def z1151 : W := mkw 0x2000302c080815a0 0x92000302c080815a 0x5dc4703c38183fff 0xf5dc4703c38183ff

def z1152 : W := mkw 0x90010b1305052850 0x090010b130505285 0xffeb0f333f2738ff 0xbffeb0f333f2738f

def z1153 : W := mkw 0xc1b055c02bc01e01 0x1c1b055c02bc01e0 0x09e077003bc01f06 0x209e077003bc01f0

def z1154 : W := mkw 0x204c302c183815a4 0xd204c302c183815a 0xffcc783f38383fff 0xfffcc783f38383ff

def z1155 : W := mkw 0x00ffe6bab2b28007 0xe00ffe6bab2b2800 0xfeffffffc7ffc008 0xffeffffffc7ffc00

def z1156 : W := mkw 0x00fea02832b28006 0xe00fea02832b2800 0xffff803c3fffc00f 0x8ffff803c3fffc00

def z1157 : W := mkw 0x00ffe6bab2b28007 0xe00ffe6bab2b2800 0x0beb7ffffb230002 0xf0beb7ffffb23000

def z1158 : W := mkw 0x00b05cc00c403601 0x100b05cc00c40360 0x3df07fc03cc03f07 0x73df07fc03cc03f0

def z1159 : W := mkw 0xc1b05dc02fc03e01 0x1c1b05dc02fc03e0 0xffffffc03fffff0f 0x7ffffffc03fffff0

def z1160 : W := mkw 0x00fe800032b28006 0x600fe800032b2800 0xd3df80003fffc00f 0x0d3df80003fffc00

def z1161 : W := mkw 0x41b054c02ac01601 0x141b054c02ac0160 0x31f07fc038c00704 0x431f07fc038c0070

def z1162 : W := mkw 0x00b3e6ba80000003 0x800b3e6ba8000000 0x0010ffffc0000000 0xf0010ffffc000000

def z1163 : W := mkw 0x00ffe6ba80000007 0x800ffe6ba8000000 0xfeffffffc7ffc00f 0xffeffffffc7ffc00

def z1164 : W := mkw 0x384d223f503d41f4 0xc384d223f503d41f 0xc20f803fc03fc0f8 0x8c20f803fc03fc0f

def z1165 : W := mkw 0x00ffe6ba80000007 0x800ffe6ba8000000 0xf4f7ffcfc0000000 0xdf4f7ffcfc000000

def z1166 : W := mkw 0x08000845444c63c0 0x008000845444c63c 0xb01488cfc4dce7c4 0xdb01488cfc4dce7c

def z1167 : W := mkw 0x08000845444c63c0 0x008000845444c63c 0xf43788cfc7dfe7cd 0xdf43788cfc7dfe7c

def z1168 : W := mkw 0x204c302c183815a4 0xd204c302c183815a 0x5fef703c3b3b3fff 0xf5fef703c3b3b3ff

def z1169 : W := mkw 0xb80019455d7d7ff0 0x5b80019455d7d7ff 0x030000003fffffff 0x0030000003ffffff

def z1170 : W := mkw 0x00ffe6bab2b28007 0xe00ffe6bab2b2800 0xffffffffff27000b 0xfffffffffff27000

def z1171 : W := mkw 0x00ffe6ba80000007 0x800ffe6ba8000000 0xfcffffffc01cc008 0xffcffffffc01cc00

def z1172 : W := mkw 0x204c302c183815a4 0xd204c302c183815a 0x1dc4703c38183ff7 0xf1dc4703c38183ff

def z1173 : W := mkw 0x00ffe6baa2800007 0x800ffe6baa280000 0xfdfffffffb000002 0xffdfffffffb00000

def z1174 : W := mkw 0xc1b05dc02fc03e01 0x1c1b05dc02fc03e0 0x3df07fc03b003f02 0x73df07fc03b003f0

def z1175 : W := mkw 0x00fe800032b28006 0x600fe800032b2800 0xbdf780003fdfc007 0x0bdf780003fdfc00

def z1176 : W := mkw 0xc1b05dc02fc03e01 0x1c1b05dc02fc03e0 0x29f07fc03fc03f02 0x729f07fc03fc03f0

def z1177 : W := mkw 0x08000845444c63c0 0x008000845444c63c 0xfe3f88ffc7ffffff 0xffe3f88ffc7fffff

def z1178 : W := mkw 0x204c302c183815a4 0xd204c302c183815a 0x5fcc703c3cfcffff 0xf5fcc703c3cfcfff

def z1179 : W := mkw 0xc1b05dc02fc03e01 0x1c1b05dc02fc03e0 0x31f07fc03fc03f04 0x731f07fc03fc03f0

def z1180 : W := mkw 0x00ffe6ba90300007 0xc00ffe6ba9030000 0xfeffffffc0380008 0xffeffffffc038000

def z1181 : W := mkw 0x284fa23fd03c41e6 0xc284fa23fd03c41e 0xc20f803fc03cc0f8 0x8c20f803fc03cc0f

def z1182 : W := mkw 0xc9fe99457ffeffc6 0x7c9fe99457ffeffc 0xffff80003fffffcf 0x0ffff80003fffffc

def z1183 : W := mkw 0x204c302c183815a4 0xd204c302c183815a 0x1fc8703038383fff 0x71fc8703038383ff

def z1184 : W := mkw 0x000166ba80000001 0x8000166ba8000000 0x082b7fffc0000000 0xf082b7fffc000000

def z1185 : W := mkw 0xc1b05dc02fc03e01 0x1c1b05dc02fc03e0 0x29f07fc03fc03f07 0x229f07fc03fc03f0

def z1186 : W := mkw 0xd1b05dc12fc53e51 0x1d1b05dc12fc53e5 0xfffb7fc03fe73fff 0x7fffb7fc03fe73ff

def z1187 : W := mkw 0x00ffe6ba80000007 0x800ffe6ba8000000 0xc8efffffc0000000 0xfc8efffffc000000

def z1188 : W := mkw 0xc1b05dc02fc03e01 0x1c1b05dc02fc03e0 0x7ff87fc03fe03f0f 0x77ff87fc03fe03f0

def z1189 : W := mkw 0x00ffe6ba80000007 0x800ffe6ba8000000 0xfcffffffc00038f0 0xffcffffffc00038f

def z1190 : W := mkw 0x00fe800032b28006 0x600fe800032b2800 0xffff80003fffe0cf 0x9ffff80003fffe0c

def z1191 : W := mkw 0x00ffe6ba90328007 0xe00ffe6ba9032800 0xfeffffffc0230000 0xffeffffffc023000

def z1192 : W := mkw 0x204c302c183815a4 0xd204c302c183815a 0x1bcc703c38383ff6 0xf1bcc703c38383ff

def z1193 : W := mkw 0xe90019457ffc7fe0 0x5e90019457ffc7fe 0x030000003ffcffff 0x0030000003ffcfff

def z1194 : W := mkw 0x00ffe6baa2800007 0x800ffe6baa280000 0xfdfffffff8c00004 0xffdfffffff8c0000

def z1195 : W := mkw 0x204c302c183815a4 0xd204c302c183815a 0x01c0703c38003ff0 0xf01c0703c38003ff

def z1196 : W := mkw 0xc1b05dc02fc03e01 0x1c1b05dc02fc03e0 0xfdf07fc03fc43f0f 0x7fdf07fc03fc43f0

def z1197 : W := mkw 0x000166ba80000001 0x8000166ba8000000 0xc004ffffc0000000 0xfc004ffffc000000

def z1198 : W := mkw 0x204c302c183a95a4 0xf204c302c183a95a 0x5fcc703c383fffff 0xf5fcc703c383ffff

def z1199 : W := mkw 0x00b2800032b28002 0x600b2800032b2800 0xbff380003fffc00f 0x0bff380003fffc00

def z1200 : W := mkw 0x08000845444c63c0 0x008000845444c63c 0xfc3488cfc7dce7cf 0xdfc3488cfc7dce7c

def z1201 : W := mkw 0x8000110009001c00 0x18000110009001c0 0x1de077003b003f07 0x71de077003b003f0

def z1202 : W := mkw 0x004fe6ba80000007 0x8004fe6ba8000000 0xdccfffffc0000000 0xfdccfffffc000000

def z1203 : W := mkw 0xc1b05dc02fc03e01 0x1c1b05dc02fc03e0 0x19f07fc03bc03f06 0x719f07fc03bc03f0

def z1204 : W := mkw 0x00b2800022828002 0x200b280002282800 0xfdf780003fdfc00f 0x0fdf780003fdfc00

def z1205 : W := mkw 0x00b3e6baa2828003 0xa00b3e6baa282800 0xa033ffffc7c7c000 0xfa033ffffc7c7c00

def z1206 : W := mkw 0x00fe800032b28006 0x600fe800032b2800 0xffff80003ffff80f 0x3ffff80003ffff80

def z1207 : W := mkw 0x00ffe6baa2828007 0xa00ffe6baa282800 0xfcffffffc0c0c000 0xffcffffffc0c0c00

def z1208 : W := mkw 0x9001031201010810 0x0900103120101081 0x0a2b0730032338fb 0x20a2b0730032338f

def z1209 : W := mkw 0x08000845444c63c0 0x008000845444c63c 0xf41488cfc0d8e7c4 0xdf41488cfc0d8e7c

def z1210 : W := mkw 0x00b0000022800000 0x000b000002280000 0xffff80003fffc00f 0x0ffff80003fffc00

def z1211 : W := mkw 0xc1b05dc02fc03e01 0x1c1b05dc02fc03e0 0xfffb7ff03fe73fff 0xffffb7ff03fe73ff

def z1212 : W := mkw 0x80b019002f803c00 0x180b019002f803c0 0x3df07f003fc03f07 0x73df07f003fc03f0

def z1213 : W := mkw 0x0000448000000001 0x0000044800000000 0x00007fcfc0000000 0xf00007fcfc000000

def z1214 : W := mkw 0x9001031301050850 0x0900103130105085 0xee2b0f33032718fa 0xbee2b0f33032718f

def z1215 : W := mkw 0x08000045404c43c0 0x008000045404c43c 0xd41480cfc0dce7cd 0xdd41480cfc0dce7c

def z1216 : W := mkw 0x204c302c183815a4 0xd204c302c183815a 0x4fc8703038383fff 0xb4fc8703038383ff

def z1217 : W := mkw 0x004e800032b28006 0x6004e800032b2800 0xef2f80003fffc00f 0x0ef2f80003fffc00

def z1218 : W := mkw 0xc9b05dc16fc47e41 0x1c9b05dc16fc47e4 0xfdf0ffc3ffc4ffcf 0xffdf0ffc3ffc4ffc

def z1219 : W := mkw 0xd9b14fd367c56a51 0x0d9b14fd367c56a5 0xa0338fc3c7c7c000 0x0a0338fc3c7c7c00

def z1220 : W := mkw 0x000166ba80000001 0x8000166ba8000000 0xfc3fffffc0000000 0xffc3fffffc000000

def z1221 : W := mkw 0x00ffe6ba80000007 0x800ffe6ba8000000 0xe03fffffc0000000 0xfe03fffffc000000

def z1222 : W := mkw 0x00fe800032b28006 0x600fe800032b2800 0xfdff80003fdfc004 0x0fdff80003fdfc00

def z1223 : W := mkw 0x0000100008001400 0x1000010000800140 0x1dc0703038003ff7 0xf1dc0703038003ff

def z1224 : W := mkw 0xc1b05dc02fc03e01 0x1c1b05dc02fc03e0 0x19f077c03fc03f07 0x619f077c03fc03f0

def z1225 : W := mkw 0x90010b1305052850 0x090010b130505285 0xe22b0f33072738fb 0x8e22b0f33072738f

def z1226 : W := mkw 0x00fe800032b28006 0x600fe800032b2800 0xf5f780003fdfc00d 0x0f5f780003fdfc00

def z1227 : W := mkw 0xc1b05dc02fc03e01 0x1c1b05dc02fc03e0 0x3df4ffc03fd8ff07 0x73df4ffc03fd8ff0

def z1228 : W := mkw 0xc1b05dc02fc03e01 0x1c1b05dc02fc03e0 0x3ff87ff03fe03f37 0x73ff87ff03fe03f3

def z1229 : W := mkw 0x204c302c183815a4 0xd204c302c183815a 0x5fdcf0fcf8383fff 0xf5fdcf0fcf8383ff

def z1230 : W := mkw 0xc1b05dc02fc03e01 0x1c1b05dc02fc03e0 0x7df87ff03fc03f07 0xf7df87ff03fc03f0

def z1231 : W := mkw 0x90010b1305052850 0x090010b130505285 0xee2b0f33032338f2 0xbee2b0f33032338f

def z1232 : W := mkw 0x61fef4ec3afa97a7 0xf61fef4ec3afa97a 0x11d4f0cc38d8c704 0x411d4f0cc38d8c70

def z1233 : W := mkw 0x204c302c183815a4 0xd204c302c183815a 0xdfcf703c383f3fff 0xfdfcf703c383f3ff

def z1234 : W := mkw 0xc1b05dc02fc03e01 0x1c1b05dc02fc03e0 0x3ff07fc03fe03fff 0x73ff07fc03fe03ff

def z1235 : W := mkw 0xc1b05dc02fc03e01 0x1c1b05dc02fc03e0 0x3df07fc038c03f04 0x73df07fc038c03f0

def z1236 : W := mkw 0x90010b1305052850 0x090010b130505285 0xaa2b0f33072738f2 0xbaa2b0f33072738f

def z1237 : W := mkw 0xc1b05dc02fc03e01 0x1c1b05dc02fc03e0 0x7df07fc03fc03fcf 0xf7df07fc03fc03fc

def z1238 : W := mkw 0x000166ba80000001 0x8000166ba8000000 0xa0237fffc0000000 0xfa0237fffc000000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z7,z5,z6]),(0,[z8,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z9,z6]),(0,[z0,z1,z3,z4,z5,z6,z10])],[(1,[z11,z12,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z13,z5,z6]),(0,[z14,z1,z3,z4,z5,z15,z6]),(0,[z0,z1,z3,z4,z16,z5,z17])],[(0,[z12,z18,z0,z3,z4,z5,z6]),(0,[z0,z1,z3,z19,z4,z5,z6]),(0,[z0,z1,z3,z19,z5,z20,z6]),(0,[z0,z1,z3,z4,z21,z7,z6]),(0,[z0,z1,z3,z22,z4,z5,z6])],[(0,[z23,z0,z1,z3,z4,z5,z6]),(0,[z24,z0,z1,z25,z4,z5,z6]),(0,[z0,z1,z3,z26,z27,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z28]),(0,[z29,z0,z1,z3,z30,z5,z6]),(0,[z0,z1,z3,z31,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z32,z6]),(0,[z33,z0,z1,z3,z4,z5,z6])],[(1,[z0,z1,z3,z34,z5,z6]),(0,[z0,z35,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z36,z4,z5,z6]),(0,[z37,z0,z1,z3,z4,z5,z6]),(1,[z38,z0,z3,z39,z5,z6]),(0,[z0,z1,z40,z3,z4,z5,z6]),(0,[z41,z0,z1,z3,z4,z5,z42])],[(0,[z11,z23,z1,z3,z4,z5,z6]),(0,[z1,z43,z3,z44,z4,z5,z6]),(0,[z0,z1,z3,z4,z45,z5,z6])],[(0,[z12,z0,z3,z4,z46,z5,z6]),(1,[z0,z47,z3,z4,z5,z6]),(0,[z48,z0,z1,z3,z4,z5,z6]),(0,[z49,z0,z1,z3,z4,z50,z6]),(0,[z51,z0,z1,z3,z4,z5,z6])],[(0,[z52,z12,z0,z3,z4,z5,z6]),(1,[z0,z53,z3,z4,z5,z6]),(0,[z54,z55,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z6,z56]),(1,[z0,z1,z3,z4,z5,z57]),(0,[z0,z1,z3,z58,z4,z5,z6])]],
   [[(0,[z0,z1,z3,z59,z4,z5,z6]),(0,[z0,z1,z3,z4,z60,z5,z6])],[(0,[z0,z1,z3,z61,z4,z5,z6]),(0,[z62,z12,z0,z3,z4,z5,z6]),(0,[z12,z0,z3,z4,z5,z63,z6]),(0,[z64,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z65,z4,z5,z6]),(0,[z0,z1,z66,z3,z4,z5,z6]),(0,[z0,z1,z3,z67,z4,z5,z6]),(0,[z0,z1,z3,z68,z4,z5,z20])],[(0,[z0,z1,z3,z4,z5,z69,z6]),(0,[z0,z1,z3,z4,z5,z6,z70]),(0,[z0,z1,z3,z4,z5,z6,z71]),(0,[z0,z1,z3,z4,z72,z5,z6])],[(0,[z12,z23,z0,z3,z4,z5,z6]),(0,[z73,z0,z43,z3,z4,z5,z6]),(0,[z41,z12,z0,z3,z4,z5,z6]),(1,[z0,z74,z3,z4,z5,z6]),(0,[z24,z0,z75,z3,z4,z5,z6])],[(1,[z76,z1,z3,z4,z5,z6]),(0,[z41,z0,z1,z3,z4,z5,z6]),(0,[z0,z77,z1,z3,z4,z5,z6])],[(0,[z0,z43,z3,z4,z5,z15,z6]),(0,[z14,z11,z1,z3,z4,z5,z6]),(0,[z78,z1,z3,z4,z26,z5,z6]),(0,[z79,z0,z1,z3,z4,z5,z6]),(0,[z80,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z81,z82,z4,z5,z6]),(0,[z0,z1,z3,z83,z46,z5,z6])],[(0,[z84,z0,z1,z3,z4,z5,z6]),(0,[z12,z85,z0,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z86,z6]),(0,[z87,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z88,z6]),(0,[z29,z0,z3,z30,z4,z5,z6]),(0,[z89,z0,z1,z3,z82,z5,z6]),(0,[z0,z1,z3,z4,z5,z90,z91]),(0,[z0,z1,z92,z3,z4,z5,z6])],[(0,[z85,z0,z1,z3,z4,z7,z6]),(0,[z93,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z94,z5,z95]),(0,[z0,z1,z96,z3,z4,z5,z6])]],
   [[(0,[z0,z43,z3,z4,z5,z95,z6]),(0,[z97,z0,z1,z3,z4,z5,z6]),(0,[z98,z0,z1,z3,z4,z5,z6]),(1,[z99,z0,z1,z3,z4,z5])],[(1,[z43,z3,z4,z7,z5,z6]),(0,[z73,z0,z1,z3,z100,z5,z6]),(0,[z101,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z102,z4,z5,z6]),(0,[z0,z1,z3,z103,z4,z5,z6])],[(0,[z0,z43,z3,z4,z5,z50,z6]),(0,[z104,z12,z0,z3,z4,z5,z6]),(0,[z0,z1,z3,z105,z4,z5,z6]),(0,[z106,z0,z1,z3,z4,z5,z6]),(0,[z107,z0,z1,z3,z4,z5,z90])],[(0,[z104,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z108,z5,z6]),(0,[z0,z1,z109,z3,z4,z5,z6]),(0,[z54,z0,z1,z3,z4,z5,z20])],[(0,[z0,z43,z3,z4,z5,z110,z6]),(0,[z0,z1,z3,z4,z111,z5,z6]),(1,[z0,z1,z3,z112,z5,z6])],[(0,[z0,z1,z113,z3,z4,z5,z6]),(0,[z24,z0,z1,z3,z4,z114,z6]),(0,[z18,z0,z1,z3,z4,z5,z115]),(0,[z0,z1,z3,z4,z5,z6,z90]),(0,[z0,z1,z3,z4,z116,z5,z6])],[(0,[z117,z0,z1,z3,z4,z5,z6]),(0,[z118,z0,z1,z3,z4,z5,z6])],[(0,[z119,z0,z1,z25,z4,z5,z6]),(0,[z0,z1,z3,z4,z94,z5,z115]),(0,[z120,z0,z1,z3,z4,z5,z6]),(0,[z73,z0,z1,z3,z4,z121,z6]),(0,[z0,z1,z3,z4,z5,z122,z6])]],
   [[(1,[z78,z1,z3,z26,z5,z6]),(1,[z0,z1,z3,z123,z5,z6]),(0,[z0,z1,z3,z4,z124,z5,z6])],[(0,[z14,z12,z0,z3,z4,z5,z6]),(0,[z12,z0,z3,z68,z4,z5,z6]),(0,[z0,z1,z4,z27,z5,z50,z6]),(0,[z125,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z94,z5,z6]),(0,[z126,z0,z1,z3,z4,z5,z6])],[(0,[z12,z0,z25,z3,z4,z5,z6]),(0,[z24,z0,z74,z3,z4,z5,z6]),(0,[z127,z119,z0,z3,z4,z5,z6]),(0,[z14,z0,z1,z3,z4,z5,z6]),(0,[z73,z0,z1,z36,z4,z5,z6]),(0,[z0,z128,z3,z4,z39,z5,z6]),(0,[z0,z1,z3,z129,z4,z94,z5])],[(0,[z12,z0,z3,z4,z5,z6,z130]),(0,[z131,z0,z1,z3,z4,z5,z6]),(1,[z14,z1,z3,z4,z15,z6]),(0,[z132,z0,z1,z3,z4,z5,z6])],[(0,[z133,z0,z1,z3,z4,z5,z6]),(0,[z80,z0,z1,z3,z134,z5,z6]),(0,[z0,z135,z1,z3,z4,z5,z6]),(1,[z136,z0,z3,z4,z5,z6]),(0,[z136,z0,z1,z3,z4,z5,z6])],[(0,[z0,z43,z3,z4,z137,z5,z6]),(0,[z0,z1,z3,z4,z5,z138,z6]),(1,[z139,z0,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z123,z5,z6]),(0,[z0,z1,z3,z100,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z140])],[(0,[z141,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z142,z4,z5,z6]),(0,[z0,z1,z3,z143,z4,z5,z6])],[(0,[z18,z1,z3,z4,z5,z6,z144])]],
   [[(0,[z11,z119,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z26,z5,z6]),(0,[z0,z1,z3,z4,z5,z145,z6]),(1,[z146,z0,z3,z4,z110,z6]),(0,[z0,z1,z4,z5,z50,z6,z90]),(1,[z41,z0,z1,z3,z17,z6]),(0,[z0,z1,z3,z4,z5,z17,z6])],[(0,[z0,z1,z3,z4,z147,z5,z6]),(0,[z0,z1,z3,z4,z5,z148,z6]),(0,[z149,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z150,z5,z6]),(0,[z151,z0,z1,z3,z4,z5,z6])],[(0,[z0,z43,z152,z3,z4,z5,z6]),(0,[z153,z0,z1,z3,z4,z5,z6]),(0,[z154,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z155,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z156,z5,z6]),(0,[z0,z1,z157,z3,z4,z5,z6])],[(0,[z23,z0,z43,z3,z4,z5,z6]),(0,[z12,z0,z3,z4,z5,z6,z144]),(1,[z158,z1,z3,z4,z5,z6]),(0,[z0,z1,z82,z4,z27,z5,z6]),(0,[z41,z0,z96,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z159]),(0,[z0,z1,z3,z4,z5,z6,z160])],[(0,[z0,z1,z3,z4,z5,z161,z6]),(0,[z12,z78,z0,z3,z4,z5,z6]),(0,[z12,z55,z0,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z162]),(0,[z163,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z164,z6]),(0,[z38,z0,z1,z3,z39,z5,z6]),(0,[z0,z1,z3,z4,z165,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z166]),(0,[z0,z1,z3,z4,z124,z21,z6]),(0,[z0,z1,z3,z4,z5,z167,z6])],[(0,[z168,z0,z1,z3,z19,z5,z6]),(0,[z80,z98,z0,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z169,z5,z6])],[(0,[z0,z1,z3,z170,z4,z5,z6]),(0,[z14,z0,z171,z3,z4,z5,z6]),(0,[z0,z1,z3,z172,z4,z5,z6])]],
   [[(0,[z0,z1,z3,z4,z173,z5,z6])],[(0,[z11,z1,z3,z4,z5,z6,z144]),(0,[z54,z0,z1,z3,z129,z4,z5])],[(0,[z119,z0,z53,z3,z4,z5,z6]),(0,[z174,z0,z1,z3,z4,z5,z6]),(0,[z29,z0,z1,z3,z39,z5,z6]),(0,[z89,z0,z1,z3,z27,z5,z6])],[(0,[z175,z0,z1,z3,z4,z5,z6]),(0,[z176,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z177,z6]),(0,[z0,z1,z3,z4,z5,z178,z6]),(0,[z107,z0,z1,z4,z5,z6,z90])],[(0,[z0,z43,z3,z179,z4,z5,z6]),(0,[z0,z43,z3,z82,z4,z5,z6]),(0,[z41,z0,z43,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z180]),(0,[z0,z1,z181,z3,z4,z5,z6])],[(0,[z80,z0,z43,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z182,z5,z6])],[(0,[z24,z0,z1,z44,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z183,z6]),(0,[z38,z184,z1,z3,z4,z5,z6]),(0,[z185,z0,z1,z3,z4,z5,z6])],[(0,[z29,z0,z43,z3,z4,z5,z6]),(0,[z12,z0,z3,z4,z5,z115,z6]),(1,[z186,z0,z3,z4,z5,z6]),(0,[z139,z85,z0,z3,z4,z5,z6]),(0,[z0,z187,z1,z3,z4,z5,z6]),(0,[z0,z184,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z188,z5,z6]),(0,[z0,z1,z3,z68,z4,z5,z90])]],
   [[(0,[z119,z1,z43,z3,z4,z5,z6]),(0,[z189,z0,z1,z3,z4,z5,z6]),(0,[z190,z0,z1,z3,z4,z5,z6]),(0,[z18,z0,z191,z3,z4,z5,z6]),(0,[z192,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z193,z5,z6])],[(1,[z43,z3,z4,z26,z5,z6]),(0,[z0,z43,z81,z3,z4,z5,z6]),(0,[z0,z43,z3,z129,z4,z5,z6]),(0,[z12,z0,z3,z4,z194,z5,z6]),(0,[z0,z1,z3,z4,z195,z5,z6]),(0,[z196,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z197,z5,z6]),(0,[z0,z1,z3,z198,z4,z5,z6]),(0,[z0,z1,z3,z4,z199,z5,z6]),(0,[z0,z1,z3,z5,z6,z200,z91])],[(0,[z0,z1,z3,z4,z201,z5,z6]),(0,[z202,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z129,z68,z4,z5]),(0,[z0,z1,z203,z4,z204,z5,z6])],[(0,[z205,z0,z1,z3,z4,z5,z6]),(0,[z206,z0,z1,z3,z4,z5,z6]),(0,[z207,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z208,z4,z5,z6]),(0,[z0,z1,z3,z209,z4,z5,z6]),(0,[z0,z1,z3,z34,z4,z5,z6]),(0,[z0,z1,z3,z4,z210,z5,z6]),(0,[z0,z1,z3,z4,z5,z211,z6]),(0,[z0,z1,z212,z3,z4,z5,z6]),(0,[z0,z1,z3,z213,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z144,z90]),(0,[z214,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z83,z4,z46,z6]),(0,[z215,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z94,z5,z130]),(0,[z0,z1,z3,z4,z216,z5,z6])],[(0,[z0,z1,z3,z217,z4,z5,z6]),(1,[z0,z1,z3,z4,z5,z166]),(0,[z0,z1,z3,z4,z218,z5,z6])],[(0,[z219,z12,z0,z3,z4,z5,z6]),(0,[z220,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z221]),(0,[z0,z1,z3,z4,z5,z222,z6])]],
   [[(0,[z0,z43,z3,z83,z4,z5,z6]),(0,[z0,z1,z3,z44,z4,z5,z6]),(0,[z0,z1,z3,z4,z223,z5,z6]),(0,[z0,z224,z1,z3,z4,z5,z6]),(0,[z54,z0,z1,z3,z68,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z225]),(0,[z0,z1,z3,z4,z94,z6,z91])],[(0,[z226,z12,z0,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z110,z50,z6]),(0,[z0,z1,z3,z4,z5,z6,z227]),(0,[z0,z1,z81,z3,z4,z228,z6]),(0,[z0,z229,z1,z3,z4,z5,z6]),(0,[z136,z0,z3,z4,z5,z6,z90]),(0,[z54,z0,z1,z3,z4,z5,z90]),(0,[z0,z1,z3,z4,z230,z5,z17])],[(0,[z14,z0,z43,z3,z4,z5,z6]),(0,[z231,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z30,z4,z5,z6]),(0,[z0,z232,z1,z3,z4,z5,z6]),(1,[z0,z1,z4,z5,z233,z6])],[(0,[z0,z43,z3,z4,z39,z5,z6]),(0,[z234,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z235,z5,z6]),(0,[z0,z1,z236,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z4,z5,z6]),(0,[z18,z0,z1,z3,z4,z5,z144]),(0,[z0,z1,z3,z4,z5,z144,z91]),(0,[z237,z0,z1,z3,z4,z5,z6]),(0,[z238,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z239,z5,z6]),(0,[z0,z1,z3,z4,z5,z20,z6]),(0,[z0,z1,z3,z240,z4,z5,z6])],[(0,[z0,z3,z30,z4,z39,z5,z6]),(0,[z0,z1,z241,z3,z4,z5,z6]),(0,[z242,z0,z1,z3,z4,z5,z6]),(0,[z243,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z244,z5,z6]),(0,[z41,z0,z1,z3,z83,z5,z6])],[(0,[z245,z0,z43,z3,z4,z5,z6]),(0,[z73,z55,z0,z3,z4,z5,z6]),(0,[z146,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z246,z5,z6]),(0,[z0,z1,z247,z3,z4,z5,z6]),(0,[z248,z0,z1,z3,z4,z5,z6])],[(0,[z11,z168,z1,z3,z4,z5,z6]),(0,[z0,z1,z249,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z250,z6]),(0,[z0,z1,z3,z4,z251,z5,z6]),(0,[z0,z1,z3,z4,z5,z57,z6]),(0,[z0,z1,z3,z4,z5,z6,z252])]],
   [[(0,[z0,z1,z253,z3,z4,z5,z6]),(0,[z0,z1,z25,z3,z4,z5,z6]),(0,[z127,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z254,z6]),(0,[z255,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z21,z5,z6])],[(0,[z0,z256,z43,z3,z4,z5,z6]),(0,[z0,z1,z3,z257,z4,z5,z6]),(0,[z0,z1,z258,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z259,z5,z6]),(0,[z0,z1,z3,z260,z4,z5,z6]),(0,[z261,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z262]),(0,[z0,z1,z263,z3,z4,z5,z6])],[(0,[z119,z0,z1,z44,z4,z5,z6]),(0,[z54,z0,z1,z3,z19,z5,z6]),(0,[z0,z1,z3,z4,z264,z5,z6]),(0,[z265,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z266,z4,z5,z6])],[(1,[z12,z43,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z267]),(1,[z0,z1,z3,z45,z5,z6]),(0,[z268,z55,z1,z3,z4,z5,z6])],[(0,[z12,z168,z0,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z269]),(0,[z0,z1,z3,z4,z270,z5,z6]),(0,[z0,z1,z3,z4,z271,z5,z6])],[(0,[z12,z0,z3,z4,z5,z15,z6]),(0,[z0,z1,z3,z272,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z115,z90]),(0,[z146,z0,z1,z3,z4,z124,z6]),(0,[z0,z1,z3,z4,z273,z5,z6])],[(0,[z0,z1,z3,z4,z5,z274,z6]),(0,[z0,z1,z3,z4,z5,z275,z6]),(0,[z268,z0,z1,z3,z4,z5,z6]),(0,[z55,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z94,z204,z5])],[(0,[z168,z1,z43,z3,z4,z5,z6]),(0,[z276,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z277,z6]),(0,[z278,z0,z1,z3,z4,z5,z6])]],
   [[(0,[z12,z0,z3,z4,z5,z95,z6]),(0,[z0,z1,z171,z3,z4,z5,z6]),(0,[z0,z1,z3,z39,z27,z5,z6]),(1,[z0,z1,z3,z83,z46,z6])],[(1,[z43,z3,z44,z4,z5,z6]),(1,[z0,z1,z3,z4,z5,z279])],[(0,[z0,z43,z3,z4,z5,z6,z280]),(0,[z12,z0,z3,z4,z5,z50,z6]),(0,[z0,z1,z3,z281,z4,z5,z6]),(1,[z0,z282,z3,z4,z5,z6]),(1,[z117,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z283]),(0,[z0,z1,z3,z4,z5,z115,z91]),(0,[z284,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z4,z21,z5,z50,z6]),(0,[z0,z1,z3,z4,z285,z5,z6])],[(0,[z0,z43,z3,z4,z5,z6,z286]),(0,[z12,z0,z3,z4,z5,z110,z6]),(0,[z168,z0,z1,z3,z4,z5,z269]),(0,[z0,z1,z287,z3,z4,z5,z6]),(0,[z288,z0,z1,z3,z4,z5,z6]),(0,[z99,z0,z1,z3,z4,z39,z5]),(0,[z289,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z290]),(0,[z0,z1,z3,z4,z5,z291,z6])],[(0,[z0,z43,z292,z3,z4,z5,z6]),(0,[z0,z1,z3,z293,z4,z5,z6]),(0,[z85,z0,z1,z3,z4,z5,z6]),(0,[z294,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z295,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z296,z6]),(0,[z0,z1,z3,z4,z297,z124,z5]),(0,[z0,z1,z298,z3,z4,z5,z6])],[(0,[z0,z1,z3,z299,z4,z5,z6]),(1,[z0,z191,z3,z4,z5,z6]),(0,[z49,z0,z1,z3,z4,z5,z6]),(0,[z300,z0,z1,z3,z4,z5,z6]),(0,[z0,z301,z1,z3,z4,z5,z6])]],
   [[(1,[z55,z0,z3,z4,z5,z286])],[(0,[z12,z0,z3,z4,z302,z5,z6]),(0,[z0,z1,z3,z4,z5,z303,z6]),(0,[z0,z1,z3,z4,z5,z304,z6]),(0,[z0,z1,z305,z3,z4,z5,z6])],[(0,[z306,z0,z1,z3,z4,z5,z6]),(0,[z0,z43,z3,z4,z204,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z307]),(0,[z0,z3,z4,z124,z5,z110,z6]),(0,[z55,z308,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z309,z4,z5,z6])],[(0,[z89,z12,z0,z3,z4,z5,z6]),(0,[z310,z0,z1,z3,z4,z5,z6]),(0,[z73,z0,z1,z3,z4,z164,z6]),(0,[z0,z1,z3,z30,z27,z5,z6]),(0,[z0,z1,z3,z4,z5,z311,z6]),(0,[z0,z1,z3,z4,z5,z233,z6]),(0,[z0,z1,z3,z4,z312,z5,z6])],[(0,[z0,z1,z3,z4,z5,z313,z6]),(0,[z89,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z27,z5,z6]),(0,[z0,z1,z3,z46,z5,z17,z6])],[(0,[z168,z0,z1,z3,z26,z5,z6]),(1,[z0,z1,z3,z4,z5,z269]),(0,[z0,z1,z3,z4,z5,z314,z6]),(0,[z0,z1,z3,z4,z204,z6,z91])],[(0,[z315,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z316,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z317]),(0,[z0,z1,z3,z4,z5,z318,z6]),(0,[z0,z1,z3,z4,z228,z5,z6])],[(0,[z168,z85,z1,z3,z4,z5,z6]),(0,[z80,z0,z47,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z319]),(0,[z0,z320,z152,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z321]),(0,[z41,z0,z1,z3,z4,z5,z57]),(0,[z0,z1,z3,z4,z5,z6,z322])]],
   [[(0,[z119,z1,z25,z3,z4,z5,z6]),(0,[z0,z1,z3,z323,z4,z5,z6]),(0,[z289,z0,z3,z4,z5,z277,z6]),(0,[z54,z289,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z6,z324]),(0,[z0,z1,z3,z325,z4,z5,z6])],[(0,[z1,z43,z3,z4,z5,z6,z144]),(0,[z326,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z327,z6]),(0,[z0,z1,z328,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z329,z5,z6]),(0,[z107,z0,z1,z247,z4,z5,z6])],[(0,[z0,z43,z330,z3,z4,z5,z6]),(0,[z12,z0,z152,z3,z4,z5,z6]),(0,[z18,z0,z1,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z277,z6,z286]),(1,[z0,z3,z4,z5,z6,z331])],[(0,[z0,z1,z43,z3,z4,z5,z6]),(0,[z0,z1,z3,z332,z4,z5,z6]),(0,[z0,z1,z3,z134,z4,z5,z6])],[(0,[z333,z0,z1,z3,z4,z5,z6]),(0,[z49,z0,z1,z3,z4,z21,z6]),(0,[z41,z76,z1,z3,z4,z5,z6])],[(0,[z334,z0,z1,z3,z4,z5,z6]),(0,[z0,z152,z3,z4,z5,z277,z6]),(0,[z0,z1,z3,z4,z5,z335,z6]),(0,[z336,z0,z1,z3,z4,z5,z6])],[(0,[z133,z12,z0,z3,z4,z5,z6]),(0,[z0,z1,z330,z44,z4,z5,z6]),(0,[z0,z1,z3,z337,z4,z5,z6]),(0,[z168,z0,z338,z3,z4,z5,z6]),(0,[z0,z1,z247,z4,z5,z50,z6]),(0,[z0,z1,z3,z4,z5,z6,z91])],[(0,[z0,z43,z3,z4,z7,z5,z6]),(0,[z0,z1,z3,z4,z339,z5,z6]),(0,[z0,z1,z3,z4,z5,z340,z6]),(1,[z268,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z21,z6,z91]),(0,[z0,z1,z3,z4,z5,z341,z6])]],
   [[(0,[z11,z80,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z342]),(0,[z85,z0,z295,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z343,z5,z6])],[(0,[z0,z43,z3,z19,z4,z5,z6]),(0,[z344,z0,z1,z3,z4,z5,z6]),(0,[z345,z0,z1,z3,z4,z5,z6])],[(0,[z346,z0,z1,z3,z4,z5,z6]),(0,[z80,z18,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z286,z90]),(0,[z347,z0,z1,z3,z4,z5,z6])],[(0,[z0,z43,z3,z36,z4,z5,z6]),(0,[z11,z12,z0,z3,z4,z5,z6]),(0,[z14,z0,z1,z3,z4,z5,z348]),(0,[z0,z1,z3,z68,z4,z5,z144]),(0,[z107,z0,z1,z3,z4,z349,z6]),(1,[z0,z1,z247,z4,z5,z95])],[(0,[z11,z0,z1,z3,z4,z5,z6]),(0,[z12,z0,z3,z82,z4,z5,z6]),(0,[z0,z1,z3,z4,z350,z5,z6]),(0,[z0,z1,z3,z351,z4,z5,z6]),(1,[z89,z0,z1,z27,z5,z6]),(0,[z0,z1,z3,z4,z5,z95,z91])],[(0,[z107,z0,z1,z3,z4,z5,z6]),(0,[z0,z352,z1,z3,z4,z5,z6])],[(0,[z12,z1,z43,z3,z4,z5,z6]),(0,[z14,z0,z1,z287,z4,z5,z6])],[(0,[z0,z43,z3,z59,z4,z5,z6]),(0,[z353,z12,z0,z3,z4,z5,z6]),(0,[z354,z0,z1,z3,z4,z5,z6]),(1,[z0,z338,z3,z4,z5,z6]),(0,[z38,z0,z3,z4,z39,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z355]),(0,[z356,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z357,z5,z6])]],
   [[(0,[z353,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z5,z319]),(0,[z0,z1,z358,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z359]),(0,[z41,z0,z1,z3,z4,z46,z6]),(0,[z0,z1,z3,z4,z360,z5,z6])],[(0,[z0,z43,z3,z4,z5,z69,z6]),(0,[z361,z12,z0,z3,z4,z5,z6]),(0,[z12,z119,z0,z3,z4,z5,z6]),(0,[z12,z0,z81,z3,z4,z5,z6]),(0,[z12,z0,z3,z129,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z362,z6]),(0,[z363,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z364]),(0,[z158,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z5,z324])],[(0,[z12,z0,z0,z3,z4,z5,z6]),(0,[z361,z0,z1,z3,z4,z5,z6]),(0,[z78,z186,z0,z3,z4,z5,z6]),(0,[z78,z0,z1,z3,z19,z5,z6]),(0,[z0,z1,z3,z4,z5,z365,z6]),(1,[z0,z128,z3,z4,z124,z6]),(0,[z0,z1,z3,z4,z5,z366,z6]),(0,[z367,z0,z1,z3,z4,z5,z6])],[(0,[z368,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z369,z6]),(1,[z370,z0,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z121,z6]),(0,[z0,z1,z3,z371,z4,z5,z6]),(0,[z0,z1,z3,z4,z372,z5,z6]),(0,[z0,z1,z3,z373,z4,z5,z6])],[(0,[z0,z1,z3,z4,z374,z5,z6]),(0,[z375,z0,z1,z3,z4,z5,z6])],[(0,[z85,z0,z43,z3,z4,z5,z6]),(0,[z0,z1,z376,z3,z4,z5,z6]),(0,[z54,z0,z1,z3,z4,z5,z144]),(0,[z0,z1,z377,z3,z4,z5,z6]),(0,[z0,z1,z247,z330,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z378,z6]),(0,[z0,z1,z3,z82,z39,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z379]),(0,[z41,z0,z1,z380,z4,z5,z6]),(0,[z0,z1,z3,z4,z381,z5,z6])],[(0,[z0,z1,z3,z382,z4,z5,z6]),(0,[z383,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z46,z5,z6]),(0,[z0,z1,z3,z46,z5,z20,z6])]],
   [[(0,[z12,z0,z3,z83,z4,z5,z6]),(0,[z168,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z384,z4,z5,z6]),(0,[z38,z158,z1,z3,z4,z5,z6]),(0,[z385,z0,z1,z3,z4,z5,z6]),(0,[z49,z0,z1,z4,z5,z50,z6])],[(0,[z386,z0,z1,z3,z4,z5,z6]),(0,[z54,z0,z1,z3,z26,z5,z6]),(0,[z0,z1,z3,z4,z5,z387,z6]),(0,[z73,z0,z3,z36,z4,z5,z6]),(1,[z0,z1,z3,z4,z5,z42])],[(0,[z0,z1,z3,z4,z5,z63,z6]),(0,[z0,z1,z44,z4,z5,z50,z6]),(0,[z0,z1,z3,z4,z388,z5,z6])],[(0,[z12,z0,z3,z4,z39,z5,z6]),(1,[z80,z1,z3,z4,z5,z115])],[(0,[z89,z0,z43,z3,z4,z5,z6]),(0,[z0,z389,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z390]),(0,[z0,z1,z4,z5,z95,z6,z90])],[(0,[z12,z289,z0,z3,z4,z5,z6]),(0,[z0,z1,z3,z19,z83,z5,z6]),(0,[z0,z1,z3,z391,z4,z5,z6])],[(0,[z0,z1,z330,z25,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z392,z6]),(0,[z393,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z394,z6]),(0,[z0,z1,z247,z3,z4,z5,z95]),(0,[z0,z1,z3,z4,z5,z6,z395])],[(0,[z0,z43,z3,z4,z124,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z396]),(1,[z0,z1,z241,z4,z5,z6]),(0,[z0,z1,z397,z3,z4,z5,z6]),(0,[z0,z1,z3,z398,z4,z5,z6]),(1,[z0,z1,z3,z4,z349,z6])]],
   [[(0,[z0,z43,z3,z4,z94,z5,z6]),(0,[z12,z0,z128,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z13,z6]),(0,[z0,z1,z3,z4,z399,z5,z6]),(0,[z0,z1,z3,z4,z124,z5,z400])],[(1,[z0,z1,z3,z4,z5,z6]),(0,[z73,z117,z1,z3,z4,z5,z6]),(0,[z0,z128,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z279,z6]),(0,[z0,z1,z3,z4,z5,z401,z6])],[(0,[z18,z0,z43,z3,z4,z5,z6]),(0,[z402,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z330,z4,z27,z5,z6])],[(0,[z0,z1,z3,z4,z137,z5,z6]),(0,[z0,z1,z3,z4,z403,z5,z6]),(0,[z404,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z405,z4,z5,z6])],[(0,[z0,z406,z43,z3,z4,z5,z6]),(0,[z407,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z408,z6]),(0,[z0,z1,z3,z4,z5,z409,z6])],[(0,[z0,z1,z3,z4,z410,z5,z6]),(1,[z23,z43,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z411]),(0,[z0,z1,z3,z4,z412,z5,z6]),(0,[z54,z0,z1,z3,z46,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z413])],[(0,[z414,z0,z1,z3,z4,z5,z6]),(0,[z415,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z330,z4,z5,z6,z90])],[(0,[z0,z43,z3,z4,z26,z5,z6]),(0,[z0,z43,z3,z4,z5,z17,z6]),(0,[z0,z1,z3,z4,z416,z5,z6]),(0,[z417,z0,z1,z3,z4,z5,z6]),(0,[z146,z12,z0,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z418,z6]),(0,[z0,z1,z3,z4,z5,z6,z419]),(0,[z0,z1,z81,z3,z4,z5,z324]),(0,[z49,z0,z1,z330,z4,z5,z6]),(0,[z420,z0,z1,z3,z4,z5,z6])]],
   [[(0,[z421,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z68,z4,z5,z115]),(0,[z422,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z277,z95]),(0,[z423,z0,z1,z3,z4,z5,z6]),(0,[z41,z0,z1,z3,z4,z50,z6]),(0,[z0,z1,z3,z4,z424,z5,z6]),(1,[z0,z1,z425,z4,z5,z6])],[(0,[z426,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z427,z6]),(0,[z0,z128,z1,z3,z4,z124,z6]),(1,[z54,z0,z1,z3,z5,z130])],[(0,[z428,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z429,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z430]),(0,[z54,z0,z1,z3,z4,z5,z95]),(0,[z0,z1,z3,z68,z4,z5,z6]),(0,[z0,z1,z3,z68,z5,z20,z6])],[(0,[z0,z43,z3,z4,z5,z161,z6]),(1,[z73,z0,z36,z4,z5,z6]),(0,[z0,z1,z3,z431,z4,z5,z6]),(1,[z0,z1,z4,z432,z5,z6]),(0,[z433,z0,z1,z3,z4,z5,z6])],[(0,[z11,z0,z43,z3,z4,z5,z6]),(0,[z12,z0,z3,z4,z5,z6,z286]),(0,[z434,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z435,z6]),(0,[z0,z1,z3,z4,z5,z6,z130])],[(0,[z153,z0,z43,z3,z4,z5,z6]),(0,[z0,z1,z436,z3,z4,z5,z6]),(0,[z0,z437,z1,z3,z4,z5,z6]),(0,[z0,z1,z438,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z439,z5,z6]),(0,[z0,z1,z47,z3,z4,z5,z6]),(0,[z0,z1,z3,z440,z4,z5,z6]),(0,[z0,z1,z3,z441,z4,z5,z6]),(1,[z308,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z442,z5,z6]),(0,[z0,z1,z3,z129,z4,z5,z91])],[(1,[z0,z171,z3,z4,z5,z6]),(0,[z85,z1,z3,z4,z7,z5,z6]),(0,[z99,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z443,z6])],[(0,[z24,z119,z1,z3,z4,z5,z6]),(0,[z24,z0,z1,z3,z4,z13,z6]),(1,[z0,z1,z3,z4,z5,z444]),(0,[z0,z1,z3,z4,z5,z445,z6]),(0,[z0,z1,z3,z4,z5,z446,z6])]],
   [[(0,[z24,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z447,z3,z4,z5,z6]),(1,[z0,z1,z3,z134,z5,z6]),(0,[z0,z1,z3,z4,z448,z5,z6]),(0,[z55,z0,z1,z3,z4,z5,z286])],[(0,[z0,z1,z3,z4,z5,z114,z6]),(0,[z14,z0,z1,z3,z4,z15,z6]),(0,[z29,z0,z3,z4,z5,z110,z6]),(0,[z0,z1,z3,z129,z4,z50,z6]),(0,[z0,z1,z3,z4,z449,z5,z6]),(0,[z0,z1,z3,z450,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z451])],[(0,[z0,z1,z3,z179,z4,z5,z6]),(0,[z12,z0,z3,z4,z204,z5,z6]),(0,[z452,z0,z1,z3,z4,z5,z6]),(0,[z54,z0,z1,z3,z4,z5,z115]),(0,[z73,z0,z1,z3,z123,z5,z6])],[(0,[z54,z12,z0,z3,z4,z5,z6])],[(1,[z0,z295,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z144]),(0,[z0,z1,z81,z3,z82,z5,z6]),(0,[z0,z1,z3,z4,z453,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z454]),(0,[z54,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z455,z3,z4,z5,z6]),(0,[z0,z1,z456,z3,z4,z5,z6]),(0,[z0,z1,z330,z81,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z457,z6])],[(1,[z0,z1,z3,z4,z5,z411]),(0,[z78,z168,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z458,z6]),(0,[z289,z0,z1,z3,z4,z5,z286]),(0,[z0,z459,z1,z3,z4,z5,z6]),(0,[z460,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z203,z3,z4,z5,z6])],[(0,[z12,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z81,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z461,z6]),(0,[z0,z1,z3,z462,z4,z5,z6]),(0,[z0,z463,z1,z3,z4,z5,z6])]],
   [[(0,[z0,z464,z1,z3,z4,z5,z6]),(0,[z0,z1,z465,z3,z4,z5,z6]),(0,[z0,z466,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z318,z6]),(0,[z0,z1,z3,z83,z4,z50,z6]),(1,[z0,z96,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z467,z5,z6])],[(0,[z49,z12,z0,z3,z4,z5,z6]),(0,[z468,z0,z1,z3,z4,z5,z6])],[(0,[z12,z0,z330,z3,z4,z5,z6]),(0,[z0,z1,z3,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z469,z6]),(0,[z0,z470,z1,z3,z4,z5,z6])],[(0,[z471,z0,z1,z3,z4,z5,z6])],[(0,[z186,z0,z1,z3,z4,z5,z6]),(0,[z14,z0,z1,z299,z4,z5,z6]),(0,[z14,z0,z1,z3,z4,z5,z166]),(0,[z0,z1,z3,z4,z472,z5,z6]),(0,[z289,z0,z1,z3,z4,z94,z5]),(0,[z0,z1,z3,z4,z473,z5,z6])],[(0,[z0,z1,z3,z474,z4,z5,z6]),(0,[z1,z3,z4,z7,z5,z15,z6]),(0,[z0,z1,z3,z4,z5,z475,z6])],[(0,[z476,z0,z1,z3,z4,z5,z6]),(0,[z477,z0,z1,z3,z4,z5,z6]),(0,[z0,z282,z1,z3,z4,z5,z6]),(0,[z478,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z5,z400]),(0,[z0,z1,z3,z479,z4,z5,z6])],[(0,[z23,z1,z43,z3,z4,z5,z6]),(0,[z0,z43,z3,z44,z4,z5,z6]),(0,[z12,z0,z3,z4,z7,z5,z6]),(0,[z73,z0,z1,z3,z4,z5,z319]),(0,[z480,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z481]),(0,[z0,z1,z3,z4,z5,z6,z482])]],
   [[(1,[z0,z1,z3,z429,z5,z6]),(0,[z0,z1,z3,z4,z5,z115,z6]),(0,[z0,z1,z3,z483,z4,z5,z6])],[(0,[z0,z43,z3,z30,z4,z5,z6]),(0,[z0,z128,z43,z3,z4,z5,z6]),(0,[z12,z0,z3,z19,z4,z5,z6]),(0,[z78,z0,z1,z3,z26,z5,z6]),(0,[z0,z1,z484,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z39,z5,z6]),(0,[z0,z128,z3,z4,z124,z5,z6]),(0,[z0,z1,z485,z3,z4,z5,z6]),(0,[z0,z1,z3,z425,z4,z5,z6])],[(0,[z0,z43,z3,z4,z5,z20,z6]),(0,[z0,z1,z3,z4,z194,z5,z6]),(0,[z0,z1,z3,z4,z486,z5,z6]),(0,[z168,z1,z3,z4,z5,z15,z6]),(0,[z487,z0,z1,z3,z4,z5,z6]),(1,[z0,z352,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z488,z5,z6])],[(0,[z12,z0,z3,z36,z4,z5,z6])],[(0,[z0,z43,z247,z3,z4,z5,z6]),(0,[z119,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z489,z6]),(0,[z49,z0,z1,z3,z4,z5,z490]),(0,[z0,z1,z3,z4,z5,z6,z491]),(0,[z0,z1,z3,z4,z432,z5,z6])],[(0,[z0,z1,z3,z4,z492,z5,z6]),(1,[z43,z3,z4,z5,z6,z144]),(0,[z11,z1,z3,z4,z7,z5,z6]),(0,[z24,z0,z1,z3,z4,z5,z411]),(0,[z493,z0,z1,z3,z4,z5,z6]),(0,[z494,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z495])],[(0,[z107,z0,z1,z3,z4,z5,z95]),(0,[z0,z1,z3,z68,z4,z5,z130])],[(0,[z0,z43,z3,z4,z21,z5,z6]),(0,[z334,z12,z0,z3,z4,z5,z6]),(0,[z0,z1,z247,z4,z5,z95,z6]),(1,[z0,z1,z203,z4,z5,z6]),(0,[z0,z1,z3,z129,z4,z204,z6]),(0,[z0,z1,z3,z4,z5,z6,z496])]],
   [[(0,[z146,z0,z43,z3,z4,z5,z6]),(0,[z497,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z498,z6]),(0,[z0,z1,z3,z4,z94,z5,z20])],[(0,[z80,z1,z43,z3,z4,z5,z6]),(0,[z12,z0,z3,z4,z5,z6,z70]),(0,[z14,z0,z1,z3,z45,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z499]),(1,[z0,z320,z152,z4,z5,z6]),(1,[z0,z1,z3,z129,z4,z94])],[(0,[z190,z168,z0,z3,z4,z5,z6]),(0,[z0,z1,z3,z500,z4,z5,z6]),(0,[z0,z1,z3,z501,z4,z5,z6]),(0,[z502,z0,z1,z3,z4,z5,z6]),(0,[z503,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z81,z3,z4,z5,z279]),(0,[z0,z1,z3,z4,z5,z504,z6])],[(0,[z0,z1,z3,z4,z5,z6,z42]),(0,[z0,z1,z3,z4,z505,z5,z6])],[(0,[z0,z1,z25,z4,z5,z50,z6]),(0,[z506,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z507,z5,z6]),(0,[z14,z0,z1,z3,z34,z5,z6])],[(0,[z0,z43,z3,z4,z5,z277,z6]),(0,[z85,z1,z3,z4,z26,z5,z6]),(0,[z508,z0,z1,z3,z4,z5,z6]),(0,[z55,z0,z1,z3,z68,z4,z5]),(0,[z509,z0,z1,z3,z4,z5,z6]),(0,[z510,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z204,z5,z91])],[(0,[z107,z12,z0,z3,z4,z5,z6]),(0,[z24,z0,z1,z3,z429,z5,z6]),(0,[z0,z1,z3,z511,z4,z5,z6]),(0,[z0,z1,z512,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z513,z6]),(0,[z0,z1,z3,z4,z514,z5,z6]),(0,[z0,z1,z3,z4,z515,z5,z6])]],
   [[(0,[z80,z0,z1,z3,z112,z5,z6]),(0,[z73,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z81,z3,z27,z5,z6]),(0,[z516,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z517,z5,z6]),(0,[z54,z0,z1,z3,z4,z5,z130])],[(0,[z55,z0,z43,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z518]),(0,[z12,z80,z0,z3,z4,z5,z6]),(0,[z519,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z520,z5,z6]),(0,[z0,z1,z330,z4,z21,z5,z6]),(0,[z521,z0,z1,z3,z4,z5,z6])],[(0,[z522,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z523,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z16,z5]),(0,[z0,z1,z524,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z200])],[(0,[z0,z1,z3,z525,z4,z5,z6]),(0,[z168,z1,z3,z19,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z6]),(0,[z0,z1,z3,z4,z5,z6,z526]),(1,[z527,z1,z3,z4,z5,z6])],[(0,[z54,z0,z43,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z444,z6]),(0,[z289,z0,z1,z3,z68,z4,z5]),(0,[z107,z0,z1,z3,z4,z449,z6]),(0,[z0,z1,z3,z528,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z529,z6]),(1,[z0,z1,z3,z68,z5,z20]),(0,[z530,z0,z1,z3,z4,z5,z6])],[(0,[z531,z0,z1,z3,z4,z5,z6])],[(0,[z14,z1,z43,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z15,z6]),(0,[z0,z1,z3,z4,z5,z6,z532]),(0,[z41,z0,z1,z3,z5,z17,z6]),(1,[z126,z0,z1,z3,z5,z6])],[(0,[z289,z0,z43,z3,z4,z5,z6]),(0,[z12,z0,z3,z4,z124,z5,z6]),(0,[z0,z1,z3,z4,z5,z490,z6]),(0,[z0,z1,z3,z68,z4,z204,z5])]],
   [[(0,[z12,z0,z3,z4,z94,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z533]),(0,[z139,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z534,z4,z5,z6]),(0,[z1,z3,z4,z5,z115,z6,z144]),(0,[z0,z1,z3,z4,z5,z6,z535]),(0,[z0,z1,z3,z536,z4,z5,z6])],[(0,[z0,z1,z3,z4,z537,z39,z5]),(0,[z0,z1,z4,z124,z5,z233,z6]),(0,[z0,z1,z3,z4,z5,z95,z6])],[(0,[z49,z0,z43,z3,z4,z5,z6]),(0,[z0,z1,z3,z82,z26,z5,z6]),(0,[z538,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z330,z3,z4,z50,z6]),(0,[z0,z1,z3,z4,z5,z539,z6])],[(0,[z0,z43,z3,z4,z27,z5,z6]),(0,[z0,z1,z3,z4,z5,z50,z6])],[(0,[z12,z0,z3,z4,z5,z138,z6]),(1,[z24,z1,z44,z4,z5,z6]),(0,[z78,z0,z1,z3,z4,z5,z6]),(0,[z370,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z540,z5,z6]),(0,[z0,z1,z3,z541,z4,z5,z6]),(0,[z0,z1,z3,z542,z4,z5,z6])],[(0,[z543,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z544,z4,z5,z6]),(0,[z29,z0,z128,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z110,z6]),(0,[z0,z1,z3,z4,z5,z545,z6]),(0,[z41,z54,z0,z1,z3,z5,z6]),(0,[z0,z546,z1,z3,z4,z5,z6])],[(1,[z168,z43,z3,z4,z5,z6]),(1,[z35,z1,z3,z4,z5,z6]),(0,[z55,z0,z1,z3,z4,z5,z277]),(0,[z0,z3,z4,z5,z6,z331,z90]),(0,[z0,z527,z1,z3,z4,z5,z6])],[(0,[z0,z43,z3,z4,z5,z6,z90]),(0,[z0,z1,z406,z3,z4,z5,z6]),(0,[z12,z0,z3,z4,z26,z5,z6]),(0,[z12,z0,z3,z4,z5,z17,z6]),(0,[z0,z1,z3,z4,z7,z50,z6]),(0,[z146,z0,z3,z4,z5,z110,z6]),(0,[z0,z1,z3,z4,z5,z91,z130])]],
   [[(0,[z547,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z548,z4,z5,z6]),(1,[z0,z1,z3,z4,z230,z5])],[(1,[z0,z1,z3,z403,z5,z6]),(0,[z0,z1,z549,z3,z4,z5,z6]),(0,[z550,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z551,z6]),(0,[z0,z1,z552,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z16,z5,z6]),(0,[z54,z0,z1,z3,z4,z204,z5])],[(0,[z0,z43,z43,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z302,z5,z6]),(0,[z38,z0,z1,z3,z30,z5,z6]),(0,[z0,z1,z3,z129,z4,z94,z6])],[(1,[z12,z0,z3,z4,z5,z6]),(0,[z0,z1,z3,z553,z4,z5,z6]),(0,[z0,z1,z3,z4,z554,z5,z6]),(1,[z29,z0,z3,z30,z5,z6]),(0,[z0,z1,z3,z555,z4,z5,z6]),(0,[z0,z1,z3,z4,z556,z5,z6]),(0,[z0,z1,z3,z68,z4,z5,z95]),(0,[z0,z1,z3,z5,z20,z6,z130]),(0,[z557,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z19,z82,z5,z6]),(0,[z85,z0,z1,z3,z4,z15,z6]),(0,[z0,z320,z1,z330,z4,z5,z6]),(0,[z289,z0,z1,z3,z4,z5,z277]),(1,[z49,z0,z1,z4,z50,z6]),(0,[z0,z1,z558,z3,z4,z5,z6]),(0,[z0,z559,z1,z3,z4,z5,z6]),(0,[z0,z1,z560,z3,z4,z5,z6])],[(0,[z0,z43,z3,z4,z5,z6,z91]),(0,[z11,z1,z3,z4,z26,z5,z6]),(0,[z561,z0,z1,z3,z4,z5,z6]),(0,[z49,z0,z1,z3,z4,z5,z562])],[(0,[z12,z0,z3,z170,z4,z5,z6]),(0,[z0,z1,z3,z83,z26,z5,z6]),(0,[z14,z85,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z563,z4,z5,z6]),(0,[z0,z1,z3,z4,z564,z5,z6]),(0,[z565,z0,z1,z3,z4,z5,z6]),(0,[z566,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z50,z6,z91])],[(0,[z0,z1,z3,z567,z4,z5,z6]),(0,[z0,z1,z3,z568,z4,z5,z6]),(0,[z0,z1,z3,z569,z4,z5,z6])]],
   [[(0,[z334,z0,z43,z3,z4,z5,z6]),(0,[z12,z0,z320,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z570,z5,z6]),(1,[z0,z1,z3,z4,z449,z6]),(0,[z571,z0,z1,z3,z4,z5,z6])],[(0,[z168,z0,z1,z3,z4,z5,z444]),(0,[z572,z0,z1,z3,z4,z5,z6])],[(0,[z573,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z5,z348]),(0,[z574,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z241,z4,z124,z5,z6]),(0,[z0,z1,z4,z204,z432,z5,z6])],[(1,[z0,z1,z3,z4,z114,z6]),(0,[z0,z1,z152,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z575,z5,z6]),(0,[z0,z1,z3,z4,z5,z576,z6]),(0,[z577,z0,z1,z3,z4,z5,z6])],[(1,[z0,z1,z3,z4,z537,z5])],[(0,[z52,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z578,z6]),(0,[z0,z1,z3,z4,z579,z5,z6]),(1,[z0,z1,z287,z4,z5,z6]),(1,[z0,z1,z3,z4,z5,z387]),(1,[z0,z1,z81,z82,z5,z6]),(0,[z0,z1,z330,z3,z4,z21,z6])],[(0,[z0,z1,z3,z4,z5,z580,z6]),(0,[z0,z320,z1,z152,z4,z5,z6]),(0,[z38,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z5,z490]),(0,[z0,z1,z3,z4,z94,z5,z90]),(0,[z0,z1,z3,z581,z4,z5,z6])],[(0,[z0,z0,z1,z3,z4,z5,z6]),(0,[z62,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z582,z6]),(0,[z0,z1,z3,z4,z5,z6,z583])]],
   [[(0,[z107,z0,z43,z3,z4,z5,z6]),(0,[z584,z0,z1,z3,z4,z5,z6]),(0,[z24,z0,z1,z3,z403,z5,z6]),(0,[z80,z0,z1,z3,z4,z5,z115]),(0,[z128,z232,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z400]),(0,[z585,z0,z1,z3,z4,z5,z6])],[(0,[z0,z75,z1,z3,z4,z5,z6]),(0,[z0,z1,z53,z3,z4,z5,z6]),(0,[z0,z1,z3,z586,z4,z5,z6]),(0,[z0,z1,z3,z4,z587,z5,z6]),(0,[z0,z1,z588,z3,z4,z5,z6]),(0,[z73,z0,z1,z4,z5,z50,z6]),(0,[z0,z1,z3,z589,z4,z5,z6]),(0,[z0,z1,z3,z4,z590,z5,z6]),(0,[z41,z0,z1,z3,z5,z20,z6])],[(0,[z24,z12,z0,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z591,z5,z6]),(0,[z0,z1,z3,z4,z5,z592,z6]),(0,[z593,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z594,z5,z6])],[(0,[z11,z12,z1,z3,z4,z5,z6]),(0,[z1,z3,z19,z4,z26,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z595]),(0,[z596,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z597]),(0,[z76,z0,z1,z3,z4,z5,z6]),(0,[z0,z598,z1,z3,z4,z5,z6])],[(1,[z14,z43,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z599,z6]),(0,[z29,z0,z1,z3,z4,z5,z6])],[(0,[z1,z43,z3,z4,z7,z5,z6]),(0,[z0,z1,z74,z3,z4,z5,z6]),(0,[z0,z600,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z82,z4,z5,z6]),(0,[z601,z0,z1,z3,z4,z5,z6])],[(0,[z0,z43,z3,z4,z46,z5,z6]),(1,[z190,z0,z3,z4,z5,z6]),(0,[z0,z1,z191,z3,z4,z5,z6]),(0,[z55,z0,z152,z3,z4,z5,z6]),(0,[z0,z1,z3,z602,z4,z5,z6]),(1,[z265,z1,z3,z4,z5,z6])],[(0,[z12,z0,z3,z44,z4,z5,z6]),(0,[z0,z1,z3,z26,z5,z17,z6]),(0,[z0,z1,z3,z4,z5,z6,z603]),(0,[z0,z320,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z604,z4,z5,z6]),(0,[z0,z1,z3,z4,z605,z5,z6]),(0,[z0,z1,z3,z4,z124,z50,z6]),(0,[z0,z1,z3,z4,z5,z606,z6]),(1,[z289,z0,z3,z4,z5,z277])]],
   [[(0,[z0,z607,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z608]),(0,[z0,z1,z3,z4,z164,z5,z6]),(0,[z609,z0,z1,z3,z4,z5,z6]),(0,[z41,z0,z1,z425,z4,z5,z6])],[(0,[z12,z12,z0,z3,z4,z5,z6]),(0,[z12,z0,z3,z30,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z115,z95]),(0,[z610,z0,z1,z3,z4,z5,z6]),(0,[z38,z29,z0,z3,z4,z5,z6]),(0,[z55,z0,z1,z3,z4,z94,z5]),(0,[z0,z1,z3,z4,z611,z5,z6])],[(0,[z12,z0,z3,z4,z5,z20,z6]),(0,[z612,z0,z1,z3,z4,z5,z6]),(0,[z613,z0,z1,z3,z4,z5,z6]),(0,[z614,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z615,z4,z5,z6]),(0,[z0,z1,z3,z129,z4,z5,z6])],[(0,[z168,z0,z43,z3,z4,z5,z6]),(0,[z0,z308,z1,z3,z4,z5,z6]),(0,[z89,z0,z1,z4,z27,z5,z6])],[(0,[z78,z0,z43,z3,z4,z5,z6]),(0,[z12,z0,z247,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z616,z5,z6])],[(0,[z0,z1,z3,z4,z5,z617,z6]),(0,[z11,z1,z3,z44,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z95,z144]),(1,[z98,z0,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z618]),(0,[z54,z0,z1,z3,z5,z6,z130])],[(0,[z0,z1,z3,z4,z112,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z562]),(0,[z41,z0,z1,z3,z4,z21,z6])],[(0,[z619,z0,z1,z3,z4,z5,z6]),(0,[z620,z0,z1,z3,z4,z5,z6]),(0,[z12,z0,z253,z3,z4,z5,z6]),(0,[z12,z0,z3,z4,z21,z5,z6]),(0,[z0,z1,z621,z3,z4,z5,z6]),(0,[z0,z152,z3,z36,z4,z5,z6]),(0,[z622,z0,z1,z3,z4,z5,z6])]],
   [[(1,[z80,z43,z3,z4,z5,z6]),(0,[z12,z0,z3,z257,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z623,z6]),(0,[z0,z1,z3,z4,z5,z624,z6]),(0,[z0,z1,z3,z19,z27,z5,z6]),(0,[z73,z0,z1,z330,z4,z5,z6]),(0,[z0,z1,z3,z4,z625,z5,z6])],[(0,[z626,z0,z1,z3,z4,z5,z6]),(0,[z73,z0,z320,z3,z4,z5,z6]),(0,[z627,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z628]),(0,[z0,z1,z3,z629,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z331]),(0,[z0,z1,z3,z83,z4,z5,z6])],[(0,[z245,z0,z1,z3,z4,z5,z6])],[(1,[z119,z43,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z630,z5,z6]),(0,[z0,z631,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z632,z4,z5,z6]),(1,[z0,z1,z380,z4,z5,z6])],[(1,[z0,z43,z3,z4,z5,z6]),(0,[z1,z3,z4,z26,z5,z15,z6]),(0,[z0,z1,z3,z4,z5,z633,z6]),(0,[z14,z0,z1,z3,z4,z7,z6]),(0,[z0,z1,z3,z634,z4,z5,z6])],[(0,[z12,z29,z0,z3,z4,z5,z6]),(0,[z635,z0,z1,z3,z4,z5,z6]),(0,[z0,z636,z1,z3,z4,z5,z6])],[(0,[z637,z0,z1,z3,z4,z5,z6]),(0,[z0,z43,z3,z4,z416,z5,z6]),(0,[z0,z256,z1,z3,z4,z5,z6]),(0,[z12,z0,z3,z4,z5,z277,z6]),(1,[z0,z1,z3,z4,z5,z435]),(0,[z80,z1,z3,z4,z5,z115,z6]),(0,[z0,z1,z3,z638,z4,z5,z6]),(0,[z0,z1,z3,z639,z4,z5,z6]),(0,[z0,z1,z640,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z641,z5,z6]),(0,[z0,z1,z3,z642,z4,z5,z6])],[(0,[z407,z0,z43,z3,z4,z5,z6]),(1,[z85,z1,z3,z4,z7,z6]),(0,[z0,z1,z3,z129,z4,z21,z6]),(0,[z0,z1,z3,z4,z5,z6,z643])]],
   [[(0,[z0,z1,z3,z4,z644,z5,z6]),(0,[z0,z1,z3,z645,z4,z5,z6]),(1,[z0,z1,z3,z4,z228,z6]),(0,[z0,z1,z3,z646,z4,z5,z6])],[(0,[z0,z43,z3,z68,z4,z5,z6]),(1,[z184,z1,z3,z4,z5,z6]),(0,[z289,z55,z0,z3,z4,z5,z6]),(0,[z647,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z648,z6])],[(0,[z649,z0,z1,z3,z4,z5,z6]),(0,[z0,z43,z25,z3,z4,z5,z6]),(0,[z417,z0,z43,z3,z4,z5,z6]),(0,[z0,z1,z3,z650,z4,z5,z6]),(0,[z73,z0,z1,z152,z4,z5,z6]),(1,[z0,z1,z3,z100,z5,z6])],[(0,[z0,z43,z3,z4,z5,z6,z130]),(0,[z146,z0,z128,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z651,z6]),(0,[z0,z1,z380,z3,z4,z5,z6])],[(0,[z1,z25,z3,z44,z4,z5,z6]),(0,[z0,z1,z3,z4,z652,z5,z6]),(0,[z370,z18,z0,z3,z4,z5,z6]),(0,[z0,z653,z1,z3,z4,z5,z6]),(0,[z654,z0,z1,z3,z4,z5,z6])],[(0,[z73,z35,z1,z3,z4,z5,z6])],[(0,[z38,z0,z43,z3,z4,z5,z6]),(0,[z78,z0,z376,z3,z4,z5,z6]),(0,[z0,z1,z338,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z15,z50,z6]),(0,[z655,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z297,z5,z6]),(0,[z89,z0,z1,z81,z4,z5,z6]),(0,[z0,z1,z3,z4,z656,z5,z6]),(0,[z0,z1,z3,z83,z4,z21,z6]),(0,[z0,z1,z3,z4,z5,z6,z657])],[(0,[z0,z0,z43,z3,z4,z5,z6]),(0,[z0,z1,z3,z19,z5,z17,z6]),(1,[z0,z1,z3,z4,z5,z562])]],
   [[(0,[z658,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z121,z6]),(1,[z0,z1,z3,z5,z6,z200])],[(0,[z659,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z81,z3,z4,z318,z6])],[(0,[z660,z0,z1,z3,z4,z5,z6]),(0,[z73,z12,z0,z3,z4,z5,z6]),(1,[z127,z0,z3,z4,z5,z6]),(0,[z0,z1,z3,z26,z5,z20,z6]),(0,[z0,z1,z3,z661,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z662,z6]),(0,[z0,z1,z3,z4,z5,z6,z663]),(0,[z0,z1,z247,z3,z4,z5,z90]),(0,[z0,z664,z1,z3,z4,z5,z6]),(0,[z41,z0,z352,z3,z4,z5,z6]),(0,[z665,z0,z1,z3,z4,z5,z6])],[(0,[z24,z0,z43,z3,z4,z5,z6]),(0,[z0,z43,z3,z4,z5,z6,z144]),(0,[z0,z1,z3,z4,z5,z6,z280]),(0,[z12,z0,z3,z4,z27,z5,z6]),(0,[z0,z1,z3,z4,z666,z5,z6]),(0,[z14,z0,z282,z3,z4,z5,z6]),(0,[z0,z1,z3,z667,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z668,z6]),(0,[z0,z1,z3,z4,z537,z5,z6]),(0,[z0,z1,z3,z669,z4,z5,z6])],[(1,[z232,z1,z3,z4,z5,z6])],[(0,[z1,z43,z3,z4,z26,z5,z6]),(0,[z24,z0,z1,z3,z4,z5,z435]),(0,[z0,z1,z3,z4,z5,z670,z6]),(0,[z0,z1,z3,z4,z5,z6,z286]),(0,[z671,z0,z1,z3,z4,z5,z6]),(0,[z41,z0,z1,z3,z4,z17,z6]),(0,[z0,z1,z3,z4,z672,z5,z6])],[(0,[z0,z1,z292,z3,z4,z5,z6]),(1,[z0,z376,z3,z4,z5,z6]),(0,[z80,z0,z1,z3,z4,z5,z144]),(0,[z673,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z20,z91])],[(0,[z0,z320,z43,z3,z4,z5,z6]),(0,[z12,z0,z3,z4,z5,z6,z90]),(0,[z0,z1,z674,z3,z4,z5,z6]),(0,[z675,z0,z1,z3,z4,z5,z6]),(0,[z0,z676,z1,z3,z4,z5,z6]),(0,[z0,z128,z1,z3,z4,z110,z6])]],
   [[(0,[z0,z320,z1,z4,z5,z50,z6]),(0,[z677,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z678]),(0,[z679,z0,z1,z3,z4,z5,z6])],[(0,[z680,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z230,z5,z6])],[(0,[z12,z0,z43,z3,z4,z5,z6]),(0,[z681,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z21,z15,z6]),(1,[z18,z1,z3,z4,z5,z144]),(0,[z0,z682,z1,z3,z4,z5,z6]),(0,[z683,z0,z1,z3,z4,z5,z6]),(1,[z107,z0,z1,z4,z5,z90])],[(1,[z119,z1,z25,z4,z5,z6]),(1,[z0,z1,z299,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z95,z286]),(0,[z0,z1,z81,z4,z5,z50,z6]),(0,[z0,z1,z3,z4,z204,z5,z6])],[(0,[z73,z0,z1,z3,z4,z5,z387]),(0,[z0,z1,z3,z30,z82,z5,z6]),(0,[z265,z128,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z277,z90]),(0,[z684,z0,z1,z3,z4,z5,z6]),(0,[z0,z685,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z686,z6])],[(0,[z12,z0,z3,z4,z5,z6,z91]),(0,[z219,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z348,z6]),(0,[z0,z1,z3,z4,z687,z5,z6])],[(0,[z688,z0,z1,z3,z4,z5,z6]),(0,[z146,z0,z1,z3,z4,z110,z6]),(1,[z0,z1,z3,z4,z297,z5]),(0,[z0,z1,z3,z4,z689,z5,z6]),(0,[z690,z0,z1,z3,z4,z5,z6])],[(0,[z0,z43,z3,z4,z5,z115,z6]),(0,[z619,z0,z43,z3,z4,z5,z6]),(0,[z226,z0,z1,z3,z4,z5,z6]),(0,[z691,z0,z1,z3,z4,z5,z6]),(0,[z73,z0,z3,z4,z5,z277,z6]),(0,[z0,z1,z3,z4,z692,z5,z6]),(0,[z0,z1,z3,z693,z4,z5,z6])]],
   [[(0,[z0,z1,z1,z3,z4,z5,z6]),(0,[z55,z0,z3,z4,z5,z6,z286]),(0,[z694,z0,z1,z3,z4,z5,z6])],[(0,[z476,z0,z43,z3,z4,z5,z6]),(0,[z695,z0,z1,z3,z4,z5,z6]),(0,[z24,z1,z3,z44,z4,z5,z6]),(0,[z0,z1,z3,z4,z696,z5,z6]),(0,[z0,z1,z3,z4,z21,z110,z6]),(0,[z55,z0,z1,z3,z4,z5,z91]),(0,[z697,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z204,z91]),(0,[z126,z0,z1,z3,z5,z6,z91])],[(0,[z0,z1,z3,z4,z94,z5,z144]),(0,[z0,z1,z3,z4,z698,z5,z6]),(0,[z0,z1,z3,z4,z5,z349,z6])],[(0,[z0,z1,z3,z4,z699,z5,z6]),(0,[z0,z1,z330,z3,z4,z5,z6]),(0,[z41,z527,z1,z3,z4,z5,z6])],[(1,[z0,z75,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z5,z6]),(0,[z0,z1,z3,z4,z700,z5,z6])],[(0,[z0,z1,z3,z4,z5,z701,z6]),(0,[z0,z3,z4,z39,z5,z110,z6]),(0,[z0,z1,z3,z83,z4,z17,z6]),(0,[z0,z1,z3,z4,z702,z5,z6])],[(0,[z703,z0,z1,z3,z4,z5,z6]),(0,[z0,z704,z1,z3,z4,z5,z6]),(0,[z0,z320,z1,z36,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z705]),(0,[z0,z1,z3,z4,z5,z6,z706])],[(0,[z119,z0,z43,z3,z4,z5,z6]),(0,[z12,z38,z0,z3,z4,z5,z6]),(0,[z289,z0,z1,z3,z4,z5,z91])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z43,z3,z403,z5,z6]),(0,[z0,z707,z3,z4,z5,z6]),(0,[z38,z0,z3,z537,z39,z5]),(0,[z0,z1,z3,z4,z5,z708]),(0,[z0,z1,z3,z5,z20,z708])],[(0,[z0,z1,z709,z4,z5,z6])],[(0,[z0,z1,z4,z710,z5,z6]),(0,[z0,z1,z3,z204,z200,z91])],[(0,[z43,z3,z4,z5,z6,z595]),(0,[z33,z43,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z711,z6]),(0,[z0,z1,z81,z82,z318,z6]),(0,[z0,z1,z3,z4,z5,z712])],[(0,[z41,z0,z1,z3,z17,z6])],[],[(0,[z12,z0,z3,z4,z228,z6]),(0,[z248,z1,z3,z4,z5,z144]),(0,[z0,z1,z241,z4,z164,z6]),(0,[z713,z1,z3,z4,z5,z6])],[(0,[z714,z0,z3,z4,z5,z6]),(0,[z375,z43,z3,z4,z5,z6]),(0,[z12,z0,z3,z715,z5,z6]),(0,[z0,z1,z3,z4,z716,z5]),(0,[z0,z1,z3,z4,z228,z6]),(0,[z717,z1,z3,z4,z5,z6]),(0,[z41,z0,z1,z3,z230,z17]),(0,[z718,z0,z1,z3,z4,z5])],[(0,[z242,z43,z3,z4,z5,z6]),(0,[z0,z1,z3,z715,z5,z6]),(0,[z12,z0,z3,z100,z5,z6]),(0,[z0,z1,z3,z4,z164,z6])],[(0,[z0,z1,z3,z4,z5,z719]),(0,[z0,z1,z720,z4,z5,z6]),(0,[z721,z1,z3,z4,z5,z6])],[(0,[z407,z43,z3,z26,z5,z6]),(0,[z0,z1,z3,z4,z5,z722]),(0,[z0,z723,z3,z4,z5,z6]),(0,[z1,z3,z4,z7,z724,z6]),(0,[z0,z1,z4,z5,z725,z6])],[(0,[z346,z43,z3,z4,z5,z6]),(0,[z0,z43,z3,z4,z537,z5]),(0,[z0,z1,z3,z4,z5,z726]),(0,[z12,z119,z25,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z727]),(0,[z0,z1,z3,z4,z5,z728])],[(0,[z607,z43,z3,z4,z5,z6]),(0,[z191,z3,z4,z5,z6,z144]),(1,[z0,z1,z3,z729,z6])],[(0,[z11,z1,z299,z4,z5,z6])],[(0,[z43,z3,z4,z112,z5,z6]),(0,[z80,z43,z3,z134,z5,z6]),(0,[z12,z0,z3,z4,z121,z6]),(0,[z85,z1,z3,z45,z5,z6]),(0,[z126,z0,z1,z3,z5,z95])],[(0,[z0,z1,z3,z4,z5,z730]),(0,[z154,z0,z1,z4,z50,z6]),(0,[z107,z0,z1,z4,z5,z731]),(0,[z0,z732,z3,z4,z5,z6])]],
   [[(0,[z117,z1,z3,z123,z5,z6]),(0,[z87,z0,z3,z4,z110,z6])],[(0,[z43,z3,z629,z4,z5,z6])],[(0,[z12,z0,z3,z4,z733,z5]),(0,[z0,z1,z3,z100,z5,z387]),(0,[z0,z1,z241,z4,z50,z6])],[(0,[z232,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z240,z4,z94]),(0,[z0,z734,z3,z4,z5,z6])],[(0,[z0,z1,z3,z5,z708,z130])],[],[(0,[z62,z0,z3,z257,z5,z6]),(0,[z0,z1,z3,z83,z652,z6])],[(0,[z0,z735,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z736])],[(0,[z153,z1,z44,z4,z5,z6]),(0,[z0,z1,z3,z4,z121,z387]),(0,[z0,z737,z3,z4,z5,z6]),(0,[z0,z1,z3,z5,z20,z159])],[(1,[z43,z299,z4,z5,z6]),(0,[z509,z43,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z738,z5]),(0,[z0,z3,z4,z5,z6,z739]),(0,[z54,z0,z1,z3,z5,z167])],[(0,[z740,z0,z1,z3,z4,z5]),(0,[z55,z308,z3,z4,z5,z286])],[(0,[z24,z1,z44,z403,z5,z6]),(1,[z1,z3,z4,z5,z741]),(0,[z54,z0,z1,z3,z5,z413]),(0,[z0,z1,z3,z4,z742,z5])],[(0,[z417,z0,z3,z4,z5,z280]),(0,[z743,z0,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z744]),(0,[z0,z1,z3,z4,z5,z745]),(0,[z308,z1,z3,z4,z5,z91])],[(0,[z746,z0,z43,z3,z4,z5]),(0,[z107,z0,z1,z4,z449,z90])],[(0,[z573,z43,z3,z4,z5,z6]),(0,[z0,z1,z4,z5,z233,z6]),(0,[z0,z1,z3,z4,z5,z747]),(0,[z0,z1,z3,z4,z239,z91]),(0,[z0,z1,z3,z129,z4,z341])],[(0,[z12,z0,z3,z4,z204,z91]),(0,[z38,z99,z0,z3,z39,z5]),(0,[z0,z1,z3,z4,z748,z5])]],
   [[(0,[z43,z3,z4,z5,z178,z6]),(0,[z0,z43,z3,z4,z5,z400]),(0,[z0,z75,z3,z403,z5,z6]),(0,[z1,z3,z4,z5,z6,z749]),(0,[z0,z1,z3,z4,z204,z91])],[(0,[z0,z1,z3,z4,z750,z6])],[(0,[z43,z3,z26,z5,z20,z6]),(0,[z0,z3,z4,z5,z751,z6])],[(0,[z0,z1,z92,z4,z5,z90])],[(0,[z0,z1,z3,z429,z5,z435]),(0,[z0,z1,z752,z4,z5,z6]),(0,[z0,z753,z3,z4,z5,z6])],[(0,[z0,z43,z3,z4,z5,z435]),(0,[z12,z85,z3,z4,z7,z6])],[(0,[z0,z1,z3,z4,z754,z6]),(0,[z0,z1,z3,z4,z5,z755]),(0,[z756,z0,z3,z4,z5,z6])],[(0,[z12,z43,z3,z4,z5,z6]),(0,[z0,z338,z3,z4,z5,z269]),(0,[z0,z171,z299,z4,z5,z6]),(0,[z80,z47,z3,z4,z5,z115])],[(0,[z11,z12,z3,z4,z5,z6]),(0,[z0,z1,z3,z757,z5,z6])],[],[(0,[z0,z1,z3,z758,z5,z6]),(0,[z43,z3,z4,z5,z144,z90]),(0,[z0,z1,z3,z4,z5,z759]),(0,[z0,z760,z3,z4,z5,z6])],[(0,[z506,z43,z3,z4,z5,z6]),(0,[z38,z0,z3,z39,z5,z6]),(0,[z0,z96,z3,z4,z50,z6]),(0,[z76,z1,z3,z4,z5,z42])],[(0,[z12,z0,z3,z4,z114,z6]),(0,[z0,z1,z3,z4,z5,z761]),(0,[z0,z1,z3,z83,z46,z6])],[(0,[z24,z12,z44,z4,z5,z6]),(0,[z73,z117,z36,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z762]),(0,[z0,z1,z763,z4,z5,z6]),(0,[z0,z764,z3,z4,z5,z6]),(0,[z0,z1,z3,z5,z6,z708])],[(0,[z383,z43,z3,z4,z5,z6]),(0,[z0,z43,z3,z4,z5,z562]),(0,[z0,z53,z3,z4,z5,z6]),(0,[z11,z1,z3,z112,z5,z6]),(0,[z0,z1,z3,z4,z5,z765])],[(0,[z0,z43,z3,z5,z6,z200]),(0,[z0,z1,z3,z4,z766,z5]),(0,[z1,z3,z4,z5,z741,z144])]],
   [[(0,[z0,z1,z767,z4,z5,z6]),(0,[z0,z1,z3,z768,z5,z6]),(0,[z136,z0,z330,z4,z5,z6]),(0,[z54,z0,z1,z3,z479,z5])],[(0,[z0,z43,z769,z4,z5,z6]),(0,[z0,z74,z3,z4,z13,z6]),(0,[z452,z1,z3,z4,z15,z6])],[(0,[z306,z43,z3,z4,z5,z6]),(0,[z0,z74,z3,z4,z5,z6]),(0,[z770,z0,z3,z4,z5,z6])],[(0,[z43,z3,z4,z699,z5,z6]),(0,[z0,z191,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z6,z771]),(0,[z0,z135,z1,z4,z50,z6])],[(1,[z772,z3,z4,z5,z6]),(0,[z43,z3,z4,z251,z5,z6]),(0,[z773,z1,z3,z4,z5,z6]),(0,[z0,z3,z30,z774,z5,z6])],[(0,[z0,z1,z3,z100,z121,z6]),(0,[z775,z1,z3,z4,z5,z6]),(0,[z0,z3,z4,z774,z5,z6]),(0,[z0,z776,z3,z4,z5,z6])],[(0,[z0,z777,z3,z4,z5,z6]),(0,[z778,z1,z3,z4,z5,z6])],[(0,[z779,z43,z3,z4,z5,z6]),(0,[z99,z0,z1,z3,z4,z5]),(0,[z0,z1,z247,z4,z5,z731])],[(0,[z0,z1,z4,z5,z6,z780]),(0,[z0,z171,z3,z34,z5,z6]),(0,[z289,z0,z3,z4,z5,z781])],[(0,[z18,z43,z3,z4,z5,z144]),(0,[z49,z0,z43,z4,z50,z6]),(0,[z0,z1,z3,z4,z5,z269])],[(0,[z43,z3,z4,z21,z7,z6]),(1,[z43,z3,z112,z5,z6]),(0,[z127,z119,z25,z4,z5,z6]),(0,[z0,z1,z3,z782,z5,z6])],[(0,[z1,z783,z44,z4,z5,z6]),(0,[z0,z1,z3,z528,z4,z94]),(1,[z0,z1,z3,z4,z742])],[(0,[z14,z43,z3,z4,z5,z348]),(0,[z0,z1,z3,z4,z784,z5]),(0,[z0,z785,z3,z4,z5,z6]),(0,[z41,z0,z96,z3,z17,z6])],[(0,[z43,z3,z4,z45,z5,z6]),(0,[z0,z43,z3,z4,z297,z5]),(0,[z0,z1,z380,z4,z5,z42])],[(0,[z12,z0,z3,z123,z5,z6]),(0,[z0,z1,z4,z786,z5,z6]),(0,[z0,z3,z4,z5,z6,z331])],[(0,[z43,z3,z281,z4,z5,z6]),(0,[z0,z1,z3,z4,z787,z6]),(0,[z0,z1,z3,z123,z5,z6])]],
   [[(0,[z12,z158,z3,z4,z5,z6]),(0,[z24,z1,z44,z4,z5,z435])],[(0,[z54,z43,z3,z26,z5,z6]),(0,[z468,z43,z3,z4,z5,z6])],[(0,[z43,z3,z4,z5,z6,z70]),(0,[z12,z308,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z788]),(0,[z0,z789,z3,z4,z5,z6])],[(0,[z268,z1,z3,z4,z5,z6]),(0,[z141,z43,z3,z4,z5,z6]),(0,[z11,z98,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z731])],[],[(0,[z0,z1,z3,z403,z5,z435]),(0,[z0,z1,z790,z4,z5,z6]),(0,[z89,z0,z1,z768,z5,z6])],[(0,[z62,z184,z3,z4,z5,z6]),(0,[z527,z1,z3,z4,z50,z6]),(0,[z0,z1,z203,z4,z204,z91])],[(0,[z0,z3,z4,z5,z6,z791])],[(0,[z0,z1,z3,z4,z5,z792]),(0,[z336,z0,z3,z30,z5,z6])],[(0,[z0,z1,z3,z4,z793,z6]),(0,[z1,z3,z4,z5,z724,z6]),(0,[z0,z794,z3,z4,z5,z6])],[(0,[z12,z0,z3,z4,z164,z6]),(0,[z0,z1,z795,z4,z5,z6]),(0,[z796,z1,z3,z4,z5,z6]),(0,[z0,z797,z3,z4,z5,z6])],[(0,[z14,z1,z287,z4,z15,z6]),(0,[z29,z232,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z349,z90])],[(0,[z0,z43,z3,z4,z5,z348]),(0,[z0,z1,z3,z798,z5,z6]),(0,[z0,z1,z799,z4,z5,z6]),(0,[z345,z0,z1,z4,z50,z6]),(0,[z0,z128,z241,z4,z124,z6]),(0,[z41,z527,z1,z3,z17,z6])],[(0,[z0,z1,z3,z4,z5,z800])],[(0,[z0,z43,z4,z5,z801,z6]),(0,[z0,z43,z3,z4,z5,z57]),(0,[z1,z3,z4,z5,z741,z6]),(0,[z0,z128,z3,z4,z124,z6]),(0,[z0,z802,z3,z4,z5,z6])],[(0,[z146,z0,z3,z4,z751,z6])]],
   [[(0,[z168,z43,z3,z19,z5,z6]),(0,[z11,z1,z3,z4,z5,z166]),(0,[z0,z1,z803,z4,z5,z6]),(0,[z1,z3,z4,z5,z115,z741]),(0,[z268,z55,z3,z4,z5,z286]),(0,[z0,z1,z3,z4,z5,z804]),(0,[z0,z1,z3,z83,z729,z6])],[(0,[z684,z43,z3,z4,z5,z6]),(0,[z219,z0,z253,z4,z5,z6]),(0,[z0,z1,z3,z4,z805,z6])],[(0,[z0,z1,z109,z4,z5,z95])],[(0,[z76,z43,z3,z4,z5,z6]),(0,[z0,z806,z3,z4,z5,z6]),(0,[z0,z1,z807,z4,z5,z6]),(0,[z0,z1,z81,z82,z228,z6])],[(0,[z98,z0,z3,z112,z5,z6]),(0,[z0,z1,z3,z4,z164,z387])],[(0,[z808,z0,z3,z4,z5,z6]),(0,[z0,z1,z3,z5,z6,z809]),(0,[z126,z0,z1,z3,z204,z91])],[(0,[z186,z0,z3,z4,z5,z6]),(0,[z127,z43,z3,z4,z5,z6]),(0,[z24,z1,z783,z4,z5,z6]),(0,[z73,z0,z36,z4,z5,z319]),(0,[z41,z76,z1,z3,z17,z6])],[(0,[z613,z12,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z810]),(0,[z460,z1,z3,z4,z5,z115])],[(0,[z43,z3,z4,z26,z5,z6]),(0,[z0,z1,z3,z4,z5,z811]),(0,[z0,z1,z3,z4,z216,z91])],[(0,[z0,z1,z3,z4,z5,z812])],[(0,[z0,z1,z3,z4,z244,z91])],[(0,[z0,z43,z3,z112,z5,z6]),(0,[z333,z43,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z813,z6])],[(0,[z43,z3,z4,z5,z6,z162]),(1,[z43,z3,z4,z5,z166]),(0,[z814,z1,z3,z4,z5,z6]),(0,[z815,z1,z3,z4,z5,z6]),(0,[z126,z0,z1,z3,z5,z20])],[(0,[z43,z3,z4,z5,z6,z166]),(0,[z11,z1,z3,z45,z5,z6]),(0,[z816,z12,z0,z3,z4,z5]),(1,[z1,z783,z4,z5,z6]),(0,[z0,z817,z3,z4,z5,z6])],[(0,[z24,z75,z44,z4,z5,z6]),(0,[z295,z3,z4,z26,z5,z6]),(0,[z0,z818,z3,z4,z5,z6])],[(0,[z43,z3,z170,z4,z5,z6]),(0,[z78,z43,z3,z26,z5,z6]),(0,[z521,z1,z3,z4,z5,z144]),(0,[z819,z1,z3,z4,z5,z6]),(0,[z0,z1,z4,z5,z731,z90])]],
   [[(0,[z820,z0,z3,z4,z5,z6]),(0,[z12,z0,z4,z5,z233,z6]),(0,[z0,z821,z3,z4,z5,z6])],[(0,[z23,z43,z3,z4,z5,z6]),(0,[z0,z822,z3,z4,z5,z6]),(0,[z0,z823,z3,z4,z5,z6]),(0,[z0,z1,z3,z669,z5,z20])],[(0,[z824,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z825,z6]),(0,[z35,z3,z36,z4,z5,z6])],[(0,[z0,z1,z3,z4,z826,z6]),(0,[z0,z827,z3,z4,z5,z6])],[(0,[z0,z43,z380,z4,z5,z6]),(0,[z0,z1,z828,z4,z5,z6]),(0,[z54,z0,z1,z3,z5,z130])],[(0,[z561,z43,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z829,z6]),(0,[z830,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z831,z5,z6])],[(0,[z0,z1,z3,z4,z5,z832]),(0,[z43,z44,z4,z5,z50,z6]),(0,[z0,z1,z3,z4,z424,z91])],[(0,[z0,z1,z3,z4,z5,z833]),(0,[z0,z834,z3,z4,z5,z6]),(0,[z0,z1,z835,z4,z5,z6]),(0,[z0,z1,z3,z4,z742,z204])],[(1,[z43,z3,z45,z5,z6]),(0,[z85,z43,z3,z4,z7,z6]),(0,[z308,z1,z3,z4,z5,z6]),(0,[z0,z1,z123,z5,z50,z6]),(1,[z0,z3,z774,z5,z6])],[(0,[z836,z0,z43,z4,z5,z6]),(0,[z158,z43,z3,z4,z5,z6]),(0,[z386,z0,z1,z4,z50,z6]),(0,[z0,z171,z3,z4,z5,z166]),(0,[z0,z1,z3,z134,z5,z115]),(0,[z0,z3,z4,z5,z277,z364]),(0,[z0,z1,z3,z4,z837,z6])],[(0,[z184,z43,z3,z4,z5,z6]),(0,[z0,z1,z4,z5,z838,z6]),(0,[z0,z1,z3,z123,z121,z6]),(0,[z41,z0,z1,z3,z446,z6])],[(0,[z43,z3,z4,z5,z211,z6]),(0,[z839,z1,z3,z4,z5,z6]),(0,[z0,z840,z3,z4,z5,z6])],[(0,[z14,z43,z299,z4,z5,z6]),(0,[z14,z43,z3,z4,z5,z166]),(0,[z841,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z842])],[(0,[z43,z3,z217,z4,z5,z6]),(0,[z126,z0,z43,z3,z5,z6]),(0,[z12,z0,z3,z83,z46,z6]),(0,[z671,z1,z3,z4,z15,z6])],[(0,[z107,z0,z43,z4,z5,z90]),(0,[z0,z843,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z844])]],
   [[(0,[z12,z508,z3,z4,z5,z6]),(0,[z845,z0,z3,z4,z5,z6])],[(0,[z0,z282,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z13,z411]),(0,[z78,z376,z3,z26,z5,z6]),(0,[z0,z1,z3,z100,z164,z6])],[(0,[z43,z3,z4,z410,z5,z6]),(0,[z0,z1,z3,z4,z5,z411]),(0,[z846,z1,z3,z4,z5,z6]),(0,[z0,z1,z847,z4,z5,z6]),(0,[z0,z1,z4,z204,z432,z91])],[(0,[z0,z1,z3,z26,z16,z5])],[(0,[z14,z779,z3,z4,z5,z6]),(0,[z0,z1,z3,z34,z5,z348]),(0,[z848,z1,z3,z4,z5,z6]),(0,[z527,z1,z3,z5,z17,z6])],[(0,[z0,z849,z3,z4,z5,z6])],[(0,[z168,z43,z3,z4,z5,z269]),(0,[z0,z43,z3,z4,z850,z6]),(0,[z0,z851,z3,z4,z5,z6]),(0,[z0,z1,z852,z4,z5,z6])],[(0,[z0,z43,z3,z4,z5,z853]),(0,[z0,z171,z3,z45,z5,z6])],[(0,[z54,z0,z1,z3,z5,z482])],[],[(0,[z14,z43,z3,z45,z5,z6]),(0,[z43,z3,z4,z264,z5,z6])],[(0,[z12,z0,z3,z4,z5,z269]),(0,[z1,z3,z4,z724,z15,z6])],[(0,[z0,z1,z3,z429,z5,z6]),(0,[z0,z74,z3,z4,z114,z6]),(0,[z854,z0,z3,z4,z5,z6]),(0,[z0,z1,z330,z4,z5,z319]),(0,[z0,z1,z4,z50,z90,z91])],[(0,[z0,z1,z3,z855,z5,z6]),(0,[z0,z43,z299,z4,z5,z6]),(0,[z0,z43,z3,z4,z5,z166]),(0,[z190,z43,z3,z4,z5,z6]),(0,[z0,z320,z253,z4,z5,z6]),(0,[z38,z184,z3,z39,z5,z6]),(0,[z0,z1,z330,z4,z5,z324])],[(0,[z14,z43,z3,z34,z5,z6]),(0,[z0,z1,z783,z4,z5,z6]),(0,[z732,z1,z3,z4,z5,z6]),(0,[z76,z1,z3,z4,z5,z57])],[(0,[z0,z1,z3,z4,z5,z856]),(0,[z0,z1,z3,z4,z5,z741])]],
   [[(0,[z54,z43,z3,z4,z5,z144]),(1,[z0,z720,z4,z5,z6]),(0,[z0,z1,z3,z4,z857,z5]),(0,[z0,z1,z3,z4,z5,z858]),(0,[z0,z1,z3,z4,z5,z859]),(0,[z860,z1,z3,z4,z5,z6])],[],[(0,[z126,z12,z0,z3,z5,z6]),(0,[z126,z0,z1,z3,z5,z90])],[(0,[z107,z12,z0,z4,z5,z90])],[(0,[z255,z43,z3,z4,z5,z6]),(0,[z0,z779,z3,z4,z5,z6]),(0,[z12,z0,z3,z4,z5,z788]),(0,[z861,z0,z3,z4,z5,z6])],[(0,[z33,z1,z3,z26,z5,z6])],[(0,[z772,z43,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z862,z5]),(0,[z0,z1,z3,z83,z539,z6])],[],[(0,[z0,z75,z3,z4,z5,z435])],[(0,[z35,z1,z3,z4,z5,z319]),(0,[z133,z232,z3,z4,z5,z6])],[(0,[z0,z43,z3,z45,z5,z6]),(0,[z0,z43,z3,z863,z5,z6]),(0,[z12,z78,z3,z26,z5,z6]),(0,[z0,z1,z4,z5,z864,z6]),(0,[z865,z0,z3,z4,z5,z6])],[(0,[z0,z1,z3,z123,z5,z387]),(0,[z89,z0,z1,z27,z5,z6]),(0,[z136,z0,z3,z4,z94,z5])],[(0,[z1,z3,z783,z4,z5,z6]),(0,[z126,z0,z1,z3,z50,z6])],[(0,[z99,z0,z43,z3,z4,z5]),(0,[z168,z295,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z866,z5]),(0,[z0,z1,z4,z867,z5,z6])],[(0,[z0,z43,z3,z34,z5,z6]),(0,[z0,z1,z3,z4,z16,z5])],[(0,[z0,z1,z3,z4,z868,z6])]],
   [[(0,[z0,z43,z3,z4,z869,z6]),(0,[z0,z43,z3,z4,z5,z279]),(0,[z49,z12,z0,z4,z50,z6]),(0,[z0,z1,z3,z870,z5,z6]),(0,[z0,z1,z3,z4,z173,z91]),(0,[z871,z0,z3,z4,z5,z6]),(0,[z0,z1,z380,z4,z5,z57])],[(0,[z117,z43,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z872,z6]),(0,[z0,z1,z3,z873,z5,z6]),(0,[z0,z152,z720,z4,z5,z6]),(0,[z0,z1,z4,z5,z874,z6]),(0,[z54,z527,z1,z3,z5,z6])],[(0,[z43,z3,z4,z492,z5,z6])],[(0,[z12,z574,z3,z4,z5,z6]),(0,[z0,z1,z3,z26,z5,z444])],[(0,[z192,z43,z3,z4,z5,z6]),(0,[z55,z0,z3,z4,z5,z70]),(0,[z0,z1,z3,z4,z5,z875]),(0,[z680,z1,z3,z4,z5,z115]),(0,[z0,z1,z876,z4,z5,z6])],[(0,[z0,z1,z3,z4,z877,z6]),(0,[z76,z1,z380,z4,z5,z6])],[(0,[z43,z330,z44,z4,z5,z6]),(0,[z190,z158,z3,z4,z5,z6]),(0,[z370,z18,z3,z4,z5,z144]),(0,[z0,z878,z3,z4,z5,z6])],[],[(0,[z43,z3,z4,z343,z5,z6]),(0,[z0,z1,z879,z4,z5,z6]),(0,[z0,z1,z3,z4,z880,z6]),(0,[z0,z1,z3,z4,z5,z42]),(0,[z0,z1,z3,z5,z20,z42])],[],[(0,[z35,z1,z3,z4,z5,z6])],[(0,[z772,z23,z3,z4,z5,z6]),(0,[z43,z3,z68,z4,z5,z144]),(0,[z881,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z882]),(0,[z0,z338,z3,z4,z5,z444]),(0,[z0,z1,z3,z883,z5,z6]),(0,[z0,z1,z884,z4,z5,z6]),(0,[z0,z1,z885,z4,z5,z6])],[(0,[z41,z0,z43,z3,z17,z6]),(0,[z886,z1,z3,z4,z5,z6])],[(0,[z407,z0,z3,z416,z5,z6]),(0,[z226,z0,z170,z4,z5,z6]),(0,[z887,z1,z3,z4,z5,z6])],[(0,[z43,z3,z4,z357,z5,z6]),(0,[z1,z3,z4,z5,z888,z6]),(0,[z0,z1,z425,z4,z5,z42])]],
   [[(0,[z889,z0,z3,z4,z5,z6]),(0,[z54,z308,z1,z3,z4,z5])],[(0,[z890,z0,z3,z4,z5,z6])],[(0,[z0,z1,z3,z891,z5,z6])],[(0,[z0,z1,z3,z4,z892,z6]),(0,[z43,z3,z371,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z893]),(0,[z136,z0,z3,z68,z4,z5]),(0,[z0,z1,z3,z4,z5,z894])],[(0,[z0,z256,z3,z4,z124,z6]),(0,[z0,z1,z3,z4,z5,z895])],[(0,[z0,z1,z3,z4,z5,z896]),(0,[z11,z127,z3,z4,z5,z6]),(0,[z0,z1,z621,z82,z5,z6]),(0,[z0,z1,z299,z34,z5,z6]),(0,[z0,z1,z3,z4,z21,z42]),(0,[z0,z897,z3,z4,z5,z6])],[(0,[z12,z0,z3,z4,z826,z6]),(0,[z0,z1,z3,z4,z5,z898]),(0,[z0,z1,z299,z4,z5,z348]),(0,[z0,z1,z3,z4,z5,z899])],[(0,[z245,z43,z3,z26,z5,z6]),(0,[z407,z1,z3,z26,z5,z6]),(0,[z0,z1,z3,z4,z900,z5])],[(0,[z168,z43,z3,z4,z5,z444]),(0,[z119,z53,z25,z4,z5,z6]),(0,[z0,z1,z3,z4,z901,z6]),(0,[z73,z0,z569,z4,z5,z6]),(0,[z0,z1,z3,z4,z537,z5]),(0,[z29,z0,z3,z351,z5,z6])],[(0,[z184,z3,z4,z39,z5,z6]),(0,[z76,z902,z3,z4,z5,z6])],[(0,[z73,z0,z36,z4,z5,z6]),(0,[z0,z1,z4,z297,z5,z233])],[],[(0,[z0,z903,z3,z4,z5,z6]),(0,[z0,z904,z3,z4,z5,z6]),(0,[z684,z1,z25,z4,z5,z6])],[(0,[z0,z171,z3,z4,z5,z6]),(0,[z12,z0,z4,z5,z838,z6]),(0,[z12,z0,z3,z4,z5,z444])],[(0,[z43,z3,z4,z5,z392,z6]),(0,[z1,z43,z299,z4,z5,z6]),(0,[z619,z0,z3,z4,z5,z277]),(0,[z0,z1,z3,z4,z5,z444]),(0,[z0,z1,z68,z4,z432,z5])],[(0,[z0,z43,z3,z4,z5,z319]),(0,[z1,z3,z4,z905,z5,z6]),(0,[z0,z1,z3,z68,z5,z595]),(0,[z0,z1,z3,z4,z906,z6]),(0,[z0,z96,z3,z4,z5,z42])]],
   [[(0,[z14,z43,z3,z4,z5,z6]),(0,[z0,z43,z3,z4,z5,z324]),(0,[z0,z1,z3,z907,z5,z6]),(0,[z0,z1,z3,z4,z5,z908]),(1,[z1,z3,z4,z724,z6]),(0,[z890,z76,z3,z4,z5,z6])],[(0,[z41,z12,z0,z3,z17,z6])],[],[(0,[z0,z3,z4,z5,z6,z909]),(0,[z0,z1,z3,z45,z5,z348]),(0,[z136,z0,z3,z4,z5,z277])],[(0,[z12,z0,z3,z4,z5,z411]),(0,[z219,z35,z3,z4,z5,z6]),(0,[z0,z1,z910,z4,z5,z6])],[(0,[z911,z0,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z912,z6])],[(0,[z0,z913,z3,z4,z5,z6])],[(0,[z914,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z915,z5,z6])],[(0,[z98,z0,z3,z4,z5,z6]),(0,[z577,z43,z3,z4,z5,z6]),(0,[z0,z352,z3,z4,z5,z42])],[],[(0,[z43,z3,z431,z4,z5,z6]),(0,[z35,z1,z4,z5,z50,z6]),(0,[z916,z1,z3,z4,z5,z6]),(0,[z0,z1,z241,z4,z5,z400]),(0,[z917,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z918,z5,z6]),(0,[z460,z43,z3,z4,z5,z6]),(0,[z12,z0,z3,z4,z5,z400]),(0,[z0,z1,z3,z4,z919,z6]),(0,[z0,z1,z3,z5,z6,z920]),(0,[z0,z1,z3,z921,z5,z6])],[(0,[z43,z3,z440,z4,z5,z6]),(0,[z0,z282,z287,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z400])],[(0,[z0,z43,z3,z4,z349,z6]),(0,[z0,z43,z241,z4,z5,z6]),(0,[z0,z1,z3,z922,z5,z6]),(0,[z12,z0,z3,z429,z5,z6]),(0,[z0,z1,z3,z429,z13,z6]),(0,[z0,z720,z36,z4,z5,z6]),(0,[z0,z1,z4,z244,z50,z6]),(1,[z0,z1,z4,z432,z91])],[(0,[z62,z43,z3,z4,z5,z6]),(0,[z0,z1,z923,z4,z5,z6]),(0,[z0,z1,z3,z924,z5,z6])]],
   [[(0,[z0,z43,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z925])],[(0,[z0,z1,z3,z4,z5,z926]),(0,[z14,z1,z3,z4,z724,z6])],[(0,[z0,z1,z81,z768,z5,z6])],[(0,[z841,z0,z43,z3,z4,z5])],[(0,[z43,z3,z4,z5,z6,z144]),(0,[z0,z1,z3,z68,z700,z5]),(0,[z0,z927,z3,z4,z5,z6])],[(0,[z928,z0,z3,z4,z5,z6])],[(0,[z265,z282,z3,z4,z5,z6]),(0,[z929,z0,z3,z4,z5,z6])],[(0,[z0,z43,z425,z4,z5,z6]),(0,[z930,z0,z3,z4,z5,z6])],[(0,[z12,z0,z3,z4,z931,z6]),(0,[z12,z0,z3,z4,z862,z5]),(0,[z0,z1,z3,z4,z932,z6]),(0,[z1,z3,z26,z5,z254,z6]),(0,[z98,z0,z3,z134,z5,z6]),(0,[z0,z320,z152,z4,z5,z6]),(0,[z933,z1,z3,z4,z5,z6])],[(0,[z0,z406,z292,z4,z5,z6]),(0,[z0,z1,z3,z4,z931,z6]),(0,[z376,z3,z4,z26,z5,z6]),(0,[z0,z1,z3,z4,z5,z934]),(0,[z0,z1,z4,z432,z6,z91])],[(0,[z43,z3,z4,z5,z95,z144]),(0,[z0,z43,z4,z432,z5,z6]),(0,[z12,z653,z3,z4,z5,z6]),(0,[z935,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z21,z400]),(0,[z936,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z937]),(0,[z527,z1,z3,z4,z5,z42])],[(0,[z0,z1,z3,z4,z5,z938]),(0,[z939,z0,z3,z4,z5,z6]),(0,[z0,z1,z3,z940,z5,z6]),(0,[z0,z1,z3,z4,z5,z941]),(0,[z0,z1,z3,z942,z5,z6]),(0,[z0,z1,z943,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z562])],[(0,[z0,z1,z3,z4,z5,z944]),(0,[z38,z158,z3,z39,z5,z6]),(0,[z0,z1,z3,z5,z6,z200])],[(0,[z73,z0,z170,z4,z5,z6]),(0,[z29,z0,z3,z257,z5,z6]),(0,[z0,z1,z3,z4,z5,z945]),(0,[z126,z0,z1,z3,z5,z42])],[(0,[z0,z946,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z947])],[(0,[z0,z43,z3,z134,z5,z6]),(0,[z1,z43,z3,z112,z5,z6]),(0,[z0,z152,z4,z5,z6,z227]),(0,[z0,z1,z3,z4,z948,z5])]],
   [[(0,[z12,z0,z3,z4,z16,z5]),(0,[z14,z282,z3,z4,z15,z6]),(0,[z126,z289,z0,z1,z3,z5])],[(0,[z190,z0,z3,z4,z5,z269]),(0,[z0,z1,z3,z4,z724,z6]),(0,[z0,z1,z3,z4,z5,z949]),(0,[z950,z1,z3,z4,z5,z6])],[(0,[z43,z3,z4,z486,z5,z6]),(0,[z0,z376,z3,z4,z5,z6]),(0,[z547,z1,z3,z26,z5,z6]),(0,[z0,z229,z3,z4,z124,z6]),(0,[z951,z1,z3,z4,z5,z6])],[(0,[z0,z1,z952,z4,z5,z6]),(0,[z126,z0,z1,z3,z5,z115]),(0,[z953,z1,z3,z4,z5,z6])],[(0,[z631,z43,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z954,z5]),(0,[z107,z136,z0,z4,z5,z90])],[(0,[z955,z1,z3,z4,z5,z6])],[(0,[z73,z0,z36,z4,z121,z6]),(0,[z956,z1,z3,z4,z5,z6])],[(0,[z0,z1,z299,z4,z5,z166])],[(0,[z957,z1,z3,z4,z5,z6]),(0,[z0,z1,z241,z4,z297,z5]),(0,[z0,z1,z4,z228,z50,z6]),(0,[z958,z0,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z21,z562]),(0,[z959,z0,z3,z4,z5,z6])],[(0,[z43,z3,z4,z5,z6,z499]),(0,[z0,z1,z3,z4,z960,z6]),(0,[z0,z1,z4,z768,z5,z6])],[(0,[z12,z0,z3,z4,z5,z42]),(0,[z24,z1,z44,z4,z13,z6])],[(0,[z24,z1,z44,z4,z5,z6]),(0,[z0,z1,z3,z4,z961,z6]),(0,[z73,z308,z3,z4,z5,z6])],[(0,[z256,z43,z3,z4,z7,z6]),(0,[z0,z962,z3,z4,z5,z6])],[(0,[z43,z3,z4,z507,z5,z6]),(0,[z675,z43,z3,z4,z5,z6]),(0,[z132,z1,z3,z4,z5,z144]),(0,[z963,z0,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z729,z6])],[],[(0,[z0,z3,z4,z5,z6,z964]),(0,[z12,z0,z3,z403,z5,z6]),(0,[z0,z1,z3,z403,z13,z6]),(0,[z0,z965,z3,z4,z5,z6]),(0,[z0,z128,z3,z4,z150,z6]),(0,[z690,z0,z1,z4,z5,z90])]],
   [[(0,[z0,z75,z3,z4,z5,z6]),(0,[z0,z1,z3,z403,z5,z6]),(0,[z0,z3,z966,z4,z5,z6]),(0,[z0,z967,z3,z4,z5,z6])],[(0,[z89,z0,z43,z27,z5,z6]),(0,[z0,z1,z968,z4,z5,z6]),(0,[z55,z0,z3,z4,z5,z319]),(0,[z0,z1,z3,z4,z5,z969]),(0,[z1,z3,z4,z970,z5,z6])],[(0,[z452,z43,z3,z4,z5,z6]),(0,[z0,z1,z3,z971,z5,z6]),(0,[z0,z1,z3,z4,z5,z972])],[(0,[z973,z0,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z974,z6]),(0,[z0,z1,z299,z45,z5,z6]),(0,[z0,z1,z3,z45,z5,z166]),(0,[z73,z0,z720,z4,z5,z6])],[(0,[z0,z43,z3,z975,z4,z5]),(0,[z0,z976,z3,z4,z5,z6]),(0,[z131,z0,z1,z27,z5,z6]),(0,[z0,z977,z3,z4,z5,z6])],[(0,[z0,z43,z203,z4,z5,z6]),(0,[z12,z0,z3,z4,z5,z895]),(0,[z12,z18,z3,z4,z5,z144]),(0,[z0,z1,z3,z4,z5,z978]),(0,[z979,z1,z3,z4,z5,z6]),(0,[z265,z128,z3,z4,z124,z6])],[(0,[z0,z1,z3,z4,z980,z6]),(0,[z55,z0,z3,z4,z5,z781]),(0,[z981,z1,z3,z4,z5,z6])],[(0,[z43,z3,z536,z4,z5,z6]),(0,[z0,z43,z3,z129,z4,z94]),(0,[z0,z1,z3,z34,z5,z166])],[(0,[z0,z982,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z983,z6]),(0,[z984,z0,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z348]),(0,[z35,z3,z4,z5,z277,z6]),(0,[z690,z0,z1,z4,z50,z6])],[(0,[z219,z43,z3,z4,z5,z6]),(0,[z43,z3,z82,z26,z5,z6]),(0,[z12,z0,z3,z4,z537,z5]),(0,[z0,z1,z985,z4,z5,z6]),(0,[z0,z1,z3,z123,z164,z6])],[(0,[z0,z1,z3,z4,z5,z57])],[(0,[z0,z1,z4,z5,z50,z562]),(0,[z54,z0,z1,z3,z5,z708])],[(0,[z685,z43,z3,z4,z5,z6])],[(0,[z0,z986,z3,z4,z5,z6]),(0,[z41,z0,z1,z380,z17,z6])],[(0,[z136,z0,z3,z4,z5,z319])]],
   [[(0,[z76,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z987,z5]),(0,[z85,z1,z3,z4,z201,z6])],[(0,[z1,z43,z3,z4,z5,z166]),(0,[z0,z988,z3,z4,z5,z6])],[(0,[z43,z3,z4,z302,z5,z6]),(0,[z527,z43,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z989]),(0,[z0,z990,z3,z4,z5,z6]),(0,[z0,z1,z425,z4,z5,z57])],[(0,[z43,z3,z4,z554,z5,z6]),(0,[z43,z3,z4,z556,z5,z6]),(0,[z0,z1,z3,z4,z5,z991]),(0,[z452,z0,z1,z3,z17,z6]),(0,[z992,z0,z3,z4,z5,z6]),(0,[z993,z1,z3,z4,z5,z6])],[(0,[z480,z0,z3,z39,z5,z6]),(0,[z0,z1,z330,z4,z228,z6]),(0,[z0,z1,z3,z4,z994,z5])],[(0,[z0,z1,z3,z995,z5,z6]),(0,[z43,z3,z4,z7,z5,z6]),(0,[z996,z0,z3,z4,z5,z6]),(0,[z997,z1,z3,z4,z5,z6])],[(0,[z998,z0,z3,z4,z5,z6]),(0,[z73,z0,z36,z4,z5,z387]),(0,[z136,z0,z3,z4,z5,z91])],[(0,[z0,z128,z3,z4,z302,z6]),(0,[z0,z320,z720,z4,z5,z6]),(0,[z999,z0,z1,z3,z5,z6]),(0,[z76,z1,z425,z4,z5,z6])],[],[(0,[z414,z43,z3,z4,z5,z6]),(0,[z680,z43,z3,z4,z5,z6]),(0,[z0,z171,z287,z4,z5,z6]),(0,[z1000,z1,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z781,z6]),(0,[z0,z1,z3,z1001,z5,z6]),(0,[z41,z0,z1,z3,z16,z17])],[],[(0,[z406,z43,z44,z4,z5,z6]),(0,[z1002,z0,z3,z4,z5,z6]),(0,[z407,z0,z3,z39,z5,z6]),(0,[z0,z1,z3,z4,z1003,z6]),(0,[z54,z136,z0,z3,z4,z5])],[(0,[z14,z43,z287,z4,z5,z6]),(0,[z73,z35,z36,z4,z5,z6]),(0,[z0,z1004,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z1005,z6]),(0,[z0,z1006,z3,z4,z5,z6])],[(0,[z80,z43,z3,z4,z5,z115]),(0,[z29,z184,z3,z4,z5,z6]),(0,[z1007,z0,z3,z4,z5,z6])],[(0,[z54,z0,z43,z3,z5,z130]),(0,[z1,z43,z3,z45,z5,z6]),(0,[z476,z0,z3,z4,z110,z6]),(0,[z0,z1,z3,z4,z1008,z6])],[(0,[z0,z43,z3,z4,z230,z5]),(0,[z0,z1,z3,z4,z114,z411]),(0,[z0,z1,z3,z4,z1009,z5])]],
   [[],[(0,[z139,z0,z3,z4,z5,z6])],[(0,[z0,z43,z3,z4,z13,z6]),(0,[z0,z1,z380,z4,z5,z6]),(0,[z0,z1,z81,z373,z5,z6]),(0,[z527,z1,z3,z83,z5,z6]),(0,[z0,z96,z3,z4,z5,z57]),(0,[z0,z1,z4,z94,z432,z5]),(0,[z126,z0,z1,z3,z204,z5])],[(0,[z190,z0,z3,z4,z5,z444]),(0,[z0,z1010,z3,z4,z5,z6]),(0,[z35,z1,z3,z100,z5,z6])],[(0,[z12,z0,z3,z4,z5,z435]),(0,[z146,z0,z3,z4,z63,z6]),(0,[z0,z74,z3,z4,z5,z411]),(0,[z0,z1,z3,z4,z13,z435])],[(0,[z386,z43,z3,z4,z5,z6]),(0,[z80,z1,z3,z4,z5,z378]),(0,[z0,z1,z3,z4,z5,z435]),(0,[z0,z1,z3,z729,z17,z6])],[(0,[z85,z1,z3,z4,z7,z6])],[(0,[z43,z3,z26,z5,z17,z6]),(0,[z43,z3,z4,z5,z606,z6]),(0,[z0,z43,z3,z4,z449,z6]),(0,[z1011,z0,z3,z4,z5,z6]),(0,[z0,z128,z3,z4,z751,z6]),(0,[z76,z96,z3,z4,z5,z6])],[(0,[z184,z1,z3,z4,z5,z6])],[(0,[z176,z43,z3,z4,z5,z6]),(0,[z0,z1,z3,z429,z114,z6]),(0,[z35,z1,z3,z4,z121,z6]),(0,[z0,z1,z4,z270,z50,z6]),(0,[z0,z1,z3,z4,z1012,z6])],[(0,[z0,z1,z358,z82,z5,z6]),(0,[z0,z1,z4,z1013,z5,z6])],[(0,[z0,z1,z3,z1014,z5,z6])],[(0,[z0,z43,z287,z4,z5,z6]),(0,[z0,z43,z81,z82,z5,z6]),(0,[z0,z43,z3,z4,z5,z387]),(0,[z0,z352,z3,z4,z5,z57])],[(0,[z0,z43,z3,z4,z5,z490]),(0,[z12,z0,z3,z4,z5,z562])],[(0,[z0,z1,z3,z4,z5,z1015]),(0,[z12,z0,z3,z5,z6,z200]),(0,[z691,z0,z1,z4,z50,z6]),(0,[z516,z0,z1,z4,z50,z6]),(0,[z49,z0,z1,z4,z50,z562]),(0,[z1016,z0,z3,z4,z5,z6])],[]],
   [[(0,[z0,z1,z3,z1017,z5,z6]),(0,[z1018,z1,z3,z4,z5,z6])],[(0,[z0,z1,z769,z4,z5,z6]),(0,[z0,z1,z3,z4,z1019,z5]),(0,[z572,z0,z3,z4,z5,z277]),(0,[z76,z352,z3,z4,z5,z6]),(0,[z41,z0,z1,z3,z16,z5]),(0,[z0,z1,z3,z46,z729,z6]),(0,[z0,z1,z3,z4,z432,z91])],[(0,[z245,z0,z3,z59,z5,z6]),(0,[z54,z12,z0,z3,z5,z130]),(0,[z0,z1,z3,z4,z1020,z6]),(0,[z73,z0,z36,z4,z164,z6]),(0,[z1021,z0,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z850,z6]),(0,[z73,z0,z36,z100,z5,z6]),(0,[z289,z0,z3,z4,z5,z225]),(0,[z939,z527,z3,z4,z5,z6])],[(0,[z1022,z1,z3,z4,z5,z6])],[(0,[z135,z43,z3,z4,z5,z6]),(0,[z1023,z0,z3,z4,z5,z6]),(0,[z1024,z0,z1,z3,z5,z6])],[(0,[z0,z902,z3,z4,z5,z6]),(0,[z0,z1,z4,z1025,z5,z6])],[(0,[z619,z0,z3,z4,z5,z69]),(0,[z1026,z0,z3,z4,z5,z6])],[(0,[z43,z3,z4,z644,z5,z6])],[(0,[z284,z43,z3,z4,z5,z6]),(0,[z85,z295,z3,z4,z7,z6]),(0,[z18,z1,z3,z4,z5,z144]),(0,[z0,z96,z380,z4,z5,z6])],[(0,[z0,z43,z3,z4,z318,z6]),(0,[z0,z1,z299,z4,z5,z6]),(0,[z0,z1027,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z166]),(0,[z136,z732,z3,z4,z5,z6])],[(0,[z361,z43,z3,z4,z5,z6])],[(0,[z43,z3,z172,z4,z5,z6]),(0,[z12,z0,z3,z4,z297,z5]),(0,[z0,z1,z3,z1028,z5,z6])],[(0,[z117,z1,z3,z4,z5,z319]),(0,[z0,z1,z3,z4,z297,z5]),(0,[z527,z1,z3,z4,z5,z57])],[(0,[z417,z0,z3,z4,z5,z286]),(0,[z0,z1,z3,z4,z751,z6]),(0,[z1029,z1,z3,z4,z5,z6])],[(0,[z671,z43,z3,z4,z5,z6]),(0,[z38,z0,z3,z774,z5,z6]),(0,[z0,z1,z3,z1030,z5,z6])]],
   [[],[(0,[z0,z1,z3,z1031,z5,z6]),(0,[z0,z1032,z3,z4,z5,z6])],[(0,[z80,z820,z3,z4,z5,z6]),(0,[z12,z117,z3,z4,z5,z6]),(0,[z0,z75,z3,z4,z13,z6]),(0,[z1033,z1,z3,z4,z5,z6])],[(0,[z0,z128,z4,z124,z233,z6]),(0,[z0,z352,z380,z4,z5,z6])],[],[(0,[z24,z1,z44,z4,z114,z6])],[(0,[z0,z1,z3,z4,z94,z742])],[(0,[z0,z43,z3,z4,z228,z6]),(0,[z0,z1,z3,z863,z5,z6]),(0,[z0,z1,z3,z45,z5,z6]),(0,[z0,z1,z212,z4,z5,z95])],[(0,[z889,z43,z3,z4,z5,z6]),(0,[z0,z1034,z3,z4,z5,z6]),(0,[z54,z0,z1,z4,z432,z5])],[(0,[z0,z43,z3,z100,z5,z6]),(0,[z35,z1,z3,z4,z5,z387]),(0,[z289,z308,z3,z4,z5,z6])],[(0,[z12,z0,z3,z34,z5,z6]),(0,[z0,z1,z3,z403,z114,z6])],[(0,[z820,z43,z3,z4,z5,z6]),(0,[z12,z0,z3,z4,z5,z348]),(0,[z0,z1035,z3,z4,z5,z6]),(0,[z0,z1,z3,z34,z5,z6]),(0,[z0,z1,z3,z4,z5,z1036]),(0,[z0,z1,z3,z4,z1037,z6])],[(0,[z1,z3,z905,z26,z5,z6]),(0,[z0,z1,z330,z123,z5,z6])],[(0,[z43,z3,z44,z4,z5,z6]),(0,[z0,z1038,z3,z4,z5,z6]),(0,[z12,z0,z3,z4,z5,z57])],[(0,[z117,z1,z3,z4,z5,z6]),(0,[z0,z1,z4,z5,z801,z6]),(0,[z163,z1,z3,z26,z5,z6])],[(0,[z0,z43,z3,z4,z121,z6]),(1,[z0,z1,z4,z50,z562]),(1,[z0,z1,z3,z5,z708])]],
   [[(0,[z43,z3,z4,z5,z144,z91]),(0,[z0,z1,z3,z1039,z5,z6]),(0,[z0,z128,z3,z4,z297,z124])],[(0,[z550,z43,z3,z4,z5,z6]),(0,[z119,z74,z3,z4,z5,z6]),(0,[z423,z0,z3,z39,z5,z6])],[(0,[z43,z3,z4,z94,z5,z144])],[(0,[z232,z43,z3,z4,z5,z6]),(0,[z231,z43,z3,z4,z5,z6]),(0,[z104,z0,z3,z4,z302,z6])],[(0,[z308,z152,z3,z4,z5,z6]),(0,[z0,z3,z774,z39,z5,z6]),(0,[z527,z1,z380,z4,z5,z6])],[(0,[z0,z1,z287,z4,z5,z348]),(0,[z80,z1,z3,z112,z5,z115])],[(0,[z0,z43,z3,z68,z5,z20]),(0,[z0,z1,z1040,z4,z5,z6]),(0,[z361,z308,z3,z4,z5,z6]),(0,[z0,z1,z1041,z4,z5,z6])],[(0,[z0,z1042,z3,z4,z5,z6])],[(0,[z153,z43,z44,z4,z5,z6]),(0,[z89,z12,z0,z27,z5,z6]),(0,[z0,z1,z3,z4,z5,z1043]),(0,[z0,z1,z3,z4,z5,z1044]),(0,[z0,z1045,z3,z4,z5,z6]),(0,[z0,z1,z3,z129,z4,z742])],[(0,[z0,z43,z3,z4,z738,z5])],[(0,[z119,z43,z25,z4,z5,z6]),(0,[z12,z0,z3,z112,z5,z6]),(0,[z1,z25,z783,z4,z5,z6])],[(0,[z43,z3,z26,z27,z5,z6]),(0,[z0,z1,z3,z112,z5,z6]),(0,[z0,z3,z4,z5,z781,z286])],[(0,[z1046,z1,z3,z4,z5,z6])],[(0,[z1047,z0,z3,z4,z5,z6]),(0,[z0,z1048,z3,z4,z5,z6]),(0,[z0,z1,z247,z4,z5,z366])],[(0,[z295,z3,z4,z7,z5,z6]),(0,[z0,z1,z3,z4,z1049,z6]),(0,[z0,z3,z4,z124,z751,z6]),(0,[z0,z1050,z3,z4,z5,z6])],[(0,[z12,z232,z3,z4,z5,z6]),(0,[z78,z1,z3,z26,z5,z6]),(0,[z0,z1051,z3,z4,z5,z6]),(0,[z0,z1,z4,z1052,z5,z6]),(0,[z0,z1,z3,z4,z1053,z6]),(0,[z41,z0,z1,z3,z17,z42])]],
   [[(0,[z519,z43,z3,z4,z5,z6]),(0,[z29,z0,z3,z774,z5,z6]),(0,[z0,z1,z3,z1054,z5,z6])],[(0,[z1055,z0,z3,z4,z5,z6]),(0,[z54,z0,z1,z3,z5,z342]),(0,[z1056,z0,z1,z3,z4,z5]),(0,[z1057,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z1058]),(0,[z0,z3,z4,z1059,z5,z6])],[(0,[z136,z0,z3,z4,z5,z6]),(0,[z0,z1,z1060,z4,z5,z6])],[(0,[z0,z1,z3,z4,z1061,z6]),(0,[z43,z3,z299,z4,z5,z6]),(0,[z12,z0,z380,z4,z5,z6]),(0,[z0,z1,z3,z19,z16,z5]),(0,[z0,z1,z4,z50,z6,z562]),(0,[z0,z1,z249,z4,z50,z6])],[(0,[z417,z43,z3,z4,z5,z144]),(0,[z153,z0,z179,z4,z5,z6]),(0,[z248,z43,z3,z4,z5,z6]),(0,[z1062,z0,z1,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1063]),(0,[z35,z1,z3,z4,z164,z6])],[],[(0,[z428,z43,z3,z4,z5,z6]),(0,[z146,z0,z3,z4,z110,z6])],[(0,[z11,z772,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1064])],[(0,[z0,z1,z3,z4,z1065,z6]),(0,[z73,z0,z36,z123,z5,z6]),(0,[z1066,z1,z3,z4,z5,z6])],[(0,[z158,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1067]),(0,[z0,z1068,z3,z4,z5,z6]),(0,[z80,z98,z3,z4,z5,z115]),(0,[z1069,z1,z3,z4,z5,z6]),(0,[z1070,z0,z3,z4,z5,z6])],[(0,[z0,z338,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z1071,z6]),(0,[z54,z0,z1,z3,z625,z5])],[(0,[z0,z1,z3,z4,z5,z319])],[(0,[z0,z43,z3,z4,z114,z6]),(0,[z928,z43,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z324])],[(0,[z0,z1,z3,z1072,z4,z5])],[(0,[z370,z0,z3,z4,z5,z6]),(0,[z12,z503,z3,z4,z5,z6]),(0,[z0,z1073,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z114,z435]),(0,[z0,z1074,z3,z4,z5,z6]),(0,[z14,z171,z3,z4,z15,z6]),(0,[z0,z1,z3,z4,z50,z42]),(0,[z0,z1,z247,z4,z349,z6]),(0,[z0,z1,z1075,z4,z5,z6])]],
   [[],[(0,[z0,z74,z3,z429,z5,z6]),(0,[z127,z117,z3,z4,z5,z6]),(0,[z0,z1,z3,z1076,z5,z6]),(0,[z0,z1,z456,z4,z5,z95])],[(0,[z0,z1,z3,z4,z5,z781])],[],[(0,[z0,z1,z3,z4,z1077,z6]),(0,[z0,z1,z3,z1078,z5,z6])],[(0,[z43,z3,z4,z5,z6,z140])],[(0,[z0,z406,z152,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1079]),(0,[z1080,z0,z3,z4,z5,z6]),(0,[z1081,z0,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z853]),(0,[z0,z1,z3,z4,z1082,z6]),(0,[z0,z1,z3,z4,z5,z1083])],[(0,[z265,z43,z3,z4,z5,z6])],[(0,[z0,z1084,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1085]),(0,[z126,z55,z0,z1,z3,z5])],[],[(0,[z43,z3,z4,z5,z6,z160]),(0,[z0,z1,z241,z4,z5,z6]),(0,[z0,z1,z129,z4,z432,z6])],[(0,[z12,z0,z1086,z4,z5,z6]),(0,[z12,z0,z299,z4,z5,z6]),(0,[z12,z0,z3,z4,z5,z166]),(0,[z0,z1,z4,z5,z6,z731])],[(0,[z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z1086,z4,z5,z6]),(0,[z0,z1,z3,z4,z1087,z6]),(0,[z0,z1088,z3,z4,z5,z6]),(0,[z0,z1,z4,z432,z5,z91])],[(0,[z0,z1,z3,z1089,z5,z6]),(0,[z308,z3,z4,z5,z6,z286]),(0,[z0,z3,z4,z5,z277,z781])],[(0,[z0,z1,z1090,z4,z5,z6]),(0,[z527,z1038,z3,z4,z5,z6])]],
   [[(0,[z54,z0,z1,z3,z5,z419]),(0,[z0,z1,z3,z1091,z5,z6]),(0,[z0,z3,z720,z4,z5,z6]),(0,[z41,z0,z1,z3,z729,z6])],[(0,[z12,z0,z3,z1092,z5,z6]),(0,[z289,z0,z3,z4,z5,z138]),(0,[z73,z0,z555,z4,z5,z6])],[(0,[z14,z43,z3,z4,z15,z6]),(0,[z0,z1,z3,z1092,z5,z6]),(0,[z671,z1,z44,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1093]),(0,[z1094,z1,z3,z4,z5,z6]),(0,[z0,z1,z4,z5,z95,z731]),(0,[z1095,z0,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z1096])],[(0,[z11,z282,z3,z4,z5,z6]),(0,[z0,z1,z3,z19,z5,z444]),(0,[z1097,z1,z3,z4,z5,z6]),(0,[z1098,z1,z3,z4,z5,z6]),(0,[z0,z1,z425,z4,z5,z6]),(0,[z136,z0,z4,z5,z50,z6]),(0,[z0,z1,z263,z4,z5,z95])],[(0,[z119,z43,z44,z4,z5,z6]),(0,[z0,z43,z4,z710,z5,z6]),(0,[z0,z1,z25,z4,z114,z6]),(0,[z0,z1,z3,z4,z5,z1099]),(0,[z0,z1,z4,z750,z50,z6]),(0,[z0,z1,z1100,z4,z5,z6])],[(0,[z772,z1,z3,z4,z5,z6]),(0,[z0,z1,z287,z4,z5,z166]),(0,[z0,z1101,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z1102])],[(0,[z0,z1,z3,z4,z5,z1103]),(0,[z0,z1,z3,z4,z5,z1104]),(0,[z0,z1,z241,z4,z21,z6]),(0,[z1105,z1,z3,z4,z5,z6])],[(0,[z202,z43,z3,z4,z5,z6]),(0,[z12,z0,z3,z45,z5,z6]),(0,[z0,z1,z3,z4,z1106,z6]),(0,[z0,z1107,z3,z4,z5,z6]),(0,[z0,z1,z380,z4,z228,z6])],[(0,[z43,z3,z4,z201,z5,z6]),(0,[z1108,z0,z3,z4,z5,z6]),(0,[z1109,z1,z3,z4,z5,z6])],[(0,[z0,z43,z3,z4,z164,z6]),(0,[z0,z1,z82,z768,z5,z6]),(0,[z0,z1,z4,z349,z6,z90])],[(0,[z43,z3,z4,z210,z5,z6]),(0,[z0,z43,z3,z4,z5,z719]),(0,[z1110,z0,z1,z3,z4,z6]),(0,[z0,z1,z3,z1111,z5,z6]),(0,[z0,z1,z1112,z4,z5,z6])],[(0,[z476,z0,z3,z4,z161,z6]),(0,[z389,z43,z3,z4,z5,z6]),(0,[z816,z0,z1,z3,z4,z5]),(0,[z24,z74,z44,z4,z5,z6]),(0,[z0,z75,z3,z4,z114,z6]),(0,[z0,z1,z4,z5,z50,z319])],[(0,[z0,z43,z3,z4,z5,z726]),(0,[z0,z1,z3,z579,z5,z20]),(0,[z0,z1,z4,z5,z50,z324]),(0,[z0,z1,z3,z4,z742,z91])],[(0,[z11,z1,z3,z4,z5,z269]),(0,[z12,z0,z3,z4,z5,z279])]],
   [[(0,[z0,z1,z3,z4,z869,z6]),(0,[z0,z1,z3,z4,z5,z279])],[(0,[z245,z0,z3,z30,z5,z6])],[(0,[z14,z43,z3,z4,z7,z6]),(0,[z0,z74,z3,z403,z5,z6]),(0,[z0,z1,z3,z1113,z5,z6]),(0,[z80,z191,z3,z4,z5,z6]),(0,[z1114,z1,z3,z4,z5,z6])],[(0,[z0,z1,z287,z45,z5,z6]),(0,[z54,z0,z1,z3,z5,z618]),(0,[z1115,z0,z1,z3,z5,z6])],[(0,[z0,z3,z4,z5,z6,z1116]),(0,[z0,z96,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z50,z400]),(0,[z0,z1,z3,z4,z1117,z6])],[],[(0,[z0,z1,z3,z4,z1118,z6])],[(0,[z0,z1,z287,z34,z5,z6]),(0,[z0,z1,z1119,z4,z5,z6]),(0,[z55,z0,z3,z4,z5,z286])],[(0,[z0,z1,z3,z1120,z5,z6])],[(0,[z256,z1,z3,z4,z7,z6]),(0,[z0,z1,z3,z5,z6,z1121])],[(0,[z52,z0,z3,z4,z5,z70])],[(1,[z43,z3,z4,z5,z269]),(0,[z80,z1,z3,z4,z5,z741]),(0,[z0,z1,z3,z129,z4,z453]),(0,[z0,z96,z425,z4,z5,z6]),(0,[z41,z0,z1,z425,z17,z6])],[(0,[z43,z3,z4,z5,z6,z269]),(0,[z153,z0,z36,z4,z5,z6]),(0,[z0,z1,z3,z1122,z5,z6]),(0,[z35,z1,z3,z123,z5,z6])],[(0,[z119,z1,z783,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z1123]),(0,[z0,z352,z3,z4,z5,z6]),(0,[z0,z1,z4,z5,z233,z400])],[(0,[z168,z43,z3,z26,z5,z6])]],
   [[(0,[z0,z1,z3,z4,z1124,z6])],[(0,[z0,z43,z4,z5,z233,z6]),(0,[z0,z96,z3,z4,z21,z6])],[(0,[z0,z1,z3,z975,z4,z5]),(0,[z0,z1125,z3,z4,z5,z6]),(0,[z1126,z0,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z50,z562])],[(0,[z43,z3,z4,z5,z6,z283]),(0,[z0,z43,z3,z4,z204,z91]),(0,[z0,z1,z3,z638,z4,z94]),(0,[z0,z1,z203,z4,z5,z6])],[(0,[z98,z43,z3,z4,z5,z6]),(0,[z12,z459,z3,z4,z5,z6]),(0,[z12,z268,z3,z4,z5,z6]),(0,[z54,z0,z1,z3,z5,z42])],[(0,[z1127,z0,z3,z4,z5,z6]),(0,[z0,z47,z3,z112,z5,z6]),(0,[z0,z1,z3,z4,z5,z1128]),(0,[z136,z0,z3,z4,z5,z286]),(0,[z0,z352,z425,z4,z5,z6]),(0,[z0,z1,z3,z129,z4,z94])],[],[(0,[z11,z190,z3,z4,z5,z6]),(0,[z0,z1129,z3,z4,z5,z6]),(0,[z139,z85,z3,z4,z7,z6]),(0,[z55,z35,z3,z4,z5,z6]),(0,[z0,z1,z3,z1130,z5,z6]),(0,[z0,z1,z3,z4,z318,z279])],[(0,[z0,z1,z768,z27,z5,z6])],[(0,[z0,z1,z3,z4,z5,z1131])],[(0,[z265,z12,z3,z4,z5,z6]),(0,[z0,z1,z247,z4,z5,z95])],[(0,[z14,z1,z3,z4,z15,z348]),(0,[z0,z320,z4,z5,z461,z6]),(0,[z0,z1,z4,z5,z750,z6])],[(0,[z1132,z0,z3,z4,z5,z6])],[(0,[z1133,z1,z3,z4,z5,z6])],[(0,[z12,z0,z3,z4,z5,z319])],[(0,[z0,z43,z3,z83,z46,z6]),(0,[z12,z0,z3,z4,z5,z324]),(0,[z527,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1134]),(0,[z527,z1,z3,z5,z20,z6])]],
   [[(0,[z0,z1,z44,z4,z114,z6]),(0,[z0,z1,z3,z134,z5,z144]),(0,[z0,z1,z3,z4,z5,z1135])],[(0,[z889,z119,z3,z4,z5,z6]),(0,[z0,z1,z3,z429,z5,z411]),(0,[z0,z1,z1136,z4,z5,z6]),(0,[z596,z0,z1,z27,z5,z6]),(0,[z0,z1,z3,z4,z204,z9])],[(0,[z128,z232,z3,z4,z124,z6]),(0,[z1137,z0,z3,z4,z5,z6]),(0,[z41,z0,z1,z3,z17,z57])],[(0,[z0,z1,z3,z1138,z5,z6])],[(0,[z43,z3,z4,z5,z6,z496]),(0,[z14,z12,z3,z4,z15,z6]),(0,[z0,z1,z3,z4,z5,z1139]),(0,[z0,z1,z3,z4,z349,z95])],[(0,[z0,z1,z4,z164,z50,z6]),(0,[z1140,z1,z3,z4,z5,z6])],[(0,[z0,z1,z1141,z4,z5,z6]),(0,[z527,z1,z425,z4,z5,z6])],[(0,[z0,z1,z3,z1142,z5,z6]),(0,[z43,z3,z4,z5,z340,z6]),(0,[z0,z74,z3,z4,z5,z435]),(0,[z117,z1,z3,z100,z5,z6]),(0,[z0,z1,z3,z16,z46,z5]),(0,[z0,z1,z3,z4,z1143,z5])],[(0,[z43,z3,z4,z5,z6,z342]),(0,[z347,z1,z3,z4,z7,z6]),(0,[z1144,z0,z3,z4,z5,z6])],[(0,[z565,z1,z3,z26,z5,z6])],[(0,[z168,z43,z3,z4,z5,z6]),(0,[z80,z43,z3,z112,z5,z6]),(0,[z0,z1,z3,z4,z1145,z6]),(0,[z80,z1,z3,z4,z5,z115])],[(0,[z1062,z0,z43,z4,z5,z6]),(0,[z0,z43,z4,z5,z6,z780]),(0,[z0,z1146,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z277,z319]),(0,[z732,z3,z4,z5,z6,z90])],[(0,[z0,z43,z3,z4,z5,z269]),(0,[z12,z99,z0,z3,z4,z5]),(0,[z0,z1147,z3,z4,z5,z6]),(0,[z1148,z1,z3,z4,z5,z6]),(0,[z527,z1,z3,z4,z21,z6]),(0,[z0,z1,z3,z4,z230,z5])],[(0,[z12,z0,z3,z4,z349,z6]),(0,[z12,z0,z241,z4,z5,z6]),(0,[z117,z1,z3,z4,z121,z6])],[(0,[z521,z43,z3,z4,z5,z6]),(0,[z493,z43,z3,z4,z5,z6]),(0,[z12,z0,z3,z4,z13,z6]),(0,[z0,z1,z3,z4,z1149,z6]),(0,[z0,z1,z3,z4,z349,z6]),(0,[z0,z1,z3,z5,z729,z6])],[(0,[z12,z0,z3,z4,z5,z6]),(0,[z0,z43,z3,z4,z784,z5]),(0,[z43,z3,z4,z5,z6,z355]),(0,[z0,z1,z3,z4,z13,z6]),(0,[z0,z1,z1150,z4,z5,z6])]],
   [[(0,[z43,z3,z4,z360,z5,z6]),(0,[z0,z1,z3,z1151,z5,z6]),(0,[z0,z1,z3,z4,z1152,z6]),(0,[z49,z0,z1,z4,z50,z6])],[],[(0,[z0,z43,z3,z123,z5,z6]),(0,[z133,z0,z3,z4,z63,z6])],[(0,[z14,z295,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1153])],[(0,[z0,z1,z3,z1154,z5,z6]),(0,[z0,z1,z3,z4,z449,z6])],[(0,[z43,z3,z534,z4,z5,z6])],[(0,[z268,z43,z3,z4,z5,z6]),(0,[z12,z0,z425,z4,z5,z6]),(0,[z527,z96,z3,z4,z5,z6])],[(0,[z43,z3,z382,z4,z5,z6]),(0,[z619,z43,z3,z4,z5,z144]),(0,[z0,z1,z3,z4,z318,z324])],[(0,[z0,z1,z3,z4,z210,z91])],[(0,[z12,z0,z4,z432,z5,z6]),(0,[z0,z1,z287,z4,z5,z6]),(0,[z80,z1,z3,z134,z5,z115])],[(0,[z0,z1,z3,z4,z5,z490]),(0,[z0,z1,z4,z432,z5,z6])],[],[(0,[z43,z3,z4,z7,z50,z6]),(0,[z12,z80,z3,z4,z5,z115]),(0,[z168,z376,z3,z4,z5,z6])],[(0,[z43,z3,z548,z4,z5,z6]),(0,[z24,z1,z44,z4,z5,z411]),(0,[z49,z0,z1,z4,z750,z6])],[(0,[z12,z0,z3,z134,z5,z6]),(0,[z1,z3,z45,z5,z15,z6]),(0,[z0,z128,z3,z4,z124,z400]),(0,[z0,z1155,z3,z4,z5,z6])],[(0,[z43,z3,z4,z5,z6,z396]),(0,[z0,z1,z3,z134,z5,z6]),(0,[z1156,z1,z3,z4,z5,z6])]],
   [[(0,[z300,z0,z3,z4,z110,z6]),(0,[z527,z352,z3,z4,z5,z6])],[(0,[z0,z1157,z3,z4,z5,z6]),(0,[z361,z0,z3,z4,z5,z138]),(0,[z1158,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z1159]),(0,[z126,z0,z1,z3,z129,z5])],[(0,[z0,z1,z3,z403,z5,z411]),(0,[z1160,z1,z3,z4,z5,z6])],[(0,[z0,z295,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z1161,z5]),(0,[z1162,z0,z3,z4,z5,z6])],[(0,[z133,z43,z3,z4,z5,z6]),(0,[z232,z3,z4,z39,z5,z6]),(0,[z0,z1163,z3,z4,z5,z6])],[(0,[z0,z1,z3,z100,z5,z319]),(0,[z0,z1,z3,z4,z1164,z5]),(0,[z0,z1165,z3,z4,z5,z6]),(0,[z278,z0,z1,z4,z5,z90]),(1,[z0,z1,z4,z349,z90]),(0,[z0,z1,z4,z5,z349,z90])],[(0,[z12,z0,z3,z4,z318,z6]),(0,[z126,z0,z1,z3,z5,z144]),(0,[z531,z0,z1,z27,z5,z6])],[(0,[z0,z1,z3,z4,z318,z6])],[(0,[z0,z1,z1166,z4,z5,z6]),(0,[z0,z1,z1167,z4,z5,z6]),(0,[z85,z1,z3,z4,z724,z6]),(0,[z0,z1,z3,z68,z273,z5])],[(0,[z0,z1,z3,z1168,z5,z6]),(0,[z0,z3,z4,z5,z1169,z6]),(0,[z0,z1,z380,z4,z50,z6]),(0,[z0,z1170,z3,z4,z5,z6])],[(0,[z0,z282,z3,z4,z5,z348])],[(0,[z0,z1171,z3,z4,z5,z6]),(0,[z0,z1,z3,z1172,z5,z6]),(0,[z0,z1,z3,z4,z121,z319]),(0,[z0,z1,z3,z4,z742,z6])],[(0,[z14,z1,z3,z4,z369,z6]),(0,[z12,z772,z3,z4,z5,z6]),(0,[z0,z1173,z3,z4,z5,z6]),(0,[z14,z1,z299,z4,z15,z6]),(0,[z14,z1,z3,z4,z15,z166]),(0,[z0,z3,z4,z751,z110,z6]),(0,[z0,z1,z81,z82,z5,z279])],[(0,[z0,z1,z3,z4,z5,z1174]),(0,[z117,z1,z3,z4,z5,z387])],[(0,[z107,z0,z4,z5,z331,z90]),(0,[z1175,z1,z3,z4,z5,z6])],[(0,[z119,z43,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1176]),(0,[z0,z1,z1177,z4,z5,z6])]],
   [[(0,[z0,z1,z3,z1178,z5,z6]),(0,[z0,z1,z3,z4,z5,z1179]),(0,[z0,z1180,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z1181,z5])],[(0,[z43,z3,z4,z5,z599,z6])],[(0,[z0,z43,z3,z891,z5,z6]),(0,[z1110,z0,z43,z3,z4,z6]),(0,[z673,z0,z1,z4,z50,z6]),(0,[z0,z3,z4,z5,z6,z1182])],[(0,[z0,z1,z3,z1183,z5,z6]),(0,[z1184,z0,z3,z4,z5,z6]),(0,[z0,z1,z3,z68,z5,z643])],[(0,[z598,z43,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1185])],[(0,[z12,z0,z203,z4,z5,z6])],[(0,[z0,z43,z3,z4,z825,z6]),(0,[z497,z43,z3,z4,z5,z6]),(0,[z506,z1,z3,z4,z5,z115]),(0,[z0,z1,z3,z100,z5,z6])],[(0,[z746,z0,z1,z3,z4,z5]),(0,[z12,z0,z3,z4,z5,z1186]),(0,[z12,z0,z3,z129,z4,z94]),(0,[z0,z1187,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1188])],[(0,[z0,z1,z3,z4,z5,z1186])],[(0,[z14,z1,z3,z45,z15,z6]),(0,[z308,z1,z3,z68,z4,z5]),(1,[z0,z3,z4,z5,z781])],[(0,[z0,z1189,z3,z4,z5,z6]),(0,[z35,z1,z330,z4,z5,z6])],[(0,[z35,z320,z3,z4,z5,z6])],[(0,[z308,z43,z3,z4,z5,z6]),(0,[z0,z256,z3,z4,z137,z6]),(0,[z466,z43,z3,z4,z5,z6]),(0,[z0,z1,z299,z4,z15,z6]),(0,[z0,z1,z3,z4,z121,z6])],[(0,[z1,z43,z3,z4,z5,z269]),(0,[z14,z1,z3,z34,z15,z6])],[(0,[z127,z0,z3,z4,z5,z6]),(0,[z0,z43,z3,z4,z5,z444]),(0,[z1190,z1,z3,z4,z5,z6])],[(0,[z119,z1,z2,z4,z5,z6]),(0,[z0,z1191,z3,z4,z5,z6])]],
   [[(0,[z0,z1,z3,z4,z733,z5]),(0,[z0,z1,z3,z1192,z5,z6])],[(0,[z836,z0,z1,z4,z5,z6]),(0,[z0,z3,z4,z5,z6,z1193])],[(0,[z43,z3,z4,z194,z5,z6]),(0,[z476,z43,z3,z4,z7,z6]),(0,[z282,z43,z3,z4,z5,z6]),(0,[z12,z0,z3,z68,z5,z20])],[(0,[z0,z1194,z3,z4,z5,z6]),(0,[z0,z1,z3,z68,z5,z20])],[(0,[z18,z1,z3,z4,z5,z741]),(0,[z107,z0,z1,z4,z349,z90])],[(0,[z0,z43,z3,z4,z5,z411]),(0,[z12,z66,z3,z4,z5,z6]),(0,[z12,z676,z3,z4,z5,z6]),(0,[z126,z0,z1,z3,z5,z6])],[(0,[z43,z3,z4,z5,z648,z6]),(0,[z353,z0,z3,z194,z5,z6]),(0,[z107,z0,z1,z4,z5,z90])],[(0,[z119,z1,z25,z4,z5,z6]),(0,[z0,z1,z3,z4,z228,z279]),(0,[z0,z1,z3,z1195,z5,z6])],[(1,[z0,z3,z4,z751,z6])],[(0,[z117,z1,z3,z4,z164,z6])],[(0,[z43,z3,z501,z4,z5,z6]),(0,[z55,z0,z181,z3,z4,z5]),(0,[z41,z0,z352,z3,z17,z6])],[(0,[z0,z1,z3,z4,z5,z1196]),(0,[z1197,z0,z3,z4,z5,z6])],[(0,[z0,z1,z3,z1198,z5,z6]),(0,[z0,z1,z299,z4,z7,z6]),(0,[z0,z1,z81,z82,z5,z324])],[(0,[z363,z0,z1,z4,z5,z90]),(0,[z1199,z1,z3,z4,z5,z6]),(1,[z0,z1,z768,z5,z6])],[(0,[z12,z0,z3,z4,z230,z5])],[(0,[z0,z43,z3,z429,z5,z6]),(0,[z0,z1,z1200,z4,z5,z6])]],
   [[(0,[z80,z43,z3,z4,z5,z144]),(0,[z78,z186,z3,z26,z5,z6]),(0,[z0,z1,z3,z4,z1201,z5])],[],[(0,[z417,z1,z3,z4,z5,z144]),(0,[z1202,z0,z3,z4,z5,z6]),(0,[z29,z0,z3,z30,z5,z6]),(0,[z126,z0,z1,z3,z21,z6])],[(0,[z74,z3,z44,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1203])],[(0,[z238,z0,z1,z4,z5,z90]),(0,[z1204,z1,z3,z4,z5,z6]),(0,[z41,z0,z1,z3,z9,z6])],[(0,[z1205,z0,z3,z4,z5,z6]),(0,[z1206,z1,z3,z4,z5,z6])],[(0,[z12,z0,z3,z4,z449,z6])],[(0,[z12,z527,z3,z4,z5,z6])],[(0,[z43,z3,z4,z5,z6,z535]),(0,[z0,z1207,z3,z4,z5,z6])],[(0,[z38,z0,z3,z194,z5,z6]),(0,[z0,z1,z3,z4,z1208,z6])],[(0,[z0,z47,z3,z4,z5,z6]),(0,[z0,z1,z1209,z4,z5,z6]),(0,[z0,z1,z3,z4,z114,z6]),(0,[z1210,z1,z3,z4,z5,z6])],[(0,[z12,z0,z287,z4,z5,z6]),(0,[z12,z0,z81,z82,z5,z6]),(0,[z12,z0,z3,z4,z5,z387]),(0,[z202,z1,z3,z26,z5,z6]),(0,[z0,z1,z3,z4,z5,z1211]),(0,[z0,z1,z3,z4,z1212,z5]),(0,[z0,z282,z299,z4,z5,z6]),(0,[z0,z282,z3,z4,z5,z166]),(0,[z0,z1,z3,z123,z5,z319]),(0,[z146,z232,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z94,z188])],[(0,[z12,z0,z3,z4,z5,z490]),(0,[z0,z1,z3,z4,z5,z387]),(0,[z0,z1,z81,z82,z5,z6]),(0,[z0,z1,z3,z46,z6,z322])],[(0,[z1213,z0,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z1214,z6]),(0,[z49,z0,z1,z4,z50,z490]),(0,[z717,z136,z3,z4,z5,z6]),(0,[z0,z1,z1215,z4,z5,z6])],[(0,[z43,z3,z4,z696,z5,z6]),(0,[z294,z43,z3,z4,z5,z6]),(0,[z0,z1,z3,z1216,z5,z6]),(0,[z1217,z1,z3,z4,z5,z6]),(1,[z732,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1218])],[(0,[z18,z191,z3,z4,z5,z144]),(0,[z0,z1,z3,z5,z6,z1219]),(0,[z0,z1,z3,z68,z5,z708])]],
   [[(0,[z101,z43,z3,z4,z5,z6]),(0,[z232,z3,z4,z124,z5,z6]),(1,[z0,z1,z4,z5,z731])],[(0,[z928,z168,z3,z4,z5,z6]),(0,[z0,z43,z3,z4,z16,z5]),(0,[z12,z35,z3,z4,z5,z6]),(0,[z12,z184,z3,z4,z5,z6]),(0,[z12,z76,z3,z4,z5,z6]),(0,[z54,z0,z1,z3,z216,z5]),(0,[z126,z0,z1,z3,z5,z130])],[(0,[z1220,z0,z3,z4,z5,z6]),(0,[z0,z1221,z3,z4,z5,z6]),(0,[z0,z1,z3,z774,z5,z6]),(0,[z1222,z1,z3,z4,z5,z6]),(0,[z289,z0,z3,z4,z473,z5])],[(0,[z1223,z0,z1,z3,z5,z6]),(0,[z268,z98,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1224]),(0,[z0,z1,z3,z4,z1225,z6]),(0,[z1226,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z1227]),(0,[z308,z1,z3,z4,z94,z5])],[(0,[z190,z0,z3,z4,z5,z6]),(0,[z265,z1,z3,z4,z5,z6]),(0,[z0,z75,z3,z4,z5,z411]),(0,[z78,z1,z3,z905,z5,z6])],[(0,[z43,z3,z83,z26,z5,z6]),(0,[z0,z171,z3,z4,z5,z348]),(0,[z289,z0,z3,z4,z5,z277]),(0,[z0,z1,z4,z239,z5,z90])],[(0,[z0,z1,z3,z4,z164,z319]),(0,[z0,z1,z3,z4,z228,z324]),(0,[z0,z1,z3,z4,z5,z1228])],[(0,[z64,z43,z3,z4,z5,z6]),(0,[z0,z1,z3,z905,z5,z6]),(0,[z0,z282,z3,z45,z5,z6]),(0,[z0,z1,z3,z1229,z5,z6])],[(0,[z0,z47,z3,z134,z5,z6]),(0,[z0,z1,z3,z4,z5,z1230])],[(0,[z24,z1,z44,z429,z5,z6])],[(0,[z24,z43,z44,z4,z5,z6]),(0,[z0,z43,z3,z4,z5,z42]),(0,[z0,z1,z3,z4,z1231,z6]),(0,[z0,z1,z330,z4,z5,z562])],[(0,[z0,z1,z3,z4,z1232,z6]),(0,[z0,z282,z3,z34,z5,z6]),(0,[z0,z1,z3,z1233,z5,z6]),(0,[z0,z1,z3,z4,z5,z1234])],[(0,[z35,z43,z3,z4,z5,z6]),(0,[z43,z3,z4,z579,z5,z6]),(0,[z43,z3,z4,z60,z5,z6])],[(0,[z772,z0,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1235]),(0,[z0,z1,z3,z4,z1236,z6]),(0,[z0,z1,z3,z4,z5,z1237])],[(0,[z80,z43,z3,z4,z5,z6]),(0,[z0,z75,z3,z429,z5,z6]),(0,[z14,z1,z3,z4,z15,z6]),(0,[z55,z0,z3,z4,z515,z5]),(0,[z1238,z0,z3,z4,z5,z6])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 505) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 505).take 514) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1019).take 271) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1290)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [505, 514, 271] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 138).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 138).take 148).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 286).take 152).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 438).take 74).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 512)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [138, 148, 152, 74] = true :=
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

end PEqualNP.Outside.L_meta_36336

theorem PEqualNP.Outside.L_meta_36336 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075690 * 2 ^ 32 + 4277067968) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075690 * 2 ^ 32 + 4277067968) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_36336.solve