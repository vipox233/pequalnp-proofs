import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_39591

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
  Nat.testBit (4294901486 * 2 ^ 32 + 4278124192) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x0a028000440888a8#64 ++ 0x0140500008811115#64 ++ 0x7bb54044cc8989ff#64 ++ 0xef76a8089991313f#64 : BitVec 256),
   (0x1c0b0001504a4a60#64 ++ 0x438160002a09494c#64 ++ 0xf76ce08b714e4e62#64 ++ 0xdeed9c116e29c9cc#64 : BitVec 256),
   (0x108c011380505050#64 ++ 0x82118022700a0a0a#64 ++ 0xeee3c3338270707f#64 ++ 0xbddc7866704e0e0f#64 : BitVec 256),
   (0x40300c2c03802505#64 ++ 0x08060185807004a0#64 ++ 0xde1fdc3c03807f86#64 ++ 0x7bc3fb8780700ff0#64 : BitVec 256),
   (0xa12016c003a50000#64 ++ 0x142402d80074a000#64 ++ 0xc1ffffc003ff8001#64 ++ 0xf83ffff8007ff000#64 : BitVec 256),
   (0xc1c01bfea8000006#64 ++ 0x1838037fd5000000#64 ++ 0x3fffdffffc000000#64 ++ 0x07fffbffff800000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.and, [0, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [6, 2]⟩, ⟨.and, [8, 4]⟩, ⟨.or, [6, 10]⟩, ⟨.or, [8, 4]⟩, ⟨.and, [9, 12]⟩, ⟨.and, [11, 5]⟩, ⟨.or, [13, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0a028000440888a8 0x0140500008811115 0x7bb54044cc8989ff 0xef76a8089991313f

def z1 : W := mkw 0x108c011380505050 0x82118022700a0a0a 0xeee3c3338270707f 0xbddc7866704e0e0f

def z2 : W := mkw 0x1c0b0001504a4a60 0x438160002a09494c 0xf76ce08b714e4e62 0xdeed9c116e29c9cc

def z3 : W := mkw 0x40300c2c03802505 0x08060185807004a0 0xde1fdc3c03807f86 0x7bc3fb8780700ff0

def z4 : W := mkw 0xa12016c003a50000 0x142402d80074a000 0xc1ffffc003ff8001 0xf83ffff8007ff000

def z5 : W := mkw 0xbbae97d3c7fdd8f8 0x9775d2fa78ffbb1f 0xfffffff7cffff9ff 0xfffffffef9ffff3f

def z6 : W := mkw 0xc1c01bfea8000006 0x1838037fd5000000 0x3fffdffffc000000 0x07fffbffff800000

def z7 : W := mkw 0xcbc29bfeec0888ae 0x1978537fdd811115 0x3fffdffffc898980 0x47fffbffff913130

def z8 : W := mkw 0x0a028000440888a8 0x0140500008811115 0x0000000000898980 0x4000000000113130

def z9 : W := mkw 0xa12016c003a50000 0x142402d80074a000 0xdbffffc403ff8987 0xfb7ffff8807ff130

def z10 : W := mkw 0x0020040003800000 0x0004008000700000 0xce1fdc3003807006 0x79c3fb8600700e00

def z11 : W := mkw 0x1008000100404040 0x0201000020080808 0xeee1c0038040407f 0xbddc38007008080f

def z12 : W := mkw 0x1e0b8001544acae8 0x43c170002a89595d 0xfffde0cffdcfcfff 0xffffbc19ffb9f9ff

def z13 : W := mkw 0x4000082c00000004 0x0800010580000000 0x3fbfdc7ccc000000 0x07f7fb8f99800000

def z14 : W := mkw 0x1c8f0113d05a5a70 0xc391e0227a0b4b4e 0xffefe3bbf37e7e7f 0xfffdfc777e6fcfcf

def z15 : W := mkw 0xb1ac17d383f55050 0x963582fa707eaa0a 0xeffffff383fff07f 0xfdfffffe707ffe0f

def z16 : W := mkw 0xc1001aec00000004 0x1820035d80000000 0x1fffdffc00000000 0x03fffbff80000000

def z17 : W := mkw 0x180a000140484860 0x030140002809090c 0xf764c00340484862 0xdeec98006809090c

def z18 : W := mkw 0x108c011380505050 0x82118022700a0a0a 0x0040030300700000 0x00080060600e0000

def z19 : W := mkw 0x108c011380505050 0x82118022700a0a0a 0x8442833302707000 0x10885066604e0e00

def z20 : W := mkw 0x1409000110424240 0x4281200022084848 0x8448a08b31464600 0x108914116628c8c0

def z21 : W := mkw 0x148d011390525250 0xc291a022720a4a4a 0xeeebe3bbb376767f 0xbddd7c77766ececf

def z22 : W := mkw 0x0084011280101010 0x8010802250020202 0x088303308230301d 0x2110606610460603

def z23 : W := mkw 0xd1cc1bffa8505056 0x9a39837ff50a0a0a 0xffffdffffe70707f 0xbffffbffffce0e0f

def z24 : W := mkw 0x0c030000500a0a20 0x418060000a014144 0x110c2088710e0e00 0x422184110e21c1c0

def z25 : W := mkw 0x1c0b0001504a4a60 0x438160002a09494c 0x3600000b70004e62 0x06c000016e0009cc

def z26 : W := mkw 0x5c3b0c2d53ca6f65 0x4b876185aa794dec 0xfe1fdc3f73807fe6 0x7fc3fb87ee700ffc

def z27 : W := mkw 0x0a028000440888a8 0x0140500008811115 0x5a154004008989ff 0xeb42a8008011313f

def z28 : W := mkw 0xc1401aec28000006 0x1828035d85000000 0x111c1ccc7c000000 0x022383998f800000

def z29 : W := mkw 0xc1c01bfea8000006 0x1838037fd5000000 0x044a9fbb30000000 0x008953f766000000

def z30 : W := mkw 0x0000000000000000 0x0000000000000000 0xc0e3c30002700001 0xb81c7860004e0000

def z31 : W := mkw 0xe1301eec03a52505 0x1c2603dd8074a4a0 0xc9fffff403ffb185 0xf93ffffe807ff630

def z32 : W := mkw 0x0000000000000000 0x0000000000000000 0x376cc08b70000000 0x06ed98116e000000

def z33 : W := mkw 0xa12016c003a50000 0x142402d80074a000 0xc0933f4003ff8001 0xf81267e8007ff000

def z34 : W := mkw 0x0a028000440888a8 0x0140500008811115 0x00000000000009fe 0x000000000000013f

def z35 : W := mkw 0xc1c01bfea8000006 0x1838037fd5000000 0x3f1c1cfffc000000 0x07e3839fff800000

def z36 : W := mkw 0xc1c01bfea8000006 0x1838037fd5000000 0x29f31ff7fc000000 0x053e63feff800000

def z37 : W := mkw 0x0a028000440888a8 0x0140500008811115 0x489100448c8989ff 0xe91220089191313f

def z38 : W := mkw 0xa10012c000250000 0x142002580004a000 0x01ffffc0007f8001 0x803ffff8000ff000

def z39 : W := mkw 0x108c011380505050 0x82118022700a0a0a 0xce43c33302707006 0x39c87866604e0e00

def z40 : W := mkw 0x0a028000440888a8 0x0140500008811115 0x40000000008989ff 0xe80000000011313f

def z41 : W := mkw 0xcbc29bfeec0888ae 0x1978537fdd811115 0x7fffdffffc8989ff 0xeffffbffff91313f

def z42 : W := mkw 0xc1f01ffeab802507 0x183e03ffd57004a0 0xffffdfffff807f86 0x7ffffbfffff00ff0

def z43 : W := mkw 0x0a028000440888a8 0x0140500008811115 0x511400444c8989ff 0xea2280088991313f

def z44 : W := mkw 0x0000000000000000 0x0000000000000000 0xd60cc00801004e02 0x5ac19801002009c0

def z45 : W := mkw 0xa12016c003a50000 0x142402d80074a000 0x01f33fc002ff8001 0xa03e67f8005ff000

def z46 : W := mkw 0xab2296c047ad88a8 0x156452d808f5b115 0xfbffffc4cfff89ff 0xff7ffff899fff13f

def z47 : W := mkw 0xe1e01ffeaba50006 0x1c3c03ffd574a000 0xffffffffffff8001 0xfffffffffffff000

def z48 : W := mkw 0x0a028000440888a8 0x0140500008811115 0x3a000004cc0009fe 0x074000009980013f

def z49 : W := mkw 0xa12016c003a50000 0x142402d80074a000 0x804abf8003760000 0x100957f0006ec000

def z50 : W := mkw 0xa13016c003a52501 0x142602d80074a4a0 0xc1ffffc003ffff87 0xf83ffff8007ffff0

def z51 : W := mkw 0x42308c2c0780a58d 0x0846118580f014b1 0x08931c748e81b19d 0x2112638e91d03633

def z52 : W := mkw 0x40300c2c03802505 0x08060185807004a0 0x840a9c3803007600 0x1081538700600ec0

def z53 : W := mkw 0x1c0b0001504a4a60 0x438160002a09494c 0x21602083704e0060 0x842c04106e09c00c

def z54 : W := mkw 0xc1c01bfea8000006 0x1838037fd5000000 0x08931f748c000000 0x011263ee91800000

def z55 : W := mkw 0x5c3b0c2d53ca6f65 0x4b876185aa794dec 0xff7ffcbf73ce7fe6 0xffefff97ee79cffc

def z56 : W := mkw 0x0a028000440888a8 0x0140500008811115 0x61b54040cc898079 0xec36a8081991300f

def z57 : W := mkw 0x40300c2c03802505 0x08060185807004a0 0xce0bdc3803007606 0x39c17b8700600ec0

def z58 : W := mkw 0x108c011380505050 0x82118022700a0a0a 0x2e0000338000707e 0x05c0000670000e0f

def z59 : W := mkw 0x0a028000440888a8 0x0140500008811115 0x21a00040cc098079 0x843400081981300f

def z60 : W := mkw 0x0a028000440888a8 0x0140500008811115 0x100000044c000980 0x0200000089800130

def z61 : W := mkw 0x40300c2c03802505 0x08060185807004a0 0x00021c3002003000 0x0000438600400600

def z62 : W := mkw 0xa12016c003a50000 0x142402d80074a000 0xc04abf8003ff8001 0xf80957f0007ff000

def z63 : W := mkw 0x0080011280000000 0x0010002250000000 0x3fefc3bbf0000000 0x07fdf8777e000000

def z64 : W := mkw 0xa12016c003a50000 0x142402d80074a000 0xc0f3df4002f18001 0xb81e7be8005e3000

def z65 : W := mkw 0x40c0093ea8000006 0x08180127d5000000 0x3e00003ffc000000 0x07c00007ff800000

def z66 : W := mkw 0xc1c01bfea8000006 0x1838037fd5000000 0x1e5fdfbf30000000 0x03cbfbf7e6000000

def z67 : W := mkw 0x0080011280000000 0x0010002250000000 0x2ee3c33380000000 0x05dc786670000000

def z68 : W := mkw 0x0030040003802501 0x00060080007004a0 0xc000000003807f86 0x7800000000700ff0

def z69 : W := mkw 0x1c0b0001504a4a60 0x438160002a09494c 0xb648a08b71464e62 0x16c914116e28c9cc

def z70 : W := mkw 0x108c011380505050 0x82118022700a0a0a 0xc44283330270707f 0xb8885066604e0e0f

def z71 : W := mkw 0xa12016c003a50000 0x142402d80074a000 0xcffffff003fff007 0xf9fffffe007ffe00

def z72 : W := mkw 0xc1401aec28000006 0x1828035d85000000 0x11ffdfcc7c000000 0x023ffbf98f800000

def z73 : W := mkw 0x0000000000000000 0x0000000000000000 0xc16ce080014e0000 0xd82d9c100029c000

def z74 : W := mkw 0xbd2b16c153ef4a60 0x57a562d82a7de94c 0xf7ffffcb73ffce63 0xfefffff96e7ff9cc

def z75 : W := mkw 0xc1c01bfea8000006 0x1838037fd5000000 0x155e9fff7c000000 0x02abd3ffef800000

def z76 : W := mkw 0xa12016c003a50000 0x142402d80074a000 0x00021f0002300000 0x000043e000460000

def z77 : W := mkw 0x1c0b0001504a4a60 0x438160002a09494c 0xfffde0cffd4e4e62 0xdfffbc19ffa9c9cc

def z78 : W := mkw 0x40300c2c03802505 0x08060185807004a0 0x08131c3402803184 0x2102638680500630

def z79 : W := mkw 0xbd0b12c1506f4a60 0x57a162582a0de94c 0x21e023c3707f8061 0x843c04786e0ff00c

def z80 : W := mkw 0x4a328c2c4788adad 0x0946518588f115b5 0xffbfdc7ccf89ffff 0xfff7fb8f99f13fff

def z81 : W := mkw 0x0e038000540a8aa8 0x41c070000a815155 0x111c20cc7d8f8f80 0x422384198fb1f1f0

def z82 : W := mkw 0x0000000000000000 0x0000000000000000 0x1a00000400000986 0x0340000080000130

def z83 : W := mkw 0x0000000000000000 0x0000000000000000 0x5a15400400800986 0x6b42a80080100130

def z84 : W := mkw 0xc1c01bfea8000006 0x1838037fd5000000 0x25ea9ffbfc000000 0x04bd53ff7f800000

def z85 : W := mkw 0x0020040003800000 0x0004008000700000 0x800a9c0003000000 0x1001538000600000

def z86 : W := mkw 0x0000000000000000 0x0000000000000000 0x41b5404000898001 0xe836a80800113000

def z87 : W := mkw 0x0000000000000000 0x0000000000000000 0x3bb54044cc000000 0x0776a80899800000

def z88 : W := mkw 0x40300c2c03802505 0x08060185807004a0 0xc40a9c3803807f86 0x7881538700700ff0

def z89 : W := mkw 0xa12016c003a50000 0x142402d80074a000 0x41bd7cc0018f8001 0xe837af980031f000

def z90 : W := mkw 0x108c011380505050 0x82118022700a0a0a 0xfeefc33b83707e7f 0xffddf867706e0fcf

def z91 : W := mkw 0x810012c000000000 0x1020025800000000 0x37ffdfcb70000000 0x06fffbf96e000000

def z92 : W := mkw 0x1c0b0001504a4a60 0x438160002a09494c 0xc0002000014e4e62 0xd80004000029c9cc

def z93 : W := mkw 0x0000000000000000 0x0000000000000000 0x2aa1400080000000 0x0554280010000000

def z94 : W := mkw 0x0000000000000000 0x0000000000000000 0xde1dc00c01804f86 0x7bc3b801803009f0

def z95 : W := mkw 0xa10012c000250000 0x142002580004a000 0x01e023c0007f8001 0x803c0478000ff000

def z96 : W := mkw 0xdfcb9bfffc4acaee 0x5bf9737fff89595d 0xfffffffffdcfcfff 0xffffffffffb9f9ff

def z97 : W := mkw 0xa12016c003a50000 0x142402d80074a000 0x81eabfc0037f8001 0x903d57f8006ff000

def z98 : W := mkw 0xab2296c047ad88a8 0x156452d808f5b115 0x111c3cc44d8f8980 0x4223879889b1f130

def z99 : W := mkw 0x1c8b0113d04a4a60 0x439160227a09494c 0xffefe3bbf14e4e62 0xdffdfc777e29c9cc

def z100 : W := mkw 0xc1c01bfea8000006 0x1838037fd5000000 0x7fffdffffc00007f 0xaffffbffff80000f

def z101 : W := mkw 0x0000000000000000 0x0000000000000000 0x3324400040000000 0x0664880008000000

def z102 : W := mkw 0x0a3284004788ada9 0x0146508008f115b5 0xc00000000389ffff 0xf800000000713fff

def z103 : W := mkw 0xddcb1bfff84a4a66 0x5bb9637fff09494c 0xf76effbb714e4e62 0xdeeddff76e29c9cc

def z104 : W := mkw 0x100c000100505050 0x82018000200a0a0a 0xc00000000270707f 0xb8000000004e0e0f

def z105 : W := mkw 0x108c011380505050 0x82118022700a0a0a 0xefefe3b3837e707f 0xfdfdfc76706fce0f

def z106 : W := mkw 0xe1e01ffeaba50006 0x1c3c03ffd574a000 0xc9fffff48fff8001 0xf93ffffe91fff000

def z107 : W := mkw 0xe1301eec03a52505 0x1c2603dd8074a4a0 0xdffffffc03ffff87 0xfbffffff807ffff0

def z108 : W := mkw 0x0000000000000000 0x0000000000000000 0x21a00040cc000000 0x0434000819800000

def z109 : W := mkw 0x81c013d2a8000002 0x1038027a55000000 0x21e003c3fc000000 0x043c00787f800000

def z110 : W := mkw 0x812016c003800000 0x102402d800700000 0xc1ffdfc003800000 0x783ffbf800700000

def z111 : W := mkw 0x0000000000000000 0x0000000000000000 0x2160008370000000 0x042c00106e000000

def z112 : W := mkw 0x2020040003a50000 0x040400800074a000 0xc000200003ff8001 0xf8000400007ff000

def z113 : W := mkw 0x60300c2c03a52505 0x0c0601858074a4a0 0xde1ffc3c03ffff87 0xfbc3ff87807ffff0

def z114 : W := mkw 0x108c011380505050 0x82118022700a0a0a 0x20e0030380700079 0x841c0060700e000f

def z115 : W := mkw 0x0000000000000000 0x0000000000000000 0x7bb54044cc00007f 0xaf76a8089980000f

def z116 : W := mkw 0xa10012c000250000 0x142002580004a000 0xc1ece3c0017f8001 0xd83d9c78002ff000

def z117 : W := mkw 0x4000082c00000004 0x0800010580000000 0x1e1fdc3c00000000 0x03c3fb8780000000

def z118 : W := mkw 0x9d0b12c1504a4a60 0x53a162582a09494c 0xf7ffffcb714e4e62 0xdefffff96e29c9cc

def z119 : W := mkw 0x100c000100505050 0x82018000200a0a0a 0xc0e3c3000270707f 0xb81c7860004e0e0f

def z120 : W := mkw 0x1e0b8001544acae8 0x43c170002a89595d 0xc000200001cfcfff 0xf80004000039f9ff

def z121 : W := mkw 0x40300c2c03802505 0x08060185807004a0 0x5a175c3402803986 0x6b42eb8680500730

def z122 : W := mkw 0xa12016c003a50000 0x142402d80074a000 0x011c3cc0018f8000 0x402387980031f000

def z123 : W := mkw 0x0000000000000000 0x0000000000000000 0xce03c03002007006 0x39c0780600400e00

def z124 : W := mkw 0xb18c13d380755050 0x9631827a700eaa0a 0xefe3e3f3827ff07f 0xbdfc7c7e704ffe0f

def z125 : W := mkw 0x0802000040080820 0x0100400008010104 0x3200000040000862 0x064000000800010c

def z126 : W := mkw 0x0000000000000000 0x0000000000000000 0xeae3c3008270007f 0xbd5c7860104e000f

def z127 : W := mkw 0xad2316c053af0a20 0x55a462d80a75e144 0xd1ffffc873ff8e01 0xfa3ffff90e7ff1c0

def z128 : W := mkw 0x0a028000440888a8 0x0140500008811115 0x6ba14040cc09807f 0xad7428081981300f

def z129 : W := mkw 0x40c0093ea8000006 0x08180127d5000000 0x3f6cc0bffc000000 0x07ed9817ff800000

def z130 : W := mkw 0xddcb1bfff84a4a66 0x5bb9637fff09494c 0xfffffffffd4e4e62 0xdfffffffffa9c9cc

def z131 : W := mkw 0xe1f01ffeaba52507 0x1c3e03ffd574a4a0 0xffffffffffffff87 0xfffffffffffffff0

def z132 : W := mkw 0xa12016c003a50000 0x142402d80074a000 0x815ebfc003ff8000 0x502bd7f8007ff000

def z133 : W := mkw 0x1a8e8113c458d8f8 0x8351d022788b1b1f 0xfff7c377cef9f9ff 0xfffef86ef9df3f3f

def z134 : W := mkw 0x5c3b0c2d53ca6f65 0x4b876185aa794dec 0xde1ffc3c03ce7fe6 0xfbc3ff878079cffc

def z135 : W := mkw 0x40c0093ea8000006 0x08180127d5000000 0x3e1fdc3ffc000000 0x07c3fb87ff800000

def z136 : W := mkw 0xa12016c003a50000 0x142402d80074a000 0x01fc3fc001ff8001 0xc03f87f8003ff000

def z137 : W := mkw 0x40300c2c03802505 0x08060185807004a0 0x1e1c1c3c01807f86 0x43c3838780300ff0

def z138 : W := mkw 0x108c011380505050 0x82118022700a0a0a 0x2e8303338230707f 0x25d0606670460e0f

def z139 : W := mkw 0x0020040003800000 0x0004008000700000 0xc01fdc0003800000 0x7803fb8000700000

def z140 : W := mkw 0x81c013d2a8000002 0x1038027a55000000 0x21ffdfc3fc000000 0x043ffbf87f800000

def z141 : W := mkw 0x4010082c00002505 0x08020105800004a0 0x1e00003c00007f86 0x03c0000780000ff0

def z142 : W := mkw 0x0200800004008088 0x0040100000801011 0x089100448c81819d 0x2112200891903033

def z143 : W := mkw 0x4c330c2c538a2f25 0x498661858a7145e4 0x111c3c8c718e0f80 0x422387918e31c1f0

def z144 : W := mkw 0xa12016c003a50000 0x142402d80074a000 0x00931f4002b18001 0x201263e800563000

def z145 : W := mkw 0x0a028000440888a8 0x0140500008811115 0x7ffdc0cffc8989ff 0xefffb819ff91313f

def z146 : W := mkw 0x8b0292c0440888a8 0x1160525808811115 0x7bffdfc4cc8989ff 0xef7ffbf89991313f

def z147 : W := mkw 0xc1c01bfea8000006 0x1838037fd5000000 0x00021f3000000000 0x000043e600000000

def z148 : W := mkw 0x108c011380505050 0x82118022700a0a0a 0xeff7c37382f9f07f 0xfdfef86e705f3e0f

def z149 : W := mkw 0xc3c09bfeac00808e 0x1878137fd5801011 0x08931f748c81819d 0x211263ee91903033

def z150 : W := mkw 0x1008000100404040 0x0201000020080808 0xe660c00300404062 0x9ccc18006008080c

def z151 : W := mkw 0x1a8e8113c458d8f8 0x8351d022788b1b1f 0x7bf54347ccf989ff 0xef7ea868f99f313f

def z152 : W := mkw 0x40300c2c03802505 0x08060185807004a0 0x101c1c0c01800f80 0x42038381803001f0

def z153 : W := mkw 0x0a028000440888a8 0x0140500008811115 0x111400444c898980 0x4222800889913130

def z154 : W := mkw 0x810012c000000000 0x1020025800000000 0xc1ffdfc002700001 0xb83ffbf8004e0000

def z155 : W := mkw 0x2a22840047ad88a8 0x0544508008f5b115 0xfbb56044cfff89ff 0xff76ac0899fff13f

def z156 : W := mkw 0x5ccb093ff84a4a66 0x4b996127ff09494c 0xff6ce0bffd4e4e62 0xdfed9c17ffa9c9cc

def z157 : W := mkw 0x0e038000540a8aa8 0x41c070000a815155 0x7bbd60ccfd8f8fff 0xef77ac199fb1f1ff

def z158 : W := mkw 0x0080011280000000 0x0010002250000000 0x20e0030380000000 0x041c006070000000

def z159 : W := mkw 0xa10012c000250000 0x142002580004a000 0xc1e3e3c0027f8001 0xb83c7c78004ff000

def z160 : W := mkw 0x0a028000440888a8 0x0140500008811115 0x3b140044cc8989fe 0x476280089991313f

def z161 : W := mkw 0xa12016c003a50000 0x142402d80074a000 0x01ffdfc002b18001 0x203ffbf800563000

def z162 : W := mkw 0x0a028000440888a8 0x0140500008811115 0x73a44040cc09887b 0xce7488081981310f

def z163 : W := mkw 0x40300c2c03802505 0x08060185807004a0 0xffbfdc7ccf807f86 0x7ff7fb8f99f00ff0

def z164 : W := mkw 0xc1f01ffeab802507 0x183e03ffd57004a0 0x3fffdffffe803184 0x27fffbffffd00630

def z165 : W := mkw 0xe1c01bfea8250006 0x1c38037fd504a000 0x3ffffffffc7f8001 0x87ffffffff8ff000

def z166 : W := mkw 0x50bc0d3f83d07555 0x8a1781a7f07a0eaa 0xfeffdf3f83f07fff 0xffdffbe7f07e0fff

def z167 : W := mkw 0x5e3b8c2d57caefed 0x4bc77185aaf95dfd 0xfffffcffffcfffff 0xffffff9ffff9ffff

def z168 : W := mkw 0x1409000110424240 0x4281200022084848 0xd64ce08b31464e02 0x5ac99c116628c9c0

def z169 : W := mkw 0x0000000000000000 0x0000000000000000 0x01b5404000000000 0x0036a80800000000

def z170 : W := mkw 0x0084011280101010 0x8010802250020202 0x0080030080300019 0x0010006010060003

def z171 : W := mkw 0x40300c2c03802505 0x08060185807004a0 0xdeffdf3c03f07f87 0xfbdffbe7807e0ff0

def z172 : W := mkw 0x0000000000000000 0x0000000000000000 0xc00cc00001000000 0x5801980000200000

def z173 : W := mkw 0xb18c13d380755050 0x9631827a700eaa0a 0x21e023c3807f8079 0x843c0478700ff00f

def z174 : W := mkw 0x40300c2c03802505 0x08060185807004a0 0x1e131c3c02807f86 0x23c2638780500ff0

def z175 : W := mkw 0x0a028000440888a8 0x0140500008811115 0x3bb54044cc098079 0x8776a8089981300f

def z176 : W := mkw 0x4a328c2c4788adad 0x0946518588f115b5 0x111c1c4c4d898f80 0x4223838989b131f0

def z177 : W := mkw 0x1c0b0001504a4a60 0x438160002a09494c 0xf7fde0cb71cfce63 0xfeffbc196e39f9cc

def z178 : W := mkw 0x1c0b0001504a4a60 0x438160002a09494c 0xc448a08b314e4e62 0xd88914116629c9cc

def z179 : W := mkw 0xc1c01bfea8000006 0x1838037fd5000000 0xffffdffffe007006 0x3ffffbffffc00e00

def z180 : W := mkw 0x810012c000000000 0x1020025800000000 0x01e003c000000000 0x003c007800000000

def z181 : W := mkw 0x40300c2c03802505 0x08060185807004a0 0x941e9c3c03807f80 0x5283d38780700ff0

def z182 : W := mkw 0x0000000000000000 0x0000000000000000 0xc1f7c34002f98001 0xf83ef868005f3000

def z183 : W := mkw 0x2020040003a50000 0x040400800074a000 0x8000200003760000 0x10000400006ec000

def z184 : W := mkw 0x0a028000440888a8 0x0140500008811115 0x31b40044cc8989f9 0xc63680089991313f

def z185 : W := mkw 0x0000000000000000 0x0000000000000000 0xd76ce088014e4e02 0xdaed9c110029c9c0

def z186 : W := mkw 0x0000000000000000 0x0000000000000000 0x6aa140008000007f 0xad5428001000000f

def z187 : W := mkw 0xc1401aec28000006 0x1828035d85000000 0x3bbd5cccfc000000 0x0777ab999f800000

def z188 : W := mkw 0x0200800004008088 0x0040100000801011 0x008000408c018019 0x0010000811803003

def z189 : W := mkw 0xd5c91bffb8424246 0x5ab9237ff7084848 0xbffffffffd464600 0x17ffffffffa8c8c0

def z190 : W := mkw 0x0080011280000000 0x0010002250000000 0x6ee3c3338000007f 0xaddc78667000000f

def z191 : W := mkw 0x1409000110424240 0x4281200022084848 0xb76ce08b71464600 0x16ed9c116e28c8c0

def z192 : W := mkw 0x1c0b0001504a4a60 0x438160002a09494c 0xa568a08b714e4660 0x94ad14116e29c8cc

def z193 : W := mkw 0x0000000000000000 0x0000000000000000 0x0448808b30000000 0x0089101166000000

def z194 : W := mkw 0xddcf1bfff85a5a76 0xdbb9e37fff0b4b4e 0xffffffffff7e7e7f 0xffffffffffefcfcf

def z195 : W := mkw 0x0a028000440888a8 0x0140500008811115 0xffb7c074ce89f9ff 0xfff6f80e99d13f3f

def z196 : W := mkw 0x0000000000000000 0x0000000000000000 0xc000000002700001 0xb8000000004e0000

def z197 : W := mkw 0x40300c2c03802505 0x08060185807004a0 0x1e1fdc3c02803184 0x23c3fb8780500630

def z198 : W := mkw 0xab0292c0442d88a8 0x156052580885b115 0x7bf563c4ccff89ff 0xef7eac78999ff13f

def z199 : W := mkw 0x0084011280101010 0x8010802250020202 0x6aa343308230307f 0xad5468661046060f

def z200 : W := mkw 0xcdc31bfef80a0a26 0x59b8637fdf014144 0x3ffffffffd0e0e00 0x47ffffffffa1c1c0

def z201 : W := mkw 0x108c011380505050 0x82118022700a0a0a 0x2000000380000078 0x040000007000000f

def z202 : W := mkw 0xdd4b1aed784a4a66 0x5ba9635daf09494c 0xf77cfccf7d4e4e62 0xdeef9f99efa9c9cc

def z203 : W := mkw 0xa12016c003a50000 0x142402d80074a000 0xebffffc083ff807f 0xfd7ffff8107ff00f

def z204 : W := mkw 0x1e8f8113d45adaf8 0xc3d1f0227a8b5b5f 0xffffe3ffffffffff 0xfffffc7fffffffff

def z205 : W := mkw 0x5cbf0d3fd3da7f75 0xcb97e1a7fa7b4fee 0xffffffbff3fe7fff 0xfffffff7fe7fcfff

def z206 : W := mkw 0x0000000000000000 0x0000000000000000 0xc000000002007006 0x3800000000400e00

def z207 : W := mkw 0x108c011380505050 0x82118022700a0a0a 0x28e303338270307d 0xa51c6066704e060f

def z208 : W := mkw 0x81c013d2a8000002 0x1038027a55000000 0x37ecc3cbfc000000 0x06fd98797f800000

def z209 : W := mkw 0xa12016c003a50000 0x142402d80074a000 0xc17cfcc001cf8000 0xd82f9f980039f000

def z210 : W := mkw 0x0200800004008088 0x0040100000801011 0x6ab140448c8181ff 0xad5628089190303f

def z211 : W := mkw 0x108c011380505050 0x82118022700a0a0a 0xee03c0338200707e 0x3dc0780670400e0f

def z212 : W := mkw 0xe1301eec03a52505 0x1c2603dd8074a4a0 0xd1ffffcc03ff8f81 0xfa3ffff9807ff1f0

def z213 : W := mkw 0xab2296c047ad88a8 0x156452d808f5b115 0x7bbd7cc4cd8f89ff 0xef77af9899b1f13f

def z214 : W := mkw 0xe1e01ffeaba50006 0x1c3c03ffd574a000 0x3fffdffffeb18001 0x27fffbffffd63000

def z215 : W := mkw 0xc1d01bfea8002507 0x183a037fd50004a0 0x3fffdffffc007f86 0x07fffbffff800ff0

def z216 : W := mkw 0x40300c2c03802505 0x08060185807004a0 0xc8131c3403807f86 0x7902638680700ff0

def z217 : W := mkw 0x0030040003802501 0x00060080007004a0 0xc01fdc0003807f86 0x7803fb8000700ff0

def z218 : W := mkw 0x40300c2c03802505 0x08060185807004a0 0x9e0a9c3c03007f86 0x13c1538780600ff0

def z219 : W := mkw 0x8bc293d2ec0888aa 0x1178527a5d811115 0x21e003c3fc098079 0x843c00787f81300f

def z220 : W := mkw 0x0000000000000000 0x0000000000000000 0xc003c00002000000 0x3800780000400000

def z221 : W := mkw 0x0802000040080820 0x0100400008010104 0x7324400040080862 0xce6488000801010c

def z222 : W := mkw 0x0080011280000000 0x0010002250000000 0x2e00003380000000 0x05c0000670000000

def z223 : W := mkw 0x0000000000000000 0x0000000000000000 0x001fdc0000000000 0x0003fb8000000000

def z224 : W := mkw 0xc1f01ffeab802507 0x183e03ffd57004a0 0x844a9fbb33007600 0x108953f766600ec0

def z225 : W := mkw 0x108c011380505050 0x82118022700a0a0a 0xfff7c377ce70707f 0xbffef86ef9ce0e0f

def z226 : W := mkw 0x91cc13d3a8505052 0x9239827a750a0a0a 0x21e003c3fc700079 0x843c00787f8e000f

def z227 : W := mkw 0x108c011380505050 0x82118022700a0a0a 0xee60c0338040707e 0x9dcc180670080e0f

def z228 : W := mkw 0x9dcb13d3f84a4a62 0x53b9627a7f09494c 0xf7ece3cbfd4e4e62 0xdefd9c797fa9c9cc

def z229 : W := mkw 0x0000000000000000 0x0000000000000000 0x4000000000800986 0x6800000000100130

def z230 : W := mkw 0x5abe8d3fc7d8fdfd 0x8b57d1a7f8fb1fbf 0xffffdf7fcff9ffff 0xfffffbeff9ff3fff

def z231 : W := mkw 0x0c030000500a0a20 0x418060000a014144 0x732c6088710e0e62 0xce658c110e21c1cc

def z232 : W := mkw 0x2a22840047ad88a8 0x0544508008f5b115 0xc000200003ff89ff 0xf8000400007ff13f

def z233 : W := mkw 0xc1c41bfea8101016 0x9838837fd5020202 0x08931f748e30301d 0x211263ee91c60603

def z234 : W := mkw 0x40d0093ea8002507 0x081a0127d50004a0 0x3e00003ffc007f86 0x07c00007ff800ff0

def z235 : W := mkw 0x0a028000440888a8 0x0140500008811115 0x7a000004cc8989ff 0xef4000009991313f

def z236 : W := mkw 0x40300c2c03802505 0x08060185807004a0 0x00081c0801000600 0x00010381002000c0

def z237 : W := mkw 0x108c011380505050 0x82118022700a0a0a 0xa4e2833382707079 0x949c5066704e0e0f

def z238 : W := mkw 0x810012c000000000 0x1020025800000000 0x3bffdfc4cc000000 0x077ffbf899800000

def z239 : W := mkw 0x1c0b0001504a4a60 0x438160002a09494c 0xf7efe38b737e4e63 0xfefdfc716e6fc9cc

def z240 : W := mkw 0xf1ec1fffabf55056 0x9e3d83fff57eaa0a 0xfffffffffffff07f 0xfffffffffffffe0f

def z241 : W := mkw 0xc1401aec28000006 0x1828035d85000000 0x377cdccf7c000000 0x06ef9b99ef800000

def z242 : W := mkw 0x0a028000440888a8 0x0140500008811115 0xfbf7c344cef989ff 0xff7ef86899df313f

def z243 : W := mkw 0x1c0b0001504a4a60 0x438160002a09494c 0x370c208b710e4e62 0x46e184116e21c9cc

def z244 : W := mkw 0xe1e01ffeaba50006 0x1c3c03ffd574a000 0x3ffffffffd8f8000 0x47ffffffffb1f000

def z245 : W := mkw 0x1c8f0113d05a5a70 0xc391e0227a0b4b4e 0xff6ce0bbf14e7e7e 0xdfed9c177e29cfcf

def z246 : W := mkw 0x0a028000440888a8 0x0140500008811115 0x3bb54044cc898980 0x4776a80899913130

def z247 : W := mkw 0x1c0f0001505a5a70 0xc381e0002a0b4b4e 0xf76ce08b737e7e7f 0xfeed9c116e6fcfcf

def z248 : W := mkw 0x1008000100404040 0x0201000020080808 0x8440800300404000 0x1088100060080800

def z249 : W := mkw 0x0000000000000000 0x0000000000000000 0x8048a08001460000 0x100914100028c000

def z250 : W := mkw 0x1c0b0001504a4a60 0x438160002a09494c 0x0000000000004e62 0x00000000000009cc

def z251 : W := mkw 0x0000000000000000 0x0000000000000000 0x8402803002007000 0x1080500600400e00

def z252 : W := mkw 0xa12016c003a50000 0x142402d80074a000 0xf7ffffcb73ff8001 0xfefffff96e7ff000

def z253 : W := mkw 0x0a028000440888a8 0x0140500008811115 0x3bb54044cc0009fe 0x0776a8089980013f

def z254 : W := mkw 0x0000000000000000 0x0000000000000000 0x01602080004e0000 0x802c04100009c000

def z255 : W := mkw 0x108c011380505050 0x82118022700a0a0a 0xffefc3bbf270707f 0xbffdf8777e4e0e0f

def z256 : W := mkw 0x1409000110424240 0x4281200022084848 0x0040208330460000 0x000804106608c000

def z257 : W := mkw 0x0084011280101010 0x8010802250020202 0x080000308000301c 0x0100000610000603

def z258 : W := mkw 0xc1401aec28000006 0x1828035d85000000 0x1f1fdcfc7c000000 0x03e3fb9f8f800000

def z259 : W := mkw 0xa10012c000250000 0x142002580004a000 0x0080034000318001 0x0010006800063000

def z260 : W := mkw 0x810012c000000000 0x1020025800000000 0xc1ffffc0014e0000 0xd83ffff80029c000

def z261 : W := mkw 0x81c013d2a8000002 0x1038027a55000000 0x2fe3c3f3fc000000 0x05fc787e7f800000

def z262 : W := mkw 0x0000000000000000 0x0000000000000000 0x1014000400800980 0x4202800080100130

def z263 : W := mkw 0x810012c000000000 0x1020025800000000 0x01ffdfc000000000 0x003ffbf800000000

def z264 : W := mkw 0xc1c01bfea8000006 0x1838037fd5000000 0x7fffdffffc800986 0x6ffffbffff900130

def z265 : W := mkw 0xebe29ffeefad88ae 0x1d7c53ffddf5b115 0xffffffffffff89ff 0xfffffffffffff13f

def z266 : W := mkw 0x1409000110424240 0x4281200022084848 0xc56ce08b314e4600 0xd8ad9c116629c8c0

def z267 : W := mkw 0x4a328c2c4788adad 0x0946518588f115b5 0x7bb75c74ce89b9ff 0xef76eb8e99d1373f

def z268 : W := mkw 0x0200800004008088 0x0040100000801011 0x49b540448c89819d 0xe936a80891913033

def z269 : W := mkw 0xab2296c047ad88a8 0x156452d808f5b115 0x7bb75f44ceb989ff 0xef76ebe899d7313f

def z270 : W := mkw 0x1e0b8001544acae8 0x43c170002a89595d 0xf7ece0cbfd4fce7b 0xdefd9c197fa9f9cf

def z271 : W := mkw 0xa12016c003a50000 0x142402d80074a000 0x01ffffc0018f8000 0x403ffff80031f000

def z272 : W := mkw 0xc1c01bfea8000006 0x1838037fd5000000 0xffffdffffe700001 0xbffffbffffce0000

def z273 : W := mkw 0x108c011380505050 0x82118022700a0a0a 0xe0e3c30382700079 0xbc1c7860704e000f

def z274 : W := mkw 0x108c011380505050 0x82118022700a0a0a 0x6ea140338000707f 0xadd4280670000e0f

def z275 : W := mkw 0x0000000000000000 0x0000000000000000 0x100c000801000e00 0x42018001002001c0

def z276 : W := mkw 0xa12016c003a50000 0x142402d80074a000 0x00083c8001060000 0x000107900020c000

def z277 : W := mkw 0xc9c21bfee8080826 0x1938437fdd010104 0x7fffdffffc080862 0xcffffbffff81010c

def z278 : W := mkw 0xa12016c003a50000 0x142402d80074a000 0xfbffffc4cfff8001 0xff7ffff899fff000

def z279 : W := mkw 0x0000000000000000 0x0000000000000000 0x1600000800004e02 0x02c00001000009c0

def z280 : W := mkw 0x40300c2c03802505 0x08060185807004a0 0xff7fdcbf73807f86 0x7feffb97ee700ff0

def z281 : W := mkw 0x10bc051383d07551 0x821780a2707a0eaa 0xeee3c33383f07fff 0xfddc7866707e0fff

def z282 : W := mkw 0x5ccb093ff84a4a66 0x4b996127ff09494c 0x3e00003ffc004e62 0x07c00007ff8009cc

def z283 : W := mkw 0x1409000110424240 0x4281200022084848 0x0400000b30004600 0x00800001660008c0

def z284 : W := mkw 0x108c011380505050 0x82118022700a0a0a 0xfef7c33782f079ff 0xffdef866f05e0f3f

def z285 : W := mkw 0x50bc0d3f83d07555 0x8a1781a7f07a0eaa 0xeeebdf3b8370767f 0xbddd7be7706e0ecf

def z286 : W := mkw 0x108c011380505050 0x82118022700a0a0a 0xae4283338270707e 0x15c85066704e0e0f

def z287 : W := mkw 0x1e0b8001544acae8 0x43c170002a89595d 0xf76ce08b71cfcfff 0xfeed9c116e39f9ff

def z288 : W := mkw 0xbd2b16c153ef4a60 0x57a562d82a7de94c 0xe1ffffc373ff8061 0xfc3ffff86e7ff00c

def z289 : W := mkw 0x0a028000440888a8 0x0140500008811115 0x3a910044cc8189ff 0x275220089990313f

def z290 : W := mkw 0x40c0093ea8000006 0x08180127d5000000 0x0400003b30000000 0x0080000766000000

def z291 : W := mkw 0x0004000000101010 0x8000800000020202 0x000000000230301d 0x2000000000460603

def z292 : W := mkw 0x0030040003802501 0x00060080007004a0 0x8000000003007600 0x1000000000600ec0

def z293 : W := mkw 0x4000082c00000004 0x0800010580000000 0x1e00003c00000000 0x03c0000780000000

def z294 : W := mkw 0x50bc0d3f83d07555 0x8a1781a7f07a0eaa 0xde5fdf3f03f07f86 0x7bcbfbe7e07e0ff0

def z295 : W := mkw 0xd1cc1bffa8505056 0x9a39837ff50a0a0a 0x3fffdffffc00707e 0x07fffbffff800e0f

def z296 : W := mkw 0xbd2b16c153ef4a60 0x57a562d82a7de94c 0xf77cfccb71cfce62 0xdeef9f996e39f9cc

def z297 : W := mkw 0x0000000000000000 0x0000000000000000 0x6bb540408089807f 0xed76a8081011300f

def z298 : W := mkw 0x188e0113c0585870 0x8311c022780b0b0e 0xffe7c333c278787f 0xfffcf866784f0f0f

def z299 : W := mkw 0x1c0b0001504a4a60 0x438160002a09494c 0xf660c00b70404e62 0x9ecc18016e0809cc

def z300 : W := mkw 0x1e0b8001544acae8 0x43c170002a89595d 0x7fb5404ffc89cfff 0xeff6a809ff9139ff

def z301 : W := mkw 0x508c093f80505054 0x8a118127f00a0a0a 0xfeffdf3f8270707f 0xbfdffbe7f04e0e0f

def z302 : W := mkw 0xc1301eec03802505 0x182603dd807004a0 0xdfffdffc03807f86 0x7bfffbff80700ff0

def z303 : W := mkw 0x1c0b0001504a4a60 0x438160002a09494c 0xffede08bf14e4e7f 0xfffdbc117e29c9cf

def z304 : W := mkw 0x40b00d3e83802505 0x081601a7d07004a0 0xfeffdf3f83807f86 0x7fdffbe7f0700ff0

def z305 : W := mkw 0x503c0c2d03d07555 0x8a078185a07a0eaa 0xde1fdc3c03f07fff 0xfbc3fb87807e0fff

def z306 : W := mkw 0x0a028000440888a8 0x0140500008811115 0xffbdc04ccd89cfff 0xfff7b80999b139ff

def z307 : W := mkw 0xe1201eec03a50004 0x1c2403dd8074a000 0xdffffffc03ff8001 0xfbffffff807ff000

def z308 : W := mkw 0x0000000000000000 0x0000000000000000 0x20a0000080000079 0x841400001000000f

def z309 : W := mkw 0x0030040003802501 0x00060080007004a0 0x0000000001800f80 0x40000000003001f0

def z310 : W := mkw 0xa1a417d283b51010 0x943482fa5076a202 0x08931f7082b1b01d 0x211263ee10563603

def z311 : W := mkw 0x0000000000000000 0x0000000000000000 0x7bb54044cc898001 0xef76a80899913000

def z312 : W := mkw 0x1409000110424240 0x4281200022084848 0xe668e08b31464662 0x9ccd1c116628c8cc

def z313 : W := mkw 0xc1c01bfea8000006 0x1838037fd5000000 0x3e931f7ffc000000 0x07d263efff800000

def z314 : W := mkw 0x1c0b0001504a4a60 0x438160002a09494c 0xf60cc00b71004e62 0x5ec198016e2009cc

def z315 : W := mkw 0x40300c2c03802505 0x08060185807004a0 0xfebfdc3c83807fff 0xffd7fb8790700fff

def z316 : W := mkw 0x1e0b8001544acae8 0x43c170002a89595d 0xf77ce0cf7dcfcfe2 0xdeef9c19efb9f9fc

def z317 : W := mkw 0x4010082c00002505 0x08020105800004a0 0x0400003800007600 0x0080000700000ec0

def z318 : W := mkw 0xa12016c003a50000 0x142402d80074a000 0x00101c4000818000 0x0002038800103000

def z319 : W := mkw 0xc1c01bfea8000006 0x1838037fd5000000 0x31fc1fcffc000000 0x063f83f9ff800000

def z320 : W := mkw 0x5c3b0c2d53ca6f65 0x4b876185aa794dec 0xf77cfc8f71ce4fe2 0xdeef9f91ee39c9fc

def z321 : W := mkw 0x5c1b082d504a6f65 0x4b836105aa094dec 0x3e00003f70007fe6 0x07c00007ee000ffc

def z322 : W := mkw 0xc1c01bfea8000006 0x1838037fd5000000 0x3bb75f74cc000000 0x0776ebee99800000

def z323 : W := mkw 0x40300c2c03802505 0x08060185807004a0 0xdfbfdc7c0389ff87 0xfbf7fb8f80713ff0

def z324 : W := mkw 0xcbc29bfeec0888ae 0x1978537fdd811115 0x3fffdffffc0009fe 0x07fffbffff80013f

def z325 : W := mkw 0xe1e01ffeaba50006 0x1c3c03ffd574a000 0xbfffffffff760000 0x17ffffffffeec000

def z326 : W := mkw 0x0284811284109098 0x8050902250821213 0x089303748eb1b19d 0x2112606e91d63633

def z327 : W := mkw 0xd1cc1bffa8505056 0x9a39837ff50a0a0a 0xbfffdffffe707000 0x17fffbffffce0e00

def z328 : W := mkw 0x0000000000000000 0x0000000000000000 0x3ffdc0cffc000000 0x07ffb819ff800000

def z329 : W := mkw 0x108c011380505050 0x82118022700a0a0a 0xc88303308270707f 0xb9106066104e0e0f

def z330 : W := mkw 0x0000000000000000 0x0000000000000000 0x088100008000001d 0x2110200010000003

def z331 : W := mkw 0x1e0b8001544acae8 0x43c170002a89595d 0x21e020c3fc4f8079 0x843c04187f89f00f

def z332 : W := mkw 0x1a8e8113c458d8f8 0x8351d022788b1b1f 0xeee3c33382f9f9ff 0xfddc7866705f3f3f

def z333 : W := mkw 0x1c0b0001504a4a60 0x438160002a09494c 0xe760e083704e4062 0x9cec1c106e09c80c

def z334 : W := mkw 0x108c011380505050 0x82118022700a0a0a 0xe6e0c3038070407b 0x9cdc1860700e080f

def z335 : W := mkw 0xb52916c113e74240 0x56a522d8227ce848 0x844abf8b33764600 0x108957f1666ec8c0

def z336 : W := mkw 0x0000000000000000 0x0000000000000000 0x40a1400000000001 0xa814280000000000

def z337 : W := mkw 0xc1c01bfea8000006 0x1838037fd5000000 0x7fffdffffc898001 0xeffffbffff913000

def z338 : W := mkw 0xa12016c003a50000 0x142402d80074a000 0xd7ffffc803ffce03 0xfafffff9007ff9c0

def z339 : W := mkw 0x54390c2d13c26745 0x4a872185a2784ce8 0x844abcbb33467600 0x108957976668cec0

def z340 : W := mkw 0x4000082c00000004 0x0800010580000000 0x040a9c3800000000 0x0081538700000000

def z341 : W := mkw 0xa12016c003a50000 0x142402d80074a000 0xc11ffcc0038f8000 0x7823ff980071f000

def z342 : W := mkw 0x1c0b0001504a4a60 0x438160002a09494c 0x954ca08b714e4e00 0x52a994116e29c9c0

def z343 : W := mkw 0x4a328c2c4788adad 0x0946518588f115b5 0xfe1fdc3ccf807ffe 0x7fc3fb8799f00fff

def z344 : W := mkw 0x1c0b0001504a4a60 0x438160002a09494c 0xe1602083714e4e62 0xdc2c04106e29c9cc

def z345 : W := mkw 0xb1ac17d383f55050 0x963582fa707eaa0a 0xe1ffffc383ff8079 0xfc3ffff8707ff00f

def z346 : W := mkw 0x1c0b0001504a4a60 0x438160002a09494c 0xe660e003014e4e62 0xdccc1c006029c9cc

def z347 : W := mkw 0x4000082c00000004 0x0800010580000000 0xde1fdc3c02007006 0x3bc3fb8780400e00

def z348 : W := mkw 0x0000000000000000 0x0000000000000000 0x4124400000080000 0xc824880000010000

def z349 : W := mkw 0x40300c2c03802505 0x08060185807004a0 0x9e1fdc3c03007600 0x13c3fb8780600ec0

def z350 : W := mkw 0x40300c2c03802505 0x08060185807004a0 0xce13dc3402807186 0x39c27b8680500e30

def z351 : W := mkw 0x0000000000000000 0x0000000000000000 0x0e00003000007006 0x01c0000600000e00

def z352 : W := mkw 0x0c030000500a0a20 0x418060000a014144 0x376ce08b710e0e00 0x46ed9c116e21c1c0

def z353 : W := mkw 0x0000000000000000 0x0000000000000000 0xc0002000014e0000 0xd80004000029c000

def z354 : W := mkw 0x4010082c00002505 0x08020105800004a0 0x1e1fdc3c00007f86 0x03c3fb8780000ff0

def z355 : W := mkw 0x1c0b0001504a4a60 0x438160002a09494c 0xff7de08f71ce4fe6 0xffefbc11ee39c9fc

def z356 : W := mkw 0xd1cc1bffa8505056 0x9a39837ff50a0a0a 0xeeebdfbbb270707f 0xbddd7bf7764e0e0f

def z357 : W := mkw 0x1c8f0113d05a5a70 0xc391e0227a0b4b4e 0x3e00003bf0007e7e 0x07c000077e000fcf

def z358 : W := mkw 0x0020040003800000 0x0004008000700000 0x001c1c0001800000 0x4003838000300000

def z359 : W := mkw 0x108c011380505050 0x82118022700a0a0a 0x2ee3c33380700079 0x85dc7866700e000f

def z360 : W := mkw 0x0a028000440888a8 0x0140500008811115 0x010000404c098000 0x0020000809813000

def z361 : W := mkw 0x0000000000000000 0x0000000000000000 0x8042830002700000 0x10085060004e0000

def z362 : W := mkw 0x0020040003800000 0x0004008000700000 0xda1fdc0403800986 0x7b43fb8080700130

def z363 : W := mkw 0x1c3b040153ca6f61 0x438760802a794dec 0xf76ce08b73ce7fe6 0xfeed9c116e79cffc

def z364 : W := mkw 0x0802000040080820 0x0100400008010104 0x4000000000080862 0xc80000000001010c

def z365 : W := mkw 0x810012c000000000 0x1020025800000000 0x00931f4000000000 0x001263e800000000

def z366 : W := mkw 0xab0292c0442d88a8 0x156052580885b115 0x21e023c0cc7f8079 0x843c0478198ff00f

def z367 : W := mkw 0x810012c000000000 0x1020025800000000 0x011c1cc000000000 0x0023839800000000

def z368 : W := mkw 0x1c0b0001504a4a60 0x438160002a09494c 0xe16ce083714e0060 0xdc2d9c106e29c00c

def z369 : W := mkw 0x2000000000250000 0x040000000004a000 0x00002000007f8001 0x80000400000ff000

def z370 : W := mkw 0xc1c01bfea8000006 0x1838037fd5000000 0x3e4a9fbffc000000 0x07c953f7ff800000

def z371 : W := mkw 0xcb429aec6c0888ae 0x1968535d8d811115 0x7bbd5cccfc8989ff 0xef77ab999f91313f

def z372 : W := mkw 0x4010082c00002505 0x08020105800004a0 0xde03c03c02007f86 0x3bc0780780400ff0

def z373 : W := mkw 0xfd3b1eed53ef6f65 0x5fa763ddaa7dedec 0xffffffff73ffffe7 0xffffffffee7ffffc

def z374 : W := mkw 0x0000000000000000 0x0000000000000000 0x7bb54044cc800986 0x6f76a80899900130

def z375 : W := mkw 0xeb329eec47adadad 0x1d6653dd88f5b5b5 0xfffffffccfffffff 0xffffffff99ffffff

def z376 : W := mkw 0x100c000100505050 0x82018000200a0a0a 0x0000000000700079 0x80000000000e000f

def z377 : W := mkw 0xb1ac17d383f55050 0x963582fa707eaa0a 0x844abfb303767000 0x108957f6606ece00

def z378 : W := mkw 0x0401000010020200 0x4080200002004040 0x0008208831060600 0x000104110620c0c0

def z379 : W := mkw 0x1c0b0001504a4a60 0x438160002a09494c 0xff6fe0bb734e7e66 0xffedfc176e69cfcc

def z380 : W := mkw 0x2020040003a50000 0x040400800074a000 0xc16ce08003ff8001 0xf82d9c10007ff000

def z381 : W := mkw 0x0a028000440888a8 0x0140500008811115 0x61a00040cc8989ff 0xec3400081991313f

def z382 : W := mkw 0x1a8e8113c458d8f8 0x8351d022788b1b1f 0xfee3c337ce7079ff 0xbfdc7866f9ce0f3f

def z383 : W := mkw 0x40c0093ea8000006 0x08180127d5000000 0x080000348c000000 0x0100000691800000

def z384 : W := mkw 0x100c000100505050 0x82018000200a0a0a 0xce03c0300270707f 0xb9c07806004e0e0f

def z385 : W := mkw 0x0000000000000000 0x0000000000000000 0x01a0004000098001 0x8034000800013000

def z386 : W := mkw 0x1a0a80014448c8e8 0x034150002889191d 0xfff5c047ccc9c9ff 0xfffeb808f999393f

def z387 : W := mkw 0x0a028000440888a8 0x0140500008811115 0x29b10044cc8981fd 0xa53620089991303f

def z388 : W := mkw 0x1c0b0001504a4a60 0x438160002a09494c 0x2000000370000060 0x040000006e00000c

def z389 : W := mkw 0x0200800004008088 0x0040100000801011 0x000000000081819d 0x2000000000103033

def z390 : W := mkw 0xf1bc1fff83f57555 0x9e3783fff07eaeaa 0xffffffff83ffffff 0xfffffffff07fffff

def z391 : W := mkw 0xd1fc1fffabd07557 0x9a3f83fff57a0eaa 0xffffdffffff07fff 0xfffffbfffffe0fff

def z392 : W := mkw 0x100c000100505050 0x82018000200a0a0a 0xe660c0030270707f 0xbccc1800604e0e0f

def z393 : W := mkw 0x0080011280000000 0x0010002250000000 0xeee3c33382700001 0xbddc7866704e0000

def z394 : W := mkw 0x108c011380505050 0x82118022700a0a0a 0x0400003300007000 0x0080000660000e00

def z395 : W := mkw 0x1c0b0001504a4a60 0x438160002a09494c 0x73646083704e0862 0xce6c8c106e09c10c

def z396 : W := mkw 0xc1f01ffeab802507 0x183e03ffd57004a0 0x3fffdffffd800f80 0x47fffbffffb001f0

def z397 : W := mkw 0x0a028000440888a8 0x0140500008811115 0x7aa14004cc0009ff 0xaf5428009980013f

def z398 : W := mkw 0x108c011380505050 0x82118022700a0a0a 0xe662c33302707062 0x9ccc5866604e0e0c

def z399 : W := mkw 0x1008000100404040 0x0201000020080808 0xf66cc00b01404e62 0xdecd9801602809cc

def z400 : W := mkw 0x1c0b0001504a4a60 0x438160002a09494c 0x3760208b704e4e62 0x86ec04116e09c9cc

def z401 : W := mkw 0x0080011280000000 0x0010002250000000 0xeee3c33382007006 0x3ddc786670400e00

def z402 : W := mkw 0x0000000000000000 0x0000000000000000 0x010c2080010e0000 0x402184100021c000

def z403 : W := mkw 0x0080011280000000 0x0010002250000000 0x0442833300000000 0x0088506660000000

def z404 : W := mkw 0xcbf29ffeef88adaf 0x197e53ffddf115b5 0xffffdfffff89ffff 0xfffffbfffff13fff

def z405 : W := mkw 0x0000000000000000 0x0000000000000000 0xc1fde0c001cf8001 0xf83fbc180039f000

def z406 : W := mkw 0x0084011280101010 0x8010802250020202 0xce83c3308230701f 0x39d0786610460e03

def z407 : W := mkw 0xe1301eec03a52505 0x1c2603dd8074a4a0 0x08931f7402b1b185 0x211263ee80563630

def z408 : W := mkw 0xab2296c047ad88a8 0x156452d808f5b115 0xd1ffffc44fff8981 0xfa3ffff889fff130

def z409 : W := mkw 0x40c0093ea8000006 0x08180127d5000000 0x3fb5407ffc000000 0x07f6a80fff800000

def z410 : W := mkw 0xcb429aec6c0888ae 0x1968535d8d811115 0x111c1ccc7c898980 0x422383998f913130

def z411 : W := mkw 0xe1301eec03a52505 0x1c2603dd8074a4a0 0xdf1ffcfc038fff86 0x7be3ff9f8071fff0

def z412 : W := mkw 0x918c13d380505050 0x9231827a700a0a0a 0xefffdff38270707f 0xbdfffbfe704e0e0f

def z413 : W := mkw 0x0802000040080820 0x0100400008010104 0xf72cc00841084e62 0xdee59801082109cc

def z414 : W := mkw 0xfdeb1ffffbef4a66 0x5fbd63ffff7de94c 0xffffffffffffce63 0xfffffffffffff9cc

def z415 : W := mkw 0x4a12882c4408adad 0x09425105888115b5 0x7fb5407ccc89ffff 0xeff6a80f99913fff

def z416 : W := mkw 0x1e0b8001544acae8 0x43c170002a89595d 0x3e00000ffc004ffe 0x07c00001ff8009ff

def z417 : W := mkw 0x0a028000440888a8 0x0140500008811115 0x7b244004cc0809fe 0xcf6488009981013f

def z418 : W := mkw 0xbd0b12c1506f4a60 0x57a162582a0de94c 0xf7ece3cb717fce63 0xdefd9c796e2ff9cc

def z419 : W := mkw 0x148d011390525250 0xc291a022720a4a4a 0x844aa3bb33767600 0x10895477666ecec0

def z420 : W := mkw 0x0c030000500a0a20 0x418060000a014144 0xd16ce088714e0e00 0xda2d9c110e29c1c0

def z421 : W := mkw 0x128c81138450d0d8 0x82519022708a1a1b 0xeef3c3778ef1f1ff 0xbdde786ef1de3e3f

def z422 : W := mkw 0xc3c09bfeac00808e 0x1878137fd5801011 0x3fffdffffc81819d 0x27fffbffff903033

def z423 : W := mkw 0x40b40d3e83903515 0x881681a7d07206a2 0x08931f3482b0319d 0x211263e690560633

def z424 : W := mkw 0xd1cc1bffa8505056 0x9a39837ff50a0a0a 0x3fffdffffc700079 0x87fffbffff8e000f

def z425 : W := mkw 0x0000000000000000 0x0000000000000000 0xc000000001004e02 0x58000000002009c0

def z426 : W := mkw 0xc1c01bfea8000006 0x1838037fd5000000 0x1e9fdf7c8c000000 0x03d3fbef91800000

def z427 : W := mkw 0x0a028000440888a8 0x0140500008811115 0x41b54040008989ff 0xe836a8080011313f

def z428 : W := mkw 0x50bc0d3f83d07555 0x8a1781a7f07a0eaa 0xfe1fdc3f83807ffe 0x7fc3fb87f0700fff

def z429 : W := mkw 0x1c0b0001504a4a60 0x438160002a09494c 0xd10c2088714e4e62 0xda2184110e29c9cc

def z430 : W := mkw 0x0200800004008088 0x0040100000801011 0x5a9540448c81899f 0x6b52a80891903133

def z431 : W := mkw 0x0000000000000000 0x0000000000000000 0x8408800801004600 0x10811001002008c0

def z432 : W := mkw 0x0084011280101010 0x8010802250020202 0xc8e3c3308270301d 0xb91c7866104e0603

def z433 : W := mkw 0x108c011380505050 0x82118022700a0a0a 0x2ee003338070707f 0x85dc0066700e0e0f

def z434 : W := mkw 0x0200800004008088 0x0040100000801011 0x080000048c00019c 0x0100000091800033

def z435 : W := mkw 0x0a028000440888a8 0x0140500008811115 0x19950044cc89899d 0x6332a00899913133

def z436 : W := mkw 0x1c0b0001504a4a60 0x438160002a09494c 0xd60ce008014e4e62 0xdac19c010029c9cc

def z437 : W := mkw 0x1e0b8001544acae8 0x43c170002a89595d 0xff6ce08ffd4e4ffe 0xdfed9c11ffa9c9ff

def z438 : W := mkw 0x100c000100505050 0x82018000200a0a0a 0xeaa140008270707f 0xbd542800104e0e0f

def z439 : W := mkw 0x0a028000440888a8 0x0140500008811115 0x51b540444c898981 0xea36a80889913130

def z440 : W := mkw 0x1c0b0001504a4a60 0x438160002a09494c 0x376ce08b704e0060 0x86ed9c116e09c00c

def z441 : W := mkw 0x40300c2c03802505 0x08060185807004a0 0x8c1b9c3c03807784 0x3183738780700ef0

def z442 : W := mkw 0x1409000110424240 0x4281200022084848 0x8000200001464600 0x100004000028c8c0

def z443 : W := mkw 0xd1c81bffa8404046 0x1a39037ff5080808 0xffffdffffc404062 0x9ffffbffff88080c

def z444 : W := mkw 0x0a028000440888a8 0x0140500008811115 0xfbfde0c4cdcf89ff 0xff7fbc1899b9f13f

def z445 : W := mkw 0xd5c91bffb8424246 0x5ab9237ff7084848 0x844abfbb31464600 0x108957f76628c8c0

def z446 : W := mkw 0x1c0b0001504a4a60 0x438160002a09494c 0x316c208b714e0e60 0xc62d84116e29c1cc

def z447 : W := mkw 0xc1c01bfea8000006 0x1838037fd5000000 0x2ef3df778c000000 0x05de7beef1800000

def z448 : W := mkw 0x4040082c28000006 0x0808010585000000 0x1000000c7c000000 0x020000018f800000

def z449 : W := mkw 0x509c093f80507555 0x8a138127f00a0eaa 0xfee3c33f82707fff 0xbfdc7867f04e0fff

def z450 : W := mkw 0xe1e01ffeaba50006 0x1c3c03ffd574a000 0x08931f748eb18001 0x211263ee91d63000

def z451 : W := mkw 0x48320c2c43882d25 0x09064185887105a4 0xff3fdc3c43887fe6 0xffe7fb8788710ffc

def z452 : W := mkw 0x0000000000000000 0x0000000000000000 0x4015400000800000 0x6802a80000100000

def z453 : W := mkw 0x1c0f0001505a5a70 0xc381e0002a0b4b4e 0xc0002000037e7e7f 0xf8000400006fcfcf

def z454 : W := mkw 0x1a8e8113c458d8f8 0x8351d022788b1b1f 0x21e00343cc798079 0x843c0068798f300f

def z455 : W := mkw 0x81c013d2a8000002 0x1038027a55000000 0x0040038330000000 0x0008007066000000

def z456 : W := mkw 0x0a028000440888a8 0x0140500008811115 0x20000000cc000078 0x040000001980000f

def z457 : W := mkw 0xa12016c003a50000 0x142402d80074a000 0xc05fff8003f60000 0x780bfff0007ec000

def z458 : W := mkw 0xb1ac17d383f55050 0x963582fa707eaa0a 0xeeebffb38376707f 0xbddd7ff6706ece0f

def z459 : W := mkw 0xb12816c103e54040 0x162502d8207ca808 0xe7ffffc303ffc063 0xfcfffff8607ff80c

def z460 : W := mkw 0x1088011380404040 0x0211002270080808 0xeee3c33380404062 0x9ddc78667008080c

def z461 : W := mkw 0x0a228400478888a8 0x0144508008f11115 0xfbbfdc44cf8989ff 0xff77fb8899f1313f

def z462 : W := mkw 0x0a028000440888a8 0x0140500008811115 0x3ba00044cc0989ff 0x877400089981313f

def z463 : W := mkw 0x810012c000000000 0x1020025800000000 0x41ffdfc000898001 0xe83ffbf800113000

def z464 : W := mkw 0x108c011380505050 0x82118022700a0a0a 0xc4e3c33302707001 0xb89c7866604e0e00

def z465 : W := mkw 0x4010082c00002505 0x08020105800004a0 0x0800003400003184 0x0100000680000630

def z466 : W := mkw 0xa12016c003a50000 0x142402d80074a000 0x81ffffc003760000 0x103ffff8006ec000

def z467 : W := mkw 0x0c030000500a0a20 0x418060000a014144 0x00002000010e0e00 0x400004000021c1c0

def z468 : W := mkw 0xc1701eec2b802507 0x182e03dd857004a0 0xdf1fdcfc7f807f86 0x7be3fb9f8ff00ff0

def z469 : W := mkw 0xa1a417d283b51010 0x943482fa5076a202 0xc9fffff083ffb01d 0xf93ffffe107ff603

def z470 : W := mkw 0x0c030000500a0a20 0x418060000a014144 0xd70ce088710e4e02 0x5ae19c110e21c9c0

def z471 : W := mkw 0x4a328c2c4788adad 0x0946518588f115b5 0x7bbd5c4ccd898fff 0xef77ab8999b131ff

def z472 : W := mkw 0x4000082c00000004 0x0800010580000000 0x101c1c0c00000000 0x0203838180000000

def z473 : W := mkw 0x1a8e8113c458d8f8 0x8351d022788b1b1f 0x7fb54077cc89f9ff 0xeff6a80ef9913f3f

def z474 : W := mkw 0xb12c16c103f55050 0x962582d8207eaa0a 0xc1ffffc003fff07f 0xf83ffff8007ffe0f

def z475 : W := mkw 0x0000000000000000 0x0000000000000000 0x2a0000008000007e 0x054000001000000f

def z476 : W := mkw 0x40300c2c03802505 0x08060185807004a0 0x00101c0400800180 0x0002038080100030

def z477 : W := mkw 0x1c3b040153ca6f61 0x438760802a794dec 0xc000200003ce7fe6 0xf80004000079cffc

def z478 : W := mkw 0x0000000000000000 0x0000000000000000 0x6220400000000062 0x8c4408000000000c

def z479 : W := mkw 0x0802000040080820 0x0100400008010104 0x73b5404040898863 0xee76a8080811310c

def z480 : W := mkw 0x4a328c2c4788adad 0x0946518588f115b5 0xde1fdc3c0389ffff 0xfbc3fb8780713fff

def z481 : W := mkw 0x1008000100404040 0x0201000020080808 0xc000000000404062 0x980000000008080c

def z482 : W := mkw 0x0000000000000000 0x0000000000000000 0x00e0030000700001 0x801c0060000e0000

def z483 : W := mkw 0x2020040003a50000 0x040400800074a000 0xc0e3e30003ff8001 0xf81c7c60007ff000

def z484 : W := mkw 0xddcb1bfff84a4a66 0x5bb9637fff09494c 0x3fffdffffc004e62 0x07fffbffff8009cc

def z485 : W := mkw 0x40200c2c03800004 0x0804018580700000 0xde1fdc3c03800000 0x7bc3fb8780700000

def z486 : W := mkw 0x0802000040080820 0x0100400008010104 0x2120000040080060 0x842400000801000c

def z487 : W := mkw 0x0084011280101010 0x8010802250020202 0x2ee3c3338230301d 0x25dc786670460603

def z488 : W := mkw 0x54390c2d13c26745 0x4a872185a2784ce8 0xde5ffcbf33c67f86 0x7bcbff97e678cff0

def z489 : W := mkw 0x5c3b0c2d53ca6f65 0x4b876185aa794dec 0xf76efcbb734e7e62 0xdeeddf976e69cfcc

def z490 : W := mkw 0x40300c2c03802505 0x08060185807004a0 0xdf7ffcbc03ce7f86 0xfbefff978079cff0

def z491 : W := mkw 0x0000000000000000 0x0000000000000000 0x3a000004cc000000 0x0740000099800000

def z492 : W := mkw 0x0000000000000000 0x0000000000000000 0xde17c03402807986 0x7bc2f80680500f30

def z493 : W := mkw 0x0802000040080820 0x0100400008010104 0x7ba54000c008087f 0xef74a8001801010f

def z494 : W := mkw 0x40300c2c03802505 0x08060185807004a0 0x1e1fdc3c01800f80 0x43c3fb87803001f0

def z495 : W := mkw 0x4000082c00000004 0x0800010580000000 0x3f7fdcbf70000000 0x07effb97ee000000

def z496 : W := mkw 0x0000000000000000 0x0000000000000000 0x0091004000818001 0x2012200800103000

def z497 : W := mkw 0xc1c41bfea8101016 0x9838837fd5020202 0x3fffdffffe30301d 0x27fffbffffc60603

def z498 : W := mkw 0x0020040003800000 0x0004008000700000 0xc17ffc8003ce0000 0xf82fff900079c000

def z499 : W := mkw 0x50cc093fa8505056 0x8a198127f50a0a0a 0xfee3c33ffe70707f 0xbfdc7867ffce0e0f

def z500 : W := mkw 0x0000000000000000 0x0000000000000000 0x4a01400000000006 0x2940280000000000

def z501 : W := mkw 0x103c040103d07551 0x82078080207a0eaa 0xc000000003f07fff 0xf8000000007e0fff

def z502 : W := mkw 0x0000000000000000 0x0000000000000000 0x00e3c30000000000 0x001c786000000000

def z503 : W := mkw 0x1c2b040153ca4a60 0x438560802a79494c 0xf77ffc8b73ce4e62 0xfeefff916e79c9cc

def z504 : W := mkw 0x4010082c00002505 0x08020105800004a0 0x1000000c00000f80 0x02000001800001f0

def z505 : W := mkw 0x2020040003a50000 0x040400800074a000 0xc1b5604003ff8001 0xf836ac08007ff000

def z506 : W := mkw 0x1c8f0113d05a5a70 0xc391e0227a0b4b4e 0xefe3e3b3f27e707f 0xbdfc7c767e4fce0f

def z507 : W := mkw 0xbdaf17d3d3ff5a70 0xd7b5e2fa7a7feb4e 0xfffffffbf3fffe7f 0xffffffff7e7fffcf

def z508 : W := mkw 0xc1401aec28000006 0x1828035d85000000 0x00101c440c000000 0x0002038881800000

def z509 : W := mkw 0x2020040003a50000 0x040400800074a000 0x0000000002b18001 0x2000000000563000

def z510 : W := mkw 0xc1701eec2b802507 0x182e03dd857004a0 0x111c1ccc7d800f80 0x422383998fb001f0

def z511 : W := mkw 0x40300c2c03802505 0x08060185807004a0 0xc41fdc3803807600 0x7883fb8700700ec0

def z512 : W := mkw 0x4010082c00002505 0x08020105800004a0 0xde0cc03c01007f86 0x5bc1980780200ff0

def z513 : W := mkw 0xa1c013d2a8250002 0x1438027a5504a000 0x21e023c3fc7f8001 0x843c04787f8ff000

def z514 : W := mkw 0xbf2b96c157efcae8 0x57e572d82afdf95d 0xffffffcfffffcfff 0xfffffff9fffff9ff

def z515 : W := mkw 0x1c0b0001504a4a60 0x438160002a09494c 0x00002000004e0060 0x800004000009c00c

def z516 : W := mkw 0x0020040003800000 0x0004008000700000 0xd61fdc0803804e02 0x7ac3fb81007009c0

def z517 : W := mkw 0xa12016c003a50000 0x142402d80074a000 0xc1e023c003ff8001 0xf83c0478007ff000

def z518 : W := mkw 0x0000000000000000 0x0000000000000000 0xf76ce08b714e0000 0xdeed9c116e29c000

def z519 : W := mkw 0x30ac051383f55050 0x861580a2707eaa0a 0xeee3e33383fff07f 0xfddc7c66707ffe0f

def z520 : W := mkw 0x0000000000000000 0x0000000000000000 0x0114004000898000 0x4022800800113000

def z521 : W := mkw 0xa12016c003a50000 0x142402d80074a000 0x41b75f4002b98001 0xe836ebe800573000

def z522 : W := mkw 0x40300c2c03802505 0x08060185807004a0 0xd61cdc0c01804f82 0x5ac39b81803009f0

def z523 : W := mkw 0x108c011380505050 0x82118022700a0a0a 0xe0e003038270707f 0xbc1c0060704e0e0f

def z524 : W := mkw 0x4ac2893eec0888ae 0x09585127dd811115 0x7fb5407ffc8989ff 0xeff6a80fff91313f

def z525 : W := mkw 0xe1301eec03a52505 0x1c2603dd8074a4a0 0xde5fffbc03f67f86 0x7bcbfff7807ecff0

def z526 : W := mkw 0x0802000040080820 0x0100400008010104 0x7bb54044cc080862 0xcf76a8089981010c

def z527 : W := mkw 0xa32096c007a58088 0x146412d800f4b011 0x08931f448eb1819d 0x211263e891d63033

def z528 : W := mkw 0x1008000100404040 0x0201000020080808 0x2060000300400060 0x840c00006008000c

def z529 : W := mkw 0x0030040003802501 0x00060080007004a0 0xda15400403807f86 0x7b42a80080700ff0

def z530 : W := mkw 0x302c040103f55050 0x86058080207eaa0a 0xc000200003fff07f 0xf8000400007ffe0f

def z531 : W := mkw 0x1008000100404040 0x0201000020080808 0xf76cc08b70404062 0x9eed98116e08080c

def z532 : W := mkw 0xcd431aec780a0a26 0x59a8635d8f014144 0x111c3ccc7d0e0e00 0x422387998fa1c1c0

def z533 : W := mkw 0xab2296c047ad88a8 0x156452d808f5b115 0xe1ffffc0cfff8079 0xfc3ffff819fff00f

def z534 : W := mkw 0x0000000000000000 0x0000000000000000 0x1a15400400000000 0x0342a80080000000

def z535 : W := mkw 0xe1e01ffeaba50006 0x1c3c03ffd574a000 0xc5fffffb33ff8001 0xf8bfffff667ff000

def z536 : W := mkw 0x1008000100404040 0x0201000020080808 0xee63c03302407066 0xbdcc780660480e0c

def z537 : W := mkw 0xb52916c113e74240 0x56a522d8227ce848 0xc5ffffcb33ffc601 0xf8bffff9667ff8c0

def z538 : W := mkw 0x1a8e8113c458d8f8 0x8351d022788b1b1f 0x3e000037cc0079fe 0x07c00006f9800f3f

def z539 : W := mkw 0xc1401aec28000006 0x1828035d85000000 0x00081c8830000000 0x0001039106000000

def z540 : W := mkw 0x0000000000000000 0x0000000000000000 0x089100448c000000 0x0112200891800000

def z541 : W := mkw 0x0a028000440888a8 0x0140500008811115 0x0000000000098079 0x800000000001300f

def z542 : W := mkw 0xcbc29bfeec0888ae 0x1978537fdd811115 0x7bb75f74cc8989ff 0xef76ebee9991313f

def z543 : W := mkw 0x3c2b040153ef4a60 0x478560802a7de94c 0xf76ce08b73ffce63 0xfeed9c116e7ff9cc

def z544 : W := mkw 0x0000000000000000 0x0000000000000000 0x111400444c000000 0x0222800889800000

def z545 : W := mkw 0x40300c2c03802505 0x08060185807004a0 0xd60edc3803007e02 0x5ac1db8700600fc0

def z546 : W := mkw 0x0000000000000000 0x0000000000000000 0xeea3c0308200707f 0xbdd4780610400e0f

def z547 : W := mkw 0x0030040003802501 0x00060080007004a0 0xce03c03003807f86 0x79c0780600700ff0

def z548 : W := mkw 0x0020040003800000 0x0004008000700000 0xc000000003800000 0x7800000000700000

def z549 : W := mkw 0xa10012c000250000 0x142002580004a000 0x41f563c000ff8001 0xe83eac78001ff000

def z550 : W := mkw 0x0000000000000000 0x0000000000000000 0x0e03c03000000000 0x01c0780600000000

def z551 : W := mkw 0x4c330c2c538a2f25 0x498661858a7145e4 0xdf1ffcbc738e7f86 0x7be3ff978e71cff0

def z552 : W := mkw 0x0200800004008088 0x0040100000801011 0x3bb54044cc81819d 0x2776a80899903033

def z553 : W := mkw 0xe1301eec03a52505 0x1c2603dd8074a4a0 0x111c3ccc018f8f80 0x422387998031f1f0

def z554 : W := mkw 0x0000000000000000 0x0000000000000000 0x7ab54004808009ff 0xef56a8009010013f

def z555 : W := mkw 0x1a0e80014458d8f8 0x8341d000288b1b1f 0xfbb54044cef9f9ff 0xff76a80899df3f3f

def z556 : W := mkw 0xad2316c053af0a20 0x55a462d80a75e144 0x111c3cc8718f8e00 0x422387990e31f1c0

def z557 : W := mkw 0x108c011380505050 0x82118022700a0a0a 0xaee3c33382707000 0x15dc7866704e0e00

def z558 : W := mkw 0xab2296c047ad88a8 0x156452d808f5b115 0xc1ffffc003ff89ff 0xf83ffff8007ff13f

def z559 : W := mkw 0xc1c01bfea8000006 0x1838037fd5000000 0xffffdffffd004e02 0x5ffffbffffa009c0

def z560 : W := mkw 0x0a028000440888a8 0x0140500008811115 0x6aa14000808989ff 0xed5428001011313f

def z561 : W := mkw 0x0a028000440888a8 0x0140500008811115 0x73244000408989ff 0xee6488000811313f

def z562 : W := mkw 0xa10012c000250000 0x142002580004a000 0x010020c0000f8000 0x002004180001f000

def z563 : W := mkw 0x4a12882c4408adad 0x09425105888115b5 0x3e00003ccc007ffe 0x07c0000799800fff

def z564 : W := mkw 0x2020040003a50000 0x040400800074a000 0xc01ffc0003ff8001 0xf803ff80007ff000

def z565 : W := mkw 0xe1601eec2ba50006 0x1c2c03dd8574a000 0x111c3ccc7d8f8000 0x422387998fb1f000

def z566 : W := mkw 0x108c011380505050 0x82118022700a0a0a 0x2ee3c3338000707e 0x05dc786670000e0f

def z567 : W := mkw 0x40300c2c03802505 0x08060185807004a0 0x5a1d5c0c01800f86 0x6b43ab81803001f0

def z568 : W := mkw 0x814012c028000002 0x1028025805000000 0x010000c07c000000 0x002000180f800000

def z569 : W := mkw 0xddfb1ffffbca6f67 0x5bbf63ffff794dec 0xffffffffffce7fe6 0xfffffffffff9cffc

def z570 : W := mkw 0xa12016c003a50000 0x142402d80074a000 0xc0ebff8003760001 0xb81d7ff0006ec000

def z571 : W := mkw 0x1c8f0113d05a5a70 0xc391e0227a0b4b4e 0xf76ee3bb737e7e62 0xdeeddc776e6fcfcc

def z572 : W := mkw 0xbd2b16c153ef4a60 0x57a562d82a7de94c 0xc1ffffc003ffce63 0xf83ffff8007ff9cc

def z573 : W := mkw 0x100c000100505050 0x82018000200a0a0a 0x8000000002707000 0x10000000004e0e00

def z574 : W := mkw 0x1008000100404040 0x0201000020080808 0x2600000300004062 0x04c000006000080c

def z575 : W := mkw 0x9dcb13d3f84a4a62 0x53b9627a7f09494c 0x21e023c3fc4e0060 0x843c04787f89c00c

def z576 : W := mkw 0x4a328c2c4788adad 0x0946518588f115b5 0xdf1fdc7c4f89ff86 0x7be3fb8f89f13ff0

def z577 : W := mkw 0xc1c01bfea8000006 0x1838037fd5000000 0x376edfbb70000000 0x06eddbf76e000000

def z578 : W := mkw 0x0020040003800000 0x0004008000700000 0x00131c0002800000 0x2002638000500000

def z579 : W := mkw 0xe1e01ffeaba50006 0x1c3c03ffd574a000 0x844abfbb33760000 0x108957f7666ec000

def z580 : W := mkw 0xc1c01bfea8000006 0x1838037fd5000000 0x199f1ffcfc000000 0x0333e3ff9f800000

def z581 : W := mkw 0xd1cc1bffa8505056 0x9a39837ff50a0a0a 0x844a9fbb32707000 0x108953f7664e0e00

def z582 : W := mkw 0x100c000100505050 0x82018000200a0a0a 0x000000000000707e 0x0000000000000e0f

def z583 : W := mkw 0x0000000000000000 0x0000000000000000 0xf76cc08b71004e02 0x5eed98116e2009c0

def z584 : W := mkw 0x0000000000000000 0x0000000000000000 0xc1efe380037e0001 0xf83dfc70006fc000

def z585 : W := mkw 0x1c0b0001504a4a60 0x438160002a09494c 0xf3246000414e4e62 0xde648c000829c9cc

def z586 : W := mkw 0x0a028000440888a8 0x0140500008811115 0x733440444c8989e2 0xce6688088991313c

def z587 : W := mkw 0x50bc0d3f83d07555 0x8a1781a7f07a0eaa 0xeef3df3782f071ff 0xbdde7be6f05e0e3f

def z588 : W := mkw 0xd1cc1bffa8505056 0x9a39837ff50a0a0a 0xeef3df778e70707f 0xbdde7beef1ce0e0f

def z589 : W := mkw 0x40300c2c03802505 0x08060185807004a0 0xde00003c03807f86 0x7bc0000780700ff0

def z590 : W := mkw 0x81c013d2a8000002 0x1038027a55000000 0x3bf543c7fc000000 0x077ea878ff800000

def z591 : W := mkw 0x0c030000500a0a20 0x418060000a014144 0x01002080700e0000 0x002004100e01c000

def z592 : W := mkw 0x5c0b082d504a4a64 0x4b816105aa09494c 0xff7ffcbf714e4e62 0xdfefff97ee29c9cc

def z593 : W := mkw 0x0084011280101010 0x8010802250020202 0x0002033002303000 0x0000406600460600

def z594 : W := mkw 0x0000000000000000 0x0000000000000000 0x110c008870000000 0x022180110e000000

def z595 : W := mkw 0xddcb1bfff84a4a66 0x5bb9637fff09494c 0x3ffffffffc4e0060 0x87ffffffff89c00c

def z596 : W := mkw 0x0000000000000000 0x0000000000000000 0x3600000b70000000 0x06c000016e000000

def z597 : W := mkw 0xc1f01ffeab802507 0x183e03ffd57004a0 0x08931f748e803184 0x211263ee91d00630

def z598 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z599 : W := mkw 0x4000082c00000004 0x0800010580000000 0x08131c3400000000 0x0102638680000000

def z600 : W := mkw 0x0200800004008088 0x0040100000801011 0x001000440c818180 0x0002000881903030

def z601 : W := mkw 0x1c0b0001504a4a60 0x438160002a09494c 0x7724400b70084e62 0xcee488016e0109cc

def z602 : W := mkw 0xe1301eec03a52505 0x1c2603dd8074a4a0 0xde9fdf7c03b1ff87 0x7bd3fbef80763ff0

def z603 : W := mkw 0x0a028000440888a8 0x0140500008811115 0x5b1540444c898986 0x6b62a80889913130

def z604 : W := mkw 0x810012c000000000 0x1020025800000000 0x004a9f8000000000 0x000953f000000000

def z605 : W := mkw 0x91cc13d3a8505052 0x9239827a750a0a0a 0xefe3c3f3fe70707f 0xbdfc787e7fce0e0f

def z606 : W := mkw 0xc1f01ffeab802507 0x183e03ffd57004a0 0xde9fdf7c8f807f86 0x7bd3fbef91f00ff0

def z607 : W := mkw 0x108c011380505050 0x82118022700a0a0a 0x8cc383338270701d 0x31987066704e0e03

def z608 : W := mkw 0xa92216c043ad0820 0x152442d80875a104 0xf3ffffc043ff8863 0xfe7ffff8087ff10c

def z609 : W := mkw 0xcbc29bfeec0888ae 0x1978537fdd811115 0x3fffdffffc098079 0x87fffbffff81300f

def z610 : W := mkw 0x42308c2c0780a58d 0x0846118580f014b1 0xde9fdc7c8f81ff9f 0x7bd3fb8f91f03ff3

def z611 : W := mkw 0x1c8f0113d05a5a70 0xc391e0227a0b4b4e 0xeee3e333837e7e7f 0xfddc7c66706fcfcf

def z612 : W := mkw 0x81c013d2a8000002 0x1038027a55000000 0x008003408c000000 0x0010006811800000

def z613 : W := mkw 0x1c8f0113d05a5a70 0xc391e0227a0b4b4e 0x21e02383f07e0079 0x843c04707e0fc00f

def z614 : W := mkw 0x0020040003800000 0x0004008000700000 0xc1bfdc4003898001 0xf837fb8800713000

def z615 : W := mkw 0x0000000000000000 0x0000000000000000 0x5bb5404400898987 0xeb76a80880113130

def z616 : W := mkw 0x4080093e80000004 0x08100127d0000000 0x3effdf3f80000000 0x07dffbe7f0000000

def z617 : W := mkw 0x1008000100404040 0x0201000020080808 0xe6e3c30302704063 0xbcdc7860604e080c

def z618 : W := mkw 0x0a3284004788ada9 0x0146508008f115b5 0xfbb54044cf89ffff 0xff76a80899f13fff

def z619 : W := mkw 0x0080011280000000 0x0010002250000000 0x0883033080000000 0x0110606610000000

def z620 : W := mkw 0xa1a017d283a50000 0x143402fa5074a000 0xeffffff383ff8001 0xfdfffffe707ff000

def z621 : W := mkw 0x4000082c00000004 0x0800010580000000 0xde1fdc3c01004e02 0x5bc3fb87802009c0

def z622 : W := mkw 0x1a0e80014458d8f8 0x8341d000288b1b1f 0xc000000002f9f9ff 0xf8000000005f3f3f

def z623 : W := mkw 0x108c011380505050 0x82118022700a0a0a 0x6ae143038070007f 0xad5c2860700e000f

def z624 : W := mkw 0x3c2b040153ef4a60 0x478560802a7de94c 0xc000200003ffce63 0xf8000400007ff9cc

def z625 : W := mkw 0xc1f01ffeab802507 0x183e03ffd57004a0 0xbfffdfffff007600 0x17fffbffffe00ec0

def z626 : W := mkw 0x40c0093ea8000006 0x08180127d5000000 0x3ee3c33ffc000000 0x07dc7867ff800000

def z627 : W := mkw 0xe1301eec03a52505 0x1c2603dd8074a4a0 0xc5fffff803fff601 0xf8bfffff007ffec0

def z628 : W := mkw 0x4010082c00002505 0x08020105800004a0 0x5e15403c00807f86 0x6bc2a80780100ff0

def z629 : W := mkw 0x40300c2c03802505 0x08060185807004a0 0xc81fdc3403803184 0x7903fb8680700630

def z630 : W := mkw 0x0010000000002501 0x00020000000004a0 0x0000000000007f86 0x0000000000000ff0

def z631 : W := mkw 0xc1c01bfea8000006 0x1838037fd5000000 0x2eebdfbbb0000000 0x05dd7bf776000000

def z632 : W := mkw 0x509c093f80507555 0x8a138127f00a0eaa 0x3e00003f80007ffe 0x07c00007f0000fff

def z633 : W := mkw 0x4ac2893eec0888ae 0x09585127dd811115 0x3e00003ffc0009fe 0x07c00007ff80013f

def z634 : W := mkw 0x1e0b8001544acae8 0x43c170002a89595d 0x7bf560c7fccf89ff 0xef7eac18ff99f13f

def z635 : W := mkw 0x0000000000000000 0x0000000000000000 0x4000000000898001 0xe800000000113000

def z636 : W := mkw 0x4000082c00000004 0x0800010580000000 0x5e1fdc3c00800986 0x6bc3fb8780100130

def z637 : W := mkw 0x0000000000000000 0x0000000000000000 0x0083030002300001 0x2010606000460000

def z638 : W := mkw 0xc1c01bfea8000006 0x1838037fd5000000 0xfffffffffd4e0000 0xdfffffffffa9c000

def z639 : W := mkw 0x4a02882c440888ac 0x0940510588811115 0x7fbfdc7ccc8989ff 0xeff7fb8f9991313f

def z640 : W := mkw 0xa1e017d2aba50002 0x143c02fa5574a000 0xe1ffffc3ffff8001 0xfc3ffff87ffff000

def z641 : W := mkw 0x1c8f0113d05a5a70 0xc391e0227a0b4b4e 0xf7ece38bf17e4e7b 0xdefd9c717e2fc9cf

def z642 : W := mkw 0x2030040003a52501 0x040600800074a4a0 0xc000200003ffff87 0xf8000400007ffff0

def z643 : W := mkw 0x0000000000000000 0x0000000000000000 0x400000000000007f 0xa80000000000000f

def z644 : W := mkw 0x0000000000000000 0x0000000000000000 0xde0fc03803007e06 0x7bc1f80700600fc0

def z645 : W := mkw 0x50bc0d3f83d07555 0x8a1781a7f07a0eaa 0x844a9f3b03707600 0x108953e7606e0ec0

def z646 : W := mkw 0x00c00112a8000002 0x0018002255000000 0x20000003fc000000 0x040000007f800000

def z647 : W := mkw 0x1c0b0001504a4a60 0x438160002a09494c 0x376cc08b70004e62 0x06ed98116e0009cc

def z648 : W := mkw 0xa32096c007a58088 0x146412d800f4b011 0xc9ffffc48fff819d 0xf93ffff891fff033

def z649 : W := mkw 0x40f00d3eab802507 0x081e01a7d57004a0 0xfe1fdc3fff807f86 0x7fc3fb87fff00ff0

def z650 : W := mkw 0xa10012c000250000 0x142002580004a000 0x0040238000760000 0x00080470000ec000

def z651 : W := mkw 0x0000000000000000 0x0000000000000000 0xc600c00000004002 0x18c0180000000800

def z652 : W := mkw 0xa12016c003a50000 0x142402d80074a000 0xc16eff80037e0000 0xd82ddff0006fc000

def z653 : W := mkw 0x40300c2c03802505 0x08060185807004a0 0xd01fdc0c03800f80 0x7a03fb81807001f0

def z654 : W := mkw 0xc1c01bfea8000006 0x1838037fd5000000 0x05ffdffb30000000 0x00bffbff66000000

def z655 : W := mkw 0x8bc293d2ec0888aa 0x1178527a5d811115 0x7bf543c7fc8989ff 0xef7ea878ff91313f

def z656 : W := mkw 0xe1301eec03a52505 0x1c2603dd8074a4a0 0x844abfb803767600 0x108957f7006ecec0

def z657 : W := mkw 0xa12016c003a50000 0x142402d80074a000 0xc11c3cc003ff8001 0xf8238798007ff000

def z658 : W := mkw 0xc1e01ffeab800006 0x183c03ffd5700000 0xffffdfffff800000 0x7ffffbfffff00000

def z659 : W := mkw 0x0000000000000000 0x0000000000000000 0x5204400000000802 0x4a40880000000100

def z660 : W := mkw 0x0802000040080820 0x0100400008010104 0x776cc08b70080862 0xceed98116e01010c

def z661 : W := mkw 0x50cc093fa8505056 0x8a198127f50a0a0a 0x3e00003ffc00707e 0x07c00007ff800e0f

def z662 : W := mkw 0x0a028000440888a8 0x0140500008811115 0x7a154004cc8009fe 0x6f42a8009990013f

def z663 : W := mkw 0x0030040003802501 0x00060080007004a0 0xd60cc00803807f86 0x7ac1980100700ff0

def z664 : W := mkw 0x0802000040080820 0x0100400008010104 0x1104000040080800 0x4220800008010100

def z665 : W := mkw 0xc1c01bfea8000006 0x1838037fd5000000 0x0cdb9fffbc000000 0x019b73fff7800000

def z666 : W := mkw 0x0000000000000000 0x0000000000000000 0x160cc00800000000 0x02c1980100000000

def z667 : W := mkw 0xc1c01bfea8000006 0x1838037fd5000000 0x3fe003fffc000000 0x07fc007fff800000

def z668 : W := mkw 0x0000000000000000 0x0000000000000000 0xcee3c33002707007 0xb9dc7866004e0e00

def z669 : W := mkw 0xa12016c003a50000 0x142402d80074a000 0x80dbbfc003f78001 0x301b77f8007ef000

def z670 : W := mkw 0x0000000000000000 0x0000000000000000 0xc060c00000400000 0x980c180000080000

def z671 : W := mkw 0xa12016c003a50000 0x142402d80074a000 0xc09fdf4003b18001 0x7813fbe800763000

def z672 : W := mkw 0x5c1b082d504a6f65 0x4b836105aa094dec 0xff6ce0bf714e7fe6 0xdfed9c17ee29cffc

def z673 : W := mkw 0x50380c2d03c06545 0x0a070185a0780ca8 0xfe7fdc3f03c07fe6 0xffcffb87e0780ffc

def z674 : W := mkw 0xc1c01bfea8000006 0x1838037fd5000000 0x09ffdff48c000000 0x013ffbfe91800000

def z675 : W := mkw 0x0020040003800000 0x0004008000700000 0xc0ffdf0003f00001 0xf81ffbe0007e0000

def z676 : W := mkw 0x0802000040080820 0x0100400008010104 0x7b354004408809e6 0xef66a8008811013c

def z677 : W := mkw 0xc1f01ffeab802507 0x183e03ffd57004a0 0xde5fdfbf33807f86 0x7bcbfbf7e6700ff0

def z678 : W := mkw 0x1c0b0001504a4a60 0x438160002a09494c 0xf600200b714e4e62 0xdec004016e29c9cc

def z679 : W := mkw 0xb1ac17d383f55050 0x963582fa707eaa0a 0xc5fffff303fff001 0xf8bffffe607ffe00

def z680 : W := mkw 0xe1601eec2ba50006 0x1c2c03dd8574a000 0xd1ffffcc7fff8001 0xfa3ffff98ffff000

def z681 : W := mkw 0x1c0b0001504a4a60 0x438160002a09494c 0xc16ce080014e4e62 0xd82d9c100029c9cc

def z682 : W := mkw 0x0a868112c41898b8 0x8150d02258831317 0x7bb74374ceb9b9ff 0xef76e86e99d7373f

def z683 : W := mkw 0x0080011280000000 0x0010002250000000 0x3ff7c377cc000000 0x07fef86ef9800000

def z684 : W := mkw 0x0000000000000000 0x0000000000000000 0x0811000400800184 0x2102200080100030

def z685 : W := mkw 0x40300c2c03802505 0x08060185807004a0 0x181f1c3c03803f84 0x6303e387807007f0

def z686 : W := mkw 0x0000000000000000 0x0000000000000000 0x0803003002003004 0x2100600600400600

def z687 : W := mkw 0x0c030000500a0a20 0x418060000a014144 0x1000000870000e00 0x020000010e0001c0

def z688 : W := mkw 0xb1ac17d383f55050 0x963582fa707eaa0a 0xeef3df7382f1f07f 0xbdde7bee705e3e0f

def z689 : W := mkw 0x0802000040080820 0x0100400008010104 0xf36ce080414e0862 0xde6d9c100829c10c

def z690 : W := mkw 0xbd2b16c153ef4a60 0x57a562d82a7de94c 0xf76eff8b737e4e62 0xdeeddff16e6fc9cc

def z691 : W := mkw 0x818013d280000000 0x1030027a50000000 0x2fffdff380000000 0x05fffbfe70000000

def z692 : W := mkw 0x0a828112c40888a8 0x0150502258811115 0x7ff7c377cc8989ff 0xeffef86ef991313f

def z693 : W := mkw 0x1a8e8113c458d8f8 0x8351d022788b1b1f 0xefe3c373ce79f07f 0xbdfc786e79cf3e0f

def z694 : W := mkw 0xa12016c003a50000 0x142402d80074a000 0x019f3fc003bf8001 0x6033e7f80077f000

def z695 : W := mkw 0x1008000100404040 0x0201000020080808 0xe76ce083014e4062 0xdced9c106029c80c

def z696 : W := mkw 0x0000000000000000 0x0000000000000000 0x2660c00300000000 0x04cc180060000000

def z697 : W := mkw 0x40b40d3e83903515 0x881681a7d07206a2 0xde9fdf3c83b07f9f 0x7bd3fbe790760ff3

def z698 : W := mkw 0x0000000000000000 0x0000000000000000 0x016cc08000000000 0x002d981000000000

def z699 : W := mkw 0x1c8f0113d05a5a70 0xc391e0227a0b4b4e 0xfee3c33bf2707e7f 0xbfdc78677e4e0fcf

def z700 : W := mkw 0x10ac051383d05050 0x821580a2707a0a0a 0xeeffdf3383f0707f 0xfddffbe6707e0e0f

def z701 : W := mkw 0x108c011380505050 0x82118022700a0a0a 0xee0000338270707f 0xbdc00006704e0e0f

def z702 : W := mkw 0x2020040003a50000 0x040400800074a000 0x00002000018f8000 0x400004000031f000

def z703 : W := mkw 0x1e0b8001544acae8 0x43c170002a89595d 0xfbb56044cdcfcfff 0xff76ac0899b9f9ff

def z704 : W := mkw 0xdbce9bffec58d8fe 0x9b79d37ffd8b1b1f 0xffffdffffef9f9ff 0xfffffbffffdf3f3f

def z705 : W := mkw 0x40300c2c03802505 0x08060185807004a0 0xd01c1c0c03807f86 0x7a03838180700ff0

def z706 : W := mkw 0x0030040003802501 0x00060080007004a0 0x0000000002803184 0x2000000000500630

def z707 : W := mkw 0x1c0b0001504a4a60 0x438160002a09494c 0x736c608b714e0e62 0xce6d8c116e29c1cc

def z708 : W := mkw 0xa12016c003a50000 0x142402d80074a000 0x81fbbfc003ff8001 0xb03f77f8007ff000

def z709 : W := mkw 0x40300c2c03802505 0x08060185807004a0 0xde13dc3c02807f86 0x3bc27b8780500ff0

def z710 : W := mkw 0x40300c2c03802505 0x08060185807004a0 0x9e1e9c3c03807f86 0x53c3d38780700ff0

def z711 : W := mkw 0x1409000110424240 0x4281200022084848 0x844aa0bb33467600 0x108954176668cec0

def z712 : W := mkw 0x40300c2c03802505 0x08060185807004a0 0xdffffcfc03cfff87 0xfbffff9f8079fff0

def z713 : W := mkw 0xe1c01bfea8250006 0x1c38037fd504a000 0x3ffffffffc0f8000 0x07ffffffff81f000

def z714 : W := mkw 0x40300c2c03802505 0x08060185807004a0 0x840a9c3803007f86 0x1081538700600ff0

def z715 : W := mkw 0xc1c01bfea8000006 0x1838037fd5000000 0x3e5fdfbffc000000 0x07cbfbf7ff800000

def z716 : W := mkw 0x108c011380505050 0x82118022700a0a0a 0xffefc3bbf3707e7f 0xfffdf8777e6e0fcf

def z717 : W := mkw 0xc1c01bfea8000006 0x1838037fd5000000 0x3fffdffffc000079 0x87fffbffff80000f

def z718 : W := mkw 0x1409000110424240 0x4281200022084848 0xbffde0cffd464600 0x17ffbc19ffa8c8c0

def z719 : W := mkw 0x108c011380505050 0x82118022700a0a0a 0xee8303338270707f 0xbdd06066704e0e0f

def z720 : W := mkw 0x1c0b0001504a4a60 0x438160002a09494c 0xf760208b714e4e62 0xdeec04116e29c9cc

def z721 : W := mkw 0xc1c01bfea8000006 0x1838037fd5000000 0x1f5fdfff7c000000 0x03ebfbffef800000

def z722 : W := mkw 0x1a8e8113c458d8f8 0x8351d022788b1b1f 0x955683774ef9f980 0x52aad06ee9df3f30

def z723 : W := mkw 0x0a028000440888a8 0x0140500008811115 0x7bf7c344cc8989ff 0xef7ef8689991313f

def z724 : W := mkw 0x108c011380505050 0x82118022700a0a0a 0xce43c3330270707f 0xb9c87866604e0e0f

def z725 : W := mkw 0x40300c2c03802505 0x08060185807004a0 0xde1fdc3c03f07f87 0xfbc3fb87807e0ff0

def z726 : W := mkw 0x40c0093ea8000006 0x08180127d5000000 0x3effdf3ffc000000 0x07dffbe7ff800000

def z727 : W := mkw 0x1e0b8001544acae8 0x43c170002a89595d 0xff7de0cf7dcfcfe6 0xffefbc19efb9f9fc

def z728 : W := mkw 0x40300c2c03802505 0x08060185807004a0 0xc41fdc3803807f86 0x7883fb8700700ff0

def z729 : W := mkw 0x40300c2c03802505 0x08060185807004a0 0x9e1fdc3c03807f80 0x53c3fb8780700ff0

def z730 : W := mkw 0xc1c01bfea8000006 0x1838037fd5000000 0x3fffdffffc098001 0x87fffbffff813000

def z731 : W := mkw 0xc1c01bfea8000006 0x1838037fd5000000 0x3fffdffffc700001 0x87fffbffff8e0000

def z732 : W := mkw 0x1c0b0001504a4a60 0x438160002a09494c 0x310c208b710e0e60 0x462184116e21c1cc

def z733 : W := mkw 0x148d011390525250 0xc291a022720a4a4a 0xfeefe3bbb3767e7f 0xffddfc77766ecfcf

def z734 : W := mkw 0x1e0b8001544acae8 0x43c170002a89595d 0xff7ce0cffdcfcffe 0xdfef9c19ffb9f9ff

def z735 : W := mkw 0xb1ac17d383f55050 0x963582fa707eaa0a 0x2f1c3cf3818ff07e 0x45e3879e7031fe0f

def z736 : W := mkw 0x81c013d2a8000002 0x1038027a55000000 0x21fc1fc3fc000000 0x043f83f87f800000

def z737 : W := mkw 0x0e038000540a8aa8 0x41c070000a815155 0x7ffde0cffd8f8fff 0xefffbc19ffb1f1ff

def z738 : W := mkw 0xc1c01bfea8000006 0x1838037fd5000000 0xffffdffffe00707f 0xbffffbffffc00e0f

def z739 : W := mkw 0x1e0b8001544acae8 0x43c170002a89595d 0xf77ce0cf7dcfcfff 0xfeef9c19efb9f9ff

def z740 : W := mkw 0x81f017d2ab802503 0x103e02fa557004a0 0xe1e003c3ff807f86 0x7c3c00787ff00ff0

def z741 : W := mkw 0xa12016c003a50000 0x142402d80074a000 0xcbffffc003ff8007 0xf97ffff8007ff000

def z742 : W := mkw 0x108c011380505050 0x82118022700a0a0a 0xeef3c3778e70707f 0xbdde786ef1ce0e0f

def z743 : W := mkw 0xc1c01bfea8000006 0x1838037fd5000000 0x3f5e9ffffc000000 0x07ebd3ffff800000

def z744 : W := mkw 0x0c030000500a0a20 0x418060000a014144 0xf76ce08b714e0e00 0xdeed9c116e29c1c0

def z745 : W := mkw 0x40300c2c03802505 0x08060185807004a0 0xde7fdc3c03c07f86 0xfbcffb8780780ff0

def z746 : W := mkw 0x1e0b8001544acae8 0x43c170002a89595d 0xf7fde0cb71cfcfff 0xfeffbc196e39f9ff

def z747 : W := mkw 0xc1c01bfea8000006 0x1838037fd5000000 0x3fffdffffc818001 0x27fffbffff903000

def z748 : W := mkw 0xa12016c003a50000 0x142402d80074a000 0xc0f3ff4003ff8001 0xf81e7fe8007ff000

def z749 : W := mkw 0x1e0b8001544acae8 0x43c170002a89595d 0xfffde0cffd4e4ffe 0xdfffbc19ffa9c9ff

def z750 : W := mkw 0xc1c01bfea8000006 0x1838037fd5000000 0x31ffdfcffc000000 0x063ffbf9ff800000

def z751 : W := mkw 0x108c011380505050 0x82118022700a0a0a 0xefefc3b38270707f 0xbdfdf876704e0e0f

def z752 : W := mkw 0x108c011380505050 0x82118022700a0a0a 0xce83c3308270707f 0xb9d07866104e0e0f

def z753 : W := mkw 0xa12016c003a50000 0x142402d80074a000 0xd1ffffc403ff8981 0xfa3ffff8807ff130

def z754 : W := mkw 0x0a028000440888a8 0x0140500008811115 0xfbb54044cd89cfff 0xff76a80899b139ff

def z755 : W := mkw 0x0a028000440888a8 0x0140500008811115 0x69b54044cc8981fd 0xed36a8089991303f

def z756 : W := mkw 0x0a028000440888a8 0x0140500008811115 0x69b10044cc8989ff 0xed3620089991313f

def z757 : W := mkw 0xc1c01bfea8000006 0x1838037fd5000000 0xffffdffffe707007 0xbffffbffffce0e00

def z758 : W := mkw 0xa12016c003a50000 0x142402d80074a000 0x41f77fc002ff8001 0xe83eeff8005ff000

def z759 : W := mkw 0x1c0b0001504a4a60 0x438160002a09494c 0xf7ece38b717e4e63 0xdefd9c716e2fc9cc

def z760 : W := mkw 0xa12016c003a50000 0x142402d80074a000 0xc1ffffc003ffce03 0xf83ffff8007ff9c0

def z761 : W := mkw 0x0084011280101010 0x8010802250020202 0xeea3c3308230707f 0xbdd4786610460e0f

def z762 : W := mkw 0xa12016c003a50000 0x142402d80074a000 0xd1ffffc873ff8001 0xfa3ffff90e7ff000

def z763 : W := mkw 0x160980011442c2c8 0x42c1300022885859 0x8cd9a0cfbdc7c79d 0x319b3419f7b8f8f3

def z764 : W := mkw 0x0a028000440888a8 0x0140500008811115 0x7bb74074ce89b9ff 0xef76e80e99d1373f

def z765 : W := mkw 0x108c011380505050 0x82118022700a0a0a 0xe8e3c3338270307d 0xbd1c7866704e060f

def z766 : W := mkw 0xa12016c003a50000 0x142402d80074a000 0xc0dbbfc003ff8001 0xf81b77f8007ff000

def z767 : W := mkw 0x108c011380505050 0x82118022700a0a0a 0xfeffc33f83f07fff 0xffdff867f07e0fff

def z768 : W := mkw 0x1c0b0001504a4a60 0x438160002a09494c 0xf76ce08b734e7e66 0xfeed9c116e69cfcc

def z769 : W := mkw 0x1409000110424240 0x4281200022084848 0xa648a08b31464662 0x14c914116628c8cc

def z770 : W := mkw 0xc1c01bfea8000006 0x1838037fd5000000 0x3e9fdf7ffc000000 0x07d3fbefff800000

def z771 : W := mkw 0x1e0b8001544acae8 0x43c170002a89595d 0x31fc20cffdcf8ff9 0xc63f8419ffb9f1ff

def z772 : W := mkw 0x108c011380505050 0x82118022700a0a0a 0xe4e3c33382707079 0xbc9c7866704e0e0f

def z773 : W := mkw 0x0a028000440888a8 0x0140500008811115 0x3bb54044cc8989fe 0x4776a8089991313f

def z774 : W := mkw 0xa10012c000250000 0x142002580004a000 0x01eabfc0007f8001 0x803d57f8000ff000

def z775 : W := mkw 0x0c030000500a0a20 0x418060000a014144 0xf76ce08b710e4e02 0x5eed9c116e21c9c0

def z776 : W := mkw 0xc1c41bfea8101016 0x9838837fd5020202 0xffffdffffe70301d 0xbffffbffffce0603

def z777 : W := mkw 0x0c870112d01a1a30 0xc190e0225a034346 0x198f23b8f33e3e1d 0x6331e4771e67c7c3

def z778 : W := mkw 0xa12016c003a50000 0x142402d80074a000 0xfbffffc4cfff8987 0xff7ffff899fff130

def z779 : W := mkw 0xc1401aec28000006 0x1828035d85000000 0x155c9ccf7c000000 0x02ab9399ef800000

def z780 : W := mkw 0x60e00d3eaba50006 0x0c1c01a7d574a000 0xfe00203fffff8001 0xffc00407fffff000

def z781 : W := mkw 0x810012c000000000 0x1020025800000000 0x3fffdfcffc000000 0x07fffbf9ff800000

def z782 : W := mkw 0xa12016c003a50000 0x142402d80074a000 0xfbffffc4cfff807f 0xff7ffff899fff00f

def z783 : W := mkw 0xa12016c003a50000 0x142402d80074a000 0xcffffff003ff8001 0xf9fffffe007ff000

def z784 : W := mkw 0x40300c2c03802505 0x08060185807004a0 0xdf7fdcbc03807f86 0x7beffb9780700ff0

def z785 : W := mkw 0x0200800004008088 0x0040100000801011 0x2a9100448c8181ff 0x255220089190303f

def z786 : W := mkw 0x5c3b0c2d53ca6f65 0x4b876185aa794dec 0x29733cb772ce31e4 0xa52e6796ee59c63c

def z787 : W := mkw 0x0a028000440888a8 0x0140500008811115 0x7b344044cc8989fe 0xcf6688089991313f

def z788 : W := mkw 0x40c0093ea8000006 0x08180127d5000000 0x3f7fdcbffc000000 0x07effb97ff800000

def z789 : W := mkw 0x108c011380505050 0x82118022700a0a0a 0xeff7c3738270707f 0xbdfef86e704e0e0f

def z790 : W := mkw 0xe1101aec00252505 0x1c22035d8004a4a0 0x1fe023fc007fff87 0x83fc047f800ffff0

def z791 : W := mkw 0x0401000010020200 0x4080200002004040 0x0448a08b31060600 0x008914116620c0c0

def z792 : W := mkw 0x108c011380505050 0x82118022700a0a0a 0xaee283338270707f 0x95dc5066704e0e0f

def z793 : W := mkw 0x108c011380505050 0x82118022700a0a0a 0xa442833382707078 0x14885066704e0e0f

def z794 : W := mkw 0x108c011380505050 0x82118022700a0a0a 0xeee3c33382f079ff 0xfddc7866705e0f3f

def z795 : W := mkw 0x1c0b0001504a4a60 0x438160002a09494c 0xb76ce08b714e4660 0x96ed9c116e29c8cc

def z796 : W := mkw 0x1c0b0001504a4a60 0x438160002a09494c 0x150c208b710e4e00 0x42a184116e21c9c0

def z797 : W := mkw 0x1409000110424240 0x4281200022084848 0xc448a08b314e4600 0xd88914116629c8c0

def z798 : W := mkw 0x40300c2c03802505 0x08060185807004a0 0xde0edc3c03007f86 0x5bc1db8780600ff0

def z799 : W := mkw 0x40300c2c03802505 0x08060185807004a0 0xde1cdc3c01807f86 0x5bc39b8780300ff0

def z800 : W := mkw 0xa16016c02ba50002 0x142c02d80574a000 0xc1ffffc07fff8001 0xf83ffff80ffff000

def z801 : W := mkw 0xa12016c003a50000 0x142402d80074a000 0xffffffcfffff8001 0xfffffff9fffff000

def z802 : W := mkw 0xd14c1aed28505056 0x9a29835da50a0a0a 0xd11c1ccc7e70707f 0xba2383998fce0e0f

def z803 : W := mkw 0x40c0093ea8000006 0x08180127d5000000 0x3e131c3ffc000000 0x07c26387ff800000

def z804 : W := mkw 0xc1c01bfea8000006 0x1838037fd5000000 0x3fffdffffc00001d 0x27fffbffff800003

def z805 : W := mkw 0x0a028000440888a8 0x0140500008811115 0x39b50044cc8989fd 0xe736a0089991313f

def z806 : W := mkw 0x1c0b0001504a4a60 0x438160002a09494c 0xf7efe38b714e4e62 0xdefdfc716e29c9cc

def z807 : W := mkw 0x108c011380505050 0x82118022700a0a0a 0xefe3c3738279f07f 0xbdfc786e704f3e0f

def z808 : W := mkw 0x0a028000440888a8 0x0140500008811115 0x21b00044cc8981f9 0x843600089991303f

def z809 : W := mkw 0x81c013d2a8000002 0x1038027a55000000 0x21ea9fc3fc000000 0x043d53f87f800000

def z810 : W := mkw 0xc1c01bfea8000006 0x1838037fd5000000 0x28931f77fc000000 0x051263eeff800000

def z811 : W := mkw 0x1c0b0001504a4a60 0x438160002a09494c 0xb56ca08b714e4e60 0xd6ad94116e29c9cc

def z812 : W := mkw 0x148d011390525250 0xc291a022720a4a4a 0xeee3e3338376767f 0xbddc7c66706ececf

def z813 : W := mkw 0x4a328c2c4788adad 0x0946518588f115b5 0xa5aa9c78cf09f679 0x94b5538f19e13ecf

def z814 : W := mkw 0x108c011380505050 0x82118022700a0a0a 0xfff7c377cef079ff 0xfffef86ef9de0f3f

def z815 : W := mkw 0xc1c01bfea8000006 0x1838037fd5000000 0x7fffdffffc080000 0xcffffbffff810000

def z816 : W := mkw 0x1c0f0001505a5a70 0xc381e0002a0b4b4e 0xf76ce08b737e7e62 0xdeed9c116e6fcfcc

def z817 : W := mkw 0x40300c2c03802505 0x08060185807004a0 0xde5ffcbc03c67f86 0x7bcbff978078cff0

def z818 : W := mkw 0xe1c01bfea8250006 0x1c38037fd504a000 0xfffffffffe7f8001 0xbfffffffffcff000

def z819 : W := mkw 0x1c0b0001504a4a60 0x438160002a09494c 0xf77de08b71ce4e62 0xfeefbc116e39c9cc

def z820 : W := mkw 0x4010082c00002505 0x08020105800004a0 0x1e0a9c3c00007f86 0x03c1538780000ff0

def z821 : W := mkw 0x1e0b8001544acae8 0x43c170002a89595d 0xffffe3cfffffcfff 0xfffffc79fffff9ff

def z822 : W := mkw 0x40300c2c03802505 0x08060185807004a0 0xff3fdc3c43807f86 0x7fe7fb8788700ff0

def z823 : W := mkw 0x108c011380505050 0x82118022700a0a0a 0x20e2033382703079 0x841c4066704e060f

def z824 : W := mkw 0xa12016c003a50000 0x142402d80074a000 0xe1ffffc083ff8079 0xfc3ffff8107ff00f

def z825 : W := mkw 0xc1c01bfea8000006 0x1838037fd5000000 0x115c1fcf7c000000 0x022b83f9ef800000

def z826 : W := mkw 0x1409000110424240 0x4281200022084848 0x9648a08b31464e02 0x12c914116628c9c0

def z827 : W := mkw 0xa12016c003a50000 0x142402d80074a000 0x01e23fc0027f8001 0x803c47f8004ff000

def z828 : W := mkw 0x1c0b0001504a4a60 0x438160002a09494c 0xf76ce08b71ce4fe6 0xfeed9c116e39c9fc

def z829 : W := mkw 0xc1c01bfea8000006 0x1838037fd5000000 0x7fffdffffc800000 0x6ffffbffff900000

def z830 : W := mkw 0xc1c41bfea8101016 0x9838837fd5020202 0x3fffdffffe303000 0x07fffbffffc60600

def z831 : W := mkw 0x108c011380505050 0x82118022700a0a0a 0xefffe3f383fff07f 0xfdfffc7e707ffe0f

def z832 : W := mkw 0x1409000110424240 0x4281200022084848 0x844aa38b33764600 0x10895471666ec8c0

def z833 : W := mkw 0x0a028000440888a8 0x0140500008811115 0xfff7c374cef9f9ff 0xfffef86e99df3f3f

def z834 : W := mkw 0xc1c01bfea8000006 0x1838037fd5000000 0x3edb9ffffc000000 0x07db73ffff800000

def z835 : W := mkw 0x0a028000440888a8 0x0140500008811115 0x7ab14044cc8189ff 0xaf5628089990313f

def z836 : W := mkw 0x0a028000440888a8 0x0140500008811115 0x71b40044cc8989ff 0xee3680089991313f

def z837 : W := mkw 0x1c0b0001504a4a60 0x438160002a09494c 0x2168208b714e0660 0x842d04116e29c0cc

def z838 : W := mkw 0xa12016c003a50000 0x142402d80074a000 0xc5ffffc803ffc601 0xf8bffff9007ff8c0

def z839 : W := mkw 0x0a028000440888a8 0x0140500008811115 0x31140044cc8989f8 0x462280089991313f

def z840 : W := mkw 0x1c0b0001504a4a60 0x438160002a09494c 0xfffde0cffdce4fe6 0xffffbc19ffb9c9fc

def z841 : W := mkw 0xeb329eec47adadad 0x1d6653dd88f5b5b5 0x111c3ccc4d8f8f80 0x4223879989b1f1f0

def z842 : W := mkw 0x1c0b0001504a4a60 0x438160002a09494c 0xfffde0cf71cfcfe7 0xffffbc19ee39f9fc

def z843 : W := mkw 0x1409000110424240 0x4281200022084848 0xc468e08b31464600 0x988d1c116628c8c0

def z844 : W := mkw 0x40300c2c03802505 0x08060185807004a0 0xfebfdc3c83807f86 0x7fd7fb8790700ff0

def z845 : W := mkw 0x0a028000440888a8 0x0140500008811115 0xfbffe3c4cfff89ff 0xff7ffc7899fff13f

def z846 : W := mkw 0x40300c2c03802505 0x08060185807004a0 0xd60edc3803807f86 0x7ac1db8700700ff0

def z847 : W := mkw 0x0a028000440888a8 0x0140500008811115 0x73b44044cc8989fb 0xce7688089991313f

def z848 : W := mkw 0xc1c01bfea8000006 0x1838037fd5000000 0x3e081cbffc000000 0x07c10397ff800000

def z849 : W := mkw 0x0a028000440888a8 0x0140500008811115 0x7fb5404ccc89cfff 0xeff6a809999139ff

def z850 : W := mkw 0xbd2b16c153ef4a60 0x57a562d82a7de94c 0x36931f4b72b1ce63 0x26d263e96e5639cc

def z851 : W := mkw 0x1409000110424240 0x4281200022084848 0xde5de08f31c64f86 0x7bcbbc11e638c9f0

def z852 : W := mkw 0x0a028000440888a8 0x0140500008811115 0xfbb54044cef989ff 0xff76a80899df313f

def z853 : W := mkw 0x108c011380505050 0x82118022700a0a0a 0xeeebe3b38376707f 0xbddd7c76706ece0f

def z854 : W := mkw 0x108c011380505050 0x82118022700a0a0a 0xeeffdf338270707f 0xbddffbe6704e0e0f

def z855 : W := mkw 0x40300c2c03802505 0x08060185807004a0 0xfeffdf3c83f07fff 0xffdffbe7907e0fff

def z856 : W := mkw 0xa12016c003a50000 0x142402d80074a000 0xc1b77f4003ff8001 0xf836efe8007ff000

def z857 : W := mkw 0x1e0b8001544acae8 0x43c170002a89595d 0x955ca0cf7dcfcf80 0x52ab9419efb9f9f0

def z858 : W := mkw 0x108c011380505050 0x82118022700a0a0a 0xeee3c33383707e7f 0xfddc7866706e0fcf

def z859 : W := mkw 0x1e0b8001544acae8 0x43c170002a89595d 0xf76ce08bfd4e4e7a 0xdeed9c117fa9c9cf

def z860 : W := mkw 0x1e0b8001544acae8 0x43c170002a89595d 0xf76ce08b714fce7b 0xdeed9c116e29f9cf

def z861 : W := mkw 0x40300c2c03802505 0x08060185807004a0 0xd81f1c3c03807f86 0x7b03e38780700ff0

def z862 : W := mkw 0x0000000000000000 0x0000000000000000 0xeee3c3308270707f 0xbddc7866104e0e0f

def z863 : W := mkw 0xc1c01bfea8000006 0x1838037fd5000000 0x39ff1ffffc000000 0x073fe3ffff800000

def z864 : W := mkw 0x60300c2c03a52505 0x0c0601858074a4a0 0xdf7ffcbc03ffff87 0xfbefff97807ffff0

def z865 : W := mkw 0x108c011380505050 0x82118022700a0a0a 0x6ae343338270307f 0xad5c6866704e060f

def z866 : W := mkw 0x40300c2c03802505 0x08060185807004a0 0x840a9c3803807f80 0x5081538700700ff0

def z867 : W := mkw 0x1c0b0001504a4a60 0x438160002a09494c 0xb74ca08b714e4e62 0x56e994116e29c9cc

def z868 : W := mkw 0xc1c01bfea8000006 0x1838037fd5000000 0x3fbd5cfffc000000 0x07f7ab9fff800000

def z869 : W := mkw 0x1e0b8001544acae8 0x43c170002a89595d 0xfffde0cffd4fce7b 0xdfffbc19ffa9f9cf

def z870 : W := mkw 0x0030040003802501 0x00060080007004a0 0xce1fdc3003807f86 0x79c3fb8600700ff0

def z871 : W := mkw 0x40300c2c03802505 0x08060185807004a0 0xce0bdc3803807f86 0x79c17b8700700ff0

def z872 : W := mkw 0x108c011380505050 0x82118022700a0a0a 0xeeefc3338370707f 0xfdddf866706e0e0f

def z873 : W := mkw 0x40300c2c03802505 0x08060185807004a0 0xfe1fdc3c83807ffe 0x7fc3fb8790700fff

def z874 : W := mkw 0x1e0b8001544acae8 0x43c170002a89595d 0xffece0cffd4fcfff 0xdffd9c19ffa9f9ff

def z875 : W := mkw 0x108c011380505050 0x82118022700a0a0a 0xfee7c3338270787f 0xffdcf866704e0f0f

def z876 : W := mkw 0x1c0b0001504a4a60 0x438160002a09494c 0xf16ce08b714e0e60 0xde2d9c116e29c1cc

def z877 : W := mkw 0x1c0b0001504a4a60 0x438160002a09494c 0x772c608b710e4e62 0xcee58c116e21c9cc

def z878 : W := mkw 0xc1c41bfea8101016 0x9838837fd5020202 0x7fffdffffe30307f 0xaffffbffffc6060f

def z879 : W := mkw 0x1c0b0001504a4a60 0x438160002a09494c 0xe56ce08b714e4660 0xdcad9c116e29c8cc

def z880 : W := mkw 0x40300c2c03802505 0x08060185807004a0 0xdfffffbc03fe7f87 0xfbfffff7807fcff0

def z881 : W := mkw 0xa12016c003a50000 0x142402d80074a000 0x01f03fc000ff8001 0x803e07f8001ff000

def z882 : W := mkw 0x1e0b8001544acae8 0x43c170002a89595d 0xf7fce0cffdcfcffb 0xdeff9c19ffb9f9ff

def z883 : W := mkw 0xa12016c003a50000 0x142402d80074a000 0xc1eeffc0037f8001 0xd83ddff8006ff000

def z884 : W := mkw 0x148d011390525250 0xc291a022720a4a4a 0xffefe3bbf376767f 0xbffdfc777e6ececf

def z885 : W := mkw 0xcbc29bfeec0888ae 0x1978537fdd811115 0x444a9fbb308989ff 0xe88953f76611313f

def z886 : W := mkw 0x10cc0113a8505052 0x82198022750a0a0a 0xeee3c333fe70707f 0xbddc78667fce0e0f

def z887 : W := mkw 0x108c011380505050 0x82118022700a0a0a 0xffefe3bbf37e707f 0xfffdfc777e6fce0f

def z888 : W := mkw 0xc1c01bfea8000006 0x1838037fd5000000 0x7fffdffffc000062 0x8ffffbffff80000c

def z889 : W := mkw 0x0084011280101010 0x8010802250020202 0x6ee3c3338230307f 0xaddc78667046060f

def z890 : W := mkw 0xe1c01bfea8250006 0x1c38037fd504a000 0x3fffdffffc318001 0x07fffbffff863000

def z891 : W := mkw 0xa12016c003a50000 0x142402d80074a000 0xd3ffffc003ff8803 0xfa7ffff8007ff100

def z892 : W := mkw 0x1409000110424240 0x4281200022084848 0xc648e08b31464602 0x18c91c116628c8c0

def z893 : W := mkw 0x40f00d3eab802507 0x081e01a7d57004a0 0xfe00003fff807f86 0x7fc00007fff00ff0

def z894 : W := mkw 0x40300c2c03802505 0x08060185807004a0 0x9c1f9c3c03807f84 0x7383f38780700ff0

def z895 : W := mkw 0x1e0b8001544acae8 0x43c170002a89595d 0xbe48a08ffd464ffe 0x17c91411ffa8c9ff

def z896 : W := mkw 0xa12016c003a50000 0x142402d80074a000 0xc1ffffc003ff8987 0xf83ffff8007ff130

def z897 : W := mkw 0x40300c2c03802505 0x08060185807004a0 0xce13dc3403807f86 0x79c27b8680700ff0

def z898 : W := mkw 0xa12016c003a50000 0x142402d80074a000 0xc1ffffc003ff807f 0xf83ffff8007ff00f

def z899 : W := mkw 0xa12016c003a50000 0x142402d80074a000 0xc0023f0003ff8001 0xf80047e0007ff000

def z900 : W := mkw 0x4010082c00002505 0x08020105800004a0 0x1e131c3c00007f86 0x03c2638780000ff0

def z901 : W := mkw 0x40300c2c03802505 0x08060185807004a0 0xdf1ffcbc038e7f86 0x7be3ff978071cff0

def z902 : W := mkw 0x1c0b0001504a4a60 0x438160002a09494c 0xb76ce08b71464e62 0x16ed9c116e28c9cc

def z903 : W := mkw 0x1409000110424240 0x4281200022084848 0xc448a08b31464e02 0x588914116628c9c0

def z904 : W := mkw 0x1409000110424240 0x4281200022084848 0xc4ebe38b33764601 0xb89d7c71666ec8c0

def z905 : W := mkw 0xc1c01bfea8000006 0x1838037fd5000000 0xbffffffffd460000 0x17ffffffffa8c000

def z906 : W := mkw 0xc1401aec28000006 0x1828035d85000000 0x371c1ccf7c000000 0x06e38399ef800000

def z907 : W := mkw 0x50bc0d3f83d07555 0x8a1781a7f07a0eaa 0x30fc1f0f81f00ff9 0xc61f83e1f03e01ff

def z908 : W := mkw 0x1c0f0001505a5a70 0xc381e0002a0b4b4e 0xff6fe0bb737e7e7f 0xffedfc176e6fcfcf

def z909 : W := mkw 0x4000082c00000004 0x0800010580000000 0x3fffdcfffc000000 0x07fffb9fff800000

def z910 : W := mkw 0x0084011280101010 0x8010802250020202 0x488303308230307f 0xa91060661046060f

def z911 : W := mkw 0xa12016c003a50000 0x142402d80074a000 0xdffffff403fff987 0xfbfffffe807fff30

def z912 : W := mkw 0x0e038000540a8aa8 0x41c070000a815155 0x7bb56044cd8f8fff 0xef76ac0899b1f1ff

def z913 : W := mkw 0x0200800004008088 0x0040100000801011 0x28b100448c8181fd 0xa51620089190303f

def z914 : W := mkw 0x4010082c00002505 0x08020105800004a0 0x5e1fdc3c00807f86 0x6bc3fb8780100ff0

def z915 : W := mkw 0x1409000110424240 0x4281200022084848 0x0048208b31460600 0x000904116628c0c0

def z916 : W := mkw 0xa12016c003a50000 0x142402d80074a000 0xc1fc3fc003ff8001 0xf83f87f8007ff000

def z917 : W := mkw 0x1409000110424240 0x4281200022084848 0x0408208b31064600 0x008104116620c8c0

def z918 : W := mkw 0xa12016c003a50000 0x142402d80074a000 0xc0ebff8003ff8001 0xf81d7ff0007ff000

def z919 : W := mkw 0x40300c2c03802505 0x08060185807004a0 0xdfbfdc7c03807f86 0x7bf7fb8f80700ff0

def z920 : W := mkw 0xa12016c003a50000 0x142402d80074a000 0xc5ffffcb33ff8001 0xf8bffff9667ff000

def z921 : W := mkw 0x0e038000540a8aa8 0x41c070000a815155 0x7bb5404cfc898fff 0xef76a8099f9131ff

def z922 : W := mkw 0x108c011380505050 0x82118022700a0a0a 0xefe7c3338278707f 0xfdfcf866704f0e0f

def z923 : W := mkw 0x108c011380505050 0x82118022700a0a0a 0xc00203300270707f 0xb8004066004e0e0f

def z924 : W := mkw 0x108c011380505050 0x82118022700a0a0a 0x6ea343338230707f 0xadd4686670460e0f

def z925 : W := mkw 0x1c0b0001504a4a60 0x438160002a09494c 0xd56ce08b714e4e00 0xdaad9c116e29c9c0

def z926 : W := mkw 0xddcb1bfff84a4a66 0x5bb9637fff09494c 0xc8933f748d4e4e62 0xd91267ee91a9c9cc

def z927 : W := mkw 0x1c0b0001504a4a60 0x438160002a09494c 0xf76ce08b71cfce63 0xfeed9c116e39f9cc

def z928 : W := mkw 0xc1c01bfea8000006 0x1838037fd5000000 0x3f1fdcfffc000000 0x07e3fb9fff800000

def z929 : W := mkw 0x108c011380505050 0x82118022700a0a0a 0x2e0203338230707e 0x05c0406670460e0f

def z930 : W := mkw 0x1c0b0001504a4a60 0x438160002a09494c 0xff6ce08ffd4e4e62 0xdfed9c11ffa9c9cc

def z931 : W := mkw 0x40300c2c03802505 0x08060185807004a0 0xde9fdc3c83807f9f 0x7bd3fb8790700ff3

def z932 : W := mkw 0xc1c01bfea8000006 0x1838037fd5000000 0xbfffdffffe007000 0x17fffbffffc00e00

def z933 : W := mkw 0x40300c2c03802505 0x08060185807004a0 0xdf3fdc3c03887f86 0xfbe7fb8780710ff0

def z934 : W := mkw 0x1c0b0001504a4a60 0x438160002a09494c 0xffede08bf14e4e62 0xdffdbc117e29c9cc

def z935 : W := mkw 0x1e3b840157caefe9 0x43c770802af95dfd 0xc000200003cfffff 0xf80004000079ffff

def z936 : W := mkw 0xc1c01bfea8000006 0x1838037fd5000000 0x3fffdffffe300001 0x27fffbffffc60000

def z937 : W := mkw 0x108c011380505050 0x82118022700a0a0a 0x088303308270307d 0xa1106066104e060f

def z938 : W := mkw 0xc1c01bfea8000006 0x1838037fd5000000 0x7fffdffffc000802 0x4ffffbffff800100

def z939 : W := mkw 0x40300c2c03802505 0x08060185807004a0 0xde9fdc7c0381ff87 0x7bd3fb8f80703ff0

def z940 : W := mkw 0xc1c01bfea8000006 0x1838037fd5000000 0x3bf75ff7fc000000 0x077eebfeff800000

def z941 : W := mkw 0x1c0b0001504a4a60 0x438160002a09494c 0xf7ede08b714e4e63 0xfefdbc116e29c9cc

def z942 : W := mkw 0x40c0093ea8000006 0x08180127d5000000 0x3fbfdc7ffc000000 0x07f7fb8fff800000

def z943 : W := mkw 0x108c011380505050 0x82118022700a0a0a 0xe4e283338270707f 0xbc9c5066704e0e0f

def z944 : W := mkw 0x108c011380505050 0x82118022700a0a0a 0xeaa343308270707f 0xbd546866104e0e0f

def z945 : W := mkw 0x40c0093ea8000006 0x08180127d5000000 0x3e1c1c3ffc000000 0x07c38387ff800000

def z946 : W := mkw 0x1c0f0001505a5a70 0xc381e0002a0b4b4e 0xf76ce08b714e7e7e 0xdeed9c116e29cfcf

def z947 : W := mkw 0x0a028000440888a8 0x0140500008811115 0xfffde0cffdcf89ff 0xffffbc19ffb9f13f

def z948 : W := mkw 0x1c0b0001504a4a60 0x438160002a09494c 0xf7ece08bf14e4e7b 0xdefd9c117e29c9cf

def z949 : W := mkw 0x148d011390525250 0xc291a022720a4a4a 0xeee3e3b3b276707f 0xbddc7c76764ece0f

def z950 : W := mkw 0x40300c2c03802505 0x08060185807004a0 0xde1fdc3c0389ff87 0xfbc3fb8780713ff0

def z951 : W := mkw 0x108c011380505050 0x82118022700a0a0a 0xeeebc3bbb270707f 0xbddd7877764e0e0f

def z952 : W := mkw 0x0200800004008088 0x0040100000801011 0x7ab540448c8189ff 0xef56a8089190313f

def z953 : W := mkw 0xc1c01bfea8000006 0x1838037fd5000000 0x3fffdffffe003004 0x27fffbffffc00600

def z954 : W := mkw 0x0a028000440888a8 0x0140500008811115 0x6ab140448c8989ff 0xed5628089191313f

def z955 : W := mkw 0x0c030000500a0a20 0x418060000a014144 0x316c208b710e0e00 0x462d84116e21c1c0

def z956 : W := mkw 0x0084011280101010 0x8010802250020202 0xeae3c3308270307f 0xbd5c7866104e060f

def z957 : W := mkw 0xc1c01bfea8000006 0x1838037fd5000000 0x7fffdffffc000006 0x2ffffbffff800000

def z958 : W := mkw 0xc1c01bfea8000006 0x1838037fd5000000 0xffffdffffd804f86 0x7ffffbffffb009f0

def z959 : W := mkw 0x40300c2c03802505 0x08060185807004a0 0x1e081c3c01007f86 0x03c1038780200ff0

def z960 : W := mkw 0x108c011380505050 0x82118022700a0a0a 0x088303308230707f 0x2110606610460e0f

def z961 : W := mkw 0x108c011380505050 0x82118022700a0a0a 0xeeebc33b8370767f 0xbddd7867706e0ecf

def z962 : W := mkw 0x108c011380505050 0x82118022700a0a0a 0xfee3c337827079ff 0xbfdc7866f04e0f3f

def z963 : W := mkw 0x0a028000440888a8 0x0140500008811115 0xffb5c044cc89c9ff 0xfff6b8089991393f

def z964 : W := mkw 0x40300c2c03802505 0x08060185807004a0 0xde1ffc3c03ce7f86 0xfbc3ff878079cff0

def z965 : W := mkw 0x1c0b0001504a4a60 0x438160002a09494c 0xffefe3bb737e7e67 0xfffdfc776e6fcfcc

def z966 : W := mkw 0xc1c01bfea8000006 0x1838037fd5000000 0x3fffdffffc898000 0x47fffbffff913000

def z967 : W := mkw 0x40300c2c03802505 0x08060185807004a0 0x141c1c3c01807f80 0x4283838780300ff0

def z968 : W := mkw 0xc1c01bfea8000006 0x1838037fd5000000 0xfffffffffd4e4e02 0xdfffffffffa9c9c0

def z969 : W := mkw 0xa12016c003a50000 0x142402d80074a000 0x41fd7fc001ff8001 0xe83faff8003ff000

def z970 : W := mkw 0xc1c01bfea8000006 0x1838037fd5000000 0x7fffdffffc8009ff 0xeffffbffff90013f

def z971 : W := mkw 0x3e2b840157efcae8 0x47c570802afdf95d 0xc000200003ffcfff 0xf8000400007ff9ff

def z972 : W := mkw 0x1c0b0001504a4a60 0x438160002a09494c 0xf16c208b714e4e62 0xde2d84116e29c9cc

def z973 : W := mkw 0x40300c2c03802505 0x08060185807004a0 0xd61edc3c03807f82 0x5ac3db8780700ff0

def z974 : W := mkw 0xc1c01bfea8000006 0x1838037fd5000000 0x35fe9ffffc000000 0x06bfd3ffff800000

def z975 : W := mkw 0xa12016c003a50000 0x142402d80074a000 0xeffffff083fff07f 0xfdfffffe107ffe0f

def z976 : W := mkw 0x1c0b0001504a4a60 0x438160002a09494c 0xf77ce08f71ce4fe2 0xdeef9c11ee39c9fc

def z977 : W := mkw 0x40300c2c03802505 0x08060185807004a0 0x5e1d5c3c01807f86 0x6bc3ab8780300ff0

def z978 : W := mkw 0x4010082c00002505 0x08020105800004a0 0x1e1c1c3c00007f86 0x03c3838780000ff0

def z979 : W := mkw 0xa12016c003a50000 0x142402d80074a000 0xc1eabfc003ff8001 0xf83d57f8007ff000

def z980 : W := mkw 0xa13016c003a52501 0x142602d80074a4a0 0xc1ffffc003fff601 0xf83ffff8007ffec0

def z981 : W := mkw 0x0a028000440888a8 0x0140500008811115 0xfbb54044ce89f9ff 0xff76a80899d13f3f

def z982 : W := mkw 0xa12016c003a50000 0x142402d80074a000 0xe7ffffc303ff8001 0xfcfffff8607ff000

def z983 : W := mkw 0xc1c01bfea8000006 0x1838037fd5000000 0x3ef3df7ffc000000 0x07de7befff800000

def z984 : W := mkw 0x40300c2c03802505 0x08060185807004a0 0xde5fdcbf33807f86 0x7bcbfb97e6700ff0

def z985 : W := mkw 0xc1c01bfea8000006 0x1838037fd5000000 0x7fffdffffc898987 0xeffffbffff913130

def z986 : W := mkw 0xc1c01bfea8000006 0x1838037fd5000000 0x3bfd5fcffc000000 0x077fabf9ff800000

def z987 : W := mkw 0xa12016c003a50000 0x142402d80074a000 0xc7ffffc003ffc003 0xf8fffff8007ff800

def z988 : W := mkw 0x1c0b0001504a4a60 0x438160002a09494c 0xff6ce0bb714e7e66 0xdfed9c176e29cfcc

def z989 : W := mkw 0x1c0b0001504a4a60 0x438160002a09494c 0xf76ee0bb734e7e62 0xdeeddc176e69cfcc

def z990 : W := mkw 0x0a028000440888a8 0x0140500008811115 0x3bb40044cc8989ff 0xc77680089991313f

def z991 : W := mkw 0x108c011380505050 0x82118022700a0a0a 0xefe3e3b3827e707f 0xbdfc7c76704fce0f

def z992 : W := mkw 0x108c011380505050 0x82118022700a0a0a 0xfee3c33bf270707f 0xbfdc78677e4e0e0f

def z993 : W := mkw 0x0a028000440888a8 0x0140500008811115 0x28910044cc8181fd 0x251220089990303f

def z994 : W := mkw 0xc1c01bfea8000006 0x1838037fd5000000 0x25ffdffbfc000000 0x04bffbff7f800000

def z995 : W := mkw 0x40300c2c03802505 0x08060185807004a0 0x1e1f1c3c03807f86 0x63c3e38780700ff0

def z996 : W := mkw 0xc1c01bfea8000006 0x1838037fd5000000 0x21e21ff3fc000000 0x043c43fe7f800000

def z997 : W := mkw 0x0a028000440888a8 0x0140500008811115 0x7bbd404ccd898fff 0xef77a80999b131ff

def z998 : W := mkw 0x60300c2c03a52505 0x0c0601858074a4a0 0xdfbffc7c03ffff87 0xfbf7ff8f807ffff0

def z999 : W := mkw 0xa12016c003a50000 0x142402d80074a000 0xd1ffffc803ff8e01 0xfa3ffff9007ff1c0

def z1000 : W := mkw 0x1e0b8001544acae8 0x43c170002a89595d 0xf76ce08b71cfcfe2 0xdeed9c116e39f9fc

def z1001 : W := mkw 0x1c0b0001504a4a60 0x438160002a09494c 0xf76ee38b737e4e62 0xdeeddc716e6fc9cc

def z1002 : W := mkw 0x40c0093ea8000006 0x08180127d5000000 0x3e0a9c3ffc000000 0x07c15387ff800000

def z1003 : W := mkw 0xc1d01bfea8002507 0x183a037fd50004a0 0xffffdffffd007f86 0x5ffffbffffa00ff0

def z1004 : W := mkw 0xc1c01bfea8000006 0x1838037fd5000000 0x377edfff7c000000 0x06efdbffef800000

def z1005 : W := mkw 0x1409000110424240 0x4281200022084848 0xf76ce08b714e4600 0xdeed9c116e29c8c0

def z1006 : W := mkw 0x108c011380505050 0x82118022700a0a0a 0xeee3e333837e707f 0xfddc7c66706fce0f

def z1007 : W := mkw 0x108c011380505050 0x82118022700a0a0a 0xe662c3330270707f 0xbccc5866604e0e0f

def z1008 : W := mkw 0x0a028000440888a8 0x0140500008811115 0x3a100044cc8189fe 0x074200089990313f

def z1009 : W := mkw 0x0084011280101010 0x8010802250020202 0x28a303308230307d 0xa51460661046060f

def z1010 : W := mkw 0x108c011380505050 0x82118022700a0a0a 0xace383338270707d 0xb59c7066704e0e0f

def z1011 : W := mkw 0x1c0f0001505a5a70 0xc381e0002a0b4b4e 0xf7efe38b737e7e7f 0xfefdfc716e6fcfcf

def z1012 : W := mkw 0xc1c01bfea8000006 0x1838037fd5000000 0xfffffffffdcf8001 0xffffffffffb9f000

def z1013 : W := mkw 0xc1c01bfea8000006 0x1838037fd5000000 0x144a9fbf7c000000 0x028953f7ef800000

def z1014 : W := mkw 0xa12016c003a50000 0x142402d80074a000 0xc17effc003ff8000 0xd82fdff8007ff000

def z1015 : W := mkw 0x108c011380505050 0x82118022700a0a0a 0xeef3c37382f1f07f 0xbdde786e705e3e0f

def z1016 : W := mkw 0x0a028000440888a8 0x0140500008811115 0x7a954044cc8189ff 0x6f52a8089990313f

def z1017 : W := mkw 0xe1c01bfea8250006 0x1c38037fd504a000 0x7ffffffffcff8001 0xefffffffff9ff000

def z1018 : W := mkw 0x1c0b0001504a4a60 0x438160002a09494c 0xf70c208b714e4e62 0xdee184116e29c9cc

def z1019 : W := mkw 0xa1e017d2aba50002 0x143c02fa5574a000 0xe1e023c3ffff8001 0xfc3c04787ffff000

def z1020 : W := mkw 0xc1c01bfea8000006 0x1838037fd5000000 0xffffdffffc004002 0x1ffffbffff800800

def z1021 : W := mkw 0x0a028000440888a8 0x0140500008811115 0xfbbdc044cd8989ff 0xff77b80899b1313f

def z1022 : W := mkw 0x1c0b0001504a4a60 0x438160002a09494c 0xf77ce0cb71cfce62 0xdeef9c196e39f9cc

def z1023 : W := mkw 0x1c0b0001504a4a60 0x438160002a09494c 0xfffde0cffdcfce63 0xffffbc19ffb9f9cc

def z1024 : W := mkw 0xa12016c003a50000 0x142402d80074a000 0x81ffffc003ff8000 0x503ffff8007ff000

def z1025 : W := mkw 0x1c0b0001504a4a60 0x438160002a09494c 0x8448a08b314e4e00 0x508914116629c9c0

def z1026 : W := mkw 0xa12016c003a50000 0x142402d80074a000 0xc19f3fc003ff8001 0xf833e7f8007ff000

def z1027 : W := mkw 0x40300c2c03802505 0x08060185807004a0 0x940a9c3c03007f80 0x1281538780600ff0

def z1028 : W := mkw 0xc1401aec28000006 0x1828035d85000000 0x3ffddccffc000000 0x07ffbb99ff800000

def z1029 : W := mkw 0x40300c2c03802505 0x08060185807004a0 0x08131c3402807f86 0x2102638680500ff0

def z1030 : W := mkw 0xa12016c003a50000 0x142402d80074a000 0xc1ebffc0037f8001 0xb83d7ff8006ff000

def z1031 : W := mkw 0x108c011380505050 0x82118022700a0a0a 0xfff7c37782f9f9ff 0xfffef86ef05f3f3f

def z1032 : W := mkw 0xa12016c003a50000 0x142402d80074a000 0xc9fffff003ffb005 0xf93ffffe007ff600

def z1033 : W := mkw 0x1e0b8001544acae8 0x43c170002a89595d 0xf7fde0cbfdcfce7b 0xfeffbc197fb9f9cf

def z1034 : W := mkw 0x1e0b8001544acae8 0x43c170002a89595d 0xff7de08f71cfcfff 0xffefbc11ee39f9ff

def z1035 : W := mkw 0xc1c01bfea8000006 0x1838037fd5000000 0x15ffdfff7c000000 0x02bffbffef800000

def z1036 : W := mkw 0x0a028000440888a8 0x0140500008811115 0x7a910044cc8989ff 0xef5220089991313f

def z1037 : W := mkw 0x108c011380505050 0x82118022700a0a0a 0xffffc3fffe70707f 0xbffff87fffce0e0f

def z1038 : W := mkw 0xa12016c003a50000 0x142402d80074a000 0xc05fff8003ff8001 0xf80bfff0007ff000

def z1039 : W := mkw 0x81c013d2a8000002 0x1038027a55000000 0x37ffdfcbfc000000 0x06fffbf97f800000

def z1040 : W := mkw 0x1409000110424240 0x4281200022084848 0x856ce08b31464600 0x10ad9c116628c8c0

def z1041 : W := mkw 0x40300c2c03802505 0x08060185807004a0 0xffbfdc7ccf89ff87 0xfff7fb8f99f13ff0

def z1042 : W := mkw 0x108c011380505050 0x82118022700a0a0a 0x2ee3c3338230707f 0x25dc786670460e0f

def z1043 : W := mkw 0x1409000110424240 0x4281200022084848 0xeee9e08bb146467f 0xbddd3c117628c8cf

def z1044 : W := mkw 0xa10012c000250000 0x142002580004a000 0xc1ffffc0017f8001 0xd83ffff8002ff000

def z1045 : W := mkw 0x1e0b8001544acae8 0x43c170002a89595d 0xf7ece0cbfdcfcfff 0xfefd9c197fb9f9ff

def z1046 : W := mkw 0xc1c01bfea8000006 0x1838037fd5000000 0xffffdffffef98001 0xfffffbffffdf3000

def z1047 : W := mkw 0x1c0b0001504a4a60 0x438160002a09494c 0xf64ce08b71464e62 0x5ec99c116e28c9cc

def z1048 : W := mkw 0x108c011380505050 0x82118022700a0a0a 0xc8e3c3308270707f 0xb91c7866104e0e0f

def z1049 : W := mkw 0x40300c2c03802505 0x08060185807004a0 0x1e021c3c02007f86 0x03c0438780400ff0

def z1050 : W := mkw 0x0e038000540a8aa8 0x41c070000a815155 0xffbde0ccfd8fcfff 0xfff7bc199fb1f9ff

def z1051 : W := mkw 0xc1c01bfea8000006 0x1838037fd5000000 0x244a9fbbfc000000 0x048953f77f800000

def z1052 : W := mkw 0xc1c01bfea8000006 0x1838037fd5000000 0x2dfb9ffffc000000 0x05bf73ffff800000

def z1053 : W := mkw 0x4010082c00002505 0x08020105800004a0 0xde1fdc3c01007f86 0x5bc3fb8780200ff0

def z1054 : W := mkw 0x108c011380505050 0x82118022700a0a0a 0xeee003338270707f 0xbddc0066704e0e0f

def z1055 : W := mkw 0xa12016c003a50000 0x142402d80074a000 0xc15fffc003ff8000 0x782bfff8007ff000

def z1056 : W := mkw 0x1c0f0001505a5a70 0xc381e0002a0b4b4e 0xffede08bf37e7e7f 0xfffdbc117e6fcfcf

def z1057 : W := mkw 0xc1c01bfea8000006 0x1838037fd5000000 0x054a9ffb7c000000 0x00a953ff6f800000

def z1058 : W := mkw 0xa12016c003a50000 0x142402d80074a000 0xdfffffcc03ffcf87 0xfbfffff9807ff9f0

def z1059 : W := mkw 0x1409000110424240 0x4281200022084848 0xa668e08b31464600 0x14cd1c116628c8c0

def z1060 : W := mkw 0xa12016c003a50000 0x142402d80074a000 0xfbffffc483ff89ff 0xff7ffff8907ff13f

def z1061 : W := mkw 0x40300c2c03802505 0x08060185807004a0 0xff7ffcbf73ce7f86 0xffefff97ee79cff0

def z1062 : W := mkw 0xc1c01bfea8000006 0x1838037fd5000000 0x3f7cdcfffc000000 0x07ef9b9fff800000

def z1063 : W := mkw 0xa12016c003a50000 0x142402d80074a000 0xc9ffffc083ff801d 0xf93ffff8107ff003

def z1064 : W := mkw 0x40300c2c03802505 0x08060185807004a0 0x1e1fdc3c01807f86 0x43c3fb8780300ff0

def z1065 : W := mkw 0x1c0b0001504a4a60 0x438160002a09494c 0xd74ce08b714e4e02 0x5ae99c116e29c9c0

def z1066 : W := mkw 0x0a028000440888a8 0x0140500008811115 0x49b540448c8989ff 0xe936a8089191313f

def z1067 : W := mkw 0x100c000100505050 0x82018000200a0a0a 0xcee3c3300270707f 0xb9dc7866004e0e0f

def z1068 : W := mkw 0x60300c2c03a52505 0x0c0601858074a4a0 0xde1fdc3c03b1ff87 0x7bc3fb8780763ff0

def z1069 : W := mkw 0x40300c2c03802505 0x08060185807004a0 0xfe3fdc3c03807fe6 0xffc7fb8780700ffc

def z1070 : W := mkw 0xab2296c047ad88a8 0x156452d808f5b115 0xba4abf84cf7609fe 0x174957f099eec13f

def z1071 : W := mkw 0x40300c2c03802505 0x08060185807004a0 0x5e175c3c02807f86 0x6bc2eb8780500ff0

def z1072 : W := mkw 0x1c0b0001504a4a60 0x438160002a09494c 0xf70ce08b710e4e62 0x5ee19c116e21c9cc

def z1073 : W := mkw 0xc1c01bfea8000006 0x1838037fd5000000 0x3fffdffffc00007e 0x07fffbffff80000f

def z1074 : W := mkw 0x108c011380505050 0x82118022700a0a0a 0xc4e3c3330270707f 0xb89c7866604e0e0f

def z1075 : W := mkw 0x60300c2c03a52505 0x0c0601858074a4a0 0xde1ffc3c03f67f86 0x7bc3ff87807ecff0

def z1076 : W := mkw 0x1c0b0001504a4a60 0x438160002a09494c 0x8548a08b714e4600 0x10a914116e29c8c0

def z1077 : W := mkw 0x1409000110424240 0x4281200022084848 0xc5fde0cb31cfc601 0xf8bfbc196639f8c0

def z1078 : W := mkw 0x108c011380505050 0x82118022700a0a0a 0xee43c3338270707e 0x3dc87866704e0e0f

def z1079 : W := mkw 0x1c0b0001504a4a60 0x438160002a09494c 0xc56ce08b314e4e62 0xd8ad9c116629c9cc

def z1080 : W := mkw 0x1409000110424240 0x4281200022084848 0x854ca08b314e4600 0x50a994116629c8c0

def z1081 : W := mkw 0x1e0b8001544acae8 0x43c170002a89595d 0xf76ce08f7d4e4fe2 0xdeed9c11efa9c9fc

def z1082 : W := mkw 0x1c0b0001504a4a60 0x438160002a09494c 0xf7ffe3cb73ffce63 0xfefffc796e7ff9cc

def z1083 : W := mkw 0x148d011390525250 0xc291a022720a4a4a 0xefefe3bbb37e767f 0xfdfdfc77766fcecf

def z1084 : W := mkw 0x108c011380505050 0x82118022700a0a0a 0xee83c3338230707f 0x3dd0786670460e0f

def z1085 : W := mkw 0x1e0b8001544acae8 0x43c170002a89595d 0xfffde0cffdcfcfe2 0xdfffbc19ffb9f9fc

def z1086 : W := mkw 0xa13016c003a52501 0x142602d80074a4a0 0xc1ffffc003ffb185 0xf83ffff8007ff630

def z1087 : W := mkw 0x108c011380505050 0x82118022700a0a0a 0x844283330270707e 0x10885066604e0e0f

def z1088 : W := mkw 0x0a028000440888a8 0x0140500008811115 0x7fbdc04ccc8989ff 0xeff7b8099991313f

def z1089 : W := mkw 0x2020040003a50000 0x040400800074a000 0xc0ffff0003ff8001 0xf81fffe0007ff000

def z1090 : W := mkw 0xc1c01bfea8000006 0x1838037fd5000000 0x311c1ccffc000000 0x06238399ff800000

def z1091 : W := mkw 0xc1c01bfea8000006 0x1838037fd5000000 0x3f6edfbffc000000 0x07eddbf7ff800000

def z1092 : W := mkw 0xc1c01bfea8000006 0x1838037fd5000000 0xffffdffffc400000 0x9ffffbffff880000

def z1093 : W := mkw 0x0a028000440888a8 0x0140500008811115 0x7ba00044cc8989ff 0xef7400089991313f

def z1094 : W := mkw 0x1c0b0001504a4a60 0x438160002a09494c 0xe668e08b314e4e62 0xdccd1c116629c9cc

def z1095 : W := mkw 0x40300c2c03802505 0x08060185807004a0 0xda175c3403807f86 0x7b42eb8680700ff0

def z1096 : W := mkw 0x108c011380505050 0x82118022700a0a0a 0xe8e303338270707f 0xbd1c6066704e0e0f

def z1097 : W := mkw 0x108c011380505050 0x82118022700a0a0a 0x2ee3c3338270307d 0xa5dc7866704e060f

def z1098 : W := mkw 0x0a028000440888a8 0x0140500008811115 0xfbb56044cdcf89ff 0xff76ac0899b9f13f

def z1099 : W := mkw 0x1409000110424240 0x4281200022084848 0xf76ce08b71464e02 0x5eed9c116e28c9c0

def z1100 : W := mkw 0x0a028000440888a8 0x0140500008811115 0x7bb74344ceb989ff 0xef76e86899d7313f

def z1101 : W := mkw 0x0a028000440888a8 0x0140500008811115 0xfbb7c044ce8989ff 0xff76f80899d1313f

def z1102 : W := mkw 0x40300c2c03802505 0x08060185807004a0 0xd41e9c3c03807f86 0x7a83d38780700ff0

def z1103 : W := mkw 0x108c011380505050 0x82118022700a0a0a 0x8442833302707079 0x90885066604e0e0f

def z1104 : W := mkw 0x1c0b0001504a4a60 0x438160002a09494c 0xf77ce0cf7d4e4e62 0xdeef9c19efa9c9cc

def z1105 : W := mkw 0x0200800004008088 0x0040100000801011 0x7bb54044cc8181ff 0xaf76a8089990303f

def z1106 : W := mkw 0xc1c01bfea8000006 0x1838037fd5000000 0x3fb75f7ffc000000 0x07f6ebefff800000

def z1107 : W := mkw 0xc1401aec28000006 0x1828035d85000000 0x3f7fdcff7c000000 0x07effb9fef800000

def z1108 : W := mkw 0x0a028000440888a8 0x0140500008811115 0x6bb14044cc8981ff 0xad7628089991303f

def z1109 : W := mkw 0x108c011380505050 0x82118022700a0a0a 0xffefe3bb837e7e7f 0xfffdfc77706fcfcf

def z1110 : W := mkw 0x40300c2c03802505 0x08060185807004a0 0xc0021c3003807f86 0x7800438600700ff0

def z1111 : W := mkw 0x1e0b8001544acae8 0x43c170002a89595d 0xff7de08ffdce4ffe 0xffefbc11ffb9c9ff

def z1112 : W := mkw 0x1c0b0001504a4a60 0x438160002a09494c 0xf7fde0cb714e4e62 0xdeffbc196e29c9cc

def z1113 : W := mkw 0x40300c2c03802505 0x08060185807004a0 0xde0bdc3c03007f86 0x3bc17b8780600ff0

def z1114 : W := mkw 0xc1c01bfea8000006 0x1838037fd5000000 0xffffdffffd000000 0x5ffffbffffa00000

def z1115 : W := mkw 0x1409000110424240 0x4281200022084848 0xa568a08b71464600 0x14ad14116e28c8c0

def z1116 : W := mkw 0x40300c2c03802505 0x08060185807004a0 0xdebfdc3c03807f87 0xfbd7fb8780700ff0

def z1117 : W := mkw 0x0a028000440888a8 0x0140500008811115 0x7bbd40ccfc8989ff 0xef77a8199f91313f

def z1118 : W := mkw 0xc1c01bfea8000006 0x1838037fd5000000 0x2ff3dff7fc000000 0x05fe7bfeff800000

def z1119 : W := mkw 0x40300c2c03802505 0x08060185807004a0 0xd41fdc3c03807f80 0x7a83fb8780700ff0

def z1120 : W := mkw 0x1c0b0001504a4a60 0x438160002a09494c 0xf76ce08b737e4e63 0xfeed9c116e6fc9cc

def z1121 : W := mkw 0x81c013d2a8000002 0x1038027a55000000 0x3bffdfc7fc000000 0x077ffbf8ff800000

def z1122 : W := mkw 0x0a028000440888a8 0x0140500008811115 0x3bb54044cc8189ff 0x2776a8089990313f

def z1123 : W := mkw 0x108c011380505050 0x82118022700a0a0a 0xeef7c33382f0707f 0xfddef866705e0e0f

def z1124 : W := mkw 0xc1d01bfea8002507 0x183a037fd50004a0 0x3fffdffffc007600 0x07fffbffff800ec0

def z1125 : W := mkw 0xc1c01bfea8000006 0x1838037fd5000000 0xbfffdffffd004600 0x17fffbffffa008c0

def z1126 : W := mkw 0x0a028000440888a8 0x0140500008811115 0x7bf54344ccf989ff 0xef7ea868999f313f

def z1127 : W := mkw 0x4010082c00002505 0x08020105800004a0 0xde1fdc3c02007f86 0x3bc3fb8780400ff0

def z1128 : W := mkw 0x40300c2c03802505 0x08060185807004a0 0x9e1b9c3c03807f86 0x33c3738780700ff0

def z1129 : W := mkw 0x0a028000440888a8 0x0140500008811115 0xfbf5c044ccc989ff 0xff7eb8089999313f

def z1130 : W := mkw 0x0e038000540a8aa8 0x41c070000a815155 0x7bb560c4fc8f89ff 0xef76ac189f91f13f

def z1131 : W := mkw 0x1e0b8001544acae8 0x43c170002a89595d 0xf76ce0cb7d4fce62 0xdeed9c196fa9f9cc

def z1132 : W := mkw 0x40300c2c03802505 0x08060185807004a0 0xcc1b9c3c03807f86 0x7983738780700ff0

def z1133 : W := mkw 0xa12016c003a50000 0x142402d80074a000 0xdffffff803fffe07 0xfbffffff007fffc0

def z1134 : W := mkw 0xc1c01bfea8000006 0x1838037fd5000000 0x3fffdffffc800980 0x47fffbffff900130

def z1135 : W := mkw 0x40300c2c03802505 0x08060185807004a0 0xffffdcffff807f86 0x7ffffb9ffff00ff0

def z1136 : W := mkw 0xc1d01bfea8002507 0x183a037fd50004a0 0x3fffdffffc000f80 0x07fffbffff8001f0

def z1137 : W := mkw 0x1c0b0001504a4a60 0x438160002a09494c 0xb76ce08b714e4e00 0x56ed9c116e29c9c0

def z1138 : W := mkw 0x0a028000440888a8 0x0140500008811115 0x7b154044cc8989fe 0x6f62a8089991313f

def z1139 : W := mkw 0x108c011380505050 0x82118022700a0a0a 0xeee3c33382f9f07f 0xfddc7866705f3e0f

def z1140 : W := mkw 0x40300c2c03802505 0x08060185807004a0 0x1e1fdc3c02807f86 0x23c3fb8780500ff0

def z1141 : W := mkw 0x1c0b0001504a4a60 0x438160002a09494c 0x3608208b71064e62 0x06c104116e20c9cc

def z1142 : W := mkw 0x0084011280101010 0x8010802250020202 0x2a8303308230307f 0x255060661046060f

def z1143 : W := mkw 0x0a028000440888a8 0x0140500008811115 0x59950044cc8989ff 0xeb32a0089991313f

def z1144 : W := mkw 0x1c0b0001504a4a60 0x438160002a09494c 0xa448a08b71464660 0x148914116e28c8cc

def z1145 : W := mkw 0xa12016c003a50000 0x142402d80074a000 0x81febfc003ff8001 0xd03fd7f8007ff000

def z1146 : W := mkw 0x0a028000440888a8 0x0140500008811115 0x3bb10044cc8989ff 0xa77620089991313f

def z1147 : W := mkw 0x0a028000440888a8 0x0140500008811115 0x3bb54044cc8981fd 0xa776a8089991303f

def z1148 : W := mkw 0x0a028000440888a8 0x0140500008811115 0x7bbfdc44cc8989ff 0xef77fb889991313f

def z1149 : W := mkw 0x0a028000440888a8 0x0140500008811115 0x7bfdc0c4cc8989ff 0xef7fb8189991313f

def z1150 : W := mkw 0x1c0b0001504a4a60 0x438160002a09494c 0xe768e08b714e4662 0x9ced1c116e29c8cc

def z1151 : W := mkw 0xa12016c003a50000 0x142402d80074a000 0xd1ffffc44fff8001 0xfa3ffff889fff000

def z1152 : W := mkw 0xc1c01bfea8000006 0x1838037fd5000000 0xffffdffffe70007f 0xbffffbffffce000f

def z1153 : W := mkw 0x40300c2c03802505 0x08060185807004a0 0xde1fdc3c03807fff 0xfbc3fb8780700fff

def z1154 : W := mkw 0xc1c01bfea8000006 0x1838037fd5000000 0x3fffdffffc800184 0x27fffbffff900030

def z1155 : W := mkw 0x1e0b8001544acae8 0x43c170002a89595d 0xffffe0ffffcfffff 0xfffffc1ffff9ffff

def z1156 : W := mkw 0x1c0b0001504a4a60 0x438160002a09494c 0xff6de08b714e4e66 0xffedbc116e29c9cc

def z1157 : W := mkw 0x1c0b0001504a4a60 0x438160002a09494c 0xff7fe0bf73ce7fe6 0xffeffc17ee79cffc

def z1158 : W := mkw 0xc1c01bfea8000006 0x1838037fd5000000 0xffffdffffe807986 0x7ffffbffffd00f30

def z1159 : W := mkw 0x1e0b8001544acae8 0x43c170002a89595d 0xc448a08b31cfcfff 0xf88914116639f9ff

def z1160 : W := mkw 0xc1d01bfea8002507 0x183a037fd50004a0 0xffffdffffe007f86 0x3ffffbffffc00ff0

def z1161 : W := mkw 0xa10012c000250000 0x142002580004a000 0x01f33fc0007f8001 0x803e67f8000ff000

def z1162 : W := mkw 0x1c0b0001504a4a60 0x438160002a09494c 0xf76fe08b734e4e62 0xfeedfc116e69c9cc

def z1163 : W := mkw 0x1409000110424240 0x4281200022084848 0xe76ce08b314e4662 0xdced9c116629c8cc

def z1164 : W := mkw 0x1409000110424240 0x4281200022084848 0xce4be0bb33467606 0x39c97c176668cec0

def z1165 : W := mkw 0x1c0b0001504a4a60 0x438160002a09494c 0xff6ce08bf14e4e7e 0xdfed9c117e29c9cf

def z1166 : W := mkw 0xc1c01bfea8000006 0x1838037fd5000000 0x3e021f3ffc000000 0x07c043e7ff800000

def z1167 : W := mkw 0xc1c01bfea8000006 0x1838037fd5000000 0x3ffffffffc4e0000 0x87ffffffff89c000

def z1168 : W := mkw 0xc1c01bfea8000006 0x1838037fd5000000 0x3eebdfbffc000000 0x07dd7bf7ff800000

def z1169 : W := mkw 0x40300c2c03802505 0x08060185807004a0 0xde9fdf3c03b07f87 0x7bd3fbe780760ff0

def z1170 : W := mkw 0xa12016c003a50000 0x142402d80074a000 0x804abf8003ff8000 0x500957f0007ff000

def z1171 : W := mkw 0x1c0b0001504a4a60 0x438160002a09494c 0xe568a08b714e4e62 0xdcad14116e29c9cc

def z1172 : W := mkw 0x108c011380505050 0x82118022700a0a0a 0xefe3c3b3f270707f 0xbdfc78767e4e0e0f

def z1173 : W := mkw 0xa12016c003a50000 0x142402d80074a000 0xc15ebfc003ff8001 0xf82bd7f8007ff000

def z1174 : W := mkw 0x1c0b0001504a4a60 0x438160002a09494c 0xb768a08b714e4e62 0x96ed14116e29c9cc

def z1175 : W := mkw 0xc1c01bfea8000006 0x1838037fd5000000 0x37fcdfcffc000000 0x06ff9bf9ff800000

def z1176 : W := mkw 0xa12016c003a50000 0x142402d80074a000 0xe3ffffc003ff8063 0xfc7ffff8007ff00c

def z1177 : W := mkw 0x40300c2c03802505 0x08060185807004a0 0xc81fdc3403807f86 0x7903fb8680700ff0

def z1178 : W := mkw 0x1e0b8001544acae8 0x43c170002a89595d 0xf7fde0cf7dcfcfe3 0xfeffbc19efb9f9fc

def z1179 : W := mkw 0x1409000110424240 0x4281200022084848 0xc44ce08b31464600 0x58899c116628c8c0

def z1180 : W := mkw 0xa12016c003a50000 0x142402d80074a000 0xc9ffffc48fff8001 0xf93ffff891fff000

def z1181 : W := mkw 0xa12016c003a50000 0x142402d80074a000 0xc09fff4003ff8001 0xf813ffe8007ff000

def z1182 : W := mkw 0xa12016c003a50000 0x142402d80074a000 0x81dfbfc003ff8001 0x703bf7f8007ff000

def z1183 : W := mkw 0x40300c2c03802505 0x08060185807004a0 0xdeffdf3c03807f86 0x7bdffbe780700ff0

def z1184 : W := mkw 0x81c013d2a8000002 0x1038027a55000000 0x21f31fc3fc000000 0x043e63f87f800000

def z1185 : W := mkw 0x1409000110424240 0x4281200022084848 0x964ce08b31464600 0x12c99c116628c8c0

def z1186 : W := mkw 0x108c011380505050 0x82118022700a0a0a 0xee62c3338270707e 0x9dcc5866704e0e0f

def z1187 : W := mkw 0xc1c01bfea8000006 0x1838037fd5000000 0x3fea9ffffc000000 0x07fd53ffff800000

def z1188 : W := mkw 0x0200800004008088 0x0040100000801011 0x489100448c8181ff 0xa91220089190303f

def z1189 : W := mkw 0xa12016c003a50000 0x142402d80074a000 0x01e83fc0017f8001 0x803d07f8002ff000

def z1190 : W := mkw 0x1c0b0001504a4a60 0x438160002a09494c 0x9448a08b71464e00 0x128914116e28c9c0

def z1191 : W := mkw 0x0a028000440888a8 0x0140500008811115 0x7fb54074cc89f9ff 0xeff6a80e99913f3f

def z1192 : W := mkw 0xa12016c003a50000 0x142402d80074a000 0x01ffffc001ff8001 0xc03ffff8003ff000

def z1193 : W := mkw 0xc1c01bfea8000006 0x1838037fd5000000 0x3fffdffffc004e02 0x07fffbffff8009c0

def z1194 : W := mkw 0xa13016c003a52501 0x142602d80074a4a0 0xd7ffffc803ffff87 0xfafffff9007ffff0

def z1195 : W := mkw 0x1e0f8001545adaf8 0xc3c1f0002a8b5b5f 0xf76ce08b73ffffff 0xfeed9c116e7fffff

def z1196 : W := mkw 0xa12016c003a50000 0x142402d80074a000 0xd7ffffc803ff8001 0xfafffff9007ff000

def z1197 : W := mkw 0x1409000110424240 0x4281200022084848 0x944ca08b31464e00 0x528994116628c9c0

def z1198 : W := mkw 0x40300c2c03802505 0x08060185807004a0 0xdf1fdc7c4f807f86 0x7be3fb8f89f00ff0

def z1199 : W := mkw 0xa13016c003a52501 0x142602d80074a4a0 0xdbffffc403ffff87 0xfb7ffff8807ffff0

def z1200 : W := mkw 0x0a028000440888a8 0x0140500008811115 0x7bbd60c4cd8f89ff 0xef77ac1899b1f13f

def z1201 : W := mkw 0xa12016c003a50000 0x142402d80074a000 0xe1ffffc373ff8001 0xfc3ffff86e7ff000

def z1202 : W := mkw 0x0000000000000000 0x0000000000000000 0xf76ce08b714e4e02 0xdeed9c116e29c9c0

def z1203 : W := mkw 0x40300c2c03802505 0x08060185807004a0 0xfe1fdc3ccf807f86 0x7fc3fb8799f00ff0

def z1204 : W := mkw 0xa12016c003a50000 0x142402d80074a000 0xe1ffffc0cfff8001 0xfc3ffff819fff000

def z1205 : W := mkw 0xa10012c000250000 0x142002580004a000 0x41ffffc000ff8001 0xe83ffff8001ff000

def z1206 : W := mkw 0x1c0b0001504a4a60 0x438160002a09494c 0xfffde08ff1ce4fff 0xffffbc11fe39c9ff

def z1207 : W := mkw 0xc1c01bfea8000006 0x1838037fd5000000 0x2febdffbfc000000 0x05fd7bff7f800000

def z1208 : W := mkw 0xa12016c003a50000 0x142402d80074a000 0xc9ffffc403ff8185 0xf93ffff8807ff030

def z1209 : W := mkw 0xa12016c003a50000 0x142402d80074a000 0x81ffffc0037f8001 0x903ffff8006ff000

def z1210 : W := mkw 0x1409000110424240 0x4281200022084848 0xd76ce08b314e4e02 0xdaed9c116629c9c0

def z1211 : W := mkw 0x0a028000440888a8 0x0140500008811115 0x7fb5404ffc8989ff 0xeff6a809ff91313f

def z1212 : W := mkw 0x1e0b8001544acae8 0x43c170002a89595d 0xa5e8a0cbfd4fc679 0x94bd14197fa9f8cf

def z1213 : W := mkw 0xc1c01bfea8000006 0x1838037fd5000000 0x21f01fc7fc000000 0x043e03f8ff800000

def z1214 : W := mkw 0x1e0b8001544acae8 0x43c170002a89595d 0x7bfd60cffdcf8fff 0xef7fac19ffb9f1ff

def z1215 : W := mkw 0xa13016c003a52501 0x142602d80074a4a0 0xc1ffffc003ff8f81 0xf83ffff8007ff1f0

def z1216 : W := mkw 0x108c011380505050 0x82118022700a0a0a 0xfee3c33b82707e7f 0xbfdc7867704e0fcf

def z1217 : W := mkw 0xe1f01ffeaba52507 0x1c3e03ffd574a4a0 0x08931f748eb1b185 0x211263ee91d63630

def z1218 : W := mkw 0xa12016c003a50000 0x142402d80074a000 0x015c3fc001ff8000 0x402b87f8003ff000

def z1219 : W := mkw 0x108c011380505050 0x82118022700a0a0a 0xeef3c33782f071ff 0xbdde7866f05e0e3f

def z1220 : W := mkw 0xc1c01bfea8000006 0x1838037fd5000000 0x37eedffbfc000000 0x06fddbff7f800000

def z1221 : W := mkw 0x1409000110424240 0x4281200022084848 0xc448a08b31464662 0x988914116628c8cc

def z1222 : W := mkw 0x1c0b0001504a4a60 0x438160002a09494c 0xffefe0bbf34e7e7f 0xfffdfc177e69cfcf

def z1223 : W := mkw 0x0401000010020200 0x4080200002004040 0x376ce08b71060600 0x06ed9c116e20c0c0

def z1224 : W := mkw 0xa10012c000250000 0x142002580004a000 0xc1ffffc0027f8001 0xb83ffff8004ff000

def z1225 : W := mkw 0xc1c01bfea8000006 0x1838037fd5000000 0x29ffdff7fc000000 0x053ffbfeff800000

def z1226 : W := mkw 0x40300c2c03802505 0x08060185807004a0 0x1e101c3c00807f86 0x03c2038780100ff0

def z1227 : W := mkw 0x1c0b0001504a4a60 0x438160002a09494c 0xf77ffc8b714e4e62 0xdeefff916e29c9cc

def z1228 : W := mkw 0xc1c01bfea8000006 0x1838037fd5000000 0x3f9f1ffffc000000 0x07f3e3ffff800000

def z1229 : W := mkw 0x108c011380505050 0x82118022700a0a0a 0xe6e2c3338270707b 0x9cdc5866704e0e0f

def z1230 : W := mkw 0xa12016c003a50000 0x142402d80074a000 0xf7ffffcb73ffce03 0xfefffff96e7ff9c0

def z1231 : W := mkw 0x0e038000540a8aa8 0x41c070000a815155 0xfbfde0ccfdcf8fff 0xff7fbc199fb9f1ff

def z1232 : W := mkw 0x40300c2c03802505 0x08060185807004a0 0xde131c3c03807f86 0x7bc2638780700ff0

def z1233 : W := mkw 0x1e0b8001544acae8 0x43c170002a89595d 0xff6ce08ffdcfcfff 0xffed9c11ffb9f9ff

def z1234 : W := mkw 0x1c0b0001504a4a60 0x438160002a09494c 0xf7ece0cb714fce63 0xdefd9c196e29f9cc

def z1235 : W := mkw 0x40300c2c03802505 0x08060185807004a0 0xde0a9c3c03807f86 0x7bc1538780700ff0

def z1236 : W := mkw 0x108c011380505050 0x82118022700a0a0a 0xfeefc33b8270707f 0xbfddf867704e0e0f

def z1237 : W := mkw 0x0a028000440888a8 0x0140500008811115 0xfffde0cccdcfcfff 0xffffbc1999b9f9ff

def z1238 : W := mkw 0x1c0b0001504a4a60 0x438160002a09494c 0xffefe38bf37e4e7f 0xfffdfc717e6fc9cf

def z1239 : W := mkw 0x0200800004008088 0x0040100000801011 0x6bb540448c8981ff 0xed76a8089191303f

def z1240 : W := mkw 0x1c0b0001504a4a60 0x438160002a09494c 0x376ce08b714e0e60 0xc6ed9c116e29c1cc

def z1241 : W := mkw 0x1e0b8001544acae8 0x43c170002a89595d 0xffede08bf1cfcfff 0xfffdbc117e39f9ff

def z1242 : W := mkw 0xa12016c003a50000 0x142402d80074a000 0xc16eff8003ff8001 0xf82ddff0007ff000

def z1243 : W := mkw 0x0e038000540a8aa8 0x41c070000a815155 0x3ffde0cffd8f8f80 0x47ffbc19ffb1f1f0

def z1244 : W := mkw 0x0a028000440888a8 0x0140500008811115 0x7bf560c4cccf89ff 0xef7eac189999f13f

def z1245 : W := mkw 0x1c0b0001504a4a60 0x438160002a09494c 0xd64ce08b314e4e62 0xdac99c116629c9cc

def z1246 : W := mkw 0x1e0b8001544acae8 0x43c170002a89595d 0xffede08ffd4e4fff 0xfffdbc11ffa9c9ff

def z1247 : W := mkw 0x108c011380505050 0x82118022700a0a0a 0xefe3c373ce70707f 0xbdfc786e79ce0e0f

def z1248 : W := mkw 0x108c011380505050 0x82118022700a0a0a 0xfff7c377cef9f07f 0xfffef86ef9df3e0f

def z1249 : W := mkw 0x40300c2c03802505 0x08060185807004a0 0xffbfdc7ccf807fff 0xfff7fb8f99f00fff

def z1250 : W := mkw 0x1c0b0001504a4a60 0x438160002a09494c 0x8448a08b314e4660 0x908914116629c8cc

def z1251 : W := mkw 0x1c0b0001504a4a60 0x438160002a09494c 0xf76ce08b714e4e7f 0xfeed9c116e29c9cf

def z1252 : W := mkw 0x1409000110424240 0x4281200022084848 0x954ca08b71464600 0x12a994116e28c8c0

def z1253 : W := mkw 0x108c011380505050 0x82118022700a0a0a 0x288303338230307d 0x251060667046060f

def z1254 : W := mkw 0x60300c2c03a52505 0x0c0601858074a4a0 0xdeffff3c03ffff87 0xfbdfffe7807ffff0

def z1255 : W := mkw 0x108c011380505050 0x82118022700a0a0a 0xfee3c337ce70707f 0xbfdc7866f9ce0e0f

def z1256 : W := mkw 0x1c0b0001504a4a60 0x438160002a09494c 0xfffde0cbf1cfce7f 0xffffbc197e39f9cf

def z1257 : W := mkw 0x40300c2c03802505 0x08060185807004a0 0xfe1fdc3f73807f86 0x7fc3fb87ee700ff0

def z1258 : W := mkw 0x0a028000440888a8 0x0140500008811115 0xfffdc0cffd89cfff 0xffffb819ffb139ff

def z1259 : W := mkw 0x0c030000500a0a20 0x418060000a014144 0x154ca08b710e0e00 0x42a994116e21c1c0

def z1260 : W := mkw 0x0a028000440888a8 0x0140500008811115 0x7bf540c7fc8989ff 0xef7ea818ff91313f

def z1261 : W := mkw 0xc1c01bfea8000006 0x1838037fd5000000 0x3ffc1ffffc000000 0x07ff83ffff800000

def z1262 : W := mkw 0x1c0b0001504a4a60 0x438160002a09494c 0xf668e08b71464e62 0x9ecd1c116e28c9cc

def z1263 : W := mkw 0x1409000110424240 0x4281200022084848 0xb648a08b71464600 0x16c914116e28c8c0

def z1264 : W := mkw 0xc1c01bfea8000006 0x1838037fd5000000 0x7fffdffffc000001 0xaffffbffff800000

def z1265 : W := mkw 0x108c011380505050 0x82118022700a0a0a 0xaee3c3338270707e 0x15dc7866704e0e0f

def z1266 : W := mkw 0xc1c01bfea8000006 0x1838037fd5000000 0x3ffffffffd0e0000 0x47ffffffffa1c000

def z1267 : W := mkw 0x0a028000440888a8 0x0140500008811115 0x089100448c8189ff 0x211220089190313f

def z1268 : W := mkw 0x40300c2c03802505 0x08060185807004a0 0x9e1fdc3c03007f86 0x13c3fb8780600ff0

def z1269 : W := mkw 0x1409000110424240 0x4281200022084848 0xf66ce08b31464e62 0xdecd9c116628c9cc

def z1270 : W := mkw 0x60300c2c03a52505 0x0c0601858074a4a0 0xde1ffc3c038fff86 0x7bc3ff878071fff0

def z1271 : W := mkw 0x148d011390525250 0xc291a022720a4a4a 0xeee3c33bb270767f 0xbddc7867764e0ecf

def z1272 : W := mkw 0x81c013d2a8000002 0x1038027a55000000 0x2fffdff3fc000000 0x05fffbfe7f800000

def z1273 : W := mkw 0x40700c2c2b802507 0x080e0185857004a0 0xde1fdc3c7f807f86 0x7bc3fb878ff00ff0

def z1274 : W := mkw 0xc1c01bfea8000006 0x1838037fd5000000 0xffffdffffe000000 0x3ffffbffffc00000

def z1275 : W := mkw 0x1e0b8001544acae8 0x43c170002a89595d 0x3f1c20cffd8fcffe 0x47e38419ffb1f9ff

def z1276 : W := mkw 0xc1401aec28000006 0x1828035d85000000 0x317c1ccf7c000000 0x062f8399ef800000

def z1277 : W := mkw 0xc1d01bfea8002507 0x183a037fd50004a0 0x3fffdffffc003184 0x07fffbffff800630

def z1278 : W := mkw 0xc1c01bfea8000006 0x1838037fd5000000 0x21e81fcbfc000000 0x043d03f97f800000

def z1279 : W := mkw 0x40300c2c03802505 0x08060185807004a0 0xdfffdf7c03f9ff87 0xfbfffbef807f3ff0

def z1280 : W := mkw 0x108c011380505050 0x82118022700a0a0a 0xffe7c333c270707f 0xbffcf866784e0e0f

def z1281 : W := mkw 0xa12016c003a50000 0x142402d80074a000 0xdbffffc403ff8001 0xfb7ffff8807ff000

def z1282 : W := mkw 0x1e0f8001545adaf8 0xc3c1f0002a8b5b5f 0xfffde0cfffffffff 0xffffbc19ffffffff

def z1283 : W := mkw 0x1409000110424240 0x4281200022084848 0xa468a08b31464660 0x948d14116628c8cc

def z1284 : W := mkw 0x0a028000440888a8 0x0140500008811115 0x089100448c8981fd 0xa11220089191303f

def z1285 : W := mkw 0xc1c01bfea8000006 0x1838037fd5000000 0x3fffdffffd000e00 0x47fffbffffa001c0

def z1286 : W := mkw 0xa12016c003a50000 0x142402d80074a000 0x00933f4002ff8001 0xa01267e8005ff000

def z1287 : W := mkw 0x1c0b0001504a4a60 0x438160002a09494c 0xd54ca08b714e4e62 0xdaa994116e29c9cc

def z1288 : W := mkw 0xe1c01bfea8250006 0x1c38037fd504a000 0x3ffffffffc760000 0x07ffffffff8ec000

def z1289 : W := mkw 0xc1c01bfea8000006 0x1838037fd5000000 0x3e101c7ffc000000 0x07c2038fff800000

def z1290 : W := mkw 0x40300c2c03802505 0x08060185807004a0 0xde9fdc7c8f807f86 0x7bd3fb8f91f00ff0

def z1291 : W := mkw 0x1c0b0001504a4a60 0x438160002a09494c 0xff7de08f714e4e62 0xdfefbc11ee29c9cc

def z1292 : W := mkw 0x40300c2c03802505 0x08060185807004a0 0xfe7fdc3f03807f86 0x7fcffb87e0700ff0

def z1293 : W := mkw 0x140d000110525250 0xc281a000220a4a4a 0x8448a08b33767600 0x10891411666ecec0

def z1294 : W := mkw 0x1c0b0001504a4a60 0x438160002a09494c 0x114c208b714e0e00 0x422984116e29c1c0

def z1295 : W := mkw 0xa12016c003a50000 0x142402d80074a000 0xc1ffffc003fff007 0xf83ffff8007ffe00

def z1296 : W := mkw 0xe1c01bfea8250006 0x1c38037fd504a000 0xfffffffffd7f8001 0xdfffffffffaff000

def z1297 : W := mkw 0x40300c2c03802505 0x08060185807004a0 0xdf1fdcbc73807f86 0x7be3fb978e700ff0

def z1298 : W := mkw 0x1c0b0001504a4a60 0x438160002a09494c 0xff6ce08f714e4fe6 0xdfed9c11ee29c9fc

def z1299 : W := mkw 0x1c0b0001504a4a60 0x438160002a09494c 0xf7ece0cbfd4e4e62 0xdefd9c197fa9c9cc

def z1300 : W := mkw 0x1409000110424240 0x4281200022084848 0x8568a08b314e4600 0x90ad14116629c8c0

def z1301 : W := mkw 0x40300c2c03802505 0x08060185807004a0 0xdf1fdc7c0389ff86 0x7be3fb8f80713ff0

def z1302 : W := mkw 0xa12016c003a50000 0x142402d80074a000 0xf3ffffc043ff8001 0xfe7ffff8087ff000

def z1303 : W := mkw 0xc1c01bfea8000006 0x1838037fd5000000 0xffffdfffff007e06 0x7ffffbffffe00fc0

def z1304 : W := mkw 0x0a028000440888a8 0x0140500008811115 0x71b54044cc8989f9 0xee36a8089991313f

def z1305 : W := mkw 0x1c0b0001504a4a60 0x438160002a09494c 0xf648a08b714e4e62 0xdec914116e29c9cc

def z1306 : W := mkw 0xc1401aec28000006 0x1828035d85000000 0x37ffdfcf7c000000 0x06fffbf9ef800000

def z1307 : W := mkw 0x0a028000440888a8 0x0140500008811115 0x7ff5c047cc8989ff 0xeffeb808f991313f

def z1308 : W := mkw 0x1e0b8001544acae8 0x43c170002a89595d 0xf76ce08b714e4ffe 0xdeed9c116e29c9ff

def z1309 : W := mkw 0x1c0b0001504a4a60 0x438160002a09494c 0x376c208b714e4e62 0xc6ed84116e29c9cc

def z1310 : W := mkw 0x0a028000440888a8 0x0140500008811115 0x5a9540448c8989ff 0xeb52a8089191313f

def z1311 : W := mkw 0x0c030000500a0a20 0x418060000a014144 0x370c208b710e0e00 0x46e184116e21c1c0

def z1312 : W := mkw 0xc1c01bfea8000006 0x1838037fd5000000 0xbfffdffffe700000 0x17fffbffffce0000

def z1313 : W := mkw 0xa12016c003a50000 0x142402d80074a000 0xc1fcffc001ff8001 0xd83f9ff8003ff000

def z1314 : W := mkw 0x1409000110424240 0x4281200022084848 0xf76ce08b71464662 0x9eed9c116e28c8cc

def z1315 : W := mkw 0x0a028000440888a8 0x0140500008811115 0x7fb7c074cc8989ff 0xeff6f80e9991313f

def z1316 : W := mkw 0x0a028000440888a8 0x0140500008811115 0x3b950044cc8989ff 0x6772a0089991313f

def z1317 : W := mkw 0x108c011380505050 0x82118022700a0a0a 0xccc383338270707f 0xb9987066704e0e0f

def z1318 : W := mkw 0xc1c01bfea8000006 0x1838037fd5000000 0x3ff31ffffc000000 0x07fe63ffff800000

def z1319 : W := mkw 0x140d000110525250 0xc281a000220a4a4a 0xc448a08b3376767f 0xb8891411666ececf

def z1320 : W := mkw 0xa12016c003a50000 0x142402d80074a000 0xc5fffff003fff001 0xf8bffffe007ffe00

def z1321 : W := mkw 0x0a028000440888a8 0x0140500008811115 0xffbfc07ccf89ffff 0xfff7f80f99f13fff

def z1322 : W := mkw 0xc1c41bfea8101016 0x9838837fd5020202 0x3fffdffffc300019 0x07fffbffff860003

def z1323 : W := mkw 0xa12016c003a50000 0x142402d80074a000 0xebffffc083ff8001 0xfd7ffff8107ff000

def z1324 : W := mkw 0xc1c01bfea8000006 0x1838037fd5000000 0x3fffdffffc007006 0x07fffbffff800e00

def z1325 : W := mkw 0x0a028000440888a8 0x0140500008811115 0x7b140044cc8989ff 0xef6280089991313f

def z1326 : W := mkw 0x108c011380505050 0x82118022700a0a0a 0x2ee303338270707f 0xa5dc6066704e0e0f

def z1327 : W := mkw 0x108c011380505050 0x82118022700a0a0a 0xaec383338270707f 0x35d87066704e0e0f

def z1328 : W := mkw 0xa12016c003a50000 0x142402d80074a000 0xc1f33fc003ff8001 0xf83e67f8007ff000

def z1329 : W := mkw 0xc1c01bfea8000006 0x1838037fd5000000 0x3fffdffffc000986 0x07fffbffff800130

def z1330 : W := mkw 0x108c011380505050 0x82118022700a0a0a 0xee4283338270707f 0xbdc85066704e0e0f

def z1331 : W := mkw 0x1c0b0001504a4a60 0x438160002a09494c 0xfffde0cffd4e4e7f 0xffffbc19ffa9c9cf

def z1332 : W := mkw 0xa12016c003a50000 0x142402d80074a000 0x804abf80037f8001 0x900957f0006ff000

def z1333 : W := mkw 0xa12016c003a50000 0x142402d80074a000 0x01ff3fc003ff8001 0xe03fe7f8007ff000

def z1334 : W := mkw 0xc1c41bfea8101016 0x9838837fd5020202 0x3fffdffffc00301c 0x07fffbffff800603

def z1335 : W := mkw 0xa13016c003a52501 0x142602d80074a4a0 0xcffffff003ffff87 0xf9fffffe007ffff0

def z1336 : W := mkw 0x1c0b0001504a4a60 0x438160002a09494c 0x8448a08b31464e62 0x108914116628c9cc

def z1337 : W := mkw 0xc1c01bfea8000006 0x1838037fd5000000 0xffffffffff7e0001 0xffffffffffefc000

def z1338 : W := mkw 0x1e0b8001544acae8 0x43c170002a89595d 0x7fbd60cffd8fcfff 0xeff7ac19ffb1f9ff

def z1339 : W := mkw 0xc1c01bfea8000006 0x1838037fd5000000 0x7fffdffffc89807f 0xeffffbffff91300f

def z1340 : W := mkw 0x40300c2c03802505 0x08060185807004a0 0xffbfdc7c8389ffff 0xfff7fb8f90713fff

def z1341 : W := mkw 0xc1d01bfea8002507 0x183a037fd50004a0 0x7fffdffffc807f86 0x6ffffbffff900ff0

def z1342 : W := mkw 0xc1c41bfea8101016 0x9838837fd5020202 0xffffdffffe30701f 0x3ffffbffffc60e03

def z1343 : W := mkw 0x1c0b0001504a4a60 0x438160002a09494c 0xff6fe0bb714e4e62 0xdfedfc176e29c9cc

def z1344 : W := mkw 0xc1c01bfea8000006 0x1838037fd5000000 0x1ddf9ffffc000000 0x03bbf3ffff800000

def z1345 : W := mkw 0xc1c01bfea8000006 0x1838037fd5000000 0x151c1cff7c000000 0x02a3839fef800000

def z1346 : W := mkw 0xa12016c003a50000 0x142402d80074a000 0x814abfc0037f8000 0x102957f8006ff000

def z1347 : W := mkw 0x0c030000500a0a20 0x418060000a014144 0x776ce08b710e0e62 0xceed9c116e21c1cc

def z1348 : W := mkw 0xa12016c003a50000 0x142402d80074a000 0xc1f3ffc002ff8001 0xb83e7ff8005ff000

def z1349 : W := mkw 0x40300c2c03802505 0x08060185807004a0 0xde5fdf3c03f07f86 0x7bcbfbe7807e0ff0

def z1350 : W := mkw 0x1e0b8001544acae8 0x43c170002a89595d 0xffede0cbfd4fce7f 0xfffdbc197fa9f9cf

def z1351 : W := mkw 0x108c011380505050 0x82118022700a0a0a 0xfef7c3378270707f 0xbfdef866f04e0e0f

def z1352 : W := mkw 0xa12016c003a50000 0x142402d80074a000 0x01ffffc002ff8001 0xa03ffff8005ff000

def z1353 : W := mkw 0x108c011380505050 0x82118022700a0a0a 0xaee3c33382707079 0x95dc7866704e0e0f

def z1354 : W := mkw 0x1c0f0001505a5a70 0xc381e0002a0b4b4e 0xf76ce08b717e4e7b 0xdeed9c116e2fc9cf

def z1355 : W := mkw 0x1c0b0001504a4a60 0x438160002a09494c 0x376ce08b710e4e62 0x46ed9c116e21c9cc

def z1356 : W := mkw 0x0a028000440888a8 0x0140500008811115 0x3bb54044cc8989f9 0xc776a8089991313f

def z1357 : W := mkw 0x40300c2c03802505 0x08060185807004a0 0xde1c1c3c03807f86 0x7bc3838780700ff0

def z1358 : W := mkw 0xa10012c000250000 0x142002580004a000 0x01fc3fc0007f8001 0x803f87f8000ff000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z0,z1,z2,z3,z4,z6,z7]),(0,[z8,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z9,z6]),(0,[z10,z0,z1,z2,z3,z4,z6])],[(0,[z0,z11,z1,z12,z3,z4,z6]),(0,[z0,z1,z2,z13,z3,z4,z6]),(0,[z0,z2,z14,z3,z4,z15,z6]),(0,[z0,z1,z2,z3,z4,z16,z6])],[(0,[z0,z1,z17,z2,z3,z4,z6]),(0,[z0,z18,z1,z2,z3,z4,z6]),(0,[z0,z19,z2,z3,z4,z15,z6]),(0,[z0,z20,z21,z2,z3,z4,z6]),(0,[z22,z0,z2,z3,z4,z6,z23]),(0,[z0,z24,z1,z25,z3,z4,z6]),(0,[z0,z1,z2,z3,z26,z4,z6]),(0,[z27,z0,z1,z2,z3,z4,z6])],[(1,[z1,z20,z12,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z28,z29]),(0,[z30,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z31]),(0,[z32,z0,z1,z2,z3,z33,z6])],[(0,[z34,z0,z1,z2,z3,z4,z6]),(0,[z22,z0,z1,z14,z3,z4,z6]),(0,[z30,z0,z1,z2,z3,z4,z35]),(0,[z0,z1,z2,z3,z4,z36,z6]),(0,[z37,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z38,z6])],[(0,[z0,z39,z1,z2,z3,z4,z6]),(0,[z40,z0,z1,z2,z3,z4,z41]),(0,[z0,z1,z2,z3,z4,z29,z42]),(0,[z43,z0,z1,z2,z3,z4,z6]),(0,[z44,z0,z1,z2,z3,z45,z6])],[(0,[z0,z1,z2,z3,z46,z6,z47]),(0,[z48,z1,z2,z3,z49,z4,z6]),(0,[z0,z1,z2,z3,z4,z50,z6])],[(0,[z0,z1,z2,z3,z51,z4,z6]),(0,[z0,z1,z2,z52,z4,z6,z42]),(0,[z0,z24,z1,z53,z3,z4,z6]),(0,[z0,z24,z1,z3,z4,z54,z6]),(0,[z44,z0,z1,z3,z55,z4,z6]),(0,[z56,z0,z1,z2,z3,z4,z6])]],
   [[(0,[z0,z1,z2,z57,z3,z4,z6]),(0,[z0,z1,z20,z3,z49,z4,z6]),(0,[z0,z58,z1,z20,z3,z4,z6]),(1,[z59,z1,z2,z52,z4,z6])],[(0,[z60,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z12,z61,z3,z4,z6]),(1,[z0,z1,z2,z3,z62,z6]),(0,[z63,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z64,z4,z6]),(0,[z0,z1,z2,z3,z65,z4,z54])],[(0,[z0,z1,z2,z3,z4,z66,z6]),(0,[z67,z0,z1,z2,z3,z4,z23])],[(0,[z0,z1,z20,z3,z4,z6,z42]),(0,[z68,z0,z1,z2,z52,z4,z6]),(0,[z0,z1,z69,z2,z3,z4,z6]),(1,[z0,z70,z2,z3,z4,z6]),(0,[z22,z0,z24,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z71,z6]),(0,[z0,z1,z2,z3,z4,z72,z6]),(0,[z67,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z25,z2,z3,z4,z6]),(1,[z73,z0,z1,z3,z74,z6])],[(0,[z0,z1,z2,z3,z4,z75,z6]),(0,[z0,z1,z2,z3,z76,z4,z6]),(0,[z0,z1,z2,z77,z3,z4,z6]),(0,[z0,z1,z53,z2,z55,z4,z6]),(1,[z0,z1,z53,z78,z4,z6])],[(0,[z0,z1,z2,z3,z4,z79,z6])],[(1,[z1,z12,z3,z4,z46,z6]),(0,[z48,z0,z1,z12,z3,z4,z6]),(0,[z1,z2,z12,z3,z80,z4,z6]),(0,[z0,z81,z1,z2,z3,z4,z6]),(0,[z82,z0,z1,z2,z3,z4,z6]),(0,[z83,z0,z1,z2,z3,z4,z84]),(0,[z85,z0,z1,z2,z3,z4,z6]),(0,[z86,z0,z1,z69,z3,z4,z6]),(0,[z87,z0,z1,z2,z88,z4,z6])],[(0,[z0,z1,z2,z3,z89,z4,z6]),(0,[z44,z0,z90,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z91,z4,z6]),(0,[z0,z1,z92,z3,z4,z54,z6])]],
   [[(0,[z93,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z12,z3,z4,z6]),(0,[z94,z0,z1,z12,z3,z4,z6]),(0,[z0,z1,z12,z3,z95,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z96]),(0,[z83,z0,z1,z2,z3,z97,z6]),(0,[z0,z1,z2,z3,z4,z98,z6]),(0,[z0,z1,z2,z3,z4,z29,z6]),(0,[z0,z1,z2,z99,z3,z4,z6])],[(1,[z0,z1,z2,z3,z4,z100]),(0,[z101,z0,z1,z2,z3,z4,z6])],[(0,[z0,z102,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z103]),(0,[z22,z0,z104,z2,z3,z4,z6]),(0,[z73,z0,z105,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z106]),(0,[z0,z1,z2,z3,z65,z6,z107])],[(0,[z108,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z109,z4,z23]),(0,[z0,z1,z2,z3,z110,z4,z6])],[(0,[z0,z1,z12,z3,z4,z28,z6]),(0,[z0,z1,z2,z3,z4,z15,z6]),(0,[z111,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z112,z3,z109,z4]),(1,[z0,z1,z2,z113,z4,z6])],[(0,[z0,z19,z1,z2,z3,z4,z6]),(0,[z0,z114,z1,z12,z3,z4,z6]),(0,[z115,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z116,z4,z6]),(0,[z0,z1,z2,z117,z4,z6,z42]),(0,[z0,z1,z2,z3,z118,z4,z6]),(0,[z0,z119,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z120,z3,z4,z6]),(0,[z0,z1,z2,z121,z3,z4,z6]),(0,[z0,z1,z2,z3,z122,z49,z6]),(0,[z123,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z124,z6])],[(0,[z125,z0,z1,z2,z3,z4,z6]),(0,[z48,z0,z1,z20,z3,z4,z6]),(0,[z126,z0,z1,z2,z3,z4,z6]),(0,[z0,z24,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z127,z6]),(0,[z128,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z129,z4,z6]),(1,[z32,z0,z1,z3,z4,z130]),(0,[z0,z1,z2,z3,z4,z6,z131])]],
   [[(0,[z0,z1,z2,z3,z132,z4,z6]),(0,[z1,z133,z2,z3,z80,z4,z6]),(0,[z0,z1,z25,z2,z3,z74,z6]),(0,[z0,z1,z2,z3,z134,z4,z6]),(0,[z0,z1,z2,z3,z135,z4,z6])],[(1,[z0,z1,z20,z3,z4,z6]),(1,[z0,z1,z2,z3,z136,z6]),(1,[z0,z1,z2,z137,z4,z6]),(0,[z73,z0,z138,z2,z3,z4,z6])],[(0,[z83,z0,z1,z2,z3,z4,z6]),(1,[z67,z0,z2,z3,z4,z23]),(0,[z139,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z140,z4]),(0,[z0,z1,z2,z117,z141,z4,z6])],[(0,[z142,z19,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z143,z4,z6]),(0,[z0,z1,z2,z3,z144,z6,z107]),(0,[z0,z145,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z146,z4,z6])],[(0,[z0,z1,z2,z3,z4,z147,z6]),(0,[z0,z1,z2,z3,z80,z4,z6]),(0,[z0,z1,z148,z2,z3,z4,z6]),(0,[z40,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z149]),(0,[z0,z150,z1,z2,z3,z4,z6]),(0,[z0,z1,z151,z2,z3,z4,z6]),(0,[z0,z114,z2,z152,z3,z4,z6]),(1,[z145,z1,z2,z3,z4,z6])],[(0,[z153,z0,z1,z12,z3,z4,z6]),(0,[z0,z1,z2,z3,z154,z4,z6]),(0,[z0,z1,z2,z155,z3,z4,z6]),(0,[z0,z1,z2,z3,z156,z4,z6])],[(0,[z0,z114,z1,z20,z3,z4,z6]),(0,[z0,z1,z92,z2,z3,z4,z23])],[(1,[z0,z1,z2,z3,z4,z75]),(0,[z0,z1,z12,z3,z65,z4,z6]),(0,[z142,z48,z1,z2,z3,z4,z6]),(0,[z24,z157,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z152,z4,z6,z107]),(0,[z0,z1,z92,z2,z3,z4,z6])]],
   [[(0,[z158,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z159,z4,z6]),(1,[z160,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z55,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z130]),(0,[z0,z1,z2,z3,z161,z4,z6])],[(1,[z157,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z42,z23]),(0,[z162,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z20,z3,z4,z74,z6]),(1,[z0,z1,z2,z163,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z164]),(0,[z73,z0,z1,z2,z3,z144,z6]),(0,[z0,z1,z2,z3,z4,z6,z165]),(0,[z0,z1,z2,z112,z3,z4,z47])],[(0,[z0,z1,z20,z133,z3,z4,z6]),(0,[z0,z1,z12,z3,z166,z4,z6]),(0,[z0,z1,z12,z3,z167,z4,z6]),(0,[z0,z1,z168,z2,z3,z4,z6]),(0,[z169,z0,z1,z2,z3,z4,z6]),(0,[z170,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z171,z4,z6]),(0,[z172,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z173,z6]),(0,[z0,z1,z2,z78,z3,z4,z6]),(1,[z0,z1,z2,z174,z4,z6]),(0,[z0,z1,z3,z144,z4,z74,z6]),(0,[z175,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z176,z4,z6]),(1,[z0,z1,z177,z3,z4,z6]),(0,[z0,z1,z178,z2,z3,z4,z6]),(0,[z123,z0,z1,z2,z3,z4,z179]),(0,[z0,z1,z2,z3,z180,z4,z6])],[(0,[z0,z1,z2,z181,z3,z4,z6]),(0,[z182,z0,z1,z2,z3,z4,z6]),(0,[z153,z0,z1,z20,z3,z4,z6]),(0,[z0,z1,z2,z183,z3,z4,z6]),(0,[z123,z184,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z95,z15,z6]),(0,[z0,z1,z2,z3,z4,z130,z47]),(0,[z185,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z1,z2,z3,z4,z6]),(0,[z186,z0,z1,z2,z181,z4,z6]),(0,[z0,z1,z2,z3,z4,z187,z6]),(0,[z0,z1,z12,z52,z3,z4,z6]),(0,[z188,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z20,z3,z95,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z189]),(0,[z0,z1,z2,z3,z49,z6,z107]),(0,[z190,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z191,z2,z3,z4,z6])]],
   [[(0,[z0,z1,z12,z3,z144,z4,z6]),(0,[z83,z0,z1,z192,z3,z4,z6])],[(0,[z19,z1,z2,z12,z3,z4,z6]),(0,[z193,z0,z1,z20,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z194]),(0,[z123,z195,z1,z2,z3,z4,z6]),(0,[z196,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z65,z4,z28]),(0,[z0,z1,z2,z197,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z198,z6]),(0,[z68,z0,z1,z2,z3,z38,z6])],[(0,[z199,z0,z1,z2,z3,z4,z6]),(0,[z59,z0,z1,z168,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z200]),(0,[z0,z201,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z202]),(0,[z68,z0,z1,z2,z3,z65,z4])],[(0,[z0,z1,z2,z3,z4,z203,z6]),(0,[z0,z1,z2,z204,z3,z4,z6]),(0,[z0,z1,z20,z3,z4,z28,z6]),(0,[z0,z1,z2,z3,z205,z4,z6]),(0,[z206,z0,z1,z2,z3,z4,z6]),(0,[z44,z0,z207,z2,z3,z4,z6])],[(0,[z186,z0,z1,z2,z3,z4,z6]),(1,[z1,z12,z3,z4,z6,z41]),(0,[z0,z1,z2,z3,z208,z4,z6]),(0,[z73,z0,z1,z2,z174,z4,z6]),(1,[z0,z1,z2,z3,z4,z165])],[(0,[z0,z133,z2,z3,z4,z6,z23]),(0,[z87,z0,z1,z12,z3,z4,z6]),(0,[z0,z1,z2,z80,z166,z4,z6]),(0,[z0,z1,z2,z3,z209,z4,z6]),(0,[z210,z0,z1,z2,z3,z4,z6]),(0,[z0,z104,z1,z2,z3,z4,z23]),(0,[z0,z1,z2,z141,z78,z4,z6]),(0,[z0,z211,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z212]),(0,[z0,z1,z2,z3,z4,z213,z6]),(0,[z0,z1,z2,z3,z4,z6,z214]),(0,[z0,z1,z2,z3,z4,z6,z215])],[(0,[z0,z1,z2,z216,z3,z4,z6]),(0,[z217,z0,z1,z2,z3,z4,z6])]],
   [[(0,[z86,z0,z1,z2,z218,z4,z6]),(0,[z0,z1,z2,z3,z219,z4,z6]),(0,[z0,z1,z2,z3,z109,z4,z29]),(0,[z220,z0,z1,z2,z3,z4,z6])],[(0,[z221,z0,z1,z12,z3,z4,z6]),(0,[z222,z0,z1,z2,z3,z4,z6]),(0,[z223,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z65,z95,z6]),(0,[z0,z1,z2,z117,z3,z65,z4]),(0,[z0,z1,z2,z3,z4,z6,z224])],[(0,[z0,z1,z225,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z226,z4,z6]),(0,[z0,z227,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z228,z4,z6])],[(0,[z0,z1,z2,z3,z95,z4,z165])],[(0,[z0,z1,z2,z3,z3,z4,z6]),(0,[z229,z0,z1,z2,z3,z4,z6]),(1,[z83,z1,z2,z80,z4,z6]),(1,[z210,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z230,z4,z6]),(0,[z0,z231,z1,z2,z3,z4,z6]),(0,[z0,z1,z12,z117,z3,z4,z6]),(0,[z0,z1,z2,z232,z3,z4,z6]),(0,[z30,z0,z1,z2,z171,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z233]),(0,[z0,z1,z2,z3,z234,z4,z6]),(0,[z235,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z236,z3,z4,z6]),(0,[z87,z0,z1,z20,z3,z4,z6]),(0,[z0,z1,z20,z3,z65,z4,z6]),(0,[z0,z1,z2,z52,z166,z4,z6]),(0,[z0,z1,z2,z3,z95,z122,z6])],[(0,[z0,z1,z20,z14,z3,z4,z6]),(0,[z0,z237,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z238,z4,z6]),(0,[z30,z0,z1,z239,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z240])]],
   [[(0,[z0,z1,z2,z12,z3,z4,z6]),(0,[z83,z0,z237,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z241,z6]),(0,[z0,z242,z1,z2,z3,z4,z6]),(1,[z0,z1,z243,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z244]),(1,[z0,z1,z2,z3,z4,z215])],[(0,[z0,z1,z2,z245,z3,z4,z6]),(0,[z246,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z247,z3,z4,z6]),(1,[z0,z1,z2,z3,z45,z6]),(0,[z0,z1,z2,z112,z3,z4,z6])],[(0,[z221,z0,z1,z20,z3,z4,z6]),(0,[z142,z59,z1,z2,z3,z4,z6]),(0,[z0,z1,z20,z3,z166,z4,z6]),(0,[z0,z1,z2,z141,z52,z4,z6]),(1,[z0,z150,z14,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z23,z47])],[(0,[z142,z1,z2,z3,z4,z6,z41]),(0,[z0,z248,z1,z20,z3,z4,z6]),(0,[z249,z0,z1,z20,z3,z4,z6]),(0,[z86,z0,z1,z2,z3,z4,z6]),(0,[z30,z0,z58,z2,z3,z4,z6]),(0,[z0,z1,z250,z2,z3,z4,z6])],[(0,[z186,z1,z133,z2,z3,z4,z6]),(0,[z32,z0,z1,z2,z3,z4,z23])],[(0,[z22,z153,z0,z2,z3,z4,z6]),(0,[z251,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z62,z4,z6]),(1,[z0,z1,z2,z3,z252,z6]),(0,[z253,z0,z1,z2,z3,z4,z6])],[(0,[z59,z0,z1,z2,z3,z4,z6]),(0,[z254,z0,z1,z2,z3,z4,z6]),(1,[z0,z255,z2,z3,z4,z6]),(1,[z0,z1,z2,z216,z4,z6])],[(0,[z67,z0,z1,z12,z3,z4,z6]),(0,[z0,z1,z25,z12,z3,z4,z6]),(0,[z0,z1,z256,z2,z3,z4,z6]),(0,[z0,z1,z20,z3,z144,z4,z6]),(1,[z0,z1,z178,z3,z4,z6]),(0,[z257,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z258,z6]),(0,[z0,z1,z2,z3,z122,z6,z107]),(0,[z0,z1,z2,z3,z259,z4,z6]),(0,[z0,z1,z2,z3,z260,z4,z6])]],
   [[(0,[z0,z1,z2,z3,z97,z4,z6]),(0,[z86,z1,z2,z3,z4,z46,z6]),(0,[z0,z1,z2,z3,z261,z4,z6]),(0,[z0,z1,z53,z78,z3,z4,z6])],[(0,[z262,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z12,z3,z4,z6,z23]),(0,[z0,z1,z12,z3,z263,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z264]),(0,[z0,z1,z2,z3,z4,z6,z265]),(0,[z0,z1,z266,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z267,z4,z6]),(0,[z268,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z269,z6])],[(1,[z0,z1,z270,z3,z4,z6]),(0,[z0,z2,z3,z122,z4,z15,z6]),(0,[z0,z1,z2,z3,z271,z4,z6])],[(0,[z0,z1,z14,z12,z3,z4,z6]),(0,[z30,z0,z1,z2,z3,z4,z272]),(1,[z0,z90,z2,z3,z4,z6]),(0,[z0,z273,z1,z2,z3,z4,z6])],[(0,[z48,z0,z1,z266,z3,z4,z6]),(0,[z0,z274,z1,z2,z3,z4,z6]),(0,[z87,z0,z1,z77,z3,z4,z6]),(0,[z275,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z276,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z277]),(1,[z0,z1,z2,z3,z278,z6]),(0,[z22,z0,z2,z3,z4,z15,z6]),(0,[z279,z0,z1,z2,z3,z4,z6]),(0,[z32,z0,z1,z2,z280,z4,z6])],[(1,[z0,z1,z266,z3,z4,z6]),(0,[z0,z1,z2,z112,z3,z74,z6]),(0,[z0,z1,z281,z2,z3,z4,z6])],[(0,[z1,z2,z3,z49,z4,z46,z6]),(0,[z87,z0,z225,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z282,z4,z6])]],
   [[(0,[z67,z0,z1,z20,z3,z4,z6]),(0,[z0,z1,z283,z2,z3,z4,z6]),(1,[z0,z284,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z285,z4,z6]),(0,[z86,z0,z286,z2,z3,z4,z6]),(0,[z0,z1,z2,z112,z3,z46,z6]),(0,[z40,z0,z1,z287,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z288,z6]),(0,[z73,z289,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z290,z4,z6]),(0,[z291,z0,z1,z2,z3,z4,z6])],[(0,[z123,z0,z1,z12,z3,z4,z6]),(0,[z0,z1,z2,z152,z80,z4,z6]),(0,[z292,z0,z1,z2,z3,z4,z6]),(0,[z86,z0,z1,z2,z3,z46,z6]),(0,[z0,z1,z2,z3,z49,z15,z6]),(0,[z0,z1,z2,z3,z4,z28,z41]),(0,[z0,z1,z2,z3,z4,z28,z47])],[(0,[z0,z24,z1,z12,z3,z4,z6]),(1,[z199,z0,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z4,z264]),(0,[z0,z1,z2,z3,z4,z4,z6])],[(0,[z0,z58,z133,z2,z3,z4,z6]),(0,[z0,z1,z12,z3,z122,z4,z6]),(0,[z1,z2,z12,z3,z4,z46,z6]),(0,[z0,z1,z20,z117,z3,z4,z6]),(0,[z0,z1,z2,z293,z3,z4,z6]),(0,[z0,z1,z2,z3,z38,z4,z6])],[(0,[z0,z1,z2,z3,z294,z4,z6]),(0,[z0,z1,z2,z177,z3,z4,z6]),(0,[z0,z1,z2,z218,z3,z4,z6]),(0,[z22,z0,z150,z2,z3,z4,z6]),(1,[z0,z105,z2,z3,z4,z6])],[(0,[z59,z1,z133,z2,z3,z4,z6]),(0,[z83,z0,z1,z12,z3,z4,z6]),(0,[z139,z0,z1,z12,z3,z4,z6]),(0,[z142,z1,z20,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z9,z6]),(0,[z0,z1,z2,z3,z4,z6,z295]),(0,[z0,z1,z2,z3,z4,z296,z6]),(0,[z0,z1,z2,z3,z74,z6,z47]),(1,[z37,z1,z2,z3,z4,z6])],[(0,[z186,z0,z1,z2,z3,z203,z6]),(0,[z297,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z15,z6,z107])]],
   [[(0,[z0,z1,z298,z2,z3,z4,z6]),(0,[z0,z150,z1,z12,z3,z4,z6]),(0,[z0,z114,z1,z2,z152,z4,z6]),(0,[z0,z1,z299,z2,z3,z4,z6]),(0,[z0,z1,z2,z300,z3,z4,z6]),(0,[z0,z1,z2,z3,z301,z4,z6])],[(0,[z0,z58,z1,z2,z3,z15,z6]),(0,[z0,z1,z2,z3,z4,z302,z6]),(0,[z0,z1,z2,z112,z3,z263,z6])],[(1,[z0,z1,z303,z3,z4,z6]),(0,[z0,z133,z2,z3,z166,z4,z6]),(0,[z0,z1,z2,z3,z4,z29,z23]),(0,[z0,z1,z2,z3,z304,z4,z6]),(0,[z0,z1,z2,z3,z305,z4,z6]),(0,[z0,z306,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z307])],[(0,[z308,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z92,z12,z3,z4,z6]),(0,[z123,z0,z1,z20,z3,z4,z6]),(0,[z309,z0,z1,z2,z3,z4,z6])],[(1,[z40,z1,z12,z3,z4,z6]),(0,[z0,z1,z53,z12,z3,z4,z6]),(0,[z0,z24,z1,z20,z3,z4,z6]),(0,[z0,z58,z2,z14,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z310,z6]),(1,[z0,z138,z2,z3,z4,z6]),(0,[z311,z0,z1,z2,z3,z4,z6])],[(1,[z0,z1,z312,z3,z4,z6]),(0,[z0,z1,z2,z3,z65,z4,z41]),(0,[z0,z1,z2,z3,z4,z313,z6])],[(0,[z1,z133,z2,z3,z4,z46,z6]),(0,[z0,z1,z2,z3,z4,z28,z42]),(0,[z0,z1,z314,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z315,z4,z6]),(1,[z0,z1,z316,z3,z4,z6]),(0,[z83,z0,z1,z20,z3,z4,z6]),(0,[z139,z0,z1,z20,z3,z4,z6]),(0,[z0,z1,z2,z317,z3,z4,z6]),(0,[z48,z0,z1,z2,z3,z49,z6]),(0,[z0,z1,z2,z3,z318,z4,z6]),(0,[z123,z0,z1,z2,z3,z4,z319]),(0,[z0,z1,z2,z3,z320,z4,z6]),(0,[z0,z1,z2,z3,z321,z4,z6])]],
   [[(0,[z0,z1,z20,z3,z4,z6,z23]),(0,[z0,z1,z2,z3,z4,z322,z6]),(1,[z0,z1,z2,z323,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z324]),(0,[z0,z1,z2,z3,z4,z6,z325]),(0,[z87,z0,z1,z2,z3,z4,z29]),(0,[z22,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z74,z6])],[(0,[z326,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z327]),(0,[z328,z0,z1,z12,z3,z4,z6]),(0,[z0,z150,z1,z20,z3,z4,z6]),(1,[z0,z1,z2,z3,z4,z313]),(1,[z0,z329,z2,z3,z4,z6]),(0,[z32,z0,z1,z3,z4,z6,z130]),(0,[z0,z1,z2,z141,z95,z4,z6])],[(0,[z330,z0,z1,z2,z3,z4,z6]),(0,[z221,z1,z2,z12,z3,z4,z6]),(0,[z0,z1,z2,z331,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z46,z6]),(0,[z0,z1,z332,z2,z3,z4,z6]),(0,[z0,z1,z333,z2,z3,z4,z6]),(0,[z0,z334,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z335,z6])],[(0,[z336,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z132,z6]),(0,[z142,z0,z1,z2,z3,z4,z6]),(0,[z86,z0,z1,z2,z3,z4,z337]),(0,[z0,z1,z2,z3,z4,z338,z6]),(0,[z0,z1,z2,z3,z339,z4,z6]),(0,[z0,z1,z2,z109,z4,z6,z107]),(0,[z68,z0,z1,z2,z109,z4,z6])],[(0,[z1,z2,z52,z3,z80,z4,z6]),(0,[z0,z1,z2,z340,z3,z4,z6]),(0,[z87,z0,z1,z178,z3,z4,z6]),(0,[z0,z1,z2,z3,z341,z4,z6]),(0,[z0,z1,z2,z141,z152,z4,z6])],[(0,[z186,z153,z1,z2,z3,z4,z6]),(1,[z0,z1,z342,z3,z4,z6]),(0,[z0,z1,z12,z141,z3,z4,z6]),(0,[z59,z1,z2,z52,z3,z4,z6]),(0,[z0,z1,z2,z3,z343,z4,z6]),(0,[z0,z24,z2,z14,z3,z4,z6]),(0,[z0,z1,z344,z2,z3,z4,z6])],[],[(0,[z0,z1,z2,z3,z4,z345,z6]),(0,[z0,z1,z346,z2,z3,z4,z6]),(1,[z0,z207,z2,z3,z4,z6]),(1,[z0,z1,z92,z3,z4,z54])]],
   [[(0,[z142,z1,z2,z3,z4,z46,z6]),(0,[z0,z114,z1,z2,z166,z4,z6]),(0,[z0,z1,z53,z2,z78,z4,z6])],[(0,[z0,z1,z12,z3,z4,z6,z107]),(1,[z123,z0,z2,z166,z4,z6]),(0,[z0,z58,z1,z2,z3,z122,z6]),(0,[z0,z1,z2,z247,z3,z4,z6]),(0,[z73,z0,z1,z2,z3,z4,z313])],[(0,[z0,z114,z133,z2,z3,z4,z6]),(1,[z153,z19,z2,z3,z4,z6]),(0,[z0,z104,z1,z12,z3,z4,z6]),(0,[z0,z150,z2,z14,z3,z4,z6]),(0,[z0,z1,z2,z152,z3,z4,z6]),(0,[z0,z1,z2,z347,z3,z4,z6]),(0,[z44,z306,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z109,z4,z130])],[(0,[z0,z58,z19,z2,z3,z4,z6]),(0,[z348,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z20,z3,z122,z4,z6]),(0,[z0,z1,z2,z349,z3,z4,z6]),(0,[z0,z1,z2,z350,z3,z4,z6]),(0,[z351,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z12,z3,z4,z54,z6]),(0,[z0,z1,z2,z3,z95,z144,z6])],[(1,[z0,z20,z21,z3,z4,z6]),(1,[z0,z352,z1,z3,z4,z6]),(0,[z0,z104,z1,z2,z3,z4,z28]),(0,[z353,z0,z1,z2,z3,z4,z6])],[(0,[z186,z142,z1,z2,z3,z4,z6]),(0,[z32,z0,z1,z92,z3,z4,z6]),(0,[z0,z1,z2,z354,z3,z4,z6])],[(1,[z0,z1,z355,z3,z4,z6]),(0,[z83,z0,z1,z2,z52,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z356]),(0,[z0,z1,z2,z357,z3,z4,z6]),(0,[z358,z0,z1,z2,z3,z4,z6]),(1,[z0,z58,z2,z3,z122,z6]),(0,[z0,z359,z1,z2,z3,z4,z6])]],
   [[(0,[z360,z0,z1,z2,z3,z4,z6]),(0,[z361,z0,z1,z2,z3,z4,z6]),(1,[z221,z1,z12,z3,z4,z6]),(0,[z362,z0,z1,z2,z3,z4,z6]),(0,[z0,z104,z2,z3,z4,z28,z6]),(0,[z0,z1,z2,z363,z3,z4,z6])],[(0,[z364,z0,z1,z2,z3,z4,z6]),(0,[z87,z0,z1,z2,z3,z62,z6]),(0,[z0,z1,z2,z3,z365,z4,z6])],[(0,[z153,z0,z133,z2,z3,z4,z6]),(0,[z1,z2,z12,z3,z4,z6,z41]),(0,[z0,z1,z2,z270,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z366,z6]),(0,[z0,z114,z2,z14,z3,z4,z6]),(1,[z139,z0,z1,z2,z6,z107])],[(0,[z0,z104,z1,z20,z3,z4,z6]),(0,[z0,z1,z2,z80,z4,z6,z107]),(0,[z87,z0,z70,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z367,z4,z6]),(0,[z0,z1,z368,z2,z3,z4,z6]),(0,[z0,z1,z2,z369,z3,z4,z6])],[(0,[z0,z104,z133,z2,z3,z4,z6]),(0,[z0,z1,z192,z2,z3,z4,z6]),(1,[z0,z1,z69,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z337]),(0,[z86,z0,z1,z2,z3,z4,z370]),(0,[z0,z1,z2,z141,z166,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z371]),(0,[z0,z1,z2,z3,z65,z4,z6])],[(0,[z153,z1,z2,z3,z80,z4,z6]),(0,[z0,z1,z2,z14,z3,z4,z6]),(0,[z0,z1,z2,z372,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z373]),(0,[z0,z1,z92,z2,z3,z4,z130]),(0,[z374,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z375]),(0,[z0,z1,z14,z3,z55,z4,z6]),(0,[z0,z376,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z377,z6]),(0,[z0,z2,z3,z4,z28,z6,z23]),(0,[z0,z1,z2,z3,z109,z4,z54]),(0,[z0,z1,z2,z141,z3,z140,z4])],[(0,[z378,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z379,z3,z4,z6]),(0,[z0,z1,z2,z380,z3,z4,z6]),(0,[z139,z0,z1,z2,z141,z4,z6]),(0,[z381,z0,z1,z2,z3,z4,z6])]],
   [[(0,[z0,z133,z2,z3,z4,z15,z6]),(0,[z0,z1,z382,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z42,z130])],[(1,[z186,z1,z12,z3,z4,z6]),(0,[z32,z0,z1,z12,z3,z4,z6]),(0,[z0,z1,z2,z3,z383,z4,z6]),(0,[z0,z384,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z112,z113,z4,z6])],[(0,[z153,z0,z2,z14,z3,z4,z6]),(0,[z59,z0,z1,z12,z3,z4,z6]),(0,[z385,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z386,z2,z3,z4,z6]),(0,[z67,z0,z2,z3,z4,z6,z23]),(0,[z387,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z388,z2,z3,z4,z6])],[(0,[z389,z0,z1,z2,z3,z4,z6]),(0,[z86,z0,z148,z2,z3,z4,z6]),(0,[z0,z1,z2,z112,z3,z49,z6]),(1,[z0,z1,z191,z3,z4,z6])],[(0,[z0,z1,z20,z141,z3,z4,z6]),(0,[z0,z1,z2,z52,z4,z6,z107]),(0,[z0,z104,z2,z14,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z390]),(0,[z0,z1,z2,z3,z4,z6,z391]),(0,[z0,z1,z2,z78,z4,z6,z42]),(0,[z0,z392,z1,z2,z3,z4,z6]),(0,[z393,z0,z1,z2,z3,z4,z6])],[(0,[z0,z394,z1,z2,z3,z4,z6]),(0,[z0,z1,z395,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z396]),(0,[z397,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z144,z4,z6])],[(0,[z0,z398,z1,z2,z3,z4,z6]),(0,[z0,z1,z20,z25,z3,z4,z6]),(1,[z86,z1,z2,z3,z46,z6]),(0,[z0,z24,z1,z3,z55,z4,z6]),(0,[z0,z399,z1,z2,z3,z4,z6]),(0,[z0,z1,z400,z2,z3,z4,z6]),(0,[z401,z0,z1,z2,z3,z4,z6])],[(0,[z402,z0,z1,z2,z3,z4,z6]),(1,[z44,z0,z1,z55,z4,z6]),(0,[z0,z1,z2,z3,z263,z6,z107])]],
   [[(0,[z403,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z20,z3,z4,z6,z107]),(0,[z0,z1,z2,z3,z4,z6,z404]),(0,[z0,z1,z2,z3,z4,z6,z41]),(0,[z0,z1,z2,z3,z4,z6,z47])],[(0,[z0,z114,z19,z2,z3,z4,z6]),(0,[z405,z0,z1,z2,z3,z4,z6]),(0,[z406,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z92,z2,z3,z4,z54]),(0,[z0,z1,z2,z3,z4,z6,z407]),(0,[z68,z0,z1,z2,z3,z50,z6])],[(0,[z0,z1,z2,z303,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z408,z6]),(0,[z30,z0,z1,z12,z3,z4,z6]),(0,[z48,z1,z2,z12,z3,z4,z6]),(0,[z32,z0,z1,z20,z3,z4,z6]),(0,[z0,z1,z2,z3,z409,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z410]),(0,[z0,z1,z2,z3,z4,z6,z411])],[(0,[z59,z0,z1,z20,z3,z4,z6]),(0,[z0,z1,z20,z53,z3,z4,z6]),(0,[z0,z1,z20,z3,z4,z54,z6]),(0,[z40,z0,z1,z2,z3,z4,z29]),(0,[z0,z1,z2,z3,z412,z4,z6])],[(0,[z0,z1,z12,z3,z76,z4,z6]),(0,[z0,z1,z256,z20,z3,z4,z6]),(0,[z413,z0,z1,z2,z3,z4,z6]),(0,[z184,z0,z1,z2,z3,z4,z6]),(1,[z242,z1,z2,z3,z4,z6]),(0,[z0,z1,z243,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z414]),(0,[z0,z1,z2,z3,z415,z4,z6])],[(0,[z186,z22,z0,z2,z3,z4,z6]),(0,[z0,z1,z416,z12,z3,z4,z6]),(0,[z417,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z140,z4,z6]),(0,[z0,z1,z2,z3,z4,z418,z6])],[(0,[z0,z1,z419,z2,z3,z4,z6]),(0,[z0,z420,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z316,z3,z4,z6]),(0,[z0,z1,z421,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z422]),(0,[z0,z1,z2,z3,z46,z6,z107]),(1,[z40,z1,z2,z3,z4,z29]),(0,[z0,z1,z2,z3,z423,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z424]),(0,[z425,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z55,z4,z6,z42]),(0,[z0,z1,z2,z3,z4,z426,z6]),(0,[z0,z1,z2,z3,z280,z4,z6]),(0,[z0,z1,z3,z4,z54,z6,z130]),(0,[z427,z0,z1,z2,z3,z4,z6])]],
   [[(0,[z0,z1,z12,z3,z4,z6,z96]),(0,[z87,z40,z1,z2,z3,z4,z6]),(0,[z0,z58,z2,z3,z122,z4,z6])],[(0,[z153,z0,z19,z2,z3,z4,z6]),(0,[z0,z1,z20,z52,z3,z4,z6]),(0,[z0,z1,z2,z3,z49,z4,z6]),(0,[z0,z1,z2,z3,z428,z4,z6]),(0,[z0,z1,z429,z2,z3,z4,z6]),(0,[z430,z0,z1,z2,z3,z4,z6])],[(0,[z431,z0,z1,z2,z3,z4,z6]),(0,[z87,z0,z1,z2,z163,z4,z6]),(0,[z67,z0,z104,z2,z3,z4,z6]),(0,[z432,z0,z1,z2,z3,z4,z6]),(0,[z0,z433,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z117,z4,z6,z107])],[(0,[z0,z104,z19,z2,z3,z4,z6]),(0,[z434,z0,z1,z2,z3,z4,z6]),(0,[z30,z0,z1,z20,z3,z4,z6]),(0,[z435,z0,z1,z2,z3,z4,z6]),(0,[z30,z0,z1,z2,z137,z4,z6]),(1,[z289,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z174,z3,z4,z6]),(0,[z0,z1,z436,z2,z3,z4,z6])],[(0,[z0,z1,z12,z3,z4,z15,z6]),(0,[z0,z1,z12,z3,z109,z4,z6]),(1,[z0,z1,z437,z3,z4,z6]),(0,[z0,z438,z1,z2,z3,z4,z6]),(0,[z439,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z42]),(0,[z0,z1,z440,z2,z3,z4,z6])],[(0,[z0,z1,z2,z441,z3,z4,z6]),(0,[z0,z81,z1,z12,z3,z4,z6]),(0,[z0,z1,z442,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z443]),(0,[z123,z0,z1,z2,z152,z4,z6]),(0,[z67,z0,z1,z2,z3,z4,z28]),(0,[z0,z444,z1,z2,z3,z4,z6])],[(0,[z32,z0,z24,z1,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z445])],[(0,[z0,z1,z446,z2,z3,z4,z6])]],
   [[(1,[z199,z0,z20,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z447,z6]),(0,[z123,z0,z1,z2,z3,z71,z6]),(0,[z0,z1,z2,z3,z448,z4,z6]),(0,[z0,z1,z2,z3,z449,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z450])],[(0,[z0,z1,z2,z3,z451,z4,z6]),(0,[z452,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z53,z14,z3,z4,z6]),(0,[z0,z1,z255,z2,z3,z4,z6])],[(0,[z0,z11,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z453,z3,z4,z6]),(0,[z0,z1,z2,z141,z109,z4,z6])],[(0,[z0,z1,z454,z2,z3,z4,z6]),(0,[z0,z1,z20,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z455,z4,z6]),(0,[z59,z0,z1,z2,z52,z4,z6]),(0,[z0,z104,z1,z247,z3,z4,z6]),(0,[z32,z0,z1,z2,z3,z4,z130])],[(0,[z0,z19,z1,z12,z3,z4,z6]),(0,[z0,z1,z12,z3,z80,z4,z6]),(0,[z0,z1,z12,z3,z4,z147,z6]),(0,[z456,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z457,z4,z6]),(0,[z0,z1,z2,z3,z4,z458,z6]),(0,[z0,z1,z2,z3,z4,z459,z6]),(0,[z73,z0,z1,z25,z3,z4,z6]),(0,[z0,z1,z25,z2,z3,z144,z6]),(0,[z0,z460,z1,z2,z3,z4,z6]),(0,[z0,z461,z1,z2,z3,z4,z6]),(0,[z462,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z141,z3,z4,z215])],[(1,[z0,z1,z2,z3,z4,z84]),(1,[z87,z1,z2,z3,z4,z41]),(0,[z0,z1,z2,z3,z463,z4,z6])],[(0,[z199,z0,z20,z2,z3,z4,z6]),(1,[z0,z1,z2,z218,z4,z6]),(0,[z0,z464,z1,z2,z3,z4,z6]),(0,[z0,z70,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z23]),(0,[z0,z1,z2,z3,z109,z4,z28]),(0,[z0,z1,z90,z2,z3,z4,z6]),(0,[z0,z1,z2,z465,z3,z4,z6]),(0,[z73,z444,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z355,z3,z4,z6]),(1,[z0,z1,z2,z3,z97,z6]),(0,[z0,z1,z2,z3,z4,z6,z6]),(0,[z0,z1,z2,z3,z466,z4,z6]),(0,[z0,z467,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z468,z6]),(0,[z44,z387,z1,z2,z3,z4,z6])]],
   [[(0,[z0,z1,z12,z3,z4,z6,z130]),(0,[z0,z1,z2,z3,z4,z469,z6]),(0,[z22,z0,z58,z2,z3,z4,z6]),(0,[z0,z470,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z471,z4,z6]),(0,[z0,z1,z2,z472,z3,z4,z6]),(0,[z0,z1,z473,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z474,z6])],[(0,[z475,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z476,z3,z4,z6]),(0,[z0,z1,z2,z477,z3,z4,z6])],[(0,[z478,z0,z1,z2,z3,z4,z6]),(0,[z186,z0,z1,z2,z315,z4,z6]),(0,[z479,z0,z1,z2,z3,z4,z6])],[(0,[z40,z0,z1,z12,z3,z4,z6]),(0,[z0,z1,z2,z3,z480,z4,z6]),(0,[z0,z481,z1,z2,z3,z4,z6]),(0,[z482,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z483,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z484]),(0,[z0,z1,z2,z141,z3,z6,z107]),(0,[z0,z1,z2,z485,z3,z4,z6])],[(1,[z0,z1,z2,z181,z4,z6]),(0,[z486,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z12,z78,z3,z4,z6]),(0,[z44,z0,z1,z2,z55,z4,z6]),(0,[z487,z0,z1,z2,z3,z4,z6])],[(0,[z0,z19,z1,z20,z3,z4,z6]),(0,[z0,z1,z20,z3,z488,z4,z6]),(0,[z0,z1,z2,z3,z4,z84,z6]),(0,[z0,z1,z2,z3,z489,z4,z6]),(0,[z123,z0,z1,z2,z166,z4,z6]),(0,[z0,z1,z2,z3,z490,z4,z6])],[(0,[z491,z0,z1,z2,z3,z4,z6]),(0,[z123,z0,z1,z2,z3,z136,z6]),(1,[z306,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z263,z95,z6])],[(0,[z492,z0,z1,z2,z3,z4,z6]),(0,[z493,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z379,z3,z4,z6]),(0,[z0,z1,z2,z494,z3,z4,z6]),(0,[z0,z1,z2,z495,z3,z4,z6]),(0,[z32,z0,z1,z2,z3,z4,z54]),(1,[z0,z1,z2,z3,z50,z6])]],
   [[(0,[z0,z0,z1,z2,z3,z4,z6]),(0,[z496,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z497]),(0,[z44,z0,z1,z53,z3,z4,z6]),(0,[z498,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z105,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z499,z4,z6])],[(1,[z0,z1,z2,z3,z4,z6]),(0,[z500,z0,z1,z2,z3,z4,z6]),(0,[z19,z1,z133,z2,z3,z4,z6]),(0,[z0,z1,z2,z61,z3,z4,z6]),(0,[z0,z501,z1,z2,z3,z4,z6]),(0,[z0,z1,z92,z2,z3,z4,z28]),(0,[z68,z0,z1,z2,z3,z109,z4]),(0,[z0,z1,z2,z3,z65,z6,z47])],[(1,[z0,z114,z2,z152,z4,z6]),(0,[z502,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z4,z35]),(0,[z0,z1,z2,z3,z4,z54,z47]),(0,[z0,z1,z2,z503,z3,z4,z6]),(1,[z0,z1,z2,z3,z263,z47]),(1,[z0,z1,z2,z354,z4,z6])],[(0,[z0,z1,z12,z204,z3,z4,z6]),(0,[z0,z1,z20,z3,z4,z15,z6]),(0,[z0,z1,z20,z3,z109,z4,z6]),(0,[z0,z1,z20,z3,z263,z4,z6]),(1,[z0,z21,z2,z3,z4,z6]),(0,[z0,z1,z2,z504,z3,z4,z6])],[(0,[z40,z0,z1,z20,z3,z4,z6]),(0,[z0,z1,z2,z505,z3,z4,z6]),(0,[z0,z1,z2,z506,z3,z4,z6])],[(0,[z0,z1,z20,z121,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z507,z6]),(0,[z0,z1,z2,z3,z4,z508,z6]),(1,[z0,z1,z446,z3,z4,z6]),(0,[z0,z1,z2,z509,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z510,z6])],[(0,[z83,z1,z2,z3,z80,z4,z6]),(0,[z0,z1,z2,z511,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z179]),(0,[z0,z1,z2,z512,z3,z4,z6]),(0,[z0,z329,z1,z2,z3,z4,z6]),(0,[z32,z0,z1,z2,z3,z252,z6]),(0,[z0,z1,z2,z3,z4,z513,z6])],[(0,[z0,z1,z12,z3,z4,z514,z6]),(0,[z0,z1,z515,z2,z3,z4,z6]),(0,[z516,z0,z1,z2,z3,z4,z6]),(0,[z32,z0,z255,z2,z3,z4,z6]),(0,[z32,z0,z1,z2,z216,z4,z6]),(0,[z0,z1,z2,z3,z517,z4,z6]),(0,[z518,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z519,z3,z4,z6])]],
   [[(0,[z520,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z20,z3,z521,z4,z6]),(0,[z0,z352,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z95,z4,z6]),(0,[z0,z1,z2,z117,z3,z109,z4])],[(0,[z0,z1,z2,z522,z3,z4,z6]),(0,[z73,z0,z1,z2,z3,z4,z6]),(0,[z0,z523,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z524,z4,z6])],[(0,[z0,z1,z2,z3,z46,z15,z6]),(0,[z0,z1,z2,z3,z4,z6,z525]),(0,[z0,z24,z150,z1,z3,z4,z6]),(0,[z123,z0,z2,z3,z166,z4,z6]),(0,[z30,z0,z1,z243,z3,z4,z6]),(0,[z0,z1,z2,z3,z144,z6,z47]),(1,[z0,z1,z2,z3,z33,z6]),(0,[z526,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z65,z263,z4])],[(0,[z186,z0,z1,z12,z3,z4,z6]),(0,[z0,z1,z20,z3,z80,z4,z6]),(0,[z0,z1,z2,z3,z4,z527,z6]),(0,[z0,z528,z1,z2,z3,z4,z6])],[(0,[z186,z0,z1,z2,z3,z4,z100]),(0,[z529,z0,z1,z2,z3,z4,z6]),(0,[z22,z0,z1,z2,z3,z4,z497]),(0,[z0,z1,z2,z530,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z28,z6]),(0,[z0,z531,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z532])],[(0,[z153,z0,z1,z312,z3,z4,z6]),(0,[z83,z0,z1,z355,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z533,z6]),(0,[z87,z0,z1,z2,z3,z278,z6]),(0,[z22,z0,z1,z2,z3,z4,z241]),(0,[z0,z1,z2,z112,z3,z65,z4])],[(0,[z534,z0,z1,z2,z3,z4,z6]),(0,[z68,z0,z1,z2,z80,z4,z6]),(1,[z0,z286,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z535]),(0,[z0,z1,z14,z3,z4,z74,z6]),(0,[z32,z0,z1,z14,z3,z4,z6]),(0,[z0,z536,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z54,z42])],[(0,[z153,z0,z1,z316,z3,z4,z6]),(0,[z0,z1,z20,z3,z4,z537,z6]),(0,[z0,z1,z20,z3,z4,z6,z130]),(0,[z68,z0,z1,z2,z3,z4,z47])]],
   [[(0,[z0,z1,z133,z2,z3,z4,z6]),(0,[z0,z1,z538,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z539,z6]),(0,[z0,z1,z12,z12,z3,z4,z6]),(0,[z540,z0,z1,z2,z3,z4,z6]),(0,[z541,z0,z1,z2,z3,z4,z6]),(0,[z123,z0,z114,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z4,z179]),(0,[z44,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z542]),(0,[z0,z1,z2,z543,z3,z4,z6])],[(0,[z544,z0,z1,z2,z3,z4,z6]),(0,[z153,z19,z1,z2,z3,z4,z6]),(0,[z0,z1,z12,z112,z3,z4,z6]),(0,[z0,z1,z2,z545,z3,z4,z6]),(0,[z193,z0,z1,z2,z3,z4,z6]),(0,[z546,z0,z1,z2,z3,z4,z6]),(1,[z184,z1,z2,z3,z4,z6]),(0,[z123,z0,z1,z379,z3,z4,z6]),(0,[z547,z0,z1,z2,z3,z4,z6]),(0,[z548,z0,z1,z2,z3,z4,z6])],[(0,[z199,z0,z1,z20,z3,z4,z6]),(0,[z68,z0,z1,z2,z55,z4,z6])],[(0,[z0,z1,z2,z3,z549,z4,z6]),(0,[z0,z195,z1,z2,z3,z4,z6]),(0,[z550,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z109,z4,z6,z42])],[(0,[z186,z0,z1,z20,z3,z4,z6]),(1,[z59,z1,z12,z3,z4,z6]),(0,[z0,z1,z2,z437,z3,z4,z6]),(0,[z0,z1,z2,z3,z551,z4,z6]),(0,[z552,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z553]),(0,[z0,z1,z2,z3,z263,z109,z4])],[(0,[z186,z0,z133,z2,z3,z4,z6]),(0,[z153,z48,z1,z2,z3,z4,z6]),(0,[z405,z0,z1,z12,z3,z4,z6]),(0,[z554,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z555,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z556,z6]),(0,[z0,z1,z2,z3,z95,z74,z6])],[(0,[z0,z1,z20,z3,z4,z6,z189]),(0,[z0,z286,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z49,z6,z47]),(1,[z0,z1,z2,z88,z4,z6]),(0,[z0,z557,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z558,z6]),(0,[z0,z24,z1,z3,z4,z74,z6]),(0,[z0,z1,z2,z3,z65,z4,z23]),(0,[z0,z207,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z559]),(0,[z73,z0,z1,z2,z3,z74,z6]),(0,[z0,z1,z2,z117,z3,z4,z47])],[(0,[z0,z1,z2,z3,z95,z46,z6]),(0,[z560,z0,z1,z2,z3,z4,z6]),(0,[z32,z37,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z113,z4,z6])]],
   [[(0,[z0,z1,z20,z21,z3,z4,z6]),(0,[z561,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z319,z6]),(0,[z0,z1,z2,z3,z562,z4,z6])],[(0,[z186,z0,z1,z2,z3,z4,z75]),(0,[z86,z0,z1,z12,z3,z4,z6]),(0,[z0,z1,z2,z3,z563,z4,z6]),(1,[z22,z0,z24,z3,z4,z6]),(0,[z289,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z141,z3,z95,z6]),(0,[z0,z1,z2,z564,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z565]),(0,[z0,z566,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z567,z3,z4,z6]),(0,[z142,z221,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z167,z4,z6]),(0,[z0,z1,z2,z3,z166,z4,z6]),(0,[z0,z1,z2,z3,z568,z4,z6]),(1,[z0,z1,z2,z3,z4,z36]),(0,[z0,z1,z2,z3,z4,z6,z569]),(1,[z0,z1,z2,z141,z95,z6]),(0,[z68,z0,z1,z2,z3,z4,z42])],[(0,[z0,z1,z342,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z570,z4,z6]),(0,[z0,z1,z2,z571,z3,z4,z6]),(0,[z0,z1,z20,z92,z3,z4,z6]),(0,[z0,z1,z2,z137,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z572,z6])],[(0,[z186,z0,z2,z14,z3,z4,z6]),(0,[z0,z573,z1,z2,z3,z4,z6]),(0,[z0,z574,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z575,z4,z6])],[(0,[z0,z1,z2,z3,z576,z4,z6]),(0,[z83,z59,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z577,z6]),(1,[z0,z237,z2,z3,z4,z6]),(0,[z0,z1,z2,z52,z3,z4,z6]),(0,[z0,z1,z25,z14,z3,z4,z6]),(0,[z32,z0,z1,z2,z3,z4,z28]),(0,[z578,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z579])]],
   [[(0,[z86,z0,z1,z2,z3,z49,z6]),(0,[z0,z1,z2,z3,z4,z580,z6]),(0,[z0,z1,z2,z3,z4,z6,z581]),(0,[z44,z0,z1,z2,z3,z338,z6]),(0,[z0,z1,z2,z3,z135,z95,z4])],[(1,[z0,z1,z2,z3,z4,z337]),(0,[z0,z2,z152,z3,z166,z4,z6]),(0,[z0,z582,z1,z2,z3,z4,z6]),(0,[z583,z0,z1,z2,z3,z4,z6])],[(0,[z221,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z109,z4,z41]),(0,[z584,z0,z1,z2,z3,z4,z6]),(0,[z160,z0,z1,z2,z3,z4,z6]),(0,[z32,z0,z329,z2,z3,z4,z6]),(0,[z0,z1,z2,z117,z3,z4,z42]),(0,[z0,z1,z2,z3,z263,z4,z47])],[(0,[z0,z248,z1,z2,z3,z4,z6]),(0,[z86,z0,z1,z20,z3,z4,z6]),(0,[z249,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z585,z2,z3,z4,z6]),(0,[z586,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z587,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z588]),(0,[z0,z1,z2,z589,z3,z4,z6])],[(1,[z0,z1,z2,z3,z203,z6]),(0,[z0,z1,z2,z3,z590,z4,z6])],[(0,[z0,z1,z2,z3,z163,z4,z6]),(0,[z0,z591,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z71,z6]),(0,[z0,z1,z2,z3,z592,z4,z6])],[(1,[z186,z133,z2,z3,z4,z6]),(0,[z593,z0,z1,z2,z3,z4,z6]),(0,[z0,z2,z14,z3,z4,z6,z23]),(0,[z594,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z595]),(0,[z596,z0,z1,z2,z3,z4,z6]),(0,[z68,z0,z1,z2,z3,z4,z6])],[(0,[z0,z19,z2,z3,z4,z6,z23]),(0,[z0,z1,z20,z12,z3,z4,z6]),(0,[z431,z0,z1,z20,z3,z4,z6]),(0,[z83,z0,z1,z2,z80,z4,z6]),(0,[z73,z0,z1,z2,z490,z4,z6]),(0,[z0,z1,z25,z3,z144,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z597])]],
   [[(0,[z598,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z20,z112,z3,z4,z6]),(0,[z0,z1,z2,z166,z4,z6,z107]),(0,[z0,z1,z2,z599,z3,z4,z6]),(0,[z0,z138,z1,z2,z3,z4,z6]),(0,[z32,z145,z1,z2,z3,z4,z6]),(0,[z139,z0,z1,z2,z3,z6,z107])],[(0,[z600,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z2,z3,z4,z6]),(0,[z0,z1,z601,z2,z3,z4,z6]),(1,[z30,z0,z2,z3,z15,z6]),(0,[z0,z1,z2,z3,z4,z6,z602]),(1,[z68,z0,z1,z2,z109,z4])],[(0,[z0,z1,z442,z20,z3,z4,z6]),(0,[z603,z0,z1,z2,z3,z4,z6]),(0,[z44,z0,z1,z2,z3,z4,z36])],[(0,[z0,z1,z12,z3,z4,z29,z6]),(0,[z0,z1,z2,z3,z604,z4,z6]),(1,[z387,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z605,z4,z6])],[(0,[z186,z0,z19,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z100]),(0,[z0,z1,z2,z3,z4,z6,z606])],[(0,[z48,z0,z1,z437,z3,z4,z6]),(1,[z0,z1,z287,z3,z4,z6]),(0,[z0,z1,z2,z117,z3,z4,z6])],[(0,[z0,z607,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z608,z6]),(0,[z0,z1,z120,z12,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z609]),(1,[z0,z1,z2,z117,z4,z42]),(0,[z0,z1,z2,z3,z263,z4,z42])],[(0,[z0,z1,z2,z3,z610,z4,z6]),(0,[z86,z0,z1,z177,z3,z4,z6]),(0,[z44,z0,z1,z2,z3,z4,z559]),(0,[z0,z1,z2,z3,z74,z6,z107])]],
   [[(0,[z153,z59,z1,z2,z3,z4,z6]),(0,[z0,z1,z12,z3,z4,z74,z6]),(0,[z0,z1,z20,z20,z3,z4,z6]),(0,[z0,z1,z283,z20,z3,z4,z6]),(1,[z0,z1,z168,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z42,z41]),(0,[z0,z150,z1,z14,z3,z4,z6]),(0,[z0,z1,z2,z611,z3,z4,z6])],[(0,[z83,z0,z284,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z612,z4,z6]),(1,[z444,z1,z2,z3,z4,z6])],[(0,[z0,z1,z12,z3,z4,z46,z6]),(1,[z0,z1,z2,z3,z4,z370]),(0,[z0,z1,z2,z613,z3,z4,z6]),(0,[z0,z1,z2,z112,z3,z65,z6])],[(0,[z0,z1,z331,z12,z3,z4,z6]),(0,[z0,z1,z2,z3,z488,z4,z6]),(0,[z0,z1,z2,z88,z3,z4,z6]),(0,[z0,z1,z2,z3,z65,z4,z29]),(0,[z0,z1,z2,z3,z136,z4,z6]),(0,[z0,z58,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z171,z4,z6])],[(0,[z186,z1,z2,z12,z3,z4,z6]),(0,[z0,z0,z1,z12,z3,z4,z6]),(0,[z83,z0,z1,z2,z3,z4,z264]),(0,[z614,z0,z1,z2,z3,z4,z6]),(0,[z30,z0,z1,z2,z3,z15,z6]),(0,[z615,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z616,z4,z6]),(0,[z30,z160,z1,z2,z3,z4,z6]),(1,[z0,z1,z239,z3,z4,z6]),(1,[z0,z104,z2,z3,z4,z28])],[(0,[z1,z2,z3,z4,z29,z6,z41]),(0,[z0,z1,z2,z3,z4,z41,z47]),(0,[z0,z1,z78,z3,z55,z4,z6]),(0,[z0,z617,z1,z2,z3,z4,z6]),(0,[z0,z618,z1,z2,z3,z4,z6])],[(0,[z22,z0,z1,z12,z3,z4,z6]),(0,[z83,z0,z1,z2,z3,z9,z6]),(0,[z619,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z272]),(0,[z0,z1,z2,z3,z4,z620,z6])]],
   [[(1,[z19,z1,z12,z3,z4,z6]),(1,[z1,z12,z3,z80,z4,z6]),(0,[z0,z1,z2,z621,z3,z4,z6])],[(0,[z0,z1,z622,z2,z3,z4,z6]),(0,[z0,z623,z1,z2,z3,z4,z6]),(1,[z0,z148,z2,z3,z4,z6]),(0,[z0,z1,z2,z624,z3,z4,z6]),(0,[z0,z1,z2,z3,z109,z4,z6]),(0,[z0,z1,z2,z3,z263,z4,z6])],[(0,[z0,z1,z12,z152,z3,z4,z6]),(0,[z142,z0,z1,z12,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z625]),(0,[z0,z1,z2,z3,z626,z4,z6])],[(0,[z0,z1,z12,z3,z55,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z627])],[(1,[z48,z1,z12,z3,z4,z6]),(0,[z0,z1,z2,z628,z3,z4,z6])],[(0,[z73,z0,z1,z12,z3,z4,z6]),(0,[z0,z0,z1,z20,z3,z4,z6]),(0,[z0,z1,z2,z141,z80,z4,z6]),(0,[z0,z1,z2,z629,z3,z4,z6]),(0,[z630,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z631,z6]),(0,[z0,z1,z2,z3,z521,z4,z6]),(0,[z0,z1,z284,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z632,z4,z6]),(0,[z0,z1,z2,z3,z45,z4,z6])],[(0,[z0,z1,z2,z3,z633,z4,z6]),(0,[z40,z1,z2,z3,z4,z29,z6]),(0,[z123,z0,z1,z446,z3,z4,z6]),(0,[z0,z1,z2,z634,z3,z4,z6]),(0,[z139,z0,z1,z2,z4,z6,z107])]],
   [[(0,[z22,z0,z1,z20,z3,z4,z6]),(0,[z635,z0,z1,z2,z3,z4,z6])],[(0,[z87,z1,z2,z3,z4,z6,z41]),(0,[z0,z1,z2,z636,z3,z4,z6]),(0,[z637,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z4,z272]),(0,[z0,z1,z2,z141,z55,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z638]),(0,[z0,z1,z2,z3,z639,z4,z6]),(0,[z0,z1,z2,z3,z4,z640,z6])],[(0,[z0,z1,z2,z416,z3,z4,z6]),(0,[z0,z1,z20,z3,z4,z29,z6]),(0,[z48,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z95,z49,z6]),(1,[z0,z1,z2,z3,z4,z319]),(0,[z0,z1,z2,z641,z3,z4,z6]),(0,[z0,z1,z2,z642,z3,z4,z6])],[(0,[z0,z1,z312,z2,z3,z4,z6]),(0,[z142,z0,z1,z20,z3,z4,z6])],[(0,[z643,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z133,z12,z3,z4,z6]),(0,[z44,z0,z1,z12,z3,z4,z6]),(0,[z94,z0,z1,z2,z3,z4,z6]),(0,[z30,z0,z1,z2,z3,z122,z6]),(0,[z0,z1,z2,z3,z122,z4,z6])],[(0,[z0,z1,z2,z3,z4,z537,z6]),(0,[z644,z0,z1,z2,z3,z4,z6]),(0,[z0,z157,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z645,z4,z6]),(0,[z0,z1,z53,z2,z3,z4,z6]),(0,[z646,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z647,z2,z3,z4,z6])],[(0,[z59,z1,z2,z12,z3,z4,z6]),(0,[z73,z0,z1,z20,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z648,z6]),(0,[z142,z1,z2,z3,z80,z4,z6]),(0,[z0,z1,z20,z3,z4,z322,z6]),(0,[z139,z0,z1,z2,z3,z95,z6])]],
   [[(0,[z0,z1,z2,z3,z649,z4,z6])],[(0,[z0,z1,z20,z3,z4,z46,z6]),(0,[z0,z1,z2,z3,z650,z4,z6]),(0,[z651,z0,z1,z2,z3,z4,z6]),(0,[z0,z114,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z78,z4,z6,z107])],[(0,[z328,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z652,z4,z6]),(0,[z142,z40,z1,z2,z3,z4,z6]),(0,[z87,z0,z1,z2,z3,z4,z41]),(0,[z0,z1,z2,z653,z3,z4,z6])],[(0,[z59,z0,z1,z2,z80,z4,z6]),(0,[z0,z1,z2,z3,z4,z654,z6]),(0,[z0,z2,z14,z3,z166,z4,z6]),(1,[z0,z1,z2,z3,z4,z638]),(0,[z0,z1,z2,z3,z33,z4,z6]),(0,[z0,z1,z2,z3,z655,z4,z6])],[(0,[z0,z19,z2,z3,z166,z4,z6]),(1,[z0,z1,z77,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z41,z23]),(0,[z22,z0,z24,z1,z3,z4,z6]),(0,[z22,z0,z2,z3,z166,z4,z6]),(1,[z0,z1,z2,z280,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z656])],[(0,[z186,z0,z1,z303,z3,z4,z6]),(0,[z44,z0,z1,z20,z3,z4,z6]),(1,[z0,z1,z2,z3,z4,z497]),(0,[z0,z1,z2,z3,z4,z35,z6]),(0,[z0,z1,z2,z3,z657,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z658])],[(0,[z659,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z21,z2,z3,z4,z6]),(0,[z660,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z4,z241]),(0,[z30,z242,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z661,z4,z6]),(0,[z662,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z112,z3,z65])],[(0,[z59,z0,z1,z270,z3,z4,z6]),(1,[z0,z225,z2,z3,z4,z6]),(0,[z663,z0,z1,z2,z3,z4,z6])]],
   [[(0,[z664,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z665,z6]),(0,[z0,z1,z12,z3,z4,z6,z41]),(0,[z0,z1,z12,z3,z4,z6,z47]),(0,[z44,z0,z1,z2,z78,z4,z6])],[(0,[z153,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z20,z152,z3,z4,z6]),(0,[z48,z0,z1,z2,z3,z46,z6]),(0,[z666,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z667,z6]),(0,[z668,z0,z1,z2,z3,z4,z6])],[(0,[z48,z1,z133,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z669,z4,z6]),(0,[z0,z1,z20,z3,z55,z4,z6]),(1,[z0,z1,z192,z3,z4,z6]),(0,[z670,z0,z1,z2,z3,z4,z6]),(0,[z22,z0,z114,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z671,z4,z6]),(0,[z0,z1,z2,z3,z672,z4,z6])],[(0,[z0,z1,z2,z3,z122,z46,z6]),(0,[z0,z1,z2,z3,z673,z4,z6]),(0,[z0,z104,z1,z2,z3,z4,z6]),(0,[z73,z0,z1,z2,z3,z4,z638]),(0,[z0,z1,z2,z3,z4,z674,z6]),(0,[z0,z1,z2,z112,z3,z4,z42])],[(0,[z0,z1,z2,z3,z4,z514,z6]),(1,[z0,z1,z2,z3,z338,z6]),(0,[z0,z1,z2,z55,z4,z6,z107])],[(0,[z0,z1,z2,z287,z3,z4,z6]),(0,[z675,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z141,z3,z4,z6])],[(0,[z186,z0,z1,z2,z3,z132,z6]),(0,[z153,z1,z2,z3,z4,z46,z6]),(0,[z0,z1,z20,z78,z3,z4,z6]),(0,[z676,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z135,z4])],[(0,[z378,z0,z1,z20,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z677]),(0,[z210,z24,z1,z2,z3,z4,z6]),(1,[z195,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z252,z6]),(0,[z0,z1,z678,z2,z3,z4,z6])]],
   [[(0,[z186,z0,z1,z342,z3,z4,z6]),(0,[z30,z0,z2,z3,z4,z15,z6]),(0,[z0,z352,z104,z1,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z679,z6]),(0,[z0,z1,z12,z3,z49,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z680]),(0,[z0,z1,z2,z3,z4,z6,z107]),(0,[z0,z1,z681,z2,z3,z4,z6])],[(0,[z593,z0,z1,z12,z3,z4,z6]),(0,[z68,z0,z1,z12,z3,z4,z6]),(0,[z0,z1,z2,z152,z52,z4,z6]),(0,[z0,z682,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z323,z4,z6])],[(0,[z683,z0,z1,z2,z3,z4,z6]),(0,[z598,z0,z1,z12,z3,z4,z6]),(0,[z0,z1,z12,z3,z4,z6,z42]),(0,[z1,z20,z2,z12,z3,z4,z6]),(0,[z684,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z54,z6])],[(0,[z0,z1,z2,z685,z3,z4,z6]),(0,[z686,z0,z1,z2,z3,z4,z6]),(0,[z0,z687,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z239,z3,z4,z6]),(0,[z73,z0,z1,z3,z4,z74,z6]),(0,[z0,z1,z2,z3,z4,z688,z6])],[(0,[z40,z0,z1,z191,z3,z4,z6]),(0,[z68,z0,z1,z2,z117,z4,z6])],[(0,[z0,z1,z2,z3,z4,z278,z6]),(0,[z0,z1,z2,z112,z354,z4,z6])]],
   [[(0,[z689,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z690,z6]),(0,[z0,z1,z2,z3,z691,z4,z6]),(0,[z0,z692,z1,z2,z3,z4,z6])],[(0,[z0,z1,z693,z2,z3,z4,z6]),(0,[z87,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z29,z47]),(0,[z0,z1,z2,z95,z4,z6,z107])],[(0,[z86,z0,z1,z2,z323,z4,z6]),(0,[z0,z1,z2,z3,z694,z4,z6]),(1,[z0,z1,z2,z490,z4,z6]),(0,[z32,z0,z1,z2,z3,z4,z6])],[(0,[z68,z0,z1,z20,z3,z4,z6]),(0,[z0,z695,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z4,z559])],[(0,[z696,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z697,z4,z6]),(0,[z698,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z699,z3,z4,z6])],[(0,[z598,z0,z1,z20,z3,z4,z6]),(0,[z0,z1,z2,z112,z3,z144,z6]),(0,[z0,z1,z2,z3,z65,z4,z130]),(0,[z0,z1,z700,z2,z3,z4,z6]),(0,[z0,z701,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z80,z4,z6,z42]),(0,[z0,z1,z2,z702,z3,z4,z6]),(0,[z68,z0,z1,z2,z78,z4,z6]),(0,[z0,z1,z2,z703,z3,z4,z6]),(0,[z0,z1,z2,z3,z263,z6,z47])],[(1,[z0,z1,z2,z315,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z704]),(0,[z0,z58,z1,z12,z3,z4,z6]),(0,[z40,z1,z2,z12,z3,z4,z6]),(0,[z0,z1,z20,z3,z4,z6,z41]),(0,[z0,z1,z20,z3,z4,z6,z47]),(0,[z86,z48,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z370,z6]),(0,[z0,z1,z14,z3,z4,z54,z6]),(0,[z0,z1,z2,z705,z3,z4,z6]),(0,[z706,z0,z1,z2,z3,z4,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z707,z3,z4,z6]),(0,[z0,z1,z2,z3,z708,z6]),(0,[z0,z1,z355,z3,z9,z6]),(0,[z0,z1,z2,z709,z4,z6])],[(0,[z0,z1,z2,z710,z4,z6]),(0,[z0,z286,z12,z3,z4,z6]),(0,[z0,z1,z711,z3,z4,z6]),(0,[z0,z1,z446,z3,z136,z6])],[(0,[z153,z19,z312,z3,z4,z6]),(0,[z1,z12,z3,z4,z6,z189]),(0,[z0,z1,z2,z712,z4,z6])],[(0,[z1,z12,z80,z4,z6,z107]),(0,[z0,z1,z12,z3,z4,z179]),(0,[z0,z1,z2,z3,z4,z713]),(0,[z145,z329,z2,z3,z4,z6]),(0,[z0,z1,z2,z714,z4,z6])],[(0,[z1,z12,z3,z4,z6,z371]),(0,[z0,z1,z12,z3,z338,z6]),(0,[z0,z1,z256,z121,z4,z6]),(0,[z0,z1,z2,z3,z4,z715]),(0,[z0,z70,z2,z88,z4,z6]),(0,[z32,z0,z1,z3,z33,z130])],[(0,[z0,z1,z2,z113,z74,z6]),(0,[z0,z716,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z717]),(0,[z1,z718,z12,z3,z4,z6]),(0,[z0,z1,z12,z3,z135,z4]),(0,[z68,z0,z1,z12,z109,z4]),(0,[z0,z352,z1,z3,z4,z28]),(0,[z0,z138,z2,z174,z4,z6])],[(0,[z0,z1,z2,z113,z46,z6]),(0,[z0,z719,z2,z3,z4,z6]),(0,[z0,z1,z720,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z721]),(0,[z1,z12,z80,z166,z4,z6]),(0,[z123,z0,z2,z166,z136,z6])],[(0,[z0,z1,z12,z88,z4,z6]),(0,[z387,z1,z2,z3,z4,z559]),(0,[z145,z1,z2,z3,z33,z6]),(0,[z0,z1,z700,z2,z6,z107])],[(0,[z0,z1,z342,z3,z4,z75]),(0,[z153,z722,z2,z3,z4,z6]),(0,[z0,z286,z20,z3,z4,z6]),(0,[z723,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z638])],[(0,[z0,z724,z2,z3,z4,z6]),(0,[z0,z1,z2,z725,z4,z6])],[(0,[z0,z1,z20,z3,z4,z179]),(0,[z0,z1,z2,z3,z726,z4])],[(0,[z0,z1,z20,z3,z338,z6]),(0,[z0,z1,z727,z3,z4,z6]),(0,[z0,z1,z2,z112,z3,z65])],[(0,[z0,z1,z331,z61,z4,z6]),(0,[z0,z1,z12,z141,z95,z6]),(0,[z0,z1,z12,z3,z4,z36]),(0,[z0,z1,z2,z728,z4,z6]),(0,[z0,z1,z2,z55,z4,z559])],[(0,[z0,z1,z2,z729,z4,z6]),(0,[z0,z1,z20,z3,z135,z4]),(0,[z0,z536,z14,z3,z4,z6]),(0,[z0,z1,z2,z347,z4,z42])]],
   [[(0,[z1,z12,z3,z4,z6,z41]),(0,[z0,z1,z2,z3,z4,z730]),(0,[z0,z1,z2,z3,z4,z731]),(0,[z0,z461,z1,z2,z6,z107]),(0,[z0,z1,z732,z3,z4,z6])],[(0,[z0,z168,z733,z3,z4,z6]),(0,[z184,z1,z2,z3,z4,z319])],[(0,[z0,z1,z20,z88,z4,z6]),(0,[z0,z1,z734,z3,z4,z6])],[(0,[z0,z2,z3,z4,z241,z23])],[(0,[z153,z1,z2,z315,z4,z6]),(0,[z560,z1,z12,z3,z4,z6]),(0,[z0,z284,z2,z80,z4,z6]),(0,[z289,z1,z266,z3,z4,z6]),(0,[z529,z0,z1,z2,z109,z4]),(0,[z195,z1,z2,z3,z4,z319]),(0,[z0,z58,z2,z3,z735,z6]),(0,[z0,z1,z2,z3,z736,z4]),(0,[z737,z1,z2,z3,z4,z6])],[(0,[z94,z1,z2,z80,z4,z6]),(0,[z0,z1,z2,z3,z4,z738]),(0,[z0,z1,z739,z3,z4,z6]),(1,[z0,z1,z2,z740,z4])],[(0,[z0,z21,z3,z4,z74,z6])],[(0,[z0,z1,z2,z3,z741,z6]),(0,[z0,z742,z2,z3,z4,z6]),(0,[z0,z1,z20,z141,z95,z6]),(0,[z0,z1,z20,z3,z4,z36]),(0,[z0,z1,z2,z80,z4,z264]),(0,[z0,z90,z53,z3,z4,z6]),(0,[z0,z1,z2,z3,z144,z165])],[(0,[z0,z1,z2,z3,z4,z743]),(0,[z297,z1,z12,z3,z4,z6]),(0,[z0,z744,z1,z3,z4,z6])],[(0,[z328,z0,z1,z3,z4,z96]),(0,[z86,z1,z2,z323,z46,z6]),(0,[z0,z1,z2,z745,z4,z6]),(0,[z0,z1,z746,z3,z4,z6])],[(0,[z0,z1,z2,z80,z9,z6]),(0,[z0,z1,z2,z740,z4,z42])],[(0,[z0,z1,z2,z3,z4,z747]),(0,[z59,z1,z168,z52,z4,z6]),(0,[z0,z1,z2,z3,z748,z6]),(0,[z123,z0,z379,z166,z4,z6]),(0,[z0,z1,z749,z3,z4,z6])],[(0,[z30,z0,z12,z3,z15,z6]),(0,[z1,z12,z3,z4,z269,z6]),(0,[z0,z1,z2,z3,z4,z750]),(0,[z0,z751,z2,z3,z4,z6])],[(0,[z1,z316,z3,z4,z46,z6]),(0,[z1,z419,z12,z3,z4,z6]),(0,[z0,z752,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z753,z6]),(0,[z387,z1,z12,z3,z4,z6]),(0,[z754,z1,z2,z3,z4,z6])],[(0,[z475,z1,z12,z3,z4,z6]),(0,[z0,z1,z2,z3,z735,z6]),(0,[z755,z1,z2,z3,z4,z6]),(0,[z756,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z757]),(0,[z0,z1,z2,z117,z234,z4])]],
   [[(0,[z0,z312,z14,z3,z4,z6]),(0,[z59,z1,z12,z52,z4,z6]),(0,[z0,z1,z2,z3,z758,z6]),(0,[z0,z1,z2,z3,z38,z42])],[(0,[z0,z1,z12,z117,z4,z42]),(0,[z0,z284,z2,z3,z4,z264]),(0,[z0,z1,z759,z3,z4,z6]),(0,[z0,z1,z2,z3,z760,z6]),(0,[z0,z1,z2,z490,z4,z6]),(0,[z0,z1,z2,z3,z252,z6])],[(0,[z104,z19,z12,z3,z4,z6]),(0,[z761,z0,z2,z3,z4,z6]),(0,[z0,z255,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z762,z6])],[(0,[z0,z1,z178,z3,z4,z6]),(0,[z1,z763,z2,z3,z4,z6]),(0,[z0,z392,z14,z3,z4,z6]),(0,[z764,z1,z2,z3,z4,z6]),(0,[z0,z765,z2,z3,z4,z6]),(0,[z0,z1,z2,z117,z740,z4])],[(0,[z0,z1,z2,z3,z766,z6]),(0,[z0,z284,z2,z3,z9,z6])],[(0,[z186,z2,z204,z3,z4,z6]),(0,[z0,z767,z2,z3,z4,z6]),(0,[z30,z0,z20,z3,z15,z6]),(0,[z0,z1,z2,z3,z97,z264]),(0,[z0,z1,z768,z3,z4,z6]),(0,[z0,z1,z769,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z770]),(0,[z0,z329,z2,z216,z4,z6]),(0,[z0,z1,z2,z740,z4,z6])],[(0,[z0,z1,z771,z3,z4,z6]),(0,[z0,z1,z12,z171,z4,z6]),(0,[z0,z1,z453,z3,z4,z54])],[(0,[z387,z1,z20,z3,z4,z6]),(0,[z0,z1,z2,z3,z9,z264]),(0,[z0,z772,z2,z3,z4,z6]),(0,[z773,z1,z2,z3,z4,z6]),(0,[z289,z1,z2,z3,z4,z313]),(0,[z185,z0,z1,z3,z74,z6]),(0,[z0,z1,z2,z141,z135,z4])],[(0,[z1,z12,z3,z294,z4,z6]),(0,[z0,z104,z12,z3,z4,z28]),(0,[z0,z1,z2,z3,z774,z6]),(0,[z644,z0,z1,z55,z4,z6])],[(0,[z475,z133,z2,z3,z4,z6]),(0,[z40,z1,z718,z3,z4,z6]),(0,[z59,z1,z20,z52,z4,z6]),(0,[z0,z1,z177,z3,z4,z337]),(0,[z427,z1,z2,z3,z4,z29]),(0,[z0,z775,z1,z3,z4,z6]),(0,[z242,z1,z2,z3,z15,z6]),(0,[z0,z1,z2,z3,z4,z776]),(0,[z518,z0,z1,z3,z4,z130])],[(0,[z0,z1,z20,z117,z4,z42]),(0,[z0,z777,z14,z3,z4,z6]),(0,[z0,z1,z2,z3,z778,z6])],[(0,[z461,z1,z12,z3,z4,z6]),(0,[z199,z0,z20,z3,z4,z779]),(0,[z0,z692,z2,z3,z4,z23]),(0,[z0,z255,z2,z3,z33,z6]),(0,[z0,z1,z2,z216,z33,z6]),(0,[z0,z1,z2,z3,z38,z6]),(0,[z0,z1,z2,z3,z780,z263])],[(0,[z0,z1,z12,z3,z781,z4])],[(0,[z0,z1,z2,z3,z782,z6])],[(0,[z0,z1,z2,z3,z783,z6]),(0,[z0,z1,z2,z784,z4,z6])],[(0,[z199,z0,z2,z3,z4,z6]),(0,[z142,z1,z2,z3,z4,z100]),(0,[z0,z1,z20,z171,z4,z6]),(0,[z785,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z786,z4,z6])]],
   [[(0,[z186,z19,z12,z3,z4,z6]),(0,[z431,z0,z1,z488,z4,z6]),(0,[z787,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z788,z4])],[(0,[z0,z104,z20,z3,z4,z28]),(0,[z0,z789,z2,z3,z4,z6]),(0,[z0,z105,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z6,z790])],[(0,[z0,z148,z2,z3,z49,z6]),(0,[z73,z0,z1,z3,z74,z6])],[(0,[z791,z0,z1,z3,z4,z6]),(0,[z157,z1,z25,z3,z4,z6])],[(0,[z22,z0,z2,z315,z4,z6]),(0,[z0,z1,z12,z3,z4,z272]),(0,[z199,z378,z0,z3,z4,z6]),(0,[z0,z792,z2,z3,z4,z6]),(0,[z0,z793,z2,z3,z4,z6])],[(0,[z0,z1,z12,z3,z4,z319]),(0,[z0,z1,z2,z642,z109,z4])],[(0,[z0,z11,z14,z3,z4,z6]),(0,[z0,z1,z442,z3,z4,z322]),(0,[z22,z0,z21,z3,z4,z6]),(0,[z0,z794,z2,z3,z4,z6]),(0,[z0,z1,z795,z3,z4,z6]),(0,[z0,z1,z2,z141,z95,z215])],[(0,[z0,z1,z796,z3,z4,z6]),(0,[z0,z1,z797,z3,z4,z6])],[(0,[z0,z19,z2,z3,z203,z6]),(0,[z126,z1,z12,z3,z4,z6]),(0,[z0,z1,z2,z798,z4,z6]),(0,[z0,z1,z178,z88,z4,z6]),(0,[z0,z1,z2,z799,z4,z6]),(0,[z157,z1,z53,z3,z4,z6]),(0,[z0,z1,z2,z3,z800,z6]),(0,[z0,z1,z440,z78,z4,z6]),(0,[z68,z0,z1,z2,z740,z4])],[(0,[z0,z1,z312,z3,z4,z6]),(0,[z0,z1,z12,z3,z801,z6]),(0,[z1,z12,z3,z524,z4,z6]),(0,[z242,z1,z2,z3,z122,z6]),(0,[z0,z1,z2,z3,z4,z802]),(0,[z0,z1,z2,z3,z803,z4]),(0,[z0,z1,z2,z3,z780,z6])],[(0,[z0,z1,z2,z3,z4,z804]),(0,[z186,z722,z2,z3,z4,z6]),(0,[z554,z1,z2,z80,z4,z6]),(0,[z0,z70,z77,z3,z4,z6]),(0,[z805,z1,z2,z3,z4,z6]),(0,[z22,z0,z420,z3,z4,z6]),(0,[z0,z1,z806,z3,z4,z6]),(0,[z0,z1,z2,z141,z116,z6])],[(0,[z0,z1,z303,z3,z132,z6]),(0,[z253,z1,z12,z3,z4,z6])],[(0,[z0,z1,z342,z181,z4,z6]),(0,[z0,z807,z2,z3,z4,z6]),(0,[z0,z195,z2,z166,z4,z6])],[(0,[z0,z1,z20,z3,z4,z272]),(0,[z808,z1,z2,z3,z4,z6]),(0,[z0,z379,z3,z166,z4,z6])],[(0,[z0,z1,z20,z3,z4,z319]),(0,[z126,z0,z2,z3,z15,z6]),(0,[z0,z1,z2,z3,z809,z4])],[(0,[z0,z1,z12,z280,z4,z6]),(0,[z0,z1,z355,z3,z4,z84]),(0,[z560,z1,z2,z3,z4,z29]),(0,[z0,z1,z2,z3,z4,z810])]],
   [[(0,[z1,z2,z12,z3,z203,z6]),(0,[z0,z1,z2,z137,z4,z6])],[(0,[z0,z1,z811,z3,z4,z6]),(1,[z133,z2,z315,z4,z6]),(0,[z0,z20,z812,z3,z4,z6]),(0,[z0,z1,z355,z3,z97,z6]),(0,[z1,z2,z813,z80,z4,z6]),(0,[z253,z1,z2,z3,z49,z6]),(0,[z0,z1,z2,z3,z140,z4]),(0,[z0,z814,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z815]),(0,[z0,z225,z12,z3,z4,z6]),(0,[z184,z1,z2,z3,z71,z6]),(0,[z145,z1,z2,z3,z4,z23])],[(0,[z0,z1,z816,z3,z4,z6]),(0,[z145,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z817,z4,z6]),(0,[z0,z1,z2,z3,z4,z818]),(0,[z0,z2,z3,z4,z735,z6])],[(0,[z0,z1,z819,z3,z4,z6]),(0,[z30,z0,z243,z3,z15,z6]),(0,[z444,z1,z3,z4,z74,z6]),(0,[z32,z145,z1,z3,z4,z130])],[(0,[z81,z19,z12,z3,z4,z6]),(0,[z0,z1,z2,z820,z4,z6]),(0,[z195,z1,z2,z3,z71,z6])],[(0,[z0,z1,z2,z3,z4,z75]),(0,[z0,z1,z821,z3,z4,z6]),(0,[z0,z114,z2,z522,z4,z6]),(0,[z145,z1,z442,z3,z4,z6]),(0,[z0,z329,z2,z3,z33,z6]),(0,[z32,z0,z1,z280,z4,z130])],[(0,[z1,z12,z3,z95,z46,z6])],[(0,[z0,z1,z2,z822,z4,z6]),(0,[z0,z823,z2,z3,z4,z6]),(0,[z0,z1,z20,z280,z4,z6]),(0,[z160,z1,z2,z3,z4,z35])],[(0,[z0,z1,z2,z3,z824,z6]),(0,[z413,z1,z12,z3,z4,z6]),(0,[z0,z283,z21,z3,z4,z6]),(0,[z44,z0,z1,z488,z4,z6]),(0,[z0,z1,z2,z3,z4,z825]),(0,[z0,z286,z2,z323,z4,z6]),(0,[z123,z0,z446,z166,z4,z6]),(0,[z0,z1,z826,z3,z4,z6])],[(0,[z0,z1,z12,z3,z827,z6]),(0,[z0,z1,z828,z3,z4,z6])],[(0,[z0,z225,z20,z3,z4,z6]),(0,[z0,z1,z2,z174,z4,z6]),(0,[z0,z1,z2,z55,z4,z215])],[(0,[z221,z1,z12,z3,z4,z6])],[(0,[z557,z1,z12,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z829]),(0,[z242,z2,z3,z4,z15,z6])],[(0,[z0,z1,z243,z171,z4,z6])],[(0,[z0,z1,z2,z3,z4,z830]),(0,[z0,z831,z2,z3,z4,z6]),(0,[z86,z1,z2,z218,z46,z6]),(0,[z40,z1,z77,z3,z4,z6]),(0,[z0,z1,z832,z3,z4,z6]),(0,[z833,z1,z2,z3,z4,z6])]],
   [[(0,[z0,z1,z2,z3,z4,z834]),(0,[z1,z12,z3,z4,z6,z581]),(0,[z835,z1,z2,z3,z4,z6]),(0,[z184,z1,z2,z3,z136,z6]),(0,[z836,z1,z2,z3,z4,z6])],[(0,[z0,z1,z837,z3,z4,z6]),(0,[z0,z1,z20,z3,z838,z6])],[(0,[z406,z0,z24,z3,z4,z6]),(0,[z839,z1,z2,z3,z4,z6]),(0,[z0,z1,z840,z3,z4,z6])],[(0,[z0,z2,z3,z4,z6,z841]),(0,[z1,z148,z2,z3,z46,z6]),(0,[z195,z1,z2,z3,z136,z6]),(0,[z0,z1,z2,z78,z338,z6]),(0,[z0,z1,z842,z3,z4,z6]),(0,[z0,z1,z2,z113,z263,z6])],[(0,[z692,z1,z12,z3,z4,z6]),(0,[z22,z0,z81,z3,z4,z6]),(0,[z199,z0,z21,z3,z4,z6]),(0,[z0,z24,z1,z280,z4,z6]),(0,[z0,z1,z843,z3,z4,z6])],[(0,[z0,z1,z2,z844,z4,z6]),(0,[z0,z1,z2,z3,z278,z41]),(0,[z845,z1,z2,z3,z4,z6])],[(0,[z186,z593,z12,z3,z4,z6]),(0,[z0,z1,z2,z846,z4,z6]),(0,[z847,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z848]),(0,[z0,z777,z1,z3,z4,z6]),(0,[z849,z1,z2,z3,z4,z6]),(0,[z0,z1,z3,z850,z74,z6])],[],[(0,[z0,z1,z303,z3,z203,z6]),(0,[z59,z1,z851,z3,z4,z6]),(0,[z852,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z354,z109,z4])],[(0,[z0,z1,z12,z315,z4,z6]),(0,[z186,z1,z12,z3,z132,z6]),(0,[z248,z1,z12,z3,z4,z6]),(0,[z0,z853,z2,z3,z4,z6]),(0,[z0,z1,z2,z141,z159,z6])],[(0,[z186,z133,z303,z3,z4,z6]),(0,[z0,z1,z2,z315,z4,z100]),(0,[z83,z1,z2,z80,z4,z6]),(1,[z0,z1,z2,z6,z790]),(0,[z0,z1,z2,z109,z50,z6])],[(0,[z0,z1,z92,z3,z4,z322]),(0,[z139,z0,z1,z2,z6,z790])],[(0,[z722,z133,z2,z3,z4,z6]),(0,[z0,z854,z2,z3,z4,z6])],[(0,[z0,z1,z2,z855,z4,z6])],[(0,[z0,z1,z20,z3,z856,z6]),(0,[z0,z70,z2,z3,z62,z6]),(0,[z0,z1,z243,z3,z4,z6]),(0,[z0,z352,z14,z3,z4,z6]),(0,[z195,z2,z3,z166,z4,z6]),(0,[z0,z1,z3,z786,z4,z6]),(0,[z145,z1,z3,z4,z6,z130]),(0,[z32,z37,z1,z3,z4,z130]),(0,[z0,z1,z2,z3,z4,z215])]],
   [[(0,[z186,z20,z133,z3,z4,z6]),(0,[z186,z1,z857,z3,z4,z6]),(0,[z1,z12,z3,z4,z42,z41]),(0,[z0,z858,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z74,z165]),(0,[z0,z1,z2,z3,z263,z131])],[(0,[z0,z1,z859,z3,z4,z6]),(0,[z0,z1,z2,z141,z140,z95])],[(0,[z0,z1,z860,z3,z4,z6]),(0,[z0,z1,z2,z3,z46,z165])],[(0,[z0,z1,z20,z315,z4,z6]),(0,[z0,z284,z2,z3,z4,z84]),(0,[z0,z1,z2,z861,z4,z6]),(0,[z184,z1,z379,z3,z4,z6]),(0,[z0,z1,z2,z3,z252,z23])],[(0,[z0,z133,z2,z315,z4,z6]),(0,[z186,z133,z2,z3,z132,z6]),(0,[z0,z1,z12,z3,z62,z6]),(0,[z862,z0,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z863]),(0,[z0,z737,z1,z3,z4,z6])],[(0,[z308,z1,z12,z3,z4,z6]),(0,[z297,z133,z2,z3,z4,z6]),(0,[z403,z0,z2,z3,z4,z23]),(0,[z607,z1,z12,z3,z4,z6]),(0,[z0,z284,z2,z3,z97,z6]),(0,[z0,z1,z2,z216,z4,z6]),(0,[z0,z1,z2,z3,z91,z47])],[(0,[z0,z1,z12,z3,z71,z6]),(0,[z0,z1,z2,z864,z4,z6])],[(0,[z0,z865,z20,z3,z4,z6]),(0,[z86,z286,z2,z3,z46,z6]),(0,[z0,z1,z2,z866,z4,z6]),(0,[z0,z1,z2,z354,z4,z47])],[(0,[z1,z857,z12,z3,z4,z6]),(0,[z30,z0,z2,z137,z15,z6])],[(0,[z0,z1,z2,z315,z4,z75]),(0,[z0,z1,z867,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z868]),(0,[z456,z1,z12,z3,z4,z6]),(0,[z0,z237,z355,z3,z4,z6]),(0,[z83,z1,z192,z80,z4,z6]),(0,[z0,z1,z2,z3,z9,z84])],[(0,[z0,z21,z25,z3,z4,z6]),(0,[z0,z1,z869,z3,z4,z6])],[(0,[z328,z1,z12,z3,z4,z41]),(0,[z870,z0,z1,z2,z4,z6]),(0,[z0,z1,z2,z3,z263,z165])],[(0,[z0,z2,z14,z315,z4,z6]),(0,[z0,z1,z2,z871,z4,z6]),(0,[z0,z1,z2,z3,z278,z6]),(0,[z32,z157,z1,z3,z4,z6]),(0,[z145,z1,z92,z3,z4,z6]),(0,[z0,z1,z2,z280,z252,z6])],[(0,[z0,z1,z20,z3,z62,z6]),(0,[z0,z1,z2,z323,z4,z370]),(0,[z0,z1,z2,z3,z238,z47]),(0,[z0,z225,z2,z3,z4,z29]),(1,[z0,z2,z3,z735,z6]),(0,[z0,z255,z2,z280,z4,z6]),(0,[z223,z0,z1,z2,z6,z107])],[(0,[z0,z872,z2,z3,z4,z6])],[(0,[z0,z1,z2,z873,z4,z6]),(0,[z1,z12,z3,z633,z4,z6]),(0,[z0,z1,z12,z113,z4,z6]),(0,[z0,z1,z120,z3,z4,z54]),(0,[z0,z1,z20,z3,z71,z6]),(0,[z0,z21,z53,z3,z4,z6]),(0,[z44,z0,z90,z55,z4,z6])]],
   [[(0,[z0,z1,z69,z3,z4,z337]),(0,[z0,z1,z874,z3,z4,z6])],[(0,[z0,z875,z2,z3,z4,z6]),(0,[z0,z225,z178,z3,z4,z6]),(0,[z0,z1,z876,z3,z4,z6])],[(0,[z0,z1,z2,z636,z4,z42])],[(1,[z722,z2,z3,z4,z6]),(0,[z0,z1,z877,z3,z4,z6]),(0,[z199,z0,z20,z3,z4,z878])],[(0,[z0,z1,z12,z3,z136,z6]),(0,[z0,z1,z879,z3,z4,z6]),(0,[z0,z148,z2,z323,z4,z6]),(0,[z0,z1,z2,z880,z4,z6]),(0,[z0,z1,z239,z137,z4,z6])],[(0,[z1,z12,z3,z645,z4,z6]),(0,[z67,z0,z12,z3,z4,z23]),(0,[z284,z2,z3,z80,z4,z6]),(0,[z0,z1,z2,z113,z49,z6]),(0,[z0,z1,z2,z3,z881,z6]),(0,[z184,z1,z882,z3,z4,z6]),(0,[z0,z1,z2,z380,z3,z65])],[(0,[z486,z1,z12,z3,z4,z6]),(0,[z0,z1,z2,z3,z883,z6]),(0,[z0,z884,z2,z3,z4,z6]),(0,[z0,z1,z14,z3,z4,z241])],[(0,[z1,z2,z3,z4,z885,z41])],[(0,[z0,z1,z2,z181,z4,z6]),(0,[z186,z1,z12,z3,z203,z6]),(0,[z0,z1,z20,z113,z4,z6]),(0,[z0,z70,z2,z163,z4,z6]),(0,[z67,z0,z2,z3,z4,z802])],[(0,[z0,z1,z20,z3,z4,z779]),(0,[z48,z148,z2,z3,z4,z6]),(0,[z0,z886,z2,z3,z4,z6])],[(0,[z0,z1,z851,z3,z4,z6]),(0,[z306,z1,z2,z3,z4,z6]),(0,[z0,z887,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z888]),(0,[z160,z1,z12,z3,z4,z6]),(0,[z1,z12,z3,z655,z4,z6]),(0,[z889,z0,z20,z3,z4,z6]),(0,[z0,z138,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z890]),(0,[z0,z1,z2,z6,z790,z107]),(0,[z0,z1,z2,z3,z50,z6])],[(0,[z153,z464,z2,z3,z4,z6]),(0,[z157,z1,z12,z3,z4,z6]),(0,[z0,z1,z2,z3,z891,z6]),(0,[z40,z1,z2,z3,z4,z577]),(0,[z85,z0,z1,z2,z6,z107]),(0,[z0,z1,z892,z3,z4,z6]),(0,[z0,z1,z2,z3,z893,z4])],[(0,[z0,z1,z12,z163,z4,z6]),(0,[z0,z1,z20,z3,z136,z6])],[(0,[z0,z1,z2,z894,z4,z6]),(0,[z0,z1,z895,z3,z4,z6]),(0,[z67,z0,z20,z3,z4,z23]),(0,[z0,z1,z2,z3,z896,z6])],[(0,[z1,z168,z12,z3,z4,z6]),(0,[z0,z1,z2,z323,z4,z6]),(0,[z0,z286,z2,z218,z4,z6]),(0,[z0,z1,z2,z897,z4,z6]),(0,[z0,z329,z2,z3,z4,z23]),(0,[z0,z1,z2,z3,z45,z559])]],
   [[(0,[z186,z14,z12,z3,z4,z6]),(0,[z1,z12,z3,z4,z533,z6]),(0,[z0,z329,z2,z3,z4,z6]),(0,[z0,z1,z2,z137,z4,z272])],[(0,[z0,z1,z2,z3,z898,z6]),(0,[z0,z1,z2,z88,z278,z6]),(0,[z0,z1,z2,z3,z154,z47])],[(0,[z186,z133,z2,z3,z203,z6])],[(0,[z1,z12,z3,z122,z46,z6]),(0,[z0,z1,z12,z3,z899,z6])],[(0,[z0,z1,z342,z3,z4,z6]),(0,[z160,z1,z20,z3,z4,z6]),(0,[z0,z104,z2,z3,z4,z241]),(0,[z0,z1,z2,z900,z4,z6])],[(0,[z126,z133,z2,z3,z4,z6]),(0,[z157,z1,z20,z3,z4,z6]),(0,[z22,z0,z777,z3,z4,z6]),(0,[z0,z1,z2,z901,z4,z6]),(0,[z0,z1,z2,z280,z4,z28])],[(0,[z0,z1,z20,z163,z4,z6]),(0,[z0,z1,z902,z3,z4,z6]),(0,[z0,z1,z2,z3,z33,z6])],[(0,[z0,z1,z12,z3,z4,z165]),(1,[z0,z2,z3,z4,z802]),(0,[z0,z1,z2,z3,z365,z47]),(0,[z0,z1,z903,z3,z4,z6])],[(0,[z0,z1,z904,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z905])],[(0,[z153,z19,z2,z3,z4,z6]),(0,[z668,z0,z2,z3,z15,z6]),(0,[z0,z90,z2,z3,z4,z559])],[(0,[z0,z248,z21,z3,z4,z6])],[(0,[z86,z1,z2,z3,z46,z370]),(0,[z0,z352,z1,z3,z4,z23]),(0,[z0,z1,z2,z3,z4,z906]),(0,[z0,z1,z436,z3,z4,z54])],[(0,[z0,z352,z1,z3,z4,z6]),(0,[z0,z2,z907,z166,z4,z6])],[(0,[z0,z19,z2,z3,z4,z100]),(0,[z0,z1,z2,z3,z49,z165])],[(0,[z145,z1,z2,z280,z4,z6]),(0,[z0,z1,z908,z3,z4,z6])],[(0,[z0,z1,z12,z909,z3,z4]),(0,[z210,z1,z12,z3,z4,z6]),(0,[z40,z1,z287,z3,z4,z29]),(0,[z910,z0,z191,z3,z4,z6]),(0,[z0,z1,z92,z3,z4,z233])]],
   [[(0,[z0,z1,z2,z3,z911,z6]),(0,[z0,z1,z20,z3,z4,z165]),(0,[z0,z237,z2,z3,z4,z264])],[(0,[z0,z237,z2,z3,z97,z6]),(0,[z912,z1,z2,z3,z4,z6]),(0,[z184,z1,z446,z3,z4,z6]),(0,[z0,z1,z2,z3,z850,z6])],[(0,[z86,z148,z2,z3,z46,z6]),(0,[z913,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z599,z4,z42])],[(0,[z0,z237,z2,z3,z9,z6]),(0,[z311,z1,z2,z3,z46,z6]),(0,[z0,z1,z2,z914,z4,z6]),(0,[z0,z1,z178,z3,z62,z6]),(0,[z195,z1,z915,z3,z4,z6]),(0,[z0,z1,z2,z3,z916,z6]),(0,[z242,z1,z917,z3,z4,z6]),(0,[z0,z1,z2,z642,z3,z65])],[(0,[z0,z1,z2,z3,z918,z6]),(0,[z0,z1,z12,z3,z45,z6])],[(0,[z186,z12,z204,z3,z4,z6]),(0,[z1,z12,z3,z109,z4,z41]),(0,[z0,z1,z2,z919,z4,z6])],[(0,[z0,z1,z20,z3,z920,z6]),(0,[z921,z1,z2,z3,z4,z6])],[(0,[z0,z922,z2,z3,z4,z6]),(0,[z676,z1,z12,z3,z4,z6]),(0,[z0,z923,z2,z3,z4,z6]),(0,[z0,z924,z20,z3,z4,z6]),(0,[z0,z1,z2,z117,z4,z215])],[(0,[z0,z1,z925,z3,z4,z6]),(0,[z251,z0,z2,z166,z4,z6]),(0,[z32,z0,z1,z3,z4,z926])],[(0,[z19,z722,z2,z3,z4,z6]),(0,[z68,z1,z12,z80,z4,z6]),(0,[z0,z1,z927,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z928]),(0,[z160,z1,z734,z3,z4,z6]),(0,[z487,z0,z2,z3,z4,z23]),(0,[z306,z1,z256,z3,z4,z6])],[(0,[z0,z1,z191,z3,z4,z6])],[(0,[z1,z256,z12,z3,z4,z6]),(0,[z0,z929,z12,z3,z4,z6]),(0,[z0,z21,z3,z4,z537,z6]),(0,[z0,z1,z930,z3,z4,z6])],[(0,[z0,z1,z2,z931,z4,z6]),(0,[z1,z316,z3,z80,z4,z6]),(0,[z0,z2,z3,z735,z15,z6])],[(0,[z0,z1,z2,z3,z4,z932]),(0,[z0,z1,z20,z3,z45,z6]),(0,[z86,z1,z2,z3,z46,z6]),(0,[z362,z0,z1,z2,z6,z107]),(0,[z0,z1,z2,z95,z6,z790])],[(0,[z0,z1,z2,z933,z4,z6]),(0,[z0,z90,z12,z3,z4,z6]),(0,[z44,z0,z1,z55,z4,z6])],[(0,[z0,z1,z934,z3,z4,z6]),(0,[z68,z0,z1,z2,z590,z4]),(0,[z0,z1,z243,z3,z4,z272]),(0,[z0,z1,z2,z503,z6,z107])]],
   [[(0,[z0,z1,z12,z935,z3,z4]),(0,[z0,z1,z2,z3,z4,z936]),(0,[z0,z937,z2,z3,z4,z6])],[(0,[z18,z1,z12,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z938]),(0,[z0,z1,z2,z939,z4,z6]),(0,[z0,z1,z2,z3,z4,z940]),(0,[z210,z2,z14,z3,z4,z6]),(0,[z0,z617,z14,z3,z4,z6]),(0,[z0,z1,z2,z152,z71,z6])],[(0,[z0,z1,z941,z3,z4,z6]),(0,[z0,z1,z2,z3,z942,z4]),(0,[z0,z1,z2,z490,z144,z6])],[(0,[z0,z284,z12,z3,z4,z6]),(0,[z0,z623,z2,z152,z4,z6]),(0,[z0,z148,z2,z3,z4,z370]),(0,[z0,z1,z2,z218,z4,z370]),(0,[z73,z0,z105,z3,z74,z6])],[(0,[z39,z1,z12,z3,z4,z6]),(0,[z0,z1,z120,z3,z4,z147]),(0,[z0,z943,z2,z3,z4,z6]),(0,[z242,z1,z2,z3,z4,z35])],[(0,[z56,z1,z12,z3,z4,z6]),(0,[z0,z944,z20,z3,z4,z6]),(0,[z0,z1,z2,z3,z945,z4]),(0,[z0,z207,z2,z3,z4,z559]),(0,[z518,z0,z1,z3,z74,z6])],[(0,[z1,z12,z3,z488,z4,z6]),(0,[z0,z1,z12,z3,z4,z264]),(0,[z94,z0,z1,z55,z4,z6]),(0,[z123,z184,z2,z166,z4,z6]),(0,[z0,z1,z946,z3,z4,z6]),(0,[z947,z1,z2,z3,z4,z6])],[(0,[z0,z1,z342,z315,z4,z6]),(0,[z0,z1,z948,z3,z4,z6]),(0,[z387,z1,z2,z3,z4,z6]),(0,[z0,z90,z20,z3,z4,z6])],[(0,[z0,z20,z949,z3,z4,z6]),(0,[z83,z1,z2,z813,z4,z6]),(0,[z374,z1,z2,z80,z4,z6]),(0,[z0,z1,z2,z163,z4,z29])],[(0,[z0,z1,z12,z3,z9,z6]),(0,[z405,z0,z1,z3,z514,z6]),(0,[z37,z1,z12,z3,z4,z6]),(0,[z195,z1,z379,z3,z4,z6])],[(0,[z0,z1,z2,z3,z97,z84]),(0,[z0,z148,z2,z218,z4,z6]),(0,[z0,z1,z2,z950,z4,z6]),(0,[z0,z1,z2,z55,z50,z6])],[(0,[z546,z1,z12,z3,z4,z6]),(0,[z0,z951,z20,z3,z4,z6]),(0,[z199,z0,z2,z3,z4,z779]),(0,[z952,z1,z2,z3,z4,z6])],[(0,[z0,z284,z20,z3,z4,z6]),(0,[z0,z1,z2,z52,z4,z215]),(0,[z0,z1,z2,z3,z46,z337]),(0,[z0,z1,z178,z163,z4,z6]),(0,[z0,z1,z2,z3,z4,z953]),(0,[z954,z1,z2,z3,z4,z6]),(0,[z0,z955,z1,z3,z4,z6])],[(0,[z956,z0,z2,z3,z4,z6])],[(0,[z0,z1,z303,z3,z4,z100]),(0,[z0,z1,z2,z3,z4,z370]),(0,[z44,z0,z1,z55,z338,z6])],[(0,[z0,z1,z2,z3,z4,z957]),(0,[z0,z1,z20,z3,z4,z264]),(0,[z0,z1,z2,z171,z4,z6])]],
   [[(0,[z0,z1,z2,z3,z4,z958]),(0,[z444,z1,z2,z3,z4,z313])],[(1,[z1,z12,z3,z203,z6]),(0,[z0,z1,z2,z959,z4,z6]),(0,[z102,z1,z12,z3,z4,z6]),(0,[z0,z1,z2,z166,z71,z6]),(0,[z0,z104,z2,z3,z4,z28]),(0,[z289,z1,z2,z3,z4,z638]),(0,[z0,z960,z2,z3,z4,z6])],[(0,[z308,z133,z2,z3,z4,z6]),(0,[z0,z1,z20,z3,z9,z6]),(0,[z30,z160,z2,z3,z15,z6]),(0,[z583,z0,z1,z55,z4,z6]),(0,[z0,z1,z2,z3,z252,z130])],[(0,[z0,z961,z20,z3,z4,z6]),(0,[z0,z962,z2,z3,z4,z6]),(0,[z963,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z964,z4,z6]),(0,[z73,z0,z1,z3,z850,z6]),(0,[z0,z1,z2,z117,z50,z6]),(0,[z0,z1,z2,z112,z3,z780])],[(0,[z0,z1,z12,z3,z4,z313]),(0,[z0,z225,z2,z3,z4,z41]),(0,[z0,z1,z965,z3,z4,z6])],[(0,[z0,z148,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z966]),(0,[z0,z1,z2,z218,z4,z6]),(0,[z910,z0,z2,z3,z4,z6])],[(0,[z0,z1,z12,z3,z132,z6])],[(0,[z0,z1,z2,z3,z132,z100]),(0,[z73,z0,z1,z3,z537,z6]),(0,[z0,z1,z2,z967,z4,z6]),(0,[z0,z1,z77,z3,z278,z6]),(0,[z387,z1,z2,z3,z338,z6]),(0,[z0,z1,z2,z3,z4,z968])],[(0,[z0,z1,z2,z3,z969,z6]),(0,[z614,z0,z1,z2,z6,z107]),(0,[z0,z1,z2,z3,z4,z970]),(0,[z44,z0,z1,z55,z4,z36])],[(0,[z492,z0,z2,z166,z4,z6]),(0,[z0,z1,z2,z971,z3,z4]),(0,[z0,z1,z972,z3,z4,z6])],[(0,[z0,z1,z2,z973,z4,z6]),(0,[z0,z207,z12,z3,z4,z6]),(0,[z0,z225,z2,z3,z278,z6])],[(0,[z0,z1,z2,z3,z4,z974]),(1,[z133,z2,z3,z203,z6]),(0,[z59,z1,z12,z80,z4,z6]),(0,[z1,z851,z12,z3,z4,z6]),(0,[z0,z1,z2,z3,z975,z6]),(0,[z0,z286,z2,z3,z4,z370]),(0,[z0,z2,z3,z907,z4,z6])],[(0,[z643,z1,z12,z3,z4,z6]),(0,[z0,z1,z976,z3,z4,z6]),(0,[z0,z1,z2,z977,z4,z6]),(0,[z123,z0,z12,z166,z4,z6]),(0,[z0,z1,z2,z978,z4,z6]),(0,[z0,z1,z2,z55,z338,z6])],[(0,[z0,z1,z20,z3,z4,z313]),(0,[z0,z1,z2,z3,z979,z6]),(0,[z0,z1,z2,z3,z980,z6]),(0,[z981,z1,z2,z3,z4,z6]),(0,[z30,z242,z2,z3,z15,z6])],[(0,[z142,z1,z342,z3,z4,z6]),(0,[z364,z1,z12,z3,z4,z6]),(0,[z0,z1,z2,z3,z252,z54]),(0,[z0,z1,z2,z3,z38,z165])],[(0,[z0,z1,z20,z3,z132,z6]),(0,[z1,z12,z3,z4,z41,z23]),(0,[z0,z1,z2,z3,z982,z6]),(0,[z0,z1,z2,z3,z4,z983]),(0,[z0,z1,z2,z263,z109,z107])]],
   [[(0,[z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z20,z984,z4,z6])],[(0,[z387,z1,z2,z3,z4,z36]),(0,[z0,z1,z2,z3,z263,z47])],[(0,[z0,z58,z12,z3,z122,z6]),(0,[z0,z1,z2,z3,z801,z6]),(0,[z32,z0,z1,z3,z4,z532]),(0,[z0,z1,z2,z3,z4,z985])],[(0,[z0,z1,z2,z3,z4,z986]),(0,[z128,z1,z12,z3,z4,z6]),(0,[z0,z207,z20,z3,z4,z6]),(0,[z0,z1,z2,z3,z987,z6]),(0,[z0,z531,z14,z3,z4,z6]),(0,[z0,z1,z988,z3,z4,z6]),(0,[z0,z1,z2,z3,z146,z47])],[(0,[z0,z1,z989,z3,z4,z6])],[(0,[z123,z0,z20,z166,z4,z6]),(0,[z0,z191,z884,z3,z4,z6]),(0,[z990,z1,z2,z3,z4,z6])],[(0,[z1,z191,z12,z3,z4,z6]),(0,[z0,z991,z2,z3,z4,z6]),(0,[z0,z992,z2,z3,z4,z6]),(0,[z993,z1,z2,z3,z4,z6])],[(0,[z48,z1,z12,z3,z46,z6]),(0,[z0,z1,z2,z3,z4,z994]),(0,[z160,z1,z2,z137,z4,z6])],[(0,[z0,z1,z177,z323,z4,z6]),(0,[z0,z1,z2,z995,z4,z6]),(0,[z22,z0,z352,z3,z4,z6]),(0,[z0,z352,z104,z3,z4,z28]),(0,[z289,z1,z2,z490,z4,z6]),(0,[z0,z105,z3,z4,z74,z6])],[(0,[z554,z1,z12,z3,z4,z6]),(0,[z0,z1,z12,z3,z4,z996]),(0,[z0,z949,z2,z3,z4,z6])],[(0,[z997,z1,z2,z3,z4,z6])],[(0,[z0,z58,z20,z3,z122,z6]),(0,[z0,z329,z2,z280,z4,z6])],[(0,[z0,z58,z2,z3,z89,z6])],[(0,[z0,z286,z2,z3,z4,z6]),(0,[z186,z1,z12,z3,z4,z100]),(0,[z662,z1,z12,z3,z4,z6]),(0,[z48,z1,z177,z3,z4,z6]),(0,[z0,z1,z2,z998,z4,z6]),(0,[z0,z1,z14,z3,z252,z6]),(0,[z0,z1,z2,z3,z999,z6]),(0,[z306,z1,z2,z3,z338,z6])],[(0,[z81,z19,z2,z3,z4,z6]),(0,[z0,z1,z192,z3,z4,z6]),(0,[z0,z1,z2,z3,z144,z638])],[(0,[z0,z1,z1000,z3,z4,z6]),(0,[z0,z1,z1001,z3,z4,z6]),(0,[z0,z1,z2,z3,z1002,z4]),(0,[z0,z1,z2,z3,z4,z179])]],
   [[(0,[z0,z1,z2,z3,z338,z6]),(0,[z0,z1,z2,z3,z118,z47])],[(0,[z153,z1,z2,z3,z203,z6]),(0,[z394,z1,z12,z3,z4,z6]),(0,[z59,z1,z2,z545,z4,z6]),(0,[z0,z1,z2,z3,z4,z1003]),(0,[z0,z1,z2,z280,z33,z6])],[(0,[z0,z237,z2,z3,z4,z84]),(0,[z0,z695,z14,z3,z4,z6]),(1,[z0,z1,z3,z4,z926]),(0,[z0,z1,z2,z3,z135,z4])],[(0,[z554,z133,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z827,z6])],[(0,[z0,z1,z2,z3,z4,z1004]),(0,[z0,z1,z12,z3,z203,z6]),(0,[z231,z1,z12,z3,z4,z6]),(0,[z142,z1,z191,z3,z4,z6]),(0,[z0,z1,z1005,z3,z4,z6])],[(0,[z0,z1,z53,z121,z4,z6]),(0,[z0,z1,z2,z88,z4,z6]),(0,[z22,z0,z470,z3,z4,z6]),(0,[z0,z1006,z2,z3,z4,z6])],[(0,[z186,z133,z12,z3,z4,z6]),(0,[z37,z1,z2,z3,z252,z6])],[(0,[z1,z120,z12,z3,z4,z41]),(0,[z242,z1,z12,z3,z4,z6]),(0,[z0,z1007,z2,z3,z4,z6]),(0,[z1008,z1,z2,z3,z4,z6]),(0,[z195,z1,z446,z3,z4,z6]),(0,[z30,z0,z2,z171,z15,z6]),(0,[z306,z1,z2,z3,z4,z36]),(0,[z37,z255,z2,z3,z4,z6]),(0,[z37,z1,z2,z216,z4,z6])],[(0,[z1,z2,z12,z3,z4,z100]),(0,[z1009,z0,z168,z3,z4,z6]),(0,[z0,z1,z2,z505,z3,z65])],[(0,[z0,z722,z2,z3,z4,z6]),(0,[z0,z1010,z2,z3,z4,z6]),(0,[z0,z574,z14,z3,z4,z6]),(0,[z30,z0,z239,z3,z15,z6]),(0,[z68,z0,z1,z2,z4,z513]),(0,[z0,z1,z2,z3,z263,z640])],[(0,[z40,z1,z12,z3,z4,z29]),(0,[z0,z150,z21,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z36]),(0,[z0,z1,z2,z141,z95,z6]),(0,[z0,z1,z1011,z3,z4,z6])],[(0,[z186,z1,z12,z3,z4,z75]),(0,[z1,z331,z12,z80,z4,z6]),(0,[z199,z0,z14,z3,z4,z6]),(0,[z160,z1,z843,z3,z4,z6]),(0,[z444,z1,z25,z3,z4,z6])],[(0,[z210,z1,z342,z3,z4,z6]),(0,[z0,z1,z12,z3,z4,z1012]),(0,[z0,z1,z2,z3,z4,z1013])],[(0,[z0,z1,z20,z3,z203,z6])],[(0,[z0,z1,z2,z3,z1014,z6]),(0,[z683,z0,z2,z3,z4,z23]),(0,[z289,z1,z12,z3,z4,z6]),(0,[z0,z1015,z2,z3,z4,z6])],[(0,[z186,z1,z316,z3,z4,z6]),(0,[z0,z1,z2,z3,z856,z6]),(0,[z1016,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z780,z47])]],
   [[(0,[z1,z12,z112,z3,z46,z6]),(0,[z242,z1,z20,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z1017]),(0,[z1,z77,z3,z4,z6,z41]),(0,[z0,z1,z1018,z3,z4,z6])],[(0,[z1,z442,z12,z3,z4,z6]),(0,[z0,z1,z2,z490,z4,z313])],[(0,[z644,z0,z2,z166,z4,z6]),(0,[z22,z0,z24,z3,z4,z497]),(0,[z0,z1,z2,z3,z4,z1019])],[(0,[z0,z1,z2,z315,z4,z6]),(0,[z40,z1,z20,z3,z4,z29]),(0,[z87,z70,z2,z3,z4,z41]),(0,[z0,z1,z2,z3,z4,z1020]),(0,[z22,z0,z24,z3,z4,z241]),(0,[z0,z1,z239,z171,z4,z6]),(0,[z1021,z1,z2,z3,z4,z6]),(0,[z32,z0,z255,z3,z4,z130]),(0,[z0,z1,z2,z564,z6,z107])],[(0,[z0,z1,z1022,z3,z4,z6]),(0,[z584,z0,z1,z3,z74,z6]),(0,[z0,z2,z3,z4,z6,z802]),(0,[z0,z1,z1023,z3,z4,z6])],[(0,[z0,z1,z718,z3,z4,z6]),(0,[z0,z1,z2,z628,z95,z6]),(0,[z0,z114,z379,z3,z4,z6]),(0,[z663,z0,z1,z2,z109,z4])],[(0,[z0,z1,z2,z3,z1024,z6]),(0,[z1,z284,z2,z80,z4,z6]),(0,[z83,z1,z355,z80,z4,z6]),(0,[z86,z1,z177,z3,z46,z6]),(0,[z242,z1,z821,z3,z4,z6]),(0,[z160,z1,z243,z3,z4,z6])],[(0,[z478,z1,z12,z3,z4,z6]),(0,[z1,z20,z12,z3,z4,z6]),(0,[z0,z1,z1025,z3,z4,z6])],[(0,[z0,z1,z12,z3,z4,z84]),(0,[z87,z1,z12,z3,z4,z41]),(0,[z0,z1,z2,z3,z1026,z6]),(0,[z30,z0,z2,z3,z15,z6])],[(0,[z0,z2,z152,z907,z4,z6]),(0,[z0,z58,z239,z3,z4,z6]),(0,[z0,z1,z2,z1027,z4,z6])],[(0,[z0,z1,z12,z3,z97,z6]),(0,[z0,z1,z12,z3,z4,z1028]),(0,[z44,z306,z1,z55,z4,z6]),(0,[z0,z1,z2,z3,z338,z36]),(0,[z0,z1,z2,z1029,z4,z6]),(0,[z0,z1,z2,z354,z65,z4])],[(0,[z0,z1,z2,z3,z1030,z6]),(0,[z0,z1031,z2,z3,z4,z6])],[(0,[z59,z1,z2,z52,z4,z6]),(0,[z0,z1,z2,z3,z1032,z6]),(0,[z358,z0,z1,z2,z6,z107])],[(0,[z0,z1,z2,z3,z62,z6]),(0,[z0,z1,z1033,z3,z4,z6]),(0,[z0,z1,z2,z117,z4,z42]),(0,[z0,z1,z1034,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z1035]),(0,[z0,z58,z2,z3,z209,z6])],[(0,[z0,z1,z2,z163,z4,z41]),(0,[z145,z1,z14,z3,z4,z6]),(0,[z0,z1,z2,z171,z4,z272]),(0,[z1036,z1,z2,z3,z4,z6])]],
   [[(0,[z0,z1037,z12,z3,z4,z6]),(0,[z0,z1,z2,z3,z1038,z6]),(0,[z0,z1,z53,z78,z4,z6]),(0,[z0,z1,z2,z3,z1039,z4]),(0,[z0,z1,z1040,z3,z4,z6]),(0,[z0,z1,z2,z1041,z4,z6])],[(0,[z22,z0,z2,z3,z203,z6]),(0,[z1,z12,z3,z4,z6,z327]),(0,[z0,z1,z20,z3,z4,z84]),(0,[z87,z1,z20,z3,z4,z41]),(0,[z0,z105,z2,z3,z4,z313]),(0,[z0,z1042,z2,z3,z4,z6])],[(0,[z133,z2,z3,z4,z203,z6]),(0,[z0,z1,z1043,z3,z4,z6]),(0,[z199,z1,z12,z3,z4,z6]),(0,[z1,z12,z3,z4,z335,z6]),(0,[z0,z1,z2,z3,z1044,z6]),(0,[z289,z1,z2,z174,z4,z6]),(0,[z73,z0,z1,z3,z74,z313]),(0,[z37,z329,z2,z3,z4,z6]),(0,[z0,z1,z2,z141,z135,z95])],[(0,[z1,z133,z2,z315,z4,z6]),(0,[z1,z12,z3,z339,z4,z6]),(0,[z0,z1,z20,z3,z97,z6]),(0,[z199,z0,z2,z3,z4,z878]),(0,[z0,z104,z2,z3,z4,z802]),(0,[z0,z1,z1045,z3,z4,z6])],[(0,[z0,z11,z204,z3,z4,z6]),(0,[z0,z1,z239,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z1046]),(0,[z0,z114,z12,z152,z4,z6]),(0,[z0,z1,z12,z3,z4,z35]),(0,[z0,z1,z12,z354,z4,z6]),(0,[z0,z1,z2,z163,z278,z6])],[(0,[z0,z21,z12,z3,z4,z6]),(0,[z0,z1,z1047,z3,z4,z6]),(0,[z0,z1048,z2,z3,z4,z6])],[(0,[z0,z1,z12,z1049,z4,z6]),(0,[z0,z1,z177,z3,z4,z370]),(0,[z123,z0,z2,z907,z4,z6])],[(0,[z546,z133,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z781,z4]),(0,[z1050,z1,z2,z3,z4,z6]),(0,[z37,z1,z2,z3,z33,z6]),(0,[z0,z1,z2,z3,z4,z1051]),(0,[z0,z1,z2,z113,z4,z6])],[(0,[z0,z1,z2,z3,z4,z1052]),(0,[z0,z1,z2,z1053,z4,z6]),(0,[z0,z1054,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z1055,z6])],[(0,[z19,z1,z316,z3,z4,z6])],[(0,[z48,z1,z2,z3,z570,z6]),(0,[z0,z1,z1056,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z1057])],[(0,[z0,z1,z12,z3,z1058,z6]),(0,[z493,z1,z12,z3,z4,z6]),(0,[z0,z256,z21,z3,z4,z6]),(0,[z0,z1,z1059,z3,z4,z6])],[(0,[z0,z114,z20,z152,z4,z6]),(0,[z0,z1,z20,z3,z4,z35]),(0,[z0,z1,z20,z354,z4,z6]),(0,[z0,z148,z177,z3,z4,z6]),(0,[z0,z1,z177,z218,z4,z6]),(0,[z0,z1,z2,z3,z1060,z6]),(0,[z67,z0,z2,z3,z4,z23]),(0,[z0,z1,z2,z1061,z4,z6])],[(0,[z0,z1,z303,z3,z4,z75]),(0,[z0,z1,z857,z3,z4,z6]),(0,[z48,z1,z316,z3,z4,z6]),(0,[z1,z2,z3,z4,z6,z885]),(0,[z0,z1,z681,z3,z4,z54])]],
   [[(0,[z0,z1,z2,z3,z4,z1062]),(0,[z0,z1,z2,z3,z4,z272])],[(0,[z0,z1,z2,z3,z1063,z6]),(0,[z405,z1,z12,z3,z46,z6]),(0,[z0,z1,z2,z3,z4,z319])],[(0,[z58,z19,z12,z3,z4,z6]),(0,[z0,z1,z2,z340,z4,z42]),(0,[z0,z1,z2,z1064,z4,z6])],[(0,[z0,z1,z1065,z3,z4,z6]),(0,[z1066,z1,z2,z3,z4,z6])],[(0,[z153,z19,z316,z3,z4,z6]),(0,[z184,z1,z12,z3,z4,z6]),(0,[z1,z12,z3,z4,z198,z6]),(0,[z0,z1,z20,z3,z4,z878]),(0,[z0,z1,z2,z80,z4,z215]),(0,[z0,z1067,z2,z3,z4,z6])],[(0,[z32,z0,z1,z3,z4,z200]),(0,[z0,z1,z2,z1068,z4,z6])],[(0,[z1,z12,z3,z4,z203,z6]),(1,[z1,z12,z3,z4,z100]),(0,[z1,z12,z3,z4,z6,z375]),(0,[z1,z12,z3,z4,z377,z6]),(0,[z0,z1,z2,z163,z4,z6]),(0,[z44,z387,z1,z55,z4,z6]),(0,[z0,z1,z2,z135,z4,z107])],[(0,[z0,z1,z2,z1069,z4,z6])],[(0,[z0,z1,z2,z3,z132,z75])],[(0,[z1,z12,z3,z4,z213,z6]),(0,[z0,z1,z177,z3,z4,z6]),(0,[z561,z1,z12,z3,z4,z6]),(0,[z0,z1,z2,z3,z1070,z6])],[(0,[z83,z284,z2,z80,z4,z6]),(0,[z0,z1,z2,z280,z4,z23]),(0,[z0,z1,z786,z55,z4,z6]),(0,[z0,z1,z2,z112,z3,z129])],[(0,[z1,z12,z3,z219,z4,z6]),(0,[z0,z1,z77,z3,z4,z6]),(0,[z0,z1,z20,z1071,z4,z6]),(0,[z0,z1,z2,z52,z50,z6]),(0,[z0,z1,z2,z280,z4,z6]),(0,[z0,z1,z2,z174,z4,z313])],[(0,[z37,z1,z191,z3,z4,z6]),(0,[z0,z1,z1072,z3,z4,z6]),(0,[z32,z0,z329,z3,z4,z130]),(0,[z0,z1,z2,z3,z140,z95]),(1,[z0,z1,z2,z3,z780])],[(0,[z0,z1,z2,z3,z4,z1073]),(0,[z184,z1,z20,z3,z4,z6]),(0,[z83,z1,z2,z80,z4,z264]),(0,[z0,z1074,z2,z3,z4,z6])],[(0,[z0,z225,z2,z3,z4,z6]),(0,[z83,z1,z2,z80,z97,z6]),(0,[z0,z1,z2,z1075,z4,z6]),(0,[z444,z1,z2,z490,z4,z6])],[(0,[z0,z1,z2,z621,z4,z42])]],
   [[(0,[z1,z342,z12,z3,z4,z6]),(0,[z1,z12,z232,z3,z4,z6]),(0,[z83,z1,z2,z80,z9,z6])],[(0,[z417,z1,z12,z3,z4,z6]),(0,[z0,z1,z1076,z3,z4,z6])],[(0,[z0,z237,z12,z3,z4,z6]),(0,[z1,z1077,z12,z3,z4,z6])],[(0,[z87,z1,z2,z3,z4,z885]),(1,[z0,z1,z786,z4,z6])],[(0,[z0,z1,z12,z3,z4,z337]),(0,[z1,z12,z3,z415,z4,z6]),(0,[z139,z0,z1,z20,z6,z107]),(0,[z0,z1,z2,z3,z838,z6]),(0,[z0,z812,z2,z3,z4,z6]),(0,[z123,z195,z2,z166,z4,z6]),(0,[z583,z0,z1,z3,z4,z130]),(0,[z0,z1,z2,z3,z38,z47]),(0,[z0,z1,z2,z3,z780,z4])],[(0,[z405,z0,z1,z3,z74,z6])],[(0,[z0,z21,z3,z4,z322,z6]),(0,[z0,z1,z2,z3,z920,z6]),(0,[z0,z1078,z2,z3,z4,z6]),(0,[z0,z286,z177,z3,z4,z6]),(0,[z0,z1,z1079,z3,z4,z6]),(0,[z0,z225,z77,z3,z4,z6]),(0,[z0,z1,z1080,z3,z4,z6])],[(0,[z0,z1,z1081,z3,z4,z6]),(0,[z1,z12,z3,z46,z6,z107]),(0,[z0,z924,z2,z3,z4,z6]),(0,[z87,z1,z178,z3,z4,z41]),(0,[z0,z1,z2,z3,z74,z638])],[(0,[z210,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z203,z100]),(0,[z0,z1,z1082,z3,z4,z6]),(0,[z114,z19,z12,z3,z4,z6]),(0,[z0,z1,z2,z909,z3,z4]),(0,[z175,z1,z2,z52,z4,z6]),(0,[z0,z266,z1083,z3,z4,z6]),(0,[z0,z1084,z2,z3,z4,z6])],[],[(0,[z186,z133,z2,z3,z4,z100]),(0,[z59,z1,z316,z3,z4,z6]),(0,[z0,z1,z2,z3,z49,z337]),(0,[z0,z24,z329,z3,z4,z6]),(0,[z0,z211,z2,z3,z122,z6]),(0,[z0,z1,z1085,z3,z4,z6]),(0,[z306,z1,z2,z3,z45,z6]),(0,[z0,z1,z2,z3,z1086,z6]),(0,[z0,z1087,z2,z3,z4,z6])],[(0,[z0,z237,z20,z3,z4,z6]),(0,[z289,z105,z2,z3,z4,z6])],[(0,[z1,z12,z3,z267,z4,z6]),(0,[z306,z1,z3,z55,z4,z6]),(0,[z1088,z1,z2,z3,z4,z6])],[(0,[z142,z1,z2,z315,z4,z6]),(0,[z0,z1,z20,z3,z4,z337]),(0,[z0,z1,z247,z3,z4,z6]),(0,[z0,z1,z2,z1089,z3,z6]),(0,[z0,z1,z2,z3,z4,z1090]),(0,[z0,z1,z2,z354,z4,z215])],[(0,[z133,z2,z3,z315,z4,z6]),(0,[z0,z1,z2,z3,z4,z1091]),(0,[z0,z150,z14,z3,z4,z6])],[(0,[z0,z1,z53,z786,z4,z6])]],
   [[(0,[z1,z12,z3,z4,z6,z277]),(0,[z0,z1,z77,z88,z4,z6]),(0,[z0,z1,z2,z3,z4,z1092])],[(0,[z0,z133,z2,z3,z203,z6]),(0,[z1093,z1,z2,z3,z4,z6])],[(0,[z246,z19,z2,z3,z4,z6]),(0,[z462,z1,z12,z3,z4,z6]),(0,[z289,z138,z2,z3,z4,z6])],[(0,[z0,z1,z1094,z3,z4,z6]),(0,[z0,z1,z20,z1095,z4,z6]),(0,[z0,z225,z2,z88,z4,z6]),(0,[z242,z1,z2,z137,z4,z6]),(0,[z0,z1096,z2,z3,z4,z6]),(0,[z0,z1097,z2,z3,z4,z6]),(0,[z1098,z1,z2,z3,z4,z6])],[(0,[z520,z1,z2,z3,z46,z6]),(0,[z444,z1,z12,z3,z4,z6]),(0,[z0,z929,z2,z3,z4,z6]),(0,[z0,z1,z1099,z3,z4,z6]),(0,[z306,z90,z2,z3,z4,z6])],[(0,[z1,z12,z3,z4,z28,z41]),(0,[z0,z944,z2,z3,z4,z6]),(0,[z1100,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z203,z75])],[(0,[z0,z90,z2,z3,z4,z6]),(0,[z1101,z1,z2,z3,z4,z6])],[(0,[z186,z133,z2,z3,z4,z75]),(0,[z30,z0,z2,z3,z15,z272])],[(0,[z0,z2,z14,z3,z203,z6]),(0,[z0,z1,z2,z1102,z4,z6]),(0,[z328,z0,z1,z3,z4,z130]),(0,[z0,z1,z2,z935,z3,z4]),(0,[z0,z1103,z2,z3,z4,z6])],[(0,[z0,z1,z266,z3,z4,z6]),(0,[z618,z1,z12,z3,z4,z6]),(0,[z0,z865,z2,z3,z4,z6]),(0,[z59,z1,z355,z3,z4,z6]),(0,[z311,z1,z2,z3,z4,z41])],[(0,[z0,z104,z2,z3,z4,z187]),(0,[z0,z951,z2,z3,z4,z6])],[(0,[z0,z1,z1104,z3,z4,z6]),(0,[z0,z329,z14,z3,z4,z6]),(0,[z1105,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z141,z517,z6])],[(0,[z464,z1,z12,z3,z4,z6]),(0,[z444,z1,z20,z3,z4,z6]),(0,[z0,z1,z20,z3,z4,z1106]),(0,[z0,z1,z2,z3,z4,z1107]),(0,[z1108,z1,z2,z3,z4,z6]),(0,[z0,z1109,z2,z3,z4,z6])],[(0,[z0,z1,z2,z490,z74,z6])],[(0,[z0,z1,z12,z1110,z4,z6]),(0,[z479,z1,z12,z3,z4,z6]),(0,[z0,z1,z1111,z3,z4,z6])]],
   [[(0,[z1,z12,z3,z65,z4,z41]),(0,[z0,z1,z1112,z3,z4,z6]),(0,[z0,z239,z3,z4,z15,z6])],[(0,[z0,z1,z303,z181,z4,z6]),(0,[z0,z1,z2,z1113,z4,z6]),(0,[z397,z1,z12,z3,z4,z6]),(0,[z0,z1,z2,z3,z604,z47])],[(0,[z1,z12,z3,z315,z4,z6]),(0,[z37,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z71,z6]),(0,[z10,z0,z1,z2,z6,z107]),(0,[z0,z1,z2,z3,z4,z1114]),(0,[z73,z444,z1,z3,z74,z6]),(0,[z0,z1,z1115,z3,z4,z6])],[(0,[z1,z12,z3,z4,z6,z324]),(0,[z0,z1,z2,z13,z4,z42])],[(0,[z0,z1,z2,z1116,z4,z6]),(0,[z59,z1,z2,z57,z4,z6]),(0,[z190,z0,z2,z3,z4,z23]),(0,[z1117,z1,z2,z3,z4,z6]),(0,[z0,z1,z239,z3,z4,z272])],[(0,[z1,z12,z3,z4,z46,z6]),(0,[z48,z1,z12,z3,z49,z6])],[(0,[z125,z1,z12,z3,z4,z6]),(0,[z0,z1,z12,z712,z4,z6]),(0,[z0,z1,z2,z3,z4,z1118]),(0,[z160,z1,z2,z171,z4,z6])],[(0,[z0,z1,z2,z1119,z4,z6]),(0,[z328,z1,z2,z3,z4,z41]),(0,[z397,z1,z2,z3,z49,z6]),(0,[z0,z1,z1120,z3,z4,z6]),(0,[z0,z90,z2,z3,z338,z6]),(0,[z0,z1,z2,z3,z65,z780])],[(0,[z0,z1,z2,z3,z1121,z4]),(0,[z0,z1,z77,z3,z62,z6]),(0,[z157,z1,z3,z4,z54,z6]),(0,[z0,z1,z2,z495,z4,z42]),(0,[z1122,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z667,z6,z107])],[(0,[z94,z0,z1,z167,z4,z6]),(0,[z0,z1123,z2,z3,z4,z6]),(0,[z73,z289,z1,z3,z74,z6])],[(0,[z0,z1,z2,z181,z132,z6]),(0,[z1,z12,z3,z46,z15,z6]),(0,[z0,z1,z2,z3,z4,z1124]),(0,[z444,z1,z2,z3,z4,z638])],[(0,[z0,z1,z316,z3,z4,z6]),(0,[z0,z1,z20,z3,z4,z1125]),(0,[z0,z225,z2,z3,z62,z6]),(0,[z0,z138,z2,z3,z4,z313])],[(0,[z32,z0,z21,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z779]),(0,[z1126,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z1127,z4,z6])],[(0,[z182,z1,z2,z3,z46,z6]),(0,[z0,z1,z2,z1128,z4,z6]),(0,[z1,z355,z3,z80,z4,z6])],[(0,[z0,z1,z12,z3,z4,z638]),(0,[z889,z0,z2,z3,z4,z6]),(0,[z1129,z1,z2,z3,z4,z6]),(0,[z1130,z1,z2,z3,z4,z6]),(0,[z44,z0,z1,z55,z45,z6]),(0,[z0,z1,z2,z592,z4,z42])],[(0,[z0,z1,z1131,z3,z4,z6]),(0,[z0,z1,z2,z1132,z4,z6]),(0,[z0,z1,z2,z3,z1133,z6]),(0,[z668,z0,z2,z166,z4,z6])]],
   [[(0,[z0,z1,z2,z3,z4,z1134]),(0,[z0,z1,z12,z1135,z4,z6]),(0,[z0,z1,z12,z3,z4,z497]),(0,[z432,z0,z24,z3,z4,z6]),(0,[z0,z1,z2,z3,z136,z6]),(0,[z0,z114,z2,z907,z4,z6]),(0,[z0,z1,z2,z3,z4,z1136]),(0,[z306,z207,z2,z3,z4,z6])],[(0,[z0,z1,z1137,z3,z4,z6]),(0,[z0,z1,z12,z112,z3,z65]),(0,[z0,z1,z12,z3,z4,z241]),(0,[z0,z1,z2,z3,z71,z179]),(0,[z0,z1,z2,z137,z4,z35]),(0,[z0,z2,z3,z4,z802,z23]),(0,[z0,z90,z2,z3,z4,z36])],[(0,[z1,z20,z300,z3,z4,z6]),(0,[z195,z1,z2,z152,z4,z6]),(0,[z1138,z1,z2,z3,z4,z6]),(0,[z242,z1,z243,z3,z4,z6])],[(0,[z586,z1,z12,z3,z4,z6]),(0,[z0,z207,z2,z3,z4,z6])],[(0,[z0,z1139,z2,z3,z4,z6])],[(0,[z1,z12,z3,z4,z366,z6]),(0,[z32,z0,z1,z3,z4,z189]),(0,[z148,z2,z3,z4,z46,z6]),(0,[z0,z1,z2,z88,z62,z6]),(0,[z444,z1,z283,z3,z4,z6]),(0,[z0,z1,z2,z1140,z4,z6]),(0,[z0,z1,z2,z3,z109,z38])],[(0,[z0,z1,z342,z3,z132,z6]),(0,[z22,z0,z2,z3,z4,z100]),(0,[z0,z1,z1141,z3,z4,z6]),(0,[z1,z12,z3,z4,z558,z6]),(0,[z1,z2,z3,z1070,z46,z6]),(0,[z1142,z0,z2,z3,z4,z6]),(0,[z1143,z1,z2,z3,z4,z6])],[(0,[z160,z1,z2,z3,z4,z6]),(0,[z0,z1,z20,z3,z4,z638]),(0,[z32,z0,z1,z3,z4,z194]),(0,[z387,z1,z2,z3,z45,z6]),(0,[z0,z1,z1144,z3,z4,z6])],[(0,[z0,z1,z2,z3,z1145,z6]),(0,[z157,z1,z2,z3,z4,z6]),(0,[z153,z419,z2,z3,z4,z6]),(0,[z675,z0,z1,z2,z6,z107]),(0,[z32,z0,z1,z3,z4,z202]),(0,[z1146,z1,z2,z3,z4,z6]),(0,[z1147,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z4,z6,z790])],[(0,[z0,z20,z21,z3,z4,z6]),(0,[z0,z1,z20,z3,z4,z497]),(0,[z185,z0,z1,z55,z4,z6]),(0,[z1148,z1,z2,z3,z4,z6])],[(0,[z1,z12,z3,z563,z4,z6]),(0,[z195,z1,z12,z3,z4,z6]),(0,[z0,z1,z20,z112,z3,z65]),(0,[z0,z1,z20,z3,z4,z241]),(0,[z1149,z1,z2,z3,z4,z6])],[(0,[z0,z1,z355,z3,z4,z6])],[(0,[z40,z1,z2,z3,z4,z885])],[(0,[z0,z1,z1150,z3,z4,z6]),(0,[z0,z1,z2,z3,z1151,z6]),(0,[z0,z1,z2,z3,z4,z1152]),(0,[z0,z273,z2,z152,z4,z6]),(0,[z0,z1,z2,z3,z65,z517])],[(0,[z0,z1,z2,z1153,z4,z6]),(0,[z682,z1,z12,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z1154]),(0,[z59,z284,z2,z3,z4,z6]),(0,[z195,z1,z1155,z3,z4,z6]),(0,[z139,z0,z1,z2,z6,z107])],[(0,[z0,z1,z1156,z3,z4,z6]),(0,[z0,z1,z1157,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z1158]),(0,[z0,z1,z1159,z3,z4,z6]),(0,[z0,z1,z2,z3,z899,z6]),(0,[z83,z1,z2,z80,z4,z84]),(0,[z0,z1,z2,z3,z136,z179]),(0,[z0,z1,z2,z3,z4,z1160]),(0,[z0,z1,z2,z512,z95,z6]),(0,[z0,z1,z2,z3,z1161,z6])]],
   [[(0,[z186,z1,z12,z181,z4,z6]),(0,[z0,z1,z1162,z3,z4,z6]),(0,[z73,z0,z1,z490,z74,z6])],[(0,[z0,z1,z77,z163,z4,z6]),(0,[z0,z104,z247,z3,z4,z28]),(0,[z387,z90,z2,z3,z4,z6])],[(0,[z0,z1,z1163,z3,z4,z6]),(0,[z0,z1,z1164,z3,z4,z6]),(0,[z0,z1,z69,z323,z4,z6]),(0,[z195,z1,z2,z166,z4,z6])],[(0,[z1,z12,z3,z4,z6,z404]),(0,[z195,z1,z20,z3,z4,z6]),(0,[z0,z1,z379,z3,z4,z6]),(0,[z0,z384,z2,z3,z4,z28]),(0,[z0,z1,z2,z3,z4,z165])],[(0,[z0,z1,z1165,z3,z4,z6]),(0,[z573,z1,z12,z3,z4,z6]),(0,[z0,z225,z2,z163,z4,z6])],[(0,[z186,z1,z12,z3,z4,z6]),(0,[z0,z1,z12,z3,z4,z1166]),(0,[z0,z1,z12,z490,z4,z6]),(0,[z0,z1,z2,z3,z4,z1167])],[(0,[z0,z1,z2,z3,z4,z1168]),(0,[z199,z20,z12,z3,z4,z6]),(0,[z0,z1,z12,z3,z4,z559]),(0,[z0,z1,z2,z1169,z4,z6]),(0,[z0,z24,z1,z3,z4,z241]),(0,[z0,z1,z2,z3,z1170,z6])],[(0,[z19,z12,z3,z4,z6,z23]),(0,[z1,z2,z52,z813,z4,z6])],[(0,[z0,z1,z2,z181,z203,z6]),(0,[z0,z1,z1171,z3,z4,z6])],[(0,[z0,z767,z12,z3,z4,z6]),(0,[z0,z1,z2,z280,z4,z130])],[(0,[z186,z133,z2,z181,z4,z6]),(0,[z0,z1,z2,z372,z95,z6]),(0,[z0,z352,z329,z3,z4,z6]),(0,[z0,z1,z2,z639,z4,z42]),(0,[z0,z1,z2,z117,z649,z4])],[(0,[z43,z1,z12,z3,z4,z6]),(0,[z0,z1172,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z1173,z6]),(0,[z0,z1,z2,z323,z4,z337])],[(0,[z0,z1,z20,z3,z758,z6]),(0,[z0,z1,z1174,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z1175]),(0,[z0,z207,z2,z3,z4,z36])],[(0,[z1,z12,z3,z4,z6,z609]),(0,[z249,z0,z1,z3,z537,z6]),(0,[z0,z1,z20,z490,z4,z6]),(1,[z148,z2,z3,z46,z6])],[(0,[z0,z1,z2,z3,z1176,z6]),(0,[z0,z1,z12,z3,z38,z6]),(0,[z761,z0,z20,z3,z4,z6]),(0,[z0,z1,z20,z3,z4,z559]),(0,[z44,z0,z207,z55,z4,z6]),(0,[z0,z105,z25,z3,z4,z6]),(0,[z0,z1,z2,z1177,z4,z6])]],
   [[(0,[z87,z1,z2,z3,z278,z41]),(0,[z0,z1,z243,z3,z4,z35]),(0,[z0,z1,z1178,z3,z4,z6]),(0,[z0,z1,z2,z3,z45,z6]),(0,[z0,z1,z1179,z3,z4,z6])],[(0,[z1,z12,z3,z4,z6,z445]),(0,[z0,z1,z2,z3,z1180,z6]),(0,[z444,z105,z2,z3,z4,z6])],[(0,[z0,z1,z379,z3,z4,z179]),(0,[z0,z1,z2,z78,z4,z559]),(0,[z0,z1,z2,z3,z1181,z6])],[(0,[z199,z0,z12,z3,z4,z6]),(0,[z0,z1,z2,z80,z50,z6])],[(0,[z0,z1,z2,z3,z1182,z6]),(0,[z0,z1,z342,z3,z203,z6]),(0,[z1,z12,z3,z451,z4,z6]),(0,[z40,z1,z12,z3,z4,z41]),(0,[z142,z1,z266,z3,z4,z6]),(0,[z0,z1,z2,z1183,z4,z6]),(0,[z737,z104,z1,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z1012]),(0,[z195,z114,z2,z3,z4,z6]),(0,[z0,z1,z882,z3,z4,z6]),(0,[z0,z1,z2,z3,z1184,z4]),(0,[z0,z1,z2,z280,z4,z54]),(0,[z0,z1,z1185,z3,z4,z6])],[(0,[z186,z133,z342,z3,z4,z6]),(0,[z0,z70,z12,z3,z4,z6]),(0,[z1,z12,z3,z4,z41,z47])],[(0,[z289,z1,z2,z3,z4,z6]),(0,[z546,z0,z2,z166,z4,z6])],[(0,[z1,z722,z2,z3,z4,z6]),(0,[z0,z1,z20,z3,z38,z6]),(0,[z444,z138,z2,z3,z4,z6])],[(0,[z133,z2,z3,z46,z15,z6]),(0,[z0,z1,z270,z3,z4,z6]),(0,[z0,z1186,z2,z3,z4,z6]),(1,[z242,z2,z3,z15,z6]),(0,[z0,z1,z2,z112,z3,z234])],[(0,[z0,z1,z2,z3,z4,z1187]),(0,[z1188,z352,z1,z3,z4,z6])],[(0,[z0,z1,z2,z3,z1189,z6]),(0,[z262,z1,z2,z80,z4,z6]),(0,[z153,z39,z2,z3,z4,z6]),(0,[z1,z12,z3,z471,z4,z6]),(0,[z0,z1,z1190,z3,z4,z6]),(0,[z0,z1,z2,z490,z4,z638])],[(0,[z0,z1,z12,z3,z4,z100]),(0,[z199,z0,z20,z3,z4,z6]),(0,[z1191,z1,z2,z3,z4,z6]),(0,[z352,z737,z1,z3,z4,z6])],[(0,[z1,z12,z141,z80,z4,z6]),(0,[z0,z1,z2,z3,z1192,z6]),(0,[z387,z207,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z1193]),(0,[z0,z1,z2,z3,z1194,z6]),(0,[z0,z1,z2,z141,z95,z165])],[(0,[z186,z22,z12,z3,z4,z6]),(0,[z492,z1,z2,z80,z4,z6]),(0,[z1,z12,z3,z480,z4,z6]),(0,[z547,z0,z1,z2,z109,z4])],[(0,[z0,z284,z2,z3,z4,z6]),(0,[z0,z1,z1195,z3,z4,z6]),(0,[z361,z0,z2,z3,z15,z6]),(0,[z0,z70,z20,z3,z4,z6]),(0,[z0,z21,z3,z4,z54,z6]),(0,[z0,z1,z2,z3,z1196,z6])]],
   [[(0,[z86,z1,z69,z3,z46,z6]),(0,[z0,z1,z1197,z3,z4,z6])],[(0,[z0,z1,z2,z1198,z4,z6]),(0,[z235,z1,z12,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z264]),(0,[z0,z1,z2,z3,z1199,z6]),(0,[z1200,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z1201,z6])],[(0,[z0,z733,z2,z3,z4,z6]),(0,[z0,z14,z3,z4,z459,z6]),(0,[z0,z1,z2,z3,z71,z319]),(0,[z393,z0,z2,z3,z4,z23]),(0,[z0,z1,z2,z483,z3,z65]),(0,[z68,z0,z1,z2,z208,z4]),(0,[z1202,z0,z1,z3,z4,z6]),(0,[z0,z1,z2,z354,z4,z42])],[(0,[z0,z1,z763,z3,z4,z6]),(0,[z0,z1,z12,z137,z4,z6]),(0,[z0,z1,z2,z1203,z4,z6])],[(0,[z0,z1,z20,z3,z4,z100]),(0,[z0,z1,z12,z3,z140,z4]),(0,[z0,z1,z2,z3,z9,z6]),(0,[z0,z1,z2,z3,z1204,z6]),(0,[z0,z1,z2,z3,z1205,z6]),(0,[z0,z1,z1206,z3,z4,z6])],[(0,[z0,z133,z2,z3,z4,z100]),(0,[z0,z1,z2,z3,z4,z1207]),(0,[z0,z1,z2,z3,z1208,z6]),(0,[z0,z961,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z1209,z6]),(0,[z0,z1,z1210,z3,z4,z6]),(0,[z0,z1,z2,z163,z62,z6]),(0,[z1211,z1,z2,z3,z4,z6])],[(0,[z0,z1,z1212,z3,z4,z6]),(0,[z145,z1,z12,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z1213]),(0,[z0,z1,z1214,z3,z4,z6]),(0,[z0,z1,z2,z3,z1215,z6])],[(0,[z115,z1,z12,z3,z4,z6]),(0,[z0,z1,z2,z171,z15,z6]),(0,[z0,z1,z2,z112,z354,z65])],[(0,[z0,z1,z303,z3,z4,z6]),(0,[z186,z421,z2,z3,z4,z6]),(0,[z603,z19,z2,z3,z4,z6]),(0,[z0,z1037,z2,z3,z4,z6]),(0,[z83,z237,z2,z80,z4,z6]),(0,[z0,z1216,z2,z3,z4,z6]),(0,[z0,z1,z3,z4,z6,z926]),(0,[z0,z1,z3,z4,z6,z1217])],[(0,[z0,z1,z12,z3,z4,z75]),(0,[z48,z1,z1077,z3,z4,z6]),(0,[z526,z1,z12,z3,z4,z6]),(0,[z0,z1,z2,z3,z1218,z6]),(0,[z86,z1,z2,z3,z46,z337]),(0,[z0,z1,z2,z3,z45,z36]),(0,[z73,z0,z1,z174,z74,z6])],[(0,[z0,z19,z2,z315,z4,z6]),(0,[z40,z1,z12,z3,z4,z6]),(0,[z0,z1219,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z1220]),(0,[z160,z1,z239,z3,z4,z6]),(0,[z444,z1,z2,z174,z4,z6]),(0,[z0,z105,z2,z3,z4,z638])],[(0,[z19,z12,z3,z166,z4,z6]),(0,[z0,z823,z12,z3,z4,z6]),(0,[z689,z1,z12,z3,z4,z6]),(0,[z0,z1,z1221,z3,z4,z6]),(0,[z73,z0,z1,z3,z74,z638])],[(0,[z0,z1,z20,z137,z4,z6]),(0,[z0,z284,z192,z3,z4,z6]),(0,[z0,z1,z1222,z3,z4,z6]),(0,[z37,z1,z2,z280,z4,z6])],[(0,[z0,z2,z14,z3,z4,z100]),(0,[z1223,z0,z1,z3,z4,z6]),(0,[z0,z1,z20,z3,z140,z4]),(0,[z0,z777,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z1224,z6]),(0,[z30,z0,z2,z3,z735,z6]),(0,[z0,z1,z2,z354,z4,z6])],[(0,[z0,z21,z2,z3,z4,z6]),(0,[z0,z1,z12,z174,z4,z6]),(0,[z0,z1,z2,z3,z4,z1225])]],
   [[(0,[z0,z1,z915,z3,z4,z6]),(0,[z0,z1,z20,z817,z4,z6]),(0,[z145,z1,z20,z3,z4,z6]),(0,[z0,z1,z192,z3,z4,z264]),(0,[z40,z1,z191,z3,z4,z29]),(0,[z1,z2,z3,z4,z29,z885]),(0,[z0,z1,z2,z1226,z4,z6]),(0,[z0,z1,z2,z3,z4,z313]),(0,[z0,z1,z1227,z3,z4,z6]),(0,[z0,z1,z2,z117,z4,z131])],[(0,[z0,z1,z69,z3,z4,z370]),(0,[z0,z274,z2,z3,z122,z6]),(0,[z0,z1,z446,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z1228]),(0,[z0,z1,z2,z3,z136,z319])],[(0,[z0,z1,z2,z3,z132,z6]),(0,[z115,z133,z2,z3,z4,z6]),(0,[z0,z1229,z2,z3,z4,z6]),(0,[z615,z1,z2,z80,z4,z6]),(0,[z0,z438,z2,z3,z4,z28]),(1,[z0,z777,z3,z4,z6]),(0,[z0,z1,z2,z3,z1230,z6])],[(0,[z1,z2,z12,z315,z4,z6]),(0,[z0,z1,z20,z3,z4,z75]),(0,[z0,z1,z12,z3,z4,z830]),(0,[z1,z12,z3,z4,z6,z542]),(0,[z0,z1,z2,z984,z4,z6]),(0,[z0,z1,z192,z3,z9,z6]),(0,[z157,z248,z1,z3,z4,z6]),(0,[z1231,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z1232,z4,z6])],[(0,[z0,z1,z2,z3,z4,z878]),(0,[z0,z1,z1233,z3,z4,z6])],[(0,[z0,z1,z1234,z3,z4,z6]),(0,[z0,z399,z14,z3,z4,z6])],[(0,[z541,z1,z12,z3,z4,z6]),(0,[z63,z0,z2,z3,z4,z23]),(0,[z0,z90,z3,z55,z4,z6]),(0,[z516,z0,z1,z2,z6,z107]),(0,[z0,z1,z92,z3,z4,z54]),(0,[z0,z1,z2,z141,z6,z790])],[(0,[z0,z1,z2,z1235,z4,z6]),(0,[z160,z1,z2,z3,z4,z272]),(0,[z0,z1236,z2,z3,z4,z6]),(0,[z1237,z1,z2,z3,z4,z6]),(0,[z68,z0,z1,z2,z109,z50]),(0,[z0,z1,z2,z65,z113,z6])],[(0,[z0,z1,z20,z174,z4,z6]),(0,[z0,z148,z69,z3,z4,z6]),(0,[z0,z1,z69,z218,z4,z6]),(0,[z0,z1,z1238,z3,z4,z6]),(0,[z1239,z1,z2,z3,z4,z6]),(0,[z123,z0,z2,z166,z4,z6]),(0,[z0,z1,z1240,z3,z4,z6]),(0,[z0,z1,z2,z171,z122,z6]),(0,[z0,z1,z1241,z3,z4,z6]),(0,[z0,z1,z2,z109,z740,z4])],[(0,[z0,z1,z2,z3,z1242,z6]),(0,[z0,z21,z3,z488,z4,z6])],[(0,[z22,z0,z312,z3,z4,z6]),(0,[z0,z1243,z1,z3,z4,z6]),(0,[z405,z1,z2,z3,z46,z6]),(0,[z0,z329,z2,z3,z4,z241]),(0,[z1244,z1,z2,z3,z4,z6])],[(0,[z0,z1,z1245,z3,z4,z6]),(0,[z22,z24,z157,z3,z4,z6])],[(0,[z94,z1,z12,z80,z4,z6]),(0,[z199,z2,z12,z3,z4,z6]),(0,[z184,z1,z892,z3,z4,z6])],[(0,[z0,z1,z1246,z3,z4,z6])],[(0,[z0,z1,z2,z323,z46,z6]),(0,[z0,z58,z2,z3,z122,z6]),(0,[z73,z0,z138,z3,z74,z6])],[(0,[z83,z1,z12,z80,z4,z6]),(1,[z1,z2,z813,z4,z6]),(0,[z0,z14,z3,z673,z4,z6])]],
   [[(0,[z268,z1,z20,z3,z4,z6]),(0,[z0,z1,z446,z3,z4,z179])],[],[(0,[z22,z0,z342,z3,z4,z6]),(0,[z186,z326,z2,z3,z4,z6]),(0,[z0,z1247,z2,z3,z4,z6]),(0,[z0,z1,z2,z218,z4,z337]),(0,[z242,z1,z2,z171,z4,z6]),(0,[z0,z1,z78,z786,z4,z6]),(0,[z0,z105,z2,z490,z4,z6]),(0,[z68,z0,z1,z2,z109,z38]),(0,[z0,z1248,z2,z3,z4,z6])],[(0,[z0,z1,z69,z3,z4,z6]),(0,[z0,z1,z12,z3,z4,z215])],[(0,[z0,z1,z379,z3,z4,z319]),(0,[z242,z1,z239,z3,z4,z6]),(0,[z0,z1,z2,z1249,z4,z6])],[(0,[z0,z1,z2,z3,z4,z996]),(0,[z59,z1,z270,z52,z4,z6]),(0,[z0,z70,z178,z3,z4,z6]),(0,[z0,z1,z2,z174,z4,z638])],[(0,[z1,z12,z80,z4,z6,z42]),(0,[z0,z207,z2,z3,z338,z6])],[(0,[z0,z853,z20,z3,z4,z6]),(0,[z123,z0,z2,z166,z4,z179])],[(0,[z0,z1,z12,z3,z252,z6]),(0,[z83,z1,z20,z80,z4,z6]),(0,[z242,z58,z2,z3,z4,z6]),(0,[z217,z0,z1,z2,z6,z107])],[(0,[z0,z312,z21,z3,z4,z6]),(0,[z0,z1,z331,z78,z4,z6]),(0,[z0,z255,z12,z3,z4,z6]),(0,[z0,z1,z12,z216,z4,z6]),(0,[z0,z1083,z2,z3,z4,z6]),(0,[z0,z138,z2,z490,z4,z6]),(0,[z0,z1,z1250,z3,z4,z6])],[(0,[z0,z1,z1251,z3,z4,z6]),(0,[z1,z763,z12,z3,z4,z6]),(0,[z0,z1,z1252,z3,z4,z6])],[(0,[z1,z20,z386,z3,z4,z6]),(0,[z0,z1,z3,z4,z54,z926]),(0,[z0,z1253,z2,z3,z4,z6])],[(0,[z0,z1,z303,z315,z4,z6]),(0,[z0,z1,z20,z3,z4,z215]),(0,[z0,z1,z2,z1254,z4,z6])],[(0,[z1,z266,z12,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z337]),(0,[z0,z1255,z2,z3,z4,z6]),(0,[z0,z1,z1256,z3,z4,z6]),(0,[z0,z1,z2,z1257,z4,z6])],[(0,[z1,z12,z3,z46,z6,z47]),(0,[z1188,z1,z2,z3,z4,z6])],[(0,[z1,z12,z3,z4,z6,z100]),(0,[z0,z1,z2,z78,z4,z215]),(0,[z32,z0,z1,z3,z252,z130])]],
   [[(0,[z0,z1,z2,z3,z203,z6]),(0,[z0,z1,z12,z3,z278,z6]),(0,[z0,z286,z69,z3,z4,z6]),(0,[z32,z0,z1,z216,z4,z130])],[(0,[z1,z12,z3,z4,z608,z6]),(0,[z20,z21,z12,z3,z4,z6]),(0,[z0,z1,z20,z3,z252,z6]),(0,[z0,z1,z368,z78,z4,z6]),(0,[z1258,z1,z2,z3,z4,z6])],[(0,[z186,z133,z2,z3,z4,z6]),(0,[z0,z255,z20,z3,z4,z6]),(0,[z0,z1,z20,z216,z4,z6]),(1,[z1,z2,z3,z4,z885])],[(0,[z242,z1,z2,z3,z4,z6]),(0,[z0,z119,z2,z3,z4,z28]),(0,[z0,z1,z2,z112,z65,z113])],[(0,[z0,z1259,z1,z3,z4,z6]),(0,[z1260,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z263,z513])],[(0,[z0,z1,z2,z315,z132,z6]),(0,[z0,z1,z2,z3,z4,z1261]),(0,[z145,z255,z2,z3,z4,z6])],[(0,[z40,z1,z2,z3,z4,z29]),(0,[z30,z0,z2,z3,z15,z35])],[(0,[z0,z1,z1262,z3,z4,z6]),(0,[z27,z1,z12,z3,z4,z6]),(0,[z157,z1,z3,z55,z4,z6]),(0,[z0,z1,z1263,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z1264]),(0,[z0,z105,z12,z3,z4,z6]),(0,[z0,z1265,z2,z3,z4,z6])],[(0,[z0,z1,z287,z3,z4,z6]),(0,[z0,z1,z20,z3,z278,z6]),(0,[z1009,z0,z2,z3,z4,z6]),(0,[z374,z1,z2,z3,z4,z41]),(0,[z22,z157,z1,z3,z4,z6])],[(0,[z0,z286,z2,z3,z4,z337]),(0,[z0,z1,z2,z3,z4,z1266]),(0,[z1267,z1,z2,z3,z4,z6])],[(0,[z182,z0,z2,z3,z15,z6]),(0,[z0,z1,z437,z3,z4,z6]),(0,[z0,z1,z2,z1268,z4,z6]),(0,[z0,z777,z150,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z926])],[(0,[z0,z1,z1269,z3,z4,z6]),(0,[z0,z1,z3,z4,z926,z130])],[(0,[z1,z20,z703,z3,z4,z6]),(0,[z0,z24,z1,z3,z252,z6]),(0,[z0,z1,z2,z1270,z4,z6]),(0,[z306,z1,z53,z3,z4,z6])],[(0,[z193,z0,z21,z3,z4,z6]),(0,[z0,z20,z1271,z3,z4,z6]),(0,[z68,z0,z1,z20,z109,z4]),(0,[z0,z1,z2,z907,z4,z6])],[(0,[z139,z0,z1,z12,z6,z107]),(0,[z0,z138,z12,z3,z4,z6]),(0,[z0,z1,z2,z3,z1272,z4]),(0,[z0,z1,z2,z1273,z4,z6])]],
   [[(0,[z1,z133,z2,z3,z203,z6]),(0,[z1142,z0,z266,z3,z4,z6]),(0,[z22,z210,z24,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z1274]),(0,[z0,z1,z2,z171,z4,z35])],[(0,[z0,z1,z1275,z3,z4,z6]),(0,[z0,z105,z20,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z1276])],[(0,[z0,z1,z2,z3,z4,z1277])],[(0,[z0,z1,z12,z323,z4,z6]),(0,[z578,z0,z1,z2,z6,z107])],[(0,[z19,z1,z12,z3,z4,z6]),(0,[z1,z12,z3,z80,z4,z6]),(0,[z1,z416,z12,z3,z46,z6]),(0,[z1,z12,z3,z639,z4,z6]),(0,[z0,z329,z12,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z84]),(0,[z87,z1,z2,z3,z4,z41]),(0,[z0,z1,z2,z3,z463,z47])],[(0,[z1,z12,z155,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z1028]),(0,[z0,z1,z1077,z3,z4,z6]),(0,[z199,z142,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z97,z6]),(0,[z0,z2,z3,z4,z28,z802])],[(0,[z0,z1,z2,z3,z4,z1278]),(0,[z0,z1,z2,z1279,z4,z6]),(0,[z0,z1280,z2,z3,z4,z6]),(0,[z193,z0,z1,z3,z4,z189]),(0,[z0,z1,z2,z3,z1281,z6]),(0,[z0,z1,z14,z280,z4,z6])],[(0,[z48,z1,z12,z3,z4,z6]),(0,[z1,z12,z3,z4,z537,z6]),(0,[z0,z138,z20,z3,z4,z6]),(0,[z0,z1,z53,z350,z4,z6])],[(0,[z0,z1,z342,z3,z4,z100]),(0,[z0,z1,z2,z323,z49,z6])],[(0,[z0,z1,z1282,z3,z4,z6]),(0,[z0,z1,z12,z3,z33,z6]),(0,[z0,z1,z1283,z3,z4,z6]),(0,[z1284,z1,z2,z3,z4,z6])],[(0,[z186,z1,z12,z315,z4,z6])],[(0,[z0,z1,z20,z323,z4,z6]),(0,[z0,z284,z2,z52,z4,z6]),(0,[z87,z1,z77,z3,z4,z41]),(0,[z0,z1,z2,z3,z4,z1285]),(0,[z0,z105,z2,z174,z4,z6]),(0,[z0,z1,z2,z113,z144,z6])],[(0,[z153,z19,z12,z3,z4,z6]),(0,[z0,z329,z20,z3,z4,z6]),(0,[z145,z1,z2,z3,z4,z28]),(0,[z44,z0,z1,z55,z4,z559])],[(0,[z56,z1,z2,z52,z4,z6]),(0,[z401,z0,z2,z3,z4,z23])],[(0,[z439,z19,z2,z3,z4,z6]),(0,[z0,z1,z2,z52,z4,z264]),(0,[z87,z225,z2,z3,z4,z41]),(0,[z0,z1,z2,z3,z1286,z6])]],
   [[(0,[z0,z1,z1287,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z1288]),(0,[z0,z1,z2,z3,z4,z1289])],[(0,[z11,z19,z12,z3,z4,z6]),(0,[z0,z1,z2,z1290,z4,z6]),(0,[z0,z1,z1291,z3,z4,z6]),(0,[z0,z114,z2,z152,z4,z6]),(0,[z0,z1,z2,z3,z4,z35])],[(0,[z34,z1,z12,z3,z4,z6]),(0,[z0,z1,z192,z3,z4,z84]),(0,[z0,z1,z2,z52,z9,z6]),(0,[z0,z1,z2,z1292,z4,z6]),(0,[z32,z0,z14,z3,z4,z23]),(0,[z0,z1,z446,z3,z4,z319])],[(0,[z0,z1,z2,z315,z203,z6]),(0,[z0,z1,z2,z1049,z4,z6]),(0,[z0,z1,z20,z3,z33,z6]),(0,[z0,z1,z1293,z3,z4,z6]),(0,[z0,z1,z2,z3,z260,z47])],[(0,[z0,z1,z192,z3,z97,z6]),(0,[z0,z1,z1294,z3,z4,z6]),(0,[z0,z148,z2,z3,z46,z6]),(0,[z0,z1,z2,z3,z1295,z6])],[(0,[z186,z133,z2,z315,z4,z6]),(0,[z0,z1,z20,z3,z4,z905]),(0,[z552,z1,z20,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z885]),(0,[z0,z1,z379,z3,z71,z6]),(0,[z0,z1,z2,z3,z4,z1296]),(0,[z0,z138,z2,z3,z4,z638])],[(0,[z153,z19,z20,z3,z4,z6]),(0,[z0,z114,z2,z567,z4,z6]),(0,[z0,z831,z12,z3,z4,z6]),(0,[z0,z1,z2,z1297,z4,z6]),(0,[z0,z255,z2,z3,z252,z6]),(0,[z0,z1,z2,z216,z252,z6])],[(0,[z0,z1,z1298,z3,z4,z6]),(0,[z0,z1,z1299,z3,z4,z6]),(0,[z584,z0,z2,z3,z15,z6]),(0,[z0,z90,z2,z3,z45,z6]),(0,[z0,z255,z2,z216,z4,z6]),(0,[z0,z1,z1300,z3,z4,z6])],[(0,[z186,z682,z2,z3,z4,z6]),(0,[z0,z1,z2,z1301,z4,z6]),(0,[z381,z1,z12,z3,z4,z6]),(0,[z0,z1,z2,z3,z140,z107])],[(0,[z0,z1,z2,z3,z1058,z6]),(0,[z0,z1,z2,z1135,z4,z6]),(0,[z1,z20,z634,z3,z4,z6]),(0,[z87,z1,z2,z88,z4,z41]),(0,[z0,z1,z2,z3,z4,z497]),(0,[z123,z0,z2,z166,z4,z319])],[(0,[z0,z1,z2,z3,z4,z241])],[(0,[z0,z1,z2,z3,z1302,z6]),(0,[z0,z923,z12,z3,z4,z6]),(0,[z0,z1,z2,z3,z278,z29]),(0,[z0,z1,z2,z3,z4,z1303]),(0,[z1304,z1,z2,z3,z4,z6])],[(0,[z1,z12,z3,z4,z679,z6]),(0,[z221,z1,z763,z3,z4,z6])],[(0,[z0,z1,z1305,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z1306])],[(0,[z0,z1,z2,z1071,z4,z6])],[(0,[z660,z1,z12,z3,z4,z6]),(0,[z0,z1,z178,z3,z278,z6]),(0,[z1307,z1,z2,z3,z4,z6]),(0,[z145,z24,z1,z3,z4,z6]),(0,[z0,z242,z2,z3,z15,z6])]],
   [[(0,[z184,z1,z2,z3,z4,z6]),(0,[z0,z1,z1308,z3,z4,z6]),(0,[z0,z1,z1309,z3,z4,z6])],[(0,[z86,z1,z12,z3,z46,z6])],[(0,[z27,z1,z2,z3,z4,z29])],[(0,[z195,z1,z2,z3,z4,z6]),(0,[z59,z1,z12,z3,z4,z6]),(0,[z157,z150,z1,z3,z4,z6]),(0,[z0,z1,z379,z3,z136,z6]),(0,[z1310,z1,z2,z3,z4,z6]),(0,[z0,z1311,z1,z3,z4,z6])],[(0,[z1,z2,z3,z813,z4,z6]),(0,[z59,z1,z2,z813,z4,z6]),(0,[z0,z2,z3,z122,z735,z6]),(0,[z0,z1,z92,z3,z4,z926])],[(0,[z0,z1,z2,z3,z4,z1312]),(0,[z0,z148,z2,z3,z4,z337]),(0,[z0,z1,z2,z3,z1313,z6])],[(0,[z0,z1,z1314,z3,z4,z6]),(0,[z387,z1,z168,z3,z4,z6]),(1,[z195,z2,z166,z4,z6]),(0,[z1315,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z65,z38])],[(0,[z86,z1,z2,z3,z1070,z6]),(0,[z1316,z1,z2,z3,z4,z6])],[(0,[z0,z1317,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z1318]),(0,[z0,z1,z3,z4,z850,z6])],[(0,[z1,z12,z3,z4,z6,z265]),(0,[z0,z1,z1319,z3,z4,z6]),(0,[z22,z0,z24,z3,z4,z6]),(0,[z0,z1,z2,z589,z95,z6])],[(0,[z142,z1,z2,z3,z203,z6]),(0,[z86,z1,z20,z3,z46,z6])],[(0,[z0,z1,z2,z3,z1320,z6])],[(0,[z128,z1,z2,z52,z4,z6]),(0,[z0,z1,z2,z112,z3,z409]),(0,[z306,z1,z2,z3,z4,z559])],[(0,[z19,z12,z3,z4,z15,z6]),(0,[z1321,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z1322])],[(0,[z0,z237,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z1166]),(0,[z0,z1,z20,z3,z4,z940]),(0,[z0,z21,z3,z55,z4,z6]),(0,[z0,z70,z2,z3,z278,z6]),(0,[z0,z1,z2,z3,z252,z28]),(0,[z44,z0,z1,z786,z4,z6])],[(0,[z0,z1,z2,z3,z1323,z6]),(0,[z435,z1,z20,z3,z4,z6]),(0,[z157,z1,z3,z4,z74,z6]),(0,[z184,z1,z2,z3,z4,z179]),(0,[z0,z1,z2,z3,z4,z1324]),(0,[z0,z1,z243,z137,z4,z6]),(0,[z0,z1,z2,z3,z4,z559])]],
   [[(0,[z1325,z1,z2,z3,z4,z6]),(0,[z0,z1326,z2,z3,z4,z6])],[(0,[z0,z1327,z2,z3,z4,z6]),(0,[z87,z1,z2,z3,z62,z41]),(0,[z0,z329,z2,z3,z252,z6])],[(0,[z1,z12,z152,z80,z4,z6]),(0,[z0,z1,z12,z3,z4,z370]),(0,[z195,z1,z2,z3,z4,z179])],[(0,[z242,z1,z2,z3,z4,z272]),(0,[z0,z207,z2,z3,z45,z6])],[(0,[z0,z1,z12,z3,z4,z958]),(0,[z0,z1,z2,z141,z549,z6]),(0,[z0,z528,z14,z3,z4,z6]),(0,[z0,z1,z2,z3,z1328,z6]),(0,[z0,z1,z2,z3,z65,z165])],[(0,[z0,z1271,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z1329]),(0,[z0,z1330,z2,z3,z4,z6]),(0,[z0,z1,z1331,z3,z4,z6])],[(0,[z593,z0,z81,z3,z4,z6]),(0,[z0,z1,z2,z1095,z4,z6]),(0,[z0,z1,z2,z3,z1332,z6])],[(0,[z1,z283,z12,z3,z4,z6]),(0,[z0,z24,z777,z3,z4,z6]),(0,[z145,z1,z2,z3,z252,z6])],[(0,[z0,z1,z2,z3,z1333,z6]),(0,[z22,z210,z2,z3,z4,z6]),(0,[z145,z1,z2,z216,z4,z6]),(0,[z68,z0,z1,z2,z109,z4])],[(0,[z0,z148,z12,z3,z4,z6]),(0,[z0,z1,z12,z218,z4,z6]),(0,[z0,z1,z2,z3,z4,z1334]),(0,[z0,z1,z2,z3,z1335,z6]),(0,[z0,z1,z1336,z3,z4,z6])],[(0,[z956,z0,z20,z3,z4,z6]),(0,[z115,z1,z2,z3,z4,z41]),(0,[z0,z1,z2,z3,z4,z1337]),(0,[z0,z1,z1338,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z1339])],[(0,[z0,z1,z20,z3,z4,z370]),(0,[z0,z1,z2,z1340,z4,z6]),(0,[z0,z1,z2,z117,z65,z107]),(0,[z0,z1,z2,z3,z740,z4])],[(0,[z162,z1,z12,z3,z4,z6]),(0,[z0,z237,z192,z3,z4,z6]),(0,[z615,z1,z2,z3,z46,z6]),(0,[z0,z1,z2,z3,z4,z1341]),(0,[z0,z1,z2,z3,z4,z1342])],[(0,[z0,z1,z12,z971,z3,z4])],[(0,[z0,z1,z1343,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z1344]),(0,[z0,z1,z12,z181,z4,z6]),(0,[z0,z70,z2,z3,z4,z6]),(0,[z0,z1,z168,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z1345]),(0,[z0,z1,z2,z3,z338,z559]),(0,[z0,z1,z2,z589,z109,z4])]],
   [[(0,[z0,z1,z2,z181,z4,z100]),(0,[z444,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z1106]),(0,[z0,z1,z2,z3,z1346,z6])],[(0,[z306,z1,z12,z3,z4,z6]),(1,[z284,z2,z80,z4,z6])],[(0,[z0,z1,z12,z3,z50,z6]),(0,[z0,z148,z20,z3,z4,z6]),(0,[z0,z1,z20,z218,z4,z6])],[(0,[z199,z0,z342,z3,z4,z6]),(0,[z0,z1,z917,z3,z4,z6]),(0,[z297,z1,z2,z3,z46,z6]),(0,[z0,z1,z446,z3,z71,z6])],[(0,[z0,z1,z12,z3,z4,z6]),(1,[z1,z12,z315,z4,z6]),(0,[z133,z2,z80,z166,z4,z6]),(0,[z0,z1347,z1,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z100]),(0,[z1,z12,z3,z343,z4,z6]),(0,[z0,z1,z12,z3,z263,z47]),(0,[z0,z1,z2,z813,z4,z6]),(0,[z0,z1,z2,z3,z1348,z6]),(0,[z0,z1,z239,z3,z4,z35])],[(0,[z1,z12,z3,z146,z4,z6])],[(1,[z199,z12,z3,z4,z6]),(0,[z199,z0,z24,z3,z4,z6]),(0,[z1,z177,z3,z4,z46,z6])],[(0,[z0,z1,z20,z181,z4,z6]),(0,[z0,z1,z2,z1349,z4,z6]),(0,[z190,z1,z12,z3,z4,z6]),(0,[z0,z1,z1155,z3,z4,z6]),(0,[z0,z1,z1350,z3,z4,z6])],[(0,[z0,z342,z14,z3,z4,z6]),(0,[z0,z1351,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z1352,z6]),(0,[z498,z0,z1,z2,z6,z107])],[(0,[z306,z1,z20,z3,z4,z6]),(0,[z0,z284,z355,z3,z4,z6]),(0,[z0,z1353,z2,z3,z4,z6]),(0,[z87,z1,z2,z163,z4,z41]),(0,[z123,z0,z2,z166,z71,z6]),(0,[z0,z329,z2,z3,z4,z28])],[(0,[z0,z1,z2,z1110,z4,z6]),(0,[z0,z1,z20,z3,z50,z6]),(0,[z0,z1,z1354,z3,z4,z6]),(0,[z32,z0,z1,z3,z4,z130])],[(1,[z0,z2,z907,z4,z6]),(0,[z0,z1,z1355,z3,z4,z6]),(0,[z0,z1,z2,z109,z4,z215])],[(0,[z0,z1,z20,z3,z4,z6]),(0,[z0,z1,z355,z3,z4,z264]),(0,[z1356,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z181,z4,z75]),(0,[z427,z1,z12,z3,z4,z6]),(0,[z0,z1,z20,z3,z263,z47]),(0,[z0,z1,z2,z3,z4,z1125]),(0,[z0,z1,z2,z1357,z4,z6]),(1,[z737,z1,z3,z4,z6]),(0,[z0,z1,z2,z3,z1358,z6]),(0,[z0,z1,z2,z78,z50,z6])],[(0,[z175,z1,z12,z3,z4,z6]),(0,[z1,z2,z3,z4,z1070,z6])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 494) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 494).take 495) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 989).take 382) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1371)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [494, 495, 382] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 109).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 109).take 110).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 219).take 115).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 334).take 109).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc4 : chunkOK 5 ((bkB.flatten.drop 443).take 69).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 512)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [109, 110, 115, 109, 69] = true :=
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

end PEqualNP.Outside.L_meta_39591

theorem PEqualNP.Outside.L_meta_39591 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4294901486 * 2 ^ 32 + 4278124192) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4294901486 * 2 ^ 32 + 4278124192) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_39591.solve