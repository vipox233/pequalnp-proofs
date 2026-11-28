import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_36350

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
  Nat.testBit (4277075690 * 2 ^ 32 + 4277074144) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x80900004282451c5#64 ++ 0x202400010a091471#64 ++ 0x7be8520cf86cd3cf#64 ++ 0xdefa14833e1b34f3#64 : BitVec 256),
   (0x08200431608522d0#64 ++ 0x4208010c582148b4#64 ++ 0xf7dcac73619723f3#64 ++ 0xbdf72b1cd865c8fc#64 : BitVec 256),
   (0x204130828218042a#64 ++ 0x88104c20a086010a#64 ++ 0xeebf318386183c7f#64 ++ 0x7bafcc60e1860f1f#64 : BitVec 256),
   (0x1282c15c05e03b01#64 ++ 0x04a0b05701780ec0#64 ++ 0xde7fc1fc07e03f82#64 ++ 0xf79ff07f01f80fe0#64 : BitVec 256),
   (0x2303fa00075a8002#64 ++ 0x08c0fe8001d6a000#64 ++ 0xc1fbfe0007ffc001#64 ++ 0xf07eff8001fff000#64 : BitVec 256),
   (0x3c03ffebd0000000#64 ++ 0x0f00fffaf4000000#64 ++ 0x3ffbfffff8000000#64 ++ 0x0ffefffffe000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [0, 1]⟩, ⟨.or, [6, 2]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [0, 3]⟩, ⟨.or, [2, 4]⟩, ⟨.and, [7, 3]⟩, ⟨.and, [9, 5]⟩, ⟨.or, [12, 10]⟩, ⟨.and, [8, 13]⟩, ⟨.or, [14, 11]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x08200431608522d0 0x4208010c582148b4 0xf7dcac73619723f3 0xbdf72b1cd865c8fc

def z1 : W := mkw 0x1282c15c05e03b01 0x04a0b05701780ec0 0xde7fc1fc07e03f82 0xf79ff07f01f80fe0

def z2 : W := mkw 0x204130828218042a 0x88104c20a086010a 0xeebf318386183c7f 0x7bafcc60e1860f1f

def z3 : W := mkw 0x2303fa00075a8002 0x08c0fe8001d6a000 0xc1fbfe0007ffc001 0xf07eff8001fff000

def z4 : W := mkw 0x3c03ffebd0000000 0x0f00fffaf4000000 0x3ffbfffff8000000 0x0ffefffffe000000

def z5 : W := mkw 0x8090000408205105 0x2024000102081441 0x49e8520c986cd00d 0xd27a1483261b3403

def z6 : W := mkw 0x80900004282451c5 0x202400010a091471 0x7be8520cf86cd3cf 0xdefa14833e1b34f3

def z7 : W := mkw 0x3c23fffbf08522d0 0x4f08fffefc2148b4 0xfffffffff99723f3 0xbffffffffe65c8fc

def z8 : W := mkw 0x204130828218042a 0x88104c20a086010a 0x2e84318380183c7f 0x0ba10c60e0060f1f

def z9 : W := mkw 0x00200000200500d0 0x4008000008014034 0x0000000000170071 0x000000000005c01c

def z10 : W := mkw 0x0820043140812210 0x4208010c50204884 0x0404007300002030 0x0101001cc000080c

def z11 : W := mkw 0x0302ca0005428000 0x00c0b2800150a000 0x0140ce0001e7c000 0x805033800079f000

def z12 : W := mkw 0x2343fa82875a842a 0x88d0fea0a1d6a10a 0xefffff8387fffc7f 0xfbffffe0e1ffff1f

def z13 : W := mkw 0x1f02cf6955428000 0x07c0b3da5550a000 0x1140ce7c79e7c000 0x8450339f1e79f000

def z14 : W := mkw 0x3f03ffebd75a8002 0x0fc0fffaf5d6a000 0xfffbffffffffc001 0xfffefffffffff000

def z15 : W := mkw 0x0202c00005400000 0x0080b00001500000 0xc07bc00007e00000 0xf01ef00001f80000

def z16 : W := mkw 0x1c0005ebd0000000 0x0700017af4000000 0x3e0001fff8000000 0x0f80007ffe000000

def z17 : W := mkw 0x3383fb5c07fabb03 0x0ce0fed701feaec0 0xdffffffc07ffff83 0xf7ffffff01ffffe0

def z18 : W := mkw 0x1080015c00a03b01 0x0420005700280ec0 0x1e0401fc00003f82 0x0781007f00000fe0

def z19 : W := mkw 0x1202c15805c02a00 0x0480b05601700a80 0x841781f007802c00 0x2105e07c01e00b00

def z20 : W := mkw 0x3e03fffbd5c02a00 0x0f80fffef5700a80 0xbfffffffff802c00 0x2fffffffffe00b00

def z21 : W := mkw 0x0000000000000000 0x0000000000000000 0xe69c200300102073 0x39a70800c004081c

def z22 : W := mkw 0x204130828218042a 0x88104c20a086010a 0x0823118086081c0c 0x4208c46021820703

def z23 : W := mkw 0xa393fa042f7ed1c7 0x28e4fe810bdfb471 0x7beb520cfe6cd3cf 0xdefad4833f9b34f3

def z24 : W := mkw 0x0800042140000000 0x0200010850000000 0x37d8ac7360000000 0x0df62b1cd8000000

def z25 : W := mkw 0x2003fa0000000000 0x0800fe8000000000 0xc1fbfe0001970001 0xb07eff800065c000

def z26 : W := mkw 0x1c02cf6950000000 0x0700b3da54000000 0x1140ce7c78000000 0x0450339f1e000000

def z27 : W := mkw 0x3f03ffebd75a8002 0x0fc0fffaf5d6a000 0xbffbffffff930000 0x2ffeffffffe4c000

def z28 : W := mkw 0x0000000000000000 0x0000000000000000 0xc1d8ac0001970001 0xb0762b000065c000

def z29 : W := mkw 0x2c013ea3d0000000 0x0b004fa8f4000000 0x21803e03f8000000 0x08600f80fe000000

def z30 : W := mkw 0x204130828218042a 0x88104c20a086010a 0x8417218306102c30 0x2105c860c1840b0c

def z31 : W := mkw 0x3c03ffebd0000000 0x0f00fffaf4000000 0x0413adf300000000 0x0104eb7cc0000000

def z32 : W := mkw 0xbc93ffeff82451c5 0x2f24fffbfe091471 0x7ffbfffff86cd3cf 0xdffefffffe1b34f3

def z33 : W := mkw 0x3c43ffebd218042a 0x8f10fffaf486010a 0xfffffffffe183c7f 0x7fffffffff860f1f

def z34 : W := mkw 0x80900004282451c5 0x202400010a091471 0x000000000064c380 0x80000000001930e0

def z35 : W := mkw 0x0000000000000000 0x0000000000000000 0x2a0000008000104e 0x0a80000020000413

def z36 : W := mkw 0x1002c14800000000 0x0400b05200000000 0x041381f000000000 0x0104e07c00000000

def z37 : W := mkw 0x0000000000000000 0x0000000000000000 0x6aa810008008104f 0x5aaa040020020413

def z38 : W := mkw 0xa393fa042f7ed1c7 0x28e4fe810bdfb471 0xfbfbfe0cffffd3cf 0xfefeff833ffff4f3

def z39 : W := mkw 0x3c03ffebd0000000 0x0f00fffaf4000000 0x3e2353fff8000000 0x0f88d4fffe000000

def z40 : W := mkw 0x2001300002180002 0x08004c0000860000 0xeabb30008618104f 0x7aaecc0021860413

def z41 : W := mkw 0x2303fa00075a8002 0x08c0fe8001d6a000 0x01c0fe0001ffc001 0x80703f80007ff000

def z42 : W := mkw 0x0000001000802200 0x0000000400200880 0xd65c807001802382 0xb597201c006008e0

def z43 : W := mkw 0x08200421600500d0 0x4208010858014034 0x21802c0360170071 0x08600b00d805c01c

def z44 : W := mkw 0x80900004282451c5 0x202400010a091471 0xfffc720ff87cf3ff 0xffff1c83fe1f3cff

def z45 : W := mkw 0x88300421680540d4 0x620c01085a015035 0x21803e03f81fc07d 0x08600f80fe07f01f

def z46 : W := mkw 0x204130828218042a 0x88104c20a086010a 0x208030038018007d 0x08200c00e006001f

def z47 : W := mkw 0xa0d13086aa3c55ef 0xa8344c21aa8f157b 0xffff738ffe7cffff 0xffffdce3ff9f3fff

def z48 : W := mkw 0x004000828218042a 0x80100020a086010a 0xee04018386183c7f 0x7b810060e1860f1f

def z49 : W := mkw 0x1282c15c05e03b01 0x04a0b05701780ec0 0xfeffe1ff07f03ff3 0xffbff87fc1fc0ffc

def z50 : W := mkw 0xa3d3fa86af7ed5ef 0xa8f4fea1abdfb57b 0xffffff8fffffffff 0xffffffe3ffffffff

def z51 : W := mkw 0x3e03ffebd5400000 0x0f80fffaf5500000 0xfffbffffffe00000 0xfffefffffff80000

def z52 : W := mkw 0x1002c14800000000 0x0400b05200000000 0x3ffbd3fcf8000000 0x0ffef4ff3e000000

def z53 : W := mkw 0x88300431688562d4 0x620c010c5a2158b5 0xf7dcbe73f99fe3ff 0xbdf72f9cfe67f8ff

def z54 : W := mkw 0x0000000000000000 0x0000000000000000 0xce3f018006003c02 0x738fc06001800f00

def z55 : W := mkw 0x1282c14c05601901 0x04a0b05301580640 0x0823418c06601c00 0x4208d06301980700

def z56 : W := mkw 0x3e83ffffd5e03b01 0x0fa0fffff5780ec0 0x3ffbfffff9e00380 0x8ffefffffe7800e0

def z57 : W := mkw 0x0080000400201101 0x0020000100080440 0x5a68400c00601382 0xd69a1003001804e0

def z58 : W := mkw 0x80d000042a3c55ef 0xa03400010a8f157b 0xc0040000067cffff 0xf0010000019f3fff

def z59 : W := mkw 0x0820043140812210 0x4208010c50204884 0xd65cac73019323b2 0xb5972b1cc064c8ec

def z60 : W := mkw 0x80100000280440c4 0x200400000a011031 0x21801200f80cc04d 0x086004803e033013

def z61 : W := mkw 0x086004b3e08526f8 0xc218012cf82149be 0xffdcadf3e1973fff 0xbff72b7cf865cfff

def z62 : W := mkw 0x0000000000000000 0x0000000000000000 0x41e85200006cc001 0xd07a1480001b3000

def z63 : W := mkw 0x2303fa00075a8002 0x08c0fe8001d6a000 0x8013ac0007930000 0x2004eb0001e4c000

def z64 : W := mkw 0x1282c15c05e03b01 0x04a0b05701780ec0 0x1e2741fc06603f82 0x4789d07f01980fe0

def z65 : W := mkw 0x0202c01005c02200 0x0080b00401700880 0xd67fc07007e02382 0xf59ff01c01f808e0

def z66 : W := mkw 0x32c3f1de87f83f2b 0x8cb0fc77a1fe0fca 0xfefff1ff87f83fff 0xffbffc7fe1fe0fff

def z67 : W := mkw 0x1082c15c00a03b01 0x0420b05700280ec0 0x1e7fc1fc00003f82 0x079ff07f00000fe0

def z68 : W := mkw 0x02a0001425e53bd1 0x40a8000509794ef4 0xc004000007f73ff3 0xf001000001fdcffc

def z69 : W := mkw 0x88b00425682551d5 0x622c01095a095475 0x7be87e0ff87fd3ff 0xdefa1f83fe1ff4ff

def z70 : W := mkw 0x80900004282451c5 0x202400010a091471 0x40000000006cd3cf 0xd0000000001b34f3

def z71 : W := mkw 0x0280001405e03b01 0x00a0000501780ec0 0xc004000007e03f82 0xf001000001f80fe0

def z72 : W := mkw 0x3e83ffffd5e03b01 0x0fa0fffff5780ec0 0xffffffffffe03f82 0xfffffffffff80fe0

def z73 : W := mkw 0x00000000200400c0 0x0000000008010030 0x73c80000600403c3 0x9cf20000180100f0

def z74 : W := mkw 0x004000000218042a 0x801000000086010a 0xc004000006183c7f 0x7001000001860f1f

def z75 : W := mkw 0x00200010208522d0 0x40080004082148b4 0xc1dcac00019723f3 0xb0772b000065c8fc

def z76 : W := mkw 0x2303fa00075a8002 0x08c0fe8001d6a000 0xc013ac0007ffc001 0xf004eb0001fff000

def z77 : W := mkw 0x00800004202411c1 0x0020000108090470 0x7be8400c606413c3 0xdefa1003181904f0

def z78 : W := mkw 0x2303fa00075a8002 0x08c0fe8001d6a000 0x002352000668c000 0x4008d480019a3000

def z79 : W := mkw 0x2b23fe3167dfa2d2 0x4ac8ff8c59f7e8b4 0xf7fffe7367ffe3f3 0xfdffff9cd9fff8fc

def z80 : W := mkw 0x08200431608522d0 0x4208010c582148b4 0x36040073600023f2 0x0d81001cd80008fc

def z81 : W := mkw 0x2343fa82875a842a 0x88d0fea0a1d6a10a 0xc9fbff8087ffdc0d 0xf27effe021fff703

def z82 : W := mkw 0x88b0043568a573d5 0x622c010d5a295cf5 0xfffcfe7ff9fff3ff 0xffff3f9ffe7ffcff

def z83 : W := mkw 0x8090000408205105 0x2024000102081441 0x0820520c9868d00c 0x42081483261a3403

def z84 : W := mkw 0x9292c15c0de07b05 0x24a4b05703781ec1 0xde7fd3fc9fe8ff8e 0xf79ff4ff27fa3fe3

def z85 : W := mkw 0x204130828218042a 0x88104c20a086010a 0x0003018006000c00 0x0000c06001800300

def z86 : W := mkw 0x00000000200400c0 0x0000000008010030 0x32000000600003c2 0x0c800000180000f0

def z87 : W := mkw 0x204130828218042a 0x88104c20a086010a 0x0000200300100030 0x00000800c004000c

def z88 : W := mkw 0xa313fa002f5ec0c6 0x28c4fe800bd7b031 0xe1fbfe00ffffc04d 0xf87eff803ffff013

def z89 : W := mkw 0xbcb3fffff8a573d5 0x6f2cfffffe295cf5 0xfffffffff9fff3ff 0xfffffffffe7ffcff

def z90 : W := mkw 0x80100000280440c4 0x200400000a011031 0x010002007804c000 0x004000801e013000

def z91 : W := mkw 0x9292c15c2de47bc5 0x24a4b0570b791ef1 0xffffd3fcffecffcf 0xfffff4ff3ffb3ff3

def z92 : W := mkw 0x9c92cf6d782451c5 0x2724b3db5e091471 0x7be8de7cf86cd3cf 0xdefa379f3e1b34f3

def z93 : W := mkw 0x2303fa00075a8002 0x08c0fe8001d6a000 0x8153ee0007f7c000 0xa054fb8001fdf000

def z94 : W := mkw 0x08200431608522d0 0x4208010c582148b4 0x11408c7061870380 0x8450231c1861c0e0

def z95 : W := mkw 0x3243f1da87d82e2a 0x8c90fc76a1f60b8a 0xeebfb1f387983c7f 0x7bafec7ce1e60f1f

def z96 : W := mkw 0x0000000000000000 0x0000000000000000 0x7be8520cf86cc001 0xdefa14833e1b3000

def z97 : W := mkw 0x23413082875a842a 0x88d04c20a1d6a10a 0xeebf318387fffc7f 0xfbafcc60e1ffff1f

def z98 : W := mkw 0x0000000000000000 0x0000000000000000 0x1658807000000000 0x0596201c00000000

def z99 : W := mkw 0x2001308280000000 0x08004c20a0000000 0x2ebb318380000000 0x0baecc60e0000000

def z100 : W := mkw 0xbf93ffefff7ed1c7 0x2fe4fffbffdfb471 0xfffbffffffffd3cf 0xfffefffffffff4f3

def z101 : W := mkw 0x0820043140812210 0x4208010c50204884 0x8414ac7301932030 0x21052b1cc064c80c

def z102 : W := mkw 0x80900004282451c5 0x202400010a091471 0x00000000000013ce 0x00000000000004f3

def z103 : W := mkw 0x00200010208522d0 0x40080004082148b4 0xc0040000019723f3 0xb00100000065c8fc

def z104 : W := mkw 0x3403fbca90000000 0x0d00fef2a4000000 0x0823538c98000000 0x0208d4e326000000

def z105 : W := mkw 0x08200421600500d0 0x4208010858014034 0xe79c2c0360172073 0x39e70b00d805c81c

def z106 : W := mkw 0x1282c15c05e03b01 0x04a0b05701780ec0 0x1040c07c01e00380 0x8410301f007800e0

def z107 : W := mkw 0x0800042140000000 0x0200010850000000 0xf7d8ac7361970001 0xbdf62b1cd865c000

def z108 : W := mkw 0x1202c14805400000 0x0480b05201500000 0xde7bc1fc07e00000 0xf79ef07f01f80000

def z109 : W := mkw 0x3c4135ebd218042a 0x8f104d7af486010a 0xfebf31fffe183c7f 0x7fafcc7fff860f1f

def z110 : W := mkw 0x08000421600400c0 0x0200010858010030 0x77d8ac73600403c3 0x9df62b1cd80100f0

def z111 : W := mkw 0x3f23fffbf7dfa2d2 0x4fc8fffefdf7e8b4 0xffffffffffffe3f3 0xfffffffffffff8fc

def z112 : W := mkw 0x829000142de47bc5 0x20a400050b791ef1 0xc004000007ecffcf 0xf001000001fb3ff3

def z113 : W := mkw 0x21013a00021a8002 0x08404e800086a000 0x000012000008c000 0x0000048000023000

def z114 : W := mkw 0x204130000218042a 0x88104c000086010a 0xc0bf300006183c7f 0x702fcc0001860f1f

def z115 : W := mkw 0x1aa2c57d65e53bd1 0x46a8b15f59794ef4 0xffffedff67f73ff3 0xfffffb7fd9fdcffc

def z116 : W := mkw 0x0c0004a3d0000000 0x03000128f4000000 0x20000003f8000000 0x08000000fe000000

def z117 : W := mkw 0x3c03ffebd0000000 0x0f00fffaf4000000 0x1553efff78000000 0x0554fbffde000000

def z118 : W := mkw 0x3703fbca975a8002 0x0dc0fef2a5d6a000 0x0823538c9e68c000 0x4208d4e3279a3000

def z119 : W := mkw 0x1282c15c05e03b01 0x04a0b05701780ec0 0xdfffedfc07f73f83 0xf7fffb7f01fdcfe0

def z120 : W := mkw 0x0040008280000428 0x80100020a000010a 0xee9c218380103c7f 0x3ba70860e0040f1f

def z121 : W := mkw 0x20613092a29d26fa 0xc8184c24a8a749be 0xeebf3183879f3fff 0xfbafcc60e1e7cfff

def z122 : W := mkw 0x1c02c5ebd0000000 0x0700b17af4000000 0x3e7bc1fff8000000 0x0f9ef07ffe000000

def z123 : W := mkw 0x21013a00021a8002 0x08404e800086a000 0x01803e00001fc001 0x00600f800007f000

def z124 : W := mkw 0x80900004282451c5 0x202400010a091471 0x1000000c78000380 0x040000031e0000e0

def z125 : W := mkw 0x1e82c5ffd5e03b01 0x07a0b17ff5780ec0 0xfe7fc1ffffe03f82 0xff9ff07ffff80fe0

def z126 : W := mkw 0x0000000000000000 0x0000000000000000 0xc1f8fe0001ffc001 0xf07e3f80007ff000

def z127 : W := mkw 0x0000000000000000 0x0000000000000000 0x3be8520cf8000000 0x0efa14833e000000

def z128 : W := mkw 0x2001300002180002 0x08004c0000860000 0xc0bb300006180001 0x702ecc0001860000

def z129 : W := mkw 0x3403fbca90000000 0x0d00fef2a4000000 0x2ebb738f98000000 0x0baedce3e6000000

def z130 : W := mkw 0x0000001000802200 0x0000000400200880 0xf6dca073019023f3 0xbdb7281cc06408fc

def z131 : W := mkw 0x0302ca0005428000 0x00c0b2800150a000 0x41e8de0001efc001 0xd07a3780007bf000

def z132 : W := mkw 0x3c03ffebd0000000 0x0f00fffaf4000000 0xfffffffffe003c02 0x7fffffffff800f00

def z133 : W := mkw 0xbc93ffeff82451c5 0x2f24fffbfe091471 0x3ffbfffff80013ce 0x0ffefffffe0004f3

def z134 : W := mkw 0x2343fa82875a842a 0x88d0fea0a1d6a10a 0xe1fbfe0387ffc07d 0xf87eff80e1fff01f

def z135 : W := mkw 0x3f03ff69575a8002 0x0fc0ffda55d6a000 0xd1fbfe7c7fffc001 0xf47eff9f1ffff000

def z136 : W := mkw 0x2c413ea3d218042a 0x8b104fa8f486010a 0x21803e03f818007d 0x08600f80fe06001f

def z137 : W := mkw 0x3443fbca9218042a 0x8d10fef2a486010a 0xeebf738f9e183c7f 0x7bafdce3e7860f1f

def z138 : W := mkw 0x08200431608522d0 0x4208010c582148b4 0x9554ac73619723b0 0xa5552b1cd865c8ec

def z139 : W := mkw 0x03000000075a8002 0x00c0000001d6a000 0xc000000007ffc001 0xf000000001fff000

def z140 : W := mkw 0x08200431608522d0 0x4208010c582148b4 0xf7fcfe7361ffe3f3 0xfdff3f9cd87ff8fc

def z141 : W := mkw 0x88b0043568a573d5 0x622c010d5a295cf5 0xf7dcac7361fff3ff 0xfdf72b1cd87ffcff

def z142 : W := mkw 0x1002c14800000000 0x0400b05200000000 0x1e7bc1fc00000000 0x079ef07f00000000

def z143 : W := mkw 0x0280001405e03b01 0x00a0000501780ec0 0xce3f018007e03f82 0xf38fc06001f80fe0

def z144 : W := mkw 0x80100000280440c4 0x200400000a011031 0x61e85200f86cc04d 0xd87a14803e1b3013

def z145 : W := mkw 0x88b0043568a573d5 0x622c010d5a295cf5 0xf7dcee7f79f7e3f3 0xbdf73b9fde7df8fc

def z146 : W := mkw 0x1002c14800000000 0x0400b05200000000 0x1040c07c00000000 0x0410301f00000000

def z147 : W := mkw 0x0000000000000000 0x0000000000000000 0x0823018006001c00 0x4208c06001800700

def z148 : W := mkw 0x80900004282451c5 0x202400010a091471 0xffff538cfe6cffcf 0xffffd4e33f9b3ff3

def z149 : W := mkw 0x1c00056950000000 0x0700015a54000000 0x1000007c78000000 0x0400001f1e000000

def z150 : W := mkw 0x2203f00007580002 0x0880fc0001d60000 0xc0fbf00007f80001 0xf03efc0001fe0000

def z151 : W := mkw 0x829000142de47bc5 0x20a400050b791ef1 0xfbec520cffecffcf 0xfefb14833ffb3ff3

def z152 : W := mkw 0x2003fa0000000000 0x0800fe8000000000 0x01fbfe0000000000 0x007eff8000000000

def z153 : W := mkw 0x286134b3e29d26fa 0xca184d2cf8a749be 0xf7dcbc73e19f23ff 0xbdf72f1cf867c8ff

def z154 : W := mkw 0x0202c00005400000 0x0080b00001500000 0xc1fbd20007ecc001 0xf07ef48001fb3000

def z155 : W := mkw 0x3c03ff6950000000 0x0f00ffda54000000 0x11fbfe7c78000000 0x047eff9f1e000000

def z156 : W := mkw 0x1000014800000000 0x0400005200000000 0x1e0001fc00000000 0x0780007f00000000

def z157 : W := mkw 0x204130828218042a 0x88104c20a086010a 0xffff738ffe183c7f 0x7fffdce3ff860f1f

def z158 : W := mkw 0x004000000218042a 0x801000000086010a 0x0000000006081c0c 0x4000000001820703

def z159 : W := mkw 0x3c03ffebd0000000 0x0f00fffaf4000000 0x7ffbfffff86cc001 0xdffefffffe1b3000

def z160 : W := mkw 0x08200431608522d0 0x4208010c582148b4 0xc414ac73019723f3 0xb1052b1cc065c8fc

def z161 : W := mkw 0x286134b3e29d26fa 0xca184d2cf8a749be 0xffffbdf3e79f3fff 0xffffef7cf9e7cfff

def z162 : W := mkw 0xa1113a002a1ec0c6 0x28444e800a87b031 0x21803e00f81fc04d 0x08600f803e07f013

def z163 : W := mkw 0xa0d13086aa3c55ef 0xa8344c21aa8f157b 0x7be8720ff87cd3ff 0xdefa1c83fe1f34ff

def z164 : W := mkw 0x0080000400201101 0x0020000100080440 0x5be8520c006cd383 0xd6fa1483001b34e0

def z165 : W := mkw 0x80900004282451c5 0x202400010a091471 0x7a68400cf86013ce 0xde9a10033e1804f3

def z166 : W := mkw 0x3f43ffebd75a842a 0x8fd0fffaf5d6a10a 0xfffffffffffffc7f 0xffffffffffffff1f

def z167 : W := mkw 0x3ba3ff7d67ffbbd3 0x4ee8ffdf59ffeef4 0xffffffff67fffff3 0xffffffffd9fffffc

def z168 : W := mkw 0x3403fbca90000000 0x0d00fef2a4000000 0x09fbff8c98000000 0x027effe326000000

def z169 : W := mkw 0xbc93ffefd8205105 0x2f24fffbf6081441 0x3ffbfffff868d00c 0x4ffefffffe1a3403

def z170 : W := mkw 0x0200000005400000 0x0080000001500000 0xc000000007e00000 0xf000000001f80000

def z171 : W := mkw 0x2343fa00075a842a 0x88d0fe8001d6a10a 0xc1fffe0007fffc7f 0xf07fff8001ffff1f

def z172 : W := mkw 0x80900004282451c5 0x202400010a091471 0x1140420c7864c380 0x845010831e1930e0

def z173 : W := mkw 0x204130828218042a 0x88104c20a086010a 0x000010008008000c 0x0000040020020003

def z174 : W := mkw 0x1080015c00a03b01 0x0420005700280ec0 0x1000007c00000380 0x0400001f000000e0

def z175 : W := mkw 0x839000042f7ed1c7 0x20e400010bdfb471 0xfbe8520cffffd3cf 0xfefa14833ffff4f3

def z176 : W := mkw 0x1202c15805c02a00 0x0480b05601700a80 0xc47fc1f007e02c00 0xf11ff07c01f80b00

def z177 : W := mkw 0x3c03ffebd0000000 0x0f00fffaf4000000 0xfffffffff8102073 0x3ffffffffe04081c

def z178 : W := mkw 0x3043f1ca8218042a 0x8c10fc72a086010a 0xfefff1ff86183c7f 0x7fbffc7fe1860f1f

def z179 : W := mkw 0x08a0043560a533d1 0x4228010d58294cf4 0xfffcec7f61f733f3 0xffff3b1fd87dccfc

def z180 : W := mkw 0x3c43ffebd218042a 0x8f10fffaf486010a 0xbffffffffe102c30 0x2fffffffff840b0c

def z181 : W := mkw 0xa1913a042a3ed1c7 0x28644e810a8fb471 0x7be87e0cf87fd3cf 0xdefa1f833e1ff4f3

def z182 : W := mkw 0x0040000000000428 0x801000000000010a 0x0004000000003c7e 0x0001000000000f1f

def z183 : W := mkw 0x0820043140812210 0x4208010c50204884 0xb7dcac7361932030 0x2df72b1cd864c80c

def z184 : W := mkw 0x8090000408205105 0x2024000102081441 0x6aa8520c9868d04f 0x5aaa1483261a3413

def z185 : W := mkw 0x21013a00021a8002 0x08404e800086a000 0x00002c0000130000 0x00000b000004c000

def z186 : W := mkw 0x80900004282451c5 0x202400010a091471 0x61801200f86cd3cf 0xd86004803e1b34f3

def z187 : W := mkw 0x3303fb48075a8002 0x0cc0fed201d6a000 0xdffbfffc07ffc001 0xf7feffff01fff000

def z188 : W := mkw 0x80900004282451c5 0x202400010a091471 0x3a00000cf80013ce 0x0e8000033e0004f3

def z189 : W := mkw 0x204130828218042a 0x88104c20a086010a 0xc417218306183c7f 0x7105c860c1860f1f

def z190 : W := mkw 0x0302ca0005428000 0x00c0b2800150a000 0xc17bce0007e7c000 0xf05ef38001f9f000

def z191 : W := mkw 0x3c013febd0000000 0x0f004ffaf4000000 0x3f803ffff8000000 0x0fe00ffffe000000

def z192 : W := mkw 0x0820042140010010 0x4208010850004004 0x00002c0300130030 0x00000b00c004c00c

def z193 : W := mkw 0x0000000000000000 0x0000000000000000 0xe7dcac0301972073 0xb9f72b00c065c81c

def z194 : W := mkw 0x3c0135ebd0000000 0x0f004d7af4000000 0x3ebb31fff8000000 0x0faecc7ffe000000

def z195 : W := mkw 0x0080001400a03301 0x0020000500280cc0 0xde7cc07c01e03382 0xf79f301f00780ce0

def z196 : W := mkw 0x0302ca0005428000 0x00c0b2800150a000 0x00008c0001830000 0x000023000060c000

def z197 : W := mkw 0x286134a3e21d04fa 0xca184d28f887413e 0x21803c03e01f007d 0x08600f00f807c01f

def z198 : W := mkw 0x3c03ffebd0000000 0x0f00fffaf4000000 0x2ebbbdf380000000 0x0baeef7ce0000000

def z199 : W := mkw 0x1402cb4810000000 0x0500b2d204000000 0x0000420c18000000 0x0000108306000000

def z200 : W := mkw 0x2303fa00275e80c2 0x08c0fe8009d7a030 0xf3fbfe0067ffc3c3 0xfcfeff8019fff0f0

def z201 : W := mkw 0x3c03ffebd0000000 0x0f00fffaf4000000 0x0c33ffff98000000 0x030cffffe6000000

def z202 : W := mkw 0x0000000000000000 0x0000000000000000 0x01408c0001870000 0x805023000061c000

def z203 : W := mkw 0x3383fb5c07fabb03 0x0ce0fed701feaec0 0xde7fedfc07f33f82 0xf79ffb7f01fccfe0

def z204 : W := mkw 0x3ea3fffff5e53bd1 0x4fa8fffffd794ef4 0xfffffffffff73ff3 0xfffffffffffdcffc

def z205 : W := mkw 0x0000000000000000 0x0000000000000000 0x0820520c98000000 0x0208148326000000

def z206 : W := mkw 0x3303fb5807daaa02 0x0cc0fed601f6aa80 0xc5fffff007ffec01 0xf17ffffc01fffb00

def z207 : W := mkw 0x80900004282451c5 0x202400010a091471 0x4820520c986cd3cf 0xd2081483261b34f3

def z208 : W := mkw 0x1202c15805c02a00 0x0480b05601700a80 0xce3f81f007803c02 0x738fe07c01e00f00

def z209 : W := mkw 0x0300000005428000 0x00c000000150a000 0x0000000001e7c000 0x800000000079f000

def z210 : W := mkw 0x2d013ea3d21a8002 0x0b404fa8f486a000 0x21803e03f81fc001 0x08600f80fe07f000

def z211 : W := mkw 0x2303fa00075a8002 0x08c0fe8001d6a000 0xc07bd20007e8c000 0xf01ef48001fa3000

def z212 : W := mkw 0xa0913086a82451c5 0x28244c21aa091471 0x7ffb738ff86cd3cf 0xdffedce3fe1b34f3

def z213 : W := mkw 0x0000000000000000 0x0000000000000000 0x2698200300000000 0x09a60800c0000000

def z214 : W := mkw 0x2303fa0005428000 0x08c0fe800150a000 0x01fbfe0001e7c000 0x807eff800079f000

def z215 : W := mkw 0x00000000200400c0 0x0000000008010030 0xf7dc2003601423f3 0xbdf70800d80508fc

def z216 : W := mkw 0x0040008280000428 0x80100020a000010a 0xee3f018386003c7e 0x7b8fc060e1800f1f

def z217 : W := mkw 0x3c03ffebd0000000 0x0f00fffaf4000000 0x7ffbfffff808104f 0x5ffefffffe020413

def z218 : W := mkw 0x3e83ffffd5e03b01 0x0fa0fffff5780ec0 0xde7fedff07e03f82 0xf79ffb7fc1f80fe0

def z219 : W := mkw 0x0080001400a03b01 0x0020000500280ec0 0x0004000000003f82 0x0001000000000fe0

def z220 : W := mkw 0x1382cb5c05e2bb01 0x04e0b2d70178aec0 0xdf7fcffc07e7ff82 0xf7dff3ff01f9ffe0

def z221 : W := mkw 0x08200431608522d0 0x4208010c582148b4 0xffffadf367973ff3 0xffffeb7cd9e5cffc

def z222 : W := mkw 0x08200431608522d0 0x4208010c582148b4 0xfffcfe7ff99723f3 0xbfff3f9ffe65c8fc

def z223 : W := mkw 0x1000015800802a00 0x0400005600200a80 0x040401f000002c00 0x0101007c00000b00

def z224 : W := mkw 0x0282c00405601101 0x00a0b00101580440 0xda7bc00c07e01382 0xf69ef00301f804e0

def z225 : W := mkw 0x21413a82821a842a 0x88504ea0a086a10a 0x21803e03801fc07d 0x08600f80e007f01f

def z226 : W := mkw 0x0000000000000000 0x0000000000000000 0x6288000000000043 0x18a2000000000010

def z227 : W := mkw 0x0000000000000000 0x0000000000000000 0x6be85200806cd04f 0xdafa1480201b3413

def z228 : W := mkw 0x204130828218042a 0x88104c20a086010a 0xe0bb30038618007d 0x782ecc00e186001f

def z229 : W := mkw 0x3c03ffebd0000000 0x0f00fffaf4000000 0x1963dffcf8000000 0x0658f7ff3e000000

def z230 : W := mkw 0x2343fa82875a842a 0x88d0fea0a1d6a10a 0xeebf73838678fc7f 0x7bafdce0e19e3f1f

def z231 : W := mkw 0x204130828218042a 0x88104c20a086010a 0xae17218386103c7e 0x2b85c860e1840f1f

def z232 : W := mkw 0x0000001000802200 0x0000000400200880 0xd7dcac7001972383 0xb5f72b1c0065c8e0

def z233 : W := mkw 0x2001300002180002 0x08004c0000860000 0xcebf318006183c03 0x73afcc6001860f00

def z234 : W := mkw 0x1c02cfebd0000000 0x0700b3faf4000000 0x3f40cffff8000000 0x0fd033fffe000000

def z235 : W := mkw 0x3c43ffebd0000428 0x8f10fffaf400010a 0x3ffffffff8003c7e 0x0ffffffffe000f1f

def z236 : W := mkw 0x0040008280000428 0x80100020a000010a 0x2e04018380003c7e 0x0b810060e0000f1f

def z237 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z238 : W := mkw 0x08200431608522d0 0x4208010c582148b4 0x31c0ac73619703f1 0x8c702b1cd865c0fc

def z239 : W := mkw 0x3f83ffffd7fabb03 0x0fe0fffff5feaec0 0xffffffffffffff83 0xffffffffffffffe0

def z240 : W := mkw 0x3c23fffbf08522d0 0x4f08fffefc2148b4 0xf7dfadf3619723f3 0xbdf7eb7cd865c8fc

def z241 : W := mkw 0x839000042f7ed1c7 0x20e400010bdfb471 0xc000000007ffd3cf 0xf000000001fff4f3

def z242 : W := mkw 0x3c43ffebd218042a 0x8f10fffaf486010a 0xeebfbdf386183c7f 0x7bafef7ce1860f1f

def z243 : W := mkw 0x2c03fea3d0000000 0x0b00ffa8f4000000 0x21fbfe03f8000000 0x087eff80fe000000

def z244 : W := mkw 0x03400000075a842a 0x80d0000001d6a10a 0xc004000007fffc7f 0xf001000001ffff1f

def z245 : W := mkw 0x3383fb5c07fabb03 0x0ce0fed701feaec0 0xde7fd3fc07e8ff82 0xf79ff4ff01fa3fe0

def z246 : W := mkw 0x1c02cf6950000000 0x0700b3da54000000 0x1f7bcffc78000000 0x07def3ff1e000000

def z247 : W := mkw 0x0000000000000000 0x0000000000000000 0x208010008008004d 0x0820040020020013

def z248 : W := mkw 0x00000000200400c0 0x0000000008010030 0x73e85200606cc3c3 0xdcfa1480181b30f0

def z249 : W := mkw 0x1c0005ebd0000000 0x0700017af4000000 0x3fd8adfff8000000 0x0ff62b7ffe000000

def z250 : W := mkw 0x1e82cf7d55e03b01 0x07a0b3df55780ec0 0xdf7fcffc7fe03f82 0xf7dff3ff1ff80fe0

def z251 : W := mkw 0x0280001405e03b01 0x00a0000501780ec0 0xd65c807007e03f82 0xf597201c01f80fe0

def z252 : W := mkw 0x0202c00005400000 0x0080b00001500000 0x0040c00001e00000 0x8010300000780000

def z253 : W := mkw 0x1282c15c05e03b01 0x04a0b05701780ec0 0x9e1781fc07803f82 0x2785e07f01e00fe0

def z254 : W := mkw 0x3683fbde95e03b01 0x0da0fef7a5780ec0 0xde7fd3fc9fe03f82 0xf79ff4ff27f80fe0

def z255 : W := mkw 0x2303fa00075a8002 0x08c0fe8001d6a000 0xc07bec0007f30000 0xf01efb0001fcc000

def z256 : W := mkw 0x2303fa00075a8002 0x08c0fe8001d6a000 0xc0bb72000678c001 0x702edc80019e3000

def z257 : W := mkw 0x2b03fe21475a8002 0x0ac0ff8851d6a000 0xf7fbfe7367ffc001 0xfdfeff9cd9fff000

def z258 : W := mkw 0x0a22c43165c522d0 0x4288b10c597148b4 0xf7ffec7367f723f3 0xfdfffb1cd9fdc8fc

def z259 : W := mkw 0xa0513082aa1c44ee 0xa8144c20aa87113b 0x21803203f81cc07d 0x08600c80fe07301f

def z260 : W := mkw 0x0000000000000000 0x0000000000000000 0x8417018006002c00 0x2105c06001800b00

def z261 : W := mkw 0x2001300002180002 0x08004c0000860000 0x0023100006080000 0x4008c40001820000

def z262 : W := mkw 0x3c03ffebd0000000 0x0f00fffaf4000000 0xfffbfffff9970001 0xbffefffffe65c000

def z263 : W := mkw 0x0040008280000428 0x80100020a000010a 0x0404018300002c30 0x01010060c0000b0c

def z264 : W := mkw 0x9092c14c282451c5 0x2424b0530a091471 0x7ffbd3fcf86cd3cf 0xdffef4ff3e1b34f3

def z265 : W := mkw 0x1002c14800000000 0x0400b05200000000 0xde7fc1fc06003c02 0x779ff07f01800f00

def z266 : W := mkw 0x1c0005ebd0000000 0x0700017af4000000 0x040001f300000000 0x0100007cc0000000

def z267 : W := mkw 0x1282c15c05e03b01 0x04a0b05701780ec0 0xdfffd3fc07ecff83 0xf7fff4ff01fb3fe0

def z268 : W := mkw 0x03000000075a8002 0x00c0000001d6a000 0xc1e8520007ffc001 0xf07a148001fff000

def z269 : W := mkw 0x0aa0043565e53bd1 0x42a8010d59794ef4 0xf7dcac7367f73ff3 0xfdf72b1cd9fdcffc

def z270 : W := mkw 0x2003fa8280000000 0x0800fea0a0000000 0x2ffbff8380000000 0x0bfeffe0e0000000

def z271 : W := mkw 0x1282c15c05e03b01 0x04a0b05701780ec0 0xffffd3fcffe03f82 0xfffff4ff3ff80fe0

def z272 : W := mkw 0x286134b3c299263a 0xca184d2cf0a6498e 0xeebfbdf3879b3c7f 0x7bafef7ce1e6cf1f

def z273 : W := mkw 0x0000000000000000 0x0000000000000000 0xc61c000000002002 0x3187000000000800

def z274 : W := mkw 0x0000000000000000 0x0000000000000000 0x4a28000000001002 0x528a000000000400

def z275 : W := mkw 0x0002c00000000000 0x0000b00000000000 0x007bc00000000000 0x001ef00000000000

def z276 : W := mkw 0x1c0005ebd0000000 0x0700017af4000000 0x3fe853fff8000000 0x0ffa14fffe000000

def z277 : W := mkw 0x3f03ffebd5428000 0x0fc0fffaf550a000 0x3ffbfffff9e7c000 0x8ffefffffe79f000

def z278 : W := mkw 0x1aa2c57d65e53bd1 0x46a8b15f59794ef4 0xfe7fc1ff67e03ff2 0xff9ff07fd9f80ffc

def z279 : W := mkw 0x0080000400201101 0x0020000100080440 0x1040400c00600380 0x84101003001800e0

def z280 : W := mkw 0x08200421600500d0 0x4208010858014034 0x2000000360000070 0x08000000d800001c

def z281 : W := mkw 0x0020001000812210 0x4008000400204884 0x8004000001932030 0x200100000064c80c

def z282 : W := mkw 0x8392ca042d66d1c5 0x20e4b2810b59b471 0x1140ce0c79e7c380 0x845033831e79f0e0

def z283 : W := mkw 0x80900004282451c5 0x202400010a091471 0x3b40420cf864d3ce 0x8ed010833e1934f3

def z284 : W := mkw 0x0000008280000000 0x00000020a0000000 0x2e00018380000000 0x0b800060e0000000

def z285 : W := mkw 0x80d00086a82455ed 0xa0340021aa09157b 0x3e04018ff8003ffe 0x0f810063fe000fff

def z286 : W := mkw 0x3f03ffebd75a8002 0x0fc0fffaf5d6a000 0x8413adf307930000 0x2104eb7cc1e4c000

def z287 : W := mkw 0x88b0043568a573d5 0x622c010d5a295cf5 0x3e04007ff80033fe 0x0f81001ffe000cff

def z288 : W := mkw 0x8090000408205105 0x2024000102081441 0x5a68520c9868d38e 0xd69a1483261a34e3

def z289 : W := mkw 0x0800042140000000 0x0200010850000000 0x3ff8fe7ff8000000 0x0ffe3f9ffe000000

def z290 : W := mkw 0x9292c14c0d605905 0x24a4b05303581641 0x0823538c9e68dc0c 0x4208d4e3279a3703

def z291 : W := mkw 0x0820043140812210 0x4208010c50204884 0x00008c7001830000 0x0000231c0060c000

def z292 : W := mkw 0x0000000000000000 0x0000000000000000 0x082010008008100c 0x4208040020020403

def z293 : W := mkw 0x20c130868238152b 0x88304c21a08e054a 0xfeff718f86783fff 0xffbfdc63e19e0fff

def z294 : W := mkw 0x08200431608522d0 0x4208010c582148b4 0xd1448c70619723f3 0xb451231c1865c8fc

def z295 : W := mkw 0x0282c01405e03b01 0x00a0b00501780ec0 0xc07fc00007e03f82 0xf01ff00001f80fe0

def z296 : W := mkw 0x88b0043568a573d5 0x622c010d5a295cf5 0x7be8de7cf9efd3cf 0xdefa379f3e7bf4f3

def z297 : W := mkw 0x21413a82821a842a 0x88504ea0a086a10a 0xefbf3f83861ffc7f 0x7befcfe0e187ff1f

def z298 : W := mkw 0x004000000218042a 0x801000000086010a 0x8004000006102c30 0x2001000001840b0c

def z299 : W := mkw 0x2303fa00075a8002 0x08c0fe8001d6a000 0x0163de0007efc000 0xc058f78001fbf000

def z300 : W := mkw 0x3703fbca975a8002 0x0dc0fef2a5d6a000 0xc9fbff8c9fffc001 0xf27effe327fff000

def z301 : W := mkw 0xa0d130868a38552f 0xa8344c21a28e154b 0x0823538c9e68dc0c 0x4208d4e3279a3703

def z302 : W := mkw 0x32c3f1de87f83f2b 0x8cb0fc77a1fe0fca 0xde7fe1ff07f03fb2 0xf79ff87fc1fc0fec

def z303 : W := mkw 0x03000000075a8002 0x00c0000001d6a000 0xc1d8ac0007ffc001 0xf0762b0001fff000

def z304 : W := mkw 0x2c013ea3d0000000 0x0b004fa8f4000000 0x00002c0300000000 0x00000b00c0000000

def z305 : W := mkw 0xa093fa04282451c5 0x2824fe810a091471 0x7bfbfe0cf86cd3cf 0xdefeff833e1b34f3

def z306 : W := mkw 0x204130828218042a 0x88104c20a086010a 0x2e27118386083c7e 0x4b89c460e1820f1f

def z307 : W := mkw 0x2303fa00075a8002 0x08c0fe8001d6a000 0xcfffff8007fffc03 0xf3ffffe001ffff00

def z308 : W := mkw 0x2303fa00075a8002 0x08c0fe8001d6a000 0xe7fffe0307ffe073 0xf9ffff80c1fff81c

def z309 : W := mkw 0x08200431608522d0 0x4208010c582148b4 0x1000007060000380 0x0400001c180000e0

def z310 : W := mkw 0x00000010208422c0 0x00000004082108b0 0xf7dc8070618423c3 0xbdf7201c186108f0

def z311 : W := mkw 0x204130828218042a 0x88104c20a086010a 0xce3f218306103c32 0x738fc860c1840f0c

def z312 : W := mkw 0x0000000000000000 0x0000000000000000 0x40a8100000080001 0x502a040000020000

def z313 : W := mkw 0x0302ca00075a8002 0x00c0b28001d6a000 0xc140ce0007ffc001 0xf050338001fff000

def z314 : W := mkw 0x1282c15c05e03b01 0x04a0b05701780ec0 0xc41781f007e03f82 0xf105e07c01f80fe0

def z315 : W := mkw 0x1c4005ebd0000428 0x8710017af400010a 0x3e0401fff8003c7e 0x0f81007ffe000f1f

def z316 : W := mkw 0x80100000280440c4 0x200400000a011031 0x73c81200f80cc3cf 0x9cf204803e0330f3

def z317 : W := mkw 0x0302ca0005428000 0x00c0b2800150a000 0xc1d8ee0001f7c001 0xb0763b80007df000

def z318 : W := mkw 0x00000000200400c0 0x0000000008010030 0x40000000000403c3 0x90000000000100f0

def z319 : W := mkw 0x2343fa82875a842a 0x88d0fea0a1d6a10a 0xeebfbd83879b3c7f 0x7bafef60e1e6cf1f

def z320 : W := mkw 0x1282c14c05601901 0x04a0b05301580640 0xc87bc18c07e01c00 0xf21ef06301f80700

def z321 : W := mkw 0x2c213ea3f00500d0 0x4b084fa8fc014034 0x21803e03f8170071 0x08600f80fe05c01c

def z322 : W := mkw 0x004000000218042a 0x801000000086010a 0x000000000018007d 0x000000000006001f

def z323 : W := mkw 0x1282c15c05e03b01 0x04a0b05701780ec0 0x9457c1fc07e02f80 0xa515f07f01f80be0

def z324 : W := mkw 0x9292c15c2de47bc5 0x24a4b0570b791ef1 0xdf7fc3fc7fe4ff82 0xf7dff0ff1ff93fe0

def z325 : W := mkw 0x2b23fe3167dfa2d2 0x4ac8ff8c59f7e8b4 0xd1fbfe7067ffc381 0xf47eff9c19fff0e0

def z326 : W := mkw 0x2303fa00075a8002 0x08c0fe8001d6a000 0xc1dbac0007970001 0xb076eb0001e5c000

def z327 : W := mkw 0x8090000408205105 0x2024000102081441 0x0800000c9800100c 0x0200000326000403

def z328 : W := mkw 0x0000000000000000 0x0000000000000000 0x33c8000060000000 0x0cf2000018000000

def z329 : W := mkw 0x9292c15c2de47bc5 0x24a4b0570b791ef1 0x7be8d27cf9ecd3cf 0xdefa349f3e7b34f3

def z330 : W := mkw 0x2001308280000000 0x08004c20a0000000 0x0413218300000000 0x0104c860c0000000

def z331 : W := mkw 0x2303fa00075a8002 0x08c0fe8001d6a000 0x01a37e00067fc001 0x4068df80019ff000

def z332 : W := mkw 0x80900004282451c5 0x202400010a091471 0x6aa81000806cd3cf 0xdaaa0400201b34f3

def z333 : W := mkw 0x10c001de80a03f29 0x84300077a0280fca 0x3e0401ff80003ffe 0x0f81007fe0000fff

def z334 : W := mkw 0x2001308280000000 0x08004c20a0000000 0x3ffb738ff8000000 0x0ffedce3fe000000

def z335 : W := mkw 0x08200431608522d0 0x4208010c582148b4 0xb614ac73619323f2 0x2d852b1cd864c8fc

def z336 : W := mkw 0x8090000408205105 0x2024000102081441 0x000000000068d00c 0x40000000001a3403

def z337 : W := mkw 0x0000001000802200 0x0000000400200880 0xde7f81f007803f82 0xf79fe07c01e00fe0

def z338 : W := mkw 0x1c2005fbf08522d0 0x4708017efc2148b4 0x3e0401fff80023f2 0x0f81007ffe0008fc

def z339 : W := mkw 0x2303fa00075a8002 0x08c0fe8001d6a000 0xfbfbfe0cffffc001 0xfefeff833ffff000

def z340 : W := mkw 0x2001300002180002 0x08004c0000860000 0xc1fb7200067cc001 0xf07edc80019f3000

def z341 : W := mkw 0x204130828218042a 0x88104c20a086010a 0xc4bf318306182c31 0x712fcc60c1860b0c

def z342 : W := mkw 0x1002c15800802200 0x0400b05600200880 0xde7fc1fc01802382 0xb79ff07f006008e0

def z343 : W := mkw 0x02c0001407f83f2b 0x80b0000501fe0fca 0xc004000007f83fff 0xf001000001fe0fff

def z344 : W := mkw 0x01000000021a8002 0x004000000086a000 0x00000000001fc001 0x000000000007f000

def z345 : W := mkw 0x08200421600500d0 0x4208010858014034 0x01000c0060070000 0x004003001801c000

def z346 : W := mkw 0x2303fa82875a8002 0x08c0fea0a1d6a000 0xeffbff8387ffc001 0xfbfeffe0e1fff000

def z347 : W := mkw 0x204130828218042a 0x88104c20a086010a 0xc827118086183c7f 0x7209c46021860f1f

def z348 : W := mkw 0x3c03ffebd0000000 0x0f00fffaf4000000 0x1e7bedff00000000 0x079efb7fc0000000

def z349 : W := mkw 0x88b0043568a573d5 0x622c010d5a295cf5 0xffdcac7ff99733ff 0xbff72b1ffe65ccff

def z350 : W := mkw 0x9292c14c2d6459c5 0x24a4b0530b591671 0x7beb538cfe6cdfcf 0xdefad4e33f9b37f3

def z351 : W := mkw 0x1002c14800000000 0x0400b05200000000 0x0823418c00000000 0x0208d06300000000

def z352 : W := mkw 0x0040008280000428 0x80100020a000010a 0x0800018080001c0c 0x0200006020000703

def z353 : W := mkw 0x204130828218042a 0x88104c20a086010a 0xce3f118086083c0e 0x738fc46021820f03

def z354 : W := mkw 0x80900004282451c5 0x202400010a091471 0x73c8420c7864c3c3 0x9cf210831e1930f0

def z355 : W := mkw 0xa0d13086aa3c55ef 0xa8344c21aa8f157b 0x7beb538cfe6cdfcf 0xdefad4e33f9b37f3

def z356 : W := mkw 0x80d00086a82455ed 0xa0340021aa09157b 0x7fec538ff86cffff 0xdffb14e3fe1b3fff

def z357 : W := mkw 0x0b20043167dfa2d2 0x42c8010c59f7e8b4 0xf7dcac7367ffe3f3 0xfdf72b1cd9fff8fc

def z358 : W := mkw 0xabb3fe356ffff3d7 0x6aecff8d5bfffcf5 0xfffffe7ffffff3ff 0xffffff9ffffffcff

def z359 : W := mkw 0x0000001000802200 0x0000000400200880 0x1040807001800380 0x8410201c006000e0

def z360 : W := mkw 0x1080014c00201901 0x0420005300080640 0x0800018c00001c00 0x0200006300000700

def z361 : W := mkw 0x0800042140000000 0x0200010850000000 0x3600007360000000 0x0d80001cd8000000

def z362 : W := mkw 0x3303fb5807daaa02 0x0cc0fed601f6aa80 0x8417adf007932c00 0x2105eb7c01e4cb00

def z363 : W := mkw 0x12c2c15c07f83f2b 0x84b0b05701fe0fca 0xde7fc1fc07f83fff 0xf79ff07f01fe0fff

def z364 : W := mkw 0x80900004282451c5 0x202400010a091471 0x3be8520cf864c380 0x8efa14833e1930e0

def z365 : W := mkw 0x08200431608522d0 0x4208010c582148b4 0xe1842c03619723f3 0xb8610b00d865c8fc

def z366 : W := mkw 0x1282c15c25e43bc1 0x04a0b05709790ef0 0xffffc1fc67e43fc3 0xfffff07f19f90ff0

def z367 : W := mkw 0x3243f1da87d82e2a 0x8c90fc76a1f60b8a 0x8417a1f307902c30 0x2105e87cc1e40b0c

def z368 : W := mkw 0x282134b3e08522d0 0x4a084d2cf82148b4 0xffffbdf3e19723f3 0xbfffef7cf865c8fc

def z369 : W := mkw 0x0820043140812210 0x4208010c50204884 0xc5dcac7301972031 0xb1772b1cc065c80c

def z370 : W := mkw 0x0380001407fabb03 0x00e0000501feaec0 0xc004000007ffff83 0xf001000001ffffe0

def z371 : W := mkw 0x2303fa00075a8002 0x08c0fe8001d6a000 0x0003000006000000 0x0000c00001800000

def z372 : W := mkw 0x3383fb5c07fabb03 0x0ce0fed701feaec0 0xd1fbfe7c07ffc381 0xf47eff9f01fff0e0

def z373 : W := mkw 0x1282c15c05e03b01 0x04a0b05701780ec0 0xd07bc07c07e00380 0xf41ef01f01f800e0

def z374 : W := mkw 0x2343fa82875a842a 0x88d0fea0a1d6a10a 0x082353808668dc0c 0x4208d4e0219a3703

def z375 : W := mkw 0x0000000000000000 0x0000000000000000 0x40000000006cc001 0xd0000000001b3000

def z376 : W := mkw 0x2001308280000000 0x08004c20a0000000 0x0823118080000000 0x0208c46020000000

def z377 : W := mkw 0x80900004282451c5 0x202400010a091471 0xfbf8fe0cf9ffd3cf 0xfefe3f833e7ff4f3

def z378 : W := mkw 0x204130828218042a 0x88104c20a086010a 0xe69f218306102c73 0x39a7c860c1840b1c

def z379 : W := mkw 0x3ae3f5ffe7fd3ffb 0xceb8fd7ff9ff4ffe 0xfffffdffe7ff3fff 0xffffff7ff9ffcfff

def z380 : W := mkw 0x88900425682451c5 0x222401095a091471 0x7ff8fe7ff86cd3cf 0xdffe3f9ffe1b34f3

def z381 : W := mkw 0x1c02cf6950000000 0x0700b3da54000000 0x37d8ee7f78000000 0x0df63b9fde000000

def z382 : W := mkw 0x2001300002180002 0x08004c0000860000 0xc1fbbc00079f0001 0xf07eef0001e7c000

def z383 : W := mkw 0x0800042140000000 0x0200010850000000 0xf7dcac7360102073 0x3df72b1cd804081c

def z384 : W := mkw 0x2383fa04077a9103 0x08e0fe8101dea440 0xdbfbfe0c07ffd383 0xf6feff8301fff4e0

def z385 : W := mkw 0x32c3f1ce87781d2b 0x8cb0fc73a1de074a 0x0823518c86681c0c 0x4208d463219a0703

def z386 : W := mkw 0x2001308282180002 0x08004c20a0860000 0xeebb318386180001 0x7baecc60e1860000

def z387 : W := mkw 0x0000000000000000 0x0000000000000000 0x4068400000600000 0xd01a100000180000

def z388 : W := mkw 0x8292c0042d6451c5 0x20a4b0010b591471 0xfbfbd20cffecd3cf 0xfefef4833ffb34f3

def z389 : W := mkw 0x286134a3e21d04fa 0xca184d28f887413e 0xefbf3d83e61f3c7f 0x7befcf60f987cf1f

def z390 : W := mkw 0x80900004282451c5 0x202400010a091471 0x3be8520cf80013ce 0x0efa14833e0004f3

def z391 : W := mkw 0x80100000280440c4 0x200400000a011031 0x00000000000cc04d 0x0000000000033013

def z392 : W := mkw 0x2343fa82875a842a 0x88d0fea0a1d6a10a 0xc5ffff8307ffec31 0xf17fffe0c1fffb0c

def z393 : W := mkw 0x0000000000000000 0x0000000000000000 0xeebf118086083c4f 0x7bafc46021820f13

def z394 : W := mkw 0x0000000000000000 0x0000000000000000 0x1140420c78000000 0x045010831e000000

def z395 : W := mkw 0x0b22ce3165c7a2d0 0x42c8b38c5971e8b4 0xf7dcee7361f7e3f3 0xbdf73b9cd87df8fc

def z396 : W := mkw 0x00200010208522d0 0x40080004082148b4 0xe69c2003019723f3 0xb9a70800c065c8fc

def z397 : W := mkw 0x204130828218042a 0x88104c20a086010a 0xe084300386183c7f 0x78210c00e1860f1f

def z398 : W := mkw 0x0800043140802200 0x0200010c50200880 0xf7dcac7361802382 0xbdf72b1cd86008e0

def z399 : W := mkw 0x00000000200400c0 0x0000000008010030 0xf3d8ac00619703c3 0xbcf62b001865c0f0

def z400 : W := mkw 0x0040008280000428 0x80100020a000010a 0x6eac118380083c7f 0x5bab0460e0020f1f

def z401 : W := mkw 0x1aa2c57d65e53bd1 0x46a8b15f59794ef4 0x1140cc7c61e70380 0x8450331f1879c0e0

def z402 : W := mkw 0x29213e21621f80d2 0x4a484f885887e034 0x21803e03601fc071 0x08600f80d807f01c

def z403 : W := mkw 0x3c23fffbf08522d0 0x4f08fffefc2148b4 0x3ffffffff80023f2 0x0ffffffffe0008fc

def z404 : W := mkw 0x2383fa1407fabb03 0x08e0fe8501feaec0 0xc1fffe0007ffff83 0xf07fff8001ffffe0

def z405 : W := mkw 0x204130828218042a 0x88104c20a086010a 0xefffbd83879f3c7f 0xfbffef60e1e7cf1f

def z406 : W := mkw 0x23013a00075a8002 0x08c04e8001d6a000 0xc1803e0007ffc001 0xf0600f8001fff000

def z407 : W := mkw 0x1382cb5c05e2bb01 0x04e0b2d70178aec0 0x1140ce7c01e7c380 0x8450339f0079f0e0

def z408 : W := mkw 0x80b0001428a573d5 0x602c00050a295cf5 0xfbec520cf9fff3ff 0xfefb14833e7ffcff

def z409 : W := mkw 0x88b0043568a573d5 0x622c010d5a295cf5 0x7fec527ff86cf3ff 0xdffb149ffe1b3cff

def z410 : W := mkw 0x1202c15805c02a00 0x0480b05601700a80 0xd65f81f007802f82 0xb597e07c01e00be0

def z411 : W := mkw 0x3c03ffebd2180002 0x0f00fffaf4860000 0xfffbfffffe180001 0x7ffeffffff860000

def z412 : W := mkw 0xbc93ffeff82451c5 0x2f24fffbfe091471 0x3ffbfffff864c380 0x8ffefffffe1930e0

def z413 : W := mkw 0x0080000400201101 0x0020000100080440 0x7ae8500c806813cf 0xdeba1403201a04f3

def z414 : W := mkw 0x0000000000000000 0x0000000000000000 0x400000000008104f 0x5000000000020413

def z415 : W := mkw 0x204130828218042a 0x88104c20a086010a 0x6aab118086081c4f 0x5aaac46021820713

def z416 : W := mkw 0x204130828218042a 0x88104c20a086010a 0x6aa830038018107f 0x5aaa0c00e006041f

def z417 : W := mkw 0x01000a0000028000 0x004002800000a000 0x01000e000007c000 0x004003800001f000

def z418 : W := mkw 0x80b0001428a573d5 0x602c00050a295cf5 0xc004000001fff3ff 0xf0010000007ffcff

def z419 : W := mkw 0x0302c000075a8002 0x00c0b00001d6a000 0xc07bc00007ffc001 0xf01ef00001fff000

def z420 : W := mkw 0x0080000400201101 0x0020000100080440 0xde7f418c06603f82 0xf79fd06301980fe0

def z421 : W := mkw 0x00000000200400c0 0x0000000008010030 0x1140000060040380 0x84500000180100e0

def z422 : W := mkw 0x204130828218042a 0x88104c20a086010a 0xe69c30038018207f 0x39a70c00e006081f

def z423 : W := mkw 0x0000000000000000 0x0000000000000000 0x3a00000cf8000000 0x0e8000033e000000

def z424 : W := mkw 0x0040008280000428 0x80100020a000010a 0x200000038000007c 0x08000000e000001f

def z425 : W := mkw 0x2001308280000000 0x08004c20a0000000 0x2080300380000000 0x08200c00e0000000

def z426 : W := mkw 0x204130828218042a 0x88104c20a086010a 0x8c37318386183c3c 0x630dcc60e1860f0f

def z427 : W := mkw 0x1202c15805c02a00 0x0480b05601700a80 0x9e7fc1fc07802c00 0x279ff07f01e00b00

def z428 : W := mkw 0x2c013ea3d0000000 0x0b004fa8f4000000 0x2fbb3f83f8000000 0x0beecfe0fe000000

def z429 : W := mkw 0x1c2005fbf08522d0 0x4708017efc2148b4 0xffdcadfff99723f3 0xbff72b7ffe65c8fc

def z430 : W := mkw 0x004000000218042a 0x801000000086010a 0xeaac100086183c7f 0x7aab040021860f1f

def z431 : W := mkw 0x1202c14805400800 0x0480b05201500200 0x0003018006000c00 0x0000c06001800300

def z432 : W := mkw 0x3403fbca90000000 0x0d00fef2a4000000 0x1e7bd3fc98000000 0x079ef4ff26000000

def z433 : W := mkw 0xa393fa042f7ed1c7 0x28e4fe810bdfb471 0xc1fbfe0007ffd3cf 0xf07eff8001fff4f3

def z434 : W := mkw 0x08200431608522d0 0x4208010c582148b4 0x37448c73618723f2 0x8dd1231cd861c8fc

def z435 : W := mkw 0x08600431629d26fa 0xc218010c58a749be 0xf7dcac73679f3fff 0xfdf72b1cd9e7cfff

def z436 : W := mkw 0x1080015c00a03b01 0x0420005700280ec0 0xde5c81fc01803f82 0xb797207f00600fe0

def z437 : W := mkw 0x3283fb5c05e03b01 0x0ca0fed701780ec0 0xdffffffc07e03f82 0xf7ffffff01f80fe0

def z438 : W := mkw 0x00200010208522d0 0x40080004082148b4 0xd65c8070019723f3 0xb597201c0065c8fc

def z439 : W := mkw 0x0202c00005400000 0x0080b00001500000 0x0023400006600000 0x4008d00001980000

def z440 : W := mkw 0x80100000280440c4 0x200400000a011031 0x6ba81200f80cd04f 0x5aea04803e033413

def z441 : W := mkw 0x1282c15c05e03b01 0x04a0b05701780ec0 0x5a68c07c01e01382 0xd69a301f007804e0

def z442 : W := mkw 0x280134a3c0000000 0x0a004d28f0000000 0x3ffbbdf3e0000000 0x0ffeef7cf8000000

def z443 : W := mkw 0x2303fa00075a8002 0x08c0fe8001d6a000 0xebfbfe0087ffd04f 0xfafeff8021fff413

def z444 : W := mkw 0x08200431608522d0 0x4208010c582148b4 0x37dcac73600023f2 0x0df72b1cd80008fc

def z445 : W := mkw 0x08200421600500d0 0x4208010858014034 0xe1d8ac0361970071 0xb8762b00d865c01c

def z446 : W := mkw 0x0202c00005400000 0x0080b00001500000 0xce7fc18007e03c02 0xf39ff06001f80f00

def z447 : W := mkw 0x08200431608522d0 0x4208010c582148b4 0xfffcbc73e19f33ff 0xffff2f1cf867ccff

def z448 : W := mkw 0x1282c15c05e03b01 0x04a0b05701780ec0 0x1863c1fc07e01f80 0xc618f07f01f807e0

def z449 : W := mkw 0x80900004282451c5 0x202400010a091471 0x7a00000cf86cd3cf 0xde8000033e1b34f3

def z450 : W := mkw 0x2003fa0002180002 0x0800fe8000860000 0xc1fbfe0006180001 0x707eff8001860000

def z451 : W := mkw 0x1802c56940000000 0x0600b15a50000000 0x3ffbedff60000000 0x0ffefb7fd8000000

def z452 : W := mkw 0x3c43ffebd218042a 0x8f10fffaf486010a 0x3ffbfffffe081c0c 0x4ffeffffff820703

def z453 : W := mkw 0x0302ca0005428000 0x00c0b2800150a000 0x000042000060c000 0x0000108000183000

def z454 : W := mkw 0x3f03ffebd75a8002 0x0fc0fffaf5d6a000 0x3ffbfffffe68c000 0x4ffeffffff9a3000

def z455 : W := mkw 0x284134a3c218042a 0x8a104d28f086010a 0xffffbdf3e6183c7f 0x7fffef7cf9860f1f

def z456 : W := mkw 0x30c131de82b83f2b 0x8c304c77a0ae0fca 0xfebf31ff86183fff 0x7fafcc7fe1860fff

def z457 : W := mkw 0x1a82c57d45e03b01 0x06a0b15f51780ec0 0xffffedff67e03f82 0xfffffb7fd9f80fe0

def z458 : W := mkw 0x2323fa1027dfa2d2 0x48c8fe8409f7e8b4 0xc1fffe0007ffe3f3 0xf07fff8001fff8fc

def z459 : W := mkw 0x0000000000000000 0x0000000000000000 0x014042000064c000 0x8050108000193000

def z460 : W := mkw 0x1c02cf6950000000 0x0700b3da54000000 0x3be8de7cf8000000 0x0efa379f3e000000

def z461 : W := mkw 0x08200431608522d0 0x4208010c582148b4 0x77cc0073600423f3 0x9df3001cd80108fc

def z462 : W := mkw 0x0000000000000000 0x0000000000000000 0xc004000006003c02 0x7001000001800f00

def z463 : W := mkw 0x2c213eb3f08522d0 0x4b084facfc2148b4 0xf7dcbe73f99723f3 0xbdf72f9cfe65c8fc

def z464 : W := mkw 0x08200421600500d0 0x4208010858014034 0x73c82c03601703f3 0x9cf20b00d805c0fc

def z465 : W := mkw 0x03000000075a8002 0x00c0000001d6a000 0x000000000668c000 0x40000000019a3000

def z466 : W := mkw 0x004000000218042a 0x801000000086010a 0xce3f018006183c7f 0x738fc06001860f1f

def z467 : W := mkw 0x2f03fea3d75a8002 0x0bc0ffa8f5d6a000 0xe1fbfe03ffffc001 0xf87eff80fffff000

def z468 : W := mkw 0x204130828218042a 0x88104c20a086010a 0xefff7383867cfc7f 0xfbffdce0e19f3f1f

def z469 : W := mkw 0x80900004282451c5 0x202400010a091471 0x31c0520cf86cc3cd 0x8c7014833e1b30f3

def z470 : W := mkw 0x204130928298262a 0x88104c24a0a6098a 0xfeffb1f387983fff 0xffbfec7ce1e60fff

def z471 : W := mkw 0x24013a8290000000 0x09004ea0a4000000 0x0000120098000000 0x0000048026000000

def z472 : W := mkw 0x0000000000000000 0x0000000000000000 0x2080200300100071 0x08200800c004001c

def z473 : W := mkw 0x3c43ffebd218042a 0x8f10fffaf486010a 0x8417adf306102c30 0x2105eb7cc1840b0c

def z474 : W := mkw 0x2343fa82875a842a 0x88d0fea0a1d6a10a 0x8417ad8307932c30 0x2105eb60c1e4cb0c

def z475 : W := mkw 0x3283f1de85e03b01 0x0ca0fc77a1780ec0 0xfefff1ff87e03f82 0xffbffc7fe1f80fe0

def z476 : W := mkw 0x80100000280440c4 0x200400000a011031 0x20000000f800004c 0x080000003e000013

def z477 : W := mkw 0x00600010229d26fa 0xc018000408a749be 0xc0040000079f3fff 0xf001000001e7cfff

def z478 : W := mkw 0x00000000200400c0 0x0000000008010030 0x7be8520cf80403c3 0x9efa14833e0100f0

def z479 : W := mkw 0x3c43ffebd218042a 0x8f10fffaf486010a 0x3ffbfffff818007d 0x0ffefffffe06001f

def z480 : W := mkw 0xb493fbce98205105 0x2d24fef3a6081441 0x0823538c9868d00c 0x4208d4e3261a3403

def z481 : W := mkw 0x2003fa0000000000 0x0800fe8000000000 0x41fbfe00006cc001 0xd07eff80001b3000

def z482 : W := mkw 0x0000000000000000 0x0000000000000000 0x21801200f8000000 0x086004803e000000

def z483 : W := mkw 0x08200431608522d0 0x4208010c582148b4 0xa594ac7361972071 0x29652b1cd865c81c

def z484 : W := mkw 0x1e82cf7d55e03b01 0x07a0b3df55780ec0 0x1140ce7c79e00380 0x8450339f1e7800e0

def z485 : W := mkw 0x0080000400201101 0x0020000100080440 0x4000000000601382 0xd0000000001804e0

def z486 : W := mkw 0x08200431608522d0 0x4208010c582148b4 0xd1d8ac7061970381 0xb4762b1c1865c0e0

def z487 : W := mkw 0x3c03ffebd0000000 0x0f00fffaf4000000 0x3e13adfff8000000 0x0f84eb7ffe000000

def z488 : W := mkw 0x1080015c00a03b01 0x0420005700280ec0 0xde3f01fc06003f82 0x778fc07f01800fe0

def z489 : W := mkw 0x0000001000802200 0x0000000400200880 0xc004000001802382 0xb0010000006008e0

def z490 : W := mkw 0x204130828218042a 0x88104c20a086010a 0x2ebb318386081c0c 0x4baecc60e1820703

def z491 : W := mkw 0x1aa2c57d65e53bd1 0x46a8b15f59794ef4 0xdf7fcdfc67e73f82 0xf7dff37f19f9cfe0

def z492 : W := mkw 0x80900004282451c5 0x202400010a091471 0x41e85200006cd3cf 0xd07a1480001b34f3

def z493 : W := mkw 0x1c22cf79708522d0 0x4708b3de5c2148b4 0x1140ce7c79870380 0x8450339f1e61c0e0

def z494 : W := mkw 0xbc13ffebf80440c4 0x2f04fffafe011031 0x3ffbfffff80cc04d 0x0ffefffffe033013

def z495 : W := mkw 0x0000000000000000 0x0000000000000000 0x01d8ac0000000000 0x00762b0000000000

def z496 : W := mkw 0x80900004282451c5 0x202400010a091471 0x5b68420c7864d382 0xd6da10831e1934e0

def z497 : W := mkw 0x204130828218042a 0x88104c20a086010a 0xaebf318386102c30 0x2bafcc60e1840b0c

def z498 : W := mkw 0x2001300002180002 0x08004c0000860000 0xe6bf300306182073 0x79afcc00c186081c

def z499 : W := mkw 0x2001300002180002 0x08004c0000860000 0x8013200006100000 0x2004c80001840000

def z500 : W := mkw 0x286134b3e29d26fa 0xca184d2cf8a749be 0xfebf31f3e6183fff 0x7fafcc7cf9860fff

def z501 : W := mkw 0x1280015c05e03b01 0x04a0005701780ec0 0xde0401fc07e03f82 0xf781007f01f80fe0

def z502 : W := mkw 0x2303fa00075a8002 0x08c0fe8001d6a000 0xc023520007ffc001 0xf008d48001fff000

def z503 : W := mkw 0x1082c14c00201101 0x0420b05300080440 0x5e7bc1fc00601382 0xd79ef07f001804e0

def z504 : W := mkw 0x08200431608522d0 0x4208010c582148b4 0x37842c73601723f3 0x0de10b1cd805c8fc

def z505 : W := mkw 0x3c23fffbd0812210 0x4f08fffef4204884 0x8417adf301932030 0x2105eb7cc064c80c

def z506 : W := mkw 0x9c92cf6d782451c5 0x2724b3db5e091471 0x1140ce7c7864c380 0x8450339f1e1930e0

def z507 : W := mkw 0x2303fa00075a8002 0x08c0fe8001d6a000 0x8033fe0007fbc000 0x600cff8001fef000

def z508 : W := mkw 0x3d03ffebd21a8002 0x0f40fffaf486a000 0x3ffbfffff81fc001 0x0ffefffffe07f000

def z509 : W := mkw 0x3c83ffefd0201101 0x0f20fffbf4080440 0x7ffbfffff8601382 0xdffefffffe1804e0

def z510 : W := mkw 0x0000000000000000 0x0000000000000000 0x41c8000000040001 0x9072000000010000

def z511 : W := mkw 0x2b23fe3147dba212 0x4ac8ff8c51f6e884 0xc5fffe7307ffe031 0xf17fff9cc1fff80c

def z512 : W := mkw 0x1282c15c05e03b01 0x04a0b05701780ec0 0xfeffd1fc87e83fcf 0xffbff47f21fa0ff3

def z513 : W := mkw 0x80900004282451c5 0x202400010a091471 0x29a0520cf86cd04d 0x4a6814833e1b3413

def z514 : W := mkw 0x2001308280000000 0x08004c20a0000000 0xeebf318386003c02 0x7bafcc60e1800f00

def z515 : W := mkw 0x21013a00021a8002 0x08404e800086a000 0x41e87e00007fc001 0xd07a1f80001ff000

def z516 : W := mkw 0x0000000000000000 0x0000000000000000 0x8414200300102030 0x21050800c004080c

def z517 : W := mkw 0x32c3f1ce87781d2b 0x8cb0fc73a1de074a 0xeebf718f86783c7f 0x7bafdc63e19e0f1f

def z518 : W := mkw 0x3e03fffbd5c02a00 0x0f80fffef5700a80 0x8417adf307802c00 0x2105eb7cc1e00b00

def z519 : W := mkw 0x0000000000000000 0x0000000000000000 0x7be8520cf808104f 0x5efa14833e020413

def z520 : W := mkw 0x0080000400201101 0x0020000100080440 0x0820400c00601000 0x4208100300180400

def z521 : W := mkw 0x3c03ffebd0000000 0x0f00fffaf4000000 0x29a37f8ff8000000 0x0a68dfe3fe000000

def z522 : W := mkw 0x1282c15c05e03b01 0x04a0b05701780ec0 0x8c37c1fc07e03c00 0x630df07f01f80f00

def z523 : W := mkw 0x2001308280000000 0x08004c20a0000000 0x6ebb31838008104f 0x5baecc60e0020413

def z524 : W := mkw 0x80900004282451c5 0x202400010a091471 0x1960520cf86cd38c 0xc65814833e1b34e3

def z525 : W := mkw 0x2c413ea3d218042a 0x8b104fa8f486010a 0xefbf3f83fe183c7f 0x7befcfe0ff860f1f

def z526 : W := mkw 0x0000000000000000 0x0000000000000000 0xc004000000102073 0x300100000004081c

def z527 : W := mkw 0x0800042140000000 0x0200010850000000 0x0410ac7300000000 0x01042b1cc0000000

def z528 : W := mkw 0x286134b3e29d26fa 0xca184d2cf8a749be 0xf7dfadf367972ff3 0xbdf7eb7cd9e5cbfc

def z529 : W := mkw 0x1c02cf6950000000 0x0700b3da54000000 0x00008c7000000000 0x0000231c00000000

def z530 : W := mkw 0x32c3f1de87f83f2b 0x8cb0fc77a1fe0fca 0xde7fd1fc87e83f8e 0xf79ff47f21fa0fe3

def z531 : W := mkw 0xa0513082aa1c44ee 0xa8144c20aa87113b 0xefbf3383fe1cfc7f 0x7befcce0ff873f1f

def z532 : W := mkw 0x0280001405e03b01 0x00a0000501780ec0 0x0000000001e00380 0x80000000007800e0

def z533 : W := mkw 0x1282c15c05e03b01 0x04a0b05701780ec0 0xd65cc07c01e02382 0xb597301f007808e0

def z534 : W := mkw 0x80900004282451c5 0x202400010a091471 0x3a20520cf868d3ce 0x4e8814833e1a34f3

def z535 : W := mkw 0x00200010208522d0 0x40080004082148b4 0x00040000000023f2 0x00010000000008fc

def z536 : W := mkw 0x0002ca0000000000 0x0000b28000000000 0x0140ce0000000000 0x0050338000000000

def z537 : W := mkw 0xbcd3ffeffa3c55ef 0xaf34fffbfe8f157b 0xfffffffffe7cffff 0xffffffffff9f3fff

def z538 : W := mkw 0x1282c14c05601901 0x04a0b05301580640 0x0000400c00600000 0x0000100300180000

def z539 : W := mkw 0x12a2c15c25e53bd1 0x44a8b05709794ef4 0xde7fc1fc07f73ff3 0xf79ff07f01fdcffc

def z540 : W := mkw 0xb493fbceb82451c5 0x2d24fef3ae091471 0x7beb538cf86cd3cf 0xdefad4e33e1b34f3

def z541 : W := mkw 0xa0d130868a38552f 0xa8344c21a28e154b 0xeebf738f9e78fc7f 0x7bafdce3e79e3f1f

def z542 : W := mkw 0x29213e31629fa2d2 0x4a484f8c58a7e8b4 0xf7dcbe73619fe3f3 0xbdf72f9cd867f8fc

def z543 : W := mkw 0x20413082a21c04ea 0x88104c20a887013a 0xffff3183e61c3fff 0xffffcc60f9870fff

def z544 : W := mkw 0x0000000000000000 0x0000000000000000 0x01802c0000170001 0x00600b000005c000

def z545 : W := mkw 0xa393fa042f7ed1c7 0x28e4fe810bdfb471 0xd1fbfe0c7fffc381 0xf47eff831ffff0e0

def z546 : W := mkw 0xa0d13086aa3c55ef 0xa8344c21aa8f157b 0xfebf318ffe183fff 0x7fafcc63ff860fff

def z547 : W := mkw 0x086004b3e08526f8 0xc218012cf82149be 0x3e0401f3e0003ffe 0x0f81007cf8000fff

def z548 : W := mkw 0x9292c15c2de47bc5 0x24a4b0570b791ef1 0xde7fc1fc07ecffcf 0xf79ff07f01fb3ff3

def z549 : W := mkw 0x18a0057d60a53bd1 0x4628015f58294ef4 0x3e0401ff60003ff2 0x0f81007fd8000ffc

def z550 : W := mkw 0x00000000200400c0 0x0000000008010030 0x7be81000e00c13cf 0xdefa0400380304f3

def z551 : W := mkw 0x08200431608522d0 0x4208010c582148b4 0x73c88c70618703c3 0x9cf2231c1861c0f0

def z552 : W := mkw 0xbe93fffffde47bc5 0x2fa4ffffff791ef1 0xffffffffffecffcf 0xfffffffffffb3ff3

def z553 : W := mkw 0x3c03ffebf00400c0 0x0f00fffafc010030 0x7ffbfffff80403c3 0x9ffefffffe0100f0

def z554 : W := mkw 0x80900004282451c5 0x202400010a091471 0x7aa8100cf80813cf 0x5eaa04033e0204f3

def z555 : W := mkw 0x2c013ea3d0000000 0x0b004fa8f4000000 0x3be87e0ff8000000 0x0efa1f83fe000000

def z556 : W := mkw 0x204130828218042a 0x88104c20a086010a 0x28a3318386181c7d 0x4a28cc60e186071f

def z557 : W := mkw 0x8392ca042d66d1c5 0x20e4b2810b59b471 0x7be8de0cf9efd3cf 0xdefa37833e7bf4f3

def z558 : W := mkw 0x0280000405601901 0x00a0000101580640 0x0000000006601c00 0x4000000001980700

def z559 : W := mkw 0x1282c15c05e03b01 0x04a0b05701780ec0 0xd044c07c07e03f82 0xf411301f01f80fe0

def z560 : W := mkw 0x3403fbca90000000 0x0d00fef2a4000000 0x0003018000000000 0x0000c06000000000

def z561 : W := mkw 0x0200001005c02a00 0x0080000401700a80 0x8004000007802c00 0x2001000001e00b00

def z562 : W := mkw 0x88b0043568a573d5 0x622c010d5a295cf5 0x1140ce7c79e7c380 0x8450339f1e79f0e0

def z563 : W := mkw 0x0000000000000000 0x0000000000000000 0xc03b000006000000 0x700ec00001800000

def z564 : W := mkw 0x1822c579608522d0 0x4608b15e582148b4 0xffffedff619723f3 0xbffffb7fd865c8fc

def z565 : W := mkw 0x3c63fffbf29d26fa 0xcf18fffefca749be 0xffffffffff9f3fff 0xffffffffffe7cfff

def z566 : W := mkw 0x204130828218042a 0x88104c20a086010a 0xa497318386182c7d 0x2925cc60e1860b1f

def z567 : W := mkw 0xa09130042a3c51c7 0x28244c010a8f1471 0xfbfb720cfe7cd3cf 0xfefedc833f9f34f3

def z568 : W := mkw 0x2303fa00075a8002 0x08c0fe8001d6a000 0x8193be00079fc001 0x2064ef8001e7f000

def z569 : W := mkw 0x286134b3c299263a 0xca184d2cf0a6498e 0x8417adf307932c30 0x2105eb7cc1e4cb0c

def z570 : W := mkw 0x3c83ffffd0a03b01 0x0f20fffff4280ec0 0x3ffffffff8003f82 0x0ffffffffe000fe0

def z571 : W := mkw 0x8010000008004004 0x2004000002001001 0x000012009808c00c 0x0000048026023003

def z572 : W := mkw 0x1282c14c05601901 0x04a0b05301580640 0x1e7bc1fc06601c00 0x479ef07f01980700

def z573 : W := mkw 0x00200010208522d0 0x40080004082148b4 0x0000000001870380 0x800000000061c0e0

def z574 : W := mkw 0x3c03ffebd0000000 0x0f00fffaf4000000 0x2593bff3f8000000 0x0964effcfe000000

def z575 : W := mkw 0x8090000408205105 0x2024000102081441 0x3be8520cf868d00c 0x4efa14833e1a3403

def z576 : W := mkw 0x204130828218042a 0x88104c20a086010a 0x2ebb31838018007d 0x0baecc60e006001f

def z577 : W := mkw 0x140001ca90000000 0x05000072a4000000 0x0800018c98000000 0x0200006326000000

def z578 : W := mkw 0x3c03ffebd0000000 0x0f00fffaf4000000 0x31c0fe7ff8000000 0x0c703f9ffe000000

def z579 : W := mkw 0x0c000e2150000000 0x0300038854000000 0x01000e0078000000 0x004003801e000000

def z580 : W := mkw 0x9ab2c57d6de57bd5 0x66acb15f5b795ef5 0xffffffffffffffff 0xffffffffffffffff

def z581 : W := mkw 0x33c3fbde87fabf2b 0x8cf0fef7a1feafca 0xffffffff87ffffff 0xffffffffe1ffffff

def z582 : W := mkw 0x80900004282451c5 0x202400010a091471 0x5140420c786cd3cf 0xd45010831e1b34f3

def z583 : W := mkw 0x0800042140000000 0x0200010850000000 0x11408c7060000000 0x0450231c18000000

def z584 : W := mkw 0x0000000000000000 0x0000000000000000 0x0e04018000003c02 0x0381006000000f00

def z585 : W := mkw 0x2823fe31608522d0 0x4a08ff8c582148b4 0xf7fffe73619723f3 0xbdffff9cd865c8fc

def z586 : W := mkw 0xa8f134b7eabd77ff 0xea3c4d2dfaaf5dff 0xffffffffffffffff 0xffffffffffffffff

def z587 : W := mkw 0x1080015c00a03b01 0x0420005700280ec0 0x5e6c41fc00603f82 0xd79b107f00180fe0

def z588 : W := mkw 0x2303fa00075a8002 0x08c0fe8001d6a000 0x41eb5200066cc001 0xd07ad480019b3000

def z589 : W := mkw 0x08200431608522d0 0x4208010c582148b4 0xf65c8073618023f2 0xbd97201cd86008fc

def z590 : W := mkw 0x1282c15c05e03b01 0x04a0b05701780ec0 0x1e7bc1fc01e00380 0x879ef07f007800e0

def z591 : W := mkw 0x2103fa00021a8002 0x0840fe800086a000 0x01fbfe00001fc001 0x007eff800007f000

def z592 : W := mkw 0x2b23fe3167dfa2d2 0x4ac8ff8c59f7e8b4 0xf7dfac73679723f3 0xbdf7eb1cd9e5c8fc

def z593 : W := mkw 0x3c23ffebf00500d0 0x4f08fffafc014034 0x3ffbfffff8170071 0x0ffefffffe05c01c

def z594 : W := mkw 0x2001308280000000 0x08004c20a0000000 0xeebf318380102073 0x3bafcc60e004081c

def z595 : W := mkw 0x204130828218042a 0x88104c20a086010a 0xc8bb318086181c0d 0x722ecc6021860703

def z596 : W := mkw 0x3383fb4c077a9903 0x0ce0fed301dea640 0xc9fbff8c07ffdc01 0xf27effe301fff700

def z597 : W := mkw 0x1c8005ffd0a03b01 0x0720017ff4280ec0 0x3e0401fff8003f82 0x0f81007ffe000fe0

def z598 : W := mkw 0x0000000000000000 0x0000000000000000 0xeebf218306103c73 0x7bafc860c1840f1c

def z599 : W := mkw 0x8090000408205105 0x2024000102081441 0x0000420c1860c000 0x0000108306183000

def z600 : W := mkw 0x3003fb4800000000 0x0c00fed200000000 0x1ffbfffc00000000 0x07feffff00000000

def z601 : W := mkw 0x9c9005eff82451c5 0x2724017bfe091471 0x3e0001fff80013ce 0x0f80007ffe0004f3

def z602 : W := mkw 0x00000000200400c0 0x0000000008010030 0x2180000060040041 0x0860000018010010

def z603 : W := mkw 0x004000000218042a 0x801000000086010a 0xe69c200306183c7f 0x79a70800c1860f1f

def z604 : W := mkw 0x3f03ffebd75a8002 0x0fc0fffaf5d6a000 0xc5fbfff307ffc001 0xf17efffcc1fff000

def z605 : W := mkw 0x3c23fffbf08522d0 0x4f08fffefc2148b4 0x3ffbfffff9870380 0x8ffefffffe61c0e0

def z606 : W := mkw 0x1382c15c07fabb03 0x04e0b05701feaec0 0xde7fc1fc07ffff83 0xf79ff07f01ffffe0

def z607 : W := mkw 0x2c013ea3d0000000 0x0b004fa8f4000000 0x37d8be73f8000000 0x0df62f9cfe000000

def z608 : W := mkw 0x0202c00005400000 0x0080b00001500000 0x8013800007800000 0x2004e00001e00000

def z609 : W := mkw 0x0000000000000000 0x0000000000000000 0x002052000068c000 0x40081480001a3000

def z610 : W := mkw 0x00200010208522d0 0x40080004082148b4 0xf3cc0000619723f3 0xbcf300001865c8fc

def z611 : W := mkw 0x08200431608522d0 0x4208010c582148b4 0x37d8ac7361870380 0x8df62b1cd861c0e0

def z612 : W := mkw 0x3443fbca9218042a 0x8d10fef2a486010a 0x0823538c9e081c0c 0x4208d4e327820703

def z613 : W := mkw 0x2003fa0000000000 0x0800fe8000000000 0x0013ac0000000000 0x0004eb0000000000

def z614 : W := mkw 0x1aa2c57d45e13b11 0x46a8b15f51784ec4 0xde7fedff07f33fb2 0xf79ffb7fc1fccfec

def z615 : W := mkw 0xa393fa040f7ad107 0x28e4fe8103deb441 0xc9fbfe0c9fffd00d 0xf27eff8327fff403

def z616 : W := mkw 0x1aa2c57d65e53bd1 0x46a8b15f59794ef4 0xf7dcec7f61f723f3 0xbdf73b1fd87dc8fc

def z617 : W := mkw 0x2003fa0000000000 0x0800fe8000000000 0x0023520000000000 0x0008d48000000000

def z618 : W := mkw 0x80100000280440c4 0x200400000a011031 0x3be8520cf80cc04d 0x0efa14833e033013

def z619 : W := mkw 0x2003fa0000000000 0x0800fe8000000000 0x3bfbfe0cf8000000 0x0efeff833e000000

def z620 : W := mkw 0x3c03ffebd0000000 0x0f00fffaf4000000 0x37dbadf360000000 0x0df6eb7cd8000000

def z621 : W := mkw 0x2b63feb3e7dfa6fa 0xcad8ffacf9f7e9be 0xfffffff3e7ffffff 0xfffffffcf9ffffff

def z622 : W := mkw 0x12c2c1de85e03f29 0x84b0b077a1780fca 0xfe7fc1ff87e03ffe 0xff9ff07fe1f80fff

def z623 : W := mkw 0x0080000400201101 0x0020000100080440 0x7be8520cf8601382 0xdefa14833e1804e0

def z624 : W := mkw 0x9c9005eff82451c5 0x2724017bfe091471 0x7fe853fff86cd3cf 0xdffa14fffe1b34f3

def z625 : W := mkw 0x0000000000000000 0x0000000000000000 0xeebc30038018307f 0x7baf0c00e0060c1f

def z626 : W := mkw 0x1a22c57965c52ad0 0x4688b15e59714ab4 0xf7dfadf367972ff3 0xbdf7eb7cd9e5cbfc

def z627 : W := mkw 0xb393fb5c2ffefbc7 0x2ce4fed70bffbef1 0xfffffffcffffffcf 0xffffffff3ffffff3

def z628 : W := mkw 0x0000000000000000 0x0000000000000000 0xc058800001800000 0xb016200000600000

def z629 : W := mkw 0x2b23fe21675f80d2 0x4ac8ff8859d7e034 0xe1fbfe0367ffc071 0xf87eff80d9fff01c

def z630 : W := mkw 0x3e83ffefd5601901 0x0fa0fffbf5580640 0x3ffbfffffe601c00 0x4ffeffffff980700

def z631 : W := mkw 0xac913ea7f82451c5 0x2b244fa9fe091471 0x7be87e0ff86cd3cf 0xdefa1f83fe1b34f3

def z632 : W := mkw 0x20013a0000000000 0x08004e8000000000 0x01803e0000000000 0x00600f8000000000

def z633 : W := mkw 0x80900004282451c5 0x202400010a091471 0x3b80120cf80cd3cf 0x0ee004833e0334f3

def z634 : W := mkw 0x28213431629d22d2 0x4a084d0c58a748b4 0xf7ffbc73679f23f3 0xfdffef1cd9e7c8fc

def z635 : W := mkw 0x08200431608522d0 0x4208010c582148b4 0xf6040073619723f3 0xbd81001cd865c8fc

def z636 : W := mkw 0x1282c15c05e03b01 0x04a0b05701780ec0 0xc827418c07e03f82 0xf209d06301f80fe0

def z637 : W := mkw 0x9292c15c2de47bc5 0x24a4b0570b791ef1 0xfe7fc1fcffe03fce 0xff9ff07f3ff80ff3

def z638 : W := mkw 0x0000000000000000 0x0000000000000000 0x01801200000cc001 0x0060048000033000

def z639 : W := mkw 0x2001300000000000 0x08004c0000000000 0x00bb300000000000 0x002ecc0000000000

def z640 : W := mkw 0x08200421600500d0 0x4208010858014034 0x37d8ac7360170071 0x0df62b1cd805c01c

def z641 : W := mkw 0x08200431608522d0 0x4208010c582148b4 0xf69c2073601023f3 0x3da7081cd80408fc

def z642 : W := mkw 0x0000000000000000 0x0000000000000000 0x2aa8100080000000 0x0aaa040020000000

def z643 : W := mkw 0x0000000000000000 0x0000000000000000 0x2604000300002072 0x09810000c000081c

def z644 : W := mkw 0x0000000000000000 0x0000000000000000 0x5248000000000382 0x94920000000000e0

def z645 : W := mkw 0x3683fbce95601901 0x0da0fef3a5580640 0x0823538c9e601c00 0x4208d4e327980700

def z646 : W := mkw 0x18a0057d60a53bd1 0x4628015f58294ef4 0xffdcadff61973ff3 0xbff72b7fd865cffc

def z647 : W := mkw 0xa0d13086aa3c55ef 0xa8344c21aa8f157b 0xeebf3183867cffff 0xfbafcc60e19f3fff

def z648 : W := mkw 0x1c22cf79708522d0 0x4708b3de5c2148b4 0xf7dcee7f799723f3 0xbdf73b9fde65c8fc

def z649 : W := mkw 0x0000000000000000 0x0000000000000000 0x01e8520000000000 0x007a148000000000

def z650 : W := mkw 0x2803fe2140000000 0x0a00ff8850000000 0x37fbfe7360000000 0x0dfeff9cd8000000

def z651 : W := mkw 0x0320001027dfa2d2 0x40c8000409f7e8b4 0xc004000007ffe3f3 0xf001000001fff8fc

def z652 : W := mkw 0x08200431608522d0 0x4208010c582148b4 0xd75c8c7061872382 0xb5d7231c1861c8e0

def z653 : W := mkw 0x80900004282451c5 0x202400010a091471 0x51e8520c786cc381 0xd47a14831e1b30e0

def z654 : W := mkw 0x23013000075a8002 0x08c04c0001d6a000 0xc0bb300007ffc001 0xf02ecc0001fff000

def z655 : W := mkw 0x1282c14c05601901 0x04a0b05301580640 0xce3f418c06603c02 0x738fd06301980f00

def z656 : W := mkw 0x0000000002180002 0x0000000000860000 0xc000000006180001 0x7000000001860000

def z657 : W := mkw 0x0000001000802200 0x0000000400200880 0x8414807001802000 0x2105201c00600800

def z658 : W := mkw 0x2303fa00075a8002 0x08c0fe8001d6a000 0xc0bbbc00079b0001 0x702eef0001e6c000

def z659 : W := mkw 0x0000000000000000 0x0000000000000000 0x8010ac0001930000 0x20042b000064c000

def z660 : W := mkw 0x2203fa0005400000 0x0880fe8001500000 0xc1fbfe0007e00000 0xf07eff8001f80000

def z661 : W := mkw 0x3c03fffbd0802200 0x0f00fffef4200880 0xfffffffff9802382 0xbffffffffe6008e0

def z662 : W := mkw 0x0b22ce3165c7a2d0 0x42c8b38c5971e8b4 0x1140ce7061e7c380 0x8450339c1879f0e0

def z663 : W := mkw 0x9292c15c2de47bc5 0x24a4b0570b791ef1 0x1140c27c79e4c380 0x8450309f1e7930e0

def z664 : W := mkw 0x2303fa00075a8002 0x08c0fe8001d6a000 0x81fbfe0007930000 0x207eff8001e4c000

def z665 : W := mkw 0xa393fa040f7ad107 0x28e4fe8103deb441 0x0823520c9e68d00c 0x4208d483279a3403

def z666 : W := mkw 0x2303fa00075a8002 0x08c0fe8001d6a000 0x01fbfe000668c000 0x407eff80019a3000

def z667 : W := mkw 0x9090015c28a47bc5 0x242400570a291ef1 0x7fec53fcf86cffcf 0xdffb14ff3e1b3ff3

def z668 : W := mkw 0x3283f15c07f83b03 0x0ca0fc5701fe0ec0 0xdefff1fc07f83f83 0xf7bffc7f01fe0fe0

def z669 : W := mkw 0x0202c00005400000 0x0080b00001500000 0xc1fbec0007f70001 0xf07efb0001fdc000

def z670 : W := mkw 0x9090015c28a47bc5 0x242400570a291ef1 0x3e0401fcf8003fce 0x0f81007f3e000ff3

def z671 : W := mkw 0x0000000000000000 0x0000000000000000 0x1a68400c00000000 0x069a100300000000

def z672 : W := mkw 0x0000001000802200 0x0000000400200880 0x1604007000002382 0x0581001c000008e0

def z673 : W := mkw 0x2303fa1007daa202 0x08c0fe8401f6a880 0xd7fffe7007ffe383 0xf5ffff9c01fff8e0

def z674 : W := mkw 0x0000000000000000 0x0000000000000000 0xc000000001970001 0xb00000000065c000

def z675 : W := mkw 0x0000000000000000 0x0000000000000000 0x0e3b018000000000 0x038ec06000000000

def z676 : W := mkw 0x2001300002180002 0x08004c0000860000 0x0080300000180001 0x00200c0000060000

def z677 : W := mkw 0x0800042140000000 0x0200010850000000 0x21802c0360000000 0x08600b00d8000000

def z678 : W := mkw 0x1202c15805c02a00 0x0480b05601700a80 0x0000807001800000 0x0000201c00600000

def z679 : W := mkw 0x80900004282451c5 0x202400010a091471 0x7bc8000cf80413cf 0x9ef200033e0104f3

def z680 : W := mkw 0x2041308280000428 0x88104c20a000010a 0x2ebf318380003c7e 0x0bafcc60e0000f1f

def z681 : W := mkw 0x0000000000000000 0x0000000000000000 0xc098200000100001 0x3026080000040000

def z682 : W := mkw 0x80d000042a3c55ef 0xa03400010a8f157b 0xfbec520cfe7cffff 0xfefb14833f9f3fff

def z683 : W := mkw 0x21013a00021a8002 0x08404e800086a000 0xc1bb3e00061fc001 0x706ecf800187f000

def z684 : W := mkw 0x2243f0828758042a 0x8890fc20a1d6010a 0xeefff18387f83c7f 0xfbbffc60e1fe0f1f

def z685 : W := mkw 0x0080000400201101 0x0020000100080440 0x1a00000c00001382 0x06800003000004e0

def z686 : W := mkw 0x1282c15c05e03b01 0x04a0b05701780ec0 0x1e44c1fc01e03f82 0x8791307f00780fe0

def z687 : W := mkw 0x03000000075a8002 0x00c0000001d6a000 0x8000000007930000 0x2000000001e4c000

def z688 : W := mkw 0x3ec3ffffd7f83f2b 0x8fb0fffff5fe0fca 0xfffffffffff83fff 0xfffffffffffe0fff

def z689 : W := mkw 0x80900004282451c5 0x202400010a091471 0x73c80000606cd3cf 0xdcf20000181b34f3

def z690 : W := mkw 0x1282c14c05601901 0x04a0b05301580640 0x5a6b418c06601f82 0xd69ad063019807e0

def z691 : W := mkw 0x0280001405e03b01 0x00a0000501780ec0 0xda6c400c07e03f82 0xf69b100301f80fe0

def z692 : W := mkw 0xb2d3f1deaffc7fef 0xacb4fc77abff1ffb 0xfffff3fffffcffff 0xfffffcffffff3fff

def z693 : W := mkw 0xac113ea3f80440c4 0x2b044fa8fe011031 0x21803e03f80cc04d 0x08600f80fe033013

def z694 : W := mkw 0x8090001428a473c5 0x202400050a291cf1 0xfffcd27cf9ecf3cf 0xffff349f3e7b3cf3

def z695 : W := mkw 0x0820043140812210 0x4208010c50204884 0xe69cac7301932073 0x39a72b1cc064c81c

def z696 : W := mkw 0x1a22c57945c12a10 0x4688b15e51704a84 0x8417adf307932c30 0x2105eb7cc1e4cb0c

def z697 : W := mkw 0x3003f1ca80000000 0x0c00fc72a0000000 0x3efbf1ff80000000 0x0fbefc7fe0000000

def z698 : W := mkw 0x3403fbca90000000 0x0d00fef2a4000000 0x3beb538cf8000000 0x0efad4e33e000000

def z699 : W := mkw 0x22c1309687f83f2b 0x88b04c25a1fe0fca 0xeebf318387f83fff 0xfbafcc60e1fe0fff

def z700 : W := mkw 0x80900004282451c5 0x202400010a091471 0x5a68400c006cd3cf 0xd69a1003001b34f3

def z701 : W := mkw 0x3c03ffebd0000000 0x0f00fffaf4000000 0x05fbfff300000000 0x017efffcc0000000

def z702 : W := mkw 0x2b23fe3147dba212 0x4ac8ff8c51f6e884 0x8417ac7307932030 0x2105eb1cc1e4c80c

def z703 : W := mkw 0x3c23fffbd0812210 0x4f08fffef4204884 0xbffffffff9932030 0x2ffffffffe64c80c

def z704 : W := mkw 0x2043fa828218042a 0x8810fea0a086010a 0xefffff8386183c7f 0x7bffffe0e1860f1f

def z705 : W := mkw 0x21013a00021a8002 0x08404e800086a000 0xc1d8be00019fc001 0xb0762f800067f000

def z706 : W := mkw 0x3383fb4c077a9903 0x0ce0fed301dea640 0x0823538c0668dc00 0x4208d4e3019a3700

def z707 : W := mkw 0x204130828218042a 0x88104c20a086010a 0xefff3183861c3c7f 0xfbffcc60e1870f1f

def z708 : W := mkw 0x3003fb4800000000 0x0c00fed200000000 0x3ffbfffcf8000000 0x0ffeffff3e000000

def z709 : W := mkw 0x3c03ffebd0000000 0x0f00fffaf4000000 0xfffffffffe083c4f 0x7fffffffff820f13

def z710 : W := mkw 0x204130828218042a 0x88104c20a086010a 0xffff738ffe7cfc7f 0xffffdce3ff9f3f1f

def z711 : W := mkw 0x2001300002180002 0x08004c0000860000 0xc1fbfe0007ffc001 0xf07eff8001fff000

def z712 : W := mkw 0xa2d13096affc7fef 0xa8b44c25abff1ffb 0xeebf318387fcffff 0xfbafcc60e1ff3fff

def z713 : W := mkw 0x08200431608522d0 0x4208010c582148b4 0xf7dfadf367972ff3 0xbdf7eb7cd9e5cbfc

def z714 : W := mkw 0x8090001428a473c5 0x202400050a291cf1 0xc004000001ecf3cf 0xf0010000007b3cf3

def z715 : W := mkw 0x1c0005ebd0000000 0x0700017af4000000 0x3f802dfff8000000 0x0fe00b7ffe000000

def z716 : W := mkw 0x2303fa00075a8002 0x08c0fe8001d6a000 0xc1fbfe0007ffd04f 0xf07eff8001fff413

def z717 : W := mkw 0x2303fa00075a8002 0x08c0fe8001d6a000 0x81d3fe0007ffc001 0xa074ff8001fff000

def z718 : W := mkw 0x1f02cfebd5428000 0x07c0b3faf550a000 0x3f40cffff9e7c000 0x8fd033fffe79f000

def z719 : W := mkw 0x204130828218042a 0x88104c20a086010a 0xeebf73838678fc7f 0x7bafdce0e19e3f1f

def z720 : W := mkw 0x2343fa82875a842a 0x88d0fea0a1d6a10a 0x21c0fe0381ffc07d 0x88703f80e07ff01f

def z721 : W := mkw 0x1282c15c05e03b01 0x04a0b05701780ec0 0xdeffd1fc07e83f83 0xf7bff47f01fa0fe0

def z722 : W := mkw 0x1c02c5ebd0000000 0x0700b17af4000000 0x3e40c1fff8000000 0x0f90307ffe000000

def z723 : W := mkw 0x88300431688562d4 0x620c010c5a2158b5 0xfffcbe73f99ff3ff 0xffff2f9cfe67fcff

def z724 : W := mkw 0x08200431608522d0 0x4208010c582148b4 0xfffcfe7ff9ffe3f3 0xffff3f9ffe7ff8fc

def z725 : W := mkw 0x80b0001428a573d5 0x602c00050a295cf5 0x4000000001efd3cf 0xd0000000007bf4f3

def z726 : W := mkw 0x1c0005ebd0000000 0x0700017af4000000 0x3e6841fff8000000 0x0f9a107ffe000000

def z727 : W := mkw 0x1282c15c05e03b01 0x04a0b05701780ec0 0xfe7fc1fc87e03fce 0xff9ff07f21f80ff3

def z728 : W := mkw 0x82d000142ffc7fef 0xa0b400050bff1ffb 0xc004000007fcffff 0xf001000001ff3fff

def z729 : W := mkw 0x0800042140000000 0x0200010850000000 0x37d8ee7f78000000 0x0df63b9fde000000

def z730 : W := mkw 0x0302ca0005428000 0x00c0b2800150a000 0x6be8de0081efd04f 0xdafa3780207bf413

def z731 : W := mkw 0x08200431608522d0 0x4208010c582148b4 0xf614ac73619723f3 0xbd852b1cd865c8fc

def z732 : W := mkw 0x3303fb48075a8002 0x0cc0fed201d6a000 0xd1fbfe7c07ffc001 0xf47eff9f01fff000

def z733 : W := mkw 0x0302ca00075a8002 0x00c0b28001d6a000 0xc1e8de0007ffc001 0xf07a378001fff000

def z734 : W := mkw 0x1c02cf6950000000 0x0700b3da54000000 0x1960de7cf8000000 0x0658379f3e000000

def z735 : W := mkw 0x80900004282451c5 0x202400010a091471 0x1140520cf86cc38c 0x845014833e1b30e3

def z736 : W := mkw 0x3f03ffebd75a8002 0x0fc0fffaf5d6a000 0xfffbffffffe8c000 0xfffefffffffa3000

def z737 : W := mkw 0x204130828218042a 0x88104c20a086010a 0xe69f218306183c7f 0x79a7c860c1860f1f

def z738 : W := mkw 0x1c000f6950000000 0x070003da54000000 0x11000e7c78000000 0x0440039f1e000000

def z739 : W := mkw 0x1c0005ebd0000000 0x0700017af4000000 0x3e0001fff800104e 0x0f80007ffe000413

def z740 : W := mkw 0x2303fa0005428000 0x08c0fe800150a000 0x0153ee0001e7c000 0x8054fb800079f000

def z741 : W := mkw 0x3c43ffebd218042a 0x8f10fffaf486010a 0xffffffffff9f3c7f 0xffffffffffe7cf1f

def z742 : W := mkw 0x1c02cf6950000000 0x0700b3da54000000 0xdf7fcffc7e003c02 0x77dff3ff1f800f00

def z743 : W := mkw 0x0302ca00075a8002 0x00c0b28001d6a000 0x0140ce0001ffc001 0x80503380007ff000

def z744 : W := mkw 0x0000000000000000 0x0000000000000000 0x3ff8d27cf8000000 0x0ffe349f3e000000

def z745 : W := mkw 0x204130828218042a 0x88104c20a086010a 0xee27118386183c7f 0x7b89c460e1860f1f

def z746 : W := mkw 0x3f03ffebd75a8002 0x0fc0fffaf5d6a000 0xffffffffffffe073 0xfffffffffffff81c

def z747 : W := mkw 0x2303fa00075a8002 0x08c0fe8001d6a000 0xd1fbfe0c7fffc001 0xf47eff831ffff000

def z748 : W := mkw 0x204130828218042a 0x88104c20a086010a 0xefffff8387fffc7f 0xfbffffe0e1ffff1f

def z749 : W := mkw 0x1c42c5ebd0000428 0x8710b17af400010a 0xfe7fc1fffe003c7e 0x7f9ff07fff800f1f

def z750 : W := mkw 0x08200431608522d0 0x4208010c582148b4 0xd65cac73019723f3 0xb5972b1cc065c8fc

def z751 : W := mkw 0x284134a3c218042a 0x8a104d28f086010a 0xfffffffffe183c7f 0x7fffffffff860f1f

def z752 : W := mkw 0x2343fa00075a842a 0x88d0fe8001d6a10a 0xebfffe0087fffc7f 0xfaffff8021ffff1f

def z753 : W := mkw 0x286134b3e29d26fa 0xca184d2cf8a749be 0x19639df0e78f1f8c 0xc658e77c39e3c7e3

def z754 : W := mkw 0x1202c15805c02a00 0x0480b05601700a80 0x945781f007802f80 0xa515e07c01e00be0

def z755 : W := mkw 0x3f03ffebd5428000 0x0fc0fffaf550a000 0xfffbfffff9f7c001 0xbffefffffe7df000

def z756 : W := mkw 0x2e813eb7d5e03b01 0x0ba04fadf5780ec0 0xe1843e03ffe03f82 0xf8610f80fff80fe0

def z757 : W := mkw 0x1c02cf6950000000 0x0700b3da54000000 0x3ffbefff78000000 0x0ffefbffde000000

def z758 : W := mkw 0x204130828218042a 0x88104c20a086010a 0xeebf738f9e183c7f 0x7bafdce3e7860f1f

def z759 : W := mkw 0x2343fa82875a842a 0x88d0fea0a1d6a10a 0xc1fbfe0307ffc031 0xf07eff80c1fff00c

def z760 : W := mkw 0x2343fa00075a842a 0x88d0fe8001d6a10a 0xc1fffe0007ffec31 0xf07fff8001fffb0c

def z761 : W := mkw 0x08200431608522d0 0x4208010c582148b4 0xf7dcee7f799723f3 0xbdf73b9fde65c8fc

def z762 : W := mkw 0x3c03ffebd0000000 0x0f00fffaf4000000 0x3e7bedfff8000000 0x0f9efb7ffe000000

def z763 : W := mkw 0x08200431608522d0 0x4208010c582148b4 0x37d8ac73619703f1 0x8df62b1cd865c0fc

def z764 : W := mkw 0x3703fbca975a8002 0x0dc0fef2a5d6a000 0xeffbff8f9fffc001 0xfbfeffe3e7fff000

def z765 : W := mkw 0x2303fa00075a8002 0x08c0fe8001d6a000 0xc5fffe0307ffe031 0xf17fff80c1fff80c

def z766 : W := mkw 0x3c43ffebd218042a 0x8f10fffaf486010a 0xbffffffffe183c3c 0x6fffffffff860f0f

def z767 : W := mkw 0x3f03ffebd75a8002 0x0fc0fffaf5d6a000 0xfffbffffffffd04f 0xfffefffffffff413

def z768 : W := mkw 0x204130828218042a 0x88104c20a086010a 0xeeff718386783c7f 0xfbbfdc60e19e0f1f

def z769 : W := mkw 0x3c0135ebd2180002 0x0f004d7af4860000 0xfebb31fffe180001 0x7faecc7fff860000

def z770 : W := mkw 0x0040008280000428 0x80100020a000010a 0x2e27018386003c7e 0x4b89c060e1800f1f

def z771 : W := mkw 0x1080015c00a03b01 0x0420005700280ec0 0x1e2701fc06003f82 0x4789c07f01800fe0

def z772 : W := mkw 0x1202c15805c02a00 0x0480b05601700a80 0x961781f007802f82 0x2585e07c01e00be0

def z773 : W := mkw 0x1382c15c05e2bb01 0x04e0b0570178aec0 0xde7fc1fc07e7ff82 0xf79ff07f01f9ffe0

def z774 : W := mkw 0x2303fa00075a8002 0x08c0fe8001d6a000 0xc1dbee0007f7c001 0xb076fb8001fdf000

def z775 : W := mkw 0x3c03ffebd0000000 0x0f00fffaf4000000 0x15fbffff78000000 0x057effffde000000

def z776 : W := mkw 0x08200421600500d0 0x4208010858014034 0xefbf2d8366173c73 0x7befcb60d985cf1c

def z777 : W := mkw 0x3c03ffebd0000000 0x0f00fffaf4000000 0x3f53effff8000000 0x0fd4fbfffe000000

def z778 : W := mkw 0x3f03ffebd5428000 0x0fc0fffaf550a000 0x3ffbfffff860c000 0x0ffefffffe183000

def z779 : W := mkw 0x1f02cf69575a8002 0x07c0b3da55d6a000 0xd140ce7c7fffc001 0xf450339f1ffff000

def z780 : W := mkw 0x1202c15805c02a00 0x0480b05601700a80 0xc41781f007802f82 0xb105e07c01e00be0

def z781 : W := mkw 0x2343fa82875a842a 0x88d0fea0a1d6a10a 0x0963df8087efdc0c 0xc258f7e021fbf703

def z782 : W := mkw 0x2303fa00075a8002 0x08c0fe8001d6a000 0xc1fffe0007fffc03 0xf07fff8001ffff00

def z783 : W := mkw 0x32c3f1de87f83f2b 0x8cb0fc77a1fe0fca 0x30c0f07f81f803fd 0x8c303c1fe07e00ff

def z784 : W := mkw 0x3c43ffebd218042a 0x8f10fffaf486010a 0x9557efff7e102c30 0x2555fbffdf840b0c

def z785 : W := mkw 0x88b0043568a573d5 0x622c010d5a295cf5 0x36040073600033fe 0x0d81001cd8000cff

def z786 : W := mkw 0x3c03ffebd0000000 0x0f00fffaf4000000 0x3ffbfffffe001c00 0x4ffeffffff800700

def z787 : W := mkw 0x1080015c00a03b01 0x0420005700280ec0 0xde7f81fc07803f82 0xf79fe07f01e00fe0

def z788 : W := mkw 0x31813b5c02babb03 0x0c604ed700aeaec0 0x1f843ffc001fff83 0x07e10fff0007ffe0

def z789 : W := mkw 0x1382cb5c05e2bb01 0x04e0b2d70178aec0 0xde7fc3fc07e0ff82 0xf79ff0ff01f83fe0

def z790 : W := mkw 0x1282c15c05e03b01 0x04a0b05701780ec0 0xdffffffc07ffff83 0xf7ffffff01ffffe0

def z791 : W := mkw 0x2303fa00075a8002 0x08c0fe8001d6a000 0x41e8fe0001ffc001 0xd07a3f80007ff000

def z792 : W := mkw 0x1c00056950000000 0x0700015a54000000 0x3be8527cf8000000 0x0efa149f3e000000

def z793 : W := mkw 0x3c0135ebd0000000 0x0f004d7af4000000 0x3ffb73fff8000000 0x0ffedcfffe000000

def z794 : W := mkw 0x1c00056950000000 0x0700015a54000000 0x1e0001fc78000000 0x0780007f1e000000

def z795 : W := mkw 0x0342ca8285428428 0x80d0b2a0a150a10a 0x2f44cf8381e7fc7e 0x8bd133e0e079ff1f

def z796 : W := mkw 0x88b0043568a573d5 0x622c010d5a295cf5 0x3a00007cf80013ce 0x0e80001f3e0004f3

def z797 : W := mkw 0x1c02cf6950000000 0x0700b3da54000000 0x1000427c78000000 0x0400109f1e000000

def z798 : W := mkw 0x88b0043568a573d5 0x622c010d5a295cf5 0x1000007c78000380 0x0400001f1e0000e0

def z799 : W := mkw 0x08200431608522d0 0x4208010c582148b4 0xd75cac73619723b2 0xb5d72b1cd865c8ec

def z800 : W := mkw 0x204130828218042a 0x88104c20a086010a 0xefbf3d83861f3c7f 0x7befcf60e187cf1f

def z801 : W := mkw 0x3703fbca975a8002 0x0dc0fef2a5d6a000 0xc1fbff8007ffc001 0xf07effe001fff000

def z802 : W := mkw 0x1282c15c05e03b01 0x04a0b05701780ec0 0xde1781fc07e03f82 0xf785e07f01f80fe0

def z803 : W := mkw 0x1282c15c05e03b01 0x04a0b05701780ec0 0x5a6bc1fc07e01f82 0xd69af07f01f807e0

def z804 : W := mkw 0x204130828218042a 0x88104c20a086010a 0xefffbd8386183c7f 0x7bffef60e1860f1f

def z805 : W := mkw 0x1282c15c05e03b01 0x04a0b05701780ec0 0xde3f81fc07803f82 0x778fe07f01e00fe0

def z806 : W := mkw 0x1c4005ebd0000428 0x8710017af400010a 0x3e0401fff8002c30 0x0f81007ffe000b0c

def z807 : W := mkw 0x3c43ffebd218042a 0x8f10fffaf486010a 0x3ffbfffffe181c7d 0x4ffeffffff86071f

def z808 : W := mkw 0x2343fa82875a842a 0x88d0fea0a1d6a10a 0xc417ad8307fffc7f 0xf105eb60c1ffff1f

def z809 : W := mkw 0x3703fb48175a8002 0x0dc0fed205d6a000 0xc1fbfe0c1fffc001 0xf07eff8307fff000

def z810 : W := mkw 0x1282c15c05e03b01 0x04a0b05701780ec0 0xfe7fc1fcffe03f82 0xff9ff07f3ff80fe0

def z811 : W := mkw 0x2303fa00075a8002 0x08c0fe8001d6a000 0xefffff8307fffc73 0xfbffffe0c1ffff1c

def z812 : W := mkw 0x3c03ffebd0000000 0x0f00fffaf4000000 0x3ffbfffff808004d 0x0ffefffffe020013

def z813 : W := mkw 0x80900004282451c5 0x202400010a091471 0x3bc0520cf86cd3cf 0x8ef014833e1b34f3

def z814 : W := mkw 0x204130828218042a 0x88104c20a086010a 0x8417218306103c7e 0x2105c860c1840f1f

def z815 : W := mkw 0x80900004282451c5 0x202400010a091471 0xfbe8520cf9ffd3cf 0xfefa14833e7ff4f3

def z816 : W := mkw 0x03000000075a8002 0x00c0000001d6a000 0xc1f8fe0007ffc001 0xf07e3f8001fff000

def z817 : W := mkw 0x1c000febd0000000 0x070003faf4000000 0x3f000ffff8000000 0x0fc003fffe000000

def z818 : W := mkw 0x3c03ffebd0000000 0x0f00fffaf4000000 0x182353fcf8000000 0x0608d4ff3e000000

def z819 : W := mkw 0x08200431608522d0 0x4208010c582148b4 0xfffcfe73e1fff3ff 0xffff3f9cf87ffcff

def z820 : W := mkw 0x1282c15c05e03b01 0x04a0b05701780ec0 0xde3f41fc06603f82 0x778fd07f01980fe0

def z821 : W := mkw 0x08200431608522d0 0x4208010c582148b4 0xf7dcee7361f7e3f3 0xbdf73b9cd87df8fc

def z822 : W := mkw 0x1282c15c05e03b01 0x04a0b05701780ec0 0xd65fc1fc07e02f82 0xb597f07f01f80be0

def z823 : W := mkw 0x2303fa82875a8002 0x08c0fea0a1d6a000 0xefffff8387ffe073 0xfbffffe0e1fff81c

def z824 : W := mkw 0x1c0005ebd0000000 0x0700017af4000000 0x7fe853fff86cc001 0xdffa14fffe1b3000

def z825 : W := mkw 0x3d03ffebd21a8002 0x0f40fffaf486a000 0xfffbfffff99fc001 0xbffefffffe67f000

def z826 : W := mkw 0x9212c1582dc46ac4 0x2484b0560b711ab1 0xa59793f0ff8cec4d 0x2965e4fc3fe33b13

def z827 : W := mkw 0x8090001428a47bc5 0x202400050a291ef1 0x0004000000003fce 0x0001000000000ff3

def z828 : W := mkw 0x23013a00075a8002 0x08c04e8001d6a000 0xc0002c0007ffc001 0xf0000b0001fff000

def z829 : W := mkw 0x3c013febd0000000 0x0f004ffaf4000000 0x31803e7ff8000000 0x0c600f9ffe000000

def z830 : W := mkw 0x08200431608522d0 0x4208010c582148b4 0x8414ac73019723b0 0xa1052b1cc065c8ec

def z831 : W := mkw 0x1282c15c05e03b01 0x04a0b05701780ec0 0xfeffc1fc07e03fc3 0xffbff07f01f80ff0

def z832 : W := mkw 0x03000a0005428000 0x00c002800150a000 0x01000e0001e7c000 0x804003800079f000

def z833 : W := mkw 0x80900004282451c5 0x202400010a091471 0x7be8de0cf9efd3cf 0xdefa37833e7bf4f3

def z834 : W := mkw 0x204130828218042a 0x88104c20a086010a 0xefff738386183c7f 0x7bffdce0e1860f1f

def z835 : W := mkw 0x3c43ffebd218042a 0x8f10fffaf486010a 0xfffffffffe182c31 0x7fffffffff860b0c

def z836 : W := mkw 0x3743fbca975a842a 0x8dd0fef2a5d6a10a 0xefffff8f9ffffc7f 0xfbffffe3e7ffff1f

def z837 : W := mkw 0x2303fa00075a8002 0x08c0fe8001d6a000 0xc153ee0007ffc001 0xf054fb8001fff000

def z838 : W := mkw 0x1c0005ebd0000000 0x0700017af4000000 0x3e10adfff8000000 0x0f842b7ffe000000

def z839 : W := mkw 0x1382cb5c05e2bb01 0x04e0b2d70178aec0 0xdfffeffc07f7ff83 0xf7fffbff01fdffe0

def z840 : W := mkw 0x3c03ffebd0000000 0x0f00fffaf4000000 0x3e33fffff8000000 0x0f8cfffffe000000

def z841 : W := mkw 0x204130828218042a 0x88104c20a086010a 0xae97318386183c7f 0x2ba5cc60e1860f1f

def z842 : W := mkw 0x3c03ff6950000000 0x0f00ffda54000000 0x1163de7c78000000 0x0458f79f1e000000

def z843 : W := mkw 0x12a2c15c05e13b11 0x44a8b05701784ec4 0xde7fc1fc07f33fb2 0xf79ff07f01fccfec

def z844 : W := mkw 0x2303fa8285428000 0x08c0fea0a150a000 0x2ffbff8381e7c000 0x8bfeffe0e079f000

def z845 : W := mkw 0x1c02cf6950000000 0x0700b3da54000000 0x7be8de7cf808104f 0x5efa379f3e020413

def z846 : W := mkw 0x3423fbdab08522d0 0x4d08fef6ac2148b4 0xc827538c999723f3 0xb209d4e32665c8fc

def z847 : W := mkw 0x80900004282451c5 0x202400010a091471 0x7aa8520cf868d3cf 0x5eaa14833e1a34f3

def z848 : W := mkw 0x2b23fe3167dfa2d2 0x4ac8ff8c59f7e8b4 0x362752736668e3f2 0x4d89d49cd99a38fc

def z849 : W := mkw 0x1c42cf695218042a 0x8710b3da5486010a 0xd144ce7c7e183c7f 0x7451339f1f860f1f

def z850 : W := mkw 0xa87134a3ea1d44fe 0xea1c4d28fa87513f 0x21803e03f81fc07d 0x08600f80fe07f01f

def z851 : W := mkw 0x1e02cf6955400000 0x0780b3da55500000 0xd17bce7c7fe00000 0xf45ef39f1ff80000

def z852 : W := mkw 0x2303fa00075a8002 0x08c0fe8001d6a000 0xc9fbfe0087ffd00d 0xf27eff8021fff403

def z853 : W := mkw 0x3c03ffebd0000000 0x0f00fffaf4000000 0xfffbfffff9ffc001 0xfffefffffe7ff000

def z854 : W := mkw 0x08200431608522d0 0x4208010c582148b4 0x37c4ac73619723f3 0x8df12b1cd865c8fc

def z855 : W := mkw 0x3c013febd0000000 0x0f004ffaf4000000 0x3e002dfff8000000 0x0f800b7ffe000000

def z856 : W := mkw 0x3f43ffebd75a842a 0x8fd0fffaf5d6a10a 0xfffbffffffffc07d 0xfffefffffffff01f

def z857 : W := mkw 0x3c43ffebd218042a 0x8f10fffaf486010a 0xbe17adfffe103c7e 0x2f85eb7fff840f1f

def z858 : W := mkw 0x1aa2c56d656519d1 0x46a8b15b59594674 0x29a36d8f66771c71 0x4a68db63d99dc71c

def z859 : W := mkw 0x8090000408205105 0x2024000102081441 0x7be8520cf868d38e 0xdefa14833e1a34e3

def z860 : W := mkw 0x1c00056950000000 0x0700015a54000000 0x11408c7c78000000 0x0450231f1e000000

def z861 : W := mkw 0x80b0001428a573d5 0x602c00050a295cf5 0x0000000001e7c380 0x800000000079f0e0

def z862 : W := mkw 0x1282c15c05e03b01 0x04a0b05701780ec0 0x841781f007e02f80 0xa105e07c01f80be0

def z863 : W := mkw 0xa8f134b7eabd77ff 0xea3c4d2dfaaf5dff 0xfebf31fffe183fff 0x7fafcc7fff860fff

def z864 : W := mkw 0x3c013febd0000000 0x0f004ffaf4000000 0x3fbb3ffff8000000 0x0feecffffe000000

def z865 : W := mkw 0x9292c15c0de07b05 0x24a4b05703781ec1 0xde7fc3fc1fe0ff82 0xf79ff0ff07f83fe0

def z866 : W := mkw 0x80b0001428a573d5 0x602c00050a295cf5 0x00040000000033fe 0x0001000000000cff

def z867 : W := mkw 0x3f03ff69575a8002 0x0fc0ffda55d6a000 0xdffbfffc7fffc001 0xf7feffff1ffff000

def z868 : W := mkw 0x2c613ea3f21d04fa 0xcb184fa8fc87413e 0x21803e03f81f007d 0x08600f80fe07c01f

def z869 : W := mkw 0x21413a82821a842a 0x88504ea0a086a10a 0xefffbf83879ffc7f 0xfbffefe0e1e7ff1f

def z870 : W := mkw 0x0820043140812210 0x4208010c50204884 0x9454ac73019323b0 0xa5152b1cc064c8ec

def z871 : W := mkw 0x204130828218042a 0x88104c20a086010a 0xaebf318386103c7e 0x2bafcc60e1840f1f

def z872 : W := mkw 0x1c42cfebd0000428 0x8710b3faf400010a 0x3f44cffff8003c7e 0x0fd133fffe000f1f

def z873 : W := mkw 0x1f02cf6955428000 0x07c0b3da5550a000 0xf7d8ee7f79f7c001 0xbdf63b9fde7df000

def z874 : W := mkw 0x80900004282451c5 0x202400010a091471 0x7fec538cf86cffcf 0xdffb14e33e1b3ff3

def z875 : W := mkw 0x2303fa00075a8002 0x08c0fe8001d6a000 0x0140de0001efc000 0x80503780007bf000

def z876 : W := mkw 0x3e03ffebd5400000 0x0f80fffaf5500000 0xfffbffffffecc001 0xfffefffffffb3000

def z877 : W := mkw 0xa393fa142ffefbc7 0x28e4fe850bffbef1 0xc1fffe0007ffffcf 0xf07fff8001fffff3

def z878 : W := mkw 0x3f03ff69575a8002 0x0fc0ffda55d6a000 0x9153ee7c7f930000 0x2454fb9f1fe4c000

def z879 : W := mkw 0x0000000000000000 0x0000000000000000 0x41e8de0001efc001 0xd07a3780007bf000

def z880 : W := mkw 0x1f0005ebd75a8002 0x07c0017af5d6a000 0xfe0001ffffffc001 0xff80007ffffff000

def z881 : W := mkw 0x1c02c5ebd0000000 0x0700b17af4000000 0x3ffbd3fff8000000 0x0ffef4fffe000000

def z882 : W := mkw 0x80900004282451c5 0x202400010a091471 0xfffcfe0ff9fff3ff 0xffff3f83fe7ffcff

def z883 : W := mkw 0x1c00056950000000 0x0700015a54000000 0x1140427c78000000 0x0450109f1e000000

def z884 : W := mkw 0x23013000075a8002 0x08c04c0001d6a000 0xc1fbbc0007ffc001 0xf07eef0001fff000

def z885 : W := mkw 0x1282c15c05e03b01 0x04a0b05701780ec0 0xffffd3fcffecff83 0xfffff4ff3ffb3fe0

def z886 : W := mkw 0x3c03ffebd2180002 0x0f00fffaf4860000 0xfffffffffe183c03 0x7fffffffff860f00

def z887 : W := mkw 0x1082c15c00a03b01 0x0420b05700280ec0 0xde7fc1fc06003f82 0x779ff07f01800fe0

def z888 : W := mkw 0x2703fa82975a8002 0x09c0fea0a5d6a000 0xc1fbfe009fffc001 0xf07eff8027fff000

def z889 : W := mkw 0x3c03ffebd0000000 0x0f00fffaf4000000 0x2db3fffff8000000 0x0b6cfffffe000000

def z890 : W := mkw 0x1c02c5ebd0000000 0x0700b17af4000000 0x3e2341fff8000000 0x0f88d07ffe000000

def z891 : W := mkw 0x2303fa00075a8002 0x08c0fe8001d6a000 0x41ebde0007efc001 0xd07af78001fbf000

def z892 : W := mkw 0x29613ea3e21f84fa 0xca584fa8f887e13e 0x21803e03e01fc07d 0x08600f80f807f01f

def z893 : W := mkw 0x1282c15c05e03b01 0x04a0b05701780ec0 0x841781f007803f82 0x2105e07c01e00fe0

def z894 : W := mkw 0x1282c15c05e03b01 0x04a0b05701780ec0 0x1e7fc1fc06603f82 0x479ff07f01980fe0

def z895 : W := mkw 0x3f03ffebd5428000 0x0fc0fffaf550a000 0x7ffbfffff9efc001 0xdffefffffe7bf000

def z896 : W := mkw 0x3c03ffebd0000000 0x0f00fffaf4000000 0xfffbfffff9800000 0xbffefffffe600000

def z897 : W := mkw 0x3f03ffebd75a8002 0x0fc0fffaf5d6a000 0xbffbfffffff7c000 0xaffefffffffdf000

def z898 : W := mkw 0xbc93ffeff82451c5 0x2f24fffbfe091471 0x4413adf3006cd3cf 0xd104eb7cc01b34f3

def z899 : W := mkw 0x08200431608522d0 0x4208010c582148b4 0xffffadf3619723f3 0xbfffeb7cd865c8fc

def z900 : W := mkw 0x08200431608522d0 0x4208010c582148b4 0xf65cac73619323f2 0xbd972b1cd864c8fc

def z901 : W := mkw 0x1282c15c05e03b01 0x04a0b05701780ec0 0x182341fc06601f80 0x4608d07f019807e0

def z902 : W := mkw 0x2303fa00075a8002 0x08c0fe8001d6a000 0xc17bde0007efc000 0xf05ef78001fbf000

def z903 : W := mkw 0x0000001000802200 0x0000000400200880 0xd65f81f007802f82 0xb597e07c01e00be0

def z904 : W := mkw 0x3c03ff6950000000 0x0f00ffda54000000 0x3bfbfe7cf8000000 0x0efeff9f3e000000

def z905 : W := mkw 0x3c03ffebd0000000 0x0f00fffaf4000000 0x35d3fffff8000000 0x0d74fffffe000000

def z906 : W := mkw 0x80900004282451c5 0x202400010a091471 0x3be8520cf868d3ce 0x4efa14833e1a34f3

def z907 : W := mkw 0x88b0043548a17315 0x622c010d52285cc5 0x8c34fe7f99fbf03c 0x630d3f9fe67efc0f

def z908 : W := mkw 0xa0f13096aabd77ff 0xe83c4c25aaaf5dff 0xeebf318387ffffff 0xfbafcc60e1ffffff

def z909 : W := mkw 0x1282c15c05e03b01 0x04a0b05701780ec0 0xd87bc1fc07e01f80 0xf61ef07f01f807e0

def z910 : W := mkw 0x1c0005ebd0000000 0x0700017af4000000 0x3e9821fff8000000 0x0fa6087ffe000000

def z911 : W := mkw 0x08200431608522d0 0x4208010c582148b4 0xf7dcac7367973ff3 0xfdf72b1cd9e5cffc

def z912 : W := mkw 0x2303fa00075a8002 0x08c0fe8001d6a000 0xe1fbfe0087ffc04d 0xf87eff8021fff013

def z913 : W := mkw 0x88300431688562d4 0x620c010c5a2158b5 0xf7fcfe73f9ffe3ff 0xfdff3f9cfe7ff8ff

def z914 : W := mkw 0x1c0005ebd0000000 0x0700017af4000000 0x3000007ff8000000 0x0c00001ffe000000

def z915 : W := mkw 0x2343fa82875a842a 0x88d0fea0a1d6a10a 0xe1fffe0387fffc7f 0xf87fff80e1ffff1f

def z916 : W := mkw 0x3c03ff6950000000 0x0f00ffda54000000 0x1153ee7c78000000 0x0454fb9f1e000000

def z917 : W := mkw 0x0800042140000000 0x0200010850000000 0xfffcfe7ff818307f 0x7fff3f9ffe060c1f

def z918 : W := mkw 0x1c0005ebd0000000 0x0700017af4000000 0x3f408dfff8000000 0x0fd0237ffe000000

def z919 : W := mkw 0x3f03ffebd75a8002 0x0fc0fffaf5d6a000 0x3e2353fffe68c000 0x4f88d4ffff9a3000

def z920 : W := mkw 0x3303fb48075a8002 0x0cc0fed201d6a000 0xc5fbfff007ffc001 0xf17efffc01fff000

def z921 : W := mkw 0x80900004282451c5 0x202400010a091471 0x5b68520cf86cd38e 0xd6da14833e1b34e3

def z922 : W := mkw 0x0302ca0005428000 0x00c0b2800150a000 0xc1fbde0007efc001 0xf07ef78001fbf000

def z923 : W := mkw 0x3c03ffebd2180002 0x0f00fffaf4860000 0xbffbfffffe100000 0x2ffeffffff840000

def z924 : W := mkw 0x1282c15c05e03b01 0x04a0b05701780ec0 0xffffd3fc87ecffcf 0xfffff4ff21fb3ff3

def z925 : W := mkw 0x3c0135ebd0000000 0x0f004d7af4000000 0x3e2311fff8000000 0x0f88c47ffe000000

def z926 : W := mkw 0x80900004282451c5 0x202400010a091471 0xfbfb520cfe6cd3cf 0xfefed4833f9b34f3

def z927 : W := mkw 0x2303fa0005428000 0x08c0fe800150a000 0xc1fbfe0001f7c001 0xb07eff80007df000

def z928 : W := mkw 0x2b03fe21475a8002 0x0ac0ff8851d6a000 0xfffbfe7fffffc001 0xfffeff9ffffff000

def z929 : W := mkw 0x23013a00075a8002 0x08c04e8001d6a000 0xc1e87e0007ffc001 0xf07a1f8001fff000

def z930 : W := mkw 0x0000001000802200 0x0000000400200880 0xf7dcac73019723f3 0xbdf72b1cc065c8fc

def z931 : W := mkw 0x0820043140812210 0x4208010c50204884 0x9614ac73019323b2 0x25852b1cc064c8ec

def z932 : W := mkw 0x1c02c5ebd0000000 0x0700b17af4000000 0x3ffbedfff8000000 0x0ffefb7ffe000000

def z933 : W := mkw 0x80900004282451c5 0x202400010a091471 0x7be87e0cf87fd3cf 0xdefa1f833e1ff4f3

def z934 : W := mkw 0x1c02cf6950000000 0x0700b3da54000000 0x3b40ce7cf8000000 0x0ed0339f3e000000

def z935 : W := mkw 0x1282c15c05e03b01 0x04a0b05701780ec0 0x941781fc07802f80 0x2505e07f01e00be0

def z936 : W := mkw 0x1c0005ebd0000000 0x0700017af4000000 0x3f4043fff8000000 0x0fd010fffe000000

def z937 : W := mkw 0x3c03ffebd0000000 0x0f00fffaf4000000 0x7ffbfffff86cd04f 0xdffefffffe1b3413

def z938 : W := mkw 0x3f03ffebd75a8002 0x0fc0fffaf5d6a000 0xbe13adffff930000 0x2f84eb7fffe4c000

def z939 : W := mkw 0x0342ca00075a842a 0x80d0b28001d6a10a 0xc144ce0007fffc7f 0xf051338001ffff1f

def z940 : W := mkw 0x204130828218042a 0x88104c20a086010a 0xfebf318ffe183c7f 0x7fafcc63ff860f1f

def z941 : W := mkw 0x204130828218042a 0x88104c20a086010a 0xfeff318386183fff 0xffbfcc60e1860fff

def z942 : W := mkw 0x08200431608522d0 0x4208010c582148b4 0x8414ac73019323f2 0x21052b1cc064c8fc

def z943 : W := mkw 0x3c03ffebd0000000 0x0f00fffaf4000000 0x3ffbfffff8100071 0x0ffefffffe04001c

def z944 : W := mkw 0x80900004282451c5 0x202400010a091471 0xfbf8720cf87cd3cf 0xfefe1c833e1f34f3

def z945 : W := mkw 0x204130828218042a 0x88104c20a086010a 0x2e07018386003c7e 0x0b81c060e1800f1f

def z946 : W := mkw 0x2343fa82875a842a 0x88d0fea0a1d6a10a 0xeffbff8387ffdc0d 0xfbfeffe0e1fff703

def z947 : W := mkw 0x3303fb48075a8002 0x0cc0fed201d6a000 0xfffbfffcffffc001 0xfffeffff3ffff000

def z948 : W := mkw 0x3c03ffebd0000000 0x0f00fffaf4000000 0x3ffbfffff9870000 0x8ffefffffe61c000

def z949 : W := mkw 0x3c03ffebd0000000 0x0f00fffaf4000000 0x37d8fe7ff8000000 0x0df63f9ffe000000

def z950 : W := mkw 0x3c43ffebd218042a 0x8f10fffaf486010a 0x3ffffffffe083c7e 0x4fffffffff820f1f

def z951 : W := mkw 0x3743fbca975a842a 0x8dd0fef2a5d6a10a 0xc9fbff8c9fffdc0d 0xf27effe327fff703

def z952 : W := mkw 0x3f03ffebd5428000 0x0fc0fffaf550a000 0xfffbffffffe7c000 0xfffefffffff9f000

def z953 : W := mkw 0x1c02cf6950000000 0x0700b3da54000000 0x117bce7c78000000 0x045ef39f1e000000

def z954 : W := mkw 0x1c0005ebd0000000 0x0700017af4000000 0x3ea811fff8000000 0x0faa047ffe000000

def z955 : W := mkw 0x83b000142ffff3d7 0x60ec00050bfffcf5 0xc004000007fff3ff 0xf001000001fffcff

def z956 : W := mkw 0x3d43ffebd21a842a 0x8f50fffaf486a10a 0xfffffffffe1ffc7f 0x7fffffffff87ff1f

def z957 : W := mkw 0x280134a3c0000000 0x0a004d28f0000000 0x3ffbfffff8000000 0x0ffefffffe000000

def z958 : W := mkw 0x0800042140000000 0x0200010850000000 0x3e00007ff8000000 0x0f80001ffe000000

def z959 : W := mkw 0x0302ca0005428000 0x00c0b2800150a000 0x8150ee0001f7c000 0xa0543b80007df000

def z960 : W := mkw 0x204130828218042a 0x88104c20a086010a 0xc4bf318306183c7f 0x712fcc60c1860f1f

def z961 : W := mkw 0x0300000005428000 0x00c000000150a000 0xc1d8ac0001f7c001 0xb0762b00007df000

def z962 : W := mkw 0x3c03ffebd0000000 0x0f00fffaf4000000 0x37dbefff78000000 0x0df6fbffde000000

def z963 : W := mkw 0x0040008280000428 0x80100020a000010a 0xae17018386003c7e 0x2b85c060e1800f1f

def z964 : W := mkw 0x80900004282451c5 0x202400010a091471 0x7ff8720ff86cd3cf 0xdffe1c83fe1b34f3

def z965 : W := mkw 0x829000142de47bc5 0x20a400050b791ef1 0xc004000007e4ff82 0xf001000001f93fe0

def z966 : W := mkw 0x3c43ffebd218042a 0x8f10fffaf486010a 0xfffbfffffe181c0d 0x7ffeffffff860703

def z967 : W := mkw 0x3c03ffebd2180002 0x0f00fffaf4860000 0x3ffbfffff8180001 0x0ffefffffe060000

def z968 : W := mkw 0x08200431608522d0 0x4208010c582148b4 0xffdcadf361973ff3 0xbff72b7cd865cffc

def z969 : W := mkw 0x2303fa82875a8002 0x08c0fea0a1d6a000 0xe1fbfe0387ffc001 0xf87eff80e1fff000

def z970 : W := mkw 0x3f03ffebd75a8002 0x0fc0fffaf5d6a000 0xfffbfffffe78c001 0x7ffeffffff9e3000

def z971 : W := mkw 0x1282c15c05e03b01 0x04a0b05701780ec0 0xdfffc1fc07e43f83 0xf7fff07f01f90fe0

def z972 : W := mkw 0x3c4135ebd218042a 0x8f104d7af486010a 0xffffbdfffe183c7f 0x7fffef7fff860f1f

def z973 : W := mkw 0x1282c15c05e03b01 0x04a0b05701780ec0 0xde7fc1fc07e83fcf 0xf79ff07f01fa0ff3

def z974 : W := mkw 0x03000000075a8002 0x00c0000001d6a000 0xc010ac0007ffc001 0xf0042b0001fff000

def z975 : W := mkw 0x3c0135ebd0000000 0x0f004d7af4000000 0x3e8031fff8000000 0x0fa00c7ffe000000

def z976 : W := mkw 0x3c03ffebd0000000 0x0f00fffaf4000000 0xfffffffffe103c73 0x7fffffffff840f1c

def z977 : W := mkw 0x80900004282451c5 0x202400010a091471 0x7a68520cf868d3ce 0xde9a14833e1a34f3

def z978 : W := mkw 0x3e03ffebd5400000 0x0f80fffaf5500000 0x3ffbfffffe600000 0x4ffeffffff980000

def z979 : W := mkw 0x1c0005ebd0000000 0x0700017af4000000 0x3fc801fff8000000 0x0ff2007ffe000000

def z980 : W := mkw 0x204130828218042a 0x88104c20a086010a 0x2ea7318386183c7f 0x4ba9cc60e1860f1f

def z981 : W := mkw 0x0302ca0005428000 0x00c0b2800150a000 0xc1fbee0007f7c001 0xf07efb8001fdf000

def z982 : W := mkw 0x80900004282451c5 0x202400010a091471 0x5960520cf86cd3cf 0xd65814833e1b34f3

def z983 : W := mkw 0x80b0001428a573d5 0x602c00050a295cf5 0xc1fcfe0001fff3ff 0xf07f3f80007ffcff

def z984 : W := mkw 0x1282c15c05e03b01 0x04a0b05701780ec0 0xd47fc1fc07e02f80 0xf51ff07f01f80be0

def z985 : W := mkw 0x3c0135ebd0000000 0x0f004d7af4000000 0x3e1321fff8000000 0x0f84c87ffe000000

def z986 : W := mkw 0x0302ca0005428000 0x00c0b2800150a000 0x00008c0001e7c000 0x800023000079f000

def z987 : W := mkw 0x3c03ffebd0000000 0x0f00fffaf4000000 0x7ffbfffff8000382 0x9ffefffffe0000e0

def z988 : W := mkw 0x1282c15c05e03b01 0x04a0b05701780ec0 0xdf7fc3fc07e4ff82 0xf7dff0ff01f93fe0

def z989 : W := mkw 0x0302ca0005428000 0x00c0b2800150a000 0x017bce0001e7c000 0x805ef3800079f000

def z990 : W := mkw 0x204130828218042a 0x88104c20a086010a 0xcc37318386183c7f 0x730dcc60e1860f1f

def z991 : W := mkw 0x1c02c56950000000 0x0700b15a54000000 0x1e7bc1fc78000000 0x079ef07f1e000000

def z992 : W := mkw 0x3f43ffebd75a842a 0x8fd0fffaf5d6a10a 0xbfffffffff932c30 0x2fffffffffe4cb0c

def z993 : W := mkw 0x2303fa00075a8002 0x08c0fe8001d6a000 0xc0bbbc0007ffc001 0xf02eef0001fff000

def z994 : W := mkw 0x0000000000000000 0x0000000000000000 0xeebf318386183c7f 0x7bafcc60e1860f1f

def z995 : W := mkw 0x204130828218042a 0x88104c20a086010a 0xffff3183e6183c7f 0x7fffcc60f9860f1f

def z996 : W := mkw 0xa0d13086aa3c55ef 0xa8344c21aa8f157b 0x9557638f7e74efb0 0xa555d8e3df9d3bec

def z997 : W := mkw 0x08200431608522d0 0x4208010c582148b4 0xf7dcac7361ffe3f3 0xfdf72b1cd87ff8fc

def z998 : W := mkw 0x1282c15c05e03b01 0x04a0b05701780ec0 0xde7fc1fc07f03ff3 0xf79ff07f01fc0ffc

def z999 : W := mkw 0x1c02cf6950000000 0x0700b3da54000000 0x51e8de7c786cc001 0xd47a379f1e1b3000

def z1000 : W := mkw 0x1382cb5c05e2bb01 0x04e0b2d70178aec0 0xdfffdffc07efff83 0xf7fff7ff01fbffe0

def z1001 : W := mkw 0x2343fa00075a842a 0x88d0fe8001d6a10a 0xe7fffe0307fffc7f 0xf9ffff80c1ffff1f

def z1002 : W := mkw 0x3f03ffebd75a8002 0x0fc0fffaf5d6a000 0xfffffffffffffc03 0xffffffffffffff00

def z1003 : W := mkw 0x1282c15c05e03b01 0x04a0b05701780ec0 0xdeffe1fc07f03f83 0xf7bff87f01fc0fe0

def z1004 : W := mkw 0x1c02cfebd0000000 0x0700b3faf4000000 0x3f7bcffff8000000 0x0fdef3fffe000000

def z1005 : W := mkw 0x3c03ffebd0000000 0x0f00fffaf4000000 0xfffffffff9972073 0xbffffffffe65c81c

def z1006 : W := mkw 0x3403fbca90000000 0x0d00fef2a4000000 0x3ffbd3fcf8000000 0x0ffef4ff3e000000

def z1007 : W := mkw 0x03000000075a8002 0x00c0000001d6a000 0xc1408c0007ffc001 0xf050230001fff000

def z1008 : W := mkw 0x286134a3e21d04fa 0xca184d28f887413e 0x20803003e018007d 0x08200c00f806001f

def z1009 : W := mkw 0x2343fa82875a842a 0x88d0fea0a1d6a10a 0xcfffff8087fffc0f 0xf3ffffe021ffff03

def z1010 : W := mkw 0x08200431608522d0 0x4208010c582148b4 0xfffcbc73e19723f3 0xbfff2f1cf865c8fc

def z1011 : W := mkw 0x2303fa00075a8002 0x08c0fe8001d6a000 0xc7fffe0007ffe003 0xf1ffff8001fff800

def z1012 : W := mkw 0x0302ca00075a8002 0x00c0b28001d6a000 0xc1d8ee0007ffc001 0xf0763b8001fff000

def z1013 : W := mkw 0x0302ca00075a8002 0x00c0b28001d6a000 0xc0008c0007ffc001 0xf000230001fff000

def z1014 : W := mkw 0x1282c15c05e03b01 0x04a0b05701780ec0 0xffffedff07f73ff3 0xfffffb7fc1fdcffc

def z1015 : W := mkw 0x3f03ffebd75a8002 0x0fc0fffaf5d6a000 0xd5fbffff7fffc001 0xf57effffdffff000

def z1016 : W := mkw 0x3c03ffebd0000000 0x0f00fffaf4000000 0x3e7bd3fff8000000 0x0f9ef4fffe000000

def z1017 : W := mkw 0x1002c14800000000 0x0400b05200000000 0x1f7bc3fc78000000 0x07def0ff1e000000

def z1018 : W := mkw 0x3f03ffebd75a8002 0x0fc0fffaf5d6a000 0x3ffbfffffe7fc001 0x4ffeffffff9ff000

def z1019 : W := mkw 0x3c03ffebd0000000 0x0f00fffaf4000000 0xbffffffff8102030 0x2ffffffffe04080c

def z1020 : W := mkw 0x9292c15c0de07b05 0x24a4b05703781ec1 0xdfffd3fc9fecff8f 0xf7fff4ff27fb3fe3

def z1021 : W := mkw 0x1f02cf6955428000 0x07c0b3da5550a000 0x7be8de7cf9efc001 0xdefa379f3e7bf000

def z1022 : W := mkw 0x80f000142abd77ff 0xe03c00050aaf5dff 0xc004000007ffffff 0xf001000001ffffff

def z1023 : W := mkw 0x1c02cf6950000000 0x0700b3da54000000 0x1b68ce7c78000000 0x06da339f1e000000

def z1024 : W := mkw 0x3c43ffebd0000428 0x8f10fffaf400010a 0x3ffffffff8002c30 0x0ffffffffe000b0c

def z1025 : W := mkw 0x3c03f5ebd0000000 0x0f00fd7af4000000 0x3efbf1fff8000000 0x0fbefc7ffe000000

def z1026 : W := mkw 0x1280015c05e03b01 0x04a0005701780ec0 0xde3f01fc07e03f82 0xf78fc07f01f80fe0

def z1027 : W := mkw 0x3c43ffebd218042a 0x8f10fffaf486010a 0x3ffbfffffe000c00 0x0ffeffffff800300

def z1028 : W := mkw 0x3f43ffebd75a842a 0x8fd0fffaf5d6a10a 0x3ffbfffffe68dc0c 0x4ffeffffff9a3703

def z1029 : W := mkw 0x2303fa00075a8002 0x08c0fe8001d6a000 0x81fbfe0007f7c000 0xa07eff8001fdf000

def z1030 : W := mkw 0x3c43ffebd218042a 0x8f10fffaf486010a 0x3e2753fffe083c7e 0x4f89d4ffff820f1f

def z1031 : W := mkw 0x1c4005ebd0000428 0x8710017af400010a 0xffdcadfff8103c7f 0x3ff72b7ffe040f1f

def z1032 : W := mkw 0x82b000142de57bd5 0x60ac00050b795ef5 0xc004000007ffffff 0xf001000001ffffff

def z1033 : W := mkw 0x80900004282451c5 0x202400010a091471 0x3be8520cf86cc3cd 0x8efa14833e1b30f3

def z1034 : W := mkw 0x3c0135ebd0000000 0x0f004d7af4000000 0x3ffbbdfff8000000 0x0ffeef7ffe000000

def z1035 : W := mkw 0x3c013febd0000000 0x0f004ffaf4000000 0x3fe87ffff8000000 0x0ffa1ffffe000000

def z1036 : W := mkw 0x1002c15800802200 0x0400b05600200880 0xde7fc1fc07803f82 0xf79ff07f01e00fe0

def z1037 : W := mkw 0x3c43ffebd218042a 0x8f10fffaf486010a 0xbffffffffe103c7e 0x2fffffffff840f1f

def z1038 : W := mkw 0x1802c56940000000 0x0600b15a50000000 0x3ffbfffff8000000 0x0ffefffffe000000

def z1039 : W := mkw 0x3c03ffebd0000000 0x0f00fffaf4000000 0x3e0301fff8000000 0x0f80c07ffe000000

def z1040 : W := mkw 0x3d03ffebd21a8002 0x0f40fffaf486a000 0x3ffbfffff8130000 0x0ffefffffe04c000

def z1041 : W := mkw 0x0302ca0005428000 0x00c0b2800150a000 0x01c0de0001efc001 0x80703780007bf000

def z1042 : W := mkw 0x1002c14800000000 0x0400b05200000000 0x3e7bc1fcf8000000 0x0f9ef07f3e000000

def z1043 : W := mkw 0x80900004282451c5 0x202400010a091471 0x1820520cf868d38c 0x460814833e1a34e3

def z1044 : W := mkw 0x08200431608522d0 0x4208010c582148b4 0xfffcac73619733f3 0xffff2b1cd865ccfc

def z1045 : W := mkw 0x0302ca0005428000 0x00c0b2800150a000 0xc140ce0001f7c001 0xb0503380007df000

def z1046 : W := mkw 0x3c03ffebd0000000 0x0f00fffaf4000000 0x31fbfe7ff8000000 0x0c7eff9ffe000000

def z1047 : W := mkw 0x2303fa00075a8002 0x08c0fe8001d6a000 0xd3fbfe0007ffc383 0xf4feff8001fff0e0

def z1048 : W := mkw 0x3c23ffebd0010010 0x4f08fffaf4004004 0x3ffbfffff8130030 0x0ffefffffe04c00c

def z1049 : W := mkw 0x23013a00075a8002 0x08c04e8001d6a000 0xc1bb3e0007ffc001 0xf06ecf8001fff000

def z1050 : W := mkw 0xa393fa042f7ed1c7 0x28e4fe810bdfb471 0xba13ac0cff9313ce 0x2e84eb033fe4c4f3

def z1051 : W := mkw 0x2303fa00075a8002 0x08c0fe8001d6a000 0xe7fbfe0307ffc001 0xf9feff80c1fff000

def z1052 : W := mkw 0x3f03ffebd75a8002 0x0fc0fffaf5d6a000 0x3ffbfffffe000000 0x0ffeffffff800000

def z1053 : W := mkw 0x004000828218042a 0x80100020a086010a 0xee3f018386183c7f 0x7b8fc060e1860f1f

def z1054 : W := mkw 0x2303fa00075a8002 0x08c0fe8001d6a000 0xdbfbfe0c07ffc001 0xf6feff8301fff000

def z1055 : W := mkw 0x204130828218042a 0x88104c20a086010a 0xee3f218386103c7e 0x7b8fc860e1840f1f

def z1056 : W := mkw 0x3c43ffebd218042a 0x8f10fffaf486010a 0x7ffbfffff818107f 0x5ffefffffe06041f

def z1057 : W := mkw 0x1c0005ebd0000000 0x0700017af4000000 0x3e5881fff8000000 0x0f96207ffe000000

def z1058 : W := mkw 0x2303fa00075a8002 0x08c0fe8001d6a000 0x8173fe0007ffc000 0xe05cff8001fff000

def z1059 : W := mkw 0x3c03ff6952180002 0x0f00ffda54860000 0xd1fbfe7c7e180001 0x747eff9f1f860000

def z1060 : W := mkw 0x1c02cf6950000000 0x0700b3da54000000 0x1140ce7c79870000 0x8450339f1e61c000

def z1061 : W := mkw 0x2303fa00075a8002 0x08c0fe8001d6a000 0x01fbfe0001ffc001 0x807eff80007ff000

def z1062 : W := mkw 0x0302ca0005428000 0x00c0b2800150a000 0xe7dcee0301f7e073 0xb9f73b80c07df81c

def z1063 : W := mkw 0x3c43ffebd218042a 0x8f10fffaf486010a 0x31c0fe7ff818007d 0x0c703f9ffe06001f

def z1064 : W := mkw 0x1000014800000000 0x0400005200000000 0x3fe853fcf8000000 0x0ffa14ff3e000000

def z1065 : W := mkw 0x3c03ffebd0000000 0x0f00fffaf4000000 0x3ebbbdfff8000000 0x0faeef7ffe000000

def z1066 : W := mkw 0x80b0001428a573d5 0x602c00050a295cf5 0xc0040000019733ff 0xb00100000065ccff

def z1067 : W := mkw 0x1c02cf6950000000 0x0700b3da54000000 0x3740ce7f78000000 0x0dd0339fde000000

def z1068 : W := mkw 0x3e03ffebd5400000 0x0f80fffaf5500000 0x3ffbfffff9e00000 0x8ffefffffe780000

def z1069 : W := mkw 0x0302ca0005428000 0x00c0b2800150a000 0x4140ce0001efc001 0xd0503380007bf000

def z1070 : W := mkw 0x9292c15c0de07b05 0x24a4b05703781ec1 0xfeffd3fc9fe8ffcf 0xffbff4ff27fa3ff3

def z1071 : W := mkw 0x08200431608522d0 0x4208010c582148b4 0xf7fcbc73619f23f3 0xfdff2f1cd867c8fc

def z1072 : W := mkw 0x1302cb4805428000 0x04c0b2d20150a000 0x1140ce7c01e7c000 0x8450339f0079f000

def z1073 : W := mkw 0x3c43ffebd218042a 0x8f10fffaf486010a 0x3ffffffff8183c7f 0x0ffffffffe060f1f

def z1074 : W := mkw 0x08200431608522d0 0x4208010c582148b4 0xffdcac73e19733ff 0xbff72b1cf865ccff

def z1075 : W := mkw 0x1c4005ebd0000428 0x8710017af400010a 0x3e0001fff8001c0c 0x0f80007ffe000703

def z1076 : W := mkw 0x1c0005ebd0000000 0x0700017af4000000 0x3e0401fff8003c02 0x0f81007ffe000f00

def z1077 : W := mkw 0x08200431608522d0 0x4208010c582148b4 0xf7fcec7361f723f3 0xfdff3b1cd87dc8fc

def z1078 : W := mkw 0x3f43ffebd75a842a 0x8fd0fffaf5d6a10a 0xfffffffffe78fc7f 0x7fffffffff9e3f1f

def z1079 : W := mkw 0x3c43ffebd218042a 0x8f10fffaf486010a 0xfffffffffe102c73 0x3fffffffff840b1c

def z1080 : W := mkw 0x3c03ffebd0000000 0x0f00fffaf4000000 0xfffbfffff8100001 0x3ffefffffe040000

def z1081 : W := mkw 0x08200431608522d0 0x4208010c582148b4 0xb5d4ac73619723f1 0xad752b1cd865c8fc

def z1082 : W := mkw 0x3c013febd0000000 0x0f004ffaf4000000 0x3e0013fff8000000 0x0f8004fffe000000

def z1083 : W := mkw 0x1202c15805c02a00 0x0480b05601700a80 0xde7f81f007803f82 0xf79fe07c01e00fe0

def z1084 : W := mkw 0x0302ca0005428000 0x00c0b2800150a000 0xcf7fcf8007e7fc02 0xf3dff3e001f9ff00

def z1085 : W := mkw 0x3f03ffebd75a8002 0x0fc0fffaf5d6a000 0x3ffbffffffefc000 0xcffefffffffbf000

def z1086 : W := mkw 0x80900004282451c5 0x202400010a091471 0x3be8520cf86cd38c 0xcefa14833e1b34e3

def z1087 : W := mkw 0x2303fa00075a8002 0x08c0fe8001d6a000 0x0140ee0001f7c000 0x80503b80007df000

def z1088 : W := mkw 0x204130828218042a 0x88104c20a086010a 0xfeffb1f386183c7f 0x7fbfec7ce1860f1f

def z1089 : W := mkw 0x1382cb5c05e2bb01 0x04e0b2d70178aec0 0xde7fcdfc07e33f82 0xf79ff37f01f8cfe0

def z1090 : W := mkw 0x3c4135ebd218042a 0x8f104d7af486010a 0xffff73fffe183c7f 0x7fffdcffff860f1f

def z1091 : W := mkw 0x1282c15c05e03b01 0x04a0b05701780ec0 0xdfffedfc07e03f82 0xf7fffb7f01f80fe0

def z1092 : W := mkw 0x2303fa00075a8002 0x08c0fe8001d6a000 0xc193be0007ffc001 0xf064ef8001fff000

def z1093 : W := mkw 0x2303fa00075a8002 0x08c0fe8001d6a000 0xe1fbfe00ffffc001 0xf87eff803ffff000

def z1094 : W := mkw 0x1c0005ebd0000000 0x0700017af4000000 0x3e3b01fff8000000 0x0f8ec07ffe000000

def z1095 : W := mkw 0x0000000000000000 0x0000000000000000 0xc1d8ee0001f7c001 0xb0763b80007df000

def z1096 : W := mkw 0x2343fa82875a842a 0x88d0fea0a1d6a10a 0xe9fbff8387ffdc7d 0xfa7effe0e1fff71f

def z1097 : W := mkw 0x1080015c00a03b01 0x0420005700280ec0 0x9e1701fc06003f82 0x2785c07f01800fe0

def z1098 : W := mkw 0x204130928298262a 0x88104c24a0a6098a 0xf6dcb073819823ff 0xbdb72c1ce06608ff

def z1099 : W := mkw 0x0302ca0005428000 0x00c0b2800150a000 0x01c0ee0001f7c001 0x80703b80007df000

def z1100 : W := mkw 0x3f03ffebd5428000 0x0fc0fffaf550a000 0x3ffbfffff9830000 0x0ffefffffe60c000

def z1101 : W := mkw 0x2303fa00075a8002 0x08c0fe8001d6a000 0xc9fbff8007ffdc01 0xf27effe001fff700

def z1102 : W := mkw 0x80900004282451c5 0x202400010a091471 0x73c8520cf86cc3cf 0x9cf214833e1b30f3

def z1103 : W := mkw 0x2303fa00075a8002 0x08c0fe8001d6a000 0xe1fbfe0307ffc071 0xf87eff80c1fff01c

def z1104 : W := mkw 0x88300431688562d4 0x620c010c5a2158b5 0xf7dcac73f99723ff 0xbdf72b1cfe65c8ff

def z1105 : W := mkw 0x3d43ffebd21a842a 0x8f50fffaf486a10a 0x3ffbfffff81fc07d 0x0ffefffffe07f01f

def z1106 : W := mkw 0x0302ca0005428000 0x00c0b2800150a000 0x01e8de0001e7c000 0x807a37800079f000

def z1107 : W := mkw 0x1c02cf6950000000 0x0700b3da54000000 0x31c0de7cf8000000 0x0c70379f3e000000

def z1108 : W := mkw 0x1282c15c05e03b01 0x04a0b05701780ec0 0x5e6f41fc06603f82 0xd79bd07f01980fe0

def z1109 : W := mkw 0x98b0057d68a57bd5 0x662c015f5a295ef5 0x3e0401fff8003ffe 0x0f81007ffe000fff

def z1110 : W := mkw 0x2303fa82875a8002 0x08c0fea0a1d6a000 0xc9fbff8087ffc001 0xf27effe021fff000

def z1111 : W := mkw 0x3c03ffebd0000000 0x0f00fffaf4000000 0x3ffbfffff864c000 0x8ffefffffe193000

def z1112 : W := mkw 0x2303fa00075a8002 0x08c0fe8001d6a000 0xc17bee0007f7c000 0xf05efb8001fdf000

def z1113 : W := mkw 0x3f03ff69575a8002 0x0fc0ffda55d6a000 0xfbfbfe7cffffc001 0xfefeff9f3ffff000

def z1114 : W := mkw 0x204130828218042a 0x88104c20a086010a 0xe8a7318386183c7f 0x7a29cc60e1860f1f

def z1115 : W := mkw 0x1c02cf6950000000 0x0700b3da54000000 0x3ff8fe7ff8000000 0x0ffe3f9ffe000000

def z1116 : W := mkw 0x1e02c5ebd5400000 0x0780b17af5500000 0xfe7bc1ffffe00000 0xff9ef07ffff80000

def z1117 : W := mkw 0x2343fa82875a842a 0x88d0fea0a1d6a10a 0xe7fffe0387ffe07f 0xf9ffff80e1fff81f

def z1118 : W := mkw 0x1282c15c05e03b01 0x04a0b05701780ec0 0x9e57c1fc07e03f82 0xa795f07f01f80fe0

def z1119 : W := mkw 0x1082c14c00201101 0x0420b05300080440 0xde7fc1fc06603f82 0xf79ff07f01980fe0

def z1120 : W := mkw 0x1282c15c05e03b01 0x04a0b05701780ec0 0x9e7fc1fc07803f82 0x279ff07f01e00fe0

def z1121 : W := mkw 0x204130828218042a 0x88104c20a086010a 0xee3f118386083c7e 0x7b8fc460e1820f1f

def z1122 : W := mkw 0x1c00056950000000 0x0700015a54000000 0x3a00007cf8000000 0x0e80001f3e000000

def z1123 : W := mkw 0x3303fb48075a8002 0x0cc0fed201d6a000 0xdffffffc07fffc03 0xf7ffffff01ffff00

def z1124 : W := mkw 0x0302ca0005428000 0x00c0b2800150a000 0x3be8de0cf9e7c000 0x8efa37833e79f000

def z1125 : W := mkw 0x004000000218042a 0x801000000086010a 0xeebf218306183c7f 0x7bafc860c1860f1f

def z1126 : W := mkw 0x3c03ffebd2180002 0x0f00fffaf4860000 0x3ffbfffffe080000 0x4ffeffffff820000

def z1127 : W := mkw 0x3703fbca95428000 0x0dc0fef2a550a000 0x0963df8c99e7c000 0x8258f7e32679f000

def z1128 : W := mkw 0x1002c14800000000 0x0400b05200000000 0x3be8d27cf8000000 0x0efa349f3e000000

def z1129 : W := mkw 0x1c00056950000000 0x0700015a54000000 0x3600007f78000000 0x0d80001fde000000

def z1130 : W := mkw 0x1c02cf6950000000 0x0700b3da54000000 0x11d8ee7c78000000 0x04763b9f1e000000

def z1131 : W := mkw 0x23413a82875a842a 0x88d04ea0a1d6a10a 0xefbf3f8387fffc7f 0xfbefcfe0e1ffff1f

def z1132 : W := mkw 0x1282c15c05e03b01 0x04a0b05701780ec0 0xc47fc1f007e03f82 0xf11ff07c01f80fe0

def z1133 : W := mkw 0x0080001400a03301 0x0020000500280cc0 0xde7fc1fc07e03f82 0xf79ff07f01f80fe0

def z1134 : W := mkw 0x80900004282451c5 0x202400010a091471 0x7ff8d27cf86cd3cf 0xdffe349f3e1b34f3

def z1135 : W := mkw 0x204130828218042a 0x88104c20a086010a 0xce3f218306183c7f 0x738fc860c1860f1f

def z1136 : W := mkw 0x3d03ffebd0028000 0x0f40fffaf400a000 0x3ffbfffff807c000 0x0ffefffffe01f000

def z1137 : W := mkw 0x3c03ffebd0000000 0x0f00fffaf4000000 0x3ffbfffff8170001 0x0ffefffffe05c000

def z1138 : W := mkw 0x3c413febd218042a 0x8f104ffaf486010a 0xffbf3ffffe183c7f 0x7fefcfffff860f1f

def z1139 : W := mkw 0x0302ca0005428000 0x00c0b2800150a000 0x4168ce0001e7c000 0xd05a33800079f000

def z1140 : W := mkw 0x1282c15c05e03b01 0x04a0b05701780ec0 0x1e0701fc06003f82 0x0781c07f01800fe0

def z1141 : W := mkw 0x8090001428a47bc5 0x202400050a291ef1 0x40040000006cffcf 0xd0010000001b3ff3

def z1142 : W := mkw 0x2343fa82875a842a 0x88d0fea0a1d6a10a 0xffffff8ffffffc7f 0xffffffe3ffffff1f

def z1143 : W := mkw 0x3c43ffebd0000428 0x8f10fffaf400010a 0x3ffbfffff8001c0c 0x0ffefffffe000703

def z1144 : W := mkw 0x08200431608522d0 0x4208010c582148b4 0xb794ac73619723f3 0x2de52b1cd865c8fc

def z1145 : W := mkw 0x3c03ffebd0000000 0x0f00fffaf4000000 0x1413adff78000000 0x0504eb7fde000000

def z1146 : W := mkw 0x08200431608522d0 0x4208010c582148b4 0xf7dcac73619f33ff 0xfdf72b1cd867ccff

def z1147 : W := mkw 0x3c413febd218042a 0x8f104ffaf486010a 0x3f843ffff8183c7f 0x0fe10ffffe060f1f

def z1148 : W := mkw 0x88b0043568a573d5 0x622c010d5a295cf5 0xfebc307ff81833ff 0x7faf0c1ffe060cff

def z1149 : W := mkw 0x204130828218042a 0x88104c20a086010a 0xee17218386183c7f 0x7b85c860e1860f1f

def z1150 : W := mkw 0x80900004282451c5 0x202400010a091471 0x39e0520cf86cd3cd 0xce7814833e1b34f3

def z1151 : W := mkw 0x9ab2c57d6de57bd5 0x66acb15f5b795ef5 0x1140ce7c79e7c380 0x8450339f1e79f0e0

def z1152 : W := mkw 0x1d02cf6950028000 0x0740b3da5400a000 0x1140ce7c7807c000 0x0450339f1e01f000

def z1153 : W := mkw 0x0202c01005c02200 0x0080b00401700880 0xde7fc1f007e03f82 0xf79ff07c01f80fe0

def z1154 : W := mkw 0x80900004282451c5 0x202400010a091471 0xfffc520cf86cf3cf 0xffff14833e1b3cf3

def z1155 : W := mkw 0x1282c15c05e03b01 0x04a0b05701780ec0 0x9c77c1fc07e03f80 0xe71df07f01f80fe0

def z1156 : W := mkw 0x3c03ffebd0000000 0x0f00fffaf4000000 0x7ffbfffff8001002 0x5ffefffffe000400

def z1157 : W := mkw 0x3c43ffebd218042a 0x8f10fffaf486010a 0xfffbfffffe18007d 0x7ffeffffff86001f

def z1158 : W := mkw 0x2343fa82875a842a 0x88d0fea0a1d6a10a 0xc9ffff8087fffc7f 0xf27fffe021ffff1f

def z1159 : W := mkw 0x0800042140000000 0x0200010850000000 0xfff8fe7ff9ffc001 0xfffe3f9ffe7ff000

def z1160 : W := mkw 0x1202c14805400000 0x0480b05201500000 0xfffbd3fcffecc001 0xfffef4ff3ffb3000

def z1161 : W := mkw 0x3e03ffebd5400000 0x0f80fffaf5500000 0xffffffffffe03c02 0xfffffffffff80f00

def z1162 : W := mkw 0x0800042140000000 0x0200010850000000 0x3be8de7cf8000000 0x0efa379f3e000000

def z1163 : W := mkw 0x2303fa00075a8002 0x08c0fe8001d6a000 0x0143ce0007e7c000 0x8050f38001f9f000

def z1164 : W := mkw 0x3c03ffebd2180002 0x0f00fffaf4860000 0xfffbfffffe7cc001 0xfffeffffff9f3000

def z1165 : W := mkw 0x2303fa00075a8002 0x08c0fe8001d6a000 0x01e3fe0007ffc001 0xc078ff8001fff000

def z1166 : W := mkw 0x2303fa00075a8002 0x08c0fe8001d6a000 0xc1fffe0007ffe073 0xf07fff8001fff81c

def z1167 : W := mkw 0x0820043140812210 0x4208010c50204884 0xc414ac73019323b2 0xb1052b1cc064c8ec

def z1168 : W := mkw 0x3f43ffebd75a842a 0x8fd0fffaf5d6a10a 0xffffffffffffec31 0xfffffffffffffb0c

def z1169 : W := mkw 0x829000142de47bc5 0x20a400050b791ef1 0xc004000007e03fce 0xf001000001f80ff3

def z1170 : W := mkw 0x21013a00021a8002 0x08404e800086a000 0xc1f8fe0001ffc001 0xf07e3f80007ff000

def z1171 : W := mkw 0x3e03ffebd5400800 0x0f80fffaf5500200 0x3ffbfffffe000c00 0x0ffeffffff800300

def z1172 : W := mkw 0x3c03ffebd0000000 0x0f00fffaf4000000 0x3ffffffff8003c02 0x0ffffffffe000f00

def z1173 : W := mkw 0x1282c15c05e03b01 0x04a0b05701780ec0 0x1e67c1fc07e03f82 0xc799f07f01f80fe0

def z1174 : W := mkw 0x3c03ff6950000000 0x0f00ffda54000000 0x37fbfe7f78000000 0x0dfeff9fde000000

def z1175 : W := mkw 0x3c43ffebd218042a 0x8f10fffaf486010a 0xbffffffffe182c7d 0x2fffffffff860b1f

def z1176 : W := mkw 0x1c02cfebd0000000 0x0700b3faf4000000 0x1940cffcf8000000 0x065033ff3e000000

def z1177 : W := mkw 0x1c0005ebd0000000 0x0700017af4000000 0xffd8adfff9970001 0xbff62b7ffe65c000

def z1178 : W := mkw 0x1c02cf6950000000 0x0700b3da54000000 0x1550ee7f78000000 0x05543b9fde000000

def z1179 : W := mkw 0x3c03ffebd2180002 0x0f00fffaf4860000 0xfffffffffe182073 0x7fffffffff86081c

def z1180 : W := mkw 0x3f03ffebd75a8002 0x0fc0fffaf5d6a000 0xbffbfffffffbc000 0x6ffefffffffef000

def z1181 : W := mkw 0x80b0001428a573d5 0x602c00050a295cf5 0xc004000001f7e3f3 0xb0010000007df8fc

def z1182 : W := mkw 0xa3b3fa142ffff3d7 0x68ecfe850bfffcf5 0xc1fffe0007fff3ff 0xf07fff8001fffcff

def z1183 : W := mkw 0x1c02c5ebd0000000 0x0700b17af4000000 0x3e1381fff8000000 0x0f84e07ffe000000

def z1184 : W := mkw 0x0302ca0005428000 0x00c0b2800150a000 0x0163ce0007e7c000 0xc058f38001f9f000

def z1185 : W := mkw 0x80b0001428a573d5 0x602c00050a295cf5 0xeebc300381fff3ff 0xfbaf0c00e07ffcff

def z1186 : W := mkw 0x3d03ffebd21a8002 0x0f40fffaf486a000 0xfffbfffffe1fc001 0x7ffeffffff87f000

def z1187 : W := mkw 0x08200431608522d0 0x4208010c582148b4 0xd5dcac73619723b1 0xb5772b1cd865c8ec

def z1188 : W := mkw 0x204130828218042a 0x88104c20a086010a 0xee9f218386103c7f 0x3ba7c860e1840f1f

def z1189 : W := mkw 0x1282cb5c05e03b01 0x04a0b2d701780ec0 0xdf7fcffc07e03f82 0xf7dff3ff01f80fe0

def z1190 : W := mkw 0x3c43ffebd218042a 0x8f10fffaf486010a 0xfffffffffe7cfc7f 0xffffffffff9f3f1f

def z1191 : W := mkw 0x3c43f5ebd218042a 0x8f10fd7af486010a 0xfefff1fffe183c7f 0x7fbffc7fff860f1f

def z1192 : W := mkw 0x3c03ffebd0000000 0x0f00fffaf4000000 0x3ebb73fff8000000 0x0faedcfffe000000

def z1193 : W := mkw 0x2303fa82875a8002 0x08c0fea0a1d6a000 0xfffbff8fffffc001 0xfffeffe3fffff000

def z1194 : W := mkw 0x80900004282451c5 0x202400010a091471 0xfbf8d20cf9ecd3cf 0xfefe34833e7b34f3

def z1195 : W := mkw 0x3c013febd0000000 0x0f004ffaf4000000 0x3fd8bffff8000000 0x0ff62ffffe000000

def z1196 : W := mkw 0x1c02cf6950000000 0x0700b3da54000000 0x11e8de7c78000000 0x047a379f1e000000

def z1197 : W := mkw 0x3f03ffebd75a8002 0x0fc0fffaf5d6a000 0x1963dffcffefc000 0xc658f7ff3ffbf000

def z1198 : W := mkw 0x3c43ffebd0000428 0x8f10fffaf400010a 0xfffffffff8103c7f 0x3ffffffffe040f1f

def z1199 : W := mkw 0x1c00056950000000 0x0700015a54000000 0x37d8ac7f78000000 0x0df62b1fde000000

def z1200 : W := mkw 0x2303fa00075a8002 0x08c0fe8001d6a000 0xcffbff8007ffc001 0xf3feffe001fff000

def z1201 : W := mkw 0x2303fa00075a8002 0x08c0fe8001d6a000 0x8013ac0007f7c000 0xa004eb0001fdf000

def z1202 : W := mkw 0x0302ca00075a8002 0x00c0b28001d6a000 0x8140ce0007f7c000 0xa050338001fdf000

def z1203 : W := mkw 0x08200431608522d0 0x4208010c582148b4 0xf7dcbc73e19f23ff 0xbdf72f1cf867c8ff

def z1204 : W := mkw 0x80900004282451c5 0x202400010a091471 0x69a0520cf86cd3cf 0xda6814833e1b34f3

def z1205 : W := mkw 0x1c0005ebd0000000 0x0700017af4000000 0x3e0401fff8002072 0x0f81007ffe00081c

def z1206 : W := mkw 0x3043f1ca8218042a 0x8c10fc72a086010a 0xfffff3fffe183c7f 0x7ffffcffff860f1f

def z1207 : W := mkw 0x1282c15c05e03b01 0x04a0b05701780ec0 0xde7fc1fc07ecff83 0xf79ff07f01fb3fe0

def z1208 : W := mkw 0x1282c15c05e03b01 0x04a0b05701780ec0 0x1043c1fc07e00f80 0x8410f07f01f803e0

def z1209 : W := mkw 0x204130828218042a 0x88104c20a086010a 0xeebf3183879f3c7f 0xfbafcc60e1e7cf1f

def z1210 : W := mkw 0x3c03ffebd0000000 0x0f00fffaf4000000 0x3ffbfffff868c000 0x4ffefffffe1a3000

def z1211 : W := mkw 0x2303fa00075a8002 0x08c0fe8001d6a000 0xc033fe0007ffc001 0xf00cff8001fff000

def z1212 : W := mkw 0x204130828218042a 0x88104c20a086010a 0xeeffb18387983c7f 0xfbbfec60e1e60f1f

def z1213 : W := mkw 0x3c03ffebd0000000 0x0f00fffaf4000000 0x19fbfffcf8000000 0x067effff3e000000

def z1214 : W := mkw 0x88f004b7e8a577fd 0xe23c012dfa295dff 0x3e0401fff8003ffe 0x0f81007ffe000fff

def z1215 : W := mkw 0x0280001405e03b01 0x00a0000501780ec0 0xde7f81f007e03f82 0xf79fe07c01f80fe0

def z1216 : W := mkw 0x0302ca00075a8002 0x00c0b28001d6a000 0x0140ce0007efc000 0xc050338001fbf000

def z1217 : W := mkw 0x08200431608522d0 0x4208010c582148b4 0xf7dcbe73f99723f3 0xbdf72f9cfe65c8fc

def z1218 : W := mkw 0x9292c15c0de07b05 0x24a4b05703781ec1 0xde7fc1fc9fe03f8e 0xf79ff07f27f80fe3

def z1219 : W := mkw 0x23413a82875a842a 0x88d04ea0a1d6a10a 0xe1843e0387fffc7f 0xf8610f80e1ffff1f

def z1220 : W := mkw 0x80900004282451c5 0x202400010a091471 0x3ba0520cf86cd3cf 0x4ee814833e1b34f3

def z1221 : W := mkw 0x08200431608522d0 0x4208010c582148b4 0x73c8ac73619703f3 0x9cf22b1cd865c0fc

def z1222 : W := mkw 0x3e03ffebd7580002 0x0f80fffaf5d60000 0xfffbfffffff80001 0xfffefffffffe0000

def z1223 : W := mkw 0x1c02cf6950000000 0x0700b3da54000000 0x1758ce7c78000000 0x05d6339f1e000000

def z1224 : W := mkw 0x3303fb48075a8802 0x0cc0fed201d6a200 0xc1fbff8007ffcc01 0xf07effe001fff300

def z1225 : W := mkw 0x0300000005428000 0x00c000000150a000 0x01408c0001e7c000 0x805023000079f000

def z1226 : W := mkw 0x1c4005ebd0000428 0x8710017af400010a 0x7fec53fff8083c7f 0x5ffb14fffe020f1f

def z1227 : W := mkw 0x3303fbca875a8002 0x0cc0fef2a1d6a000 0xfffbffff87ffc001 0xfffeffffe1fff000

def z1228 : W := mkw 0x1c02cf6950000000 0x0700b3da54000000 0xf7dcee7f78102073 0x3df73b9fde04081c

def z1229 : W := mkw 0x21413a82821a842a 0x88504ea0a086a10a 0xefff7f83867ffc7f 0xfbffdfe0e19fff1f

def z1230 : W := mkw 0x0302ca0005428000 0x00c0b2800150a000 0x01d8ee0001e7c000 0x80763b800079f000

def z1231 : W := mkw 0x3c43ffebd218042a 0x8f10fffaf486010a 0xfebfbdfffe183c7f 0x7fafef7fff860f1f

def z1232 : W := mkw 0x1c02cf6950000000 0x0700b3da54000000 0x1963cffc78000000 0x0658f3ff1e000000

def z1233 : W := mkw 0x3c03ffebd0000000 0x0f00fffaf4000000 0x3ffbfffff808100c 0x4ffefffffe020403

def z1234 : W := mkw 0x1282c14c05601901 0x04a0b05301580640 0x5e7bc1fc06601f82 0xd79ef07f019807e0

def z1235 : W := mkw 0x2343fa82875a842a 0x88d0fea0a1d6a10a 0x8557ef8307f7ec30 0xa155fbe0c1fdfb0c

def z1236 : W := mkw 0x1202c15805c02a00 0x0480b05601700a80 0xde7fc1fc07802f82 0xb79ff07f01e00be0

def z1237 : W := mkw 0x3c03ffebd0000000 0x0f00fffaf4000000 0xfffbfffffe000000 0x7ffeffffff800000

def z1238 : W := mkw 0x0800042140000000 0x0200010850000000 0x3fd8ac7ff8000000 0x0ff62b1ffe000000

def z1239 : W := mkw 0x2303fa00075a8002 0x08c0fe8001d6a000 0xfbfbfe0cffffd04f 0xfefeff833ffff413

def z1240 : W := mkw 0x1282c15c05e03b01 0x04a0b05701780ec0 0xfefff1ff87f83fff 0xffbffc7fe1fe0fff

def z1241 : W := mkw 0x1c02cfebd0000000 0x0700b3faf4000000 0x3fe8dffff8000000 0x0ffa37fffe000000

def z1242 : W := mkw 0x08200431608522d0 0x4208010c582148b4 0x9414ac73619323b0 0x25052b1cd864c8ec

def z1243 : W := mkw 0x2343fa00075a842a 0x88d0fe8001d6a10a 0xcfffff8007fffc7f 0xf3ffffe001ffff1f

def z1244 : W := mkw 0x2343fa82875a842a 0x88d0fea0a1d6a10a 0xe7ffff8307ffec73 0xf9ffffe0c1fffb1c

def z1245 : W := mkw 0x2303fa0005428000 0x08c0fe800150a000 0xc1fbfe0007e7c000 0xf07eff8001f9f000

def z1246 : W := mkw 0x3c03ffebd0000000 0x0f00fffaf4000000 0x3fc0fffff8000000 0x0ff03ffffe000000

def z1247 : W := mkw 0x829000142de47bc5 0x20a400050b791ef1 0xeebf118087ecffcf 0xfbafc46021fb3ff3

def z1248 : W := mkw 0x3d013febd21a8002 0x0f404ffaf486a000 0x3f803ffff81fc001 0x0fe00ffffe07f000

def z1249 : W := mkw 0x1c0005ebd0000000 0x0700017af4000000 0x7ea811fff808104f 0x5faa047ffe020413

def z1250 : W := mkw 0x3f03ffebd75a8002 0x0fc0fffaf5d6a000 0xfffbffffff9b0001 0x7ffeffffffe6c000

def z1251 : W := mkw 0x1c4005ebd218042a 0x8710017af486010a 0xfe0401fffe183c7f 0x7f81007fff860f1f

def z1252 : W := mkw 0x3c03ffebd0000000 0x0f00fffaf4000000 0x3fa37ffff8000000 0x0fe8dffffe000000

def z1253 : W := mkw 0x1282c15c05e03b01 0x04a0b05701780ec0 0xfe7fc1ff07e03ff2 0xff9ff07fc1f80ffc

def z1254 : W := mkw 0x3703fbca975a8002 0x0dc0fef2a5d6a000 0xdffbfffc9fffc001 0xf7feffff27fff000

def z1255 : W := mkw 0x3c03ffebd0000000 0x0f00fffaf4000000 0xbffffffffe002c00 0x2fffffffff800b00

def z1256 : W := mkw 0x1282c15c05e03b01 0x04a0b05701780ec0 0xffffd3fcffe83fcf 0xfffff4ff3ffa0ff3

def z1257 : W := mkw 0x1282c15c05e03b01 0x04a0b05701780ec0 0xfeffe1ff07e03f82 0xffbff87fc1f80fe0

def z1258 : W := mkw 0x08200431608522d0 0x4208010c582148b4 0xb7dcac73619323f2 0x2df72b1cd864c8fc

def z1259 : W := mkw 0x1282c15c05e03b01 0x04a0b05701780ec0 0x9e37c1fc07e03f82 0x678df07f01f80fe0

def z1260 : W := mkw 0x3f03ffebd75a8002 0x0fc0fffaf5d6a000 0x31c0fe7ff9ffc001 0x8c703f9ffe7ff000

def z1261 : W := mkw 0x1282c15c05e03b01 0x04a0b05701780ec0 0xdf7fcdfc07e73f82 0xf7dff37f01f9cfe0

def z1262 : W := mkw 0x2343fa00075a842a 0x88d0fe8001d6a10a 0xc1fbfe0007ffdc0d 0xf07eff8001fff703

def z1263 : W := mkw 0x1282c15c05e03b01 0x04a0b05701780ec0 0xcc37c1fc07e03f82 0xf30df07f01f80fe0

def z1264 : W := mkw 0x80900004282451c5 0x202400010a091471 0xfbec520cfe6cffcf 0xfefb14833f9b3ff3

def z1265 : W := mkw 0x1282c15c05e03b01 0x04a0b05701780ec0 0x1e7bc1fc07e01f80 0xc79ef07f01f807e0

def z1266 : W := mkw 0x2303fa0005428000 0x08c0fe800150a000 0x0163de0001e7c000 0x8058f7800079f000

def z1267 : W := mkw 0x204130828218042a 0x88104c20a086010a 0xefbf3383fe183c7f 0x7befcce0ff860f1f

def z1268 : W := mkw 0x1282c15c05e03b01 0x04a0b05701780ec0 0xce3f81f007e03f82 0xf38fe07c01f80fe0

def z1269 : W := mkw 0x3d03ffebd21a8002 0x0f40fffaf486a000 0x7ffbfffff87fc001 0xdffefffffe1ff000

def z1270 : W := mkw 0x1c0005ebd0000000 0x0700017af4000000 0x140001ff78000000 0x0500007fde000000

def z1271 : W := mkw 0x1f02cf6955428000 0x07c0b3da5550a000 0x1140ce7c79830000 0x0450339f1e60c000

def z1272 : W := mkw 0x3343fbca875a842a 0x8cd0fef2a1d6a10a 0xffffffff87fffc7f 0xffffffffe1ffff1f

def z1273 : W := mkw 0x204130828218042a 0x88104c20a086010a 0xeebfbd83879b3c7f 0x7bafef60e1e6cf1f

def z1274 : W := mkw 0x1c0005ebd0000000 0x0700017af4000000 0x3e2053fff8000000 0x0f8814fffe000000

def z1275 : W := mkw 0x204130828218042a 0x88104c20a086010a 0xfeff718f86183c7f 0x7fbfdc63e1860f1f

def z1276 : W := mkw 0x3c03ffebd0000000 0x0f00fffaf4000000 0x7ffbfffff8080001 0x5ffefffffe020000

def z1277 : W := mkw 0x08200431608522d0 0x4208010c582148b4 0xc5dcac73019723f3 0xb1772b1cc065c8fc

def z1278 : W := mkw 0x1002c14800000000 0x0400b05200000000 0x1140c27c78000000 0x0450309f1e000000

def z1279 : W := mkw 0x33c3fbce877a9d2b 0x8cf0fef3a1dea74a 0x0823538c8668dc0c 0x4208d4e3219a3703

def z1280 : W := mkw 0x0302ca0005428000 0x00c0b2800150a000 0xc158ce0001e7c000 0xb05633800079f000

def z1281 : W := mkw 0x80900004282451c5 0x202400010a091471 0x7bf8fe0cf86cd3cf 0xdefe3f833e1b34f3

def z1282 : W := mkw 0x21413082821a842a 0x88504c20a086a10a 0xeebf3183861ffc7f 0x7bafcc60e187ff1f

def z1283 : W := mkw 0x2303fa0005428000 0x08c0fe800150a000 0x41fbfe0001efc001 0xd07eff80007bf000

def z1284 : W := mkw 0x3d03ffebd21a8002 0x0f40fffaf486a000 0x3ffbfffff808c000 0x0ffefffffe023000

def z1285 : W := mkw 0x80900004282451c5 0x202400010a091471 0x7a20520cf86cd3cf 0xde8814833e1b34f3

def z1286 : W := mkw 0x3c03ffebd0000000 0x0f00fffaf4000000 0xfffffffff818307f 0x7ffffffffe060c1f

def z1287 : W := mkw 0x1080015c00a03b01 0x0420005700280ec0 0xde7f41fc06603f82 0xf79fd07f01980fe0

def z1288 : W := mkw 0x1c02cf6950000000 0x0700b3da54000000 0x31c0ee7f78000000 0x0c703b9fde000000

def z1289 : W := mkw 0x3c03ffebd0000000 0x0f00fffaf4000000 0xbffbfffff9930000 0x2ffefffffe64c000

def z1290 : W := mkw 0x3f03ffebd75a8002 0x0fc0fffaf5d6a000 0x7ffbfffffe6cc001 0xdffeffffff9b3000

def z1291 : W := mkw 0x2343fa82875a842a 0x88d0fea0a1d6a10a 0xeffbff8387ffc07d 0xfbfeffe0e1fff01f

def z1292 : W := mkw 0x3c03ffebd2180002 0x0f00fffaf4860000 0xfffbfffffe18104f 0x7ffeffffff860413

def z1293 : W := mkw 0x03000a00075a8002 0x00c0028001d6a000 0xc1000e0007ffc001 0xf040038001fff000

def z1294 : W := mkw 0x3c03ff6950000000 0x0f00ffda54000000 0x11c0fe7c78000000 0x04703f9f1e000000

def z1295 : W := mkw 0x3d03ff69521a8002 0x0f40ffda5486a000 0x11c0fe7c781fc001 0x04703f9f1e07f000

def z1296 : W := mkw 0x2303fa00075a8002 0x08c0fe8001d6a000 0xc1d8fe0001ffc001 0xb0763f80007ff000

def z1297 : W := mkw 0x3c43ffebd218042a 0x8f10fffaf486010a 0x7ffbfffffe081c4f 0x5ffeffffff820713

def z1298 : W := mkw 0x2343fa82875a842a 0x88d0fea0a1d6a10a 0xcfffff8307fffc33 0xf3ffffe0c1ffff0c

def z1299 : W := mkw 0x03400000075a842a 0x80d0000001d6a10a 0xe7dcac0307fffc7f 0xf9f72b00c1ffff1f

def z1300 : W := mkw 0x80900004282451c5 0x202400010a091471 0x7ffb538cf86cd3cf 0xdffed4e33e1b34f3

def z1301 : W := mkw 0x0000000000000000 0x0000000000000000 0x0140ce0001e7c000 0x805033800079f000

def z1302 : W := mkw 0x3f03ffebd75a8002 0x0fc0fffaf5d6a000 0xfffbfffffff30000 0xfffefffffffcc000

def z1303 : W := mkw 0x08200431608522d0 0x4208010c582148b4 0xffffbdf3e79f3fff 0xffffef7cf9e7cfff

def z1304 : W := mkw 0x08200431608522d0 0x4208010c582148b4 0xffdcac7ff99723f3 0xbff72b1ffe65c8fc

def z1305 : W := mkw 0x1c02cf6950000000 0x0700b3da54000000 0x1140ce7c7864c000 0x8450339f1e193000

def z1306 : W := mkw 0x3c03ffebd0000000 0x0f00fffaf4000000 0x3bebdffcf8000000 0x0efaf7ff3e000000

def z1307 : W := mkw 0x1c4005ebd0000428 0x8710017af400010a 0x3e0001fff800007c 0x0f80007ffe00001f

def z1308 : W := mkw 0x0302ca0005428000 0x00c0b2800150a000 0xc1f8fe0001ffc001 0xf07e3f80007ff000

def z1309 : W := mkw 0x204130828218042a 0x88104c20a086010a 0x2ebf318386083c7e 0x4bafcc60e1820f1f

def z1310 : W := mkw 0x3e03ffebd5400000 0x0f80fffaf5500000 0xbffbffffff800000 0x2ffeffffffe00000

def z1311 : W := mkw 0x1c02cfebd0000000 0x0700b3faf4000000 0x1540cfff78000000 0x055033ffde000000

def z1312 : W := mkw 0x21413a82821a842a 0x88504ea0a086a10a 0xeebf33838618fc7f 0x7bafcce0e1863f1f

def z1313 : W := mkw 0x0040008280000428 0x80100020a000010a 0xeebf118386083c7f 0x7bafc460e1820f1f

def z1314 : W := mkw 0x80900004282451c5 0x202400010a091471 0x7be8720ff87cd3ff 0xdefa1c83fe1f34ff

def z1315 : W := mkw 0x204130828218042a 0x88104c20a086010a 0xe497318386183c7f 0x7925cc60e1860f1f

def z1316 : W := mkw 0x03000000075a8002 0x00c0000001d6a000 0xc1802c0007ffc001 0xf0600b0001fff000

def z1317 : W := mkw 0x1282c15c05e03b01 0x04a0b05701780ec0 0xde7fd3fc9fe03f82 0xf79ff4ff27f80fe0

def z1318 : W := mkw 0x2303fa00075a8002 0x08c0fe8001d6a000 0xefffff8087fffc4f 0xfbffffe021ffff13

def z1319 : W := mkw 0x23013a00075a8002 0x08c04e8001d6a000 0x01803e0001ffc001 0x80600f80007ff000

def z1320 : W := mkw 0x2303fa82875a8002 0x08c0fea0a1d6a000 0xeffbff8387ffd04f 0xfbfeffe0e1fff413

def z1321 : W := mkw 0x08200431608522d0 0x4208010c582148b4 0xfffcfe7ff99f33ff 0xffff3f9ffe67ccff

def z1322 : W := mkw 0x3c4135ebd218042a 0x8f104d7af486010a 0xbe1721fffe102c30 0x2f85c87fff840b0c

def z1323 : W := mkw 0x3c03ffebd0000000 0x0f00fffaf4000000 0x1143cffc78000000 0x0450f3ff1e000000

def z1324 : W := mkw 0x80900004282451c5 0x202400010a091471 0x71c0520cf86cd3cf 0xdc7014833e1b34f3

def z1325 : W := mkw 0x08200431608522d0 0x4208010c582148b4 0xf69cac73619323f3 0x3da72b1cd864c8fc

def z1326 : W := mkw 0x1282c15c05e03b01 0x04a0b05701780ec0 0xdfffd3fc07e03f82 0xf7fff4ff01f80fe0

def z1327 : W := mkw 0x1282c15c05e03b01 0x04a0b05701780ec0 0xde7fc1fc07f73f83 0xf79ff07f01fdcfe0

def z1328 : W := mkw 0x3f03ffebd75a8002 0x0fc0fffaf5d6a000 0x3ffbfffff9ffc001 0x8ffefffffe7ff000

def z1329 : W := mkw 0x1002c14800000000 0x0400b05200000000 0xffffd3fcfe083c4f 0x7ffff4ff3f820f13

def z1330 : W := mkw 0x23013a00075a8002 0x08c04e8001d6a000 0xc1d8be0007ffc001 0xf0762f8001fff000

def z1331 : W := mkw 0x1c0005ebd0000000 0x0700017af4000000 0x3ff8fffff8000000 0x0ffe3ffffe000000

def z1332 : W := mkw 0x08200431608522d0 0x4208010c582148b4 0xb7dcac73619723b0 0xadf72b1cd865c8ec

def z1333 : W := mkw 0x1f02cf6955428000 0x07c0b3da5550a000 0xdf7bcffc7fe7c000 0xf7def3ff1ff9f000

def z1334 : W := mkw 0x2303fa0005428000 0x08c0fe800150a000 0x01c0fe0001e7c000 0x80703f800079f000

def z1335 : W := mkw 0x204130828218042a 0x88104c20a086010a 0xacb7318386183c7d 0x6b2dcc60e1860f1f

def z1336 : W := mkw 0x0302ca0005428000 0x00c0b2800150a000 0x41c8ce0001e7c001 0x907233800079f000

def z1337 : W := mkw 0x3c4135ebd218042a 0x8f104d7af486010a 0x3e8031fff818007d 0x0fa00c7ffe06001f

def z1338 : W := mkw 0x3c03ffebd0000000 0x0f00fffaf4000000 0x7ffbfffff8600000 0xdffefffffe180000

def z1339 : W := mkw 0x08200431608522d0 0x4208010c582148b4 0xf7dcbe73619fe3f3 0xbdf72f9cd867f8fc

def z1340 : W := mkw 0x3303fb48075a8002 0x0cc0fed201d6a000 0xc9fbff8c07ffc001 0xf27effe301fff000

def z1341 : W := mkw 0x80b0001428a573d5 0x602c00050a295cf5 0x40040000006cf3ff 0xd0010000001b3cff

def z1342 : W := mkw 0x88300431688562d4 0x620c010c5a2158b5 0xf7dcac73619fe3ff 0xbdf72b1cd867f8ff

def z1343 : W := mkw 0x80900004282451c5 0x202400010a091471 0x3b60520cf86cd3ce 0xced814833e1b34f3

def z1344 : W := mkw 0x3e43ffebd758042a 0x8f90fffaf5d6010a 0xfffffffffff83c7f 0xfffffffffffe0f1f

def z1345 : W := mkw 0x0302ca0005428000 0x00c0b2800150a000 0x8153ce0007e7c000 0xa054f38001f9f000

def z1346 : W := mkw 0x08200431608522d0 0x4208010c582148b4 0xe69cac73019723f3 0xb9a72b1cc065c8fc

def z1347 : W := mkw 0x2303fa00075a8002 0x08c0fe8001d6a000 0xc163de0007ffc001 0xf058f78001fff000

def z1348 : W := mkw 0x3f43ffebd75a842a 0x8fd0fffaf5d6a10a 0xfffbffffffffdc0d 0xfffefffffffff703

def z1349 : W := mkw 0x3c43ffebd218042a 0x8f10fffaf486010a 0x3ffbfffff808000c 0x0ffefffffe020003

def z1350 : W := mkw 0x1282c15c05e03b01 0x04a0b05701780ec0 0xfeffd1fc87e03f82 0xffbff47f21f80fe0

def z1351 : W := mkw 0x1282c15c05e03b01 0x04a0b05701780ec0 0xdf7fc3fc7fe03f82 0xf7dff0ff1ff80fe0

def z1352 : W := mkw 0x0000001000802200 0x0000000400200880 0xde3f01f006003f82 0x778fc07c01800fe0

def z1353 : W := mkw 0x1c02cf6950000000 0x0700b3da54000000 0x33c8ce7c78000000 0x0cf2339f1e000000

def z1354 : W := mkw 0x1000014800000000 0x0400005200000000 0x3e0001fcf8000000 0x0f80007f3e000000

def z1355 : W := mkw 0x1682cb5c15e03b01 0x05a0b2d705780ec0 0xde7fc3fc1fe03f82 0xf79ff0ff07f80fe0

def z1356 : W := mkw 0x2343fa82875a842a 0x88d0fea0a1d6a10a 0xefffff8387ffec31 0xfbffffe0e1fffb0c

def z1357 : W := mkw 0x3c03ffebd0000000 0x0f00fffaf4000000 0x39e3fffff8000000 0x0e78fffffe000000

def z1358 : W := mkw 0x1302cb4805428000 0x04c0b2d20150a000 0x1f7bcffc01e7c000 0x87def3ff0079f000

def z1359 : W := mkw 0x1202c15805c02a00 0x0480b05601700a80 0xd67fc1f007e02f82 0xf59ff07c01f80be0

def z1360 : W := mkw 0x1c02cf6950000000 0x0700b3da54000000 0xd1d8ee7c79970001 0xb4763b9f1e65c000

def z1361 : W := mkw 0x08200431608522d0 0x4208010c582148b4 0xd554ac73619723f3 0xb5552b1cd865c8fc

def z1362 : W := mkw 0x1c0005ebd0000000 0x0700017af4000000 0x180001fcf8000000 0x0600007f3e000000

def z1363 : W := mkw 0x3c03ffebd0000000 0x0f00fffaf4000000 0x3ffffffff8002072 0x0ffffffffe00081c

def z1364 : W := mkw 0x3c43ffebd0000428 0x8f10fffaf400010a 0xfffffffffe003c7e 0x7fffffffff800f1f

def z1365 : W := mkw 0x3f03ffebd75a8002 0x0fc0fffaf5d6a000 0xbffbffffff9fc001 0x2ffeffffffe7f000

def z1366 : W := mkw 0x1282c15c05e03b01 0x04a0b05701780ec0 0x9e7fc1fc07e02f80 0xa79ff07f01f80be0

def z1367 : W := mkw 0x3c43ffebd218042a 0x8f10fffaf486010a 0xfebf73fffe183c7f 0x7fafdcffff860f1f

def z1368 : W := mkw 0x3f03ffebd75a8002 0x0fc0fffaf5d6a000 0xf1fbfe7fffffc001 0xfc7eff9ffffff000

def z1369 : W := mkw 0x3c03ffebd0000000 0x0f00fffaf4000000 0x3fdbadfff8000000 0x0ff6eb7ffe000000

def z1370 : W := mkw 0x8292c0142de47bc5 0x20a4b0050b791ef1 0xc1ffd20007ecffcf 0xf07ff48001fb3ff3

def z1371 : W := mkw 0x3f43ffebd75a842a 0x8fd0fffaf5d6a10a 0xffffffffff9b3c7f 0x7fffffffffe6cf1f

def z1372 : W := mkw 0x2303fa82875a8002 0x08c0fea0a1d6a000 0xefffff8387fffc03 0xfbffffe0e1ffff00

def z1373 : W := mkw 0x2343fa82875a842a 0x88d0fea0a1d6a10a 0xc5ffff8307fffc7f 0xf17fffe0c1ffff1f

def z1374 : W := mkw 0x3703fbca975a8002 0x0dc0fef2a5d6a000 0xfbfbff8cffffc001 0xfefeffe33ffff000

def z1375 : W := mkw 0x3003f1ca80000000 0x0c00fc72a0000000 0x3ffbf3fff8000000 0x0ffefcfffe000000

def z1376 : W := mkw 0x0040008280000428 0x80100020a000010a 0xeebf218386103c7f 0x7bafc860e1840f1f

def z1377 : W := mkw 0x3c43ffebd218042a 0x8f10fffaf486010a 0xfffffffffe083c0e 0x7fffffffff820f03

def z1378 : W := mkw 0x0820043140812210 0x4208010c50204884 0xd7dcac73019723b3 0xb5f72b1cc065c8ec

def z1379 : W := mkw 0x3f03ffebd75a8002 0x0fc0fffaf5d6a000 0xfffbffffff970001 0xbffeffffffe5c000

def z1380 : W := mkw 0x1c0005ebd0000000 0x0700017af4000000 0xfe3f01fffe003c02 0x7f8fc07fff800f00

def z1381 : W := mkw 0x08200431608522d0 0x4208010c582148b4 0xe594ac73619723f3 0xb9652b1cd865c8fc

def z1382 : W := mkw 0x1c02cf6950000000 0x0700b3da54000000 0x3ffbdffcf8000000 0x0ffef7ff3e000000

def z1383 : W := mkw 0x2343fa82875a842a 0x88d0fea0a1d6a10a 0xc1fbfe0087ffc00d 0xf07eff8021fff003

def z1384 : W := mkw 0x286134a3e21d04fa 0xca184d28f887413e 0x21802c0360170071 0x08600b00d805c01c

def z1385 : W := mkw 0x3c03ffebd0000000 0x0f00fffaf4000000 0x3ffbfffff80cc001 0x0ffefffffe033000

def z1386 : W := mkw 0x9292c15c0de07b05 0x24a4b05703781ec1 0xffffd3fcffe8ff8e 0xfffff4ff3ffa3fe3

def z1387 : W := mkw 0x2303fa00075a8002 0x08c0fe8001d6a000 0x01fbfe0007efc000 0xc07eff8001fbf000

def z1388 : W := mkw 0x2003fa0000000000 0x0800fe8000000000 0xc1fbfe0001ffc001 0xf07eff80007ff000

def z1389 : W := mkw 0x23413082875a842a 0x88d04c20a1d6a10a 0xefffbd8387fffc7f 0xfbffef60e1ffff1f

def z1390 : W := mkw 0x2303fa00075a8002 0x08c0fe8001d6a000 0xc1c0fe0007ffc001 0xf0703f8001fff000

def z1391 : W := mkw 0x204130828218042a 0x88104c20a086010a 0xefbf3383861cfc7f 0x7befcce0e1873f1f

def z1392 : W := mkw 0xac513ea3fa1c44ee 0xab144fa8fe87113b 0x21803e03f81cc07d 0x08600f80fe07301f

def z1393 : W := mkw 0x3c03ffebd0000000 0x0f00fffaf4000000 0x3be8fe7ff8000000 0x0efa3f9ffe000000

def z1394 : W := mkw 0x3e03ffebd5400000 0x0f80fffaf5500000 0xfffbfffffff70001 0xfffefffffffdc000

def z1395 : W := mkw 0x829000142de47bc5 0x20a400050b791ef1 0x4000000001ecd3cf 0xd0000000007b34f3

def z1396 : W := mkw 0x3c43ffebd0000428 0x8f10fffaf400010a 0x7ffffffff8083c7f 0x5ffffffffe020f1f

def z1397 : W := mkw 0x80900004282451c5 0x202400010a091471 0xfbec520cf87cf3ff 0xfefb14833e1f3cff

def z1398 : W := mkw 0x1702cb4815428000 0x05c0b2d20550a000 0x0140ce0c19e7c000 0x805033830679f000

def z1399 : W := mkw 0x2303fa00075a8002 0x08c0fe8001d6a000 0xc9fbfe0c9fffc001 0xf27eff8327fff000

def z1400 : W := mkw 0x0202c00005400000 0x0080b00001500000 0xc1fbfe0007ffc001 0xf07eff8001fff000

def z1401 : W := mkw 0x3c03ffebd0000000 0x0f00fffaf4000000 0x1140ee7f78000000 0x04503b9fde000000

def z1402 : W := mkw 0x1282c15c05e03b01 0x04a0b05701780ec0 0xd457c1fc07e03f82 0xf515f07f01f80fe0

def z1403 : W := mkw 0x2303fa00075a8002 0x08c0fe8001d6a000 0xd7fbfe7007ffc001 0xf5feff9c01fff000

def z1404 : W := mkw 0x2343fa82875a842a 0x88d0fea0a1d6a10a 0xebfbff8087ffdc4f 0xfafeffe021fff713

def z1405 : W := mkw 0x3c03ffebd0000000 0x0f00fffaf4000000 0x1140de7cf8000000 0x0450379f3e000000

def z1406 : W := mkw 0x80900004282451c5 0x202400010a091471 0x7fec520ff86cf3ff 0xdffb1483fe1b3cff

def z1407 : W := mkw 0x1282c15c05e03b01 0x04a0b05701780ec0 0xde7fe1ff07f03fb2 0xf79ff87fc1fc0fec

def z1408 : W := mkw 0x2303fa00075a8002 0x08c0fe8001d6a000 0x81b3fe0007ffc001 0x606cff8001fff000

def z1409 : W := mkw 0x2303fa00075a8002 0x08c0fe8001d6a000 0xe3fbfe0007ffc043 0xf8feff8001fff010

def z1410 : W := mkw 0x3c03ffebd0000000 0x0f00fffaf4000000 0x3f93bffff8000000 0x0fe4effffe000000

def z1411 : W := mkw 0x3f03ffebd75a8002 0x0fc0fffaf5d6a000 0x9553efff7ff7c000 0xa554fbffdffdf000

def z1412 : W := mkw 0x08200431608522d0 0x4208010c582148b4 0xf7fcfe73619723f3 0xbdff3f9cd865c8fc

def z1413 : W := mkw 0x88300431688562d4 0x620c010c5a2158b5 0xf7dcae737997e3f3 0xbdf72b9cde65f8fc

def z1414 : W := mkw 0x21413a82821a842a 0x88504ea0a086a10a 0xeebf3d83861b3c7f 0x7bafcf60e186cf1f

def z1415 : W := mkw 0x3c03ffebd0000000 0x0f00fffaf4000000 0x3feb53fff8000000 0x0ffad4fffe000000

def z1416 : W := mkw 0x1282c15c05e03b01 0x04a0b05701780ec0 0xffffc1fc67e03f82 0xfffff07f19f80fe0

def z1417 : W := mkw 0x2303fa00075a8002 0x08c0fe8001d6a000 0xc5ffff8007ffec01 0xf17fffe001fffb00

def z1418 : W := mkw 0x2303fa82875a8002 0x08c0fea0a1d6a000 0xc5fbff8307ffc001 0xf17effe0c1fff000

def z1419 : W := mkw 0x839000142ffefbc7 0x20e400050bffbef1 0xc004000007ffffcf 0xf001000001fffff3

def z1420 : W := mkw 0x9cb005fff8a573d5 0x672c017ffe295cf5 0x3e0401fff80033fe 0x0f81007ffe000cff

def z1421 : W := mkw 0x3c43ffebd0000428 0x8f10fffaf400010a 0x3ffbfffff800007c 0x0ffefffffe00001f

def z1422 : W := mkw 0x3c03ffebd0000000 0x0f00fffaf4000000 0x1d73fffff8000000 0x075cfffffe000000

def z1423 : W := mkw 0x3c03ff6950000000 0x0f00ffda54000000 0x1ffbfffc78000000 0x07feffff1e000000

def z1424 : W := mkw 0x1e02cf6955400000 0x0780b3da55500000 0x1140ce7c79e00000 0x8450339f1e780000

def z1425 : W := mkw 0x0302ca00075a8002 0x00c0b28001d6a000 0xc17bce0007ffc001 0xf05ef38001fff000

def z1426 : W := mkw 0x1c02cfebd0000000 0x0700b3faf4000000 0x3e008dfff8000000 0x0f80237ffe000000

def z1427 : W := mkw 0x1c02cf6950000000 0x0700b3da54000000 0x1553cffc78000000 0x0554f3ff1e000000

def z1428 : W := mkw 0x3c03ffebd2180002 0x0f00fffaf4860000 0xfffbffffff9f0001 0xfffeffffffe7c000

def z1429 : W := mkw 0x08200431608522d0 0x4208010c582148b4 0xf1d8ac73619703f1 0xbc762b1cd865c0fc

def z1430 : W := mkw 0x1282c15c05e03b01 0x04a0b05701780ec0 0xde7fedfc07f33f82 0xf79ffb7f01fccfe0

def z1431 : W := mkw 0x0820043140812210 0x4208010c50204884 0xf6dcac73019323f3 0xbdb72b1cc064c8fc

def z1432 : W := mkw 0x1282c15c05e03b01 0x04a0b05701780ec0 0xde5f81fc07803f82 0xb797e07f01e00fe0

def z1433 : W := mkw 0x204130828218042a 0x88104c20a086010a 0xeebf3183867cfc7f 0xfbafcc60e19f3f1f

def z1434 : W := mkw 0x2c013ea3d0000000 0x0b004fa8f4000000 0x3ff8fe7ff8000000 0x0ffe3f9ffe000000

def z1435 : W := mkw 0x1282c15c05e03b01 0x04a0b05701780ec0 0xd65f81f007e03f82 0xf597e07c01f80fe0

def z1436 : W := mkw 0x0302c000075a8002 0x00c0b00001d6a000 0xc1fbec0007ffc001 0xf07efb0001fff000

def z1437 : W := mkw 0x1282c15c05e03b01 0x04a0b05701780ec0 0xde7fd3fc07e8ff82 0xf79ff4ff01fa3fe0

def z1438 : W := mkw 0x1c02cfebd0000000 0x0700b3faf4000000 0x3e0043fff8000000 0x0f8010fffe000000

def z1439 : W := mkw 0x9292c15c0de07b05 0x24a4b05703781ec1 0xde7fc1fc07e8ff8e 0xf79ff07f01fa3fe3

def z1440 : W := mkw 0x3c43ffebd218042a 0x8f10fffaf486010a 0x3ffbfffff8100030 0x0ffefffffe04000c

def z1441 : W := mkw 0x2343fa82875a842a 0x88d0fea0a1d6a10a 0xebfbfe0387ffd07f 0xfafeff80e1fff41f

def z1442 : W := mkw 0x0302ca0005428000 0x00c0b2800150a000 0x1140ce0c79e7c000 0x845033831e79f000

def z1443 : W := mkw 0x2303fa00075a8002 0x08c0fe8001d6a000 0xcbfbfe0007ffd003 0xf2feff8001fff400

def z1444 : W := mkw 0x88300431688562d4 0x620c010c5a2158b5 0xfffcfe7ff99fe3ff 0xbfff3f9ffe67f8ff

def z1445 : W := mkw 0x2303fa00075a8002 0x08c0fe8001d6a000 0xc1a37e0007ffc001 0xf068df8001fff000

def z1446 : W := mkw 0x1282c15c05e03b01 0x04a0b05701780ec0 0xde7fd1fc87e83f8e 0xf79ff47f21fa0fe3

def z1447 : W := mkw 0x2343fa82875a842a 0x88d0fea0a1d6a10a 0xcdffff8387fffc3d 0xf37fffe0e1ffff0f

def z1448 : W := mkw 0x2303fa00075a8002 0x08c0fe8001d6a000 0xeffffe0387fff07f 0xfbffff80e1fffc1f

def z1449 : W := mkw 0x3c03ffebd0000000 0x0f00fffaf4000000 0x3ffbfffff800104e 0x0ffefffffe000413

def z1450 : W := mkw 0x204130828218042a 0x88104c20a086010a 0x6eaf118386083c7f 0x5babc460e1820f1f

def z1451 : W := mkw 0x1c02cf6950000000 0x0700b3da54000000 0x10008c7c78000000 0x0400231f1e000000

def z1452 : W := mkw 0x1282c15c05e03b01 0x04a0b05701780ec0 0xde2741fc07e03f82 0xf789d07f01f80fe0

def z1453 : W := mkw 0x1282c15c05e03b01 0x04a0b05701780ec0 0xd867c1fc07e03f82 0xf619f07f01f80fe0

def z1454 : W := mkw 0x3f03ff69575a8002 0x0fc0ffda55d6a000 0xf7fbfe7f7fffc001 0xfdfeff9fdffff000

def z1455 : W := mkw 0x3c4135ebd218042a 0x8f104d7af486010a 0x3e2311fffe081c0c 0x4f88c47fff820703

def z1456 : W := mkw 0x0820043140812210 0x4208010c50204884 0xf7dcac73619323b2 0xbdf72b1cd864c8ec

def z1457 : W := mkw 0x3c43ffebd218042a 0x8f10fffaf486010a 0x1963dffcfe081c0c 0x4658f7ff3f820703

def z1458 : W := mkw 0x2041308280000428 0x88104c20a000010a 0xeebf318386003c7e 0x7bafcc60e1800f1f

def z1459 : W := mkw 0x0000000000000000 0x0000000000000000 0xeffcfe0381fff07f 0xfbff3f80e07ffc1f

def z1460 : W := mkw 0x0302ca0005428000 0x00c0b2800150a000 0xc140ce0007e7c000 0xf050338001f9f000

def z1461 : W := mkw 0x3c43ffebd218042a 0x8f10fffaf486010a 0xfffffffffe103c32 0x7fffffffff840f0c

def z1462 : W := mkw 0x3c03ffebd0000000 0x0f00fffaf4000000 0xfffffffff8002002 0x3ffffffffe000800

def z1463 : W := mkw 0x3c03ffebd0000000 0x0f00fffaf4000000 0x1f7befff78000000 0x07defbffde000000

def z1464 : W := mkw 0x1c0005ebd0000000 0x0700017af4000000 0x3f8013fff8000000 0x0fe004fffe000000

def z1465 : W := mkw 0x1c0005ebd0000000 0x0700017af4000000 0xfe9c21fff8102073 0x3fa7087ffe04081c

def z1466 : W := mkw 0x1c02c56950000000 0x0700b15a54000000 0x1040c07c78000000 0x0410301f1e000000

def z1467 : W := mkw 0x829000142de47bc5 0x20a400050b791ef1 0x0000000001e4c380 0x80000000007930e0

def z1468 : W := mkw 0x2803fe2140000000 0x0a00ff8850000000 0x3ffbfe7ff8000000 0x0ffeff9ffe000000

def z1469 : W := mkw 0x3c03ffebd0000000 0x0f00fffaf4000000 0x1f7bdffcf8000000 0x07def7ff3e000000

def z1470 : W := mkw 0x0800042140000000 0x0200010850000000 0x3fe8527ff8000000 0x0ffa149ffe000000

def z1471 : W := mkw 0x08200431608522d0 0x4208010c582148b4 0xb754ac73619723f2 0xadd52b1cd865c8fc

def z1472 : W := mkw 0x2343fa82875a842a 0x88d0fea0a1d6a10a 0xeebfbd8387fffc7f 0xfbafef60e1ffff1f

def z1473 : W := mkw 0x80900004282451c5 0x202400010a091471 0x59e8520cf86cd38d 0xd67a14833e1b34e3

def z1474 : W := mkw 0x204130828218042a 0x88104c20a086010a 0xae37318386183c7e 0x6b8dcc60e1860f1f

def z1475 : W := mkw 0x08200431608522d0 0x4208010c582148b4 0xfffcec7f619723f3 0xbfff3b1fd865c8fc

def z1476 : W := mkw 0x24413a829218042a 0x89104ea0a486010a 0xeebf33839e183c7f 0x7bafcce0e7860f1f

def z1477 : W := mkw 0x3c43ffebd218042a 0x8f10fffaf486010a 0xfffffffff818207f 0x3ffffffffe06081f

def z1478 : W := mkw 0x1c02cfebd0000000 0x0700b3faf4000000 0x3fd8effff8000000 0x0ff63bfffe000000

def z1479 : W := mkw 0x2303fa00075a8002 0x08c0fe8001d6a000 0xc1dbac0007ffc001 0xf076eb0001fff000

def z1480 : W := mkw 0x0800042140000000 0x0200010850000000 0x1140ce7c78000000 0x0450339f1e000000

def z1481 : W := mkw 0x1c02cfebd0000000 0x0700b3faf4000000 0x3140ce7ff8000000 0x0c50339ffe000000

def z1482 : W := mkw 0x80900004282451c5 0x202400010a091471 0xffff738ffe7cffff 0xffffdce3ff9f3fff

def z1483 : W := mkw 0x3c03ffebd0000000 0x0f00fffaf4000000 0x7ffbfffff8040001 0x9ffefffffe010000

def z1484 : W := mkw 0x08200431608522d0 0x4208010c582148b4 0xf1c4ac73619723f3 0xbc712b1cd865c8fc

def z1485 : W := mkw 0x80b00004282551d5 0x602c00010a095475 0x7be8520cf87fd3ff 0xdefa14833e1ff4ff

def z1486 : W := mkw 0x3f03ff69575a8002 0x0fc0ffda55d6a000 0x1163de7c7e68c000 0x4458f79f1f9a3000

def z1487 : W := mkw 0x80900004282451c5 0x202400010a091471 0x71e8520cf86cc3cd 0xdc7a14833e1b30f3

def z1488 : W := mkw 0x1c02cf6950000000 0x0700b3da54000000 0x1f40cffc78000000 0x07d033ff1e000000

def z1489 : W := mkw 0x88b0043568a573d5 0x622c010d5a295cf5 0x3604007f780023f2 0x0d81001fde0008fc

def z1490 : W := mkw 0x2343fa82875a842a 0x88d0fea0a1d6a10a 0xc1fbff8007ffcc01 0xf07effe001fff300

def z1491 : W := mkw 0x2343fa00075a842a 0x88d0fe8001d6a10a 0xc1fbfe0007ffc07d 0xf07eff8001fff01f

def z1492 : W := mkw 0x2303fa00075a8002 0x08c0fe8001d6a000 0xebfbfe0087ffc001 0xfafeff8021fff000

def z1493 : W := mkw 0x1f02cf6955428000 0x07c0b3da5550a000 0x1140ce7c7860c000 0x0450339f1e183000

def z1494 : W := mkw 0x0302ca0005428000 0x00c0b2800150a000 0x0160de0001efc000 0xc0583780007bf000

def z1495 : W := mkw 0x08200431608522d0 0x4208010c582148b4 0xf7ffac73679723f3 0xfdffeb1cd9e5c8fc

def z1496 : W := mkw 0x3c03ffebd0000000 0x0f00fffaf4000000 0x7ffbfffff8000043 0x1ffefffffe000010

def z1497 : W := mkw 0x2343fa82875a842a 0x88d0fea0a1d6a10a 0xe5ffff8387ffec7d 0xf97fffe0e1fffb1f

def z1498 : W := mkw 0x20413a828218042a 0x88104ea0a086010a 0xefbf3f8386183c7f 0x7befcfe0e1860f1f

def z1499 : W := mkw 0x2303fa00075a8002 0x08c0fe8001d6a000 0xc07bec0007ffc001 0xf01efb0001fff000

def z1500 : W := mkw 0x3f03ffebd75a8002 0x0fc0fffaf5d6a000 0xd9fbfffcffffc001 0xf67effff3ffff000

def z1501 : W := mkw 0x2303fa00075a8002 0x08c0fe8001d6a000 0xf3fbfe0067ffc001 0xfcfeff8019fff000

def z1502 : W := mkw 0x08200431608522d0 0x4208010c582148b4 0x1140ac73619703b0 0x84502b1cd865c0ec

def z1503 : W := mkw 0x3c03ffebd0000000 0x0f00fffaf4000000 0x3f63dffff8000000 0x0fd8f7fffe000000

def z1504 : W := mkw 0x0000000000000000 0x0000000000000000 0xc1d8ac0001ffc001 0xf0762b00007ff000

def z1505 : W := mkw 0x80900004282451c5 0x202400010a091471 0x7beb538cfe6cdfcf 0xdefad4e33f9b37f3

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z0,z1,z2,z3,z4,z7,z6])],[(0,[z0,z1,z8,z2,z3,z4,z6])],[(0,[z9,z0,z1,z2,z3,z4,z6]),(0,[z10,z0,z1,z2,z3,z4,z6]),(1,[z11,z0,z1,z12,z4,z6]),(0,[z0,z1,z13,z2,z3,z14,z6])],[(0,[z15,z0,z1,z2,z3,z14,z6]),(0,[z0,z1,z16,z2,z3,z14,z6])],[(0,[z15,z0,z1,z2,z17,z4,z6]),(0,[z0,z18,z19,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z20,z6]),(0,[z0,z1,z16,z2,z3,z12,z6])],[(0,[z21,z0,z1,z22,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z23]),(0,[z24,z0,z1,z2,z12,z4,z6]),(0,[z0,z1,z25,z2,z3,z4,z6]),(1,[z0,z1,z26,z2,z12,z6]),(1,[z0,z1,z2,z3,z27,z6])],[(0,[z28,z0,z1,z16,z2,z3,z6]),(0,[z11,z0,z1,z2,z29,z4,z6]),(1,[z0,z1,z30,z12,z4,z6])],[(0,[z0,z1,z2,z3,z31,z4,z32])],[(0,[z11,z0,z1,z22,z2,z4,z6]),(0,[z0,z1,z2,z3,z29,z14,z6]),(0,[z0,z1,z2,z2,z3,z33,z6]),(0,[z0,z1,z2,z3,z4,z34,z6])],[(0,[z0,z1,z30,z3,z12,z4,z6]),(0,[z35,z0,z1,z2,z3,z4,z6])],[(0,[z0,z36,z1,z2,z3,z4,z6]),(0,[z37,z0,z1,z30,z3,z4,z6]),(0,[z0,z1,z2,z3,z14,z6,z38])],[(0,[z0,z1,z2,z3,z39,z4,z6]),(0,[z0,z1,z40,z2,z3,z4,z6])],[(1,[z0,z1,z2,z41,z4,z6]),(1,[z11,z0,z1,z2,z14,z6])],[(0,[z42,z43,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z4,z44]),(0,[z0,z1,z2,z3,z4,z6,z45]),(0,[z0,z18,z46,z2,z3,z4,z6]),(1,[z0,z1,z12,z4,z6,z47]),(0,[z48,z0,z1,z2,z3,z4,z6])],[(0,[z21,z0,z49,z2,z3,z4,z6]),(0,[z0,z1,z2,z12,z4,z6,z50])],[(0,[z0,z1,z2,z3,z4,z51,z6]),(1,[z0,z52,z1,z2,z3,z6])]],
   [[(0,[z0,z1,z2,z3,z4,z6,z53])],[(0,[z54,z42,z0,z2,z3,z4,z6]),(0,[z11,z0,z55,z1,z2,z4,z6]),(0,[z0,z1,z2,z3,z4,z56,z6]),(0,[z57,z0,z19,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z33,z34,z6]),(0,[z0,z1,z2,z3,z4,z6,z58])],[(0,[z59,z1,z2,z3,z4,z60,z6]),(0,[z0,z61,z1,z2,z3,z4,z6]),(0,[z62,z0,z1,z2,z63,z4,z6])],[(1,[z0,z64,z2,z3,z4,z6]),(0,[z65,z0,z1,z2,z3,z4,z6]),(0,[z0,z46,z2,z3,z66,z4,z6]),(0,[z11,z0,z1,z16,z2,z3,z6]),(0,[z0,z1,z16,z2,z4,z14,z6]),(0,[z0,z67,z1,z2,z3,z4,z6])],[(0,[z68,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z69])],[(0,[z24,z0,z1,z2,z3,z70,z6]),(0,[z71,z0,z1,z2,z3,z72,z6])],[(0,[z73,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z12,z4,z60,z6]),(0,[z74,z0,z1,z2,z3,z33,z6]),(0,[z75,z0,z1,z16,z2,z3,z6]),(0,[z0,z1,z2,z76,z3,z4,z6])],[(0,[z77,z0,z1,z2,z3,z4,z6]),(0,[z1,z2,z78,z3,z79,z4,z6]),(1,[z80,z1,z2,z78,z4,z6])],[(1,[z0,z1,z2,z81,z4,z6]),(0,[z1,z2,z3,z79,z4,z6,z82]),(0,[z0,z2,z3,z4,z83,z6,z84])],[],[(0,[z0,z1,z85,z2,z3,z4,z6]),(0,[z86,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z87,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z88])],[(1,[z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z89]),(0,[z0,z1,z2,z3,z4,z90,z6]),(0,[z0,z19,z1,z2,z3,z4,z91]),(0,[z0,z1,z2,z3,z4,z6,z92]),(0,[z37,z0,z1,z2,z93,z4,z6]),(0,[z0,z1,z2,z93,z3,z4,z6])],[(0,[z94,z0,z1,z2,z3,z33,z6]),(0,[z0,z1,z2,z3,z95,z4,z6]),(0,[z96,z0,z1,z2,z3,z14,z6]),(0,[z0,z1,z2,z3,z97,z4,z6])],[(0,[z98,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z99,z2,z3,z33,z6]),(0,[z0,z1,z2,z3,z14,z6,z100])],[(0,[z101,z0,z1,z2,z12,z4,z6]),(0,[z0,z1,z2,z3,z4,z102,z6])],[(0,[z101,z80,z1,z2,z3,z4,z6]),(0,[z62,z80,z0,z1,z2,z4,z6]),(1,[z103,z1,z2,z3,z104,z6]),(0,[z105,z0,z1,z2,z3,z4,z6]),(0,[z11,z0,z106,z1,z2,z4,z6]),(0,[z107,z0,z1,z2,z3,z14,z6]),(0,[z0,z108,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z109,z6]),(0,[z110,z0,z1,z2,z3,z4,z6])]],
   [[(0,[z54,z0,z1,z3,z12,z4,z6]),(0,[z0,z1,z2,z3,z14,z111,z6])],[(0,[z0,z1,z2,z3,z4,z6,z112])],[(0,[z0,z1,z2,z113,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z72,z6]),(0,[z62,z0,z1,z2,z3,z14,z6]),(0,[z0,z1,z16,z114,z2,z3,z6])],[(0,[z0,z115,z2,z3,z66,z4,z6]),(0,[z0,z55,z1,z2,z3,z14,z6]),(0,[z0,z19,z106,z2,z3,z4,z6]),(0,[z0,z116,z1,z2,z3,z4,z6]),(0,[z74,z0,z1,z26,z2,z3,z6]),(1,[z0,z1,z2,z3,z117,z6]),(0,[z0,z1,z2,z3,z118,z14,z6])],[(0,[z28,z0,z119,z2,z3,z4,z6]),(0,[z120,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z121,z3,z4,z6]),(0,[z0,z1,z2,z12,z4,z6,z47]),(1,[z0,z1,z99,z3,z33,z6])],[(0,[z54,z43,z0,z2,z3,z4,z6]),(0,[z0,z1,z122,z2,z123,z3,z6]),(0,[z0,z1,z2,z12,z4,z124,z6]),(0,[z0,z1,z16,z125,z2,z3,z6])],[(0,[z80,z0,z1,z2,z12,z4,z6]),(0,[z0,z1,z16,z2,z3,z104,z6]),(0,[z126,z0,z1,z2,z3,z4,z6]),(0,[z127,z71,z0,z1,z2,z3,z6]),(0,[z0,z1,z128,z2,z3,z33,z6])],[(0,[z0,z1,z2,z3,z129,z4,z6]),(0,[z103,z0,z1,z16,z2,z3,z6]),(0,[z0,z1,z30,z2,z3,z14,z6])],[(0,[z0,z1,z115,z2,z12,z4,z6]),(0,[z15,z0,z1,z2,z3,z51,z6]),(0,[z0,z1,z2,z12,z4,z70,z6])],[(0,[z94,z0,z1,z26,z2,z3,z6]),(0,[z0,z1,z2,z3,z4,z83,z38]),(0,[z130,z0,z1,z2,z3,z4,z6])],[(1,[z131,z0,z1,z2,z4,z6])],[(0,[z0,z1,z2,z3,z33,z72,z6])],[(1,[z0,z1,z2,z3,z132,z6]),(1,[z127,z0,z1,z2,z3,z32])],[(0,[z0,z1,z2,z3,z4,z6,z133])],[(0,[z0,z1,z46,z2,z134,z4,z6]),(0,[z0,z1,z2,z3,z4,z135,z6])],[(0,[z0,z1,z2,z3,z6,z112,z91]),(0,[z0,z1,z2,z3,z136,z4,z6])]],
   [[(0,[z0,z1,z2,z3,z137,z4,z6]),(1,[z0,z18,z2,z123,z4,z6]),(0,[z37,z138,z1,z2,z3,z4,z6]),(0,[z139,z0,z1,z2,z63,z4,z6]),(1,[z140,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z141])],[(0,[z0,z142,z1,z2,z3,z33,z6]),(0,[z143,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z144,z6]),(0,[z0,z1,z2,z3,z4,z6,z145])],[(0,[z0,z146,z1,z2,z3,z4,z6])],[(0,[z147,z0,z1,z2,z3,z4,z6]),(0,[z54,z0,z1,z2,z3,z4,z148]),(1,[z0,z1,z149,z2,z3,z6])],[(0,[z21,z0,z1,z2,z3,z33,z6]),(0,[z11,z101,z0,z1,z2,z4,z6]),(0,[z0,z1,z2,z150,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z151]),(0,[z0,z1,z152,z2,z12,z4,z6])],[(0,[z0,z1,z2,z3,z153,z4,z6]),(0,[z154,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z155,z4,z6]),(0,[z0,z1,z2,z3,z33,z14,z6])],[(0,[z37,z0,z1,z2,z3,z14,z6]),(0,[z0,z156,z1,z16,z2,z3,z6]),(0,[z127,z0,z1,z157,z3,z4,z6])],[(0,[z158,z0,z1,z2,z3,z4,z6]),(0,[z62,z0,z1,z2,z3,z159,z6]),(0,[z160,z0,z1,z2,z3,z4,z6])],[(0,[z11,z0,z1,z2,z161,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z162])],[(0,[z0,z1,z2,z3,z4,z6,z163]),(0,[z164,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z165,z6]),(0,[z0,z1,z149,z2,z12,z4,z6])],[(0,[z0,z1,z2,z3,z161,z14,z6]),(1,[z0,z1,z2,z12,z166,z6])],[(0,[z0,z1,z2,z3,z167,z4,z6]),(0,[z43,z0,z2,z3,z4,z6,z91]),(0,[z0,z1,z2,z3,z168,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z169]),(0,[z170,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z171,z4,z6])],[(0,[z0,z1,z2,z3,z79,z4,z6]),(0,[z139,z80,z0,z1,z2,z4,z6]),(0,[z0,z18,z1,z2,z3,z14,z6]),(0,[z0,z1,z2,z12,z4,z172,z6])],[(0,[z0,z1,z173,z2,z3,z4,z6]),(0,[z43,z0,z1,z26,z2,z3,z6]),(1,[z54,z0,z1,z12,z4,z6]),(0,[z54,z0,z1,z2,z3,z14,z6]),(0,[z0,z18,z1,z2,z17,z4,z6]),(0,[z0,z142,z1,z26,z2,z3,z6]),(0,[z0,z19,z1,z2,z3,z33,z6]),(0,[z0,z174,z1,z2,z12,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z175]),(0,[z0,z176,z1,z2,z3,z4,z6])],[(1,[z0,z1,z2,z3,z177,z6]),(0,[z0,z156,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z178,z4,z6]),(0,[z0,z179,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z180,z6])]],
   [[(0,[z0,z1,z2,z3,z4,z6,z181]),(0,[z182,z0,z1,z2,z3,z14,z6]),(0,[z139,z0,z1,z2,z3,z14,z6]),(0,[z183,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z184,z6]),(0,[z11,z94,z0,z1,z2,z4,z6]),(0,[z139,z0,z1,z2,z17,z4,z6])],[(0,[z0,z1,z2,z78,z3,z14,z6]),(0,[z0,z1,z2,z3,z4,z6,z82]),(0,[z0,z1,z2,z185,z3,z4,z6]),(0,[z0,z1,z2,z12,z31,z4,z6])],[(0,[z0,z1,z22,z2,z3,z14,z6]),(0,[z0,z1,z2,z3,z4,z186,z6]),(0,[z11,z0,z1,z3,z12,z4,z6]),(0,[z0,z1,z2,z3,z4,z159,z6])],[(0,[z0,z1,z2,z3,z187,z4,z6])],[(1,[z28,z0,z1,z2,z14,z6])],[(0,[z0,z1,z16,z2,z3,z188,z6]),(1,[z0,z1,z189,z3,z4,z6])],[(0,[z0,z1,z26,z2,z3,z66,z6]),(0,[z190,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z191,z6]),(0,[z0,z1,z99,z2,z3,z4,z6])],[(0,[z192,z0,z1,z2,z3,z4,z6]),(0,[z193,z0,z1,z2,z3,z4,z6]),(0,[z127,z0,z1,z2,z3,z14,z6])],[(0,[z103,z24,z1,z2,z3,z4,z6]),(0,[z11,z0,z1,z2,z3,z194,z6])],[(0,[z42,z0,z1,z2,z3,z4,z6]),(0,[z57,z0,z1,z2,z3,z14,z6])],[(0,[z43,z0,z55,z2,z3,z4,z6]),(0,[z195,z0,z1,z2,z3,z4,z6]),(0,[z0,z19,z1,z26,z2,z3,z6]),(0,[z0,z1,z2,z12,z12,z4,z6]),(0,[z196,z11,z0,z1,z2,z4,z6])],[(1,[z0,z2,z3,z197,z4,z6])],[(0,[z0,z1,z16,z2,z3,z79,z6]),(0,[z0,z1,z2,z3,z4,z83,z6]),(0,[z0,z1,z2,z3,z198,z4,z6])],[(0,[z0,z1,z199,z2,z3,z4,z6])],[]],
   [[(0,[z0,z1,z26,z2,z3,z161,z6]),(0,[z0,z1,z2,z3,z200,z4,z6]),(0,[z0,z1,z2,z3,z201,z4,z6]),(0,[z0,z1,z128,z2,z3,z4,z6]),(0,[z202,z11,z0,z1,z2,z4,z6]),(0,[z0,z1,z2,z3,z203,z4,z6])],[(0,[z0,z1,z2,z3,z4,z204,z6]),(0,[z21,z0,z1,z2,z3,z4,z44]),(0,[z205,z0,z1,z2,z3,z4,z6]),(0,[z73,z0,z1,z16,z2,z3,z6]),(0,[z0,z1,z2,z3,z206,z4,z6])],[(0,[z0,z1,z2,z3,z4,z207,z6]),(0,[z0,z1,z2,z3,z4,z83,z188]),(0,[z0,z208,z1,z2,z3,z4,z6])],[(0,[z209,z11,z0,z1,z2,z4,z6]),(0,[z0,z1,z2,z3,z210,z4,z6])],[(0,[z28,z0,z1,z2,z3,z14,z6])],[(0,[z0,z1,z2,z211,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z212]),(1,[z0,z1,z16,z2,z3,z6])],[(0,[z213,z0,z1,z2,z3,z4,z6])],[(0,[z74,z0,z1,z2,z214,z4,z6]),(0,[z215,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z63,z3,z4,z188])],[(0,[z15,z0,z18,z2,z3,z4,z6]),(0,[z216,z0,z1,z123,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z217,z6]),(0,[z0,z1,z2,z3,z4,z218,z6])],[(0,[z94,z1,z22,z2,z3,z4,z6]),(0,[z219,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z91,z47]),(0,[z0,z1,z2,z4,z188,z6,z38]),(0,[z127,z0,z1,z2,z76,z4,z6])],[(0,[z0,z1,z16,z2,z3,z6,z82])],[(1,[z0,z1,z2,z134,z4,z6]),(1,[z11,z0,z220,z2,z4,z6])],[(0,[z101,z0,z1,z2,z3,z4,z83]),(1,[z221,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z12,z4,z6,z32]),(0,[z127,z222,z1,z2,z3,z4,z6])],[(0,[z11,z80,z0,z1,z2,z4,z6]),(0,[z0,z223,z1,z2,z3,z4,z6]),(0,[z0,z116,z1,z16,z2,z3,z6]),(0,[z224,z0,z1,z2,z3,z4,z6])],[(0,[z21,z0,z1,z2,z3,z4,z6]),(0,[z11,z0,z142,z1,z2,z4,z6]),(0,[z0,z1,z2,z225,z3,z4,z6]),(1,[z0,z1,z2,z3,z155,z6])]],
   [[(0,[z226,z0,z1,z2,z3,z4,z6]),(0,[z227,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z30,z3,z4,z33,z6])],[(0,[z0,z1,z228,z2,z3,z4,z6]),(0,[z74,z0,z1,z2,z171,z4,z6])],[(0,[z28,z1,z2,z3,z79,z4,z6]),(0,[z11,z0,z1,z2,z17,z4,z6]),(0,[z11,z0,z1,z2,z2,z4,z6])],[(0,[z0,z1,z2,z3,z229,z4,z6]),(0,[z0,z1,z2,z3,z230,z4,z6]),(0,[z0,z1,z26,z2,z3,z12,z6]),(0,[z37,z0,z1,z2,z3,z217,z6]),(0,[z131,z0,z1,z30,z2,z4,z6]),(0,[z62,z0,z1,z231,z3,z4,z6])],[(0,[z28,z0,z1,z2,z4,z14,z6]),(0,[z232,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z233,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z17,z14,z6]),(0,[z0,z142,z1,z2,z3,z29,z6])],[(0,[z0,z2,z3,z197,z161,z4,z6]),(0,[z0,z1,z234,z2,z3,z4,z6])],[(0,[z0,z1,z16,z2,z3,z83,z6]),(1,[z0,z1,z2,z3,z235,z6]),(0,[z236,z11,z0,z1,z2,z4,z6])],[(0,[z43,z1,z2,z3,z161,z4,z6]),(0,[z237,z11,z0,z1,z2,z4,z6])],[(0,[z238,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z60,z6]),(1,[z11,z0,z1,z16,z2,z6])],[(0,[z0,z106,z115,z2,z3,z4,z6]),(0,[z0,z1,z16,z2,z78,z3,z6]),(0,[z0,z1,z2,z3,z14,z239,z6])],[(0,[z0,z1,z2,z123,z12,z4,z6]),(0,[z0,z1,z2,z3,z31,z33,z6])],[(0,[z21,z1,z2,z3,z161,z4,z6]),(0,[z0,z1,z2,z3,z4,z240,z6])],[(0,[z0,z1,z2,z63,z3,z33,z6])],[(0,[z0,z106,z1,z2,z12,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z241]),(0,[z0,z1,z2,z3,z4,z242,z6])],[(0,[z0,z1,z2,z3,z243,z4,z6])],[(0,[z244,z0,z1,z2,z3,z4,z6])]],
   [[(0,[z0,z1,z2,z3,z245,z4,z6]),(1,[z0,z1,z246,z2,z3,z6]),(0,[z247,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z188,z6])],[(0,[z248,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z249,z2,z3,z6]),(0,[z11,z0,z1,z2,z4,z14,z6]),(0,[z0,z1,z26,z250,z2,z3,z6])],[(0,[z251,z0,z1,z2,z3,z4,z6]),(0,[z101,z0,z1,z26,z2,z3,z6]),(0,[z0,z1,z2,z3,z191,z4,z6]),(0,[z0,z1,z2,z63,z3,z4,z38])],[(0,[z0,z1,z2,z3,z12,z33,z6]),(0,[z252,z11,z0,z1,z2,z4,z6]),(0,[z74,z0,z1,z99,z3,z4,z6])],[(0,[z43,z0,z1,z2,z3,z33,z6]),(0,[z1,z22,z2,z3,z161,z4,z6]),(1,[z0,z119,z2,z3,z4,z6]),(0,[z62,z0,z253,z2,z3,z4,z6])],[(0,[z0,z1,z2,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z254,z4,z6]),(0,[z0,z1,z2,z255,z3,z4,z6])],[(0,[z0,z1,z2,z256,z3,z4,z6]),(0,[z0,z1,z2,z3,z257,z4,z6]),(0,[z0,z258,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z259]),(0,[z0,z1,z16,z2,z63,z3,z6])],[(0,[z260,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z16,z99,z2,z3,z6])],[(0,[z0,z1,z26,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z4,z166,z6])],[(0,[z0,z1,z261,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z262,z6]),(0,[z71,z11,z0,z1,z2,z4,z6]),(0,[z0,z1,z2,z3,z33,z188,z6])],[(0,[z1,z2,z3,z161,z4,z6,z82]),(0,[z28,z0,z1,z2,z78,z4,z6]),(0,[z263,z0,z1,z2,z3,z4,z6])],[],[(0,[z0,z1,z115,z26,z2,z3,z6]),(0,[z0,z1,z2,z3,z4,z6,z264]),(0,[z0,z265,z1,z2,z3,z33,z6]),(0,[z0,z1,z152,z2,z3,z33,z6]),(0,[z0,z1,z30,z2,z3,z180,z6]),(0,[z0,z1,z266,z2,z3,z4,z6]),(1,[z0,z267,z2,z3,z4,z6])],[(0,[z268,z0,z1,z2,z3,z4,z6])],[(0,[z236,z0,z1,z3,z161,z4,z6]),(0,[z0,z269,z1,z2,z3,z4,z6]),(0,[z0,z1,z270,z2,z12,z4,z6]),(1,[z0,z1,z149,z2,z12,z6]),(0,[z0,z1,z26,z152,z2,z3,z6]),(0,[z0,z1,z271,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z272,z4,z6])]],
   [[(0,[z273,z0,z1,z2,z3,z4,z6]),(0,[z274,z0,z1,z2,z3,z4,z6]),(0,[z275,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z63,z3,z27,z6]),(0,[z0,z1,z276,z2,z3,z4,z6])],[(0,[z94,z0,z1,z16,z2,z3,z6]),(0,[z0,z1,z16,z2,z3,z60,z6]),(1,[z11,z0,z1,z2,z277,z6]),(0,[z0,z1,z2,z3,z33,z166,z6])],[],[(0,[z101,z55,z1,z2,z3,z4,z6]),(0,[z21,z0,z1,z2,z3,z177,z6]),(0,[z0,z1,z278,z2,z3,z4,z6]),(0,[z54,z0,z1,z46,z3,z4,z6]),(0,[z279,z0,z1,z2,z3,z4,z6]),(0,[z74,z0,z1,z2,z3,z4,z6])],[(0,[z280,z0,z1,z2,z3,z4,z6]),(0,[z0,z64,z1,z2,z3,z4,z6])],[(0,[z42,z0,z1,z16,z2,z3,z6]),(0,[z0,z1,z26,z2,z3,z104,z6]),(0,[z0,z1,z2,z3,z4,z172,z91]),(1,[z1,z2,z3,z4,z6,z53])],[(0,[z281,z0,z1,z2,z3,z4,z6]),(0,[z127,z0,z142,z1,z2,z3,z6])],[(0,[z11,z0,z1,z2,z78,z4,z6]),(0,[z11,z0,z1,z2,z4,z7,z6]),(0,[z0,z1,z2,z3,z4,z6,z282]),(0,[z0,z222,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z283,z6]),(0,[z138,z0,z1,z2,z3,z4,z6])],[(0,[z94,z0,z1,z2,z3,z4,z6]),(0,[z284,z0,z1,z2,z3,z4,z6]),(0,[z37,z0,z1,z2,z3,z4,z172]),(0,[z0,z1,z2,z3,z4,z6,z285]),(0,[z0,z1,z2,z3,z4,z286,z6])],[(0,[z0,z1,z2,z4,z6,z287,z82]),(0,[z0,z1,z2,z3,z14,z102,z6])],[(0,[z103,z0,z1,z2,z3,z7,z6])],[(0,[z0,z1,z26,z22,z2,z3,z6]),(1,[z0,z1,z2,z3,z194,z6])],[(0,[z0,z1,z2,z3,z4,z288,z6]),(0,[z236,z0,z1,z2,z12,z4,z6])],[(0,[z0,z1,z2,z3,z33,z6,z82]),(0,[z237,z0,z1,z2,z12,z4,z6]),(0,[z0,z1,z149,z26,z2,z3,z6])],[(0,[z24,z0,z1,z2,z3,z33,z6]),(1,[z289,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z4,z6,z290])]],
   [[(0,[z291,z0,z1,z2,z3,z4,z6]),(0,[z292,z0,z1,z2,z3,z4,z6]),(1,[z54,z0,z3,z66,z4,z6]),(0,[z0,z1,z2,z293,z3,z4,z6]),(1,[z0,z1,z30,z3,z33,z6])],[(0,[z294,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z14,z6,z38])],[(0,[z43,z55,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z84]),(0,[z0,z1,z26,z2,z3,z17,z6]),(0,[z295,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z296]),(0,[z0,z1,z123,z297,z3,z4,z6]),(0,[z298,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z26,z2,z3,z6,z92]),(1,[z0,z1,z157,z3,z4,z6])],[(0,[z0,z1,z2,z299,z3,z4,z6]),(0,[z0,z1,z2,z12,z104,z4,z6]),(0,[z0,z1,z2,z104,z300,z4,z6]),(0,[z54,z0,z18,z2,z3,z4,z6]),(1,[z0,z142,z2,z3,z72,z6]),(0,[z11,z0,z1,z2,z63,z4,z6]),(0,[z0,z1,z2,z3,z31,z4,z6])],[(0,[z11,z0,z1,z99,z2,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z301])],[(0,[z0,z142,z1,z16,z2,z3,z6]),(0,[z0,z1,z2,z63,z3,z4,z6])],[(0,[z0,z1,z2,z3,z302,z4,z6])],[(0,[z103,z0,z1,z2,z3,z104,z6])],[(0,[z0,z1,z2,z3,z33,z83,z6]),(0,[z0,z1,z2,z3,z14,z14,z6]),(1,[z0,z1,z2,z63,z4,z188])],[(0,[z42,z0,z19,z2,z3,z4,z6]),(0,[z21,z0,z1,z16,z2,z3,z6]),(1,[z303,z0,z1,z2,z4,z6]),(1,[z0,z1,z2,z3,z4,z148]),(0,[z0,z1,z26,z2,z3,z72,z6]),(0,[z0,z1,z3,z4,z172,z6,z47])],[(0,[z101,z1,z2,z3,z161,z4,z6]),(0,[z0,z1,z2,z3,z304,z4,z6])],[(0,[z24,z0,z1,z26,z2,z3,z6]),(0,[z11,z0,z1,z2,z66,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z305])],[(0,[z0,z1,z2,z12,z4,z6,z91]),(0,[z0,z1,z2,z3,z12,z4,z6])],[(0,[z43,z0,z1,z2,z3,z4,z6]),(0,[z55,z1,z2,z3,z4,z6,z82]),(0,[z0,z1,z306,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z66,z14,z6]),(0,[z0,z142,z1,z2,z3,z4,z6]),(1,[z37,z0,z1,z3,z4,z47]),(0,[z0,z1,z189,z2,z3,z4,z6])],[(0,[z73,z0,z1,z2,z3,z14,z6]),(0,[z0,z1,z2,z3,z307,z4,z6]),(0,[z15,z11,z0,z1,z2,z4,z6]),(1,[z0,z1,z16,z2,z14,z6])]],
   [[(0,[z0,z1,z2,z3,z308,z4,z6]),(0,[z309,z0,z1,z2,z3,z4,z6]),(0,[z71,z0,z1,z2,z12,z4,z6]),(0,[z310,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z16,z2,z12,z6])],[],[(0,[z0,z1,z311,z2,z3,z4,z6]),(0,[z0,z1,z2,z12,z4,z33,z6]),(0,[z0,z1,z2,z3,z4,z277,z6])],[(0,[z42,z0,z46,z2,z3,z4,z6]),(0,[z0,z19,z1,z16,z2,z3,z6]),(0,[z0,z1,z2,z3,z4,z6,z50])],[(1,[z0,z106,z46,z3,z4,z6]),(1,[z15,z0,z2,z17,z4,z6]),(0,[z0,z19,z1,z2,z3,z4,z60]),(0,[z312,z0,z1,z2,z3,z4,z6]),(0,[z11,z0,z1,z2,z3,z14,z6]),(0,[z313,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z14,z6])],[(0,[z0,z1,z26,z2,z3,z14,z6]),(0,[z37,z0,z1,z2,z3,z4,z47]),(0,[z127,z0,z314,z2,z3,z4,z6])],[(0,[z0,z1,z315,z2,z3,z33,z6]),(0,[z0,z265,z1,z2,z3,z4,z6]),(0,[z0,z1,z26,z2,z3,z135,z6])],[(1,[z0,z19,z2,z3,z4,z60])],[(0,[z0,z1,z2,z3,z4,z316,z6]),(0,[z317,z0,z1,z22,z2,z4,z6]),(0,[z318,z0,z1,z2,z3,z4,z6]),(0,[z101,z0,z1,z2,z3,z33,z6]),(0,[z0,z108,z1,z2,z3,z14,z6])],[(0,[z11,z0,z1,z2,z4,z72,z6]),(0,[z0,z1,z2,z3,z319,z4,z6]),(0,[z127,z0,z271,z2,z3,z4,z6])],[(0,[z0,z320,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z321,z4,z6]),(0,[z322,z0,z1,z2,z3,z4,z6]),(0,[z37,z0,z323,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z324]),(0,[z0,z1,z2,z157,z3,z4,z6])],[(0,[z0,z1,z2,z3,z325,z4,z6]),(0,[z0,z1,z2,z326,z3,z4,z6]),(0,[z0,z19,z1,z2,z3,z4,z6]),(1,[z0,z1,z3,z33,z6,z47])],[],[(1,[z313,z0,z1,z2,z4,z6])],[(1,[z94,z1,z22,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z327,z6])],[(0,[z0,z19,z2,z3,z17,z4,z6]),(0,[z0,z1,z122,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z32])]],
   [[(0,[z80,z0,z1,z2,z3,z33,z6]),(0,[z328,z0,z1,z2,z3,z4,z6]),(0,[z15,z0,z1,z2,z123,z4,z6]),(0,[z71,z0,z1,z2,z3,z70,z6])],[],[(0,[z0,z1,z115,z2,z3,z33,z6]),(0,[z73,z1,z2,z3,z4,z6,z82])],[(0,[z0,z1,z2,z3,z4,z6,z329]),(0,[z0,z1,z330,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z33,z60,z6]),(0,[z0,z1,z125,z2,z3,z4,z6])],[(0,[z0,z1,z2,z331,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z332,z6])],[(1,[z0,z1,z2,z76,z4,z6])],[(1,[z317,z0,z1,z2,z4,z6]),(0,[z28,z0,z1,z2,z79,z4,z6]),(0,[z0,z333,z1,z2,z3,z4,z6]),(0,[z37,z0,z1,z2,z12,z4,z6]),(0,[z0,z1,z334,z2,z3,z4,z6]),(0,[z0,z1,z266,z16,z2,z3,z6]),(0,[z62,z335,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z336,z6]),(0,[z103,z0,z1,z2,z3,z14,z6]),(0,[z0,z1,z16,z2,z3,z31,z6])],[(1,[z337,z0,z2,z3,z4,z6]),(0,[z0,z1,z338,z2,z3,z4,z6]),(0,[z0,z1,z46,z2,z3,z14,z6]),(0,[z0,z1,z2,z3,z4,z6,z47]),(0,[z0,z1,z2,z3,z339,z4,z6])],[(0,[z0,z1,z2,z3,z4,z124,z6]),(0,[z0,z1,z340,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z159,z6]),(0,[z0,z1,z341,z2,z3,z4,z6])],[(0,[z317,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z128,z3,z12,z4,z6])],[(0,[z0,z342,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z104,z33,z6]),(0,[z343,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z30,z2,z3,z4,z172])],[(0,[z80,z0,z1,z26,z2,z3,z6]),(0,[z344,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z70,z6])],[(0,[z62,z11,z0,z1,z2,z4,z6]),(0,[z74,z0,z1,z16,z2,z3,z6]),(1,[z0,z1,z13,z2,z3,z6])],[(0,[z345,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z249,z2,z3,z4,z6]),(0,[z0,z106,z2,z3,z4,z6,z91]),(0,[z0,z1,z2,z3,z346,z4,z6])]],
   [[(0,[z0,z1,z347,z2,z3,z4,z6]),(0,[z54,z0,z1,z2,z307,z4,z6]),(0,[z0,z1,z2,z3,z348,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z349])],[(0,[z0,z1,z2,z3,z4,z6,z350]),(0,[z0,z106,z1,z3,z66,z4,z6]),(0,[z209,z0,z1,z2,z3,z33,z6])],[(0,[z0,z351,z1,z2,z3,z4,z6]),(1,[z139,z0,z1,z16,z2,z6])],[(0,[z0,z1,z2,z3,z31,z4,z70])],[(0,[z352,z0,z1,z2,z3,z4,z6]),(0,[z11,z0,z1,z2,z79,z4,z6]),(0,[z284,z0,z1,z16,z2,z3,z6])],[(0,[z0,z1,z26,z2,z3,z83,z6])],[(0,[z0,z1,z353,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z354,z6]),(0,[z0,z1,z2,z3,z79,z14,z6]),(0,[z15,z0,z1,z2,z12,z4,z6]),(1,[z0,z1,z122,z2,z3,z6]),(0,[z0,z1,z16,z2,z12,z4,z6]),(1,[z0,z1,z152,z2,z14,z6])],[(0,[z0,z1,z2,z3,z4,z6,z355]),(0,[z0,z1,z2,z3,z4,z6,z356]),(1,[z0,z1,z26,z3,z33,z6]),(0,[z74,z0,z1,z3,z4,z6,z47]),(0,[z0,z357,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z358]),(0,[z0,z1,z16,z2,z3,z6,z32])],[(0,[z359,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z51,z6])],[(0,[z0,z360,z1,z2,z3,z4,z6]),(0,[z361,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z362,z4,z6]),(0,[z0,z1,z363,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z364,z6])],[(0,[z103,z1,z2,z3,z4,z6,z82]),(0,[z365,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z93,z4,z6])],[],[(0,[z0,z1,z3,z12,z4,z6,z47]),(0,[z295,z0,z1,z16,z2,z3,z6])],[(0,[z0,z1,z366,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z367,z4,z6]),(0,[z0,z1,z2,z3,z368,z4,z6]),(0,[z369,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z41,z3,z4,z6]),(0,[z370,z0,z1,z2,z3,z4,z6])]],
   [[(0,[z0,z1,z2,z371,z3,z4,z6]),(0,[z0,z1,z2,z3,z372,z4,z6]),(0,[z0,z1,z99,z2,z3,z14,z6])],[],[(0,[z101,z0,z1,z2,z3,z4,z6]),(0,[z0,z373,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z172,z6]),(0,[z0,z1,z16,z2,z3,z6,z47])],[(0,[z42,z0,z1,z2,z3,z14,z6]),(0,[z127,z103,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z374,z12,z4,z6]),(0,[z37,z11,z0,z1,z2,z4,z6]),(0,[z375,z0,z1,z2,z3,z4,z6])],[(0,[z11,z43,z0,z1,z2,z4,z6]),(1,[z24,z1,z2,z3,z7,z6]),(0,[z11,z0,z1,z2,z4,z83,z6])],[(0,[z0,z1,z376,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z377]),(0,[z0,z1,z378,z2,z3,z4,z6]),(0,[z237,z0,z1,z2,z3,z33,z6]),(0,[z0,z1,z3,z4,z33,z6,z47]),(0,[z0,z1,z26,z2,z63,z3,z6])],[(0,[z0,z1,z2,z3,z379,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z380]),(0,[z0,z1,z26,z99,z2,z3,z6]),(0,[z0,z1,z16,z2,z3,z70,z6])],[],[(1,[z0,z1,z381,z2,z3,z6]),(0,[z0,z1,z30,z2,z3,z4,z47])],[(0,[z43,z0,z1,z16,z2,z3,z6]),(0,[z73,z0,z1,z2,z3,z4,z82]),(0,[z0,z1,z128,z2,z3,z14,z6]),(0,[z0,z1,z16,z128,z2,z3,z6])],[(0,[z0,z1,z382,z2,z3,z4,z6]),(0,[z54,z11,z0,z1,z2,z4,z6]),(0,[z383,z0,z1,z2,z3,z33,z6])],[(0,[z0,z1,z2,z3,z384,z4,z6]),(1,[z0,z1,z2,z3,z6,z112]),(0,[z0,z1,z2,z3,z33,z172,z6])],[(0,[z0,z1,z115,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z385,z4,z6]),(0,[z139,z11,z0,z1,z2,z4,z6]),(0,[z0,z1,z2,z3,z210,z14,z6]),(0,[z0,z1,z2,z3,z14,z188,z6]),(0,[z0,z1,z386,z2,z3,z4,z6])],[(0,[z387,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z388])],[(0,[z0,z1,z26,z3,z4,z33,z6])],[(0,[z0,z1,z2,z3,z389,z4,z6]),(0,[z74,z0,z1,z30,z3,z4,z6])]],
   [[(0,[z0,z1,z26,z2,z3,z60,z6]),(0,[z0,z1,z2,z3,z194,z4,z6]),(1,[z138,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z390,z6])],[(0,[z236,z0,z1,z26,z2,z3,z6])],[(0,[z0,z1,z2,z3,z4,z391,z6]),(0,[z237,z0,z1,z26,z2,z3,z6]),(0,[z0,z1,z2,z3,z392,z4,z6])],[(0,[z28,z0,z1,z2,z3,z262,z6]),(0,[z393,z0,z1,z2,z3,z4,z6]),(0,[z394,z0,z1,z26,z2,z3,z6]),(0,[z0,z1,z16,z30,z2,z3,z6]),(0,[z219,z0,z1,z2,z3,z14,z6])],[(0,[z127,z11,z0,z1,z2,z4,z6]),(0,[z0,z395,z1,z2,z3,z4,z6]),(0,[z396,z0,z1,z26,z2,z3,z6]),(0,[z0,z1,z2,z3,z14,z166,z6])],[(0,[z0,z1,z397,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z72,z6,z91]),(0,[z62,z0,z1,z2,z12,z4,z6]),(1,[z0,z1,z231,z3,z4,z6])],[(0,[z42,z1,z2,z3,z4,z6,z82]),(0,[z0,z55,z1,z2,z12,z4,z6]),(0,[z398,z0,z1,z2,z3,z4,z6]),(0,[z57,z11,z0,z1,z2,z4,z6]),(0,[z0,z1,z26,z2,z2,z3,z6]),(0,[z399,z0,z1,z2,z3,z4,z6]),(0,[z400,z0,z1,z2,z3,z4,z6])],[(0,[z236,z0,z1,z22,z3,z4,z6])],[(0,[z0,z1,z401,z2,z3,z4,z6]),(0,[z21,z0,z1,z2,z3,z14,z6]),(0,[z0,z1,z2,z3,z402,z4,z6]),(0,[z0,z1,z2,z3,z4,z403,z6]),(0,[z0,z1,z2,z3,z404,z4,z6]),(1,[z0,z1,z2,z3,z135,z6]),(0,[z0,z1,z26,z2,z3,z188,z6])],[(0,[z28,z0,z1,z405,z3,z4,z6]),(0,[z101,z1,z2,z3,z4,z7,z6]),(0,[z0,z19,z2,z3,z66,z4,z6]),(1,[z0,z1,z2,z406,z4,z6]),(0,[z0,z142,z2,z3,z4,z72,z6]),(0,[z0,z1,z152,z2,z3,z4,z6])],[(0,[z28,z0,z1,z2,z4,z188,z6]),(0,[z0,z1,z407,z2,z3,z4,z6]),(0,[z0,z18,z1,z2,z123,z4,z6]),(0,[z0,z1,z2,z12,z29,z4,z6]),(0,[z0,z1,z30,z2,z12,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z408]),(0,[z0,z1,z2,z3,z300,z4,z6]),(0,[z0,z1,z16,z2,z3,z172,z6])],[(0,[z0,z1,z2,z3,z4,z6,z409]),(0,[z289,z0,z1,z2,z3,z6,z82]),(1,[z0,z410,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z411,z6]),(0,[z0,z1,z2,z3,z4,z6,z412])],[(0,[z80,z1,z2,z78,z3,z4,z6]),(0,[z139,z0,z1,z2,z123,z4,z6]),(0,[z127,z160,z1,z2,z3,z4,z6])],[(0,[z0,z1,z149,z2,z3,z4,z6])],[(0,[z0,z1,z26,z2,z3,z79,z6]),(0,[z413,z0,z1,z2,z3,z4,z6]),(0,[z11,z0,z1,z2,z4,z60,z6]),(0,[z414,z0,z1,z2,z3,z4,z6]),(0,[z127,z0,z1,z2,z3,z4,z32])]],
   [[(0,[z28,z11,z0,z1,z2,z4,z6]),(0,[z0,z1,z16,z2,z123,z3,z6])],[(0,[z0,z1,z2,z3,z14,z6,z82]),(0,[z0,z1,z2,z3,z4,z6,z287]),(0,[z0,z1,z415,z2,z3,z4,z6]),(1,[z190,z0,z1,z2,z4,z6]),(0,[z0,z1,z416,z2,z3,z4,z6]),(0,[z417,z11,z0,z1,z2,z4,z6])],[(0,[z0,z174,z1,z2,z3,z4,z6]),(0,[z71,z0,z2,z3,z4,z6,z91])],[(0,[z0,z1,z2,z3,z6,z418,z82])],[(0,[z24,z0,z1,z16,z2,z3,z6]),(0,[z0,z1,z2,z123,z3,z33,z6]),(0,[z71,z0,z1,z26,z2,z3,z6])],[(0,[z419,z0,z1,z2,z3,z4,z6])],[(0,[z0,z19,z2,z3,z4,z72,z6]),(0,[z420,z0,z1,z2,z3,z4,z6]),(1,[z0,z253,z2,z3,z4,z6])],[(0,[z43,z0,z46,z2,z3,z4,z6]),(0,[z62,z28,z0,z1,z2,z4,z6]),(0,[z73,z101,z1,z2,z3,z4,z6]),(0,[z0,z106,z1,z2,z3,z33,z6]),(0,[z11,z0,z19,z1,z2,z4,z6]),(0,[z11,z0,z1,z128,z2,z4,z6]),(0,[z11,z0,z1,z2,z4,z188,z6])],[(0,[z421,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z422,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z7,z33,z6]),(1,[z0,z1,z2,z3,z180,z6]),(0,[z423,z0,z1,z2,z3,z4,z6])],[(0,[z424,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z425,z2,z3,z4,z6])],[(0,[z0,z1,z426,z2,z3,z4,z6]),(0,[z0,z410,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z33,z6,z32])],[(0,[z0,z18,z115,z2,z3,z4,z6]),(0,[z24,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z14,z83,z6]),(1,[z222,z1,z2,z3,z4,z6]),(0,[z0,z427,z1,z2,z3,z4,z6])],[(0,[z0,z1,z26,z2,z3,z6,z82]),(0,[z0,z1,z2,z3,z428,z4,z6]),(0,[z11,z11,z0,z1,z2,z4,z6]),(0,[z127,z0,z1,z2,z3,z31,z6])],[(0,[z236,z0,z106,z1,z3,z4,z6]),(0,[z0,z1,z2,z3,z70,z6,z32])],[(0,[z0,z1,z16,z429,z2,z3,z6]),(0,[z430,z0,z1,z2,z3,z4,z6])]],
   [[(0,[z0,z18,z1,z2,z12,z4,z6]),(0,[z394,z0,z1,z2,z3,z4,z6])],[(0,[z0,z431,z1,z2,z3,z4,z6]),(0,[z54,z0,z1,z2,z12,z4,z6]),(0,[z0,z1,z246,z46,z2,z3,z6]),(0,[z11,z0,z1,z30,z2,z4,z6]),(0,[z396,z0,z1,z2,z3,z4,z6]),(1,[z0,z314,z2,z3,z4,z6])],[],[(0,[z0,z1,z2,z3,z432,z4,z6]),(0,[z139,z0,z1,z2,z12,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z433])],[(1,[z0,z1,z2,z299,z4,z6]),(0,[z0,z106,z1,z26,z2,z3,z6]),(0,[z383,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z78,z12,z4,z6]),(0,[z0,z1,z2,z3,z33,z6,z47]),(0,[z361,z0,z1,z16,z2,z3,z6]),(1,[z0,z271,z2,z3,z4,z6])],[(1,[z0,z1,z12,z161,z4,z6]),(0,[z0,z1,z22,z2,z12,z4,z6]),(0,[z434,z0,z1,z2,z3,z4,z6]),(0,[z0,z435,z1,z2,z3,z4,z6])],[(0,[z0,z436,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z437,z4,z6])],[],[(0,[z0,z2,z3,z4,z60,z6,z91]),(0,[z0,z1,z2,z12,z4,z6,z38]),(0,[z0,z1,z2,z3,z33,z70,z6])],[(0,[z438,z0,z1,z2,z3,z4,z6])],[(0,[z439,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z26,z2,z78,z3,z6]),(0,[z0,z1,z2,z3,z4,z440,z6]),(0,[z127,z0,z1,z2,z12,z4,z6]),(0,[z0,z441,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z442,z4,z6]),(0,[z11,z0,z1,z2,z4,z6,z82]),(0,[z74,z0,z1,z2,z3,z14,z6]),(0,[z0,z1,z2,z3,z443,z4,z6]),(0,[z444,z0,z1,z2,z3,z4,z6])],[(1,[z0,z1,z22,z12,z4,z6]),(0,[z101,z0,z1,z16,z2,z3,z6]),(0,[z445,z0,z1,z2,z3,z4,z6]),(0,[z57,z0,z1,z2,z12,z4,z6]),(0,[z446,z0,z1,z2,z12,z4,z6]),(0,[z0,z447,z1,z2,z3,z4,z6]),(0,[z127,z0,z1,z2,z3,z6,z32])],[(0,[z28,z0,z1,z306,z3,z4,z6]),(0,[z11,z0,z1,z2,z123,z4,z6]),(1,[z0,z1,z2,z187,z4,z6])],[(1,[z0,z448,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z449,z6])]],
   [[(0,[z103,z101,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z214,z3,z4,z6])],[(0,[z103,z11,z0,z1,z2,z4,z6]),(0,[z0,z1,z450,z2,z3,z33,z6])],[(1,[z42,z115,z2,z3,z4,z6]),(0,[z0,z55,z106,z2,z3,z4,z6]),(0,[z94,z0,z1,z2,z3,z14,z6]),(0,[z0,z1,z16,z46,z2,z3,z6]),(0,[z0,z1,z2,z3,z29,z33,z6]),(0,[z11,z0,z395,z1,z2,z4,z6])],[(0,[z0,z1,z451,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z452,z6]),(0,[z24,z1,z2,z3,z4,z7,z6]),(0,[z0,z1,z315,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z217,z6])],[(0,[z453,z11,z0,z1,z2,z4,z6])],[(0,[z80,z0,z1,z16,z2,z3,z6]),(0,[z0,z1,z2,z3,z4,z454,z6]),(0,[z0,z1,z2,z3,z455,z4,z6]),(0,[z37,z447,z1,z2,z3,z4,z6])],[(1,[z11,z0,z1,z2,z33,z6]),(0,[z0,z1,z231,z2,z3,z4,z6])],[(0,[z0,z1,z115,z16,z2,z3,z6]),(0,[z28,z0,z1,z2,z12,z4,z6]),(0,[z0,z1,z2,z3,z456,z4,z6]),(0,[z0,z1,z2,z3,z14,z60,z6]),(0,[z236,z0,z1,z2,z3,z33,z6]),(0,[z0,z1,z26,z2,z3,z31,z6]),(1,[z0,z323,z2,z3,z4,z6])],[(0,[z0,z1,z457,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z458,z4,z6])],[(1,[z0,z2,z3,z4,z6,z84]),(1,[z57,z0,z2,z3,z4,z91]),(0,[z459,z11,z0,z1,z2,z4,z6]),(0,[z11,z0,z1,z2,z3,z277,z6]),(0,[z0,z1,z460,z30,z2,z3,z6]),(0,[z461,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z418]),(0,[z15,z0,z1,z26,z2,z3,z6]),(0,[z0,z1,z16,z26,z2,z3,z6]),(0,[z0,z1,z429,z2,z3,z4,z6])],[(0,[z462,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z463,z4,z6]),(0,[z11,z0,z1,z2,z31,z4,z6])],[(0,[z0,z142,z1,z2,z3,z72,z6]),(0,[z57,z0,z2,z3,z4,z6,z91]),(0,[z464,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z12,z161,z4,z6]),(0,[z80,z0,z1,z2,z3,z4,z6]),(0,[z465,z0,z1,z2,z3,z4,z6]),(0,[z466,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z467,z4,z6]),(0,[z0,z1,z2,z3,z31,z14,z6])],[(0,[z0,z1,z2,z123,z3,z4,z6]),(0,[z313,z0,z1,z99,z2,z4,z6]),(0,[z62,z0,z1,z468,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z469,z6]),(0,[z0,z1,z2,z63,z3,z14,z6])]],
   [[],[(0,[z0,z1,z2,z470,z3,z4,z6]),(0,[z0,z1,z2,z3,z471,z4,z6]),(0,[z472,z0,z1,z2,z3,z4,z6]),(0,[z28,z0,z1,z2,z3,z4,z377]),(0,[z0,z106,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z473,z33,z6])],[(0,[z0,z1,z2,z474,z12,z4,z6]),(0,[z0,z1,z2,z3,z475,z4,z6])],[(0,[z0,z1,z2,z3,z4,z476,z6])],[(0,[z1,z115,z2,z3,z161,z4,z6]),(1,[z0,z106,z1,z12,z4,z6]),(0,[z0,z1,z2,z406,z3,z4,z6]),(0,[z0,z2,z3,z29,z4,z72,z6]),(0,[z11,z0,z1,z2,z12,z4,z6])],[(0,[z477,z0,z1,z2,z3,z4,z6]),(0,[z94,z1,z2,z3,z4,z6,z82]),(0,[z478,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z26,z2,z12,z4,z6])],[(0,[z101,z1,z2,z3,z79,z4,z6]),(1,[z0,z1,z2,z307,z4,z6]),(0,[z0,z1,z2,z3,z4,z479,z6]),(0,[z0,z1,z2,z3,z12,z14,z6]),(0,[z196,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z480]),(0,[z0,z1,z481,z2,z3,z4,z6])],[(0,[z43,z0,z1,z2,z3,z14,z6]),(0,[z0,z142,z1,z2,z3,z14,z6]),(0,[z482,z0,z1,z2,z3,z4,z6]),(0,[z127,z0,z1,z2,z339,z4,z6])],[(0,[z483,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z22,z2,z3,z452,z6]),(0,[z0,z1,z2,z3,z104,z4,z6]),(0,[z0,z1,z484,z2,z3,z4,z6]),(0,[z485,z0,z1,z2,z3,z4,z6]),(0,[z486,z0,z1,z2,z3,z4,z6]),(0,[z11,z0,z1,z2,z4,z277,z6]),(0,[z0,z1,z2,z3,z14,z70,z6]),(0,[z0,z1,z149,z16,z2,z3,z6]),(0,[z62,z0,z1,z2,z3,z487,z6])],[(0,[z0,z1,z2,z78,z3,z454,z6]),(0,[z71,z0,z1,z2,z3,z33,z6])],[(0,[z42,z101,z1,z2,z3,z4,z6]),(0,[z202,z0,z1,z2,z3,z4,z6]),(1,[z0,z488,z2,z3,z4,z6]),(0,[z11,z0,z488,z2,z3,z4,z6])],[(0,[z489,z0,z1,z2,z3,z4,z6]),(1,[z28,z1,z2,z79,z4,z6]),(0,[z0,z1,z490,z2,z3,z4,z6])],[(0,[z0,z55,z1,z2,z3,z33,z6]),(0,[z0,z1,z491,z2,z3,z4,z6]),(0,[z0,z1,z26,z2,z3,z332,z6]),(0,[z0,z1,z2,z3,z4,z492,z6])],[(0,[z0,z1,z493,z2,z3,z4,z6]),(1,[z0,z1,z2,z17,z14,z6]),(0,[z0,z1,z2,z3,z4,z6,z494]),(0,[z209,z0,z1,z2,z3,z4,z6])],[(1,[z236,z11,z0,z1,z4,z6]),(0,[z0,z1,z220,z2,z3,z4,z6]),(0,[z0,z1,z30,z2,z392,z4,z6]),(0,[z0,z1,z2,z63,z4,z14,z6])]],
   [[(0,[z11,z0,z1,z46,z2,z4,z6])],[(0,[z43,z0,z19,z2,z3,z4,z6]),(0,[z495,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z26,z2,z3,z6,z47])],[(0,[z0,z1,z2,z3,z4,z496,z6]),(0,[z0,z1,z2,z3,z4,z6,z91]),(0,[z0,z1,z270,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z166,z6]),(0,[z0,z1,z497,z2,z3,z4,z6])],[(1,[z0,z1,z2,z3,z262,z6]),(0,[z0,z1,z2,z3,z4,z188,z82])],[(0,[z0,z1,z498,z2,z3,z4,z6]),(0,[z0,z19,z1,z2,z3,z14,z6]),(0,[z0,z1,z499,z2,z3,z4,z6]),(0,[z423,z0,z1,z16,z2,z3,z6])],[(0,[z0,z1,z2,z3,z500,z4,z6]),(0,[z0,z1,z26,z2,z3,z70,z6]),(0,[z0,z501,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z502,z3,z4,z6]),(0,[z11,z0,z1,z2,z4,z6,z32]),(0,[z0,z503,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z82,z47]),(0,[z504,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z297,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z33,z6])],[(0,[z55,z1,z115,z2,z3,z4,z6]),(0,[z103,z0,z1,z2,z12,z4,z6]),(0,[z0,z1,z26,z128,z2,z3,z6]),(0,[z11,z0,z1,z26,z2,z4,z6])],[(1,[z0,z1,z405,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z505,z6]),(0,[z0,z1,z46,z2,z12,z4,z6]),(0,[z62,z0,z1,z26,z2,z3,z6]),(1,[z335,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z506])],[(0,[z0,z55,z1,z26,z2,z3,z6])],[(0,[z73,z11,z0,z1,z2,z4,z6]),(0,[z0,z1,z450,z2,z3,z4,z6])],[(0,[z337,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z507,z3,z4,z6]),(0,[z0,z1,z2,z123,z3,z508,z6]),(0,[z0,z1,z2,z3,z4,z508,z6]),(0,[z0,z1,z2,z3,z4,z509,z6]),(0,[z0,z19,z2,z3,z4,z60,z6])],[(0,[z42,z1,z115,z2,z3,z4,z6]),(1,[z0,z1,z2,z12,z33,z6])],[(0,[z510,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z511,z4,z6]),(0,[z0,z18,z2,z123,z3,z4,z6]),(0,[z37,z0,z512,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z14,z172,z6])],[(0,[z0,z1,z2,z3,z4,z513,z6]),(0,[z0,z1,z514,z2,z3,z4,z6]),(0,[z71,z0,z2,z3,z29,z4,z6])]],
   [[(0,[z0,z1,z16,z2,z3,z29,z6]),(0,[z0,z1,z2,z515,z3,z4,z6]),(1,[z11,z0,z1,z2,z4,z6]),(0,[z11,z0,z1,z2,z4,z6,z47]),(0,[z0,z1,z2,z3,z33,z33,z6])],[(0,[z516,z0,z1,z2,z3,z4,z6]),(0,[z236,z0,z1,z2,z3,z4,z6]),(0,[z37,z0,z1,z2,z3,z33,z6])],[(0,[z237,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z517,z4,z6]),(0,[z0,z1,z2,z3,z4,z518,z6]),(0,[z519,z0,z1,z2,z3,z33,z6]),(0,[z0,z1,z26,z30,z2,z3,z6])],[(0,[z520,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z49,z2,z3,z4,z6]),(0,[z11,z0,z18,z1,z2,z4,z6]),(0,[z0,z314,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z521,z4,z6]),(0,[z0,z522,z1,z2,z3,z4,z6]),(0,[z11,z0,z1,z2,z4,z70,z6])],[(0,[z0,z1,z2,z3,z161,z33,z6]),(1,[z0,z1,z2,z3,z31,z70])],[(0,[z0,z1,z2,z12,z17,z4,z6]),(0,[z0,z1,z16,z2,z3,z492,z6])],[(0,[z0,z1,z523,z2,z3,z4,z6])],[(0,[z21,z0,z1,z2,z299,z4,z6]),(0,[z103,z0,z1,z2,z3,z70,z6])],[(1,[z0,z1,z2,z3,z4,z524]),(0,[z0,z1,z2,z3,z525,z4,z6]),(1,[z160,z1,z2,z3,z4,z6])],[(0,[z526,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z26,z2,z3,z172,z6])],[(0,[z527,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z16,z2,z3,z6,z91]),(0,[z1,z2,z3,z4,z60,z6,z53]),(0,[z0,z1,z2,z3,z528,z4,z6]),(0,[z0,z1,z2,z3,z4,z27,z6])],[(1,[z0,z1,z2,z3,z229,z6]),(0,[z0,z1,z2,z78,z3,z33,z6]),(0,[z0,z1,z99,z3,z4,z33,z6]),(0,[z0,z1,z529,z26,z2,z3,z6])],[(0,[z0,z1,z2,z3,z530,z4,z6]),(0,[z0,z1,z22,z2,z3,z33,z6])],[(0,[z0,z1,z2,z3,z81,z4,z6]),(0,[z252,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z297,z3,z4,z6]),(0,[z0,z142,z1,z2,z187,z4,z6]),(0,[z37,z0,z1,z26,z2,z3,z6])],[(0,[z42,z0,z115,z2,z3,z4,z6]),(0,[z71,z0,z142,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z531])]],
   [[(0,[z0,z1,z2,z405,z3,z4,z6]),(0,[z15,z0,z1,z2,z3,z33,z6]),(0,[z59,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z16,z2,z3,z33,z6])],[(0,[z0,z1,z2,z3,z3,z4,z6]),(0,[z532,z0,z1,z2,z3,z33,z6])],[(0,[z0,z533,z1,z2,z3,z4,z6]),(0,[z28,z0,z1,z2,z3,z4,z534]),(0,[z535,z0,z1,z2,z3,z4,z6]),(0,[z0,z18,z2,z3,z4,z6,z91])],[(0,[z21,z0,z448,z2,z3,z4,z6])],[(0,[z0,z18,z1,z26,z2,z3,z6]),(0,[z71,z0,z1,z2,z3,z4,z6]),(0,[z536,z11,z0,z1,z2,z4,z6])],[(0,[z54,z0,z1,z3,z66,z4,z6]),(0,[z54,z0,z1,z26,z2,z3,z6]),(0,[z0,z1,z2,z3,z4,z6,z537])],[],[(0,[z139,z0,z1,z26,z2,z3,z6])],[(0,[z0,z538,z1,z2,z3,z4,z6]),(0,[z24,z0,z1,z2,z3,z7,z6]),(0,[z0,z1,z539,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z540])],[(0,[z0,z1,z2,z3,z4,z6,z541]),(0,[z0,z1,z2,z3,z542,z4,z6]),(0,[z11,z0,z1,z2,z4,z172,z6]),(0,[z74,z0,z1,z26,z3,z4,z6])],[(0,[z337,z0,z2,z3,z161,z4,z6]),(0,[z0,z1,z2,z543,z3,z4,z6]),(0,[z126,z0,z1,z2,z4,z6,z82])],[(0,[z28,z80,z1,z2,z3,z4,z6]),(0,[z101,z0,z1,z2,z3,z14,z6]),(0,[z54,z0,z1,z2,z3,z4,z469]),(0,[z0,z1,z2,z3,z474,z4,z6]),(0,[z62,z0,z1,z2,z3,z4,z188]),(0,[z0,z1,z2,z3,z4,z6,z38])],[(0,[z544,z0,z1,z2,z3,z4,z6]),(0,[z0,z106,z1,z16,z2,z3,z6]),(0,[z0,z1,z2,z3,z72,z14,z6]),(1,[z0,z1,z2,z3,z277,z6]),(0,[z0,z1,z2,z3,z4,z6,z545])],[(0,[z71,z0,z1,z2,z3,z29,z6])],[(1,[z0,z1,z306,z3,z4,z6]),(0,[z0,z1,z2,z3,z33,z6,z537]),(0,[z0,z1,z2,z3,z14,z6,z32]),(0,[z0,z1,z2,z3,z4,z6,z546])],[(0,[z0,z547,z1,z2,z3,z4,z6]),(0,[z127,z0,z1,z26,z2,z3,z6])]],
   [[(1,[z0,z1,z2,z63,z14,z6])],[(0,[z0,z18,z55,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z4,z6]),(0,[z57,z0,z1,z26,z2,z3,z6]),(0,[z0,z1,z2,z3,z4,z6,z548])],[(0,[z0,z1,z549,z2,z3,z4,z6]),(0,[z11,z0,z1,z115,z2,z4,z6]),(0,[z73,z0,z1,z2,z12,z4,z6])],[(0,[z0,z448,z1,z2,z3,z4,z6])],[(0,[z550,z0,z1,z2,z3,z4,z6]),(0,[z551,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z115,z2,z3,z14,z6]),(0,[z24,z0,z1,z2,z3,z104,z6]),(0,[z0,z1,z2,z3,z4,z6,z552]),(0,[z0,z488,z1,z2,z3,z4,z6]),(0,[z0,z1,z386,z2,z3,z14,z6]),(0,[z0,z1,z2,z3,z4,z109,z6])],[(0,[z0,z1,z2,z3,z4,z553,z6])],[(1,[z0,z1,z2,z12,z4,z6]),(0,[z11,z0,z1,z2,z194,z4,z6]),(0,[z0,z1,z2,z3,z4,z554,z6]),(0,[z0,z1,z512,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z555,z4,z6]),(0,[z0,z1,z2,z225,z12,z4,z6]),(0,[z0,z1,z2,z3,z14,z6,z47])],[(0,[z0,z1,z556,z2,z3,z4,z6]),(0,[z0,z1,z246,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z557]),(0,[z37,z0,z1,z2,z443,z4,z6])],[(0,[z558,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z308,z4,z6]),(0,[z0,z1,z26,z2,z3,z6,z32])],[(0,[z0,z1,z2,z12,z4,z7,z6]),(0,[z0,z1,z2,z3,z4,z83,z172]),(0,[z62,z140,z1,z2,z3,z4,z6])],[(0,[z0,z142,z1,z2,z406,z4,z6]),(0,[z0,z559,z1,z2,z3,z4,z6]),(0,[z519,z0,z1,z2,z3,z4,z6])],[(1,[z80,z0,z1,z2,z14,z6]),(0,[z0,z1,z2,z3,z560,z4,z6]),(0,[z216,z0,z1,z2,z3,z4,z6]),(0,[z561,z0,z1,z2,z3,z4,z6])],[(0,[z11,z24,z0,z1,z2,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z562]),(0,[z563,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z564,z2,z3,z4,z6]),(0,[z0,z1,z250,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z100])],[(0,[z42,z11,z0,z1,z2,z4,z6]),(0,[z0,z1,z2,z3,z161,z4,z6]),(0,[z0,z1,z2,z3,z4,z565,z6]),(0,[z103,z1,z2,z3,z104,z4,z6]),(0,[z1,z2,z3,z4,z83,z6,z82]),(0,[z62,z0,z1,z2,z3,z33,z6]),(0,[z139,z0,z1,z16,z2,z4,z6])]],
   [[(0,[z54,z0,z106,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z44]),(1,[z0,z1,z2,z3,z4,z377]),(0,[z0,z1,z2,z3,z4,z111,z6]),(0,[z0,z1,z566,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z567])],[(0,[z0,z1,z2,z3,z4,z132,z6]),(0,[z0,z1,z2,z568,z3,z4,z6]),(0,[z0,z1,z2,z3,z171,z4,z6]),(0,[z0,z1,z152,z2,z3,z14,z6]),(0,[z0,z1,z2,z63,z4,z188,z6])],[(0,[z11,z0,z220,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z569,z4,z6]),(0,[z0,z1,z2,z3,z4,z570,z6]),(0,[z57,z0,z1,z2,z3,z4,z91]),(0,[z0,z1,z30,z2,z3,z33,z6]),(0,[z0,z1,z2,z4,z14,z6,z38]),(0,[z0,z1,z16,z2,z3,z6,z38])],[(0,[z62,z0,z1,z2,z3,z4,z38])],[(0,[z0,z1,z2,z3,z4,z571,z6]),(0,[z0,z572,z1,z2,z3,z4,z6])],[(0,[z573,z0,z1,z2,z3,z33,z6])],[(0,[z0,z1,z2,z3,z574,z4,z6]),(0,[z244,z0,z1,z2,z12,z4,z6]),(0,[z0,z1,z149,z2,z3,z12,z6])],[(0,[z101,z1,z2,z3,z4,z83,z6]),(0,[z0,z1,z13,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z575,z6]),(0,[z0,z106,z46,z2,z3,z4,z6]),(0,[z15,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z16,z2,z3,z4,z6])],[(0,[z532,z0,z1,z2,z3,z4,z6]),(1,[z11,z0,z1,z26,z2,z6])],[(0,[z94,z1,z115,z2,z3,z4,z6]),(0,[z0,z1,z2,z17,z4,z14,z6]),(1,[z71,z0,z2,z3,z29,z6]),(0,[z236,z0,z1,z16,z2,z3,z6]),(0,[z0,z1,z276,z2,z63,z3,z6])],[(0,[z0,z1,z576,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z473,z6]),(0,[z131,z0,z1,z2,z3,z4,z6]),(0,[z237,z0,z1,z16,z2,z3,z6])],[(0,[z303,z0,z1,z2,z104,z4,z6]),(0,[z0,z1,z2,z3,z33,z6,z91]),(0,[z0,z1,z2,z2,z12,z4,z6]),(0,[z0,z1,z16,z2,z3,z109,z6])],[(0,[z0,z1,z577,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z6]),(0,[z54,z0,z1,z2,z3,z578,z6]),(0,[z0,z1,z2,z3,z29,z4,z6])]],
   [[(0,[z0,z1,z2,z12,z66,z4,z6]),(0,[z11,z0,z1,z220,z2,z4,z6]),(0,[z0,z579,z1,z26,z2,z3,z6])],[],[(1,[z447,z1,z2,z3,z4,z6]),(0,[z0,z1,z152,z2,z4,z14,z6])],[(0,[z0,z1,z3,z12,z161,z4,z6]),(0,[z28,z0,z1,z2,z3,z39,z6]),(0,[z54,z0,z1,z2,z3,z132,z6]),(1,[z0,z1,z2,z339,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z580]),(0,[z21,z11,z0,z1,z2,z4,z6]),(0,[z54,z238,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z177,z6]),(0,[z24,z0,z1,z2,z3,z14,z6]),(0,[z236,z0,z1,z2,z3,z155,z6]),(0,[z236,z0,z1,z3,z4,z6,z47])],[(0,[z0,z1,z2,z3,z4,z60,z172])],[(0,[z0,z1,z2,z3,z4,z83,z47]),(0,[z0,z1,z2,z12,z581,z4,z6]),(0,[z0,z1,z2,z3,z4,z582,z6]),(0,[z583,z0,z1,z26,z2,z3,z6])],[],[(0,[z80,z0,z1,z2,z78,z4,z6]),(0,[z584,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z346,z4,z6]),(0,[z0,z1,z2,z3,z585,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z586]),(0,[z0,z18,z1,z2,z3,z33,z6]),(0,[z0,z587,z1,z2,z3,z4,z6])],[(1,[z43,z55,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z524,z6]),(0,[z0,z1,z2,z588,z3,z4,z6]),(0,[z54,z0,z1,z2,z3,z33,z6])],[(0,[z0,z106,z1,z3,z12,z4,z6]),(0,[z589,z0,z1,z2,z3,z4,z6]),(0,[z236,z0,z1,z2,z3,z235,z6]),(0,[z0,z590,z1,z2,z3,z4,z6])],[(0,[z21,z0,z1,z2,z3,z4,z524]),(0,[z28,z139,z0,z1,z2,z4,z6]),(0,[z0,z1,z2,z12,z4,z72,z6]),(0,[z139,z0,z1,z2,z3,z33,z6])],[(0,[z0,z1,z381,z2,z3,z4,z6]),(1,[z126,z0,z1,z2,z4,z6]),(0,[z0,z1,z2,z591,z3,z4,z6]),(0,[z0,z52,z1,z2,z3,z6,z91]),(0,[z0,z1,z2,z3,z592,z4,z6])],[(0,[z21,z94,z1,z2,z3,z4,z6]),(0,[z71,z0,z1,z16,z2,z3,z6]),(1,[z59,z1,z2,z3,z4,z6])]],
   [[(0,[z0,z1,z2,z3,z4,z593,z6]),(0,[z21,z0,z1,z2,z3,z229,z6]),(0,[z0,z1,z594,z2,z3,z4,z6])],[(0,[z0,z1,z595,z2,z3,z4,z6]),(0,[z0,z2,z123,z3,z17,z4,z6]),(1,[z0,z1,z276,z2,z3,z6])],[(0,[z94,z0,z1,z2,z12,z4,z6]),(0,[z0,z1,z2,z3,z134,z4,z6]),(0,[z0,z1,z26,z2,z123,z3,z6])],[(0,[z0,z1,z2,z3,z596,z4,z6]),(0,[z0,z1,z597,z2,z3,z4,z6]),(0,[z236,z0,z1,z128,z3,z4,z6]),(0,[z0,z1,z99,z2,z12,z4,z6]),(0,[z96,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z1,z2,z3,z4,z6]),(0,[z598,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z599,z6]),(0,[z193,z0,z1,z2,z12,z4,z6])],[(0,[z127,z24,z0,z1,z2,z3,z6]),(0,[z101,z0,z1,z2,z3,z4,z82]),(0,[z0,z1,z2,z3,z4,z172,z82]),(0,[z0,z1,z2,z3,z600,z4,z6]),(0,[z127,z0,z1,z2,z3,z33,z6])],[(0,[z42,z0,z1,z2,z12,z4,z6]),(0,[z107,z0,z1,z2,z3,z4,z6])],[(0,[z57,z0,z1,z2,z3,z33,z6]),(0,[z0,z1,z2,z3,z4,z6,z601])],[(0,[z602,z0,z1,z2,z3,z4,z6]),(0,[z603,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z12,z4,z14,z6]),(0,[z0,z1,z2,z3,z4,z604,z6])],[(0,[z0,z1,z2,z3,z4,z605,z6]),(0,[z62,z0,z1,z2,z3,z4,z6])],[(0,[z0,z55,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z118,z4,z6]),(0,[z0,z1,z606,z2,z3,z4,z6])],[(0,[z0,z2,z3,z17,z4,z6,z91])],[(0,[z0,z1,z2,z3,z607,z4,z6]),(0,[z21,z0,z1,z3,z161,z4,z6]),(0,[z608,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z128,z2,z12,z4,z6])],[(0,[z609,z0,z1,z2,z3,z4,z6]),(0,[z610,z0,z1,z2,z3,z4,z6])],[(0,[z0,z55,z2,z3,z17,z4,z6]),(0,[z611,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z30,z2,z3,z4,z6])],[(0,[z190,z0,z1,z46,z2,z4,z6])]],
   [[(0,[z0,z1,z2,z3,z612,z33,z6]),(0,[z0,z1,z613,z2,z3,z4,z6]),(1,[z0,z1,z468,z3,z4,z6])],[(0,[z28,z0,z1,z2,z3,z33,z6])],[(1,[z0,z1,z2,z3,z4,z534]),(0,[z0,z1,z614,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z615]),(0,[z0,z1,z2,z3,z4,z60,z47])],[(0,[z0,z1,z616,z2,z3,z4,z6]),(0,[z62,z0,z1,z2,z4,z6,z38])],[(0,[z583,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z617,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z618,z6]),(0,[z0,z1,z619,z2,z3,z4,z6])],[(0,[z42,z0,z2,z3,z4,z6,z91]),(0,[z0,z1,z2,z3,z620,z4,z6]),(0,[z0,z1,z2,z12,z621,z4,z6]),(0,[z0,z1,z622,z2,z3,z4,z6])],[(0,[z0,z0,z1,z2,z3,z4,z6]),(0,[z80,z0,z1,z2,z3,z14,z6]),(0,[z303,z0,z1,z2,z3,z4,z6]),(0,[z54,z0,z1,z2,z41,z4,z6]),(0,[z15,z0,z1,z2,z3,z191,z6]),(0,[z623,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z411,z6]),(0,[z37,z0,z1,z16,z2,z3,z6])],[(0,[z0,z142,z1,z2,z12,z4,z6]),(0,[z0,z1,z2,z3,z33,z6,z38])],[(0,[z0,z1,z2,z12,z79,z4,z6]),(0,[z0,z1,z2,z3,z66,z33,z6]),(0,[z74,z11,z0,z1,z2,z4,z6]),(0,[z0,z1,z2,z3,z117,z4,z6])],[(0,[z309,z0,z1,z2,z12,z4,z6])],[(0,[z0,z1,z26,z2,z3,z6,z91]),(0,[z0,z1,z2,z3,z286,z14,z6]),(0,[z335,z0,z1,z2,z3,z4,z6])],[(0,[z21,z0,z1,z2,z12,z4,z6]),(0,[z0,z1,z16,z2,z3,z6,z624]),(1,[z0,z1,z2,z3,z487,z6]),(0,[z127,z0,z1,z2,z3,z4,z70])],[(0,[z0,z1,z2,z3,z7,z14,z6]),(0,[z227,z0,z1,z2,z12,z4,z6]),(0,[z0,z1,z2,z3,z4,z235,z6]),(0,[z0,z1,z529,z2,z3,z4,z6]),(1,[z0,z1,z2,z392,z4,z6])],[(0,[z625,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z626,z2,z3,z4,z6])],[(0,[z21,z0,z1,z2,z308,z4,z6]),(0,[z28,z0,z1,z26,z2,z3,z6]),(0,[z0,z1,z249,z2,z78,z3,z6]),(0,[z11,z0,z1,z2,z3,z33,z6]),(0,[z37,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z26,z2,z3,z33,z6])]],
   [[(0,[z11,z0,z1,z2,z104,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z627]),(0,[z0,z1,z460,z2,z3,z4,z6])],[(0,[z628,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z17,z33,z6]),(1,[z11,z0,z1,z2,z194,z6])],[(0,[z0,z1,z2,z3,z629,z4,z6]),(0,[z0,z1,z2,z3,z4,z630,z6]),(0,[z0,z1,z2,z3,z104,z14,z6]),(1,[z73,z1,z2,z3,z4,z82]),(0,[z0,z1,z46,z2,z3,z479,z6]),(0,[z0,z1,z2,z3,z4,z6,z631])],[],[(0,[z42,z0,z55,z2,z3,z4,z6]),(0,[z0,z410,z2,z3,z4,z83,z6]),(0,[z0,z1,z26,z46,z2,z3,z6]),(0,[z0,z18,z1,z2,z3,z4,z6]),(0,[z0,z1,z632,z2,z3,z4,z6]),(0,[z0,z19,z1,z2,z12,z4,z6]),(0,[z0,z1,z2,z3,z12,z166,z6])],[(1,[z0,z1,z2,z300,z4,z6]),(0,[z54,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z633,z6]),(0,[z15,z0,z1,z16,z2,z3,z6]),(0,[z0,z1,z2,z3,z634,z4,z6]),(0,[z0,z1,z99,z2,z346,z4,z6]),(0,[z0,z1,z16,z16,z2,z3,z6])],[(0,[z80,z0,z1,z2,z4,z14,z6]),(0,[z73,z0,z1,z26,z2,z3,z6]),(1,[z0,z220,z2,z3,z4,z6]),(0,[z37,z0,z1,z2,z3,z117,z6])],[(0,[z0,z1,z22,z2,z81,z4,z6]),(0,[z0,z142,z1,z2,z3,z70,z6]),(0,[z182,z0,z1,z2,z3,z4,z6]),(0,[z11,z0,z488,z1,z2,z4,z6]),(0,[z635,z0,z1,z2,z3,z4,z6]),(0,[z139,z0,z1,z2,z3,z4,z6])],[(0,[z0,z636,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z78,z3,z4,z6]),(0,[z80,z1,z2,z3,z4,z6,z82]),(0,[z11,z0,z1,z2,z4,z6,z91])],[(0,[z0,z1,z22,z2,z3,z4,z6]),(0,[z0,z1,z577,z16,z2,z3,z6]),(0,[z0,z1,z16,z2,z3,z3,z6]),(0,[z0,z1,z2,z3,z4,z6,z637])],[(1,[z0,z1,z2,z4,z6,z287]),(0,[z638,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z639,z2,z3,z4,z6]),(0,[z11,z0,z1,z26,z2,z3,z6]),(1,[z0,z1,z26,z2,z3,z6]),(0,[z0,z1,z2,z3,z33,z565,z6]),(0,[z0,z140,z1,z2,z3,z4,z6])],[(0,[z640,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z26,z26,z2,z3,z6])],[(0,[z0,z52,z1,z2,z3,z4,z6]),(0,[z641,z0,z1,z2,z3,z4,z6])],[(0,[z11,z0,z1,z2,z4,z33,z6]),(0,[z642,z0,z1,z2,z3,z4,z6]),(0,[z0,z253,z1,z2,z3,z4,z6])],[(0,[z643,z0,z1,z2,z3,z4,z6]),(0,[z101,z94,z1,z2,z3,z4,z6]),(0,[z127,z0,z1,z2,z3,z4,z6])]],
   [[(0,[z644,z0,z1,z2,z3,z4,z6]),(0,[z0,z2,z3,z66,z4,z6,z91])],[(1,[z0,z1,z2,z3,z4,z469]),(0,[z15,z0,z2,z3,z17,z4,z6]),(0,[z0,z1,z2,z3,z645,z4,z6]),(0,[z57,z0,z1,z2,z3,z4,z6]),(0,[z446,z0,z1,z2,z3,z4,z6]),(0,[z139,z0,z1,z2,z4,z6,z38])],[(0,[z103,z0,z1,z2,z3,z33,z6]),(0,[z0,z1,z2,z3,z136,z33,z6])],[(0,[z28,z0,z64,z2,z3,z4,z6]),(0,[z0,z1,z46,z2,z3,z33,z6]),(0,[z0,z1,z646,z2,z3,z4,z6])],[(0,[z0,z1,z234,z128,z2,z3,z6]),(0,[z0,z1,z2,z3,z4,z6,z647])],[(0,[z0,z1,z2,z3,z197,z4,z6]),(0,[z0,z1,z26,z648,z2,z3,z6]),(0,[z649,z0,z1,z2,z3,z4,z6])],[(0,[z94,z0,z1,z3,z161,z4,z6]),(0,[z80,z0,z1,z2,z79,z4,z6])],[(0,[z0,z1,z2,z3,z650,z4,z6]),(0,[z651,z0,z1,z2,z3,z4,z6]),(0,[z652,z0,z1,z2,z3,z4,z6])],[(0,[z289,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z653,z6])],[(1,[z0,z49,z2,z3,z4,z6]),(0,[z236,z0,z1,z2,z3,z14,z6]),(0,[z0,z1,z2,z3,z612,z4,z6]),(0,[z0,z1,z2,z654,z3,z4,z6])],[(0,[z0,z655,z1,z2,z3,z4,z6]),(0,[z28,z0,z1,z2,z3,z4,z6]),(0,[z656,z0,z1,z2,z3,z4,z6]),(0,[z237,z0,z1,z2,z3,z14,z6])],[(0,[z657,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z534,z6]),(0,[z417,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z658,z3,z4,z6])],[(1,[z0,z1,z2,z3,z452,z6])],[(0,[z43,z94,z1,z2,z3,z4,z6])],[(0,[z659,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z454,z6]),(0,[z103,z0,z1,z26,z2,z3,z6]),(0,[z74,z0,z1,z2,z12,z4,z6]),(0,[z536,z0,z1,z26,z2,z3,z6])]],
   [[(0,[z0,z1,z2,z3,z79,z33,z6]),(0,[z0,z1,z2,z660,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z661,z6]),(0,[z0,z662,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z663]),(0,[z143,z0,z1,z26,z2,z3,z6]),(0,[z0,z1,z2,z664,z3,z4,z6])],[(0,[z0,z1,z2,z3,z66,z4,z6]),(1,[z11,z0,z488,z2,z4,z6])],[(1,[z0,z1,z2,z3,z39,z6]),(0,[z11,z0,z1,z16,z2,z4,z6]),(0,[z0,z146,z1,z26,z2,z3,z6]),(0,[z0,z1,z26,z2,z3,z6,z38]),(1,[z0,z1,z460,z2,z3,z6]),(0,[z0,z1,z2,z3,z4,z6,z665])],[(0,[z0,z1,z2,z666,z3,z4,z6]),(1,[z0,z1,z2,z3,z6,z418]),(0,[z0,z1,z2,z3,z4,z6,z667]),(0,[z0,z1,z2,z3,z668,z4,z6]),(0,[z62,z0,z1,z16,z2,z3,z6])],[(0,[z0,z55,z1,z16,z2,z3,z6]),(0,[z11,z641,z0,z1,z2,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z624])],[(0,[z0,z1,z16,z2,z3,z7,z6]),(1,[z0,z1,z2,z443,z4,z6])],[(0,[z669,z0,z1,z2,z3,z4,z6])],[(0,[z0,z55,z2,z3,z66,z4,z6]),(0,[z11,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z30,z3,z4,z172])],[(0,[z0,z1,z2,z3,z4,z82,z38]),(0,[z0,z1,z2,z3,z581,z4,z6]),(0,[z0,z46,z2,z3,z17,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z670]),(0,[z0,z1,z26,z2,z3,z4,z6]),(0,[z139,z0,z1,z152,z2,z4,z6])],[(1,[z0,z1,z2,z123,z14,z6]),(0,[z671,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z3,z14,z6])],[(0,[z672,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z17,z4,z6]),(0,[z0,z1,z128,z2,z3,z411,z6]),(0,[z0,z1,z2,z12,z4,z188,z6]),(0,[z0,z1,z26,z2,z654,z3,z6]),(0,[z535,z0,z1,z2,z3,z14,z6]),(0,[z75,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z673,z4,z6]),(0,[z674,z0,z1,z2,z3,z4,z6]),(0,[z675,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z676,z2,z3,z4,z6]),(0,[z236,z11,z0,z1,z3,z4,z6]),(0,[z0,z1,z16,z152,z2,z3,z6]),(1,[z62,z0,z1,z2,z4,z38])],[(0,[z42,z0,z1,z2,z3,z33,z6]),(1,[z21,z1,z3,z161,z4,z6]),(0,[z71,z0,z1,z2,z3,z14,z6]),(1,[z0,z1,z234,z2,z3,z6]),(1,[z74,z0,z1,z26,z3,z6])],[(0,[z677,z0,z1,z2,z3,z4,z6]),(0,[z54,z236,z0,z1,z3,z4,z6])],[(0,[z0,z678,z1,z2,z3,z4,z6])]],
   [[(0,[z0,z1,z2,z3,z4,z679,z6]),(0,[z0,z579,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z479,z6]),(0,[z236,z0,z1,z30,z3,z4,z6]),(0,[z0,z1,z680,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z14,z6,z91])],[(0,[z681,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z22,z3,z12,z4,z6]),(0,[z0,z1,z26,z2,z3,z29,z6]),(0,[z0,z1,z2,z63,z12,z4,z6]),(0,[z11,z0,z1,z2,z4,z6,z38]),(1,[z0,z1,z315,z2,z3,z6]),(0,[z0,z1,z2,z3,z4,z6,z682])],[(0,[z0,z1,z2,z3,z578,z4,z6]),(0,[z0,z1,z2,z683,z3,z4,z6]),(0,[z0,z1,z2,z684,z3,z4,z6]),(0,[z685,z0,z1,z2,z3,z4,z6]),(0,[z0,z686,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z12,z4,z166,z6]),(0,[z687,z0,z1,z2,z3,z4,z6])],[(0,[z573,z0,z1,z2,z3,z4,z6]),(0,[z1,z2,z3,z104,z4,z7,z6]),(0,[z73,z0,z1,z2,z3,z4,z83])],[(1,[z0,z1,z2,z3,z578,z6])],[(0,[z43,z0,z115,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z688,z6]),(0,[z71,z0,z19,z2,z3,z4,z6])],[(0,[z0,z221,z1,z2,z3,z4,z6]),(0,[z0,z1,z16,z2,z3,z66,z6])],[(0,[z0,z115,z2,z3,z17,z4,z6]),(0,[z0,z1,z648,z2,z3,z4,z6]),(0,[z0,z1,z114,z2,z3,z4,z6])],[(0,[z42,z0,z1,z26,z2,z3,z6]),(0,[z43,z0,z1,z2,z12,z4,z6]),(0,[z0,z1,z16,z22,z2,z3,z6]),(0,[z0,z1,z2,z3,z4,z689,z6]),(0,[z0,z690,z1,z2,z3,z4,z6]),(1,[z238,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z123,z3,z14,z6]),(0,[z0,z1,z2,z3,z4,z14,z6]),(0,[z127,z0,z1,z189,z3,z4,z6])],[],[(0,[z94,z0,z1,z22,z3,z4,z6]),(0,[z103,z0,z1,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z7,z6,z82]),(0,[z73,z0,z1,z2,z3,z33,z6]),(0,[z536,z0,z1,z2,z3,z4,z6]),(0,[z691,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z119,z2,z3,z4,z6]),(0,[z0,z1,z46,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z692]),(0,[z0,z106,z1,z2,z3,z14,z6]),(0,[z0,z323,z1,z2,z3,z4,z6])],[(0,[z11,z0,z1,z2,z4,z554,z6]),(0,[z0,z1,z199,z26,z2,z3,z6]),(1,[z0,z512,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z693])],[(0,[z453,z0,z1,z2,z3,z4,z6]),(0,[z0,z106,z1,z46,z3,z4,z6]),(0,[z0,z18,z1,z16,z2,z3,z6])]],
   [[(0,[z0,z1,z2,z3,z4,z6,z694]),(0,[z0,z1,z2,z12,z4,z6,z82]),(0,[z54,z0,z1,z16,z2,z3,z6]),(0,[z0,z1,z16,z2,z3,z17,z6]),(1,[z0,z1,z2,z12,z14,z6]),(0,[z11,z0,z1,z2,z4,z6,z557]),(0,[z0,z1,z2,z3,z33,z688,z6]),(1,[z0,z1,z2,z214,z4,z6]),(0,[z695,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z31,z70,z6])],[(0,[z0,z1,z16,z2,z3,z161,z6]),(1,[z0,z1,z2,z3,z33,z6])],[(0,[z0,z1,z696,z2,z3,z4,z6]),(0,[z37,z0,z1,z3,z4,z6,z47]),(0,[z139,z0,z1,z16,z2,z3,z6])],[(0,[z54,z0,z2,z3,z66,z4,z6]),(0,[z0,z1,z2,z3,z697,z4,z6])],[(0,[z459,z0,z1,z2,z3,z4,z6])],[(1,[z216,z0,z1,z3,z4,z6]),(0,[z0,z1,z267,z2,z3,z4,z6])],[(1,[z0,z1,z2,z3,z508,z6])],[(0,[z0,z1,z2,z3,z621,z4,z6]),(0,[z0,z1,z2,z3,z698,z4,z6]),(0,[z54,z221,z1,z2,z3,z4,z6])],[(0,[z0,z1,z16,z2,z3,z72,z6]),(0,[z0,z1,z2,z699,z3,z4,z6])],[(0,[z80,z0,z1,z2,z4,z188,z6]),(0,[z0,z1,z2,z3,z4,z700,z6]),(0,[z0,z1,z2,z3,z701,z4,z6])],[(0,[z0,z1,z2,z3,z702,z4,z6]),(0,[z0,z1,z2,z123,z4,z14,z6]),(0,[z11,z0,z1,z152,z2,z4,z6]),(0,[z127,z0,z1,z16,z2,z3,z6]),(0,[z62,z0,z267,z2,z3,z4,z6]),(0,[z0,z1,z2,z468,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z703,z6]),(0,[z0,z1,z2,z12,z4,z83,z6]),(0,[z0,z1,z30,z3,z4,z172,z6])],[(0,[z54,z0,z2,z3,z17,z4,z6]),(0,[z57,z0,z1,z16,z2,z3,z6]),(1,[z0,z1,z128,z12,z4,z6]),(0,[z0,z1,z2,z704,z3,z4,z6]),(0,[z0,z1,z2,z3,z487,z4,z6])],[(0,[z0,z1,z2,z705,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z239,z6]),(0,[z57,z0,z1,z2,z3,z4,z60]),(0,[z0,z1,z2,z3,z374,z4,z6])],[(0,[z0,z1,z381,z22,z2,z3,z6]),(0,[z0,z1,z2,z3,z4,z6,z148])],[(0,[z21,z0,z1,z26,z2,z3,z6]),(0,[z0,z1,z2,z3,z706,z4,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z19,z2,z3,z4,z513]),(0,[z139,z0,z119,z2,z4,z6]),(0,[z335,z1,z26,z2,z3,z6])],[(0,[z0,z1,z707,z3,z4,z6]),(0,[z0,z1,z2,z3,z708,z6]),(0,[z0,z1,z2,z3,z709,z6]),(0,[z0,z1,z30,z12,z166,z6]),(0,[z131,z0,z1,z231,z4,z6]),(0,[z0,z1,z710,z3,z4,z6])],[(0,[z0,z1,z711,z2,z4,z6]),(0,[z0,z1,z378,z12,z4,z6]),(0,[z0,z1,z12,z4,z83,z47]),(0,[z0,z1,z2,z3,z6,z112]),(0,[z59,z1,z2,z12,z4,z6]),(0,[z313,z0,z1,z2,z194,z6]),(0,[z573,z1,z2,z3,z612,z6])],[(0,[z0,z1,z2,z3,z33,z524]),(0,[z0,z1,z2,z12,z39,z6]),(0,[z75,z1,z2,z3,z104,z6]),(0,[z221,z1,z2,z3,z4,z148]),(0,[z0,z1,z597,z2,z14,z6]),(0,[z0,z1,z2,z3,z6,z712]),(0,[z160,z1,z2,z3,z33,z6])],[(0,[z598,z0,z1,z12,z4,z6]),(0,[z94,z1,z16,z22,z3,z6]),(0,[z0,z1,z2,z12,z6,z418]),(0,[z713,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z6,z714]),(0,[z0,z46,z3,z389,z4,z6]),(0,[z0,z1,z715,z2,z3,z6]),(0,[z0,z1,z12,z4,z6,z586]),(0,[z11,z160,z1,z2,z4,z6]),(0,[z0,z1,z2,z716,z4,z6])],[(0,[z0,z1,z381,z2,z12,z6])],[(0,[z0,z1,z2,z717,z4,z6]),(0,[z0,z18,z122,z2,z123,z6]),(0,[z0,z1,z718,z2,z3,z6])],[(0,[z359,z115,z2,z3,z4,z6]),(0,[z0,z1,z26,z2,z299,z6]),(0,[z337,z0,z3,z12,z4,z6]),(0,[z28,z64,z2,z79,z4,z6]),(0,[z0,z1,z719,z3,z4,z6]),(0,[z54,z0,z1,z720,z4,z6]),(0,[z0,z721,z2,z3,z4,z6]),(0,[z0,z1,z30,z12,z4,z172]),(0,[z0,z1,z189,z76,z4,z6])],[(0,[z0,z1,z722,z2,z3,z6]),(0,[z0,z1,z12,z4,z6,z663]),(0,[z0,z19,z16,z2,z3,z60]),(0,[z11,z222,z1,z2,z4,z6])],[(0,[z1,z2,z3,z4,z6,z723]),(0,[z724,z1,z2,z3,z14,z6])],[(0,[z0,z1,z30,z12,z180,z6]),(0,[z37,z0,z1,z3,z14,z47]),(0,[z222,z1,z189,z3,z4,z6])],[(0,[z11,z0,z2,z197,z4,z6]),(0,[z0,z1,z2,z3,z6,z725]),(0,[z0,z1,z306,z3,z4,z534]),(0,[z0,z1,z2,z134,z14,z6]),(0,[z0,z1,z726,z2,z3,z6]),(0,[z0,z727,z2,z3,z4,z6]),(0,[z11,z0,z220,z2,z14,z6]),(0,[z0,z512,z2,z3,z4,z47])],[(0,[z0,z1,z2,z3,z39,z377]),(0,[z221,z1,z2,z3,z14,z6]),(0,[z11,z0,z1,z2,z4,z469]),(0,[z0,z1,z2,z3,z6,z728]),(0,[z0,z1,z2,z14,z6,z627]),(0,[z729,z0,z1,z2,z3,z6])],[(0,[z730,z0,z1,z12,z4,z6]),(0,[z11,z0,z1,z718,z2,z6])],[(0,[z0,z64,z2,z3,z262,z6]),(0,[z0,z1,z2,z600,z14,z6]),(0,[z0,z1,z270,z2,z14,z6]),(0,[z0,z1,z3,z33,z6,z506]),(0,[z731,z1,z2,z3,z4,z6])]],
   [[(0,[z0,z1,z26,z2,z3,z524]),(0,[z28,z1,z2,z79,z4,z6]),(0,[z0,z1,z2,z732,z4,z6]),(0,[z0,z1,z2,z406,z4,z6]),(0,[z733,z0,z1,z2,z4,z6]),(0,[z160,z1,z26,z2,z3,z6])],[(0,[z0,z1,z149,z12,z161,z6]),(0,[z0,z1,z734,z2,z3,z6])],[(0,[z0,z1,z2,z3,z4,z735]),(0,[z0,z1,z2,z3,z736,z6]),(0,[z28,z0,z1,z306,z14,z6]),(0,[z24,z0,z1,z2,z300,z6]),(0,[z0,z1,z2,z17,z14,z6]),(0,[z0,z1,z2,z194,z277,z6]),(0,[z0,z1,z157,z76,z4,z6])],[(0,[z0,z1,z2,z673,z14,z6]),(0,[z0,z410,z2,z3,z4,z6]),(0,[z598,z0,z3,z66,z4,z6]),(0,[z0,z1,z737,z3,z4,z6]),(0,[z0,z106,z1,z149,z12,z6]),(0,[z0,z1,z738,z2,z3,z6]),(0,[z232,z0,z1,z2,z14,z6]),(0,[z236,z11,z0,z1,z4,z6]),(0,[z0,z1,z468,z12,z4,z6]),(0,[z0,z1,z3,z166,z6,z47]),(0,[z131,z0,z1,z12,z4,z6]),(0,[z0,z1,z739,z2,z3,z6]),(0,[z0,z1,z266,z2,z3,z492]),(0,[z0,z1,z2,z740,z4,z6])],[(0,[z0,z1,z2,z3,z741,z6]),(0,[z0,z1,z26,z3,z455,z6]),(0,[z0,z1,z742,z2,z3,z6]),(0,[z743,z0,z1,z2,z4,z6]),(0,[z0,z323,z2,z3,z33,z6])],[(0,[z744,z0,z1,z2,z3,z6]),(0,[z0,z64,z405,z3,z4,z6]),(0,[z0,z1,z745,z3,z4,z6]),(0,[z0,z1,z2,z214,z277,z6]),(0,[z0,z253,z16,z2,z3,z6])],[(0,[z0,z1,z2,z3,z746,z6]),(0,[z80,z1,z2,z588,z4,z6]),(0,[z0,z16,z2,z3,z6,z84]),(0,[z0,z1,z149,z128,z12,z6]),(0,[z0,z1,z2,z3,z166,z6]),(0,[z0,z1,z26,z2,z747,z6])],[(0,[z0,z1,z2,z3,z262,z6]),(0,[z139,z0,z1,z2,z4,z377]),(0,[z0,z1,z748,z4,z6,z82]),(0,[z54,z0,z1,z134,z4,z6]),(0,[z0,z1,z2,z307,z578,z6]),(0,[z15,z0,z1,z297,z4,z6]),(0,[z0,z1,z749,z2,z3,z6]),(0,[z750,z1,z2,z3,z4,z6])],[(0,[z42,z11,z115,z2,z4,z6]),(0,[z0,z1,z306,z3,z33,z6]),(0,[z0,z1,z2,z3,z751,z6]),(0,[z190,z0,z1,z2,z4,z6]),(0,[z1,z2,z3,z14,z6,z53]),(0,[z11,z0,z1,z460,z2,z6]),(0,[z0,z1,z2,z752,z4,z6])],[(0,[z0,z1,z3,z753,z4,z6]),(0,[z0,z754,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z755,z6]),(0,[z0,z2,z3,z756,z4,z6])],[(0,[z0,z1,z757,z2,z3,z6]),(0,[z0,z1,z758,z3,z4,z6]),(0,[z238,z1,z2,z12,z4,z6]),(0,[z0,z1,z2,z759,z4,z6]),(0,[z236,z11,z0,z220,z4,z6]),(0,[z0,z1,z2,z760,z4,z6]),(0,[z761,z1,z26,z2,z3,z6])],[(0,[z337,z0,z16,z2,z3,z6]),(0,[z0,z1,z2,z307,z132,z6]),(0,[z11,z0,z106,z46,z4,z6]),(0,[z0,z1,z13,z2,z17,z6]),(0,[z0,z1,z2,z3,z762,z6]),(0,[z222,z1,z16,z2,z3,z6])],[(0,[z0,z1,z308,z161,z4,z6]),(0,[z238,z1,z2,z307,z4,z6]),(0,[z763,z1,z2,z3,z4,z6]),(0,[z0,z686,z1,z12,z4,z6]),(0,[z11,z0,z1,z16,z12,z6]),(0,[z0,z1,z26,z3,z109,z6])],[(0,[z42,z0,z2,z3,z4,z148]),(0,[z0,z1,z2,z299,z4,z44]),(0,[z0,z1,z405,z3,z4,z6]),(0,[z0,z1,z2,z764,z4,z6]),(0,[z335,z1,z2,z3,z4,z6]),(0,[z0,z1,z12,z4,z60,z47]),(0,[z383,z1,z2,z3,z565,z6]),(0,[z532,z0,z2,z3,z136,z6])],[(0,[z0,z1,z2,z765,z4,z6]),(0,[z0,z1,z2,z3,z766,z6]),(0,[z0,z512,z2,z12,z4,z6]),(0,[z0,z1,z2,z443,z767,z6])],[(0,[z0,z1,z26,z2,z300,z6]),(0,[z216,z0,z18,z123,z4,z6])]],
   [[(0,[z221,z18,z2,z3,z4,z6]),(0,[z11,z0,z1,z246,z2,z6]),(0,[z0,z1,z768,z3,z4,z6]),(0,[z0,z1,z2,z474,z166,z6]),(0,[z11,z0,z1,z2,z769,z6]),(0,[z0,z1,z2,z3,z180,z6]),(0,[z430,z0,z1,z26,z3,z6]),(0,[z0,z1,z2,z63,z14,z38])],[(0,[z770,z0,z1,z3,z4,z6]),(0,[z94,z1,z2,z3,z4,z44]),(0,[z0,z771,z2,z3,z4,z6]),(0,[z0,z1,z2,z12,z33,z6]),(0,[z11,z0,z1,z149,z2,z6])],[(0,[z0,z1,z2,z3,z229,z44]),(0,[z0,z772,z2,z3,z4,z6]),(0,[z0,z773,z2,z3,z4,z6]),(0,[z295,z0,z116,z2,z3,z6])],[(0,[z1,z12,z161,z4,z6,z82]),(0,[z0,z1,z261,z12,z4,z6]),(0,[z0,z1,z2,z774,z4,z6]),(0,[z0,z1,z2,z307,z33,z6]),(0,[z48,z0,z1,z26,z3,z6])],[(0,[z0,z1,z2,z308,z33,z6]),(0,[z1,z26,z2,z3,z6,z53]),(0,[z0,z1,z30,z12,z4,z47]),(0,[z0,z1,z2,z3,z775,z6]),(0,[z361,z1,z429,z2,z3,z6])],[(0,[z776,z0,z2,z3,z4,z6]),(0,[z337,z101,z2,z3,z4,z6]),(0,[z28,z0,z119,z2,z14,z6]),(0,[z126,z1,z2,z79,z4,z6]),(0,[z0,z1,z3,z33,z6,z531]),(0,[z0,z1,z2,z3,z777,z6])],[(0,[z0,z1,z549,z2,z14,z6]),(0,[z0,z142,z271,z2,z3,z6]),(0,[z11,z0,z1,z2,z778,z6]),(0,[z0,z1,z779,z2,z3,z6]),(0,[z0,z1,z13,z152,z2,z6])],[(0,[z0,z780,z2,z3,z4,z6])],[(0,[z0,z448,z2,z3,z4,z44]),(0,[z0,z1,z2,z781,z4,z6]),(0,[z0,z1,z2,z782,z4,z6]),(0,[z0,z3,z783,z66,z4,z6]),(0,[z0,z19,z2,z3,z4,z440]),(0,[z0,z314,z2,z3,z4,z6]),(0,[z0,z488,z2,z3,z33,z6]),(0,[z0,z1,z2,z3,z784,z6]),(0,[z0,z1,z2,z4,z6,z785])],[(0,[z0,z1,z2,z3,z786,z6]),(0,[z0,z787,z2,z3,z4,z6]),(1,[z0,z2,z788,z4,z6]),(0,[z0,z220,z2,z12,z4,z6])],[(0,[z0,z789,z2,z3,z4,z6]),(0,[z0,z267,z231,z3,z4,z6])],[(0,[z0,z1,z2,z299,z4,z6]),(0,[z0,z1,z2,z3,z33,z377]),(0,[z215,z1,z2,z3,z4,z82]),(0,[z0,z790,z2,z3,z4,z6]),(0,[z126,z0,z1,z2,z6,z418]),(0,[z0,z1,z2,z791,z4,z6]),(0,[z0,z1,z792,z2,z3,z6]),(0,[z11,z0,z1,z2,z793,z6])],[(0,[z24,z0,z1,z157,z3,z6]),(0,[z0,z1,z794,z2,z3,z6]),(0,[z11,z0,z1,z2,z479,z6]),(0,[z0,z271,z2,z3,z4,z6]),(0,[z795,z0,z1,z2,z4,z6]),(0,[z0,z1,z30,z3,z235,z6]),(0,[z0,z267,z2,z3,z14,z6])],[(0,[z0,z1,z2,z4,z6,z796])],[(0,[z0,z1,z797,z405,z3,z6]),(0,[z0,z1,z2,z4,z6,z798]),(0,[z799,z1,z2,z3,z4,z6]),(0,[z0,z1,z450,z2,z14,z6])],[(0,[z0,z1,z800,z3,z4,z6]),(0,[z80,z1,z2,z14,z6,z82]),(0,[z0,z1,z2,z801,z4,z6]),(0,[z0,z1,z3,z33,z6,z541]),(0,[z131,z0,z1,z2,z180,z6]),(0,[z0,z802,z2,z3,z4,z6])]],
   [[(0,[z0,z1,z2,z3,z229,z6]),(0,[z0,z803,z2,z3,z4,z6]),(0,[z0,z1,z804,z3,z4,z6]),(0,[z0,z805,z2,z3,z4,z6]),(0,[z0,z1,z806,z2,z3,z6])],[(0,[z0,z1,z2,z3,z807,z6]),(0,[z43,z0,z2,z3,z4,z148]),(0,[z11,z0,z1,z2,z578,z6]),(0,[z0,z1,z2,z808,z4,z6]),(0,[z0,z1,z26,z2,z809,z6]),(0,[z0,z810,z16,z2,z3,z6])],[(0,[z21,z1,z3,z161,z4,z524]),(0,[z37,z0,z1,z93,z4,z47])],[(0,[z0,z1,z2,z811,z4,z6]),(0,[z0,z1,z16,z12,z161,z6]),(0,[z54,z0,z106,z12,z4,z6]),(0,[z0,z1,z2,z3,z812,z6]),(0,[z0,z1,z2,z591,z14,z6]),(0,[z37,z0,z323,z3,z4,z47])],[(0,[z0,z1,z2,z3,z4,z813]),(0,[z0,z1,z2,z12,z4,z469]),(0,[z0,z1,z814,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z815]),(0,[z28,z1,z16,z2,z79,z6]),(0,[z816,z0,z1,z2,z4,z6]),(0,[z11,z0,z1,z2,z132,z6]),(0,[z0,z1,z817,z2,z3,z6]),(0,[z0,z1,z2,z12,z818,z6]),(0,[z0,z1,z2,z12,z27,z6])],[(0,[z0,z448,z2,z3,z4,z6]),(0,[z0,z1,z2,z14,z82,z38]),(0,[z819,z1,z2,z12,z4,z6]),(0,[z11,z0,z820,z2,z4,z6]),(0,[z11,z821,z1,z2,z4,z6]),(0,[z11,z0,z512,z2,z4,z6]),(0,[z131,z0,z1,z16,z2,z6]),(0,[z0,z1,z125,z2,z14,z6]),(0,[z127,z0,z1,z2,z3,z624])],[(0,[z0,z1,z22,z308,z4,z6]),(0,[z0,z1,z2,z17,z51,z6]),(0,[z11,z0,z1,z30,z4,z172]),(0,[z11,z0,z314,z2,z4,z6]),(0,[z761,z1,z2,z3,z4,z6])],[(0,[z0,z822,z2,z3,z4,z6]),(0,[z0,z1,z26,z2,z3,z377]),(0,[z0,z1,z2,z823,z4,z6]),(0,[z0,z1,z16,z128,z12,z6]),(0,[z0,z1,z152,z2,z166,z6]),(0,[z236,z795,z0,z1,z4,z6]),(0,[z0,z1,z824,z2,z3,z6])],[(0,[z42,z115,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z825,z6]),(0,[z54,z0,z1,z12,z166,z6]),(0,[z0,z1,z297,z3,z508,z6]),(0,[z57,z0,z2,z3,z4,z826]),(0,[z0,z1,z2,z3,z6,z827])],[(0,[z62,z0,z1,z2,z4,z377])],[(0,[z71,z0,z2,z3,z210,z6]),(0,[z0,z52,z1,z2,z828,z6]),(0,[z0,z1,z2,z12,z829,z6]),(0,[z0,z1,z16,z2,z277,z6]),(0,[z830,z1,z2,z3,z33,z6])],[(0,[z0,z831,z2,z3,z4,z6]),(0,[z126,z0,z1,z748,z4,z6]),(0,[z0,z108,z2,z17,z14,z6]),(0,[z832,z0,z1,z2,z4,z6]),(0,[z11,z0,z1,z680,z4,z6])],[(0,[z54,z43,z0,z12,z4,z6]),(0,[z0,z1,z2,z12,z4,z44]),(0,[z0,z1,z121,z12,z4,z6]),(0,[z11,z0,z1,z2,z4,z833]),(0,[z641,z0,z1,z2,z277,z6]),(0,[z0,z1,z2,z339,z33,z6]),(0,[z0,z1,z834,z3,z4,z6]),(0,[z0,z1,z2,z3,z835,z6])],[(0,[z0,z1,z2,z3,z39,z534]),(0,[z0,z1,z2,z836,z4,z6]),(0,[z0,z323,z2,z3,z4,z6]),(0,[z0,z1,z2,z837,z4,z6])],[(0,[z0,z1,z838,z2,z3,z6]),(0,[z57,z0,z2,z3,z112,z91]),(0,[z0,z1,z12,z4,z6,z647])]],
   [[(0,[z0,z49,z2,z308,z4,z6]),(0,[z550,z1,z2,z3,z4,z82]),(0,[z193,z1,z3,z161,z4,z6]),(0,[z0,z839,z2,z3,z4,z6]),(0,[z0,z662,z1,z12,z4,z6]),(0,[z57,z0,z2,z3,z4,z91]),(0,[z0,z1,z2,z3,z277,z6])],[(0,[z0,z1,z2,z3,z840,z6]),(0,[z0,z1,z841,z3,z4,z6]),(0,[z0,z1,z407,z2,z14,z6])],[(0,[z0,z1,z2,z3,z842,z6]),(0,[z0,z843,z2,z3,z4,z6]),(0,[z11,z0,z1,z2,z508,z6]),(0,[z0,z1,z2,z844,z4,z6]),(0,[z236,z11,z0,z1,z26,z6]),(0,[z0,z267,z2,z3,z159,z6])],[(0,[z0,z64,z2,z12,z4,z6]),(0,[z0,z488,z2,z41,z4,z6]),(0,[z216,z0,z1,z122,z3,z6]),(0,[z0,z1,z2,z346,z33,z6]),(0,[z0,z1,z845,z2,z3,z6]),(0,[z0,z1,z16,z2,z93,z6]),(0,[z0,z1,z157,z3,z14,z6])],[(0,[z80,z0,z1,z13,z2,z6]),(0,[z1,z2,z3,z846,z4,z6]),(0,[z0,z1,z2,z63,z14,z6])],[(0,[z43,z55,z2,z3,z33,z6]),(0,[z0,z1,z2,z3,z4,z847]),(0,[z1,z2,z3,z848,z4,z6]),(0,[z11,z0,z220,z12,z4,z6]),(0,[z11,z0,z253,z2,z4,z6]),(1,[z0,z1,z849,z3,z6]),(0,[z0,z146,z250,z2,z3,z6])],[(0,[z0,z2,z3,z4,z6,z850]),(0,[z0,z1,z16,z2,z257,z6]),(0,[z0,z1,z851,z2,z3,z6]),(0,[z0,z116,z1,z2,z14,z6]),(0,[z127,z0,z1,z2,z187,z6]),(0,[z0,z323,z2,z3,z117,z6])],[(0,[z21,z1,z299,z161,z4,z6]),(0,[z0,z1,z2,z852,z4,z6]),(0,[z659,z0,z1,z2,z14,z6]),(0,[z0,z1,z2,z3,z853,z6]),(0,[z854,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z855,z6]),(0,[z635,z0,z1,z2,z14,z6])],[(0,[z126,z0,z1,z2,z33,z6]),(0,[z0,z1,z2,z3,z856,z6]),(0,[z419,z0,z1,z16,z2,z6]),(0,[z0,z1,z2,z3,z857,z6]),(0,[z0,z1,z276,z2,z76,z6])],[(0,[z858,z115,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z859]),(0,[z0,z1,z860,z2,z3,z6]),(0,[z0,z1,z2,z3,z6,z861]),(0,[z0,z2,z3,z33,z6,z84]),(0,[z0,z2,z123,z788,z4,z6]),(0,[z0,z67,z2,z123,z4,z6]),(1,[z0,z488,z12,z4,z6]),(0,[z0,z862,z2,z3,z33,z6]),(0,[z447,z1,z26,z2,z3,z6]),(0,[z0,z1,z2,z63,z14,z188])],[(0,[z0,z1,z2,z3,z846,z6]),(0,[z303,z0,z1,z2,z14,z6]),(0,[z0,z1,z2,z4,z6,z863]),(0,[z0,z1,z2,z3,z14,z148]),(0,[z11,z0,z1,z2,z864,z6])],[(0,[z0,z2,z3,z4,z6,z865]),(0,[z0,z1,z2,z6,z866,z287]),(0,[z0,z106,z1,z12,z4,z6]),(0,[z0,z1,z2,z3,z867,z6]),(0,[z0,z2,z3,z868,z33,z6]),(0,[z37,z138,z1,z3,z4,z47])],[(0,[z0,z1,z869,z3,z4,z6]),(0,[z870,z1,z2,z3,z4,z6]),(0,[z0,z1,z871,z3,z4,z6])],[(0,[z0,z64,z2,z3,z4,z377]),(0,[z0,z1,z2,z307,z4,z6]),(0,[z0,z1,z872,z2,z3,z6]),(0,[z74,z11,z0,z1,z26,z6]),(0,[z138,z1,z2,z3,z14,z6]),(0,[z0,z1,z30,z392,z4,z172])],[(0,[z126,z0,z1,z2,z4,z38]),(0,[z0,z410,z16,z2,z3,z6]),(0,[z393,z0,z1,z3,z4,z47]),(0,[z0,z1,z311,z3,z4,z172])],[(0,[z0,z1,z2,z299,z177,z6]),(0,[z0,z1,z873,z2,z3,z6])]],
   [[(0,[z0,z1,z3,z33,z82,z47]),(0,[z0,z1,z2,z3,z4,z874]),(0,[z62,z0,z1,z2,z487,z38])],[(0,[z0,z1,z2,z875,z4,z6]),(0,[z80,z0,z1,z2,z14,z6]),(0,[z0,z19,z2,z3,z4,z144]),(0,[z0,z1,z2,z3,z876,z6]),(0,[z11,z0,z1,z2,z27,z6])],[(0,[z43,z55,z26,z2,z3,z6]),(0,[z0,z488,z2,z3,z4,z6])],[(0,[z0,z1,z2,z581,z14,z6]),(0,[z190,z0,z1,z26,z2,z6]),(0,[z0,z1,z2,z12,z479,z6]),(0,[z0,z1,z2,z3,z6,z877]),(0,[z0,z1,z2,z3,z878,z6]),(0,[z0,z314,z189,z3,z4,z6])],[(0,[z879,z0,z1,z2,z4,z6]),(0,[z28,z0,z1,z2,z454,z6]),(0,[z126,z80,z1,z2,z4,z6]),(0,[z0,z106,z46,z3,z14,z6]),(0,[z15,z0,z2,z17,z14,z6]),(0,[z59,z2,z3,z4,z6,z91]),(0,[z0,z1,z99,z12,z33,z6])],[(0,[z139,z0,z1,z880,z2,z6])],[(0,[z279,z0,z2,z3,z4,z91]),(0,[z0,z1,z2,z17,z135,z6]),(0,[z0,z1,z881,z2,z3,z6]),(0,[z59,z1,z26,z2,z3,z6]),(0,[z0,z1,z2,z12,z4,z882]),(0,[z0,z1,z883,z2,z3,z6]),(0,[z0,z1,z2,z3,z286,z70])],[(0,[z10,z0,z1,z2,z14,z6]),(0,[z0,z19,z2,z3,z14,z60]),(0,[z0,z1,z149,z30,z12,z6]),(0,[z236,z11,z0,z1,z155,z6]),(0,[z0,z1,z26,z2,z884,z6]),(0,[z0,z885,z2,z3,z4,z6]),(0,[z0,z1,z468,z3,z487,z6]),(0,[z0,z271,z189,z3,z4,z6])],[(0,[z0,z1,z2,z12,z578,z6]),(0,[z54,z0,z1,z16,z12,z6]),(0,[z11,z0,z1,z8,z4,z6]),(0,[z0,z1,z2,z3,z886,z6]),(0,[z0,z1,z576,z3,z33,z6]),(1,[z0,z2,z3,z4,z826]),(0,[z0,z887,z2,z3,z33,z6]),(0,[z335,z1,z16,z2,z3,z6]),(0,[z222,z1,z157,z3,z4,z6])],[(0,[z0,z1,z2,z888,z4,z6]),(0,[z11,z0,z1,z2,z4,z44]),(0,[z0,z1,z278,z2,z14,z6]),(0,[z54,z238,z1,z12,z4,z6]),(0,[z0,z1,z16,z114,z12,z6])],[(0,[z0,z1,z2,z3,z889,z6]),(0,[z0,z1,z890,z2,z3,z6]),(0,[z0,z448,z2,z3,z177,z6]),(0,[z0,z1,z2,z884,z4,z6]),(0,[z54,z0,z3,z783,z4,z6]),(0,[z0,z1,z2,z14,z6,z181]),(0,[z0,z1,z270,z2,z166,z6]),(0,[z0,z1,z468,z3,z33,z6]),(0,[z0,z1,z2,z63,z159,z6])],[(0,[z0,z142,z1,z2,z339,z6]),(0,[z11,z0,z1,z468,z4,z6])],[(0,[z0,z1,z2,z891,z4,z6]),(0,[z0,z1,z2,z3,z33,z534]),(0,[z0,z1,z2,z12,z132,z6]),(0,[z0,z1,z2,z297,z14,z6]),(0,[z0,z2,z12,z892,z4,z6]),(0,[z0,z893,z2,z3,z14,z6])],[(0,[z0,z894,z2,z3,z4,z6]),(0,[z0,z18,z2,z3,z4,z148]),(0,[z313,z0,z1,z2,z14,z6]),(0,[z0,z1,z2,z3,z895,z6])],[(0,[z0,z1,z2,z3,z896,z6]),(0,[z94,z1,z22,z3,z14,z6]),(0,[z0,z1,z297,z3,z4,z6]),(0,[z236,z11,z0,z1,z235,z6]),(0,[z0,z1,z2,z93,z897,z6]),(0,[z0,z1,z2,z3,z4,z898])],[(0,[z899,z1,z2,z3,z4,z6]),(0,[z900,z1,z2,z3,z4,z6]),(0,[z0,z901,z2,z3,z4,z6])]],
   [[(0,[z0,z1,z2,z902,z4,z6]),(0,[z563,z0,z1,z12,z4,z6]),(0,[z71,z0,z2,z3,z29,z6]),(0,[z393,z0,z1,z12,z4,z6]),(0,[z140,z1,z2,z12,z4,z6]),(0,[z0,z1,z2,z63,z4,z554]),(0,[z903,z0,z2,z3,z4,z6])],[(0,[z361,z0,z1,z2,z14,z6]),(0,[z0,z1,z2,z3,z904,z6]),(0,[z0,z271,z157,z3,z4,z6])],[(0,[z446,z0,z106,z12,z4,z6]),(0,[z0,z1,z152,z2,z277,z6])],[(0,[z0,z1,z2,z3,z905,z6]),(0,[z0,z116,z1,z2,z187,z6]),(0,[z0,z1,z341,z12,z4,z6]),(0,[z0,z1,z2,z3,z767,z6]),(0,[z0,z314,z16,z2,z3,z6])],[(0,[z0,z1,z2,z3,z4,z906]),(0,[z24,z1,z2,z3,z846,z6]),(0,[z73,z1,z2,z3,z4,z907]),(0,[z447,z1,z2,z443,z4,z6])],[(0,[z103,z0,z1,z2,z339,z6]),(0,[z0,z1,z2,z3,z6,z908]),(0,[z0,z1,z340,z12,z4,z6])],[(0,[z0,z1,z16,z306,z3,z6]),(0,[z0,z2,z3,z783,z4,z6]),(0,[z252,z0,z1,z297,z4,z6]),(0,[z0,z1,z2,z392,z33,z6]),(0,[z0,z1,z2,z76,z14,z6])],[(0,[z11,z0,z1,z2,z4,z6]),(0,[z0,z909,z2,z3,z4,z6]),(0,[z0,z1,z910,z2,z3,z6]),(0,[z317,z0,z1,z2,z14,z6]),(0,[z80,z0,z1,z2,z159,z6]),(0,[z399,z1,z2,z3,z4,z82]),(0,[z911,z1,z2,z3,z4,z6]),(0,[z216,z0,z1,z26,z3,z6]),(0,[z0,z1,z13,z12,z4,z6]),(0,[z0,z271,z16,z2,z3,z6]),(0,[z127,z0,z1,z157,z3,z32])],[(0,[z0,z1,z16,z2,z3,z524]),(0,[z11,z24,z1,z2,z7,z6]),(0,[z54,z238,z3,z66,z4,z6]),(0,[z0,z1,z2,z912,z4,z6]),(0,[z1,z2,z3,z4,z6,z913]),(0,[z216,z0,z1,z12,z4,z6]),(0,[z71,z0,z2,z3,z136,z6]),(0,[z11,z0,z1,z2,z155,z6]),(0,[z11,z0,z220,z16,z2,z6]),(0,[z160,z1,z16,z2,z3,z6])],[(0,[z337,z0,z2,z3,z14,z6]),(0,[z28,z119,z2,z79,z4,z6]),(0,[z0,z1,z26,z2,z3,z534]),(0,[z0,z1,z914,z2,z3,z6]),(0,[z0,z1,z2,z12,z508,z6]),(0,[z0,z1,z2,z915,z4,z6]),(0,[z222,z1,z2,z3,z14,z6]),(0,[z0,z1,z2,z3,z916,z6])],[(0,[z1,z2,z78,z848,z4,z6]),(0,[z917,z0,z1,z2,z3,z6]),(0,[z11,z0,z1,z12,z277,z6]),(0,[z202,z0,z1,z2,z277,z6])],[(0,[z625,z1,z3,z161,z4,z6]),(0,[z0,z1,z918,z2,z3,z6]),(0,[z0,z1,z2,z3,z919,z6]),(0,[z0,z46,z2,z17,z14,z6]),(0,[z0,z1,z2,z920,z4,z6]),(0,[z0,z1,z128,z12,z411,z6]),(0,[z11,z0,z1,z2,z109,z6])],[(0,[z0,z1,z2,z3,z4,z921]),(0,[z73,z1,z2,z3,z33,z82]),(0,[z0,z1,z794,z2,z134,z6]),(0,[z0,z1,z114,z12,z4,z6]),(0,[z0,z1,z2,z3,z31,z70])],[(0,[z922,z0,z1,z2,z4,z6]),(0,[z0,z1,z2,z3,z923,z6]),(0,[z0,z1,z2,z346,z4,z6]),(0,[z0,z924,z2,z3,z4,z6]),(0,[z37,z11,z0,z1,z4,z47])],[(0,[z11,z0,z1,z297,z4,z6]),(0,[z11,z140,z1,z2,z4,z6])],[(0,[z43,z55,z2,z3,z4,z6]),(0,[z21,z1,z12,z161,z4,z6]),(0,[z0,z1,z2,z3,z925,z6]),(0,[z0,z1,z2,z300,z33,z6]),(0,[z393,z0,z3,z66,z4,z6]),(0,[z236,z11,z0,z1,z16,z6]),(0,[z11,z0,z1,z2,z117,z6]),(0,[z0,z1,z613,z2,z14,z6])]],
   [[(0,[z0,z1,z2,z3,z4,z524]),(0,[z0,z119,z2,z3,z262,z6]),(0,[z160,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z926]),(0,[z0,z220,z2,z3,z33,z6])],[(0,[z0,z448,z16,z2,z3,z6]),(0,[z0,z1,z2,z927,z4,z6]),(0,[z80,z1,z2,z4,z188,z82]),(0,[z0,z1,z2,z3,z928,z6]),(0,[z0,z18,z1,z297,z4,z6])],[(0,[z126,z0,z1,z2,z4,z6]),(0,[z0,z1,z2,z929,z4,z6]),(0,[z0,z1,z26,z2,z76,z6])],[(0,[z0,z1,z12,z161,z14,z6]),(0,[z103,z1,z2,z3,z698,z6]),(0,[z0,z1,z914,z2,z307,z6])],[(0,[z42,z115,z16,z2,z3,z6]),(0,[z930,z1,z2,z3,z4,z6]),(0,[z931,z1,z2,z3,z4,z6]),(0,[z138,z1,z2,z93,z4,z6])],[(0,[z0,z1,z932,z2,z3,z6]),(0,[z0,z1,z2,z3,z4,z933]),(0,[z0,z2,z3,z868,z4,z6]),(0,[z0,z26,z2,z3,z6,z84]),(0,[z0,z1,z792,z2,z12,z6])],[(0,[z0,z119,z405,z3,z4,z6]),(0,[z0,z221,z1,z12,z4,z6]),(0,[z0,z1,z189,z12,z4,z6]),(0,[z0,z1,z99,z346,z33,z6])],[(0,[z24,z222,z1,z2,z3,z6]),(0,[z0,z1,z16,z2,z300,z6]),(0,[z126,z0,z1,z2,z4,z188]),(0,[z0,z1,z2,z14,z6,z88]),(0,[z0,z1,z3,z33,z6,z546]),(0,[z0,z1,z934,z2,z3,z6])],[(0,[z0,z935,z2,z12,z4,z6]),(0,[z0,z265,z2,z3,z688,z6]),(0,[z0,z1,z936,z2,z3,z6])],[(0,[z139,z0,z1,z2,z39,z6]),(0,[z73,z1,z26,z2,z3,z82]),(1,[z0,z1,z12,z4,z148]),(0,[z0,z1,z12,z4,z6,z148]),(0,[z15,z0,z2,z17,z51,z6]),(0,[z0,z1,z26,z12,z6,z47]),(0,[z0,z1,z16,z30,z12,z6]),(0,[z0,z1,z2,z3,z937,z6]),(0,[z0,z1,z450,z2,z166,z6]),(0,[z138,z1,z2,z3,z217,z6]),(0,[z0,z323,z16,z2,z3,z6]),(0,[z0,z1,z2,z3,z938,z6])],[(0,[z0,z1,z407,z12,z4,z6]),(0,[z939,z0,z1,z2,z4,z6]),(0,[z74,z0,z1,z460,z3,z6]),(0,[z37,z0,z1,z3,z217,z47])],[(0,[z337,z115,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z33,z469]),(0,[z57,z0,z16,z2,z3,z91]),(0,[z139,z0,z1,z149,z2,z6]),(0,[z11,z0,z1,z26,z33,z6]),(0,[z0,z1,z2,z93,z14,z6]),(0,[z222,z1,z2,z76,z4,z6])],[(0,[z0,z2,z3,z788,z4,z6]),(0,[z0,z1,z311,z12,z4,z6]),(0,[z209,z0,z1,z16,z2,z6]),(0,[z127,z0,z1,z2,z3,z92]),(0,[z447,z512,z2,z3,z4,z6]),(0,[z0,z1,z940,z3,z4,z6]),(0,[z0,z1,z2,z3,z6,z898])],[(0,[z0,z64,z306,z3,z4,z6]),(0,[z0,z1,z498,z12,z4,z6]),(0,[z0,z220,z26,z2,z3,z6])],[(0,[z0,z1,z941,z3,z4,z6]),(0,[z0,z64,z2,z3,z4,z534]),(0,[z11,z0,z1,z122,z2,z6]),(0,[z942,z1,z2,z3,z4,z6]),(0,[z335,z267,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z943,z6]),(0,[z0,z1,z2,z3,z4,z944]),(0,[z28,z0,z1,z2,z14,z377]),(0,[z126,z0,z1,z945,z4,z6]),(0,[z447,z1,z2,z3,z33,z6])]],
   [[(0,[z0,z1,z2,z946,z4,z6]),(0,[z216,z0,z3,z17,z4,z6]),(1,[z0,z1,z2,z947,z6]),(0,[z0,z488,z2,z3,z194,z6])],[(0,[z0,z1,z2,z3,z948,z6]),(0,[z11,z0,z220,z2,z277,z6]),(0,[z0,z1,z880,z2,z4,z6]),(0,[z0,z1,z824,z2,z14,z6])],[(0,[z0,z1,z2,z3,z949,z6]),(0,[z0,z1,z306,z3,z950,z6]),(0,[z54,z0,z174,z12,z4,z6]),(0,[z0,z887,z2,z3,z4,z6]),(0,[z0,z1,z2,z951,z33,z6])],[(0,[z0,z1,z2,z308,z4,z44]),(0,[z0,z1,z26,z22,z12,z6]),(0,[z0,z1,z2,z3,z952,z6]),(0,[z0,z1,z953,z2,z3,z6]),(0,[z0,z1,z2,z255,z14,z6]),(0,[z0,z1,z954,z2,z93,z6])],[(0,[z0,z49,z2,z3,z33,z6]),(0,[z0,z1,z2,z3,z6,z955]),(0,[z0,z1,z297,z3,z956,z6]),(1,[z0,z1,z13,z12,z6]),(0,[z236,z11,z0,z1,z194,z6]),(0,[z11,z0,z271,z2,z4,z6])],[(0,[z0,z1,z306,z3,z4,z6]),(0,[z0,z1,z2,z3,z957,z6]),(0,[z0,z1,z2,z39,z14,z6]),(0,[z958,z0,z1,z2,z3,z6]),(0,[z959,z0,z1,z2,z4,z6]),(0,[z0,z1,z16,z960,z3,z6])],[(0,[z94,z1,z381,z22,z3,z6]),(0,[z73,z1,z2,z4,z287,z82]),(0,[z0,z1,z2,z14,z83,z38]),(0,[z961,z0,z1,z2,z33,z6])],[(0,[z0,z1,z2,z3,z962,z6]),(0,[z0,z1,z2,z200,z14,z6]),(0,[z963,z0,z1,z3,z4,z6]),(0,[z417,z0,z488,z2,z4,z6])],[(0,[z0,z1,z2,z3,z4,z964]),(0,[z337,z0,z12,z161,z4,z6]),(0,[z0,z1,z594,z3,z33,z6]),(0,[z0,z1,z26,z2,z3,z469]),(0,[z0,z1,z2,z206,z14,z6]),(0,[z11,z0,z773,z2,z4,z6]),(0,[z0,z1,z2,z63,z135,z6])],[(0,[z0,z1,z2,z134,z856,z6]),(0,[z0,z142,z2,z406,z72,z6]),(0,[z0,z1,z2,z3,z6,z965])],[(0,[z0,z1,z2,z3,z966,z6]),(0,[z0,z1,z16,z2,z6,z287]),(0,[z0,z1,z2,z3,z967,z6]),(0,[z0,z1,z2,z3,z947,z6]),(0,[z0,z1,z2,z3,z411,z6]),(0,[z0,z1,z386,z3,z166,z6]),(0,[z0,z1,z710,z3,z14,z6])],[(0,[z11,z0,z1,z2,z177,z6]),(0,[z968,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z969,z4,z6])],[(0,[z0,z1,z2,z3,z970,z6]),(0,[z73,z1,z2,z3,z418,z82]),(0,[z0,z1,z378,z3,z33,z6]),(0,[z59,z1,z2,z3,z33,z6]),(0,[z11,z0,z488,z2,z33,z6])],[(0,[z28,z0,z64,z2,z14,z6]),(0,[z0,z971,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z972,z6]),(0,[z221,z1,z2,z12,z4,z6]),(0,[z446,z0,z2,z17,z4,z6]),(0,[z0,z488,z16,z2,z3,z6]),(0,[z0,z973,z2,z3,z4,z6]),(0,[z0,z1,z2,z135,z6,z38])],[(0,[z0,z1,z2,z12,z4,z6]),(0,[z598,z0,z1,z3,z33,z6]),(0,[z974,z0,z1,z2,z4,z6]),(0,[z0,z1,z16,z880,z2,z6])],[(0,[z0,z1,z2,z405,z14,z6]),(0,[z221,z1,z2,z307,z4,z6]),(0,[z190,z0,z1,z2,z975,z6]),(0,[z0,z1,z2,z12,z155,z6]),(0,[z244,z0,z1,z16,z2,z6]),(0,[z0,z1,z2,z63,z166,z6]),(0,[z0,z1,z2,z3,z487,z6]),(0,[z423,z0,z1,z2,z3,z624])]],
   [[(0,[z0,z1,z2,z3,z976,z6]),(0,[z0,z1,z2,z3,z4,z977]),(0,[z0,z1,z2,z443,z33,z6])],[(0,[z0,z1,z2,z3,z978,z6]),(0,[z0,z1,z2,z308,z4,z6]),(0,[z0,z49,z26,z2,z3,z6]),(0,[z0,z1,z16,z157,z3,z6]),(0,[z196,z0,z1,z468,z4,z6])],[(0,[z103,z1,z2,z12,z104,z6]),(0,[z0,z1,z2,z12,z109,z6]),(0,[z0,z1,z30,z3,z33,z172]),(0,[z0,z1,z189,z339,z4,z6])],[(0,[z0,z1,z979,z2,z3,z6]),(0,[z11,z0,z1,z2,z191,z6]),(0,[z0,z1,z2,z704,z14,z6]),(0,[z0,z1,z13,z2,z63,z6])],[(0,[z0,z1,z980,z3,z4,z6]),(0,[z981,z0,z1,z2,z4,z6]),(0,[z0,z1,z2,z3,z4,z982]),(0,[z0,z1,z2,z3,z177,z524]),(0,[z0,z1,z2,z3,z6,z983]),(0,[z0,z106,z1,z26,z12,z6]),(0,[z0,z984,z2,z3,z4,z6]),(0,[z0,z1,z680,z3,z33,z6]),(0,[z0,z1,z523,z3,z33,z6])],[(0,[z80,z0,z1,z2,z135,z6]),(0,[z11,z0,z1,z2,z194,z6]),(0,[z0,z1,z149,z3,z109,z6]),(0,[z0,z1,z231,z3,z14,z6])],[(0,[z73,z1,z2,z3,z4,z82]),(0,[z11,z289,z0,z1,z2,z6]),(0,[z0,z1,z2,z12,z117,z6]),(0,[z11,z0,z789,z2,z4,z6]),(0,[z62,z0,z1,z2,z33,z38]),(0,[z0,z1,z30,z3,z217,z6]),(0,[z0,z1,z2,z3,z985,z6]),(0,[z0,z1,z2,z14,z6,z162]),(0,[z986,z0,z1,z157,z4,z6])],[],[(0,[z0,z1,z2,z3,z4,z377]),(0,[z0,z1,z2,z326,z4,z188]),(0,[z0,z1,z26,z2,z443,z6])],[(0,[z0,z1,z2,z300,z4,z6]),(0,[z289,z1,z2,z3,z7,z6]),(0,[z0,z1,z2,z406,z14,z6]),(0,[z140,z1,z468,z3,z4,z6])],[(0,[z0,z1,z2,z3,z987,z6]),(0,[z0,z1,z2,z848,z4,z6]),(0,[z71,z0,z2,z3,z6,z548]),(0,[z0,z988,z2,z3,z4,z6])],[(0,[z0,z119,z306,z3,z4,z6]),(0,[z0,z2,z17,z14,z6,z91]),(0,[z989,z0,z1,z2,z4,z6]),(0,[z0,z1,z699,z3,z33,z6]),(0,[z160,z1,z189,z3,z4,z6])],[(0,[z80,z0,z1,z2,z166,z6]),(0,[z0,z1,z990,z3,z4,z6]),(0,[z0,z410,z2,z3,z14,z6]),(0,[z0,z1,z991,z2,z3,z6]),(0,[z0,z1,z2,z3,z992,z6])],[(0,[z209,z0,z1,z315,z2,z6])],[(0,[z21,z1,z3,z753,z4,z6]),(0,[z54,z221,z1,z12,z4,z6]),(0,[z0,z1,z2,z581,z166,z6]),(0,[z0,z1,z26,z2,z346,z6]),(0,[z0,z1,z2,z993,z4,z6])],[(0,[z994,z0,z1,z3,z4,z6]),(0,[z0,z1,z2,z4,z6,z287]),(0,[z0,z1,z995,z3,z4,z6])]],
   [[(0,[z0,z49,z2,z3,z4,z44]),(0,[z317,z0,z1,z12,z4,z6]),(0,[z1,z2,z3,z846,z7,z6]),(0,[z0,z1,z3,z33,z83,z47]),(0,[z0,z1,z2,z17,z166,z6]),(0,[z37,z0,z1,z3,z4,z996]),(0,[z997,z1,z2,z3,z4,z6]),(0,[z0,z314,z157,z3,z4,z6]),(0,[z127,z0,z1,z2,z76,z32])],[(0,[z21,z1,z308,z161,z4,z6]),(0,[z0,z998,z2,z3,z4,z6]),(0,[z11,z0,z1,z405,z4,z6]),(0,[z28,z395,z1,z2,z4,z6]),(0,[z190,z0,z1,z2,z14,z6]),(0,[z453,z641,z1,z2,z4,z6])],[(0,[z11,z0,z1,z249,z2,z6]),(0,[z11,z0,z1,z26,z2,z6]),(0,[z0,z1,z999,z2,z3,z6]),(0,[z131,z0,z1000,z2,z4,z6])],[(0,[z0,z1,z16,z2,z299,z6]),(0,[z96,z0,z1,z2,z3,z32])],[(0,[z0,z119,z2,z12,z4,z6]),(0,[z0,z1,z2,z1001,z4,z6]),(0,[z236,z221,z1,z3,z4,z6]),(0,[z238,z1,z2,z3,z33,z6]),(0,[z0,z1,z2,z307,z1002,z6]),(0,[z0,z106,z225,z3,z4,z6]),(0,[z0,z1,z3,z4,z6,z996]),(0,[z140,z1,z2,z3,z487,z6]),(0,[z0,z253,z231,z3,z4,z6])],[(0,[z0,z1003,z2,z3,z4,z6]),(0,[z1,z2,z3,z753,z4,z6]),(0,[z0,z1,z945,z3,z4,z6]),(0,[z0,z1,z1004,z2,z3,z6]),(0,[z0,z2,z788,z17,z4,z6]),(0,[z0,z19,z2,z17,z14,z6]),(0,[z0,z52,z2,z3,z72,z6]),(0,[z0,z1,z2,z3,z1005,z6]),(0,[z131,z0,z1,z2,z985,z6]),(0,[z160,z1,z157,z3,z4,z6])],[(0,[z0,z1,z2,z3,z1006,z6]),(0,[z1007,z0,z1,z2,z4,z6]),(0,[z303,z0,z1,z16,z2,z6]),(0,[z0,z1,z849,z99,z3,z6]),(0,[z0,z253,z2,z3,z14,z6])],[(0,[z0,z2,z3,z1008,z4,z6]),(0,[z420,z0,z1,z12,z4,z6]),(0,[z0,z1,z2,z93,z217,z6])],[(0,[z0,z1,z2,z1009,z4,z6]),(0,[z11,z0,z1,z97,z4,z6]),(0,[z1010,z1,z2,z3,z4,z6]),(0,[z0,z512,z2,z3,z33,z6]),(0,[z830,z1,z2,z3,z4,z6])],[(0,[z447,z1,z2,z3,z4,z6]),(0,[z0,z1,z293,z12,z4,z6])],[(0,[z43,z55,z16,z2,z3,z6]),(0,[z11,z795,z0,z1,z4,z6]),(0,[z0,z1,z341,z3,z33,z6]),(0,[z0,z1,z2,z214,z33,z6]),(0,[z0,z1,z2,z339,z4,z6])],[(0,[z0,z1,z2,z1011,z4,z6]),(0,[z248,z1,z2,z3,z4,z82]),(0,[z0,z1,z231,z3,z159,z6])],[(0,[z1012,z0,z1,z2,z4,z6]),(0,[z0,z2,z3,z14,z6,z84]),(0,[z0,z267,z2,z12,z4,z6]),(0,[z0,z1,z2,z951,z4,z6]),(0,[z1013,z0,z1,z2,z4,z6])],[(0,[z126,z0,z1,z26,z2,z6]),(0,[z54,z221,z3,z66,z4,z6]),(0,[z0,z1014,z2,z12,z4,z6]),(0,[z0,z1,z2,z3,z1015,z6])],[(0,[z0,z49,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z1016,z6]),(0,[z0,z2,z3,z892,z4,z6]),(0,[z0,z1,z2,z81,z452,z6]),(0,[z0,z119,z2,z3,z4,z377]),(0,[z0,z1,z595,z12,z4,z6]),(0,[z383,z1,z2,z3,z7,z6]),(0,[z0,z142,z2,z187,z72,z6]),(0,[z11,z0,z1,z189,z4,z6]),(0,[z0,z1,z30,z3,z33,z47]),(0,[z0,z1,z13,z3,z33,z6]),(0,[z0,z1017,z1,z2,z3,z6])],[(0,[z0,z1,z2,z3,z1018,z6]),(0,[z0,z1,z2,z3,z1019,z6]),(0,[z0,z64,z2,z3,z39,z6]),(0,[z0,z2,z3,z4,z6,z1020]),(0,[z1,z2,z3,z200,z4,z82]),(0,[z0,z1,z849,z2,z3,z6]),(0,[z131,z0,z1,z2,z895,z6])]],
   [[(0,[z28,z0,z1,z2,z14,z534]),(0,[z0,z1,z2,z507,z14,z6]),(0,[z961,z0,z1,z2,z4,z6]),(0,[z0,z1,z1021,z2,z3,z6])],[(1,[z858,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z452,z6]),(0,[z238,z1,z26,z2,z3,z6]),(0,[z11,z0,z1,z276,z2,z6]),(0,[z447,z1,z2,z3,z117,z6]),(0,[z0,z314,z2,z3,z14,z6])],[(0,[z0,z1,z2,z12,z177,z6]),(0,[z0,z1,z2,z3,z6,z1022]),(0,[z0,z1,z2,z3,z578,z469]),(0,[z0,z1,z1023,z2,z3,z6]),(0,[z11,z0,z1,z2,z235,z6]),(0,[z0,z1,z2,z3,z1024,z6]),(0,[z11,z0,z1,z2,z1025,z6]),(0,[z0,z1026,z26,z2,z3,z6])],[(0,[z21,z49,z3,z161,z4,z6]),(0,[z0,z1,z2,z3,z1027,z6]),(0,[z0,z1,z2,z3,z454,z6]),(0,[z107,z80,z1,z2,z14,z6]),(0,[z0,z1,z2,z187,z72,z6]),(0,[z0,z265,z2,z3,z72,z6]),(0,[z0,z1,z2,z3,z1028,z6]),(0,[z209,z0,z220,z2,z4,z6]),(0,[z0,z1,z2,z1029,z4,z6]),(0,[z0,z156,z125,z2,z3,z6])],[(0,[z0,z1,z2,z299,z14,z6]),(0,[z0,z1,z2,z3,z1030,z6]),(0,[z0,z1,z1031,z2,z3,z6]),(0,[z140,z1,z26,z2,z3,z6]),(0,[z0,z1,z266,z2,z14,z6])],[(0,[z0,z1,z2,z3,z6,z1032]),(0,[z0,z1,z2,z308,z177,z6]),(0,[z309,z0,z1,z2,z14,z6]),(0,[z317,z0,z1,z2,z755,z6]),(0,[z641,z1,z2,z78,z4,z6]),(0,[z103,z1,z2,z3,z612,z6]),(0,[z0,z1,z2,z3,z4,z1033]),(0,[z0,z1,z30,z3,z166,z6]),(0,[z0,z512,z26,z2,z3,z6]),(0,[z0,z271,z2,z3,z14,z6]),(0,[z0,z1,z157,z3,z31,z6])],[(0,[z59,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z168,z14,z6]),(0,[z0,z1,z2,z3,z132,z469]),(0,[z11,z0,z488,z2,z4,z6]),(0,[z0,z1,z128,z12,z33,z6]),(0,[z0,z862,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z1034,z6]),(0,[z0,z1,z2,z3,z39,z6]),(0,[z238,z1,z2,z3,z4,z469]),(0,[z0,z1,z2,z3,z1035,z6]),(0,[z0,z1,z460,z2,z3,z6])],[(0,[z0,z1,z2,z3,z6,z418]),(0,[z0,z1036,z2,z3,z33,z6]),(0,[z0,z1,z276,z2,z3,z6]),(0,[z0,z1,z2,z3,z1037,z6])],[(0,[z54,z0,z3,z456,z4,z6]),(0,[z313,z0,z1,z16,z2,z6])],[(0,[z0,z1,z1038,z2,z3,z6]),(0,[z0,z1,z2,z12,z191,z6]),(0,[z219,z0,z2,z3,z210,z6])],[(0,[z126,z0,z1,z2,z1039,z6]),(0,[z0,z1,z3,z33,z60,z47]),(0,[z227,z0,z1,z2,z4,z38])],[(0,[z126,z140,z1,z2,z4,z6]),(0,[z0,z1,z2,z3,z1040,z6]),(0,[z1041,z0,z1,z2,z4,z6]),(0,[z0,z1,z2,z12,z194,z6]),(0,[z0,z1,z30,z3,z4,z172]),(0,[z0,z1,z619,z2,z14,z6]),(0,[z0,z253,z2,z3,z159,z6])],[(0,[z317,z94,z1,z22,z4,z6]),(0,[z0,z1,z22,z12,z14,z6]),(1,[z0,z119,z2,z14,z6]),(0,[z71,z0,z1,z157,z3,z6]),(0,[z0,z488,z3,z12,z4,z6]),(0,[z0,z1042,z1,z2,z3,z6]),(0,[z0,z1,z266,z2,z339,z6])],[(0,[z0,z1,z12,z161,z166,z6]),(0,[z0,z1,z2,z187,z14,z6])],[(0,[z0,z448,z2,z3,z14,z6]),(0,[z28,z1,z2,z848,z4,z6]),(0,[z73,z11,z1,z2,z4,z82]),(1,[z0,z1,z748,z4,z6]),(0,[z0,z1,z2,z788,z4,z6]),(0,[z295,z0,z2,z3,z29,z6]),(0,[z0,z1,z2,z12,z4,z1043]),(0,[z0,z1,z12,z4,z6,z282]),(0,[z0,z1,z497,z12,z4,z6]),(0,[z0,z1,z276,z2,z12,z6]),(0,[z0,z1,z3,z97,z33,z6])]],
   [[(0,[z0,z1,z30,z12,z33,z6]),(0,[z138,z323,z2,z3,z4,z6]),(0,[z62,z0,z1,z2,z4,z38])],[(0,[z0,z538,z1,z12,z4,z6]),(0,[z0,z1,z16,z2,z3,z534]),(0,[z417,z0,z1,z2,z14,z6]),(0,[z0,z1,z880,z2,z3,z6])],[(0,[z42,z115,z2,z3,z14,z6]),(0,[z1044,z1,z2,z3,z4,z6])],[(0,[z54,z0,z470,z3,z4,z6]),(0,[z317,z0,z1,z16,z2,z6]),(0,[z1045,z0,z1,z2,z4,z6]),(0,[z289,z0,z1,z2,z6,z287]),(0,[z0,z1,z2,z3,z1046,z6]),(0,[z0,z1,z157,z12,z4,z6]),(0,[z0,z314,z2,z76,z4,z6])],[(0,[z0,z1,z2,z1047,z4,z6]),(0,[z0,z1,z2,z3,z1048,z6]),(0,[z0,z2,z41,z17,z4,z6])],[(0,[z193,z0,z1,z2,z14,z6]),(0,[z0,z1,z26,z2,z1049,z6]),(0,[z62,z0,z1,z2,z4,z1050])],[(0,[z0,z1,z2,z1051,z4,z6]),(0,[z0,z1,z2,z3,z1052,z6]),(0,[z0,z1,z2,z41,z33,z6]),(0,[z0,z1,z315,z2,z3,z6]),(0,[z222,z314,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z33,z44]),(0,[z317,z0,z1,z306,z4,z6]),(0,[z0,z1,z121,z3,z33,z6]),(0,[z0,z1,z468,z3,z4,z6]),(0,[z0,z323,z2,z3,z14,z6]),(0,[z0,z271,z2,z76,z4,z6])],[(0,[z28,z80,z1,z2,z14,z6]),(0,[z139,z0,z1,z297,z4,z6])],[(0,[z0,z1,z2,z3,z4,z534]),(0,[z1053,z0,z1,z3,z4,z6]),(0,[z0,z1,z2,z1054,z4,z6]),(0,[z57,z0,z2,z3,z14,z91]),(0,[z420,z0,z2,z3,z4,z91]),(0,[z0,z1,z26,z2,z732,z6]),(0,[z284,z0,z1,z3,z109,z6])],[(0,[z337,z11,z0,z2,z4,z6]),(0,[z0,z1,z2,z17,z277,z6]),(0,[z0,z1,z1055,z3,z4,z6]),(0,[z0,z1,z460,z30,z3,z172]),(0,[z0,z1,z2,z203,z14,z6]),(0,[z0,z1,z16,z2,z76,z6]),(0,[z222,z271,z2,z3,z4,z6])],[(0,[z115,z2,z470,z3,z4,z6]),(0,[z0,z1,z490,z12,z4,z6]),(0,[z143,z0,z2,z3,z29,z6]),(0,[z0,z1,z2,z3,z1056,z6]),(0,[z11,z0,z988,z2,z4,z6])],[(0,[z0,z1,z405,z78,z4,z6]),(0,[z0,z1,z2,z307,z4,z148]),(1,[z0,z1,z880,z2,z6]),(0,[z96,z0,z1,z2,z4,z38])],[(0,[z0,z1,z1057,z2,z3,z6]),(0,[z0,z64,z2,z3,z33,z6]),(0,[z0,z1,z12,z4,z6,z301]),(0,[z37,z0,z1,z26,z3,z47])],[(0,[z238,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z1058,z4,z6]),(0,[z0,z1,z2,z3,z1059,z6]),(0,[z446,z0,z2,z581,z4,z6]),(0,[z37,z0,z1,z12,z4,z47]),(0,[z62,z0,z1,z2,z4,z557])],[(0,[z0,z1,z1060,z2,z3,z6]),(0,[z80,z1,z26,z2,z78,z6]),(0,[z0,z1,z2,z1061,z4,z6]),(0,[z0,z1026,z2,z3,z4,z6])]],
   [[(0,[z0,z1,z26,z2,z81,z6]),(0,[z0,z512,z2,z443,z4,z6])],[(0,[z1,z3,z753,z161,z4,z6]),(0,[z1062,z0,z1,z22,z4,z6]),(0,[z73,z1,z16,z2,z3,z82]),(0,[z0,z1,z2,z3,z1063,z6]),(0,[z0,z1064,z1,z2,z3,z6]),(0,[z11,z0,z1,z2,z1065,z6]),(0,[z0,z1,z468,z4,z6,z38]),(0,[z0,z1,z2,z3,z6,z1066])],[(0,[z0,z16,z2,z3,z197,z6]),(0,[z0,z1,z2,z81,z33,z6]),(0,[z0,z1,z1067,z2,z3,z6]),(0,[z0,z512,z2,z3,z4,z6]),(0,[z0,z208,z2,z3,z4,z60]),(0,[z11,z0,z1,z2,z1068,z6]),(0,[z1069,z0,z1,z2,z4,z6])],[(0,[z0,z2,z3,z4,z6,z1070]),(0,[z0,z1,z16,z2,z3,z377]),(0,[z0,z2,z3,z4,z84,z47]),(0,[z1071,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z392,z4,z6])],[(0,[z0,z1,z26,z2,z3,z44]),(0,[z0,z106,z46,z12,z4,z6]),(0,[z0,z106,z1,z12,z14,z6]),(0,[z0,z1,z1072,z2,z4,z6])],[(0,[z0,z1,z2,z3,z33,z6]),(0,[z0,z1,z2,z3,z1073,z6]),(0,[z0,z1,z12,z4,z91,z47]),(0,[z1074,z1,z2,z3,z4,z6]),(0,[z11,z0,z323,z2,z4,z6])],[(1,[z1,z3,z753,z4,z6]),(0,[z0,z1,z1075,z2,z3,z6]),(0,[z0,z1,z2,z307,z14,z6]),(0,[z0,z1,z1076,z2,z3,z6]),(0,[z1077,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z4,z1050])],[(0,[z42,z221,z2,z3,z4,z6]),(0,[z28,z0,z1,z468,z4,z6]),(0,[z0,z1,z2,z3,z1078,z6]),(0,[z0,z1,z2,z3,z1079,z6]),(1,[z0,z1,z2,z3,z898])],[(0,[z130,z115,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z1080,z6]),(0,[z80,z1,z2,z118,z4,z6]),(0,[z1081,z1,z2,z3,z4,z6]),(0,[z0,z1,z3,z217,z6,z47])],[(0,[z11,z0,z2,z4,z6,z84]),(0,[z0,z1,z2,z41,z4,z469]),(0,[z0,z2,z3,z4,z6,z826]),(0,[z0,z1,z2,z12,z235,z6]),(0,[z519,z0,z1,z2,z3,z32])],[(0,[z0,z1,z2,z3,z1082,z6]),(0,[z21,z1,z3,z161,z33,z6]),(0,[z0,z1083,z2,z3,z4,z6]),(0,[z0,z64,z26,z2,z3,z6]),(0,[z1084,z0,z1,z2,z4,z6]),(0,[z0,z2,z3,z756,z72,z6])],[(0,[z0,z1,z2,z299,z1085,z6]),(0,[z0,z1,z2,z3,z4,z1086]),(0,[z238,z1,z2,z3,z578,z6]),(0,[z216,z0,z1,z123,z14,z6]),(0,[z0,z1,z2,z1087,z4,z6]),(0,[z227,z0,z1,z12,z4,z47]),(0,[z0,z488,z2,z3,z14,z6])],[(0,[z0,z1,z1088,z3,z4,z6]),(0,[z28,z1,z2,z79,z14,z6]),(0,[z0,z488,z2,z17,z4,z6]),(0,[z11,z0,z1089,z2,z4,z6]),(0,[z0,z1,z2,z3,z1090,z6])],[(0,[z0,z220,z2,z3,z4,z6]),(1,[z0,z220,z2,z14,z6]),(0,[z0,z1,z3,z33,z6,z647])],[(0,[z0,z2,z12,z197,z4,z6]),(0,[z0,z1091,z2,z3,z4,z6]),(0,[z0,z1,z2,z166,z6,z50])],[(0,[z0,z119,z2,z3,z4,z534]),(0,[z238,z1,z2,z3,z132,z6]),(0,[z0,z1,z26,z2,z134,z6]),(0,[z236,z11,z0,z1,z14,z6]),(0,[z0,z1,z157,z339,z4,z6])]],
   [[(0,[z0,z1,z2,z1092,z4,z6]),(0,[z0,z1,z2,z1093,z4,z6]),(0,[z0,z1,z128,z12,z4,z6]),(0,[z795,z0,z1,z128,z4,z6]),(0,[z0,z1,z2,z319,z14,z6]),(0,[z0,z885,z2,z3,z14,z6]),(0,[z0,z1,z2,z3,z4,z1050])],[(0,[z42,z2,z3,z4,z6,z580]),(0,[z24,z1,z429,z2,z3,z6]),(0,[z0,z1,z1094,z2,z41,z6]),(0,[z0,z1,z26,z3,z242,z6]),(0,[z1095,z0,z1,z2,z4,z6]),(0,[z62,z0,z253,z2,z4,z38])],[(0,[z0,z1,z26,z2,z3,z6]),(0,[z0,z1,z2,z1096,z4,z6]),(0,[z0,z1036,z2,z3,z4,z6]),(0,[z131,z0,z1097,z2,z4,z6])],[(0,[z0,z2,z1098,z3,z4,z6]),(0,[z1099,z0,z1,z2,z4,z6]),(0,[z105,z55,z2,z3,z4,z6]),(0,[z11,z0,z1,z13,z2,z6]),(0,[z11,z0,z1,z2,z1100,z6]),(0,[z196,z0,z1,z2,z14,z6])],[(0,[z0,z1,z2,z1101,z4,z6]),(0,[z0,z1,z2,z3,z4,z1102]),(0,[z126,z289,z0,z1,z2,z6]),(0,[z54,z0,z333,z3,z4,z6]),(0,[z0,z1,z16,z718,z2,z6]),(0,[z447,z1,z16,z2,z3,z6]),(0,[z0,z1,z2,z14,z6,z282])],[(0,[z0,z1,z2,z1103,z4,z6]),(0,[z11,z0,z142,z2,z72,z6]),(0,[z0,z267,z468,z3,z4,z6])],[(0,[z11,z0,z1,z2,z4,z148]),(0,[z1,z2,z3,z4,z6,z1104]),(0,[z0,z1,z2,z12,z1105,z6]),(0,[z0,z1,z991,z2,z12,z6]),(0,[z0,z1,z824,z2,z63,z6]),(0,[z1106,z0,z1,z2,z4,z6])],[(0,[z54,z0,z2,z17,z14,z6]),(0,[z0,z1,z297,z3,z14,z6]),(0,[z0,z1,z484,z12,z4,z6]),(0,[z0,z1,z1107,z2,z3,z6]),(0,[z11,z0,z787,z2,z4,z6]),(0,[z335,z1,z231,z3,z4,z6])],[(0,[z0,z1108,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z469]),(0,[z0,z1,z41,z12,z4,z6]),(0,[z0,z1,z26,z2,z41,z6]),(0,[z54,z0,z12,z17,z4,z6]),(0,[z11,z0,z1,z704,z4,z6]),(0,[z11,z335,z1,z2,z4,z6])],[(0,[z0,z1,z2,z4,z6,z1109]),(0,[z0,z49,z16,z2,z3,z6]),(0,[z0,z1,z2,z1110,z4,z6]),(0,[z0,z1,z405,z3,z14,z6]),(0,[z15,z0,z220,z2,z4,z6]),(0,[z216,z0,z18,z3,z4,z6]),(0,[z0,z1,z26,z297,z3,z6]),(0,[z0,z1,z26,z2,z12,z6]),(0,[z0,z1,z2,z3,z818,z6]),(0,[z11,z0,z1,z2,z1111,z6]),(0,[z335,z1,z2,z3,z14,z6])],[(0,[z28,z140,z1,z2,z4,z6]),(0,[z0,z1,z2,z1112,z4,z6]),(0,[z0,z18,z2,z123,z33,z6]),(0,[z0,z1,z30,z12,z4,z6]),(0,[z819,z1,z2,z3,z4,z6]),(0,[z140,z1,z2,z3,z33,z6]),(0,[z0,z1,z2,z3,z1113,z6])],[(0,[z0,z1,z1114,z3,z4,z6]),(0,[z43,z221,z2,z3,z4,z6]),(0,[z0,z1,z1115,z2,z3,z6]),(0,[z0,z1,z2,z33,z6,z287]),(0,[z0,z1,z1116,z2,z123,z6]),(0,[z127,z11,z0,z1,z2,z32])],[(0,[z0,z1,z2,z1117,z4,z6]),(0,[z1,z2,z3,z79,z4,z377]),(0,[z0,z1,z26,z2,z307,z6]),(0,[z154,z0,z2,z17,z4,z6]),(0,[z0,z1118,z2,z3,z4,z6]),(0,[z0,z1119,z2,z3,z33,z6])],[(0,[z94,z1,z415,z3,z4,z6]),(0,[z0,z1120,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z826]),(0,[z795,z0,z1,z12,z4,z6]),(0,[z0,z323,z2,z93,z4,z6])],[(0,[z11,z0,z1,z230,z4,z6]),(1,[z0,z3,z783,z4,z6]),(0,[z0,z18,z2,z123,z508,z6]),(0,[z0,z1,z2,z3,z829,z6]),(0,[z11,z0,z1,z30,z33,z6])]],
   [[(0,[z0,z1,z1121,z3,z4,z6]),(1,[z0,z2,z3,z756,z6]),(0,[z11,z0,z1,z2,z14,z6]),(0,[z0,z1,z13,z12,z14,z6]),(0,[z0,z1,z16,z2,z443,z6]),(0,[z0,z1,z1122,z2,z3,z6]),(0,[z140,z1,z2,z3,z4,z38]),(0,[z0,z267,z2,z3,z487,z6])],[(0,[z147,z0,z1,z12,z4,z6]),(0,[z0,z1,z2,z3,z4,z44]),(0,[z59,z1,z16,z2,z3,z6]),(0,[z11,z0,z1,z149,z12,z6]),(0,[z11,z0,z488,z26,z2,z6]),(0,[z0,z1,z2,z1123,z33,z6]),(0,[z127,z160,z1,z2,z3,z32])],[(0,[z0,z1,z2,z809,z4,z6]),(0,[z80,z1,z2,z78,z454,z6]),(0,[z0,z1,z16,z2,z502,z6]),(0,[z54,z0,z41,z66,z4,z6]),(0,[z216,z0,z1,z3,z33,z6]),(0,[z0,z1,z149,z12,z6,z47]),(0,[z11,z0,z1,z319,z4,z6]),(0,[z1124,z0,z1,z2,z4,z6])],[(0,[z1125,z0,z1,z3,z4,z6]),(0,[z0,z52,z1,z2,z3,z6]),(0,[z0,z323,z2,z3,z217,z6])],[(0,[z0,z1,z2,z3,z1126,z6]),(0,[z0,z1,z2,z1127,z4,z6]),(0,[z101,z410,z2,z3,z4,z6])],[(0,[z0,z1128,z1,z2,z3,z6]),(0,[z0,z1,z26,z30,z3,z172]),(0,[z127,z222,z1,z2,z3,z32])],[(0,[z21,z1,z3,z161,z4,z44]),(0,[z0,z1,z1129,z2,z81,z6]),(0,[z0,z1,z2,z919,z14,z6]),(0,[z11,z0,z19,z2,z4,z60]),(0,[z0,z1,z2,z346,z14,z6]),(0,[z0,z1,z2,z171,z33,z6])],[(0,[z0,z64,z2,z3,z4,z6]),(0,[z0,z1,z297,z4,z14,z6]),(0,[z216,z0,z1,z3,z508,z6]),(0,[z0,z1,z2,z660,z14,z6]),(0,[z0,z1,z26,z12,z33,z6]),(0,[z236,z0,z1,z13,z3,z6]),(0,[z62,z0,z1,z468,z4,z38])],[(0,[z0,z119,z26,z2,z3,z6]),(0,[z0,z1,z1130,z306,z3,z6]),(0,[z54,z11,z0,z66,z4,z6]),(0,[z54,z0,z1,z12,z33,z6]),(0,[z0,z1,z2,z1131,z4,z6]),(0,[z0,z1132,z2,z3,z4,z6]),(0,[z335,z253,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z14,z524]),(0,[z1133,z0,z2,z3,z4,z6]),(0,[z0,z1,z405,z4,z14,z6]),(0,[z0,z1,z2,z14,z6,z305]),(0,[z160,z1,z2,z3,z14,z6]),(0,[z0,z1,z2,z3,z898,z32])],[(0,[z0,z1,z2,z3,z4,z1134]),(0,[z103,z1,z2,z3,z118,z6]),(0,[z0,z1,z12,z272,z4,z6]),(0,[z0,z1,z1135,z3,z4,z6]),(0,[z11,z0,z1,z2,z1136,z6])],[(0,[z0,z1,z2,z3,z1137,z6]),(0,[z0,z1,z2,z3,z1138,z6]),(0,[z0,z1,z2,z3,z769,z6]),(0,[z0,z395,z1,z12,z4,z6]),(0,[z62,z0,z1,z26,z2,z38])],[(0,[z0,z1,z2,z81,z4,z6]),(0,[z0,z1,z149,z22,z12,z6]),(0,[z221,z106,z2,z3,z4,z6]),(0,[z0,z18,z26,z2,z123,z6]),(0,[z1139,z0,z1,z2,z4,z6]),(0,[z0,z1,z566,z12,z4,z6]),(0,[z0,z1,z2,z63,z277,z6])],[(0,[z1,z2,z3,z161,z4,z44]),(0,[z0,z1,z2,z41,z578,z6]),(0,[z0,z106,z1,z134,z4,z6]),(0,[z190,z0,z1,z16,z2,z6]),(0,[z0,z1,z2,z515,z14,z6]),(0,[z0,z1,z2,z443,z4,z6]),(0,[z400,z11,z0,z1,z4,z6])],[(0,[z126,z0,z1140,z2,z4,z6]),(0,[z0,z1,z2,z3,z6,z1141]),(0,[z0,z1,z2,z1142,z4,z6]),(0,[z0,z1,z460,z189,z3,z6])],[(0,[z42,z614,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z1143,z6]),(0,[z1,z2,z3,z4,z172,z53]),(0,[z11,z0,z1,z12,z33,z6]),(0,[z335,z1,z2,z3,z159,z6])]],
   [[(0,[z0,z1,z2,z3,z6,z866]),(0,[z1144,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z12,z1145,z6]),(0,[z0,z1,z2,z14,z6,z50]),(0,[z0,z1,z189,z3,z33,z6]),(0,[z1146,z1,z2,z3,z4,z6]),(0,[z0,z1,z814,z3,z14,z6])],[(0,[z0,z1,z2,z3,z778,z6]),(0,[z0,z1,z2,z41,z132,z6]),(0,[z0,z1,z2,z123,z14,z6]),(0,[z15,z0,z2,z788,z4,z6]),(0,[z0,z1,z2,z3,z1147,z6]),(0,[z0,z1,z460,z2,z12,z6]),(0,[z0,z1,z276,z2,z14,z6])],[(0,[z0,z1,z2,z4,z6,z1148]),(0,[z238,z1,z2,z41,z4,z6]),(0,[z0,z1,z2,z123,z135,z6]),(0,[z0,z1,z386,z12,z4,z6]),(0,[z0,z1,z1149,z3,z4,z6]),(0,[z0,z1,z880,z152,z2,z6])],[(0,[z0,z1,z2,z3,z4,z1150]),(0,[z0,z1,z3,z4,z6,z1151]),(0,[z0,z1,z1152,z2,z3,z6]),(0,[z1153,z0,z2,z12,z4,z6])],[(0,[z0,z1,z2,z3,z4,z1154]),(0,[z21,z1,z3,z161,z4,z6]),(0,[z24,z1,z2,z12,z7,z6]),(0,[z0,z1,z234,z2,z3,z6]),(0,[z74,z0,z1,z26,z3,z6]),(0,[z535,z1,z2,z3,z118,z6])],[(0,[z0,z1,z556,z12,z4,z6]),(0,[z0,z1155,z2,z3,z4,z6]),(0,[z0,z1,z26,z2,z187,z6]),(0,[z0,z1,z30,z392,z33,z6]),(0,[z0,z1,z2,z443,z117,z6])],[(0,[z0,z2,z3,z197,z33,z6]),(0,[z94,z1,z3,z753,z4,z6]),(0,[z0,z1,z2,z3,z1156,z6]),(0,[z59,z19,z2,z3,z4,z6]),(0,[z0,z1,z311,z3,z33,z6]),(0,[z0,z1,z2,z3,z793,z6]),(0,[z11,z0,z1,z2,z159,z6]),(1,[z0,z1,z3,z4,z996])],[(0,[z1,z2,z3,z4,z316,z82]),(1,[z1,z2,z3,z846,z6]),(0,[z0,z1,z2,z3,z479,z6]),(0,[z0,z1,z2,z372,z14,z6]),(0,[z0,z1,z2,z3,z1157,z6]),(0,[z0,z142,z2,z12,z72,z6]),(0,[z942,z1,z2,z3,z14,z6])],[(0,[z0,z1,z1129,z2,z3,z6]),(0,[z0,z1,z22,z12,z166,z6]),(0,[z0,z1,z99,z3,z33,z6]),(0,[z139,z0,z1,z2,z109,z6]),(0,[z0,z1,z157,z3,z6,z32])],[(0,[z317,z0,z839,z2,z4,z6]),(0,[z0,z1,z405,z79,z4,z6]),(0,[z80,z0,z1,z2,z277,z6]),(0,[z238,z1,z16,z2,z3,z6])],[(0,[z42,z626,z2,z3,z4,z6]),(0,[z0,z1,z2,z1158,z4,z6]),(0,[z1159,z0,z1,z2,z3,z6]),(0,[z0,z1160,z1,z2,z3,z6]),(0,[z0,z1,z2,z12,z1161,z6]),(0,[z0,z1,z2,z3,z4,z882]),(0,[z0,z1,z880,z2,z14,z6]),(0,[z62,z140,z1,z2,z4,z38])],[(0,[z0,z55,z106,z12,z4,z6]),(0,[z317,z0,z1,z2,z925,z6]),(0,[z54,z0,z1,z12,z4,z469]),(0,[z0,z1,z234,z2,z12,z6]),(0,[z74,z0,z1,z26,z12,z6]),(0,[z0,z1,z40,z12,z4,z6]),(0,[z0,z220,z2,z3,z194,z6]),(0,[z160,z1,z2,z76,z4,z6])],[(0,[z1162,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z1163,z4,z6]),(0,[z0,z1,z2,z3,z578,z6]),(0,[z0,z441,z1,z12,z4,z6]),(0,[z0,z1,z2,z3,z1164,z6])],[(0,[z0,z1,z2,z1165,z4,z6]),(0,[z0,z1,z2,z1166,z4,z6]),(0,[z216,z0,z1,z41,z4,z6]),(0,[z0,z1,z2,z12,z4,z148]),(0,[z0,z1,z2,z828,z4,z6]),(0,[z74,z0,z1,z849,z3,z6]),(0,[z0,z512,z16,z2,z3,z6])],[(0,[z101,z1,z12,z161,z4,z6]),(0,[z0,z1,z306,z3,z14,z6]),(0,[z0,z1,z26,z2,z406,z6]),(0,[z0,z1,z2,z474,z4,z188]),(0,[z0,z1,z2,z4,z6,z1050])],[(0,[z1167,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z474,z4,z124]),(0,[z0,z1,z315,z2,z14,z6]),(0,[z0,z1,z2,z392,z1168,z6]),(0,[z0,z1,z2,z3,z6,z1169])]],
   [[(0,[z0,z1,z2,z1170,z4,z6]),(0,[z0,z1,z2,z3,z1171,z6]),(0,[z0,z119,z2,z3,z39,z6]),(0,[z0,z1,z2,z3,z132,z6]),(0,[z0,z1,z2,z3,z1172,z6]),(0,[z0,z1,z2,z683,z14,z6]),(0,[z193,z0,z1,z2,z166,z6]),(0,[z138,z1,z2,z12,z4,z6]),(0,[z0,z1,z315,z2,z12,z6])],[(0,[z0,z106,z422,z3,z4,z6]),(0,[z0,z1173,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z1174,z6]),(0,[z0,z1,z2,z3,z70,z151]),(0,[z0,z1,z2,z3,z1175,z6])],[(0,[z0,z1,z171,z4,z6,z47])],[],[(0,[z21,z1,z26,z3,z161,z6]),(0,[z140,z1,z2,z3,z4,z6]),(0,[z0,z1,z1176,z2,z3,z6]),(0,[z80,z1,z2,z78,z33,z6]),(0,[z0,z18,z2,z123,z4,z6]),(0,[z0,z1,z16,z12,z6,z47])],[(0,[z0,z49,z2,z3,z177,z6]),(0,[z0,z1,z1177,z2,z3,z6]),(0,[z11,z0,z1,z2,z51,z6]),(0,[z0,z1,z231,z12,z4,z6])],[(0,[z0,z1,z1178,z2,z3,z6]),(0,[z0,z1,z2,z134,z33,z6]),(0,[z11,z0,z220,z2,z33,z6]),(0,[z0,z1119,z2,z3,z4,z6])],[(0,[z0,z1,z12,z389,z4,z6]),(0,[z317,z0,z1,z381,z2,z6]),(1,[z0,z1,z2,z14,z377]),(0,[z625,z0,z1,z3,z4,z47]),(0,[z221,z1,z2,z3,z33,z6]),(0,[z54,z0,z622,z3,z4,z6]),(0,[z1,z2,z12,z4,z6,z53]),(0,[z0,z1,z2,z214,z4,z6]),(0,[z0,z1,z2,z12,z14,z6]),(0,[z11,z0,z1,z231,z4,z6]),(0,[z0,z1,z149,z2,z346,z6])],[(0,[z0,z1,z2,z3,z4,z833]),(0,[z0,z1,z2,z3,z1179,z6]),(0,[z54,z0,z26,z3,z66,z6]),(0,[z0,z1,z2,z12,z135,z6]),(0,[z0,z220,z16,z2,z3,z6]),(0,[z0,z1,z2,z4,z1050,z38])],[(0,[z0,z1,z2,z299,z229,z6]),(0,[z337,z221,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z1180,z6]),(0,[z0,z1,z26,z468,z3,z6]),(0,[z0,z1,z2,z3,z6,z1181]),(0,[z75,z0,z1,z2,z14,z6]),(0,[z140,z1,z2,z3,z4,z188])],[(0,[z0,z1,z2,z308,z14,z6]),(0,[z0,z1,z2,z3,z6,z1182]),(0,[z54,z0,z3,z66,z4,z469]),(0,[z0,z106,z416,z3,z4,z6]),(0,[z0,z19,z2,z12,z4,z60])],[(0,[z94,z1,z353,z3,z4,z6]),(0,[z139,z0,z1,z122,z2,z6]),(0,[z0,z1,z1183,z2,z3,z6]),(0,[z313,z0,z1,z99,z33,z6]),(0,[z0,z1,z2,z1123,z4,z6])],[(0,[z0,z1,z26,z405,z3,z6]),(0,[z28,z0,z1,z13,z2,z6]),(0,[z216,z0,z1,z3,z4,z6]),(0,[z196,z0,z1,z12,z4,z6]),(0,[z11,z0,z1,z2,z217,z6])],[(0,[z1184,z0,z1,z2,z4,z6]),(0,[z0,z1,z2,z3,z6,z1185]),(0,[z0,z1,z2,z3,z1186,z6]),(0,[z0,z1,z2,z3,z508,z6]),(0,[z0,z142,z1,z157,z3,z6]),(0,[z1187,z1,z2,z3,z4,z6]),(0,[z0,z512,z2,z3,z117,z6])],[(0,[z0,z1,z16,z22,z12,z6]),(0,[z62,z0,z1,z405,z4,z6]),(0,[z0,z1,z1094,z2,z3,z6])],[(0,[z0,z448,z2,z299,z4,z6]),(0,[z0,z1,z1188,z3,z4,z6]),(0,[z0,z106,z1,z12,z166,z6]),(0,[z11,z0,z1189,z2,z4,z6]),(0,[z0,z1,z468,z3,z1190,z6])]],
   [[(0,[z1,z115,z12,z161,z4,z6]),(0,[z0,z1,z2,z3,z1191,z6]),(0,[z127,z0,z1,z2,z3,z264]),(0,[z0,z1,z2,z171,z4,z6]),(0,[z11,z0,z1,z2,z1192,z6]),(0,[z0,z1,z2,z1193,z4,z6])],[(0,[z11,z0,z448,z2,z4,z6]),(0,[z94,z1,z22,z12,z4,z6]),(0,[z0,z1,z2,z3,z14,z377]),(0,[z603,z0,z1,z26,z3,z6]),(0,[z252,z0,z1,z12,z4,z6]),(0,[z0,z1,z26,z397,z3,z6]),(0,[z71,z0,z2,z3,z756,z6])],[(0,[z0,z1,z2,z3,z4,z1194]),(0,[z0,z1,z2,z3,z1195,z6]),(0,[z54,z0,z1,z12,z4,z6]),(0,[z54,z0,z12,z66,z4,z6]),(0,[z11,z0,z1,z684,z4,z6]),(0,[z37,z447,z1,z3,z4,z47]),(0,[z0,z1,z1196,z2,z3,z6])],[(0,[z0,z1,z2,z3,z1197,z6]),(0,[z0,z1,z2,z3,z1198,z6]),(0,[z0,z1,z16,z2,z3,z469]),(0,[z0,z1,z1199,z2,z3,z6]),(0,[z399,z0,z1,z2,z14,z6]),(0,[z127,z0,z314,z2,z3,z32])],[(0,[z0,z448,z2,z3,z229,z6]),(0,[z221,z1,z26,z2,z3,z6]),(0,[z0,z1,z2,z1200,z4,z6]),(0,[z0,z1,z2,z1201,z33,z6])],[(0,[z0,z1,z2,z3,z864,z6]),(0,[z0,z106,z12,z4,z6,z91])],[(0,[z0,z1,z748,z3,z4,z6]),(0,[z0,z1,z2,z123,z51,z6]),(0,[z0,z253,z2,z12,z4,z6]),(0,[z1202,z0,z1,z2,z4,z6])],[(0,[z24,z0,z1,z2,z339,z6]),(0,[z103,z0,z1,z157,z3,z6]),(0,[z0,z2,z3,z4,z826,z91]),(0,[z11,z0,z1,z2,z6,z112]),(0,[z11,z0,z488,z2,z194,z6]),(0,[z131,z0,z1,z2,z33,z6])],[(0,[z21,z1,z3,z161,z177,z6]),(0,[z0,z820,z2,z3,z4,z6]),(0,[z0,z1,z16,z2,z81,z6]),(0,[z28,z1,z2,z79,z262,z6]),(0,[z0,z1,z3,z473,z33,z47])],[(0,[z28,z0,z1,z2,z14,z6]),(0,[z54,z0,z12,z581,z4,z6]),(0,[z1203,z1,z2,z3,z4,z6]),(0,[z57,z0,z52,z2,z3,z91]),(0,[z11,z0,z1,z12,z4,z6]),(0,[z0,z1,z474,z12,z4,z47]),(0,[z0,z1,z26,z189,z3,z6])],[(0,[z0,z1,z2,z3,z4,z1204]),(0,[z0,z1,z2,z705,z14,z6]),(0,[z0,z1,z1205,z2,z3,z6]),(0,[z1,z2,z3,z4,z907,z82]),(0,[z221,z1,z2,z3,z4,z469]),(0,[z57,z11,z0,z2,z4,z91]),(0,[z0,z1,z2,z3,z1206,z6]),(0,[z202,z395,z1,z2,z4,z6]),(0,[z0,z1207,z2,z3,z4,z6])],[(0,[z669,z0,z2,z17,z4,z6]),(0,[z583,z1,z648,z2,z3,z6]),(0,[z0,z1,z2,z159,z6,z38])],[(0,[z0,z1,z16,z2,z3,z44]),(0,[z337,z0,z2,z12,z4,z6]),(0,[z103,z11,z1,z2,z104,z6]),(0,[z0,z1208,z2,z3,z4,z6]),(0,[z466,z0,z1,z26,z3,z6]),(0,[z222,z1,z2,z12,z4,z6]),(0,[z0,z935,z2,z3,z4,z6]),(0,[z0,z1,z3,z33,z6,z212]),(0,[z0,z1,z2,z3,z27,z6])],[(0,[z54,z0,z1,z149,z12,z6]),(0,[z466,z0,z1,z12,z4,z6]),(0,[z11,z59,z1,z2,z4,z6]),(0,[z0,z1,z2,z12,z159,z6]),(0,[z0,z1,z26,z2,z171,z6]),(0,[z1106,z0,z1,z189,z4,z6])],[(0,[z337,z0,z1,z12,z4,z6]),(0,[z0,z119,z2,z3,z33,z6]),(0,[z28,z1,z405,z79,z4,z6]),(0,[z0,z1,z12,z4,z6,z329])],[(0,[z0,z1,z1209,z3,z4,z6]),(0,[z0,z1,z2,z3,z1210,z6]),(0,[z0,z1,z2,z1211,z4,z6]),(0,[z54,z0,z1,z12,z578,z6]),(0,[z236,z131,z0,z1,z4,z6])]],
   [[(0,[z0,z1,z1212,z3,z4,z6]),(0,[z0,z2,z3,z197,z4,z6]),(0,[z11,z138,z1,z2,z4,z6])],[(0,[z0,z1,z2,z3,z1213,z6]),(0,[z0,z1,z2,z4,z14,z377]),(0,[z0,z1,z2,z720,z4,z6]),(0,[z0,z1,z16,z2,z604,z6])],[(0,[z0,z1,z2,z4,z6,z1214]),(0,[z0,z64,z16,z2,z3,z6]),(0,[z0,z1,z405,z3,z741,z6]),(0,[z0,z1,z2,z14,z6,z377]),(0,[z54,z0,z18,z12,z4,z6]),(0,[z139,z0,z1,z2,z194,z6]),(0,[z447,z1,z2,z3,z14,z6])],[(0,[z0,z1,z426,z12,z4,z6]),(1,[z221,z1,z12,z4,z6]),(0,[z0,z1,z2,z41,z4,z6]),(0,[z54,z0,z1,z12,z132,z6]),(0,[z0,z1,z293,z3,z33,z6]),(0,[z0,z1,z330,z3,z33,z6]),(0,[z1215,z0,z26,z2,z3,z6]),(0,[z0,z1,z2,z339,z14,z6]),(0,[z461,z0,z1,z2,z14,z6]),(0,[z0,z1132,z16,z2,z3,z6])],[(0,[z190,z0,z220,z2,z4,z6]),(0,[z0,z1,z12,z4,z6,z47]),(0,[z11,z0,z1,z2,z135,z6]),(0,[z0,z1,z3,z33,z6,z92]),(0,[z0,z1,z26,z2,z339,z6])],[(0,[z0,z1,z405,z3,z262,z6]),(0,[z1216,z0,z1,z2,z4,z6]),(0,[z0,z1,z338,z2,z14,z6])],[(0,[z303,z0,z1,z2,z39,z6]),(0,[z1217,z1,z2,z3,z4,z6]),(0,[z417,z0,z1,z2,z277,z6]),(0,[z0,z267,z2,z3,z33,z6])],[(0,[z1062,z0,z1,z2,z4,z6]),(0,[z0,z2,z3,z4,z6,z1218]),(0,[z0,z1,z2,z1219,z4,z6])],[(0,[z0,z1,z2,z3,z4,z1220]),(0,[z1221,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z1222,z6]),(0,[z252,z0,z220,z2,z4,z6]),(0,[z0,z1,z845,z30,z3,z6])],[(0,[z0,z1,z1223,z2,z3,z6]),(0,[z0,z1,z2,z1224,z4,z6]),(0,[z1225,z0,z1,z2,z4,z6]),(0,[z0,z106,z2,z3,z4,z148]),(0,[z0,z1,z16,z2,z346,z6]),(0,[z0,z1,z2,z63,z4,z390])],[(0,[z0,z1,z470,z12,z4,z6]),(0,[z0,z1,z1226,z2,z3,z6])],[(0,[z43,z55,z2,z3,z14,z6]),(0,[z80,z1,z2,z374,z4,z6]),(0,[z413,z0,z2,z3,z4,z91]),(0,[z0,z1,z2,z1227,z4,z6]),(0,[z11,z0,z1,z2,z166,z6]),(0,[z0,z1,z13,z12,z166,z6])],[(0,[z0,z1,z1228,z2,z3,z6]),(0,[z0,z1,z405,z4,z188,z6]),(0,[z11,z0,z1,z2,z262,z6]),(0,[z0,z1,z2,z12,z51,z6]),(0,[z0,z1,z1229,z3,z4,z6])],[(0,[z0,z18,z2,z705,z4,z6]),(0,[z0,z52,z1,z2,z12,z6]),(0,[z0,z1,z12,z33,z6,z47]),(0,[z37,z0,z1,z443,z4,z47])],[(0,[z0,z1,z26,z2,z308,z6]),(0,[z80,z1,z2,z78,z4,z6]),(0,[z139,z0,z1,z405,z4,z6]),(0,[z126,z0,z1,z2,z14,z6]),(0,[z54,z0,z3,z66,z578,z6]),(0,[z0,z106,z1,z16,z12,z6]),(0,[z0,z1,z514,z12,z4,z6]),(0,[z0,z1,z2,z437,z14,z6])],[(0,[z0,z1,z2,z3,z950,z6]),(0,[z28,z0,z1,z2,z159,z6]),(0,[z1230,z0,z1,z2,z4,z6]),(0,[z59,z1,z2,z3,z14,z6]),(0,[z986,z0,z1,z2,z4,z6]),(0,[z0,z1,z2,z3,z1231,z6]),(0,[z127,z0,z1,z2,z3,z898])]],
   [[(0,[z0,z1,z1232,z2,z3,z6]),(0,[z0,z1,z2,z3,z1233,z6]),(0,[z0,z1234,z2,z3,z4,z6]),(0,[z0,z1,z2,z134,z4,z6]),(0,[z0,z1,z16,z2,z41,z6]),(0,[z0,z106,z3,z783,z4,z6]),(0,[z0,z1,z2,z1235,z4,z6]),(0,[z0,z1,z468,z63,z4,z6])],[(0,[z0,z12,z197,z161,z4,z6]),(0,[z0,z1236,z2,z3,z4,z6]),(0,[z0,z174,z2,z225,z4,z6]),(0,[z0,z1,z1122,z2,z392,z6])],[(0,[z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z12,z4,z6,z355]),(0,[z0,z1,z2,z3,z1237,z6]),(0,[z59,z19,z2,z3,z4,z60]),(0,[z0,z1,z2,z225,z14,z6]),(0,[z196,z0,z1,z2,z4,z554]),(0,[z0,z1089,z2,z3,z4,z6]),(0,[z1238,z0,z1,z2,z3,z6])],[(0,[z0,z1,z2,z3,z155,z6]),(0,[z309,z0,z1,z2,z166,z6]),(0,[z0,z1,z2,z12,z217,z6]),(0,[z11,z0,z267,z2,z4,z6]),(0,[z0,z1,z2,z1239,z33,z6]),(0,[z0,z267,z26,z2,z3,z6])],[(0,[z94,z1,z22,z3,z452,z6]),(0,[z0,z1240,z2,z3,z4,z6]),(0,[z0,z1,z2,z362,z14,z6]),(0,[z0,z1,z1241,z2,z3,z6]),(0,[z1242,z1,z2,z12,z4,z6])],[(0,[z410,z2,z3,z4,z6,z82]),(0,[z0,z1,z2,z1243,z4,z6]),(0,[z11,z0,z1,z2,z180,z6]),(0,[z74,z0,z1,z13,z3,z6]),(0,[z131,z0,z1,z460,z2,z6]),(0,[z0,z1,z30,z3,z14,z172])],[(0,[z598,z1,z3,z161,z4,z6]),(0,[z11,z94,z1,z22,z4,z6]),(0,[z103,z1,z2,z3,z104,z6]),(0,[z0,z1,z2,z1244,z4,z6]),(0,[z0,z1,z2,z3,z109,z6]),(0,[z11,z0,z805,z2,z4,z6]),(0,[z536,z0,z1,z2,z14,z6])],[(0,[z0,z1,z2,z1245,z4,z6])],[(0,[z0,z1,z401,z12,z4,z6]),(0,[z24,z1,z648,z2,z3,z6]),(0,[z0,z1,z2,z3,z1039,z6]),(0,[z0,z1,z2,z3,z1246,z6]),(0,[z0,z1,z2,z134,z479,z6]),(0,[z0,z1,z123,z297,z14,z6]),(0,[z0,z1,z2,z3,z6,z1247]),(0,[z222,z1,z2,z339,z4,z6])],[(0,[z0,z106,z115,z12,z4,z6]),(0,[z0,z1,z2,z14,z6,z409]),(0,[z0,z1,z2,z3,z1248,z6]),(0,[z0,z1,z497,z3,z33,z6]),(0,[z0,z1,z1249,z2,z3,z6]),(0,[z0,z1,z2,z3,z1250,z6]),(0,[z62,z0,z1,z2,z14,z38])],[(0,[z337,z43,z2,z3,z4,z6]),(0,[z54,z0,z3,z66,z33,z6]),(0,[z71,z11,z0,z2,z29,z6]),(0,[z0,z1,z2,z3,z117,z6]),(0,[z0,z1,z1251,z2,z3,z6]),(0,[z0,z1,z2,z3,z473,z70])],[(0,[z0,z1,z2,z3,z1252,z6]),(0,[z0,z1253,z2,z3,z4,z6]),(0,[z0,z1,z460,z2,z392,z6])],[(0,[z0,z1,z2,z1254,z4,z6]),(0,[z486,z1,z22,z3,z4,z6]),(0,[z0,z1,z415,z12,z4,z6]),(0,[z0,z1,z2,z3,z1255,z6]),(0,[z0,z1,z2,z123,z166,z6]),(0,[z11,z0,z1,z16,z2,z6]),(0,[z730,z0,z1,z2,z4,z6]),(0,[z0,z1,z26,z2,z993,z6])],[(0,[z317,z0,z1,z2,z452,z6]),(0,[z238,z1,z2,z3,z4,z148]),(0,[z0,z1,z233,z12,z4,z6]),(0,[z0,z1,z157,z3,z33,z6]),(0,[z0,z1256,z2,z3,z33,z6]),(0,[z0,z1,z16,z30,z3,z172]),(0,[z268,z0,z1,z16,z2,z6])],[(0,[z0,z1,z2,z14,z6,z287]),(0,[z221,z1,z2,z3,z578,z6]),(0,[z0,z1,z2,z187,z70,z6]),(0,[z0,z1,z2,z12,z6,z112]),(0,[z11,z0,z1,z33,z6,z47]),(0,[z0,z1,z2,z1201,z4,z6]),(0,[z139,z0,z1,z276,z2,z6])],[(0,[z42,z696,z2,z3,z4,z6]),(0,[z0,z1257,z2,z3,z4,z6]),(0,[z0,z1,z2,z458,z14,z6]),(0,[z0,z1,z845,z3,z33,z6]),(0,[z74,z0,z1,z26,z171,z6]),(0,[z140,z1,z16,z2,z3,z6])]],
   [[(0,[z11,z0,z1,z306,z4,z6]),(0,[z103,z0,z1,z2,z300,z6]),(0,[z0,z1,z2,z6,z418,z287]),(0,[z0,z2,z3,z4,z172,z84]),(0,[z0,z1,z468,z3,z14,z6]),(0,[z1258,z1,z2,z3,z4,z6])],[(0,[z0,z1259,z2,z3,z4,z6]),(0,[z131,z0,z1,z2,z4,z6]),(0,[z0,z1,z3,z109,z6,z47])],[(0,[z0,z1,z2,z3,z14,z534]),(0,[z221,z1,z2,z3,z132,z6]),(0,[z0,z1,z2,z3,z1260,z6]),(1,[z0,z220,z2,z277,z6])],[(0,[z0,z1,z119,z2,z14,z6]),(0,[z0,z1,z2,z748,z4,z6]),(0,[z0,z18,z2,z515,z4,z6]),(0,[z0,z52,z271,z2,z3,z6]),(0,[z0,z1,z2,z63,z33,z188]),(0,[z127,z0,z1,z2,z3,z32])],[(0,[z303,z0,z1,z2,z33,z6]),(0,[z0,z1,z2,z3,z33,z148]),(0,[z216,z0,z1,z16,z3,z6]),(0,[z236,z11,z0,z1,z277,z6]),(0,[z11,z0,z1261,z2,z4,z6]),(0,[z0,z1,z315,z3,z6,z47]),(0,[z0,z1,z149,z13,z2,z6])],[(0,[z11,z0,z1,z2,z229,z6]),(0,[z0,z1,z2,z1262,z4,z6]),(0,[z0,z1,z490,z3,z33,z6]),(0,[z361,z0,z1,z2,z300,z6]),(0,[z0,z18,z2,z225,z4,z6]),(0,[z0,z1,z2,z384,z14,z6]),(0,[z96,z0,z1,z2,z14,z38])],[(0,[z1,z2,z848,z79,z4,z6]),(0,[z0,z1263,z2,z3,z4,z6]),(0,[z73,z289,z1,z2,z3,z82]),(0,[z160,z314,z2,z3,z4,z6])],[(0,[z0,z533,z1,z12,z4,z6]),(1,[z1,z2,z848,z4,z6]),(0,[z0,z1,z2,z3,z4,z1264]),(0,[z11,z0,z1,z12,z194,z6]),(0,[z0,z1,z26,z2,z214,z6]),(0,[z0,z1,z2,z3,z4,z996])],[(0,[z0,z119,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z177,z44]),(0,[z0,z1265,z2,z3,z4,z6]),(0,[z289,z222,z1,z2,z3,z6]),(0,[z236,z11,z0,z488,z4,z6]),(0,[z37,z0,z1,z3,z33,z47])],[(0,[z0,z1,z2,z299,z4,z524]),(0,[z190,z0,z1,z2,z952,z6]),(0,[z447,z1,z2,z93,z4,z6]),(0,[z0,z1,z30,z443,z4,z6]),(0,[z0,z1,z231,z3,z487,z6]),(0,[z0,z1,z2,z63,z4,z1050])],[(0,[z0,z115,z2,z17,z14,z6]),(0,[z0,z1,z306,z3,z262,z6]),(0,[z103,z289,z1,z2,z3,z6]),(0,[z0,z1,z2,z1266,z4,z6]),(0,[z15,z0,z26,z2,z17,z6]),(0,[z0,z1,z1267,z3,z4,z6]),(0,[z127,z0,z1,z2,z12,z32]),(0,[z0,z1,z315,z2,z166,z6]),(0,[z0,z1,z2,z194,z14,z6]),(0,[z0,z1268,z26,z2,z3,z6]),(0,[z160,z271,z2,z3,z4,z6])],[(0,[z421,z1,z2,z3,z4,z82]),(0,[z11,z238,z1,z2,z4,z6]),(0,[z0,z18,z123,z297,z4,z6]),(0,[z0,z1,z2,z3,z1269,z6]),(0,[z0,z1,z149,z2,z3,z6]),(0,[z0,z1,z1270,z2,z443,z6]),(0,[z0,z1,z1271,z2,z3,z6])],[(0,[z236,z0,z1,z41,z4,z6]),(0,[z0,z1,z2,z1272,z4,z6]),(0,[z0,z1,z2,z392,z14,z6]),(0,[z0,z1,z13,z2,z6,z38])],[],[(0,[z0,z1,z2,z3,z229,z524]),(0,[z0,z1,z1273,z3,z4,z6]),(0,[z0,z106,z46,z3,z33,z6]),(0,[z447,z1,z2,z3,z217,z6])],[(0,[z0,z410,z2,z12,z4,z6]),(0,[z0,z1,z2,z326,z14,z6]),(0,[z0,z1,z1274,z2,z3,z6]),(0,[z0,z1,z1275,z3,z4,z6]),(0,[z623,z0,z2,z3,z4,z91]),(0,[z0,z1,z2,z3,z1276,z6]),(0,[z62,z0,z1,z2,z159,z38])]],
   [[(0,[z0,z267,z2,z3,z4,z6]),(0,[z0,z1,z16,z2,z467,z6]),(0,[z394,z0,z1,z2,z3,z92]),(0,[z0,z1,z2,z14,z6,z433]),(0,[z1277,z1,z2,z3,z4,z6])],[(0,[z80,z1,z2,z118,z14,z6]),(0,[z0,z1,z26,z2,z3,z148]),(0,[z164,z0,z2,z3,z4,z91]),(0,[z0,z1278,z1,z2,z3,z6]),(0,[z0,z1,z2,z947,z6,z91]),(0,[z0,z19,z2,z3,z33,z60]),(0,[z1,z2,z12,z1279,z4,z6]),(0,[z0,z1014,z2,z3,z4,z6]),(0,[z0,z1,z149,z2,z14,z6])],[(0,[z1280,z0,z1,z2,z4,z6]),(0,[z0,z1,z2,z3,z4,z1281]),(0,[z73,z1,z2,z3,z14,z82]),(0,[z0,z1,z2,z404,z14,z6]),(0,[z0,z1,z2,z12,z166,z6]),(0,[z0,z1,z149,z2,z12,z6]),(0,[z107,z1,z2,z3,z111,z6]),(0,[z96,z0,z1,z2,z3,z100])],[(0,[z11,z0,z119,z2,z4,z6]),(0,[z28,z0,z1,z405,z14,z6]),(0,[z0,z1,z2,z12,z262,z6]),(0,[z396,z1,z2,z3,z104,z6]),(0,[z0,z1,z1282,z3,z4,z6]),(0,[z0,z1,z13,z2,z123,z6]),(0,[z0,z1,z2,z1283,z4,z6]),(0,[z0,z1,z26,z704,z3,z6])],[(0,[z0,z1,z2,z3,z1284,z6]),(0,[z43,z2,z3,z153,z4,z6]),(0,[z0,z448,z2,z3,z4,z524]),(0,[z0,z1,z2,z3,z4,z1285]),(0,[z0,z1,z2,z3,z1286,z6]),(0,[z244,z0,z1,z149,z2,z6]),(0,[z0,z1287,z2,z3,z4,z6]),(0,[z138,z1,z26,z2,z3,z6]),(0,[z131,z0,z1,z30,z4,z172])],[(0,[z0,z1,z1288,z2,z3,z6]),(0,[z453,z0,z1,z405,z4,z6]),(0,[z0,z1,z2,z3,z1289,z6]),(0,[z0,z1,z2,z300,z14,z6]),(0,[z0,z1,z2,z3,z1290,z6]),(0,[z0,z1,z2,z1291,z4,z6]),(0,[z11,z0,z1,z2,z277,z6]),(0,[z0,z1,z2,z3,z1292,z6])],[(0,[z0,z1,z2,z3,z177,z6]),(0,[z1293,z0,z1,z2,z4,z6]),(0,[z0,z407,z46,z3,z4,z6]),(0,[z216,z0,z1,z3,z1294,z6]),(0,[z0,z1,z16,z2,z406,z6]),(0,[z0,z220,z2,z3,z14,z6]),(0,[z0,z1,z468,z3,z159,z6])],[(0,[z280,z0,z1,z2,z14,z6]),(0,[z0,z1,z297,z12,z4,z6]),(0,[z0,z1,z2,z3,z1295,z6]),(0,[z313,z0,z1,z2,z33,z6]),(0,[z0,z1,z2,z63,z27,z188])],[(0,[z0,z1,z2,z1296,z4,z6]),(0,[z0,z1,z2,z3,z1297,z6]),(0,[z0,z1,z2,z3,z956,z6]),(0,[z0,z1,z2,z1298,z4,z6]),(0,[z0,z901,z2,z12,z4,z6])],[(0,[z0,z1,z405,z12,z4,z6]),(0,[z94,z1,z26,z22,z3,z6]),(0,[z103,z1,z2,z3,z6,z141]),(0,[z1299,z0,z1,z2,z4,z6]),(0,[z0,z1,z26,z3,z137,z6]),(0,[z0,z1,z2,z3,z4,z1300]),(0,[z19,z2,z3,z4,z60,z53]),(0,[z0,z1,z128,z12,z14,z6]),(0,[z335,z1,z2,z12,z4,z6])],[(0,[z80,z1,z16,z2,z78,z6]),(0,[z0,z1,z25,z2,z14,z6]),(0,[z1301,z0,z1,z2,z4,z6]),(0,[z0,z1,z2,z3,z1302,z6]),(0,[z11,z0,z1,z2,z4,z847]),(0,[z0,z253,z2,z3,z487,z6])],[(0,[z54,z0,z1,z26,z12,z6]),(0,[z1303,z1,z2,z3,z4,z6]),(0,[z0,z1,z276,z2,z63,z188])],[(0,[z55,z2,z3,z4,z6,z45]),(0,[z21,z1,z16,z3,z161,z6]),(0,[z0,z1,z2,z12,z180,z6]),(0,[z0,z1,z26,z849,z3,z6]),(0,[z1304,z1,z2,z3,z4,z6]),(0,[z0,z1,z1305,z2,z3,z6])],[(0,[z0,z1,z2,z3,z1306,z6]),(0,[z0,z1,z2,z3,z262,z377]),(0,[z28,z0,z1,z2,z135,z6]),(0,[z0,z1,z1307,z2,z3,z6]),(0,[z0,z1,z1116,z2,z3,z6]),(0,[z0,z1,z1199,z2,z12,z6]),(0,[z11,z0,z1,z315,z2,z6]),(0,[z0,z1,z189,z3,z4,z6]),(0,[z0,z1,z2,z1239,z4,z6]),(0,[z0,z1,z481,z2,z14,z6])],[(0,[z0,z1,z2,z3,z191,z6]),(0,[z0,z19,z26,z2,z3,z60]),(0,[z0,z1,z3,z12,z109,z6])],[(0,[z1308,z0,z1,z2,z4,z6]),(0,[z0,z1,z1309,z3,z4,z6]),(0,[z0,z1,z2,z3,z1310,z6]),(0,[z236,z0,z1,z3,z109,z6]),(0,[z0,z1,z1311,z2,z3,z6])]],
   [[(0,[z54,z0,z16,z3,z66,z6]),(0,[z0,z108,z2,z17,z4,z6]),(0,[z0,z1,z2,z3,z194,z6]),(0,[z0,z1,z2,z76,z33,z6]),(0,[z396,z1,z199,z2,z3,z6]),(0,[z62,z0,z1,z231,z4,z38]),(0,[z127,z0,z271,z2,z3,z32])],[(0,[z0,z1,z1312,z3,z4,z6]),(0,[z317,z0,z1,z2,z33,z6]),(0,[z0,z1,z347,z12,z4,z6]),(0,[z0,z1,z2,z3,z14,z469]),(0,[z1313,z0,z1,z3,z4,z6]),(0,[z0,z1,z484,z3,z33,z6]),(0,[z0,z2,z3,z29,z756,z6]),(0,[z0,z1,z16,z468,z3,z6])],[(0,[z0,z1,z2,z3,z4,z1314]),(0,[z0,z1,z1315,z3,z4,z6]),(0,[z11,z0,z1,z26,z12,z6])],[(0,[z1316,z0,z1,z2,z4,z6]),(0,[z337,z0,z2,z3,z33,z6]),(0,[z0,z1,z405,z3,z4,z377]),(0,[z0,z1317,z2,z3,z4,z6]),(0,[z0,z1,z543,z12,z4,z6]),(0,[z0,z1,z3,z33,z91,z47]),(0,[z0,z1,z2,z1318,z4,z6]),(0,[z0,z1,z2,z3,z4,z1043]),(0,[z0,z1,z220,z2,z14,z6]),(0,[z0,z1,z2,z1319,z33,z6]),(0,[z0,z1,z2,z1320,z4,z6])],[(0,[z0,z26,z2,z3,z197,z6]),(0,[z0,z1,z2,z4,z188,z377]),(0,[z28,z0,z1,z2,z166,z6]),(0,[z54,z0,z3,z66,z4,z6]),(0,[z0,z314,z2,z12,z4,z6]),(0,[z0,z1,z30,z3,z33,z6]),(0,[z1321,z1,z2,z3,z33,z6]),(0,[z0,z1,z26,z114,z3,z6]),(0,[z0,z1,z2,z3,z1322,z6])],[(0,[z0,z1,z2,z3,z1323,z6]),(0,[z221,z1,z2,z41,z4,z6]),(0,[z0,z1,z2,z3,z4,z1324]),(0,[z140,z267,z2,z3,z4,z6])],[(0,[z495,z0,z1,z2,z14,z6]),(0,[z28,z357,z1,z2,z4,z6]),(0,[z1,z2,z543,z3,z4,z82]),(0,[z0,z1,z2,z123,z277,z6]),(0,[z0,z220,z2,z4,z14,z6]),(0,[z1325,z1,z2,z3,z4,z6]),(0,[z0,z1,z529,z3,z33,z6]),(0,[z0,z1,z26,z2,z392,z6]),(0,[z0,z1,z16,z13,z2,z6]),(0,[z0,z1,z157,z1142,z4,z6])],[(0,[z478,z1,z2,z3,z4,z82]),(0,[z126,z0,z1,z2,z853,z6]),(0,[z0,z1,z157,z3,z4,z6]),(0,[z0,z1268,z2,z3,z4,z6]),(0,[z0,z1,z2,z286,z14,z38])],[(0,[z11,z0,z410,z2,z4,z6]),(0,[z0,z271,z2,z12,z4,z6]),(0,[z0,z1326,z2,z3,z4,z6])],[(0,[z0,z1,z2,z12,z4,z524]),(0,[z0,z1327,z2,z3,z4,z6]),(0,[z0,z1,z2,z41,z1328,z6]),(0,[z0,z1329,z1,z2,z3,z6]),(0,[z0,z1,z99,z3,z109,z6]),(0,[z74,z0,z1,z26,z214,z6])],[(0,[z0,z1,z353,z12,z4,z6]),(0,[z0,z1,z2,z1330,z4,z6]),(0,[z0,z49,z2,z3,z14,z6]),(0,[z0,z1,z1331,z2,z3,z6]),(0,[z127,z0,z1,z2,z3,z380]),(0,[z0,z1,z16,z2,z134,z6]),(0,[z1332,z1,z2,z3,z4,z6])],[(0,[z43,z655,z2,z3,z4,z6]),(0,[z11,z0,z49,z2,z4,z6]),(0,[z260,z0,z1,z12,z4,z6]),(0,[z54,z0,z3,z581,z4,z6]),(0,[z0,z1,z1333,z2,z3,z6]),(0,[z0,z2,z210,z17,z14,z6]),(0,[z0,z1,z2,z1334,z4,z6]),(1,[z795,z0,z1,z4,z6]),(0,[z11,z0,z220,z26,z2,z6]),(0,[z11,z0,z1,z157,z4,z6])],[(0,[z0,z1,z2,z12,z229,z6]),(0,[z80,z0,z1,z2,z454,z6]),(0,[z221,z1,z16,z2,z3,z6])],[(0,[z0,z1,z16,z2,z3,z6]),(0,[z0,z1,z1335,z3,z4,z6]),(0,[z1336,z0,z1,z2,z4,z6]),(0,[z0,z1,z632,z2,z14,z6]),(0,[z0,z1,z2,z63,z4,z188])],[(0,[z0,z1,z2,z3,z1337,z6]),(0,[z0,z1,z2,z3,z1168,z6]),(0,[z0,z1,z529,z157,z3,z6])],[(0,[z0,z1,z2,z308,z229,z6]),(0,[z126,z0,z790,z2,z4,z6]),(0,[z519,z0,z1,z2,z3,z537]),(0,[z138,z1,z2,z443,z4,z6])]],
   [[(0,[z337,z0,z26,z2,z3,z6]),(0,[z0,z1,z2,z3,z1338,z6]),(0,[z1339,z1,z2,z3,z4,z6]),(0,[z48,z11,z0,z1,z4,z6]),(0,[z0,z1,z334,z3,z33,z6]),(0,[z0,z1,z460,z3,z33,z6]),(0,[z222,z1,z26,z2,z3,z6])],[(0,[z0,z142,z2,z3,z756,z6]),(0,[z0,z19,z2,z3,z4,z826]),(0,[z724,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z1340,z4,z6]),(0,[z0,z448,z2,z12,z4,z6]),(0,[z0,z1,z2,z3,z6,z1341]),(0,[z1,z2,z3,z4,z6,z1342]),(0,[z11,z0,z488,z2,z14,z6]),(0,[z0,z512,z2,z93,z4,z6]),(0,[z37,z0,z1,z3,z4,z47]),(0,[z0,z108,z2,z3,z239,z6]),(0,[z0,z1,z231,z3,z1037,z6])],[(0,[z0,z1,z2,z3,z4,z1343]),(0,[z0,z106,z26,z46,z3,z6]),(0,[z0,z1,z2,z3,z1344,z6]),(0,[z71,z0,z52,z2,z3,z6]),(0,[z1345,z0,z1,z2,z4,z6]),(0,[z11,z0,z220,z2,z4,z6]),(0,[z821,z1,z2,z3,z4,z6]),(0,[z1346,z1,z26,z2,z3,z6]),(0,[z0,z1,z16,z2,z14,z6])],[(0,[z221,z1,z2,z3,z4,z6]),(0,[z21,z11,z1,z161,z4,z6]),(0,[z101,z80,z1,z2,z14,z6]),(0,[z0,z1,z16,z297,z3,z6]),(0,[z0,z1,z16,z2,z12,z6]),(0,[z62,z335,z1,z2,z4,z38])],[(0,[z42,z115,z2,z12,z4,z6]),(0,[z0,z448,z2,z308,z4,z6]),(0,[z0,z1,z2,z1347,z4,z6]),(0,[z0,z1,z2,z81,z1348,z6]),(0,[z80,z1,z249,z2,z78,z6]),(0,[z54,z0,z3,z66,z132,z6]),(0,[z0,z1,z3,z783,z4,z6]),(0,[z0,z1,z514,z3,z33,z6]),(0,[z11,z0,z887,z2,z4,z6]),(0,[z0,z1,z2,z769,z14,z6]),(0,[z0,z1,z2,z93,z33,z6])],[(0,[z0,z18,z220,z2,z4,z6]),(0,[z0,z1,z566,z3,z33,z6]),(0,[z0,z1,z2,z443,z14,z6])],[(0,[z0,z1,z2,z3,z1349,z6]),(0,[z0,z1,z16,z2,z307,z6]),(0,[z0,z1,z12,z4,z6,z531]),(0,[z0,z1350,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z473,z34]),(0,[z0,z1351,z26,z2,z3,z6])],[(0,[z0,z1,z2,z3,z1348,z6]),(0,[z11,z0,z64,z2,z4,z6]),(0,[z1352,z0,z2,z3,z4,z6]),(0,[z0,z1,z1353,z2,z3,z6]),(0,[z221,z2,z3,z17,z4,z6]),(0,[z0,z106,z46,z3,z4,z6]),(0,[z0,z1,z2,z3,z1328,z6]),(0,[z0,z488,z2,z123,z4,z6]),(0,[z0,z1354,z1,z2,z3,z6]),(0,[z0,z1355,z26,z2,z3,z6]),(0,[z0,z1,z2,z1356,z4,z6])],[(0,[z0,z1,z2,z3,z1357,z6]),(0,[z0,z1,z1358,z2,z4,z6]),(0,[z0,z1,z149,z2,z654,z6])],[(0,[z0,z1359,z2,z3,z4,z6]),(0,[z120,z11,z0,z1,z4,z6]),(0,[z1,z2,z3,z104,z846,z6]),(0,[z0,z323,z2,z12,z4,z6]),(0,[z536,z0,z1,z2,z135,z6]),(0,[z37,z0,z1,z3,z117,z47])],[(0,[z54,z42,z0,z12,z4,z6]),(0,[z0,z1,z2,z4,z188,z409]),(0,[z0,z1,z2,z3,z578,z148]),(0,[z0,z1,z386,z12,z14,z6]),(0,[z0,z1,z2,z3,z31,z332])],[(0,[z0,z1,z1360,z2,z3,z6]),(0,[z0,z1,z2,z3,z1294,z6]),(0,[z57,z0,z2,z12,z4,z91]),(0,[z0,z1,z2,z12,z277,z6]),(0,[z1361,z1,z2,z3,z4,z6]),(0,[z0,z1,z386,z3,z33,z6]),(0,[z131,z0,z1,z26,z2,z6]),(0,[z0,z1,z16,z2,z339,z6])],[(0,[z0,z1,z1362,z2,z3,z6]),(0,[z0,z1,z2,z3,z1363,z6]),(0,[z0,z1,z910,z2,z299,z6]),(0,[z21,z1,z3,z161,z14,z6]),(0,[z0,z1,z2,z3,z1025,z6]),(0,[z0,z1,z2,z3,z1364,z6]),(0,[z0,z1,z2,z3,z1365,z6]),(0,[z0,z1,z2,z3,z235,z6]),(0,[z0,z1,z2,z225,z166,z6]),(0,[z0,z1,z2,z277,z6,z38]),(0,[z0,z1366,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z1367,z6])],[(0,[z0,z1,z556,z3,z33,z6]),(0,[z0,z1,z2,z3,z132,z148]),(0,[z0,z1,z2,z3,z1368,z6]),(0,[z227,z0,z1,z3,z4,z47])]],
   [[(0,[z0,z1,z2,z3,z1369,z6]),(0,[z0,z1,z12,z455,z4,z6]),(0,[z0,z106,z46,z3,z479,z6]),(0,[z0,z314,z2,z339,z4,z6])],[(0,[z0,z1,z12,z4,z6,z541]),(0,[z313,z0,z1,z2,z4,z6]),(0,[z11,z0,z1,z2,z31,z70]),(0,[z0,z1,z2,z3,z286,z102])],[(0,[z958,z0,z1,z2,z6,z287]),(0,[z0,z1,z12,z456,z4,z6]),(0,[z0,z142,z250,z2,z3,z6]),(0,[z0,z1,z2,z3,z6,z1370]),(0,[z0,z1,z26,z231,z3,z6])],[(0,[z1215,z0,z2,z3,z4,z6]),(0,[z0,z119,z16,z2,z3,z6]),(0,[z0,z1,z26,z3,z178,z6]),(0,[z0,z488,z2,z3,z277,z6])],[(0,[z0,z1,z246,z2,z134,z6]),(0,[z0,z1,z2,z3,z1371,z6]),(0,[z37,z0,z512,z3,z4,z47]),(0,[z0,z1,z2,z658,z14,z6]),(0,[z0,z271,z2,z339,z4,z6])],[(0,[z11,z0,z1,z2,z4,z524]),(0,[z0,z1,z26,z2,z63,z188])],[(0,[z0,z1,z16,z2,z308,z6]),(0,[z28,z1,z306,z79,z4,z6]),(0,[z0,z1,z2,z1372,z4,z6]),(0,[z0,z1,z2,z166,z6,z38]),(0,[z0,z1,z2,z1373,z4,z6])],[(0,[z28,z1,z2,z79,z4,z534]),(0,[z0,z1,z2,z1374,z4,z6]),(0,[z0,z1,z246,z2,z3,z6]),(0,[z0,z1,z2,z3,z1375,z6]),(0,[z0,z18,z16,z2,z123,z6]),(0,[z138,z512,z2,z3,z4,z6])],[(0,[z1376,z0,z1,z3,z4,z6]),(0,[z0,z1,z2,z3,z1377,z6]),(0,[z0,z1,z26,z12,z161,z6]),(0,[z0,z1,z249,z2,z3,z6]),(0,[z126,z73,z1,z2,z4,z82]),(0,[z11,z0,z1026,z2,z4,z6])],[(0,[z232,z115,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z1002,z6]),(0,[z1378,z1,z2,z3,z4,z6])],[(0,[z28,z1,z26,z2,z79,z6]),(0,[z126,z0,z1,z16,z2,z6]),(0,[z238,z1,z2,z3,z14,z6]),(0,[z0,z1,z2,z3,z1105,z6]),(0,[z138,z1,z2,z3,z33,z6]),(0,[z0,z1,z2,z3,z1190,z6]),(0,[z0,z1,z30,z3,z180,z172]),(0,[z127,z0,z1,z189,z3,z32])],[(0,[z0,z1,z2,z3,z1379,z6]),(0,[z0,z1,z1380,z2,z3,z6]),(0,[z1381,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z277,z6,z557]),(0,[z196,z0,z1,z2,z277,z6]),(0,[z1277,z1,z16,z2,z3,z6]),(0,[z0,z267,z16,z2,z3,z6])],[(1,[z337,z0,z12,z4,z6]),(0,[z0,z1,z1382,z2,z3,z6]),(0,[z71,z0,z2,z3,z555,z6]),(0,[z62,z0,z267,z2,z4,z38]),(0,[z0,z1,z2,z3,z31,z898])],[(0,[z0,z1,z2,z1383,z4,z6]),(0,[z0,z1,z493,z3,z33,z6]),(0,[z0,z1,z2,z1319,z4,z6]),(0,[z0,z1189,z26,z2,z3,z6]),(0,[z140,z1,z2,z3,z14,z6])],[(0,[z0,z1,z2,z3,z262,z534]),(0,[z0,z1,z246,z2,z12,z6]),(0,[z0,z18,z2,z788,z4,z6]),(0,[z0,z488,z2,z12,z4,z6]),(0,[z0,z1,z149,z12,z109,z6]),(0,[z0,z512,z2,z3,z14,z6])],[(0,[z0,z1,z249,z2,z12,z6]),(0,[z0,z678,z1,z12,z4,z6]),(0,[z309,z1,z2,z374,z4,z6]),(0,[z0,z1,z30,z3,z4,z653]),(0,[z0,z1,z231,z3,z33,z6]),(0,[z0,z2,z3,z1384,z4,z6])]],
   [[(0,[z11,z0,z1,z381,z2,z6]),(0,[z0,z1,z381,z22,z12,z6]),(0,[z11,z221,z1,z2,z4,z6]),(0,[z0,z1,z16,z2,z187,z6]),(0,[z0,z488,z1,z12,z4,z6]),(0,[z0,z1,z12,z14,z6,z47]),(0,[z0,z1,z2,z214,z14,z6])],[(0,[z0,z547,z1,z2,z14,z6]),(0,[z15,z0,z2,z17,z33,z6]),(0,[z0,z1,z12,z4,z6,z557])],[(0,[z0,z1,z2,z331,z14,z6]),(0,[z21,z337,z3,z161,z4,z6]),(0,[z103,z1,z2,z3,z846,z6]),(0,[z0,z1,z616,z12,z4,z6]),(0,[z795,z0,z1,z3,z4,z6]),(0,[z335,z1,z468,z3,z4,z6]),(0,[z0,z253,z468,z3,z4,z6])],[(0,[z42,z858,z2,z3,z4,z6]),(0,[z0,z1,z22,z12,z452,z6]),(0,[z0,z1,z2,z3,z1385,z6]),(0,[z0,z1000,z2,z3,z4,z6])],[(0,[z0,z1,z405,z3,z4,z534]),(0,[z0,z2,z3,z4,z6,z1386]),(0,[z589,z0,z1,z2,z14,z6])],[(0,[z55,z858,z2,z3,z4,z6]),(0,[z0,z1,z2,z1387,z4,z6]),(0,[z0,z1355,z2,z3,z4,z6]),(0,[z0,z1,z1388,z2,z4,z6]),(0,[z216,z0,z1,z3,z14,z6]),(0,[z0,z1,z13,z3,z12,z6]),(0,[z0,z1,z149,z2,z135,z6]),(0,[z447,z323,z2,z3,z4,z6]),(0,[z0,z1,z1270,z2,z3,z6]),(0,[z0,z1,z2,z339,z31,z6]),(0,[z127,z0,z1,z2,z339,z32])],[(0,[z0,z1,z2,z1389,z4,z6]),(0,[z0,z1,z2,z1390,z4,z6]),(0,[z0,z1,z1391,z3,z4,z6]),(0,[z11,z0,z1,z2,z948,z6]),(0,[z0,z1,z2,z109,z14,z6])],[(0,[z0,z108,z2,z3,z72,z6]),(0,[z0,z1,z3,z235,z6,z47]),(0,[z0,z2,z3,z4,z6,z1392]),(0,[z1304,z1,z16,z2,z3,z6])],[(0,[z0,z1,z2,z308,z746,z6]),(0,[z0,z1,z85,z12,z4,z6]),(0,[z0,z1,z2,z3,z1393,z6]),(0,[z0,z1,z26,z2,z93,z6])],[(0,[z0,z1,z2,z3,z1394,z6]),(0,[z28,z1,z2,z79,z4,z377]),(0,[z193,z1,z2,z621,z4,z6]),(0,[z0,z1,z2,z171,z14,z6]),(0,[z0,z1,z2,z664,z14,z6])],[(0,[z49,z2,z3,z161,z4,z6]),(0,[z0,z1,z381,z2,z81,z6]),(0,[z0,z1,z2,z3,z6,z1395]),(0,[z0,z1,z122,z2,z3,z6]),(0,[z216,z0,z1,z3,z1364,z6]),(0,[z0,z1,z499,z12,z4,z6]),(0,[z0,z1,z2,z3,z1396,z6])],[(0,[z0,z2,z3,z4,z288,z91]),(0,[z0,z1,z2,z3,z4,z1397]),(0,[z193,z1,z12,z161,z4,z6]),(0,[z94,z1,z22,z3,z33,z6]),(0,[z0,z2,z12,z4,z6,z84]),(0,[z190,z0,z1,z2,z33,z6]),(0,[z0,z1,z26,z3,z33,z6]),(0,[z0,z1,z16,z2,z654,z6])],[(0,[z1,z2,z3,z4,z6,z53]),(0,[z193,z1,z2,z79,z4,z6]),(0,[z0,z1,z1398,z2,z4,z6]),(0,[z0,z1,z2,z1399,z4,z6]),(0,[z1,z2,z3,z4,z6,z907]),(0,[z221,z1,z3,z12,z4,z6]),(0,[z0,z1,z2,z1049,z4,z6]),(0,[z71,z0,z2,z12,z29,z6]),(0,[z0,z1,z2,z3,z1065,z6]),(0,[z519,z0,z1,z3,z33,z47])],[(0,[z43,z1,z12,z161,z4,z6]),(0,[z0,z1,z2,z3,z1068,z6]),(0,[z0,z1,z960,z3,z4,z6]),(0,[z335,z1,z2,z3,z487,z6])],[(0,[z1400,z0,z1,z2,z4,z6]),(0,[z107,z1,z2,z3,z7,z6]),(0,[z0,z19,z106,z12,z4,z6]),(0,[z0,z2,z293,z3,z4,z91]),(0,[z0,z1,z2,z3,z897,z6])],[(0,[z0,z1,z2,z500,z14,z6]),(0,[z11,z0,z1,z2,z411,z6])]],
   [[(0,[z0,z1,z12,z500,z4,z6]),(0,[z101,z1,z2,z3,z4,z575]),(0,[z0,z1,z2,z3,z1401,z6]),(0,[z0,z1402,z2,z3,z4,z6]),(0,[z0,z253,z2,z3,z33,z6]),(0,[z0,z2,z3,z33,z6,z1392])],[(0,[z0,z1,z797,z2,z3,z6]),(0,[z0,z1,z122,z297,z3,z6]),(0,[z11,z0,z220,z2,z194,z6]),(0,[z0,z1,z443,z4,z6,z47]),(0,[z0,z1,z2,z392,z180,z6])],[(0,[z0,z1,z2,z1403,z4,z6]),(0,[z202,z0,z1,z2,z14,z6]),(0,[z0,z1,z12,z4,z82,z47]),(0,[z0,z1,z2,z1404,z4,z6]),(0,[z0,z1,z2,z41,z4,z148]),(0,[z15,z0,z16,z2,z17,z6]),(0,[z11,z0,z1,z12,z14,z6]),(0,[z0,z1,z2,z747,z4,z6]),(0,[z0,z1,z2,z443,z217,z6])],[(0,[z0,z1,z2,z3,z1405,z6]),(0,[z0,z410,z26,z2,z3,z6]),(0,[z0,z1,z460,z30,z12,z6]),(0,[z140,z1,z2,z3,z159,z6])],[(0,[z0,z1,z2,z3,z4,z1406]),(0,[z0,z1407,z2,z3,z4,z6]),(0,[z86,z1,z2,z3,z4,z82]),(0,[z0,z1,z128,z12,z166,z6]),(0,[z0,z1,z2,z3,z1145,z6])],[(0,[z0,z1,z2,z1408,z4,z6]),(0,[z0,z1,z2,z1409,z4,z6]),(0,[z103,z222,z1,z2,z3,z6]),(0,[z1,z2,z3,z33,z6,z53]),(0,[z0,z773,z2,z3,z33,z6])],[(0,[z289,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z1410,z6]),(0,[z0,z1,z1116,z2,z14,z6]),(0,[z0,z1,z30,z12,z14,z6]),(0,[z222,z1,z2,z3,z33,z6]),(0,[z0,z1,z2,z3,z1411,z6]),(0,[z1412,z1,z2,z3,z4,z6])],[(0,[z43,z858,z2,z3,z4,z6]),(0,[z1153,z0,z2,z3,z4,z6]),(0,[z0,z1,z16,z405,z3,z6]),(0,[z1,z2,z3,z4,z6,z1413]),(0,[z0,z1,z1414,z3,z4,z6])],[(0,[z0,z1,z2,z3,z1415,z6]),(0,[z24,z1,z2,z3,z7,z6]),(0,[z0,z1416,z2,z3,z4,z6]),(0,[z0,z1,z2,z1417,z4,z6]),(0,[z0,z1,z2,z12,z31,z70]),(0,[z0,z1,z2,z1418,z4,z6]),(0,[z0,z1,z529,z2,z3,z332]),(0,[z0,z1,z2,z14,z6,z38])],[(0,[z0,z2,z3,z197,z14,z6]),(0,[z303,z0,z1,z26,z2,z6]),(0,[z0,z1,z2,z3,z975,z6]),(0,[z0,z1,z2,z185,z14,z6]),(0,[z0,z924,z2,z12,z4,z6]),(0,[z0,z1,z2,z14,z6,z545])],[(0,[z0,z1,z543,z3,z33,z6]),(0,[z0,z1256,z2,z3,z4,z6]),(0,[z37,z0,z1,z16,z3,z47]),(0,[z0,z1,z2,z3,z70,z898])],[(0,[z43,z55,z2,z12,z4,z6]),(0,[z0,z142,z2,z3,z72,z6]),(0,[z11,z0,z488,z12,z4,z6]),(0,[z0,z1,z849,z3,z33,z6]),(0,[z0,z1,z315,z30,z3,z6])],[(0,[z0,z1,z381,z2,z3,z6]),(0,[z1,z374,z12,z161,z4,z6]),(0,[z80,z0,z1,z468,z4,z6]),(0,[z0,z1,z2,z41,z14,z6]),(0,[z160,z1,z2,z12,z4,z6]),(0,[z0,z1,z2,z4,z188,z1050])],[(0,[z43,z2,z3,z4,z6,z290]),(0,[z0,z1,z2,z3,z14,z44]),(0,[z11,z0,z1,z2,z4,z377]),(0,[z0,z1,z426,z3,z33,z6]),(0,[z289,z0,z1,z2,z12,z6]),(0,[z0,z1,z2,z3,z6,z1419]),(0,[z0,z253,z26,z2,z3,z6]),(0,[z0,z1,z954,z2,z3,z6])],[(0,[z0,z1,z2,z299,z33,z6]),(0,[z0,z1,z2,z4,z6,z1420]),(0,[z0,z1,z2,z3,z1161,z6]),(0,[z0,z1,z2,z3,z1100,z6])],[(0,[z0,z55,z2,z17,z14,z6]),(0,[z0,z1,z2,z308,z4,z524]),(0,[z0,z1,z2,z3,z1421,z6]),(0,[z0,z1,z234,z128,z12,z6]),(0,[z0,z271,z2,z3,z33,z6]),(0,[z0,z1,z30,z171,z4,z6])]],
   [[(0,[z0,z1,z12,z161,z33,z6]),(0,[z930,z1,z2,z12,z4,z6]),(0,[z227,z0,z1,z2,z4,z50]),(0,[z0,z1,z16,z12,z109,z6])],[(0,[z303,z0,z1,z2,z4,z6]),(0,[z0,z1,z2,z3,z4,z148]),(0,[z0,z1,z12,z166,z6,z47]),(0,[z0,z1,z189,z1373,z4,z6])],[(0,[z445,z55,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z1422,z6]),(0,[z317,z0,z771,z2,z4,z6]),(0,[z221,z2,z3,z66,z4,z6]),(0,[z0,z1,z2,z3,z1423,z6]),(0,[z0,z2,z3,z4,z60,z826])],[(0,[z0,z64,z2,z3,z14,z6]),(0,[z0,z1140,z2,z3,z4,z6])],[(0,[z0,z1,z470,z3,z33,z6]),(0,[z138,z1,z2,z3,z4,z6]),(0,[z0,z1,z1424,z2,z3,z6]),(0,[z216,z11,z0,z1,z4,z6]),(0,[z0,z1,z12,z525,z4,z6]),(0,[z11,z447,z1,z2,z4,z6]),(0,[z0,z1,z2,z3,z1111,z6]),(0,[z0,z1,z16,z189,z3,z6])],[(0,[z0,z1,z382,z2,z14,z6]),(0,[z0,z2,z3,z17,z4,z148]),(0,[z1425,z0,z1,z2,z4,z6]),(0,[z1,z16,z2,z3,z6,z53]),(0,[z0,z1,z2,z12,z937,z6]),(0,[z209,z0,z1,z2,z194,z6])],[(0,[z71,z0,z271,z2,z3,z6]),(0,[z0,z1,z12,z528,z4,z6]),(0,[z0,z1,z2,z14,z6,z557]),(0,[z0,z1,z1426,z2,z3,z6])],[(0,[z0,z1,z22,z12,z33,z6]),(0,[z80,z1,z2,z78,z14,z6]),(0,[z0,z1,z2,z3,z70,z408]),(0,[z0,z1,z1427,z2,z3,z6]),(0,[z139,z0,z1,z315,z2,z6]),(0,[z0,z1,z16,z2,z135,z6]),(0,[z447,z1,z2,z3,z4,z172])],[(0,[z0,z1,z2,z81,z14,z6]),(0,[z28,z1,z2,z79,z39,z6]),(0,[z126,z0,z1,z2,z4,z377]),(1,[z0,z1,z297,z14,z6]),(0,[z0,z1,z2,z187,z33,z6]),(0,[z0,z1,z16,z2,z171,z6]),(0,[z641,z0,z1,z2,z14,z6]),(0,[z0,z314,z26,z2,z3,z6])],[(0,[z0,z448,z2,z3,z33,z6]),(0,[z0,z1,z2,z3,z1428,z6]),(0,[z28,z0,z1,z2,z919,z6]),(0,[z1429,z1,z2,z3,z4,z6]),(0,[z0,z106,z46,z134,z4,z6]),(0,[z0,z1,z2,z3,z756,z6]),(0,[z0,z1,z231,z3,z4,z6])],[(0,[z0,z1,z2,z596,z14,z6]),(0,[z0,z1430,z2,z3,z4,z6]),(0,[z1431,z1,z2,z3,z4,z6]),(0,[z0,z512,z2,z3,z217,z6])],[(0,[z0,z1,z2,z3,z14,z6]),(0,[z0,z1,z26,z306,z3,z6]),(0,[z0,z1432,z2,z3,z4,z6]),(0,[z15,z0,z2,z17,z4,z6])],[(0,[z42,z115,z2,z3,z33,z6]),(0,[z0,z1,z1130,z2,z3,z6]),(0,[z190,z0,z106,z46,z4,z6]),(0,[z0,z1,z2,z3,z135,z6]),(0,[z11,z1325,z1,z2,z4,z6]),(0,[z313,z0,z1,z26,z2,z6]),(0,[z0,z271,z26,z2,z3,z6]),(0,[z138,z1,z2,z3,z117,z6]),(0,[z0,z1,z1433,z3,z4,z6])],[(0,[z11,z0,z1,z234,z2,z6])],[(0,[z0,z19,z2,z3,z4,z618]),(0,[z0,z19,z2,z3,z4,z60]),(0,[z0,z1,z16,z2,z166,z6]),(0,[z0,z1,z16,z2,z392,z6])],[(0,[z0,z1,z2,z3,z1434,z6]),(0,[z80,z140,z1,z2,z4,z6]),(0,[z0,z18,z2,z41,z4,z6]),(0,[z0,z1,z2,z568,z14,z6])]],
   [[(0,[z0,z1,z2,z666,z14,z6])],[(0,[z0,z1,z306,z12,z4,z6]),(0,[z0,z1435,z2,z3,z4,z6]),(0,[z190,z0,z1,z246,z2,z6])],[(0,[z0,z1,z401,z3,z33,z6]),(0,[z1436,z0,z1,z2,z4,z6]),(0,[z94,z1,z22,z81,z4,z6]),(0,[z0,z1,z2,z12,z4,z534]),(0,[z0,z1437,z2,z3,z4,z6]),(0,[z0,z1,z3,z33,z6,z47]),(0,[z0,z1,z1196,z231,z3,z6])],[(0,[z0,z1,z1438,z2,z3,z6]),(0,[z0,z2,z3,z4,z6,z1439]),(0,[z0,z1,z2,z3,z4,z907]),(0,[z190,z0,z2,z17,z4,z6]),(0,[z0,z1,z2,z3,z1440,z6]),(0,[z0,z1,z2,z29,z187,z6]),(0,[z57,z0,z2,z3,z33,z91]),(0,[z0,z1,z2,z947,z4,z6]),(0,[z0,z1,z3,z4,z996,z47]),(0,[z0,z893,z2,z3,z4,z6])],[(0,[z0,z1,z378,z3,z4,z172])],[(0,[z94,z1,z22,z3,z4,z6]),(0,[z0,z1,z405,z3,z39,z6]),(0,[z0,z1,z2,z3,z1136,z6]),(0,[z0,z1,z2,z1441,z4,z6]),(0,[z0,z1,z2,z474,z14,z6])],[(0,[z544,z0,z1,z2,z14,z6]),(0,[z0,z448,z26,z2,z3,z6]),(0,[z317,z0,z1,z26,z2,z6]),(0,[z11,z0,z1,z2,z452,z6]),(0,[z0,z1,z122,z2,z406,z6]),(0,[z0,z1,z2,z12,z411,z6]),(0,[z519,z0,z1,z3,z4,z47]),(0,[z1442,z0,z1,z2,z4,z6])],[(0,[z0,z1,z2,z1443,z4,z6]),(0,[z1,z2,z3,z4,z6,z1444]),(0,[z11,z0,z1287,z2,z4,z6])],[(0,[z0,z1,z2,z1445,z4,z6]),(0,[z0,z1446,z2,z3,z4,z6]),(0,[z11,z0,z1,z2,z454,z6]),(0,[z103,z303,z1,z2,z104,z6]),(0,[z0,z1,z2,z1447,z4,z6]),(0,[z143,z0,z579,z2,z3,z6]),(0,[z182,z0,z1,z13,z3,z6]),(0,[z160,z1,z2,z339,z4,z6])],[(0,[z42,z115,z26,z2,z3,z6]),(0,[z0,z1,z2,z1448,z4,z6]),(0,[z0,z1,z12,z4,z6,z546]),(0,[z131,z0,z1,z30,z33,z6])],[(0,[z0,z49,z2,z299,z4,z6]),(0,[z337,z236,z0,z3,z4,z6]),(0,[z0,z253,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z1449,z6]),(0,[z131,z0,z1,z2,z14,z6])],[(0,[z0,z1,z306,z3,z4,z377]),(0,[z0,z1,z1450,z3,z4,z6]),(0,[z0,z106,z16,z46,z3,z6]),(0,[z0,z1,z2,z12,z487,z6]),(0,[z0,z220,z2,z3,z277,z6]),(0,[z0,z1,z30,z3,z4,z364]),(0,[z0,z1,z1451,z468,z3,z6])],[(0,[z0,z49,z2,z3,z4,z524]),(0,[z0,z1452,z2,z3,z4,z6]),(0,[z11,z0,z1,z2,z39,z6]),(0,[z11,z0,z1,z2,z1034,z6])],[(0,[z0,z1453,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z1454,z6]),(0,[z11,z0,z1,z2,z6,z418]),(0,[z190,z0,z1,z2,z479,z6]),(0,[z139,z0,z220,z2,z4,z6]),(0,[z0,z1,z2,z76,z4,z6])],[(0,[z94,z49,z2,z3,z4,z6]),(0,[z317,z0,z1,z2,z4,z6]),(0,[z0,z1,z2,z3,z1455,z6]),(0,[z0,z46,z3,z783,z4,z6]),(0,[z0,z106,z1,z12,z33,z6]),(0,[z0,z1,z228,z12,z4,z6]),(0,[z0,z1,z26,z30,z12,z6]),(0,[z11,z0,z488,z16,z2,z6]),(0,[z0,z323,z26,z2,z3,z6]),(0,[z140,z1,z231,z3,z4,z6])],[(0,[z11,z43,z55,z2,z4,z6]),(0,[z0,z49,z2,z3,z229,z6]),(0,[z0,z2,z123,z17,z14,z6])]],
   [[(0,[z337,z0,z2,z3,z4,z6]),(0,[z222,z1,z2,z3,z4,z6]),(0,[z0,z18,z2,z123,z14,z6]),(0,[z57,z0,z26,z2,z3,z91]),(0,[z0,z1,z26,z128,z12,z6]),(0,[z0,z1,z12,z4,z109,z6])],[(0,[z337,z2,z3,z4,z6,z82]),(0,[z0,z119,z2,z3,z14,z6]),(0,[z28,z0,z1,z2,z277,z6]),(0,[z54,z0,z307,z66,z4,z6]),(0,[z1456,z1,z2,z3,z4,z6]),(0,[z1321,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z159,z6])],[(0,[z1,z858,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z1457,z6]),(0,[z73,z1,z2,z12,z4,z82]),(0,[z0,z1,z1458,z3,z4,z6])],[(0,[z1346,z1,z2,z3,z4,z6]),(0,[z447,z1,z2,z3,z4,z47])],[(0,[z21,z3,z197,z161,z4,z6]),(0,[z0,z1,z2,z12,z4,z377]),(0,[z0,z1,z26,z347,z3,z6]),(0,[z1459,z0,z1,z2,z4,z6]),(0,[z54,z0,z1,z12,z4,z148]),(0,[z1460,z0,z1,z2,z4,z6]),(0,[z0,z1,z2,z3,z1461,z6]),(0,[z459,z0,z1,z2,z4,z557])],[(0,[z80,z1,z2,z3,z4,z377]),(0,[z190,z0,z18,z2,z4,z6]),(0,[z0,z1,z13,z2,z3,z6]),(0,[z0,z1,z849,z3,z4,z6]),(0,[z0,z1,z30,z3,z109,z6]),(0,[z0,z1,z2,z3,z31,z492])],[(0,[z0,z1,z2,z3,z1462,z6]),(0,[z28,z1,z2,z79,z33,z6]),(0,[z0,z1,z720,z12,z4,z6]),(0,[z0,z1,z2,z3,z1463,z6]),(0,[z0,z1,z2,z406,z33,z6]),(0,[z0,z1,z1464,z2,z3,z6])],[(0,[z0,z1,z1465,z2,z3,z6]),(0,[z80,z1,z2,z848,z4,z6]),(0,[z0,z1,z1466,z2,z3,z6]),(0,[z0,z1,z2,z3,z6,z1467]),(0,[z0,z1,z1451,z2,z3,z6]),(0,[z0,z1351,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z1468,z6]),(0,[z0,z142,z125,z2,z3,z6]),(0,[z0,z1,z2,z12,z992,z6]),(0,[z0,z1,z220,z2,z277,z6]),(0,[z62,z0,z1,z16,z2,z38])],[(0,[z0,z1,z2,z3,z1469,z6]),(0,[z0,z1,z1362,z2,z308,z6]),(0,[z1470,z0,z1,z2,z3,z6]),(0,[z0,z410,z2,z3,z33,z6]),(0,[z0,z1,z3,z12,z4,z148]),(0,[z1471,z1,z2,z3,z4,z6]),(0,[z236,z11,z0,z1,z33,z6]),(0,[z139,z0,z1,z16,z2,z6])],[(0,[z0,z1,z12,z161,z4,z6]),(0,[z1,z22,z3,z753,z4,z6]),(0,[z236,z317,z0,z1,z4,z6]),(0,[z236,z0,z1,z3,z4,z148]),(0,[z0,z1,z26,z3,z525,z6]),(0,[z0,z1,z16,z231,z3,z6]),(0,[z0,z1,z2,z1472,z4,z6])],[(0,[z0,z220,z2,z4,z277,z6])],[(0,[z0,z1,z2,z3,z4,z1473]),(0,[z0,z1,z1474,z3,z4,z6]),(0,[z1475,z1,z2,z3,z4,z6]),(0,[z0,z1,z12,z4,z6,z567]),(0,[z0,z1,z13,z2,z12,z6]),(0,[z75,z1,z577,z2,z3,z6])],[(0,[z0,z1,z3,z1476,z4,z6]),(0,[z453,z0,z1,z12,z4,z6]),(0,[z11,z1,z2,z4,z6,z53]),(0,[z0,z1,z12,z634,z4,z6]),(0,[z0,z1,z152,z2,z14,z6]),(0,[z0,z1,z149,z114,z3,z6]),(0,[z0,z1,z16,z940,z3,z6]),(0,[z0,z1,z16,z2,z63,z188])],[(0,[z0,z1,z2,z3,z1477,z6]),(0,[z0,z1,z1478,z2,z3,z6]),(0,[z11,z0,z1,z2,z4,z534]),(0,[z54,z0,z1,z12,z14,z6]),(0,[z0,z1,z1466,z297,z3,z6]),(0,[z0,z1,z152,z2,z135,z6])],[(0,[z0,z1,z12,z569,z4,z6]),(0,[z103,z1,z2,z104,z300,z6]),(0,[z0,z1,z26,z2,z6,z287]),(0,[z0,z1,z149,z2,z166,z6]),(0,[z0,z1,z13,z3,z166,z6]),(0,[z0,z1,z2,z14,z6,z624]),(0,[z140,z253,z2,z3,z4,z6])]],
   [[(0,[z0,z1,z2,z1479,z4,z6]),(0,[z1480,z0,z1,z2,z3,z6]),(0,[z0,z106,z225,z12,z4,z6]),(0,[z0,z1,z2,z3,z51,z6]),(0,[z0,z1,z1481,z2,z3,z6]),(0,[z0,z512,z2,z3,z4,z172])],[(0,[z0,z1,z2,z3,z4,z1482]),(0,[z0,z1,z22,z12,z4,z6]),(0,[z0,z119,z2,z4,z14,z6]),(0,[z0,z1,z297,z3,z33,z6]),(0,[z0,z1,z2,z12,z1005,z6]),(0,[z11,z0,z1,z99,z33,z6]),(0,[z0,z1,z2,z109,z166,z6])],[(0,[z0,z1,z2,z3,z1085,z6]),(0,[z21,z1,z3,z161,z229,z6]),(0,[z0,z1,z2,z187,z4,z6]),(0,[z0,z1,z2,z93,z4,z6]),(0,[z0,z488,z26,z2,z3,z6]),(0,[z0,z1,z16,z2,z214,z6])],[(0,[z0,z1,z405,z3,z33,z6]),(0,[z0,z1,z2,z307,z4,z469]),(0,[z54,z0,z3,z66,z4,z148]),(0,[z0,z1,z122,z2,z14,z6]),(0,[z335,z1,z2,z3,z33,z6])],[(0,[z0,z858,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z1483,z6]),(0,[z1484,z1,z2,z3,z4,z6]),(0,[z0,z1,z122,z2,z12,z6]),(0,[z0,z1,z2,z171,z166,z6]),(0,[z0,z1,z2,z14,z6,z601])],[(0,[z0,z1,z2,z3,z4,z1485]),(0,[z0,z1261,z2,z3,z4,z6]),(0,[z0,z106,z246,z46,z3,z6]),(0,[z447,z1,z2,z12,z4,z6]),(0,[z0,z1,z16,z2,z97,z6])],[(0,[z0,z1,z2,z3,z1486,z6]),(0,[z0,z1,z2,z3,z4,z1487]),(0,[z1,z2,z3,z1279,z4,z6]),(0,[z0,z1,z1488,z2,z3,z6]),(0,[z0,z1,z26,z157,z3,z6]),(0,[z0,z1,z30,z3,z4,z996]),(0,[z0,z1,z2,z4,z6,z1489]),(0,[z0,z1,z189,z3,z14,z6]),(0,[z0,z810,z2,z3,z4,z6])],[(0,[z0,z1,z2,z1490,z4,z6]),(0,[z0,z1,z2,z1491,z4,z6]),(0,[z15,z0,z2,z17,z191,z6]),(0,[z11,z0,z488,z2,z277,z6]),(0,[z11,z0,z1,z2,z487,z6]),(0,[z0,z1,z2,z1492,z4,z6]),(0,[z0,z1,z2,z3,z217,z6]),(0,[z0,z1,z3,z4,z172,z996])],[(0,[z21,z448,z3,z161,z4,z6]),(0,[z0,z1,z1493,z2,z3,z6]),(0,[z1494,z0,z1,z2,z4,z6]),(0,[z1495,z1,z2,z3,z4,z6]),(0,[z1242,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z339,z6,z32])],[(0,[z669,z0,z1,z2,z14,z6]),(0,[z0,z1,z2,z3,z1496,z6]),(0,[z1062,z0,z1,z12,z4,z6]),(0,[z0,z1,z2,z1497,z4,z6]),(0,[z0,z323,z2,z443,z4,z6])],[(0,[z0,z49,z2,z12,z4,z6]),(0,[z0,z1,z306,z3,z39,z6]),(0,[z0,z1,z1498,z3,z4,z6]),(0,[z11,z0,z1,z2,z33,z6]),(0,[z0,z488,z220,z2,z4,z6]),(0,[z0,z1,z2,z93,z117,z6])],[(0,[z0,z1,z2,z3,z1192,z6]),(1,[z0,z1,z405,z14,z6]),(0,[z71,z0,z1,z2,z339,z6]),(0,[z0,z52,z1,z2,z947,z6])],[(0,[z0,z1,z16,z2,z3,z148]),(0,[z0,z1,z683,z12,z4,z6]),(0,[z0,z1,z2,z1499,z4,z6]),(0,[z1,z2,z3,z4,z53,z47]),(0,[z0,z1097,z2,z3,z4,z6])],[(0,[z0,z2,z3,z4,z6,z84]),(0,[z0,z1,z2,z3,z1500,z6]),(0,[z0,z1,z2,z12,z452,z6]),(0,[z0,z1,z2,z1501,z4,z6]),(0,[z54,z0,z3,z66,z14,z6]),(0,[z1502,z1,z2,z3,z4,z6]),(0,[z11,z0,z1,z12,z166,z6]),(0,[z236,z0,z488,z3,z4,z6]),(0,[z0,z1189,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z1503,z6]),(0,[z1,z22,z12,z161,z4,z6]),(0,[z0,z1,z382,z12,z4,z6]),(0,[z80,z1,z2,z4,z6,z349]),(0,[z11,z0,z52,z1,z2,z6]),(0,[z730,z0,z1,z30,z4,z6]),(1,[z0,z1,z12,z109,z6]),(0,[z536,z0,z1,z2,z277,z6]),(0,[z0,z314,z2,z3,z33,z6]),(0,[z1504,z0,z1,z2,z4,z6])],[(0,[z0,z1,z2,z3,z4,z1505]),(0,[z0,z1,z2,z12,z454,z6]),(0,[z0,z1,z2,z14,z6,z615]),(0,[z0,z2,z3,z66,z4,z148]),(0,[z0,z1,z2,z12,z1028,z6]),(0,[z138,z1,z16,z2,z3,z6])]]]

def SA : ℕ × List W → Bool := fun c => !inB2 16 512 bkA c

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 462) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 462).take 463) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 925).take 465) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb3 : chunkB SB 1 ((bkA.flatten.flatten.drop 1390).take 261) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1651)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [462, 463, 465, 261] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_cons pb3 (windowsG_nil pbend))))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 86).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 86).take 79).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 165).take 81).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 246).take 73).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc4 : chunkOK 5 ((bkB.flatten.drop 319).take 72).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc5 : chunkOK 5 ((bkB.flatten.drop 391).take 81).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc6 : chunkOK 5 ((bkB.flatten.drop 472).take 40).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 512)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [86, 79, 81, 73, 72, 81, 40] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_cons pc3 (windowsF_cons pc4 (windowsF_cons pc5 (windowsF_cons pc6 (windowsF_nil pcend)))))))

theorem reject : search 8 rows = false :=
  search_false_C2 (dp := 0) (J := 5) (d := 2) (g1 := 16) (nb1 := 512) (g2 := 16) (nb2 := 512) (by norm_num) gf windowsC windowsB windowsA

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

end PEqualNP.Outside.L_meta_36350

theorem PEqualNP.Outside.L_meta_36350 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075690 * 2 ^ 32 + 4277074144) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075690 * 2 ^ 32 + 4277074144) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_36350.solve