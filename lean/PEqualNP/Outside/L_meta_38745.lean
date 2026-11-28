import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_38745

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
  Nat.testBit (4276808426 * 2 ^ 32 + 4004176032) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x1000001414422c2b#64 ++ 0x0800000a0a211615#64 ++ 0xea808e7c7cc7fc7f#64 ++ 0xf540473e3e63fe3f#64 : BitVec 256),
   (0x208334b1b1596599#64 ++ 0x90419a58d8acb2cc#64 ++ 0xdf8775b3b3796799#64 ++ 0xefc3bad9d9bcb3cc#64 : BitVec 256),
   (0x40385942c38182d4#64 ++ 0x201c2ca161c0c16a#64 ++ 0xbf7879c3c38187ff#64 ++ 0xdfbc3ce1e1c0c3ff#64 : BitVec 256),
   (0x815d81fc02ee0761#64 ++ 0xc0aec0fe017703b0#64 ++ 0x7dff81fc03fe07e1#64 ++ 0xbeffc0fe01ff03f0#64 : BitVec 256),
   (0x006efe0003b5d000#64 ++ 0x00377f0001dae800#64 ++ 0xf9fffe0003fff801#64 ++ 0x7cffff0001fffc00#64 : BitVec 256),
   (0x0277efeb68000000#64 ++ 0x013bf7f5b4000000#64 ++ 0xfe7ffffffc000000#64 ++ 0xff3ffffffe000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [1, 3]⟩, ⟨.or, [0, 6]⟩, ⟨.or, [2, 4]⟩, ⟨.and, [7, 8]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [1, 10]⟩, ⟨.and, [2, 11]⟩, ⟨.or, [0, 12]⟩, ⟨.and, [13, 5]⟩, ⟨.or, [9, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x006efe0003b5d000 0x00377f0001dae800 0xf9fffe0003fff801 0x7cffff0001fffc00

def z1 : W := mkw 0x0277efeb68000000 0x013bf7f5b4000000 0xfe7ffffffc000000 0xff3ffffffe000000

def z2 : W := mkw 0x1000001414422c2b 0x0800000a0a211615 0xea808e7c7cc7fc7f 0xf540473e3e63fe3f

def z3 : W := mkw 0x208334b1b1596599 0x90419a58d8acb2cc 0xdf8775b3b3796799 0xefc3bad9d9bcb3cc

def z4 : W := mkw 0x40304942c00002d4 0x201824a16000016a 0xbe7879c3c00007fe 0xdf3c3ce1e00003ff

def z5 : W := mkw 0x40385942c38182d4 0x201c2ca161c0c16a 0xbf7879c3c38187ff 0xdfbc3ce1e1c0c3ff

def z6 : W := mkw 0x815d81fc02ee0761 0xc0aec0fe017703b0 0x7dff81fc03fe07e1 0xbeffc0fe01ff03f0

def z7 : W := mkw 0x8110014c00020260 0x408800a600010130 0x0000004c00000060 0x0000002600000030

def z8 : W := mkw 0x1028581417c3ac2b 0x08142c0a0be1d615 0xfbf8fe7c7fc7fc7f 0xfdfc7f3e3fe3fe3f

def z9 : W := mkw 0x81000014006e0521 0xc080000a00370290 0x00800000007e0000 0x00400000003f0000

def z10 : W := mkw 0x005581e800000000 0x002ac0f400000000 0x7c7f81fc00000000 0xbe3fc0fe00000000

def z11 : W := mkw 0x8108001402ee0761 0xc084000a017703b0 0x0180000003fe07e1 0x00c0000001ff03f0

def z12 : W := mkw 0x208334a1a1194190 0x90419a50d08ca0c8 0x1507718383380380 0x0a83b8c1c19c01c0

def z13 : W := mkw 0x0000001400420421 0x0000000a00210210 0x6880807c00c60461 0xb440403e00630230

def z14 : W := mkw 0x0000000000000000 0x0000000000000000 0xca00043030000000 0xe500021818000000

def z15 : W := mkw 0x20eefe1093fdf599 0x90777f0849fefacc 0xf9fffe0003ffff99 0x7cffff0001ffffcc

def z16 : W := mkw 0x0000000400020020 0x0000000200010010 0x2000804c00860060 0x1000402600430030

def z17 : W := mkw 0x815d81e802ac0340 0xc0aec0f4015601a0 0x157f018003380380 0x0abf80c0019c01c0

def z18 : W := mkw 0x915d81fc16ee2f6b 0xc8aec0fe0b7717b5 0xffff8ffc7fffffff 0xffffc7fe3fffffff

def z19 : W := mkw 0x1000001414422c2b 0x0800000a0a211615 0x0280007c7cc7fc7f 0x8140003e3e63fe3f

def z20 : W := mkw 0x027fffeb6bb5d000 0x013ffff5b5dae800 0xfffffffffffff801 0xfffffffffffffc00

def z21 : W := mkw 0x1277efff7c422c2b 0x093bf7ffbe211615 0xfefffffffcc7fc7f 0xff7ffffffe63fe3f

def z22 : W := mkw 0x20800001b0002098 0x10400000d800104c 0x02000003b0000018 0x01000001d800000c

def z23 : W := mkw 0x208334a1b1116098 0x10419a50d888b04c 0xde0775b3b0016018 0xef03bad9d800b00c

def z24 : W := mkw 0x308334b5b55b6dbb 0x98419a5adaadb6dd 0xff87ffffffffffff 0xffc3ffffffffffff

def z25 : W := mkw 0x1000000404020822 0x0800000202010411 0x20008a4c4c869866 0x1000452626434c33

def z26 : W := mkw 0x20823401a1114090 0x10411a00d088a048 0x0000700380000000 0x00003801c0000000

def z27 : W := mkw 0x0000100081010090 0x0000080040808048 0x9f00718383010799 0xcf8038c1c18083cc

def z28 : W := mkw 0x0066ee0000000000 0x0033770000000000 0xf87ffe0000000000 0x7c3fff0000000000

def z29 : W := mkw 0x208100a1a0080190 0x90408050d00400c8 0x0400018380000380 0x020000c1c00001c0

def z30 : W := mkw 0x004c800002a40000 0x0026400001520000 0x79ff800003fe0001 0x3cffc00001ff0000

def z31 : W := mkw 0x427fffebeb8182d4 0x213ffff5f5c0c16a 0xff7fffffff8187ff 0xffbfffffffc0c3ff

def z32 : W := mkw 0xb1dfb5fdb7ff6ffb 0xd8efdafedbffb7fd 0xffffffffffffffff 0xffffffffffffffff

def z33 : W := mkw 0x427fefeb6a808244 0x213ff7f5b5404122 0xfe7ffffffc808066 0xff3ffffffe404033

def z34 : W := mkw 0x1000001414422c2b 0x0800000a0a211615 0x4080863c3c467800 0x2040431e1e233c00

def z35 : W := mkw 0x021101eb68000000 0x010880f5b4000000 0x060001fffc000000 0x830000fffe000000

def z36 : W := mkw 0x006efe0003b5d000 0x00377f0001dae800 0x117f700003380000 0x08bfb800019c0000

def z37 : W := mkw 0x1000001414422c2b 0x0800000a0a211615 0xaa00087c7c81847f 0xd500043e3e40c23f

def z38 : W := mkw 0x811101fc004a0761 0xc08880fe002503b0 0x040001fc000007e0 0x820000fe000003f0

def z39 : W := mkw 0x8118015402ee0761 0xc08c00aa017703b0 0x3df801c003fe07e1 0x9efc00e001ff03f0

def z40 : W := mkw 0x004c900003b5d000 0x0026480001dae800 0x79ff800003fff801 0x3cffc00001fffc00

def z41 : W := mkw 0xa1dfa5fd32fe6769 0xd0efd2fe997f33b4 0x7dff85fc33fe67e1 0xbeffc2fe19ff33f0

def z42 : W := mkw 0x006ffeb003fdd501 0x8037ff5801feea80 0xfdffffb003ffff81 0xfeffffd801ffffc0

def z43 : W := mkw 0x20effeb1b3fdf599 0x9077ff58d9fefacc 0xffffffb3b3ffff99 0xffffffd9d9ffffcc

def z44 : W := mkw 0x006efe0003818000 0x00377f0001c0c000 0xf97ffe0003818001 0x7cbfff0001c0c000

def z45 : W := mkw 0x50385956d7c3aeff 0x281c2cab6be1d77f 0xfff8ffffffc7ffff 0xfffc7fffffe3ffff

def z46 : W := mkw 0x917ffffc17ffff6b 0xc8bffffe0bffffb5 0xfffffffc7fffffff 0xfffffffe3fffffff

def z47 : W := mkw 0x0010014240000000 0x000800a120000000 0x060001c3c0000000 0x830000e1e0000000

def z48 : W := mkw 0x20a27e01b111f098 0x10513f00d888f84c 0x82007e03b001f818 0x41003f01d800fc0c

def z49 : W := mkw 0x000100b000480501 0x8000805800240280 0x5d8701b003780781 0xaec380d801bc03c0

def z50 : W := mkw 0x815d81fc02ee0761 0xc0aec0fe017703b0 0x15ff018003fe07e1 0x0aff80c001ff03f0

def z51 : W := mkw 0x40385942c38182d4 0x201c2ca161c0c16a 0x1578718383000380 0x0abc38c1c18001c0

def z52 : W := mkw 0x001901f002c80741 0x800c80f8016403a0 0x7dff01f003f807e1 0xbeff80f801fc03f0

def z53 : W := mkw 0x4277efebe80002d4 0x213bf7f5f400016a 0xfe7ffffffc0007fe 0xff3ffffffe0003ff

def z54 : W := mkw 0x0277efeb68000000 0x013bf7f5b4000000 0x147f718380000000 0x0a3fb8c1c0000000

def z55 : W := mkw 0x837dcbfe4aee0761 0xc1bee5ff257703b0 0x7dff8bfc4ffe07e1 0xbeffc5fe27ff03f0

def z56 : W := mkw 0x0020480240000000 0x0010240120000000 0x82007803c0000000 0x41003c01e0000000

def z57 : W := mkw 0x2082341091596599 0x90411a0848acb2cc 0xd987740003796799 0x6cc3ba0001bcb3cc

def z58 : W := mkw 0x1000001414422c2b 0x0800000a0a211615 0x0080000000c7fc7f 0x004000000063fe3f

def z59 : W := mkw 0x208334a1a1194190 0x90419a50d08ca0c8 0xdf0775b3b3380380 0xef83bad9d99c01c0

def z60 : W := mkw 0x62fffffbfbd9e7dd 0xb17ffffdfdecf3ee 0xfffffffffff9e7ff 0xfffffffffffcf3ff

def z61 : W := mkw 0x1000001414422c2b 0x0800000a0a211615 0x22008a7c7c869c7e 0x9100453e3e434e3f

def z62 : W := mkw 0x021325eb68000000 0x010992f5b4000000 0xde0775fffc000000 0xef03bafffe000000

def z63 : W := mkw 0x000100b010482509 0x8000805808241284 0xdf8705b033796799 0xefc382d819bcb3cc

def z64 : W := mkw 0x308334b1b5596d9b 0x98419a58daacb6cd 0xdf877fb3ff79ff9f 0xefc3bfd9ffbcffcf

def z65 : W := mkw 0x814580bc006e0521 0xc0a2c05e00370290 0x4087803c007e0000 0x2043c01e003f0000

def z66 : W := mkw 0xc17dd9fec3ef87f5 0xe0beecff61f7c3fa 0xfffff9ffc3ff87ff 0xfffffcffe1ffc3ff

def z67 : W := mkw 0x815d81e802ac0340 0xc0aec0f4015601a0 0x7d7f81fc03380380 0xbebfc0fe019c01c0

def z68 : W := mkw 0x006eee0002a49000 0x0037770001524800 0xf87ffe0000869800 0x7c3fff0000434c00

def z69 : W := mkw 0x40100142c00002d4 0x200800a16000016a 0x060001c3c00007fe 0x830000e1e00003ff

def z70 : W := mkw 0x407eff42c3b5d2d4 0x203f7fa161dae96a 0xffffffc3c3ffffff 0xffffffe1e1ffffff

def z71 : W := mkw 0x815c814c02a60260 0x40ae40a601530130 0x2078804c00860060 0x103c402600430030

def z72 : W := mkw 0xa1dfb5fdb3ff67f9 0xd0efdafed9ffb3fc 0xfffff5ffb3ff67f9 0xfffffaffd9ffb3fc

def z73 : W := mkw 0x1018015416c22e6b 0x080c00aa0b611735 0xfff88ffc7fc7ffff 0xfffc47fe3fe3ffff

def z74 : W := mkw 0xc11101fec04a07f5 0xe08880ff602503fa 0x060001ffc00007fe 0x830000ffe00003ff

def z75 : W := mkw 0x1000000404020822 0x0800000202010411 0x0000004c4c000066 0x0000002626000033

def z76 : W := mkw 0x40205802c1018094 0x20102c016080c04a 0xaa007843c081847f 0xd5003c21e040c23f

def z77 : W := mkw 0x000110b081490591 0x8000885840a482c8 0xdf8771b383790799 0xefc3b8d9c1bc83cc

def z78 : W := mkw 0x0000000000000000 0x0000000000000000 0xe8808e0000c7f801 0x744047000063fc00

def z79 : W := mkw 0x40385942c38182d4 0x201c2ca161c0c16a 0xfff8ffc3c3c7ffff 0xfffc7fe1e1e3ffff

def z80 : W := mkw 0x837fefff6aee0761 0xc1bff7ffb57703b0 0xfffffffffffe07e1 0xffffffffffff03f0

def z81 : W := mkw 0x02226e0368000000 0x01113701b4000000 0x82007e03fc000000 0x41003f01fe000000

def z82 : W := mkw 0x0028580003818000 0x00142c0001c0c000 0xf9f8fe0003c7f801 0x7cfc7f0001e3fc00

def z83 : W := mkw 0x000324a120000000 0x0001925090000000 0xde0775b3b0000000 0xef03bad9d8000000

def z84 : W := mkw 0x0000000000000000 0x0000000000000000 0x820008004001801e 0x410004002000c00f

def z85 : W := mkw 0x0018014002800240 0x000c00a001400120 0x2078004000800060 0x103c002000400030

def z86 : W := mkw 0x0018014002800240 0x000c00a001400120 0x3d7801c0038007e1 0x9ebc00e001c003f0

def z87 : W := mkw 0x1000001414422c2b 0x0800000a0a211615 0x0200007c7c00047e 0x8100003e3e00023f

def z88 : W := mkw 0x027fefeb6aa49000 0x013ff7f5b5524800 0xfe7ffffffc869800 0xff3ffffffe434c00

def z89 : W := mkw 0x0000000000000000 0x0000000000000000 0xaa0008404081847f 0xd50004202040c23f

def z90 : W := mkw 0x005581e800000000 0x002ac0f400000000 0xfe7f8ffc7c000000 0xff3fc7fe3e000000

def z91 : W := mkw 0x0000000000000000 0x0000000000000000 0xea008e7c7c000000 0xf500473e3e000000

def z92 : W := mkw 0x006efe0003b5d000 0x00377f0001dae800 0x11ff700003fff801 0x08ffb80001fffc00

def z93 : W := mkw 0x20823401b1116098 0x10411a00d888b04c 0x82007403b0016018 0x41003a01d800b00c

def z94 : W := mkw 0x835d81ff6aee0761 0xc1aec0ffb57703b0 0x7fff81fffffe07e1 0xbfffc0ffffff03f0

def z95 : W := mkw 0x004c801402e60421 0x0026400a01730210 0x79ff807c03fe0461 0xbcffc03e01ff0230

def z96 : W := mkw 0x106cca1416e6bc2b 0x0836650a0b735e15 0xeaf88e7c7cc7fc7f 0xf57c473e3e63fe3f

def z97 : W := mkw 0x0000001010402409 0x0000000808201204 0x0080000000416419 0x004000000020b20c

def z98 : W := mkw 0x406efe0083b5d2d4 0x20377f0041dae96a 0xf9fffe0003ffffff 0x7cffff0001ffffff

def z99 : W := mkw 0x815c814802a40240 0x40ae40a401520120 0x0078000000000000 0x003c000000000000

def z100 : W := mkw 0x001101e800000000 0x000880f400000000 0x040001fc00000000 0x820000fe00000000

def z101 : W := mkw 0x0000000000000000 0x0000000000000000 0xa800080000818001 0x540004000040c000

def z102 : W := mkw 0x407cdb42c3a592d4 0x203e6da161d2c96a 0xbf78fbc3c3879fff 0xdfbc7de1e1c3cfff

def z103 : W := mkw 0x000324b130402409 0x0001925898201204 0xde8775b3b0416419 0xef43bad9d820b20c

def z104 : W := mkw 0x4008000002808244 0x2004000001404122 0x0000000000808066 0x0000000000404033

def z105 : W := mkw 0x000100b4004a0521 0x8000805a00250290 0x7d8781fc03fe07e1 0xbec3c0fe01ff03f0

def z106 : W := mkw 0x0046a60000345000 0x00235300001a2800 0xe8878e0000fff801 0x7443c700007ffc00

def z107 : W := mkw 0x208324b130586509 0x90419258982c3284 0x4087043030786000 0x20438218183c3000

def z108 : W := mkw 0x4038494242808244 0x201c24a121404122 0x2078084040808066 0x103c042020404033

def z109 : W := mkw 0x0028580003818000 0x00142c0001c0c000 0x1178700003000000 0x08bc380001800000

def z110 : W := mkw 0x208324b1b0586599 0x90419258d82c32cc 0x468705b3b0786798 0xa34382d9d83c33cc

def z111 : W := mkw 0x22f7ffebe9194190 0x917bfff5f48ca0c8 0x157f718383380380 0x0abfb8c1c19c01c0

def z112 : W := mkw 0x006efe0003b5d000 0x00377f0001dae800 0x51fff600037e7800 0x28fffb0001bf3c00

def z113 : W := mkw 0x0028580003818000 0x00142c0001c0c000 0xbb7878404381847f 0xddbc3c2021c0c23f

def z114 : W := mkw 0x0028580003818000 0x00142c0001c0c000 0xb978780003818001 0x5cbc3c0001c0c000

def z115 : W := mkw 0x026ffea92bb5d000 0x0137ff5495dae800 0xf9fffe3c3ffff801 0x7cffff1e1ffffc00

def z116 : W := mkw 0x1000001414422c2b 0x0800000a0a211615 0xca80043030c7fc7f 0xe54002181863fe3f

def z117 : W := mkw 0x0247a6a928000000 0x0123d35494000000 0x4007863c3c000000 0x2003c31e1e000000

def z118 : W := mkw 0x40081000838182d4 0x2004080041c0c16a 0x01000000038187ff 0x0080000001c0c3ff

def z119 : W := mkw 0x0030494240000000 0x001824a120000000 0xfe78fffffc000000 0xff3c7ffffe000000

def z120 : W := mkw 0x0000000000000000 0x0000000000000000 0x4000863c3c000000 0x2000431e1e000000

def z121 : W := mkw 0x0274cb4a48000000 0x013a65a524000000 0x0078000000000000 0x003c000000000000

def z122 : W := mkw 0x0000001000480501 0x8000000800240280 0x0180000003780781 0x00c0000001bc03c0

def z123 : W := mkw 0x9108001416ee2f6b 0xc884000a0b7717b5 0xeb808e7c7fffffff 0xf5c0473e3fffffff

def z124 : W := mkw 0x915c814c06a60a62 0x48ae40a603530531 0x20788a4c4c869866 0x103c452626434c33

def z125 : W := mkw 0x208334b1b1596599 0x90419a58d8acb2cc 0x170771b3b3380798 0x8b83b8d9d99c03cc

def z126 : W := mkw 0x0257a7eb68000000 0x012bd3f5b4000000 0x460787fffc000000 0xa303c3fffe000000

def z127 : W := mkw 0x02336feb68000000 0x0119b7f5b4000000 0x86007ffffc000000 0xc3003ffffe000000

def z128 : W := mkw 0x0000000000000000 0x0000000000000000 0xea008e7c7c81847f 0xf500473e3e40c23f

def z129 : W := mkw 0x0277effb68480501 0x813bf7fdb4240280 0xffffffffff780781 0xffffffffffbc03c0

def z130 : W := mkw 0x0046a60000345000 0x00235300001a2800 0x0007000000380000 0x00038000001c0000

def z131 : W := mkw 0x006efe0003b5d000 0x00377f0001dae800 0xfbfffe7c7ffff801 0xfdffff3e3ffffc00

def z132 : W := mkw 0x915d81fc16ee2f6b 0xc8aec0fe0b7717b5 0x7dff87fc3ffe7fe1 0xbeffc3fe1fff3ff0

def z133 : W := mkw 0x0000000000000000 0x0000000000000000 0xea808e7c7cc7f801 0xf540473e3e63fc00

def z134 : W := mkw 0x308334b5b55b6dbb 0x98419a5adaadb6dd 0xdf8775ffff7967ff 0xefc3baffffbcb3ff

def z135 : W := mkw 0x815d81e802ac0340 0xc0aec0f4015601a0 0x7dff818003fe0381 0x3effc0c001ff01c0

def z136 : W := mkw 0x421101ebe80002d4 0x210880f5f400016a 0x060001fffc0007fe 0x830000fffe0003ff

def z137 : W := mkw 0x20effea1a3bdd190 0x9077ff50d1dee8c8 0xfdffff8383fffb81 0x7effffc1c1fffdc0

def z138 : W := mkw 0x50205802d501a89e 0x28102c016a80d44f 0x82007e03fc01f81e 0x41003f01fe00fc0f

def z139 : W := mkw 0x817fffe803bdd340 0xc0bffff401dee9a0 0xfdffff8003fffb81 0x7effffc001fffdc0

def z140 : W := mkw 0x1046a61414767c2b 0x0823530a0a3b3e15 0xea878e7c7cfffc7f 0xf543c73e3e7ffe3f

def z141 : W := mkw 0x4277ffebe9018094 0x213bfff5f480c04a 0xfe7ffffffc01801e 0xff3ffffffe00c00f

def z142 : W := mkw 0x837fffff6bffd761 0xc1bfffffb5ffebb0 0xffffffffffffffe1 0xfffffffffffffff0

def z143 : W := mkw 0x006cca0002a49000 0x0036650001524800 0x20788a0000869800 0x103c450000434c00

def z144 : W := mkw 0x208100b1b0482599 0x90408058d82412cc 0x060001b3b0000798 0x830000d9d80003cc

def z145 : W := mkw 0x835fa7fd2aee0761 0xc1afd3fe957703b0 0x7dff87fc3ffe07e1 0xbeffc3fe1fff03f0

def z146 : W := mkw 0x40385952d3c1a6dd 0x201c2ca969e0d36e 0xfff87df3f3c1e7ff 0xfffc3ef9f9e0f3ff

def z147 : W := mkw 0x027fffeb6b818000 0x013ffff5b5c0c000 0xff7fffffff818001 0xffbfffffffc0c000

def z148 : W := mkw 0x609335f3f15967dd 0xb0499af9f8acb3ee 0xdf8775f3f37967ff 0xefc3baf9f9bcb3ff

def z149 : W := mkw 0x0008100003b5d000 0x0004080001dae800 0xe9808e0003fff801 0x74c0470001fffc00

def z150 : W := mkw 0x815581fc004a0761 0xc0aac0fe002503b0 0x7c7f81fc000007e0 0xbe3fc0fe000003f0

def z151 : W := mkw 0x229335fbf9596599 0x91499afdfcacb2cc 0xdf8775ffff796799 0xefc3baffffbcb3cc

def z152 : W := mkw 0x020100a928000000 0x0100805494000000 0x0000003c3c000000 0x0000001e1e000000

def z153 : W := mkw 0x0277efeb68000000 0x013bf7f5b4000000 0x167f71fffc000000 0x8b3fb8fffe000000

def z154 : W := mkw 0x0044820000241000 0x0022410000120800 0x0000820000061800 0x0000410000030c00

def z155 : W := mkw 0x0046a60000345000 0x00235300001a2800 0x40878600007e7800 0x2043c300003f3c00

def z156 : W := mkw 0x00227e000111d000 0x00113f000088e800 0x80007e000001f800 0x40003f000000fc00

def z157 : W := mkw 0x40385942c38182d4 0x201c2ca161c0c16a 0x15787183838187ff 0x0abc38c1c1c0c3ff

def z158 : W := mkw 0x004580a800000000 0x0022c05400000000 0x4007803c00000000 0x2003c01e00000000

def z159 : W := mkw 0x30823401b511689a 0x18411a00da88b44d 0x82007e03fc01f81e 0x41003f01fe00fc0f

def z160 : W := mkw 0x100000001400280a 0x080000000a001405 0x82000e007c01f81e 0x410007003e00fc0f

def z161 : W := mkw 0x208334b1a1594591 0x90419a58d0aca2c8 0x5d8771b383780781 0xaec3b8d9c1bc03c0

def z162 : W := mkw 0x000100a000080100 0x8000805000040080 0x1507018003380380 0x0a8380c0019c01c0

def z163 : W := mkw 0x004d80b002ec0501 0x8026c05801760280 0x7dff81b003fe0781 0xbeffc0d801ff03c0

def z164 : W := mkw 0x407ccb4242a49244 0x203e65a121524922 0x20788a4040869866 0x103c452020434c33

def z165 : W := mkw 0x4038494242808244 0x201c24a121404122 0xbe7879c3c0808066 0xdf3c3ce1e0404033

def z166 : W := mkw 0x000324b120480501 0x8001925890240280 0xdf8775b3b3780781 0xefc3bad9d9bc03c0

def z167 : W := mkw 0x8347a6bd286e0521 0xc1a3d35e94370290 0x4087863c3c7e0000 0x2043c31e1e3f0000

def z168 : W := mkw 0x4038494242808244 0x201c24a121404122 0xaa7808404081847f 0xd53c04202040c23f

def z169 : W := mkw 0x815d81fc02ee0761 0xc0aec0fe017703b0 0xffff89fc43ff87ff 0xffffc4fe21ffc3ff

def z170 : W := mkw 0x100000001400280a 0x080000000a001405 0xaa000e407c81fc7f 0xd50007203e40fe3f

def z171 : W := mkw 0x0000000000000000 0x0000000000000000 0x0200007c7c000000 0x8100003e3e000000

def z172 : W := mkw 0x1000001414422c2b 0x0800000a0a211615 0x6a80807c7cc6047f 0xb540403e3e63023f

def z173 : W := mkw 0x0000100081010090 0x0000080040808048 0x1500718383000380 0x0a8038c1c18001c0

def z174 : W := mkw 0x006eee0002b4d000 0x00377700015a6800 0x60ff8e0000fef800 0x307fc700007f7c00

def z175 : W := mkw 0x4020480240008004 0x2010240120004002 0x0000080040008006 0x0000040020004003

def z176 : W := mkw 0x0000001400420421 0x0000000a00210210 0x0080000000c60461 0x0040000000630230

def z177 : W := mkw 0x40181140838182d4 0x200c08a041c0c16a 0x3d7801c0038187ff 0x9ebc00e001c0c3ff

def z178 : W := mkw 0x406efe02c3b5d094 0x20377f0161dae84a 0xfbfffe03c3fff81f 0x7dffff01e1fffc0f

def z179 : W := mkw 0x8108000402a60260 0x4084000201530130 0x0000000000860060 0x0000000000430030

def z180 : W := mkw 0x403a7f42c391d2d4 0x201d3fa161c8e96a 0xbf787fc3c381ffff 0xdfbc3fe1e1c0ffff

def z181 : W := mkw 0x22f7fffbf9596599 0x917bfffdfcacb2cc 0xffffffffff796799 0xffffffffffbcb3cc

def z182 : W := mkw 0xa3fffffffbff67f9 0xd1fffffffdffb3fc 0xffffffffffff67f9 0xffffffffffffb3fc

def z183 : W := mkw 0x32f7fffffd5b6dbb 0x997bfffffeadb6dd 0xffffffffffffffff 0xffffffffffffffff

def z184 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z185 : W := mkw 0x40205802c1018094 0x20102c016080c04a 0x82007803c001801e 0x41003c01e000c00f

def z186 : W := mkw 0x0018014002800240 0x000c00a001400120 0x1578018003000380 0x0abc00c0018001c0

def z187 : W := mkw 0x006efe0083b5d090 0x00377f0041dae848 0xffffff8383ffff99 0xffffffc1c1ffffcc

def z188 : W := mkw 0x1000001414422c2b 0x0800000a0a211615 0xc2808e3c7c47f81e 0x6140471e3e23fc0f

def z189 : W := mkw 0x0008100003b5d000 0x0004080001dae800 0x0100000003380000 0x00800000019c0000

def z190 : W := mkw 0x1000000404020822 0x0800000202010411 0x0000820c0c061800 0x0000410606030c00

def z191 : W := mkw 0xc17dd9eac3ad83d4 0xe0beecf561d6c1ea 0xbf7f79c3c3b987ff 0xdfbfbce1e1dcc3ff

def z192 : W := mkw 0x02226e0368000000 0x01113701b4000000 0xea00fe7ffc000000 0xf5007f3ffe000000

def z193 : W := mkw 0x427fffebeb8182d4 0x213ffff5f5c0c16a 0xbf7f79c3c38187ff 0xdfbfbce1e1c0c3ff

def z194 : W := mkw 0x005581f800480501 0x802ac0fc00240280 0x7dff81fc03780781 0xbeffc0fe01bc03c0

def z195 : W := mkw 0x1277efff7c422c2b 0x093bf7ffbe211615 0xfefffffffc467800 0xff7ffffffe233c00

def z196 : W := mkw 0x815d81fc02ee0761 0xc0aec0fe017703b0 0x60ff807c00fe0060 0x307fc03e007f0030

def z197 : W := mkw 0x507eff56d7f7feff 0x283f7fab6bfbff7f 0xffffffffffffffff 0xffffffffffffffff

def z198 : W := mkw 0x0002340001114000 0x00011a000088a000 0xd987740003796001 0x6cc3ba0001bcb000

def z199 : W := mkw 0x815d81fc02ee0761 0xc0aec0fe017703b0 0xffff8ffc7ffe07e1 0xffffc7fe3fff03f0

def z200 : W := mkw 0x42227e03e9018094 0x21113f01f480c04a 0x82007e03fc01801e 0x41003f01fe00c00f

def z201 : W := mkw 0x006cca0002a49000 0x0036650001524800 0xe8f88e0000c7f801 0x747c47000063fc00

def z202 : W := mkw 0x308334b5b55b6dbb 0x98419a5adaadb6dd 0xdf87f7bfbf7f7f99 0xefc3fbdfdfbfbfcc

def z203 : W := mkw 0x208334a1a1194190 0x90419a50d08ca0c8 0xdd87758383796381 0x6ec3bac1c1bcb1c0

def z204 : W := mkw 0x2088101093fdf599 0x9044080849fefacc 0x0180000003ffff99 0x00c0000001ffffcc

def z205 : W := mkw 0x0030494240000000 0x001824a120000000 0xbe7879c3c0000000 0xdf3c3ce1e0000000

def z206 : W := mkw 0x911101fc144a2f6b 0xc88880fe0a2517b5 0x060001fc7c0007fe 0x830000fe3e0003ff

def z207 : W := mkw 0x2080101091596599 0x9040080848acb2cc 0x0180000003796799 0x00c0000001bcb3cc

def z208 : W := mkw 0x0075c9ea40000000 0x003ae4f520000000 0xfe7ff9ffc0000000 0xff3ffcffe0000000

def z209 : W := mkw 0x81000014004a0761 0xc080000a002503b0 0x00000000000007e0 0x00000000000003f0

def z210 : W := mkw 0x815d91fc03ffd761 0xc0aec8fe01ffebb0 0x7dff81fc03ffffe1 0xbeffc0fe01fffff0

def z211 : W := mkw 0x02204a0248000000 0x0110250124000000 0x00000a004c000000 0x0000050026000000

def z212 : W := mkw 0x208100b130482509 0x9040805898241284 0x0000003030000000 0x0000001818000000

def z213 : W := mkw 0x0274cb4a48000000 0x013a65a524000000 0x20788a4c4c000000 0x103c452626000000

def z214 : W := mkw 0x423a7f43eb8182d4 0x211d3fa1f5c0c16a 0xbf787fc3ff8187ff 0xdfbc3fe1ffc0c3ff

def z215 : W := mkw 0x006efe0003b5d000 0x00377f0001dae800 0xd9ff740003796001 0x6cffba0001bcb000

def z216 : W := mkw 0x815d81e802ac0340 0xc0aec0f4015601a0 0x3d7f01c003b807e1 0x9ebf80e001dc03f0

def z217 : W := mkw 0x0046a60000000000 0x0023530000000000 0x4007860000000000 0x2003c30000000000

def z218 : W := mkw 0x208334a1a1194190 0x90419a50d08ca0c8 0x9f07718383390799 0xcf83b8c1c19c83cc

def z219 : W := mkw 0x0247a6a928000000 0x0123d35494000000 0xea078e7c7c000000 0xf503c73e3e000000

def z220 : W := mkw 0x0000100081010090 0x0000080040808048 0x8200700380010018 0x41003801c000800c

def z221 : W := mkw 0x0008100003b5d000 0x0004080001dae800 0x0180000003fff801 0x00c0000001fffc00

def z222 : W := mkw 0x021101eb68000000 0x010880f5b4000000 0x0400018380000000 0x020000c1c0000000

def z223 : W := mkw 0x0000000000000000 0x0000000000000000 0x9e00718380000000 0xcf0038c1c0000000

def z224 : W := mkw 0x006efe0003b5d000 0x00377f0001dae800 0xfbfffe4043fffc7f 0xfdffff2021fffe3f

def z225 : W := mkw 0x937fefff7eee2f6b 0xc9bff7ffbf7717b5 0xffffffffffffffff 0xffffffffffffffff

def z226 : W := mkw 0x106efe1417f7fc2b 0x08377f0a0bfbfe15 0xfbfffe7c7ffffc7f 0xfdffff3e3ffffe3f

def z227 : W := mkw 0x817ffffc03ffd761 0xc0bffffe01ffebb0 0xfdfffffc03ffffe1 0xfefffffe01fffff0

def z228 : W := mkw 0x000100a000000000 0x0000805000000000 0x5c0701b000000000 0xae0380d800000000

def z229 : W := mkw 0x027fefeb6a800240 0x013ff7f5b5400120 0xff7fffffff8007e1 0xffbfffffffc003f0

def z230 : W := mkw 0xa1dfb5f9b3fd67d9 0xd0efdafcd9feb3ec 0xdfff75b3b3796799 0xefffbad9d9bcb3cc

def z231 : W := mkw 0xa1dd91fc93ff67f9 0xd0eec8fe49ffb3fc 0x7dff81fc03ff67f9 0xbeffc0fe01ffb3fc

def z232 : W := mkw 0x0277efeb68000000 0x013bf7f5b4000000 0xfefffffffcc7f801 0xff7ffffffe63fc00

def z233 : W := mkw 0x1008101417f7fc2b 0x0804080a0bfbfe15 0x0180000003fffc7f 0x00c0000001fffe3f

def z234 : W := mkw 0x1030495654422c2b 0x081824ab2a211615 0xfef8fffffcc7fc7f 0xff7c7ffffe63fe3f

def z235 : W := mkw 0x815d81ec02ae0360 0xc0aec0f6015701b0 0x357f81cc03be03e0 0x1abfc0e601df01f0

def z236 : W := mkw 0x427fffebeb8182d4 0x213ffff5f5c0c16a 0xff7fffffff000380 0xffbfffffff8001c0

def z237 : W := mkw 0x208334b1b1596599 0x90419a58d8acb2cc 0x1587718383796799 0x0ac3b8c1c1bcb3cc

def z238 : W := mkw 0x1000001414422c2b 0x0800000a0a211615 0xe8808e0000c7fc7f 0x744047000063fe3f

def z239 : W := mkw 0x40385942c38182d4 0x201c2ca161c0c16a 0xbd78798383818381 0x5ebc3cc1c1c0c1c0

def z240 : W := mkw 0x0000100001010000 0x0000080000808000 0x9900700003010001 0x4c80380001808000

def z241 : W := mkw 0x10227e141553fc2b 0x08113f0a0aa9fe15 0xea80fe7c7cc7fc7f 0xf5407f3e3e63fe3f

def z242 : W := mkw 0x0046b60001355000 0x00235b00009aa800 0xd987f600037f7801 0x6cc3fb0001bfbc00

def z243 : W := mkw 0x006ffea123b5d000 0x0037ff5091dae800 0xffffffb3b3fff801 0xffffffd9d9fffc00

def z244 : W := mkw 0x407dd9eac38182d4 0x203eecf561c0c16a 0xff7ff9ffc38187ff 0xffbffcffe1c0c3ff

def z245 : W := mkw 0x0277efeb68000000 0x013bf7f5b4000000 0x547ff7bfbc000000 0x2a3ffbdfde000000

def z246 : W := mkw 0x0000000080000090 0x0000000040000048 0x0600018380000798 0x830000c1c00003cc

def z247 : W := mkw 0x915d81fc16ee2f6b 0xc8aec0fe0b7717b5 0x7dff81fc03ffffff 0xbeffc0fe01ffffff

def z248 : W := mkw 0x810900b402ee0761 0xc084805a017703b0 0x5d8701b003fe07e1 0xaec380d801ff03f0

def z249 : W := mkw 0x0000000000000000 0x0000000000000000 0x20008a0000869800 0x1000450000434c00

def z250 : W := mkw 0x027eff4a4bb5d000 0x013f7fa525dae800 0xf9fffe4c4ffff801 0x7cffff2627fffc00

def z251 : W := mkw 0x915d81fc06ee0f63 0xc8aec0fe037707b1 0x7dff8bfc4ffe9fe7 0xbeffc5fe27ff4ff3

def z252 : W := mkw 0x006cca0002a49000 0x0036650001524800 0x79ff8a0003fe9801 0x3cffc50001ff4c00

def z253 : W := mkw 0x121101ff7c422c2b 0x090880ffbe211615 0xee808ffffcc7fc7f 0xf74047fffe63fe3f

def z254 : W := mkw 0x1000001414422c2b 0x0800000a0a211615 0xe8808e3c3cc7f801 0x7440471e1e63fc00

def z255 : W := mkw 0x0054814800000000 0x002a40a400000000 0x2078804c00000000 0x103c402600000000

def z256 : W := mkw 0x815c815c02e60661 0x40ae40ae01730330 0x68f8807c00c60461 0xb47c403e00630230

def z257 : W := mkw 0x0000000000000000 0x0000000000000000 0x80000e000001f800 0x400007000000fc00

def z258 : W := mkw 0x40385942c38182d4 0x201c2ca161c0c16a 0xff78ffffff8187ff 0xffbc7fffffc0c3ff

def z259 : W := mkw 0x20823411b1516499 0x10411a08d8a8b24c 0xca807433b0416419 0xe5403a19d820b20c

def z260 : W := mkw 0x0200000368000000 0x01000001b4000000 0x02000003fc000000 0x01000001fe000000

def z261 : W := mkw 0x1000001414422c2b 0x0800000a0a211615 0x0080000000467800 0x0040000000233c00

def z262 : W := mkw 0x0000100081010090 0x0000080040808048 0x0100000003010799 0x00800000018083cc

def z263 : W := mkw 0x0000000000000000 0x0000000000000000 0x1d00018003000781 0x8e8000c0018003c0

def z264 : W := mkw 0x004ea60002b45000 0x00275300015a2800 0x79ff860003fe7801 0x3cffc30001ff3c00

def z265 : W := mkw 0x0277ffeb69114000 0x013bfff5b488a000 0xffffffffff796001 0xffffffffffbcb000

def z266 : W := mkw 0x60bb7df3f3d9e7dd 0xb05dbef9f9ecf3ee 0xffff7df3f3f9e7ff 0xffffbef9f9fcf3ff

def z267 : W := mkw 0x22a27e03f9116098 0x11513f01fc88b04c 0x82007e03fc016018 0x41003f01fe00b00c

def z268 : W := mkw 0x5008101497c3aeff 0x2804080a4be1d77f 0xeb808e7c7fc7ffff 0xf5c0473e3fe3ffff

def z269 : W := mkw 0x22f7ffebe9194190 0x917bfff5f48ca0c8 0xff7fffffff380380 0xffbfffffff9c01c0

def z270 : W := mkw 0x837fefeb6aac0340 0xc1bff7f5b55601a0 0xff7fffffff380380 0xffbfffffff9c01c0

def z271 : W := mkw 0x811101e800080340 0xc08880f4000401a0 0x0400018000000380 0x020000c0000001c0

def z272 : W := mkw 0x100000001400280a 0x080000000a001405 0xea808e007cc7f81f 0x754047003e63fc0f

def z273 : W := mkw 0x0066ee0000000000 0x0033770000000000 0xf8fffe0000c7f801 0x7c7fff000063fc00

def z274 : W := mkw 0x00305942c1010090 0x00182ca160808048 0xbf7879c3c3010799 0xdfbc3ce1e18083cc

def z275 : W := mkw 0x1000001414422c2b 0x0800000a0a211615 0x82000e7c7c01fc7e 0xc100073e3e00fe3f

def z276 : W := mkw 0x70bb7df7f7dbefff 0xb85dbefbfbedf7ff 0xffffffffffffffff 0xffffffffffffffff

def z277 : W := mkw 0x0000101091412499 0x0000080848a0924c 0xdf8075b3b3416799 0xefc03ad9d9a0b3cc

def z278 : W := mkw 0xc17dd9fec3ef87f5 0xe0beecff61f7c3fa 0x7dfff1ff83fe07e1 0xbefff8ffc1ff03f0

def z279 : W := mkw 0x815d81fc02ee0761 0xc0aec0fe017703b0 0xfdff8ffc03ffffe1 0xfeffc7fe01fffff0

def z280 : W := mkw 0x0276ef4a48000000 0x013b77a524000000 0xf87ffe4c4c000000 0x7c3fff2626000000

def z281 : W := mkw 0x0277efeb68000000 0x013bf7f5b4000000 0xbe7f79c3c0000000 0xdf3fbce1e0000000

def z282 : W := mkw 0x20ab7cb1b3d9e599 0x9055be58d9ecf2cc 0xffff7db3b3f9e799 0xffffbed9d9fcf3cc

def z283 : W := mkw 0x0277efeb68000000 0x013bf7f5b4000000 0x607f8e7c7c000000 0x303fc73e3e000000

def z284 : W := mkw 0x308334b5b55b6dbb 0x98419a5adaadb6dd 0xdf8775b3b3ffffff 0xefc3bad9d9ffffff

def z285 : W := mkw 0x22c7b6b9b9596599 0x9163db5cdcacb2cc 0xdf87f7bfbf796799 0xefc3fbdfdfbcb3cc

def z286 : W := mkw 0x0000001010402409 0x0000000808201204 0xca80043030416419 0xe54002181820b20c

def z287 : W := mkw 0x0077efe800000000 0x003bf7f400000000 0xfc7ffffc00000000 0xfe3ffffe00000000

def z288 : W := mkw 0x1247a6bd3c422c2b 0x0923d35e9e211615 0xea878e7c7cc7fc7f 0xf543c73e3e63fe3f

def z289 : W := mkw 0x0000000010002008 0x0000000008001004 0x8200040030016018 0x410002001800b00c

def z290 : W := mkw 0x8144800c00260020 0x40a2400600130010 0x0000800c00060000 0x0000400600030000

def z291 : W := mkw 0x000100a120000000 0x0000805090000000 0x060001b3b0000000 0x830000d9d8000000

def z292 : W := mkw 0x40227e02c111d094 0x20113f016088e84a 0x82007e03c001f81e 0x41003f01e000fc0f

def z293 : W := mkw 0x60bb7df3f3d9e7dd 0xb05dbef9f9ecf3ee 0xdfff75b3b3796799 0xefffbad9d9bcb3cc

def z294 : W := mkw 0x00227e000111d000 0x00113f000088e800 0xe880fe0000c7f801 0x74407f000063fc00

def z295 : W := mkw 0x002a7c000391c000 0x00153e0001c8e000 0xf9ff7c0003f9e001 0x7cffbe0001fcf000

def z296 : W := mkw 0x5038495656c2ae6f 0x281c24ab2b615737 0xeaf88e7c7cc7fc7f 0xf57c473e3e63fe3f

def z297 : W := mkw 0xa1c7a4bd307e6529 0xd0e3d25e983f3294 0x4087843c307e6000 0x2043c21e183f3000

def z298 : W := mkw 0x0066ee0000000000 0x0033770000000000 0x107f700000000000 0x083fb80000000000

def z299 : W := mkw 0x40100142c00002d4 0x200800a16000016a 0x0400018380000380 0x020000c1c00001c0

def z300 : W := mkw 0x000100b000480501 0x8000805800240280 0x4087003000780000 0x20438018003c0000

def z301 : W := mkw 0x1002341415536c2b 0x08011a0a0aa9b615 0xfb87fe7c7ffffc7f 0xfdc3ff3e3ffffe3f

def z302 : W := mkw 0x815fb5fc03ff4761 0xc0afdafe01ffa3b0 0xfdfff5fc03ff67e1 0xfefffafe01ffb3f0

def z303 : W := mkw 0x6088101093d9e7dd 0xb044080849ecf3ee 0x0180000003f9e7ff 0x00c0000001fcf3ff

def z304 : W := mkw 0x60a27c03f111e09c 0x30513e01f888f04e 0x82007c03f001e01e 0x41003e01f800f00f

def z305 : W := mkw 0x0274cb4a48000000 0x013a65a524000000 0xea788e7c7c000000 0xf53c473e3e000000

def z306 : W := mkw 0x60b85952d3d9e7dd 0xb05c2ca969ecf3ee 0xbff879c3c3f9e7ff 0xdffc3ce1e1fcf3ff

def z307 : W := mkw 0x815c814c02a60260 0x40ae40a601530130 0x3d7881cc038607e1 0x9ebc40e601c303f0

def z308 : W := mkw 0xa1dfb5e9a3bd43d0 0xd0efdaf4d1dea1e8 0x157f718383380380 0x0abfb8c1c19c01c0

def z309 : W := mkw 0x0000000000000000 0x0000000000000000 0x6880800000c60001 0x3440400000630000

def z310 : W := mkw 0x0066ee0000000000 0x0033770000000000 0xfa7ffe7c7c000000 0xfd3fff3e3e000000

def z311 : W := mkw 0x814580a8002c0100 0xc0a2c05400160080 0x0007000000380000 0x00038000001c0000

def z312 : W := mkw 0x20effeb1b3fdf599 0x9077ff58d9fefacc 0xdfff75b3b3796799 0xefffbad9d9bcb3cc

def z313 : W := mkw 0x0002340081114090 0x00011a004088a048 0xdf87758383796799 0xefc3bac1c1bcb3cc

def z314 : W := mkw 0x814d80bc02ee0521 0xc0a6c05e01770290 0x79ff803c03fe0001 0x3cffc01e01ff0000

def z315 : W := mkw 0xd17dd9fed7efafff 0xe8beecff6bf7d7ff 0xffffffffffffffff 0xffffffffffffffff

def z316 : W := mkw 0x0000000000000000 0x0000000000000000 0xc880040000416001 0x644002000020b000

def z317 : W := mkw 0x00227e000111d000 0x00113f000088e800 0x0000700000000000 0x0000380000000000

def z318 : W := mkw 0x817fffe803bdd340 0xc0bffff401dee9a0 0x157f718003380380 0x0abfb8c0019c01c0

def z319 : W := mkw 0x9108001416ee2f6b 0xc884000a0b7717b5 0x0180000003ffffff 0x00c0000001ffffff

def z320 : W := mkw 0x8108000002ac0340 0xc0840000015601a0 0x0100000003380380 0x00800000019c01c0

def z321 : W := mkw 0x006efe0003b5d000 0x00377f0001dae800 0xf97ffe0003380000 0x7cbfff00019c0000

def z322 : W := mkw 0x308100b5b44a2dbb 0x9840805ada2516dd 0x060001fffc0007fe 0x830000fffe0003ff

def z323 : W := mkw 0x0002340001114000 0x00011a000088a000 0xf987fe0003fff801 0x7cc3ff0001fffc00

def z324 : W := mkw 0x208334b131596509 0x90419a5898acb284 0xd987743033796001 0x6cc3ba1819bcb000

def z325 : W := mkw 0x40100142c00002d4 0x200800a16000016a 0xae0009c3c08187ff 0xd70004e1e040c3ff

def z326 : W := mkw 0x026efe036bb5d000 0x01377f01b5dae800 0xfbfffe03fffff801 0x7dffff01fffffc00

def z327 : W := mkw 0x811101fc004a0761 0xc08880fe002503b0 0x5d8701fc037807e1 0xaec380fe01bc03f0

def z328 : W := mkw 0x208100b1b0482599 0x90408058d82412cc 0xce8005b3b0416799 0xe74002d9d820b3cc

def z329 : W := mkw 0x40081000838182d4 0x2004080041c0c16a 0x0100000003000380 0x00800000018001c0

def z330 : W := mkw 0x815d81fc12ee2769 0xc0aec0fe097713b4 0xffff85fc33ff67f9 0xffffc2fe19ffb3fc

def z331 : W := mkw 0x0275cbea48000000 0x013ae5f524000000 0x7c7f8bfc4c000000 0xbe3fc5fe26000000

def z332 : W := mkw 0x0000001010402409 0x0000000808201204 0xea808e7c7c416419 0xf540473e3e20b20c

def z333 : W := mkw 0x0002340001114000 0x00011a000088a000 0x1107700003380000 0x0883b800019c0000

def z334 : W := mkw 0x0277effb78402409 0x013bf7fdbc201204 0xfefffffffc416419 0xff7ffffffe20b20c

def z335 : W := mkw 0x0044800000000000 0x0022400000000000 0x787f800000000000 0x3c3fc00000000000

def z336 : W := mkw 0x60ba7d43f391e2dc 0x305d3ea1f9c8f16e 0xbf787dc3f381e7ff 0xdfbc3ee1f9c0f3ff

def z337 : W := mkw 0x40101142c10102d4 0x200808a16080816a 0x9f0071c3c30107ff 0xcf8038e1e18083ff

def z338 : W := mkw 0xa1dd81fdb2ee27f9 0xd0eec0fed97713fc 0x7fff81ffb3fe07f9 0xbfffc0ffd9ff03fc

def z339 : W := mkw 0x208110b091596599 0x9040885848acb2cc 0x5d8701b003796799 0xaec380d801bcb3cc

def z340 : W := mkw 0x40385942c38182d4 0x201c2ca161c0c16a 0xa2787843c081807e 0x513c3c21e040c03f

def z341 : W := mkw 0x40180142c28002d4 0x200c00a16140016a 0x3f7801c3c38007ff 0x9fbc00e1e1c003ff

def z342 : W := mkw 0x815c815c02ee0761 0xc0ae40ae017703b0 0x21f8804c03fe07e1 0x10fc402601ff03f0

def z343 : W := mkw 0x817eff4c03b7d260 0x40bf7fa601dbe930 0xf9fffe4c03fff861 0x7cffff2601fffc30

def z344 : W := mkw 0x1000001414422c2b 0x0800000a0a211615 0xca80047c7c41647f 0xe540023e3e20b23f

def z345 : W := mkw 0x407eff42c3b5d2d4 0x203f7fa161dae96a 0x157f718383380380 0x0abfb8c1c19c01c0

def z346 : W := mkw 0x0038594003818240 0x001c2ca001c0c120 0xbd7879c0038187e1 0xdebc3ce001c0c3f0

def z347 : W := mkw 0x0202260128000000 0x0101130094000000 0x000006003c000000 0x000003001e000000

def z348 : W := mkw 0x407eff4243b5d244 0x203f7fa121dae922 0xf9fffe4043fff867 0x7cffff2021fffc33

def z349 : W := mkw 0x30823415b5536cbb 0x18411a0adaa9b65d 0xea80fe7ffcc7fc7f 0xf5407f3ffe63fe3f

def z350 : W := mkw 0x0000100001114000 0x000008000088a000 0x0180000003796001 0x00c0000001bcb000

def z351 : W := mkw 0x208110b1b1492599 0x90408858d8a492cc 0x9f0071b3b3010799 0xcf8038d9d98083cc

def z352 : W := mkw 0x0277efeb68000000 0x013bf7f5b4000000 0x7c7ff1ff80000000 0xbe3ff8ffc0000000

def z353 : W := mkw 0x0277ffebe9010090 0x013bfff5f4808048 0xff7fffffff010799 0xffbfffffff8083cc

def z354 : W := mkw 0x000334a121114000 0x00019a509088a000 0xdf8775b3b3796001 0xefc3bad9d9bcb000

def z355 : W := mkw 0x40385942c3b5d2d4 0x201c2ca161dae96a 0xbff879c3c3ffffff 0xdffc3ce1e1ffffff

def z356 : W := mkw 0x407cd942c3a582d4 0x203e6ca161d2c16a 0xfffff9c3c3ff87ff 0xfffffce1e1ffc3ff

def z357 : W := mkw 0x50100156d4422eff 0x280800ab6a21177f 0x060001fffc0007fe 0x830000fffe0003ff

def z358 : W := mkw 0x40305942c10182d4 0x20182ca16080c16a 0x860079c3c00187fe 0xc3003ce1e000c3ff

def z359 : W := mkw 0x40081000838182d4 0x2004080041c0c16a 0xab000840438187ff 0xd580042021c0c3ff

def z360 : W := mkw 0x40205802c1018094 0x20102c016080c04a 0x0000700380000000 0x00003801c0000000

def z361 : W := mkw 0x40384942c28082d4 0x201c24a16140416a 0x267809c3c08087fe 0x933c04e1e04043ff

def z362 : W := mkw 0x1000001414422c2b 0x0800000a0a211615 0x4280867c7c467c7e 0xa140433e3e233e3f

def z363 : W := mkw 0x005c814002a40240 0x002e40a001520120 0x7dff81c003fe07e1 0xbeffc0e001ff03f0

def z364 : W := mkw 0x50385942d781aade 0x281c2ca16bc0d56f 0xbf787fc3ff81ffff 0xdfbc3fe1ffc0ffff

def z365 : W := mkw 0x12226e037c00280a 0x09113701be001405 0x82007e03fc01f81e 0x41003f01fe00fc0f

def z366 : W := mkw 0x0002240120000000 0x0001120090000000 0x82007403b0000000 0x41003a01d8000000

def z367 : W := mkw 0x1000001414422c2b 0x0800000a0a211615 0x6880807c00c7fc7f 0xb440403e0063fe3f

def z368 : W := mkw 0x0277efff68420421 0x013bf7ffb4210210 0xfefffffffcc60461 0xff7ffffffe630230

def z369 : W := mkw 0x0000000000345000 0x00000000001a2800 0x00800000007e7800 0x00400000003f3c00

def z370 : W := mkw 0x021101eb68000000 0x010880f5b4000000 0xee008ffffc000000 0xf70047fffe000000

def z371 : W := mkw 0x208334b1b1596599 0x90419a58d8acb2cc 0xff87ffffff796799 0xffc3ffffffbcb3cc

def z372 : W := mkw 0x1000001414422c2b 0x0800000a0a211615 0x4080863c3cc7fc7f 0x2040431e1e63fe3f

def z373 : W := mkw 0x00226e0000000000 0x0011370000000000 0x80007e0000000000 0x40003f0000000000

def z374 : W := mkw 0x1000001414422c2b 0x0800000a0a211615 0xea008e7c7c00047e 0xf500473e3e00023f

def z375 : W := mkw 0x208334b1b1596599 0x90419a58d8acb2cc 0xff87ffb3b3ffff99 0xffc3ffd9d9ffffcc

def z376 : W := mkw 0x40385942c38182d4 0x201c2ca161c0c16a 0xbf7879c3c3000380 0xdfbc3ce1e18001c0

def z377 : W := mkw 0x22fffffbfbfdf599 0x917ffffdfdfefacc 0xffffffffffffff99 0xffffffffffffffcc

def z378 : W := mkw 0x006efe0003b5d000 0x00377f0001dae800 0xa078fe000087f800 0x503c7f000043fc00

def z379 : W := mkw 0x20effea1a3bdd190 0x9077ff50d1dee8c8 0x157f718383380380 0x0abfb8c1c19c01c0

def z380 : W := mkw 0x0030494240000000 0x001824a120000000 0x2078084040000000 0x103c042020000000

def z381 : W := mkw 0x1277efef6c020822 0x093bf7f7b6010411 0xfe7ffffffc869866 0xff3ffffffe434c33

def z382 : W := mkw 0x005581e800000000 0x002ac0f400000000 0x147f018000000000 0x0a3f80c000000000

def z383 : W := mkw 0x0076ef4240000000 0x003b77a120000000 0xfe7fffc3c0000000 0xff3fffe1e0000000

def z384 : W := mkw 0xc15d81fec2ee07f5 0xe0aec0ff617703fa 0x7fff81ffc3fe07ff 0xbfffc0ffe1ff03ff

def z385 : W := mkw 0x0000001010402409 0x0000000808201204 0x4080043030406000 0x2040021818203000

def z386 : W := mkw 0x02236ea368000000 0x0111b751b4000000 0xde077fb3fc000000 0xef03bfd9fe000000

def z387 : W := mkw 0x40385942c38182d4 0x201c2ca161c0c16a 0x177871c3c30007fe 0x8bbc38e1e18003ff

def z388 : W := mkw 0x427cdb4acb8182d4 0x213e6da565c0c16a 0xbf78fbcfcf8187ff 0xdfbc7de7e7c0c3ff

def z389 : W := mkw 0x0000001400420421 0x0000000a00210210 0xea808e7c7cc60461 0xf540473e3e630230

def z390 : W := mkw 0x815d81f802ec0741 0xc0aec0fc017603a0 0x5dff01b003780781 0xaeff80d801bc03c0

def z391 : W := mkw 0x0000001010402409 0x0000000808201204 0xea800c7070c1e47f 0xf54006383860f23f

def z392 : W := mkw 0x0276ef4b68000000 0x013b77a5b4000000 0xa278fe4ffc000000 0x513c7f27fe000000

def z393 : W := mkw 0x30effeb5b7fffdbb 0x9877ff5adbfffedd 0xffffffffffffffff 0xffffffffffffffff

def z394 : W := mkw 0x0267eeab68000000 0x0133f755b4000000 0xc207fe3ffc000000 0x6103ff1ffe000000

def z395 : W := mkw 0x60a37cb3f159e59d 0xb051be59f8acf2ce 0xdf877db3f379e79f 0xefc3bed9f9bcf3cf

def z396 : W := mkw 0x000010000111d000 0x000008000088e800 0x000000000001f800 0x000000000000fc00

def z397 : W := mkw 0x1046a61414767c2b 0x0823530a0a3b3e15 0x4087863c3c7e7800 0x2043c31e1e3f3c00

def z398 : W := mkw 0x004c800002a40000 0x0026400001520000 0x2078800000860000 0x103c400000430000

def z399 : W := mkw 0x308100b5b44a2dbb 0x9840805ada2516dd 0xee808ffffcc7ffff 0xf74047fffe63ffff

def z400 : W := mkw 0x023149eb68000000 0x0118a4f5b4000000 0xbe7879fffc000000 0xdf3c3cfffe000000

def z401 : W := mkw 0x025581eb68000000 0x012ac0f5b4000000 0x7e7f81fffc000000 0xbf3fc0fffe000000

def z402 : W := mkw 0x837ccb4e4aa60260 0x41be65a725530130 0x20788a4c4c860060 0x103c452626430030

def z403 : W := mkw 0x106efe0017b5f80a 0x08377f000bdafc05 0xfbfffe007ffff81f 0x7dffff003ffffc0f

def z404 : W := mkw 0x006efe1013f5f409 0x00377f0809fafa04 0xfbfffe3033fffc19 0xfdffff1819fffe0c

def z405 : W := mkw 0x4038494242808244 0x201c24a121404122 0x0078000000000000 0x003c000000000000

def z406 : W := mkw 0x0066ee0000345000 0x00337700001a2800 0xf8fffe00007e7800 0x7c7fff00003f3c00

def z407 : W := mkw 0xc1385956c3ef87f5 0xe09c2cab61f7c3fa 0xbff879c3c3ff87ff 0xdffc3ce1e1ffc3ff

def z408 : W := mkw 0x027fffeb6bb5d000 0x013ffff5b5dae800 0xfdffff8383fff801 0x7effffc1c1fffc00

def z409 : W := mkw 0x208334a1b1196198 0x90419a50d88cb0cc 0x97077583b3396398 0x4b83bac1d99cb1cc

def z410 : W := mkw 0x915c815c16e62e6b 0x48ae40ae0b731735 0xeaf88e7c7cc7fc7f 0xf57c473e3e63fe3f

def z411 : W := mkw 0xc13959fec3cb87f5 0xe09cacff61e5c3fa 0xbf7879ffc38187ff 0xdfbc3cffe1c0c3ff

def z412 : W := mkw 0x22f7ffebf9116098 0x117bfff5fc88b04c 0xfe7ffffffc016018 0xff3ffffffe00b00c

def z413 : W := mkw 0x0244820808000000 0x0122410404000000 0x0000820c0c000000 0x0000410606000000

def z414 : W := mkw 0x208334b1b1596599 0x90419a58d8acb2cc 0x558775b3b3786380 0x2ac3bad9d9bc31c0

def z415 : W := mkw 0x0000001400420421 0x0000000a00210210 0xe8808e7c00c7fc61 0xf440473e0063fe30

def z416 : W := mkw 0x0002240000104000 0x0001120000082000 0x4087040000786000 0x20438200003c3000

def z417 : W := mkw 0x815fa5fd22ee0761 0xc0afd2fe917703b0 0xfffff5ffb3fe07e1 0xfffffaffd9ff03f0

def z418 : W := mkw 0xc37fffffebef87f5 0xe1bffffff5f7c3fa 0xffffffffffff87ff 0xffffffffffffc3ff

def z419 : W := mkw 0x1000000004000802 0x0800000002000401 0x00000a004c009806 0x0000050026004c03

def z420 : W := mkw 0x106efe1417f7fc2b 0x08377f0a0bfbfe15 0xf9fffe0003fffc7f 0x7cffff0001fffe3f

def z421 : W := mkw 0x0277efeb68000000 0x013bf7f5b4000000 0x347ffbcfcc000000 0x1a3ffde7e6000000

def z422 : W := mkw 0x0064ca0000000000 0x0032650000000000 0x20788a0000000000 0x103c450000000000

def z423 : W := mkw 0x1000000404020822 0x0800000202010411 0xaa008a4c4c879c7f 0xd50045262643ce3f

def z424 : W := mkw 0x0067eea120000000 0x0033f75090000000 0xfe7fffb3b0000000 0xff3fffd9d8000000

def z425 : W := mkw 0x0000001010402409 0x0000000808201204 0xea808e3030c7fc19 0xf54047181863fe0c

def z426 : W := mkw 0x815581fc006e0761 0xc0aac0fe003703b0 0x448781fc007e07e0 0xa243c0fe003f03f0

def z427 : W := mkw 0x1000001414422c2b 0x0800000a0a211615 0xca80863c3c477c19 0xe540431e1e23be0c

def z428 : W := mkw 0x0000000000000000 0x0000000000000000 0x4080860000467800 0x2040430000233c00

def z429 : W := mkw 0x20823411b1596599 0x90411a08d8acb2cc 0x83807403b3796799 0x41c03a01d9bcb3cc

def z430 : W := mkw 0x40285802c38182d4 0x20142c0161c0c16a 0x83007803c38187ff 0x41803c01e1c0c3ff

def z431 : W := mkw 0x0000000000000000 0x0000000000000000 0xea808e4040c7fc7f 0xf54047202063fe3f

def z432 : W := mkw 0x0274cb4a48000000 0x013a65a524000000 0xbe78fbcfcc000000 0xdf3c7de7e6000000

def z433 : W := mkw 0x1000001414422c2b 0x0800000a0a211615 0x6880867c3cc67c61 0xb440433e1e633e30

def z434 : W := mkw 0x0275cbeb68000000 0x013ae5f5b4000000 0x26788bfffc000000 0x933c45fffe000000

def z435 : W := mkw 0x837fefeb6aac0340 0xc1bff7f5b55601a0 0x157f718383380380 0x0abfb8c1c19c01c0

def z436 : W := mkw 0x208334b1b1596599 0x90419a58d8acb2cc 0xff877df3f3f9e7ff 0xffc3bef9f9fcf3ff

def z437 : W := mkw 0x914580bc146e2d2b 0xc8a2c05e0a371695 0xea878e7c7cfffc7f 0xf543c73e3e7ffe3f

def z438 : W := mkw 0x004c800002a40000 0x0026400001520000 0x117f000003380000 0x08bf8000019c0000

def z439 : W := mkw 0x0000001410422429 0x0000000a08211214 0xea80847c30c76479 0xf540423e1863b23c

def z440 : W := mkw 0x208334b1b1596599 0x90419a58d8acb2cc 0xc2877433b0796018 0x6143ba19d83cb00c

def z441 : W := mkw 0x006cd80003a58000 0x00366c0001d2c000 0xf9fff80003ff8001 0x7cfffc0001ffc000

def z442 : W := mkw 0x2080100091116098 0x104008004888b04c 0x0000000000016018 0x000000000000b00c

def z443 : W := mkw 0x0038494242800240 0x001c24a121400120 0xbf7879c3c38007e1 0xdfbc3ce1e1c003f0

def z444 : W := mkw 0x002a7e000391d000 0x00153f0001c8e800 0xb9787e000381f801 0x5cbc3f0001c0fc00

def z445 : W := mkw 0x0000000000000000 0x0000000000000000 0xaa00084040000000 0xd500042020000000

def z446 : W := mkw 0x308324b5345a6d2b 0x9841925a9a2d3695 0x4087863c3c7e7800 0x2043c31e1e3f3c00

def z447 : W := mkw 0x423959ebeb8182d4 0x211cacf5f5c0c16a 0xbf7879ffff8187ff 0xdfbc3cffffc0c3ff

def z448 : W := mkw 0x427ccb4a4a808244 0x213e65a525404122 0x20788a4c4c808066 0x103c452626404033

def z449 : W := mkw 0x0057a5e920000000 0x002bd2f490000000 0xfe7ff5ffb0000000 0xff3ffaffd8000000

def z450 : W := mkw 0x811101fc004a0761 0xc08880fe002503b0 0x6c8081fc00c607e1 0xb64040fe006303f0

def z451 : W := mkw 0x0000000000000000 0x0000000000000000 0x020000404000047e 0x810000202000023f

def z452 : W := mkw 0x40385942c38182d4 0x201c2ca161c0c16a 0x357879c3c38083e6 0x1abc3ce1e1c041f3

def z453 : W := mkw 0x004eb40003b54000 0x00275a0001daa000 0xf9fff40003ff6001 0x7cfffa0001ffb000

def z454 : W := mkw 0x1066ee1414422c2b 0x0833770a0a211615 0xfafffe7c7cc7fc7f 0xfd7fff3e3e63fe3f

def z455 : W := mkw 0x0008000002800000 0x0004000001400000 0x3978000003800001 0x1cbc000001c00000

def z456 : W := mkw 0x527fffffffc3aeff 0x293fffffffe1d77f 0xffffffffffc7ffff 0xffffffffffe3ffff

def z457 : W := mkw 0x000334a1a1010090 0x00019a50d0808048 0xdf0775b3b3010799 0xef83bad9d98083cc

def z458 : W := mkw 0x208324b130586509 0x90419258982c3284 0xde8775b3b0786000 0xef43bad9d83c3000

def z459 : W := mkw 0x0277ffeb6911d000 0x013bfff5b488e800 0xfe7ffffffc01f800 0xff3ffffffe00fc00

def z460 : W := mkw 0xa19335fdb15b67f9 0xd0c99afed8adb3fc 0xdf8775ffb37967f9 0xefc3baffd9bcb3fc

def z461 : W := mkw 0x0000001400420421 0x0000000a00210210 0x4080803c00460000 0x2040401e00230000

def z462 : W := mkw 0xa1fffffdb3fff7f9 0xd0fffffed9fffbfc 0xffffffffb3fffff9 0xffffffffd9fffffc

def z463 : W := mkw 0x0000001400420421 0x0000000a00210210 0xea80887c40c7847f 0xf540443e2063c23f

def z464 : W := mkw 0x0000000000000000 0x0000000000000000 0x2800004000800461 0x9400002000400230

def z465 : W := mkw 0x817feffc02ee0761 0xc0bff7fe017703b0 0xfdfffffc03fe07e1 0xfefffffe01ff03f0

def z466 : W := mkw 0x407eff42c3b5d2d4 0x203f7fa161dae96a 0xbf7f79c3c3b987ff 0xdfbfbce1e1dcc3ff

def z467 : W := mkw 0x0277efeb68000000 0x013bf7f5b4000000 0xfe7ffffffc81847f 0xff3ffffffe40c23f

def z468 : W := mkw 0x000100b000480501 0x8000805800240280 0x040001b000000780 0x820000d8000003c0

def z469 : W := mkw 0x4008100083b5d2d4 0x2004080041dae96a 0x0180000003ffffff 0x00c0000001ffffff

def z470 : W := mkw 0x121101ff7c422c2b 0x090880ffbe211615 0x060001fffc00047e 0x830000fffe00023f

def z471 : W := mkw 0x308324b5345a6d2b 0x9841925a9a2d3695 0xea878e7c7cfffc7f 0xf543c73e3e7ffe3f

def z472 : W := mkw 0x0257a7e928000000 0x012bd3f494000000 0x7c7f87fc3c000000 0xbe3fc3fe1e000000

def z473 : W := mkw 0x0066fe0001114000 0x00337f000088a000 0xf9fffe0003796001 0x7cffff0001bcb000

def z474 : W := mkw 0x22a37eb3f9596599 0x9151bf59fcacb2cc 0xdf877fb3ff796799 0xefc3bfd9ffbcb3cc

def z475 : W := mkw 0x5008101497c3aeff 0x2804080a4be1d77f 0x0180000003c7ffff 0x00c0000001e3ffff

def z476 : W := mkw 0x814580bc006e0521 0xc0a2c05e00370290 0x6887807c00fe0461 0xb443c03e007f0230

def z477 : W := mkw 0x0002240000000000 0x0001120000000000 0xd807740000000000 0x6c03ba0000000000

def z478 : W := mkw 0x815d81fc02ee0761 0xc0aec0fe017703b0 0x157f01fc033807e0 0x8abf80fe019c03f0

def z479 : W := mkw 0x027ccb4a4aa49000 0x013e65a525524800 0x20788a4c4c869800 0x103c452626434c00

def z480 : W := mkw 0xa188101493ff67f9 0xd0c4080a49ffb3fc 0x0180000003ff67f9 0x00c0000001ffb3fc

def z481 : W := mkw 0x1000001414422c2b 0x0800000a0a211615 0xaa80084040c7fc7f 0xd54004202063fe3f

def z482 : W := mkw 0x0010014000000000 0x000800a000000000 0x3c7801c000000000 0x9e3c00e000000000

def z483 : W := mkw 0x0018014002800240 0x000c00a001400120 0xbf7809c0438187ff 0xdfbc04e021c0c3ff

def z484 : W := mkw 0x0020480000000000 0x0010240000000000 0xb878780000000000 0x5c3c3c0000000000

def z485 : W := mkw 0x915d81fc16ee2f6b 0xc8aec0fe0b7717b5 0x7fff81fc7ffe07ff 0xbfffc0fe3fff03ff

def z486 : W := mkw 0x60bb7de3e399c3d4 0xb05dbef1f1cce1ea 0xbf7f79c3c3b987ff 0xdfbfbce1e1dcc3ff

def z487 : W := mkw 0x60b959f3f3c9a7dd 0xb05cacf9f9e4d3ee 0xbf7879f3f38187ff 0xdfbc3cf9f9c0c3ff

def z488 : W := mkw 0xc17ffffec3ffd7f5 0xe0bfffff61ffebfa 0xffffffffc3ffffff 0xffffffffe1ffffff

def z489 : W := mkw 0x810100bc004a0521 0xc080805e00250290 0x0000003c00000000 0x0000001e00000000

def z490 : W := mkw 0x0247a6a928345000 0x0123d354941a2800 0x4087863c3c7e7800 0x2043c31e1e3f3c00

def z491 : W := mkw 0x0008100003818000 0x0004080001c0c000 0x0100000003818001 0x0080000001c0c000

def z492 : W := mkw 0x1000000404020822 0x0800000202010411 0xe8808e4c4cc7f867 0x744047262663fc33

def z493 : W := mkw 0x004eb60003b5d000 0x00275b0001dae800 0x4187860003fff801 0x20c3c30001fffc00

def z494 : W := mkw 0x831101ff684a0761 0xc18880ffb42503b0 0x060001fffc0007e0 0x830000fffe0003f0

def z495 : W := mkw 0x208334b1b1596599 0x90419a58d8acb2cc 0x860075b3b0016798 0xc3003ad9d800b3cc

def z496 : W := mkw 0x30801014955b6dbb 0x9840080a4aadb6dd 0x0180000003ffffff 0x00c0000001ffffff

def z497 : W := mkw 0x4038594243818244 0x201c2ca121c0c122 0xb978784043818067 0x5cbc3c2021c0c033

def z498 : W := mkw 0x22c7a6b938586509 0x9163d35c9c2c3284 0x4087863c3c786000 0x2043c31e1e3c3000

def z499 : W := mkw 0x811901fc02ca0761 0xc08c80fe016503b0 0x3d7801fc038007e1 0x9ebc00fe01c003f0

def z500 : W := mkw 0x005d81e802800240 0x002ec0f401400120 0x7d7f81fc038007e1 0xbebfc0fe01c003f0

def z501 : W := mkw 0x0277efeb68000000 0x013bf7f5b4000000 0xde7f75b3b0000000 0xef3fbad9d8000000

def z502 : W := mkw 0x0038594243818000 0x001c2ca121c0c000 0xbf7879c3c3818001 0xdfbc3ce1e1c0c000

def z503 : W := mkw 0x1247a6bd3c422c2b 0x0923d35e9e211615 0x4087863c3c467800 0x2043c31e1e233c00

def z504 : W := mkw 0x0066fe000111d000 0x00337f000088e800 0xf87ffe000001f800 0x7c3fff000000fc00

def z505 : W := mkw 0x106efe1417f7fc2b 0x08377f0a0bfbfe15 0xf9fffe3c3ffff801 0x7cffff1e1ffffc00

def z506 : W := mkw 0x007eff4003b5d240 0x003f7fa001dae920 0xfdffffc003ffffe1 0xfeffffe001fffff0

def z507 : W := mkw 0x0008000002a49000 0x0004000001524800 0x0000000000869800 0x0000000000434c00

def z508 : W := mkw 0x20d7b5f9b1596599 0x906bdafcd8acb2cc 0xfffff5ffb3796799 0xfffffaffd9bcb3cc

def z509 : W := mkw 0x20c7b6b1b17d7599 0x9063db58d8bebacc 0xdf87f7b3b37f7f99 0xefc3fbd9d9bfbfcc

def z510 : W := mkw 0xa1dfb5fda3ff47f1 0xd0efdafed1ffa3f8 0x7dfff1ff83fe07e1 0xbefff8ffc1ff03f0

def z511 : W := mkw 0x208334b5b15b65b9 0x90419a5ad8adb2dc 0xff87f5ffb3ff67f9 0xffc3faffd9ffb3fc

def z512 : W := mkw 0x50205816d543acbf 0x28102c0b6aa1d65f 0xea80fe7ffcc7fc7f 0xf5407f3ffe63fe3f

def z513 : W := mkw 0xe1fffdfff3ffe7fd 0xf0fffefff9fff3fe 0xfffffdfff3ffe7ff 0xfffffefff9fff3ff

def z514 : W := mkw 0x027fffeb6bb5d000 0x013ffff5b5dae800 0xff7fffffff380000 0xffbfffffff9c0000

def z515 : W := mkw 0x4038494242808244 0x201c24a121404122 0x3d7809c0438087e7 0x9ebc04e021c043f3

def z516 : W := mkw 0x427fffebebb5d2d4 0x213ffff5f5dae96a 0xffffffffffffffff 0xffffffffffffffff

def z517 : W := mkw 0xc17cd94ec3a782f4 0x60be6ca761d3c17a 0xbf78f9cfc38787ff 0xdfbc7ce7e1c3c3ff

def z518 : W := mkw 0x817dc9fe42ee0761 0xc0bee4ff217703b0 0xfffff9ffc3fe07e1 0xfffffcffe1ff03f0

def z519 : W := mkw 0x007eff4243b5d000 0x003f7fa121dae800 0xffffffc3c3fff801 0xffffffe1e1fffc00

def z520 : W := mkw 0x814580bc006e0521 0xc0a2c05e00370290 0x5d8781bc037e0781 0xaec3c0de01bf03c0

def z521 : W := mkw 0x815d81fc02ee0761 0xc0aec0fe017703b0 0x55ff81bc037e0380 0x2affc0de01bf01c0

def z522 : W := mkw 0x1274cb4e4c020822 0x093a65a726010411 0x20788a4c4c869866 0x103c452626434c33

def z523 : W := mkw 0x00204a0000009000 0x0010250000004800 0x00000a0000009800 0x0000050000004c00

def z524 : W := mkw 0x815d91fc83ef07f1 0xc0aec8fe41f783f8 0xfffff1ff83ff07f9 0xfffff8ffc1ff83fc

def z525 : W := mkw 0x40385956c3c386f5 0x201c2cab61e1c37a 0xfff8f9ffc3c787ff 0xfffc7cffe1e3c3ff

def z526 : W := mkw 0x22f7effb78586509 0x917bf7fdbc2c3284 0xfefffffffc786000 0xff7ffffffe3c3000

def z527 : W := mkw 0x816ffebc03ffd521 0xc0b7ff5e01ffea90 0xf9fffe3c03fff801 0x7cffff1e01fffc00

def z528 : W := mkw 0x208324b1b0482599 0x90419258d82412cc 0xde0775b3b0000798 0xef03bad9d80003cc

def z529 : W := mkw 0x0000000000000000 0x0000000000000000 0x6800807c00000000 0xb400403e00000000

def z530 : W := mkw 0x50385946c7838af6 0x281c2ca363c1c57b 0xbf78fbcfcf879fff 0xdfbc7de7e7c3cfff

def z531 : W := mkw 0x00181140838102d0 0x000c08a041c08168 0xbf7871c3838107f9 0xdfbc38e1c1c083fc

def z532 : W := mkw 0x0044800000240000 0x0022400000120000 0x40878000007e0000 0x2043c000003f0000

def z533 : W := mkw 0x000324a120000000 0x0001925090000000 0x4007043030000000 0x2003821818000000

def z534 : W := mkw 0x100100b4144a2d2b 0x8800805a0a251695 0xff878ffc7fffffff 0xffc3c7fe3fffffff

def z535 : W := mkw 0x0002260000105000 0x0001130000082800 0x0000060000007800 0x0000030000003c00

def z536 : W := mkw 0x0000000000000000 0x0000000000000000 0x8a00000000010419 0xc50000000000820c

def z537 : W := mkw 0x407eff42c3b5d2d4 0x203f7fa161dae96a 0xfdffff8383fffb81 0x7effffc1c1fffdc0

def z538 : W := mkw 0x0277efeb68000000 0x013bf7f5b4000000 0xfc7fff8380000000 0x7e3fffc1c0000000

def z539 : W := mkw 0x127fffff7ff7fc2b 0x093fffffbffbfe15 0xfffffffffffffc7f 0xfffffffffffffe3f

def z540 : W := mkw 0x005d81e802a40000 0x002ec0f401520000 0x7dff81fc03fe0001 0xbeffc0fe01ff0000

def z541 : W := mkw 0x4010014240000244 0x200800a120000122 0x0000004040000066 0x0000002020000033

def z542 : W := mkw 0x817dcbfc02ee9761 0xc0bee5fe01774bb0 0x7dff8bfc03fe9fe1 0xbeffc5fe01ff4ff0

def z543 : W := mkw 0x403959f2c3c987d5 0xa01cacf961e4c3ea 0xffff79f3c3f987ff 0xffffbcf9e1fcc3ff

def z544 : W := mkw 0x02326f4368000000 0x011937a1b4000000 0xbe787fc3fc000000 0xdf3c3fe1fe000000

def z545 : W := mkw 0x10227e001511f80a 0x08113f000a88fc05 0x82007e007c01f81e 0x41003f003e00fc0f

def z546 : W := mkw 0x50100156d4422eff 0x280800ab6a21177f 0xee808ffffcc7ffff 0xf74047fffe63ffff

def z547 : W := mkw 0x00336de360000000 0x0019b6f1b0000000 0xfe7f7df3f0000000 0xff3fbef9f8000000

def z548 : W := mkw 0x006efe0003b5d000 0x00377f0001dae800 0xb97f780003b98001 0x5cbfbc0001dcc000

def z549 : W := mkw 0x0277efeb68000000 0x013bf7f5b4000000 0x967f7f83fc000000 0x4b3fbfc1fe000000

def z550 : W := mkw 0x1000001414422c2b 0x0800000a0a211615 0x000000000000047e 0x000000000000023f

def z551 : W := mkw 0x0247a6a928000000 0x0123d35494000000 0xde07f7bfbc000000 0xef03fbdfde000000

def z552 : W := mkw 0x817ffffc03ffd761 0xc0bffffe01ffebb0 0x7dfff1fc03fe07e1 0xbefff8fe01ff03f0

def z553 : W := mkw 0x60fffff3f3fdf7dd 0xb07ffff9f9fefbee 0xfffffff3f3ffffff 0xfffffff9f9ffffff

def z554 : W := mkw 0x8147a6bc007e5521 0xc0a3d35e003f2a90 0x4087863c007e7800 0x2043c31e003f3c00

def z555 : W := mkw 0x8377efff686e0521 0xc1bbf7ffb4370290 0xfefffffffc7e0000 0xff7ffffffe3f0000

def z556 : W := mkw 0x1277efeb7c00280a 0x093bf7f5be001405 0xfe7ffffffc01f81e 0xff3ffffffe00fc0f

def z557 : W := mkw 0x20eefe01b3b5f098 0x10777f00d9daf84c 0xfbfffe03b3fff819 0x7dffff01d9fffc0c

def z558 : W := mkw 0x006cda0003a59000 0x00366d0001d2c800 0xb978fa0003879801 0x5cbc7d0001c3cc00

def z559 : W := mkw 0x814c801402ee0761 0xc0a6400a017703b0 0x79ff800003fe07e1 0x3cffc00001ff03f0

def z560 : W := mkw 0x1000001414422c2b 0x0800000a0a211615 0x0000003c3c000000 0x0000001e1e000000

def z561 : W := mkw 0x0277efeb68345000 0x013bf7f5b41a2800 0xfefffffffc7e7800 0xff7ffffffe3f3c00

def z562 : W := mkw 0x100000001400280a 0x080000000a001405 0xea008e7c7c01f81e 0xf500473e3e00fc0f

def z563 : W := mkw 0x40305942c1018094 0x20182ca16080c04a 0xbe7879c3c001801e 0xdf3c3ce1e000c00f

def z564 : W := mkw 0x403a7d42c391c2d4 0x201d3ea161c8e16a 0xffff7dc3c3f9e7ff 0xffffbee1e1fcf3ff

def z565 : W := mkw 0x1000101495432cbb 0x0800080a4aa1965d 0xff80ffffffc7ffff 0xffc07fffffe3ffff

def z566 : W := mkw 0x914580bc146e2d2b 0xc8a2c05e0a371695 0x4087863c3c7e7800 0x2043c31e1e3f3c00

def z567 : W := mkw 0x403b7de3e38182d4 0x201dbef1f1c0c16a 0xff7f7df3f38187ff 0xffbfbef9f9c0c3ff

def z568 : W := mkw 0x0000000000000000 0x0000000000000000 0xe8008e0000000000 0x7400470000000000

def z569 : W := mkw 0x815d81fc02ee0761 0xc0aec0fe017703b0 0x247881fc008607e0 0x923c40fe004303f0

def z570 : W := mkw 0x22f7fffbf9596599 0x917bfffdfcacb2cc 0xdfff75b3b3796799 0xefffbad9d9bcb3cc

def z571 : W := mkw 0x817dd9fc03ef8761 0xc0beecfe01f7c3b0 0xfdfff9fc03ff87e1 0xfefffcfe01ffc3f0

def z572 : W := mkw 0x0266ee0368000000 0x01337701b4000000 0xfa7ffe03fc000000 0x7d3fff01fe000000

def z573 : W := mkw 0x100000001400280a 0x080000000a001405 0x000000000001f81e 0x000000000000fc0f

def z574 : W := mkw 0x100000001400280a 0x080000000a001405 0x020000007c00001e 0x010000003e00000f

def z575 : W := mkw 0x00227e000111d000 0x00113f000088e800 0xd9877e000379f801 0x6cc3bf0001bcfc00

def z576 : W := mkw 0x106cca0406a69822 0x0836650203534c11 0x20788a4c4c869866 0x103c452626434c33

def z577 : W := mkw 0x815c814c02a60260 0x40ae40a601530130 0x79ff804c03fe0061 0x3cffc02601ff0030

def z578 : W := mkw 0x0000001400420421 0x0000000a00210210 0x0000007c00000460 0x8000003e00000230

def z579 : W := mkw 0x0008000002800240 0x0004000001400120 0x01000000038007e1 0x0080000001c003f0

def z580 : W := mkw 0x5038494646828a66 0x281c24a323414533 0x20788a4c4c869866 0x103c452626434c33

def z581 : W := mkw 0x60bb7de3e399c3d4 0xb05dbef1f1cce1ea 0x157f718383380380 0x0abfb8c1c19c01c0

def z582 : W := mkw 0x837fefef6aa60260 0x41bff7f7b5530130 0xfe7ffffffc860060 0xff3ffffffe430030

def z583 : W := mkw 0x1000000404020822 0x0800000202010411 0xea008e7c7c869866 0xf500473e3e434c33

def z584 : W := mkw 0x2080001010586509 0x90400008082c3284 0x0080000000786000 0x00400000003c3000

def z585 : W := mkw 0x816efe1403ffd761 0xc0b77f0a01ffebb0 0xf9fffe0003ffffe1 0x7cffff0001fffff0

def z586 : W := mkw 0x40181142c38182d4 0x200c08a161c0c16a 0x070001c3c38187ff 0x838000e1e1c0c3ff

def z587 : W := mkw 0x0000000000000000 0x0000000000000000 0x5987000003780001 0x2cc3800001bc0000

def z588 : W := mkw 0x0000001010402409 0x0000000808201204 0x0200003030000418 0x810000181800020c

def z589 : W := mkw 0xc17dc9fe42ee8765 0xe0bee4ff217743b2 0x7dff89fc43fe87e7 0xbeffc4fe21ff43f3

def z590 : W := mkw 0x40385942c38182d4 0x201c2ca161c0c16a 0x97787983c301839e 0x4bbc3cc1e180c1cf

def z591 : W := mkw 0x100000041402282a 0x080000020a011415 0xa2008e4c7c87f87e 0x510047263e43fc3f

def z592 : W := mkw 0x20e7feb1b1596599 0x9073ff58d8acb2cc 0xffffffb3b3796799 0xffffffd9d9bcb3cc

def z593 : W := mkw 0x8108101403ffd761 0xc084080a01ffebb0 0x0180000003ffffe1 0x00c0000001fffff0

def z594 : W := mkw 0x1000000404020822 0x0800000202010411 0x0000000000869866 0x0000000000434c33

def z595 : W := mkw 0x40081000838182d4 0x2004080041c0c16a 0x9f007183838187ff 0xcf8038c1c1c0c3ff

def z596 : W := mkw 0x007fffe803b5d000 0x003ffff401dae800 0xfdfffffc03fff801 0xfefffffe01fffc00

def z597 : W := mkw 0x30801014955b6dbb 0x9840080a4aadb6dd 0xeb808e7c7fffffff 0xf5c0473e3fffffff

def z598 : W := mkw 0x20a37eb1b159f599 0x9051bf58d8acfacc 0xdf877fb3b379ff99 0xefc3bfd9d9bcffcc

def z599 : W := mkw 0xc15d91fc83ef87f5 0xe0aec8fe41f7c3fa 0x7dff81fc03ff87ff 0xbeffc0fe01ffc3ff

def z600 : W := mkw 0x1000001014402c0b 0x080000080a201605 0xca800e307c41fc1f 0xe54007183e20fe0f

def z601 : W := mkw 0x50385956d7c3aeff 0x281c2cab6be1d77f 0xbf7879ffff8187ff 0xdfbc3cffffc0c3ff

def z602 : W := mkw 0x100324b534422c2b 0x0801925a9a211615 0xfe87fffffcc7fc7f 0xff43fffffe63fe3f

def z603 : W := mkw 0x0000100081010090 0x0000080040808048 0xbf0079c3c38187ff 0xdf803ce1e1c0c3ff

def z604 : W := mkw 0x1277efff7c422c2b 0x093bf7ffbe211615 0xfe7ffffffc00047e 0xff3ffffffe00023f

def z605 : W := mkw 0x2080100081194190 0x90400800408ca0c8 0x0100000003380380 0x00800000019c01c0

def z606 : W := mkw 0x0000001000400401 0x0000000800200200 0x4880003000400401 0xa440001800200200

def z607 : W := mkw 0x004c800002a40000 0x0026400001520000 0xf9ff8e0003fff801 0x7cffc70001fffc00

def z608 : W := mkw 0x50385956d7c3aeff 0x281c2cab6be1d77f 0xbff879c3c3c7ffff 0xdffc3ce1e1e3ffff

def z609 : W := mkw 0x2082240130106008 0x1041120098083004 0x0000040030006000 0x0000020018003000

def z610 : W := mkw 0x0010014000000240 0x000800a000000120 0x040001c0000007e0 0x820000e0000003f0

def z611 : W := mkw 0x0210014a48000000 0x010800a524000000 0x0000004c4c000000 0x0000002626000000

def z612 : W := mkw 0x0028580083818090 0x00142c0041c0c048 0xbf78798383818799 0xdfbc3cc1c1c0c3cc

def z613 : W := mkw 0x027fefeb6aa40000 0x013ff7f5b5520000 0xfffffffffffe0001 0xffffffffffff0000

def z614 : W := mkw 0x002a7e0003b5d000 0x00153f0001dae800 0x81807e0003fff801 0x40c03f0001fffc00

def z615 : W := mkw 0x8377efff684a0761 0xc1bbf7ffb42503b0 0xfe7ffffffc0007e0 0xff3ffffffe0003f0

def z616 : W := mkw 0x40285802c3818094 0x20142c0161c0c04a 0xbb787803c381801f 0x5dbc3c01e1c0c00f

def z617 : W := mkw 0x608b34b1b3d9e7dd 0xb0459a58d9ecf3ee 0xdf8775b3b3f9e7ff 0xefc3bad9d9fcf3ff

def z618 : W := mkw 0x208110b1b1596599 0x90408858d8acb2cc 0x078001b3b3796799 0x83c000d9d9bcb3cc

def z619 : W := mkw 0x02227e036911d000 0x01113f01b488e800 0x82007e03fc01f800 0x41003f01fe00fc00

def z620 : W := mkw 0x22f7effbf8482599 0x917bf7fdfc2412cc 0xfe7ffffffc000798 0xff3ffffffe0003cc

def z621 : W := mkw 0x209b35f1b3d967d9 0x904d9af8d9ecb3ec 0xffff75f3b3f967f9 0xffffbaf9d9fcb3fc

def z622 : W := mkw 0x0008000002a40000 0x0004000001520000 0x0180000003fe0001 0x00c0000001ff0000

def z623 : W := mkw 0x100000001400280a 0x080000000a001405 0x000006003c007800 0x000003001e003c00

def z624 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000000081847f 0x000000000040c23f

def z625 : W := mkw 0x105581fc14422c2b 0x082ac0fe0a211615 0xfeff8ffc7cc7fc7f 0xff7fc7fe3e63fe3f

def z626 : W := mkw 0x8108001402ee0761 0xc084000a017703b0 0x6980807c03fe07e1 0xb4c0403e01ff03f0

def z627 : W := mkw 0x40205802c1018094 0x20102c016080c04a 0x9f007983c301879f 0xcf803cc1e180c3cf

def z628 : W := mkw 0x0000000000000000 0x0000000000000000 0x0080000000c7f801 0x004000000063fc00

def z629 : W := mkw 0x006cca0002a49000 0x0036650001524800 0x0078000000000000 0x003c000000000000

def z630 : W := mkw 0x1000001414422c2b 0x0800000a0a211615 0x82800e007cc7fc7f 0x414007003e63fe3f

def z631 : W := mkw 0x0030494240000000 0x001824a120000000 0x1478718380000000 0x0a3c38c1c0000000

def z632 : W := mkw 0x815d81ec02a60260 0x40aec0f601530130 0x7c7f81fc00860060 0xbe3fc0fe00430030

def z633 : W := mkw 0x814d80bc02ee0761 0xc0a6c05e017703b0 0x4187803c03fe07e1 0x20c3c01e01ff03f0

def z634 : W := mkw 0x817ccb4c02a69260 0x40be65a601534930 0x20788a4c00869860 0x103c452600434c30

def z635 : W := mkw 0x0030494240000000 0x001824a120000000 0xbe7879c3c081847f 0xdf3c3ce1e040c23f

def z636 : W := mkw 0x006efe0003b5d000 0x00377f0001dae800 0x317ffa0003be9800 0x18bffd0001df4c00

def z637 : W := mkw 0x20effeb133fdf509 0x9077ff5899fefa84 0xf9fffe3033fff801 0x7cffff1819fffc00

def z638 : W := mkw 0x0002341011516409 0x00011a0808a8b204 0xdb87743033796419 0xedc3ba1819bcb20c

def z639 : W := mkw 0x000324a120000000 0x0001925090000000 0x1407718380000000 0x0a03b8c1c0000000

def z640 : W := mkw 0xa18b34b5b3ff67f9 0xd0c59a5ad9ffb3fc 0xdf8775b3b3ff67f9 0xefc3bad9d9ffb3fc

def z641 : W := mkw 0x006efe0003b5d000 0x00377f0001dae800 0x917f7e000339f800 0x48bfbf00019cfc00

def z642 : W := mkw 0x20cfb4b1b3fd6599 0x9067da58d9feb2cc 0xfffff5b3b3ff6799 0xfffffad9d9ffb3cc

def z643 : W := mkw 0x40385942c38182d4 0x201c2ca161c0c16a 0x21780840438187ff 0x10bc042021c0c3ff

def z644 : W := mkw 0x1008101417f7fc2b 0x0804080a0bfbfe15 0xeb808e7c7ffffc7f 0xf5c0473e3ffffe3f

def z645 : W := mkw 0x208b34b1b3fdf599 0x90459a58d9fefacc 0xdf8775b3b3ffff99 0xefc3bad9d9ffffcc

def z646 : W := mkw 0x0000000000000000 0x0000000000000000 0x20008a4c4c000000 0x1000452626000000

def z647 : W := mkw 0x40385942c38182d4 0x201c2ca161c0c16a 0x9f78718383010799 0xcfbc38c1c18083cc

def z648 : W := mkw 0x208324a120184100 0x90419250900c2080 0x0007000000380000 0x00038000001c0000

def z649 : W := mkw 0x1000001404420c23 0x0800000a02210611 0x68808a7c4cc69c67 0xb440453e26634e33

def z650 : W := mkw 0x2080101091596599 0x9040080848acb2cc 0xcb80043033796799 0xe5c0021819bcb3cc

def z651 : W := mkw 0x837fefff6aee0761 0xc1bff7ffb57703b0 0x7dfff1ff83fe07e1 0xbefff8ffc1ff03f0

def z652 : W := mkw 0x006cda0003b5d000 0x00366d0001dae800 0x21f88a0003fff801 0x10fc450001fffc00

def z653 : W := mkw 0x000324a120000000 0x0001925090000000 0xfe07fffffc000000 0xff03fffffe000000

def z654 : W := mkw 0x40285800838182d4 0x20142c0041c0c16a 0xb9787800038187ff 0x5cbc3c0001c0c3ff

def z655 : W := mkw 0x0267eea928000000 0x0133f75494000000 0xf87ffe3c3c000000 0x7c3fff1e1e000000

def z656 : W := mkw 0x208100b1b0482599 0x90408058d82412cc 0x5f8701b3b3780799 0xafc380d9d9bc03cc

def z657 : W := mkw 0x40385942c38182d4 0x201c2ca161c0c16a 0x3d7871c3838007e1 0x9ebc38e1c1c003f0

def z658 : W := mkw 0xc108101483ef87f5 0xe084080a41f7c3fa 0x0180000003ff87ff 0x00c0000001ffc3ff

def z659 : W := mkw 0x1000001414422c2b 0x0800000a0a211615 0x20808a4c4cc7fc7f 0x104045262663fe3f

def z660 : W := mkw 0x20b37df3f1596599 0x9059bef9f8acb2cc 0xffff7df3f3796799 0xffffbef9f9bcb3cc

def z661 : W := mkw 0x2080001090482599 0x90400008482412cc 0x0000000000000798 0x00000000000003cc

def z662 : W := mkw 0x40000002c0000094 0x200000016000004a 0x02000003c000001e 0x01000001e000000f

def z663 : W := mkw 0x000334b001594501 0x80019a5800aca280 0xdd8775b003796781 0xeec3bad801bcb3c0

def z664 : W := mkw 0x106efe0407b7d822 0x08377f0203dbec11 0xf9fffe4c4ffff867 0x7cffff2627fffc33

def z665 : W := mkw 0x407eff42c38182d4 0x203f7fa161c0c16a 0xff7fffc3c38187ff 0xffbfffe1e1c0c3ff

def z666 : W := mkw 0x104c801416e62c2b 0x0826400a0b731615 0xfbff8e7c7ffffc7f 0xfdffc73e3ffffe3f

def z667 : W := mkw 0x208334b1b1596599 0x90419a58d8acb2cc 0x4187043033796799 0x20c3821819bcb3cc

def z668 : W := mkw 0xc17cc94e42a68264 0x60be64a721534132 0x2078884c40868066 0x103c442620434033

def z669 : W := mkw 0x20823401b1116098 0x10411a00d888b04c 0xdb877403b3796019 0x6dc3ba01d9bcb00c

def z670 : W := mkw 0x1000001414422c2b 0x0800000a0a211615 0x60808e7c7cc6f866 0x3040473e3e637c33

def z671 : W := mkw 0xc17dd9eac3ad83d4 0xe0beecf561d6c1ea 0x157f718383380380 0x0abfb8c1c19c01c0

def z672 : W := mkw 0x027fffeb6bb5d000 0x013ffff5b5dae800 0x157f718383380000 0x0abfb8c1c19c0000

def z673 : W := mkw 0x0020580001018000 0x00102c000080c000 0x8000780000018000 0x40003c000000c000

def z674 : W := mkw 0x0066fe000135d000 0x00337f00009ae800 0xc087fe00007ff800 0x6043ff00003ffc00

def z675 : W := mkw 0x006efe0003b5d000 0x00377f0001dae800 0x79fff00003fe0001 0x3cfff80001ff0000

def z676 : W := mkw 0x20c7a6b1307c7509 0x9063d358983e3a84 0x40878630307e7800 0x2043c318183f3c00

def z677 : W := mkw 0x4000100081018094 0x200008004080c04a 0x000000000001801e 0x000000000000c00f

def z678 : W := mkw 0x609101f3f04827dd 0xb04880f9f82413ee 0x060001f3f00007fe 0x830000f9f80003ff

def z679 : W := mkw 0x208324b130586509 0x90419258982c3284 0x5d8705b033786781 0xaec382d819bc33c0

def z680 : W := mkw 0x0002340001114000 0x00011a000088a000 0x8000740000016000 0x40003a000000b000

def z681 : W := mkw 0x0000000000000000 0x0000000000000000 0x2000084040808066 0x1000042020404033

def z682 : W := mkw 0x208324b130586509 0x90419258982c3284 0xca87043030796419 0xe5438218183cb20c

def z683 : W := mkw 0x12226e177c422c2b 0x0911370bbe211615 0xea80fe7ffcc7fc7f 0xf5407f3ffe63fe3f

def z684 : W := mkw 0x811901fc02ee0761 0xc08c80fe017703b0 0x058001fc03fe07e1 0x82c000fe01ff03f0

def z685 : W := mkw 0x0028480002808000 0x0014240001404000 0x2078080000808000 0x103c040000404000

def z686 : W := mkw 0x40000000800002d4 0x200000004000016a 0x00000000000007fe 0x00000000000003ff

def z687 : W := mkw 0x02226e0368000000 0x01113701b4000000 0x0000700380000000 0x00003801c0000000

def z688 : W := mkw 0x0000000000000000 0x0000000000000000 0x82000e007c000000 0x410007003e000000

def z689 : W := mkw 0x2080101091596599 0x9040080848acb2cc 0x9f80718383796799 0xcfc038c1c1bcb3cc

def z690 : W := mkw 0x006efe1403f7d421 0x00377f0a01fbea10 0xf9fffe7c03fffc61 0xfcffff3e01fffe30

def z691 : W := mkw 0x815581fc006e0521 0xc0aac0fe00370290 0x7cff81fc007e0000 0xbe7fc0fe003f0000

def z692 : W := mkw 0x000a340003b5d000 0x00051a0001dae800 0xd987740003fff801 0x6cc3ba0001fffc00

def z693 : W := mkw 0x229101fbf8482599 0x914880fdfc2412cc 0x060001fffc000798 0x830000fffe0003cc

def z694 : W := mkw 0x0028580003b5d000 0x00142c0001dae800 0xb9f8780003fff801 0x5cfc3c0001fffc00

def z695 : W := mkw 0x1000001414422c2b 0x0800000a0a211615 0xea808e7c7c467800 0xf540473e3e233c00

def z696 : W := mkw 0x1274cb5e5c422c2b 0x093a65af2e211615 0xeaf88e7c7cc7fc7f 0xf57c473e3e63fe3f

def z697 : W := mkw 0x815fa7fc02fe5761 0xc0afd3fe017f2bb0 0x7dff87fc03fe7fe1 0xbeffc3fe01ff3ff0

def z698 : W := mkw 0x0247a6a928000000 0x0123d35494000000 0x0007000000000000 0x0003800000000000

def z699 : W := mkw 0xa1c7b4bdb17f65b9 0xd0e3da5ed8bfb2dc 0xdf87f5bfb37f6799 0xefc3fadfd9bfb3cc

def z700 : W := mkw 0x005581fc00420421 0x002ac0fe00210210 0x7cff81fc00c60461 0xbe7fc0fe00630230

def z701 : W := mkw 0x427fffebeb8182d4 0x213ffff5f5c0c16a 0x157f718383000380 0x0abfb8c1c18001c0

def z702 : W := mkw 0x0018015402c20661 0x000c00aa01610330 0x7df881fc03c607e1 0xbefc40fe01e303f0

def z703 : W := mkw 0x20823401b1116098 0x10411a00d888b04c 0x9f007583b3016799 0xcf803ac1d980b3cc

def z704 : W := mkw 0x911101fc144a2f6b 0xc88880fe0a2517b5 0xee808ffc7cc7ffff 0xf74047fe3e63ffff

def z705 : W := mkw 0x006eee0002a40000 0x0037770001520000 0xf9fffe0003fe0001 0x7cffff0001ff0000

def z706 : W := mkw 0xa19101fdb04a27f9 0xd0c880fed82513fc 0x060001ffb00007f8 0x830000ffd80003fc

def z707 : W := mkw 0x81337ffc015bd761 0xc099bffe00adebb0 0x84007ffc0001ffe0 0xc2003ffe0000fff0

def z708 : W := mkw 0x915d81fc16ee2f6b 0xc8aec0fe0b7717b5 0xffff89fc43ffffff 0xffffc4fe21ffffff

def z709 : W := mkw 0x20a27e11b151f499 0x10513f08d8a8fa4c 0xea80fe33b0c7fc19 0xf5407f19d863fe0c

def z710 : W := mkw 0x002a7c000391c000 0x00153e0001c8e000 0xf9fffe0003fff801 0x7cffff0001fffc00

def z711 : W := mkw 0xb1c7a4bd347e6d2b 0xd8e3d25e9a3f3695 0x4087863c3c7e7800 0x2043c31e1e3f3c00

def z712 : W := mkw 0x006cca0002a49000 0x0036650001524800 0xf9ff8e0003fff801 0x7cffc70001fffc00

def z713 : W := mkw 0x911101fc144a2f6b 0xc88880fe0a2517b5 0x040001fc000007fe 0x820000fe000003ff

def z714 : W := mkw 0x2082341091596599 0x90411a0848acb2cc 0xdf87758383796799 0xefc3bac1c1bcb3cc

def z715 : W := mkw 0x026efe012bb5d000 0x01377f0095dae800 0xf9fffe003ffff801 0x7cffff001ffffc00

def z716 : W := mkw 0x004ea60002b45000 0x00275300015a2800 0xf9ff8e0003fff801 0x7cffc70001fffc00

def z717 : W := mkw 0x32a27e17fd536cbb 0x19513f0bfea9b65d 0xea80fe7ffcc7fc7f 0xf5407f3ffe63fe3f

def z718 : W := mkw 0x208110b1b1492599 0x90408858d8a492cc 0xdf8771b3b3790799 0xefc3b8d9d9bc83cc

def z719 : W := mkw 0x815d81fc02ee0761 0xc0aec0fe017703b0 0x357f81fc03be07e0 0x9abfc0fe01df03f0

def z720 : W := mkw 0x026efe080bb5d000 0x01377f0405dae800 0xf9fffe0c0ffff801 0x7cffff0607fffc00

def z721 : W := mkw 0x021911eb6bb5d000 0x010c88f5b5dae800 0x078001fffffff801 0x83c000fffffffc00

def z722 : W := mkw 0x915d81fc16ee2f6b 0xc8aec0fe0b7717b5 0x177f01fc7f3807fe 0x8bbf80fe3f9c03ff

def z723 : W := mkw 0x815d81fc02ee0761 0xc0aec0fe017703b0 0x7dff87fc03fe7fe1 0xbeffc3fe01ff3ff0

def z724 : W := mkw 0x006cd80003b5d000 0x00366c0001dae800 0xf9fff80003fff801 0x7cfffc0001fffc00

def z725 : W := mkw 0x815d81fc02ee0761 0xc0aec0fe017703b0 0x7dff89fc43fe87e7 0xbeffc4fe21ff43f3

def z726 : W := mkw 0x915d81fc16ee2f6b 0xc8aec0fe0b7717b5 0x15ff018003ffffff 0x0aff80c001ffffff

def z727 : W := mkw 0x006efe0003b5d000 0x00377f0001dae800 0xfbfffe7c7ffffc7f 0xfdffff3e3ffffe3f

def z728 : W := mkw 0xc165d8bec16f85b5 0xe0b2ec5f60b7c2da 0xc287f83fc07f801e 0x6143fc1fe03fc00f

def z729 : W := mkw 0x0277efeb68000000 0x013bf7f5b4000000 0xfe7ffffffc01f800 0xff3ffffffe00fc00

def z730 : W := mkw 0x0277efeb68080100 0x813bf7f5b4040080 0xff7fffffff380380 0xffbfffffff9c01c0

def z731 : W := mkw 0x20edcab1b2ecb599 0x9076e558d9765acc 0x26788bb3b0869f98 0x933c45d9d8434fcc

def z732 : W := mkw 0x208336b1b1597599 0x90419b58d8acbacc 0xdf8777b3b3797f99 0xefc3bbd9d9bcbfcc

def z733 : W := mkw 0x308334b5b55b6dbb 0x98419a5adaadb6dd 0xdf87f7bfbfffffff 0xefc3fbdfdfffffff

def z734 : W := mkw 0x0276ef4b68000000 0x013b77a5b4000000 0xea78fe7ffc000000 0xf53c7f3ffe000000

def z735 : W := mkw 0x60bb6df372d8e74d 0xb05db6f9b96c73a6 0x60ff0c7070f8e066 0x307f8638387c7033

def z736 : W := mkw 0x005c815402e60661 0x002e40aa01730330 0x7dff81fc03fe07e1 0xbeffc0fe01ff03f0

def z737 : W := mkw 0x000324b120480501 0x8001925890240280 0x5d8771b383780781 0xaec3b8d9c1bc03c0

def z738 : W := mkw 0xc17cc95e42e68665 0x60be64af21734332 0xeaf8887c40c7847f 0xf57c443e2063c23f

def z739 : W := mkw 0x60a27c03e111c094 0x30513e01f088e04a 0x0000700380000000 0x00003801c0000000

def z740 : W := mkw 0x915d81fc16ee2f6b 0xc8aec0fe0b7717b5 0x7fff87fc7ffe7fff 0xbfffc3fe3fff3fff

def z741 : W := mkw 0x407ccb4242a49244 0x203e65a121524922 0xeaf88e4040c7fc7f 0xf57c47202063fe3f

def z742 : W := mkw 0x815d81fc02ee0761 0xc0aec0fe017703b0 0x5dff81bc037e0781 0xaeffc0de01bf03c0

def z743 : W := mkw 0x0277efeb68000000 0x013bf7f5b4000000 0xfe7ffffffc869800 0xff3ffffffe434c00

def z744 : W := mkw 0x815d83fc02ee1761 0xc0aec1fe01770bb0 0x7dff83fc03fe1fe1 0xbeffc1fe01ff0ff0

def z745 : W := mkw 0x4056a742c03452d4 0x202b53a1601a296a 0x468787c3c07e7ffe 0xa343c3e1e03f3fff

def z746 : W := mkw 0x208334a1a1194190 0x90419a50d08ca0c8 0x5d87718383780381 0x2ec3b8c1c1bc01c0

def z747 : W := mkw 0x915d81fc16ee2f6b 0xc8aec0fe0b7717b5 0x7fff81fc7fffffff 0xbfffc0fe3fffffff

def z748 : W := mkw 0x1000001414422c2b 0x0800000a0a211615 0xa2008e7c7c87fc7e 0xd100473e3e43fe3f

def z749 : W := mkw 0xc17cc94a42a48244 0x60be64a521524122 0x0078000000000000 0x003c000000000000

def z750 : W := mkw 0x0277efeb68240000 0x013bf7f5b4120000 0xfefffffffc7e0000 0xff7ffffffe3f0000

def z751 : W := mkw 0x424fb6a9ab8182d4 0x2127db54d5c0c16a 0x4107863c3f8187ff 0x2083c31e1fc0c3ff

def z752 : W := mkw 0x815d81fc02ee0761 0xc0aec0fe017703b0 0xfdff85fc03ff67e1 0xfeffc2fe01ffb3f0

def z753 : W := mkw 0x208334a1a1194190 0x90419a50d08ca0c8 0xdd07758383380380 0x6e83bac1c19c01c0

def z754 : W := mkw 0x208334a1a1194190 0x90419a50d08ca0c8 0xdf0775b3b3390799 0xef83bad9d99c83cc

def z755 : W := mkw 0x70a27c03f511e89e 0x38513e01fa88f44f 0x82007e03fc01f81e 0x41003f01fe00fc0f

def z756 : W := mkw 0x106efe1417f7fc2b 0x08377f0a0bfbfe15 0x137f707c7f38047e 0x89bfb83e3f9c023f

def z757 : W := mkw 0x406efe0083b5d2d4 0x20377f0041dae96a 0xf9fffe0003fffb81 0x7cffff0001fffdc0

def z758 : W := mkw 0x006efe0123b5d000 0x00377f0091dae800 0xfbfffe03b3fff801 0x7dffff01d9fffc00

def z759 : W := mkw 0x208334b1b1596599 0x90419a58d8acb2cc 0xff877db3b3f9e799 0xffc3bed9d9fcf3cc

def z760 : W := mkw 0x0277efeb68000000 0x013bf7f5b4000000 0x967f7ffffc000000 0xcb3fbffffe000000

def z761 : W := mkw 0x0277efeb68000000 0x013bf7f5b4000000 0xfe7ffffffc010419 0xff3ffffffe00820c

def z762 : W := mkw 0x815d81fc02ee0761 0xc0aec0fe017703b0 0xffff81fc03ff07f9 0xffffc0fe01ff83fc

def z763 : W := mkw 0xa1dd81fd32ee2769 0xd0eec0fe997713b4 0x7dff81fc33fe07e1 0xbeffc0fe19ff03f0

def z764 : W := mkw 0x005581fc004a0521 0x802ac0fe00250290 0x7dff81fc03fe07e1 0xbeffc0fe01ff03f0

def z765 : W := mkw 0x0277efeb68000000 0x013bf7f5b4000000 0xfc7fffbfbc000000 0x7e3fffdfde000000

def z766 : W := mkw 0x22f4db5ad9596599 0x917a6dad6cacb2cc 0x21f88a4c4f796799 0x10fc452627bcb3cc

def z767 : W := mkw 0xa1deb54db3b762f8 0x50ef5aa6d9dbb17c 0xa278f44fb0876078 0x513c7a27d843b03c

def z768 : W := mkw 0x608334b1b159e59d 0xb0419a58d8acf2ce 0xdf8775b3b379e79f 0xefc3bad9d9bcf3cf

def z769 : W := mkw 0x40385942c38182d4 0x201c2ca161c0c16a 0x177871c3c38187ff 0x8bbc38e1e1c0c3ff

def z770 : W := mkw 0x40385942c38182d4 0x201c2ca161c0c16a 0xbf7879ffff8187ff 0xdfbc3cffffc0c3ff

def z771 : W := mkw 0x832a6e176aee0761 0xc195370bb57703b0 0x83807e03fffe07e1 0x41c03f01ffff03f0

def z772 : W := mkw 0x814d80bc02ee0521 0xc0a6c05e01770290 0x7dff81bc03fe0781 0xbeffc0de01ff03c0

def z773 : W := mkw 0x507ccb5656e6be6f 0x283e65ab2b735f37 0xeaf88e7c7cc7fc7f 0xf57c473e3e63fe3f

def z774 : W := mkw 0x7088101497dbefff 0xb844080a4bedf7ff 0x0180000003ffffff 0x00c0000001ffffff

def z775 : W := mkw 0x3088101497fffdbb 0x9844080a4bfffedd 0x0180000003ffffff 0x00c0000001ffffff

def z776 : W := mkw 0x815d81e802ac0340 0xc0aec0f4015601a0 0x5dff018003780381 0x2eff80c001bc01c0

def z777 : W := mkw 0x02336deb68000000 0x0119b6f5b4000000 0xfe7f7dfffc000000 0xff3fbefffe000000

def z778 : W := mkw 0x915d81e816ac2b4a 0xc8aec0f40b5615a5 0x977f0f807f39fb9e 0x4bbf87c03f9cfdcf

def z779 : W := mkw 0x20a27e01b1116098 0x10513f00d888b04c 0x82007e03b0016018 0x41003f01d800b00c

def z780 : W := mkw 0xc15d81fe42ee0765 0xe0aec0ff217703b2 0x7dff81fc43fe07e7 0xbeffc0fe21ff03f3

def z781 : W := mkw 0x006efe0003b5d000 0x00377f0001dae800 0x51fff60003fff801 0x28fffb0001fffc00

def z782 : W := mkw 0x208334a1a1194190 0x90419a50d08ca0c8 0xbf0779c3c3b987ff 0xdf83bce1e1dcc3ff

def z783 : W := mkw 0x50227e02d511f89e 0x28113f016a88fc4f 0x82007e03fc01f81e 0x41003f01fe00fc0f

def z784 : W := mkw 0x811901f402ee0761 0xc08c80fa017703b0 0x7dff01f003fe07e1 0xbeff80f801ff03f0

def z785 : W := mkw 0x006efe0083b5d090 0x00377f0041dae848 0xf9fffe0003ffff99 0x7cffff0001ffffcc

def z786 : W := mkw 0x20eefe01a3b5d090 0x10777f00d1dae848 0xf9fffe0383fff801 0x7cffff01c1fffc00

def z787 : W := mkw 0x837ccb4a4aa40240 0x41be65a525520120 0x20788a4c4c000000 0x103c452626000000

def z788 : W := mkw 0x835d81ff6aee0761 0xc1aec0ffb57703b0 0xffff8ffffffe07e1 0xffffc7ffffff03f0

def z789 : W := mkw 0x208334b1b1596599 0x90419a58d8acb2cc 0x9f0771b3b3390799 0xcf83b8d9d99c83cc

def z790 : W := mkw 0x815d81e802ac0340 0xc0aec0f4015601a0 0xfdff8f8003fffb81 0x7effc7c001fffdc0

def z791 : W := mkw 0x0277efeb68345000 0x013bf7f5b41a2800 0xfe7ffffffc380000 0xff3ffffffe1c0000

def z792 : W := mkw 0x105c815416e62e6b 0x082e40aa0b731735 0xffff8ffc7fffffff 0xffffc7fe3fffffff

def z793 : W := mkw 0x40385942c38182d4 0x201c2ca161c0c16a 0x9f787183838187ff 0xcfbc38c1c1c0c3ff

def z794 : W := mkw 0x00336de360000000 0x0019b6f1b0000000 0xfe7ffffffc000000 0xff3ffffffe000000

def z795 : W := mkw 0x000110b091492599 0x8000885848a492cc 0xdf8775b3b3796799 0xefc3bad9d9bcb3cc

def z796 : W := mkw 0x208334b1b1596599 0x90419a58d8acb2cc 0xdf0775b3b3380798 0xef83bad9d99c03cc

def z797 : W := mkw 0x40385942c38182d4 0x201c2ca161c0c16a 0xfff8f9c3c3c787ff 0xfffc7ce1e1e3c3ff

def z798 : W := mkw 0x815d81fc02ee0761 0xc0aec0fe017703b0 0x5dff01b003fe07e1 0xaeff80d801ff03f0

def z799 : W := mkw 0x915d81fc16ee2f6b 0xc8aec0fe0b7717b5 0x7dff8bfc4fffffff 0xbeffc5fe27ffffff

def z800 : W := mkw 0x10000014144a2d2b 0x8800000a0a251695 0xeb808e7c7fffffff 0xf5c0473e3fffffff

def z801 : W := mkw 0x006eee0002b4d000 0x00377700015a6800 0x79ff8e0003fef801 0x3cffc70001ff7c00

def z802 : W := mkw 0x006efe0003b5d000 0x00377f0001dae800 0x31fffa0003fff801 0x18fffd0001fffc00

def z803 : W := mkw 0x208334b1a1594591 0x90419a58d0aca2c8 0xdf8775b3b3780781 0xefc3bad9d9bc03c0

def z804 : W := mkw 0x911101fc144a2f6b 0xc88880fe0a2517b5 0x040001fc3c0007e0 0x820000fe1e0003f0

def z805 : W := mkw 0x40305942c10182d4 0x20182ca16080c16a 0xbe7879c3c00187fe 0xdf3c3ce1e000c3ff

def z806 : W := mkw 0x208334b1b159f599 0x90419a58d8acfacc 0xdf8775b3b379ff99 0xefc3bad9d9bcffcc

def z807 : W := mkw 0x1277efff7c422c2b 0x093bf7ffbe211615 0x14ff718380c7fc7f 0x0a7fb8c1c063fe3f

def z808 : W := mkw 0x815d81f802ec0741 0xc0aec0fc017603a0 0x15ff018003780781 0x0aff80c001bc03c0

def z809 : W := mkw 0x002a7c0003b5d000 0x00153e0001dae800 0xf9ff7c0003fff801 0x7cffbe0001fffc00

def z810 : W := mkw 0x815d81fc02ee0761 0xc0aec0fe017703b0 0x15ff01fc03fe07e1 0x8aff80fe01ff03f0

def z811 : W := mkw 0x006efe0003b5d000 0x00377f0001dae800 0xf9fffe00037e7800 0x7cffff0001bf3c00

def z812 : W := mkw 0x0266ee0368000000 0x01337701b4000000 0xfa7ffe7ffc000000 0xfd3fff3ffe000000

def z813 : W := mkw 0x105581fc144a2d2b 0x882ac0fe0a251695 0xffff8ffc7fffffff 0xffffc7fe3fffffff

def z814 : W := mkw 0x006efe0003b5d000 0x00377f0001dae800 0xfbfffe0003fffc19 0xfdffff0001fffe0c

def z815 : W := mkw 0x308334b1b5596d9b 0x98419a58daacb6cd 0xff87ffb3ffffff9f 0xffc3ffd9ffffffcf

def z816 : W := mkw 0x006efe0003b5d000 0x00377f0001dae800 0xfbfffe4043fff801 0xfdffff2021fffc00

def z817 : W := mkw 0x308334b5b55b6dbb 0x98419a5adaadb6dd 0xff87f5ffb3ffffff 0xffc3faffd9ffffff

def z818 : W := mkw 0x0274cb4a48000000 0x013a65a524000000 0xfe78fffffc000000 0xff3c7ffffe000000

def z819 : W := mkw 0x0275cbeb68000000 0x013ae5f5b4000000 0xbe78fbfffc000000 0xdf3c7dfffe000000

def z820 : W := mkw 0x406efe0083b5d2d4 0x20377f0041dae96a 0xfbfffe4043ffffff 0xfdffff2021ffffff

def z821 : W := mkw 0x0275c9eb68000000 0x013ae4f5b4000000 0xfe7ff9fffc000000 0xff3ffcfffe000000

def z822 : W := mkw 0x004ea60002b45000 0x00275300015a2800 0x60ff860000fe7800 0x307fc300007f3c00

def z823 : W := mkw 0x000110a081090190 0x80008850408480c8 0x9f07718383390799 0xcf83b8c1c19c83cc

def z824 : W := mkw 0x000324a120080100 0x8001925090040080 0x1507718383380380 0x0a83b8c1c19c01c0

def z825 : W := mkw 0x208334b1b1596599 0x90419a58d8acb2cc 0xdf8775f3f37967ff 0xefc3baf9f9bcb3ff

def z826 : W := mkw 0x005d81f002ec0741 0x802ec0f8017603a0 0x7dff81f003fe07e1 0xbeffc0f801ff03f0

def z827 : W := mkw 0x104d80b416ee2d2b 0x8826c05a0b771695 0xffff8ffc7fffffff 0xffffc7fe3fffffff

def z828 : W := mkw 0x004d80a002ac0100 0x8026c05001560080 0x7dff818003fe0381 0x3effc0c001ff01c0

def z829 : W := mkw 0x000334b081594591 0x80019a5840aca2c8 0xdf8775b383796799 0xefc3bad9c1bcb3cc

def z830 : W := mkw 0x208334b1b1596599 0x90419a58d8acb2cc 0xff87fffffff9e7ff 0xffc3fffffffcf3ff

def z831 : W := mkw 0x835d81fd2aee0761 0xc1aec0fe957703b0 0x7dff81fc3ffe07e1 0xbeffc0fe1fff03f0

def z832 : W := mkw 0x006efe0003b5d000 0x00377f0001dae800 0x61ff8e0003fff801 0x30ffc70001fffc00

def z833 : W := mkw 0x915d81fc16ee2f6b 0xc8aec0fe0b7717b5 0x7dff87fc3fffffff 0xbeffc3fe1fffffff

def z834 : W := mkw 0x004c800002a40240 0x0026400001520120 0x79ff800003fe07e1 0x3cffc00001ff03f0

def z835 : W := mkw 0x208334b5a15b45b1 0x90419a5ad0ada2d8 0x7d87f1ff83fe07e1 0xbec3f8ffc1ff03f0

def z836 : W := mkw 0x5008101497c3aeff 0x2804080a4be1d77f 0x01000000038187ff 0x0080000001c0c3ff

def z837 : W := mkw 0x0267eea928000000 0x0133f75494000000 0xfe7fffbfbc000000 0xff3fffdfde000000

def z838 : W := mkw 0x40227e02c111d094 0x20113f016088e84a 0x82007803c001801e 0x41003c01e000c00f

def z839 : W := mkw 0x208334a1a1194190 0x90419a50d08ca0c8 0xff07ffffff380380 0xff83ffffff9c01c0

def z840 : W := mkw 0x208334b1b1596599 0x90419a58d8acb2cc 0xdd87758383796799 0x6ec3bac1c1bcb3cc

def z841 : W := mkw 0x308334b5b55b6dbb 0x98419a5adaadb6dd 0xff877dfffff9e7ff 0xffc3befffffcf3ff

def z842 : W := mkw 0x815581fc006e0521 0xc0aac0fe00370290 0x7dff81fc037e0781 0xbeffc0fe01bf03c0

def z843 : W := mkw 0xb19101fdb44a2ffb 0xd8c880feda2517fd 0x060001fffc0007fe 0x830000fffe0003ff

def z844 : W := mkw 0x000324a120080100 0x8001925090040080 0xdf0775b3b3380380 0xef83bad9d99c01c0

def z845 : W := mkw 0x00305942c1010090 0x00182ca160808048 0xbf7879c3c38187ff 0xdfbc3ce1e1c0c3ff

def z846 : W := mkw 0x20823401b1116098 0x10411a00d888b04c 0xdf877583b3796799 0xefc3bac1d9bcb3cc

def z847 : W := mkw 0x308334b5b55b6dbb 0x98419a5adaadb6dd 0xff87f5ffffff67ff 0xffc3faffffffb3ff

def z848 : W := mkw 0x915d81fc16ee2f6b 0xc8aec0fe0b7717b5 0xffff85fc33ffffff 0xffffc2fe19ffffff

def z849 : W := mkw 0x00227e008111d090 0x00113f004088e848 0x82007e038001f818 0x41003f01c000fc0c

def z850 : W := mkw 0x208334b1b1596599 0x90419a58d8acb2cc 0xdf87f7b3b37f7f99 0xefc3fbd9d9bfbfcc

def z851 : W := mkw 0x815d81e802ac0340 0xc0aec0f4015601a0 0x157f018003b807e1 0x0abf80c001dc03f0

def z852 : W := mkw 0x0046a60000345000 0x00235300001a2800 0x78ff8600007e7800 0x3c7fc300003f3c00

def z853 : W := mkw 0x208334a1a1194190 0x90419a50d08ca0c8 0x9d07718383390381 0x4e83b8c1c19c81c0

def z854 : W := mkw 0x835d83fc0aee0761 0xc1aec1fe057703b0 0x7dff83fc0ffe07e1 0xbeffc1fe07ff03f0

def z855 : W := mkw 0x815d81e802ac0340 0xc0aec0f4015601a0 0x3d7f01c003380380 0x9ebf80e0019c01c0

def z856 : W := mkw 0x308334b5b55b6dbb 0x98419a5adaadb6dd 0xdf8775b3b37f7f99 0xefc3bad9d9bfbfcc

def z857 : W := mkw 0x001901f012c82749 0x800c80f8096413a4 0xffff0df073f9e7ff 0xffff86f839fcf3ff

def z858 : W := mkw 0x815d81fc02ee0761 0xc0aec0fe017703b0 0xffff8ffc43ffffff 0xffffc7fe21ffffff

def z859 : W := mkw 0x308334b5b55b6dbb 0x98419a5adaadb6dd 0xff87ffbfbfffff99 0xffc3ffdfdfffffcc

def z860 : W := mkw 0x006efe0083b5d090 0x00377f0041dae848 0xffffffc3c3ffffff 0xffffffe1e1ffffff

def z861 : W := mkw 0xd17cc94e46a68a66 0x68be64a723534533 0x20788a4c4c869866 0x103c452626434c33

def z862 : W := mkw 0x100110b4954b2dbb 0x8800885a4aa596dd 0xff87ffffffffffff 0xffc3ffffffffffff

def z863 : W := mkw 0x0257a7e928000000 0x012bd3f494000000 0xfe7ff7ffbc000000 0xff3ffbffde000000

def z864 : W := mkw 0x0277efeb68000000 0x013bf7f5b4000000 0xff7fffffff000781 0xffbfffffff8003c0

def z865 : W := mkw 0x40181140838182d4 0x200c08a041c0c16a 0xbf7871c3838187ff 0xdfbc38e1c1c0c3ff

def z866 : W := mkw 0x915d81fc16ee2f6b 0xc8aec0fe0b7717b5 0xffff85fc7fff67ff 0xffffc2fe3fffb3ff

def z867 : W := mkw 0x60a27c03e111c094 0x30513e01f088e04a 0x82007803c001801e 0x41003c01e000c00f

def z868 : W := mkw 0x208334b1b1596599 0x90419a58d8acb2cc 0xd78775b3b3796398 0x6bc3bad9d9bcb1cc

def z869 : W := mkw 0x40385942c38182d4 0x201c2ca161c0c16a 0x377879c3c38087fe 0x9bbc3ce1e1c043ff

def z870 : W := mkw 0x208334a1a1194190 0x90419a50d08ca0c8 0x1507718383390799 0x0a83b8c1c19c83cc

def z871 : W := mkw 0x006efe0003b5d000 0x00377f0001dae800 0xfdffff8003ffff81 0xfeffffc001ffffc0

def z872 : W := mkw 0x811901fc02ca0761 0xc08c80fe016503b0 0x7dff01fc03f807e1 0xbeff80fe01fc03f0

def z873 : W := mkw 0x0277efeb68000000 0x013bf7f5b4000000 0xfefffffffc467800 0xff7ffffffe233c00

def z874 : W := mkw 0x0277efeb68000000 0x013bf7f5b4000000 0xfefffffffcc7fc7f 0xff7ffffffe63fe3f

def z875 : W := mkw 0x32c7a6bd3c5a6d2b 0x9963d35e9e2d3695 0x4087863c3c7e7800 0x2043c31e1e3f3c00

def z876 : W := mkw 0x0277efeb68000000 0x013bf7f5b4000000 0x7c7ff7ffbc000000 0xbe3ffbffde000000

def z877 : W := mkw 0x005581e800080100 0x802ac0f400040080 0x7d7f81fc03380380 0xbebfc0fe019c01c0

def z878 : W := mkw 0x02326f4368000000 0x011937a1b4000000 0xfe78fffffc000000 0xff3c7ffffe000000

def z879 : W := mkw 0x40385b42c38192d4 0x201c2da161c0c96a 0xbf787bc3c3819fff 0xdfbc3de1e1c0cfff

def z880 : W := mkw 0x006eee0002b45000 0x00377700015a2800 0xf9fffe0003fe7801 0x7cffff0001ff3c00

def z881 : W := mkw 0x308334b5b55b6dbb 0x98419a5adaadb6dd 0x170771ffff3807fe 0x8b83b8ffff9c03ff

def z882 : W := mkw 0x0277efeb68000000 0x013bf7f5b4000000 0xffffffffff780001 0xffffffffffbc0000

def z883 : W := mkw 0x006efe0003b5d000 0x00377f0001dae800 0x71fffe0003fef800 0x38ffff0001ff7c00

def z884 : W := mkw 0x406efe0083b5d094 0x20377f0041dae84a 0xf9fffe0003fff81f 0x7cffff0001fffc0f

def z885 : W := mkw 0x915d81fc16ee2f6b 0xc8aec0fe0b7717b5 0x7dff81fc03fe07ff 0xbeffc0fe01ff03ff

def z886 : W := mkw 0x22a27e03e9114090 0x11513f01f488a048 0x82007e03fc000000 0x41003f01fe000000

def z887 : W := mkw 0x915d81fc16ee2f6b 0xc8aec0fe0b7717b5 0xfdff8ffc03ffffff 0xfeffc7fe01ffffff

def z888 : W := mkw 0x0277efeb68000000 0x013bf7f5b4000000 0x7e7ff1fffc000000 0xbf3ff8fffe000000

def z889 : W := mkw 0x40304942c00002d4 0x201824a16000016a 0x167871c3c00007fe 0x8b3c38e1e00003ff

def z890 : W := mkw 0x815d81fc12ee2769 0xc0aec0fe097713b4 0xffff8dfc73ffe7ff 0xffffc6fe39fff3ff

def z891 : W := mkw 0x40304942c00002d4 0x201824a16000016a 0xbe7879c3c08187ff 0xdf3c3ce1e040c3ff

def z892 : W := mkw 0x22a27e03e9114090 0x11513f01f488a048 0x0000700380000000 0x00003801c0000000

def z893 : W := mkw 0x208334a1b1196198 0x90419a50d88cb0cc 0x15077583b3386380 0x0a83bac1d99c31c0

def z894 : W := mkw 0x006efe0003b5d000 0x00377f0001dae800 0xf9fffe3c3ffff801 0x7cffff1e1ffffc00

def z895 : W := mkw 0x40305942c10102d4 0x20182ca16080816a 0xbf7879c3c30107ff 0xdfbc3ce1e18083ff

def z896 : W := mkw 0x40385942c38182d4 0x201c2ca161c0c16a 0x977879c3c30187fe 0xcbbc3ce1e180c3ff

def z897 : W := mkw 0x0277efeb68345000 0x013bf7f5b41a2800 0xfefffffffcfff801 0xff7ffffffe7ffc00

def z898 : W := mkw 0x20a27c01b111e098 0x10513e00d888f04c 0x82007c03b001e018 0x41003e01d800f00c

def z899 : W := mkw 0x815d81fc02ee0761 0xc0aec0fe017703b0 0x157f01bc03380380 0x0abf80de019c01c0

def z900 : W := mkw 0x006efe0003b5d000 0x00377f0001dae800 0x11ff7000037e7800 0x08ffb80001bf3c00

def z901 : W := mkw 0x60a27c03f111e09c 0x30513e01f888f04e 0x82007403b0016018 0x41003a01d800b00c

def z902 : W := mkw 0x914c801416ee2f6b 0xc8a6400a0b7717b5 0xf9ff8e0003ffffff 0x7cffc70001ffffff

def z903 : W := mkw 0x815d81fc02ee0761 0xc0aec0fe017703b0 0x61ff807c03fe07e1 0x30ffc03e01ff03f0

def z904 : W := mkw 0x208334b1b1596599 0x90419a58d8acb2cc 0x1507718383380798 0x0a83b8c1c19c03cc

def z905 : W := mkw 0x000334b1a1490591 0x80019a58d0a482c8 0xdf8775b3b3790799 0xefc3bad9d9bc83cc

def z906 : W := mkw 0x001901f402ca0761 0x800c80fa016503b0 0x7dff81fc03fe07e1 0xbeffc0fe01ff03f0

def z907 : W := mkw 0x208334a1b1196198 0x90419a50d88cb0cc 0xdf877583b3796399 0x6fc3bac1d9bcb1cc

def z908 : W := mkw 0x0277efeb68105000 0x013bf7f5b4082800 0xfe7ffffffc007800 0xff3ffffffe003c00

def z909 : W := mkw 0x004c800002a40000 0x0026400001520000 0x7dff818003fe0781 0xbeffc0c001ff03c0

def z910 : W := mkw 0x004c800002a40000 0x0026400001520000 0x79ff800003fff801 0x3cffc00001fffc00

def z911 : W := mkw 0x208334b1a1594591 0x90419a58d0aca2c8 0x1587718383780781 0x0ac3b8c1c1bc03c0

def z912 : W := mkw 0x815d81f802ec0741 0xc0aec0fc017603a0 0x7dff01f003f807e1 0xbeff80f801fc03f0

def z913 : W := mkw 0x006eee0002a40000 0x0037770001520000 0xf9fffe0003fff801 0x7cffff0001fffc00

def z914 : W := mkw 0xc17cc94a42a48244 0x60be64a521524122 0x2078084040808066 0x103c042020404033

def z915 : W := mkw 0x815d81fc02ee0761 0xc0aec0fe017703b0 0x7dff81bc03fe0381 0x3effc0de01ff01c0

def z916 : W := mkw 0x937ccb5e5ee62e6b 0x49be65af2f731735 0xeaf88e7c7cc7fc7f 0xf57c473e3e63fe3f

def z917 : W := mkw 0x50385956d7c3aeff 0x281c2cab6be1d77f 0x55f8f7bfbf467b80 0x2afc7bdfdfa33dc0

def z918 : W := mkw 0x0066fe0001114000 0x00337f000088a000 0xf9fffe0003fff801 0x7cffff0001fffc00

def z919 : W := mkw 0x814c801402ee0761 0xc0a6400a017703b0 0x11ff000003fe07e1 0x08ff800001ff03f0

def z920 : W := mkw 0x40385942c38182d4 0x201c2ca161c0c16a 0x97787983c38187ff 0x4bbc3cc1e1c0c3ff

def z921 : W := mkw 0x228334b9b9596599 0x91419a5cdcacb2cc 0xdf8775bfbf796799 0xefc3badfdfbcb3cc

def z922 : W := mkw 0x208334a1a1194190 0x90419a50d08ca0c8 0xfd87ff8383fffb81 0x7ec3ffc1c1fffdc0

def z923 : W := mkw 0x000900b002c80501 0x8004805801640280 0x7dff01b003f80781 0xbeff80d801fc03c0

def z924 : W := mkw 0x006eee0002b4d000 0x00377700015a6800 0x40ff8600007e7800 0x207fc300003f3c00

def z925 : W := mkw 0x005d81f802c80741 0x802ec0fc016403a0 0x7dff81fc03f807e1 0xbeffc0fe01fc03f0

def z926 : W := mkw 0x006efe0003b5d000 0x00377f0001dae800 0xe0fffe0000fff800 0x707fff00007ffc00

def z927 : W := mkw 0x42385b42cb8182d4 0x211c2da165c0c16a 0xbf787bc3cf8187ff 0xdfbc3de1e7c0c3ff

def z928 : W := mkw 0x208334b1b1596599 0x90419a58d8acb2cc 0xdf877fb3b379ff99 0xefc3bfd9d9bcffcc

def z929 : W := mkw 0x8377efeb682c0100 0xc1bbf7f5b4160080 0xfe7ffffffc380000 0xff3ffffffe1c0000

def z930 : W := mkw 0x837ccb4e4aa69260 0x41be65a725534930 0x20788a4c4c869860 0x103c452626434c30

def z931 : W := mkw 0x0066fe0001355000 0x00337f00009aa800 0xf9fffe00037f7801 0x7cffff0001bfbc00

def z932 : W := mkw 0x006eee0002b4d000 0x00377700015a6800 0xe8ff8e0000fff801 0x747fc700007ffc00

def z933 : W := mkw 0x208334b1b1596599 0x90419a58d8acb2cc 0xff877df3f3796799 0xffc3bef9f9bcb3cc

def z934 : W := mkw 0x40227e008111d094 0x20113f004088e84a 0x80007e000001f81e 0x40003f000000fc0f

def z935 : W := mkw 0x0067eea120000000 0x0033f75090000000 0xfe7ffffffc000000 0xff3ffffffe000000

def z936 : W := mkw 0x427fffebebb5d2d4 0x213ffff5f5dae96a 0x157f718383380380 0x0abfb8c1c19c01c0

def z937 : W := mkw 0x004d80b402ee0521 0x8026c05a01770290 0x7dff81fc03fe07e1 0xbeffc0fe01ff03f0

def z938 : W := mkw 0x407cc94242a48244 0x203e64a121524122 0x2078884040868066 0x103c442020434033

def z939 : W := mkw 0x407ccb4242a49244 0x203e65a121524922 0x20788a0000869800 0x103c450000434c00

def z940 : W := mkw 0x815d81fc12ee2769 0xc0aec0fe097713b4 0x7dff81fc03ff67f9 0xbeffc0fe01ffb3fc

def z941 : W := mkw 0x407ccb4242a49244 0x203e65a121524922 0x0078000000000000 0x003c000000000000

def z942 : W := mkw 0x40385942c38182d4 0x201c2ca161c0c16a 0xbf787fc3c381ffff 0xdfbc3fe1e1c0ffff

def z943 : W := mkw 0x815d81fc02ee0761 0xc0aec0fe017703b0 0x7fff81fc43fe07ff 0xbfffc0fe21ff03ff

def z944 : W := mkw 0x406efe0083b5d2d4 0x20377f0041dae96a 0xffffff8383ffffff 0xffffffc1c1ffffff

def z945 : W := mkw 0xb188101497ff6ffb 0xd8c4080a4bffb7fd 0x0180000003ffffff 0x00c0000001ffffff

def z946 : W := mkw 0x815d81f802ec0741 0xc0aec0fc017603a0 0x55ff01b003780380 0x2aff80d801bc01c0

def z947 : W := mkw 0x000324b130482509 0x8001925898241284 0xdf8775b3b3796799 0xefc3bad9d9bcb3cc

def z948 : W := mkw 0x22a27e03f9116098 0x11513f01fc88b04c 0x82007403b0016018 0x41003a01d800b00c

def z949 : W := mkw 0x426efe03ebb5d094 0x21377f01f5dae84a 0xfbfffe03fffff81f 0x7dffff01fffffc0f

def z950 : W := mkw 0x0066fe000135d000 0x00337f00009ae800 0xf8fffe00007ff800 0x7c7fff00003ffc00

def z951 : W := mkw 0x815d81f802ec0741 0xc0aec0fc017603a0 0x7dff81fc03780781 0xbeffc0fe01bc03c0

def z952 : W := mkw 0x208334b5b15b65b9 0x90419a5ad8adb2dc 0xdf8775ffb37967f9 0xefc3baffd9bcb3fc

def z953 : W := mkw 0x208334b1b1596599 0x90419a58d8acb2cc 0xdf877fb3ff796799 0xefc3bfd9ffbcb3cc

def z954 : W := mkw 0x815d81fc02ee0761 0xc0aec0fe017703b0 0x3d7f01fc03b807e1 0x9ebf80fe01dc03f0

def z955 : W := mkw 0x208334a1a1194190 0x90419a50d08ca0c8 0x5d0771b383380380 0xae83b8d9c19c01c0

def z956 : W := mkw 0x931101ff7c4a2f6b 0xc98880ffbe2517b5 0x060001fffc0007fe 0x830000fffe0003ff

def z957 : W := mkw 0x915d81ec06ae0b62 0xc8aec0f6035705b1 0x357f8bcc4fbe9be6 0x1abfc5e627df4df3

def z958 : W := mkw 0x30c7a6b5347e7d2b 0x9863d35a9a3f3e95 0x4087863c3c7e7800 0x2043c31e1e3f3c00

def z959 : W := mkw 0x815d81e802ac0340 0xc0aec0f4015601a0 0x357f818003be0380 0x1abfc0c001df01c0

def z960 : W := mkw 0x308334b5b55b6dbb 0x98419a5adaadb6dd 0x1587718383ffffff 0x0ac3b8c1c1ffffff

def z961 : W := mkw 0x005c814002a40240 0x002e40a001520120 0x157f018003380380 0x0abf80c0019c01c0

def z962 : W := mkw 0x308334a1b519699a 0x98419a50da8cb4cd 0x97077f83ff39fb9e 0x4b83bfc1ff9cfdcf

def z963 : W := mkw 0x00181140838102d0 0x000c08a041c08168 0xbf7879c3c38187ff 0xdfbc3ce1e1c0c3ff

def z964 : W := mkw 0x208334a1b1196198 0x90419a50d88cb0cc 0x17077183b3380398 0x0b83b8c1d99c01cc

def z965 : W := mkw 0x023149eb68000000 0x0118a4f5b4000000 0x167871fffc000000 0x8b3c38fffe000000

def z966 : W := mkw 0x0277efeb68000000 0x013bf7f5b4000000 0xbe7f79fffc000000 0xdf3fbcfffe000000

def z967 : W := mkw 0x915d81fc16ee2f6b 0xc8aec0fe0b7717b5 0xffff8ffc7ffe7fe1 0xffffc7fe3fff3ff0

def z968 : W := mkw 0x0277efeb68000000 0x013bf7f5b4000000 0xde7f75fffc000000 0xef3fbafffe000000

def z969 : W := mkw 0x40081000838182d4 0x2004080041c0c16a 0xeb008e7c7f8187ff 0xf580473e3fc0c3ff

def z970 : W := mkw 0x006eee0002b4d000 0x00377700015a6800 0xf8fffe0000fef800 0x7c7fff00007f7c00

def z971 : W := mkw 0x20a27e01a111d090 0x10513f00d088e848 0x80007e038001f800 0x40003f01c000fc00

def z972 : W := mkw 0x40227c02c111c094 0x20113e016088e04a 0x82007c03c001e01e 0x41003e01e000f00f

def z973 : W := mkw 0x32a27e03fd11689a 0x19513f01fe88b44d 0x82007e03fc01f81e 0x41003f01fe00fc0f

def z974 : W := mkw 0x20a27e009111f098 0x10513f004888f84c 0x80007e000001f818 0x40003f000000fc0c

def z975 : W := mkw 0xc17cc94e42a68264 0x60be64a721534132 0x2078804c00860060 0x103c402600430030

def z976 : W := mkw 0x208334a1a1194190 0x90419a50d08ca0c8 0x9f07718383380380 0xcf83b8c1c19c01c0

def z977 : W := mkw 0x208334b1b1596599 0x90419a58d8acb2cc 0xdf877db3f379e79f 0xefc3bed9f9bcf3cf

def z978 : W := mkw 0x815d81fd22ee0761 0xc0aec0fe917703b0 0x7fff81ffb3fe07e1 0xbfffc0ffd9ff03f0

def z979 : W := mkw 0x815d81ec02ae0360 0xc0aec0f6015701b0 0x157f01cc033803e0 0x0abf80e6019c01f0

def z980 : W := mkw 0x40181142c38102d4 0x200c08a161c0816a 0xbf7871c3c38107ff 0xdfbc38e1e1c083ff

def z981 : W := mkw 0x308334b5b55b6dbb 0x98419a5adaadb6dd 0xdf877fffff79ffff 0xefc3bfffffbcffff

def z982 : W := mkw 0x208334b1b1596599 0x90419a58d8acb2cc 0xdd8775b3b3796381 0x6ec3bad9d9bcb1c0

def z983 : W := mkw 0x005c814002a40240 0x002e40a001520120 0xffff8fc043ffffff 0xffffc7e021ffffff

def z984 : W := mkw 0x40385942c38182d4 0x201c2ca161c0c16a 0xff78f9ffc38187ff 0xffbc7cffe1c0c3ff

def z985 : W := mkw 0x815c815402ee0761 0xc0ae40aa017703b0 0x7dff81c003fe07e1 0xbeffc0e001ff03f0

def z986 : W := mkw 0x308334b5b55b6dbb 0x98419a5adaadb6dd 0xdf87f7ffff7f7fff 0xefc3fbffffbfbfff

def z987 : W := mkw 0x9347a6bd3c6e2d2b 0xc9a3d35e9e371695 0x4087863c3c7e7800 0x2043c31e1e3f3c00

def z988 : W := mkw 0x004eb60003b5d000 0x00275b0001dae800 0x79ff860003fff801 0x3cffc30001fffc00

def z989 : W := mkw 0x406efe02c3b5d094 0x20377f0161dae84a 0xffffff83c3ffff9f 0xffffffc1e1ffffcf

def z990 : W := mkw 0x815d81fc02ee9761 0xc0aec0fe01774bb0 0x7dff81fc03fe9fe1 0xbeffc0fe01ff4ff0

def z991 : W := mkw 0x004ea60002b45000 0x00275300015a2800 0x51ff8600037e7800 0x28ffc30001bf3c00

def z992 : W := mkw 0x100324b5344a2d2b 0x8801925a9a251695 0xff87ffffffffffff 0xffc3ffffffffffff

def z993 : W := mkw 0x814d80b402ee0761 0xc0a6c05a017703b0 0x7dff81b003fe07e1 0xbeffc0d801ff03f0

def z994 : W := mkw 0x0030494240000000 0x001824a120000000 0xbe7879fffc000000 0xdf3c3cfffe000000

def z995 : W := mkw 0x815d81fc02ee0761 0xc0aec0fe017703b0 0x157f0180033807e0 0x0abf80c0019c03f0

def z996 : W := mkw 0x005d81f802ec0501 0x802ec0fc01760280 0x7dff81fc03fe0781 0xbeffc0fe01ff03c0

def z997 : W := mkw 0x835d81ff6aee0761 0xc1aec0ffb57703b0 0x7dff81ff83fe07e1 0xbeffc0ffc1ff03f0

def z998 : W := mkw 0x0066ee0000345000 0x00337700001a2800 0xf8fffe0000fff801 0x7c7fff00007ffc00

def z999 : W := mkw 0x30a27e01b511f89a 0x18513f00da88fc4d 0x82007e03fc01f81e 0x41003f01fe00fc0f

def z1000 : W := mkw 0x815d81fc02ee0761 0xc0aec0fe017703b0 0x55ff81fc037e07e0 0xaaffc0fe01bf03f0

def z1001 : W := mkw 0x815d81ec02ae0360 0xc0aec0f6015701b0 0x7dff81cc03fe03e1 0x3effc0e601ff01f0

def z1002 : W := mkw 0x006efe0003b5d000 0x00377f0001dae800 0xf9fffe0003fffc7f 0x7cffff0001fffe3f

def z1003 : W := mkw 0x308334b5b55b6dbb 0x98419a5adaadb6dd 0x5587f7bfbf7e7b80 0x2ac3fbdfdfbf3dc0

def z1004 : W := mkw 0x006efe0003b5d000 0x00377f0001dae800 0xf9fffe4043fff867 0x7cffff2021fffc33

def z1005 : W := mkw 0x815d81fc02ee0761 0xc0aec0fe017703b0 0x7dff81fc03ff87ff 0xbeffc0fe01ffc3ff

def z1006 : W := mkw 0x815d81e802ac0340 0xc0aec0f4015601a0 0x1d7f018003380781 0x8ebf80c0019c03c0

def z1007 : W := mkw 0x004d80b012ec2509 0x8026c05809761284 0xffff8fb033ffff99 0xffffc7d819ffffcc

def z1008 : W := mkw 0x228336b1b9596599 0x91419b58dcacb2cc 0xdf8777b3bf796799 0xefc3bbd9dfbcb3cc

def z1009 : W := mkw 0x308334b5b55b6dbb 0x98419a5adaadb6dd 0xff87ffffff7f7f99 0xffc3ffffffbfbfcc

def z1010 : W := mkw 0x815c814c02a60260 0x40ae40a601530130 0x7dff81cc03fe07e1 0xbeffc0e601ff03f0

def z1011 : W := mkw 0x006efe0003b5d000 0x00377f0001dae800 0xf9fffe4c4ffff801 0x7cffff2627fffc00

def z1012 : W := mkw 0x815d81e802ac0340 0xc0aec0f4015601a0 0x557f81bc03380380 0x2abfc0de019c01c0

def z1013 : W := mkw 0x308334a5a51b49b2 0x98419a52d28da4d9 0x3507fbcfcfbe9be6 0x1a83fde7e7df4df3

def z1014 : W := mkw 0x208334b5b15b65b9 0x90419a5ad8adb2dc 0xdf8775b3b3ff67f9 0xefc3bad9d9ffb3fc

def z1015 : W := mkw 0x935d81ff7eee2f6b 0xc9aec0ffbf7717b5 0xffff8fffffffffff 0xffffc7ffffffffff

def z1016 : W := mkw 0x815d81fc02ee0761 0xc0aec0fe017703b0 0x7dff818003fe07e1 0x3effc0c001ff03f0

def z1017 : W := mkw 0x001101f000480501 0x800880f800240280 0x7dff01f003780781 0xbeff80f801bc03c0

def z1018 : W := mkw 0x22f7efeb68184100 0x917bf7f5b40c2080 0xfe7ffffffc380000 0xff3ffffffe1c0000

def z1019 : W := mkw 0x004eb40003b54000 0x00275a0001daa000 0xf9fffe0003fff801 0x7cffff0001fffc00

def z1020 : W := mkw 0x208334b1b1596599 0x90419a58d8acb2cc 0x5d8771b383796799 0xaec3b8d9c1bcb3cc

def z1021 : W := mkw 0x4277efeb68008004 0x213bf7f5b4004002 0xfe7ffffffc008006 0xff3ffffffe004003

def z1022 : W := mkw 0x208334b1b1596599 0x90419a58d8acb2cc 0xdf8775ffff796799 0xefc3baffffbcb3cc

def z1023 : W := mkw 0x815d81e802ac0340 0xc0aec0f4015601a0 0xbf7f09c043b987ff 0xdfbf84e021dcc3ff

def z1024 : W := mkw 0x308334b1b5596d9b 0x98419a58daacb6cd 0xdf8777b3bf797f99 0xefc3bbd9dfbcbfcc

def z1025 : W := mkw 0x60a27c13f151e49d 0x30513e09f8a8f24e 0xea807c73f0c1e47f 0xf5403e39f860f23f

def z1026 : W := mkw 0x208334a1a1194190 0x90419a50d08ca0c8 0xdf87758383796799 0xefc3bac1c1bcb3cc

def z1027 : W := mkw 0x815d81fc02ee0761 0xc0aec0fe017703b0 0x35ff81cc03fe07e1 0x1affc0e601ff03f0

def z1028 : W := mkw 0x208334a1a1194190 0x90419a50d08ca0c8 0x550775b3b3380380 0x2a83bad9d99c01c0

def z1029 : W := mkw 0x208334b5b15b65b9 0x90419a5ad8adb2dc 0xdf87f5bfb37f6799 0xefc3fadfd9bfb3cc

def z1030 : W := mkw 0x815d81e802ac0340 0xc0aec0f4015601a0 0x15ff018003fe0381 0x0aff80c001ff01c0

def z1031 : W := mkw 0x1000001414422c2b 0x0800000a0a211615 0x60808e7c7cc7fc7f 0x3040473e3e63fe3f

def z1032 : W := mkw 0x006efe0083b5d090 0x00377f0041dae848 0xfbfffe0383fff819 0x7dffff01c1fffc0c

def z1033 : W := mkw 0x406efe02c3b5d094 0x20377f0161dae84a 0xf9fffe0383fff801 0x7cffff01c1fffc00

def z1034 : W := mkw 0x406efe0003b5d244 0x20377f0001dae922 0xf9fffe0003fff867 0x7cffff0001fffc33

def z1035 : W := mkw 0x0277efeb68000000 0x013bf7f5b4000000 0xde7ff7bfbc000000 0xef3ffbdfde000000

def z1036 : W := mkw 0x0057a5e920000000 0x002bd2f490000000 0xfe7ffffffc000000 0xff3ffffffe000000

def z1037 : W := mkw 0x0277efeb68241000 0x013bf7f5b4120800 0xfe7ffffffc061800 0xff3ffffffe030c00

def z1038 : W := mkw 0x004c800002a40000 0x0026400001520000 0x79ff860003fe7801 0x3cffc30001ff3c00

def z1039 : W := mkw 0x22a27e03f911f098 0x11513f01fc88f84c 0x82007e03fc01f818 0x41003f01fe00fc0c

def z1040 : W := mkw 0x026efe036bb5d000 0x01377f01b5dae800 0xfbfffe7ffffff801 0xfdffff3ffffffc00

def z1041 : W := mkw 0x915d81fc16ee2f6b 0xc8aec0fe0b7717b5 0xfdff8ffc3fffffe1 0xfeffc7fe1ffffff0

def z1042 : W := mkw 0x30a27e15b553fcbb 0x18513f0adaa9fe5d 0xea80fe7ffcc7fc7f 0xf5407f3ffe63fe3f

def z1043 : W := mkw 0x208334b1b1596599 0x90419a58d8acb2cc 0x97877583b3796799 0x4bc3bac1d9bcb3cc

def z1044 : W := mkw 0x915d81fc06ee0f63 0xc8aec0fe037707b1 0xffff8ffc7ffe9fe7 0xffffc7fe3fff4ff3

def z1045 : W := mkw 0x814c801402ee0761 0xc0a6400a017703b0 0x79ff807c03fe07e1 0xbcffc03e01ff03f0

def z1046 : W := mkw 0x40385942c38182d4 0x201c2ca161c0c16a 0xff787df3f38187ff 0xffbc3ef9f9c0c3ff

def z1047 : W := mkw 0x817cc94e42a60260 0x40be64a721530130 0x2078884c40860060 0x103c442620430030

def z1048 : W := mkw 0x208334b1b1596599 0x90419a58d8acb2cc 0x9f87718383796799 0xcfc3b8c1c1bcb3cc

def z1049 : W := mkw 0x208334b1b1596599 0x90419a58d8acb2cc 0x150771b3b3380380 0x0a83b8d9d99c01c0

def z1050 : W := mkw 0x815d81e802ac0340 0xc0aec0f4015601a0 0x5d7f01b003380380 0xaebf80d8019c01c0

def z1051 : W := mkw 0x0028580083818090 0x00142c0041c0c048 0xbf7879c3c38187ff 0xdfbc3ce1e1c0c3ff

def z1052 : W := mkw 0x208334a1a1194190 0x90419a50d08ca0c8 0x97077583b3380380 0x4b83bac1d99c01c0

def z1053 : W := mkw 0x914c801416ee2f6b 0xc8a6400a0b7717b5 0xfbff8e7c7fffffff 0xfdffc73e3fffffff

def z1054 : W := mkw 0x815d81e802ac0340 0xc0aec0f4015601a0 0x7d7f81fc03b807e1 0xbebfc0fe01dc03f0

def z1055 : W := mkw 0x026efe024bb5d000 0x01377f0125dae800 0xf9fffe004ffff801 0x7cffff0027fffc00

def z1056 : W := mkw 0x40227e02c111d094 0x20113f016088e84a 0x80007e038001f800 0x40003f01c000fc00

def z1057 : W := mkw 0x208334b1b1596599 0x90419a58d8acb2cc 0xdf8775b3b3ffff99 0xefc3bad9d9ffffcc

def z1058 : W := mkw 0x815c815c02ee0761 0xc0ae40ae017703b0 0x79ff804c03fe07e1 0x3cffc02601ff03f0

def z1059 : W := mkw 0x004eb60003b55000 0x00275b0001daa800 0xf9fff60003ff7801 0x7cfffb0001ffbc00

def z1060 : W := mkw 0x0277efeb68000000 0x013bf7f5b4000000 0x747ffffffc000000 0x3a3ffffffe000000

def z1061 : W := mkw 0x406efe02c3b5d2d4 0x20377f0161dae96a 0xfbfffe03c3ffffff 0x7dffff01e1ffffff

def z1062 : W := mkw 0x329101fffc4a2dbb 0x994880fffe2516dd 0x060001fffc0007fe 0x830000fffe0003ff

def z1063 : W := mkw 0x814d80bc02ee0761 0xc0a6c05e017703b0 0x79ff803c03fe07e1 0x3cffc01e01ff03f0

def z1064 : W := mkw 0x0002340081114090 0x00011a004088a048 0xdd87758383796381 0x6ec3bac1c1bcb1c0

def z1065 : W := mkw 0x60a27e03f111f09c 0x30513f01f888f84e 0x82007e03f001f81e 0x41003f01f800fc0f

def z1066 : W := mkw 0x815d81f802ec0741 0xc0aec0fc017603a0 0x157f01b003380780 0x8abf80d8019c03c0

def z1067 : W := mkw 0x815d81e802ac0340 0xc0aec0f4015601a0 0x3d7f018003b80381 0x1ebf80c001dc01c0

def z1068 : W := mkw 0x62a27e03f911e09c 0x31513f01fc88f04e 0x82007e03fc01e01e 0x41003f01fe00f00f

def z1069 : W := mkw 0x001901e002880340 0x800c80f0014401a0 0x3d7f01c003b807e1 0x9ebf80e001dc03f0

def z1070 : W := mkw 0x006efe0083b5d090 0x00377f0041dae848 0xfdffff8383fffb81 0x7effffc1c1fffdc0

def z1071 : W := mkw 0x40385942c38182d4 0x201c2ca161c0c16a 0xbf78fbcfcf8187ff 0xdfbc7de7e7c0c3ff

def z1072 : W := mkw 0x406efe0243b5d004 0x20377f0121dae802 0xf9fffe0043fff807 0x7cffff0021fffc03

def z1073 : W := mkw 0x006efe0003b5d240 0x00377f0001dae920 0xf9fffe0003ffffe1 0x7cffff0001fffff0

def z1074 : W := mkw 0x208334a1a1194190 0x90419a50d08ca0c8 0x1707718383380798 0x8b83b8c1c19c03cc

def z1075 : W := mkw 0x208334a1b1196198 0x90419a50d88cb0cc 0xdf0775b3b3396398 0xef83bad9d99cb1cc

def z1076 : W := mkw 0x915d81fc06ee0f63 0xc8aec0fe037707b1 0x7dff83fc0ffe1fe1 0xbeffc1fe07ff0ff0

def z1077 : W := mkw 0x006efe0003b5d000 0x00377f0001dae800 0xd1fffe00037ff800 0x68ffff0001bffc00

def z1078 : W := mkw 0x308334b5b55b6dbb 0x98419a5adaadb6dd 0xdf8775b3b37967ff 0xefc3bad9d9bcb3ff

def z1079 : W := mkw 0x208334b1b1596599 0x90419a58d8acb2cc 0x558775b3b3796799 0x2ac3bad9d9bcb3cc

def z1080 : W := mkw 0x837ccb4a4aa40240 0x41be65a525520120 0x0078000000000000 0x003c000000000000

def z1081 : W := mkw 0x815d81fc02ee0761 0xc0aec0fe017703b0 0x7fff81fc7ffe07e1 0xbfffc0fe3fff03f0

def z1082 : W := mkw 0x935d81ff7eee2f6b 0xc9aec0ffbf7717b5 0x7fff81fffffe07ff 0xbfffc0ffffff03ff

def z1083 : W := mkw 0x006efe0243b5d000 0x00377f0121dae800 0xfbfffe03c3fff801 0x7dffff01e1fffc00

def z1084 : W := mkw 0x815d81fc02ee0761 0xc0aec0fe017703b0 0xffff8ffc7fffffe1 0xffffc7fe3ffffff0

def z1085 : W := mkw 0x40385942c38182d4 0x201c2ca161c0c16a 0x9f7871c3c30107ff 0xcfbc38e1e18083ff

def z1086 : W := mkw 0x40385942c3b5d2d4 0x201c2ca161dae96a 0xfff8ffc3c3ffffff 0xfffc7fe1e1ffffff

def z1087 : W := mkw 0x0018014002800240 0x000c00a001400120 0x7dff01c003f807e1 0xbeff80e001fc03f0

def z1088 : W := mkw 0x815d81fc02ee0761 0xc0aec0fe017703b0 0x15ff0180037e0380 0x0aff80c001bf01c0

def z1089 : W := mkw 0x208334b1b1596599 0x90419a58d8acb2cc 0xff87ffb3b3796799 0xffc3ffd9d9bcb3cc

def z1090 : W := mkw 0x40385942c38182d4 0x201c2ca161c0c16a 0xbff879c3c3c7ffff 0xdffc3ce1e1e3ffff

def z1091 : W := mkw 0x006efe0003b5d000 0x00377f0001dae800 0xffffff8383fff801 0xffffffc1c1fffc00

def z1092 : W := mkw 0x208334b1a1594591 0x90419a58d0aca2c8 0xdf8771b383790799 0xefc3b8d9c1bc83cc

def z1093 : W := mkw 0x005c814002a40240 0x002e40a001520120 0x3d7f01c003b807e1 0x9ebf80e001dc03f0

def z1094 : W := mkw 0x0277efeb68000000 0x013bf7f5b4000000 0x147f71bfbc000000 0x0a3fb8dfde000000

def z1095 : W := mkw 0x40227e02c111d094 0x20113f016088e84a 0xea80fe43c0c7fc7f 0xf5407f21e063fe3f

def z1096 : W := mkw 0x20a27c03f1116098 0x10513e01f888b04c 0x82007c03f0016018 0x41003e01f800b00c

def z1097 : W := mkw 0x000110b4814b05b1 0x8000885a40a582d8 0xff87f9ffc3ff87ff 0xffc3fcffe1ffc3ff

def z1098 : W := mkw 0x001901e002880340 0x800c80f0014401a0 0x157f018003380380 0x0abf80c0019c01c0

def z1099 : W := mkw 0x1000001414422c2b 0x0800000a0a211615 0xfb878e7c7ffffc7f 0xfdc3c73e3ffffe3f

def z1100 : W := mkw 0x0000100081010090 0x0000080040808048 0xdf87718383790799 0xefc3b8c1c1bc83cc

def z1101 : W := mkw 0x427ccb4a4aa49244 0x213e65a525524922 0x20788a4c4c869866 0x103c452626434c33

def z1102 : W := mkw 0x40285800838182d4 0x20142c0041c0c16a 0xbf787983838187ff 0xdfbc3cc1c1c0c3ff

def z1103 : W := mkw 0x208334b1a1594591 0x90419a58d0aca2c8 0xdd8775b383796781 0xeec3bad9c1bcb3c0

def z1104 : W := mkw 0x208334b1b1596599 0x90419a58d8acb2cc 0xff87fff3f3ffffff 0xffc3fff9f9ffffff

def z1105 : W := mkw 0x0038494242800240 0x001c24a121400120 0xbf7879c3c38187ff 0xdfbc3ce1e1c0c3ff

def z1106 : W := mkw 0x1002341495536cbb 0x08011a0a4aa9b65d 0xff87ffffffffffff 0xffc3ffffffffffff

def z1107 : W := mkw 0x815d81fc02ee0761 0xc0aec0fe017703b0 0x7dff8bfc03fe9fe1 0xbeffc5fe01ff4ff0

def z1108 : W := mkw 0x001901f002c80741 0x800c80f8016403a0 0x5dff01b003780781 0xaeff80d801bc03c0

def z1109 : W := mkw 0x308334b5b55b6dbb 0x98419a5adaadb6dd 0xff877df3f3ffffff 0xffc3bef9f9ffffff

def z1110 : W := mkw 0x915d81fc16ee2f6b 0xc8aec0fe0b7717b5 0x7dff81fc3ffe07e1 0xbeffc0fe1fff03f0

def z1111 : W := mkw 0x004c900003b5d000 0x0026480001dae800 0xf9ff8e0003fff801 0x7cffc70001fffc00

def z1112 : W := mkw 0x208334b1b1596599 0x90419a58d8acb2cc 0xdf8775b3b3786380 0xefc3bad9d9bc31c0

def z1113 : W := mkw 0x709101f7f44a2fff 0xb84880fbfa2517ff 0x060001fffc0007fe 0x830000fffe0003ff

def z1114 : W := mkw 0x815581fc004a0761 0xc0aac0fe002503b0 0x7dff81fc037807e1 0xbeffc0fe01bc03f0

def z1115 : W := mkw 0x42227e03e911d094 0x21113f01f488e84a 0x82007e03fc01f81e 0x41003f01fe00fc0f

def z1116 : W := mkw 0x004d80a002ac0100 0x8026c05001560080 0x157f018003380380 0x0abf80c0019c01c0

def z1117 : W := mkw 0x815d81fc02ee0761 0xc0aec0fe017703b0 0x7d7f81fc033807e0 0xbebfc0fe019c03f0

def z1118 : W := mkw 0x815d81fc02ee0761 0xc0aec0fe017703b0 0x7dff8bfc4ffe07e1 0xbeffc5fe27ff03f0

def z1119 : W := mkw 0x308334b5b55b6dbb 0x98419a5adaadb6dd 0xdf877fb3ffffffff 0xefc3bfd9ffffffff

def z1120 : W := mkw 0x8377efeb68080340 0xc1bbf7f5b40401a0 0xfe7ffffffc000380 0xff3ffffffe0001c0

def z1121 : W := mkw 0x40385942c38182d4 0x201c2ca161c0c16a 0xbf787fc3ff8187ff 0xdfbc3fe1ffc0c3ff

def z1122 : W := mkw 0x004d80b002ec0501 0x8026c05801760280 0x5dff01b003780781 0xaeff80d801bc03c0

def z1123 : W := mkw 0x0002340081114090 0x00011a004088a048 0x1507718383380380 0x0a83b8c1c19c01c0

def z1124 : W := mkw 0x815d81fc02ee0761 0xc0aec0fe017703b0 0xffff89fc43fe07e1 0xffffc4fe21ff03f0

def z1125 : W := mkw 0x308334b1b5596d9b 0x98419a58daacb6cd 0xdf8775b3b379ff9f 0xefc3bad9d9bcffcf

def z1126 : W := mkw 0x815d81e802ac0340 0xc0aec0f4015601a0 0x157f01fc03380380 0x8abf80fe019c01c0

def z1127 : W := mkw 0x208334b5b15b65b9 0x90419a5ad8adb2dc 0xff87ffffb3fffff9 0xffc3ffffd9fffffc

def z1128 : W := mkw 0x006efe0003b5d000 0x00377f0001dae800 0x79fff60003fe7801 0x3cfffb0001ff3c00

def z1129 : W := mkw 0x406efe02c3b5d094 0x20377f0161dae84a 0xfbfffe43c3fffc7f 0xfdffff21e1fffe3f

def z1130 : W := mkw 0x40385942c38182d4 0x201c2ca161c0c16a 0x3f7871c3c38007ff 0x9fbc38e1e1c003ff

def z1131 : W := mkw 0x815d81fc02ee0761 0xc0aec0fe017703b0 0x3dff01c003fe07e1 0x9eff80e001ff03f0

def z1132 : W := mkw 0x308334b5b55b6dbb 0x98419a5adaadb6dd 0xdf87ffbfff7fff9f 0xefc3ffdfffbfffcf

def z1133 : W := mkw 0x40385942c38182d4 0x201c2ca161c0c16a 0x3d7871c3838187ff 0x9ebc38e1c1c0c3ff

def z1134 : W := mkw 0x815d81fc02ee0761 0xc0aec0fe017703b0 0x75ff81fc03fe03e0 0x3affc0fe01ff01f0

def z1135 : W := mkw 0x006cda0003b5d000 0x00366d0001dae800 0x79ff8a0003fff801 0x3cffc50001fffc00

def z1136 : W := mkw 0x915d81fc16ee2f6b 0xc8aec0fe0b7717b5 0x55ff87bc3f7e7b80 0x2affc3de1fbf3dc0

def z1137 : W := mkw 0x006efe0003b5d000 0x00377f0001dae800 0xd9ff740003fff801 0x6cffba0001fffc00

def z1138 : W := mkw 0xc17ccb4e42a69264 0x60be65a721534932 0x20788a4c40869866 0x103c452620434c33

def z1139 : W := mkw 0xc37ccb4e4aa68264 0x61be65a725534132 0x20788a4c4c868066 0x103c452626434033

def z1140 : W := mkw 0x815d81e802ac0340 0xc0aec0f4015601a0 0x7dff81fc03fe0381 0xbeffc0fe01ff01c0

def z1141 : W := mkw 0x40385942c3a592d4 0x201c2ca161d2c96a 0xbf7879c3c3879fff 0xdfbc3ce1e1c3cfff

def z1142 : W := mkw 0x20a27e01b111f098 0x10513f00d888f84c 0x82007403b0016018 0x41003a01d800b00c

def z1143 : W := mkw 0x0002340081114090 0x00011a004088a048 0x9f07718383390799 0xcf83b8c1c19c83cc

def z1144 : W := mkw 0x308334b1b5596d9b 0x98419a58daacb6cd 0xdf8775b3ff79679f 0xefc3bad9ffbcb3cf

def z1145 : W := mkw 0x208334b5b15b65b9 0x90419a5ad8adb2dc 0xff87ffffffff67f9 0xffc3ffffffffb3fc

def z1146 : W := mkw 0x1000001414422c2b 0x0800000a0a211615 0xe2808e7c7cc7f87e 0x7140473e3e63fc3f

def z1147 : W := mkw 0x40385942c3a582d4 0x201c2ca161d2c16a 0xbff879c3c3ff87ff 0xdffc3ce1e1ffc3ff

def z1148 : W := mkw 0x40385942c391d2d4 0x201c2ca161c8e96a 0xbf7879c3c381ffff 0xdfbc3ce1e1c0ffff

def z1149 : W := mkw 0x006efe0003b5d000 0x00377f0001dae800 0xfbfffe007ffff801 0x7dffff003ffffc00

def z1150 : W := mkw 0x0277efeb68000000 0x013bf7f5b4000000 0xfe7ffffffc800461 0xff3ffffffe400230

def z1151 : W := mkw 0x4277efeb68000244 0x213bf7f5b4000122 0xfe7ffffffc000066 0xff3ffffffe000033

def z1152 : W := mkw 0x815d81f802ec0741 0xc0aec0fc017603a0 0x7dff81b003fe0781 0xbeffc0d801ff03c0

def z1153 : W := mkw 0x208334b1a1594591 0x90419a58d0aca2c8 0x150771b383380780 0x8a83b8d9c19c03c0

def z1154 : W := mkw 0x815d81fc02ee0761 0xc0aec0fe017703b0 0xffff85fc33fe07e1 0xffffc2fe19ff03f0

def z1155 : W := mkw 0x006efe0003b5d000 0x00377f0001dae800 0xf9fffe7c03fff801 0xfcffff3e01fffc00

def z1156 : W := mkw 0x0002340081114090 0x00011a004088a048 0xff87ffc3c3ffffff 0xffc3ffe1e1ffffff

def z1157 : W := mkw 0xd108101497efafff 0xe884080a4bf7d7ff 0x0180000003ffffff 0x00c0000001ffffff

def z1158 : W := mkw 0x208334a1a1194190 0x90419a50d08ca0c8 0xdf8775b3b3796381 0xefc3bad9d9bcb1c0

def z1159 : W := mkw 0x40384942c28082d4 0x201c24a16140416a 0xbe7879c3c08087fe 0xdf3c3ce1e04043ff

def z1160 : W := mkw 0x000324b5204a0521 0x8001925a90250290 0xff87fffffffe07e1 0xffc3ffffffff03f0

def z1161 : W := mkw 0x40385942c38182d4 0x201c2ca161c0c16a 0xbf78fbc3c3879fff 0xdfbc7de1e1c3cfff

def z1162 : W := mkw 0x40385942c391c2d4 0x201c2ca161c8e16a 0xbff879c3c3f9e7ff 0xdffc3ce1e1fcf3ff

def z1163 : W := mkw 0x004580b000480501 0x8022c05800240280 0x7dff81b003780781 0xbeffc0d801bc03c0

def z1164 : W := mkw 0x40385942c38182d4 0x201c2ca161c0c16a 0x357879c3c38187ff 0x1abc3ce1e1c0c3ff

def z1165 : W := mkw 0x937ccb4e4ea60a62 0x49be65a727530531 0x20788a4c4c869866 0x103c452626434c33

def z1166 : W := mkw 0x40385942c38182d4 0x201c2ca161c0c16a 0xfff8ffffffc7ffff 0xfffc7fffffe3ffff

def z1167 : W := mkw 0x004c801002ec0501 0x8026400801760280 0x79ff800003fe0781 0x3cffc00001ff03c0

def z1168 : W := mkw 0x835d81fe4aee0761 0xc1aec0ff257703b0 0x7dff81fc4ffe07e1 0xbeffc0fe27ff03f0

def z1169 : W := mkw 0x0277efeb68000000 0x013bf7f5b4000000 0xfe7ffffffc808066 0xff3ffffffe404033

def z1170 : W := mkw 0x208334b1b1596599 0x90419a58d8acb2cc 0xdf87f7bfbf796799 0xefc3fbdfdfbcb3cc

def z1171 : W := mkw 0x20a27e01a111d090 0x10513f00d088e848 0x0000700380000000 0x00003801c0000000

def z1172 : W := mkw 0x40227e02c111d094 0x20113f016088e84a 0x0000700380000000 0x00003801c0000000

def z1173 : W := mkw 0x835d81eb6aac0340 0xc1aec0f5b55601a0 0x157f018383380380 0x0abf80c1c19c01c0

def z1174 : W := mkw 0x308334b5b55b6dbb 0x98419a5adaadb6dd 0xdf8775bfbf796799 0xefc3badfdfbcb3cc

def z1175 : W := mkw 0x005c814002a40240 0x002e40a001520120 0x7dff818003fe0381 0x3effc0c001ff01c0

def z1176 : W := mkw 0x915d81fc16ee2f6b 0xc8aec0fe0b7717b5 0x7dff8ffc7ffeffe7 0xbeffc7fe3fff7ff3

def z1177 : W := mkw 0x70a27c17f553ecbf 0x38513e0bfaa9f65f 0xea80fe7ffcc7fc7f 0xf5407f3ffe63fe3f

def z1178 : W := mkw 0x004c900003b5d000 0x0026480001dae800 0x11ff000003fff801 0x08ff800001fffc00

def z1179 : W := mkw 0x815d81fc02ee0761 0xc0aec0fe017703b0 0x5dff01fc037807e1 0xaeff80fe01bc03f0

def z1180 : W := mkw 0x0277efeb68000240 0x013bf7f5b4000120 0xfe7ffffffc0007e0 0xff3ffffffe0003f0

def z1181 : W := mkw 0x915d81fc16ee2f6b 0xc8aec0fe0b7717b5 0x7fff8bfc7ffe9fff 0xbfffc5fe3fff4fff

def z1182 : W := mkw 0x308334b5b55b6dbb 0x98419a5adaadb6dd 0xdf8775ffffffffff 0xefc3baffffffffff

def z1183 : W := mkw 0x5008101497f7feff 0x2804080a4bfbff7f 0x0180000003ffffff 0x00c0000001ffffff

def z1184 : W := mkw 0x208334a1a1194190 0x90419a50d08ca0c8 0x1d07718383380781 0x8e83b8c1c19c03c0

def z1185 : W := mkw 0x815d81fc02ee0761 0xc0aec0fe017703b0 0xfdff8ffc03fe07e1 0xfeffc7fe01ff03f0

def z1186 : W := mkw 0x101901f416ca2f6b 0x880c80fa0b6517b5 0xffff8ffc7fffffff 0xffffc7fe3fffffff

def z1187 : W := mkw 0xd17cc95e56e6ae6f 0x68be64af2b735737 0xeaf88e7c7cc7fc7f 0xf57c473e3e63fe3f

def z1188 : W := mkw 0x0277efeb68000000 0x013bf7f5b4000000 0xe27ffe7ffc000000 0x713fff3ffe000000

def z1189 : W := mkw 0x815d81e802ac0340 0xc0aec0f4015601a0 0x55ff8180037e0380 0x2affc0c001bf01c0

def z1190 : W := mkw 0x815d81fc02ee0761 0xc0aec0fe017703b0 0xfdff89fc03ff87e1 0xfeffc4fe01ffc3f0

def z1191 : W := mkw 0x815d81ec02ae0360 0xc0aec0f6015701b0 0x157f018003be03e0 0x0abf80c001df01f0

def z1192 : W := mkw 0x004eb40003b5d000 0x00275a0001dae800 0xf9fff40003fff801 0x7cfffa0001fffc00

def z1193 : W := mkw 0x1030495654422c2b 0x081824ab2a211615 0xbef879c3c0c7fc7f 0xdf7c3ce1e063fe3f

def z1194 : W := mkw 0x005581e800080100 0x802ac0f400040080 0x157f018003380380 0x0abf80c0019c01c0

def z1195 : W := mkw 0x006efe0003b5d000 0x00377f0001dae800 0xfbfffe0043fff81f 0x7dffff0021fffc0f

def z1196 : W := mkw 0x815d81f812ec2749 0xc0aec0fc097613a4 0xdfff05b033796799 0xefff82d819bcb3cc

def z1197 : W := mkw 0x815d81ec02ae0360 0xc0aec0f6015701b0 0x3d7f81cc03be07e1 0x9ebfc0e601df03f0

def z1198 : W := mkw 0x0277efeb68000000 0x013bf7f5b4000000 0xa678fffffc000000 0xd33c7ffffe000000

def z1199 : W := mkw 0x100000041402282a 0x080000020a011415 0xea008e7c7c87f87e 0xf500473e3e43fc3f

def z1200 : W := mkw 0x1000001414422c2b 0x0800000a0a211615 0xff808ffc7fc7ffff 0xffc047fe3fe3ffff

def z1201 : W := mkw 0x50227e16d553fcbf 0x28113f0b6aa9fe5f 0xea80fe7ffcc7fc7f 0xf5407f3ffe63fe3f

def z1202 : W := mkw 0x0277efeb68000000 0x013bf7f5b4000000 0xd67fffbffc000000 0x6b3fffdffe000000

def z1203 : W := mkw 0x208324b1b0482599 0x90419258d82412cc 0xdf8775b3b3780799 0xefc3bad9d9bc03cc

def z1204 : W := mkw 0x208334b1b1596599 0x90419a58d8acb2cc 0x578775b3b3786798 0xabc3bad9d9bc33cc

def z1205 : W := mkw 0x915d81fc16ee2f6b 0xc8aec0fe0b7717b5 0xffff89fc7fff87ff 0xffffc4fe3fffc3ff

def z1206 : W := mkw 0x005581f800480501 0x802ac0fc00240280 0x5dff01b003780781 0xaeff80d801bc03c0

def z1207 : W := mkw 0x915d81fc16ee2f6b 0xc8aec0fe0b7717b5 0xffff87fc3fff7ff9 0xffffc3fe1fffbffc

def z1208 : W := mkw 0x815d81fc02ee0761 0xc0aec0fe017703b0 0x7dff81fc037e0380 0xbeffc0fe01bf01c0

def z1209 : W := mkw 0x006efe0003b5d000 0x00377f0001dae800 0xf9fffe4003fffc61 0xfcffff2001fffe30

def z1210 : W := mkw 0x40385942c3b5d2d4 0x201c2ca161dae96a 0xbf7879c3c3b987ff 0xdfbc3ce1e1dcc3ff

def z1211 : W := mkw 0x208334a1a1194190 0x90419a50d08ca0c8 0x170771b3b3380380 0x8b83b8d9d99c01c0

def z1212 : W := mkw 0x507ccb4646a69a66 0x283e65a323534d33 0x20788a4c4c869866 0x103c452626434c33

def z1213 : W := mkw 0x814c800002ac0340 0xc0a64000015601a0 0x117f000003380380 0x08bf8000019c01c0

def z1214 : W := mkw 0x208334b1b1596599 0x90419a58d8acb2cc 0xff8775f3b3f967f9 0xffc3baf9d9fcb3fc

def z1215 : W := mkw 0x815d81fc02ee0761 0xc0aec0fe017703b0 0x7dff87fc3ffe07e1 0xbeffc3fe1fff03f0

def z1216 : W := mkw 0x006efe0003b5d000 0x00377f0001dae800 0x79fff00003fff801 0x3cfff80001fffc00

def z1217 : W := mkw 0x000110b081490591 0x8000885840a482c8 0x5d8771b383780781 0xaec3b8d9c1bc03c0

def z1218 : W := mkw 0x308334b5b55b6dbb 0x98419a5adaadb6dd 0xff87ffffff7967ff 0xffc3ffffffbcb3ff

def z1219 : W := mkw 0x815d81e802ac0340 0xc0aec0f4015601a0 0x157f01c0033807e0 0x8abf80e0019c03f0

def z1220 : W := mkw 0x915d81fc06ee0f63 0xc8aec0fe037707b1 0x7dff81fc03fe9fe7 0xbeffc0fe01ff4ff3

def z1221 : W := mkw 0x005581f810482509 0x802ac0fc08241284 0xffff8ffc7f796799 0xffffc7fe3fbcb3cc

def z1222 : W := mkw 0x006efe0003b5d000 0x00377f0001dae800 0xb9ff780003fff801 0x5cffbc0001fffc00

def z1223 : W := mkw 0x815d81fc12ee2769 0xc0aec0fe097713b4 0xffff8ffc33fffff9 0xffffc7fe19fffffc

def z1224 : W := mkw 0xd11101fed44a2fff 0xe88880ff6a2517ff 0x060001fffc0007fe 0x830000fffe0003ff

def z1225 : W := mkw 0x815d81ec02ae0360 0xc0aec0f6015701b0 0x157f818c033e0380 0x0abfc0c6019f01c0

def z1226 : W := mkw 0x915d81fc16ee2f6b 0xc8aec0fe0b7717b5 0x7dff81fc03fe7fe1 0xbeffc0fe01ff3ff0

def z1227 : W := mkw 0x407ccb4242a49244 0x203e65a121524922 0x2078084040808066 0x103c042020404033

def z1228 : W := mkw 0x208334b1b1596599 0x90419a58d8acb2cc 0xff87f5ffb3796799 0xffc3faffd9bcb3cc

def z1229 : W := mkw 0x814c800002ac0340 0xc0a64000015601a0 0x79ff800003fe0381 0x3cffc00001ff01c0

def z1230 : W := mkw 0x0277efeb68104000 0x013bf7f5b4082000 0xfefffffffc786000 0xff7ffffffe3c3000

def z1231 : W := mkw 0x40385942c38182d4 0x201c2ca161c0c16a 0xbf7879c3c30007fe 0xdfbc3ce1e18003ff

def z1232 : W := mkw 0x815d81e802ac0340 0xc0aec0f4015601a0 0x7d7f818003380380 0x3ebfc0c0019c01c0

def z1233 : W := mkw 0x815d81fe42ee0761 0xc0aec0ff217703b0 0x7fff81ffc3fe07e1 0xbfffc0ffe1ff03f0

def z1234 : W := mkw 0x000100b000480501 0x8000805800240280 0xdf8771b383780781 0xefc3b8d9c1bc03c0

def z1235 : W := mkw 0x815d81e802ac0340 0xc0aec0f4015601a0 0x7dff81c003fe07e1 0xbeffc0e001ff03f0

def z1236 : W := mkw 0x815d81fc02ee0761 0xc0aec0fe017703b0 0xfffff1ff83fe07e1 0xfffff8ffc1ff03f0

def z1237 : W := mkw 0x208334a1b1196198 0x90419a50d88cb0cc 0x9f077583b3396799 0xcf83bac1d99cb3cc

def z1238 : W := mkw 0x4238594acb8182d4 0x211c2ca565c0c16a 0xbf7879cfcf8187ff 0xdfbc3ce7e7c0c3ff

def z1239 : W := mkw 0x208334a1b1196198 0x90419a50d88cb0cc 0x1507718383396398 0x0a83b8c1c19cb1cc

def z1240 : W := mkw 0x023149eb68000000 0x0118a4f5b4000000 0xfe78fffffc000000 0xff3c7ffffe000000

def z1241 : W := mkw 0x0277efeb68000000 0x013bf7f5b4000000 0xfe7ffffffc818001 0xff3ffffffe40c000

def z1242 : W := mkw 0x915d81fc06ee0f63 0xc8aec0fe037707b1 0xfdff8ffc4fffffe7 0xfeffc7fe27fffff3

def z1243 : W := mkw 0x0000000000000000 0x0000000000000000 0xea808e7c7cc7fc7f 0xf540473e3e63fe3f

def z1244 : W := mkw 0x1000001414422c2b 0x0800000a0a211615 0xfe80fffffcc7fc7f 0xff407ffffe63fe3f

def z1245 : W := mkw 0x208334a1a1194190 0x90419a50d08ca0c8 0x1587718383796381 0x0ac3b8c1c1bcb1c0

def z1246 : W := mkw 0x0066ee0000345000 0x00337700001a2800 0x50fff600007e7800 0x287ffb00003f3c00

def z1247 : W := mkw 0x0277efeb68009000 0x013bf7f5b4004800 0xfe7ffffffc009800 0xff3ffffffe004c00

def z1248 : W := mkw 0x40385942c38182d4 0x201c2ca161c0c16a 0xfff87dc3c3c1e7ff 0xfffc3ee1e1e0f3ff

def z1249 : W := mkw 0x915d81fc06ee0f63 0xc8aec0fe037707b1 0xffff8bfc4fff9fff 0xffffc5fe27ffcfff

def z1250 : W := mkw 0x208334a1a1194190 0x90419a50d08ca0c8 0x5587758383786380 0x2ac3bac1c1bc31c0

def z1251 : W := mkw 0x208334a1a1194190 0x90419a50d08ca0c8 0x9507758383396380 0x4a83bac1c19cb1c0

def z1252 : W := mkw 0x40385942c38182d4 0x201c2ca161c0c16a 0x15787183830007fe 0x0abc38c1c18003ff

def z1253 : W := mkw 0x208324b130586509 0x90419258982c3284 0xdf8775b3b3786781 0xefc3bad9d9bc33c0

def z1254 : W := mkw 0x40385942c38182d4 0x201c2ca161c0c16a 0xbd787983838187ff 0x5ebc3cc1c1c0c3ff

def z1255 : W := mkw 0xa18334bdb15b65b9 0xd0c19a5ed8adb2dc 0xdf8775bfb3796799 0xefc3badfd9bcb3cc

def z1256 : W := mkw 0x004c800002b45000 0x00264000015a2800 0x79ff800003fe7801 0x3cffc00001ff3c00

def z1257 : W := mkw 0x40385942c38182d4 0x201c2ca161c0c16a 0xffff79c3c3f987ff 0xffffbce1e1fcc3ff

def z1258 : W := mkw 0x000334b121594501 0x80019a5890aca280 0xdf8775b3b3796781 0xefc3bad9d9bcb3c0

def z1259 : W := mkw 0x308334b1b5596d9b 0x98419a58daacb6cd 0xff877ff3fff9ffff 0xffc3bff9fffcffff

def z1260 : W := mkw 0x0075c9ea40000000 0x003ae4f520000000 0xfe7ffffffc000000 0xff3ffffffe000000

def z1261 : W := mkw 0x000334a1a1114090 0x00019a50d088a048 0xdf8775b3b3796799 0xefc3bad9d9bcb3cc

def z1262 : W := mkw 0x026efe036bb5d000 0x01377f01b5dae800 0xf9fffe0383fff801 0x7cffff01c1fffc00

def z1263 : W := mkw 0x208334b5b15b65b9 0x90419a5ad8adb2dc 0xff87fdfff3ffe7ff 0xffc3fefff9fff3ff

def z1264 : W := mkw 0x308334b5b55b6dbb 0x98419a5adaadb6dd 0xff87ffb3b3ffffff 0xffc3ffd9d9ffffff

def z1265 : W := mkw 0x005d81e802a40240 0x002ec0f401520120 0x7dff81fc03fe07e1 0xbeffc0fe01ff03f0

def z1266 : W := mkw 0x0267eeab68000000 0x0133f755b4000000 0xfa7ffe3ffc000000 0x7d3fff1ffe000000

def z1267 : W := mkw 0x0277efeb68000000 0x013bf7f5b4000000 0xfefffffffc416001 0xff7ffffffe20b000

def z1268 : W := mkw 0x815d81fc02ee0761 0xc0aec0fe017703b0 0x7dff81fc03ffffe1 0xbeffc0fe01fffff0

def z1269 : W := mkw 0x308334b1b5596d9b 0x98419a58daacb6cd 0xff87ffffff79ff9f 0xffc3ffffffbcffcf

def z1270 : W := mkw 0x208334b1b1596599 0x90419a58d8acb2cc 0xff87ffffffffff99 0xffc3ffffffffffcc

def z1271 : W := mkw 0x208334b1b1596599 0x90419a58d8acb2cc 0xdf8775b3b3f9e7ff 0xefc3bad9d9fcf3ff

def z1272 : W := mkw 0x208334b1b1596599 0x90419a58d8acb2cc 0x1587718383786380 0x0ac3b8c1c1bc31c0

def z1273 : W := mkw 0x208334b1b1596599 0x90419a58d8acb2cc 0x178771b3b3796799 0x8bc3b8d9d9bcb3cc

def z1274 : W := mkw 0x915d81fc16ee2f6b 0xc8aec0fe0b7717b5 0xffff8ffc7ffe07ff 0xffffc7fe3fff03ff

def z1275 : W := mkw 0x0277efeb68000000 0x013bf7f5b4000000 0xfefffffffcc60001 0xff7ffffffe630000

def z1276 : W := mkw 0x815d81fc02ee0761 0xc0aec0fe017703b0 0x55ff81bc03fe07e1 0x2affc0de01ff03f0

def z1277 : W := mkw 0x837ccb4e4aa60260 0x41be65a725530130 0x2078804c00860060 0x103c402600430030

def z1278 : W := mkw 0xc15d81fc02ee8765 0xe0aec0fe017743b2 0x7dff81fc03fe87e7 0xbeffc0fe01ff43f3

def z1279 : W := mkw 0x006cd80003a58000 0x00366c0001d2c000 0xf9fffe0003fff801 0x7cffff0001fffc00

def z1280 : W := mkw 0x208334b1b1596599 0x90419a58d8acb2cc 0x970775b3b3396798 0xcb83bad9d99cb3cc

def z1281 : W := mkw 0x0066ee0000345000 0x00337700001a2800 0x60ff8e00007e7800 0x307fc700003f3c00

def z1282 : W := mkw 0x815d81e802ac0340 0xc0aec0f4015601a0 0x357f01c003b803e0 0x1abf80e001dc01f0

def z1283 : W := mkw 0x0277efeb68000000 0x013bf7f5b4000000 0x367ffbfffc000000 0x9b3ffdfffe000000

def z1284 : W := mkw 0x000110a081090190 0x80008850408480c8 0x1507718383380380 0x0a83b8c1c19c01c0

def z1285 : W := mkw 0x0277efeb68000000 0x013bf7f5b4000000 0x567ff7fffc000000 0xab3ffbfffe000000

def z1286 : W := mkw 0x0277efeb68000000 0x013bf7f5b4000000 0xfe7ffffffc00047e 0xff3ffffffe00023f

def z1287 : W := mkw 0x837ccb5e4ae60661 0x41be65af25730330 0xeaf88e7c7cc60461 0xf57c473e3e630230

def z1288 : W := mkw 0x208334b1b1596599 0x90419a58d8acb2cc 0xff87f5b3b3ff6799 0xffc3fad9d9ffb3cc

def z1289 : W := mkw 0x0076ef4240000000 0x003b77a120000000 0xfe7ffffffc000000 0xff3ffffffe000000

def z1290 : W := mkw 0x0002341091516499 0x00011a0848a8b24c 0xdf8775b3b3796799 0xefc3bad9d9bcb3cc

def z1291 : W := mkw 0x308334b5b55b6dbb 0x98419a5adaadb6dd 0xff87f7ffbfff7ff9 0xffc3fbffdfffbffc

def z1292 : W := mkw 0x0257a5eb68000000 0x012bd2f5b4000000 0xfe7ff5fffc000000 0xff3ffafffe000000

def z1293 : W := mkw 0x815d81fc12ee2769 0xc0aec0fe097713b4 0x7dff85fc33fe67e1 0xbeffc2fe19ff33f0

def z1294 : W := mkw 0x006efe0003b5d000 0x00377f0001dae800 0xfbfffe3033fff801 0xfdffff1819fffc00

def z1295 : W := mkw 0x02336feb68000000 0x0119b7f5b4000000 0xbe787ffffc000000 0xdf3c3ffffe000000

def z1296 : W := mkw 0x815d81fc12ee2769 0xc0aec0fe097713b4 0x7fff81fc33fe07f9 0xbfffc0fe19ff03fc

def z1297 : W := mkw 0x815d81e802ac0340 0xc0aec0f4015601a0 0xff7f8ffc7f380380 0xffbfc7fe3f9c01c0

def z1298 : W := mkw 0x0277efeb68000000 0x013bf7f5b4000000 0xfe7ffffffc01801e 0xff3ffffffe00c00f

def z1299 : W := mkw 0x40384942c28002d4 0x201c24a16140016a 0xbf7879c3c38007ff 0xdfbc3ce1e1c003ff

def z1300 : W := mkw 0x208334b1b1596599 0x90419a58d8acb2cc 0x5f8771b3b3780799 0xafc3b8d9d9bc03cc

def z1301 : W := mkw 0x006efe0003b5d000 0x00377f0001dae800 0x91ff7e0003fff801 0x48ffbf0001fffc00

def z1302 : W := mkw 0x40385942c38182d4 0x201c2ca161c0c16a 0xa67879c3c08187fe 0xd33c3ce1e040c3ff

def z1303 : W := mkw 0x22a27e13f9516499 0x11513f09fca8b24c 0xea80fe7ffc416419 0xf5407f3ffe20b20c

def z1304 : W := mkw 0x40385942c38182d4 0x201c2ca161c0c16a 0xff78ffc3c38187ff 0xffbc7fe1e1c0c3ff

def z1305 : W := mkw 0x815d81ec02ae0360 0xc0aec0f6015701b0 0x7d7f81fc03be03e0 0xbebfc0fe01df01f0

def z1306 : W := mkw 0x815d81fc02ee0761 0xc0aec0fe017703b0 0xffff8ffc7fff87ff 0xffffc7fe3fffc3ff

def z1307 : W := mkw 0x208110b091596599 0x9040885848acb2cc 0xdf8771b383796799 0xefc3b8d9c1bcb3cc

def z1308 : W := mkw 0x915d81fc06ee0f63 0xc8aec0fe037707b1 0x7dff81fc4ffe07e7 0xbeffc0fe27ff03f3

def z1309 : W := mkw 0x208334a1a1194190 0x90419a50d08ca0c8 0x9707718383390398 0x4b83b8c1c19c81cc

def z1310 : W := mkw 0x208334b1b1596599 0x90419a58d8acb2cc 0x5d8775b3b3786781 0xaec3bad9d9bc33c0

def z1311 : W := mkw 0x815d81e802ac0340 0xc0aec0f4015601a0 0x357f81cc03380380 0x1abfc0e6019c01c0

def z1312 : W := mkw 0x208334b1a1594591 0x90419a58d0aca2c8 0x558771b383780380 0x2ac3b8d9c1bc01c0

def z1313 : W := mkw 0x815d81fc12ee2769 0xc0aec0fe097713b4 0xffff8ffc7fff67f9 0xffffc7fe3fffb3fc

def z1314 : W := mkw 0x006efe0003b5d000 0x00377f0001dae800 0xd9fff600037f7801 0x6cfffb0001bfbc00

def z1315 : W := mkw 0x835d81eb6aac0340 0xc1aec0f5b55601a0 0x177f01ffff380380 0x8bbf80ffff9c01c0

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z0,z1,z2,z3,z5,z7,z6]),(0,[z0,z1,z2,z8,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z9,z6]),(0,[z10,z0,z1,z2,z3,z5,z11]),(0,[z10,z0,z1,z2,z12,z5,z6]),(0,[z13,z0,z1,z2,z3,z5,z6])],[(0,[z14,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z15,z5,z6]),(0,[z16,z0,z1,z2,z3,z5,z6]),(1,[z0,z1,z3,z5,z17,z18])],[(0,[z0,z1,z19,z2,z3,z5,z6]),(0,[z0,z20,z2,z21,z3,z5,z6]),(0,[z0,z1,z2,z22,z3,z5,z6]),(0,[z0,z1,z2,z23,z3,z5,z6]),(1,[z0,z1,z2,z24,z5,z6]),(0,[z0,z1,z25,z2,z12,z5,z6]),(0,[z0,z1,z2,z26,z12,z5,z6]),(0,[z27,z0,z1,z2,z12,z5,z6])],[(0,[z28,z0,z1,z2,z3,z5,z18]),(0,[z0,z1,z2,z29,z3,z5,z6]),(0,[z30,z0,z1,z2,z3,z5,z17]),(0,[z0,z1,z2,z24,z5,z31,z6]),(0,[z10,z0,z1,z2,z24,z5,z6]),(0,[z0,z1,z2,z3,z5,z18,z32]),(0,[z0,z1,z2,z3,z5,z33,z6])],[(0,[z0,z1,z34,z2,z12,z5,z6]),(0,[z0,z1,z2,z2,z3,z5,z18])],[(0,[z0,z35,z1,z2,z3,z5,z17]),(0,[z36,z0,z1,z2,z3,z5,z17]),(0,[z0,z1,z37,z2,z3,z5,z6]),(0,[z30,z0,z1,z2,z3,z5,z38]),(0,[z0,z1,z2,z3,z5,z39,z6]),(0,[z40,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z41]),(0,[z0,z42,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z43,z24,z5,z6]),(0,[z44,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z34,z2,z3,z45,z6]),(0,[z0,z1,z2,z3,z5,z18,z46])],[(0,[z47,z0,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z48,z5]),(0,[z49,z30,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z50,z6]),(0,[z0,z1,z3,z51,z5,z45,z6]),(1,[z52,z0,z1,z2,z3,z5])]],
   [[(0,[z0,z1,z2,z3,z5,z53,z6]),(0,[z0,z54,z1,z2,z24,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z55]),(0,[z56,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z17,z6])],[(0,[z0,z1,z2,z57,z3,z5,z6]),(0,[z0,z1,z58,z2,z59,z5,z6]),(0,[z0,z1,z58,z2,z3,z5,z18]),(0,[z0,z1,z2,z3,z5,z60,z6])],[(0,[z0,z1,z61,z2,z3,z5,z6]),(0,[z0,z62,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z12,z5,z18]),(0,[z63,z0,z1,z2,z3,z5,z18]),(1,[z0,z1,z2,z64,z5,z6]),(0,[z0,z1,z2,z3,z65,z6,z66])],[(0,[z0,z1,z58,z2,z3,z5,z67]),(0,[z68,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z24,z5,z6]),(0,[z13,z0,z1,z2,z3,z5,z18])],[(0,[z0,z1,z2,z3,z69,z5,z6]),(0,[z0,z1,z2,z3,z51,z70,z6]),(0,[z0,z54,z58,z2,z3,z5,z6]),(0,[z0,z1,z2,z5,z71,z6,z72]),(0,[z0,z1,z2,z73,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z74])],[(0,[z0,z1,z75,z2,z3,z5,z6]),(1,[z0,z1,z2,z24,z5,z18]),(1,[z0,z1,z34,z3,z51,z6]),(0,[z0,z1,z2,z3,z76,z5,z17]),(1,[z77,z0,z1,z2,z5,z6])],[(0,[z78,z0,z1,z2,z3,z79,z6]),(1,[z10,z0,z2,z3,z5,z80]),(0,[z0,z81,z1,z2,z3,z5,z11]),(0,[z0,z81,z1,z2,z12,z5,z6]),(0,[z0,z1,z2,z12,z5,z6,z72]),(0,[z82,z0,z1,z2,z3,z5,z6])],[(0,[z83,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z31,z17]),(0,[z84,z0,z1,z2,z3,z5,z6]),(0,[z85,z0,z1,z2,z3,z5,z6]),(0,[z49,z86,z0,z1,z2,z3,z5])]],
   [[(0,[z78,z0,z1,z87,z3,z5,z6]),(0,[z0,z1,z87,z2,z3,z5,z17]),(0,[z0,z1,z88,z2,z3,z5,z6]),(1,[z89,z0,z1,z3,z45,z6]),(0,[z90,z0,z1,z2,z3,z5,z6])],[(0,[z91,z92,z1,z2,z3,z5,z6]),(0,[z0,z81,z1,z2,z24,z5,z6]),(0,[z0,z1,z2,z93,z5,z71,z6])],[(0,[z91,z0,z1,z2,z3,z5,z6])],[(0,[z28,z0,z1,z2,z24,z5,z6]),(0,[z0,z35,z1,z2,z3,z5,z94]),(0,[z95,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z96,z3,z5,z6]),(0,[z97,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z98,z6]),(0,[z0,z1,z2,z3,z5,z99,z6]),(0,[z0,z1,z2,z3,z5,z17,z18]),(0,[z0,z1,z2,z3,z64,z5,z6])],[(0,[z100,z0,z1,z2,z3,z5,z6]),(0,[z101,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z102,z6]),(0,[z103,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z104,z5,z6]),(0,[z0,z1,z2,z2,z24,z5,z6]),(0,[z105,z0,z1,z2,z24,z5,z6]),(0,[z106,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z107,z108,z5,z6])],[(0,[z109,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z110,z3,z5,z6]),(0,[z0,z1,z2,z3,z111,z5,z6]),(0,[z112,z0,z1,z2,z3,z5,z6])],[(0,[z113,z0,z1,z2,z3,z5,z6]),(0,[z114,z1,z2,z3,z5,z70,z6]),(0,[z0,z1,z2,z3,z5,z70,z6]),(0,[z0,z115,z1,z2,z3,z5,z6])],[(0,[z91,z0,z54,z2,z3,z5,z6]),(0,[z0,z1,z116,z2,z3,z5,z6]),(0,[z0,z117,z1,z2,z3,z118,z6]),(0,[z77,z0,z1,z2,z5,z6,z66])]],
   [[(0,[z0,z2,z3,z5,z11,z6,z80]),(1,[z119,z0,z2,z3,z5,z6])],[(0,[z1,z87,z2,z3,z5,z38,z6]),(0,[z120,z0,z1,z2,z3,z5,z6]),(0,[z0,z121,z1,z2,z3,z5,z6]),(0,[z0,z1,z58,z2,z24,z5,z6]),(0,[z122,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z80,z18]),(0,[z0,z1,z2,z3,z5,z6,z123]),(0,[z0,z1,z2,z3,z5,z124,z18])],[(1,[z0,z1,z2,z125,z5,z6]),(0,[z0,z126,z1,z2,z3,z5,z6]),(0,[z0,z127,z1,z2,z3,z5,z6]),(0,[z128,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z107,z3,z5,z17]),(0,[z49,z0,z1,z2,z108,z5,z6]),(0,[z0,z1,z129,z2,z3,z5,z6])],[(0,[z130,z0,z1,z2,z3,z5,z6]),(1,[z131,z1,z2,z3,z5,z6]),(0,[z13,z0,z1,z2,z24,z5,z6]),(0,[z0,z1,z34,z2,z3,z5,z132]),(0,[z90,z0,z1,z2,z3,z5,z18])],[(0,[z133,z0,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z134,z5,z6]),(0,[z0,z1,z87,z2,z3,z5,z135]),(0,[z0,z1,z2,z3,z5,z136,z6]),(0,[z0,z1,z2,z3,z137,z5,z6]),(0,[z89,z0,z1,z34,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z138,z6]),(0,[z0,z1,z2,z3,z5,z6,z139])],[(0,[z0,z1,z2,z125,z3,z5,z6]),(0,[z36,z1,z2,z3,z5,z70,z6]),(0,[z0,z1,z2,z140,z3,z5,z6]),(0,[z0,z1,z2,z24,z5,z38,z6]),(0,[z91,z0,z1,z2,z3,z5,z18]),(0,[z119,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z141,z6])],[(0,[z0,z1,z2,z3,z5,z6,z142]),(0,[z0,z117,z54,z2,z3,z5,z6])],[(0,[z78,z0,z1,z2,z12,z5,z6]),(0,[z143,z0,z1,z2,z144,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z145]),(0,[z0,z1,z2,z3,z5,z146,z6])]],
   [[(0,[z0,z1,z147,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z148,z6]),(0,[z149,z0,z1,z2,z3,z5,z6]),(0,[z10,z0,z1,z2,z93,z3,z5]),(0,[z49,z0,z1,z2,z3,z5,z17])],[(0,[z0,z1,z2,z3,z5,z150,z6]),(0,[z0,z1,z2,z3,z151,z5,z6]),(0,[z0,z152,z1,z2,z3,z5,z6]),(0,[z0,z153,z1,z2,z3,z5,z6]),(0,[z154,z0,z1,z2,z3,z5,z6]),(0,[z114,z155,z1,z2,z3,z5,z6]),(0,[z156,z0,z1,z2,z3,z5,z11]),(0,[z156,z0,z1,z2,z12,z5,z6]),(0,[z91,z0,z1,z2,z3,z157,z6]),(0,[z158,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z159,z24,z5,z6]),(0,[z0,z1,z160,z2,z161,z5,z6]),(0,[z162,z0,z1,z2,z3,z5,z17]),(0,[z0,z1,z2,z108,z5,z71,z6])],[(0,[z0,z1,z1,z2,z3,z5,z6]),(0,[z0,z20,z2,z3,z118,z5,z6]),(0,[z163,z0,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z5,z164,z6]),(1,[z156,z1,z2,z3,z5,z38]),(0,[z0,z1,z2,z3,z165,z5,z6]),(1,[z166,z0,z1,z2,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z167]),(0,[z0,z1,z2,z12,z168,z5,z6]),(0,[z89,z0,z1,z2,z3,z5,z169]),(0,[z0,z1,z170,z2,z3,z5,z6])],[(0,[z171,z0,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z69,z5,z70,z6]),(0,[z0,z1,z172,z2,z3,z5,z6]),(0,[z173,z0,z1,z2,z12,z5,z6]),(1,[z174,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z175,z5,z6])],[(0,[z176,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z177,z5,z6]),(1,[z1,z2,z3,z5,z178,z6])],[(0,[z0,z1,z2,z3,z134,z5,z6]),(0,[z0,z1,z2,z21,z12,z5,z6]),(0,[z0,z1,z2,z3,z5,z179,z6]),(1,[z13,z0,z1,z3,z5,z18])],[(0,[z0,z1,z2,z144,z3,z5,z17]),(0,[z155,z0,z1,z2,z12,z5,z6]),(0,[z0,z1,z2,z3,z5,z180,z6]),(0,[z83,z0,z2,z3,z181,z5,z6]),(0,[z0,z1,z2,z12,z181,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z182]),(0,[z0,z81,z2,z3,z5,z11,z6]),(0,[z0,z1,z2,z24,z183,z5,z6]),(0,[z184,z0,z1,z2,z12,z5,z6]),(0,[z0,z1,z2,z12,z185,z5,z6]),(0,[z186,z0,z1,z2,z3,z5,z17]),(0,[z0,z187,z1,z2,z3,z5,z6]),(0,[z0,z1,z188,z2,z3,z5,z6])],[(0,[z189,z0,z1,z2,z3,z5,z6]),(0,[z83,z0,z1,z2,z12,z5,z6]),(0,[z0,z1,z190,z2,z3,z5,z6]),(0,[z89,z0,z1,z2,z12,z5,z6]),(0,[z0,z1,z2,z3,z5,z17,z191]),(0,[z0,z192,z1,z2,z3,z5,z6])]],
   [[(0,[z1,z2,z3,z43,z5,z70,z6]),(0,[z0,z1,z2,z3,z5,z193,z6]),(1,[z194,z0,z1,z2,z3,z5]),(0,[z89,z0,z1,z3,z5,z45,z6]),(0,[z0,z1,z2,z195,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z18,z66]),(0,[z0,z1,z2,z3,z5,z196,z6]),(0,[z77,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z197,z6]),(0,[z198,z0,z1,z2,z43,z5,z6]),(0,[z0,z1,z2,z3,z5,z38,z17]),(0,[z91,z0,z1,z2,z3,z5,z199]),(0,[z0,z1,z2,z3,z5,z200,z6]),(0,[z201,z0,z1,z2,z12,z5,z6]),(0,[z89,z0,z1,z2,z3,z45,z6]),(0,[z89,z0,z1,z2,z3,z5,z17]),(1,[z0,z1,z2,z202,z5,z6])],[(0,[z0,z1,z2,z203,z3,z5,z6]),(0,[z0,z1,z2,z3,z204,z5,z6]),(0,[z83,z0,z1,z2,z24,z5,z6]),(0,[z205,z0,z1,z2,z12,z5,z6]),(0,[z1,z2,z3,z5,z6,z206,z18])],[(0,[z0,z1,z2,z3,z48,z5,z6]),(0,[z0,z1,z2,z3,z5,z164,z6]),(0,[z0,z1,z2,z207,z3,z5,z6]),(0,[z0,z1,z2,z93,z12,z5,z6]),(0,[z0,z208,z1,z2,z3,z5,z6])],[(1,[z198,z1,z2,z43,z5,z6]),(0,[z205,z0,z1,z2,z3,z5,z17])],[(0,[z0,z1,z2,z3,z5,z209,z6]),(0,[z0,z1,z2,z3,z5,z6,z210]),(0,[z0,z35,z2,z3,z118,z5,z6]),(0,[z91,z0,z1,z2,z24,z5,z6]),(0,[z0,z211,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z93,z3,z5,z17])],[(0,[z0,z1,z2,z212,z3,z5,z6]),(0,[z49,z156,z0,z1,z2,z3,z5]),(0,[z0,z213,z1,z2,z181,z5,z6]),(0,[z0,z1,z2,z3,z5,z214,z6]),(0,[z0,z81,z1,z2,z93,z3,z5]),(0,[z0,z1,z3,z5,z17,z6,z18])],[(0,[z215,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z34,z2,z3,z5,z216])]],
   [[(0,[z217,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z24,z5,z6,z66]),(1,[z0,z1,z2,z218,z5,z6]),(0,[z0,z219,z1,z2,z3,z5,z6]),(0,[z220,z0,z1,z2,z3,z5,z6])],[(0,[z221,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z20,z2,z3,z5,z6]),(0,[z0,z222,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z79,z6]),(0,[z223,z0,z1,z2,z3,z5,z6]),(0,[z0,z117,z1,z2,z12,z5,z6]),(1,[z224,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z18,z225]),(0,[z0,z1,z2,z3,z5,z71,z6])],[(0,[z78,z0,z1,z226,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z17,z227]),(0,[z228,z0,z1,z2,z3,z5,z6]),(1,[z40,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z202,z5,z6])],[(1,[z0,z1,z2,z93,z5,z71]),(0,[z0,z1,z229,z2,z3,z5,z6])],[(0,[z0,z1,z2,z5,z164,z70,z6]),(0,[z156,z1,z2,z3,z5,z38,z6]),(0,[z0,z121,z1,z2,z24,z5,z6]),(0,[z0,z1,z2,z3,z159,z5,z6]),(0,[z0,z1,z2,z3,z5,z17,z230])],[(0,[z0,z1,z2,z3,z5,z6,z231]),(0,[z0,z1,z34,z2,z218,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z206])],[(0,[z30,z1,z20,z2,z3,z5,z6]),(1,[z0,z232,z2,z3,z5,z6]),(0,[z78,z30,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z233,z3,z5,z6]),(0,[z155,z1,z2,z3,z69,z5,z6]),(0,[z194,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z207,z3,z5,z18]),(0,[z0,z1,z2,z234,z3,z5,z6]),(1,[z0,z1,z2,z3,z5,z235]),(0,[z0,z1,z2,z3,z5,z236,z6])],[(0,[z0,z117,z1,z2,z3,z70,z6]),(1,[z0,z1,z2,z237,z5,z6]),(1,[z0,z1,z2,z3,z5,z50]),(0,[z0,z1,z2,z3,z5,z6,z80]),(0,[z49,z0,z1,z2,z5,z6,z72])]],
   [[(0,[z36,z1,z20,z2,z3,z5,z6]),(0,[z221,z35,z1,z2,z3,z5,z6]),(0,[z0,z1,z238,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z239,z5,z6]),(0,[z240,z0,z1,z2,z3,z5,z6]),(0,[z156,z30,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z241,z3,z5,z6]),(0,[z242,z0,z1,z2,z3,z5,z6])],[(0,[z78,z36,z1,z2,z3,z5,z6]),(0,[z0,z243,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z181,z5,z6]),(0,[z0,z1,z2,z3,z5,z244,z6]),(0,[z89,z0,z245,z2,z3,z5,z6]),(0,[z27,z0,z1,z2,z107,z5,z6])],[(0,[z221,z1,z2,z226,z3,z5,z6]),(0,[z246,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z247]),(0,[z0,z1,z2,z3,z5,z248,z6])],[(0,[z0,z1,z2,z24,z118,z5,z6])],[(0,[z0,z1,z20,z2,z3,z5,z18]),(0,[z221,z0,z1,z2,z3,z5,z18]),(0,[z0,z1,z2,z3,z157,z5,z6])],[(1,[z0,z1,z2,z3,z4,z6]),(0,[z249,z0,z1,z2,z3,z5,z6]),(0,[z198,z0,z1,z2,z12,z5,z6]),(0,[z155,z30,z1,z2,z3,z5,z6]),(0,[z0,z1,z250,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z5,z251]),(1,[z0,z1,z2,z3,z5,z169]),(0,[z252,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z253,z3,z5,z6]),(0,[z0,z1,z254,z2,z3,z5,z6]),(0,[z255,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z12,z5,z6,z18]),(0,[z0,z1,z2,z12,z5,z256,z6]),(0,[z86,z0,z1,z2,z3,z185,z6])],[(0,[z257,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z258,z6]),(0,[z0,z1,z2,z12,z5,z11,z6])]],
   [[(0,[z155,z36,z1,z2,z3,z5,z6]),(0,[z198,z0,z1,z2,z24,z5,z6]),(1,[z30,z1,z2,z3,z5,z227]),(0,[z0,z1,z25,z2,z3,z5,z251]),(0,[z0,z1,z2,z259,z3,z5,z6])],[(0,[z1,z20,z2,z3,z5,z38,z6]),(0,[z0,z260,z1,z2,z3,z5,z6]),(0,[z156,z0,z1,z2,z93,z3,z5]),(0,[z0,z1,z261,z2,z3,z5,z6]),(0,[z262,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z65,z6])],[(0,[z0,z1,z2,z3,z5,z79,z6]),(0,[z0,z213,z1,z2,z3,z5,z17]),(0,[z263,z0,z1,z2,z3,z5,z6]),(0,[z264,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z265,z2,z3,z5,z6]),(0,[z0,z1,z2,z207,z12,z5,z6]),(0,[z49,z0,z81,z1,z2,z3,z5]),(0,[z0,z1,z2,z108,z5,z266,z6]),(0,[z86,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z181,z5,z18]),(0,[z0,z1,z2,z3,z267,z181,z5]),(0,[z0,z1,z2,z3,z5,z268,z6]),(0,[z0,z1,z2,z3,z269,z5,z6]),(1,[z0,z1,z2,z3,z5,z17]),(0,[z0,z1,z2,z3,z185,z5,z18]),(0,[z0,z1,z2,z3,z5,z6,z270])],[(0,[z0,z1,z2,z3,z5,z271,z6]),(0,[z0,z1,z272,z2,z3,z5,z6]),(0,[z273,z0,z1,z2,z3,z5,z6]),(0,[z274,z0,z1,z2,z3,z5,z6]),(0,[z10,z0,z1,z2,z3,z5,z17]),(0,[z27,z0,z1,z2,z3,z266,z6])],[(0,[z0,z1,z275,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z6]),(0,[z91,z131,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z207,z24,z5,z6]),(0,[z0,z1,z2,z3,z5,z276,z6]),(0,[z277,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z278])],[(0,[z0,z1,z2,z3,z5,z6,z279]),(0,[z143,z0,z1,z2,z3,z5,z6]),(0,[z0,z280,z1,z2,z3,z5,z6]),(1,[z0,z54,z58,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z67,z6]),(0,[z0,z1,z2,z3,z118,z45,z6]),(0,[z0,z1,z2,z3,z118,z5,z17]),(0,[z0,z1,z25,z2,z3,z5,z17]),(0,[z0,z281,z1,z2,z3,z5,z6]),(0,[z27,z0,z1,z2,z3,z5,z17]),(0,[z0,z1,z2,z3,z108,z5,z6])]],
   [[(0,[z0,z1,z2,z3,z282,z5,z6]),(0,[z0,z54,z1,z58,z3,z5,z6]),(0,[z0,z54,z1,z2,z12,z5,z6]),(0,[z0,z1,z25,z12,z3,z5,z6]),(0,[z0,z283,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z284,z5,z6]),(0,[z0,z1,z2,z3,z285,z5,z6]),(0,[z286,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z34,z2,z3,z5,z17])],[(0,[z28,z0,z20,z2,z3,z5,z6]),(0,[z0,z287,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z288,z3,z5,z6]),(0,[z289,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z290,z6])],[(0,[z291,z0,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z292,z5]),(0,[z0,z1,z2,z3,z51,z5,z17]),(0,[z0,z1,z2,z3,z5,z293,z6]),(0,[z294,z0,z1,z2,z3,z5,z6]),(0,[z295,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z296,z6]),(0,[z0,z1,z2,z3,z5,z6,z297])],[(0,[z298,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z20,z2,z24,z5,z6]),(0,[z221,z0,z1,z2,z24,z5,z6]),(0,[z0,z1,z2,z3,z299,z5,z6]),(0,[z0,z1,z2,z59,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z65,z18]),(0,[z300,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z301,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z302]),(0,[z0,z1,z2,z3,z5,z6,z124]),(0,[z27,z0,z1,z2,z5,z266,z6]),(0,[z0,z1,z2,z3,z5,z303,z6]),(0,[z0,z1,z2,z3,z5,z304,z266]),(1,[z0,z1,z2,z107,z108,z6])],[(0,[z0,z1,z2,z24,z5,z6,z32]),(0,[z0,z305,z1,z2,z3,z5,z6]),(0,[z86,z0,z1,z2,z3,z5,z18])],[(0,[z0,z1,z2,z3,z5,z306,z6]),(0,[z0,z1,z160,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z307,z6]),(0,[z0,z1,z2,z3,z5,z6,z308])]],
   [[(0,[z0,z35,z2,z21,z3,z5,z6]),(0,[z309,z0,z1,z2,z3,z5,z6]),(0,[z310,z0,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z5,z135]),(0,[z83,z0,z1,z2,z5,z71,z6]),(0,[z119,z0,z2,z3,z5,z45,z6]),(0,[z0,z1,z2,z3,z5,z311,z6])],[(0,[z0,z1,z2,z3,z312,z5,z6]),(0,[z313,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z314,z6]),(0,[z0,z1,z2,z3,z5,z256,z6]),(0,[z0,z1,z2,z3,z5,z6,z315]),(0,[z0,z1,z2,z3,z5,z6,z18])],[(1,[z0,z1,z2,z3,z5,z94]),(0,[z316,z0,z1,z2,z3,z5,z6]),(0,[z317,z0,z1,z2,z3,z5,z6]),(0,[z143,z0,z1,z2,z3,z5,z18]),(0,[z0,z1,z2,z3,z5,z6,z318]),(0,[z0,z1,z2,z3,z108,z5,z18]),(0,[z0,z1,z2,z3,z5,z6,z319])],[(0,[z28,z0,z1,z2,z12,z5,z6]),(0,[z0,z1,z2,z3,z5,z320,z6]),(0,[z0,z81,z1,z2,z3,z5,z17]),(0,[z0,z1,z2,z3,z5,z266,z6])],[(0,[z30,z0,z1,z2,z3,z5,z80]),(0,[z321,z0,z1,z2,z3,z5,z6]),(0,[z286,z0,z1,z2,z3,z5,z18]),(0,[z0,z1,z2,z322,z24,z5,z6]),(0,[z323,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z2,z12,z5,z6]),(1,[z0,z245,z2,z3,z5,z6])],[(0,[z0,z1,z2,z324,z3,z5,z6]),(0,[z0,z1,z2,z12,z51,z5,z6]),(0,[z0,z1,z2,z3,z5,z45,z6]),(0,[z0,z1,z2,z3,z5,z216,z6])],[(0,[z78,z0,z232,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z325,z5,z6]),(0,[z30,z0,z1,z2,z3,z185,z5]),(0,[z81,z326,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z2,z3,z5,z17])],[(0,[z0,z1,z2,z3,z5,z304,z6]),(1,[z264,z1,z2,z3,z5,z6])]],
   [[(0,[z0,z1,z2,z3,z5,z327,z6]),(0,[z83,z0,z1,z2,z181,z5,z6])],[(0,[z0,z1,z2,z328,z3,z5,z6]),(0,[z0,z1,z2,z3,z329,z5,z6]),(0,[z0,z1,z58,z2,z12,z5,z6]),(1,[z1,z2,z3,z5,z98,z6]),(1,[z0,z1,z2,z3,z5,z330]),(0,[z0,z1,z2,z24,z5,z17,z6]),(0,[z89,z224,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z5,z132]),(0,[z0,z331,z1,z2,z3,z5,z6])],[(0,[z332,z0,z1,z2,z3,z5,z6]),(0,[z40,z81,z1,z2,z3,z5,z6]),(0,[z0,z1,z160,z2,z3,z5,z18])],[(0,[z333,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z227,z18]),(0,[z0,z1,z334,z2,z3,z5,z6]),(0,[z286,z0,z1,z3,z24,z5,z6]),(0,[z13,z0,z1,z2,z12,z5,z6]),(0,[z0,z1,z34,z3,z51,z5,z6]),(0,[z0,z1,z2,z107,z3,z266,z6])],[(0,[z335,z0,z1,z2,z3,z5,z6]),(0,[z221,z1,z2,z3,z5,z38,z6]),(0,[z0,z1,z2,z12,z5,z31,z6]),(0,[z0,z1,z2,z24,z24,z5,z6]),(0,[z27,z49,z0,z1,z2,z5,z6]),(0,[z0,z1,z2,z3,z5,z336,z6])],[(0,[z0,z1,z2,z3,z337,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z338]),(0,[z0,z1,z2,z24,z69,z5,z6]),(0,[z0,z1,z2,z12,z5,z6,z227]),(0,[z83,z0,z1,z2,z207,z5,z6]),(0,[z166,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z339,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z11,z18]),(0,[z317,z0,z1,z2,z3,z5,z18]),(0,[z0,z1,z2,z3,z340,z5,z6])],[(0,[z0,z0,z1,z2,z3,z5,z6]),(0,[z114,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z341,z5,z6]),(0,[z0,z1,z2,z3,z5,z342,z6]),(0,[z86,z0,z1,z2,z24,z5,z6]),(0,[z0,z1,z2,z29,z12,z5,z6]),(0,[z0,z1,z2,z3,z5,z266,z18]),(0,[z0,z1,z2,z3,z5,z6,z343])],[(0,[z0,z1,z344,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z345,z6]),(0,[z346,z0,z1,z2,z3,z5,z6]),(0,[z205,z0,z2,z3,z5,z31,z6]),(1,[z0,z1,z2,z24,z5,z17])]],
   [[(0,[z0,z347,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z45,z18]),(0,[z0,z1,z2,z3,z5,z348,z6]),(0,[z0,z1,z2,z3,z349,z5,z6]),(0,[z264,z1,z2,z3,z185,z5,z6])],[(0,[z350,z0,z1,z2,z3,z5,z6]),(0,[z155,z1,z2,z3,z43,z5,z6]),(0,[z0,z1,z2,z351,z3,z5,z6]),(0,[z0,z352,z1,z2,z3,z5,z6]),(0,[z0,z1,z353,z2,z3,z5,z6])],[(0,[z354,z0,z1,z2,z3,z5,z6]),(0,[z221,z0,z1,z2,z3,z355,z6]),(0,[z143,z0,z1,z2,z24,z5,z6]),(0,[z0,z1,z2,z3,z5,z356,z6]),(0,[z91,z0,z1,z2,z237,z5,z6]),(0,[z0,z1,z2,z3,z5,z357,z6])],[(0,[z30,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z358,z5,z6]),(0,[z0,z1,z2,z3,z359,z5,z6]),(0,[z0,z1,z2,z3,z360,z5,z6])],[(0,[z78,z0,z1,z2,z3,z5,z17]),(0,[z0,z1,z2,z3,z361,z5,z6]),(0,[z0,z1,z362,z2,z3,z5,z6]),(0,[z363,z0,z1,z2,z3,z5,z6]),(0,[z0,z2,z3,z118,z5,z31,z6]),(0,[z286,z0,z1,z2,z24,z5,z6]),(0,[z0,z1,z2,z24,z5,z99,z6]),(0,[z0,z1,z2,z3,z5,z364,z6]),(0,[z0,z1,z2,z3,z5,z6,z72])],[(0,[z0,z35,z1,z2,z3,z5,z6]),(0,[z36,z0,z1,z2,z3,z5,z6]),(1,[z36,z1,z87,z3,z5,z6]),(0,[z155,z0,z1,z2,z3,z69,z6]),(0,[z0,z1,z2,z365,z3,z5,z6]),(0,[z366,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z367,z2,z3,z5,z6]),(0,[z0,z1,z368,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z191])],[(0,[z369,z0,z1,z2,z3,z5,z6]),(0,[z0,z370,z1,z2,z3,z5,z6]),(0,[z156,z0,z1,z2,z3,z5,z17]),(1,[z0,z1,z2,z371,z5,z6]),(0,[z0,z1,z372,z2,z3,z5,z6])],[(0,[z373,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z374,z2,z3,z5,z6]),(0,[z78,z0,z1,z2,z375,z5,z6]),(0,[z0,z1,z2,z226,z3,z5,z6]),(0,[z0,z1,z2,z24,z5,z70,z6]),(1,[z363,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z376,z5,z6])]],
   [[(0,[z0,z1,z2,z3,z377,z5,z6]),(1,[z313,z0,z1,z2,z5,z6]),(0,[z156,z0,z1,z2,z3,z5,z38]),(0,[z91,z205,z0,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z24,z5,z17]),(0,[z378,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z379,z5,z6]),(0,[z114,z0,z1,z2,z3,z5,z18]),(0,[z205,z0,z1,z2,z3,z69,z6]),(0,[z0,z1,z2,z3,z69,z45,z6]),(0,[z0,z1,z2,z3,z69,z5,z17]),(0,[z380,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z381,z3,z5,z6]),(0,[z382,z0,z1,z2,z3,z5,z17])],[(0,[z0,z383,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z384]),(0,[z0,z1,z2,z21,z3,z5,z17]),(0,[z385,z0,z1,z2,z3,z5,z6]),(0,[z0,z386,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z387,z5,z6]),(0,[z155,z0,z1,z2,z3,z5,z17]),(0,[z0,z1,z2,z3,z5,z388,z6]),(0,[z389,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z390,z6]),(0,[z184,z0,z1,z2,z3,z5,z17]),(0,[z391,z0,z1,z2,z3,z5,z6]),(0,[z0,z392,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z393,z5,z6]),(0,[z83,z0,z1,z2,z3,z5,z17]),(1,[z187,z1,z2,z3,z5,z6]),(0,[z0,z394,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z395,z6])],[(0,[z28,z1,z2,z3,z5,z70,z6]),(0,[z396,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z397,z3,z5,z6]),(0,[z398,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z399,z5,z6]),(0,[z0,z400,z1,z2,z3,z5,z6]),(0,[z0,z401,z1,z2,z3,z5,z6]),(0,[z91,z0,z1,z58,z3,z5,z6]),(0,[z91,z0,z1,z2,z12,z5,z6]),(1,[z0,z1,z2,z5,z6,z402]),(1,[z0,z1,z2,z3,z5,z216]),(0,[z0,z1,z2,z403,z3,z5,z6]),(0,[z0,z1,z2,z3,z76,z5,z6]),(0,[z86,z0,z1,z2,z3,z6,z66])],[(0,[z30,z0,z1,z2,z3,z5,z18]),(0,[z0,z404,z1,z2,z3,z5,z6]),(1,[z286,z0,z1,z24,z5,z6]),(0,[z0,z1,z2,z3,z405,z5,z6]),(0,[z0,z1,z2,z3,z360,z5,z18])],[(0,[z143,z1,z2,z144,z3,z5,z6]),(0,[z27,z143,z0,z1,z2,z5,z6]),(0,[z0,z1,z2,z3,z371,z5,z6]),(0,[z91,z0,z1,z2,z3,z5,z17]),(1,[z406,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z407]),(0,[z323,z0,z1,z2,z24,z5,z6]),(0,[z27,z187,z1,z2,z3,z5,z6])]],
   [[(0,[z0,z35,z1,z2,z3,z5,z18]),(0,[z0,z1,z87,z2,z3,z5,z6]),(0,[z36,z0,z1,z2,z3,z5,z18]),(0,[z0,z117,z1,z2,z3,z69,z6]),(0,[z0,z1,z2,z3,z5,z6,z227]),(0,[z0,z1,z408,z2,z3,z5,z6]),(1,[z0,z1,z2,z409,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z410])],[(0,[z0,z1,z232,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z411]),(1,[z0,z1,z2,z3,z258,z6])],[(0,[z0,z1,z2,z226,z3,z5,z18]),(0,[z0,z1,z2,z3,z5,z6,z230]),(0,[z0,z1,z2,z3,z412,z5,z6])],[(0,[z0,z1,z2,z3,z5,z70,z17]),(0,[z0,z58,z2,z21,z3,z5,z6]),(0,[z0,z413,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z414,z5,z6])],[(0,[z415,z0,z1,z2,z3,z5,z6])],[(0,[z30,z1,z87,z2,z3,z5,z6]),(0,[z416,z0,z1,z2,z3,z5,z6]),(0,[z30,z1,z2,z3,z5,z6,z227]),(0,[z0,z1,z2,z3,z5,z6,z417]),(0,[z0,z1,z2,z3,z5,z6,z418]),(0,[z0,z1,z419,z2,z3,z5,z6]),(0,[z13,z0,z1,z160,z3,z5,z6])],[(0,[z0,z1,z2,z12,z5,z38,z6]),(0,[z0,z1,z2,z420,z3,z5,z6]),(0,[z0,z117,z1,z2,z3,z5,z17]),(0,[z0,z1,z2,z3,z5,z6,z402]),(0,[z0,z421,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z161,z5,z6])],[(0,[z422,z0,z1,z2,z3,z5,z6]),(0,[z36,z1,z87,z2,z3,z5,z6]),(0,[z313,z0,z1,z2,z5,z70,z6]),(0,[z0,z1,z423,z2,z3,z5,z6]),(1,[z49,z0,z1,z2,z5,z72])]],
   [[(0,[z198,z1,z2,z3,z43,z5,z6]),(0,[z424,z0,z1,z2,z3,z5,z6]),(0,[z425,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z168,z5,z6])],[(0,[z0,z1,z2,z3,z5,z426,z6]),(0,[z0,z1,z427,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z31,z18])],[(0,[z428,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z87,z2,z3,z5,z18]),(0,[z30,z0,z1,z2,z3,z5,z11]),(0,[z0,z1,z2,z429,z3,z5,z6]),(0,[z0,z1,z2,z3,z430,z5,z6]),(0,[z0,z1,z2,z414,z3,z5,z6]),(1,[z1,z2,z3,z5,z6,z206]),(0,[z1,z2,z3,z185,z5,z178,z6])],[(0,[z198,z0,z1,z2,z108,z5,z6]),(0,[z431,z0,z1,z2,z3,z5,z6]),(1,[z326,z1,z2,z3,z5,z6]),(0,[z0,z432,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z185,z5,z6]),(0,[z0,z1,z433,z2,z3,z5,z6])],[(0,[z0,z434,z1,z2,z3,z5,z6]),(0,[z0,z54,z2,z3,z5,z31,z6]),(0,[z0,z1,z2,z3,z5,z6,z435]),(1,[z0,z1,z2,z436,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z437])],[(0,[z30,z0,z1,z2,z24,z5,z6]),(0,[z438,z0,z1,z2,z3,z5,z17])],[(0,[z363,z0,z1,z2,z3,z5,z70]),(0,[z0,z1,z34,z2,z3,z51,z6]),(0,[z439,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z440,z3,z5,z6]),(0,[z441,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z185,z5,z65])]],
   [[(0,[z0,z35,z1,z2,z24,z5,z6]),(0,[z0,z1,z2,z442,z3,z5,z6]),(0,[z443,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z409,z3,z5,z6]),(0,[z49,z0,z1,z2,z3,z5,z6]),(0,[z444,z0,z1,z2,z3,z5,z6])],[(0,[z445,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z446,z5,z6]),(0,[z162,z0,z1,z2,z3,z5,z6]),(1,[z112,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z447,z6]),(0,[z78,z0,z1,z2,z3,z5,z279]),(0,[z0,z1,z2,z226,z24,z5,z6]),(0,[z198,z0,z1,z2,z3,z5,z17]),(0,[z0,z1,z2,z3,z5,z448,z6]),(0,[z0,z1,z2,z24,z5,z71,z6]),(0,[z449,z0,z1,z2,z3,z5,z6])],[(0,[z221,z0,z20,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z450,z6]),(0,[z451,z0,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z284,z5,z6])],[(1,[z0,z400,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z452,z5,z6]),(0,[z453,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z454,z3,z5,z6]),(0,[z455,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z456,z6]),(0,[z0,z1,z2,z3,z31,z45,z6]),(0,[z457,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z458,z3,z5,z6]),(0,[z0,z1,z2,z107,z3,z5,z18])],[(0,[z0,z1,z2,z3,z292,z5,z6]),(0,[z1,z2,z3,z5,z38,z6,z227]),(0,[z0,z1,z459,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z460]),(0,[z0,z1,z2,z3,z436,z5,z6]),(0,[z461,z0,z1,z2,z3,z5,z6])],[(0,[z221,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z5,z6,z462]),(0,[z463,z0,z1,z2,z3,z5,z6])]],
   [[(0,[z194,z0,z1,z2,z3,z181,z5]),(0,[z0,z1,z2,z207,z3,z5,z17]),(0,[z0,z1,z2,z24,z5,z6,z80]),(0,[z464,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z6,z465]),(0,[z205,z0,z35,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z466,z6]),(1,[z143,z1,z2,z144,z5,z6]),(0,[z1,z2,z3,z5,z70,z38,z6]),(0,[z205,z0,z1,z2,z3,z31,z6]),(0,[z0,z1,z2,z12,z5,z6,z66]),(0,[z89,z0,z467,z2,z3,z5,z6]),(0,[z86,z0,z1,z2,z3,z5,z65])],[(1,[z0,z1,z2,z375,z5,z6]),(0,[z78,z1,z2,z226,z3,z5,z6]),(0,[z468,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z469,z5,z6]),(0,[z0,z1,z2,z470,z3,z5,z6])],[(0,[z0,z1,z87,z2,z24,z5,z6]),(0,[z49,z0,z1,z2,z3,z5,z18]),(0,[z0,z1,z2,z3,z471,z5,z6])],[(0,[z0,z1,z20,z2,z12,z5,z6]),(0,[z221,z0,z1,z2,z12,z5,z6]),(0,[z0,z1,z2,z3,z5,z206,z18]),(0,[z0,z472,z1,z2,z3,z5,z6])],[(0,[z30,z0,z1,z2,z3,z5,z227]),(0,[z0,z54,z1,z2,z3,z5,z17])],[(0,[z143,z0,z1,z2,z43,z5,z6]),(0,[z473,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z474,z5,z6]),(1,[z0,z2,z3,z5,z475,z6]),(0,[z0,z1,z2,z3,z5,z476,z6]),(0,[z0,z1,z2,z3,z5,z71,z17])],[(0,[z477,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z478,z6]),(0,[z83,z0,z213,z2,z3,z5,z6])]],
   [[(0,[z0,z1,z479,z2,z3,z5,z6]),(1,[z114,z1,z2,z3,z70,z6]),(0,[z0,z1,z2,z3,z5,z6,z480])],[(0,[z155,z1,z2,z226,z3,z5,z6]),(0,[z0,z1,z2,z3,z48,z43,z5]),(0,[z0,z1,z2,z144,z3,z5,z18]),(0,[z91,z0,z1,z2,z371,z5,z6]),(0,[z0,z1,z481,z2,z3,z5,z6]),(1,[z86,z0,z1,z2,z3,z66])],[(0,[z0,z131,z1,z2,z3,z5,z6]),(0,[z482,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z24,z5,z65,z6]),(0,[z483,z0,z1,z2,z3,z5,z18])],[(0,[z484,z0,z1,z2,z3,z5,z6]),(0,[z155,z28,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z375,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z485]),(0,[z0,z58,z2,z3,z118,z5,z6]),(0,[z406,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z12,z5,z486,z6])],[(0,[z0,z1,z2,z3,z43,z5,z17]),(0,[z0,z1,z2,z3,z5,z487,z6]),(0,[z0,z1,z2,z3,z5,z6,z488]),(0,[z0,z1,z2,z3,z5,z489,z6]),(0,[z0,z1,z2,z12,z118,z5,z6])],[(0,[z155,z143,z1,z2,z3,z5,z6]),(0,[z10,z0,z81,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z11,z6])],[(0,[z0,z490,z1,z2,z3,z5,z6]),(0,[z491,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z492,z2,z3,z5,z6]),(0,[z493,z0,z1,z2,z3,z5,z6]),(0,[z10,z0,z1,z2,z3,z5,z80]),(0,[z0,z1,z2,z3,z5,z6,z494])],[(0,[z0,z1,z2,z495,z3,z5,z6]),(0,[z0,z1,z2,z3,z496,z5,z6])]],
   [[(0,[z28,z0,z1,z2,z3,z5,z17]),(0,[z0,z1,z87,z2,z203,z5,z6]),(0,[z0,z1,z2,z3,z497,z5,z6]),(1,[z0,z1,z2,z3,z5,z247]),(0,[z0,z1,z2,z3,z498,z5,z6]),(0,[z286,z0,z1,z2,z3,z5,z235]),(0,[z0,z1,z2,z24,z108,z5,z6])],[(0,[z0,z1,z2,z3,z5,z499,z6]),(0,[z500,z0,z1,z2,z3,z5,z6]),(0,[z0,z501,z1,z2,z3,z5,z6])],[(0,[z502,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z503,z3,z5,z6]),(0,[z0,z1,z58,z2,z284,z5,z6]),(0,[z504,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z12,z3,z5,z6]),(0,[z0,z1,z2,z505,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z18,z18]),(0,[z0,z1,z2,z3,z5,z18,z315]),(0,[z0,z506,z1,z2,z3,z5,z6])],[(0,[z507,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z508,z5,z6]),(0,[z89,z0,z1,z2,z414,z5,z6]),(0,[z13,z0,z1,z3,z5,z6,z18])],[(0,[z0,z1,z2,z3,z509,z5,z6]),(0,[z91,z0,z1,z2,z3,z258,z6]),(0,[z0,z1,z2,z12,z5,z6,z510]),(1,[z0,z1,z2,z511,z5,z6])],[(0,[z0,z1,z2,z259,z3,z5,z17]),(0,[z0,z1,z2,z3,z5,z512,z6])],[(0,[z0,z1,z2,z12,z43,z5,z6]),(0,[z143,z0,z1,z2,z108,z5,z6]),(0,[z0,z1,z58,z2,z3,z5,z17]),(0,[z0,z117,z2,z3,z118,z5,z6]),(0,[z86,z0,z1,z2,z12,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z513]),(0,[z49,z0,z1,z2,z3,z5,z72])],[(0,[z0,z1,z514,z2,z3,z5,z6]),(1,[z0,z1,z2,z12,z5,z17]),(0,[z0,z1,z2,z3,z515,z5,z6])]],
   [[(0,[z0,z1,z2,z3,z5,z516,z6]),(0,[z0,z1,z2,z3,z5,z6,z199]),(0,[z13,z0,z1,z2,z3,z5,z17]),(0,[z0,z1,z2,z3,z5,z6,z517])],[(0,[z1,z2,z144,z3,z43,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z518]),(0,[z0,z1,z160,z3,z5,z17,z6]),(0,[z0,z1,z2,z3,z5,z17,z66]),(1,[z0,z1,z2,z3,z5,z304])],[(0,[z143,z0,z1,z2,z12,z5,z6]),(0,[z0,z213,z1,z2,z3,z5,z6]),(0,[z0,z519,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z24,z5,z6,z18]),(0,[z89,z0,z1,z2,z3,z51,z6]),(0,[z0,z1,z2,z3,z5,z271,z17]),(0,[z0,z1,z2,z3,z5,z520,z6])],[(0,[z221,z30,z1,z2,z3,z5,z6]),(0,[z27,z198,z0,z1,z2,z5,z6]),(1,[z0,z1,z12,z24,z5,z6]),(0,[z89,z0,z1,z2,z3,z5,z521])],[(0,[z0,z1,z2,z522,z3,z5,z6]),(0,[z0,z81,z1,z2,z3,z5,z80]),(0,[z166,z0,z1,z2,z5,z6,z80]),(0,[z286,z0,z1,z2,z12,z5,z6]),(0,[z0,z1,z2,z24,z5,z266,z6]),(1,[z0,z467,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z108,z5,z17])],[(1,[z0,z1,z2,z3,z5,z279]),(0,[z523,z0,z1,z2,z3,z5,z6]),(0,[z91,z0,z1,z2,z3,z5,z50]),(0,[z10,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z12,z3,z5,z18]),(0,[z89,z0,z1,z2,z436,z5,z6]),(0,[z0,z1,z2,z3,z511,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z524])],[(0,[z221,z36,z1,z2,z3,z5,z6]),(0,[z286,z0,z1,z2,z3,z5,z17]),(0,[z0,z1,z2,z24,z5,z45,z6]),(0,[z0,z1,z2,z3,z5,z525,z6]),(0,[z0,z1,z2,z3,z526,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z527])],[(0,[z0,z1,z2,z528,z3,z5,z6]),(0,[z529,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z25,z2,z3,z5,z6]),(0,[z27,z0,z1,z2,z3,z5,z6])]],
   [[(0,[z0,z1,z2,z3,z51,z31,z6]),(0,[z0,z1,z2,z3,z5,z530,z6]),(0,[z0,z1,z2,z3,z5,z17,z17]),(0,[z531,z0,z1,z2,z3,z5,z6])],[(0,[z532,z0,z1,z2,z3,z5,z6]),(0,[z533,z0,z1,z2,z3,z5,z6]),(0,[z0,z305,z1,z2,z12,z5,z6]),(0,[z89,z112,z1,z2,z3,z5,z6]),(0,[z0,z1,z34,z2,z3,z5,z6]),(0,[z0,z1,z2,z534,z3,z5,z6])],[(0,[z535,z0,z1,z2,z3,z5,z6]),(0,[z536,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z160,z2,z12,z5,z6]),(0,[z0,z1,z2,z3,z5,z537,z6])],[(0,[z0,z538,z1,z2,z3,z5,z6]),(0,[z155,z0,z400,z2,z3,z5,z6]),(0,[z0,z213,z2,z207,z3,z5,z6]),(0,[z0,z1,z2,z3,z51,z5,z6]),(0,[z0,z1,z2,z93,z3,z5,z72])],[(0,[z0,z1,z2,z539,z3,z5,z6]),(0,[z540,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z541,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z542]),(1,[z0,z81,z2,z3,z5,z11]),(0,[z0,z1,z2,z3,z5,z543,z6]),(0,[z0,z544,z1,z2,z3,z5,z6])],[(0,[z0,z35,z54,z2,z3,z5,z6]),(1,[z0,z153,z2,z3,z5,z6]),(0,[z0,z1,z2,z545,z3,z5,z6]),(0,[z0,z1,z2,z3,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z546,z6]),(0,[z0,z213,z1,z2,z3,z5,z18]),(0,[z0,z1,z160,z2,z24,z5,z6]),(0,[z0,z1,z2,z3,z5,z319,z18]),(0,[z0,z1,z2,z3,z5,z18,z72]),(0,[z547,z0,z1,z2,z3,z5,z6])],[(0,[z548,z0,z1,z2,z3,z5,z6]),(0,[z0,z549,z1,z2,z3,z5,z6])],[(0,[z0,z1,z550,z2,z3,z5,z6]),(1,[z0,z1,z2,z59,z5,z6]),(0,[z0,z1,z2,z3,z267,z5,z6]),(1,[z0,z1,z2,z3,z5,z18])]],
   [[(0,[z10,z0,z1,z2,z3,z5,z18]),(0,[z0,z551,z1,z2,z3,z5,z6])],[(0,[z36,z0,z1,z87,z3,z5,z6]),(1,[z0,z1,z2,z3,z5,z67])],[(0,[z28,z0,z35,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z552]),(0,[z0,z1,z2,z3,z5,z553,z6]),(0,[z0,z1,z2,z3,z5,z554,z6]),(0,[z92,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z31,z6]),(0,[z0,z1,z2,z3,z118,z5,z18]),(0,[z0,z1,z25,z2,z3,z5,z18]),(0,[z0,z1,z2,z12,z12,z5,z6]),(0,[z0,z1,z2,z12,z5,z17,z6]),(0,[z0,z1,z2,z3,z5,z45,z17]),(0,[z27,z0,z1,z2,z3,z5,z18]),(0,[z0,z1,z2,z3,z5,z6,z555])],[(0,[z0,z1,z2,z556,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z99,z17]),(0,[z0,z1,z2,z3,z557,z5,z6])],[(0,[z1,z87,z2,z226,z3,z5,z6]),(0,[z0,z1,z34,z2,z3,z5,z18]),(0,[z558,z0,z1,z2,z3,z5,z6])],[(0,[z0,z35,z1,z2,z3,z5,z559]),(0,[z0,z1,z560,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z5,z6]),(1,[z0,z561,z2,z3,z5,z6]),(1,[z0,z213,z2,z207,z5,z6]),(0,[z0,z1,z2,z12,z24,z5,z6]),(0,[z0,z1,z2,z24,z5,z6,z72]),(0,[z0,z1,z160,z2,z64,z5,z6])],[(0,[z0,z1,z2,z12,z69,z5,z6]),(0,[z0,z1,z562,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z563,z5,z6]),(0,[z105,z0,z1,z2,z3,z5,z6]),(0,[z333,z0,z1,z2,z12,z5,z6]),(0,[z0,z1,z2,z3,z51,z5,z18]),(0,[z49,z0,z1,z2,z3,z185,z5])],[(0,[z0,z1,z2,z3,z5,z564,z6]),(0,[z156,z0,z1,z2,z3,z5,z80]),(0,[z0,z1,z2,z565,z3,z5,z6])]],
   [[(0,[z78,z0,z1,z2,z3,z5,z478]),(0,[z0,z1,z2,z3,z5,z566,z18])],[(0,[z114,z0,z1,z2,z12,z5,z6]),(0,[z156,z0,z1,z2,z3,z185,z5]),(0,[z0,z1,z2,z3,z5,z567,z6]),(1,[z0,z1,z160,z3,z5,z17])],[(0,[z568,z0,z1,z2,z3,z5,z6]),(0,[z1,z2,z226,z3,z5,z70,z6]),(0,[z198,z0,z1,z2,z144,z5,z6]),(0,[z0,z1,z2,z3,z5,z569,z6]),(0,[z91,z0,z2,z21,z3,z5,z6]),(0,[z0,z1,z2,z3,z570,z5,z6]),(1,[z83,z0,z2,z181,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z32]),(0,[z52,z0,z1,z2,z3,z5,z266])],[(0,[z0,z1,z2,z3,z5,z6,z571]),(0,[z0,z572,z1,z2,z3,z5,z6]),(0,[z0,z1,z573,z2,z3,z5,z6]),(0,[z286,z0,z1,z2,z3,z5,z330])],[(0,[z0,z1,z574,z2,z3,z5,z6]),(0,[z143,z1,z2,z3,z5,z70,z6]),(0,[z114,z0,z1,z2,z24,z5,z6]),(0,[z0,z1,z2,z181,z24,z5,z6]),(0,[z49,z0,z213,z1,z2,z5,z6]),(0,[z575,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z576,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z46]),(0,[z0,z1,z87,z2,z3,z5,z485]),(0,[z0,z1,z2,z3,z5,z577,z6]),(0,[z0,z213,z1,z2,z24,z5,z6]),(0,[z0,z1,z2,z24,z393,z5,z6]),(0,[z0,z1,z2,z107,z3,z5,z6])],[(1,[z28,z20,z2,z3,z5,z6]),(0,[z578,z0,z1,z2,z3,z5,z6]),(0,[z30,z0,z1,z2,z12,z5,z6]),(0,[z0,z54,z1,z21,z3,z5,z6]),(0,[z0,z81,z1,z2,z3,z5,z18]),(1,[z0,z1,z2,z3,z5,z521]),(0,[z27,z0,z1,z2,z3,z108,z6]),(0,[z86,z0,z1,z2,z93,z3,z5])],[(0,[z0,z1,z2,z3,z5,z135,z6]),(0,[z114,z0,z1,z2,z3,z70,z6]),(0,[z1,z2,z3,z118,z5,z98,z6]),(0,[z579,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z24,z405,z5,z6]),(0,[z0,z1,z2,z3,z5,z580,z6]),(0,[z0,z1,z2,z3,z5,z581,z6]),(0,[z0,z1,z2,z3,z5,z6,z582])]],
   [[(0,[z0,z35,z1,z2,z12,z5,z6]),(0,[z36,z0,z1,z2,z12,z5,z6]),(0,[z0,z1,z2,z12,z5,z70,z6]),(0,[z0,z1,z583,z2,z3,z5,z6]),(0,[z0,z1,z2,z584,z3,z5,z6]),(0,[z0,z1,z2,z3,z118,z51,z6]),(0,[z0,z1,z2,z3,z5,z6,z585])],[(0,[z0,z1,z2,z3,z586,z5,z6]),(0,[z587,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z24,z5,z6,z227]),(0,[z0,z117,z2,z21,z3,z5,z6])],[(0,[z0,z1,z2,z226,z12,z5,z6]),(0,[z588,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z25,z2,z24,z5,z6]),(0,[z27,z0,z1,z2,z24,z5,z6])],[(0,[z78,z0,z1,z2,z3,z387,z6]),(0,[z36,z0,z1,z2,z24,z5,z6]),(0,[z0,z1,z2,z3,z5,z17,z270]),(0,[z0,z1,z2,z3,z5,z6,z589]),(0,[z0,z1,z2,z93,z3,z185,z5])],[(0,[z78,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z226,z3,z5,z17]),(0,[z0,z1,z34,z2,z24,z5,z6]),(0,[z0,z1,z2,z3,z590,z5,z6]),(0,[z52,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z591,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z592,z5,z6]),(0,[z0,z1,z2,z3,z5,z593,z6]),(0,[z0,z1,z594,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z595,z5,z6]),(0,[z0,z596,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z185,z65,z6])],[(0,[z156,z0,z1,z2,z3,z5,z6]),(0,[z49,z83,z0,z1,z2,z5,z6]),(0,[z0,z1,z2,z3,z597,z5,z6]),(0,[z0,z1,z2,z12,z137,z5,z6])],[(0,[z0,z1,z2,z3,z598,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z599]),(0,[z0,z1,z2,z161,z3,z5,z6]),(0,[z0,z192,z1,z2,z3,z5,z17]),(0,[z0,z1,z600,z2,z3,z5,z6])]],
   [[(0,[z0,z1,z2,z3,z5,z601,z6]),(0,[z173,z0,z1,z2,z3,z5,z6]),(0,[z0,z245,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z144,z3,z5,z6]),(0,[z382,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z602,z3,z5,z6]),(0,[z603,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z475,z6]),(0,[z186,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z604,z3,z5,z6]),(0,[z86,z30,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z21,z3,z5,z6]),(0,[z0,z1,z2,z605,z3,z5,z6]),(0,[z606,z0,z1,z2,z3,z5,z6]),(0,[z0,z2,z3,z5,z475,z45,z6]),(0,[z607,z1,z2,z3,z5,z6,z18]),(0,[z483,z0,z1,z2,z3,z5,z6])],[(0,[z184,z0,z1,z2,z3,z5,z6]),(0,[z28,z1,z20,z2,z3,z5,z6]),(0,[z0,z1,z87,z2,z12,z5,z6]),(0,[z163,z0,z1,z2,z3,z43,z5]),(0,[z155,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z608,z6]),(0,[z0,z1,z2,z609,z3,z5,z6])],[(1,[z0,z1,z2,z203,z5,z6]),(0,[z610,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z38,z6]),(0,[z49,z10,z0,z1,z2,z3,z5]),(0,[z89,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z218,z3,z5,z6]),(0,[z13,z0,z1,z2,z409,z5,z6])],[(0,[z0,z611,z1,z2,z3,z5,z6]),(0,[z78,z0,z153,z2,z3,z5,z6]),(0,[z612,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z613,z2,z3,z5,z6]),(0,[z205,z0,z1,z2,z3,z118,z6]),(0,[z614,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z24,z185,z5,z6])],[(0,[z0,z1,z2,z3,z5,z6,z615]),(0,[z0,z1,z2,z3,z616,z5,z6]),(0,[z0,z1,z2,z3,z5,z617,z6]),(0,[z201,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z618,z3,z5,z6]),(0,[z0,z619,z1,z2,z3,z5,z6]),(0,[z78,z0,z1,z2,z3,z5,z18]),(0,[z205,z0,z1,z2,z3,z5,z6])]],
   [[(0,[z0,z1,z2,z3,z620,z5,z6]),(0,[z0,z1,z2,z93,z3,z5,z6])],[(0,[z0,z1,z20,z2,z3,z5,z17]),(0,[z221,z0,z1,z2,z3,z5,z17]),(0,[z156,z0,z1,z2,z3,z5,z18]),(0,[z0,z1,z2,z3,z621,z5,z6])],[(0,[z622,z0,z1,z2,z3,z5,z6]),(0,[z155,z35,z1,z2,z3,z5,z6]),(1,[z163,z0,z1,z2,z3,z5]),(0,[z0,z1,z623,z2,z3,z5,z6]),(1,[z1,z2,z3,z5,z206,z18]),(0,[z0,z1,z2,z3,z185,z5,z66])],[(0,[z36,z0,z1,z226,z3,z5,z6]),(0,[z624,z0,z1,z2,z3,z5,z6]),(0,[z0,z117,z1,z2,z3,z31,z6]),(0,[z0,z1,z2,z625,z3,z5,z6]),(0,[z0,z1,z2,z3,z24,z5,z18])],[(0,[z0,z1,z2,z3,z69,z5,z18]),(0,[z0,z1,z2,z3,z5,z626,z6]),(0,[z0,z1,z2,z107,z3,z108,z6]),(0,[z0,z1,z2,z3,z627,z5,z6])],[(0,[z628,z0,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z355,z6]),(0,[z629,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z21,z3,z5,z18]),(0,[z0,z1,z2,z3,z183,z5,z6]),(1,[z0,z1,z2,z3,z267,z5]),(0,[z0,z1,z630,z2,z3,z5,z6]),(0,[z0,z1,z2,z107,z12,z5,z6])],[(0,[z155,z0,z1,z2,z3,z5,z18]),(0,[z631,z0,z1,z2,z3,z5,z6]),(0,[z0,z2,z207,z3,z181,z5,z6]),(0,[z0,z1,z2,z3,z5,z632,z6]),(0,[z0,z117,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z633,z6]),(0,[z184,z0,z1,z2,z3,z5,z18])],[(0,[z0,z1,z2,z3,z5,z6,z634]),(0,[z0,z1,z2,z3,z5,z38,z18]),(0,[z635,z0,z1,z2,z3,z5,z6]),(0,[z83,z0,z1,z2,z3,z5,z18]),(0,[z636,z0,z1,z2,z3,z5,z6]),(0,[z89,z0,z1,z2,z3,z5,z18]),(0,[z607,z0,z1,z2,z3,z5,z6]),(1,[z27,z0,z1,z2,z266,z6]),(0,[z0,z1,z2,z3,z637,z5,z6])]],
   [[(0,[z30,z1,z2,z3,z5,z70,z6]),(0,[z0,z1,z2,z3,z70,z45,z6]),(0,[z0,z1,z2,z5,z6,z402,z80]),(0,[z0,z1,z2,z107,z24,z5,z6])],[(0,[z638,z0,z1,z2,z3,z5,z6]),(0,[z639,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z181,z5,z17]),(0,[z0,z1,z2,z3,z5,z6,z640]),(0,[z641,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z185,z5,z17])],[(0,[z0,z1,z2,z3,z642,z5,z6]),(0,[z91,z0,z2,z3,z118,z5,z6]),(0,[z0,z1,z2,z3,z643,z5,z6]),(0,[z205,z0,z1,z2,z3,z5,z18]),(0,[z0,z1,z2,z24,z5,z276,z6])],[(0,[z0,z1,z2,z644,z3,z5,z6]),(1,[z0,z1,z2,z3,z5,z478]),(0,[z49,z0,z1,z2,z12,z5,z6]),(0,[z0,z1,z2,z12,z5,z71,z6]),(0,[z0,z1,z2,z93,z3,z5,z18])],[(0,[z1,z20,z2,z226,z3,z5,z6]),(0,[z0,z1,z2,z3,z645,z5,z6]),(0,[z155,z0,z561,z2,z3,z5,z6]),(0,[z646,z0,z1,z2,z3,z5,z6]),(0,[z406,z1,z2,z3,z118,z5,z6]),(0,[z0,z1,z2,z3,z647,z5,z6]),(0,[z162,z0,z1,z2,z12,z5,z6]),(0,[z0,z1,z2,z648,z3,z5,z6]),(1,[z607,z1,z2,z3,z5,z6]),(0,[z0,z1,z649,z2,z3,z5,z6]),(0,[z86,z0,z1,z2,z3,z5,z66])],[(0,[z0,z1,z2,z650,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z651]),(0,[z652,z0,z1,z2,z3,z5,z6]),(0,[z653,z0,z1,z2,z3,z5,z6])],[(0,[z205,z0,z20,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z654,z5,z6]),(0,[z438,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z70,z18]),(0,[z0,z655,z1,z2,z3,z5,z6]),(0,[z30,z0,z1,z2,z93,z3,z5]),(0,[z49,z0,z1,z2,z24,z5,z6]),(0,[z0,z1,z2,z3,z5,z17,z139]),(0,[z0,z1,z2,z3,z5,z178,z6])],[(0,[z78,z0,z1,z2,z24,z5,z6]),(0,[z0,z1,z2,z656,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z251]),(0,[z0,z1,z467,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z169]),(0,[z0,z1,z2,z3,z657,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z658]),(0,[z0,z1,z2,z3,z5,z6,z66])]],
   [[(0,[z0,z1,z659,z2,z3,z5,z6]),(0,[z205,z0,z117,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z660,z5,z6])],[(0,[z0,z1,z2,z144,z12,z5,z6]),(0,[z156,z0,z1,z2,z24,z5,z6]),(0,[z0,z117,z1,z2,z3,z5,z18]),(0,[z0,z1,z2,z12,z5,z6,z80]),(0,[z0,z1,z2,z3,z5,z65,z17])],[(0,[z0,z1,z2,z661,z3,z5,z6]),(0,[z198,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z69,z51,z6]),(0,[z0,z1,z2,z3,z662,z5,z6]),(0,[z0,z1,z2,z605,z12,z5,z6]),(0,[z607,z0,z1,z2,z3,z5,z18])],[(0,[z35,z1,z2,z3,z5,z70,z6]),(0,[z91,z0,z1,z21,z3,z5,z6]),(0,[z0,z213,z1,z2,z5,z71,z6]),(0,[z0,z1,z2,z3,z5,z235,z6]),(0,[z0,z1,z2,z3,z5,z17,z72]),(0,[z86,z0,z1,z2,z3,z5,z17]),(0,[z27,z174,z1,z2,z3,z5,z6])],[(1,[z221,z35,z2,z3,z5,z6]),(0,[z0,z1,z2,z144,z24,z5,z6]),(0,[z0,z1,z2,z3,z292,z5,z70]),(0,[z663,z0,z1,z2,z3,z5,z6]),(0,[z603,z0,z1,z2,z24,z5,z6]),(0,[z0,z1,z2,z664,z3,z5,z6]),(0,[z49,z0,z1,z2,z93,z5,z6])],[(0,[z0,z1,z2,z3,z5,z665,z6]),(0,[z0,z1,z2,z666,z3,z5,z6]),(0,[z0,z1,z2,z21,z24,z5,z6]),(0,[z0,z1,z2,z667,z3,z5,z6]),(1,[z0,z1,z2,z5,z6,z668]),(1,[z0,z1,z2,z3,z185,z65])],[(0,[z0,z1,z2,z3,z5,z355,z6]),(1,[z0,z1,z2,z3,z387,z6]),(0,[z155,z0,z1,z2,z24,z5,z6]),(0,[z0,z1,z2,z669,z3,z5,z6]),(1,[z92,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z24,z5,z11,z6]),(0,[z184,z0,z1,z2,z24,z5,z6]),(0,[z0,z1,z670,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z671])],[(1,[z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z672,z2,z3,z5,z6]),(0,[z143,z0,z1,z2,z3,z5,z17]),(0,[z673,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z496,z24,z5,z6]),(0,[z89,z0,z1,z2,z24,z5,z6]),(1,[z607,z1,z2,z3,z5,z18]),(0,[z674,z0,z1,z2,z3,z5,z6])]],
   [[(0,[z0,z1,z87,z2,z134,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z225]),(0,[z27,z0,z1,z2,z5,z71,z6])],[(0,[z155,z0,z1,z2,z3,z70,z6]),(0,[z0,z1,z2,z3,z5,z486,z6]),(0,[z0,z1,z2,z5,z6,z668,z66])],[(0,[z0,z1,z2,z3,z5,z559,z6]),(0,[z0,z1,z2,z3,z118,z5,z6]),(0,[z205,z0,z1,z2,z24,z5,z6]),(0,[z0,z1,z2,z26,z3,z5,z6]),(0,[z675,z0,z1,z2,z3,z5,z6])],[(0,[z221,z0,z35,z2,z3,z5,z6]),(1,[z78,z1,z226,z3,z5,z6]),(0,[z0,z1,z2,z3,z676,z5,z6]),(0,[z0,z2,z21,z3,z5,z31,z6]),(0,[z0,z1,z2,z3,z677,z5,z6]),(0,[z0,z1,z2,z93,z24,z5,z6]),(0,[z0,z1,z2,z12,z5,z65,z6]),(0,[z0,z224,z1,z2,z3,z5,z6]),(0,[z0,z1,z34,z2,z202,z5,z6]),(0,[z294,z0,z1,z2,z3,z5,z17]),(0,[z0,z1,z2,z3,z5,z678,z6]),(0,[z0,z1,z2,z679,z3,z5,z6])],[(0,[z680,z0,z1,z2,z3,z5,z6]),(1,[z0,z1,z25,z12,z5,z6])],[(0,[z198,z0,z1,z2,z3,z5,z18]),(0,[z205,z0,z1,z2,z3,z70,z6]),(0,[z0,z54,z1,z2,z3,z5,z6]),(0,[z681,z0,z1,z2,z3,z5,z6])],[(0,[z205,z0,z58,z2,z3,z5,z6]),(0,[z0,z1,z2,z446,z24,z5,z6]),(0,[z0,z1,z2,z12,z269,z5,z6]),(0,[z49,z0,z1,z2,z3,z5,z71]),(0,[z0,z1,z2,z3,z5,z6,z668])],[(0,[z78,z1,z2,z3,z5,z38,z6]),(0,[z198,z143,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z682,z3,z5,z6]),(0,[z0,z1,z160,z2,z3,z5,z17])]],
   [[(0,[z0,z1,z561,z2,z3,z5,z6]),(0,[z156,z0,z1,z2,z3,z5,z227]),(0,[z0,z213,z1,z2,z207,z5,z6]),(0,[z0,z1,z2,z683,z3,z5,z6]),(0,[z629,z0,z1,z2,z24,z5,z6]),(0,[z0,z1,z2,z3,z5,z311,z17])],[(0,[z0,z1,z2,z3,z5,z684,z6]),(1,[z0,z1,z2,z3,z5,z485]),(0,[z685,z0,z1,z2,z3,z5,z6]),(0,[z86,z156,z0,z1,z2,z3,z5]),(0,[z0,z117,z1,z2,z24,z5,z6]),(0,[z639,z0,z1,z2,z12,z5,z6]),(0,[z0,z1,z2,z12,z108,z5,z6]),(0,[z174,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z686,z5,z6]),(0,[z0,z687,z1,z2,z3,z5,z6]),(0,[z0,z1,z58,z2,z3,z5,z247]),(0,[z0,z1,z2,z3,z5,z11,z17]),(0,[z0,z1,z2,z3,z5,z6,z510])],[(0,[z688,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z689,z3,z5,z6]),(0,[z0,z326,z1,z2,z3,z5,z6]),(0,[z286,z0,z1,z25,z3,z5,z6]),(0,[z0,z690,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z320,z17]),(0,[z0,z1,z2,z3,z5,z266,z17])],[(0,[z0,z1,z2,z3,z5,z6,z94]),(1,[z0,z1,z2,z3,z5,z559]),(0,[z0,z1,z2,z3,z43,z5,z6]),(0,[z0,z1,z2,z3,z5,z691,z6]),(0,[z0,z1,z2,z648,z12,z5,z6])],[(0,[z692,z0,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z5,z390]),(0,[z0,z1,z2,z26,z3,z5,z18])],[(0,[z155,z1,z2,z3,z5,z38,z6]),(1,[z0,z1,z2,z3,z157,z6]),(1,[z0,z117,z2,z3,z118,z6]),(0,[z0,z81,z1,z2,z3,z5,z6])],[(0,[z78,z0,z1,z2,z125,z5,z6]),(1,[z91,z0,z21,z3,z5,z6]),(1,[z205,z0,z2,z3,z31,z6]),(0,[z0,z1,z2,z12,z3,z5,z17])]],
   [[(0,[z28,z0,z1,z2,z3,z5,z6]),(0,[z114,z0,z1,z2,z3,z69,z6]),(0,[z0,z54,z1,z2,z3,z5,z18]),(0,[z653,z0,z1,z2,z24,z5,z6]),(0,[z0,z1,z12,z3,z24,z5,z6]),(0,[z0,z1,z25,z2,z3,z5,z390]),(0,[z13,z0,z1,z2,z511,z5,z6])],[(0,[z221,z28,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z693,z5,z6]),(0,[z694,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z695,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z17,z80]),(0,[z0,z1,z2,z3,z5,z521,z6]),(0,[z0,z1,z2,z3,z5,z71,z18])],[(0,[z0,z1,z2,z696,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z6,z697]),(0,[z0,z1,z2,z237,z3,z5,z6]),(0,[z0,z698,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z330]),(0,[z0,z1,z2,z3,z5,z6,z132]),(0,[z0,z1,z2,z93,z3,z5,z71])],[(0,[z0,z54,z20,z2,z3,z5,z6]),(0,[z0,z1,z2,z24,z51,z5,z6])],[(0,[z0,z213,z1,z2,z12,z5,z6]),(0,[z10,z0,z2,z3,z5,z6,z80]),(0,[z0,z1,z2,z3,z322,z5,z6]),(0,[z0,z1,z2,z12,z5,z266,z6]),(0,[z0,z687,z1,z2,z3,z5,z18]),(0,[z0,z1,z2,z3,z5,z6,z699])],[(0,[z35,z1,z20,z2,z3,z5,z6]),(0,[z114,z0,z1,z2,z3,z5,z17]),(0,[z0,z1,z58,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z5,z199]),(0,[z700,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z701,z6]),(0,[z702,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z566]),(0,[z0,z1,z2,z703,z3,z5,z6])],[(0,[z0,z1,z2,z3,z43,z5,z18]),(0,[z0,z1,z2,z3,z5,z6,z704]),(0,[z705,z0,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z12,z5,z6]),(0,[z0,z1,z2,z12,z5,z45,z6]),(0,[z63,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z706])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z96,z24,z5,z6]),(0,[z1,z2,z3,z5,z707,z6]),(0,[z0,z1,z2,z3,z5,z708]),(0,[z326,z1,z2,z3,z5,z17])],[(0,[z113,z1,z2,z3,z70,z6]),(0,[z0,z1,z2,z3,z709,z5]),(0,[z710,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z18,z711]),(0,[z0,z1,z3,z5,z18,z671])],[(0,[z221,z370,z2,z3,z5,z6]),(0,[z712,z1,z2,z3,z5,z6])],[(0,[z607,z1,z2,z3,z5,z6]),(0,[z0,z1,z61,z3,z5,z18]),(0,[z1,z2,z3,z5,z6,z713]),(0,[z0,z1,z160,z64,z5,z17])],[(0,[z0,z1,z2,z714,z5,z6]),(0,[z715,z1,z2,z3,z5,z6]),(0,[z716,z1,z2,z3,z5,z18])],[(0,[z0,z1,z344,z24,z5,z6])],[],[(0,[z0,z1,z2,z3,z717,z5]),(0,[z1,z2,z24,z5,z206,z18])],[(0,[z0,z1,z2,z718,z5,z6]),(0,[z0,z54,z1,z24,z5,z18]),(0,[z194,z0,z213,z1,z2,z5])],[(0,[z0,z1,z2,z3,z5,z719]),(0,[z0,z1,z2,z125,z5,z18]),(0,[z720,z1,z2,z3,z5,z6])],[(0,[z721,z1,z2,z3,z5,z6]),(0,[z0,z54,z58,z284,z5,z6])],[(0,[z0,z117,z2,z3,z469,z6]),(0,[z438,z1,z2,z3,z5,z139])],[(0,[z205,z0,z2,z3,z516,z6]),(0,[z0,z1,z2,z3,z5,z722]),(0,[z0,z1,z34,z24,z51,z6])],[(0,[z92,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z723]),(0,[z143,z1,z2,z144,z5,z17]),(0,[z724,z1,z2,z3,z5,z6]),(0,[z10,z0,z2,z24,z5,z80]),(0,[z389,z0,z1,z3,z5,z18]),(0,[z0,z1,z2,z202,z5,z6]),(0,[z0,z1,z2,z3,z5,z725]),(0,[z607,z1,z2,z26,z3,z5]),(0,[z712,z1,z2,z3,z5,z18]),(0,[z0,z1,z600,z3,z5,z17])],[(0,[z294,z1,z2,z3,z5,z38]),(0,[z607,z1,z2,z3,z5,z18])],[(0,[z0,z1,z2,z3,z5,z726]),(0,[z89,z0,z1,z24,z45,z6]),(0,[z607,z1,z2,z3,z5,z319])]],
   [[(0,[z727,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z728,z66])],[(0,[z0,z729,z2,z3,z5,z6]),(0,[z0,z730,z2,z12,z5,z6])],[(0,[z1,z2,z144,z731,z5,z6]),(0,[z0,z1,z2,z732,z5,z6]),(0,[z415,z0,z1,z3,z5,z18]),(0,[z0,z1,z2,z733,z5,z6]),(0,[z0,z2,z3,z5,z475,z17]),(0,[z0,z734,z2,z3,z5,z17]),(0,[z0,z1,z2,z107,z735,z6])],[(0,[z736,z0,z1,z2,z3,z5]),(0,[z737,z0,z1,z2,z5,z6]),(0,[z0,z1,z2,z5,z17,z402])],[(0,[z0,z1,z2,z5,z6,z738]),(0,[z0,z1,z2,z3,z5,z739])],[(0,[z0,z1,z666,z24,z5,z6]),(0,[z0,z1,z241,z3,z5,z18])],[(0,[z0,z1,z2,z3,z76,z65])],[(0,[z0,z1,z2,z24,z355,z6]),(0,[z0,z1,z2,z3,z5,z740]),(0,[z0,z1,z2,z5,z741,z6]),(0,[z0,z127,z2,z3,z5,z11]),(0,[z119,z0,z2,z24,z5,z6]),(0,[z0,z1,z2,z3,z5,z742])],[(0,[z0,z1,z2,z3,z5,z485]),(0,[z323,z1,z2,z43,z5,z6]),(0,[z0,z1,z2,z202,z5,z18])],[(0,[z0,z743,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z744]),(0,[z607,z1,z2,z3,z360,z5])],[(0,[z221,z721,z2,z3,z5,z6]),(0,[z0,z1,z2,z12,z5,z478]),(0,[z1,z2,z3,z745,z70,z6]),(0,[z0,z1,z2,z746,z5,z6]),(0,[z131,z1,z2,z24,z5,z6]),(0,[z0,z1,z2,z108,z735,z6])],[(0,[z0,z1,z2,z3,z5,z559]),(0,[z0,z1,z2,z3,z5,z747]),(0,[z0,z232,z2,z3,z5,z279]),(0,[z0,z1,z748,z3,z5,z6]),(0,[z0,z1,z2,z237,z5,z6]),(0,[z0,z1,z2,z5,z6,z749])],[(0,[z1,z2,z3,z79,z38,z6]),(0,[z0,z750,z2,z3,z5,z6]),(0,[z92,z1,z2,z3,z157,z6]),(0,[z205,z0,z2,z3,z751,z6])],[(0,[z0,z1,z2,z3,z5,z752]),(0,[z0,z1,z2,z3,z157,z6]),(0,[z607,z1,z3,z5,z17,z18])],[(0,[z0,z1,z2,z753,z5,z6]),(0,[z0,z153,z2,z3,z79,z6]),(0,[z1,z2,z226,z3,z79,z6]),(0,[z332,z0,z1,z24,z5,z6]),(0,[z40,z81,z2,z3,z5,z11]),(0,[z264,z1,z2,z3,z5,z17])],[(0,[z27,z0,z1,z2,z564,z6]),(0,[z0,z54,z58,z3,z5,z247]),(0,[z0,z1,z2,z754,z5,z6]),(0,[z0,z1,z2,z3,z5,z755]),(0,[z0,z1,z12,z349,z5,z6])]],
   [[(0,[z1,z2,z756,z3,z5,z6]),(0,[z1,z2,z3,z5,z757,z6]),(0,[z758,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z759,z5,z6]),(0,[z0,z760,z2,z3,z5,z6]),(0,[z156,z1,z2,z24,z5,z38]),(0,[z0,z1,z25,z12,z5,z390]),(0,[z0,z467,z2,z3,z5,z169]),(0,[z1,z2,z3,z5,z17,z206]),(0,[z27,z52,z0,z1,z2,z266])],[(0,[z0,z761,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z762]),(0,[z174,z1,z2,z24,z5,z6])],[(0,[z0,z1,z2,z3,z5,z763]),(0,[z764,z0,z1,z2,z24,z5])],[(0,[z313,z187,z1,z2,z5,z6])],[(0,[z0,z1,z2,z12,z387,z6]),(0,[z0,z765,z2,z3,z5,z6]),(0,[z92,z1,z2,z12,z5,z6]),(0,[z0,z213,z2,z766,z5,z6]),(1,[z0,z1,z2,z5,z767])],[(0,[z0,z1,z2,z12,z5,z6]),(0,[z221,z35,z2,z24,z5,z6]),(0,[z0,z1,z2,z237,z5,z18]),(0,[z607,z1,z2,z12,z5,z18])],[(0,[z224,z1,z2,z414,z5,z6])],[(0,[z0,z1,z2,z5,z768,z6]),(0,[z0,z467,z2,z3,z5,z17])],[(0,[z0,z1,z2,z3,z769,z6]),(0,[z0,z1,z2,z3,z770,z6]),(1,[z0,z2,z3,z5,z771])],[(0,[z20,z2,z454,z3,z5,z6]),(0,[z0,z1,z301,z3,z5,z18]),(0,[z0,z1,z2,z3,z5,z772]),(0,[z0,z1,z2,z5,z773,z6]),(0,[z1,z2,z3,z5,z707,z227]),(0,[z0,z2,z24,z5,z774,z6])],[(0,[z1,z2,z3,z98,z45,z6])],[(0,[z0,z1,z2,z3,z4,z18]),(0,[z0,z1,z12,z399,z5,z6])],[(0,[z78,z1,z226,z24,z5,z6]),(0,[z0,z2,z3,z775,z5,z6]),(0,[z0,z1,z2,z3,z5,z776]),(0,[z0,z777,z2,z3,z5,z6]),(0,[z607,z1,z2,z3,z5,z227]),(0,[z91,z0,z21,z3,z157,z6])],[(0,[z0,z1,z3,z5,z778,z18])],[(0,[z0,z1,z2,z3,z779,z5]),(0,[z83,z0,z2,z766,z5,z6])]],
   [[(0,[z0,z1,z2,z12,z5,z485]),(0,[z0,z1,z2,z3,z5,z780]),(0,[z781,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z782,z5,z6])],[(0,[z0,z1,z2,z3,z5,z783]),(0,[z0,z1,z659,z12,z5,z6]),(0,[z40,z1,z2,z24,z5,z6]),(0,[z0,z1,z2,z12,z5,z18]),(0,[z0,z1,z2,z64,z5,z6]),(0,[z224,z1,z2,z436,z5,z6])],[(0,[z0,z1,z2,z3,z5,z784]),(0,[z785,z1,z2,z3,z5,z6]),(0,[z1,z2,z12,z786,z5,z6]),(0,[z0,z1,z2,z5,z6,z787])],[(0,[z0,z1,z2,z59,z5,z17]),(0,[z1,z2,z3,z51,z98,z6]),(0,[z187,z1,z2,z3,z5,z17])],[(0,[z0,z1,z2,z3,z5,z788]),(0,[z694,z1,z2,z3,z70,z6])],[(0,[z0,z1,z2,z789,z5,z6]),(0,[z0,z1,z2,z3,z5,z790]),(0,[z0,z791,z2,z3,z5,z6]),(0,[z1,z2,z731,z43,z5,z6]),(0,[z0,z1,z2,z12,z157,z6]),(0,[z0,z58,z3,z5,z268,z6]),(0,[z0,z213,z2,z496,z5,z6]),(0,[z0,z1,z2,z24,z5,z235])],[(0,[z91,z0,z21,z12,z5,z6]),(0,[z0,z1,z116,z24,z5,z6])],[(0,[z572,z20,z2,z3,z5,z6]),(0,[z0,z1,z2,z792,z3,z5]),(0,[z0,z1,z2,z3,z793,z6]),(0,[z794,z0,z2,z24,z5,z6]),(0,[z0,z1,z2,z24,z5,z390]),(0,[z607,z1,z2,z3,z5,z46])],[(0,[z0,z54,z58,z3,z5,z67]),(0,[z795,z0,z1,z2,z5,z18])],[(0,[z0,z1,z2,z796,z5,z6]),(0,[z1,z2,z3,z731,z5,z6]),(0,[z0,z213,z2,z207,z5,z17]),(0,[z205,z0,z2,z24,z31,z6])],[(0,[z35,z2,z3,z469,z5,z6])],[(0,[z0,z1,z2,z3,z797,z6]),(0,[z0,z1,z2,z3,z5,z798]),(0,[z0,z1,z2,z3,z5,z799]),(0,[z0,z1,z800,z3,z5,z6]),(0,[z0,z1,z2,z3,z185,z566]),(0,[z801,z1,z2,z3,z5,z6])],[(0,[z612,z1,z2,z3,z70,z6]),(0,[z30,z1,z2,z3,z5,z593]),(0,[z802,z1,z2,z3,z5,z6]),(0,[z0,z1,z24,z5,z6,z123]),(0,[z0,z1,z2,z64,z5,z18])],[(0,[z1,z2,z3,z5,z98,z6]),(0,[z0,z1,z87,z24,z5,z18]),(0,[z0,z1,z2,z803,z5,z6]),(0,[z119,z0,z2,z3,z118,z6]),(0,[z0,z1,z2,z3,z5,z330]),(0,[z1,z2,z3,z5,z804,z132])],[(0,[z0,z1,z2,z3,z805,z6]),(0,[z0,z1,z2,z806,z5,z6]),(0,[z86,z0,z1,z2,z3,z191])],[(0,[z0,z54,z807,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z808])]],
   [[(0,[z0,z1,z2,z24,z5,z199])],[(0,[z0,z1,z34,z24,z5,z18])],[(0,[z221,z127,z2,z3,z5,z6]),(0,[z809,z1,z2,z3,z5,z6]),(0,[z0,z1,z695,z3,z51,z6])],[(0,[z0,z1,z2,z3,z5,z810]),(0,[z0,z1,z2,z134,z5,z6]),(0,[z1,z2,z3,z5,z38,z485]),(0,[z811,z1,z2,z3,z5,z6]),(0,[z0,z245,z2,z3,z5,z18])],[(0,[z0,z812,z2,z3,z5,z6])],[(0,[z0,z1,z2,z813,z3,z5]),(0,[z814,z1,z2,z3,z5,z6]),(0,[z0,z1,z423,z12,z5,z6])],[(0,[z133,z1,z226,z3,z5,z6]),(0,[z81,z326,z2,z3,z5,z11]),(0,[z0,z1,z2,z5,z71,z589])],[(0,[z0,z1,z2,z815,z5,z6]),(0,[z816,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z817,z5,z6]),(0,[z0,z2,z3,z5,z11,z771]),(0,[z0,z818,z2,z3,z5,z6])],[(0,[z83,z194,z0,z1,z2,z5]),(0,[z1,z2,z3,z5,z98,z18])],[(0,[z0,z819,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z820,z6]),(0,[z166,z0,z1,z2,z5,z6])],[(0,[z0,z821,z2,z3,z5,z6]),(0,[z0,z1,z2,z371,z5,z6]),(0,[z194,z0,z1,z2,z24,z5]),(0,[z822,z1,z2,z3,z5,z6])],[(0,[z823,z0,z1,z2,z5,z17])],[(0,[z1,z2,z12,z5,z6,z206]),(0,[z13,z0,z1,z3,z5,z18])],[(0,[z0,z1,z2,z134,z5,z485]),(0,[z10,z0,z2,z3,z5,z771]),(0,[z824,z0,z1,z2,z5,z6])],[(0,[z0,z1,z2,z134,z5,z18]),(0,[z0,z1,z2,z825,z5,z6]),(0,[z826,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z827,z3,z5]),(0,[z828,z0,z1,z2,z3,z5])],[(0,[z829,z0,z1,z2,z5,z6]),(0,[z0,z1,z2,z830,z5,z6])]],
   [[(0,[z0,z1,z2,z203,z5,z17])],[(0,[z0,z1,z2,z3,z5,z831]),(0,[z0,z232,z2,z3,z5,z478]),(0,[z36,z561,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z216])],[(0,[z832,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z833]),(0,[z834,z1,z2,z3,z5,z98]),(0,[z0,z1,z2,z835,z5,z6]),(0,[z162,z0,z1,z2,z5,z72]),(0,[z0,z245,z2,z3,z5,z521])],[(0,[z0,z1,z61,z12,z5,z6]),(0,[z0,z1,z2,z107,z168,z6])],[(0,[z0,z2,z3,z5,z836,z6]),(0,[z0,z837,z2,z3,z5,z6]),(0,[z0,z2,z766,z181,z5,z6]),(0,[z166,z0,z1,z2,z5,z18])],[(0,[z0,z1,z2,z3,z838,z5]),(0,[z0,z1,z2,z3,z258,z6]),(0,[z0,z1,z2,z371,z5,z18]),(0,[z0,z1,z2,z839,z5,z6])],[(0,[z0,z1,z2,z840,z5,z6]),(0,[z0,z1,z2,z841,z5,z6]),(0,[z0,z1,z2,z3,z5,z842]),(0,[z1,z2,z3,z5,z6,z843]),(0,[z844,z0,z1,z2,z5,z17]),(0,[z0,z730,z2,z3,z5,z17])],[(0,[z1,z2,z3,z5,z713,z247]),(0,[z0,z1,z2,z12,z267,z5]),(0,[z845,z0,z1,z2,z24,z6])],[(0,[z0,z1,z2,z846,z5,z6])],[(0,[z0,z1,z2,z847,z5,z6]),(0,[z131,z1,z2,z3,z5,z199]),(0,[z0,z807,z21,z3,z5,z6]),(0,[z89,z0,z3,z475,z45,z6])],[(0,[z0,z1,z2,z3,z5,z848]),(0,[z849,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z93,z5,z71])],[(0,[z0,z1,z2,z850,z5,z6]),(0,[z0,z1,z2,z48,z24,z5]),(0,[z155,z1,z2,z3,z337,z6]),(0,[z0,z1,z3,z5,z318,z18]),(0,[z0,z1,z2,z3,z5,z851]),(0,[z49,z0,z1,z2,z5,z72])],[(0,[z28,z721,z2,z3,z5,z6]),(0,[z0,z232,z2,z3,z387,z6]),(0,[z78,z1,z226,z3,z79,z6]),(0,[z431,z1,z226,z3,z5,z6]),(0,[z0,z1,z2,z203,z5,z135]),(0,[z198,z187,z1,z2,z5,z6]),(0,[z852,z1,z2,z3,z5,z6])],[(0,[z0,z232,z2,z3,z5,z6]),(0,[z0,z1,z2,z853,z5,z6]),(0,[z119,z0,z2,z3,z70,z6]),(0,[z493,z1,z2,z3,z69,z6]),(0,[z92,z1,z2,z237,z5,z6]),(0,[z0,z1,z2,z3,z5,z854]),(0,[z712,z1,z2,z12,z5,z6])],[(0,[z78,z1,z756,z3,z5,z6]),(0,[z117,z1,z2,z3,z98,z6]),(0,[z607,z1,z2,z12,z5,z6])],[(0,[z0,z1,z226,z24,z5,z18]),(0,[z0,z2,z12,z5,z475,z6]),(0,[z0,z818,z2,z12,z5,z6])]],
   [[(0,[z0,z1,z2,z3,z258,z18]),(0,[z49,z40,z1,z2,z3,z5])],[(0,[z0,z1,z2,z3,z5,z855]),(0,[z0,z467,z2,z436,z5,z6]),(0,[z0,z1,z670,z3,z5,z18])],[(0,[z406,z20,z2,z3,z5,z6]),(0,[z0,z1,z2,z375,z5,z478]),(0,[z0,z1,z2,z856,z5,z6]),(0,[z406,z117,z2,z3,z118,z6]),(0,[z857,z0,z1,z2,z3,z5])],[(0,[z0,z1,z2,z3,z5,z858]),(0,[z0,z1,z2,z859,z5,z6]),(0,[z860,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z5,z6,z861])],[(0,[z406,z561,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z169]),(0,[z0,z1,z2,z862,z5,z6])],[(0,[z91,z0,z21,z3,z258,z6]),(0,[z112,z467,z2,z3,z5,z6]),(0,[z0,z863,z2,z3,z5,z6])],[(0,[z27,z52,z0,z1,z2,z5])],[(0,[z30,z1,z2,z3,z5,z227]),(0,[z0,z1,z2,z284,z5,z6])],[(0,[z0,z232,z2,z3,z5,z18]),(0,[z0,z864,z2,z3,z5,z6])],[(0,[z1,z2,z3,z654,z70,z6]),(0,[z0,z1,z2,z3,z865,z6]),(0,[z0,z1,z25,z12,z5,z251])],[(0,[z0,z1,z2,z3,z387,z17]),(0,[z0,z1,z2,z3,z5,z866]),(0,[z92,z1,z2,z3,z5,z17]),(0,[z653,z0,z2,z181,z5,z6]),(0,[z0,z1,z2,z3,z5,z867]),(0,[z0,z1,z3,z5,z18,z308])],[(0,[z0,z1,z2,z3,z5,z17])],[(0,[z0,z1,z2,z868,z5,z6])],[(0,[z0,z1,z2,z3,z869,z6]),(0,[z163,z0,z1,z2,z12,z5]),(0,[z0,z1,z2,z237,z157,z6]),(0,[z0,z219,z2,z3,z118,z6])],[(0,[z0,z1,z2,z375,z5,z6]),(0,[z91,z0,z21,z237,z5,z6]),(0,[z406,z1,z2,z24,z5,z6])],[(0,[z0,z1,z2,z375,z5,z279]),(0,[z0,z1,z2,z870,z5,z6]),(0,[z871,z1,z2,z3,z5,z6])]],
   [[(0,[z0,z1,z2,z3,z5,z872]),(0,[z795,z0,z1,z2,z5,z6])],[(0,[z36,z1,z2,z3,z355,z6]),(0,[z36,z1,z87,z203,z5,z6]),(0,[z40,z1,z2,z3,z5,z11]),(0,[z0,z1,z2,z414,z5,z521])],[(0,[z0,z873,z2,z3,z5,z6]),(0,[z0,z874,z2,z3,z5,z6]),(0,[z0,z1,z2,z284,z5,z18]),(0,[z0,z1,z2,z24,z875,z6]),(0,[z0,z876,z2,z3,z5,z6]),(0,[z27,z174,z1,z2,z266,z6])],[(0,[z0,z1,z2,z24,z79,z6]),(0,[z224,z1,z2,z24,z5,z6]),(0,[z877,z0,z1,z2,z12,z5]),(0,[z0,z878,z2,z3,z5,z17])],[(0,[z0,z1,z2,z3,z879,z6]),(0,[z114,z1,z2,z3,z70,z6]),(0,[z128,z0,z21,z3,z5,z6])],[(0,[z0,z232,z2,z12,z5,z6]),(0,[z0,z1,z583,z3,z5,z18]),(0,[z880,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z93,z474,z5])],[(0,[z0,z1,z2,z12,z5,z559]),(0,[z0,z1,z2,z881,z5,z6]),(0,[z0,z882,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z778])],[(0,[z0,z1,z2,z3,z5,z135]),(0,[z49,z0,z211,z1,z2,z5]),(0,[z883,z1,z2,z3,z5,z6]),(0,[z294,z1,z2,z3,z5,z271])],[(0,[z1,z2,z3,z5,z884,z6])],[(0,[z0,z1,z2,z3,z5,z94]),(0,[z0,z1,z2,z3,z5,z885]),(0,[z0,z1,z2,z375,z5,z18]),(0,[z0,z1,z2,z24,z5,z50]),(0,[z0,z1,z2,z3,z886,z5])],[(0,[z0,z1,z2,z3,z5,z887]),(0,[z0,z1,z301,z12,z5,z6]),(0,[z0,z1,z2,z3,z157,z17]),(0,[z0,z305,z2,z605,z5,z6])],[(0,[z0,z245,z2,z3,z5,z6]),(0,[z91,z0,z21,z3,z5,z17]),(0,[z326,z1,z2,z24,z5,z6]),(0,[z0,z1,z2,z436,z5,z521])],[(0,[z0,z1,z2,z12,z4,z6]),(0,[z313,z114,z1,z2,z70,z6]),(0,[z0,z1,z2,z3,z5,z247]),(0,[z0,z54,z481,z3,z5,z6]),(0,[z0,z1,z2,z12,z5,z169]),(0,[z264,z1,z2,z3,z185,z65])],[(0,[z0,z1,z34,z218,z51,z6])],[(0,[z0,z888,z2,z3,z5,z6]),(0,[z63,z0,z1,z2,z5,z32]),(0,[z607,z1,z2,z93,z3,z5]),(0,[z49,z0,z1,z2,z621,z5])],[(0,[z114,z1,z2,z3,z70,z18]),(0,[z0,z1,z2,z3,z889,z6]),(0,[z0,z1,z2,z24,z5,z251]),(0,[z112,z1,z2,z3,z5,z521]),(0,[z0,z1,z2,z3,z5,z890])]],
   [[(0,[z0,z1,z2,z3,z891,z6]),(0,[z0,z1,z2,z3,z892,z5]),(0,[z0,z1,z2,z3,z735,z6])],[(0,[z0,z1,z2,z108,z102,z6]),(0,[z0,z81,z2,z3,z5,z771])],[(0,[z0,z1,z2,z893,z5,z6])],[(0,[z894,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z12,z5,z17])],[(0,[z0,z1,z2,z3,z895,z6]),(0,[z0,z1,z2,z3,z896,z6]),(0,[z156,z1,z2,z3,z557,z5]),(0,[z0,z897,z2,z3,z5,z6])],[(0,[z0,z1,z756,z3,z5,z6]),(0,[z0,z1,z2,z3,z898,z5]),(0,[z0,z1,z2,z3,z5,z899]),(0,[z49,z0,z1,z2,z642,z5]),(0,[z0,z401,z2,z3,z5,z80]),(0,[z900,z1,z2,z3,z5,z6]),(0,[z0,z1,z3,z5,z17,z778])],[(0,[z0,z1,z2,z3,z5,z901])],[(0,[z0,z1,z2,z3,z5,z902]),(0,[z0,z1,z2,z59,z5,z247]),(0,[z0,z1,z12,z24,z5,z6]),(0,[z463,z0,z1,z3,z5,z18])],[(0,[z0,z1,z2,z3,z5,z903]),(0,[z0,z1,z111,z24,z5,z6]),(0,[z0,z1,z2,z5,z735,z6])],[(0,[z0,z1,z2,z904,z5,z6]),(0,[z363,z0,z1,z2,z24,z5]),(0,[z0,z54,z58,z24,z5,z6]),(0,[z0,z1,z2,z5,z402,z18]),(0,[z49,z0,z1,z2,z5,z308])],[(0,[z36,z1,z2,z3,z79,z6]),(0,[z30,z1,z2,z3,z5,z485]),(0,[z905,z0,z1,z2,z5,z6]),(0,[z906,z0,z1,z2,z3,z5])],[(0,[z0,z1,z2,z907,z5,z6]),(0,[z0,z908,z2,z3,z5,z6]),(0,[z0,z1,z2,z511,z5,z18]),(0,[z909,z187,z1,z2,z3,z5])],[(0,[z36,z1,z87,z3,z5,z6]),(0,[z92,z1,z2,z371,z5,z6]),(0,[z910,z1,z2,z3,z5,z247])],[(0,[z0,z1,z2,z24,z292,z5]),(0,[z0,z1,z2,z911,z5,z6]),(0,[z0,z1,z2,z3,z5,z912])],[(0,[z30,z1,z2,z3,z5,z178]),(0,[z0,z2,z3,z118,z751,z6]),(0,[z0,z1,z2,z64,z5,z17])],[(0,[z0,z1,z2,z12,z5,z135]),(0,[z0,z1,z12,z5,z17,z18])]],
   [[(0,[z0,z232,z2,z125,z5,z6]),(0,[z78,z1,z666,z3,z5,z6]),(0,[z913,z1,z2,z3,z5,z6]),(0,[z323,z1,z2,z393,z5,z6]),(0,[z0,z1,z2,z5,z17,z914])],[(0,[z0,z1,z2,z12,z5,z94]),(0,[z0,z1,z2,z3,z5,z915]),(0,[z0,z1,z2,z5,z6,z916]),(0,[z0,z1,z34,z3,z917,z6]),(0,[z77,z0,z1,z2,z5,z17])],[(0,[z0,z153,z2,z3,z5,z279]),(0,[z131,z1,z2,z3,z5,z50]),(0,[z918,z1,z2,z24,z5,z6]),(0,[z0,z1,z12,z24,z5,z18])],[(0,[z0,z1,z2,z3,z5,z919]),(0,[z0,z1,z2,z292,z5,z164]),(0,[z0,z1,z3,z5,z17,z704]),(0,[z0,z1,z2,z3,z920,z6]),(0,[z0,z245,z2,z12,z5,z6])],[(0,[z0,z721,z2,z3,z5,z6]),(0,[z0,z1,z2,z921,z5,z6]),(0,[z561,z2,z226,z3,z5,z6]),(0,[z0,z1,z565,z3,z5,z18])],[(0,[z286,z0,z1,z24,z5,z6])],[(0,[z0,z1,z2,z922,z5,z6]),(0,[z36,z1,z87,z3,z5,z485]),(0,[z923,z0,z1,z2,z3,z5]),(0,[z924,z1,z2,z24,z5,z6]),(0,[z89,z0,z467,z3,z45,z6])],[(0,[z1,z87,z756,z3,z5,z6]),(0,[z36,z1,z87,z3,z5,z18]),(0,[z0,z1,z275,z3,z5,z17]),(0,[z0,z1,z2,z3,z5,z707]),(0,[z92,z1,z2,z3,z258,z6]),(0,[z925,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z409,z5,z6]),(0,[z926,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z927,z6]),(0,[z0,z1,z2,z12,z5,z330])],[(0,[z264,z1,z2,z24,z5,z6])],[(0,[z0,z1,z2,z414,z5,z6]),(0,[z0,z1,z2,z26,z5,z256]),(0,[z0,z467,z2,z414,z5,z6]),(1,[z0,z1,z3,z5,z778])],[(0,[z619,z1,z2,z3,z5,z38]),(0,[z35,z721,z2,z3,z5,z6]),(0,[z0,z1,z2,z928,z5,z6]),(0,[z155,z163,z1,z2,z3,z5]),(0,[z0,z1,z2,z24,z5,z132]),(0,[z0,z2,z3,z5,z6,z929]),(0,[z913,z1,z2,z3,z5,z18])],[(0,[z0,z1,z2,z371,z157,z6]),(0,[z1,z2,z24,z5,z178,z6])],[(0,[z0,z54,z2,z3,z258,z6]),(0,[z91,z0,z21,z371,z5,z6]),(0,[z0,z81,z2,z3,z412,z5])],[(0,[z0,z1,z2,z5,z6,z930]),(0,[z0,z1,z2,z125,z5,z17]),(0,[z931,z1,z2,z3,z5,z6]),(0,[z932,z1,z2,z3,z5,z6]),(0,[z0,z1,z188,z3,z5,z17])],[(0,[z431,z0,z1,z3,z45,z6]),(0,[z0,z1,z2,z933,z5,z6]),(0,[z0,z1,z2,z3,z934,z5]),(0,[z935,z0,z2,z24,z5,z6]),(0,[z1,z2,z3,z5,z18,z843])]],
   [[(0,[z0,z1,z3,z5,z936,z6]),(0,[z937,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z134,z5,z17]),(0,[z0,z1,z2,z5,z938,z6]),(0,[z0,z1,z2,z59,z5,z67]),(0,[z286,z0,z1,z24,z5,z18])],[(0,[z0,z1,z2,z5,z939,z6]),(0,[z0,z812,z2,z3,z5,z17])],[(0,[z28,z20,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z940]),(0,[z89,z119,z0,z3,z45,z6]),(0,[z0,z1,z2,z409,z5,z18])],[(0,[z0,z1,z492,z12,z5,z6]),(0,[z0,z1,z2,z5,z941,z6]),(0,[z0,z1,z3,z597,z5,z18]),(0,[z607,z1,z2,z3,z5,z17])],[(0,[z28,z561,z2,z3,z5,z6]),(0,[z0,z1,z2,z24,z5,z279]),(0,[z36,z1,z87,z12,z5,z6]),(0,[z0,z1,z2,z436,z5,z6])],[(0,[z0,z1,z2,z3,z942,z6]),(0,[z0,z1,z2,z3,z5,z943]),(0,[z607,z1,z2,z3,z5,z38]),(0,[z0,z1,z2,z237,z258,z6]),(0,[z0,z1,z367,z3,z5,z18]),(0,[z0,z1,z2,z414,z5,z18]),(0,[z607,z1,z2,z3,z5,z225])],[(0,[z834,z0,z1,z2,z3,z5]),(0,[z166,z0,z1,z2,z5,z17]),(0,[z0,z1,z34,z3,z51,z132])],[(0,[z1,z2,z3,z5,z944,z6]),(0,[z0,z2,z24,z5,z6,z945]),(0,[z13,z0,z1,z12,z5,z18]),(0,[z0,z1,z2,z3,z5,z946])],[(0,[z133,z0,z21,z3,z5,z6]),(0,[z112,z1,z2,z3,z5,z6]),(0,[z947,z0,z1,z2,z5,z18])],[(0,[z0,z1,z2,z3,z948,z5]),(0,[z83,z0,z2,z269,z5,z6]),(0,[z1,z2,z3,z5,z949,z6]),(0,[z950,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z349,z5,z71])],[(1,[z1,z2,z3,z5,z707])],[(0,[z0,z400,z2,z3,z5,z6]),(0,[z198,z163,z1,z2,z43,z5]),(0,[z205,z0,z2,z3,z258,z6])],[(0,[z0,z1,z2,z134,z5,z135]),(0,[z0,z1,z2,z3,z5,z951]),(0,[z0,z1,z2,z12,z5,z216]),(0,[z0,z1,z2,z5,z18,z861])],[(0,[z28,z20,z2,z3,z5,z18]),(0,[z0,z1,z2,z952,z5,z6]),(0,[z0,z1,z2,z953,z5,z6]),(0,[z0,z1,z2,z202,z5,z17])],[(0,[z0,z1,z2,z3,z5,z954]),(0,[z0,z2,z207,z766,z5,z6]),(0,[z0,z1,z2,z446,z405,z6]),(0,[z187,z1,z2,z24,z5,z6])],[(0,[z49,z0,z1,z2,z5,z417]),(0,[z89,z224,z1,z3,z45,z6]),(0,[z0,z1,z2,z436,z5,z18]),(0,[z607,z1,z2,z3,z5,z206])]],
   [[(0,[z0,z1,z2,z375,z387,z6]),(0,[z0,z1,z2,z12,z258,z6]),(0,[z0,z1,z2,z955,z5,z6])],[(0,[z1,z2,z3,z5,z6,z956]),(0,[z0,z1,z24,z5,z296,z6]),(0,[z0,z1,z670,z12,z5,z6])],[(0,[z0,z305,z2,z207,z5,z6])],[(0,[z0,z1,z172,z3,z5,z18]),(0,[z90,z0,z2,z3,z5,z80]),(0,[z0,z1,z2,z3,z5,z957]),(0,[z86,z0,z1,z2,z24,z66]),(0,[z112,z1,z2,z3,z5,z18])],[(0,[z0,z1,z630,z3,z5,z17]),(0,[z0,z1,z3,z5,z435,z18])],[(0,[z0,z1,z2,z3,z958,z6]),(0,[z0,z1,z2,z3,z5,z959]),(0,[z156,z1,z2,z3,z5,z178]),(0,[z224,z1,z2,z3,z45,z6]),(0,[z27,z0,z1,z2,z304,z266])],[(0,[z163,z0,z1,z2,z3,z5]),(0,[z0,z400,z2,z3,z5,z18]),(0,[z932,z1,z2,z12,z5,z6]),(0,[z1,z2,z3,z5,z206,z18])],[(0,[z30,z1,z2,z3,z5,z585]),(0,[z0,z1,z2,z960,z5,z6])],[],[(0,[z961,z0,z1,z2,z3,z5])],[(0,[z0,z232,z2,z3,z5,z17]),(0,[z114,z1,z2,z164,z70,z6]),(0,[z0,z1,z2,z962,z5,z6])],[(0,[z0,z1,z2,z237,z5,z17]),(0,[z963,z0,z1,z2,z24,z6]),(0,[z27,z0,z1,z2,z266,z6]),(0,[z86,z0,z1,z2,z3,z728])],[(0,[z83,z0,z129,z2,z5,z6]),(0,[z877,z0,z1,z2,z3,z5])],[(0,[z77,z86,z0,z1,z2,z66])],[(0,[z0,z1,z2,z964,z5,z6]),(0,[z0,z965,z2,z3,z5,z6]),(0,[z0,z1,z2,z93,z5,z395])],[(0,[z363,z0,z1,z2,z12,z5])]],
   [[(0,[z0,z1,z2,z159,z5,z71])],[(0,[z0,z1,z2,z3,z4,z17]),(0,[z0,z966,z2,z3,z5,z6]),(0,[z36,z1,z87,z134,z5,z6]),(0,[z0,z1,z2,z3,z5,z967]),(0,[z0,z1,z3,z5,z17,z410])],[(0,[z0,z968,z2,z3,z5,z6]),(0,[z30,z1,z2,z12,z5,z227]),(0,[z1,z2,z3,z5,z38,z707]),(0,[z0,z2,z3,z969,z5,z6])],[(0,[z232,z2,z3,z5,z38,z6]),(0,[z194,z0,z1,z2,z12,z5]),(0,[z970,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z511,z5,z6])],[(0,[z28,z1,z2,z3,z355,z6]),(0,[z631,z0,z2,z3,z31,z6])],[(0,[z0,z1,z583,z12,z5,z6]),(0,[z0,z1,z2,z12,z5,z867])],[(0,[z27,z0,z1,z2,z266,z18])],[(0,[z30,z506,z1,z2,z3,z5])],[(0,[z0,z153,z2,z3,z5,z478]),(0,[z0,z1,z2,z3,z971,z5]),(0,[z1,z2,z3,z5,z6,z804]),(0,[z0,z1,z2,z3,z5,z304])],[(0,[z149,z35,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z972,z5]),(0,[z0,z1,z2,z3,z973,z5]),(0,[z0,z1,z2,z218,z5,z132]),(0,[z49,z0,z1,z2,z5,z767]),(0,[z0,z1,z2,z3,z185,z65])],[(0,[z0,z1,z2,z3,z974,z5]),(0,[z89,z0,z1,z3,z917,z6]),(0,[z0,z1,z2,z5,z6,z975])],[(0,[z0,z117,z2,z3,z359,z6]),(0,[z0,z1,z2,z976,z5,z6]),(0,[z0,z1,z600,z24,z5,z6])],[],[],[(0,[z1,z2,z8,z3,z70,z6]),(0,[z0,z2,z807,z3,z5,z6]),(0,[z0,z1,z2,z5,z71,z55]),(0,[z382,z0,z2,z3,z5,z270])],[(0,[z30,z232,z2,z3,z5,z6]),(0,[z114,z1,z2,z12,z70,z6]),(0,[z0,z1,z2,z977,z5,z6])]],
   [[(0,[z0,z1,z2,z3,z5,z978]),(0,[z78,z1,z226,z3,z5,z279]),(0,[z0,z1,z2,z3,z5,z979]),(0,[z0,z1,z2,z3,z980,z6]),(0,[z0,z1,z2,z981,z5,z6]),(0,[z0,z1,z25,z12,z5,z6])],[(0,[z0,z1,z2,z982,z5,z6]),(0,[z983,z0,z1,z2,z3,z5]),(0,[z0,z245,z2,z3,z5,z169])],[(0,[z30,z1,z2,z3,z5,z142]),(0,[z0,z1,z2,z3,z984,z6]),(0,[z49,z607,z1,z2,z3,z5]),(0,[z27,z0,z1,z2,z735,z6]),(0,[z1,z2,z3,z185,z178,z65])],[(0,[z221,z35,z2,z3,z5,z18]),(0,[z0,z1,z2,z3,z5,z985]),(0,[z0,z153,z2,z3,z387,z6]),(0,[z0,z1,z2,z986,z5,z6]),(0,[z0,z81,z2,z3,z5,z11]),(0,[z0,z1,z2,z24,z6,z711]),(0,[z0,z1,z3,z917,z45,z6])],[(0,[z0,z153,z2,z3,z5,z6]),(0,[z0,z1,z2,z371,z258,z6]),(0,[z0,z1,z2,z3,z6,z987]),(0,[z988,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z771]),(0,[z0,z1,z2,z12,z886,z5]),(0,[z1,z2,z3,z5,z989,z6])],[(0,[z0,z1,z2,z3,z5,z990])],[(0,[z0,z1,z534,z12,z5,z6]),(0,[z0,z1,z2,z202,z5,z216]),(0,[z439,z0,z1,z3,z5,z18]),(0,[z991,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z12,z5,z247]),(0,[z0,z1,z2,z992,z5,z6])],[(0,[z313,z1,z2,z43,z5,z6]),(0,[z0,z1,z2,z3,z5,z67]),(0,[z0,z245,z2,z3,z5,z17])],[(0,[z0,z1,z2,z3,z5,z993]),(0,[z994,z0,z2,z3,z5,z6]),(0,[z0,z2,z3,z5,z774,z6])],[(0,[z0,z1,z2,z3,z5,z995]),(0,[z996,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z997]),(0,[z0,z1,z2,z24,z5,z478]),(0,[z0,z117,z2,z3,z118,z6])],[(1,[z1,z756,z3,z5,z6]),(0,[z998,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z24,z999,z5]),(0,[z0,z1,z25,z12,z5,z18])],[(0,[z0,z561,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z1000]),(0,[z0,z1,z2,z3,z5,z1001]),(0,[z1002,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z1003,z5,z6])],[(0,[z1,z2,z3,z5,z98,z17]),(0,[z629,z1,z2,z322,z5,z6])],[(0,[z1004,z1,z2,z3,z5,z6])],[(0,[z0,z54,z238,z3,z5,z6]),(0,[z0,z153,z2,z3,z5,z18]),(0,[z91,z131,z21,z3,z5,z6]),(0,[z0,z1,z2,z259,z5,z99]),(0,[z0,z1,z2,z3,z76,z311])]],
   [[(0,[z947,z0,z1,z2,z5,z6]),(0,[z0,z1,z2,z3,z5,z1005]),(0,[z0,z1,z2,z3,z5,z1006])],[(0,[z1007,z0,z1,z2,z3,z5]),(0,[z83,z0,z2,z181,z5,z6]),(0,[z0,z1,z2,z1008,z5,z6]),(0,[z0,z1,z2,z1009,z5,z6])],[(0,[z0,z1,z2,z3,z5,z1010]),(0,[z205,z131,z2,z3,z5,z6]),(0,[z1011,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z1012]),(0,[z0,z1,z24,z5,z581,z6]),(0,[z0,z1,z12,z1013,z5,z6])],[(0,[z35,z561,z2,z3,z5,z6]),(0,[z0,z1,z2,z1014,z5,z6])],[(0,[z298,z20,z2,z3,z5,z6]),(0,[z91,z92,z21,z3,z5,z6]),(0,[z0,z1,z565,z12,z5,z6]),(0,[z77,z0,z1,z2,z185,z5])],[(0,[z0,z1,z2,z3,z5,z1015]),(0,[z0,z1,z2,z24,z387,z6]),(0,[z764,z0,z1,z2,z3,z5]),(0,[z0,z117,z2,z3,z118,z18]),(0,[z63,z0,z1,z2,z5,z72])],[(0,[z0,z1,z2,z24,z5,z6]),(0,[z0,z1,z2,z3,z5,z1016]),(0,[z1017,z0,z1,z2,z3,z5]),(0,[z205,z0,z2,z3,z31,z18]),(0,[z0,z467,z2,z24,z5,z6]),(0,[z0,z2,z3,z1018,z5,z6])],[(0,[z0,z561,z2,z3,z5,z18]),(0,[z0,z1,z696,z24,z5,z6]),(0,[z1019,z1,z2,z24,z5,z6])],[(0,[z198,z1,z2,z731,z5,z6]),(0,[z0,z1,z2,z1020,z5,z6]),(0,[z0,z2,z3,z5,z1021,z6])],[(0,[z0,z1,z2,z1022,z5,z6]),(0,[z30,z1,z2,z3,z5,z206]),(0,[z86,z0,z1,z2,z12,z66])],[(1,[z721,z2,z3,z5,z6]),(0,[z131,z2,z21,z3,z5,z6]),(0,[z0,z1,z2,z371,z5,z17]),(0,[z0,z1,z2,z3,z5,z1023]),(0,[z0,z1,z2,z1024,z5,z6]),(0,[z0,z1,z2,z3,z5,z1025])],[(0,[z49,z531,z0,z1,z2,z5])],[(0,[z83,z0,z2,z181,z5,z18]),(0,[z83,z0,z2,z267,z181,z5]),(0,[z13,z0,z1,z3,z5,z778])],[(0,[z0,z1,z2,z1026,z5,z6]),(0,[z313,z363,z0,z1,z2,z5])],[(0,[z205,z0,z2,z3,z447,z6]),(0,[z0,z1,z2,z3,z5,z1027]),(0,[z0,z1,z2,z1028,z5,z6]),(0,[z0,z1,z2,z1029,z5,z6])],[(0,[z0,z1,z2,z3,z5,z1030]),(0,[z0,z1,z1031,z3,z5,z6]),(0,[z849,z187,z1,z2,z3,z5]),(0,[z1032,z1,z2,z3,z5,z6])]],
   [[(0,[z198,z1,z2,z48,z43,z5]),(0,[z286,z0,z1,z1013,z5,z6]),(0,[z0,z687,z2,z3,z5,z319]),(0,[z1,z2,z3,z5,z1033,z18]),(0,[z0,z1,z649,z3,z5,z18])],[(0,[z1,z2,z3,z5,z1034,z6]),(0,[z0,z1,z2,z24,z5,z18]),(0,[z0,z1,z34,z3,z51,z6])],[(0,[z30,z1,z2,z3,z5,z697]),(0,[z10,z0,z2,z3,z5,z80]),(0,[z286,z0,z1,z24,z5,z17])],[(0,[z313,z0,z1,z2,z292,z5]),(0,[z1,z2,z24,z5,z6,z206]),(0,[z0,z1,z433,z3,z5,z18])],[(0,[z0,z1035,z2,z3,z5,z6]),(0,[z89,z0,z1,z3,z45,z6]),(0,[z0,z1,z2,z409,z5,z17]),(0,[z0,z1,z2,z5,z17,z787])],[(0,[z36,z1,z87,z3,z5,z135]),(0,[z0,z1,z2,z3,z258,z17])],[(0,[z91,z0,z21,z24,z5,z6]),(0,[z0,z1,z602,z12,z5,z6]),(0,[z1036,z0,z2,z24,z5,z6]),(0,[z607,z1,z2,z3,z185,z5])],[],[(0,[z1,z2,z3,z5,z206,z485])],[],[(0,[z0,z1037,z2,z3,z5,z6]),(1,[z0,z2,z766,z5,z6]),(0,[z0,z1,z2,z436,z5,z169]),(0,[z1038,z1,z2,z3,z5,z132]),(0,[z1,z2,z3,z5,z18,z956])],[(0,[z0,z1,z2,z3,z1039,z5]),(0,[z0,z1,z160,z24,z5,z17]),(0,[z1040,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z355,z6]),(0,[z0,z1,z2,z3,z5,z1041]),(0,[z119,z0,z2,z3,z5,z6]),(0,[z0,z1,z34,z3,z51,z18])],[(0,[z28,z20,z2,z12,z5,z6])],[(0,[z0,z1,z2,z3,z1042,z5]),(0,[z0,z1,z2,z1043,z5,z6]),(0,[z112,z1,z2,z3,z5,z169])],[(0,[z131,z1,z2,z3,z5,z6]),(0,[z91,z0,z1,z24,z5,z18]),(0,[z0,z1,z2,z3,z5,z1044]),(0,[z89,z0,z1,z3,z45,z18])]],
   [[(0,[z0,z1,z2,z3,z5,z1045]),(0,[z0,z232,z2,z375,z5,z6]),(0,[z0,z1,z2,z24,z5,z521])],[(0,[z143,z1,z2,z351,z5,z6]),(0,[z13,z0,z1,z511,z5,z18])],[(0,[z0,z1,z2,z3,z1046,z6]),(0,[z0,z1,z2,z5,z6,z1047])],[(0,[z35,z1,z2,z3,z355,z6]),(0,[z0,z1,z2,z1048,z5,z6]),(0,[z112,z1,z2,z12,z5,z6])],[(0,[z0,z1,z2,z1049,z5,z6]),(0,[z0,z192,z2,z3,z5,z320])],[(0,[z0,z1,z2,z3,z5,z1050]),(0,[z83,z194,z0,z2,z181,z5])],[(0,[z78,z1,z226,z3,z5,z478]),(0,[z0,z400,z2,z12,z5,z6]),(0,[z156,z1,z2,z3,z5,z38]),(0,[z1051,z0,z1,z2,z24,z6]),(0,[z653,z0,z2,z183,z5,z6]),(0,[z0,z2,z24,z5,z475,z6])],[(0,[z0,z1,z2,z3,z355,z18]),(0,[z0,z153,z2,z125,z5,z6]),(0,[z174,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z284,z5,z17]),(0,[z40,z1,z2,z3,z5,z80]),(0,[z286,z0,z1,z24,z5,z330]),(0,[z119,z0,z2,z3,z5,z18])],[(0,[z0,z400,z2,z3,z5,z17]),(0,[z106,z1,z2,z3,z69,z6])],[(0,[z30,z1,z2,z3,z5,z707]),(0,[z0,z1,z2,z1052,z5,z6])],[(0,[z131,z1,z2,z3,z5,z18])],[(0,[z221,z35,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z1053]),(0,[z0,z1,z2,z3,z5,z1054]),(0,[z1055,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z93,z5,z256])],[(0,[z0,z1,z2,z3,z1056,z5]),(0,[z0,z1,z2,z5,z6,z668])],[(0,[z0,z1,z2,z1057,z5,z6]),(0,[z0,z1,z2,z3,z5,z1058]),(0,[z406,z35,z2,z3,z5,z6])],[(0,[z0,z1,z2,z375,z5,z17]),(0,[z114,z1,z2,z3,z745,z6]),(0,[z89,z0,z1,z3,z45,z521]),(0,[z1059,z1,z2,z3,z5,z6])],[(0,[z0,z1060,z2,z3,z5,z6])]],
   [[(0,[z198,z1,z2,z43,z5,z6]),(0,[z1,z2,z3,z5,z1061,z6])],[(0,[z78,z1,z226,z3,z387,z6]),(0,[z1,z2,z24,z1062,z5,z6]),(0,[z0,z245,z2,z436,z5,z6]),(0,[z0,z1,z3,z5,z17,z437])],[(0,[z78,z1,z226,z3,z5,z6]),(0,[z174,z1,z2,z3,z5,z18])],[(0,[z0,z1,z2,z3,z5,z1063]),(0,[z30,z1,z2,z3,z5,z139]),(0,[z0,z2,z3,z5,z6,z945]),(0,[z1,z2,z3,z5,z178,z18])],[(0,[z114,z1,z2,z3,z70,z17]),(0,[z27,z0,z1,z2,z543,z6]),(0,[z0,z1,z2,z3,z5,z767])],[(0,[z224,z467,z2,z3,z5,z6]),(0,[z112,z245,z2,z3,z5,z6]),(0,[z1064,z0,z1,z2,z5,z6])],[(0,[z40,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z79,z279]),(0,[z0,z1,z2,z3,z5,z1065]),(0,[z0,z58,z807,z3,z5,z6]),(0,[z0,z1,z2,z93,z5,z410])],[(0,[z1,z756,z226,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z1066]),(0,[z0,z1,z2,z3,z5,z1067]),(0,[z0,z1,z2,z3,z5,z1068])],[(0,[z221,z35,z2,z3,z5,z559]),(0,[z0,z1,z2,z284,z5,z247]),(0,[z13,z0,z1,z409,z5,z18])],[(0,[z0,z1,z188,z24,z5,z6]),(0,[z1069,z0,z1,z2,z12,z5]),(0,[z1070,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z235])],[(0,[z198,z1,z2,z43,z5,z18]),(1,[z0,z2,z3,z751,z6]),(0,[z607,z1,z2,z3,z5,z11]),(0,[z0,z1,z534,z3,z5,z17])],[(0,[z0,z1,z2,z3,z5,z390]),(0,[z710,z1,z2,z24,z5,z6]),(0,[z794,z0,z2,z3,z5,z6])],[(0,[z78,z1,z226,z3,z5,z18]),(0,[z0,z2,z3,z118,z258,z6]),(0,[z0,z1,z2,z3,z18,z987])],[(0,[z0,z1,z2,z3,z1071,z6]),(0,[z205,z0,z2,z3,z31,z6]),(0,[z607,z1,z2,z24,z5,z6]),(0,[z1,z2,z3,z5,z1072,z6])],[(0,[z1073,z1,z2,z3,z5,z6])]],
   [[(0,[z0,z1,z2,z3,z79,z18]),(0,[z114,z1,z2,z3,z292,z70]),(0,[z0,z1,z2,z1074,z5,z6]),(0,[z0,z1,z2,z511,z5,z17])],[(0,[z0,z1,z2,z1075,z5,z6]),(0,[z40,z1,z2,z3,z5,z18])],[(0,[z0,z1,z2,z267,z24,z5]),(0,[z0,z1,z2,z3,z5,z1076]),(0,[z483,z0,z1,z2,z3,z315])],[(0,[z221,z35,z2,z12,z5,z6]),(0,[z363,z0,z1,z2,z5,z164]),(0,[z0,z1,z2,z12,z971,z5]),(0,[z0,z1,z2,z12,z5,z304]),(0,[z1077,z1,z2,z3,z5,z6])],[(0,[z30,z1,z2,z3,z5,z210]),(0,[z92,z1,z2,z3,z5,z199]),(0,[z0,z1,z2,z12,z185,z65])],[(0,[z0,z1,z2,z1078,z5,z6]),(0,[z0,z1,z2,z3,z5,z199])],[(0,[z0,z1,z2,z1079,z5,z6]),(0,[z117,z2,z3,z118,z98,z6]),(0,[z0,z1,z2,z5,z6,z1080]),(0,[z52,z0,z1,z2,z108,z5])],[(0,[z0,z1,z2,z3,z5,z1081]),(0,[z0,z1,z2,z3,z5,z1082]),(0,[z1083,z1,z2,z3,z5,z6]),(0,[z0,z1,z12,z24,z5,z17])],[(0,[z0,z1,z2,z3,z5,z1084]),(0,[z0,z1,z2,z3,z1085,z6]),(0,[z143,z187,z1,z2,z5,z6]),(0,[z92,z1,z2,z24,z5,z6]),(0,[z0,z1,z2,z3,z1086,z6]),(0,[z0,z467,z2,z3,z45,z6]),(0,[z1,z2,z3,z5,z1033,z6])],[(0,[z607,z1,z2,z24,z5,z18]),(0,[z52,z0,z1,z2,z24,z5])],[(0,[z78,z1,z226,z12,z5,z6]),(0,[z1,z2,z12,z5,z98,z6])],[(0,[z1087,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z1088])],[(0,[z0,z1,z2,z1089,z5,z6]),(0,[z0,z1,z2,z3,z1090,z6]),(0,[z1091,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z1092,z5,z6])],[],[(0,[z1093,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z48,z5]),(0,[z0,z1094,z2,z3,z5,z6]),(0,[z0,z81,z2,z12,z5,z11]),(0,[z224,z1,z2,z3,z51,z6])],[(0,[z0,z153,z2,z12,z5,z6]),(0,[z0,z1,z2,z3,z292,z5]),(0,[z0,z1,z2,z3,z1095,z5]),(0,[z0,z1,z2,z3,z1096,z5]),(0,[z1097,z0,z1,z2,z5,z6]),(0,[z224,z1,z2,z3,z5,z521])]],
   [[(0,[z156,z1,z2,z3,z5,z707]),(0,[z1098,z0,z1,z2,z3,z5])],[(0,[z0,z153,z2,z3,z5,z17]),(0,[z0,z1,z1099,z3,z5,z6]),(0,[z1100,z0,z1,z2,z5,z6])],[(0,[z0,z1,z2,z5,z1101,z6]),(0,[z0,z1,z2,z3,z1102,z6])],[(0,[z0,z1,z2,z24,z5,z485]),(0,[z0,z1,z2,z1103,z5,z6]),(0,[z201,z1,z2,z144,z5,z6]),(0,[z0,z1,z2,z12,z5,z67]),(0,[z1,z2,z3,z934,z5,z98]),(0,[z0,z1,z2,z414,z5,z169]),(0,[z0,z1,z34,z202,z51,z6]),(0,[z991,z1,z2,z3,z5,z17])],[(0,[z0,z1,z2,z1104,z5,z6]),(0,[z0,z1,z2,z3,z157,z199]),(0,[z391,z0,z1,z24,z5,z6]),(0,[z0,z1,z2,z12,z5,z390])],[(0,[z91,z0,z21,z3,z5,z199]),(0,[z1105,z0,z1,z2,z3,z6]),(0,[z0,z117,z2,z12,z118,z6]),(0,[z0,z1,z2,z93,z5,z767])],[(0,[z0,z1,z2,z24,z5,z559]),(0,[z0,z1,z2,z1106,z5,z6]),(0,[z91,z0,z807,z3,z5,z6]),(0,[z0,z54,z58,z59,z5,z6]),(0,[z0,z54,z58,z3,z5,z18]),(0,[z205,z0,z2,z12,z31,z6]),(0,[z0,z1,z24,z5,z17,z18])],[(0,[z0,z1,z2,z3,z5,z1107]),(0,[z0,z561,z2,z12,z5,z6])],[(0,[z198,z1,z2,z137,z5,z6]),(0,[z0,z1,z2,z24,z157,z6]),(0,[z924,z1,z2,z3,z5,z6])],[(0,[z1108,z0,z1,z2,z3,z5])],[(0,[z0,z1,z2,z24,z5,z755]),(0,[z0,z1,z2,z414,z5,z17])],[(0,[z0,z1,z2,z1109,z5,z6]),(0,[z0,z2,z3,z5,z6,z771]),(0,[z0,z1,z73,z3,z5,z17])],[],[(0,[z0,z1,z2,z12,z5,z199]),(0,[z205,z1,z2,z3,z98,z6]),(0,[z0,z1,z2,z3,z5,z132]),(0,[z0,z1,z3,z349,z5,z18]),(0,[z49,z264,z1,z2,z3,z5])],[(0,[z0,z1,z2,z3,z5,z1110]),(0,[z1111,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z1112,z5,z6])]],
   [[(0,[z639,z0,z2,z269,z5,z6]),(0,[z173,z0,z1,z2,z486,z6]),(0,[z0,z1,z649,z12,z5,z6]),(0,[z1105,z0,z1,z2,z3,z18])],[(0,[z0,z1,z2,z1013,z5,z6]),(0,[z1,z2,z24,z5,z1113,z6]),(0,[z0,z1,z2,z3,z917,z6])],[(0,[z28,z20,z2,z3,z5,z17]),(0,[z163,z1,z2,z3,z5,z70])],[(0,[z0,z1,z2,z3,z5,z1114])],[(0,[z0,z1,z2,z3,z5,z1115]),(0,[z1,z2,z3,z292,z5,z178]),(0,[z0,z1,z2,z436,z5,z17]),(0,[z13,z607,z1,z3,z5,z18])],[(0,[z78,z1,z226,z125,z5,z6]),(0,[z0,z400,z2,z3,z69,z6]),(0,[z0,z1,z625,z3,z5,z17]),(0,[z166,z10,z0,z1,z2,z5]),(0,[z105,z0,z1,z2,z5,z32])],[(0,[z0,z1,z2,z12,z48,z5]),(0,[z1116,z0,z1,z2,z3,z5])],[(0,[z0,z1,z2,z3,z5,z1117]),(0,[z131,z54,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z1118])],[(0,[z143,z1,z2,z5,z348,z6]),(0,[z112,z1,z2,z3,z5,z17])],[(0,[z0,z1,z2,z5,z164,z6]),(0,[z0,z1,z2,z1119,z5,z6]),(0,[z1111,z1,z2,z3,z5,z18])],[(0,[z0,z1,z12,z471,z5,z6]),(0,[z0,z245,z2,z414,z5,z6]),(0,[z483,z607,z1,z2,z3,z5])],[(0,[z0,z2,z3,z5,z6,z1120]),(0,[z363,z0,z1,z2,z3,z5]),(0,[z1,z2,z3,z5,z178,z6])],[(0,[z0,z1,z2,z3,z79,z478]),(1,[z0,z807,z3,z5,z6])],[(0,[z10,z0,z2,z12,z5,z80])],[(0,[z30,z561,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z1121,z6])],[(0,[z1122,z0,z1,z2,z3,z5]),(0,[z1123,z0,z1,z2,z5,z6]),(0,[z131,z1,z2,z237,z5,z6]),(0,[z0,z1,z2,z3,z5,z1124]),(0,[z0,z1,z2,z1125,z5,z6]),(0,[z194,z0,z1,z2,z3,z5]),(0,[z89,z0,z1,z12,z45,z6])]],
   [[(0,[z0,z1,z2,z3,z5,z1126]),(0,[z0,z1,z2,z1127,z5,z6]),(0,[z1128,z1,z2,z3,z5,z6]),(0,[z27,z187,z1,z2,z266,z6]),(0,[z0,z1,z2,z108,z6,z517])],[(0,[z109,z1,z2,z3,z70,z6]),(0,[z131,z1,z2,z3,z157,z6]),(0,[z0,z1,z2,z5,z6,z402]),(0,[z27,z0,z1,z2,z486,z6]),(0,[z1,z2,z3,z5,z1129,z6])],[(0,[z86,z607,z1,z2,z3,z5])],[(0,[z406,z1,z2,z3,z5,z6]),(0,[z156,z1,z2,z3,z5,z206]),(0,[z0,z121,z2,z496,z5,z6])],[(0,[z0,z1,z2,z3,z1130,z6]),(0,[z0,z1,z2,z5,z164,z18]),(0,[z0,z1,z2,z3,z5,z1131]),(0,[z0,z1,z562,z3,z5,z17]),(0,[z0,z1,z2,z1132,z5,z6])],[(0,[z0,z1,z275,z24,z5,z6]),(0,[z0,z1,z2,z3,z1133,z6]),(0,[z0,z1,z2,z5,z18,z668]),(0,[z0,z1,z2,z5,z71,z767])],[(0,[z0,z1,z2,z3,z5,z1134]),(0,[z86,z0,z1,z2,z3,z543])],[(0,[z0,z1,z2,z12,z355,z6]),(0,[z0,z1,z666,z3,z5,z17]),(0,[z0,z1,z2,z3,z875,z6]),(0,[z1135,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z218,z5,z6]),(0,[z119,z0,z2,z12,z5,z6]),(0,[z0,z1,z2,z3,z5,z1136])],[(0,[z0,z1,z2,z3,z79,z6]),(0,[z224,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z24,z5,z330])],[(0,[z1,z2,z3,z616,z70,z6]),(0,[z1137,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z5,z767,z72])],[(0,[z0,z1,z2,z5,z6,z1138]),(0,[z131,z1,z2,z12,z5,z6]),(0,[z0,z1,z2,z161,z5,z6])],[(0,[z0,z1,z2,z5,z6,z1139]),(0,[z201,z1,z2,z29,z5,z6]),(0,[z27,z0,z1,z2,z266,z17])],[(0,[z721,z20,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z1140]),(0,[z845,z0,z1,z2,z3,z6]),(0,[z63,z607,z1,z2,z3,z5]),(0,[z0,z2,z3,z5,z18,z945])],[(0,[z0,z1,z2,z3,z1141,z6]),(0,[z0,z1,z2,z3,z1142,z5]),(0,[z92,z1,z2,z3,z5,z50]),(0,[z0,z213,z2,z5,z6,z582]),(0,[z0,z2,z3,z5,z17,z929])],[(0,[z221,z1,z2,z3,z5,z559]),(0,[z232,z2,z226,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z50]),(0,[z406,z1,z2,z3,z5,z18]),(0,[z166,z10,z0,z2,z5,z80])],[(0,[z89,z112,z1,z3,z45,z6]),(0,[z77,z86,z0,z1,z2,z5])]],
   [[(0,[z326,z1,z2,z3,z5,z6]),(0,[z1143,z0,z1,z2,z5,z6])],[(0,[z221,z35,z2,z3,z4,z6]),(0,[z78,z232,z226,z3,z5,z6]),(0,[z0,z1,z2,z1144,z5,z6]),(0,[z156,z1,z2,z12,z5,z38])],[(0,[z0,z1,z2,z1145,z5,z6]),(0,[z174,z1,z2,z12,z5,z6]),(0,[z0,z1,z2,z218,z5,z18]),(0,[z0,z1,z1146,z3,z5,z6]),(0,[z0,z1,z2,z3,z185,z728])],[(0,[z0,z1,z2,z3,z1147,z6]),(0,[z224,z1,z2,z3,z5,z18])],[(0,[z0,z1,z2,z3,z1148,z6]),(0,[z1149,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z251]),(0,[z0,z1150,z2,z3,z5,z6])],[(0,[z0,z2,z3,z5,z1151,z6]),(1,[z0,z1,z1013,z5,z6]),(1,[z0,z1,z3,z917,z6]),(0,[z0,z1,z2,z161,z5,z18])],[(0,[z0,z1,z2,z3,z5,z1152]),(0,[z0,z1,z2,z1153,z5,z6]),(0,[z0,z1,z2,z3,z5,z1154]),(0,[z1155,z1,z2,z3,z5,z6]),(0,[z0,z1,z234,z24,z5,z6])],[(0,[z1156,z0,z1,z2,z5,z6]),(0,[z13,z0,z1,z24,z5,z18]),(0,[z0,z2,z3,z5,z6,z1157]),(0,[z0,z1,z2,z3,z5,z728])],[(0,[z0,z1,z2,z1158,z5,z6]),(0,[z0,z1,z2,z3,z1159,z6]),(0,[z221,z35,z2,z3,z5,z17]),(0,[z114,z363,z1,z2,z3,z70]),(0,[z1160,z0,z1,z2,z5,z6]),(0,[z0,z1,z2,z93,z5,z99]),(0,[z0,z1,z2,z735,z266,z6])],[(0,[z0,z1,z2,z3,z1161,z6])],[(0,[z0,z1,z2,z3,z1162,z6]),(0,[z0,z1,z170,z3,z5,z17]),(0,[z86,z0,z1,z2,z668,z66])],[(0,[z326,z1,z2,z3,z5,z18])],[(0,[z0,z1,z2,z24,z5,z216])],[(0,[z143,z1,z2,z144,z5,z6]),(0,[z0,z1,z2,z3,z157,z50])],[(0,[z1163,z0,z1,z2,z3,z5]),(0,[z30,z1,z2,z3,z355,z6]),(0,[z0,z54,z58,z3,z5,z6]),(0,[z0,z1,z2,z3,z1164,z6]),(0,[z91,z0,z21,z3,z5,z50]),(0,[z0,z1,z2,z5,z6,z1165])],[(0,[z273,z20,z2,z3,z5,z6]),(0,[z78,z1,z226,z3,z5,z17]),(0,[z36,z1,z37,z3,z5,z6]),(0,[z0,z1,z160,z161,z5,z17])]],
   [[(0,[z0,z1,z2,z12,z79,z6]),(0,[z0,z1,z2,z24,z258,z6]),(0,[z0,z1,z25,z12,z5,z17]),(0,[z224,z1,z2,z12,z5,z6])],[(0,[z0,z1,z272,z3,z5,z17]),(0,[z40,z1,z2,z12,z5,z6])],[(0,[z0,z734,z2,z3,z5,z6])],[(0,[z0,z20,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z1166,z6]),(0,[z0,z1,z2,z3,z185,z180]),(0,[z0,z2,z3,z766,z5,z6]),(0,[z1167,z0,z1,z2,z3,z5])],[(0,[z0,z1,z2,z3,z5,z1168]),(0,[z205,z0,z2,z3,z53,z6]),(0,[z635,z0,z2,z3,z31,z6]),(0,[z0,z1,z2,z284,z5,z67]),(0,[z0,z1169,z2,z3,z5,z6]),(0,[z1070,z1,z2,z12,z5,z6]),(0,[z0,z1,z2,z107,z108,z6])],[(0,[z0,z1,z2,z237,z5,z199]),(0,[z0,z1,z2,z12,z5,z235]),(0,[z86,z0,z1,z2,z3,z66])],[(0,[z221,z35,z2,z3,z5,z94]),(0,[z0,z1,z2,z1170,z5,z6])],[(0,[z0,z153,z2,z375,z5,z6]),(0,[z0,z1,z2,z3,z1171,z5]),(0,[z918,z1,z2,z3,z5,z6]),(0,[z112,z1,z2,z414,z5,z6]),(0,[z0,z1,z34,z3,z51,z216])],[(0,[z0,z232,z2,z24,z5,z6]),(0,[z143,z1,z2,z144,z5,z18]),(0,[z0,z1,z2,z3,z1172,z5])],[],[(0,[z0,z1,z2,z3,z5,z1173]),(0,[z0,z117,z2,z3,z118,z17]),(0,[z0,z1,z3,z5,z512,z18])],[(0,[z205,z0,z2,z3,z31,z17]),(0,[z49,z449,z0,z1,z2,z5])],[(0,[z0,z561,z2,z3,z5,z17]),(0,[z0,z1,z2,z12,z5,z251])],[(0,[z0,z1,z2,z1174,z5,z6]),(0,[z963,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z185,z336])],[(0,[z264,z1,z2,z3,z5,z6]),(0,[z131,z1,z2,z371,z5,z6]),(0,[z0,z2,z24,z775,z5,z6]),(0,[z1175,z0,z1,z2,z3,z5])],[(0,[z0,z1,z2,z24,z4,z6]),(0,[z0,z1,z2,z24,z5,z169]),(0,[z0,z1,z2,z107,z108,z18]),(0,[z0,z1,z2,z3,z5,z1176]),(0,[z0,z1,z2,z3,z5,z1177])]],
   [[(0,[z1178,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z1179]),(0,[z83,z0,z2,z181,z5,z17]),(0,[z112,z1,z2,z436,z5,z6])],[(0,[z0,z1180,z2,z3,z5,z6]),(0,[z30,z1,z2,z24,z5,z227]),(0,[z0,z1,z2,z26,z5,z124])],[(0,[z0,z1,z2,z3,z745,z6]),(0,[z0,z1,z24,z5,z45,z18])],[(0,[z935,z0,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z1181]),(0,[z0,z81,z2,z3,z5,z319])],[(0,[z0,z1,z2,z1182,z5,z6]),(0,[z0,z2,z3,z5,z1183,z6]),(0,[z86,z0,z1,z2,z3,z356]),(0,[z0,z1,z12,z597,z5,z6]),(0,[z0,z1,z2,z1184,z5,z6])],[(0,[z0,z1,z2,z3,z5,z1185]),(0,[z119,z0,z2,z3,z258,z6]),(0,[z0,z54,z58,z12,z5,z6]),(0,[z0,z1,z2,z24,z5,z17]),(0,[z186,z0,z1,z2,z3,z191]),(0,[z0,z1,z2,z1186,z3,z5]),(0,[z0,z1,z2,z5,z6,z1187])],[(0,[z30,z1,z2,z3,z79,z6]),(0,[z0,z1188,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z387,z279]),(0,[z0,z1,z2,z3,z5,z1189]),(0,[z205,z0,z2,z3,z136,z6]),(0,[z1,z2,z3,z786,z5,z6]),(0,[z1038,z1,z2,z3,z5,z6]),(0,[z963,z0,z1,z2,z3,z18])],[(0,[z0,z1,z2,z3,z5,z279]),(0,[z131,z1,z2,z3,z258,z6]),(0,[z264,z1,z2,z3,z5,z18])],[(0,[z0,z1,z2,z3,z5,z1190]),(0,[z0,z1,z2,z12,z292,z5]),(0,[z91,z0,z234,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z1191]),(0,[z1192,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z125,z79,z6]),(0,[z0,z2,z1193,z3,z5,z6]),(0,[z1194,z0,z1,z2,z3,z5]),(0,[z1195,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z5,z17,z668])],[],[(0,[z89,z0,z1,z3,z45,z169]),(0,[z317,z1,z2,z3,z5,z206])],[(0,[z1,z2,z24,z5,z98,z6]),(0,[z0,z1,z2,z3,z5,z1196]),(0,[z0,z1,z2,z259,z5,z71])],[(0,[z155,z1,z2,z3,z586,z6]),(0,[z36,z232,z2,z3,z5,z6]),(0,[z313,z0,z1,z2,z5,z6]),(0,[z114,z1,z2,z24,z70,z6]),(0,[z0,z1,z2,z3,z5,z1197])]],
   [[(0,[z1,z2,z3,z5,z70,z559]),(0,[z0,z1198,z2,z3,z5,z6]),(0,[z0,z1,z1199,z3,z5,z6]),(0,[z166,z0,z81,z1,z2,z5]),(0,[z603,z0,z1,z2,z276,z6]),(0,[z0,z2,z12,z1018,z5,z6]),(0,[z0,z1,z1200,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z1201]),(0,[z40,z1,z2,z93,z3,z5]),(0,[z0,z1202,z2,z3,z5,z6]),(0,[z0,z1,z34,z3,z51,z17]),(1,[z0,z1,z2,z735,z6])],[(0,[z0,z1,z2,z24,z5,z135])],[(0,[z187,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z59,z5,z6]),(0,[z0,z1,z24,z5,z6,z410]),(0,[z0,z467,z2,z3,z5,z18]),(0,[z1,z3,z5,z17,z206,z18]),(0,[z1,z2,z3,z786,z5,z18])],[(0,[z0,z1,z2,z1203,z5,z6]),(0,[z0,z1,z2,z24,z5,z94]),(0,[z0,z1,z2,z1204,z5,z6]),(0,[z0,z1,z2,z3,z5,z1205]),(0,[z1206,z0,z1,z2,z3,z5]),(0,[z89,z0,z1,z3,z45,z17]),(0,[z1019,z1,z2,z3,z5,z18]),(0,[z0,z1,z2,z3,z5,z1207])],[(0,[z1,z2,z3,z292,z5,z38])],[(0,[z119,z0,z2,z3,z69,z6]),(0,[z0,z245,z2,z24,z5,z6])],[(1,[z0,z1,z2,z3,z728])],[(0,[z0,z1,z2,z3,z5,z1208]),(0,[z1036,z0,z2,z3,z5,z6]),(0,[z0,z1,z2,z12,z5,z132]),(0,[z1209,z1,z2,z3,z5,z6])],[(0,[z0,z213,z2,z207,z5,z6])],[(0,[z313,z0,z1,z2,z5,z18])],[(0,[z0,z1,z2,z3,z1210,z6]),(0,[z155,z1,z2,z3,z5,z559]),(0,[z0,z1,z2,z1211,z5,z6]),(0,[z1040,z1,z2,z3,z5,z17])],[(0,[z0,z1,z2,z3,z355,z17]),(0,[z0,z2,z3,z5,z751,z6]),(0,[z119,z0,z2,z3,z5,z17]),(0,[z49,z0,z1,z2,z5,z524])],[(0,[z425,z0,z1,z24,z5,z6]),(0,[z603,z0,z1,z2,z266,z6])],[(0,[z0,z1,z2,z5,z1212,z6]),(0,[z0,z1,z2,z59,z5,z18]),(0,[z187,z1,z2,z3,z5,z18])],[(0,[z131,z1,z2,z3,z5,z17])]],
   [[(0,[z0,z1,z2,z3,z5,z1213]),(0,[z0,z1,z2,z1214,z5,z6])],[(0,[z0,z1,z379,z24,z5,z6]),(0,[z30,z1,z2,z3,z292,z5]),(0,[z0,z1,z2,z3,z5,z1215]),(0,[z0,z467,z2,z3,z51,z6]),(0,[z0,z1,z2,z3,z360,z566])],[(0,[z1,z2,z3,z5,z6,z206]),(0,[z52,z0,z1,z2,z12,z5]),(0,[z0,z467,z2,z3,z5,z521]),(0,[z0,z1,z2,z3,z5,z521])],[(0,[z1216,z1,z2,z3,z5,z6]),(0,[z49,z0,z1,z2,z508,z5]),(0,[z1,z2,z12,z5,z206,z18]),(0,[z1217,z0,z1,z2,z5,z6]),(0,[z1036,z0,z2,z3,z5,z18]),(0,[z162,z0,z1,z2,z5,z230])],[(0,[z0,z1,z2,z1218,z5,z6]),(0,[z0,z1,z2,z371,z5,z199]),(0,[z0,z213,z2,z207,z5,z18])],[(0,[z126,z1,z2,z3,z70,z6]),(0,[z0,z1,z2,z3,z5,z1219]),(0,[z0,z1,z2,z3,z5,z1220]),(0,[z0,z1,z2,z766,z5,z6]),(0,[z10,z0,z2,z5,z402,z80]),(0,[z1069,z0,z1,z2,z3,z5])],[(0,[z0,z1,z2,z5,z164,z17])],[(0,[z0,z232,z2,z3,z79,z6]),(0,[z36,z1,z87,z24,z5,z6]),(0,[z0,z1,z2,z93,z598,z5]),(0,[z1221,z0,z1,z2,z3,z5]),(0,[z90,z0,z2,z3,z5,z225]),(0,[z174,z1,z2,z3,z5,z17])],[(0,[z1222,z1,z2,z3,z5,z6]),(0,[z0,z1,z160,z3,z5,z778]),(0,[z1,z2,z3,z5,z178,z17])],[(0,[z0,z1,z2,z3,z5,z1223]),(0,[z0,z2,z3,z118,z608,z6]),(0,[z1,z2,z3,z5,z6,z1224]),(0,[z0,z1,z2,z3,z5,z1225])],[(0,[z0,z1,z2,z3,z5,z1226])],[(0,[z0,z1,z2,z5,z1227,z6]),(0,[z0,z1,z2,z1228,z5,z6]),(0,[z0,z1,z427,z24,z5,z6]),(0,[z823,z0,z1,z2,z5,z6])],[(0,[z0,z1,z2,z3,z5,z1229]),(0,[z49,z0,z1,z2,z5,z230])],[(0,[z0,z1230,z2,z3,z5,z6]),(0,[z0,z1,z3,z5,z17,z123]),(0,[z0,z1,z2,z5,z6,z767])],[(0,[z0,z1,z2,z237,z5,z50]),(0,[z406,z1,z2,z12,z5,z6]),(0,[z224,z1,z2,z3,z5,z169]),(0,[z1,z2,z3,z5,z1129,z17])],[(0,[z0,z1,z2,z3,z1231,z6]),(0,[z0,z1,z2,z3,z258,z199])]],
   [[(0,[z0,z1,z2,z3,z5,z1232]),(0,[z0,z1,z2,z3,z5,z1233]),(0,[z198,z1,z2,z43,z5,z17]),(0,[z1234,z0,z1,z2,z5,z6]),(0,[z0,z2,z3,z5,z18,z1157]),(0,[z483,z0,z1,z2,z3,z66])],[(0,[z0,z1,z2,z3,z5,z1235]),(0,[z607,z1,z2,z3,z5,z80])],[],[(0,[z0,z1,z2,z3,z5,z1236]),(0,[z0,z1,z2,z1237,z5,z6])],[(0,[z0,z1,z2,z3,z1238,z6]),(0,[z143,z1,z2,z731,z5,z6]),(0,[z156,z1,z2,z3,z5,z494]),(0,[z0,z1,z2,z1239,z5,z6]),(0,[z0,z1,z2,z218,z5,z17])],[(0,[z78,z1,z226,z375,z5,z6]),(0,[z0,z1,z2,z3,z79,z17]),(0,[z0,z1240,z2,z3,z5,z6]),(0,[z0,z2,z3,z5,z475,z6]),(0,[z0,z1,z24,z5,z6,z308]),(0,[z333,z1,z2,z137,z5,z6]),(0,[z224,z1,z2,z3,z5,z17])],[(0,[z0,z1241,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z1242]),(0,[z40,z1,z2,z3,z5,z17]),(0,[z0,z1,z2,z446,z108,z6]),(0,[z0,z1,z591,z12,z5,z6]),(0,[z844,z0,z1,z2,z5,z6])],[(0,[z1243,z0,z1,z3,z5,z6]),(0,[z0,z1,z1244,z3,z5,z6]),(0,[z0,z1,z2,z5,z18,z1165])],[(0,[z0,z1,z2,z1245,z5,z6]),(0,[z1246,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z6,z711])],[(0,[z0,z1247,z2,z3,z5,z6]),(0,[z0,z1,z2,z12,z5,z50])],[(0,[z0,z1,z2,z3,z1248,z6])],[(0,[z326,z1,z2,z12,z5,z6]),(0,[z0,z1,z2,z3,z5,z1249])],[(0,[z0,z1,z2,z125,z5,z279]),(0,[z0,z1,z2,z1250,z5,z6]),(0,[z0,z1,z2,z1251,z5,z6])],[(0,[z28,z20,z2,z24,z5,z6])],[(0,[z0,z1,z2,z3,z1252,z6]),(0,[z0,z1,z2,z3,z387,z478]),(0,[z0,z1,z2,z1253,z5,z6])],[(0,[z0,z1,z2,z3,z1254,z6]),(0,[z0,z1,z2,z3,z5,z478])]],
   [[(0,[z493,z35,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z999,z5]),(0,[z0,z1,z2,z5,z6,z1255]),(0,[z1,z2,z3,z1062,z5,z6]),(0,[z0,z2,z3,z751,z31,z6]),(0,[z1256,z1,z2,z3,z5,z6]),(0,[z0,z2,z3,z5,z475,z18])],[(0,[z607,z1,z2,z3,z5,z279]),(0,[z860,z1,z2,z24,z5,z6])],[(0,[z1,z2,z226,z3,z355,z6]),(0,[z0,z1,z2,z3,z1257,z6]),(0,[z10,z0,z129,z2,z3,z5]),(0,[z828,z0,z1,z2,z12,z5]),(0,[z0,z1,z2,z202,z5,z132])],[(0,[z1258,z0,z1,z2,z5,z6]),(0,[z112,z1,z2,z24,z5,z6]),(0,[z89,z0,z1,z414,z45,z6]),(0,[z13,z1,z3,z5,z206,z18]),(0,[z0,z1,z3,z5,z6,z778]),(0,[z0,z1,z2,z1259,z5,z6])],[(0,[z0,z1260,z2,z3,z5,z6])],[(0,[z224,z245,z2,z3,z5,z6])],[(0,[z1261,z0,z1,z2,z5,z6]),(0,[z0,z400,z2,z24,z5,z6]),(0,[z0,z1,z2,z3,z751,z6])],[(0,[z131,z2,z3,z118,z5,z6]),(0,[z1262,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z1263,z5,z6])],[(0,[z0,z1,z2,z1264,z5,z6]),(0,[z1051,z0,z1,z2,z3,z6]),(0,[z906,z0,z1,z2,z24,z5])],[(0,[z0,z400,z2,z3,z70,z6])],[(0,[z1265,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z387,z6]),(0,[z0,z1266,z2,z3,z5,z6]),(0,[z0,z2,z3,z5,z17,z1120])],[(0,[z0,z1,z2,z3,z5,z6]),(0,[z0,z467,z2,z3,z5,z6]),(0,[z0,z54,z58,z3,z5,z17])],[(0,[z0,z1267,z2,z3,z5,z6]),(0,[z1019,z1,z2,z3,z5,z6])],[(0,[z0,z1,z683,z3,z5,z18]),(0,[z0,z734,z2,z12,z5,z6]),(0,[z89,z0,z1,z436,z45,z6])],[(0,[z0,z1,z2,z3,z5,z1268]),(0,[z0,z1,z2,z1269,z5,z6]),(0,[z0,z1,z2,z159,z5,z99]),(0,[z0,z1,z2,z5,z6,z914])],[(0,[z0,z1,z2,z1270,z5,z6]),(0,[z128,z0,z1,z3,z45,z6]),(0,[z0,z1,z562,z24,z5,z6]),(0,[z0,z1260,z2,z3,z5,z18])]],
   [[(0,[z166,z156,z0,z1,z2,z5]),(0,[z0,z1,z2,z1271,z5,z6]),(0,[z0,z1,z2,z24,z958,z6])],[(0,[z0,z1,z2,z107,z108,z17])],[(0,[z0,z1,z2,z1272,z5,z6]),(0,[z1262,z1,z2,z3,z5,z18])],[(0,[z0,z1,z2,z1273,z5,z6]),(0,[z0,z1,z2,z3,z5,z1274]),(0,[z0,z878,z2,z3,z5,z6])],[(0,[z0,z1275,z2,z3,z5,z6]),(0,[z0,z1,z254,z3,z51,z6])],[(0,[z0,z1,z2,z3,z387,z18]),(0,[z92,z1,z2,z3,z5,z18]),(0,[z0,z1,z2,z3,z5,z1276]),(0,[z0,z1,z2,z5,z6,z1277]),(0,[z0,z1,z2,z3,z5,z1278]),(0,[z1279,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z18]),(0,[z310,z20,z2,z3,z5,z6])],[(0,[z0,z1,z2,z1280,z5,z6]),(0,[z0,z117,z2,z3,z751,z6])],[(0,[z78,z153,z226,z3,z5,z6]),(0,[z0,z1,z372,z24,z5,z6]),(0,[z0,z1,z1013,z24,z5,z6])],[(0,[z1,z2,z3,z355,z38,z6]),(0,[z264,z1,z2,z12,z5,z6])],[(0,[z1,z2,z3,z5,z745,z6]),(0,[z0,z1,z2,z24,z5,z247]),(0,[z1281,z1,z2,z3,z5,z6])],[(0,[z0,z35,z2,z3,z4,z6]),(0,[z91,z0,z21,z3,z5,z6]),(0,[z910,z1,z2,z3,z5,z6])],[(0,[z82,z1,z2,z3,z70,z6]),(0,[z0,z2,z234,z3,z31,z6]),(0,[z0,z1,z2,z3,z5,z1282])],[(0,[z0,z1283,z2,z3,z5,z6]),(0,[z0,z1,z2,z371,z5,z50]),(0,[z1284,z0,z1,z2,z5,z6]),(0,[z0,z1,z2,z218,z5,z216]),(0,[z1178,z1,z2,z3,z5,z17])],[(0,[z0,z1285,z2,z3,z5,z6]),(0,[z937,z0,z1,z2,z24,z5])],[(0,[z0,z1,z2,z648,z168,z6])]],
   [[(0,[z0,z1286,z2,z3,z5,z6]),(0,[z0,z1,z2,z5,z6,z1287]),(0,[z162,z0,z1,z2,z5,z510]),(0,[z0,z1,z160,z3,z5,z17]),(0,[z1279,z1,z2,z3,z5,z18])],[(0,[z0,z1,z2,z1288,z5,z6])],[(0,[z0,z1289,z2,z3,z5,z6]),(0,[z1290,z0,z1,z2,z5,z6]),(0,[z313,z143,z1,z2,z5,z6]),(0,[z0,z1,z2,z1291,z5,z6])],[(0,[z1,z87,z3,z5,z6,z704]),(0,[z0,z1,z2,z24,z5,z304]),(0,[z0,z467,z2,z12,z5,z6])],[(0,[z0,z1,z2,z12,z5,z279]),(0,[z286,z0,z1,z24,z5,z235]),(0,[z0,z1,z2,z24,z973,z5]),(0,[z0,z1,z2,z24,z185,z65])],[(0,[z0,z1292,z2,z3,z5,z6]),(0,[z143,z1,z2,z322,z5,z6]),(0,[z30,z42,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z157,z18]),(0,[z0,z1,z3,z5,z17,z18])],[(0,[z155,z1,z2,z3,z325,z6]),(0,[z91,z0,z21,z3,z5,z18]),(0,[z0,z1,z2,z3,z5,z1293]),(0,[z439,z0,z1,z24,z5,z6]),(0,[z89,z0,z245,z3,z45,z6])],[],[(0,[z1294,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z258,z50])],[(0,[z0,z1295,z2,z3,z5,z6]),(0,[z49,z0,z1,z2,z5,z510]),(0,[z0,z1,z2,z26,z5,z71])],[(0,[z0,z1,z2,z731,z5,z6]),(0,[z1,z2,z24,z5,z6,z843])],[(0,[z0,z490,z2,z3,z118,z6]),(0,[z0,z1,z2,z3,z5,z1296]),(0,[z0,z1,z25,z1013,z5,z6]),(0,[z52,z0,z1,z2,z3,z5]),(0,[z49,z0,z1,z2,z175,z5])],[(0,[z313,z0,z1,z2,z5,z17])],[],[(0,[z1,z20,z2,z3,z5,z559]),(0,[z0,z81,z2,z24,z5,z11]),(0,[z187,z1,z2,z12,z5,z6])],[(0,[z0,z153,z2,z24,z5,z6]),(0,[z166,z30,z0,z1,z2,z5]),(0,[z0,z1,z2,z3,z5,z1297]),(0,[z105,z0,z1,z2,z5,z72]),(0,[z0,z1298,z2,z3,z5,z6])]],
   [[(0,[z1,z2,z3,z5,z1113,z6])],[(0,[z0,z1,z2,z3,z1299,z6]),(0,[z77,z0,z1,z2,z5,z6])],[(0,[z0,z1,z2,z125,z5,z478]),(0,[z0,z1,z2,z1300,z5,z6]),(0,[z1301,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z18,z1224])],[(0,[z0,z1,z2,z203,z5,z6]),(0,[z0,z1,z2,z3,z1302,z6]),(0,[z0,z1,z2,z24,z5,z67]),(0,[z0,z1,z2,z3,z1303,z5]),(0,[z406,z1,z2,z3,z5,z17]),(0,[z0,z1,z3,z51,z917,z6]),(0,[z0,z1,z2,z93,z5,z124]),(0,[z0,z1,z2,z3,z65,z728])],[(0,[z163,z0,z1,z2,z24,z5]),(0,[z49,z0,z1,z2,z5,z32])],[(0,[z0,z117,z2,z24,z118,z6]),(0,[z0,z1,z3,z1013,z5,z6]),(0,[z1,z2,z12,z5,z178,z6])],[(0,[z909,z0,z1,z2,z3,z5])],[(0,[z0,z1,z2,z3,z1304,z6]),(0,[z1,z2,z3,z5,z38,z279]),(0,[z0,z561,z2,z24,z5,z6]),(0,[z0,z1,z807,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z1305]),(0,[z0,z1,z2,z3,z5,z1306]),(0,[z0,z1,z2,z1307,z5,z6]),(0,[z0,z2,z3,z5,z771,z80]),(0,[z0,z192,z2,z3,z5,z11])],[(0,[z0,z1,z2,z3,z5,z1308]),(0,[z0,z1,z160,z12,z5,z17]),(0,[z0,z1,z2,z3,z6,z728]),(0,[z0,z1,z2,z1309,z5,z6])],[(0,[z221,z35,z2,z3,z355,z6]),(0,[z561,z2,z3,z5,z38,z6]),(0,[z119,z0,z2,z3,z31,z6]),(0,[z0,z1,z73,z24,z5,z6]),(0,[z0,z730,z2,z3,z5,z6]),(0,[z0,z1,z2,z1310,z5,z6]),(0,[z716,z1,z2,z3,z5,z6]),(0,[z264,z1,z2,z93,z3,z5])],[(0,[z205,z35,z2,z3,z70,z6]),(0,[z36,z1,z756,z3,z5,z6]),(0,[z0,z1,z2,z161,z5,z17])],[(0,[z0,z1,z2,z375,z79,z6]),(0,[z30,z1,z2,z3,z5,z279]),(0,[z0,z1,z2,z3,z5,z1311]),(0,[z0,z1,z591,z3,z5,z17]),(0,[z0,z1,z2,z534,z5,z72]),(0,[z0,z1,z2,z1312,z5,z6])],[(0,[z484,z1,z2,z3,z70,z6]),(0,[z0,z1,z2,z3,z267,z5]),(0,[z0,z1,z2,z3,z5,z1313]),(0,[z1314,z1,z2,z3,z5,z6]),(0,[z77,z0,z1,z2,z5,z18])],[(0,[z36,z1,z374,z3,z5,z6]),(0,[z0,z1,z2,z125,z387,z6]),(0,[z0,z1,z2,z203,z5,z485]),(1,[z1,z2,z731,z5,z6]),(0,[z0,z2,z21,z3,z258,z6]),(0,[z0,z1,z2,z12,z5,z521]),(0,[z0,z1,z3,z5,z917,z6])],[(0,[z0,z1,z2,z3,z5,z1315]),(0,[z0,z1,z2,z125,z5,z6]),(0,[z0,z1,z2,z203,z5,z18])],[(0,[z10,z0,z2,z3,z5,z270])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 501) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 501).take 511) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1012).take 399) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1411)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [501, 511, 399] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 158).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 158).take 162).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 320).take 175).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 495).take 17).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 512)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [158, 162, 175, 17] = true :=
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

end PEqualNP.Outside.L_meta_38745

theorem PEqualNP.Outside.L_meta_38745 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808426 * 2 ^ 32 + 4004176032) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808426 * 2 ^ 32 + 4004176032) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_38745.solve